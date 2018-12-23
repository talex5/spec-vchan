A TLA+ specification for Xen vchan.

A Xen vchan is a bidirectional channel, similar to a Unix-domain socket,
but for communicating between different VMs (running on a single host).

One of the two VMs, the "server", allocates three regions of memory:

1. A ring buffer for sending data from the client to the server.
2. A ring buffer for sending data from the server to the client.
3. A control structure.

If the ring buffers are small enough, all three can be in the same physical
page of memory. The server grants the client access to the pages. It also
creates a listening (unbound) event channel port for the client.
The server publishes details of the shared memory and event port to e.g. XenStore.
The client maps the memory into its address space and connects to the event channel.

A vchan is bidirectional, but the two directions are largely independent, so this
specification is written in terms of a single direction only. To model the complete
channel you would instantiate this module twice, sharing the event channel and
liveness flags between them (but reversing them, so that SenderLive refers to
the client's liveness flag in one direction and to the server's in the other).

We assume here that the memory has already been allocated, shared, and mapped
by the client. The algorithm described here provides reliable lock-free operation,
allowing the sender and receiver to write to and read from the buffer at the same
time without risk of data corruption or deadlock.

I believe that the C implementation implements this algorithm except for one detail:
when the sender closes the connection (and the receiver doesn't) this version
ensures that all data already transmitted will be received. My assumption is that
this is simply a bug in the C implementation, but perhaps it was intentional.
I have no special information about the design of the protocol; I just read the
code and made guesses.

The C implementation can be used in blocking or non-blocking mode. I believe this
algorithm covers both cases, depending on whether you consider the blocking states
to be part of the library or part of the application.

The library can be used in streaming mode or in packet mode. In packet mode, sending
waits until there is enough space for the whole message before starting to write it,
while in streaming mode it writes as much as possible.

TODO: Currently, the specification assumes streaming mode.
That is, we assume that the sender will eventually send some data whenever there is
space, which is not the case for packet mode.

The C implementation also provides packet-based receive, which waits until there
is enough data in the buffer before starting to read. I believe that if you want
to read a fixed-size message, it would be better to stream it into a fixed-size
buffer by calling the streaming read function in a loop. If the sender is doing
matching fixed-size writes then this will always succeed in a single read, and
if not then it avoids the risk of deadlock.

This specification is organised as follows:

1. Constants and definitions.
2. The algorithm (as PlusCal, followed by its translation to TLA).
3. The properties (`Availability' and `Integrity').
4. How to check the properties using TLC.
5. Inductive invariants for Integrity and deadlock freedom.
6. Proofs of the above.
7. Some additional proofs (`ReadLimit` and `WriteLimit`).

-- Thomas Leonard, 2018

------------------------------- MODULE vchan -------------------------------

EXTENDS Naturals, Sequences, TLAPS, SequenceTheorems

CONSTANT Byte           \* 0..255, but overridable for modelling purposes.

(* The size of the ring buffer in bytes. The two directions do not need to use
   the same size buffer. In reality, the buffer size must be a power of 2
   between 2^10 and 2^20. For modelling purposes however it is convenient to
   allow any size greater than zero. *)
CONSTANT BufferSize
ASSUME BufferSizeType == BufferSize \in Nat \ {0}

(* The most data a sender will try to send in one go.
   This will typically be MAX_INT, but it is convenient to set it lower in models. *)
CONSTANT MaxWriteLen
ASSUME MaxWriteLenType == MaxWriteLen \in Nat

(* The most data a receiver will try to read in one go.
   This will typically be MAX_INT, but it is convenient to set it lower in models. *)
CONSTANT MaxReadLen
ASSUME MaxReadLenType == MaxReadLen \in Nat

(* Normally a receiving application will start by performing a read call, and blocking
   only if the buffer is empty. However, some applications (e.g. QubesDB) block first
   without checking the buffer. *)
CONSTANT ReceiverBlocksFirst
ASSUME ReceiverBlocksFirst \in BOOLEAN

Min(x, y) == IF x < y THEN x ELSE y

(* The type of the entire message the client application sends. *)
MESSAGE == Seq(Byte)

(* The type of finite messages up to length L.
   A sequence in TLA is a function from index to value.
   [ 1..N -> Byte ] is the set of all Byte sequences of length N. *)
FINITE_MESSAGE(L) == UNION ( { [ 1..N -> Byte ] : N \in 0..L } )

(* MSG is the set of messages we may try to send.
   This is the set of messages with lengths from 1 to
   MaxWriteLen (i.e. excluding << >>): *)
MSG == FINITE_MESSAGE(MaxWriteLen) \ { << >> }

(* Take(m, i) is just the first i elements of message m.
   Sequences in TLA+ can be confusing because they are indexed from 1.
   Using Take avoids this issue. *)
Take(m, i) == SubSeq(m, 1, i)

(* Everything except the first i elements of message m. *)
Drop(m, i) == SubSeq(m, i + 1, Len(m))

(* The system is modelled as five processes, each with its own ID.
   The close operations are modelled as separate processes because they can
   occur in parallel with a read or write operation. *)
SenderWriteID    == "SW"   \* The sender writing data to the buffer
SenderCloseID    == "SC"   \* The sender closing the channel
ReceiverReadID   == "RR"   \* The receiver reading from the buffer
ReceiverCloseID  == "RC"   \* The receiver closing the channel
SpuriousID       == "SP"   \* Spurious interrupts from the other direction

-----------------------------------------------------------------------------

(* Overview of the algorithm:

   On the sending side:

   1. The sending application asks to send some bytes.
      We check whether the receiver has closed the channel and abort if so.
   2. We check the amount of buffer space available.
   3. If there isn't enough, we set NotifyRead so the receiver will notify us when there is more.
      We also check the space again after this, in case it changed while setting the flag.
   4. If there is any space:
      - We write as much data as we can to the buffer.
      - If the NotifyWrite flag is set, we clear it and notify the receiver of the write.
   5. If we wrote everything, we return success.
   6. Otherwise, we wait to be notified of more space.
   7. We check whether the receiver has closed the channel.
      If so we abort. Otherwise, we go back to step 2.

   On the receiving side:

   1. The receiving application asks us to read some data.
   2. We check the amount of data available in the buffer.
   3. If there isn't any, we set NotifyWrite so the sender will notify us when there is.
      We also check the space again after this, in case it changed while setting the flag.
   4. If there is some data, we read some or all of it.
      If the NotifyRead flag is set, we clear it and notify the receiver of the new space.
      We return the data read to the application.
   5. Otherwise, we check whether the sender has closed the connection.
      If it has, we check the buffer again in case data was added after we checked.
      If the buffer is still empty, we abort.
      If there is now data available, we go back to step 2 to read it.
   6. Otherwise (if the connection is still open), we wait to be notified of more data
      and go back to 2.

   Either side can close the connection by clearing their "live" flag and signalling
   the other side. We assume there is also some process-local way that the close operation
   can notify its own side if it's currently blocked. *)

(* --algorithm vchan {
   (* This section gives PlusCal code for each of the five processes and their state.
      Note: each label in the code below represents a state of the process,
      and the blocks of code between the labels are modelled as a single atomic action.

      These variables represent state shared by the client and server.
      Only one access (read or write) to a shared variable is allowed per atomic block.
      Otherwise, it wouldn't be possible to implement this in real code.
      (TLA calls this the "Single Access Rule") *)
  variables
    (* In the real system, srv_live and cli_live indicate the status of the endpoints.
       Either end can set its own value to 0 to indicate that it is closing the connection.
       If the client exits, the server detects this and sets cli_live to 0 on the client's behalf.
       For simplicity, we represent these as the "sender" and "receiver" states.
       For the client->server stream, SenderLive is cli_live, while
       for the server->client stream, SenderLive is srv_live, etc.
       Here, we are only modelling a single stream. *)
    SenderLive = TRUE,          \* Cleared by sender
    ReceiverLive = TRUE,        \* Cleared by receiver

    (* Buffer represents the data in transit from the sender to the receiver.

       In reality, we have a Xen ring, with a producer counter, a consumer counter,
       and an array used as a ring buffer. As such ring buffers are standard to Xen, we
       don't model it here in detail. Instead, the buffer is represented as the
       sequence of bytes that have been produced but not yet consumed. This sequence
       can be any length from 0 to the size of the buffer.

       The sender only changes this by appending to it (writing data and updating the producer counter
       in the real system), while the receiver only changes it by removing a prefix from the beginning
       (i.e. reading the data and updating the consumer counter).

       Calculating Len(Buffer) corresponds to taking the difference of the two counters.
       It is considered to be a single atomic read because in reality one of the two counters
       will be our local copy, so we only need one access to the shared state. *)
    Buffer = << >>,

    (* NotifyWrite is a shared flag that is set by the receiver to indicate that it wants to know when data
       has been written to the buffer. The sender checks it after adding data. If set, the sender
       clears the flag and notifies the receiver using the event channel. This is represented by
       DataReadyInt being set to TRUE. It becomes FALSE when the receiver handles the event.
       NotifyWrite is initialised to TRUE to support some programs (e.g. QubesDB) that block first,
       before checking the buffer state. *)
    NotifyWrite = TRUE,       \* Set by receiver, cleared by sender
    DataReadyInt = FALSE,     \* Set by sender, cleared by receiver

    (* NotifyRead is a shared flag that indicates that the sender wants to know when some data
       has been read and removed from the buffer (and, therefore, that more space is now available).
       If the receiver sees that this is set after removing data from the buffer,
       it clears the flag and signals the sender via the event channel, represented by SpaceAvailableInt. *)
    NotifyRead = FALSE,         \* Set by sender, cleared by receiver
    SpaceAvailableInt = FALSE;  \* Set by receiver, cleared by sender

  (* This process represents the sender application using the vchan library to send messages. *)
  fair process (SenderWrite = SenderWriteID)
  variables (* Our local belief about the space available for writing: *)
            free = 0,
            (* The remaining data that has not yet been added to the buffer: *)
            msg = << >>,
            (* Pseudo-variable recording all data ever sent by sender (for modelling): *)
            Sent = << >>;
  {
                      \* We are waiting for the application to send some data.
                      \*  The "-" means that it's OK if the application stops at this point
                      \* and never sends any more data.
sender_ready:-        while (TRUE) {
                        if (~SenderLive \/ ~ReceiverLive) goto Done
                        else {
                          \* Set msg to the message that the client is trying to send:
                          with (m \in MSG) { msg := m };
                          Sent := Sent \o msg;    \* Remember we wanted to send this
                        };
sender_write:           while (TRUE) {
                          free := BufferSize - Len(Buffer);
sender_request_notify:    if (free >= Len(msg)) goto sender_write_data
                          else NotifyRead := TRUE;
sender_recheck_len:       free := BufferSize - Len(Buffer);
sender_write_data:        if (free > 0) {
                            Buffer := Buffer \o Take(msg, Min(Len(msg), free));
                            msg := Drop(msg, Min(Len(msg), free));
                            free := 0;
sender_check_notify_data:   if (NotifyWrite) {
                              NotifyWrite := FALSE;   \* Atomic test-and-clear
sender_notify_data:           DataReadyInt := TRUE;   \* Signal receiver
                              if (msg = << >>) goto sender_ready
                            } else if (msg = << >>) goto sender_ready
                          };
sender_blocked:           await SpaceAvailableInt \/ ~SenderLive;
                          if (~SenderLive) goto Done;
                          else SpaceAvailableInt := FALSE;
sender_check_recv_live:   if (~ReceiverLive) goto Done;
                        }
                      }
  }

  (* This process represents the sender application asking the vchan library to close the channel,
     which can happen concurrently with a write operation. *)
  fair process (SenderClose = SenderCloseID) {
    \* "-" because we're not forced ever to close the connection.
    sender_open:-         SenderLive := FALSE;  \* Clear liveness flag
    sender_notify_closed: DataReadyInt := TRUE; \* Signal receiver
  }

  (* This process represents the receiver application asking the vchan library to read data into a buffer.
     The whole process is marked as "fair", meaning that the receiving application must keep performing
     reads. Otherwise, we can't show any useful liveness property of the system, since data might never
     get read. *)
  fair process (ReceiverRead = ReceiverReadID)
  variables have = 0,     \* The amount of data we think the buffer contains.
            Got = << >>;  \* Pseudo-variable recording all data ever received by receiver.
  {
recv_init:          if (ReceiverBlocksFirst) {
                      \* (QubesDB does this)
                      goto recv_await_data;
                    };
recv_ready:         while (ReceiverLive) {
recv_reading:         while (TRUE) {
                        have := Len(Buffer);
recv_got_len:           either {
                          if (have > 0) goto recv_read_data
                          else NotifyWrite := TRUE;
                        } or { \* (see note 1)
                          NotifyWrite := TRUE;
                        };
recv_recheck_len:       have := Len(Buffer);
recv_read_data:         if (have > 0) {
                          with (len \in 1..have) {
                            Got := Got \o Take(Buffer, len);
                            Buffer := Drop(Buffer, len);
                          };
                          have := 0;
recv_check_notify_read:   if (NotifyRead) {
                            NotifyRead := FALSE;      \* (atomic test-and-clear)
recv_notify_read:           SpaceAvailableInt := TRUE;
                            goto recv_ready;          \* Return success
                          } else goto recv_ready;     \* Return success
                        } else if (~SenderLive \/ ~ReceiverLive) {
                          \* (see note 2)
recv_final_check:         if (Len(Buffer) = 0) goto Done;
                          else goto recv_reading;
                        };
recv_await_data:        await DataReadyInt \/ ~ReceiverLive;
                        if (~ReceiverLive) goto Done;
                        else DataReadyInt := FALSE;
                      }
                    }
  }

  (* The receiver can close the connection at any time, so model close as a separate process. *)
  fair process (ReceiverClose = ReceiverCloseID) {
    (* "-" because we're not required ever to close the connection. *)
    recv_open:-         ReceiverLive := FALSE;      \* Clear liveness flag
    recv_notify_closed: SpaceAvailableInt := TRUE;  \* Signal sender
  }

  (* We share our event channel with the stream going in the other direction,
     so we can receive wakeups even when there's nothing to do. This process
     represents that possibility. Also, there are various inefficient ways to
     use the library that involve setting the flags unnecessarily. This show
     that doing that is always safe. *)
  process (SpuriousInterrupts = SpuriousID) {
    spurious: while (TRUE) {
                either SpaceAvailableInt := TRUE
                or     DataReadyInt := TRUE
              }
  }
}
*)

(* Notes on the algorithm:

   Note 1:
   
   The C receiver code sets NotifyWrite whenever there isn't enough data to fill the
   buffer provided by the application completely. Typically, however, an application
   will just give us a buffer big enough for the largest possible message and be happy
   with whatever actual message we return. Therefore, it would probably be better to
   set the flag here only if there is no data at all.

   The first branch of the `either' represents the recommended algorithm. 
   The `or' branch allows an implementation to set the NotifyWrite flag in other cases too.
   This covers the behaviour of the C implementation when there is data in Buffer
   but not as much as requested, as well as the behaviour of QubesDB (which always
   sets the flag however much data there is).

   Note 2:
   
   The C code doesn't do the recv_final_check check, but that presumably means that it
   might not read all of the client's data.

   Note on formatting:
   
   TLA's PDF rendering gets the indentation wrong if you put a semicolon after a closing brace,
   but the PlusCal-to-TLA translator requires it.
*)

-----------------------------------------------------------------------------

(* This section is just the generated translation of the above PlusCal. You can skip it. *)

\* BEGIN TRANSLATION
VARIABLES SenderLive, ReceiverLive, Buffer, NotifyWrite, DataReadyInt, 
          NotifyRead, SpaceAvailableInt, pc, free, msg, Sent, have, Got

vars == << SenderLive, ReceiverLive, Buffer, NotifyWrite, DataReadyInt, 
           NotifyRead, SpaceAvailableInt, pc, free, msg, Sent, have, Got >>

ProcSet == {SenderWriteID} \cup {SenderCloseID} \cup {ReceiverReadID} \cup {ReceiverCloseID} \cup {SpuriousID}

Init == (* Global variables *)
        /\ SenderLive = TRUE
        /\ ReceiverLive = TRUE
        /\ Buffer = << >>
        /\ NotifyWrite = TRUE
        /\ DataReadyInt = FALSE
        /\ NotifyRead = FALSE
        /\ SpaceAvailableInt = FALSE
        (* Process SenderWrite *)
        /\ free = 0
        /\ msg = << >>
        /\ Sent = << >>
        (* Process ReceiverRead *)
        /\ have = 0
        /\ Got = << >>
        /\ pc = [self \in ProcSet |-> CASE self = SenderWriteID -> "sender_ready"
                                        [] self = SenderCloseID -> "sender_open"
                                        [] self = ReceiverReadID -> "recv_init"
                                        [] self = ReceiverCloseID -> "recv_open"
                                        [] self = SpuriousID -> "spurious"]

sender_ready == /\ pc[SenderWriteID] = "sender_ready"
                /\ IF ~SenderLive \/ ~ReceiverLive
                      THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "Done"]
                           /\ UNCHANGED << msg, Sent >>
                      ELSE /\ \E m \in MSG:
                                msg' = m
                           /\ Sent' = Sent \o msg'
                           /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_write"]
                /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                                DataReadyInt, NotifyRead, SpaceAvailableInt, 
                                free, have, Got >>

sender_write == /\ pc[SenderWriteID] = "sender_write"
                /\ free' = BufferSize - Len(Buffer)
                /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_request_notify"]
                /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                                DataReadyInt, NotifyRead, SpaceAvailableInt, 
                                msg, Sent, have, Got >>

sender_request_notify == /\ pc[SenderWriteID] = "sender_request_notify"
                         /\ IF free >= Len(msg)
                               THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_write_data"]
                                    /\ UNCHANGED NotifyRead
                               ELSE /\ NotifyRead' = TRUE
                                    /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_recheck_len"]
                         /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                         NotifyWrite, DataReadyInt, 
                                         SpaceAvailableInt, free, msg, Sent, 
                                         have, Got >>

sender_recheck_len == /\ pc[SenderWriteID] = "sender_recheck_len"
                      /\ free' = BufferSize - Len(Buffer)
                      /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_write_data"]
                      /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                      NotifyWrite, DataReadyInt, NotifyRead, 
                                      SpaceAvailableInt, msg, Sent, have, Got >>

sender_write_data == /\ pc[SenderWriteID] = "sender_write_data"
                     /\ IF free > 0
                           THEN /\ Buffer' = Buffer \o Take(msg, Min(Len(msg), free))
                                /\ msg' = Drop(msg, Min(Len(msg), free))
                                /\ free' = 0
                                /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_check_notify_data"]
                           ELSE /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_blocked"]
                                /\ UNCHANGED << Buffer, free, msg >>
                     /\ UNCHANGED << SenderLive, ReceiverLive, NotifyWrite, 
                                     DataReadyInt, NotifyRead, 
                                     SpaceAvailableInt, Sent, have, Got >>

sender_check_notify_data == /\ pc[SenderWriteID] = "sender_check_notify_data"
                            /\ IF NotifyWrite
                                  THEN /\ NotifyWrite' = FALSE
                                       /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_notify_data"]
                                  ELSE /\ IF msg = << >>
                                             THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_ready"]
                                             ELSE /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_blocked"]
                                       /\ UNCHANGED NotifyWrite
                            /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                            DataReadyInt, NotifyRead, 
                                            SpaceAvailableInt, free, msg, Sent, 
                                            have, Got >>

sender_notify_data == /\ pc[SenderWriteID] = "sender_notify_data"
                      /\ DataReadyInt' = TRUE
                      /\ IF msg = << >>
                            THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_ready"]
                            ELSE /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_blocked"]
                      /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                      NotifyWrite, NotifyRead, 
                                      SpaceAvailableInt, free, msg, Sent, have, 
                                      Got >>

sender_blocked == /\ pc[SenderWriteID] = "sender_blocked"
                  /\ SpaceAvailableInt \/ ~SenderLive
                  /\ IF ~SenderLive
                        THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "Done"]
                             /\ UNCHANGED SpaceAvailableInt
                        ELSE /\ SpaceAvailableInt' = FALSE
                             /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_check_recv_live"]
                  /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                  NotifyWrite, DataReadyInt, NotifyRead, free, 
                                  msg, Sent, have, Got >>

sender_check_recv_live == /\ pc[SenderWriteID] = "sender_check_recv_live"
                          /\ IF ~ReceiverLive
                                THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "Done"]
                                ELSE /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_write"]
                          /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                          NotifyWrite, DataReadyInt, 
                                          NotifyRead, SpaceAvailableInt, free, 
                                          msg, Sent, have, Got >>

SenderWrite == sender_ready \/ sender_write \/ sender_request_notify
                  \/ sender_recheck_len \/ sender_write_data
                  \/ sender_check_notify_data \/ sender_notify_data
                  \/ sender_blocked \/ sender_check_recv_live

sender_open == /\ pc[SenderCloseID] = "sender_open"
               /\ SenderLive' = FALSE
               /\ pc' = [pc EXCEPT ![SenderCloseID] = "sender_notify_closed"]
               /\ UNCHANGED << ReceiverLive, Buffer, NotifyWrite, DataReadyInt, 
                               NotifyRead, SpaceAvailableInt, free, msg, Sent, 
                               have, Got >>

sender_notify_closed == /\ pc[SenderCloseID] = "sender_notify_closed"
                        /\ DataReadyInt' = TRUE
                        /\ pc' = [pc EXCEPT ![SenderCloseID] = "Done"]
                        /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                        NotifyWrite, NotifyRead, 
                                        SpaceAvailableInt, free, msg, Sent, 
                                        have, Got >>

SenderClose == sender_open \/ sender_notify_closed

recv_init == /\ pc[ReceiverReadID] = "recv_init"
             /\ IF ReceiverBlocksFirst
                   THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_await_data"]
                   ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_ready"]
             /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                             DataReadyInt, NotifyRead, SpaceAvailableInt, free, 
                             msg, Sent, have, Got >>

recv_ready == /\ pc[ReceiverReadID] = "recv_ready"
              /\ IF ReceiverLive
                    THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_reading"]
                    ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "Done"]
              /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                              DataReadyInt, NotifyRead, SpaceAvailableInt, 
                              free, msg, Sent, have, Got >>

recv_reading == /\ pc[ReceiverReadID] = "recv_reading"
                /\ have' = Len(Buffer)
                /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_got_len"]
                /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                                DataReadyInt, NotifyRead, SpaceAvailableInt, 
                                free, msg, Sent, Got >>

recv_got_len == /\ pc[ReceiverReadID] = "recv_got_len"
                /\ \/ /\ IF have > 0
                            THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_read_data"]
                                 /\ UNCHANGED NotifyWrite
                            ELSE /\ NotifyWrite' = TRUE
                                 /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_recheck_len"]
                   \/ /\ NotifyWrite' = TRUE
                      /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_recheck_len"]
                /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, DataReadyInt, 
                                NotifyRead, SpaceAvailableInt, free, msg, Sent, 
                                have, Got >>

recv_recheck_len == /\ pc[ReceiverReadID] = "recv_recheck_len"
                    /\ have' = Len(Buffer)
                    /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_read_data"]
                    /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                    NotifyWrite, DataReadyInt, NotifyRead, 
                                    SpaceAvailableInt, free, msg, Sent, Got >>

recv_read_data == /\ pc[ReceiverReadID] = "recv_read_data"
                  /\ IF have > 0
                        THEN /\ \E len \in 1..have:
                                  /\ Got' = Got \o Take(Buffer, len)
                                  /\ Buffer' = Drop(Buffer, len)
                             /\ have' = 0
                             /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_check_notify_read"]
                        ELSE /\ IF ~SenderLive \/ ~ReceiverLive
                                   THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_final_check"]
                                   ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_await_data"]
                             /\ UNCHANGED << Buffer, have, Got >>
                  /\ UNCHANGED << SenderLive, ReceiverLive, NotifyWrite, 
                                  DataReadyInt, NotifyRead, SpaceAvailableInt, 
                                  free, msg, Sent >>

recv_check_notify_read == /\ pc[ReceiverReadID] = "recv_check_notify_read"
                          /\ IF NotifyRead
                                THEN /\ NotifyRead' = FALSE
                                     /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_notify_read"]
                                ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_ready"]
                                     /\ UNCHANGED NotifyRead
                          /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                          NotifyWrite, DataReadyInt, 
                                          SpaceAvailableInt, free, msg, Sent, 
                                          have, Got >>

recv_notify_read == /\ pc[ReceiverReadID] = "recv_notify_read"
                    /\ SpaceAvailableInt' = TRUE
                    /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_ready"]
                    /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                    NotifyWrite, DataReadyInt, NotifyRead, 
                                    free, msg, Sent, have, Got >>

recv_final_check == /\ pc[ReceiverReadID] = "recv_final_check"
                    /\ IF Len(Buffer) = 0
                          THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "Done"]
                          ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_reading"]
                    /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                    NotifyWrite, DataReadyInt, NotifyRead, 
                                    SpaceAvailableInt, free, msg, Sent, have, 
                                    Got >>

recv_await_data == /\ pc[ReceiverReadID] = "recv_await_data"
                   /\ DataReadyInt \/ ~ReceiverLive
                   /\ IF ~ReceiverLive
                         THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "Done"]
                              /\ UNCHANGED DataReadyInt
                         ELSE /\ DataReadyInt' = FALSE
                              /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_reading"]
                   /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                   NotifyWrite, NotifyRead, SpaceAvailableInt, 
                                   free, msg, Sent, have, Got >>

ReceiverRead == recv_init \/ recv_ready \/ recv_reading \/ recv_got_len
                   \/ recv_recheck_len \/ recv_read_data
                   \/ recv_check_notify_read \/ recv_notify_read
                   \/ recv_final_check \/ recv_await_data

recv_open == /\ pc[ReceiverCloseID] = "recv_open"
             /\ ReceiverLive' = FALSE
             /\ pc' = [pc EXCEPT ![ReceiverCloseID] = "recv_notify_closed"]
             /\ UNCHANGED << SenderLive, Buffer, NotifyWrite, DataReadyInt, 
                             NotifyRead, SpaceAvailableInt, free, msg, Sent, 
                             have, Got >>

recv_notify_closed == /\ pc[ReceiverCloseID] = "recv_notify_closed"
                      /\ SpaceAvailableInt' = TRUE
                      /\ pc' = [pc EXCEPT ![ReceiverCloseID] = "Done"]
                      /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                      NotifyWrite, DataReadyInt, NotifyRead, 
                                      free, msg, Sent, have, Got >>

ReceiverClose == recv_open \/ recv_notify_closed

spurious == /\ pc[SpuriousID] = "spurious"
            /\ \/ /\ SpaceAvailableInt' = TRUE
                  /\ UNCHANGED DataReadyInt
               \/ /\ DataReadyInt' = TRUE
                  /\ UNCHANGED SpaceAvailableInt
            /\ pc' = [pc EXCEPT ![SpuriousID] = "spurious"]
            /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                            NotifyRead, free, msg, Sent, have, Got >>

SpuriousInterrupts == spurious

Next == SenderWrite \/ SenderClose \/ ReceiverRead \/ ReceiverClose
           \/ SpuriousInterrupts
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars((pc[SenderWriteID] # "sender_ready") /\ SenderWrite)
        /\ WF_vars((pc[SenderCloseID] # "sender_open") /\ SenderClose)
        /\ WF_vars(ReceiverRead)
        /\ WF_vars((pc[ReceiverCloseID] # "recv_open") /\ ReceiverClose)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

-----------------------------------------------------------------------------

(* To be implemented without locks, each atomic step must only access at most one shared
   variable. The elements of Buffer are not considered to be shared in this sense,
   as there is never a moment when any one element can be accessed by two processes.

   Here are the steps and the shared variables they access:

  - SenderWrite: (SenderLive and the producer index are considered to be local)
    - sender_ready: ReceiverLive
    - sender_write: Len(Buffer)               (get consumer index)
    - sender_request_notify: NotifyRead
    - sender_recheck_len: Len(Buffer)
    - sender_write_data: Buffer               (write producer index)
    - sender_check_notify_data: NotifyWrite   (atomic test-and-clear operation)
    - sender_notify_data: DataReadyInt
    - sender_blocked: SpaceAvailableInt
    - sender_check_recv_live: ReceiverLive

  - SenderClose:
    - sender_open: -
    - sender_notify_closed: DataReadyInt

  - ReceiverRead: (ReceiverLive and the consumer index are considered to be local)
    - recv_init: -
    - recv_ready: -
    - recv_reading: Len(Buffer)               (get producer index)
    - recv_got_len: NotifyWrite
    - recv_recheck_len: Len(Buffer)
    - recv_read_data: Buffer or SenderLive    (depending on local variable `have')
    - recv_check_notify_read: NotifyRead      (atomic test-and-clear operation)
    - recv_notify_read: SpaceAvailableInt
    - recv_final_check: Buffer
    - recv_await_data: DataReadyInt

  - ReceiverClose:
    - recv_open: -
    - recv_notify_closed: SpaceAvailableInt
  *)

-----------------------------------------------------------------------------

\* Properties the algorithm should satisfy.

(* An invariant describing the types of all variables (except pc). *)
TypeOK ==
  /\ Sent \in MESSAGE
  /\ Got \in MESSAGE
  /\ Buffer \in FINITE_MESSAGE(BufferSize)
  /\ SenderLive \in BOOLEAN
  /\ ReceiverLive \in BOOLEAN
  /\ NotifyWrite \in BOOLEAN
  /\ DataReadyInt \in BOOLEAN
  /\ NotifyRead \in BOOLEAN
  /\ SpaceAvailableInt \in BOOLEAN
  /\ free \in 0..BufferSize
  /\ msg \in FINITE_MESSAGE(MaxWriteLen)
  /\ have \in 0..BufferSize

(* Whatever we receive is the same as what was sent.
   (i.e. `Got' is a prefix of `Sent') *)
Integrity ==
  Take(Sent, Len(Got)) = Got

AvailabilityNat == Nat    \* Just to allow overriding it in TLC

(* Any data that the write function reports has been sent successfully
   (i.e. data in Sent when it is back at "sender_ready") will eventually
   be received (if the receiver doesn't close the connection).
   In particular, this says that it's OK for the sender to close its
   end immediately after sending some data.
   Note that this is not currently true of the C implementation. *)
Availability ==
  \A x \in AvailabilityNat :
    x = Len(Sent) /\ SenderLive /\ pc[SenderWriteID] = "sender_ready"
      ~> \/ Len(Got) >= x
         \/ ~ReceiverLive

(* If either side closes the connection, both end up in their Done state
   (or sender_ready, which is also outside the library). *)
ShutdownOK ==
  ~SenderLive \/ ~ReceiverLive
  ~> <>[] /\ pc[SenderWriteID] \in {"sender_ready", "Done"}
          /\ pc[ReceiverReadID] = "Done"

(* All the possible states of the program counter. *)
PCOK == pc \in [
    SW: {"sender_ready", "sender_write", "sender_request_notify", "sender_recheck_len",
         "sender_write_data", "sender_blocked", "sender_check_notify_data", "sender_notify_data",
         "sender_check_recv_live", "Done"},
    SC: {"sender_open", "sender_notify_closed", "Done"},
    RR: {"recv_init", "recv_ready", "recv_reading", "recv_got_len", "recv_recheck_len",
         "recv_read_data", "recv_final_check", "recv_await_data",
         "recv_check_notify_read", "recv_notify_read", "Done"},
    RC: {"recv_open", "recv_notify_closed", "Done"},
    SP: {"spurious"}
]

-----------------------------------------------------------------------------

(* Model checking

   You can load this file into the TLA Toolbox and create a new model to check for it.
   These parameters work well to test the claims above:

   "What is the model?":
     - BufferSize = 2
     - MaxReadLen = 2
     - MaxWriteLen = 2
     - Byte = 0..5

   Definition Overrides:
     - MSG <- MSG_SEQ
     - AvailabilityNat <- 0..5

   State Constraints:
     - Len(Sent) < 4

   Invariants:
     - TypeOK
     - PCOK
     - Integrity

   Properties:
     - Availability
     - ReadLimitCorrect
 *)

(* Override MSG with this to limit Sent to the form << 1, 2, 3, ... >>.
   This is much faster to check and will still detect any dropped or reordered bytes. *)
MSG_SEQ == { [ x \in 1..N |-> Len(Sent) + x ] : N \in 1..MaxWriteLen }

\* These are just here because we can't put expressions in TLC config files.
ZeroToFive == 0..5
LimitSent == Len(Sent) < 4

-----------------------------------------------------------------------------

\* Why does it work? (inductive invariants)

(* An inductive invariant that can be used to prove Integrity. i.e.
     /\ Init => IntegrityI
     /\ IntegrityI /\ Next => IntegrityI'
   The key properties are that:
   - The buffer always contains at least `have' bytes, even if the sender adds more.
   - The buffer always has at least `free' bytes unused, even if the receiver frees more.
   - Bytes are transferred atomically between the stages (msg, Buffer, Got).
 *)
IntegrityI ==
  /\ PCOK
  /\ pc[SenderWriteID] \in {"sender_ready"} => msg = << >>
  /\ TypeOK
  /\ Sent = Got \o Buffer \o msg
  /\ have <= Len(Buffer)
  /\ free <= BufferSize - Len(Buffer)
  /\ pc[SenderWriteID] \in {"sender_write", "sender_request_notify", "sender_recheck_len",
                            "sender_write_data", "sender_blocked", "sender_check_recv_live"} => msg /= << >>
  \* `have' is only used in these states:
  /\ pc[ReceiverReadID] \in {"recv_got_len", "recv_recheck_len", "recv_read_data"} \/ have = 0
  \* `free` is only used in these states:
  /\ pc[SenderWriteID] \in {"sender_write", "sender_request_notify", "sender_recheck_len",
                            "sender_write_data"} \/ free = 0

(* For deadlock / liveness properties, the key idea is (roughly):
   - Whenever NotifyRead is set, the sender's information is still accurate.
   - Whenever NotifyWrite is set, the receiver's information is still accurate. *)

(* The sender's information is accurate if whenever it is going to block, the buffer
   really is full. *)
SenderInfoAccurate ==
  \* We have accurate information:
  \/ Len(Buffer) + free = BufferSize
  \* In these states, we're going to check the buffer before blocking:
  \/ pc[SenderWriteID] \in {"sender_ready", "sender_request_notify", "sender_write",
                            "sender_recheck_len", "sender_check_recv_live", "Done"}
  \/ pc[SenderWriteID] \in {"sender_request_notify"} /\ free < Len(msg)
  \* If we've been signalled, we'll immediately wake next time we try to block:
  \/ SpaceAvailableInt
  \* We're about to write some data:
  \/ /\ pc[SenderWriteID] \in {"sender_write_data"}
     /\ free >= Len(msg)                \* We won't need to block
  \* If we wrote all the data we intended to, we'll return without blocking:
  \/ /\ pc[SenderWriteID] \in {"sender_check_notify_data", "sender_notify_data"}
     /\ Len(msg) = 0

(* The receiver's information is accurate if whenever it is going to block, the buffer
   really is empty. *)
ReaderInfoAccurate ==
  \* The buffer really is empty:
  \/ Len(Buffer) = 0
  \* In these states we're going to check the buffer before blocking, so
  \* we don't have any information to be out-of-date:
  \/ pc[ReceiverReadID] \in {"recv_ready", "recv_reading",
                             "recv_got_len", "recv_recheck_len",
                             "recv_check_notify_read", "recv_notify_read", "recv_final_check",
                             "Done"}  \* (if we're Done then we don't care)
  \* If we've been signalled, we'll immediately wake and check again even if we try to block:
  \/ DataReadyInt
  \* If we know there are some bytes in the buffer, we'll read them and return
  \* without blockig:
  \/ pc[ReceiverReadID] \in {"recv_read_data"} /\ have > 0

(* The notify flags are set correctly.
   If we're on a path to block, then we must have set our notify flag.
   Therefore, either it's still set, or the other process has cleared it and sent an event. *)
NotifyFlagsCorrect ==
  /\ (/\ pc[ReceiverReadID] \in {"recv_init", "recv_recheck_len", "recv_read_data", "recv_await_data"}
      /\ have = 0
      /\ ReceiverLive)
     => \/ NotifyWrite
        \/ DataReadyInt
        \/ pc[SenderWriteID] = "sender_notify_data"
  /\ (\/ pc[SenderWriteID] \in {"sender_recheck_len", "sender_write_data"} /\ free < Len(msg)
      \/ pc[SenderWriteID] \in {"sender_check_notify_data", "sender_notify_data"} /\ Len(msg) > 0
      \/ pc[SenderWriteID] \in {"sender_blocked"}
     ) /\ SenderLive
     => \/ NotifyRead
        \/ SpaceAvailableInt
        \/ pc[ReceiverReadID] = "recv_notify_read"

(* Some obvious facts about shutting down connections. *)
CloseOK ==
  \* An endpoint is live iff its close thread hasn't done anything:
  /\ pc[SenderCloseID] = "sender_open" <=> SenderLive
  /\ pc[ReceiverCloseID] = "recv_open" <=> ReceiverLive
  \* The send and receive loops don't terminate unless someone has closed the connection:
  /\ pc[ReceiverReadID] \in {"recv_final_check", "Done"} => ~ReceiverLive \/ ~SenderLive
  /\ pc[SenderWriteID] \in {"Done"} => ~ReceiverLive \/ ~SenderLive
  \* If the receiver closed the connection then we will get (or have got) the signal:
  /\ pc[ReceiverCloseID] = "Done" =>
          \/ SpaceAvailableInt
          \/ pc[SenderWriteID] \in {"sender_check_recv_live", "Done"}

(* The main inductive invariant:
   - The notify flags must have been set correctly.
   - If the notify flags are still set, the information is still up-to-date. *)
I ==
  /\ IntegrityI
  /\ CloseOK
  /\ NotifyFlagsCorrect
  \* If NotifyRead is set then:
  /\ NotifyRead =>
      \* The sender has accurate information about the buffer:
      \/ SenderInfoAccurate
      \* Or the flag is just about to be cleared:
      \/ pc[ReceiverReadID] \in {"recv_check_notify_read"}
  \* If NotifyWrite is set then:
  /\ NotifyWrite =>
      \* The receiver has accurate information about the buffer:
      \/ ReaderInfoAccurate
      \* Or the flag is just about to be cleared:
      \/ pc[SenderWriteID] \in {"sender_check_notify_data"}

-----------------------------------------------------------------------------

\* Checking the inductive invariants with TLC

\* A quick way to generate valid buffer configurations for model checking:
SentMax == 1
BufferI ==
  \E gl \in 0..SentMax :
  \E bl \in 0..Min(BufferSize, SentMax - gl) :
  \E ml \in 0..(SentMax - bl - gl):
  /\ Got    = [ x \in 1..gl |-> 1 ]
  /\ Buffer = [ x \in 1..bl |-> 1 ]
  /\ msg    = [ x \in 1..ml |-> 1 ]
  /\ Sent = Got \o Buffer \o msg

\* Faster replacement for TypeOK in the initial state
TypeOKI ==
  /\ BufferI
  /\ SenderLive \in BOOLEAN
  /\ ReceiverLive \in BOOLEAN
  /\ NotifyWrite \in BOOLEAN
  /\ DataReadyInt \in BOOLEAN
  /\ NotifyRead \in BOOLEAN
  /\ SpaceAvailableInt \in BOOLEAN
  /\ free \in 0..BufferSize
  /\ have \in 0..BufferSize

-----------------------------------------------------------------------------

\* Proof of Spec => []I
\* These proofs have all been verified automatically by TLAPS.

\* The only operations we do on messages are to split and join them.
\* TLAPS needs a lot of help to prove facts about this, so do it here all in one place:
LEMMA TakeDropFacts ==
  ASSUME NEW m \in MESSAGE,
         NEW i \in 1..Len(m)
  PROVE  /\ Take(m, i) \in MESSAGE
         /\ Drop(m, i) \in MESSAGE
         /\ Len(Take(m, i)) = i
         /\ Len(Drop(m, i)) = Len(m) - i
         /\ Take(m, i) \o Drop(m, i) = m
<1>1. /\ Take(m, i) \in MESSAGE
      /\ Len(Take(m, i)) = i
      /\ \A j \in 1..i : Take(m, i)[j] = m[j]
      BY DEF Take, MESSAGE
<1>2. /\ Drop(m, i) \in MESSAGE
      /\ Len(Drop(m, i)) = Len(m) - i
      /\ \A j \in 1 .. Len(m) - i : Drop(m, i)[j] = m[j + i]
    <2> DEFINE sm == i + 1
    <2> DEFINE sn == Len(m)
    <2> m \in Seq(Byte) BY DEF MESSAGE
    <2> sm \in 1..Len(m) + 1 OBVIOUS
    <2> sn \in sm-1..Len(m) OBVIOUS
    <2> SUFFICES
         /\ SubSeq(m, sm, sn) \in Seq(Byte)
         /\ Len(SubSeq(m, sm, sn)) = sn - sm + 1
         /\ \A j \in 1 .. sn-sm+1 : SubSeq(m, sm, sn)[j] = m[sm + j - 1] BY DEF Drop, MESSAGE
    <2> HIDE DEF sm, sn
    <2> QED BY SubSeqProperties
<1>3. Take(m, i) \o Drop(m, i) = m
    <2> DEFINE s1 == Take(m, i)
    <2> DEFINE s2 == Drop(m, i)
    <2> DEFINE t == s1 \o s2
    <2> Len(m) = Len(t) BY <1>1, <1>2
    <2> m \in Seq(Byte) BY DEF MESSAGE
    <2> t \in Seq(Byte)
        <3> s1 \in Seq(Byte) BY <1>1 DEF MESSAGE
        <3> s2 \in Seq(Byte) BY <1>2 DEF MESSAGE
        <3> QED BY ConcatProperties
    <2> ASSUME NEW j \in 1 .. Len(m)
        PROVE  m[j] = t[j]
        <3> \A k \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[k] =
                     IF k <= Len(s1) THEN s1[k] ELSE s2[k - Len(s1)] BY ConcatProperties
        <3> j \in 1..Len(s1) + Len(s2) OBVIOUS
        <3> CASE j <= Len(s1)
            <4> (s1 \o s2)[j] = s1[j] OBVIOUS
            <4> QED BY <1>1
        <3> CASE j > Len(s1)
            <4> (s1 \o s2)[j] = s2[j - Len(s1)] OBVIOUS
            <4> QED BY <1>2
        <3> QED OBVIOUS
    <2> SUFFICES m = t OBVIOUS
    <2> HIDE DEF t
    <2> QED BY SeqEqual
<1> QED BY <1>1, <1>2, <1>3 DEF MESSAGE, Take, Drop

\* A version of ConcatProperties in terms of the MESSAGE type.
LEMMA ConcatFacts ==
  ASSUME NEW a \in MESSAGE,
         NEW b \in MESSAGE
  PROVE  /\ a \o b \in MESSAGE
         /\ Len(a \o b) = Len(a) + Len(b)
BY ConcatProperties DEF MESSAGE

\* A FINITE_MESSAGE is a MESSAGE with a limited length.
LEMMA FiniteMessageFacts ==
  /\ BufferSize \in Nat
  /\ MaxWriteLen \in Nat
  /\ MaxReadLen \in Nat
  /\ \A n \in Nat : \A s :
     s \in MESSAGE /\ Len(s) <= n <=> s \in FINITE_MESSAGE(n)
BY BufferSizeType, MaxWriteLenType, MaxReadLenType DEF FINITE_MESSAGE, MESSAGE

\* Proving IntegrityI is sufficient to prove Integrity.
THEOREM IntegrityIUseful == IntegrityI => Integrity
<1> SUFFICES ASSUME IntegrityI,
                    Sent = Got \o Buffer \o msg
             PROVE  Take(Sent, Len(Got)) = Got
    BY DEF Integrity, IntegrityI
<1> TypeOK BY DEF IntegrityI
<1> /\ Buffer \in MESSAGE
    /\ Got \in MESSAGE
    /\ Sent \in MESSAGE
    /\ msg \in MESSAGE
    BY FiniteMessageFacts DEF TypeOK
<1> QED
    BY DEF MESSAGE, Take

\* Expose the string forms of these to the provers, so they can see they're all distinct.
USE DEF SenderWriteID, SenderCloseID, ReceiverReadID, ReceiverCloseID, SpuriousID

\* Some useful facts about lengths that are implied by TypeOK.
LEMMA LengthFacts ==
  ASSUME TypeOK
  PROVE  /\ Len(Buffer) \in 0..BufferSize
         /\ Len(msg) \in 0..MaxWriteLen
         /\ free \in 0..BufferSize
         /\ BufferSize \in Nat \ {0}
         /\ MaxWriteLen \in Nat
         /\ MaxReadLen \in Nat
         /\ BufferSize - Len(Buffer) \in 0..BufferSize
         /\ \A n \in Nat : \A m \in FINITE_MESSAGE(n) : Len(m) \in 0..n
         /\ \A m \in MESSAGE : Len(m) \in Nat
BY BufferSizeType, MaxWriteLenType, MaxReadLenType, BufferSizeType DEF TypeOK, FINITE_MESSAGE

(* Things that are true when we are transferring i bytes from src to dst, to give src2, dst2.
   This is a work-around to help TLAPS find the right lemma to use. *)
TransferResults(src, src2, dst, dst2, i) ==
  /\ src2 \in MESSAGE
  /\ Len(src2) = Len(src) - i
  /\ dst2 \in MESSAGE
  /\ Len(dst2) = Len(dst) + i
  /\ UNCHANGED (dst \o src)

(* Things that are true when we transfer some bytes from the start of `src'
   to the end of `dst' (e.g. from msg to Buffer, or from Buffer to Got). *)
LEMMA TransferFacts ==
  ASSUME NEW src, NEW src2,   \* (TLAPS doesn't cope with "NEW VARAIBLE src")
         NEW dst, NEW dst2,
         NEW i \in 1..Len(src),
         src \in MESSAGE,
         dst \in MESSAGE,
         dst2 = dst \o Take(src, i),
         src2 = Drop(src, i)
 PROVE  TransferResults(src, src2, dst, dst2, i)
<1> Len(Take(src, i)) = i BY TakeDropFacts
<1>1. src2 \in MESSAGE /\ Len(src2) = Len(src) - i BY TakeDropFacts
<1>2. dst2 \in MESSAGE /\ Len(dst2) = Len(dst) + i BY TakeDropFacts, ConcatFacts
<1>3. dst2 \o src2 = dst \o src
      <2> dst2 \o src2 = dst \o Take(src, i) \o Drop(src, i) OBVIOUS
      <2> QED BY TakeDropFacts
<1> QED BY <1>1, <1>2, <1>3 DEF TransferResults

LEMMA SenderWritePreservesI ==
  I /\ SenderWrite => I'
<1> SUFFICES ASSUME I, SenderWrite
             PROVE  I'
  OBVIOUS
<1> IntegrityI BY DEF I
<1> TypeOK BY DEF IntegrityI
<1> PCOK BY DEF IntegrityI
<1>1. CASE sender_ready
      <2> USE <1>1 DEF sender_ready
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> PCOK' BY DEF PCOK
      <2> TypeOK' BY FiniteMessageFacts, ConcatFacts, LengthFacts DEF TypeOK, MSG
      <2> IntegrityI' BY DEF TypeOK, PCOK, IntegrityI, MSG
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>2. CASE sender_write
      <2> USE <1>2 DEF sender_write
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[SenderWriteID] = "sender_request_notify" BY DEF PCOK
      <2> free' \in 0..BufferSize BY FiniteMessageFacts, BufferSizeType DEF TypeOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>3. CASE sender_request_notify
      <2> USE <1>3 DEF sender_request_notify
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> CASE free >= Len(msg)
          <3> pc'[SenderWriteID] = "sender_write_data" BY DEF PCOK
          <3> ~ (free < Len(msg)) BY DEF TypeOK
          <3> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
          <3> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
      <2> CASE free < Len(msg)
          <3> pc'[SenderWriteID] = "sender_recheck_len" BY DEF PCOK, TypeOK
          <3> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
          <3> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
      <2> QED BY DEF TypeOK
<1>4. CASE sender_recheck_len
      <2> USE <1>4 DEF sender_recheck_len
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[SenderWriteID] = "sender_write_data" BY DEF PCOK
      <2> free' \in 0..BufferSize BY LengthFacts
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY LengthFacts DEF IntegrityI
      <2> ASSUME free' < Len(msg) /\ SenderLive
          PROVE  \/ NotifyRead
                 \/ SpaceAvailableInt
                 \/ pc[ReceiverReadID] = "recv_notify_read"
          \* If we're going to block, show we set NotifyRead correctly.
          <3> CASE free < Len(msg)
              \* We already set the flag because we previously saw there wasn't enough space.
              BY DEF NotifyFlagsCorrect, I
          <3> CASE free >= Len(msg)
              \* There was enough space, but now there isn't. Can't happen.
              <4> BufferSize - Len(Buffer) >= free BY DEF IntegrityI
              <4> QED BY free' >= free, free' >= Len(msg)
          <3> QED BY DEF TypeOK
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> Len(Buffer) + free' = BufferSize BY LengthFacts, BufferSizeType DEF TypeOK
      <2> SenderInfoAccurate' BY LengthFacts DEF SenderInfoAccurate
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>5a. CASE sender_write_data /\ free > 0
      <2> USE <1>5a DEF sender_write_data
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[SenderWriteID] = "sender_check_notify_data" BY DEF PCOK
      <2> DEFINE len == Min(Len(msg), free)
      <2> /\ Buffer' \in FINITE_MESSAGE(BufferSize)
          /\ msg' \in FINITE_MESSAGE(MaxWriteLen)
          /\ Len(Buffer') = Len(Buffer) + len
          /\ len = Len(msg) <=> Len(msg') = 0
          /\ Len(Buffer') > 0
          /\ Len(Buffer') <= BufferSize
          /\ Len(Buffer') \in Nat
          /\ Sent = Got \o Buffer' \o msg'
            <3> len <= Len(msg) BY FiniteMessageFacts DEF Min, TypeOK
            <3> Len(msg) > 0 BY DEF IntegrityI, TypeOK
            <3> len \in Nat BY DEF Min, TypeOK
            <3> len > 0 BY DEF Min
            <3> len \in 1..Len(msg) BY DEF TypeOK
            <3> Buffer' = Buffer \o Take(msg, len) OBVIOUS
            <3> msg' = Drop(msg, len) OBVIOUS
            <3> len <= free BY DEF Min, TypeOK
            <3> HIDE DEF len
            <3> TransferResults(msg, msg', Buffer, Buffer', len)
                BY TransferFacts, FiniteMessageFacts DEF TypeOK
            <3> USE DEF TransferResults
            <3> Len(Buffer') <= BufferSize
                <4> free <= BufferSize - Len(Buffer) BY LengthFacts DEF IntegrityI
                <4> len <= BufferSize - Len(Buffer) BY BufferSizeType DEF TypeOK
                <4> Len(Buffer') = Len(Buffer) + len OBVIOUS
                <4> Len(Buffer') <= Len(Buffer) + (BufferSize - Len(Buffer)) BY BufferSizeType
                <4> Len(Buffer') \in Nat BY LengthFacts
                <4> Len(Buffer') <= BufferSize BY BufferSizeType
                <4> QED BY TakeDropFacts, LengthFacts
            <3> Sent = Got \o Buffer \o msg BY DEF IntegrityI
            <3> Len(msg') <= MaxWriteLen BY LengthFacts, FiniteMessageFacts
            <3> len = Len(msg) <=> Len(msg') = 0 OBVIOUS
            <3> Len(Buffer') <= BufferSize BY BufferSizeType
            <3> QED BY FiniteMessageFacts
      <2> TypeOK' BY free' = 0, BufferSizeType DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI'
        <3> DEFINE lb1 == Len(Buffer)
        <3> DEFINE lb2 == Len(Buffer')
        <3> lb1 \in 0..BufferSize BY LengthFacts
        <3> lb2 \in 0..BufferSize OBVIOUS
        <3> have <= lb2
            <4> have <= lb1 BY DEF IntegrityI, TypeOK
            <4> len \in Nat BY DEF Min, TypeOK
            <4> have \in Nat BY DEF TypeOK
            <4> SUFFICES have <= lb2 OBVIOUS
            <4> lb2 = lb1 + len OBVIOUS
            <4> len >= 0 BY DEF Min, TypeOK
            <4> HIDE DEF lb1, lb2, len
            <4> SUFFICES lb2 >= lb1 OBVIOUS
            <4> QED OBVIOUS
        <3> free' <= BufferSize - lb2
            <4> SUFFICES 0 <= BufferSize - lb2 OBVIOUS
            <4> HIDE DEF lb1, lb2
            <4> QED BY BufferSizeType
        <3> QED
          BY DEF IntegrityI
      <2> ASSUME Len(msg') > 0 /\ SenderLive
          PROVE  \/ NotifyRead
                 \/ SpaceAvailableInt
                 \/ pc[ReceiverReadID] = "recv_notify_read"
          \* We didn't transmit the whole message, so we're going to block.
          \* Show that we already knew this and set the flags correctly.
          <3> len < Len(msg) BY DEF Min, TypeOK
          <3> len = free BY DEF Min
          <3> free < Len(msg) OBVIOUS
          <3> QED BY DEF NotifyFlagsCorrect, I
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> ASSUME NotifyRead
          PROVE  \/ SenderInfoAccurate'
                 \/ pc[ReceiverReadID] \in {"recv_check_notify_read"}
          \* If NotifyRead was set, then our information is still accurate.
          <3> \/ SpaceAvailableInt
              \/ free >= Len(msg)
              \/ Len(Buffer) + free = BufferSize
              \/ pc[ReceiverReadID] \in {"recv_check_notify_read"}
              BY DEF SenderInfoAccurate, I
          <3> CASE Len(Buffer) = BufferSize
              \* Our information was previously accurate because the buffer was full,
              \* yet we still wrote something. This can't happen.
              <4> free <= BufferSize - Len(Buffer) BY DEF IntegrityI
              <4> free <= 0 BY BufferSizeType
              <4> QED BY LengthFacts, free = 0
          <3> CASE free >= Len(msg)
              \* If we knew we had enough space then we wrote the whole message
              \* and don't need to block.
              <4> len = Len(msg) BY DEF Min, TypeOK
              <4> Len(msg') = 0 OBVIOUS
              <4> QED BY DEF SenderInfoAccurate
          <3> CASE /\ Len(Buffer) + free = BufferSize
                   /\ free < Len(msg)
              \* There really wasn't enough space for the whole message.
              \* The buffer is now full, and we are correct to block.
              <4> len = free BY DEF Min, TypeOK
              <4> Len(Buffer') = BufferSize OBVIOUS
              <4> free' = 0 OBVIOUS
              <4> QED BY DEF SenderInfoAccurate
          <3> QED BY DEF SenderInfoAccurate, TypeOK
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>5b. CASE sender_write_data /\ free = 0
      <2> USE <1>5b DEF sender_write_data
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[SenderWriteID] = "sender_blocked" BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> free < Len(msg) BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>6. CASE sender_check_notify_data
      <2> USE <1>6 DEF sender_check_notify_data
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>7. CASE sender_notify_data
      <2> USE <1>7 DEF sender_notify_data
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>8. CASE sender_blocked
      <2> USE <1>8 DEF sender_blocked
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>9. CASE sender_check_recv_live
      <2> USE <1>9 DEF sender_check_recv_live
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5a, <1>5b, <1>6, <1>7, <1>8, <1>9 DEF SenderWrite, TypeOK

LEMMA SenderClosePreservesI ==
  I /\ SenderClose => I'
<1> SUFFICES ASSUME I,
                    SenderClose
             PROVE  I'
  OBVIOUS
<1> IntegrityI BY DEF I
<1> TypeOK BY DEF IntegrityI
<1> PCOK BY DEF IntegrityI
<1>1. CASE sender_open
      <2> USE <1>1 DEF sender_open
      <2> UNCHANGED << pc[SenderWriteID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[SenderCloseID] = "sender_notify_closed" BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>2. CASE sender_notify_closed
      <2> USE <1>2 DEF sender_notify_closed
      <2> UNCHANGED << pc[SenderWriteID], pc[ReceiverReadID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[SenderCloseID] = "Done" BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>3. QED
  BY <1>1, <1>2 DEF SenderClose

LEMMA ReceiverReadPreservesI ==
  I /\ ReceiverRead => I'
<1> SUFFICES ASSUME I, ReceiverRead
             PROVE  I'
  OBVIOUS
<1> IntegrityI BY DEF I
<1> TypeOK BY DEF IntegrityI
<1> PCOK BY DEF IntegrityI
<1>0. CASE recv_init
      <2> USE <1>0 DEF recv_init
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>1. CASE recv_ready
      <2> USE <1>1 DEF recv_ready
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>2. CASE recv_reading
      <2> USE <1>2 DEF recv_reading
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[ReceiverReadID] = "recv_got_len" BY DEF PCOK
      <2> TypeOK'
          <3> have' \in 0..BufferSize BY LengthFacts, BufferSizeType
          <3> QED BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>3. CASE recv_got_len
      <2> USE <1>3 DEF recv_got_len
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> ASSUME NotifyWrite'
          PROVE  \/ ReaderInfoAccurate'
                 \/ pc[SenderWriteID] \in {"sender_check_notify_data"}
          BY DEF I, ReaderInfoAccurate, TypeOK
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>4. CASE recv_recheck_len
      <2> USE <1>4 DEF recv_recheck_len
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[ReceiverReadID] = "recv_read_data" BY DEF PCOK
      <2> have' \in 0..BufferSize BY LengthFacts, have' >= 0 DEF Min
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> have' = 0 => have = 0 BY DEF IntegrityI, TypeOK
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> IntegrityI' BY LengthFacts DEF IntegrityI, Min
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>5a. CASE recv_read_data /\ have > 0
      <2> USE <1>5a DEF recv_read_data
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[ReceiverReadID] = "recv_check_notify_read" BY DEF PCOK
      <2> /\ TypeOK'
          /\ UNCHANGED (Got \o Buffer)
          /\ Len(Buffer') < Len(Buffer)
          <3> PICK len \in 1..have :
                  /\ Got' = Got \o Take(Buffer, len)
                  /\ Buffer' = Drop(Buffer, len)
              OBVIOUS
          <3> len \in 1..Len(Buffer) BY DEF IntegrityI, TypeOK
          <3> TransferResults(Buffer, Buffer', Got, Got', len)
              <4> Got' = Got \o Take(Buffer, len) OBVIOUS
              <4> Buffer' = Drop(Buffer, len) OBVIOUS
              <4> QED BY TransferFacts, FiniteMessageFacts DEF TypeOK
          <3> DEFINE lb1 == Len(Buffer)
          <3> DEFINE lb2 == Len(Buffer')
          <3> lb2 = lb1 - len BY DEF TransferResults
          <3> lb1 \in Nat /\ lb2 \in Nat BY DEF TypeOK
          <3> SUFFICES lb2 < lb1
              BY LengthFacts, FiniteMessageFacts DEF TypeOK, TransferResults
          <3> HIDE DEF lb1, lb2
          <3> QED OBVIOUS
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI'
        <3> free <= BufferSize - Len(Buffer') BY BufferSizeType DEF TypeOK, IntegrityI
        <3> QED BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>5b. CASE recv_read_data /\ have = 0
      <2> USE <1>5b DEF recv_read_data
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>6. CASE recv_check_notify_read
      <2> USE <1>6 DEF recv_check_notify_read
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>7. CASE recv_notify_read
      <2> USE <1>7 DEF recv_notify_read
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> pc'[ReceiverReadID] = "recv_ready" BY DEF PCOK
      <2> TypeOK' BY DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>8. CASE recv_await_data
      <2> USE <1>8 DEF recv_await_data
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY MaxReadLenType DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>9. CASE recv_final_check
      <2> USE <1>9 DEF recv_final_check
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >> BY DEF PCOK
      <2> TypeOK' BY MaxReadLenType DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1> QED BY <1>0, <1>1, <1>2, <1>3, <1>4, <1>5a, <1>5b, <1>6, <1>7, <1>8, <1>9 DEF ReceiverRead, TypeOK

LEMMA ReceiverClosePreservesI ==
  I /\ ReceiverClose => I'
<1> SUFFICES ASSUME I,
                    ReceiverClose
             PROVE  I'
  OBVIOUS
<1> IntegrityI BY DEF I
<1> TypeOK BY DEF IntegrityI
<1> PCOK BY DEF IntegrityI
<1>1. CASE recv_open
      <2> USE <1>1 DEF recv_open
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverReadID] >> BY DEF PCOK
      <2> pc'[ReceiverCloseID] = "recv_notify_closed" BY DEF PCOK
      <2> TypeOK' BY MaxReadLenType DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>2. CASE recv_notify_closed
      <2> USE <1>2 DEF recv_notify_closed
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverReadID] >> BY DEF PCOK
      <2> pc'[ReceiverCloseID] = "Done" BY DEF PCOK
      <2> TypeOK' BY MaxReadLenType DEF TypeOK
      <2> PCOK' BY DEF PCOK
      <2> IntegrityI' BY DEF IntegrityI
      <2> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>3. QED
  BY <1>1, <1>2 DEF ReceiverClose

LEMMA SpuriousPreservesI ==
  ASSUME I, SpuriousInterrupts
  PROVE  I'
<1> spurious BY DEF SpuriousInterrupts
<1> USE DEF spurious
<1> IntegrityI BY DEF I
<1> TypeOK BY DEF IntegrityI
<1> PCOK BY DEF IntegrityI
<1> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >>
    BY DEF PCOK
<1> TypeOK' BY DEF TypeOK
<1> PCOK' BY DEF PCOK
<1> IntegrityI' BY DEF IntegrityI
<1> NotifyFlagsCorrect' BY DEF NotifyFlagsCorrect, I
<1> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK

LEMMA NextPreservesI ==
  I /\ [Next]_vars => I'
<1>1. CASE UNCHANGED vars
      <2> USE <1>1 DEF vars
      <2> UNCHANGED IntegrityI BY DEF IntegrityI, PCOK, TypeOK
      <2> UNCHANGED NotifyFlagsCorrect BY DEF NotifyFlagsCorrect
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>2. CASE Next
      <2>1. CASE SenderWrite BY <2>1, SenderWritePreservesI
      <2>2. CASE SenderClose BY <2>2, SenderClosePreservesI
      <2>3. CASE ReceiverRead BY <2>3, ReceiverReadPreservesI
      <2>4. CASE ReceiverClose BY <2>4, ReceiverClosePreservesI
      <2>5. CASE SpuriousInterrupts BY <2>5, SpuriousPreservesI
      <2>6. CASE (\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars
            BY <2>6, <1>1
      <2>7. QED
        BY <1>2, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Next
<1>3. QED
      BY <1>1, <1>2

THEOREM AlwaysI ==
  Init /\ [][Next]_vars => []I
<1>1. ASSUME Init
      PROVE  I
      <2> USE <1>1 DEF Init, ProcSet
      <2> Buffer \in FINITE_MESSAGE(BufferSize) BY BufferSizeType DEF FINITE_MESSAGE, MESSAGE
      <2> msg \in FINITE_MESSAGE(MaxWriteLen) BY MaxWriteLenType DEF FINITE_MESSAGE, MESSAGE
      <2> TypeOK BY BufferSizeType, MaxReadLenType DEF TypeOK, MESSAGE
      <2> PCOK BY DEF PCOK
      <2> IntegrityI BY LengthFacts DEF IntegrityI, TypeOK
      <2> NotifyFlagsCorrect BY DEF NotifyFlagsCorrect
      <2> QED BY DEF I, SenderInfoAccurate, ReaderInfoAccurate, CloseOK
<1>2. I /\ [][Next]_vars => []I
      BY NextPreservesI, PTL
<1>3. QED
      BY <1>1, <1>2

(* Finally: I really is an invariant of Spec.
   And therefore so is Integrity, via IntegrityIUseful. *)
THEOREM Spec => []I
BY AlwaysI DEF Spec

-----------------------------------------------------------------------------
\* Deadlock

(* We can't get into a state where the sender and receiver are both blocked
   and there is no wakeup pending: *)
THEOREM DeadlockFree1 ==
  ASSUME I
  PROVE  ~ /\ pc[SenderWriteID] = "sender_blocked"
           /\ ~SpaceAvailableInt /\ SenderLive
           /\ pc[ReceiverReadID] = "recv_await_data"
           /\ ~DataReadyInt /\ ReceiverLive
<1> SUFFICES ASSUME /\ pc[SenderWriteID] = "sender_blocked"
                    /\ ~SpaceAvailableInt /\ SenderLive
                    /\ pc[ReceiverReadID] = "recv_await_data"
                    /\ ~DataReadyInt /\ ReceiverLive
             PROVE  FALSE
    OBVIOUS
<1> NotifyFlagsCorrect BY DEF I
<1> CASE ~NotifyRead BY DEF NotifyFlagsCorrect
<1> CASE ~NotifyWrite
    <2> have /= 0 BY DEF NotifyFlagsCorrect
    <2> QED BY DEF IntegrityI, I
<1> CASE NotifyRead /\ NotifyWrite
    <2> SenderInfoAccurate /\ ReaderInfoAccurate BY DEF I
    <2> free = 0 BY DEF IntegrityI, I
    <2> Len(Buffer) = BufferSize BY DEF SenderInfoAccurate
    <2> Len(Buffer) = 0 BY DEF ReaderInfoAccurate
    <2> QED BY BufferSizeType
<1> QED OBVIOUS

(* We can't get into a state where the sender is idle and the receiver is blocked
   unless the buffer is empty (all data sent has been consumed): *)
THEOREM DeadlockFree2 ==
  ASSUME I, pc[SenderWriteID] = "sender_ready", SenderLive,
         pc[ReceiverReadID] = "recv_await_data", ReceiverLive,
         ~DataReadyInt
  PROVE  Len(Buffer) = 0
<1> NotifyFlagsCorrect BY DEF I
<1> CASE ~NotifyWrite
    <2> have /= 0 BY DEF NotifyFlagsCorrect
    <2> QED BY DEF I, IntegrityI
<1> CASE NotifyWrite
    <2> ReaderInfoAccurate BY DEF I
    <2> Len(Buffer) = 0 BY DEF ReaderInfoAccurate
    <2> QED OBVIOUS
<1> QED OBVIOUS

(* TLAPS currently can't prove liveness facts.
   However, if we don't end up forever in a behaviour with both processes blocked,
   then some process must keep getting signalled. We only send signals after making
   progress, so lack of deadlock implies progress. *)

-----------------------------------------------------------------------------

\* ReadLimit

(* The number of bytes that the receiver will eventually get without further action
   from the sender (assuming the receiver doesn't decide to close the connection). *)
ReadLimit ==
  LET PC == pc[ReceiverReadID] IN
  CASE PC \in {"recv_ready", "recv_reading", "recv_got_len", "recv_recheck_len",
               "recv_check_notify_read", "recv_notify_read", "recv_final_check"} ->
              Len(Got) + Len(Buffer)       \* Will check again
              \* (for recv_final_check we might also exit if Len(Buffer) = 0,
              \* but then this is equal to Len(Got), so still correct)
    [] PC \in {"recv_read_data"} ->
              IF have > 0 \/ DataReadyInt \/ ~SenderLive
              THEN Len(Got) + Len(Buffer)  \* Will read and check again
              ELSE Len(Got)                \* Will read nothing and block
    [] PC \in {"recv_await_data"} ->
              IF DataReadyInt
              THEN Len(Got) + Len(Buffer)  \* Will check again
              ELSE Len(Got)                \* Will continue blocking
    [] PC \in {"recv_init"} ->
              IF DataReadyInt \/ ~ReceiverBlocksFirst
              THEN Len(Got) + Len(Buffer)  \* Will check again
              ELSE Len(Got)                \* Will block
    [] PC \in {"Done"} ->
              Len(Got)

(* If ReadLimit says we will read some amount of data, then we will (unless
   we decide to close the connection).
   This should be checked without weak fairness (so just Init /\ [][Next]_vars). *)
ReadLimitCorrect ==
  /\ WF_vars(ReceiverRead) =>
      \A i \in AvailabilityNat :
        ReadLimit = i ~> Len(Got) >= i \/ ~ReceiverLive
  \* ReadLimit can only decrease if we decide to shut down:
  /\ [][ReadLimit' >= ReadLimit \/ ~ReceiverLive]_vars
  \* ReceiverRead steps don't change the read limit:
  /\ [][ReceiverRead => UNCHANGED ReadLimit \/ ~ReceiverLive]_vars

(* Whenever the sender is blocked or idle, the receiver can read everything in
   the buffer without further action from any other process. *)
THEOREM ReadAllIfSenderBlocked ==
  ASSUME I, SenderLive, ReceiverLive, ~SpaceAvailableInt,
         pc[SenderWriteID] \in {"sender_ready", "sender_blocked"}
  PROVE  ReadLimit = Len(Got) + Len(Buffer)
<1> IntegrityI BY DEF I
<1> PCOK BY DEF IntegrityI
<1> TypeOK BY DEF IntegrityI
<1> CloseOK BY DEF I
<1> NotifyFlagsCorrect BY DEF I
<1> CASE pc[ReceiverReadID] \in  {"recv_ready", "recv_reading", "recv_got_len",
            "recv_recheck_len", "recv_check_notify_read",
            "recv_notify_read", "recv_final_check"} BY DEF ReadLimit
<1> CASE pc[ReceiverReadID] \in {"recv_read_data"}
    <3> CASE have > 0 \/ DataReadyInt \/ ~SenderLive BY DEF ReadLimit
    <3> CASE have = 0 /\ ~DataReadyInt /\ SenderLive
        <4> ReadLimit = Len(Got) BY DEF ReadLimit
        <4> SUFFICES Len(Buffer) = 0 OBVIOUS
        <4> \/ NotifyWrite
            \/ DataReadyInt
            \/ pc[SenderWriteID] = "sender_notify_data"
            BY DEF NotifyFlagsCorrect
        <4> CASE NotifyWrite /\ Len(Buffer) > 0
            BY have > 0 DEF ReaderInfoAccurate, I
        <4> QED OBVIOUS
    <3> QED BY DEF TypeOK
<1> CASE pc[ReceiverReadID] \in {"recv_init", "recv_await_data"}
    <2> CASE DataReadyInt BY DEF ReadLimit
    <2> CASE ~DataReadyInt
        <3> have = 0 BY DEF IntegrityI
        <3> NotifyWrite BY DEF NotifyFlagsCorrect
        <3> ReaderInfoAccurate BY DEF I
        <3> Len(Buffer) = 0 BY DEF ReaderInfoAccurate
        <3> QED BY DEF ReadLimit
    <2> QED OBVIOUS
<1> CASE pc[ReceiverReadID] \in {"Done"} BY DEF CloseOK
<1> QED BY DEF PCOK

(* ReceiverRead steps don't change ReadLimit, as long as the receiver hasn't closed
   the connection. Therefore ReadLimit is correct:
   - When the receiver is blocked it cannot read any more than it has without help.
   - ReadLimit is Len(Got) then, so ReadLimit is obviously correct in this case.
   - Since read steps preserve ReadLimit, this shows that ReadLimit is correct
     in all cases.
   e.g. if ReadLimit = 5 and no other processes do anything, then we will end
   up in a state with the receiver blocked, and ReadLimit = Len(Got) = 5 and so
   we really did read a total of 5 bytes. *)
THEOREM ReceiverReadPreservesReadLimit ==
  ASSUME I, ReceiverLive, ReceiverRead
  PROVE  UNCHANGED ReadLimit
<1> IntegrityI BY DEF I
<1> PCOK BY DEF IntegrityI
<1> TypeOK BY DEF IntegrityI
<1> CloseOK BY DEF I
<1> NotifyFlagsCorrect BY DEF I
<1> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >>
    BY DEF ReceiverRead, recv_init, recv_ready, recv_reading, recv_got_len,
            recv_recheck_len, recv_read_data,
            recv_check_notify_read, recv_notify_read,
            recv_await_data, recv_final_check, PCOK
<1>1. CASE recv_read_data
      <2> USE <1>1
      <2> USE DEF recv_read_data
      <2> CASE have > 0
          <3> PICK len \in 1..have :
                  /\ Got' = Got \o Take(Buffer, len)
                  /\ Buffer' = Drop(Buffer, len)
              OBVIOUS
          <3> len \in 1..Len(Buffer) BY DEF TypeOK, IntegrityI
          <3> Buffer \in MESSAGE BY FiniteMessageFacts DEF TypeOK
          <3> Take(Buffer, len) \o Drop(Buffer, len) = Buffer
              BY TakeDropFacts
          <3> UNCHANGED (Got \o Buffer) BY DEF TypeOK
          <3> QED BY DEF ReadLimit
      <2> CASE have = 0 BY DEF recv_read_data, TypeOK, ReadLimit
      <2> QED BY DEF TypeOK
<1>2. CASE ~recv_read_data
    <2> USE <1>2
    <2> UNCHANGED << Got, Buffer >>
        BY DEF ReceiverRead, recv_init, recv_ready, recv_reading, recv_got_len,
            recv_recheck_len, recv_read_data,
            recv_check_notify_read, recv_notify_read,
            recv_await_data, recv_final_check
    <2>1. CASE recv_final_check BY <2>1 DEF recv_final_check, TypeOK, ReadLimit
    <2>2. CASE recv_reading \/ recv_check_notify_read \/ recv_notify_read
          <4> USE <2>2
          <4> USE DEF ReadLimit, recv_ready, recv_reading,
                  recv_recheck_len, recv_read_data,
                  recv_check_notify_read, recv_notify_read,
                  recv_await_data, recv_final_check
          <4> pc'[ReceiverReadID] \in {"recv_ready", "recv_reading", "recv_got_len",
                     "recv_recheck_len", "recv_check_notify_read",
                     "recv_await_data", "recv_notify_read", "recv_final_check"} BY DEF PCOK
          <4> QED BY DEF ReadLimit
    <2>3. CASE recv_await_data
          BY <2>3 DEF recv_await_data, ReadLimit
    <2>4. CASE recv_ready BY <2>4 DEF recv_ready, ReadLimit
    <2>5. CASE recv_recheck_len
          <4> USE <2>5 DEF recv_recheck_len
          <4> ReadLimit = Len(Got) + Len(Buffer) BY DEF ReadLimit
          <4> pc'[ReceiverReadID] = "recv_read_data" BY DEF PCOK
          <4> CASE have' > 0 \/ DataReadyInt
                <5> ReadLimit' = Len(Got) + Len(Buffer) BY DEF ReadLimit
                <5> QED OBVIOUS
          <4> CASE have' = 0 /\ ~DataReadyInt
                <5> ReadLimit' = Len(Got) BY DEF ReadLimit
                <5> Len(Buffer) = 0 BY LengthFacts
                <5> QED OBVIOUS
          <4> QED BY have' >= 0 DEF TypeOK
    <2>6. CASE recv_got_len
          <3> USE <2>6 DEF recv_got_len
          <3> ReadLimit = Len(Got) + Len(Buffer) BY DEF ReadLimit
          <3> CASE pc'[ReceiverReadID] = "recv_read_data"
              <4> have > 0 BY DEF TypeOK
              <4> QED BY DEF ReadLimit
          <3> CASE pc'[ReceiverReadID] = "recv_recheck_len"
              <4> QED BY DEF ReadLimit
          <3> QED BY DEF TypeOK, PCOK
    <2>7. CASE recv_init BY <2>7 DEF recv_init, ReadLimit, PCOK
    <2> QED BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7 DEF ReceiverRead
<1> QED BY <1>1, <1>2 DEF SenderWrite

(* ReadLimit never decreases (unless the receiver decides to close the connection). *)
THEOREM ReadLimitMonotonic ==
  ASSUME I, Next, ReceiverLive
  PROVE  ReadLimit' >= ReadLimit
<1> IntegrityI BY DEF I
<1> TypeOK BY DEF IntegrityI
<1> PCOK BY DEF IntegrityI
<1> TypeOK' BY NextPreservesI, I', IntegrityI' DEF I, IntegrityI
<1> SUFFICES ReadLimit' >= ReadLimit \/ UNCHANGED ReadLimit
    BY DEF ReadLimit, TypeOK
<1>1. CASE SenderWrite
      <2> USE <1>1
      <2> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >>
          BY DEF SenderWrite, sender_ready, sender_write, sender_request_notify,
                    sender_recheck_len, sender_write_data,
                    sender_check_notify_data, sender_notify_data,
                    sender_blocked, sender_check_recv_live, PCOK
      <2> CASE sender_write_data BY DEF sender_write_data, TypeOK, ReadLimit
      <2> CASE ~sender_write_data
            <3> UNCHANGED << Got, Buffer >>
                BY DEF SenderWrite, sender_ready, sender_write,
                        sender_request_notify, sender_recheck_len,
                        sender_check_notify_data, sender_notify_data,
                        sender_blocked, sender_check_recv_live
            <3> QED BY DEF ReadLimit
      <2> QED BY DEF SenderWrite
<1>2. CASE SenderClose
      <2> USE <1>2
      <2> UNCHANGED << pc[SenderWriteID], pc[ReceiverReadID], pc[ReceiverCloseID] >>
            BY DEF SenderClose, sender_open, sender_notify_closed, PCOK
      <2> UNCHANGED << Got, Buffer >>
          BY DEF SenderClose, sender_open, sender_notify_closed
      <2> QED BY UNCHANGED ReadLimit DEF ReadLimit
<1>3. CASE ReceiverRead BY <1>3, ReceiverReadPreservesReadLimit
<1>4. CASE ReceiverClose
    <2> USE <1>4
    <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverReadID] >>
        BY DEF ReceiverClose, recv_open, recv_notify_closed, PCOK
    <2> UNCHANGED << Got, Buffer >>
        BY DEF ReceiverClose, recv_open, recv_notify_closed, PCOK
    <2> QED BY UNCHANGED ReadLimit DEF ReadLimit
<1>5. CASE SpuriousInterrupts
    <2> USE <1>5 DEF spurious
    <2> spurious BY DEF SpuriousInterrupts
    <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverReadID] >> BY DEF PCOK
    <2> UNCHANGED << Got, Buffer >> OBVIOUS
    <2> CASE DataReadyInt' = FALSE BY UNCHANGED ReadLimit DEF ReadLimit
    <2> CASE DataReadyInt' = TRUE
        <3> CASE pc[ReceiverReadID] \in {"recv_init", "recv_ready", "recv_reading", "recv_got_len",
                  "recv_recheck_len", "recv_read_data", "recv_final_check",
                  "recv_await_data", "recv_check_notify_read",
                  "recv_notify_read", "Done"}
            BY LengthFacts DEF ReadLimit, PCOK, TypeOK
        <3> QED BY DEF PCOK
    <2> QED OBVIOUS
<1>6. CASE UNCHANGED vars BY <1>6 DEF ReadLimit, vars
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

-----------------------------------------------------------------------------

\* WriteLimit

(* The number of bytes that the sender will eventually send without further action
   from the other processes or the client application, assuming the connection isn't
   closed by either end. *)
WriteLimit ==
  LET PC == pc[SenderWriteID] IN
  LET current == Len(Got) + Len(Buffer) IN
  IF SenderInfoAccurate THEN Len(Got) + Min(BufferSize, Len(Buffer) + Len(msg))
  ELSE
    CASE PC \in {"sender_write_data"} ->
                current + free  \* Will write and block
      [] PC \in {"sender_check_notify_data", "sender_notify_data", "sender_blocked"} ->
                current         \* Will block

(* If WriteLimit says we will send some amount of data then we will eventually send
   at least that much data (or close the connection).
   This should be checked without weak fairness (so just I /\ [][Next]_vars). *)
WriteLimitCorrect ==
  /\ WF_vars(SenderWrite) =>
      \A i \in AvailabilityNat :
        WriteLimit = i ~> Len(Got) + Len(Buffer) >= i \/ ~SenderLive \/ ~ReceiverLive
  \* WriteLimit can only decrease if we decide to shut down:
  /\ [][WriteLimit' >= WriteLimit \/ pc'[SenderWriteID] = "Done"]_vars
  \* SenderWrite steps don't change the write limit, except at sender_ready
  \* when the application decides to send more data:
  /\ [][SenderWrite => \/ UNCHANGED WriteLimit
                       \/ pc[SenderWriteID] \in {"sender_ready"}
                       \/ pc'[SenderWriteID] \in {"Done"}]_vars

(* Whenever the receiver is blocked, the sender will fill the buffer (or write everything
   it wants to write) without further action from any other process. *)
THEOREM WriteAllIfReceiverBlocked ==
  ASSUME I, SenderLive, ReceiverLive,
         pc[ReceiverReadID] = "recv_await_data", ~DataReadyInt
  PROVE  WriteLimit = Len(Got) + Min(BufferSize, Len(Buffer) + Len(msg))
<1> IntegrityI BY DEF I
<1> PCOK BY DEF IntegrityI
<1> TypeOK BY DEF IntegrityI
<1> CloseOK BY DEF I
<1> NotifyFlagsCorrect BY DEF I
<1> pc[SenderWriteID] \in {"sender_ready", "sender_write", "sender_request_notify",
                           "sender_recheck_len", "sender_write_data", "sender_blocked",
                           "sender_check_notify_data", "sender_notify_data",
                           "sender_check_recv_live", "Done"}
    BY DEF PCOK
<1> CASE SpaceAvailableInt BY DEF SenderInfoAccurate, WriteLimit, CloseOK, PCOK
<1> CASE NotifyRead /\ ~SpaceAvailableInt
    <3> SenderInfoAccurate BY DEF I
    <3> QED BY DEF WriteLimit
<1> CASE ~NotifyRead /\ ~SpaceAvailableInt
    <3> /\ pc[SenderWriteID] \in {"sender_recheck_len", "sender_write_data"}
           => free >= Len(msg)
        /\ pc[SenderWriteID] \in {"sender_check_notify_data", "sender_notify_data"}
           => Len(msg) <= 0
        /\ pc[SenderWriteID] \notin {"sender_blocked"}
        BY DEF NotifyFlagsCorrect, TypeOK
    <3> CASE pc[SenderWriteID] \in {"sender_write_data"} /\ free >= Len(msg)
        BY DEF SenderInfoAccurate, WriteLimit
    <3> CASE pc[SenderWriteID] \in {"sender_recheck_len", "sender_check_notify_data",
                                    "sender_notify_data"}
        BY DEF SenderInfoAccurate, WriteLimit
    <3> CASE pc[SenderWriteID] \in {"sender_blocked"} BY DEF I
    <3> CASE pc[SenderWriteID] \in {"Done"} BY DEF CloseOK
    <3> QED BY DEF SenderInfoAccurate, WriteLimit
<1> QED OBVIOUS

(* Sender steps preserve WriteLimit (except for sender_ready, where the application
   decides to send more data). *)
THEOREM SenderWritePreservesWriteLimit ==
  ASSUME I, SenderLive, ReceiverLive, SenderWrite, ~sender_ready
  PROVE  UNCHANGED WriteLimit
<1> IntegrityI BY DEF I
<1> PCOK BY DEF IntegrityI
<1> TypeOK BY DEF IntegrityI
<1> CloseOK BY DEF I
<1> NotifyFlagsCorrect BY DEF I
<1> TypeOK' BY NextPreservesI, I', IntegrityI' DEF I, IntegrityI, Next
<1> UNCHANGED << pc[SenderCloseID], pc[ReceiverReadID], pc[ReceiverCloseID] >>
    BY DEF SenderWrite, sender_ready, sender_write, sender_request_notify,
              sender_recheck_len, sender_write_data,
              sender_check_notify_data, sender_notify_data,
              sender_blocked, sender_check_recv_live, PCOK
<1>1. CASE sender_ready BY <1>1
<1>2. CASE \/ sender_write \/ sender_request_notify
           \/ sender_check_notify_data \/ sender_notify_data
           \/ sender_blocked \/ sender_check_recv_live
      <3> USE <1>2 DEF sender_write, sender_request_notify,
                       sender_check_notify_data, sender_notify_data,
                       sender_blocked, sender_check_recv_live
      <3> UNCHANGED << Got, Buffer, msg >> OBVIOUS
      <3> UNCHANGED SenderInfoAccurate BY DEF SenderInfoAccurate
      <3> CASE SenderInfoAccurate BY DEF WriteLimit
      <3> CASE ~SenderInfoAccurate BY DEF WriteLimit, SenderInfoAccurate
      <3> QED OBVIOUS
<1>3. CASE sender_recheck_len
      <3> USE <1>3 DEF sender_recheck_len
      <3> UNCHANGED << Got, Buffer, msg >> OBVIOUS
      <3> pc'[SenderWriteID] = "sender_write_data" BY DEF PCOK
      <3> SenderInfoAccurate BY DEF SenderInfoAccurate
      <3> SenderInfoAccurate'
          <4> free' \in Nat BY LengthFacts
          <4> Len(Buffer) + free' = BufferSize BY LengthFacts
          <4> QED BY DEF SenderInfoAccurate
      <3> QED BY DEF WriteLimit
<1>4. CASE sender_write_data /\ free > 0
      <2> USE <1>4 DEF sender_write_data
      <2> pc'[SenderWriteID] = "sender_check_notify_data" BY DEF PCOK
      <2> DEFINE len == Min(Len(msg), free)
      <2> free <= BufferSize - Len(Buffer) BY DEF IntegrityI
      <2> Len(msg) > 0 BY DEF IntegrityI
      <2> len \in 1..Len(msg) BY len > 0 DEF TypeOK, Min
      <2> TransferResults(msg, msg', Buffer, Buffer', len)
          BY TransferFacts, FiniteMessageFacts DEF TypeOK
      <2> Len(Buffer') = Len(Buffer) + len BY DEF TransferResults
      <2> UNCHANGED (Len(Buffer) + Len(msg))
          <3> UNCHANGED Len(Buffer \o msg) BY DEF TransferResults
          <3> Buffer \in MESSAGE /\ msg \in MESSAGE BY BufferSizeType, FiniteMessageFacts DEF TypeOK
          <3> Len(Buffer \o msg) = Len(Buffer) + Len(msg) BY ConcatFacts
          <3> Buffer' \in MESSAGE /\ msg' \in MESSAGE BY DEF TransferResults
          <3> Len(Buffer' \o msg') = Len(Buffer') + Len(msg') BY ConcatFacts
          <3> QED OBVIOUS
      <2> CASE SenderInfoAccurate
          <3> SUFFICES SenderInfoAccurate' BY DEF WriteLimit
          <3> \/ SpaceAvailableInt
              \/ free >= Len(msg)
              \/ Len(Buffer) + free = BufferSize
              BY DEF SenderInfoAccurate
          <3> CASE free >= Len(msg)
              <4> len = Len(msg) BY DEF Min
              <4> Len(msg') = 0 BY DEF TransferResults
              <4> QED BY DEF SenderInfoAccurate
          <3> CASE Len(Buffer) + free = BufferSize /\ free < Len(msg)
              <4> len = free BY DEF Min, TypeOK
              <4> Len(Buffer') = BufferSize OBVIOUS
              <4> QED BY DEF SenderInfoAccurate
          <3> CASE SpaceAvailableInt
              <4> QED BY DEF SenderInfoAccurate
          <3> QED BY DEF TypeOK
      <2> CASE ~SenderInfoAccurate
          <3> free < Len(msg) BY DEF SenderInfoAccurate, TypeOK
          <3> len = free BY DEF Min, TypeOK
          <3> ~SenderInfoAccurate' BY DEF SenderInfoAccurate
          <3> SUFFICES Len(Got) + Len(Buffer) + free = Len(Got') + Len(Buffer') BY DEF WriteLimit
          <3> SUFFICES Len(Buffer) + free = Len(Buffer') BY LengthFacts DEF TypeOK
          <3> QED OBVIOUS
      <2> QED OBVIOUS
<1>4b. CASE sender_write_data /\ free = 0
       <2> USE <1>4b DEF sender_write_data
       <2> pc'[SenderWriteID] = "sender_blocked" BY DEF PCOK
       <2> UNCHANGED << Got, Buffer, msg >> OBVIOUS
       <2> CASE SenderInfoAccurate
            <3> \/ SpaceAvailableInt
                \/ free >= Len(msg)
                \/ Len(Buffer) + free = BufferSize
                BY DEF SenderInfoAccurate
            <3> SUFFICES SenderInfoAccurate' BY DEF WriteLimit
            <3> CASE free >= Len(msg) BY Len(msg) > 0 DEF IntegrityI
            <3> QED BY DEF SenderInfoAccurate
       <2> CASE ~SenderInfoAccurate
           <3> ~SenderInfoAccurate' BY DEF SenderInfoAccurate, TypeOK
           <3> QED BY DEF WriteLimit
       <2> QED OBVIOUS
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>4b DEF SenderWrite, TypeOK

(* When in the ready or blocked states, WriteLimit predicts that we will write exactly
   what we have already written, which is obviously the correct answer.
   In other states, and if no other process runs, we must eventually reach one of these
   known-correct states without performing a sender_ready step. Therefore, WriteLimit will
   not have changed (due to SenderWritePreservesWriteLimit) and it must have been correct.
   For example, if we are at sender_write and WriteLimit says we will write 6 bytes, and
   we only take SenderWrite steps, then we will end up in a state where:
   WriteLimit = 6 = Len(Got) + Len(Buffer)
   And therefore we have indeed written 6 bytes. *)
THEOREM WriteLimitCorrectWhenBlocked ==
  ASSUME I, SenderLive,
         \/ pc[SenderWriteID] = "sender_ready"
         \/ pc[SenderWriteID] = "sender_blocked" /\ ~SpaceAvailableInt
  PROVE WriteLimit = Len(Got) + Len(Buffer)
<1> TypeOK /\ PCOK /\ IntegrityI BY DEF I, IntegrityI
<1> CASE pc[SenderWriteID] = "sender_ready"
    <2> Len(msg) = 0 BY DEF IntegrityI
    <2> SenderInfoAccurate BY DEF SenderInfoAccurate
    <2> Min(BufferSize, Len(Buffer) + Len(msg)) = Len(Buffer)
        BY LengthFacts DEF Min
    <2> QED BY DEF WriteLimit
<1> CASE pc[SenderWriteID] = "sender_blocked" /\ ~SpaceAvailableInt
    <2> CASE SenderInfoAccurate
        <3> Len(Buffer) + free = BufferSize BY DEF SenderInfoAccurate
        <3> free = 0 BY DEF IntegrityI
        <3> Len(Buffer) = BufferSize OBVIOUS
        <3> WriteLimit = Len(Got) + Min(BufferSize, BufferSize + Len(msg)) BY DEF WriteLimit
        <3> QED BY LengthFacts DEF Min
    <2> CASE ~SenderInfoAccurate BY DEF WriteLimit
    <2> QED OBVIOUS
<1> QED BY DEF WriteLimit

(* The obvious fact that if WriteLimit doesn't change then it doesn't decrease. *)
LEMMA UnchangedWriteLimitGe ==
  ASSUME I, UNCHANGED WriteLimit
  PROVE WriteLimit' >= WriteLimit
<1> TypeOK /\ PCOK BY DEF IntegrityI, I
<1> pc[SenderWriteID] \in {"sender_ready", "sender_write", "sender_request_notify",
      "sender_recheck_len", "sender_write_data", "sender_blocked", "sender_check_notify_data",
      "sender_notify_data", "sender_check_recv_live", "Done"} BY DEF PCOK
<1> Len(Buffer) + Len(msg) \in Nat BY LengthFacts DEF WriteLimit, TypeOK
<1> CASE SenderInfoAccurate
    <2> Min(BufferSize, Len(Buffer) + Len(msg)) \in Nat BY LengthFacts DEF Min
    <2> Len(Got) \in Nat BY LengthFacts
    <2> WriteLimit \in Nat BY DEF WriteLimit
    <2> QED OBVIOUS
<1> CASE ~SenderInfoAccurate BY DEF WriteLimit, SenderInfoAccurate, TypeOK
<1> QED OBVIOUS

(* The difficult case for WriteLimitMonotonic is showing that when the receiver
   moves data from Buffer to Got, WriteLimit doesn't go down: *)
LEMMA RecvTransferWriteLimit ==
  ASSUME I, recv_read_data, SenderLive, have > 0
  PROVE  WriteLimit' >= WriteLimit
<1> USE DEF recv_read_data
<1> IntegrityI /\ TypeOK /\ PCOK BY DEF IntegrityI, I
<1> TypeOK' BY NextPreservesI, I', IntegrityI' DEF Next, ReceiverRead, I, IntegrityI
<1> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >>
    BY DEF recv_read_data, PCOK
<1> PICK len \in 1..have :
            /\ Got' = Got \o Take(Buffer, len)
            /\ Buffer' = Drop(Buffer, len)
    OBVIOUS
<1> len \in 1..Len(Buffer) BY DEF IntegrityI, TypeOK
<1> TransferResults(Buffer, Buffer', Got, Got', len)
    BY TransferFacts, FiniteMessageFacts DEF TypeOK
<1> UNCHANGED (Len(Got) + Len(Buffer))
    <2> UNCHANGED (Got \o Buffer) BY DEF TransferResults
    <2> QED BY ConcatFacts
<1> pc[SenderWriteID] \in {"sender_ready", "sender_write", "sender_request_notify",
      "sender_recheck_len", "sender_write_data", "sender_blocked", "sender_check_notify_data",
      "sender_notify_data", "sender_check_recv_live", "Done"} BY DEF PCOK
<1> DEFINE lg1 == Len(Got)
<1> DEFINE lb1 == Len(Buffer)
<1> DEFINE lg2 == Len(Got')
<1> DEFINE lb2 == Len(Buffer')
<1> DEFINE lm  == Len(msg)
<1> lb2 = lb1 - len BY DEF TransferResults
<1> lb2 < lb1 BY LengthFacts
<1> lg1 + lb1 = lg2 + lb2 OBVIOUS
<1> lg2 > lg1 OBVIOUS
<1> /\ lg1 \in Nat
    /\ lg2 \in Nat
    /\ lb1 \in Nat
    /\ lb2 \in Nat
    /\ lm  \in Nat
    /\ BufferSize \in Nat
    BY LengthFacts
<1> CASE SenderInfoAccurate
    <2> CASE SenderInfoAccurate'
        <3> SUFFICES lg2 + Min(BufferSize, lb2 + lm)
                     >= lg1 + Min(BufferSize, lb1 + lm) BY DEF WriteLimit
        <3> HIDE DEF lg1, lg2, lb1, lb2, lm
        <3> SUFFICES Min(lg2 + BufferSize, lg2 + lb2 + lm)
                     >= Min(lg1 + BufferSize, lg1 + lb1 + lm)
            <4> DEFINE x1 == lb1 + lm
            <4> DEFINE x2 == lb2 + lm
            <4> SUFFICES lg2 + Min(BufferSize, x2) >= lg1 + Min(BufferSize, x1) OBVIOUS
            <4> x1 \in Nat /\ x2 \in Nat OBVIOUS
            <4> lg2 + (lb2 + lm) = (lg2 + lb2) + lm OBVIOUS
            <4> lg1 + (lb1 + lm) = (lg1 + lb1) + lm OBVIOUS
            <4> Min(lg2 + BufferSize, lg2 + (lb2 + lm))
                     >= Min(lg1 + BufferSize, lg1 + (lb1 + lm)) OBVIOUS
            <4> Min(lg2 + BufferSize, lg2 + x2) >= Min(lg1 + BufferSize, lg1 + x1) OBVIOUS
            <4> HIDE DEF x1, x2
            <4> lg2 + Min(BufferSize, x2) >= lg1 + Min(BufferSize, x1)
                BY BufferSizeType DEF Min
            <4> QED OBVIOUS
        <3> SUFFICES Min(lg2 + BufferSize, (lg2 + lb2) + lm)
                     >= Min(lg1 + BufferSize, (lg1 + lb1) + lm)
            OBVIOUS
        <3> (lg2 + lb2) + lm = (lg1 + lb1) + lm OBVIOUS
        <3> SUFFICES lg2 + BufferSize >= lg1 + BufferSize BY DEF Min
        <3> QED OBVIOUS
    <2> CASE ~SenderInfoAccurate'
        <3> pc[SenderWriteID] \in {"sender_write_data", "sender_check_notify_data",
                                   "sender_notify_data", "sender_blocked"}
            BY DEF SenderInfoAccurate
        <3> CASE pc[SenderWriteID] \in {"sender_write_data"}
            <4> free < lm BY DEF SenderInfoAccurate, TypeOK
            <4> lb1 + free = BufferSize BY DEF SenderInfoAccurate
            <4> SUFFICES lg2 + lb2 + free >= lg1 + Min(BufferSize, Len(Buffer) + lm)
                BY DEF WriteLimit
            <4> SUFFICES lg1 + lb1 + free >= lg1 + Min(BufferSize, Len(Buffer) + lm)
                OBVIOUS
            <4> SUFFICES lg1 + BufferSize >= lg1 + Min(BufferSize, Len(Buffer) + lm)
                BY DEF TypeOK
            <4> QED BY DEF Min
        <3> CASE pc[SenderWriteID] \in {"sender_check_notify_data",
                                        "sender_notify_data", "sender_blocked"}
            <4> \/ lb1 + free = BufferSize
                \/ lm = 0 BY DEF SenderInfoAccurate
            <4> CASE lb1 + free = BufferSize
                <5> free = 0 BY DEF IntegrityI, TypeOK
                <5> SUFFICES lg2 + lb2 >= lg1 + Min(BufferSize, BufferSize + lm) BY DEF WriteLimit
                <5> SUFFICES lg2 + lb2 >= lg1 + BufferSize BY DEF Min
                <5> SUFFICES lg1 + lb1 >= lg1 + BufferSize OBVIOUS
                <5> QED OBVIOUS
            <4> CASE lm = 0
                <5> SUFFICES lg2 + lb2  >= lg1 + Min(BufferSize, lb1)
                    BY DEF WriteLimit
                <5> SUFFICES lg1 + lb1 >= lg1 + Min(BufferSize, lb1)
                    OBVIOUS
                <5> QED BY DEF Min
            <4> QED OBVIOUS
        <3> QED OBVIOUS
    <2> QED OBVIOUS
<1> CASE ~SenderInfoAccurate
    <2> ~SenderInfoAccurate'
        <3> CASE lb2 + free = BufferSize
            <4> CASE free = 0
                <5> lb2 = BufferSize OBVIOUS
                <5> Len(Buffer) > BufferSize BY LengthFacts
                <5> Len(Buffer) <= BufferSize BY LengthFacts
                <5> Len(Buffer) \in Nat /\ BufferSize \in Nat BY LengthFacts
                <5> QED OBVIOUS
            <4> CASE free > 0
                <5> pc[SenderWriteID] \in {"sender_write", "sender_request_notify",
                                           "sender_recheck_len", "sender_write_data"}
                    BY DEF IntegrityI
                <5> CASE /\ pc[SenderWriteID] \in {"sender_write_data"}
                         /\ Len(Buffer') + free = BufferSize
                    <6> Len(Buffer) + free < BufferSize
                        <7> Len(Buffer) + free /= BufferSize BY LengthFacts DEF TypeOK
                        <7> free <= BufferSize - Len(Buffer) BY DEF IntegrityI
                        <7> QED BY LengthFacts, BufferSizeType DEF TypeOK
                    <6> Len(Buffer') + free < BufferSize BY LengthFacts, BufferSizeType DEF TypeOK
                    <6> free < Len(msg) BY DEF SenderInfoAccurate, TypeOK
                    <6> QED BY DEF SenderInfoAccurate, TypeOK
                <5> QED BY DEF SenderInfoAccurate
            <4> QED BY DEF TypeOK
        <3> QED BY DEF SenderInfoAccurate, IntegrityI
    <2> pc[SenderWriteID] \in {"sender_write_data", "sender_check_notify_data",
                               "sender_notify_data", "sender_blocked"}
        BY DEF SenderInfoAccurate
    <2> CASE pc[SenderWriteID] \in {"sender_write_data"}
        <3> SUFFICES Len(Got') + Len(Buffer') + free >= Len(Got) + Len(Buffer) + free
            BY DEF WriteLimit
        <3> QED BY LengthFacts DEF TypeOK
    <2> CASE pc[SenderWriteID] \in {"sender_check_notify_data",
                                    "sender_notify_data", "sender_blocked"}
        BY LengthFacts DEF WriteLimit, TypeOK
    <2> QED OBVIOUS
<1> QED OBVIOUS

(* Signalling the sender cannot lower WriteLimit. *)
LEMMA NotifySenderWriteLimit ==
  ASSUME I, SpaceAvailableInt',
         UNCHANGED pc[SenderWriteID],
         UNCHANGED << Got, Buffer, msg, free >>
  PROVE WriteLimit' >= WriteLimit
<1> IntegrityI /\ TypeOK /\ PCOK BY DEF IntegrityI, I
<1>1. CASE SpaceAvailableInt
      <3> USE <1>1
      <3> UNCHANGED SenderInfoAccurate BY DEF SenderInfoAccurate
      <3> QED BY UNCHANGED WriteLimit, UnchangedWriteLimitGe DEF WriteLimit
<1>2. CASE ~SpaceAvailableInt
      <3> USE <1>2
      <3> SenderInfoAccurate' BY DEF SenderInfoAccurate
      <3> CASE SenderInfoAccurate BY UnchangedWriteLimitGe DEF WriteLimit
      <3> CASE ~SenderInfoAccurate
          <4> DEFINE m == Min(BufferSize, Len(Buffer) + Len(msg))
          <4> m \in Nat BY LengthFacts DEF TypeOK, Min
          <4> WriteLimit' = Len(Got) + m BY DEF WriteLimit
          <4> CASE pc[SenderWriteID] = "sender_write_data"
              <5> WriteLimit = Len(Got) + Len(Buffer) + free BY DEF WriteLimit
              <5> /\ free < Len(msg)
                  /\ Len(Buffer) + free /= BufferSize
                  BY DEF SenderInfoAccurate, TypeOK
              <5> free \in 0..BufferSize BY DEF TypeOK
              <5> SUFFICES Len(Got) + m >= Len(Got) + Len(Buffer) + free OBVIOUS
              <5> SUFFICES m >= Len(Buffer) + free OBVIOUS
              <5> free <= BufferSize - Len(Buffer) BY DEF IntegrityI
              <5> CASE m = Len(Buffer) + Len(msg)
                  <6> SUFFICES Len(msg) >= free OBVIOUS
                  <6> QED BY DEF TypeOK
              <5> QED BY DEF Min
          <4> CASE pc[SenderWriteID] \in {"sender_check_notify_data", "sender_notify_data",
                                          "sender_blocked"}
              <5> WriteLimit = Len(Got) + Len(Buffer) BY DEF WriteLimit
              <5> SUFFICES Len(Got) + m >= Len(Got) + Len(Buffer) OBVIOUS
              <5> SUFFICES m >= Len(Buffer) OBVIOUS
              <5> QED BY LengthFacts DEF Min
          <4> QED BY DEF SenderInfoAccurate, PCOK
      <3> QED OBVIOUS
<1> QED BY <1>1, <1>2

(* WriteLimit never decreases (unless the sender or receiver decides to close the connection). *)
THEOREM WriteLimitMonotonic ==
  ASSUME I, Next, SenderLive, ReceiverLive
  PROVE  WriteLimit' >= WriteLimit
<1> IntegrityI BY DEF I
<1> TypeOK BY DEF IntegrityI
<1> PCOK BY DEF IntegrityI
<1> CloseOK BY DEF I
<1> TypeOK' /\ IntegrityI' BY NextPreservesI, I', IntegrityI' DEF I, IntegrityI
<1>1. CASE SenderWrite
      <2> USE <1>1
      <2> CASE sender_ready
          <3> USE DEF sender_ready
          <3> pc'[SenderWriteID] = "sender_write" BY DEF PCOK
          <3> SenderInfoAccurate BY DEF SenderInfoAccurate
          <3> SenderInfoAccurate' BY DEF SenderInfoAccurate
          <3> Len(msg') > Len(msg) BY DEF IntegrityI
          <3> DEFINE l1 == Len(Buffer) + Len(msg)
          <3> DEFINE l2 == Len(Buffer) + Len(msg')
          <3> l2 > l1 OBVIOUS
          <3> l1 \in Nat /\ l2 \in Nat OBVIOUS
          <3> SUFFICES Len(Got) + Min(BufferSize, l2)
                       >= Len(Got) + Min(BufferSize, l1) BY DEF WriteLimit
          <3> HIDE DEF l1, l2
          <3> Min(BufferSize, l2) >= Min(BufferSize, l1) BY BufferSizeType DEF Min
          <3> Len(Got) \in Nat BY LengthFacts DEF TypeOK
          <3> QED BY BufferSizeType DEF Min
      <2> QED BY SenderWritePreservesWriteLimit, UnchangedWriteLimitGe DEF SenderWrite
<1>2. CASE SenderClose
      <2> USE <1>2
      <2> SUFFICES UNCHANGED WriteLimit BY UnchangedWriteLimitGe
      <2> UNCHANGED << pc[SenderWriteID], pc[ReceiverReadID], pc[ReceiverCloseID] >>
            BY DEF SenderClose, sender_open, sender_notify_closed, PCOK
      <2> UNCHANGED << Got, Buffer, msg, free, SpaceAvailableInt >>
          BY DEF SenderClose, sender_open, sender_notify_closed
      <2> UNCHANGED SenderInfoAccurate BY DEF SenderInfoAccurate
      <2> QED BY UNCHANGED WriteLimit DEF WriteLimit
<1>3. CASE ReceiverRead
      <2> USE <1>3
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverCloseID] >>
        BY DEF ReceiverRead, recv_init, recv_ready, recv_reading, recv_got_len,
                  recv_recheck_len, recv_read_data,
                  recv_check_notify_read, recv_notify_read,
                  recv_await_data, recv_final_check, PCOK
      <2>1. CASE \/ recv_init \/ recv_ready \/ recv_reading \/ recv_got_len
                 \/ recv_recheck_len \/ recv_check_notify_read
                 \/ recv_await_data \/ recv_final_check
            <3> USE <2>1
            <3> UNCHANGED << Got, Buffer, msg, free, SpaceAvailableInt >>
                BY DEF recv_init, recv_ready, recv_reading, recv_got_len,
                    recv_recheck_len, recv_check_notify_read,
                    recv_await_data, recv_final_check
            <3> UNCHANGED SenderInfoAccurate BY DEF SenderInfoAccurate
            <3> QED BY UNCHANGED WriteLimit, UnchangedWriteLimitGe DEF WriteLimit
      <2>2. CASE recv_read_data
            <3> USE <2>2
            <3> USE DEF recv_read_data
            <3>1. CASE have = 0
                  <4> USE <3>1
                  <4> UNCHANGED << Got, Buffer, msg >> OBVIOUS
                  <4> QED BY UNCHANGED WriteLimit, UnchangedWriteLimitGe DEF SenderInfoAccurate, WriteLimit
            <3>2. CASE have > 0
                  <4> USE <3>2
                  <4> QED BY RecvTransferWriteLimit
          <3> QED BY <3>1, <3>2 DEF TypeOK
      <2>3. CASE recv_notify_read BY <2>3, NotifySenderWriteLimit DEF recv_notify_read
      <2> QED BY <2>1, <2>2, <2>3 DEF ReceiverRead
<1>4. CASE ReceiverClose
      <2> USE <1>4
      <2> SUFFICES UNCHANGED WriteLimit BY UnchangedWriteLimitGe
      <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverReadID] >>
          BY DEF ReceiverClose, recv_open, recv_notify_closed, PCOK
      <2> UNCHANGED << Got, Buffer, msg, free, SpaceAvailableInt >>
          BY DEF ReceiverClose, recv_open, recv_notify_closed, CloseOK
      <2> UNCHANGED SenderInfoAccurate BY DEF SenderInfoAccurate
      <2> QED BY UNCHANGED WriteLimit DEF WriteLimit
<1>5. CASE SpuriousInterrupts
    <2> USE <1>5 DEF spurious
    <2> spurious BY DEF SpuriousInterrupts
    <2> UNCHANGED << pc[SenderWriteID], pc[SenderCloseID], pc[ReceiverReadID] >> BY DEF PCOK
    <2> UNCHANGED << Got, Buffer, msg >> OBVIOUS
    <2>1. CASE ~SpaceAvailableInt'
          <3> USE <2>1
          <3> UNCHANGED SpaceAvailableInt OBVIOUS
          <3> UNCHANGED SenderInfoAccurate BY DEF SenderInfoAccurate
          <3> UNCHANGED WriteLimit BY DEF WriteLimit
          <3> QED BY UnchangedWriteLimitGe
    <2>2. CASE SpaceAvailableInt' BY <2>2, NotifySenderWriteLimit
    <2> QED BY <2>1, <2>2
<1>6. CASE UNCHANGED vars
      <2> USE <1>6 DEF vars
      <2> UNCHANGED pc[SenderWriteID] BY DEF PCOK
      <2> QED BY UnchangedWriteLimitGe DEF SenderInfoAccurate, WriteLimit
<1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Next

=============================================================================
