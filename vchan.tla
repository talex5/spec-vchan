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
by the client. The algorithm described here provides reliable lockfree operation,
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

TODO: Consider weird ways of using it (e.g. QubesDB).

The library can be used in streaming mode or in packet mode. In packet mode, sending
waits until there is enough space for the whole message before starting to write it,
while in streaming mode it writes as much as possible.

TODO: Currently, the specification's fairness assumptions only cover streaming mode.
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
2. The algorithm (as PlusCal, followed by it's translation to TLA).
3. The properties (Availability and Integrity).
4. TODO: Inductive invariants for Integrity and deadlock freedom.
5. TODO: Proofs of the above.

-- Thomas Leonard, 2018

------------------------------- MODULE vchan -------------------------------

EXTENDS Naturals, Sequences   \* Import some libraries we use.

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
SpuriousID       == "SP"   \* Spurious interrupts from the other channel

(* Overview of the algorithm:

   On the sending side:

   1. The sending application asks to send some bytes.
      We check whether the receiver has closed the channel and abort if so.
   2. We check the amount of buffer space available.
   3. If there isn't enough, we set NotifyRead so the receiver will notify us when there is more.
      We also check the space again after this, in case it changed while setting the flag.
   4. If there is any space:
      a. We write as much data as we can to the buffer.
      b. If the NotifyWrite flag is set, we clear it and notify the receiver of the write.
   5. If we wrote everything, we return success.
   6. Otherwise, we wait to be notified of more space.
   7. We check whether the receiver has closed the channel.
      If so we abort. Otherwise, we go back to step 2.

   On the receiving side:

   1. The receiving application asks us to read up to some amount data.
   2. We check the amount of data available in the buffer.
   3. If there isn't enough, we set NotifyWrite so the sender will notify us when there is.
      We also check the space again after this, in case it changed while setting the flag.
   4. If there is any data, we read up to the amount requested.
      If the NotifyRead flag is set, we clear it and notify the receiver of the new space.
      We return success to the application (even if we didn't get as much as requested).
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
       I'm not sure why NotifyWrite is initialised to TRUE, but that's what the C code does.
       It may be a backwards-compatibility hack for e.g. QubesDB. *)
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
            want = 0,     \* The amount of data the user wants us to read.
            Got = << >>;  \* Pseudo-variable recording all data ever received by receiver.
  {
recv_ready:         while (ReceiverLive) {
                      with (n \in 1..MaxReadLen) want := n;
recv_reading:         while (TRUE) {
                        have := Len(Buffer);
recv_got_len:           if (have >= want) goto recv_read_data \* (see note 1)
                        else NotifyWrite := TRUE;
recv_recheck_len:       have := Len(Buffer);
recv_read_data:         if (have > 0) {
                          Got := Got \o Take(Buffer, Min(want, have));
                          Buffer := Drop(Buffer, Min(want, have));
                          want := 0;
                          have := 0;
recv_check_notify_read:   if (NotifyRead) {
                            NotifyRead := FALSE;      \* (atomic test-and-clear)
recv_notify_read:           SpaceAvailableInt := TRUE;
                            goto recv_ready;          \* Return success
                          } else goto recv_ready;     \* Return success
                        } else if (~SenderLive \/ ~ReceiverLive) {
                          \* (see note 2)
recv_final_check:         if (Len(Buffer) = 0) { want := 0; goto Done }
                          else goto recv_reading;
                        };
recv_await_data:        await DataReadyInt \/ ~ReceiverLive;
                        if (~ReceiverLive) { want := 0; goto Done }
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

   Note 2:
   The C code doesn't do the recv_final_check check, but that presumably means that it
   might not read all of the client's data.

   Note on formatting:
   TLA's PDF rendering gets the indentation wrong if you put a semicolon after a closing brace,
   but the PlusCal-to-TLA translator requires it.
*)


\* BEGIN TRANSLATION
VARIABLES SenderLive, ReceiverLive, Buffer, NotifyWrite, DataReadyInt, 
          NotifyRead, SpaceAvailableInt, pc, free, msg, Sent, have, want, Got

vars == << SenderLive, ReceiverLive, Buffer, NotifyWrite, DataReadyInt, 
           NotifyRead, SpaceAvailableInt, pc, free, msg, Sent, have, want, 
           Got >>

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
        /\ want = 0
        /\ Got = << >>
        /\ pc = [self \in ProcSet |-> CASE self = SenderWriteID -> "sender_ready"
                                        [] self = SenderCloseID -> "sender_open"
                                        [] self = ReceiverReadID -> "recv_ready"
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
                                free, have, want, Got >>

sender_write == /\ pc[SenderWriteID] = "sender_write"
                /\ free' = BufferSize - Len(Buffer)
                /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_request_notify"]
                /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                                DataReadyInt, NotifyRead, SpaceAvailableInt, 
                                msg, Sent, have, want, Got >>

sender_request_notify == /\ pc[SenderWriteID] = "sender_request_notify"
                         /\ IF free >= Len(msg)
                               THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_write_data"]
                                    /\ UNCHANGED NotifyRead
                               ELSE /\ NotifyRead' = TRUE
                                    /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_recheck_len"]
                         /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                         NotifyWrite, DataReadyInt, 
                                         SpaceAvailableInt, free, msg, Sent, 
                                         have, want, Got >>

sender_recheck_len == /\ pc[SenderWriteID] = "sender_recheck_len"
                      /\ free' = BufferSize - Len(Buffer)
                      /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_write_data"]
                      /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                      NotifyWrite, DataReadyInt, NotifyRead, 
                                      SpaceAvailableInt, msg, Sent, have, want, 
                                      Got >>

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
                                     SpaceAvailableInt, Sent, have, want, Got >>

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
                                            have, want, Got >>

sender_notify_data == /\ pc[SenderWriteID] = "sender_notify_data"
                      /\ DataReadyInt' = TRUE
                      /\ IF msg = << >>
                            THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_ready"]
                            ELSE /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_blocked"]
                      /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                      NotifyWrite, NotifyRead, 
                                      SpaceAvailableInt, free, msg, Sent, have, 
                                      want, Got >>

sender_blocked == /\ pc[SenderWriteID] = "sender_blocked"
                  /\ SpaceAvailableInt \/ ~SenderLive
                  /\ IF ~SenderLive
                        THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "Done"]
                             /\ UNCHANGED SpaceAvailableInt
                        ELSE /\ SpaceAvailableInt' = FALSE
                             /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_check_recv_live"]
                  /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                  NotifyWrite, DataReadyInt, NotifyRead, free, 
                                  msg, Sent, have, want, Got >>

sender_check_recv_live == /\ pc[SenderWriteID] = "sender_check_recv_live"
                          /\ IF ~ReceiverLive
                                THEN /\ pc' = [pc EXCEPT ![SenderWriteID] = "Done"]
                                ELSE /\ pc' = [pc EXCEPT ![SenderWriteID] = "sender_write"]
                          /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                          NotifyWrite, DataReadyInt, 
                                          NotifyRead, SpaceAvailableInt, free, 
                                          msg, Sent, have, want, Got >>

SenderWrite == sender_ready \/ sender_write \/ sender_request_notify
                  \/ sender_recheck_len \/ sender_write_data
                  \/ sender_check_notify_data \/ sender_notify_data
                  \/ sender_blocked \/ sender_check_recv_live

sender_open == /\ pc[SenderCloseID] = "sender_open"
               /\ SenderLive' = FALSE
               /\ pc' = [pc EXCEPT ![SenderCloseID] = "sender_notify_closed"]
               /\ UNCHANGED << ReceiverLive, Buffer, NotifyWrite, DataReadyInt, 
                               NotifyRead, SpaceAvailableInt, free, msg, Sent, 
                               have, want, Got >>

sender_notify_closed == /\ pc[SenderCloseID] = "sender_notify_closed"
                        /\ DataReadyInt' = TRUE
                        /\ pc' = [pc EXCEPT ![SenderCloseID] = "Done"]
                        /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                        NotifyWrite, NotifyRead, 
                                        SpaceAvailableInt, free, msg, Sent, 
                                        have, want, Got >>

SenderClose == sender_open \/ sender_notify_closed

recv_ready == /\ pc[ReceiverReadID] = "recv_ready"
              /\ IF ReceiverLive
                    THEN /\ \E n \in 1..MaxReadLen:
                              want' = n
                         /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_reading"]
                    ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "Done"]
                         /\ want' = want
              /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                              DataReadyInt, NotifyRead, SpaceAvailableInt, 
                              free, msg, Sent, have, Got >>

recv_reading == /\ pc[ReceiverReadID] = "recv_reading"
                /\ have' = Len(Buffer)
                /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_got_len"]
                /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                                DataReadyInt, NotifyRead, SpaceAvailableInt, 
                                free, msg, Sent, want, Got >>

recv_got_len == /\ pc[ReceiverReadID] = "recv_got_len"
                /\ IF have >= want
                      THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_read_data"]
                           /\ UNCHANGED NotifyWrite
                      ELSE /\ NotifyWrite' = TRUE
                           /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_recheck_len"]
                /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, DataReadyInt, 
                                NotifyRead, SpaceAvailableInt, free, msg, Sent, 
                                have, want, Got >>

recv_recheck_len == /\ pc[ReceiverReadID] = "recv_recheck_len"
                    /\ have' = Len(Buffer)
                    /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_read_data"]
                    /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                    NotifyWrite, DataReadyInt, NotifyRead, 
                                    SpaceAvailableInt, free, msg, Sent, want, 
                                    Got >>

recv_read_data == /\ pc[ReceiverReadID] = "recv_read_data"
                  /\ IF have > 0
                        THEN /\ Got' = Got \o Take(Buffer, Min(want, have))
                             /\ Buffer' = Drop(Buffer, Min(want, have))
                             /\ want' = 0
                             /\ have' = 0
                             /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_check_notify_read"]
                        ELSE /\ IF ~SenderLive \/ ~ReceiverLive
                                   THEN /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_final_check"]
                                   ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_await_data"]
                             /\ UNCHANGED << Buffer, have, want, Got >>
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
                                          have, want, Got >>

recv_notify_read == /\ pc[ReceiverReadID] = "recv_notify_read"
                    /\ SpaceAvailableInt' = TRUE
                    /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_ready"]
                    /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                    NotifyWrite, DataReadyInt, NotifyRead, 
                                    free, msg, Sent, have, want, Got >>

recv_final_check == /\ pc[ReceiverReadID] = "recv_final_check"
                    /\ IF Len(Buffer) = 0
                          THEN /\ want' = 0
                               /\ pc' = [pc EXCEPT ![ReceiverReadID] = "Done"]
                          ELSE /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_reading"]
                               /\ want' = want
                    /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                    NotifyWrite, DataReadyInt, NotifyRead, 
                                    SpaceAvailableInt, free, msg, Sent, have, 
                                    Got >>

recv_await_data == /\ pc[ReceiverReadID] = "recv_await_data"
                   /\ DataReadyInt \/ ~ReceiverLive
                   /\ IF ~ReceiverLive
                         THEN /\ want' = 0
                              /\ pc' = [pc EXCEPT ![ReceiverReadID] = "Done"]
                              /\ UNCHANGED DataReadyInt
                         ELSE /\ DataReadyInt' = FALSE
                              /\ pc' = [pc EXCEPT ![ReceiverReadID] = "recv_reading"]
                              /\ want' = want
                   /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                   NotifyWrite, NotifyRead, SpaceAvailableInt, 
                                   free, msg, Sent, have, Got >>

ReceiverRead == recv_ready \/ recv_reading \/ recv_got_len
                   \/ recv_recheck_len \/ recv_read_data
                   \/ recv_check_notify_read \/ recv_notify_read
                   \/ recv_final_check \/ recv_await_data

recv_open == /\ pc[ReceiverCloseID] = "recv_open"
             /\ ReceiverLive' = FALSE
             /\ pc' = [pc EXCEPT ![ReceiverCloseID] = "recv_notify_closed"]
             /\ UNCHANGED << SenderLive, Buffer, NotifyWrite, DataReadyInt, 
                             NotifyRead, SpaceAvailableInt, free, msg, Sent, 
                             have, want, Got >>

recv_notify_closed == /\ pc[ReceiverCloseID] = "recv_notify_closed"
                      /\ SpaceAvailableInt' = TRUE
                      /\ pc' = [pc EXCEPT ![ReceiverCloseID] = "Done"]
                      /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, 
                                      NotifyWrite, DataReadyInt, NotifyRead, 
                                      free, msg, Sent, have, want, Got >>

ReceiverClose == recv_open \/ recv_notify_closed

spurious == /\ pc[SpuriousID] = "spurious"
            /\ \/ /\ SpaceAvailableInt' = TRUE
                  /\ UNCHANGED DataReadyInt
               \/ /\ DataReadyInt' = TRUE
                  /\ UNCHANGED SpaceAvailableInt
            /\ pc' = [pc EXCEPT ![SpuriousID] = "spurious"]
            /\ UNCHANGED << SenderLive, ReceiverLive, Buffer, NotifyWrite, 
                            NotifyRead, free, msg, Sent, have, want, Got >>

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

(* To be implemented without locks, each atomic step must only access at most one shared
   variable. The elements of Buffer are not considered to be shared in this sense,
   as there is never a moment when any one element can be accessed by two processes.

   Here are the steps and the shared variables they access:

  SenderWrite: (SenderLive and the producer index are considered to be local)
    sender_ready: ReceiverLive
    sender_write: Len(Buffer)               (get consumer index)
    sender_request_notify: NotifyRead
    sender_recheck_len: Len(Buffer)
    sender_write_data: Buffer               (write producer index)
    sender_check_notify_data: NotifyWrite   (atomic test-and-clear operation)
    sender_notify_data: DataReadyInt
    sender_blocked: SpaceAvailableInt
    sender_check_recv_live: ReceiverLive

  SenderClose:
    sender_open: -
    sender_notify_closed: DataReadyInt

  ReceiverRead: (ReceiverLive and the consumer index are considered to be local)
    recv_ready: -
    recv_reading: Len(Buffer)               (get producer index)
    recv_got_len: NotifyWrite
    recv_recheck_len: Len(Buffer)
    recv_read_data: Buffer or SenderLive    (depending on local variable have)
    recv_check_notify_read: NotifyRead      (atomic test-and-clear operation)
    recv_notify_read: SpaceAvailableInt
    recv_final_check: Buffer
    recv_await_data: DataReadyInt

  ReceiverClose:
    recv_open: -
    recv_notify_closed: SpaceAvailableInt
  *)

\* An invariant describing the types of all variables (except pc).
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
  /\ want \in 0..MaxReadLen
  /\ have \in 0..BufferSize

\* Whatever we receive is the same as what was sent.
\* (i.e. Got is a prefix of Sent)
Integrity ==
  Take(Sent, Len(Got)) = Got

\* TLC can normally detect deadlock by itself, but we also want to consider
\* the system as deadlocked if closing the connection is the only way out.
NoDeadlock ==
  \/ []<><<SpuriousInterrupts>>_vars  \* (ignoring spurious interrupts)
  \/ /\ <>[] (pc[SenderWriteID] \in {"sender_ready", "Done"})
     /\ <>[] (pc[ReceiverReadID] \in {"recv_ready", "recv_await_data", "Done"})

AvailabilityNat == Nat    \* Just to allow overriding it in TLC

\* Any data that the write function reports has been sent successfully
\* (i.e. data in Sent when it is back at "sender_ready") will eventually
\* be received (if the receiver doesn't close the connection).
\* In particular, this says that it's OK for the sender to close its
\* end immediately after sending some data.
Availability ==
  \A x \in AvailabilityNat :
    x = Len(Sent) /\ SenderLive /\ pc[SenderWriteID] = "sender_ready" ~>
         \/ Len(Got) >= x
         \/ ~ReceiverLive

(* Model checking

   Suggested parameters for "What is the model?":
     BufferSize = 2
     MaxReadLen = 2
     MaxWriteLen = 2
     Byte = 0..5

   Definition Overrides:
     MSG <- MSG_SEQ
     AvailabilityNat <- 0..4

   State Constraints:
     Len(Sent) < 4

   Invariants:
     TypeOK
     Integrity

   Properties:
     Availability
 *)

(* Override MSG with this to limit Sent to the form << 1, 2, 3, ... >>.
   This is much faster to check and will still detect any dropped or reordered bytes. *)
MSG_SEQ == { [ x \in 1..N |-> Len(Sent) + x ] : N \in 1..MaxWriteLen }

=============================================================================
