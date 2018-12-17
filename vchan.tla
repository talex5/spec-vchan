------------------------------- MODULE vchan -------------------------------

EXTENDS Naturals, Sequences   \* Library imports
CONSTANT BufferSize
Byte == 0..255
MSG  == Seq(Byte)

Take(m, i) == SubSeq(m, 1, i)
Drop(m, i) == SubSeq(m, i + 1, Len(m))

VARIABLES Got, Buffer, Sent
vars == << Got, Buffer, Sent >> 

\* Desired properties

Integrity       == Take(Sent, Len(Got)) = Got

AvailabilityNat == Nat
Availability    == \A x \in AvailabilityNat :
                    Len(Sent) = x ~> Len(Got) >= x

\* Algorithm

Read  == \E n \in 1..Len(Buffer) :
          /\ Got' = Got \o Take(Buffer, n)
          /\ Buffer' = Drop(Buffer, n)
          /\ UNCHANGED Sent

Write == \E m \in MSG :
          /\ Buffer' = Buffer \o m
          /\ Len(Buffer') <= BufferSize
          /\ Sent' = Sent \o m
          /\ UNCHANGED Got

Next  == Read \/ Write

Init  == /\ Sent   = << >>
         /\ Buffer = << >>
         /\ Got    = << >>

Spec  == Init /\ [][Next]_vars /\ WF_vars(Read)

BufferOK == Len(Buffer) <= BufferSize

\* Model checking

MSG_SEQ(max) == { [ x \in 1..N |-> Len(Sent) + x ] : N \in 1..max }

=============================================================================
  