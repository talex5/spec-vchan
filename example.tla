------------------------------ MODULE example ------------------------------

(* A sender writes data to a buffer and a receiver reads it.
   The actual data isn't modelled, just the counters.
   This is intended as a simple demonstration of proving a liveness
   property (that the receiver eventually reads anything that is sent). *)

EXTENDS Naturals, TLAPS

CONSTANT BufferSize 
ASSUME BufferSizeType == BufferSize \in Nat \ {0}

VARIABLES Sent, Got
vars == << Sent, Got >>

BufferUsed == Sent - Got
BufferFree == BufferSize - BufferUsed

-----------------------------------------------------------------------------
(* Properties *)

LivenessNat == Nat  (* (need to override this for model checking) *)

(* If we have sent n bytes then we will eventually receive at least n bytes. *)
Liveness ==
  \A n \in LivenessNat :
    Sent = n ~> Got >= n

-----------------------------------------------------------------------------
(* Spec *)

Init ==
  /\ Sent = 0
  /\ Got = 0

(* The sender sends more bytes, up to the amount of free space in the buffer. *)
Send ==
  \E n \in 1..BufferFree :
    /\ Sent' = Sent + n
    /\ UNCHANGED Got

(* The receiver reads everything currently in the buffer. *)
Recv ==
  /\ BufferUsed > 0
  /\ Got' = Got + BufferUsed
  /\ UNCHANGED Sent

Next ==
  \/ Send
  \/ Recv

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Recv)     (* The receiver must eventually read, if it can *)

-----------------------------------------------------------------------------

(* Invariant *)

I ==
  /\ Sent \in Nat
  /\ Got \in Nat
  /\ Sent >= Got                    (* We can't receive more than was sent *)
  /\ BufferUsed \in 0..BufferSize   (* The buffer doesn't overflow *)

USE DEF BufferUsed, BufferFree

LEMMA NextPreservesI ==
  ASSUME I, Next
  PROVE  I'
<1> CASE Send BY BufferSizeType DEF I, Send
<1> CASE Recv BY BufferSizeType DEF I, Recv
<1> QED BY DEF Next

THEOREM AlwaysI == Spec => []I
<1> Init => I BY BufferSizeType DEF Init, I
<1> I /\ [Next]_vars => I' BY NextPreservesI DEF vars, I
<1> QED BY PTL DEF Spec

-----------------------------------------------------------------------------

(* Proving liveness.

   We can prove that A ~> B by showing that:
   
   - All possible steps from A either stay in A or move to B.
   - There is some action that moves from A to B.
   - While in state A, that action is always possible.
   - If the action is always possible then it will eventually happen (fairness).
   
   In this example, A indicates that some number of bytes have been sent
   but not received, and B that they have been received. *)

(* If we're already at A, we always either stay there or move to B.
   (for this proof, we don't need the bits about B, but that might
   be useful in other cases so I left them in). *)
LEMMA NoBacksliding ==
  ASSUME NEW n \in Nat, I, [Next]_vars,        
             Sent >= n, ~(Got >= n)
  PROVE  Sent' >= n \/ Got' >= n
<1> CASE Send BY DEF Send, I
<1> CASE Recv BY DEF Recv, I
<1> QED BY DEF Next, vars

(* Performing a Recv step from A takes us to our goal, B. *)
LEMMA RecvUseful ==
  ASSUME NEW n \in Nat, Sent >= n, ~(Got >= n), I, Recv
  PROVE  Got' >= n
BY DEF Recv, I

(* If we're at A, Recv is possible.
   In this simple example the solver can prove this directly,
   but typically proving ENABLED <<X>>_vars directly is too hard 
   and it's better to prove ENABLED X and use ENABLEDaxioms,
   which is what we do here.
   Warning: ENABLEDaxioms is fussy about the exact syntax (<=>) used. *)
LEMMA EnabledRecv ==
  ASSUME NEW n \in Nat, I,
         Sent >= n, ~(Got >= n)
  PROVE  ENABLED <<Recv>>_vars
<1> <<Recv>>_vars <=> Recv BY DEF vars, Recv, I
<1> ENABLED <<Recv>>_vars <=> ENABLED Recv BY ENABLEDaxioms
<1> SUFFICES ENABLED Recv OBVIOUS
<1> BufferUsed > 0 BY DEF I
<1> QED BY AutoUSE, ExpandENABLED DEF Recv

THEOREM
  ASSUME NEW n \in Nat
  PROVE  Spec => Liveness
<1> DEFINE B == Got >= n
<1> DEFINE A == Sent >= n /\ ~B
<1> SUFFICES ASSUME []I,
                    [][Next]_vars,
                    WF_vars(Recv)
             PROVE  Sent = n ~> B
    <2> Spec => []I BY PTL, AlwaysI DEF Spec
    <2> QED BY DEF Spec, I, Liveness
<1> SUFFICES A ~> B
    <2> Sent = n => Sent >= n OBVIOUS
    <2> Sent = n ~> Sent >= n BY PTL
    <2> QED BY PTL
<1> I BY PTL
<1> A /\ Recv => B' BY RecvUseful
<1> A /\ [Next]_vars => (A \/ B)' BY NoBacksliding
<1> A => ENABLED <<Recv>>_vars BY EnabledRecv, PTL
<1> QED BY PTL

=============================================================================
