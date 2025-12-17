------------------------------ MODULE example ------------------------------

(* A sender writes data to a buffer and a receiver reads it.
   The actual data isn't modelled, just the counters.
   This is intended as a simple demonstration of proving a liveness
   property (that the receiver eventually reads anything that is sent). *)

EXTENDS Naturals, NaturalsInduction, TLAPS

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

(* The receiver reads some or all of the data in the buffer. *)
Recv ==
  \E n \in 1..BufferUsed :
    /\ Got' = Got + n
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

(* Like spec, but in terms of the invariant rather than the initial state.
   Things proved using ISpec are true from any state, not just the initial one. *)
ISpec ==
  /\ []I
  /\ [][Next]_vars
  /\ WF_vars(Recv)

LEMMA SpecImpliesISpec == Spec => ISpec
BY AlwaysI DEF Spec, ISpec

-----------------------------------------------------------------------------

(* Proving liveness.

   We can prove that A ~> B by showing that:
   
   - All possible steps from A either stay in A or move to B.
   - There is some action that moves from A to B.
   - While in state A, that action is always possible.
   - If the action is always possible then it will eventually happen (fairness).
   
   In this example, A indicates that we're i+1 bytes away from our goal
   and B is that we're within i steps. *)

(* Dist(n, i) says we are within i bytes of getting the first n bytes. *)
Dist(n, i) == Sent >= n /\ n - Got <= i

(* If we're already at A, we always either stay there or move to B. *)
LEMMA NoBacksliding ==
  ASSUME NEW n \in Nat, NEW i \in Nat,
         I, [Next]_vars,
         Dist(n, i + 1)
  PROVE  Dist(n, i + 1)'
<1> CASE Send BY DEF Send, I, Dist
<1> CASE Recv BY DEF Recv, I, Dist
<1> QED BY DEF Next, vars, Dist

(* Performing a Recv step from A takes us to our goal, B. *)
LEMMA RecvUseful ==
  ASSUME NEW n \in Nat, NEW i \in Nat,
         I, Recv,
         Dist(n, i + 1)
  PROVE  Dist(n, i)'
BY DEF Recv, I, Dist

(* If we're at A, Recv is possible. *)
LEMMA EnabledRecv ==
  ASSUME NEW n \in Nat, NEW i \in Nat, I,
         Dist(n, i + 1), ~Dist(n, i)
  PROVE  ENABLED <<Recv>>_vars
<1> SUFFICES ENABLED Recv
    <2> <<Recv>>_vars <=> Recv BY DEF vars, Recv, I
    <2> ENABLED <<Recv>>_vars <=> ENABLED Recv BY ENABLEDaxioms
    <2> QED OBVIOUS
<1> BufferUsed > 0 BY DEF I, Dist
<1> QED BY AutoUSE, ExpandENABLED DEF Recv, I

(* If we're within i+1 bytes of our goal, then eventually
   we'll be within i bytes. *)
LEMMA Progress ==
  ASSUME NEW n \in Nat, NEW i \in Nat
  PROVE  ISpec /\ Dist(n, i+1) ~> Dist(n, i)
<1> DEFINE B == Dist(n, i)
<1> DEFINE A == Dist(n, i+1) /\ ~B
<1> SUFFICES ASSUME []I,
                    [][Next]_vars,
                    WF_vars(Recv)
             PROVE  A ~> B
    BY PTL DEF ISpec
<1> I BY PTL
<1> A /\ Recv => B' BY RecvUseful
<1> A /\ [Next]_vars => (A \/ B)' BY NoBacksliding DEF Dist
<1> A => ENABLED <<Recv>>_vars BY EnabledRecv, PTL
<1> QED BY PTL

(* By induction, we'll always eventually be 0 bytes from our goal. *)
EventuallyDone_prop(n, i) == Dist(n, i) ~> Dist(n, 0)
LEMMA EventuallyDone ==
  ASSUME NEW n \in Nat
  PROVE  ISpec => \A i \in Nat : EventuallyDone_prop(n, i)
<1> SUFFICES ASSUME []ISpec
             PROVE \A i \in Nat : Dist(n, i) ~> Dist(n, 0)
    BY PTL DEF ISpec, EventuallyDone_prop
<1> ISpec /\ I BY PTL DEF ISpec
<1> DEFINE R(i) == Dist(n, i) ~> Dist(n, 0)
<1>1 R(0) BY PTL
<1>2 ASSUME NEW i \in Nat, R(i) PROVE R(i + 1)
    <2> Dist(n, i+1) ~> Dist(n, i) BY PTL, Progress
    <2> Dist(n, i) ~> Dist(n, 0) BY <1>2
    <2> QED BY PTL
<1> \A i \in Nat : R(i)
    <2> HIDE DEF R
    <2> QED BY NatInduction, Isa, <1>1, <1>2
<1> SUFFICES ASSUME NEW i \in Nat PROVE R(i)
    OBVIOUS
<1> HIDE DEF R
<1> QED OBVIOUS

THEOREM Spec => Liveness
<1> SUFFICES ASSUME []ISpec PROVE Liveness
    BY PTL, SpecImpliesISpec DEF ISpec
<1> ISpec /\ I BY PTL DEF ISpec
<1> SUFFICES ASSUME NEW n \in Nat PROVE Sent = n ~> Got >= n
    BY DEF Liveness, LivenessNat, I
<1> Sent = n => Dist(n, BufferSize) BY BufferSizeType DEF Dist, I
<1> Dist(n, BufferSize) ~> Dist(n, 0)
    <2> EventuallyDone_prop(n, BufferSize) BY BufferSizeType, EventuallyDone
    <2> QED BY DEF EventuallyDone_prop
<1> Dist(n, 0) => Got >= n BY DEF Dist, I
<1> QED BY PTL

=============================================================================
