----------------------------- MODULE RailwayCrossing -----------------------------

EXTENDS Naturals, TLC

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)

VARIABLES train, car, barrier

(***************************************************************************)
(* CONSTANTS                                                               *)
(***************************************************************************)

CONSTANTS 
    Idle, Approaching, Crossing, Passed

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)

Init ==
    /\ train = Idle
    /\ car = Idle
    /\ barrier = "UP"

(***************************************************************************)
(* TRANSITIONS                                                             *)
(***************************************************************************)

Next ==
    \/ /\ train = Idle
       /\ train' = Approaching
       /\ car' = car
       /\ barrier' = barrier

    \/ /\ train = Approaching
       /\ train' = Crossing
       /\ car' = car
       /\ barrier' = "DOWN"

    \/ /\ train = Crossing
       /\ train' = Passed
       /\ car' = car
       /\ barrier' = "DOWN"

    \/ /\ train = Passed
       /\ train' = Idle
       /\ car' = car
       /\ barrier' = "UP"

    \/ /\ car = Idle
       /\ car' = Crossing
       /\ train' = train
       /\ IF barrier = "DOWN" THEN barrier' = barrier ELSE barrier' = barrier

    \/ /\ car = Crossing
       /\ car' = Passed
       /\ train' = train
       /\ barrier' = barrier

    \/ /\ car = Passed
       /\ car' = Idle
       /\ train' = train
       /\ barrier' = barrier

(***************************************************************************)
(* SPECIFICATION                                                           *)
(***************************************************************************)

Spec == Init /\ [][Next]_<<train, car, barrier>>

(***************************************************************************)
(* SAFETY PROPERTIES                                                       *)
(***************************************************************************)

SafetyInvariant ==
    ~(train = Crossing /\ car = Crossing)

(***************************************************************************)
(* LIVENESS PROPERTIES                                                     *)
(***************************************************************************)

Liveness ==
    WF_<<train, car, barrier>>(Next)

=============================================================================
