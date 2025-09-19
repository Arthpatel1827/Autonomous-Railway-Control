----------------------------- MODULE RailwayCrossing -----------------------------
EXTENDS TLC

(***************************************************************************)
(* VARIABLES                                                               *)
(***************************************************************************)
VARIABLES train, car, barrier
vars == << train, car, barrier >>

(***************************************************************************)
(* INITIAL STATE                                                           *)
(***************************************************************************)
Init ==
  /\ train = "Idle"
  /\ car   = "Idle"
  /\ barrier = "UP"

(***************************************************************************)
(* TRAIN TRANSITIONS                                                       *)
(***************************************************************************)
(* Train is detected far enough away that we pre-close the barrier *)
TrainIdleToApproaching ==
  /\ train = "Idle"
  /\ train' = "Approaching"
  /\ barrier' = "DOWN"      \* pre-close
  /\ UNCHANGED car

(* Train may enter the crossing only when the car is not on it *)
TrainApproachingToCrossing ==
  /\ train = "Approaching"
  /\ car # "Crossing"
  /\ train' = "Crossing"
  /\ barrier' = "DOWN"
  /\ UNCHANGED car

TrainCrossingToPassed ==
  /\ train = "Crossing"
  /\ train' = "Passed"
  /\ barrier' = "DOWN"
  /\ UNCHANGED car

TrainPassedToIdle ==
  /\ train = "Passed"
  /\ train' = "Idle"
  /\ barrier' = "UP"
  /\ UNCHANGED car

(***************************************************************************)
(* CAR TRANSITIONS                                                         *)
(***************************************************************************)
(* A car may START crossing only when no train is approaching/crossing *)
CarIdleToCrossing ==
  /\ car = "Idle"
  /\ train = "Idle"         \* stricter than just barrier="UP"
  /\ barrier = "UP"
  /\ car' = "Crossing"
  /\ UNCHANGED << train, barrier >>

CarCrossingToPassed ==
  /\ car = "Crossing"
  /\ car' = "Passed"
  /\ UNCHANGED << train, barrier >>

CarPassedToIdle ==
  /\ car = "Passed"
  /\ car' = "Idle"
  /\ UNCHANGED << train, barrier >>

(***************************************************************************)
(* SYSTEM NEXT, SPEC, FAIRNESS                                             *)
(***************************************************************************)
Next ==
  \/ TrainIdleToApproaching
  \/ TrainApproachingToCrossing
  \/ TrainCrossingToPassed
  \/ TrainPassedToIdle
  \/ CarIdleToCrossing
  \/ CarCrossingToPassed
  \/ CarPassedToIdle

(* Fairness: if these actions remain enabled, they must eventually occur *)
Spec ==
  Init /\ [][Next]_vars
      /\ WF_vars(CarCrossingToPassed)
      /\ WF_vars(TrainCrossingToPassed)
      /\ WF_vars(TrainApproachingToCrossing)   \* optional but prevents waiting forever in Approaching

(***************************************************************************)
(* SAFETY & LIVENESS PROPERTIES                                            *)
(***************************************************************************)
(* Never both on the crossing *)
SafetyInvariant ==
  ~(train = "Crossing" /\ car = "Crossing")

(* When the train is crossing, the barrier must be down *)
BarrierWhenTrainCrossing ==
  (train = "Crossing") => (barrier = "DOWN")

(* Progress: once someone starts/approaches crossing, they eventually pass *)
TrainProgress ==
  []( (train = "Approaching" \/ train = "Crossing") => <> (train = "Passed") )

CarProgress ==
  []( (car = "Crossing") => <> (car = "Passed") )

=============================================================================
