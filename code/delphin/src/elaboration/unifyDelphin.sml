(* Delphin Unification *)
(* Author: Adam Poswolsky *)

structure UnifyDelphinNoTrail =
  UnifyDelphin (structure Trail = NoTrail
		structure U = UnifyNoTrail)

structure UnifyDelphinTrail =
  UnifyDelphin (structure Trail = Trail
		structure U = UnifyTrail)
