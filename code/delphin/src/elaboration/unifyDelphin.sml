(* Delphin Unification *)
(* Author: Adam Poswolsky *)

structure UnifyDelphinOpsemTrail =
  UnifyDelphin (structure Trail = Trail
		structure U = UnifyTrail)


structure UnifyDelphinNoTrail =
  UnifyDelphin (structure Trail = NoTrail
		structure U = UnifyNoTrail)
