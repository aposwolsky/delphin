(* Nabla Type Checker *)
(* Author: Adam Poswolsky *)

signature NABLA_TYPECHECK = 
  sig
    exception Error of string
    val inferType : (NablaIntSyntax.Dec IntSyn.Ctx) list * NablaIntSyntax.Exp -> NablaIntSyntax.Formula

  end
