(* The nabla programming language operational semantics *)
(* Author: Adam Poswolsky and Carsten Schuermann *)

signature NABLA_OPSEM = 
  sig
    exception NoSolution
    val eval0 : NablaIntSyntax.Exp -> NablaIntSyntax.Exp

  end
