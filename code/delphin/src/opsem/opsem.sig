(* The delphin programming language operational semantics *)
(* Author: Adam Poswolsky and Carsten Schuermann *)

signature DELPHIN_OPSEM = 
  sig
    exception NoSolution
    val eval0 : DelphinIntSyntax.Exp -> DelphinIntSyntax.Exp

  end
