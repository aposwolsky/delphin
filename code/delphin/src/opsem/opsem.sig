(* The delphin programming language operational semantics *)
(* Author: Adam Poswolsky *)

signature DELPHIN_OPSEM = 
  sig
    exception NoSolution
    val eval0 : DelphinIntSyntax.Exp -> DelphinIntSyntax.Exp

    val reduceCase : DelphinIntSyntax.Dec IntSyn.Ctx -> DelphinIntSyntax.Dec IntSyn.Ctx
                    -> DelphinIntSyntax.CaseBranch -> DelphinIntSyntax.CaseBranch
    val eval : DelphinIntSyntax.Dec IntSyn.Ctx -> DelphinIntSyntax.Exp
               -> DelphinIntSyntax.Exp
  end
