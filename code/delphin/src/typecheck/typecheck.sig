(* Delphin Type Checker *)
(* Author: Adam Poswolsky *)

signature DELPHIN_TYPECHECK = 
  sig
    exception Error of string
    val checkType : ((DelphinIntSyntax.Dec) IntSyn.Ctx) * DelphinIntSyntax.Exp * DelphinIntSyntax.Types -> unit
                        (* Checks the type of a program.. pass in a FVar (as single element list)
			 * to infer the type of a delphin program. 
			 *
			 * raises Error if it does not typecheck 
			 *)

    val inferType : ((DelphinIntSyntax.Dec) IntSyn.Ctx) * DelphinIntSyntax.Exp -> DelphinIntSyntax.Types
                         
  end
