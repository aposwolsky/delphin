(* Delphin Type Checker *)
(* Author: Adam Poswolsky *)

signature DELPHIN_TYPECHECK = 
  sig
    exception Error of string
    val checkType : DelphinIntSyntax.decCtx * DelphinIntSyntax.Exp * DelphinIntSyntax.Types -> unit
                        (* Checks the type of a program.. pass in a FVar (as single element list)
			 * to infer the type of a delphin program. 
			 *
			 * raises Error if it does not typecheck 
			 *)

    val inferType : DelphinIntSyntax.decCtx * DelphinIntSyntax.Exp -> DelphinIntSyntax.Types
                         
  end
