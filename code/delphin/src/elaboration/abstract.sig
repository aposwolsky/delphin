(* Delphin Abstraction (for pattern variables) *)
(* Author: Adam Poswolsky *)

signature DELPHINABSTRACT =
sig
  exception Error of Paths.region * string
  exception LeftOverConstraints of (Paths.region * IntSyn.cnstr list) list

  datatype EFLPVar =
      EV of Paths.region * IntSyn.Exp			 (* Y ::= X         for  GX |- X : VX   *)
    | FV of Paths.region * string * bool * IntSyn.Exp 	 (*     | (F, b, V)        if . |- F : V  *)
                                                         (*              and b is true if it is a parameter *)
    | LV of Paths.region * IntSyn.Block                  (*     | L             if . |- L in W  *) 
    | PV of Paths.region * string                        (*     | PatVar (Delphin)              *)

  val abstractPatVarsExp : DelphinIntermediateSyntax.Exp -> DelphinIntermediateSyntax.Exp
  val abstractPatVarsFunList : (Paths.region *  DelphinIntermediateSyntax.NormalDec * DelphinIntermediateSyntax.Exp) list  ->  (Paths.region *  DelphinIntermediateSyntax.NormalDec * DelphinIntermediateSyntax.Exp) list 

  val addImplicitTypesDec : DelphinIntermediateSyntax.NormalDec ->  DelphinIntermediateSyntax.NormalDec
  val addImplicitTypesForm : DelphinIntermediateSyntax.Formula ->  DelphinIntermediateSyntax.Formula

end;  (* signature ABSTRACT *)
