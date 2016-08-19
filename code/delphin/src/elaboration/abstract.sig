(* Delphin Abstraction (for pattern variables) *)
(* Author: Adam Poswolsky *)

signature DELPHINABSTRACT =
sig
  exception Error of Paths.region * string
  exception LeftOverConstraints of (Paths.region * IntSyn.cnstr list) list

  datatype EFLPVar =
      EV of Paths.region * IntSyn.Exp * ((IntSyn.Exp * int * (int list)) ref)	   (* Y ::= X         for  GX |- X : VX   
							    * The type is saved in an option ref.
							    *)
    | FV of Paths.region * string * (bool ref) * IntSyn.Exp 	 (*     | (F, b, V)        if . |- F : V  *)
                                                         (*              and b is true if it is a parameter *)
    | LV of Paths.region * IntSyn.Block                  (*     | L             if . |- L in W  *) 
    | PV of Paths.region * string                        (*     | PatVar (Delphin)              *)

  val abstractPatVarsExp :  Paths.region * DelphinIntermediateSyntax.Exp * DelphinIntSyntax.Types -> DelphinIntermediateSyntax.Exp
  val abstractPatVarsFunList :  (Paths.region *  DelphinIntermediateSyntax.NormalDec * DelphinIntermediateSyntax.Exp) list  ->  (Paths.region *  DelphinIntermediateSyntax.NormalDec * DelphinIntermediateSyntax.Exp) list 

  val addImplicitTypesDec : DelphinIntermediateSyntax.NormalDec * (EFLPVar IntSyn.Ctx) ->  DelphinIntermediateSyntax.NormalDec
  val addImplicitTypesForm : DelphinIntermediateSyntax.Formula * (EFLPVar IntSyn.Ctx) ->  DelphinIntermediateSyntax.Formula

  val addSomeVars : Paths.region * IntSyn.Exp -> (DelphinIntSyntax.Dec IntSyn.Ctx * IntSyn.Exp)
  val transformDelExp : int * DelphinIntermediateSyntax.Exp * (EFLPVar IntSyn.Ctx) * bool -> DelphinIntermediateSyntax.Exp * (EFLPVar IntSyn.Ctx)
  val collectDelNormalDec : int * DelphinIntermediateSyntax.NormalDec * (EFLPVar IntSyn.Ctx) * bool -> (EFLPVar IntSyn.Ctx)
  val collectDelNewDec : int * DelphinIntermediateSyntax.NewDec * (EFLPVar IntSyn.Ctx) * bool -> (EFLPVar IntSyn.Ctx)
  val collectDelTypes : int * DelphinIntermediateSyntax.Types * (EFLPVar IntSyn.Ctx) * bool -> (EFLPVar IntSyn.Ctx)
  val LFcollectExp : Paths.region * int * (IntSyn.Exp * IntSyn.Sub) * (EFLPVar IntSyn.Ctx) * bool -> (EFLPVar IntSyn.Ctx)

end;  (* signature ABSTRACT *)
