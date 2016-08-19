(* Delphin Abstraction (for pattern variables) *)
(* Author: Adam Poswolsky *)

signature DELPHINABSTRACT =
sig
  exception Error of Paths.region * string
  exception LeftOverConstraints of (Paths.region * IntSyn.cnstr list) list

  datatype EFLPVar =
      EV of Paths.region * IntSyn.Exp * (((IntSyn.Exp option) * int * (int list)) ref)
                                    (* Y ::= X         for  GX |- X : VX   
				     * The type is saved in an option ref.
				     *)
    | FV of Paths.region * string * (bool ref) * IntSyn.Exp 	 (*     | (F, b, V)        if . |- F : V                 *)
                                                                 (*              and b is true if it is a parameter      *)
    | LV of Paths.region * IntSyn.Block                          (*     | L             if . |- L in W                   *) 
    | PV of Paths.region * string * string                       (*     | PatVar (Delphin -- (name and original name) )  *)

  val abstractPatVarsExp :  Paths.region * DelphinIntermediateSyntax.Exp * DelphinIntermediateSyntax.Types * bool
                            -> DelphinIntermediateSyntax.Exp
  val abstractPatVarsFunList :  (Paths.region *  DelphinIntermediateSyntax.NormalDec * DelphinIntermediateSyntax.Exp) list  
                            ->  (Paths.region *  DelphinIntermediateSyntax.NormalDec * DelphinIntermediateSyntax.Exp) list 

  val addImplicitTypesDec : DelphinIntermediateSyntax.NormalDec * (EFLPVar IntSyn.Ctx) 
                            ->  DelphinIntermediateSyntax.NormalDec
  val addImplicitTypesForm : DelphinIntermediateSyntax.Formula * (EFLPVar IntSyn.Ctx) 
                            ->  DelphinIntermediateSyntax.Formula

  val addSomeVars : DelphinIntermediateSyntax.LFExpWorld 
                    -> DelphinIntermediateSyntax.LFExpWorld

 (* first argument is an optional indication on how far it is to the *global* context
  * it is used in an enhancement in abstracting EVars... optional!
  *)
  val transformDelExp : ((int*int) option) * DelphinIntermediateSyntax.Exp * (EFLPVar IntSyn.Ctx) * bool 
                        -> DelphinIntermediateSyntax.Exp * (EFLPVar IntSyn.Ctx)
  val collectDelNormalDec : ((int*int) option) * DelphinIntermediateSyntax.NormalDec * (EFLPVar IntSyn.Ctx) * bool 
                            -> (EFLPVar IntSyn.Ctx)
  val collectDelNewDec : ((int*int) option) * DelphinIntermediateSyntax.NewDec * (EFLPVar IntSyn.Ctx) * bool 
                          -> (EFLPVar IntSyn.Ctx)
  val collectDelTypes : ((int*int) option) * DelphinIntermediateSyntax.Types * (EFLPVar IntSyn.Ctx) * bool 
                         -> (EFLPVar IntSyn.Ctx)
  val LFcollectExp : Paths.region * ((int*int) option) * (IntSyn.Exp * IntSyn.Sub) * (EFLPVar IntSyn.Ctx) * bool 
                     -> (EFLPVar IntSyn.Ctx)

end;  (* signature ABSTRACT *)
