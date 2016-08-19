(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature NABLAABSTRACT =
sig
  exception Error of string

  val piDepend  : (IntSyn.Dec * IntSyn.Depend) * IntSyn.Exp -> IntSyn.Exp
  val closedDec : IntSyn.Dec IntSyn.Ctx * (IntSyn.Dec * IntSyn.Sub) -> bool
  val closedSub : IntSyn.Dec IntSyn.Ctx * IntSyn.Sub -> bool
  val closedExp : IntSyn.Dec IntSyn.Ctx * (IntSyn.Exp * IntSyn.Sub) -> bool
  val closedCtx : IntSyn.Dec IntSyn.Ctx -> bool

  val abstractDecImp : IntSyn.Exp  -> (int * IntSyn.Exp)
  val abstractDef : (IntSyn.Exp * IntSyn.Exp)
                     -> (int * (IntSyn.Exp * IntSyn.Exp))
  val abstractCtxs : (IntSyn.Dec IntSyn.Ctx) list
                     -> (IntSyn.Dec IntSyn.Ctx) * (IntSyn.Dec IntSyn.Ctx) list


  val checkConstraints : (NablaIntSyntax.Dec IntSyn.Ctx) -> NablaIntSyntax.Exp -> bool
    
  val abstractNabla : (NablaIntSyntax.Dec IntSyn.Ctx) -> NablaIntSyntax.Exp
        -> (NablaIntSyntax.Dec IntSyn.Ctx * NablaIntSyntax.Exp)

  val abstractSpine : IntSyn.Spine * IntSyn.Sub -> (IntSyn.dctx * IntSyn.Spine)

  val hasLFTypeEVars : (NablaIntSyntax.Dec IntSyn.Ctx) list * NablaIntSyntax.Exp -> bool

  val collectEVars : IntSyn.dctx * IntSyn.eclo * IntSyn.Exp list -> IntSyn.Exp list
  val collectEVarsSpine : IntSyn.dctx * (IntSyn.Spine * IntSyn.Sub) * IntSyn.Exp list -> IntSyn.Exp list
                         

  val raiseTerm    : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp
  val raiseType    : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp

  val occursInExp  : int * IntSyn.Exp -> IntSyn.Depend
  val occurs  : int * NablaIntSyntax.Exp -> IntSyn.Depend
  val occurs'  : int option list * NablaIntSyntax.Exp -> IntSyn.Depend


end;  (* signature ABSTRACT *)
