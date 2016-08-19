(* Nabla Elaborator (convert from external to internal syntax) *)
(* Author: Adam Poswolsky *)

signature NABLA_ELABORATOR =
  sig
    exception NotImplemented of string
    exception Error of string

    val reset : unit -> unit
    val setFilename : string -> unit
    val getFilename : unit -> string

    val lfdecTokens : NablaExtSyntax.LFDec -> (Lexer.Token * Paths.region) list

    val convertFix0 : (NablaIntSyntax.Dec IntSyn.Ctx) * NablaExtSyntax.MetaTerm 
                       -> (NablaIntSyntax.Dec IntSyn.Ctx) * NablaIntSyntax.Exp

    val convertFixList0 :(NablaIntSyntax.Dec IntSyn.Ctx) * 
                         ((Paths.region * NablaExtSyntax.MetaDec * NablaExtSyntax.MetaTerm) list)
                       -> (NablaIntSyntax.Dec IntSyn.Ctx) * NablaIntSyntax.Exp

    val convertMeta0 : (NablaIntSyntax.Dec IntSyn.Ctx) * NablaExtSyntax.MetaTerm 
                       -> NablaIntSyntax.Exp

    val renameVarsFixList0 : (Paths.region * NablaExtSyntax.MetaDec * NablaExtSyntax.MetaTerm) list
                           -> (Paths.region * NablaExtSyntax.MetaDec * NablaExtSyntax.MetaTerm) list

    val renameVars0 : NablaExtSyntax.MetaTerm -> NablaExtSyntax.MetaTerm
  end