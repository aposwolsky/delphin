(* Delphin Elaborator (convert from external to internal syntax) *)
(* Author: Adam Poswolsky *)

signature DELPHIN_ELABORATOR =
  sig
    exception Error of string
    type metaSignature = (string * DelphinApprox.Formula * DelphinIntSyntax.Formula) list  (* for type aliasing *)
    val reset : metaSignature ref -> unit
    val setFilename : string -> unit
    val getFilename : unit -> string

    val convertMeta0 : bool * (DelphinIntSyntax.Dec IntSyn.Ctx) * DelphinExtSyntax.Exp
                       -> DelphinIntSyntax.Exp * DelphinIntSyntax.Types

    val convertFormula0 : (DelphinIntSyntax.Dec IntSyn.Ctx) * DelphinExtSyntax.Formula 
                           -> DelphinApprox.Formula * DelphinIntSyntax.Formula

    val convertFixList0 :   
      bool * (DelphinIntSyntax.Dec IntSyn.Ctx)
      * (Paths.region * DelphinExtSyntax.NormalDec * DelphinExtSyntax.Exp) list
      -> DelphinIntSyntax.Exp

    val saveData : unit
          -> string * int * DelphinApprox.Formula StringRedBlackTree.Table * 
             (int * DelphinIntSyntax.Formula) StringRedBlackTree.Table * 
             DelphinIntSyntax.Dec IntSyn.Ctx

    val restoreData : 
          string * int * DelphinApprox.Formula StringRedBlackTree.Table * 
          (int * DelphinIntSyntax.Formula) StringRedBlackTree.Table * 
          DelphinIntSyntax.Dec IntSyn.Ctx
          -> unit


  end