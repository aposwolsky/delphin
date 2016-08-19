(* Delphin Elaborator (convert from external to internal syntax) *)
(* Author: Adam Poswolsky *)

signature DELPHIN_ELABORATOR =
  sig
    exception Error of string
    type metaSignature = (string * DelphinApprox.Formula * DelphinIntSyntax.Formula) list  (* for type aliasing *)
    val reset : metaSignature ref -> unit
    val setFilename : string -> unit
    val getFilename : unit -> string

    val convertMeta0 : bool  * DelphinIntSyntax.decCtx * DelphinExtSyntax.Exp
                       -> DelphinIntSyntax.Exp * DelphinIntSyntax.Types

    val convertFormula0 : DelphinIntSyntax.decCtx * DelphinExtSyntax.Formula 
                           -> DelphinApprox.Formula * DelphinIntSyntax.Formula

    val convertFixList0 :   
      bool *  DelphinIntSyntax.decCtx
      * (Paths.region * DelphinExtSyntax.NormalDec * DelphinExtSyntax.Exp) list
      -> DelphinIntSyntax.Exp

    val convertWorld : DelphinExtSyntax.WorldDeclaration -> DelphinIntSyntax.World

    val saveData : unit
          -> string * int * DelphinApprox.Formula StringRedBlackTree.Table * 
             (int * DelphinIntSyntax.Formula) StringRedBlackTree.Table * 
             DelphinIntSyntax.decCtx

    val restoreData : 
          string * int * DelphinApprox.Formula StringRedBlackTree.Table * 
          (int * DelphinIntSyntax.Formula) StringRedBlackTree.Table * 
          DelphinIntSyntax.decCtx
          -> unit


  end