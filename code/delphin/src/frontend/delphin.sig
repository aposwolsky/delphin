(* Delphin Frontend *)

signature  DELPHIN =
sig
  val version : string
  val debug : bool ref
  val enableCoverage : bool ref
  val enableTermination : bool ref
  val stopOnWarning : bool ref
  val parseDebug : bool ref
  val pageWidth : int ref
  val smartInj : bool ref
  val printPatternVars : bool ref
  val printImplicit : bool ref
  val doubleCheck : bool ref
  val loadFile : string -> unit    
  val top : unit ->  unit
  val changePath : string -> unit
  val resetMetaSigAndWorld : unit -> unit

  val initTop' : unit -> unit
  val top' :  (DelphinIntSyntax.decCtx) ref  *
              (DelphinIntSyntax.Sub) ref
              -> unit
end
