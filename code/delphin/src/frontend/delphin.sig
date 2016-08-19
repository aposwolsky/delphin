(* Delphin Frontend *)

signature  DELPHIN =
sig
  val version : string
  val debug : bool ref
  val parseDebug : bool ref
  val pageWidth : int ref
  val smartInj : bool ref
  val loadFile : string -> unit    
  val top : unit ->  unit
  val changePath : string -> unit
  val resetMetaSig : unit -> unit

  val top' :  (DelphinIntSyntax.Dec IntSyn.Ctx) ref  *
              (DelphinIntSyntax.Sub) ref
              -> unit
end
