(* Nabla Frontend *)

signature  NABLA =
sig
  val version : string
  val debug : bool ref
  val loadFile : string -> unit    
  val top : unit ->  unit

  val top' :  (NablaIntSyntax.Dec IntSyn.Ctx) ref  *
              (NablaIntSyntax.Sub) ref
              -> unit
end
