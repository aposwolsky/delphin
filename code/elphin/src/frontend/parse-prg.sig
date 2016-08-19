(* The Parser *)

signature PARSE =
sig
  val fparse : string -> NablaExtSyntax.NablaProgram
  val sparse : unit -> NablaExtSyntax.NablaProgram
    

end  (* signature PARSE *)
