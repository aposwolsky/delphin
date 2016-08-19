(* The Parser *)

signature PARSE =
sig
  val fparse : string * string -> DelphinExtSyntax.DelphinProgram
  val sparse : unit -> DelphinExtSyntax.DelphinProgram
    

end  (* signature PARSE *)
