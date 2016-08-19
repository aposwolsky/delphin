(* Interface for error reporting  syntax *)

signature INTERFACE =
sig

  type pos
  val noPos : pos
  val lineNum : pos ref
  val linePos : pos list ref

  val fnameOpt : string option ref
  val reset : unit -> unit
  val toString : pos -> string
  val error :  string * pos * pos -> unit
  val intToPos: int -> pos
  val incLineNum: int -> unit
  val add' : (pos * int) -> pos
    
  type arg
  val nothing : arg

  val saveData : unit -> string option * int * int list
  val restoreData : string option * int * int list -> unit

end  (* signature INTERFACE *)

