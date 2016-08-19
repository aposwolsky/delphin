(* Tabled Syntax *)
(* Author: Brigitte Pientka *)

signature TABLEDSYN =
sig

  (*! structure IntSyn : INTSYN !*)

  exception Error of string

  val reset : unit -> unit
  val installTabled : IntSyn.cid  -> unit 
  val tabledLookup : IntSyn.cid -> bool

end;  (* signature TABLEDSYN *)
