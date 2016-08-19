(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

signature PRINT =
sig
  (*! structure IntSyn : INTSYN !*)
  structure Formatter : FORMATTER

  val implicit : bool ref
  val printDepth : int option ref
  val printLength : int option ref

  val formatDec : IntSyn.dctx * IntSyn.Dec -> Formatter.format
  val formatExp : IntSyn.dctx * IntSyn.Exp -> Formatter.format
  val formatSpine : IntSyn.dctx * IntSyn.Spine -> Formatter.format list
  val formatConDec : IntSyn.ConDec -> Formatter.format
  val formatConDecI : IntSyn.ConDec -> Formatter.format
  val formatCnstr : IntSyn.Cnstr -> Formatter.format
  val formatCtx : IntSyn.dctx * IntSyn.dctx -> Formatter.format

  val decToString : IntSyn.dctx * IntSyn.Dec -> string
  val expToString : IntSyn.dctx * IntSyn.Exp -> string
  val conDecToString : IntSyn.ConDec -> string
  val cnstrToString : IntSyn.Cnstr -> string
  val cnstrsToString : IntSyn.cnstr list -> string (* assigns names in contexts *)
  val ctxToString : IntSyn.dctx * IntSyn.dctx -> string

  val evarInstToString : (IntSyn.Exp * string) list -> string
  val evarCnstrsToStringOpt : (IntSyn.Exp * string) list -> string option

  val printSgn : unit -> unit

  val formatExpMarked : (int list) * IntSyn.dctx * IntSyn.Exp -> Formatter.format (* ABP:  the list indicates
										   * variables we want to print
										   * a "#" after..
										   *)


end;  (* signature PRINT *)
