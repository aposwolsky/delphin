(* Advanced Variable Counting with no constants in signature) *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig <nat : type> <z : nat> <s : nat -> nat> ;
sig <exp' : type>;

sig     <dummy : (exp' -> exp') -> type> ;
	(* this is necessary just to state that 
	 * we want the subordination relation to allow exp'
	 * to occur in exp'.
	 * We do not actually use "dummy" anywhere.
	 * And perhaps other syntax can be developed.
	 *)

params = <exp'>;

fun plus : {<app' : exp' -> exp' -> exp'>} {<lam' : (exp' -> exp') -> exp'>}
	    <nat> -> <nat> -> <nat>
	   = {<app'>}{<lam'>}
              fn <z> <N> => <N>
               | <s N> <M> => <s> @ ((plus \app' \lam') <N> <M>) ;


fun cntvar' : {<app' : exp' -> exp' -> exp'>} {<lam' : (exp' -> exp') -> exp'>}
             <exp'> -> <nat>
             = {<app'>}{<lam'>}
             fn <app' E1 E2> => (plus \app' \lam') ((cntvar' \app' \lam') <E1>) ((cntvar' \app' \lam') <E2>)
              | <lam' E> => (case ({<x:exp'>} ((cntvar' \app' \lam') <E x>))
                             of {<x:exp'>}<N> => <N>)
              | [<e:exp'#>]<e> => <s z>;

val result = {<app'>}{<lam'>} (cntvar' \app' \lam') <lam' [x] (app' x x)> ; 
(*
val it : {<app' : {x:exp'} {x1:exp'} exp'#>} {<lam' : {x:{x:exp'} exp'} exp'#>} <nat>
*)
