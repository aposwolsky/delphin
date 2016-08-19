(* Advanced Variable Counting *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig <nat : type> <z : nat> <s : nat -> nat> ;
fun plus = fn <z> <N> => <N>
            | <s N> <M> => <s> @ (plus <N> <M>) ;

sig <exp' : type>;

fun cntvar' : {<app' : exp' -> exp' -> exp'>} {<lam' : (exp' -> exp') -> exp'>}
             <exp'> -> <nat>
             = {<app'>}{<lam'>}
             fn <app' E1 E2> => plus ((cntvar' \app' \lam') <E1>) ((cntvar' \app' \lam') <E2>)
              | <lam' E> => (case ({<x:exp'>} ((cntvar' \app' \lam') <E x>))
                             of {<x:exp'>}<N> => <N>)
              | [<e:exp'#>]<e> => <s z>;

val result = {<app'>}{<lam'>} (cntvar' \app' \lam') <lam' [x] (app' x x)> ; 
(*
val it : {<app' : {x:exp'} {x1:exp'} exp'#>} {<lam' : {x:{x:exp'} exp'} exp'#>} <nat>
*)
