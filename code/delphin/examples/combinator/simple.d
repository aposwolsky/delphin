(* Translation from lambda calculus into combinator calculus *)
(* Simply-typed Version *)
(* Using delphin function saving 
 * relationship between parameters *)

(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<comb : type>
	<k : comb>
	<s : comb>
	<mp : comb -> comb -> comb>;

sig	<exp : type>
	<lam : (exp -> exp) -> exp>
	<app : exp -> exp -> exp>;

params = <comb>, <exp> ;

fun ded : <comb -> comb> -> <comb> =
   fn [<c:comb#>] <[x] c> => <c>
   | <[x] x> => <mp (mp s k) k>
   | <[x] k> => <mp k k>
   | <[x] s> => <mp k s>
   | <[x] (mp (C1 x) (C2 x))> =>
       <mp> @ (<mp> @ <s> @ (ded <C1>)) @ (ded <C2>) ;

type world = <x:exp#> -> <comb>

fun c2d : world -> <exp> -> <comb> =
   fn W <x#> => W <x>
    | W <app E1 E2> => <mp> @ (c2d W <E1>) @ (c2d W <E2>)
    | W <lam E> => case {<c:comb#>}{<x:exp#>} c2d (W with <x> => <c>) <E x> of
                 ({<c>}{<x>}<C c> => ded <C>) ;

val c2d'1  = c2d (fn .) <lam [x] x>;
val c2d'2  = c2d (fn .) <lam [x] app x x>;
val c2d'3  = c2d (fn .) <app (lam [x] x) (lam [x] x)>;
val c2d'4  = c2d (fn .) <lam [x] lam [y] x>;
