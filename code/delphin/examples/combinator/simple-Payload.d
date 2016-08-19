(* Translation from lambda calculus into combinator calculus *)
(* Simply-typed Version with Payload-carrying parameters *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<comb : type>
	<k : comb>
	<s : comb>
	<mp : comb -> comb -> comb>;

sig	<exp : type>
	<lam : (exp -> exp) -> exp>
	<app : exp -> exp -> exp>;

sig     <dummy : (comb -> exp) -> type> ;
	(* this is necessary just to state that 
	 * we want the subordination relation to allow comb
	 * to occur in exp.
	 * We do not actually use "dummy" anywhere.
	 * And perhaps other syntax can be developed.
	 *)

params = <comb>, <comb -> exp> ;

fun ded : <comb -> comb> -> <comb> =
   fn [<c:comb#>] <[x] c> => <c>
   | <[x] x> => <mp (mp s k) k>
   | <[x] k> => <mp k k>
   | <[x] s> => <mp k s>
   | <[x] (mp (C1 x) (C2 x))> =>
       <mp> @ (<mp> @ <s> @ (ded <C1>)) @ (ded <C2>) ;

val d1 : <comb> = ded <[x:comb] mp k x> ;
val d2 :<comb -> comb> = case ({<c>} <mp k c>) of {<c>}<C c> => <C>;

(* ******************************************* *)
(* Conversion using payload-carrying parameters *)
(* ******************************************* *)

fun e2c : <exp> -> <comb> =
   fn [<x:comb -> exp #>] <x C> => <C>
   | <app E1 E2> => <mp> @ (e2c <E1>) @ (e2c <E2>)
   | <lam E> => case {<c:comb#>}{<x:comb -> exp #>} e2c <E (x c)> of
                 ({<c>}{<x>}<C c> => ded <C>) ;

val e2c'1  = e2c <lam [x] x>;
val e2c'2  = e2c <lam [x] app x x>;
val e2c'3  = e2c <app (lam [x] x) (lam [x] x)>;
val e2c'4  = e2c <lam [x] lam [y] x>;