(* Translation from lambda calculus into combinator calculus *)
(* Simply-typed Version *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<comb : type>
	<k : comb>
	<s : comb>
	<mp : comb -> comb -> comb>;

sig	<exp : type>
	<lam : (exp -> exp) -> exp>
	<app : exp -> exp -> exp>;

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

fun c2d-Payload : <exp> -> <comb> =
   fn [<x:comb -> exp #>] <x C> => <C>
   | <app E1 E2> => <mp> @ (c2d-Payload <E1>) @ (c2d-Payload <E2>)
   | <lam E> => case {<c:comb#>}{<x:comb -> exp #>} c2d-Payload <E (x c)> of
                 ({<c>}{<x>}<C c> => ded <C>) ;

val c2d'1  = c2d-Payload <lam [x] x>;
val c2d'2  = c2d-Payload <lam [x] app x x>;
val c2d'3  = c2d-Payload <app (lam [x] x) (lam [x] x)>;
val c2d'4  = c2d-Payload <lam [x] lam [y] x>;



(* ******************************************* *)
(* Conversion using delphin function saving 
 * relationship between parameters *)
(* ******************************************* *)

type world = <x:exp#> -> <comb>

fun extend : world -> {<c:comb#>}{<x:exp#>} world =
   fn W => fn {<c>}{<x>} (x => <c>)
            | [<x'#>] {<c>}{<x>} (x' => 
	                          (let val R = W x'
                                   in {<c>}{<x>} R
                                  end) \c \x);

fun c2d : world -> <exp> -> <comb> =
   fn W [<x : exp#>] <x> => W x
    | W <app E1 E2> => <mp> @ (c2d W <E1>) @ (c2d W <E2>)
    | W <lam E> => case {<c:comb#>}{<x:exp#>} c2d ((extend W) \c \x) <E x> of
                 ({<c>}{<x>}<C c> => ded <C>) ;

val c2d'1  = c2d (fn .) <lam [x] x>;
val c2d'2  = c2d (fn .) <lam [x] app x x>;
val c2d'3  = c2d (fn .) <app (lam [x] x) (lam [x] x)>;
val c2d'4  = c2d (fn .) <lam [x] lam [y] x>;
