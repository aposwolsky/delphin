(* Natural Numbers *)
sig <nat : type>
    <z : nat>
    <s : nat -> nat> ;

(* Expressions *)
sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp> ;

(* Formulas *)
sig <o : type> 
    <ar : o -> o -> o> %infix right 10 ;

(* Natural Deduction *)
sig <nd : o -> type>
    <impi : (nd A -> nd B) -> nd (A ar B)> 
    <impe : nd (A ar B) -> nd A -> nd B> ;

(* Addition *)
fun plus : <nat> -> <nat> -> <nat> = 
   fn <z> <M> => <M>
    | <s N> <M> => let 
		      val <x> = plus <N> <M>
                    in 
	 	       <s x>
		    end;

(* Interpreter *)
fun eval : <exp> -> <exp> = 
   fn <app E1 E2> => (case (eval <E1>, eval <E2>) of
                      (<lam F>, <V>) => eval <F V>)
    | <lam E> => <lam E> ;


(* Beta Reduction *)
fun evalBeta : <exp> -> <exp> =
   fn <app E1 E2> => (case (evalBeta <E1>, evalBeta <E2>)
                      of (<lam F>, <V>) => evalBeta <F V>
                       | [<x:exp#>](<x>, <V>) => <app x V>)
    | <lam E> => (case ({<x>} evalBeta <E x>)
                    of {<x>}<E' x> => <lam E'>)
    | [<x:exp#>] <x> => <x> ;


(* Variable Counting *)
fun cntvar  : <exp> -> <nat>
 = fn <app E E3>     =>  plus (cntvar <E>) (cntvar <E3>)
    | <lam E>        =>  (case ( {<x>} cntvar <E x>)
                            of  ({<x>} <N>)  => <N>)
    | [<x:exp#>] <x> => <s z>;

(* Lemma 1 is over any type A, tau and sigma,
 * but we just show it for one example.
 *)
fun lemma1-1 : ({<x:exp#>} (<exp> -> <nat>))  -> (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) 
 = fn u1 u2 => {<x:exp#>} (u1 \x) (u2 \x) ;

fun lemma1-2 : (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) -> ({<x:exp#>} (<exp> -> <nat>))
 = fn u1 => fn {<x:exp#>} ((E \x) => (u1 E) \x) ;

fun lemma1-3 : ({<x:exp#>} (<exp> * <nat>))  -> (({<x:exp#>}<exp>) * {<x:exp#>}<nat>) 
 = fn {<x>}((u1 \x), (u2 \x)) => (u1, u2) ;

fun lemma1-4 : (({<x:exp#>}<exp>) * {<x:exp#>}<nat>) -> ({<x:exp#>} (<exp> * <nat>))
 = fn (u1, u2) => {<x:exp#>} ((u1 \x), (u2 \x));

val exampleF1 : ({<x:exp#>} (<exp> -> <nat>)) = fn {<x>} (<x> => <s z>)
                                                 | {<x>} (<_> => <z>) ;
val exampleF2 : (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) = fn {<x>} <x> => {<x>} <s z> 
                                                          | {<x>} <_> => {<x>} <z> ;
val test1 = {<x>} (exampleF1 \x) <x> ;
val test1' = {<x>} (exampleF1 \x) <lam [x] x> ;
val test2 = exampleF2 ({<x>} <x>) ;
val test2' = exampleF2 ({<x>} <lam [x] x>) ;


val test3 = {<x>} ((lemma1-2 exampleF2) \x) <x> ;
val test3' = {<x>} ((lemma1-2 exampleF2) \x) <lam [x] x> ;
val test4 = (lemma1-1 exampleF1) ({<x>} <x>) ;
val test4' = (lemma1-1 exampleF1) ({<x>} <lam [x] x>) ;



(* Combinators *)
sig <comb : o -> type> 
    <K : comb (A ar B ar A)>
    <S : comb ((A ar B ar C) ar (A ar B) ar A ar C) > 
    <MP : comb (A ar B) -> comb A -> comb B> ;


fun ba : <comb A -> comb B> -> <comb (A ar B)> 
  = fn <F> => <MP (MP S K) (K : comb (A ar A ar A))>
     | <[x] MP (D1 x) (D2 x)> =>   (case ((ba <D1>), (ba <D2>))
	                                 of (<D1'>,<D2'>) => <MP (MP S D1') D2'>)
     | <[x] U> => <MP K U> ;

type convParamFun = (<A:o> -> <D: nd A#> -> <comb A>)

fun convert : convParamFun  -> <D:nd A> -> <comb A> =
      fn W <impi D'> => 
	    (case ({<d>}{<u>} 
		let
		    fun W' = fn <_> d => <u>
			      | ([<B'>][<d'>] {<d>}{<u>} (<B'> d' => 
						         (let val R = W <B'> d' in {<d>}{<u>}R end) \d \u))
							  \d \u 
	        in					 
	             convert W' <D' d>
		end)
	      of ({<d>}{<u>} <D'' u>) => ba <D''>)
       | W <impe D1 D2> => (case ((convert W <D1>), (convert W <D2>))
	                                      of (<U1>,<U2>) => <MP U1 U2>) 
	     
       | [<x:nd A#>] W <x> => W <A> x;

(* Convert simplified using Delphin "with" construct *)
fun convert : convParamFun  -> <D:nd A> -> <comb A> =
      fn W <impi D'> => 
	    (case ({<d>}{<u>} convert (W with <_> d => <u>) <D' d>)
	      of ({<d>}{<u>} <D'' u>) => ba <D''>)
       | W <impe D1 D2> => (case ((convert W <D1>), (convert W <D2>))
	                                      of (<U1>,<U2>) => <MP U1 U2>) 
	     
       | [<x:nd A#>] W <x> => W <A> x;

val testConvert = {<A>} convert (fn .)  <impi [x:nd A] x> ;
  (* evaluates to  {<A : o#>} <MP (MP S K) K> *)
val testConvert2 = {<A>}{<B>} convert (fn .) < impi [x:nd (A ar B)] impi [y: nd A] impe x y> ;
  (* evaluates to  {<A : o#>} {<B : o#>} <MP (MP S K) K> *)


