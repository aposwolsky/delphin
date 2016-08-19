(* PLS Lunch Talk
 * October 8th, 2007
 * Adam Poswolsky
 *)

sig <nat : type>
    <z : nat>
    <s : nat -> nat> ;

sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp> ;

sig <fooexp : type>
    <fooapp : fooexp -> fooexp -> fooexp>
    <foolam: (fooexp -> fooexp) -> fooexp>;

sig <eval : exp -> exp -> type> 
    <evlam : ({x:exp} eval x x -> eval (E x) (E' x)) -> eval (lam [x] E x) (lam [x] E' x)> 
    <evbeta1 : (eval E1 (lam [x] E' x)) -> (eval E2 V1) -> (eval (E' V1) V2) -> (eval (app E1 E2) V2)> 
    <evbeta2 : {x} (eval E1 x) -> (eval E2 V1) -> (eval (app E1 E2) (app x V1))> ;

params = . ;
fun eval : <exp> -> <exp>
   = fn <lam E> => <lam E>
      | <app E1 E2> => let 
	 		val <lam eFun> = eval <E1>
			val <v> = eval <E2>
                       in
			 eval <eFun v>
                       end;


params = <exp>, <fooexp> ;

fun plus : <nat> -> <nat> -> <nat> 
   = fn <z> <N> => <N>
      | <s N> <M> => let 
                       val <R> = plus <N> <M>
                     in
                       <s R>
                     end;




fun eval : <exp> -> <exp>
   = fn <lam E> => (case ({<x:exp#>} eval <E x>)
		      of ({<x:exp#>} <E' x>) => <lam E'>)
      | <app E1 E2> => (case (eval <E1>, eval <E2>)
                          of (<lam [x] E' x>, <V1>) => eval <E' V1>
                           | (<x:exp#>, <V1>) => <app x V1>)
      | <x:exp#> => <x> ;



fun cntvar : <exp> -> <nat>
   = fn <app E1 E2> => plus (cntvar <E1> ) (cntvar <E2>)
      | <lam E> => (case ({<x>} cntvar <E x>)
                       of {<x>}<N> => <N>)
      | <x:exp#> => <s z> ;



fun convert : (<fooexp#> -> <exp>) -> <fooexp> -> <exp>
    = fn W <fooapp E1 E2> =>
			let val <E1'> = convert W <E1>
			    val <E2'> = convert W <E2>
			in
			   <app E1' E2'>
			end
       | W <foolam E> => (case (
			{<x:fooexp#>}{<y:exp#>} convert 
						(fn <x> => <y>
                                                  | <x':fooexp#> => W <x'>)
						<E x>)
                         of {<x>}{<y>} <E' y> => <lam E'>)
                       

       | W <x:fooexp#> => W <x>;


fun convert : (<fooexp#> -> <exp>) -> <fooexp> -> <exp>
    = fn W <fooapp E1 E2> =>
			let val <E1'> = convert W <E1>
			    val <E2'> = convert W <E2>
			in
			   <app E1' E2'>
			end
       | W <foolam E> => (case (
			{<x:fooexp#>}{<y:exp#>} convert 
						(fn <x> => <y>
                                                  | ([<x'>]{<x>}{<y>} (<x':fooexp#> => (let val R = W <x'> in {<x>}{<y>}R end) \x \y )) \x \y )
						<E x>)
                         of {<x>}{<y>} <E' y> => <lam E'>)
                       

       | W <x:fooexp#> => W <x>;


fun convert : (<fooexp#> -> <exp>) -> <fooexp> -> <exp>
    = fn W <fooapp E1 E2> =>
			let val <E1'> = convert W <E1>
			    val <E2'> = convert W <E2>
			in
			   <app E1' E2'>
			end
       | W <foolam E> => (case ({<x:fooexp#>}{<y:exp#>} convert (W with <x> => <y>) <E x>)
                         of {<x>}{<y>} <E' y> => <lam E'>)
                       

       | W <x:fooexp#> => W <x>;


type world = (<fooexp#> -> <exp>);
fun convert : world -> <fooexp> -> <exp> 
  = fn W <fooapp E1 E2> => let
		           val <E1'> = convert W <E1>
		           val <E2'> = convert W <E2>
			 in
			   <app E1' E2'>
		 	 end
     | W <foolam E> => (case ({<x:fooexp#>}{<y:exp#>} convert (W with <x> => <y>) <E x>)
                         of {<x>}{<y>}<E' y> => <lam E'>)

     | W <x:fooexp#> => W <x>  ;

params = . ;
val example = convert (fn .) <foolam [x:fooexp] fooapp x x> ;
 

params = <exp>, <eval E V> ;

type worldEval = <E:exp#> -> <V:exp> * <eval E V> ;

fun eval0 : worldEval -> <E:exp> -> <V:exp> * <eval E V>
   = fn W <lam E> => (case ({<x:exp#>}{<u:eval x x #>} eval0 (W with <x> => (<x>, <u>)) <E x>)
		      of ({<x:exp#>}{<u:eval x x #>} (<E' x>, <D' x u>)) => (<lam E'>, <evlam D'>))
      | W <app E1 E2> => (case (eval0 W <E1>, eval0 W <E2>)
                          of ((<lam [x] E' x>, <D1>), (<V1>, <D2>)) => 
			 		let 
					   val (<V2>, <D3>) = eval0 W <E' V1>
					in
					   (<V2>, <evbeta1 D1 D2 D3>)
					end
                           | ((<x:exp#>, <D1>), (<V1>, <D2>)) => (<app x V1>, <evbeta2 x D1 D2>))
      | W <x:exp#> => W <x> ;

params = . ;
fun eval : <E:exp> -> <V:exp> * <eval E V> =
    fn <E> => eval0 (fn .) <E> ;
					     



(* Formulas *)
sig <o : type> 
    <ar : o -> o -> o> %infix right 10 ;

(* Natural Deduction *)
sig <nd : o -> type>
    <impi : (nd A -> nd B) -> nd (A ar B)> 
    <impe : nd (A ar B) -> nd A -> nd B> ;

(* Combinators *)
sig <comb : o -> type> 
    <K : comb (A ar B ar A)>
    <S : comb ((A ar B ar C) ar (A ar B) ar A ar C) > 
    <MP : comb (A ar B) -> comb A -> comb B> ;

type convParamFun = (<A:o> -> <nd A#> -> <comb A>)

fun ba : <comb A -> comb B> -> <comb (A ar B)> 
  = fn <F> => <MP (MP S K) (K : comb (A ar A ar A))>
     | <[x] MP (D1 x) (D2 x)> =>   (case ((ba <D1>), (ba <D2>))
	                                 of (<D1'>,<D2'>) => <MP (MP S D1') D2'>)
     | <[x] U> => <MP K U> ;


fun convert : convParamFun  -> <D:nd A> -> <comb A> =
      fn W <impi D'> => (case ({<d>}{<u>} convert (W with <_> <d> => <u>) <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <D''>) 
       | W <impe D1 D2> => (case ((convert W <D1>), (convert W <D2>))
	                                      of (<U1>,<U2>) => <MP U1 U2>) 
	     
       | W <x#> => W <A> <x>;

val testConvert1 = {<A>}{<B>} convert (fn .) <impi [u:nd A] impi [v:nd B] u> ;
  (* evaluates to  {<A : o#>} {<B : o#>} <MP (MP S (MP K K)) (MP (MP S K) K)> *)
                   
