(* PLS Lunch Talk
 * October 8th, 2007
 * Adam Poswolsky
 *)

sig <nat : type>
    <z : nat>
    <s : nat -> nat> ;

params = . ;

fun plus : <nat> -> <nat> -> <nat> 
   = fn <z> <N> => <N>
      | <s N> <M> => let 
                       val <R> = plus <N> <M>
                     in
                       <s R>
                     end;

sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp> ;


fun eval : <exp> -> <exp>
   = fn <lam E> => <lam E>
      | <app E1 E2> => let 
	 		val <lam eFun> = eval <E1>
			val <v> = eval <E2>
                       in
			 eval <eFun v>
                       end;

val example1 = case ({<x:nat#>} <s z>)
                 of {<x:nat#>}<F> => <F> ;

val example2 = case ({<x:nat#>} <s x>)
                 of {<x:nat#>}<F> => <F> ;

params = <exp> ;

fun eval : <exp> -> <exp>
   = fn <lam E> => (case ({<x:exp#>} eval <E x>)
		      of ({<x:exp#>} <E' x>) => <lam E'>)
      | <app E1 E2> => (case (eval <E1>, eval <E2>)
                          of (<lam [x] E' x>, <V1>) => eval <E' V1>
                           | (<x:exp#>, <V1>) => <app x V1>)
      | <x:exp#> => <x> ;


fun plus : <nat> -> <nat> -> <nat> 
   = fn <z> <N> => <N>
      | <s N> <M> => let 
                       val <R> = plus <N> <M>
                     in
                       <s R>
                     end;


fun cntvar : <exp> -> <nat>
   = fn <app E1 E2> => plus (cntvar <E1> ) (cntvar <E2>)
      | <lam E> => (case ({<x>} cntvar <E x>)
                       of {<x>}<N> => <N>)
      | <x:exp#> => <s z> ;


sig <fooexp : type>
    <fooapp : fooexp -> fooexp -> fooexp>
    <foolam: (fooexp -> fooexp) -> fooexp>;

params = <fooexp>, <exp> ;

type world = (<x:fooexp#> -> <exp>);
fun convert : world -> <fooexp> -> <exp> 
  = fn W <fooapp E1 E2> => let
		           val <E1'> = convert W <E1>
		           val <E2'> = convert W <E2>
			 in
			   <app E1' E2'>
		 	 end
     | W <foolam E> => (case ({<x:fooexp#>}{<y:exp#>} convert (fn x => <y> | [<e:fooexp#>] e => W e) <E x>)
                         of {<x>}{<y>}<E' y> => <lam E'>)

     | W [<x:fooexp#>] <x> => W x  ;

val example = convert (fn .) <foolam [x:fooexp] fooapp x x> ;
 


sig <eval : exp -> exp -> type> 
    <evlam : ({x:exp} eval x x -> eval (E x) (E' x)) -> eval (lam [x] E x) (lam [x] E' x)> 
    <evbeta1 : (eval E1 (lam [x] E' x)) -> (eval E2 V1) -> (eval (E' V1) V2) -> (eval (app E1 E2) V2)> 
    <evbeta2 : {x} (eval E1 x) -> (eval E2 V1) -> (eval (app E1 E2) (app x V1))> ;

params = <exp>, <eval E V> ;

type worldEval = <E:exp#> -> <V:exp> * <eval E V> ;

fun extendWorld : worldEval -> {<x:exp#>}{<u: eval x x #>} worldEval 
   = fn W => fn {<x>}{<u>} (x => (<x>,<u>))
	      | [<x'>]{<x>}{<u>} (x' => (let
					   val R = W x'
					 in
					    {<x>}{<u>} R
					 end) \x \u ) ;

fun eval0 : worldEval -> <E:exp> -> <V:exp> * <eval E V>
   = fn W <lam E> => (case ({<x:exp#>}{<u:eval x x #>} eval0 ((extendWorld W) \x \u) <E x>)
		      of ({<x:exp#>}{<u:eval x x #>} (<E' x>, <D' x u>)) => (<lam E'>, <evlam D'>))
      | W <app E1 E2> => (case (eval0 W <E1>, eval0 W <E2>)
                          of ((<lam [x] E' x>, <D1>), (<V1>, <D2>)) => 
			 		let 
					   val (<V2>, <D3>) = eval0 W <E' V1>
					in
					   (<V2>, <evbeta1 D1 D2 D3>)
					end
                           | ((<x:exp#>, <D1>), (<V1>, <D2>)) => (<app x V1>, <evbeta2 x D1 D2>))
      | W [<x:exp#>] <x> => W x ;

fun eval : <E:exp> -> <V:exp> * <eval E V> =
    fn <E> => eval0 (fn .) <E> ;
					     
                   