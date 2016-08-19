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
 
params = <exp>, <eval E# V#> ;

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