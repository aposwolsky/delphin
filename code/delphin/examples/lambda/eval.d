sig	<exp : type>
	<app : exp -> exp -> exp>
	<lam : (exp -> exp) -> exp> ;

params = .;

(* Interpreter *)
fun eval : <exp> -> <exp> = 
   fn <app E1 E2> => (case (eval <E1>, eval <E2>) of
                      (<lam F>, <V>) => eval <F V>)
    | <lam E> => <lam E> ;


params = <exp> ;

(* Beta Reduction *)
fun evalBeta : <exp> -> <exp> =
   fn <app E1 E2> => (case (evalBeta <E1>, evalBeta <E2>)
                      of (<lam F>, <V>) => evalBeta <F V>
                       | (<U>, <V>) => <app U V>)
    | <lam E> => (case ({<x>} evalBeta <E x>)
                    of {<x>}<E' x> => <lam E'>)
    | <x#> => <x> ;
