sig	<exp : type>
	<app : exp -> exp -> exp>
	<lam : (exp -> exp) -> exp> ;

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
