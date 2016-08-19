(* Parallel reduction *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<exp : type>
	<app : exp -> exp -> exp>
	<lam : (exp -> exp) -> exp>;

params = <exp> ;

fun par : <exp> -> <exp> =
 fn <x#> => <x>
 | <app E1 E2> =>  par' <E1> (par <E2>)
 | <lam E1>    =>  case {<x:exp#>} par <E1 x> of ({<x>}<F1 x> => <lam F1>)

and par' : <exp> -> <exp> -> <exp> =
 fn <x#> => (fn <E3> => <app x E3>)
 | <app E1 E2> => (fn <E2'> => <app> @ (par' <E1> (par <E2>)) @ <E2'>)
 | <lam E1> => (fn <E2'> =>  
     case {<x:exp#>} par <E1 x> of ({<x>}<F1 x> => <F1 E2'>)) ;


val p1  = par <lam [x] x>;
val p2  = par <lam [x] app x x>;
val p3  = par <app (lam [x] x) (lam [x] x)>;
val p4  = par <lam [x] lam [y] x>;

