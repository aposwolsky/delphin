(* Counting things inside lambda expressions *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig 	<exp  : type>
	<app  : exp -> exp -> exp>
	<lam  : (exp -> exp) -> exp>;


fun plus : <rational> -> <rational> -> <rational>
 = fn <X> => fn <Y> => <X + Y> ;

(* Count the number of bound variables *)

fun cntvar : <exp> -> <rational> =
 fn [<p:exp#>] <p> => <1>
 | <app E1 E2> => plus (cntvar <E1>) (cntvar <E2>)
 | <lam E> => case ({<p:exp#>} cntvar <E p>) of ({<p>} <N> => <N>) ;

val cntvar'1 = cntvar <lam [x] x>;
val cntvar'2 = cntvar <lam [x] app x x>;
val cntvar'3 = cntvar <app (lam [x] x) (lam [x] x)>;
val cntvar'4 = cntvar <lam [x] lam [y] x>;

(* Count the number of lambda binders *)

fun cntlam : <exp> -> <rational> =
 fn [<x:exp#>] <x> => <0>
 | <app E1 E2> => plus (cntlam <E1>) (cntlam <E2>)
 | <lam E> => case {<p:exp#>} cntlam <E p> of ({<p>}<N> => <N + 1>) ;

val cntlam'1 = cntlam <lam [x] x>;
val cntlam'2 = cntlam <lam [x] app x x>;
val cntlam'3 = cntlam <app (lam [x] x) (lam [x] x)>;
val cntlam'4 = cntlam <lam [x] lam [y] x>;

(* Constructor free programming *)
(* A variation on the count example from above.
	Difference: a and l are dynamically introduced
*)

fun cntvar : <exp> -> <rational> =
 fn [<x#>] <x> => <1>
 | [<a#>] <a E1 E2> => plus (cntvar <E1>) (cntvar <E2>)
 | [<l#>] <l E> => case {<p:exp#>} cntvar <E p> of ({<p>}<N> => <N>) ;



val cntvar'1 = case ({<a  : exp -> exp -> exp>}
                     {<l  : (exp -> exp) -> exp>}
                     (cntvar <l [x] x>))
               of {<a>}{<l>}<N> => <N> ;

val cntvar'2 = case ({<a  : exp -> exp -> exp>}
                     {<l  : (exp -> exp) -> exp>}
                     (cntvar <l [x] a x x>))
               of {<a>}{<l>}<N> => <N> ;


val cntvar'3 = case ({<a  : exp -> exp -> exp>}
                     {<l  : (exp -> exp) -> exp>}
                     (cntvar <a (l [x] x) (l [x] x)>))
               of {<a>}{<l>}<N> => <N> ;


val cntvar'4 = case ({<a  : exp -> exp -> exp>}
                     {<l  : (exp -> exp) -> exp>}
                     (cntvar <l [x] l [y] x>))
               of {<a>}{<l>}<N> => <N> ;
