(* Debruijn expressions *)
(* Author: Adam Poswolsky, Carsten Schuermann *)
(* This shows how to transform simply-typed HOAS terms into
 * a debruijn-representation utilizing "payload-carrying" parameters.
 * NOTE:  This example does not use any "parameter functions"
 * The example in debruijn-advanced.d is better and we use dependent types
 * to prove the transformation is an isomorphism.
 *)

sig	<exp  : type>
	<app  : exp -> exp -> exp>
	<lam  : (exp -> exp) -> exp>;

sig	<db   : type>
	<v    : rational -> db>
	<l    : db -> db>
	<a    : db -> db -> db>;

sig     <dummy : (rational -> exp) -> type> ;
	(* this is necessary just to state that 
	 * we want the subordination relation to allow rational
	 * to occur in exp.
	 * We do not actually use "dummy" anywhere.
	 * And perhaps other syntax can be developed.
	 *)

(* ******************************************* *)
(* Conversion using payload-carrying parameters *)
(* ******************************************* *)

params = <rational -> exp> ;

fun db-Payload : <exp> -> <rational> -> <db> =
   fn <x# M> => (fn <N> => <v (N + (~ M))> )
   | <app E1 E2>   => (fn <N> =>  <a> @ (db-Payload <E1> <N>) 
                                    @ (db-Payload <E2> <N>))
   | <lam E> => (fn <N> =>  
        case {<x:rational -> exp #>} (db-Payload <E (x (N + 1))> <N + 1>) of
            ({<x>}<F> => <l F>)) ;

fun db-Payload-trans : <exp> -> <db> =
 fn <E> => db-Payload <E> <1> ;

val db'1  = db-Payload-trans <lam [x] x> ;
val db'2  = db-Payload-trans <lam [x] app x x> ;
val db'3  = db-Payload-trans  <app (lam [x] x) (lam [x] x)>;
val db'4  = db-Payload-trans  <lam [x] lam [y] x>;