(* Debruijn expressions *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<exp  : type>
<app  : exp -> exp -> exp>
<lam  : (exp -> exp) -> exp>

<db   : type>
<v    : rational -> db>
<l    : db -> db>
<a    : db -> db -> db>

db : <exp> -> <rational> -> <db>
   = {{x}} <x M> |--> <N> |--> <v (N + (~ M))> 
   | <app E1 E2> |--> <N> |-->  <a> @ (db <E1> <N>) 
                                    @ (db <E2> <N>)
   | <lam E> |--> <N> |--> {x:rational -> exp} 
        case (db <E (x (N + 1))> <N + 1>) of
            (<F> |--> pop <l F>) ;

dbtrans : <exp> -> <db>
 = <E> |--> db <E> <1> ;

db'1  = dbtrans <lam [x] x> ;
db'2  = dbtrans <lam [x] app x x> ;
db'3  = dbtrans  <app (lam [x] x) (lam [x] x)>;
db'4  = dbtrans  <lam [x] lam [y] x>;
