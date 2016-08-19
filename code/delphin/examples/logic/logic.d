(* Sample programs related to first-order logic *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<o : type>
	<i : type>
	<eq : i -> i -> o>
	<imp : o -> o -> o>
	<forall : (i -> o) -> o>;

fun plus : <rational> -> <rational> -> <rational> =
 fn <X> => fn <Y> => <X + Y> ;

fun cnteq : <o> -> <rational> =
 fn <eq X Y>   => <1>
 | <imp F1 F2> => plus (cnteq <F1>) (cnteq <F2>)
 | <forall F>  => case {<t:i#>} (cnteq <F t>) of
                        ({<t>}<N> => <N>) ;


val c1 = cnteq <forall [x] eq x x> ;
val c2 = cnteq <forall [x] forall [y] imp (eq x y) (eq y x)> ;
val c3 = cnteq <forall [x] forall [y] forall [z]
              imp (eq x y) (imp (eq y z) (eq x z))> ;


