(* Sample arithmetical functions *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<nat : type>
	<z : nat>
	<s : nat -> nat>;

fun plus : <nat> -> <nat> -> <nat> =
 fn <z> => (fn <Y> => <Y>)
 | <s X> => (fn <Y> => <s> @ (plus <X> <Y>)) ;

val p0 = plus <s (s z)> <s (s z)>;
val p1 = plus <s (s (s z))> <s (s z)> ;
val p2 = plus <s (s (s z))> <s (s (s (s z)))> ;

fun mult : <nat> -> <nat> -> <nat> =
 fn <z> => (fn <Y> => <z>)
 | <s X> => (fn <Y> => plus (mult <X> <Y>) <Y>);

val m0 = mult <s (s z)> <s (s z)>;
val m1 = mult <s (s (s z))> <s (s z)> ;
val m2 = mult <s (s (s z))> <s (s (s (s z)))> ;

fun factorial : <nat> -> <nat> =
 fn <z> => <s z>
 | <s X> => mult <s X> (factorial <X>) ;

val f1 = factorial <s z> ;
val f2 = factorial <s (s z)> ;
val f3 = factorial <s (s (s z))> ;
val f4 = factorial <s (s (s (s z)))> ;
val f5 = factorial <s (s (s (s (s z))))> ;
val f6 = factorial <s (s (s (s (s (s z)))))> ;
(* f7 = factorial <s (s (s (s (s (s (s z))))))> ; *)

fun ex : <nat> -> <nat> -> <nat> =
 fn <X> <z>  => <s z>
 | <X> <s Y> =>  mult (ex <X> <Y>) <X> ;

val e0 = ex <s (s z)> <s (s z)>;
val e1 = ex <s (s (s z))> <s (s z)> ;
val e1a = ex <s (s (s z))> <s (s (s (z)))> ;
val e2 = ex <s (s (s z))> <s (s (s (s z)))> ;

	
fun minus : <nat> -> <nat> -> <nat> =
 fn <X> <z> => <X>
 | <z> <s Y> => <z>
 | <s X> <s Y> => minus <X> <Y> ;

val mi0 = minus <s (s z)> <s (s z)>;
val mi1 = minus <s (s (s z))> <s (s z)> ;
val mi2 = minus <s (s (s z))> <s (s (s (s z)))> ;


fun acker : <nat> -> <nat>  -> <nat> =
 fn <z> <Y> => <s Y>
 | <s X> <z> => acker  <X> <s  z>
 | <s X> <s Y> => acker  <X> (acker  <s  X> <Y>) ;

val a0 = acker <s (s z)> <s (s z)>;
val a1 : <nat>
   = acker <s (s (s z))> <s (s z)> ;
val a2 : <nat>
   = acker <s (s (s z))> <s (s (s (s z)))> ;

(* Conversion to the built-in rational numbers *)

fun add   = fn <X> => fn <Y> => <X + Y> ;

fun nat2rat : <nat> -> <rational> =
        fn <z> => <0>
 	| <s X> => add (nat2rat <X>) <1>;

val ratf1 : <rational>
          = nat2rat (f1) ;

val ratf2 : <rational>
          = nat2rat (f2) ;

val ratf3 : <rational>
          = nat2rat (f3) ;

val ratf4 : <rational>
          = nat2rat (f4) ;

val ratf5 : <rational>
          = nat2rat (f5) ;

val ratf6 : <rational>
          = nat2rat (f6) ;

val ratacker0 : <rational>
          = nat2rat (a0) ;

val ratacker1: <rational>
          = nat2rat (a1) ;

val ratacker2: <rational>
          = nat2rat (a2) ;
