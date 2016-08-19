(* Sample Boolean functions *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<bool : type>
	<true : bool>
	<false : bool>;

params = .;

fun not : <bool> -> <bool> =
 fn <true> => <false>
 | <false> => <true> ;

val n1 = not <true> ;
val n2 = not <false> ;
 
fun or : <bool> -> <bool> -> <bool> =
 fn <true> <true> => <true>
 | <true> <false> => <true>
 | <false> <true> => <true>
 | <false> <false> => <false> ;

val o1 = or <true> <true> ;
val o2 = or <false> <true> ;
val o3 = or <true> <false> ;
val o4 = or <false> <false> ;

fun con : <bool> -> <bool> -> <bool> =
 fn <true> <B> => <B>
 | <false> <B> => <false>;

val a1 = con <true> <true> ;
val a2 = con <false> <true> ;
val a3 = con <true> <false> ;
val a4 = con <false> <false> ;

sig	<nat : type>
	<z : nat>
	<s : nat -> nat> ;

fun gt : <nat> -> <bool> =
 fn <z> => <false>
 | <s X> => <true> ;

val g0 = gt <z> ;
val g1 = gt <s (s z)> ;
val g2 = gt <s (s (s z))> ;
val g3 = gt <s (s (s (s z)))> ;
