(* Circuits example *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<pin : type> 
	<zero : pin>
	<one : pin>;

sig	<circuit : type>
	<newpin : (pin -> circuit) -> circuit>
	<compose : circuit -> circuit -> circuit>
	<andgate : pin -> pin -> pin -> circuit>
	<nandgate : pin -> pin -> pin -> circuit>
	<notgate : pin -> pin -> circuit>;

params = <pin>;

fun add  = fn <X> => fn <Y> => <X + Y> ;
fun mult  = fn <X> => fn <Y> => <X * Y> ;

fun count : <circuit> -> <rational> =
  fn <andgate P Q R> => <1> 
  | <nandgate P Q R>  => <1> 
  | <notgate P R> => <1>  
  | <compose C D> => add (count <C>) (count <D>) 
  | <newpin C> => case {<p:pin #>} count <C p> 
                     of ({<p>}<N> => <N>) ;

val flipflop : <circuit>
   = <newpin [x] newpin [y] newpin [p] newpin [q] 
	    compose (nandgate x q p) (nandgate p y q) > ;

val query1 = count flipflop;

fun nandify : <circuit> -> <circuit> =
 fn <andgate P Q R> => 
     <newpin [x] compose (nandgate P Q x) (nandgate x x R)>
 | <nandgate P Q R> => <nandgate P Q R>
 | <notgate P R> => <nandgate P P R>
 | <compose C D> => 
     <compose> @ (nandify <C>) @ (nandify <D>)
 | <newpin C> =>
      case {<p:pin #>} nandify <C p> 
         of ({<p>}<D p> => <newpin D>) ;

val flipflop2 = <newpin [x] newpin [y] newpin [p] newpin [q] 
	       compose (newpin [n] compose (andgate x q n) (notgate n p)) 
	               (newpin [n] compose (andgate p y n) (notgate n q))> ;

val query2 = nandify flipflop;

val query3 = nandify flipflop2;

sig	<bool : type>
	<true : bool>
	<false : bool>;

fun not : <bool> -> <bool> =
 fn <true> => <false>
 | <false> => <true> ;

fun or : <bool> -> <bool> -> <bool> =
 fn <true>  <true> => <true>
 | <true>   <false> => <true>
 | <false>  <true> => <true>
 | <false>  <false> => <false> ;

fun conj: <bool> -> <bool> -> <bool> =
 fn <true> <B> => <B>
 | <false> <B> => <false> ;

fun nandfree : <circuit> -> <bool>  =
 fn <compose C1 C2> => conj (nandfree <C1>) (nandfree <C2>)
 | <andgate P1 P2 P3> => <true>
 | <nandgate P1 P2 P3> => <false>
 | <notgate P1 P2> => <true>  
 | <newpin C> => case {<q:pin #>}(nandfree <C q>) of 
                      ({<q:pin #>}<B> => <B>) ;

val nf1 : <bool>
 = nandfree flipflop ;

val nf2 : <bool>
 = nandfree flipflop2 ;
params = .;

fun sat : <circuit> -> <rational> =
 fn <andgate one one one> => <1>
 | <andgate one zero zero> => <1>
 | <andgate zero one zero> => <1>
 | <andgate zero zero zero> => <1>

 | <andgate one one zero> => <0>
 | <andgate one zero one> => <0>
 | <andgate zero one one> => <0>
 | <andgate zero zero one> => <0>
  
 | <nandgate one one zero> => <1>
 | <nandgate one zero one> => <1>
 | <nandgate zero one one> => <1>
 | <nandgate zero zero one> => <1>

 | <nandgate one one one> => <0>
 | <nandgate one zero zero> => <0>
 | <nandgate zero one zero> => <0>
 | <nandgate zero zero zero> => <0>

 | <notgate one zero> => <1>
 | <notgate zero one> => <1> 
 | <notgate one one> => <0>
 | <notgate zero zero> => <0> 

 | <compose C1 C2> => mult (sat <C1>) (sat <C2>)
 | <newpin C> => add (sat <C zero>) (sat <C one>) ;


val s1 : <rational>
 = sat flipflop ;

val s2 : <rational>
 = sat flipflop2 ;

