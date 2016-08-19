(* Circuits example *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<pin : type> 
<zero : pin>
<one : pin>

<circuit : type>
<newpin : (pin -> circuit) -> circuit>
<compose : circuit -> circuit -> circuit>
<andgate : pin -> pin -> pin -> circuit>
<nandgate : pin -> pin -> pin -> circuit>
<notgate : pin -> pin -> circuit>

add  = <X> |--> <Y> |--> <X + Y> ;
mult  = <X> |--> <Y> |--> <X * Y> ;

count : <circuit> -> <rational>
  = <andgate P Q R> |--> <1> 
  | <nandgate P Q R>  |--> <1> 
  | <notgate P R> |--> <1>  
  | <compose C D> |--> add (count <C>) (count <D>) 
  | <newpin C> |--> {p:pin} case count <C p> of (<N> |--> pop <N>) ;

flipflop : <circuit>
   = <newpin [x] newpin [y] newpin [p] newpin [q] 
	    compose (nandgate x q p) (nandgate p y q) > ;

query1 = count flipflop;

nandify : <circuit> -> <circuit> 
 = <andgate P Q R> |--> 
     <newpin [x] compose (nandgate P Q x) (nandgate x x R)>
 | <nandgate P Q R> |--> <nandgate P Q R>
 | <notgate P R> |--> <nandgate P P R>
 | <compose C D> |--> 
     <compose> @ (nandify <C>) @ (nandify <D>)
 | <newpin C> |-->
     {p:pin} case nandify <C p> of (<D p> |--> pop <newpin D>) ;

flipflop2 = <newpin [x] newpin [y] newpin [p] newpin [q] 
	       compose (newpin [n] compose (andgate x q n) (notgate n p)) 
	               (newpin [n] compose (andgate p y n) (notgate n q))> ;

query2 = nandify flipflop;

query3 = nandify flipflop2;

<bool : type>
<true : bool>
<false : bool>

not : <bool> -> <bool> 
 = <true> |--> <false>
 | <false> |--> <true> ;

or : <bool> -> <bool> -> <bool> 
 = <true> |--> <true> |--> <true>
 | <true> |--> <false> |--> <true>
 | <false> |--> <true> |--> <true>
 | <false> |--> <false> |--> <false> ;

conj: <bool> -> <bool> -> <bool> 
 = <true> |--> <B> |--> <B>
 | <false> |--> <B> |--> <false> ;

nandfree : <circuit> -> <bool> 
 = <compose C1 C2> |--> conj (nandfree <C1>) (nandfree <C2>)
 | <andgate P1 P2 P3> |--> <true>
 | <nandgate P1 P2 P3> |--> <false>
 | <notgate P1 P2> |--> <true>  
 | <newpin C> |--> {q:pin} case (nandfree <C q>) of (<B> |--> pop <B>) ;

nf1 : <bool>
 = nandfree flipflop ;

nf2 : <bool>
 = nandfree flipflop2 ;


sat : <circuit> -> <rational> 
 = <andgate one one one> |--> <1>
 | <andgate one zero zero> |--> <1>
 | <andgate zero one zero> |--> <1>
 | <andgate zero zero zero> |--> <1>

 | <andgate one one zero> |--> <0>
 | <andgate one zero one> |--> <0>
 | <andgate zero one one> |--> <0>
 | <andgate zero zero one> |--> <0>
  
 | <nandgate one one zero> |--> <1>
 | <nandgate one zero one> |--> <1>
 | <nandgate zero one one> |--> <1>
 | <nandgate zero zero one> |--> <1>

 | <nandgate one one one> |--> <0>
 | <nandgate one zero zero> |--> <0>
 | <nandgate zero one zero> |--> <0>
 | <nandgate zero zero zero> |--> <0>

 | <notgate one zero> |--> <1>
 | <notgate zero one> |--> <1> 
 | <notgate one one> |--> <0>
 | <notgate zero zero> |--> <0> 

 | <compose C1 C2> |--> mult (sat <C1>) (sat <C2>)
 | <newpin C> |--> add (sat <C zero>) (sat <C one>) ;


s1 : <rational>
 = sat flipflop ;

s2 : <rational>
 = sat flipflop2 ;

