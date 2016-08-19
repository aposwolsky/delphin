(* Sample arithmetical functions *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<nat : type>
<z : nat>
<s : nat -> nat>

plus : <nat> -> <nat> -> <nat> 
 = <z> |--> (<Y> |--> <Y>)
 | <s X> |--> (<Y> |--> <s> @ (plus <X> <Y>)) ;

p0 = plus <s (s z)> <s (s z)>;
p1 = plus <s (s (s z))> <s (s z)> ;
p2 = plus <s (s (s z))> <s (s (s (s z)))> ;

mult : <nat> -> <nat> -> <nat> 
 = <z> |--> <Y> |--> <z>
 | <s X> |--> <Y> |--> plus <Y> (mult <X> <Y>) ;

m0 = mult <s (s z)> <s (s z)>;
m1 = mult <s (s (s z))> <s (s z)> ;
m2 = mult <s (s (s z))> <s (s (s (s z)))> ;


factorial : <nat> -> <nat> 
 = <z> |--> <s z>
 | <s X> |--> mult <s X> (factorial <X>) ;

f1 = factorial <s z> ;
f2 = factorial <s (s z)> ;
f3 = factorial <s (s (s z))> ;
f4 = factorial <s (s (s (s z)))> ;
f5 = factorial <s (s (s (s (s z))))> ;
f6 = factorial <s (s (s (s (s (s z)))))> ;
(* f7 = factorial <s (s (s (s (s (s (s z))))))> ; *)

ex : <nat> -> <nat> -> <nat> 
 = <X> |--> (<z> |--> <s z>)
 | <X> |--> (<s Y> |--> mult (ex <X> <Y>) <X>) ;

e0 = ex <s (s z)> <s (s z)>;
e1 = ex <s (s (s z))> <s (s z)> ;
e1a = ex <s (s (s z))> <s (s (s (z)))> ;
e2 = ex <s (s (s z))> <s (s (s (s z)))> ;

	
minus : <nat> -> <nat> -> <nat> 
 = <X> |--> <z> |--> <X>
 | <z> |--> <s Y> |--> <z>
 | <s X> |--> <s Y> |--> minus <X> <Y> ;

mi0 = minus <s (s z)> <s (s z)>;
mi1 = minus <s (s (s z))> <s (s z)> ;
mi2 = minus <s (s (s z))> <s (s (s (s z)))> ;


acker : <nat> -> <nat>  -> < nat> 
 = (<z> |--> [y:nat]  <y> |--> <s  y>)
 | ([x:nat]  <s x> |--> <z> |--> acker  <x> <s  z>)
 | ([x:nat]  <s x> |--> [y:nat]  <s  y> |--> acker  <x> (acker  <s  x> <y>)) ;

a0 = acker <s (s z)> <s (s z)>;
a1 : <nat>
   = acker <s (s (s z))> <s (s z)> ;
a2 : <nat>
   = acker <s (s (s z))> <s (s (s (s z)))> ;

(* Conversion to the built-in rational numbers *)

add   = <X> |--> <Y> |--> <X + Y> ;

nat2rat : <nat> -> <rational>
        = <z> |--> <0>
 	| (<s X> |--> add (nat2rat <X>) <1>);

ratf1 : <rational>
          = nat2rat (f1) ;

ratf2 : <rational>
          = nat2rat (f2) ;

ratf3 : <rational>
          = nat2rat (f3) ;

ratf4 : <rational>
          = nat2rat (f4) ;

ratf5 : <rational>
          = nat2rat (f5) ;

ratf6 : <rational>
          = nat2rat (f6) ;

ratacker0 : <rational>
          = nat2rat (a0) ;

ratacker1: <rational>
          = nat2rat (a1) ;

ratacker2: <rational>
          = nat2rat (a2) ;
