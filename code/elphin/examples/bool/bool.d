(* Sample Boolean functions *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<bool : type>
<true : bool>
<false : bool>

not : <bool> -> <bool> 
 = <true> |--> <false>
 | <false> |--> <true> ;

n1 = not <true> ;
n2 = not <false> ;
 
or : <bool> -> <bool> -> <bool> 
 = <true> |--> <true> |--> <true>
 | <true> |--> <false> |--> <true>
 | <false> |--> <true> |--> <true>
 | <false> |--> <false> |--> <false> ;

o1 = or <true> <true> ;
o2 = or <false> <true> ;
o3 = or <true> <false> ;
o4 = or <false> <false> ;

con : <bool> -> <bool> -> <bool> 
 = <true> |--> <B> |--> <B>
 | <false> |--> <B> |--> <false> ;

a1 = con <true> <true> ;
a2 = con <false> <true> ;
a3 = con <true> <false> ;
a4 = con <false> <false> ;

<nat : type>
<z : nat>
<s : nat -> nat> ;

gt : <nat> -> <bool> 
 = <z> |--> <false>
 | <s X> |--> <true> ;

g0 = gt <z> ;
g1 = gt <s (s z)> ;
g2 = gt <s (s (s z))> ;
g3 = gt <s (s (s (s z)))> ;
