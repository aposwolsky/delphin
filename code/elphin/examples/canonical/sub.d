(* Substititution into canonical/atomic forms *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

<nf: type>
<at: type>
<atnf : at -> nf>
<l : (at -> nf) -> nf>
<a : at -> nf -> at>
<c : at>

(* subat' is just temporarily here.  Once mutual recursion is 
   completely implemented, remove it and  rename all occurrences of subst' 
   by subat *)

subnf : <at -> nf> -> <at> -> <nf> 
 = <[x:at] l [y:at] N x y> |--> <Q> |--> {y:at} 
      case subnf <[x:at] N x y> <Q> of (<F y> |--> pop <l F>)
 | <[x:at] atnf (P x)> |--> <Q> |--> <atnf> @ (subat <[x:at] P x> <Q>) 

and 

subat : <at -> at> -> <at> -> <at>
 = <[x:at] c> |--> <Q> |--> <c>
 | <[x:at] a (P x) (N x)> |--> <Q> |--> 
      <a> @ (subat <[x:at] P x> <Q>) @ (subnf <[x:at] N x> <Q>)
 | {{y:at}} <[x:at] y> |--> <Q> |--> <y>
 | <[x:at] x> |--> <Q> |--> <Q> ;

(* Add some examples *)

result1 = subnf <[x] atnf x> <c> ;
result2 = subnf <[x] l ([y] atnf (a x (atnf y)))> <c> ;	