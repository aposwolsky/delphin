(* Substititution into canonical/atomic forms *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<nf: type>
	<at: type>
	<atnf : at -> nf>
	<l : (at -> nf) -> nf>
	<a : at -> nf -> at>
	<c : at>;

params = <at>;

fun subnf : <at -> nf> -> <at> -> <nf> =
 fn <[x:at] l [y:at] N x y> => (fn <Q> =>   
      case {<y:at#>} subnf <[x:at] N x y> <Q> of ({<y>}<F y> => <l F>))
 | <[x:at] atnf (P x)> => (fn <Q> => <atnf> @ (subat <[x:at] P x> <Q>) )

and 

subat : <at -> at> -> <at> -> <at> =
 fn <[x:at] c> => (fn <Q> => <c>)
 | <[x:at] a (P x) (N x)> => (fn <Q> =>
      <a> @ (subat <[x:at] P x> <Q>) @ (subnf <[x:at] N x> <Q>))
 | [<y:at#>] <[x:at] y> => (fn <Q> => <y>)
 | <[x:at] x> => (fn <Q> => <Q>) ;

(* Add some examples *)

val result1 = subnf <[x] atnf x> <c> ;
val result2 = subnf <[x] l ([y] atnf (a x (atnf y)))> <c> ;	