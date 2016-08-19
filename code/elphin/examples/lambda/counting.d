(* Counting things inside lambda expressions *)
(* Author: Carsten Schuermann, Adamo Poswolsky *)

<exp  : type>
<app  : exp -> exp -> exp>
<lam  : (exp -> exp) -> exp>


plus : <rational> -> <rational> -> <rational>
 = <X> |--> <Y> |--> <X + Y> ;

(* Count the number of bound variables *)

cntvar : <exp> -> <rational> 
 = {{p:exp}} <p> |--> <1>
 | <app E1 E2> |--> plus (cntvar <E1>) (cntvar <E2>)
 | <lam E> |--> {p:exp} 
             case cntvar <E p> of (<N> |--> pop <N>) ;

cntvar'1 = cntvar <lam [x] x>;
cntvar'2 = cntvar <lam [x] app x x>;
cntvar'3 = cntvar <app (lam [x] x) (lam [x] x)>;
cntvar'4 = cntvar <lam [x] lam [y] x>;

(* Count the number of lambda binders *)

cntlam : <exp> -> <rational> 
 = {{x:exp}} <x> |--> <0>
 | <app E1 E2> |--> plus (cntlam <E1>) (cntlam <E2>)
 | <lam E> |--> {p:exp} 
             case cntlam <E p> of (<N> |--> pop <N + 1>) ;

cntlam'1 = cntlam <lam [x] x>;
cntlam'2 = cntlam <lam [x] app x x>;
cntlam'3 = cntlam <app (lam [x] x) (lam [x] x)>;
cntlam'4 = cntlam <lam [x] lam [y] x>;

(* Constructor free programming *)
(* A variation on the count example from above.
	Difference: a and l are dynamically introduced
*)

cntvar : <exp> -> <rational> 
 = {{x:exp}} <x> |--> <1>
 | {{a:exp -> exp -> exp}} <a E1 E2> |--> plus (cntvar <E1>) (cntvar <E2>)
 | {{l:(exp -> exp) -> exp}} <l E> |--> {p:exp} 
             case cntvar <E p> of (<N> |--> pop <N>) ;

cntvar'1 = {a  : exp -> exp -> exp}
           {l  : (exp -> exp) -> exp}
			  case (cntvar <l [x] x>)
			    of (<N> |--> pop (pop <N>)) ;
cntvar'2 = {a  : exp -> exp -> exp}
           {l  : (exp -> exp) -> exp}
			  case (cntvar <l [x] a x x>)
			    of (<N> |--> pop (pop <N>)) ;
cntvar'3 = {a  : exp -> exp -> exp}
           {l  : (exp -> exp) -> exp}
			  case (cntvar <a (l [x] x) (l [x] x)>)
			    of (<N> |--> pop (pop <N>)) ;
cntvar'4 = {a  : exp -> exp -> exp}
           {l  : (exp -> exp) -> exp}
			  case (cntvar <l [x] l [y] x>)
			    of (<N> |--> pop (pop <N>)) ;
