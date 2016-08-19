(* Mini-ML evaluator *)
(* Executes code a given destinations.  *)
(* Author: Carsten Schuermann *)

(* Expressions and Values *)

<exp : type>
<val : type>

<v : val -> exp>
<z : exp>			 (* zero *)
<s : exp -> exp>			 (* succ *)
<c : exp -> exp -> (val -> exp) -> exp> (* case *)
<l : (val -> exp) -> exp>	 	 (* lam *)
<a : exp -> exp -> exp>		 (* app *)
<f : (exp -> exp) -> exp>	 	 (* fix *)

(* Destinations *)

<dest : type>

<z' : val> 
<s' : val -> val>
<l' : (val -> exp) -> val>

(* Evaluation *)

eval : <dest> -> <val>
  = {{d:exp -> dest}} <d (v V)> |--> <V>
  | {{d:exp -> dest}} <d z> |--> <z'> 
  | {{d:exp -> dest}} <d (s E)>  |--> 
     {d' : exp -> dest} case (eval <d' E>) of
		       (<V> |--> pop <s' V>) 
  | {{d:exp -> dest}} <d (c E1 E2 E3)> |-->
     {d' : exp -> dest} case (eval <d' E1>) of
	         ( <z'> |--> pop (eval <d E2>) 	
		 | <s' V> |-->  pop (eval <d (E3 V)>)) 
  | {{d:exp -> dest}} <d (l E)> |--> <l' E> 
  | {{d:exp -> dest}} <d (a E1 E2)> |--> 
     {d' : exp -> dest} case (eval <d' E1>) of
       (<l' E1'> |--> {d'' : exp -> dest} case (eval <d'' E2>) of
          (<V2> |--> pop (pop (eval <d (E1' V2)>))))
  | {{d:exp -> dest}} <d (f E)> |--> eval <d (E (f E))> ;

evaluate : <exp> -> <val>
	 = <E> |--> {d:exp -> dest} case eval <d E> of (<V> |--> pop <V>) ;

(* Examples *)	      

double = <f [double] l [x] c (v x) z [y] s (s (a double (v y)))> ;

test1 = evaluate <s (s (s z))> ;
test2 = evaluate <c (s (s (s z))) (s z) [x] z> ;
test3 = evaluate (<a> @ double @ <s (s z)>) ;