(* Continuation Semantics *)
(* Author: Carsten Schuermann *)

<exp  : type>
<cont : type>
<num  : rational -> exp>
<plus : exp -> exp -> exp>
<mult : exp -> exp -> exp>
<app  : exp -> exp -> exp>
<lam  : (exp -> exp) -> exp>
<callcc : (cont -> exp) -> exp>
<throw  : cont -> exp -> exp>

initL  : <cont> -> (<exp> -> <exp>) = fail ;
init   = <X:exp> |--> <X> ;

eval : (<cont> -> (<exp> -> <exp>)) -> <exp> -> (<exp> -> <exp>) -> <exp> 
     = L |-->   ( <app E1 E2>     |--> K |--> eval L <E1> (<lam X1> |--> eval L <E2> (<V> |--> eval L <X1 V> K))
     	      | <plus E1 E2>      |--> K |--> eval L <E1> (<num N1> |--> eval L <E2> (<num N2> |--> K <num (N1 + N2)>))
     	      | <mult E1 E2>      |--> K |--> eval L <E1> (<num N1> |--> eval L <E2> (<num N2> |--> K <num (N1 * N2)>))
     	      | <lam E>           |--> K |--> K <lam E> 
     	      | <callcc E>        |--> K |--> {k:cont} case (eval (L | <k> |--> K) <E k> K) of (X |--> pop X)
     	      | {{k}} <throw k E> |--> K |--> eval L <E> (L <k>)
     	      | <num N>           |--> K |--> K <num N>);


eval'1 = eval initL <lam [x] x> init;
eval'2 = eval initL <lam [x] app x x> init;
eval'3 = eval initL <app (lam [x] x) (lam [x] x)> init;
eval'4 = eval initL <lam [x] lam [y] x> init;
eval'5 = eval initL <mult (num 6) (num 7)> init;
eval'6 = eval initL <callcc [k] plus (num 2) (throw k (mult (num 3) (num 4)))> init;
eval'7 = eval initL <callcc [k] throw k (plus (throw k (num 7)) (num 1) )> init;
eval'8 = eval initL <app (callcc [k] lam [x] throw k x) (lam [x] x)> init ;
