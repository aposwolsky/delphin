(* Continuation Semantics *)
(* Author: Carsten Schuermann, Adam Poswolsky, Jeffrey Sarnat *)

<exp  : type>
<cont : type>
<num  : rational -> exp>
<plus : exp -> exp -> exp>
<mult : exp -> exp -> exp>
<app  : exp -> exp -> exp>
<lam  : (exp -> exp) -> exp>
<callcc : (cont -> exp) -> exp>
<throw  : cont -> exp -> exp>

initL  : <cont> -> <exp> -> <exp> = fail ;

init : <exp> -> (<cont> -> <exp> -> <exp>) -> <exp> 
     = <X> |--> L |--> <X> ;

eval : <exp> -> (<exp> -> (<cont> -> <exp> -> <exp>) -> <exp>) -> (<cont> -> <exp> -> <exp>) -> <exp> 
     = <app E1 E2>  |--> K |--> eval <E1> (<lam X1> |--> eval <E2> (<V> |--> eval <X1 V> K)) 
     | <lam E>      |--> K |--> K <lam E> 
     | <num N>      |--> K |--> K <num N>  
     | <plus E1 E2> |--> K |--> eval <E1> (<num N1> |--> eval <E2> (<num N2> |--> K <num (N1 + N2)>)) 
     | <mult E1 E2> |--> K |--> eval <E1> (<num N1> |--> eval <E2> (<num N2> |--> K <num (N1 * N2)>)) 
     | <callcc E>   |--> K |--> L |--> {k:cont} case (eval <E k> K (L | <k> |--> <X> |--> K <X> L)) of (X |--> pop X)
     | {{k}} <throw k E> |--> K |--> eval <E> (<X> |--> L' |--> L' <k> <X>)
 ;


eval' = <E> |--> eval <E> init initL;
 
eval'1 = eval' <lam [x] x>;
eval'2 = eval' <lam [x] app x x>;
eval'3 = eval' <app (lam [x] x) (lam [x] x)>;
eval'4 = eval' <lam [x] lam [y] x>;
eval'5 = eval' <mult (num 6) (num 7)>;
eval'6 = eval' <callcc [k] plus (num 2) (throw k (mult (num 3) (num 4)))>;
eval'7 = eval' <callcc [k] throw k (plus (throw k (num 7)) (num 1) )>;
eval'8 = eval' <app (callcc [k] lam [x] throw k x) (lam [x] x)> ;

