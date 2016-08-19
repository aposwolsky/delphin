(* Parallel reduction *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<exp : type>
<app : exp -> exp -> exp>
<lam : (exp -> exp) -> exp>

par : <exp> -> <exp> 
 = {{x:exp}} <x> |--> <x>
 | <app E1 E2> |--> par' <E1> (par <E2>)
 | <lam E1> |--> {x:exp} case par <E1 x> of (<F1 x> |--> pop <lam F1>)

and par' : <exp> -> <exp> -> <exp> 
 = {{x:exp}} <x> |--> <E3> |--> <app x E3>
 | <app E1 E2> |--> (<E2'> |--> <app> @ (par' <E1> (par <E2>)) @ <E2'>)
 | <lam E1> |--> <E2'> |--> {x:exp} 
     case par <E1 x> of (<F1 x> |--> pop <F1 E2'>) ;


p1  = par <lam [x] x>;
p2  = par <lam [x] app x x>;
p3  = par <app (lam [x] x) (lam [x] x)>;
p4  = par <lam [x] lam [y] x>;

