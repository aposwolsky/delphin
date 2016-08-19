(* Translation from lambda calculus into combinator calculus *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<comb : type>
<k : comb>
<s : comb>
<mp : comb -> comb -> comb>

<exp : type>
<lam : (exp -> exp) -> exp>
<app : exp -> exp -> exp>

ded : <comb -> comb> -> <comb>
   = {{c:comb}} <[x] c> |--> <c>
   | <[x] x> |--> <mp (mp s k) k>
   | <[x] k> |--> <mp k k>
   | <[x] s> |--> <mp k s>
   | <[x] (mp (C1 x) (C2 x))> |-->
       <mp> @ (<mp> @ <s> @ (ded <C1>)) @ (ded <C2>) ;

d1 : <comb> = ded <[x:comb] mp k x> ;
d2 :<comb -> comb> = {c} (<C c> |--> (pop <C>)) (<mp k c>);

c2d : <exp> -> <comb>
   = {{x:comb -> exp}} <x C> |--> <C>
   | <app E1 E2> |--> <mp> @ (c2d <E1>) @ (c2d <E2>)
   | <lam E> |--> {c:comb}{x:comb -> exp}
                  case c2d <E (x c)> of
                 (<C c> |--> pop (pop (ded <C>))) ;

c2d'1  = c2d <lam [x] x>;
c2d'2  = c2d <lam [x] app x x>;
c2d'3  = c2d <app (lam [x] x) (lam [x] x)>;
c2d'4  = c2d <lam [x] lam [y] x>;
