(* Translation from simply-typed lambda calculus into combinator calculus *)
(* Simplified using Delphin "with" syntactic sugar.. *)
(* Dependently-typed Version *)
(* Author: Adam Poswolsky, Carsten schuermann *)


(* Types *)
sig <tp : type> 
    <ar : tp -> tp -> tp> %infix right 10 ;

(* Simply-Typed lambda calculus *)
sig <exp : tp -> type>
    <lam : (exp A -> exp B) -> exp (A ar B)> 
    <app : exp (A ar B) -> exp A -> exp B> ;

(* Combinator calculus *)
sig <comb : tp -> type> 
    <k : comb (A ar B ar A)>
    <s : comb ((A ar B ar C) ar (A ar B) ar A ar C) > 
    <mp : comb (A ar B) -> comb A -> comb B> ;

params = <tp>, <exp A>, <comb A>;

fun ba : <comb A -> comb B> -> <comb (A ar B)> 
  = fn <F> => <mp (mp s k) (k : comb (A ar A ar A))>
     | <[x] mp (D1 x) (D2 x)> =>   (case ((ba <D1>), (ba <D2>))
	                                 of (<D1'>,<D2'>) => <mp (mp s D1') D2'>)
     | <[x] U> => <mp k U> ;

type paramFun = <D:exp B #> -> <comb B>;

fun convert : paramFun  -> <D:exp A> -> <comb A> =
      fn W <lam D'> => (case ({<d>}{<u>} convert (W with <d> => <u>) <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <D''>) 
       | W <app D1 D2> => (case ((convert W <D1>), (convert W <D2>))
	                                      of (<U1>,<U2>) => <mp U1 U2>) 
	     
       | W <x#> => W <x>;

val testConvert1 = {<A>} {<B>} convert (fn .) <lam [u:exp A] lam [v:exp B] u> ;
val testConvert2 = {<A>} convert (fn .)  <lam [x:exp A] x> ;
val testConvert3 = {<A>}{<B>} convert (fn .) < lam [x:exp (A ar B)] lam [y: exp A] app x y> ;
