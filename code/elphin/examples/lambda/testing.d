(* Testing properties about lambda expressions *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<exp : type>
<app : exp -> exp -> exp>
<lam : (exp -> exp) -> exp>

<bool : type>
<true : bool>
<false : bool>

not : <bool> -> <bool> 
 = <true> |--> <false>
 | <false> |--> <true> ;
 
or : <bool> -> <bool> -> <bool> 
 = <true> |--> <true> |--> <true>
 | <true> |--> <false> |--> <true>
 | <false> |--> <true> |--> <true>
 | <false> |--> <false> |--> <false> ;

conj : <bool> -> <bool> -> <bool> 
 = <true> |--> <B> |--> <B>
 | <false> |--> <B> |--> <false> ;

const : <exp -> exp> -> < bool> 
= {{y:exp}} <[x:exp] y> |--> <true>
 | <[x:exp] x> |--> <false>
 | <[x:exp] app (E1 x) (E2 x)> |--> conj (const <[x:exp] E1 x>) (const <[x:exp] E2 x>)
 | <[x:exp] lam [y:exp] E x y> |--> {y:exp} case const <[x:exp] E x y> of (<B> |--> pop <B>) ;

c1  = const <[x:exp] x>;
c2  = const <[x:exp] app x x>;
c3  = const <[x:exp] app (lam [y:exp] y) (lam [y:exp] y)>;
c4  = const <[x:exp] lam [y] x>;
	
betatest : <exp> -> < bool> 
 = [f:exp -> exp] <lam f> |--> <false>
 | <app E1 E2> |--> case <E1> of (<lam F> |--> <true>
                                 | <app E3 E4> |--> <false>) ;

b1  = betatest <lam [x] x>;
b2  = betatest <lam [x] app x x>;
b3  = betatest <app (lam [x] x) (lam [x] x)>;
b4  = betatest <lam [x] lam [y] x>;


idtest : <exp -> exp> -> <bool> 
 = <[x:exp] x> |--> <true>
 | {{y:exp}} <[x:exp] y> |--> <false>
 | <[x:exp] app (E1 x) (E2 x)> |--> <false>
 | <[x:exp] lam [y:exp] E x y> |--> <false> ;

i1  = idtest <[x:exp] x>; 
i2  = idtest <[x:exp] app x x>;
i3  = idtest <[x:exp] app (lam [y:exp] y) (lam [y:exp] x)>;
i4  = idtest <[x:exp] lam [y:exp] x>;


etatest : <exp> -> < bool> 
 = <lam E> |--> case <E> of ( <[x:exp] lam [y:exp] E' x y> |--> <false>
                            | <[x:exp] app (E1' x) (E2' x)> |--> conj (const <E1'>) (idtest <E2'>)
			    | <[x:exp] x> |--> <false>)
 | <app E1 E2> |--> <false> ;

e1 = etatest <lam [x:exp] x>;
e2 = etatest <lam [x:exp] app x x>;
e3 = etatest <app (lam [x:exp] x) (lam [x:exp] x)>;
e4 = etatest <lam [x:exp] lam [y:exp] x>;
e4 = etatest <lam [x:exp] lam [y:exp] x>;


