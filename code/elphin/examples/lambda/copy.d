(* Counting things inside lambda expressions *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<exp  : type>
<app  : exp -> exp -> exp>
<lam  : (exp -> exp) -> exp>

cp : <exp> -> <exp>
   = {{p:exp}} <p> |--> <p>
   | <app E1 E2> |--> <app> @ (cp <E1>) @ (cp <E2>)
   | <lam E> |--> {p:exp} case (cp <E p>) of
                     (<F p> |--> pop <lam F>)  ;

cp'1  = cp <lam [x] x>;
cp'2  = cp <lam [x] app x x>;
cp'3  = cp <app (lam [x] x) (lam [x] x)>;
cp'4  = cp <lam [x] lam [y] x>;

