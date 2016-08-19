(* Copy example.  With semantic equations *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<exp  : type>
<app  : exp -> exp -> exp>
<lam  : (exp -> exp) -> exp>

cp : <exp> -> (<exp> -> <exp>) -> <exp>
   = {{x:exp}} <x> |--> K |--> K <x>
   | <app E1 E2> |--> K |--> <app> @ (cp <E1> K) @ (cp <E2> K)
   | <lam E> |--> K |--> {p:exp} case cp <E p> (K | <p> |--> <p>) of
                     (<F p> |--> pop <lam F>)  ;

K : <exp> -> <exp> = fail ;

cp'1  = cp <lam [x] x> K;
cp'2  = cp <lam [x] app x x> K;
cp'3  = cp <app (lam [x] x) (lam [x] x)> K;
cp'4  = cp <lam [x] lam [y] x> K;


H : <exp> -> <exp> -> <exp>
  = X |--> Y |--> <app> @ X @ Y;

G : (<exp> -> <exp>) -> <exp>
  = F |--> ({x:exp} case (F <x>) of (<Y x> |--> pop <lam Y>)) ;

cp : <exp> -> (<exp> -> <exp>) -> <exp>
   = {{x:exp}} <x> |--> K |--> K <x> 
    | <app E1 E2> |--> K |--> H (cp <E1> K) (cp <E2> K) 
    | <lam E> |--> K |--> G (X |--> {p:exp} case cp <E p> (K | <p> |--> X) of
                     (Y |--> pop Y)) ;

cp'1  = cp <lam [x] x> K;
cp'2  = cp <lam [x] app x x> K;
cp'3  = cp <app (lam [x] x) (lam [x] x)> K;
cp'4  = cp <lam [x] lam [y] x> K;

cp' : (<exp> -> <exp>) -> <exp>  -> <exp>
   = K |--> ( <X> |--> K <X> 
              | <app E1 E2> |--> H (cp' K <E1>) (cp' K <E2>) 
              | <lam E> |--> G (X |--> {p:exp} case cp' (K | <p> |--> X) <E p> of
                     (Y |--> pop Y))) ;


cp'1  = cp' K <lam [x] x>;
cp'2  = cp' K <lam [x] app x x>;
cp'3  = cp' K <app (lam [x] x) (lam [x] x)>;
cp'4  = cp' K <lam [x] lam [y] x>;


