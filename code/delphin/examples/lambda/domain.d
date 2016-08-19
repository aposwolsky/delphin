(* Copy example.  With semantic equations *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<exp  : type>
	<app  : exp -> exp -> exp>
	<lam  : (exp -> exp) -> exp>;

fun cp : <exp> -> (<exp> -> <exp>) -> <exp> =
   fn [<x:exp#>] <x> => (fn K => K <x>)
   | <app E1 E2> => (fn K => <app> @ (cp <E1> K) @ (cp <E2> K))
   | <lam E> => (fn K => (case {<p:exp#>} cp <E p> (fn <p> => <p>  |  <E'> => K <E'>)
                            of {<p>}<F p> => <lam F>));

fun Kinitial : <exp> -> <exp> = fn . ;

val cp'1  = cp <lam [x] x> Kinitial;
val cp'2  = cp <lam [x] app x x> Kinitial;
val cp'3  = cp <app (lam [x] x) (lam [x] x)> Kinitial;
val cp'4  = cp <lam [x] lam [y] x> Kinitial;


fun H : <exp> -> <exp> -> <exp>
  = fn X => fn Y => <app> @ X @ Y;

fun G : (<exp> -> <exp>) -> <exp>
  = fn F => (case {<x:exp#>} (F <x>) of ({<x>}<Y x> => <lam Y>)) ;

fun cp : <exp> -> (<exp> -> <exp>) -> <exp> =
   fn [<x:exp#>] <x> => (fn K => K <x> )
    | <app E1 E2> => (fn K => H (cp <E1> K) (cp <E2> K))
    | <lam E> => (fn K => G (fn X => case {<p:exp#>} cp <E p> (fn <p> => X  | <E'> => K <E'>) of
                     ({<p>}Y => Y))) ;

val cp'1  = cp <lam [x] x> Kinitial;
val cp'2  = cp <lam [x] app x x> Kinitial;
val cp'3  = cp <app (lam [x] x) (lam [x] x)> Kinitial;
val cp'4  = cp <lam [x] lam [y] x> Kinitial;

fun cp' : (<exp> -> <exp>) -> <exp>  -> <exp> =
   fn K => ( fn [<x:exp#>]<x> => K <x> 
                | <app E1 E2> => H (cp' K <E1>) (cp' K <E2>) 
                | <lam E> => G (fn X => case {<p:exp#>} cp' (fn <p> => X | <E'> => K <E'>) <E p> of
                     ({<p>}Y => Y))) ;


val cp'1  = cp' Kinitial <lam [x] x>;
val cp'2  = cp' Kinitial <lam [x] app x x>;
val cp'3  = cp' Kinitial <app (lam [x] x) (lam [x] x)>;
val cp'4  = cp' Kinitial <lam [x] lam [y] x>;


