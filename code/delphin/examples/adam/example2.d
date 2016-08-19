sig <nat : type>
    <z : nat>
    <s : nat -> nat>
    <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>
    <eq : exp -> exp -> type> 
    <eq_app : eq E1 F1 -> eq E2 F2 -> eq (app E1 E2) (app F1 F2)>
    <eq_lam : ({x}eq x x -> eq (E x) (F x)) -> eq (lam E) (lam F)>
    <comb : type>
    <k : comb>
    <s' : comb>
    <mp : comb -> comb -> comb>;



(* Counting number variables *)
fun plus : <nat> -> <nat> -> <nat>
 = fn <z> => (fn N => N)
    | <s N1> => fn M => 
	        case (plus <N1> M)
	        of (<N3>) => <s N3>;

fun cntvar 
 = fn  <lam E> =>
                   (case ( {<x>} cntvar <E x>)
                          of  ({<x>} <N>)  => <N>)
    |  <app E E3> =>
                          plus (cntvar <E>) (cntvar <E3>)
    | [<x:exp#>] <x> => <s z>;


(* combinator *)
(* Translation from lambda calculus into combinator calculus *)
(* SIMPLY-Typed version *)
fun ded : <comb -> comb> -> <comb>
   = fn [<c:comb#>] <[x] c> => <c>
   | <[x] x> => <mp (mp s' k) k>
   | <[x] k> => <mp k k>
   | <[x] s'> => <mp k s'>
   | <[x] (mp (C1 x) (C2 x))> =>
       <mp> @ (<mp> @ <s'> @ (ded <C1>)) @ (ded <C2>) ;


fun c2d : <exp> -> <comb>
   = fn [<x:(comb -> exp)#>] <x C> => <C>
   | <app E1 E2> => <mp> @ (c2d <E1>) @ (c2d <E2>)
   | <lam E> => case ({<c:comb#>}{<x:comb -> exp#>} c2d <E (x c)>)
	         of {<c>}{<x>} <C c> => ded <C> ;



(* Dependent-Types:  Copy Example.. *)

fun extend : (<f:exp#> -> <eq f f>) -> {<x:exp#>}{<u:eq x x#>} (<f:exp#> -> <eq f f>) =
  fn W => fn {<x>} {<u>} (x => <u>)  
          | [<e:exp#>] {<x>} {<u>} (e => let
					   val result = W e
					 in
					   {<x>}{<u>} result
					 end \x \u);


fun eqfun : _ -> <e:exp> -> <eq e e> = 
  fn W => 

  (fn <app E1 E2> => (case ((eqfun W <E1>), (eqfun W <E2>))
                                of (<D1>, <D2>) => <eq_app D1 D2>)
   | <lam E> => (case ({<x>}{<u>} eqfun ((extend W) \x \u) <E x>)
                            of ({<x>}{<u>} <D x u>) => <eq_lam D>)

   | [<x:exp#>] <x> => W x) ;
