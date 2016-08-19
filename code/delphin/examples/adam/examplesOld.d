(* Natural Numbers *)
sig <nat : type>
    <z : nat>
    <s : nat -> nat> ;

(* Expressions *)
sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp> ;

(* Formulas *)
sig <o : type> 
    <ar : o -> o -> o> %infix right 10 ;

(* Natural Deduction *)
sig <nd : o -> type>
    <impi : (nd A -> nd B) -> nd (A ar B)> 
    <impe : nd (A ar B) -> nd A -> nd B> ;

(* Addition *)
fun plus : <nat> -> <nat> -> <nat> = 
   fn <z> <M> => <M>
    | <s N> <M> => case (plus <N> <M>)
                    of <x> => <s x> ;


(* Interpreter *)
fun eval : <exp> -> <exp> = 
   fn <app E1 E2> => (case (eval <E1>, eval <E2>) of
                      (<lam F>, <V>) => eval <F V>)
    | <lam E> => <lam E> ;


(* Beta Reduction *)
fun evalBeta : <exp> -> <exp> =
   fn <app E1 E2> => (case (evalBeta <E1>, evalBeta <E2>)
                      of (<lam F>, <V>) => evalBeta <F V>
                       | [<x:exp#>](<x>, <V>) => <app x V>)
    | <lam E> => (case ({<x>} evalBeta <E x>)
                    of {<x>}<E' x> => <lam E'>)
    | [<x:exp#>] <x> => <x> ;


(* Variable Counting *)
fun cntvar  : <exp> -> <nat>
 = fn  <lam E> =>  (case ( {<x>} cntvar <E x>)
                          of  ({<x>} <N>)  => <N>)
    |  <app E E3> =>
                          plus (cntvar <E>) (cntvar <E3>)
    | [<x:exp#>] <x> => <s z>;

(* Lemma 5.2 is over any type rho, tau, and sigma,
 * but we just show it for an example where rho=tau=exp and sigma=name
 *)
fun lemma5-1 : ({<x:exp#>} (<exp> -> <nat>))  -> (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) 
 = fn u1 u2 => {<x:exp#>} (u1 \x) (u2 \x) ;

fun lemma5-2 : (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) -> ({<x:exp#>} (<exp> -> <nat>))
 = fn u1 => fn {<x:exp#>} ((E \x) => (u1 E) \x) ;

fun lemma5-3 : ({<x:exp#>} (<exp> * <nat>))  -> (({<x:exp#>}<exp>) * {<x:exp#>}<nat>) 
 = fn {<x>}((u1 \x), (u2 \x)) => (u1, u2) ;

fun lemma5-4 : (({<x:exp#>}<exp>) * {<x:exp#>}<nat>) -> ({<x:exp#>} (<exp> * <nat>))
 = fn (u1, u2) => {<x:exp#>} ((u1 \x), (u2 \x));

val exampleF1 : ({<x:exp#>} (<exp> -> <nat>)) = fn {<x>} (<x> => <s z>)
                                                 | {<x>} (<_> => <z>) ;
val exampleF2 : (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) = fn {<x>} <x> => {<x>} <s z> 
                                                          | {<x>} <_> => {<x>} <z> ;
val test1 = {<x>} (exampleF1 \x) <x> ;
val test1' = {<x>} (exampleF1 \x) <lam [x] x> ;
val test2 = exampleF2 ({<x>} <x>) ;
val test2' = exampleF2 ({<x>} <lam [x] x>) ;


val test3 = {<x>} ((lemma5-2 exampleF2) \x) <x> ;
val test3' = {<x>} ((lemma5-2 exampleF2) \x) <lam [x] x> ;
val test4 = (lemma5-1 exampleF1) ({<x>} <x>) ;
val test4' = (lemma5-1 exampleF1) ({<x>} <lam [x] x>) ;


(* Structural Identity *)
sig <eq : exp -> exp -> type> 
    <eq_app : eq E1 F1 -> eq E2 F2 -> eq (app E1 E2) (app F1 F2)>
    <eq_lam : ({x}eq x x -> eq (E x) (F x)) -> eq (lam E) (lam F)>;

type eqParamFun = <f:exp#> -> <eq f f> ;

fun extend : eqParamFun -> {<x:exp#>}{<u:eq x x#>}eqParamFun =
  fn W => fn {<x>} {<u>} (x => <u>)  
          | [<e:exp#>] {<x>} {<u>} (e => (let
					   val result = W e
					 in
					   {<x>}{<u>} result
					 end) \x \u);


fun eqfun : eqParamFun -> <e:exp> -> <eq e e> = 
  fn W => 

  (fn <app E1 E2> => (case ((eqfun W <E1>), (eqfun W <E2>))
                                of (<D1>, <D2>) => <eq_app D1 D2>)
   | <lam E> => (case ({<x>}{<u>} eqfun ((extend W) \x \u) <E x>)
                            of ({<x>}{<u>} <D x u>) => <eq_lam D>)

   | [<x:exp#>] <x> => W x) ;


val exampleEq1 = eqfun (fn .) <lam [x] app x x>;
  (* evaluates to  <eq_lam ([x:exp] [x1:eq x x] eq_app x1 x1)> *)

(* Combinators *)
sig <comb : o -> type> 
    <K : comb (A ar B ar A)>
    <S : comb ((A ar B ar C) ar (A ar B) ar A ar C) > 
    <MP : comb (A ar B) -> comb A -> comb B> ;

type convParamFun = (<A:o> -> <D: nd A#> -> <comb A>);
fun extendC : convParamFun -> <B:o> -> {<x:nd B#>}{<y:comb B#>}convParamFun = 
  fn W => fn <B> => fn {<x>} {<y>} (<B> => fn x => <y>) 
	            | [<e>] {<x>} {<u>} (<_> => fn e =>  let
							   val result = W <_> e
							 in
							   {<x>}{<u>} result
							 end \x \u);

fun ba : <comb A -> comb B> -> <comb (A ar B)> 
  = fn <F> => <MP (MP S K) (K : comb (A ar A ar A))>
     | <[x] MP (D1 x) (D2 x)> =>   (case ((ba <D1>), (ba <D2>))
	                                 of (<D1'>,<D2'>) => <MP (MP S D1') D2'>)
     | <[x] U> => <MP K U> ;


fun convert : convParamFun  -> <D:nd A> -> <comb A> =
      fn W <impi D'> => (case ({<d>}{<u>} convert ((extendC W <_>) \d \u) <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <D''>) 
       | W <impe D1 D2> => (case ((convert W <D1>), (convert W <D2>))
	                                      of (<U1>,<U2>) => <MP U1 U2>) 
	     
       | W [<x:nd A#>] <x> => W <A> x;

val testConvert1 = {<A>}{<B>} convert (fn .) <impi [u:nd A] impi [v:nd B] u> ;
  (* evaluates to  {<A : o#>} {<B : o#>} <MP (MP S (MP K K)) (MP (MP S K) K)> *)
val testConvert2 = {<A>} convert (fn .)  <impi [x:nd A] x> ;
  (* evaluates to  {<A : o#>} <MP (MP S K) K> *)
val testConvert3 = {<A>}{<B>} convert (fn .) < impi [x:nd (A ar B)] impi [y: nd A] impe x y> ;
  (* evaluates to  {<A : o#>} {<B : o#>} <MP (MP S K) K> *)


(* Sequent Calculus *)
sig <hyp : o -> type> 
    <conc : o -> type>
   
    <axiom : hyp A -> conc A>
    <impr : (hyp A -> conc B) -> conc (A ar B)>
    <impl : conc A -> (hyp B -> conc C) -> (hyp (A ar B) -> conc C)> ;

(* Admissibility of Cut *)
fun ca : <conc A> -> <hyp A -> conc C> -> <conc C> 
  = fn <axiom H> <E> => <E H>
     | <D> <axiom> => <D>
     | <impr D2> <[h] impl (E1 h) (E2 h) h> =>
                       (case (ca <impr D2> <E1>)
                       of <E1'> => case ({<h2>} ca <impr D2> <[h] E2 h h2>)
                                   of   {<h2>}<E2' h2> => ca (ca <E1'> <D2>) <E2'>)
     | <impl D1 D2 H> <E> => (case ({<h2>} ca <D2 h2> <E>)
                              of {<h2>}<D2' h2> => <impl D1 D2' H>)
     | <D> <[h] axiom H1> => <axiom H1>
     | <D> <[h] impr (E2 h)> => (case ({<h2>} ca <D> <[h] E2 h h2>)
                                     of {<h2>} <E2' h2> => <impr E2'>)
     | <D> <[h] impl (E1 h) (E2 h) H> =>
                                (case (ca <D> <E1>)
                                  of <E1'> => case ({<h2>} ca <D> <[h] E2 h h2>)
                                                of {<h2>}<E2' h2> => <impl E1' E2' H>);


fun caElim : ({<cut : {A}{C}conc A -> (hyp A -> conc C) -> conc C #>} <conc A>) -> <conc A>
   = fn {<cut>} <cut A C (D1 cut) (D2 cut)> =>
                                          (case (caElim ({<cut>} <D1 cut>))
                                          of <D1'> => case ({<h>} caElim ({<cut>} <D2 cut h>))
                                                       of {<h>} <D2' h> => ca <D1'> <D2'>)
      | {<cut>} <axiom H> => <axiom H>
      | {<cut>} <impr (D1 cut)> => (case {<h>} caElim ({<cut>} <D1 cut h>)
                                      of {<h>} <D1' h> => <impr D1'>)
      
      | {<cut>} <impl (D1 cut) (D2 cut) H> =>
                                  (case caElim ({<cut>}<D1 cut>)
                                     of <D1'> => case {<h>} caElim ({<cut>} <D2 cut h>)
                                                   of {<h>} <D2' h> => <impl D1' D2' H>);
