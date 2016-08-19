(* Delphin source code for SimpleDelphin Chapter
 * by Adam Poswolsky
 *)

(* Natural Numbers (Example 2.1.1) *)
sig <nat : type> %name N n
    <z : nat>
    <s : nat -> nat>;

(* Untyped $\lambda$-expressions using HOAS (Example 2.1.2) *)
sig <exp : type> %name E x
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>;

(* Untyped $\lambda$-expressions a la de Bruijn (Example 2.1.4) *)

   (* Variables *)
   sig <variable : type> %name X
       <one : variable>
       <succ : variable -> variable>;

   (* Expressions *)
   sig <term : type> %name T t
       <lam' : term -> term>
       <app' : term -> term -> term>
       <var' : variable -> term>;

(* Untyped Combinators (Example 2.1.5) *)
sig <comb : type> %name C u
    <K : comb>
    <S : comb> 
    <MP : comb -> comb -> comb> ;


(* Addition (Example 3.3.3) *)
params = <exp>, <comb>;
fun plus : <nat> -> <nat> -> <nat> 
 = fn <z> <M> => <M>
    | <s N> <M> => let 
		     val <x> = plus <N> <M>
                   in 
		     <s x>
	           end;

(* Closed Eager Evaluator (Example 3.3.4 and 5.2.3 *)
params = .;
fun eval : <exp> -> <exp> 
 = fn <app E1 E2> => (case (eval <E1>, eval <E2>) of
                      (<lam [x] F x>, <V>) => eval <F V>
                       (* Match Non-Exhaustive Warning:  We do not handle <app> *)  
                       (* Termination Warning:  <F V> not smaller than <app E1 E2> *)
                     )
    | <lam [x] E x> => <lam [x] E x> ;

(* Open Evaluator (Example 3.3.5) 
 * This is also for Example 5.2.2, but we
 * use a different world than in the code because we are limited to simply-typed examples
 * The important part is that the world contains "exp".
 *)
params = <exp>, <comb>;
fun evalBeta : <exp> -> <exp> 
 = fn <app E1 E2> => (case (evalBeta <E1>, evalBeta <E2>)
                      of (<lam [x] F x>, <V>) => evalBeta <F V>
                            (* Termination Warning:  <F V> not smaller than <app E1 E2> *)
                       | (<x>, <V>) => <app x V>)
    | <lam [x] E x> => (case ({<x>} evalBeta <E x>)
                         of {<x>}<E' x> => <lam [x] E' x>)
    | <x#> => <x> ;


(* 
 * Sample execution of evalBeta 
 * (Example 3.3.6 and 5.2.4) 
 *)
val sample1 = evalBeta <lam [y:exp] y> ;
(* OUTPUT:
 * val sample1 : <exp>
 *     = <lam ([x:exp] x)>
 *)



(* Variable Counting (Example 3.3.7 *)
params = <exp>, <comb>;
fun cntvar  : <exp> -> <nat>
 = fn <app E1 E2>     =>  plus (cntvar <E1>) (cntvar <E2>)
    | <lam [x] E x>   =>  (case ( {<x>} cntvar <E x>)
                            of  ({<x>} <N>)  => <N>)
    | [<x:exp#>] <x>  => <s z>;

(* Sample execution of cntvar (Example 3.3.8) *)
val sample2 = cntvar <lam [y:exp] app y y> ;
(* OUTPUT:
 * val sample2 : <nat>
 *     = <s (s z)>
 *)


(* Lemma 3.4.2 is over any type A, $\tau$ and $\sigma$,
 * but we just show it for one example.
 *)
params = *;
fun lemma-part1 : ({<x:exp#>} (<exp> -> <nat>))  -> (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) 
 = fn u1 => fn u2 => {<x:exp#>} (u1 \x) (u2 \x) ;

params = *;
fun lemma-part2 : (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) -> ({<x:exp#>} (<exp> -> <nat>))
 = fn u1 => fn {<x:exp#>} ((E \x) => (u1 E) \x) ;

params = *;
fun lemma-part3 : ({<x:exp#>} (<exp> * <nat>))  -> (({<x:exp#>}<exp>) * {<x:exp#>}<nat>) 
 = fn {<x>}((u1 \x), (u2 \x)) => (u1, u2) ;

params = *;
fun lemma-part4 : (({<x:exp#>}<exp>) * {<x:exp#>}<nat>) -> ({<x:exp#>} (<exp> * <nat>))
 = fn (u1, u2) => {<x:exp#>} ((u1 \x), (u2 \x));


val exampleF : (({<x:exp#>}<exp>) -> {<x:exp#>}<nat>) = fn {<x>} <x> => {<x>} <s z> 
                                                          | {<x>} <_> => {<x>} <z> ;
val lemmaTest = {<x>} ((lemma-part2 exampleF) \x) <x> ;
(* OUTPUT:
 * val exampleF : ({<x : exp#>} <exp>) -> ({<x : exp#>} <nat>)
 *     = fn ...
 * val lemmaTest : {<x : exp#>} <nat>
 *     = {<x : exp#>} <s z>
*)


(* Combinators to $\lambda$-expressions (Example 3.7.1) *)
params = . ;
fun comb2exp : <comb> -> <exp> 
  = fn <K> => <lam [x:exp] lam [y:exp] x> 
     | <S> => <lam [x:exp]
		     lam [y:exp]
		     lam [z:exp] app (app x z) (app y z)>

     | <MP C1 C2> => let
		       val <E1> = comb2exp <C1>
		       val <E2> = comb2exp <C2>
		     in 
		       <app E1 E2>
		     end;

val id1 :  <exp> = comb2exp <MP (MP S K) K> ;
(* OUTPUT:
 * val id1 : <exp>
 *     = <app
 *          (app
 *              (lam
 *                  ([x:exp]
 *                      lam ([y:exp] lam ([z1:exp] app (app x z1) (app y z1)))))
 *              (lam ([x:exp] lam ([y:exp] x))))
 *          (lam ([x:exp] lam ([y:exp] x)))>
 *)

val reducedId1 = evalBeta id1;
(* OUTPUT:
 * val reducedId1 : <exp>
 *        = <lam ([x:exp] x)>
 *)


(* Bracket Abstraction (Example 3.7.2) *)
params = <exp>, <comb>;
fun ba : <comb -> comb> -> <comb> 
  = fn <[x] x> => <MP (MP S K) K>
     | <[x] MP (C1 x) (C2 x)> => 
                      let
                        val <C1'> = ba <[x] C1 x>
                        val <C2'> = ba <[x] C2 x>
                      in
                        <MP (MP S C1') C2'>
                      end
     | <[x] C> => <MP K C> ;


(* Untyped $\lambda$-expressions to Combinators (Example 3.7.3) *)
type convParamFun = <exp#> -> <comb>
params = <exp>, <comb>;
fun exp2comb : convParamFun  -> <exp> -> <comb> 
 = fn W =>
      fn <lam [x] E x> => 
	    (case ({<x>}{<u>} exp2comb (W with <x> => <u>) <E x>)
	      of ({<x>}{<u>} <C u>) => ba <[u] C u>)
       | <app E1 E2> => 
            let
               val <C1> = exp2comb W <E1>
               val <C2> = exp2comb W <E2>
            in
	       <MP C1 C2>
            end
	     
       | <x#> => W <x>;

(* Same as above with desugared "with" (Section 3.7.2) *)
params = <exp>, <comb>;
fun exp2comb : convParamFun  -> <exp> -> <comb> 
 = fn W =>
      fn <lam [x] E x> => 
	    (case ({<x:exp#>}{<u:comb#>} exp2comb 
		                          ((fn {<x>}{<u>}(<x> => <u>)
                                             | {<x>}{<u>}(<y> => 
                                               (let 
                                                  val <R> = W <y> 
                                                in 
                                                  {<x>}{<u>}<R> 
                                                end) \x \u ))
                                              \x \u) 
                                           <E x>)
	      of ({<x:exp#>}{<u:comb#>} <C u>) => ba <[u] C u>)

       | <app E1 E2> => 
            let
	      val <C1> = exp2comb W <E1>
	      val <C2> = exp2comb W <E2>
            in
	      <MP C1 C2>
            end
	     
       | <x#> => W <x>;

(* Example Execution of exp2comb (Example 3.7.4) *)
val idC = exp2comb (fn .) <lam [x] x> ; (* = <MP (MP S K) K> *)
(* OUTPUT:
 * val idC : <comb>
 *     = <MP (MP S K) K>
 *)



(* HOAS to de Bruijn (Example 3.8.1) *)
params = <exp>, <comb>;
fun toDebruijn : (<exp#> -> <variable>) -> <exp> -> <term> 
 = fn W =>
     fn <lam [x] E x> => 
            let
	      val W' = fn <y#> => <succ> @ (W <y>)
	    in
	      case ({<x:exp#>} toDebruijn (W' with <x> => <one>) <E x>)
		of {<x:exp#>}(<T>) => <lam' T>
	    end

       | <app E1 E2> =>
            let
	      val <T1> = toDebruijn W <E1>
	      val <T2> = toDebruijn W <E2>
            in
	      <app' T1 T2>
	    end
 
       | <x#> => <var'> @ (W <x>);

(* de Bruijn to HOAS (Example 3.8.2) *)
params = <exp>, <comb>;
fun toHOAS : (<variable> -> <exp>) -> <term> -> <exp> 
 = fn W =>
     fn <lam' T> =>
	     (case ({<x:exp#>} toHOAS 
                                   ((fn {<x>}(<one> => <x>)
				     | {<x>}(<succ X> => (let val <E> = W <X> in {<x>}<E> end)\x  )) \x)
                                  <T>)
                of {<x>} <E x> => <lam [x] E x>)

      | <app' T1 T2> =>
            let
	      val <E1> = toHOAS W <T1>
	      val <E2> = toHOAS W <T2>
	    in
	      <app E1 E2>
	    end

      | <var' X>  => W <X>;

(* Examples converting between representations (Example 3.8.3) *)
val test1 = toDebruijn (fn .) <lam [x] lam [y] app x y>;
(* OUTPUT:
 * val test1 : <term>
 *     = <lam' (lam' (app' (var' (succ one)) (var' one)))>
 *)

val test2 = toHOAS (fn .) test1;
(* Match Non-Exhaustive Warning generated for "fn ."
 * OUTPUT:
 * val test2 : <exp>
 *     = <lam ([x:exp] lam ([x1:exp] app x x1))>
 *)
