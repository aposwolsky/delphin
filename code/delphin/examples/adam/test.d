(* combinators *)

sig
<o : type> 
<ar : o -> o -> o> %infix right 10
<nd : o -> type>
<impi : (nd A -> nd B) -> nd (A ar B)> 
<impe : nd (A ar B) -> nd A -> nd B> 
<comb : o -> type> 
<k : comb (A ar B ar A)>
<s : comb ((A ar B ar C) ar (A ar B) ar A ar C) > 
<mp : comb (A ar B) -> comb A -> comb B> ;


fun ba : <A:o> -> <B:o> -> <comb A -> comb B> -> <comb (A ar B)> 
= fn <A> => fn <A> => (fn <F> => <mp (mp s k) (k : comb (A ar A ar A))>)
	     | <B> => fn <[x] mp (D1 x) (D2 x)> =>
                                           (case ((ba <_> <_> <D1>), (ba <_> <_> <D2>))
	                                    of (<D1'>,<D2'>) => <mp (mp s D1') D2'>)
	               | <[x] U> => <mp k U> ;




fun extendC : (<A:o> -> <D: nd A#> -> <comb A>) -> <B:o> -> {<x:nd B#>}{<y:comb B#>}(<A:o> -> <D: nd A#> -> <comb A>) = 
  fn W => fn <B> => fn {<x>} {<y>} (<B> => fn x => <y>) 
	            | [<e>] {<x>} {<u>} (<A'> => fn e => let
							   val result = W <A'> e
							 in
							   {<x>}{<u>} result
							 end \x \u);



fun convert : _ -> <A:o> -> <D:nd A> -> <comb A> =
      fn W =>
              fn <_> and <impi D'> => (case ({<d>}{<u>} convert ((extendC W <_>) \d \u) <_> <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <_> <_> <D''>) 
               | <_> and <impe D1 D2> => (case ((convert W <_> <D1>), (convert W <_> <D2>))
	                                      of (<U1>,<U2>) => <mp U1 U2>) 
	     
	       | [<x:nd A#>] <A> and <x> => W <A> x;




val x1 = {<A>}{<B>} <impi [u:nd A] impi [v:nd B] u> ;
val test = {<A>}{<B>} convert (fn .) <_> <impi [u:nd A] impi [v:nd B] u> ;
val test = {<A>} convert (fn .) <_> <impi [x:nd A] x> ;


val x2 = {<A>}{<B>} < impi [x:nd (A ar B)] impi [y: nd A] impe x y>;
val test = {<A>}{<B>} convert (fn .) <_> < impi [x:nd (A ar B)] impi [y: nd A] impe x y> ;



sig 
<nat : type>
<z : nat>
<s : nat -> nat>
<exp : type>
<lam : (exp -> exp) -> exp>
<app : exp -> exp -> exp>
<eq : exp -> exp -> type> 
<eq_app : eq E1 F1 -> eq E2 F2 -> eq (app E1 E2) (app F1 F2)>
<eq_lam : ({x}eq x x -> eq (E x) (F x)) -> eq (lam E) (lam F)>;


fun extend : (<f:exp#> -> <eq f f>) -> {<x:exp#>}{<u:eq x x#>} (<f:exp#> -> <eq f f>) =
  fn W => fn {<x>} {<u>} (x => <u>)  
          | [<e:exp#>] {<x>} {<u>} (e => let
					   val result = W e
					 in
					   {<x>}{<u>} result
					 end \x \u);

val y = {<x>}{<u>} (extend (fn .)\x \u) x ;



fun eqfun : _ -> <e:exp> -> <eq e e> = 
  fn W => 

  (fn <app E1 E2> => (case ((eqfun W <E1>), (eqfun W <E2>))
                                of (<D1>, <D2>) => <eq_app D1 D2>)
   | <lam E> => (case ({<x>}{<u>} eqfun ((extend W) \x \u) <E x>)
                            of ({<x>}{<u>} <D x u>) => <eq_lam D>)

   | [<x:exp#>] <x> => W x) ;


val y = {<x>}{<u>} eqfun ((extend (fn .)) \x \u) <x> ;


val test = eqfun (fn .) <lam [x] app x x>;


fun plus 
 = fn <z> => (fn [<n>] <n> => <n>)
    | [<n1:nat>]<s n1> => fn [<n2:nat>] <n2> => 
	        case (plus <n1> <n2>)
	        of [<n3>](<n3>) => <s n3>;

sig <adam : nat -> type> ;
sig <adamz : adam z> ;
sig <adamind : {x:nat} adam x -> adam (s x)> ;
sig <adamind2 : adam X -> adam (s X)> ;
sig <adambar : adam X -> nat> ;
sig <foo : {x:nat} adam x> ;

fun foo : <E : {n}adam n> ->  unit = 
  fn [<G>]<G> => () ;

fun foo : <E : {n}adam n> ->  unit = 
  fn <G> => () ;


(* Bad dependencies!

val x = (fn <F:{x} adam x> => fn <E:nat> => <F E>) ;
<foo> @ <z>;
<adamind> @ <z> @ <adamz>;

(fn <E : {n}adam n> => fn <F:nat> => <E F>) <foo> <z> ; 
(fn <E : {n}adam n> => fn <F:nat> => <E F>) ;
(fn <E : {n}adam n> => fn <F:nat> => (<E F>, ())) ;

(* parameter dependency if smartInj *)
val x = 
   fn [<E : {x : nat} adam x>] <E> =>
                                  (fn <F> => (<E F>, ()));

(* Abstraction creates three epsilons! *)
val x = 
   fn <E : {x : nat} adam x> =>
                                  (fn [<F:nat>] <F> => (<E F>, ()));

val x = 
      fn <E: {x : nat} adam x> =>  (fn <F> => (<E F>, ()));


fn <E:{x} adam x> => fn <F> => (<E F>,()) (* works when smartInj = false*)

*)


fun foo : <E : {n}adam n> -> <N:nat> -> <X1: adam N> * unit = 
  fn [<G>]<G> => fn <F:nat> => (<(G F)>,()) ;

fun foo : <E : {n}adam n> -> <N:nat> -> <X1: adam N> * unit = 
  fn <G> => fn <F:nat> => (<(G F)>,()) ;


fun foo : <E : {n}adam n> ->  unit = 
  fn <G> => () ;


fun foo : <E : {n}adam n> -> <N:nat> -> <adam N> = 
  fn <E:{n}adam n> => fn <F:nat> => (<(E F) : adam F>,()) ;


fun foo : <E : {n}adam n> -> <N:nat> -> <adam N> = 
  fn <E:{n}adam n> => fn <F:nat> => (<(E F) : adam F>) ;


fun foo : <E : {n : nat} adam n> -> <N : nat> -> (<X1 : adam N> * unit) = 
   fn [<E : {x : nat} adam x>] <E> =>
                                  (fn [<F : nat>] <F> => (<E F> , ()));


val f : <mm : {x} adam x> -> <w:nat> -> (<NN : adam w> * unit)
 = (fn <E : {x} adam x> => fn <F> => (<E F>,()));


val f : <mm : {x} adam x> -> unit
 = (fn [<e>]<e> => ()) ;




<adambar> @ <adamz> ;

(* or this *)
(fn <E : (adam z -> nat)> => (fn <F> => <E F>)) <adambar> <adamz> ;


fun cntvar 
 = fn  <lam E> =>
                   (case ( {<x>} cntvar <E x>)
                          of  ({<x>} <N>)  => <N>)
    |  <app E E3> =>
                          plus (cntvar <E>) (cntvar <E3>)
    | [<x:exp#>] <x> => <s z>;


fun adam  = fn [<n2:nat>] <n2> => (<n2>, ());

fun adam = (fn [<N1 : nat>] <N1> =>
                            (fn [<N2 : nat>] <N2>  => <N2> , ()));

sig <adam : nat -> type> ; sig <adamz : adam z> ;


val adam = (fn [<N1 : nat>] <N1> =>
                            (fn [<N2 : nat>] (<N2>, ())  => <N2> , ()));




fun cntvar 
 = fn [<E>] <lam E> =>
                   (case ( { <x>  } cntvar <E x>)
                          of [<N>] { <x : exp#> } <N>  => <N>)
    | [<E1>] [<E2>] <app E1 E2> =>
                          plus (cntvar <E1>) (cntvar <E2>)
    | [<x:exp#>] <x> => <s z>;



fun test = fn <s N> => <N> ;

fun plus : <nat> -> <nat> -> <nat>
 = fn <z> => (fn N => N)
    | <s N1> => fn M => 
	        case (plus <N1> M)
	        of (<N3>) => <s N3>;

fun plus : <nat> -> <nat> -> <nat>
 = fn <z> and N => N
    | <s N1> and M => 
	        case (plus <N1> M)
	        of (<N3>) => <s N3>;


fun cntvar 
 = fn <lam E> =>
                   (case ( {<x>} cntvar <E x>)
                          of  ({<x>} <N>)  => <N>)
    |  <app E1 E2> =>
                          plus (cntvar <E1>) (cntvar <E2>)
    | [<x:exp#>] <x> => <s z>;

fun dist : ({<x:nat#>} <nat -> nat>) -> ({<x:nat#>} <nat>) -> {<x:nat#>} <nat>
  = fn . ;

fun foo = fn [<n>] <s n> => () ;

fun foo : <nat> -> unit = fn <z> => ();
sig <cp : exp -> exp -> type> ;

sig <cp_app : cp E1 F1 -> cp E2 F2 -> cp (app E1 E2) (app F1 F2)> ;
sig <cp_lam : ({x}cp x x -> cp (E x) (F x)) -> cp (lam E) (lam F)> ;

sig <foo : nat -> type> ;
sig <fooz : foo (s z)> ;
	

fun foo = fn [<n>] <s n> => (<z>, ()) : <nat> * unit ;

fun plus : <nat> -> <nat> -> <nat> * unit
 = fn <z> => (fn [<n:nat>] <n> => (<n>, ()))
    | [<n1 : nat>]<s n1> => fn [<n2:nat>] <n2> => 
	        case ((plus <n1> <n2>) : <nat> * unit)
	        of [<n3:nat>]((<n3>,()) : <nat> * unit) => ((<s n3>, ()) : <nat> * unit);





fun cntvar : <exp> -> <nat> * unit
 = fn [<E1:exp>][<E2:exp>] <app E1 E2> => 
	(case ((cntvar <E1>) : <nat> * unit) of
	   [<N1:nat>](<N1>,()): <nat> * unit  => case ((cntvar <E2>) : <nat> * unit) 
                                  of [<N2:nat>](<N2>,()) : <nat> * unit => ((plus <N1> <N2>) : <nat> * unit))
 | [<E : exp -> exp>] <lam E> =>
                   case (({<x:exp#>} cntvar <E x>) : {<x:exp#>} <nat> * unit)
                          of [<N:nat>] {<x:exp#>} (<N>,()) : <nat> * unit => ( (<N>, ()) : <nat> * unit );
                  


fun foo : <nat> -> <nat> * unit = fn <z> => foo <z>;



fun plus 
 = fn <z> => (fn [<n>] <n> => (<n>, ()))
    | [<n1>]<s n1> => fn [<n2>] <n2> => 
	        case (plus <n1> <n2>)
	        of [<n3>](<n3>,()) => (<s n3>,());

fun plus : <nat> -> <nat> -> <nat> * unit
 = fn <z> => (fn [<n:nat>] <n> => (<n>, ()))
    | [<n1:nat>]<s n1> => fn [<n2:nat>] <n2> => 
	        case (plus <n1> <n2>)
	        of [<n3:nat>](<n3>,()) => (<s n3>,());


(* THIS CRASHES!!!? *)
case (<z>, ()) of ((<z>, ()))=> ((<z>,()));

case (<z>, ()) of ((<z>, ()) : <nat> * unit)=> ((<z>,()) : <nat> * unit);

case ((<z>, ()) : <nat> * unit)  of (<z>, ()) => ((<z>,()) : <nat> * unit);

fn ((<z>, ()) : <nat> * unit)=> ((<z>,()) : <nat> * unit);
fn (<z>, ())=> ((<z>,()) : <nat> * unit);



fun plus : <nat> -> <nat> -> <nat> * unit
 = fn <z> => (fn  <N:nat> => (<N>, ()));

fun foo : <nat> -> (unit * unit)
  = fn <z> => ((), ());


fun addOne : <nat> -> <nat> * unit
   = fn <z> => (<s z>, ());

fun plus : <nat> -> <nat> -> <nat> * unit
 = fn <z> => (fn [<n:nat>] <n> => (<n>, ()))
    | [<n1:nat>]<s n1> => fn [<n2:nat>] <n2> => (<n2>, ());


fun mutualrectest1 = fn <z> => <s z>
                      | <s X> => mutualrectest2 <X> 
and mutualrectest2 = fn <X> => mutualrectest1 <z> ;

fun foo : <exp> -> <exp> 
      = fn <lam E> => case ({<x>} foo <E x>)
                      of {<x>}<_> => <lam [x] x> ;
(* this is equivalent to *)

fun foo : <exp> -> <exp> = 
   fn [<E : exp -> exp>] (<lam ([x:exp] E x)> => (fn [<X1 : exp -> exp>] ({<x : exp#>} <X1 x> => <lam ([x:exp] x)>)) ({<x : exp#>} foo <E x>));

