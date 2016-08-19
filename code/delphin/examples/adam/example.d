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


fun cntvar 
 = fn  <lam E> =>
                   (case ( {<x>} cntvar <E x>)
                          of  ({<x>} <N>)  => <N>)
    |  <app E E3> =>
                          plus (cntvar <E>) (cntvar <E3>)
    | <x#> => <s z>;

val example1 = cntvar <lam [x] app x x>;

(* Execute in an extended world.. result stays in the extended world *)
val example2 = {<x:exp#>} cntvar <app x x>;


(* combinator *)
(* Translation from lambda calculus into combinator calculus *)
(* SIMPLY-Typed version *)
fun ded : <comb -> comb> -> <comb>
   = fn <[x] c#> => <c>
   | <[x] x> => <mp (mp s' k) k>
   | <[x] k> => <mp k k>
   | <[x] s'> => <mp k s'>
   | <[x] (mp (C1 x) (C2 x))> =>
       <mp> @ (<mp> @ <s'> @ (ded <C1>)) @ (ded <C2>) ;

val d1 : <comb> = ded <[x:comb] mp k x> ;
val d2 :<comb -> comb> = case ({<c>} <mp k c>) of {<c>} <C c> => <C>;

fun c2d : <exp> -> <comb>
   = fn <x# C> => <C>
   | <app E1 E2> => <mp> @ (c2d <E1>) @ (c2d <E2>)
   | <lam E> => case ({<c:comb#>}{<x:comb -> exp#>} c2d <E (x c)>)
	         of {<c>}{<x>} <C c> => ded <C> ;

val c2d'1  = c2d <lam [x] x>;
val c2d'2  = c2d <lam [x] app x x>;

val c2d'3  = c2d <app (lam [x] x) (lam [x] x)>;
val c2d'4  = c2d <lam [x] lam [y] x>;


(* Dependent-Types:  Copy Example.. *)

fun extend : (<f:exp#> -> <eq f f>) -> {<x:exp#>}{<u:eq x x#>} (<f:exp#> -> <eq f f>) =
  fn W => fn {<x>} {<u>} (x => <u>)  
          | [<e:exp#>] {<x>} {<u>} (e => let
					   val result = W e
					 in
					   {<x>}{<u>} result
					 end \x \u);

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


val example1 = eqfun (fn .) <lam [x] app x x>;




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


val id : {<x:o>} <comb (x ar x)> = {<x:o>} <(mp (mp s k) (k : comb (x ar x ar x)))> ;  


fun ba : <A:o> -> <B:o> -> <comb A -> comb B> -> <comb (A ar B)> 
= fn <A> => fn <A> => (fn <F> => <mp (mp s k) (k : comb (A ar A ar A))>)
	     | <B> => fn <[x] mp (D1 x) (D2 x)> =>
                                           (case ((ba <_> <_> <D1>), (ba <_> <_> <D2>))
	                                    of (<D1'>,<D2'>) => <mp (mp s D1') D2'>)
	               | <[x] U> => <mp k U> ;


fun extendC : (<A:o> -> <D: nd A#> -> <comb A>) -> <B:o> -> {<x:nd B#>}{<y:comb B#>}(<A:o> -> <D: nd A#> -> <comb A>) = 
  fn W => fn <B> => fn {<x>} {<y>} (<B> x => <y>) 
	            | [<e>] {<x>} {<u>} (<A'> e => let
							   val result = W <A'> e
							 in
							   {<x>}{<u>} result
							 end \x \u);

fun extendC : (<A:o> -> <D: nd A#> -> <comb A>) -> <B:o> -> {<x:nd B#>}{<y:comb B#>}(<A:o> -> <D: nd A#> -> <comb A>) = 
  fn W => fn <B> => fn {<x>} {<y>} (<B> x => <y>) 
	            | [<e>] {<x>} {<u>} (<_> e =>  let
							   val result = W <_> e
							 in
							   {<x>}{<u>} result
							 end \x \u);

fun convert : _ -> <A:o> -> <D:nd A> -> <comb A> =
      fn W =>
              fn <B ar C> <impi D'> => (case ({<d>}{<u>} convert ((extendC W <B>) \d \u) <C> <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <B> <C> <D''>) 
               | <A> <impe D1 D2> => (case ((convert W <B ar A> <D1>), (convert W <B> <D2>))
	                                      of (<U1>,<U2>) => <mp U1 U2>) 
	     
	       | [<x:nd A#>] <A> <x> => W <A> x;

fun convert : _ -> <A:o> -> <D:nd A> -> <comb A> =
      fn W =>
              fn <_> <impi D'> => (case ({<d>}{<u>} convert ((extendC W <_>) \d \u) <_> <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <_> <_> <D''>) 
               | <_> <impe D1 D2> => (case ((convert W <_> <D1>), (convert W <_> <D2>))
	                                      of (<U1>,<U2>) => <mp U1 U2>) 
	     
	       | [<x:nd A#>] <A> <x> => W <A> x;



val x1 = {<A>}{<B>} <impi [u:nd A] impi [v:nd B] u> ;
val test = {<A>}{<B>} convert (fn .) <_> <impi [u:nd A] impi [v:nd B] u> ;
val test = {<A>} convert (fn .) <_> <impi [x:nd A] x> ;

val x2 = {<A>}{<B>} < impi [x:nd (A ar B)] impi [y: nd A] impe x y>;
val test = {<A>}{<B>} convert (fn .) <_> < impi [x:nd (A ar B)] impi [y: nd A] impe x y> ;

fun convert : _ -> <<A:o>> -> <D:nd A> -> <comb A> =
      fn W <impi D'> => (case ({<d>}{<u>} convert ((extendC W <_>) \d \u) <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <_> <_> <D''>) 
       | W <impe D1 D2> => (case ((convert W <D1>), (convert W <D2>))
	                                      of (<U1>,<U2>) => <mp U1 U2>) 
	     
       | [<x:nd A#>] W <x> => W <A> x;






(* IMPLICIT EXAMPLE *)
(* BUG:  Re-parsing the output complains about bad dependency! *)

fun extendC : (<A:o> -> <D: nd A#> -> <comb A>) -> <B:o> -> {<x:nd B#>}{<y:comb B#>}(<A:o> -> <D: nd A#> -> <comb A>) = 
  fn W => fn <B> => fn {<x>} {<y>} (<B> x => <y>) 
	            | [<e>] {<x>} {<u>} (<_> e =>  let
							   val result = W <_> e
							 in
							   {<x>}{<u>} result
							 end \x \u);

fun ba : <comb A -> comb B> -> <comb (A ar B)> 
  = fn <F> => <mp (mp s k) (k : comb (A ar A ar A))>
     | <[x] mp (D1 x) (D2 x)> =>   (case ((ba <D1>), (ba <D2>))
	                                 of (<D1'>,<D2'>) => <mp (mp s D1') D2'>)
     | <[x] U> => <mp k U> ;


fun convert : _  -> <D:nd A> -> <comb A> =
      fn W <impi D'> => (case ({<d>}{<u>} convert ((extendC W <_>) \d \u) <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <D''>) 
       | W <impe D1 D2> => (case ((convert W <D1>), (convert W <D2>))
	                                      of (<U1>,<U2>) => <mp U1 U2>) 
	     
       | [<x:nd A#>] W <x> => W <A> x;

val test = {<A>}{<B>} convert (fn .) <impi [u:nd A] impi [v:nd B] u> ;
val test = {<A>} convert (fn .)  <impi [x:nd A] x> ;
val test = {<A>}{<B>} convert (fn .) < impi [x:nd (A ar B)] impi [y: nd A] impe x y> ;