(* 
 * First-Order Logic
 * Fragment with implication, negation, universal quantification.
 * 
 * Author: Adam Poswolsky
 * (converted Twelf code by Frank Pfenning into Delphin
 * FOR THE TWELF ENTHUSIAST, it may be very illuminating
 * to compare this to fol.elf
 *
 * This code is from the article
 * 
 *    Logical Frameworks
 *    Handbook of Automated Reasoning
 *    Alan Robinson and Andrei Voronkov, editors
 *    Chapter 16
 *    Elsevier Science and MIT Press
 *)

sig 
  <i : type> %name T x (* individuals *)
  <o : type> %name A p (* formulas *);

(* Formulas *)
sig 
  <imp    : o -> o -> o>   %infix right 10
  <not    : o -> o>        %prefix 12
  <forall : (i -> o) -> o>;

(* Natural deductions *)

sig
  <nd : o -> type> %name D u

  <impi    : (nd A -> nd B) -> nd (A imp B)>
  <impe    : nd (A imp B) -> nd A -> nd B>

  <noti    : ({p:o} nd A -> nd p) -> nd (not A)>
  <note    : nd (not A) -> {C:o} nd A -> nd C>

  <foralli : ({a:i} nd (A a)) -> nd (forall A)>
  <foralle : nd (forall A) -> {T:i} nd (A T)>;

(* Allow the creation of parameters of type "nd A, o, and i" *)
(* This is NOT needed for type-checking, only for proving totality *)
params = <nd A>, <o>, <i> ;


(* Example *)
val example1 : {<A>}{<B>} <nd (A imp (B imp A))>
  = {<A>}{<B>} <impi [u:nd A] impi [v:nd B] u>;

val example2 : <nd (A imp (B imp A))>
  = <impi [u:nd A] impi [v:nd B] u>;


(*  Hilbert deductions *)

sig <hil : o -> type> %name H u  (* Hilbert deductions *)

    <k : hil (A imp (B imp A))>
    <s : hil ((A imp (B imp C)) imp ((A imp B) imp (A imp C)))>

    <n1 : hil ((A imp (not B)) imp ((A imp B) imp (not A)))>
    <n2 : hil ((not A) imp (A imp B))>

    <f1 : {T:i} hil ((forall [x:i] A x) imp (A T))>
    <f2 : hil ((forall [x:i] (B imp A x)) imp (B imp forall [x:i] A x))>

    <mp : hil (A imp B) -> hil A -> hil B>
    <ug : ({a:i} hil (A a)) -> hil (forall [x:i] A x)>;

params = . ; (* no parameters allowed *)

(* Local reductions *)
fun localRed : <nd A> -> <nd A> = 
   fn <impe (impi [u:nd A] D u) E> => <D E>
    | <note (noti [p:o] [u:nd A] D p u) C E> => <D C E>
    | <foralle (foralli [a:i] D a) T> => <D T>;

(* Local expansions *)
fun localExpansion : <nd A> -> <nd A> =
   fn [<D:nd (A imp B)>] <D> => <impi [u: nd A] impe D u> 
    | [<D:nd (not A)>] <D> => <noti [p:o] [u:nd A] note D p u>
    | [<D:nd (forall A)>] <D> => <foralli [a:i] foralle D a>;


(* Sequent calculus search result *)

val dn : {<A>} <nd (A imp not not A)> = 
   {<A>} <impi [u:nd A] noti [p:o] [w:nd (not A)] note w p u>;

(* Translating Hilbert derivations to natural deductions *)

params = <i>, <o> ; (* allow parameters of type i and o*)
(* NOTE:  we do not need the "o" to prove the totality of hilnd, but we will later
 * use hilnd in examples in worlds with formulas (o).
 *)
fun hilnd : <hil A> -> <nd A> = 
    fn <k> => <impi [u:nd A] impi [v:nd B] u> 
     | <s> => <impi [u:nd (A imp B imp C)]
		     impi [v:nd (A imp B)]
		     impi [w:nd A] impe (impe u w) (impe v w)>
     | <n1> => <impi [u:nd (A imp (not B))]
			   impi [v:nd (A imp B)]
			   noti [p:o] [w:nd A]
			   note (impe u w) p (impe v w)>
     | <n2> => <impi [u:nd (not A)]
			   impi [v:nd A] note u B v> 
     | <f1 T> => <impi [u:nd (forall [x:i] A x)] foralle u T>
     | <f2> => <impi [u:nd (forall [x:i] (B imp A x))]
		     impi [v:nd B]
		     foralli [a:i] impe (foralle u a) v>

     | <mp H1 H2> => let
		      val <D1> = hilnd <H1>
		      val <D2> = hilnd <H2>
		     in 
		       <impe D1 D2>
		     end
     | <ug H1> => (case {<a:i>} hilnd <H1 a>
		     of ({<a:i>} <D1 a>) => <foralli D1>) ;

(* Example *)
val id' :  {<A:o>} <nd (A imp A)> = {<A:o>} hilnd <mp (mp s k) (k : hil (A imp (A imp A)))> ;
(* evaluation result
val id' : {<A : o#>} <nd (A imp A)>
    = {<A : o#>} <impe
                     (impe
                         (impi
                             ([u:nd (A imp (A imp A) imp A)]
                                 impi
                                    ([v:nd (A imp A imp A)]
                                        impi
                                           ([w:nd A] impe (impe u w) (impe v w)))))
                         (impi ([u:nd A] impi ([v:nd (A imp A)] u))))
                     (impi ([u:nd A] impi ([v:nd A] u)))>
*)


(* The deduction theorem for Hilbert derivations *)
params = <i>, <o>, <nd A>, <hil A> ; (* allow parameters of type i,o, and hil A *)

fun ded : <hil A -> hil B> -> <hil (A imp B)> =
  fn <[u:hil A] u> =>  <mp (mp s k) (k : hil (A imp (A imp A)))>
   | <[u:hil A] k> =>  <mp k k>
   | <[u:hil A] s> =>  <mp k s>
   | <[u:hil A] n1> => <mp k n1>
   | <[u:hil A] n2> => <mp k n2>
   | <[u:hil A] f1 T> => <mp k (f1 T)>
   | <[u:hil A] f2> => <mp k f2>
   | <[u:hil A] mp (H1 u) (H2 u)> => 
           let 
	     val <H1'> = ded <H1>
	     val <H2'> = ded <H2>
	   in 
	     <mp (mp s H1') H2'>
	   end
   | <[u:hil A] ug (H1 u)> =>
	   (case {<a:i>} ded <[u:hil A] H1 u a>
	      of ({<a:i>} <H1' a>) => <mp f2 (ug H1')>)

   (* finally handle parameters of hil A *)
   | <[w: hil C] v#> => <mp k v> ; 

(*  Mapping natural deductions to Hilbert derivations. *)






(* ndhil simplified using Delphin "with" construct 
 * See ../examples08.d for an expanded version (a "convert" function not utilizing
 * the "with" syntactic sugar)
 *)				     
params = <i>, <o>, <nd A>, <hil A> ; (* allow parameters of type i,o, nd A, and hil A *)
(* NOTE that this is simpler than the world used in Twelf
 * as we do not need parameters of "ded" or "ndhil" 
 * HOWEVER, we do need to pass a meta-level function of type convParamFun saving the relationship
 * between parameters of "nd A" and "hil A"
 *)

type convParamFun = (<A:o> -> <D: nd A#> -> <hil A>);

fun ndhil : convParamFun -> <nd A> -> <hil A> =
  fn W <impi D1> =>
	    (case ({<u:nd A1>}{<v: hil A1>} ndhil (W with <A1> <u> => <v>) <D1 u>)
	      of ({<u>}{<v>} <H1 v>) => ded <H1>)

   | W <impe D1 D2> =>
	       let
		 val <H1> = ndhil W <D1>
		 val <H2> = ndhil W <D2>
	       in
		 <mp H1 H2>
	       end

   | W <noti D1> =>
	    (case ({<p:o>} {<u:nd A1>}{<v: hil A1>} ndhil (W with <A1> <u> => <v>) <D1 p u>)
	      of ({<p>}{<u>}{<v>} <H1 p v>) => 
		                  let
				    val <H1'> = ded <H1 (not A1)>
				    val <H1''> = ded <H1 A1> 
				  in
				    <mp (mp n1 H1') H1''>
				  end)
   | W <note D1 C D2> =>
        let 
	  val <H1> = ndhil W <D1>
	  val <H2> = ndhil W <D2>
	in
	  <mp (mp n2 H1) H2>
	end

   | W <foralli D1> =>
	(case {<a:i>} ndhil (W with .) <D1 a>
	   of {<a:i>} <H1 a> => <ug H1>)

   | W <foralle D1 T> =>
	   let
	     val <H1> = ndhil W <D1>
	   in
	     <mp (f1 T) H1>
	   end

   (* And finally, we handle parameters of type "nd _" *)
   | W <x#> => W <_> <x>;