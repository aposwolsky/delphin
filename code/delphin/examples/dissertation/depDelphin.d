(* Delphin source code for (dependent) Delphin chapter
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


(* Formulas (Example 2.2.2) *)
sig <o : type>  %name A
    <ar : o -> o -> o> %infix right 10 
    <p : o> (* base type... we could also represent them as LF variables *) ;
 

(* Natural Deduction (Example 2.2.3) *)
sig <nd : o -> type> %name D d
    <impi : (nd A -> nd B) -> nd (A ar B)> 
    <impe : nd (A ar B) -> nd A -> nd B> ;


(* Typed Combinators (AKA Hilbert-Style Calculus) (Example 2.2.4) *)
sig <comb : o -> type> %name H h
    <K : comb (A ar B ar A)>
    <S : comb ((A ar B ar C) ar (A ar B) ar A ar C) > 
    <MP : comb (A ar B) -> comb A -> comb B> ;

(* Well-formed untyped $\lambda$-expressions 
   a la de Bruijn (Example 2.2.5) *)

   (* an expression of type "variable N" is a number representing 1 to N *)
   sig <variable : nat -> type> %name X
       <one : variable (s N)>
       <succ : variable N -> variable (s N)> ;

   (* Expressions (indexed by size of context) *)
   sig <term : nat -> type> %name T t
       <var' : variable P -> term P>
       <lam' : term (s P) -> term P>
       <app' : term P -> term P -> term P> ;

(* Equality relation (Example 2.2.6) *)
sig <equiv : {P} exp -> term P -> type>
    <eqVar : equiv P E (var' X) -> equiv (s P) E (var' (succ X))> 
          (* eqVar is saying:
	   *   if E is the Xth variable when the context has size P,
           *   then E is also the (X+1)st variable in the same context 
           *        extended with one element.
           *)
    <eqLam : ({x:exp} (equiv (s P) x (var' one)) -> equiv (s P) (E x) T) 
              -> equiv P (lam [x] E x) (lam' T)>
    <eqApp : equiv P E1 T1 -> equiv P E2 T2 -> equiv P (app E1 E2) (app' T1 T2)>;



(* Simple identity function *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun id : <A:o> -> <nd A> -> <nd A>
    = fn <A> => fn <D> => <D>;

(* First (BAD) attempt at recursive identity function (Example 4.1.1) *)
(* Causes Match Non-Exhaustive Warnings on inner functions
 * as well as Termination Warnings since the order is set 
 * defaultly to the order of the explicit arguments, but 
 * we want the order to only be on the second argument.
 * (Solution is to make the first argument implicit.)
 *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun id1 : <A:o> -> <nd A> -> <nd A>
     = fn <A ar B> => (fn <impi [d] D d> => (case {<d:nd A>} id1 <B> <D d>
                                            of   {<d:nd A>} <D' d> => <impi [d:nd A] D' d>)
                       )
        | <B> => (fn <impe D1 D2> => 
                          let
                            val <D1'> = id1 <A ar B> <D1>
                            val <D2'> = id1 <A> <D2>
                          in
			    <impe D1' D2'>
                          end)
        | <A> => fn <d#> => <d>;

(* Good (fully explicit) recursive identity function (Example 4.1.2) 
 * Causes Termination Warnings since the order is set 
 * defaultly to the order of the explicit arguments, but 
 * we want the order to only be on the second argument.
 * (Solution is to make the first argument implicit.)
 *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun id2 : (<A:o> and <nd A>) -> <nd A>
     = fn (<A ar B> and <impi [d] D d>) => (case {<d:nd A>} id2 (<B> and <D d>)
                                            of   {<d:nd A>} <D' d> => <impi [d:nd A] D' d>)
        | (<B> and <impe D1 D2>) => 
                          let
                            val <D1'> = id2 (<A ar B> and <D1>)
                            val <D2'> = id2 (<A> and <D2>)
                          in
			    <impe D1' D2'>
                          end
        | (<A> and <d#>) => <d>;

(* Final recursive identity function utilizing implicit types (Example 4.1.3) *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun id3 : <nd A> -> <nd A>
     = fn <impi [d] D d> => (case {<d>} id3 <D d>
                               of {<d>}<D' d> => <impi [d] D' d>)
        | <impe D1 D2> => let
                            val <D1'> = id3 <D1>
                            val <D2'> = id3 <D2>
                          in
			    <impe D1' D2'>
                          end
        | <d#> => <d>;

                        
(* Combinators to natural deduction derivations (Example 4.5.1 and 5.4.1) *)
params = . ;
fun hil2nd : <comb A> -> <nd A> = 
    fn <K> => <impi [x:nd A] impi [y:nd B] x> 
     | <S> => <impi [x:nd (A ar B ar C)]
		     impi [y:nd (A ar B)]
		     impi [z:nd A] impe (impe x z) (impe y z)>

     | <MP H1 H2> => let
		      val <D1> = hil2nd <H1>
		      val <D2> = hil2nd <H2>
		     in 
		       <impe D1 D2>
		     end;


(* Bracket Abstraction (Example 4.5.2 and 5.4.2) *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun ba : <comb A -> comb B> -> <comb (A ar B)> 
  = fn <[x] x> => <MP (MP S K) (K : comb (A ar A ar A))>
     | <[x] MP (H1 x) (H2 x)> =>  
                      let
                        val <H1'> = ba <[x] H1 x>
                        val <H2'> = ba <[x] H2 x>
                      in
                        <MP (MP S H1') H2'>
                      end

     | <[x] H> => <MP K H> ;

type ndParamFun = (<nd B#> -> <comb B>)

(* Natural deduction derivations to Combinators (Example 4.5.3 and 5.4.3) *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun nd2hil : ndParamFun  -> <nd A> -> <comb A> 
 = fn W =>
      fn <impi [d] D d> => 
	    (case ({<d>}{<h>} nd2hil (W with <d> => <h>) <D d>)
	      of ({<d>}{<h>} <H h>) => ba <[h] H h>)
       | <impe D1 D2> => 
	    let
	      val <H1> = nd2hil W <D1>
	      val <H2> = nd2hil W <D2>
	    in
	      <MP H1 H2>
	    end
	     
       | <d#> => W <d>;

(* Sample execution (Example 4.5.4 and 5.4.4) *)
val test-nd2hil = nd2hil (fn .)  <impi [d:nd p] d> ;
(* OUTPUT:
 * val test-nd2hil : <comb (p ar p)>
 *     = <MP (MP S K) K>
 *)


(* HOAS to de Bruijn (Example 4.6.1 and 5.4.5) *)
(* We comment out the first argument because it is inferable
 * and we do not want it in the termination order *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun toDebruijn : (* <P:nat> -> *) (<E:exp#> -> <X: variable P> * <equiv P E (var' X)>) 
                 -> <E:exp> -> <T:term P> * <equiv P E T>
  = (* fn <P> => *)
     fn W =>
      (fn <lam [x] E x> => 
            let
	      val W' : <x:exp#> -> <Y: variable (s P)> * <equiv (s P) x (var' Y)> 
		= fn <x#> => let val (<Y>,<D>) = W <x> in (<succ Y>, <eqVar D>) end
	    in
              case ({<x:exp#>}{<d:(equiv (s P) x (var' one))#>} 
                           toDebruijn (* <s P> *) (W' with <x> => (<one>,<d>)) <E x>)
               of {<x>}{<d>}(<T>, <D x d>) => (<lam' T>, <eqLam [x] [d] D x d>)
	    end

        | <app E1 E2> => 
            let
		val (<T1>,<D1>) = toDebruijn (* <P> *) W <E1>
		val (<T2>,<D2>) = toDebruijn (* <P> *) W <E2>
             in
                 (<app' T1 T2>, <eqApp D1 D2>)
             end

       | <x#> => 
		let
		   val (<Y>, <D>) = W <x>
		in
		   (<var' Y>, <D>)
		end);

(* de Bruijn to HOAS (Example 4.6.2 and 5.4.6) *)
(* We comment out the first argument because it is inferable
 * and we do not want it in the termination order *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;
fun toHOAS : (* <P:nat> -> *) (<X:variable P> -> <E:exp> * <equiv P E (var' X)>) 
             -> <T:term P> -> <E:exp> * <equiv P E T>
  = (* fn <P> => *)
     fn W =>
       (fn <lam' T> =>
	     (case ({<x:exp>}{<d:equiv (s P) x (var' one)>} toHOAS (* <s P> *)
                                   ((fn  {<x>}{<d>} (<one> => (<x>, <d>))
				    |  {<x>}{<d>} (<succ X> => (let 
								  val (<E>, <D>) = W <X>
								in		
								  {<x>}{<d>} (<E>, <eqVar D>)
								end) \x \d)
				   ) \x \d)
                                  <T>)
                of {<x>}{<d>} (<E x>, <D x d>) => (<lam [x] E x>, <eqLam [x] [d] D x d>))

        | <app' T1 T2> =>
            let
		val (<E1>,<D1>) = toHOAS (* <P> *) W <T1>
		val (<E2>,<D2>) = toHOAS (* <P> *) W <T2>
             in
                 (<app E1 E2>, <eqApp D1 D2>)
             end

        | <var' X>  => W <X>);
 

(* Sample conversions (Example 4.6.3) *)
val test1 : (<T:term z> * _) = toDebruijn (* <z> *) (fn .)  <lam [x] lam [y] app x y>;
(* OUTPUT:
 * val test1 : <T : term z> * <equiv z (lam ([x:exp] lam ([y:exp] app x y))) T>
 *     = <lam' (lam' (app' (var' (succ one)) (var' one)))> ,
 *          <eqLam
 *              ([x:exp] [d:equiv (s z) x (var' one)]
 *                  eqLam
 *                     ([x1:exp] [d1:equiv (s (s z)) x1 (var' one)]
 *                         eqApp (eqVar d) d1))>
 *)

val test2 = let 
	     val (<T>,<_>) = test1
	     val (<E>,<_>) = toHOAS (* <z> *) (fn .) <T>
	   in
	     <E>
	   end;
(* OUTPUT:
 * val test2 : <exp>
 *     = <lam ([x:exp] lam ([x1:exp] app x x1))>
 *)
