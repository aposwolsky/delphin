(* Conversion of simply-types HOAS terms into a debruijn notation *)
(* Author: Adam Poswolsky *)

(* Here we convert HOAS terms (exp) into debruijn terms (term N)
 * where N indicates the size of the context.  We also
 * encode what it means for two terms to be equal in "trans"
 * and show that our conversion function in both directions is an isomorphism.
 *
 * It is useful to compare this to the Twelf alternative at
 * http://twelf.plparty.org/wiki/Concrete_representation
 * (Notice that they use an inadequate encoding of terms (their "fvar^" constant),
 * we solve the problem using adequate encodings.)
 * 
 *
 * This example highlights the versatile use of parameter functions
 * as the addition of a new parameter x will map "x to 1" and then add 1
 * to the mapping of all other parameters. 
 *)


(* HOAS representation of lambda-terms *)
sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>;


sig <nat : type> 
     <z : nat>
     <s : nat -> nat> ;

(* meaning (variable N) = A number representing variables in a context of size N (1 to N) *)
sig <variable : nat -> type>
    <var_one : variable (s N)>
    <var_s : variable N -> variable (s N)> ;

(* Encoding of well-formed de-bruijn terms with contexts of length N *)
sig <term : nat -> type>
    <bvar' : variable N -> term N>
    <lam' : term (s N) -> term N>
    <app' : term N -> term N -> term N> ;

(* Equality relation we will use to show the isomorphism *)
sig <trans : exp -> term N -> type>
    <trans_app : trans E1 T1 -> trans E2 T2 -> trans (app E1 E2) (app' T1 T2)>
    <trans_lam : ({x:exp} (trans x (bvar' (var_one : variable (s N) ))) -> trans (E x) (T: term (s N) )) -> trans (lam E) (lam' T)>
    <trans_var : trans E (bvar' M) -> trans E (bvar' (var_s M))> ;
          (* trans_var is saying:
	       if E is the Mth variable when the context has size N
               then E is also the (M+1)st variable in the same context extended with one element.
           *)

(* These next two relations allow us to state that terms/exps are equal(identical).
 * We will say if E --> E'  and E' --> E''  then  E equals E''.
 *)
sig <eqexp : exp -> exp -> type>
    <eqid : eqexp E E>;

sig <eqterm : term N -> term N -> type>
    <eqtermid : eqterm T T>;

(* It is useful to have an empty type to argue about something being impossible.
 * This is useful for coverage in stating that certain cases are impossible.
 *)
sig <empty : type>;

(* Standard less-than relation *)
sig <lt : nat -> nat -> type> 
    <lt_b : lt M (s M)>
    <lt_ind : lt M N -> lt M (s N)> ;

(* Here we indicate what parameters will be dynamically created.
 * We will create "exp"s as well as proofs that "parameters of exp are mapped to var_one in some context"
 *)
params = <exp>, <trans (E#) (bvar' var_one)> ;

(* Here we use a parameter function mapping exp# to variables and proofs.
 * This function extends the parameter function to map a fresh x to var_one, and to increment all the rest
 *)
fun extend : (<E:exp#> -> <M: variable N> * <trans E (bvar' M)>) ->
		{<x:exp>}{<d: trans x (bvar' (var_one : variable (s N) ))>}(<E:exp#> -> <M: variable (s N)> * <trans E (bvar' M)>) 
		= fn W => fn {<x:exp>}{<d: trans x (bvar' (var_one : variable (s N) ))>} (<x> =>
										(* parameter is mapped to one *)
										(<var_one>, <d>))
		            |{<x:exp>}{<d: trans x (bvar' (var_one : variable (s N) ))>} (<y> =>
				(let
				    val (<M>, <D>) = W <y> 
				in
				    {<x>}{<d>} (<var_s M>, <trans_var D>)
				end \x \d) );

fun toDebruijn : (<E:exp#> -> <M: variable N> * <trans E (bvar' M)>) -> <E:exp> -> <T:term N> * <trans E T>
    = fn W <app E1 E2> => 
            let
		val (<T1>,<P1>) = toDebruijn W <E1>
		val (<T2>,<P2>) = toDebruijn W <E2>
             in
                 (<app' T1 T2>, <trans_app P1 P2>)
             end
       | W <lam E> => 
             (case ({<x:exp>}{<d:trans x (bvar' (var_one : variable (s N)))>} toDebruijn ((extend W) \x \d) <E x>)
               of {<x>}{<d>}(<T>, <P x d>) => (<lam' T>, <trans_lam P>))

       | W <x#> => 
		let
		   val (<V>, <D>) = W <x>
		in
		   (<bvar' V>, <D>)
		end;

    

fun toHOAS : (<M:variable N> -> <E:exp> * <trans E (bvar' M)>) -> <T:term N> -> <E:exp> * <trans E T>
   = fn W <app' T1 T2> =>
            let
		val (<E1>,<D1>) = toHOAS W <T1>
		val (<E2>,<D2>) = toHOAS W <T2>
             in
                 (<app E1 E2>, <trans_app D1 D2>)
             end

      | W <bvar' M>  => W <M>
 
      | W <lam' T> =>
	     (case ({<x:exp>}{<d:trans x (bvar' (var_one : variable (s N)))>} toHOAS 
                                   ((fn  {<x>}{<d>} (<var_one> => (<x>, <d>))
				    |  {<x>}{<d>} (<var_s M> => (let 
						  		   val (<E>, <D>) = W <M>
						               in		
						     		   {<x>}{<d>} (<E>, <trans_var D>)
							       end) \x \d)
				   ) \x \d)
                                  <T>)
                of {<x>}{<d>} (<E x>, <D x d>) => (<lam E>, <trans_lam D>));


(* ********************************************************************** *)
(* ********************************************************************** *)
(* Now we have the functions that transform both, so we now prove that it is
 * an isomorphism, by showing
 * and 
 * (PART A) toHOAS (toDebruijn E) = E (fun iso)
 * and
 * (PART B)toDebruijn(toHOAS T) = T (fun iso2)
 *)
(* ********************************************************************** *)
(* ********************************************************************** *)

(* ********************************************* 
 * (PART A)	    
 ********************************************** 
 *)

fun equalApp : <eqexp E1 E1'> -> <eqexp E2 E2'> -> <eqexp (app E1 E2) (app E1' E2')>
         = fn <eqid> <eqid> => <eqid> ;


fun equalLam : <{x:exp} eqexp (E1 x) (E1' x)> -> <eqexp (lam E1) (lam E1')>
         = fn <[x] eqid> => <eqid> ;


fun contradiction : <empty> -> <E:exp> -> <E':exp> -> <eqexp E E'> = fn .;



fun lessProp2 : <lt (s M) N> -> <lt M N> =
       fn <lt_b> => <lt_ind lt_b>
	| <lt_ind L> => let val <P> = lessProp2 <L>
                        in <lt_ind P>
                        end;


fun lessProp1 : <lt (s M) (s N)> -> <lt M N> = 
	fn <lt_b> => <lt_b>
         | <lt_ind L> => lessProp2 <L> ;

fun lessContra2 : <M:nat> -> <lt (s M) M> -> <empty> 
     = fn <s N> <L> => lessContra2 <N> (lessProp1 <L>);

fun lessContra : <lt M M> -> <empty> 
     = fn <lt_ind L> => lessContra2 <_> <L>;


fun lessProp : <N:nat> -> <lt (s M) N> -> <lt M N> 
    = fn <s N> <L> =>  <lt_ind> @ (lessProp1 <L>);



fun extendContradiction : (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
                         -> {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>}
                            (<N':nat> -> <lt (s N) N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
			= fn C => fn {<x>}{<d>} (<s N> <L> <_> <_> <d> => lessContra <L>)
			           | {<x>}{<d>} (<s M> <L> <B> <E> <D> =>
						 let
						   val <L2> = lessProp <_> <L>
						   val R = C <s M> <L2> <B> <E> <D>
						 in
						   {<x>}{<d>} R
						 end \x \d );



type isoWorld = (<M:nat> -> <B:variable M> -> <E:exp#> -> <E':exp#> -> <trans E (bvar' B) #> -> <trans E' (bvar' B) #> -> <eqexp E E'>);

fun extend : (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>) ->
             isoWorld 
            -> {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>} isoWorld
	      = fn C => fn W => fn {<x>}{<d:trans x (bvar' (var_one : variable (s N) ))>} (<s N> <var_one> <x> <x> <d> <d> => <eqid>)
	                 | {<x>}{<d:trans x (bvar' (var_one : variable (s N) ))>} (<s N> <var_one> <x> <X'> <d> <D'> => 
							let
							  val <bottom> = C <s N> <lt_b> <var_one> <_> <D'>
							in 
							  {<x>}{<d>} (contradiction <bottom> <_> <_>)
							end \x \d)
	                 | {<x>}{<d:trans x (bvar' (var_one : variable (s N) ))>} (<s N> <var_one> <X'> <x> <D'> <d> => 
							let
							  val <bottom> = C <s N> <lt_b> <var_one> <_> <D'>
							in 
							  {<x>}{<d>} (contradiction <bottom> <_> <_>)
							end \x \d)

	                 | {<x>}{<d:trans x (bvar' (var_one : variable (s N) ))>} (<M> <B> <Y1> <Y2> <D1> <D2> => 
	                        let
				  val <R> = W <M> <B> <Y1> <Y2> <D1> <D2>
				in
				  {<x>}{<d>}<R>
				end \x \d);

fun isoVar : isoWorld -> <E:exp> -> <E':exp> -> <B:variable N> -> <trans E (bvar' B)> -> <trans E' (bvar' B)> -> <eqexp E E'> = fn W <E#> <E'#> <var_one> <D1#> <D2#> => W <_> <var_one> <E> <E'> <D1> <D2>
    | W <E> <E'> <var_s B> <trans_var D1> <trans_var D2> => isoVar W <E> <E'> <B> <D1> <D2> ;

(* This next function shows:
	toHOAS (toDebruijn E) = E
*)
fun iso : (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
         -> isoWorld
         -> <E:exp> -> <E':exp> -> <T:term N> -> <trans E T> -> <trans E' T> -> <eqexp E E'> =
        fn C W <app E1 E2> <app E1' E2'> <app' T1 T2> <trans_app D1 D2> <trans_app D1' D2'> =>
	            let
		      val <P1> = iso C W <E1> <E1'> <T1> <D1> <D1'>
		      val <P2> = iso C W <E2> <E2'> <T2> <D2> <D2'>
		    in
		      equalApp <P1> <P2>
		    end
	 | C W <lam E> <lam E'> <lam' T> <trans_lam D1> <trans_lam D2> => 
		    (case {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>} 
		                       iso ((extendContradiction C) \x \d) ((extend C W) \x \d) <E x> <E' x> <T> <D1 x d> <D2 x d>
		       of {<x>}{<d>}<EQ x> => equalLam <EQ>)
	 | C W <E> <E'> <bvar' B> <D1> <D2> => isoVar W <E> <E'> <B> <D1> <D2>;



(* ********************************************* 
 * (PART A)	    
 ********************************************** 
 *)




fun equalApp : <eqterm T1 T1'> -> <eqterm T2 T2'> -> <eqterm (app' T1 T2) (app' T1' T2')>
         = fn <eqtermid> <eqtermid> => <eqtermid> ;

fun equalLam : <eqterm T1 T1'> -> <eqterm (lam' T1) (lam' T1')>
         = fn <eqtermid> => <eqtermid> ;

fun equalBvar : <eqterm (bvar' B) (bvar' B')> -> <eqterm (bvar' (var_s B)) (bvar' (var_s B'))>
         = fn <eqtermid> => <eqtermid> ;
(* maybe forall M1 and forall M2?? *)
type iso2World = (<M:nat> -> <B:variable M> -> <E:exp#> -> <E':exp#> -> <trans E (bvar' B) #> -> <trans E' (bvar' B) #> -> <eqexp E E'>);

fun contra : <empty> -> <eqterm T1 T2> = fn .;

type iso2World = (<M:nat> -> <B1:variable M> -> <B2:variable M> -> <E:exp#> -> <trans E (bvar' B1) #> -> <trans E (bvar' B2) #> -> <eqterm (bvar' B1) (bvar' B2)>);

fun extend : iso2World 
            -> {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>} iso2World
	      = fn W => fn {<x>}{<d:trans x (bvar' (var_one : variable (s N) ))>} (<s N> <var_one> <var_one> <x> <d> <d> => <eqtermid>)
	                 | {<x>}{<d:trans x (bvar' (var_one : variable (s N) ))>} (<M> <B1> <B2> <Y> <D1> <D2> => 
	                        let
				  val <R> = W <M> <B1> <B2> <Y> <D1> <D2>
				in
				  {<x>}{<d>}<R>
				end \x \d);



fun impossibleParam : <trans E (bvar' (var_s B)) #> -> <empty>
     = fn .;


type iso2Contradiction = <E:exp#> -> <N':nat> -> <N:nat> -> <lt N' N> -> <B0 : variable N> -> <trans E (bvar' B0) #> -> <B: variable N'> -> <trans E (bvar' B) #> -> <empty>;

fun extendContradiction : iso2Contradiction
             -> {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>} iso2Contradiction

        = fn C => fn {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>} (<x> <_> <_> <L> <_> <d> <_> <d> => lessContra <L>)
		   | {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>}
			   (<E> <N1> <N2> <L> <B1> <D1> <B2> <D2> =>
			       let
				 val <bot> = C <E> <N1> <N2> <L> <B1> <D1> <B2> <D2> 
			       in
				 {<x>}{<d>}<bot>
			       end \x \d)
		   | {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>}
			   (<E> <_> <_> <L> <var_s B1> <Dbad> <B2> <D2> => 
			       let
				 val <bot> = impossibleParam <Dbad>				   
			       in
				 {<x>}{<d>}<bot>
			       end \x \d);

fun iso2Var : <B: variable N> -> <trans E (bvar' (var_s B))> -> <M:nat> * <lt M (s N)> * <B2 : variable M> * <trans E (bvar' B2) #>
     = fn <var_one> <trans_var (D#)> => (<_>, <lt_b>, <var_one>, <D>)
        | <var_s B> <trans_var D> =>
                              let
				val (<M>,<L>,<B2>,<D2>) = iso2Var <B> <D>
			      in
				(<M>, <lt_ind L>, <B2>, <D2>)
			      end;
(* This next function shows
	toDebruijn(toHOAS T) = T (fun iso2)
*)

fun contraApp : <N:nat> -> <M:variable N> -> <E1:exp> -> <E2:exp> -> <trans (app E1 E2) (bvar' M)> -> <empty> 
  	          = fn <s N> <var_s M> <E1> <E2> <trans_var D > => contraApp <N> <M> <E1> <E2> <D>;

fun contraLam : <N:nat> -> <M:variable N> -> <E:exp -> exp> -> <trans (lam E) (bvar' M)> -> <empty>
 		= fn <s N> <var_s M> <E> <trans_var D> => contraLam <N> <M> <E> <D>;

(* This is a more "explicit" version of the one below.
   fun iso2 : iso2Contradiction -> iso2World
	    -> <T1:term N> -> <T2:term N> -> <E:exp> -> <trans E T1> -> <trans E T2> -> <eqterm T1 T2> =
        fn C W <app' T1 T2> <app' T1' T2'> <app E1 E2> <trans_app D1 D2> <trans_app D1' D2'> =>
	            let
		      val <P1> = iso2 C W <T1> <T1'> <E1> <D1> <D1'>
		      val <P2> = iso2 C W <T2> <T2'> <E2> <D2> <D2'>
		    in
		      equalApp <P1> <P2>
		    end

	 | C W <_> <_> <app E1 E2> <trans_var D> <_> => contra (contraApp <_> <_> <E1> <E2> <D>)
	 | C W <_> <_> <app E1 E2> <_> <trans_var D> => contra (contraApp <_> <_> <E1> <E2> <D>)

	 | C W <lam' T> <lam' T'> <lam E> <trans_lam D1> <trans_lam D2> => 
		    (case {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>} 
		                       iso2 ((extendContradiction C) \x \d) ((extend W) \x \d) <T> <T'> <E x> <D1 x d> <D2 x d>
		       of {<x>}{<d>}<EQ> => equalLam <EQ>)

	 | C W <_> <_> <lam E> <trans_var D> <_> => contra (contraLam <_> <_> <E> <D>)
	 | C W <_> <_> <lam E> <_> <trans_var D> => contra (contraLam <_> <_> <E> <D>)
	 | C W <bvar' B1> <bvar' B2> <E#> <D1#> <D2#> => W <_> <B1> <B2> <E> <D1> <D2>
	 | C W <bvar' (var_s B1)> <bvar' (var_s B2)> <E#> <trans_var D1> <trans_var D2> =>
		                                           equalBvar (iso2 C W <bvar' B1> <bvar' B2> <E> <D1> <D2>)

	 | C W <bvar' var_one> <bvar' (var_s B2)> <E#> <D1#> <trans_var D2> => 
		    let  
		      val (<M'>, <L'>, <B2'>, <D2'>) = iso2Var <B2> <trans_var D2>
		      val <bot> = C <E> <M'> <s N> <L'> <var_one> <D1> <B2'> <D2'>
		    in
		      contra <bot>
		    end
	 | C W <bvar' (var_s B1)> <bvar' var_one>  <E#> <trans_var D1> <D2#> => 
		    let
		      val (<M'>, <L'>, <B1'>, <D1'>) = iso2Var <B1> <trans_var D1>
		      val <bot> = C <E> <_> <_> <L'> <var_one> <D2> <B1'> <D1'>
		    in
		      contra <bot>
		    end;
*)

fun iso2 : iso2Contradiction -> iso2World
	    -> <trans E T1> -> <trans E T2> -> <eqterm T1 T2> =
        fn C W <trans_app D1 D2> <trans_app D1' D2'> =>
	            let
		      val <P1> = iso2 C W <D1> <D1'>
		      val <P2> = iso2 C W <D2> <D2'>
		    in
		      equalApp <P1> <P2>
		    end

	 | C W  <trans_var D> <_> => contra (contraApp <_> <_> <E1> <E2> <D>)
	 | C W  <_> <trans_var D> => contra (contraApp <_> <_> <E1> <E2> <D>)

	 | C W <trans_lam D1> <trans_lam D2> => 
		    (case {<x>}{<d: trans x (bvar' (var_one : variable (s N) ))>} 
		                       iso2 ((extendContradiction C) \x \d) ((extend W) \x \d) <D1 x d> <D2 x d>
		       of {<x>}{<d>}<EQ> => equalLam <EQ>)

	 | C W <trans_var D> <_> => contra (contraLam <_> <_> <E> <D>)
	 | C W <_> <trans_var D> => contra (contraLam <_> <_> <E> <D>)
	 | C W <D1#> <D2#> => W <_> <B1> <B2> <E> <D1> <D2>
	 | C W <trans_var D1> <trans_var D2> => equalBvar (iso2 C W <D1> <D2>)

	 | C W <D1#> <trans_var D2> => 
		    let  
		      val (<M'>, <L'>, <B2'>, <D2'>) = iso2Var <B2> <trans_var D2>
		      val <bot> = C <E> <M'> <s N> <L'> <var_one> <D1> <B2'> <D2'>
		    in
		      contra <bot>
		    end
	 | C W <trans_var D1> <D2#> => 
		    let
		      val (<M'>, <L'>, <B1'>, <D1'>) = iso2Var <B1> <trans_var D1>
		      val <bot> = C <E> <_> <_> <L'> <var_one> <D2> <B1'> <D1'>
		    in
		      contra <bot>
		    end;


(* ********************************************* *)
(* TESTING	 			         *)
(* ********************************************* *)

	
val testToDebruijn : <T:term z> * <_> = 
	 toDebruijn (fn .)  <lam [x] lam [y] app y (lam [z] app y (app z x))>;
val testToHOAS = let 
	            val (<T>,<_>) = testToDebruijn
	            val (<E>,<_>) = toHOAS (fn .) <T>
		  in
		    <E>
                  end;
