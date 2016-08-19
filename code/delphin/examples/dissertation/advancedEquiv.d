use "depDelphin.d";


(* ADVANCED SECTION OF DISSERTATION.. *)

(* These next two relations allow us to state that terms/exps are equal (identical).
 *)
sig <eqexp : exp -> exp -> type>
    <eqexpid : eqexp E E>;

sig <eqterm : term N -> term N -> type>
    <eqtermid : eqterm T T>;

(* It is useful to have an empty type to argue about something being impossible.
 *)
sig <empty : type>;

(* Standard less-than relation (we will use it to talk about context extensions) *)
sig <lt : nat -> nat -> type> 
    <lt_b : lt M (s M)>
    <lt_ind : lt M N -> lt M (s N)> ;


(* 
 * *********************************************
 * *********************************************
 * We now show that (equiv P E T) is deterministic.
 * Which allows us to conclude:
 *
 * PART A:  toHOAS (toDebruijn E) = E
 *   This is shown by proving
 *     <equiv P E1 T> -> <equiv P E2 T> -> <eqexp E1 E2>   (as fun detA-closed)
 * 
 * PART B:  toDebruijn(toHOAS T) = T 
 *   This is shown by proving
 *     <equiv P E T1> -> <equiv P E T2> -> <eqterm T1 T2>  (as fun detB-closed)
 * **********************************************
 * ********************************************** 
 *)


(* 
 * ********************************************* 
 * (PART A)	    
 ***********************************************
 *)

(* The scope of params applies to all fun declarations until
 * the next params.
 *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;


fun equalApp : <eqexp E1 E1'> -> <eqexp E2 E2'> -> <eqexp (app E1 E2) (app E1' E2')>
         = fn <eqexpid> <eqexpid> => <eqexpid> ;

fun equalLam : <{x:exp} eqexp (E1 x) (E1' x)> -> <eqexp (lam [x] E1 x) (lam [x] E1' x)>
         = fn <[x] eqexpid> => <eqexpid> ;



fun lessProp2 : <lt (s M) N> -> <lt M N> 
    =  fn <lt_b> => <lt_ind lt_b>
	| <lt_ind L> => let 
			  val <P> = lessProp2 <L>
                        in 
			  <lt_ind P>
                        end;

fun lessProp1 : <lt (s M) (s N)> -> <lt M N> 
     = fn <lt_b> => <lt_b>
        | <lt_ind L> => lessProp2 <L> ;

fun lessContra2 : <M:nat> -> <lt (s M) M> -> <empty> 
     = fn <s N> <L> => lessContra2 <N> (lessProp1 <L>);

fun lessContra : <lt M M> -> <empty> 
     = fn <lt_ind L> => lessContra2 <_> <L>;


fun lessProp : <N:nat> -> <lt (s M) N> -> <lt M N> 
    = fn <s N> <L> =>  <lt_ind> @ (lessProp1 <L>);



type detA-World = <equiv (s P) E (var' one) #> -> <equiv (s P) E' (var' one) #> 
                -> <eqexp E E'>;

fun extend : (<P':nat> -> <lt P (s P')> -> <E:exp> -> <(equiv (s P') E (var' one))#> -> <empty>)
              -> detA-World 
              -> {<x>}{<d: equiv (s P) x (var' one)>} detA-World
  = fn C => fn W 
            => fn {<x>}{<d:equiv (s P) x (var' one)>} (<d> <d> => <eqexpid>)
	        | {<x>}{<d:equiv (s P) x (var' one)>} (<d> <D#> => 
						       let
							 val <bot> = C <P> <lt_b> <_> <D>
						       in 
							 {<x>}{<d>} (fn .) <bot>
                                                          (* (fn .) is a total function of
                                                           * type <empty> -> ...
                                                           *)
						       end \x \d)

                | {<x>}{<d:equiv (s P) x (var' one)>} (<D#> <d> => 
						       let
							 val <bot> = C <P> <lt_b> <_> <D>
						       in 
							 {<x>}{<d>} (fn .) <bot>
                                                          (* (fn .) is a total function of
                                                           * type <empty> -> ...
                                                           *)
						       end \x \d)


	        | {<x>}{<d:equiv (s P) x (var' one)>} (<D1#> <D2#> => 
						       let
							 val <R> = W <D1> <D2>
						       in
							 {<x>}{<d>}<R>
						       end \x \d);

fun detA-Var : detA-World -> <equiv P E (var' X)> -> <equiv P E' (var' X)> -> <eqexp E E'> 
 = fn W <D1 : (equiv _ E (var' one))#> <D2#> => W <D1> <D2>
    | W <eqVar D1> <eqVar D2> => detA-Var W <D1> <D2> ;

fun detA : (<P':nat> -> <lt P (s P')> -> <E:exp> -> <(equiv (s P') E (var' one))#> -> <empty>)
         -> detA-World
         -> <equiv P E T> -> <equiv P E' T> -> <eqexp E E'> 
     =  fn C W <eqApp D1 D2> <eqApp D1' D2'> =>
	            let
		      val <P1> = detA C W <D1> <D1'>
		      val <P2> = detA C W <D2> <D2'>
		    in
		      equalApp <P1> <P2>
		    end

	 | C W <eqLam [x] [d] D1 x d> <eqLam [x] [d] D2 x d> => 
		    let
		      val Cnew : (<P':nat> -> <lt (s P) (s P')> -> <E:exp> 
                                  -> <(equiv (s P') E (var' one))#> -> <empty>) 
		        = fn <P'> <L:lt (s P) (s P')> <E3> <D3#> 
                                => C <P'> (lessProp <s P'> <L>) <E3> <D3>
		    in
		      (case {<x>}{<d: equiv (s P) x (var' one)>} 
		                  detA (Cnew with <P> <L:lt (s P) (s P)> <x> <d> => lessContra <L>) 
                                       ((extend C W) \x \d)
				       <D1 x d> 
				       <D2 x d>
			  of {<x>}{<d>}<EQ x> => equalLam <[x] EQ x>)
		   end


	 | C W <D1 : equiv P E (var' X)> <D2 : equiv P E' (var' X)> => detA-Var W  <D1> <D2>;


(* Putting it all together *)
params = .;
fun detA-closed  : <equiv P E1 T> -> <equiv P E2 T> -> <eqexp E1 E2> 
                 = fn <D1> <D2> => detA (fn .) (fn .) <D1> <D2>;


(* 
 * ********************************************* 
 * (PART B)
 ***********************************************
 *)
params = <nd A>, <comb A>, <exp>, <equiv (s P) (E#) (var' one)>;



fun equalApp : <eqterm T1 T1'> -> <eqterm T2 T2'> -> <eqterm (app' T1 T2) (app' T1' T2')>
         = fn <eqtermid> <eqtermid> => <eqtermid> ;

fun equalLam : <eqterm T1 T1'> -> <eqterm (lam' T1) (lam' T1')>
         = fn <eqtermid> => <eqtermid> ;

fun equalBvar : <eqterm (var' X) (var' Y)> -> <eqterm (var' (succ X)) (var' (succ Y))>
         = fn <eqtermid> => <eqtermid> ;


type detB-World = <equiv P E (var' X) #> -> <equiv P E (var' Y) #> -> <eqterm (var' X) (var' Y)>;

type detB-Contradiction = <lt (s P') (s P)> -> <equiv (s P) E (var' one) #> 
                          -> <equiv (s P') E (var' one) #> -> <empty>;

fun detB-Var : <X: variable P> -> <equiv (s P) E (var' (succ X))> 
              -> <P':nat> * <lt (s P') (s P)> * <equiv (s P') E (var' one) #>
     = fn <one> <eqVar D#> => (<_>, <lt_b>, <D>)
        | <succ X> <eqVar D> =>
                              let
				val (<P'>, <L'>, <D'>) = detB-Var <X> <D>
			      in
				(<P'>, <lt_ind L'>, <D'>)
			      end;

fun contraApp : <P:nat> -> <equiv P (app E1 E2) (var' X)> -> <empty> 
  	          = fn <s P> <eqVar D > => contraApp <P> <D>;

fun contraLam : <P:nat> -> <equiv P (lam E) (var' X)> -> <empty>
 		= fn <s P> <eqVar D> => contraLam <P> <D>;


fun detB : detB-Contradiction -> detB-World
	    -> <equiv P E T1> -> <equiv P E T2> -> <eqterm T1 T2> 
      = fn C W <eqApp D1 D2> <eqApp D1' D2'> =>
	            let
		      val <P1> = detB C W <D1> <D1'>
		      val <P2> = detB C W <D2> <D2'>
		    in
		      equalApp <P1> <P2>
		    end


	 | C W <eqLam [x] [d] D1 x d> <eqLam [x] [d] D2 x d> => 
		    (case {<x>}{<d: equiv (s P) x (var' one)>} 
		                       detB (C with <L> <d> <d> => lessContra <L>)
                                            (W with <d> <d> => <eqtermid>)
                                            <D1 x d> 
                                            <D2 x d>
		       of {<x>}{<d>}<EQ> => equalLam <EQ>)


	 | C W <D1#> <D2#> => W <D1> <D2>
	 | C W <eqVar (D1 : equiv P E (var' X))> <eqVar (D2 : equiv P E (var' Y))> => 
                    equalBvar (detB C W <D1> <D2>)

	 | C W <D1 : (equiv (s P) E (var' one))#> <eqVar (D2 : equiv P E (var' X))> => 
		    let  
		      val (<P'>, <L'>, <D2'>) = detB-Var <X> <eqVar D2>
		      val <bot> = C <L'> <D1> <D2'>
		    in
		      (fn .) <bot>
  		      (* (fn .) is a total function of
		       * type <empty> -> ...
		       *)

		    end
	 | C W <eqVar (D1 : equiv P E (var' X))> <D2 : (equiv (s P) E (var' one))#> => 
		    let
		      val (<P'>, <L'>, <D1'>) = detB-Var <X> <eqVar D1>
		      val <bot> = C <L'> <D2> <D1'>
		    in
		      (fn .) <bot>
  		      (* (fn .) is a total function of
		       * type <empty> -> ...
		       *)

		    end

         (* The next four cases handle impossible cases
	  * We prove these cases are impossible by using contraApp and contraLam
	  * which return an object of type empty, of which there are none.
          *
          * Given an E : <empty>, we can conclude anything, which
          * is why we just do:  (fn .) E
	  * The type of (fn .) will be <empty> -> T.
          *)
	 | C W  <eqVar (D : equiv P (app E1 E2) (var' X))> <_> => (fn .) (contraApp <P> <D>)
	 | C W  <_> <eqVar (D : equiv P (app E1 E2) (var' X))> => (fn .) (contraApp <P> <D>)
	 | C W <eqVar (D : equiv P (lam E) (var' X))> <_> => (fn .) (contraLam <P> <D>)
	 | C W <_> <eqVar (D : equiv P (lam E) (var' X))> => (fn .) (contraLam <P> <D>);



(* Putting it all together *)
params = .;
fun detB-closed : <equiv P E T1> -> <equiv P E T2> -> <eqterm T1 T2> 
                = fn <D1> <D2> => detB (fn .) (fn .) <D1> <D2>;
