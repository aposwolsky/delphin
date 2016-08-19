sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>;

sig <nat : type> 
     <z : nat>
     <s : nat -> nat> ;

sig <lt : nat -> nat -> type> 
    <lt_b : lt M (s M)>
    <lt_ind : lt M N -> lt M (s N)> ;

(* Encoding of well-formed de-bruijn terms with contexts of length N *)
sig <term : nat -> type>
    <var' : {M} lt M N -> term N>
    <lam' : term (s N) -> term N>
    <app' : term N -> term N -> term N> ;


sig <trans : exp -> term N -> type>
    <trans_app : trans E1 T1 -> trans E2 T2 -> trans (app E1 E2) (app' T1 T2)>
    <trans_lam : ({x:exp} (trans x (var' z (L : lt z (s N)))) -> trans (E x) (T : term (s N))) -> trans (lam E) (lam' T)>
    <trans_var : {L:lt M N} {L2: lt (s M) (s N)} (trans E (var' M L)) -> (trans E (var' (s M) L2))> 
          (* trans_var is saying:
	       if E is the Mth variable in a context of size N  (guaranteed by L : lt M N)
               then E is also the (M+1)st variable in that context extended with one element (guaranteed by L2 : lt (s M) (s N))
           *)
    <trans_varEqual : {L:lt z N} {L2: lt z N} trans E (var' z L) -> trans E (var' z L2)> ; (* BEST to prove this admissible! *)

sig <eqexp : exp -> exp -> type>
    <eqid : eqexp E E>;

sig <eqterm : term N -> term N -> type>
    <eqtermid : eqterm T T>;

params = <exp>, <trans (E#) (var' z L)> ;


fun zeroMin : <N:nat> -> <lt z (s N)>
          = fn <z> => <lt_b>
             | <s N> => <lt_ind> @ (zeroMin <N>);



fun addLt : <lt M N> -> <lt (s M) (s N)> = 
	fn <lt_b> => <lt_b>
         | <lt_ind L> => <lt_ind> @ (addLt <L>);



fun extend : (<E:exp#> -> <M:nat> * <L: lt M N>  * <trans E (var' M L)>) -> 
                  {<x:exp>}{<d: trans x (var' z (L' : lt z (s N)))>} 
                  (<E'':exp#> -> <M'':nat> * <L'': lt M'' (s N)>  * <trans E'' (var' M'' L'')>) 
     = fn W => fn {<x:exp>}{<d: trans x (var' z L')>}(<x> => (* parameter x is mapped to z *)
				                             (<z>, <L'>, <d>))
	        | {<x>}{<d>}(<y> => 
				(let
				    val (<M>, <L>, <D>) = W <y>
				    val <L2> = addLt <L>
				    val <D2> = <trans_var L L2 D>
				in
				    {<x>}{<d>} (<s M>, <L2>, <D2>)
				end \x \d) );

fun toDebruijn : <N:nat> -> (<E:exp#> -> <M:nat> * <L: lt M N>  * <trans E (var' M L)>) -> <E:exp> -> <T:term N> * <trans E T>
    = fn <N> W <app E1 E2> => 
            let
		val (<T1>,<P1>) = toDebruijn <N> W <E1>
		val (<T2>,<P2>) = toDebruijn <N> W <E2>
             in
                 (<app' T1 T2>, <trans_app P1 P2>)
             end
       | <N> W <lam E> =>
          let
	     val <L> = zeroMin <N>
	  in
             (case ({<x:exp>}{<d:trans x (var' z L)>} toDebruijn <s N> ((extend W) \x \d) <E x>)
               of {<x>}{<d>}(<T>, <P x d>) => (<lam' T>, <trans_lam P>))
          end

       | <N> W <x#> => 
		let
		   val (<M>, <L>, <D>) = W <x>
		in
		   (<var' M L>, <D>)
		end;


fun lessProp2 : <lt (s M) N> -> <lt M N> =
       fn <lt_b> => <lt_ind lt_b>
	| <lt_ind L> => let val <P> = lessProp2 <L>
                        in <lt_ind P>
                        end;


fun lessProp : <lt (s M) (s N)> -> <lt M N> = 
	fn <lt_b> => <lt_b>
         | <lt_ind L> => lessProp2 <L> ;

    


fun toHOAS : <N:nat> -> (<M:nat> -> <L:lt M N> -> <E:exp> * <trans E (var' M L)>) -> <T:term N>  -> <E:exp> * <trans E T>
   = fn <N> W <app' T1 T2> =>
            let
		val (<E1>,<D1>) = toHOAS <N> W <T1>
		val (<E2>,<D2>) = toHOAS <N> W <T2>
             in
                 (<app E1 E2>, <trans_app D1 D2>)
             end

      | <N> W <var' M L>  => W <M> <L>
 
      | <N> W <lam' T> =>
	     let
	       val <Lz> = zeroMin <N>  
	     in
	       case ({<x:exp>}{<d:trans x (var' z Lz)>} toHOAS <s N> 
                                   (fn <z> <L> => (<x>, <trans_varEqual Lz L d>)
				    | <s M> <L> => let 
						     val <L'> = lessProp <L>
						     val (<E>, <D>) = W <M> <L'>
				                   in
						     (<E>, <trans_var L' L D>)
						   end
				   )
                                  <T>)
                of {<x>}{<d>} (<E x>, <D x d>) => (<lam E>, <trans_lam D>)
	     end;



			    
fun empty : <M:nat> -> <L:lt M z> -> (<E:exp> * <trans E (var' M L)>)  = fn . ;
fun toHOAS_closed : <T:term z> -> <E:exp> * <trans E T> = toHOAS <z> empty ;



fun fooApp : <eqexp E1 E1'> -> <eqexp E2 E2'> -> <eqexp (app E1 E2) (app E1' E2')>
         = fn <eqid> <eqid> => <eqid> ;


fun fooLam : <{x:exp} eqexp (E1 x) (E1' x)> -> <eqexp (lam E1) (lam E1')>
         = fn <[x] eqid> => <eqid> ;
(* 
fun iso :<E:exp> -> <E':exp> -> <T:term N> -> <trans E T> -> <trans E' T> -> <eqexp E E'> =
        fn <app E1 E2> <app E1' E2'> <app' T1 T2> <trans_app D1 D2> <trans_app D1' D2'> =>
	            let
		      val <P1> = iso <E1> <E1'> <T1> <D1> <D1'>
		      val <P2> = iso <E2> <E2'> <T2> <D2> <D2'>
		    in
		      fooApp <P1> <P2>
		    end
	 | [<N:nat>][<E: exp -> exp>] [<T: term (s N)>] [<L1 : lt z (s N)>] [<L2 : lt z (s N)>][<D1 : {x:exp} trans x (var' z L1) -> trans (E x) T>] [<D2 : {x:exp} trans x (var' z L2) -> trans (E' x) T>] 
	    <lam E> <lam E'> <lam' T> <trans_lam D1> <trans_lam D2> => 
		    let
		      val <L> = zeroMin <_>
		    in
		      case {<x>}{<d: trans x (var' z L)>} iso <E x> <E' x> <T> <D1 x d> <D2 x d>
			of {<x>}{<d>}<EQ x> => fooLam <EQ>
		    end;
*)
	                                           
fun iso2: <trans E T> -> <trans E T'> -> <eqterm T T'> = fn .;


(*
params = .;
fun toDebruijn_closed : <E:exp> -> <T:term z> * <trans E T> = toDebruijn <z> (fn .);
	
val test = toDebruijn_closed  <lam [x] lam [y] app y (lam [z] app y (app z x))>;

val test2 = let val (<T>,<_>) = test 
	        val (<E>, <_>) = toHOAS_closed <T>
	    in
	      <E>
	    end;
*)