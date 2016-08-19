sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>;

sig <nat : type> 
     <z : nat>
     <s : nat -> nat> ;

sig <term : type>
    <var' : nat -> term>
    <lam' : term -> term>
    <app' : term -> term -> term> ;


sig <lt : nat -> nat -> type> 
    <lt_b : lt M (s M)>
    <lt_ind : lt M N -> lt M (s N)> ;

sig <maxInd : nat -> term -> type> 
    <maxV : lt M N -> maxInd N (var' M)> 
    <maxA : maxInd N T1 -> maxInd N T2 -> maxInd N (app' T1 T2)>
    <maxL : maxInd (s N) T -> maxInd N (lam' T)> ;

	
params = <exp> ;


type debruijnWorldFun = <exp#> -> <nat>;
fun extend : debruijnWorldFun -> {<x:exp>}debruijnWorldFun
    = fn W => fn {<x>}(<x> => <z>) (* Parameter x is mapped to z *)
                | {<x>}(<y> =>  (* All other parameters are now mapped to 1 + (previous mapping) *)
			   (let
			       val <N> = W <y>
                           in
				{<x>} <s N>
			   end) \x );


fun toDebruijn : debruijnWorldFun -> <exp> -> <term>
    = fn W <app E1 E2> => 
            let
		val <T1> = toDebruijn W <E1>
		val <T2> = toDebruijn W <E2>
             in
                 <app' T1 T2>	
             end
       | W <lam E> =>
             (case ({<x:exp>} toDebruijn ((extend W) \x) <E x>)
               of {<x>}<T> => <lam' T>)

       | W <x#> => <var'> @ (W <x>);

fun zeroMin : <N:nat> -> <lt z (s N)>
          = fn <z> => <lt_b>
             | <s N> => <lt_ind> @ (zeroMin <N>);

fun addSucc : <lt M N> -> <lt (s M) (s N)> =
       fn <lt_b> => <lt_b>
	| <lt_ind L> => let val <P> = addSucc <L>
                        in <lt_ind P>
                        end;
        


fun extend : (<exp#> -> <M:nat> * <lt M N>) -> {<x:exp>}(<exp#> -> <M:nat> * <lt M (s N)>)
    = fn W => fn {<x>}(<x> => (<z>, zeroMin <_>)) (* Parameter x is mapped to z *)
                | {<x>}(<y> =>  (* All other parameters are now mapped to 1 + (previous mapping) *)
			   (let
			       val (<M>,<P>) = W <y>
                           in
				{<x>} (<s M>, addSucc <P>)
			   end) \x );


fun toDebruijn : <N:nat> -> (<exp#> -> <M:nat> * <lt M N>)  -> <exp> -> <T:term> * <maxInd N T>
    = fn <N> W <app E1 E2> => 
            let
		val (<T1>, <P1>) = toDebruijn <N> W <E1>
		val (<T2>, <P2>) = toDebruijn <N> W <E2>
             in
                 (<app' T1 T2>, <maxA P1 P2>)
             end
       | <N> W <lam E> =>
             (case ({<x:exp>} toDebruijn <s N> ((extend W) \x) <E x>)
               of {<x>}(<T>, <P>) => (<lam' T>, <maxL P>))

       | <N> W <x#> => 
		let 
		  val (<M>, <L>) = W <x>
                in
		 (<var' M>, <maxV L>)
		end;


type hoasWorldFun = <nat> -> <exp>;
fun toHOAS : hoasWorldFun -> <term> -> <exp>
    = fn W <var' N> => W <N>
       | W <app' T1 T2> =>
            let
		val <E1> = toHOAS W <T1>
		val <E2> = toHOAS W <T2>
             in
                 <app E1 E2>	
             end
       | W <lam' T> =>
             (case ({<x:exp>} toHOAS (fn <z> => <x>  | <s N> => W <N>) <T>)
               of {<x>}<E x> => <lam E>); 


fun lessProp2 : <lt (s M) N> -> <lt M N> =
       fn <lt_b> => <lt_ind lt_b>
	| <lt_ind L> => let val <P> = lessProp2 <L>
                        in <lt_ind P>
                        end;


fun lessProp : <lt (s M) (s N)> -> <lt M N> = 
	fn <lt_b> => <lt_b>
         | <lt_ind L> => lessProp2 <L> ;

    


fun toHOAS : <N:nat> -> (<M:nat> -> <lt M N> -> <exp>) -> <T:term> -> <maxInd N T> -> <exp>
   = fn <N> W <app' T1 T2> <maxA P1 P2> =>
            let
		val <E1> = toHOAS <N> W <T1> <P1>
		val <E2> = toHOAS <N> W <T2> <P2>
             in
                 <app E1 E2>
             end

      | <N> W <lam' T> <maxL P> =>
           (case ({<x:exp>} toHOAS <s N> 
                                  (fn <z> <L> => <x>
                                    | <s M> <L> => W <M> (lessProp <L>))
                                  <T> <P>)
                of {<x:exp>}<E x> => <lam E>)

     | <N> W <var' M> <maxV P> => W <M> (<P>);


fun empty : <M:nat> -> <lt M z> -> <exp> = fn . ;
fun toHOAS_closed : <T:term> -> <maxInd z T> -> <exp> = toHOAS <z> empty ;

params = .;
fun toDebruijn_closed : <exp> -> <T:term> * <maxInd z T> = toDebruijn <z> (fn .);
	
val test = toDebruijn_closed  <lam [x] lam [y] app y (lam [z] app y (app z x))>;

val test2 = let	      
	      val (<T>, <P>) = test
	    in
	     toHOAS_closed <T> <P>
           end;


fun iso : <exp> -> <exp> =
    fn <E> => let
		val (<T>, <P>) = toDebruijn_closed <E>
              in
		toHOAS_closed <T> <P>
              end;
