sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>;

sig <nat : type> 
     <z : nat>
     <s : nat -> nat> ;

sig <lt : nat -> nat -> type> 
    <lt_b : lt M (s M)>
    <lt_ind : lt M N -> lt M (s N)> ;

(* Encoding of well-formed (closed) de-bruijn terms *)
sig <term : nat -> type>
    <var' : {M} lt M N -> term N>
    <lam' : term (s N) -> term N>
    <app' : term N -> term N -> term N> ;

params = <exp> ;


fun zeroMin : <N:nat> -> <lt z (s N)>
          = fn <z> => <lt_b>
             | <s N> => <lt_ind> @ (zeroMin <N>);


fun addSucc : <term N> -> <term (s N)>
	= fn <var' M L> =>  <var' M (lt_ind L)> 
	   | <app' T1 T2> => <app'> @ (addSucc <T1>) @ (addSucc <T2>)
	   | <lam' T> => <lam'> @ (addSucc <T>);

fun extend : (<exp#> -> <term N>) -> {<x:exp#>}(<exp#> -> <term (s N)>)
    = fn W => fn {<x>}(<x> => <var' z> @ (zeroMin <N>)) (* Parameter x is mapped to z *)
                | {<x>}(<y> =>  (* All other parameters are now mapped to 1 + (previous mapping) *)
			   (let
			       val <T> = W <y>
                           in
				{<x>} (addSucc <T>)
			   end) \x );

fun toDebruijn : <N:nat> -> (<exp#> -> <term N>)  -> <exp> -> <term N>
    = fn <N> W <app E1 E2> => 
            let
		val <T1> = toDebruijn <N> W <E1>
		val <T2> = toDebruijn <N> W <E2>
             in
                 <app' T1 T2>
             end
       | <N> W <lam E> =>
             (case ({<x:exp>} toDebruijn <s N> ((extend W) \x) <E x>)
               of {<x>}<T> => <lam' T>)

       | <N> W <x#> => W <x>;


fun lessProp2 : <lt (s M) N> -> <lt M N> =
       fn <lt_b> => <lt_ind lt_b>
	| <lt_ind L> => let val <P> = lessProp2 <L>
                        in <lt_ind P>
                        end;


fun lessProp : <lt (s M) (s N)> -> <lt M N> = 
	fn <lt_b> => <lt_b>
         | <lt_ind L> => lessProp2 <L> ;

    


fun toHOAS : <N:nat> -> (<M:nat> -> <lt M N> -> <exp>) -> <term N>  -> <exp>
   = fn <N> W <app' T1 T2> =>
            let
		val <E1> = toHOAS <N> W <T1>
		val <E2> = toHOAS <N> W <T2>
             in
                 <app E1 E2>
             end

      | <N> W <lam' T> =>
           (case ({<x:exp>} toHOAS <s N> 
                                  (fn <z> <L> => <x>
                                    | <s M> <L> => W <M> (lessProp <L>))
                                  <T>)
                of {<x:exp>}<E x> => <lam E>)

     | <N> W <var' M L>  => W <M> <L>;
			    
fun empty : <M:nat> -> <lt M z> -> <exp> = fn . ;
fun toHOAS_closed : <term z> -> <exp> = toHOAS <z> empty ;

params = .;
fun toDebruijn_closed : <exp> -> <term z> = toDebruijn <z> (fn .);
	
val test = toDebruijn_closed  <lam [x] lam [y] app y (lam [z] app y (app z x))>;

val test2 = toHOAS_closed test;

fun iso : <exp> -> <exp> =
    fn E => toHOAS_closed (toDebruijn_closed E);

fun iso2 : <term z> -> <term z> =
    fn E => toDebruijn_closed (toHOAS_closed E);
