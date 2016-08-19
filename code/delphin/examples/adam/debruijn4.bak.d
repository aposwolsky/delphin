sig <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>;

sig <nat : type> 
     <z : nat>
     <s : nat -> nat> ;

(* meaning (variable N) = A number representing variables in a context of size N (0 to N-1) *)
sig <variable : nat -> type>
    <var_z : variable (s N)>
    <var_s : variable N -> variable (s N)> ;

(* Encoding of well-formed de-bruijn terms with contexts of length N *)
sig <term : nat -> type>
    <bvar' : variable N -> term N>
    <lam' : term (s N) -> term N>
    <app' : term N -> term N -> term N> ;


sig <trans : exp -> term N -> type>
    <trans_app : trans E1 T1 -> trans E2 T2 -> trans (app E1 E2) (app' T1 T2)>
    <trans_lam : ({x:exp} (trans x (bvar' (var_z : variable (s N) ))) -> trans (E x) (T: term (s N) )) -> trans (lam E) (lam' T)>
    <trans_var : trans E (bvar' M) -> trans E (bvar' (var_s M))> ;
          (* trans_var is saying:
	       if E is the Mth variable when the context has size N
               then E is also the (M+1)st variable in the same context extended with one element.
           *)


sig <eqexp : exp -> exp -> type>
    <eqid : eqexp E E>;

sig <eqterm : term N -> term N -> type>
    <eqtermid : eqterm T T>;

params = <exp>, <trans (E#) (bvar' var_z)> ;


fun extend : (<E:exp#> -> <M: variable N> * <trans E (bvar' M)>) ->
		{<x:exp>}{<d: trans x (bvar' (var_z : variable (s N) ))>}(<E:exp#> -> <M: variable (s N)> * <trans E (bvar' M)>) 
		= fn W => fn {<x:exp>}{<d: trans x (bvar' (var_z : variable (s N) ))>} (<x> =>
										(* parameter is mapped to z *)
										(<var_z>, <d>))
		            |{<x:exp>}{<d: trans x (bvar' (var_z : variable (s N) ))>} (<y> =>
				(let
				    val (<M>, <D>) = W <y> 
				in
				    {<x>}{<d>} (<var_s M>, <trans_var D>)
				end \x \d) );

fun toDebruijn : <N:nat> -> (<E:exp#> -> <M: variable N> * <trans E (bvar' M)>) -> <E:exp> -> <T:term N> * <trans E T>
    = fn <N> W <app E1 E2> => 
            let
		val (<T1>,<P1>) = toDebruijn <N> W <E1>
		val (<T2>,<P2>) = toDebruijn <N> W <E2>
             in
                 (<app' T1 T2>, <trans_app P1 P2>)
             end
       | <N> W <lam E> => 
             (case ({<x:exp>}{<d:trans x (bvar' (var_z : variable (s N)))>} toDebruijn <s N> ((extend W) \x \d) <E x>)
               of {<x>}{<d>}(<T>, <P x d>) => (<lam' T>, <trans_lam P>))

       | <N> W <x#> => 
		let
		   val (<V>, <D>) = W <x>
		in
		   (<bvar' V>, <D>)
		end;

    

fun toHOAS : <N:nat> -> (<M:variable N> -> <E:exp> * <trans E (bvar' M)>) -> <T:term N> -> <E:exp> * <trans E T>
   = fn <N> W <app' T1 T2> =>
            let
		val (<E1>,<D1>) = toHOAS <N> W <T1>
		val (<E2>,<D2>) = toHOAS <N> W <T2>
             in
                 (<app E1 E2>, <trans_app D1 D2>)
             end

      | <N> W <bvar' M>  => W <M>
 
      | <N> W <lam' T> =>
	     (case ({<x:exp>}{<d:trans x (bvar' (var_z : variable (s N)))>} toHOAS <s N> 
                                   (fn <var_z> => (<x>, <d>)
				    | <var_s M> => let 
						     val (<E>, <D>) = W <M>
				                   in
						     (<E>, <trans_var D>)
						   end
				   )
                                  <T>)
                of {<x>}{<d>} (<E x>, <D x d>) => (<lam E>, <trans_lam D>));



			    
fun empty : <M:variable z>  -> (<E:exp> * <trans E (bvar' M)>)  = fn . ;
fun toHOAS_closed : <T:term z> -> <E:exp> * <trans E T> = toHOAS <z> empty ;



fun fooApp : <eqexp E1 E1'> -> <eqexp E2 E2'> -> <eqexp (app E1 E2) (app E1' E2')>
         = fn <eqid> <eqid> => <eqid> ;


fun fooLam : <{x:exp} eqexp (E1 x) (E1' x)> -> <eqexp (lam E1) (lam E1')>
         = fn <[x] eqid> => <eqid> ;

(* BUG:  cannot make the N:nat implicit!! find out why! *)
sig <empty : type>;
sig <le : nat -> nat -> type>
    <le_b : le M M>
    <le_ind : le M N -> le M (s N)>;

sig <lt : nat -> nat -> type> 
    <lt_b : lt M (s M)>
    <lt_ind : lt M N -> lt M (s N)> ;

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
                         -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>}
                            (<N':nat> -> <lt (s N) N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
			= fn C => fn {<x>}{<d>} (<s N> <L> <_> <_> <d> => lessContra <L>)
			           | {<x>}{<d>} (<s M> <L> <B> <E> <D> =>
						 let
						   val <L2> = lessProp <_> <L>
						   val R = C <s M> <L2> <B> <E> <D>
						 in
						   {<x>}{<d>} R
						 end \x \d );


fun extendContradictionBUG : (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
                         -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>}
                            (<N':nat> -> <lt (s N) N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
			= fn C => fn .;

(* BUG in delphin.. also works even if (s N) is N .. above works without any cases.. *)
fun extendBUG : (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
                         -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>}
                            (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>)
			= fn C {<x>}{<d>} <N'> <L> <B> <E> => fn . ;
(*
val example = {<x:exp>}{<d : trans x (bvar' (var_z : variable (s z)))>} ((extendBUG (fn .)) \x \d) <s z> <lt_b> <var_z> <x> <d>;
*)

type isoWorld = (<M:nat> -> <B:variable M> -> <E:exp#> -> <E':exp#> -> <trans E (bvar' B) #> -> <trans E' (bvar' B) #> -> <eqexp E E'>);

fun extend : (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>) ->
             isoWorld 
            -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} isoWorld
	      = fn C => fn W => fn {<x>}{<d:trans x (bvar' (var_z : variable (s N) ))>} (<s N> <var_z> <x> <x> <d> <d> => <eqid>)
	                 | {<x>}{<d:trans x (bvar' (var_z : variable (s N) ))>} (<s N> <var_z> <x> <X'> <d> <D'> => 
							let
							  val <bottom> = C <s N> <lt_b> <var_z> <_> <D'>
							in 
							  {<x>}{<d>} (contradiction <bottom> <_> <_>)
							end \x \d)
	                 | {<x>}{<d:trans x (bvar' (var_z : variable (s N) ))>} (<s N> <var_z> <X'> <x> <D'> <d> => 
							let
							  val <bottom> = C <s N> <lt_b> <var_z> <_> <D'>
							in 
							  {<x>}{<d>} (contradiction <bottom> <_> <_>)
							end \x \d)

	                 | {<x>}{<d:trans x (bvar' (var_z : variable (s N) ))>} (<M> <B> <Y1> <Y2> <D1> <D2> => 
	                        let
				  val <R> = W <M> <B> <Y1> <Y2> <D1> <D2>
				in
				  {<x>}{<d>}<R>
				end \x \d);

fun isoVar : isoWorld -> <E:exp> -> <E':exp> -> <B:variable N> -> <trans E (bvar' B)> -> <trans E' (bvar' B)> -> <eqexp E E'> = fn W <E#> <E'#> <var_z> <D1#> <D2#> => W <_> <var_z> <E> <E'> <D1> <D2>
    | W <E> <E'> <var_s B> <trans_var D1> <trans_var D2> => isoVar W <E> <E'> <B> <D1> <D2> ;


fun iso : (<N':nat> -> <lt N N'> -> <B:variable N'> -> <E:exp> -> <trans E (bvar' B) #> -> <empty>) (* contradiction *)
         -> isoWorld
         -> <E:exp> -> <E':exp> -> <T:term N> -> <trans E T> -> <trans E' T> -> <eqexp E E'> =
        fn C W <app E1 E2> <app E1' E2'> <app' T1 T2> <trans_app D1 D2> <trans_app D1' D2'> =>
	            let
		      val <P1> = iso C W <E1> <E1'> <T1> <D1> <D1'>
		      val <P2> = iso C W <E2> <E2'> <T2> <D2> <D2'>
		    in
		      fooApp <P1> <P2>
		    end
	 | C W <lam E> <lam E'> <lam' T> <trans_lam D1> <trans_lam D2> => 
		    (case {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} 
		                       iso ((extendContradiction C) \x \d) ((extend C W) \x \d) <E x> <E' x> <T> <D1 x d> <D2 x d>
		       of {<x>}{<d>}<EQ x> => fooLam <EQ>)
	 | C W <E> <E'> <bvar' B> <D1> <D2> => isoVar W <E> <E'> <B> <D1> <D2>;


(*  ************************************************** *)




fun fooApp : <eqterm T1 T1'> -> <eqterm T2 T2'> -> <eqterm (app' T1 T2) (app' T1' T2')>
         = fn <eqtermid> <eqtermid> => <eqtermid> ;

fun fooLam : <eqterm T1 T1'> -> <eqterm (lam' T1) (lam' T1')>
         = fn <eqtermid> => <eqtermid> ;

fun fooBvar : <eqterm (bvar' B) (bvar' B')> -> <eqterm (bvar' (var_s B)) (bvar' (var_s B'))>
         = fn <eqtermid> => <eqtermid> ;
(* maybe forall M1 and forall M2?? *)
type iso2World = (<M:nat> -> <B:variable M> -> <E:exp#> -> <E':exp#> -> <trans E (bvar' B) #> -> <trans E' (bvar' B) #> -> <eqexp E E'>);

type iso2Contra1 = <N:nat> -> <M:variable N> -> <E1:exp> -> <E2:exp> -> <trans (app E1 E2) (bvar' M)> -> <empty> ;
type iso2Contra2 = <N:nat> -> <M:variable N> -> <E:exp -> exp> -> <trans (lam E) (bvar' M)> -> <empty> ;
fun contra : <empty> -> <eqterm T1 T2> = fn .;

type iso2World = (<M:nat> -> <B1:variable M> -> <B2:variable M> -> <E:exp#> -> <trans E (bvar' B1) #> -> <trans E (bvar' B2) #> -> <eqterm (bvar' B1) (bvar' B2)>);

fun extend : iso2World 
            -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} iso2World
	      = fn W => fn {<x>}{<d:trans x (bvar' (var_z : variable (s N) ))>} (<s N> <var_z> <var_z> <x> <d> <d> => <eqtermid>)
	                 | {<x>}{<d:trans x (bvar' (var_z : variable (s N) ))>} (<M> <B1> <B2> <Y> <D1> <D2> => 
	                        let
				  val <R> = W <M> <B1> <B2> <Y> <D1> <D2>
				in
				  {<x>}{<d>}<R>
				end \x \d);

(* BUG???  this does not pass coverage if E:exp is marked as parameter! *)
type iso2Contra3 = <E:exp#> -> <N:nat> -> <trans E (bvar' (var_z : variable (s N))) #> -> <B: variable N> -> <trans E (bvar' B)> -> <empty> ;

fun extendContradictionBUG : iso2Contra3 
             -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} iso2Contra3 
        = fn C => fn {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} 
                           (<E> <M> <D1> <B> <D2> => 
			       let
				 val R = C <E> <M> <D1> <B> <D2>
			       in
				 {<x>}{<d>}R
			       end \x \d);


type iso2Contra3 = <E:exp#> -> <N:nat> -> <trans E (bvar' (var_z : variable (s N))) #> -> <B: variable N> -> <trans E (bvar' B)> -> <empty> ;


fun impossibleParam : <trans E (bvar' (var_s B)) #> -> <empty>
     = fn .;

fun extendContradictionBUG : (<E:exp#> -> <N':nat> -> <lt N' N> -> <B0 : variable N> -> <trans E (bvar' B0) #> -> <B: variable N'> -> <trans E (bvar' B) #> -> <empty>)
             -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} 
                 (<E:exp#> -> <N':nat> -> <lt N' (s N)> -> <B0 : variable (s N)> -> <trans E (bvar' B0) #> -> <B: variable N'> -> <trans E (bvar' B) #> -> <empty>)
        = fn C => fn {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} (<x> <s N> <L: lt (s N) (s N)> <_> <d> <_> <d> => lessContra <L>)
		   | {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>}
			   (<E> <s N'> <L> <var_s B1> <Dbad> <B2> <D2> => 
			       let
				 val <bot> = impossibleParam <Dbad>				   
			       in
				 {<x>}{<d>}<bot>
			       end \x \d)
		   | {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>}
			   (<E> <s N'> <L> <B1> <D1> <var_s B2> <Dbad> => 
			       let
				 val <bot> = impossibleParam <Dbad>				   
			       in
				 {<x>}{<d>}<bot>
			       end \x \d);


type iso2Contra3 = <E:exp#> -> <N':nat> -> <N:nat> -> <lt N' N> -> <B0 : variable N> -> <trans E (bvar' B0) #> -> <B: variable N'> -> <trans E (bvar' B) #> -> <empty>;

fun extendContradiction : iso2Contra3
             -> {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} iso2Contra3

        = fn C => fn {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} (<x> <_> <_> <L> <_> <d> <_> <d> => lessContra <L>)
		   | {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>}
			   (<E> <N1> <N2> <L> <B1> <D1> <B2> <D2> =>
			       let
				 val <bot> = C <E> <N1> <N2> <L> <B1> <D1> <B2> <D2> 
			       in
				 {<x>}{<d>}<bot>
			       end \x \d)
		   | {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>}
			   (<E> <_> <_> <L> <var_s B1> <Dbad> <B2> <D2> => 
			       let
				 val <bot> = impossibleParam <Dbad>				   
			       in
				 {<x>}{<d>}<bot>
			       end \x \d);

fun iso2Var : <B: variable N> -> <trans E (bvar' (var_s B))> -> <M:nat> * <lt M (s N)> * <B2 : variable M> * <trans E (bvar' B2) #>
     = fn <var_z> <trans_var (D#)> => (<_>, <lt_b>, <var_z>, <D>)
        | <var_s B> <trans_var D> =>
                              let
				val (<M>,<L>,<B2>,<D2>) = iso2Var <B> <D>
			      in
				(<M>, <lt_ind L>, <B2>, <D2>)
			      end;

fun iso2 : iso2Contra1
         -> iso2Contra2 
         -> iso2Contra3
	 -> iso2World -> <T1:term N> -> <T2:term N> -> <E:exp> -> <trans E T1> -> <trans E T2> -> <eqterm T1 T2> =
        fn C1 C2 C3 W <app' T1 T2> <app' T1' T2'> <app E1 E2> <trans_app D1 D2> <trans_app D1' D2'> =>
	            let
		      val <P1> = iso2 C1 C2 C3 W <T1> <T1'> <E1> <D1> <D1'>
		      val <P2> = iso2 C1 C2 C3 W <T2> <T2'> <E2> <D2> <D2'>
		    in
		      fooApp <P1> <P2>
		    end

	 | C1 C2 C3 W <_> <_> <app E1 E2> <trans_var D> <_> => contra (C1 <_> <_> <E1> <E2> <D>)
	 | C1 C2 C3 W <_> <_> <app E1 E2> <_> <trans_var D> => contra (C1 <_> <_> <E1> <E2> <D>)

	 | C1 C2 C3 W <lam' T> <lam' T'> <lam E> <trans_lam D1> <trans_lam D2> => 
		    (case {<x>}{<d: trans x (bvar' (var_z : variable (s N) ))>} 
		                       iso2 C1 C2 ((extendContradiction C3) \x \d) ((extend W) \x \d) <T> <T'> <E x> <D1 x d> <D2 x d>
		       of {<x>}{<d>}<EQ> => fooLam <EQ>)

	 | C1 C2 C3 W <_> <_> <lam E> <trans_var D> <_> => contra (C2 <_> <_> <E> <D>)
	 | C1 C2 C3 W <_> <_> <lam E> <_> <trans_var D> => contra (C2 <_> <_> <E> <D>)
	 | C1 C2 C3 W <bvar' B1> <bvar' B2> <E#> <D1#> <D2#> => W <_> <B1> <B2> <E> <D1> <D2>
	 | C1 C2 C3 W <bvar' (var_s B1)> <bvar' (var_s B2)> <E#> <trans_var D1> <trans_var D2> =>
		                                           fooBvar (iso2 C1 C2 C3 W <bvar' B1> <bvar' B2> <E> <D1> <D2>)

	 | C1 C2 C3 W <bvar' var_z> <bvar' (var_s B2)> <E#> <D1#> <trans_var D2> => 
		    let  
		      val (<M'>, <L'>, <B2'>, <D2'>) = iso2Var <B2> <trans_var D2>
		      val <bot> = C3 <E> <M'> <s N> <L'> <var_z> <D1> <B2'> <D2'>
		    in
		      contra <bot>
		    end
	 | C1 C2 C3 W <bvar' (var_s B1)> <bvar' var_z>  <E#> <trans_var D1> <D2#> => 
		    let
		      val (<M'>, <L'>, <B1'>, <D1'>) = iso2Var <B1> <trans_var D1>
		      val <bot> = C3 <E> <_> <_> <L'> <var_z> <D2> <B1'> <D1'>
		    in
		      contra <bot>
		    end;


(*
params = .;

fun iso_closed : <E:exp> -> <E':exp> -> <T:term z> -> <trans E T> -> <trans E' T> -> <eqexp E E'>
                 = iso (fn .) (fn .);

fun toDebruijn_closed : <E:exp> -> <T:term z> * <trans E T> = toDebruijn <z> (fn .);
	
val test = toDebruijn_closed  <lam [x] lam [y] app y (lam [z] app y (app z x))>;

val test2 = let val (<T>,<_>) = test 
	        val (<E>, <_>) = toHOAS_closed <T>
	    in
	      <E>
	    end;
*)