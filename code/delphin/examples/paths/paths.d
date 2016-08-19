(* Paths through lambda terms
 * Author: Adam Poswolsky
 * Based on a proof by Andrew Gacek in Abella (http://abella.cs.umn.edu/development/examples/path.html)
 *
 * We use Delphin to prove that if all paths in a term M are also paths in a term N, then M = N
 * This is an example utilizing the higher-order nature of Delphin as the hypothesis is itself
 * a function.  This cannot be directly encoded in Twelf.
 *)

(* Untyped lambda-expressions *)
sig <tm : type> %name M x
    <app : tm -> tm -> tm>
    <abs : (tm -> tm) -> tm>;

sig <trace : type> %name P p
    <fst : trace -> trace>
    <snd : trace -> trace>
    <bnd : (trace -> trace) -> trace>
    <done : trace>;

(* Paths through lambda-expressions *)
sig <path : tm -> trace -> type> %name D u
    <p_appL : path M P -> path (app M N) (fst P)>
    <p_appR : path N P -> path (app M N) (snd P)>
    <p_abs : ({x} {p} path x p -> path (R x) (S p)) -> path (abs R) (bnd S)>
    <p_done : path M done> (* partial path *) ;

(* Simple definition of equality *)
sig <eq : tm -> tm -> type>
    <eq_base : eq M M>;


(* The following functions make sense in a world containing parameters of the
 * following types
 *)
params = <tm>, <trace>, <path (x#) (p#)>;

(* If (path N (fst P)) then N = (app N1 N2) *)
fun appInversion : <path N (fst P)> -> <N1:tm> * <N2:tm> * <eq N (app N1 N2)>
                 = fn <(p_appL D) : (path (app N1 N2) (fst P))> => (<N1>, <N2>, <eq_base>);

(* If (path N (bnd P)) then N = (abs S) *)
fun absInversion : <path N (bnd P)> -> <S:(tm -> tm)> * <eq N (abs S)>
                 = fn <(p_abs D) : (path (abs S) _)> => (<S>, <eq_base>);

(* If N = (app N1 N2) and M1 = N1 and M2 = N2, then (app M1 M2) = N *)
fun eqPropApp : <eq N (app N1 N2)> -> <eq M1 N1> -> <eq M2 N2> -> <eq (app M1 M2) N>
              = fn <eq_base> <eq_base> <eq_base> => <eq_base>;

(* If N = (abs S) and forall x. (M x) = (S x), then (abs M) = N *)
fun eqPropAbs : <eq N (abs S)> -> <{x} eq (M x) (S x)> -> <eq (abs M) N>
              = fn <eq_base> <[x] eq_base> => <eq_base>;


(* This next function takes a property of paths on (app M1 M2) and converts
 * it to a property on paths of M1 and paths of M2
 *)
fun  appProp : <eq N (app N1 N2)> -> (<P:trace> -> <path (app M1 M2) P> -> <path N P>)
               -> (<P:trace> -> <path M1 P> -> <path N1 P>) * (<P:trace> -> <path M2 P> -> <path N2 P>)
     = fn <eq_base> pathProp =>
          let
	    val pathProp1 : (<P:trace> -> <path M1 P> -> <path N1 P>)
                          = fn <P> <D> => (case (pathProp <fst P> <p_appL D>)
                                              of <p_appL D'> => <D'>)

	    val pathProp2 : (<P:trace> -> <path M2 P> -> <path N2 P>)
                          = fn <P> <D> => (case (pathProp <snd P> <p_appR D>)
                                              of <p_appR D'> => <D'>)					   
	  in
	    (pathProp1, pathProp2)
	  end;

(* This next function takes a property of paths on (abs M) and creates
 * a property on paths for (M x) where x is a new parameter
 *)
fun  absProp : <eq N (abs S)> -> (<P:trace> -> <path (abs M) P> -> <path N P>)
               -> {<x:tm>}{<p:trace>}{<d:path x p>}(<P:trace> -> <path (M x) P> -> <path (S x) P>)
     = fn <eq_base> pathProp =>
         fn {<x>}{<p>}{<d: path x p>} <P p> <D x p d> => 
	            let
		      val <p_abs R> = pathProp <bnd P> <p_abs D>
		    in
		      {<x>}{<p>}{<d>} <R x p d>
		    end \x \p \d;

(* This is the main function which states for all M,N if
   (1) for every parameter x, then (var x) is a valid path.
   (2) forall P, (path M P) implies (path N P)
  then
   M = N
*)
fun path_equal : <M:tm> 
                 -> <N:tm>
                 -> (<x:tm#> -> <y:trace#> * <path x y>) (* Property 1 of context *)
                 -> (<x:tm#> -> <y:trace#> -> <R:tm> -> <path x y> -> <path R y> -> <eq x R>) (* Property 2 of context *)
                 -> (<P:trace> -> <path M P> -> <path N P>) (* N has all the same paths as M *)
                 -> <eq M N> (* then M = N *)
  = fn <app M1 M2> <N> ctxProp1 ctxProp2 pathProp =>
         let
           (* We know the trace (fst done) expresses a path for (app M1 M2),
            * with proof term (p_appL p_done)
	    * so we apply pathProp to argue that (fst done) is also good for N *)
	   val equivPath : <path N (fst done)> = pathProp <fst done> <p_appL p_done>
	   val (<N1>, <N2>, <D : eq N (app N1 N2)>) = appInversion equivPath
	   val (pathPropM1, pathPropM2) = appProp <D> pathProp

	   val <eqM1N1> = path_equal <M1> <N1> ctxProp1 ctxProp2 pathPropM1
	   val <eqM2N2> = path_equal <M2> <N2> ctxProp1 ctxProp2 pathPropM2
	 in
	   eqPropApp <D> <eqM1N1> <eqM2N2>
	 end

     | <abs [x] M x> <N> ctxProp1 ctxProp2 pathProp =>
         let
           (* We know the trace (bnd [p] done) expresses a path for (abs [x] M x),
            * with proof term (p_abs [x][d] p_done)
	    * so we apply pathProp to argue that (bnd [p] done) is also good for N *)
	   val equivPath : <path N (bnd [p] done)> = pathProp <bnd [p] done> <p_abs [x] [p] [d] p_done>
	   val (<S>, <D : eq N (abs S)>) = absInversion equivPath
	 in
	   case {<x>}{<p>}{<d>} (path_equal 
                                      <M x> 
                                      <S x> 
                                      (ctxProp1 with <x> => (<p>, <d>)) 
                                      (ctxProp2 with <x> <p> <x> <d> <d> => <eq_base>)
                                      ((absProp <D> pathProp) \x \p \d))
	     of {<x>}{<p>}{<d>} <D' x> =>
	           eqPropAbs <D> <D'>
	 end


     | <x#> <N> ctxProp1 ctxProp2 pathProp =>
         let
	   val (<y>, givenPath) = ctxProp1 <x>
	   val equivPath : <path N y> = pathProp <y> givenPath
         in
	   ctxProp2 <x> <y> <N> givenPath equivPath
	 end;   

(* The property on the context holds on closed terms, so our final theorem
 * gets rid of the context property 
*)
params = . ; (* indicates that subsequent functions are over closed expressions *)

fun path_equalClosed : (<P:trace> -> <path M P> -> <path N P>) -> <eq M N>
                     = fn pathProp => path_equal <_> <_> (fn .) (fn .) pathProp;

