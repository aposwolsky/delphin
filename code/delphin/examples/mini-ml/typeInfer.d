(* Hindley-Milner Type Inference Algorithm 
 *
 *
 * Author: Adam Poswolsky
 *
 * This shows how to conduct type inference where 
 * references + environments serve the role of references 
 * in the standard Hindly-Milner style algorithms.
 *
 * Environments are Delphin functions mapping
 * parameters to types.
 *
 * We use a continuation-style approach to create
 * new parameters and continue computation with those new parameters.
 *)

sig use "mini-ml.elf";
sig use "eval.elf";
sig use "value.elf";
sig use "tp.elf";
sig use "tpinf.elf";

params = <exp>, <tp>, <of _ _> ;

(* expEnv maps "exp" variables to types *)
type expEnv = <E:exp#> -> <tp>;


(* tpEnv maps "tp" variables to other types.
 * This will be used in unification, as two types will
 * be considered equal if they are mapped to the same result,
 * i.e. if they point to the same data.
 *)
type tpEnv  = <T:tp#> -> <tp>; 


(* normalize (G, T) = T' such that T' is the type T where we follow all the pointers in G *)
fun normalize : tpEnv -> <tp> -> <tp> =
    fn G <t#> => (case (G <t>) 
                       of <t> => <t> (* if it points to itself, then it is in normal form. *)
                        | <T> => normalize G <T>)
     | G <cross T1 T2> => <cross> @ (normalize G <T1>) @ (normalize G <T2>)
     | G <arrow T1 T2> => <arrow> @ (normalize G <T1>) @ (normalize G <T2>)

     | G <forall T> => let
			 val {<t>}<T' t> = {<t>} normalize (G with <t> => <t>) <T t>
                       in
                         <forall T'>
                       end
     | G <nat> => <nat>;


(* 
 * free :  Our routine to deallocate references.
 * 
 * i.e.  free({<t:tp#>} G) = G' 
 *      Where G' is G where all occurrences of <t> are removed.
 * 
 *      If the reference cell "t" does not hold a concrete type,
 *      then the expression we are typing is polymorphic in "t"
 *      and we make it a "forall". 
 *)

fun freeG : ({<t:tp#>} tpEnv) -> tpEnv
            = fn G <t2#> => case {<t>} normalize (G \t) <t2>
                                  of {<t>} <T> => <T> 
                                   | {<t>} <T t> => <forall T>;

fun freeGB : ({<x:exp#>} tpEnv) -> tpEnv
            = fn G <t2#> => case {<x>} normalize (G \x) <t2>
                                  of {<x>} <T> => <T>;

fun freeGtwice : ({<t1:tp#>} {<t2:tp#>} tpEnv) -> tpEnv
            = fn  G <t3#> => case {<t1>}{<t2>} normalize (G \t1 \t2) <t3>
                                  of {<t1>}{<t2>} <T> => <T> 
                                   | {<t1>}{<t2>} <T t1> => <forall T> 
                                   | {<t1>}{<t2>} <T t2> => <forall T> 
                                   | {<t1>}{<t2>} <T t1 t2> => <forall [t1] forall [t2] T t1 t2>;

fun freeGtwiceB : ({<t2:tp#>} {<x:exp#>} tpEnv) -> tpEnv
            = fn G <t3#> => case {<t2>}{<x>} normalize (G \t2 \x) <t3>
                                  of {<t2>}{<x>} <T> => <T> 
                                   | {<t2>}{<x>} <T t2> => <forall T>;

fun freeGthrice : ({<t1:tp#>} {<x:exp#>} {<t2:tp#>} tpEnv) -> tpEnv
            = fn G <t3#> => case {<t1>}{<x>}{<t2>} normalize (G \t1 \x \t2) <t3>
                                  of {<t1>}{<x>}{<t2>} <T> => <T> 
                                   | {<t1>}{<x>}{<t2>} <T t1> => <forall T> 
                                   | {<t1>}{<x>}{<t2>} <T t2> => <forall T> 
                                   | {<t1>}{<x>}{<t2>} <T t1 t2> => <forall [t1] forall [t2] T t1 t2>;


(* Unification.. 
 *   
 * unifyTypes G T1 T2 = G'
 * G' is an an update to the mapping in G to make T1 == T2
 *)
fun unifyTypes : tpEnv -> <tp> -> <tp> -> tpEnv =
          fn G T1 T2 => unifyTypesN G (normalize G T1) (normalize G T2)

and unifyTypesN : tpEnv -> <tp> -> <tp> -> tpEnv =
     fn G <t#> <t#> => G
      | G <t#> <T> => (fn <t> => <T>
                        | <t'> => G <t'>) 
      | G <T> <t#> => (fn <t> => <T>
                        | <t'> => G <t'>)
      | G <cross T1 T2> <cross T3 T4> => 
                         let
                             val G2 = unifyTypes G <T1> <T3>
                             val G3 = unifyTypes G2 <T2> <T4>
                         in
                             G3
                         end

      | G <arrow T1 T2> <arrow T3 T4> => 
                         let
                             val G2 = unifyTypes G <T1> <T3>
                             val G3 = unifyTypes G2 <T2> <T4>
                         in
                             G3
                         end


      | G <forall T1> <forall T2> =>
                 (case  ({<t>} let
                                 val Gnew = (G with <t> => <t>)
                              in
                                 unifyTypes Gnew <T1 t> <T2 t> 
                              end)

                    of  Gextended => freeG Gextended (* gets rid of occurrence of t *) )

      | G <nat> <nat> => G;


(* checkTypeSchema G <Tschema> <Targ> <Tresult> K  = G'
 * This function checks that the schema (Tschema) is compatible with argument (Targ)
 * and that the result of the application is Tresult.
 *
 * where K is a continuation
 *)
fun checkTypeSchema : tpEnv -> <tp> -> <tp> -> <tp> -> (tpEnv -> tpEnv) ->  tpEnv =
     fn G <Tschema> <Targ> <Tresult> K => checkTypeSchemaN G (normalize G <Tschema>) <Targ> <Tresult> K

and checkTypeSchemaN : tpEnv -> <tp> -> <tp> -> <tp> -> (tpEnv -> tpEnv) -> tpEnv =
     fn G <arrow T1 T2> <Targ> <Tresult> K => 
                   let
		     val G2 = unifyTypes G <T1> <Targ>
		     val G3 = unifyTypes G2 <T2> <Tresult>
                   in
                     K G3
                   end

      | G <forall T> <Targ> <Tresult> K => 
           (case ({<t>}
                      let
			val G' = (G with <t> => <t>)
                      in
			checkTypeSchema G' <T t> <Targ> <Tresult> K
                      end)
             of Gextended => freeG Gextended);



(* checkType (W, G, E, T, K) = G'
 * 
 * This is the MAIN function where
 *
 * W : map of exp variables
 * G : map of tp variables
 * E : exp we are typing
 * T : desired type of E
 * 
 * K is the continuation returning a G'
 *)
fun checkType : expEnv -> tpEnv -> <exp> -> <tp> -> (tpEnv -> tpEnv) ->  tpEnv =
     fn W G <x#> <T> K => K (unifyTypes G (W <x>) <T>) 
      | W G <z> <T> K => K (unifyTypes G <nat> <T>)
      | W G <s E> <T> K => checkType W G <E> <nat> (fn G2 => K (unifyTypes G2 <nat> <T>))
      | W G <case E1 E2 E3> <T> K =>
                checkType W G <E1> <nat>
                            (fn G2 => checkType W G2 <E2> <T>
                                  (fn G3 => case {<x>} checkType (W with <x> => <nat>) G3 <E3 x> <T> K
                                                 of Gextended => freeGB Gextended))

       | W G <pair E1 E2> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = G with <t1> => <t1>  | <t2> => <t2> 
                        in
			   checkType W G' <E1> <t1> (fn G2 => checkType W G2 <E2> <t2> (fn G3 => K (unifyTypes G3 <T> <cross t1 t2>)))
                        end
	      of Gextended => freeGtwice Gextended)

       | W G <fst E> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = G with <t1> => <t1>  | <t2> => <t2> 
                        in
			   checkType W G' <E> <cross t1 t2> (fn G2 => K (unifyTypes G2 <T> <t1>))
                        end
	      of Gextended => freeGtwice Gextended)

       | W G <snd E> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = G with <t1> => <t1>  | <t2> => <t2> 
                        in
			   checkType W G' <E> <cross t1 t2> (fn G2 => K (unifyTypes G2 <T> <t2>))
                        end
	      of Gextended => freeGtwice Gextended)


       | W G <lam E> <T> K =>  
             (case
               {<t1>}{<x>}{<t2>}
                       let
                          val W' = W with <x> => <t1>
			  val G' = G with <t1> => <t1> | <t2> => <t2>
                       in
                          checkType W' G' <E x> <t2> (fn G2 => K (unifyTypes G2 <T> <arrow t1 t2>))
		       end
               of Gextended => freeGthrice Gextended)



       | W G <app E1 E2> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = G with <t1> => <t1>  | <t2> => <t2>
                        in
			   checkType W G' <E2> <t1> (fn G2 =>
                                                      checkType W G2 <E1> <t2> (fn G3 =>
                                                                                checkTypeSchema G3 <t2> <t1> <T> K))
                        end
	      of Gextended => freeGtwice Gextended)


       | W G <letv E1 E2> <T> K =>
	     let
               fun getType : ({<t:tp#>} tpEnv) -> <tp>
                    = fn GG  => case {<t>} normalize (GG \t) <t>
                                  of {<t>} <T'> => <T'> 
                                   | {<t>} <T' t> => <forall T'> 
	       val Gnew = {<t>} checkType W G <E1> <t> (fn G' => G')
	       val <Targ> = getType Gnew
	       val Gnew' = freeG Gnew
             in
              case
                  {<t2>}{<x>}
                       let
                          val W' = (W with <x> => <Targ>)
			  val G' = (Gnew' with <t2> => <t2>)
                       in
                          checkType W' G' <E2 x> <t2> (fn G3 => K (unifyTypes G3 <T> <t2>))
		       end
               of Gextended => freeGtwiceB Gextended
             end


       | W G <letn E1 E2> <T> K  =>
	     let
               fun getType : ({<t:tp#>} tpEnv) -> <tp>
                    = fn GG  => case {<t>} normalize (GG \t) <t>
                                  of {<t>} <T'> => <T'> 
                                   | {<t>} <T' t> => <forall T'> 
	       val Gnew = {<t>} checkType W G <E1> <t> (fn G' => G')
	       val <Targ> = getType Gnew
	       val Gnew' = freeG Gnew
             in
              case
                 {<t2>}
                       let
			  val G' = Gnew' with <t2> => <t2>
                       in
                          checkType W G' <E2 E1> <t2> (fn G3 => K (unifyTypes G3 <T> <t2>))
		       end
               of Gextended => freeG Gextended
             end

       | W G <fix E> <T> K =>  
             (case
               {<t1>}{<x>}
                       let
                          val W' = (W with <x> => <t1>)
			  val G' = (G with <t1> => <t1>)
                       in
                          checkType W' G' <E x> <t1> (fn G2 => K (unifyTypes G2 <T> <t1>))
		       end
               of Gextended => freeGtwiceB Gextended);


val inferType : <exp> -> <tp> 
 = fn <E> => let
               val G = {<t>} checkType (fn .) (fn <t'#> => <t'>) <E> <t> (fn G' => G')

               fun getType : ({<t:tp#>} tpEnv) -> <tp>
                    = fn G  => case {<t>} normalize (G \t) <t>
                                  of {<t>} <T> => <T> 
                                   | {<t>} <T t> => <forall T> 
             in
               getType G
             end;


val example3' = inferType <lam [x] x> ;
val example4' = inferType <letv (lam [x] x) ([u:exp] pair (app u z) (app u (pair z z)))> ;
