(* Hindley-Milner Type Inference Algorithm 
 *
 *
 * Author: Adam Poswolsky
 *
 * This shows how to conduct type inference utilizing 
 * parameters instead of references.  We pass around
 * environments mapping parameters to schemes (forall quantified types).
 *
 * Uses a continuation style approach.
 *)

sig use "mini-ml.elf";
sig use "eval.elf";
sig use "value.elf";
sig use "tp.elf";
sig use "tpinf.elf";

type expEnv = <E:exp#> -> <scheme>;
type tpEnv  = <T:tp#> -> <scheme>; 

fun extendW : expEnv -> <T':scheme> -> {<x:exp#>} expEnv
           = fn W => fn <T'> => fn {<x>} (<x> => <T'>)
                               | {<x>} (<x'> =>   (let
                                                         val result = W <x'>
                                                       in
                                                         {<x>} result
                                                       end) \x);

fun extendG : tpEnv -> {<t:tp#>} tpEnv
           = fn G => fn {<x>} (<x> => <! x>)
                      | {<x>} (<x'> => (let
                                              val result = G <x'>
                                            in
                                              {<x>} result
                                            end)\x );


fun normalize : tpEnv -> <scheme> -> <scheme> =
    fn G <! t#> => (case (G <t>) 
                        of <! t> => <! t>
                         | <S> => normalize G <S>)
     | G <! (cross T1 T2)> => let
				val <! T1'> = normalize G <! T1>
                                val <! T2'> = normalize G <! T2>
                              in
	                        <! (cross T1' T2')>
			      end
     | G <! (arrow T1 T2)> => let
				val <! T1'> = normalize G <! T1>
                                val <! T2'> = normalize G <! T2>
                              in
	                        <! (arrow T1' T2')>
			      end

     | G <! nat> => <! nat>
     | G <forall T> =>  let
			   val {<t>}<T' t> = {<t>} normalize ((extendG G)\t) <T t>
		        in
                           <forall T'>
		        end;


fun shrinkG : ({<t:tp#>} tpEnv) -> tpEnv
            = fn G <t2#> => case {<t>} normalize (G \t) <! t2>
                                  of {<t>} <T> => <T> 
                                   | {<t>} <T t> => <forall T>;

fun shrinkGB : ({<x:exp#>} tpEnv) -> tpEnv
            = fn G <t2#> => case {<x>} normalize (G \x) <! t2>
                                  of {<x>} <T> => <T>;

fun shrinkGtwice : ({<t1:tp#>} {<t2:tp#>} tpEnv) -> tpEnv
            = fn G <t3#> => case {<t1>}{<t2>} normalize (G \t1 \t2) <! t3>
                                  of {<t1>}{<t2>} <T> => <T> 
                                   | {<t1>}{<t2>} <T t1> => <forall T> 
                                   | {<t1>}{<t2>} <T t2> => <forall T> 
                                   | {<t1>}{<t2>} <T t1 t2> => <forall [t1] forall [t2] T t1 t2>;

fun shrinkGtwiceB : ({<t2:tp#>} {<x:exp#>} tpEnv) -> tpEnv
            = fn G <t3#> => case {<t2>}{<x>} normalize (G \t2 \x) <! t3>
                                  of {<t2>}{<x>} <T> => <T> 
                                   | {<t2>}{<x>} <T t2> => <forall T>;

fun shrinkGthrice : ({<t1:tp#>} {<x:exp#>} {<t2:tp#>} tpEnv) -> tpEnv
            = fn G <t3#> => case {<t1>}{<x>}{<t2>} normalize (G \t1 \x \t2) <! t3>
                                  of {<t1>}{<x>}{<t2>} <T> => <T> 
                                   | {<t1>}{<x>}{<t2>} <T t1> => <forall T> 
                                   | {<t1>}{<x>}{<t2>} <T t2> => <forall T> 
                                   | {<t1>}{<x>}{<t2>} <T t1 t2> => <forall [t1] forall [t2] T t1 t2>;



(* unifyTypes G T1 T2 = G'
 * Where G is an environment mapping tp params to other types.
 *)
fun unifyTypes : tpEnv -> <tp> -> <tp> -> tpEnv =
          fn G <T1> <T2> => unifyScheme G <! T1> <! T2>

and unifyScheme : tpEnv -> <scheme> -> <scheme> -> tpEnv = 
	  fn G <S1> <S2> => unifySchemeN G (normalize G <S1>) (normalize G <S2>)

and unifySchemeN : tpEnv -> <scheme> -> <scheme> -> tpEnv =
     fn G <! t#> <! t> => G
      | G <! t#> <T> => (fn <t> => <T>
                         | <t'> => G <t'>) 
      | G <T> <! t#> => (fn <t> => <T>
                          | <t'#> => G <t'>)
      | G <! (cross T1 T2)> <! (cross T3 T4)> => 
                         let
                             val G2 = unifyTypes G <T1> <T3>
                             val G3 = unifyTypes G2 <T2> <T4>
                         in
                             G3
                         end

      | G <! (arrow T1 T2)> <! (arrow T3 T4)> => 
                         let
                             val G2 = unifyTypes G <T1> <T3>
                             val G3 = unifyTypes G2 <T2> <T4>
                         in
                             G3
                         end

      | G <! nat> <! nat> => G

      | G <forall T1> <forall T2> =>
                 (case  ({<t>} let
                                 val Gnew = (extendG G) \t
                              in
                                 unifyScheme Gnew <T1 t> <T2 t> 
                              end)

                    of  Gextended => shrinkG Gextended);




(* checkTypeSchema G <Tschema> <Targ> <Tresult> K *)
fun checkTypeSchema : tpEnv -> <scheme> -> <tp> -> <tp> -> (tpEnv -> tpEnv) ->  tpEnv =
     fn G <Tschema> <Targ> <Tresult> K => checkTypeSchemaN G (normalize G <Tschema>) <Targ> <Tresult> K

and checkTypeSchemaN : tpEnv -> <scheme> -> <tp> -> <tp> -> (tpEnv -> tpEnv) -> tpEnv =
     fn G <! (arrow T1 T2)> <Targ> <Tresult> K => 
                   let
		     val G2 = unifyTypes G <T1> <Targ>
		     val G3 = unifyTypes G2 <T2> <Tresult>
                   in
                     K G3
                   end

      | G <forall T> <Targ> <Tresult> K => 
           (case ({<t>}
                      let
			val G' = (extendG G) \t
                      in
			checkTypeSchema G' <T t> <Targ> <Tresult> K
                      end)
             of Gextended => shrinkG Gextended);



(* checkType expEnvironment tpEnvironment exp continuation *) 
fun checkType : expEnv -> tpEnv -> <exp> -> <tp> -> (tpEnv -> tpEnv) ->  tpEnv =
     fn W G <x#> <T> K => K (unifyScheme G (W <x>) <! T>) 
      | W G <z> <T> K => K (unifyTypes G <nat> <T>)
      | W G <s E> <T> K => checkType W G <E> <nat> (fn G2 => K (unifyTypes G2 <nat> <T>))
      | W G <case E1 E2 E3> <T> K =>
                checkType W G <E1> <nat>
                            (fn G2 => checkType W G2 <E2> <T>
                                  (fn G3 => case {<x>} checkType ((extendW W <! nat>) \x) G3 <E3 x> <T> K
                                                 of Gextended => shrinkGB Gextended))


       | W G <pair E1 E2> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = ((extendG ((extendG G) \t1)) \t2)
                        in
			   checkType W G' <E1> <t1> (fn G2 => checkType W G2 <E2> <t2> (fn G3 => K (unifyTypes G3 <T> <cross t1 t2>)))
                        end
	      of Gextended => shrinkGtwice Gextended)

       | W G <fst E> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = ((extendG ((extendG G) \t1)) \t2)
                        in
			   checkType W G' <E> <cross t1 t2> (fn G2 => K (unifyTypes G2 <T> <t1>))
                        end
	      of Gextended => shrinkGtwice Gextended)

       | W G <snd E> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = ((extendG ((extendG G) \t1)) \t2)
                        in
			   checkType W G' <E> <cross t1 t2> (fn G2 => K (unifyTypes G2 <T> <t2>))
                        end
	      of Gextended => shrinkGtwice Gextended)


       | W G <lam E> <T> K =>  
             (case
               {<t1>}{<x>}{<t2>}
                       let
                          val W' = (let val R = ((extendW W <! t1>) \x) in {<t2>}R end) \t2
			  val G' = (extendG ((let 
                                                  val G' = (extendG G) \t1
                                              in {<x>}G'
                                              end) \x)) \t2
                       in
                          checkType W' G' <E x> <t2> (fn G2 => K (unifyTypes G2 <T> <arrow t1 t2>))
		       end
               of Gextended => shrinkGthrice Gextended)



       | W G <app E1 E2> <T> K =>
             (case
                {<t1>}{<t2>} 
                        let
                           val G' = ((extendG ((extendG G) \t1)) \t2)
                        in
			   checkType W G' <E2> <t1> (fn G2 =>
                                                      checkType W G2 <E1> <t2> (fn G3 =>
                                                                                checkTypeSchema G3 <! t2> <t1> <T> K))
                        end
	      of Gextended => shrinkGtwice Gextended)


       | W G <letv E1 E2> <T> K =>
	     let
               fun getType : ({<t:tp#>} tpEnv) -> <scheme>
                    = fn GG  => case {<t>} normalize (GG \t) <! t>
                                  of {<t>} <T'> => <T'> 
                                   | {<t>} <T' t> => <forall T'> 
	       val Gnew = {<t>} checkType W G <E1> <t> (fn G' => G')
	       val <Targ> = getType Gnew
	       val Gnew' = shrinkG Gnew
             in
              case
                  {<t2>}{<x>}
                       let
                          val W' = (extendW W <Targ>) \x
			  val G' = (let val G' = (extendG Gnew') \t2
                                          in {<x>}G'
                                    end) \x
                       in
                          checkType W' G' <E2 x> <t2> (fn G3 => K (unifyTypes G3 <T> <t2>))
		       end
               of Gextended => shrinkGtwiceB Gextended
             end


       | W G <letn E1 E2> <T> K  =>
	     let
               fun getType : ({<t:tp#>} tpEnv) -> <scheme>
                    = fn GG  => case {<t>} normalize (GG \t) <! t>
                                  of {<t>} <T'> => <T'> 
                                   | {<t>} <T' t> => <forall T'> 
	       val Gnew = {<t>} checkType W G <E1> <t> (fn G' => G')
	       val <Targ> = getType Gnew
	       val Gnew' = shrinkG Gnew
             in
              case
                 {<t2>}
                       let
			  val G' = (extendG Gnew') \t2
                       in
                          checkType W G' <E2 E1> <t2> (fn G3 => K (unifyTypes G3 <T> <t2>))
		       end
               of Gextended => shrinkG Gextended
             end

       | W G <fix E> <T> K =>  
             (case
               {<t1>}{<x>}
                       let
                          val W' = (extendW W <! t1>) \x
			  val G' = (let val G' = (extendG G) \t1
                                          in {<x>}G'
                                    end) \x
                       in
                          checkType W' G' <E x> <t1> (fn G2 => K (unifyTypes G2 <T> <t1>))
		       end
               of Gextended => shrinkGtwiceB Gextended);


fun inferType : <exp> -> <scheme> 
 = fn <E> => let
               (* warning:  If you make this "val G" then you cannot use "G" as a fresh pattern variable below.. *)
               val G99 = {<t>} checkType (fn .) (fn <t'#> => <! t'>) <E> <t> (fn G' => G')

               fun getType : ({<t:tp#>} tpEnv) -> <scheme>
                    = fn G  => case {<t>} normalize (G \t) <! t>
                                  of {<t>} <T> => <T> 
                                   | {<t>} <T t> => <forall T> 
             in
               getType G99
             end;


val example3' = inferType <lam [x] x> ;
val example4' = inferType <letv (lam [x] x) ([u:exp] pair (app u z) (app u (pair z z)))> ;
