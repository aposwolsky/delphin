(* Meta Properties of Mini-ML
 * Author: Adam Poswolsky
 *)

use "typeInfer.d"; (* loads signature and some type inference functions, including "checkType" *)


(* Execution of eval judgment *)
fun executeEval : <E:exp> -> <V:exp> * <eval E V>
  = fn <z> => (<z>, <ev_z>)
     | <s X> =>
           let 
              val (<V>, <D>) = executeEval <X>
           in
             (<s V>, <ev_s D>)
           end

     | <case E1 E2 E3> => 
           (case (executeEval <E1>)
             of (<z>, <D1>) => 
                              let 
                                 val (<V>,<D2>) = executeEval <E2>
                              in
				 (<V>, <ev_case_z D1 D2>)
                              end
              | (<s X>, <D1>) =>
                              let 
                                 val (<V>,<D3>) = executeEval <E3 X>
                              in
				 (<V>, <ev_case_s D1 D3>)
                              end)

     | <pair E1 E2> => 
             let
                val (<V1>, <D1>) = executeEval <E1>
                val (<V2>, <D2>) = executeEval <E2>
             in
                (<pair V1 V2>, <ev_pair D1 D2>)
             end

     | <fst E> =>
             let
                val (<pair V1 V2>, <D>) = executeEval <E>
             in
                (<V1>, <ev_fst D>)
             end

     | <snd E> =>
             let
                val (<pair V1 V2>, <D>) = executeEval <E>
             in
                (<V2>, <ev_snd D>)
             end

     | <lam E> => (<lam E>, <ev_lam>)

     | <app E1 E2> =>
             let
                val (<lam E1'>, <D1>) = executeEval <E1>
                val (<V2>, <D2>) = executeEval <E2>
                val (<V>, <D3>) = executeEval <E1' V2>
             in
                (<V>, <ev_app D1 D2 D3>)
             end

     | <letv E1 E2> =>
             let
                val (<V1>, <D1>) = executeEval <E1>
                val (<V>, <D2>) = executeEval <E2 V1>
             in
                (<V>, <ev_letv D1 D2>)
             end

     | <letn E1 E2> =>
             let
                val (<V>, <D>) = executeEval <E2 E1>
             in
                (<V>, <ev_letn D>)
             end

    | <fix E> =>
             let
                val (<V>, <D>) = executeEval <E (fix E)>
             in
                (<V>, <ev_fix D>)
             end;


(* Value Soundness *)
fun vs : <eval E V> -> <value V>
  = fn <ev_z> => <val_z> 
     | <ev_s D> => <val_s> @ (vs <D>)
     | <ev_case_z D1 D2> => vs <D2>
     | <ev_case_s D1 D3> => vs <D3>
     | <ev_pair D1 D2> => <val_pair> @ (vs <D1>) @ (vs <D2>)
     | <ev_fst D> => (case (vs <D>)
                     of <val_pair P1 P2> => <P1>)
     | <ev_snd D> => (case (vs <D>)
                     of <val_pair P1 P2> => <P2>)
     | <ev_lam>   => <val_lam>
     | <ev_app D1 D2 D3> => vs <D3>
     | <ev_letv D1 D2> => vs <D2>
     | <ev_letn D2> => vs <D2>
     | <ev_fix D1> => vs <D1>;


(* Type Preservation *)


fun tps_pres : <eval E V> -> <ofs E S> -> <ofs V S>
        = fn <D> <!of! P> => let
                                val <Q> = tp_pres <D> <P>
                             in
                                <!of! Q>
                             end

           | <D> <ofs_polyelim Targ P> =>
                             (* D : eval E V
                              * P : ofs E (forall T) 
                              *)
                             let
                                val <Q> = tps_pres <D> <P>
                             in
				case <Q> of
                                  <ofs_polyintro Df> => <Df Targ>
                                 | _ =>  <ofs_polyelim Targ Q>
                             end

                   
           | <D> <ofs_polyintro P> =>
                             (* D : eval E V
                              * P : {t:tp} ofs E (T t)
                              *)
                              (case {<t>} tps_pres <D> <P t>
                               of {<t>}<Q t> => <ofs_polyintro Q>)


and tp_pres : <eval E V> -> <of E T> -> <of V T>
        = fn <E> <apply_scheme S>  => let
                                         val <S'> = tps_pres <E> <S>
                                      in
                                         case <S'>
                                         of <!of! R> => <R>
                                          | _ => <apply_scheme S'> 
                                      end

           | <ev_z> <tp_z>         => <tp_z>
           | <ev_s D1> <tp_s P1>   => <tp_s> @ (tp_pres <D1> <P1>)
           | <ev_case_z D1 D2> <tp_case P1 P2 P3> => tp_pres <D2> <P2> 
           | <ev_case_s D1 D3> <tp_case P1 P2 P3> => 
	               let
	                 val <tp_s Q1'> = tp_pres <D1> <P1>      
		       in
                         tp_pres <D3> <P3 _ Q1'>
                       end
	   | <ev_pair D1 D2> <tp_pair P1 P2> => 
                       let
			  val <Q1> = tp_pres <D1> <P1>
                          val <Q2> = tp_pres <D2> <P2>
                       in
                          <tp_pair Q1 Q2>
		       end

           | <ev_fst D1> <tp_fst P1> =>
                       let
                          val <tp_pair Q1 Q2> = tp_pres <D1> <P1> 
                       in
			  <Q1>
                       end
           | <ev_snd D1> <tp_snd P1> =>
                       let
                          val <tp_pair Q1 Q2> = tp_pres <D1> <P1> 
                       in
			  <Q1>
                       end

           | <ev_lam> <tp_lam P> => <tp_lam P>

	   | <ev_app D1 D2 D3> <tp_app P1 P2>  =>
                       (* D1 : eval E1 (lam E1')
                        * D2 : eval E2 V2
                        * D3 : eval (E1' V2) V
                        *
                        * P1 : of E1 (arrow T1 T2)
                        * P2 : of E2 T1
                        *)
                       let
			  val <tp_lam Q1> = tp_pres <D1> <P1> (* Q1 : {x} of x T1 -> of (E1' x) T2 *) 
                          val <Q2> = tp_pres <D2> <P2> (* Q2 : of V2 T1  *)
                        in
			  tp_pres <D3> <Q1 _ Q2>
 			end


           | <ev_letv D1 D2> <tp_letv P1 P2> =>
                       (* D1 : eval E1 V1
                        * D2 : eval (E2 V1) V
                        *
                        * P1: ofs E1 S1
                        * P2 : ({x}ofs x S1 -> of (E2 x) T2)
                        *)
                       let
                          val <Q1> = tps_pres <D1> <P1>
                       in
                          tp_pres <D2> <P2 _ Q1>
                       end

           | <ev_letn D2> <tp_letn P1 P2> => tp_pres <D2> <P2>

           | <ev_fix D1> <tp_fix P1> => tp_pres <D1> <P1 _ (tp_fix P1)>;


type world = <E:exp#> -> <S:scheme> * <ofs E S>;

fun inferSchemeW : world -> <exp> -> <scheme> 
 = fn W <E> => let
                  fun convW : world -> expEnv
                             = fn W1 [<e>] e => (case (W1 e)
                                                of (<T>, R) => <T>)
                 
                  val G99 = {<t>} checkType (convW W) (fn [<t':tp#>]t' => <! t'>) <E> <t> (fn G' => G')

                  fun getType : ({<t:tp#>} tpEnv) -> <scheme>
                        = fn G  => case {<t>} normalize (G \t) <! t>
                                  of {<t>} <T> => <T> 
				   | {<t>} <T t> => <forall T> 
             in
               getType G99
             end;


fun inferTypeW : world -> <exp> -> <tp> 
 = fn W <E> => let
                  val <! T> = inferSchemeW W <E>
               in
                  <T>
               end;

fun extend : world -> <T':tp> -> {<x:exp#>}{<y:of x T'>}world
           = fn W => fn <T'> => fn {<x>}{<y>} (x => (<! T'>, <!of! y>))
                               | [<x'>]{<x>}{<y>} (x' => 
                                                       (let
                                                         val result = W x'
                                                       in
                                                         {<x>}{<y>} result
                                                       end) \x \y);

fun extendScheme : world -> <S:scheme> -> {<x:exp#>}{<y:ofs x S>}world
           = fn W => fn <S> => fn {<x>}{<y>} (x => (<S>, <y>))
                               | [<x'>]{<x>}{<y>} (x' => 
                                                       (let
                                                         val result = W x'
                                                       in
                                                         {<x>}{<y>} result
                                                       end) \x \y);

fun reduceScheme' : tpEnv -> <S:scheme>  -> <Targ:tp> -> <Tres:tp> -> tpEnv = 
     fn G <! T> <Targ> <Tresult> => unifyTypes G <T> <arrow Targ Tresult>

      | G <forall Tfun> <Targ> <Tresult> => 
                  let
                     val Gextended = {<t:tp#>} reduceScheme' ((extendG G)\t) <Tfun t> <Targ> <Tresult>
		  in
		     shrinkG Gextended
                  end;


fun reduceScheme : <ofs E S> -> <Targ:tp> -> <Tres:tp> -> <ofs E (! (arrow Targ Tres))> = 
     fn <D : ofs E (! (arrow Targ Tres))> <Targ> <Tres> => <D>

      | <ofs_polyintro (D : {t}ofs E (Tfun t))> <Targ> <Tres> =>
                                         (* D : {t}ofs E (Tfun t) *)
                                         let
                                            val Gextended = {<t:tp>} reduceScheme' (fn [<T':tp#>]T' => <! T'>) <Tfun t> <Targ> <Tres>

		 		            fun getType : ({<t:tp#>} tpEnv) -> <tp>
                        			= fn G  => case {<t>} normalize (G \t) <! t>
                                    			   of {<t>} <! T> => <T> 
                     
                     			    val <T'> = getType Gextended
					    val <P> = reduceScheme <D T'> <Targ> <Tres> 
			                in
		     			    <P>
                			end

      | <D : ofs E (forall [t] (Tfun t))> <Targ> <Tres> =>
                                         let
                                            val Gextended = {<t:tp>} reduceScheme' (fn [<T':tp#>]T' => <! T'>) <Tfun t> <Targ> <Tres>

		 		            fun getType : ({<t:tp#>} tpEnv) -> <tp>
                        			= fn G  => case {<t>} normalize (G \t) <! t>
                                    			   of {<t>} <! T> => <T> 
                     
                     			    val <T'> = getType Gextended
					    val <P> = reduceScheme <ofs_polyelim T' D> <Targ> <Tres> 
			                in
		     			    <P>
                			end;




fun calcOfs : world -> <E:exp> -> <S:scheme> -> <ofs E S> =
      fn W [<x#>]<x> <S> => 
			  let 
                               fun paramCase : world -> <S:scheme> -> <E:exp#> -> <ofs E S> =
			            fn W <S> [<x#>] x => (case (W x) 
				                         of (<S>, <D>) => <D>)
                          in
				paramCase W <S> x
                          end

       | W <E> <forall T> => (case {<t:tp#>} calcOfs W <E> <T t>
                               of {<t:tp#>} <D t> => <ofs_polyintro D>)

       | W <E> <! T> => let
			   val <D> = calcOf W <E> <T>
                        in
                           <!of! D>
                        end


and calcOf : world -> <E:exp> -> <T:tp> -> <of E T> =
      fn W [<x#>]<x> <T> => 
			  let 
                                fun paramCase : world -> <T:tp> -> <E:exp#> -> <of E T> =
			            fn W <T> [<x#>] x => (case (W x) 
				                         of (<! T>, <!of! D>) => <D>)
                          in
				paramCase W <T> x
                          end

       | W <z> <nat> => <tp_z>
       | W <s E> <nat> =>
                let 
                  val <D1> = calcOf W <E> <nat>
                in
		  <tp_s D1>
                end

       | W <case E1 E2 E3> <T> =>
                let 
                  val <D1> = calcOf W <E1> <nat>
                  val <D2> = calcOf W <E2> <T>
                  val <D3> = case ({<x>}{<y: of x nat>} calcOf ((extend W <nat>) \x \y) <E3 x> <T>)
                               of {<x>}{<y>} <D3 x y> => <D3>
                in
		  <tp_case D1 D2 D3>
                end

       | W <pair E1 E2> <cross T1 T2> =>
                let 
                  val <D1> = calcOf W <E1> <T1>
                  val <D2> = calcOf W <E2> <T2>
                in
		  <tp_pair D1 D2>
                end

       | W <fst E> <T> =>
                let 
		  val <cross T T2> = inferTypeW W <E>
                  val <D> = calcOf W <E> <cross T T2>
                in
		  <tp_fst D>
                end

       | W <snd E> <T> =>
                let 
		  val <cross T1 T> = inferTypeW W <E>
                  val <D> = calcOf W <E> <cross T1 T>
                in
		  <tp_snd D>
                end


       | W <lam E> <arrow T1 T2> =>  
               (case ({<x>}{<y: of x T1>} calcOf ((extend W <T1>) \x \y) <E x> <T2>)
                         of {<x>}{<y>} <D3 x y> => <tp_lam D3>)

       | W <app E1 E2> <T> =>
                let
		  val <Targ> = inferTypeW W <E2>  
		  val <S> = inferSchemeW W <E1>
                  val <D1> = calcOfs W <E1> <S>  (* D1 : ofs E1 S *)
                  val <D1'> = reduceScheme <D1> <Targ> <T> (* D1' : ofs E1 (! (arrow Targ T)) *)
                  val <D2> = calcOf W <E2> <Targ>
                in
		  <tp_app (apply_scheme D1') D2>
		end

       | W <letv E1 E2> <T2> =>
                let 
		  val <S> = inferSchemeW W <E1>
                  val <D1> = calcOfs W <E1> <S>
                  val <D2> = case ({<x>}{<y: ofs x S>} calcOf ((extendScheme W <S>) \x \y) <E2 x> <T2>)
									      of ({<x>}{<y>} <D2' x y>) => <D2'>
                in
		  <tp_letv D1 D2>
                end

       | W <letn E1 E2> <T2> =>
                let 
		  val <S> = inferSchemeW W <E1>
                  val <D1> = calcOfs W <E1> <S>
                  val <D2> = calcOf W <E2 E1> <T2>
                in
		  <tp_letn D1 D2>
                end

       | W <fix E> <T> =>  
		 (case ({<x>}{<y: of x T>} calcOf ((extend W <T>) \x \y) <E x> <T>)
                    of {<x>}{<y>} <D x y> => <tp_fix D>);



fun infer : _ -> <E:exp> -> <T:tp> * <of E T> =
      fn W <E> =>
            let
		val <T> = inferTypeW W <E>
            in
	        (<T>, calcOf W <E> <T>)
	    end;

fun infer_s : _ -> <E:exp> -> <S:scheme> * <ofs E S> =
      fn W <E> =>
            let
		val <S> = inferSchemeW W <E>
            in
	        (<S>, calcOfs W <E> <S>)
	    end;




(* Put it all together... *)

fun test_of : <E:exp> -> <V:exp> * <eval E V> * <T:tp> * <of E T> * <of V T> =
   fn <E> => 
            let
	        val (<V>, <Deval>) = executeEval <E>
                val <Dval> = vs <Deval>
                val (<T>, <DofE>) = infer (fn .) <E>
                val <DofV> = tp_pres <Deval> <DofE>
            in
                (<V>,<Deval>,<T>,<DofE>,<DofV>)
            end;

fun test_ofs : <E:exp> -> <V:exp> * <eval E V> * <S:scheme> * <ofs E S> * <ofs V S> =
   fn <E> => 
            let
	        val (<V>, <Deval>) = executeEval <E>
                val <Dval> = vs <Deval>
                val (<T>, <DofsE>) = infer_s (fn .) <E>
                val <DofsV> = tps_pres <Deval> <DofsE>
            in
                (<V>,<Deval>,<T>,<DofsE>,<DofsV>)
            end;

val example = test_of <case z (s z) ([x:exp] z)> ;
val example2 = test_of <lam [x] pair x (s x)> ;

val example3  = test_ofs <lam [x] x> ;
val example4  = test_of <letv (lam [x] x) ([u:exp] pair (app u z) (app u (pair z z)))> ;
