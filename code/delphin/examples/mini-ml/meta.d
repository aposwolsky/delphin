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

fun tpscheme : <of (lam E1') T> -> <of V2 T1> -> <ofscheme T T1 T2> -> <eval (E1' V2) V> -> <of V T2> =
     fn <tp_lam Q1> <Q2> <ofscheme_arrow> <D> => tps <D> <Q1 _ Q2> 
      | <tp_polyintro Q1> <Q2> <ofscheme_poly Targ P> <D> => 
               (* T == forall [t] (T t)
 		* Q1 : {t} of (lam E1') (T t)
		* Q2 : of V2 T1
		* P : ofscheme (T Targ) T1 T2
                * D : eval (E1' V2) V
                *)
               tpscheme <Q1 Targ> <Q2> <P> <D>
                                
       

and tps : <eval E V> -> <of E T> -> <of V T>
        = fn <ev_z> <tp_z>         => <tp_z>
           | <ev_s D1> <tp_s P1>   => <tp_s> @ (tps <D1> <P1>)
           | <ev_case_z D1 D2> <tp_case P1 P2 P3> => tps <D2> <P2> 
           | <ev_case_s D1 D3> <tp_case P1 P2 P3> => 
	               let
	                 val <tp_s Q1'> = tps <D1> <P1>                     
		       in
                         tps <D3> <P3 _ Q1'>
                       end
	   | <ev_pair D1 D2> <tp_pair P1 P2> => 
                       let
			  val <Q1> = tps <D1> <P1>
                          val <Q2> = tps <D2> <P2>
                       in
                          <tp_pair Q1 Q2>
		       end

           | <ev_fst D1> <tp_fst P1> =>
                       let
                          val <tp_pair Q1 Q2> = tps <D1> <P1>
                       in
			  <Q1>
                       end
           | <ev_snd D1> <tp_snd P1> =>
                       let
                          val <tp_pair Q1 Q2> = tps <D1> <P1>
                       in
			  <Q1>
                       end

           | <ev_lam> <tp_lam P> => <tp_lam P>

	   | <ev_app D1 D2 D3> <tp_app P1 P2 P3>  =>
                       (* D1 : eval E1 (lam E1')
                        * D2 : eval E2 V2
                        * D3 : eval (E1' V2) V
                        *
                        * P1 : of E1 T
                        * P2 : of E2 T1
                        * P3 : ofscheme T T1 T2
                        *)
                       let
                          val <Q1> = tps <D1> <P1> (* Q1 : of (lam E1') T *)
                          val <Q2> = tps <D2> <P2> (* Q2 : of V2 T1       *)
                        in
                          tpscheme <Q1> <Q2> <P3> <D3>
                        end



           | <ev_letv D1 D2> <tp_letv P1 P2> =>
                       let
                          val <Q1> = tps <D1> <P1>
                       in
                          tps <D2> <P2 _ Q1>
                       end

           | <ev_letn D2> <tp_letn P1 P2> => tps <D2> <P2>

           | <ev_fix D1> <tp_fix P1> => tps <D1> <P1 _ (tp_fix P1)>

	   | <D> <tp_polyintro P> => (case {<t:tp#>} tps <D> <P t>
                                        of {<t:tp#>} <P' t> => <tp_polyintro P'>);



type world = <E:exp#> -> <T:tp> * <of E T>;

fun inferTypeW : world -> <exp> -> <tp> 
 = fn W <E> => let
                  fun convW : world -> expEnv
                             = fn W1 [<e>] e => (case (W1 e)
                                                of (<T>, R) => <T>)
                 
                  val G99 = {<t>} checkType (convW W) (fn [<t':tp#>]t' => <t'>) <E> <t> (fn G' => G')

                  fun getType : ({<t:tp#>} tpEnv) -> <tp>
                        = fn G  => case {<t>} normalize (G \t) <t>
                                  of {<t>} <T> => <T> 
				   | {<t>} <T t> => <forall T> 
             in
               getType G99
             end;



fun extend : world -> <T':tp> -> {<x:exp#>}{<y:of x T'>}world
           = fn W => fn <T'> => fn {<x>}{<y>} (x => (<T'>, <y>))
                               | [<x'>]{<x>}{<y>} (x' => 
                                                       (let
                                                         val result = W x'
                                                       in
                                                         {<x>}{<y>} result
                                                       end) \x \y);

fun getScheme' : tpEnv -> <Tscheme : tp> -> <Targ: tp> -> <Tresult : tp> -> tpEnv =
     fn G <arrow T1 T2> <Targ> <Tresult> => 
                  let
		     val G2 = unifyTypes G <T1> <Targ>
		     val G3 = unifyTypes G2 <T2> <Tresult>
                  in
                     G3
                  end

      | G <forall Tfun> <Targ> <Tresult> => 
                  let
                     val Gextended = {<t:tp>} getScheme' ((extendG G)\t) <Tfun t> <Targ> <Tresult>
		  in
		     shrinkG Gextended
                  end;

fun getScheme : <Tscheme : tp> -> <Targ: tp> -> <Tresult : tp> -> <ofscheme Tscheme Targ Tresult> =
      fn <arrow T1 T2> <T1> <T2> => <ofscheme_arrow>
       | <forall Tfun> <Targ> <Tresult> => 
                let
		     val Gextended = {<t:tp>} getScheme' (fn [<T':tp#>]T' => <T'>) <Tfun t> <Targ> <Tresult>

	             fun getType : ({<t:tp#>} tpEnv) -> <tp>
                        = fn G  => case {<t>} normalize (G \t) <t>
                                    of {<t>} <T> => <T> 
                                     | {<t>} <T t> => <forall T> 
                     
                     val <T'> = getType Gextended

		     val <P> = getScheme <Tfun T'> <Targ> <Tresult>
                in
		     <ofscheme_poly T' P>
                end;


fun calcOf : world -> <E:exp> -> <T:tp> -> <of E T> =
      fn W [<x#>]<x> <T> => 
			  let 
                                fun paramCase : world -> <T:tp> -> <E:exp#> -> <of E T> =
			            fn W <T> [<x#>] x => (case (W x) 
				                         of (<T>, <D>) => <D>)
                          in
				paramCase W <T> x
                          end

       | W <E> <forall T> => (case {<t:tp#>} calcOf W <E> <T t>
                               of {<t:tp#>} <D t> => <tp_polyintro D>)

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
                  val <Tscheme> = inferTypeW W <E1>
		  val <D1> = calcOf W <E1> <Tscheme>
		  val <Targ> = inferTypeW W <E2>
                  val <D2> = calcOf W <E2> <Targ>
		  val <P> = getScheme <Tscheme> <Targ> <T>
                in
		  <tp_app D1 D2 P>
		end

       | W <letv E1 E2> <T2> =>
                let 
		  val <T1> = inferTypeW W <E1>
                  val <D1> = calcOf W <E1> <T1>
                  val <D2> = case ({<x>}{<y: of x T1>} calcOf ((extend W <T1>) \x \y) <E2 x> <T2>)
									      of ({<x>}{<y>} <D2' x y>) => <D2'>
                in
		  <tp_letv D1 D2>
                end

       | W <letn E1 E2> <T2> =>
                let 
		  val <T1> = inferTypeW W <E1>
                  val <D1> = calcOf W <E1> <T1>
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




(* Put it all together... *)

fun test : <E:exp> -> <V:exp> * <eval E V> * <T:tp> * <of E T> * <of V T> =
   fn <E> => 
            let
	        val (<V>, <Deval>) = executeEval <E>
                val <Dval> = vs <Deval>
                val (<T>, <DofE>) = infer (fn .) <E>
                val <DofV> = tps <Deval> <DofE>
            in
                (<V>,<Deval>,<T>,<DofE>,<DofV>)
            end;

val example = test <case z (s z) ([x:exp] z)> ;
val example2 = test <lam [x] pair x (s x)> ;

val example3  = test <lam [x] x> ;
val example4  = test <letv (lam [x] x) ([u:exp] pair (app u z) (app u (pair z z)))> ;
