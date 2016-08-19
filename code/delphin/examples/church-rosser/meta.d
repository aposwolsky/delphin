(* Church Rosser Theorems 
 * by Adam Poswolsky (from Twelf code by Frank Pfenning) 
 *)

sig use "lam.elf";
sig use "ord-red.elf";
sig use "par-red.elf";


(* The Church-Rosser theorem for parallel reduction *)
params = <term>, <X# => X>;


fun identity : (<x:term#> -> <x => x>) -> <M:term> -> <M => M>
    = fn W <lam M1> => 
           (case {<x:term>} {<eqx: x => x>} identity (W with <x> => <eqx>) <M1 x> 
             of {<x>}{<eqx>}<R1 x eqx> => <lm R1>)

       | W <app M1 M2> =>
             let
               val <R1> = identity W <M1>
               val <R2> = identity W <M2>
             in
               <ap R1 R2>
             end

       | W <x:term#> => W <x>;


(* Parallel multi-step reduction is transitive *)

fun append : <M =>* M'> -> <M' =>* M''> -> <M =>* M''>
  = fn <id> <S*> => <S*>
     | <R1 | R2*> <S*> =>
            let
              val <S2*'> = append <R2*> <S*>
            in
              <R1 | S2*'>
            end;


fun subst : <{x:term} x => x -> M x => M' x> -> <{x:term}{y:term} x => y -> M x => M' y>
   = fn <[x:term] [idx: x => x] idx> => <[x][y][r] r>
      | <[x:term] [idx: x => x] beta (R1 x idx) (R2 x idx)> =>
	    (case {<z>}{<idz>} subst <[x][idx : x => x] R1 x idx z idz>
               of {<z>}{<idz>} <[x][y][r] R1' x y r z idz> =>
                                       let
					   val <R2'> = subst <R2>
                                       in
                                           <[x][y][r : x => y] beta (R1' x y r) (R2' x y r)>
                                       end)
      | <[x:term] [idx: x => x] ap (R1 x idx) (R2 x idx)> =>
              let
		val <R1'> = subst <R1>
                val <R2'> = subst <R2>
              in
		<[x][y][r] ap (R1' x y r) (R2' x y r)>
	      end

      | <[x:term] [idx: x => x] lm (R1 x idx)> =>
	    (case {<z>}{<idz>} subst <[x][idx : x => x] R1 x idx z idz>
               of {<z>}{<idz>} <[x][y][r] R1' x y r z idz> => <[x][y][r] lm (R1' x y r)>)

      | <[x][idx] R> => <[x][y][r] R>;


fun dia :  <M => M'>  ->  <M => M''>  ->  <N:_> * <M' => N>  * <M'' => N>
      = fn <beta R1' R2'> <beta R1'' R2''> =>
           let
		val {<x>}{<idx>}(<_>, <S1' x idx>, <S1'' x idx>) =  {<x:term>}{<idx: x => x>} dia <R1' x idx> <R1'' x idx>
		val (<_>, <S2'>, <S2''>) = dia <R2'> <R2''>
		val <S1'G> = subst <S1'>
		val <S1''G> = subst <S1''>
	   in
		(<_>, <S1'G _ _ S2'>, <S1''G _ _ S2''>)
	   end

         | <beta R1' R2'> <ap (lm R1'') R2''> =>
           let
		val {<x>}{<idx>}(<_>, <S1' x idx>, <S1'' x idx>) =  {<x:term>}{<idx: x => x>} dia <R1' x idx> <R1'' x idx>
		val (<_>, <S2'>, <S2''>) = dia <R2'> <R2''>
		val <S1'G> = subst <S1'>
	   in
		(<_>, <S1'G _ _ S2'>, <beta S1'' S2''>)
	   end


	 | <ap (lm R1') R2'> <beta R1'' R2''> =>
           let
		val {<x>}{<idx>}(<_>, <S1' x idx>, <S1'' x idx>) =  {<x:term>}{<idx: x => x>} dia <R1' x idx> <R1'' x idx>
		val (<_>, <S2'>, <S2''>) = dia <R2'> <R2''>
		val <S1''G> = subst <S1''>
	   in
		(<_>, <beta S1' S2'>, <S1''G _ _ S2''>)
	   end

	 | <ap R1' R2'> <ap R1'' R2''> =>
           let
	 	val (<_>, <S1'>, <S1''>) = dia <R1'> <R1''>
	 	val (<_>, <S2'>, <S2''>) = dia <R2'> <R2''>
	   in
		(<_>, <ap S1' S2'>, <ap S1'' S2''>)
	   end


	 | <lm R1'> <lm R1''> =>
	   let
		val {<x>}{<idx>}(<_>, <S1' x idx>, <S1'' x idx>) =  {<x:term>}{<idx: x => x>} dia <R1' x idx> <R1'' x idx>
	   in
		(<_>, <lm S1'>, <lm S1''>)
	   end

	(* And finally for the parameter case.. all parameters are of the form  M1 => M1 *)
	 | <R1 : M1 => M1> <R2 : M1 => M1> => (<M1>, <R1>, <R2>);



(* The strip lemma for parallel reduction *)
fun strip : <M =>* M''> -> <M => M'> -> <N:_> * <M' =>* N> * <M'' => N>
        = fn <id> <R'> => (<_>, <id>, <R'>)
           | <R1'' | R2*''> <R'> =>
                let
		   val (<_>, <S1'>, <S1''>) = dia <R'> <R1''>
                   val (<_>, <S2*'>, <S''>) = strip <R2*''> <S1''>
                in
                   (<_>, <S1' | S2*'>, <S''>)
                end;

fun conf : <M =>* M'> -> <M =>* M''> -> <N:_> * <M' =>* N> * <M'' =>* N>
        = fn <id> <R*''> => (<_>, <R*''>, <id>)
           | <R1' | R2*'> <R*''> =>
		let
		   val (<_>, <S1*'>, <S1''>) = strip <R*''> <R1'>
                   val (<_>, <S*'>, <S2*''>) = conf <R2*'> <S1*'>
                in
		   (<_>, <S*'>, <S1'' | S2*''>)
		end;

fun cr : <M <=> M'> -> <N:_> * <M =>* N> * <M' =>* N>
        = fn <reduce R*> => (<_>, <R*>, <id>)
           | <expand R*> => (<_>, <id>, <R*>)
           | <C1 || C2> =>
    		let
		   val (<_>, <S1*>, <R1*>) = cr <C1>
		   val (<_>, <R2*>, <S2*>) = cr <C2>
 		   val (<_>, <T1*>, <T2*>) = conf <R1*> <R2*>
		   val <S*> = append <S1*> <T1*>
		   val <S*'> = append <S2*> <T2*>
		in
		   (<_>, <S*>, <S*'>)
		end;


(* Lemmas concerning ordinary multi-step reduction *)
fun appd : <M -->* M'> -> <M' -->* M''> -> <M -->* M''>
    = fn <id1> <S*> => <S*>
       | <step1 R1 R2*> <S*> =>
            let
		val <S2*'> = appd <R2*> <S*>
            in
		<step1 R1 S2*'>
           end;
(* Multi-step reduction is a congruence *)
fun lm1 : <{x:term} M x -->* M' x> -> <(lam M) -->* (lam M')>
     = fn <[x:term] id1> => <id1>
        | <[x:term] step1 (R1 x) (R2* x)> =>
                let
			val <S2*> = lm1 <R2*>
		in
			<step1 (lm1 R1) S2*>
		end;

fun apl1 : < M1 -->* M1' > -> < (app M1 M2) -->* (app M1' M2) > 
        = fn <id1> => <id1>
           | <step1 R1 R2*> =>
                let
			val <S2*> = apl1 <R2*>
                in
			<step1 (apl1 R1) S2*>
		end;

fun apr1 : < M2 -->* M2' > -> < (app M1 M2) -->* (app M1 M2') > 
        = fn <id1> => <id1>
           | <step1 R1 R2*> =>
                let
			val <S2*> = apr1 <R2*>
                in
			<step1 (apr1 R1) S2*>
		end;


(* Equivalence of ordinary and parallel reduction *)
fun eq1 : <M => N> -> <M -->* N>
       = fn <beta R1 R2> =>
            let
		val {<x:term>}{<eqx : x => x>} <S1* x> = {<x:term>}{<eqx : x => x>}  eq1 <R1 x eqx>
		val <S1*'> = lm1 <S1*>
		val <S1*''> = apl1 <S1*'>
		val <S2*> = eq1 <R2>
		val <S2*'> = apr1 <S2*>
		val <S*'> = appd <S2*'> <step1 beta1 id1>
		val <S*> = appd <S1*''> <S*'>
	    in
		<S*>
	    end

          | <ap R1 R2> =>
            let
		val <S1*> = eq1 <R1>
		val <S*'> = apl1 <S1*>
		val <S2*> = eq1 <R2>
		val <S*''> = apr1 <S2*>
		val <S*> = appd <S*'> <S*''>
	    in
		<S*>
	    end

          | <lm R1> =>
            let
		val {<x:term>}{<eqx : x => x>} <S1* x> = {<x:term>}{<eqx : x => x>} eq1 <R1 x eqx>
		val <S*> = lm1 <S1*>
	    in
		<S*>
	    end

	  | <R : M1 => M1> => <id1> ;


fun eq2 : (<x:term#> -> <x => x>) -> <M --> N> -> <M => N>
     = fn W <beta1> =>
	  let
		val {<x:term>}{<eqx: x => x>} <I1 x eqx> = {<x:term>}{<eqx: x => x>} identity (W with <x> => <eqx>) <M1 x>
		val <I2> = identity W <M2>
	  in
		<beta I1 I2>
	  end

        | W <lm1 R1> =>
	  let
		val {<x:term>}{<eqx: x => x>} <S1 x eqx> = {<x:term>}{<eqx: x => x>} eq2 (W with <x> => <eqx>) <R1 x>
	  in
		<lm S1>
	  end

        | W <apl1 R1> =>
	  let
		val <S1> = eq2 W <R1>
		val <I2> = identity W <M2>
	  in
		<ap S1 I2>
	  end

        | W <apr1 R2> =>
	  let
		val <S2> = eq2 W <R2>
		val <I1> = identity W <M1>
	  in
		<ap I1 S2>
	  end;

(* We will now only work with closed terms! *)
params = . ;  

fun eq3 : <M -->* N> -> <M =>* N>
     = fn <id1> => <id>
        | <step1 R1 R2*> =>
           let
		val <S1> = eq2 (fn .) <R1>
                val <S2*> = eq3 <R2*>
           in
	        <S1 | S2*>
	   end;

fun eq4 : <M =>* N> -> <M -->* N>
     = fn <id> => <id1>
        | <R1 | R2*> => 
           let
		val <S1*> = eq1 <R1>
                val <S2*> = eq4 <R2*>
		val <S*> = appd <S1*> <S2*>
           in
	        <S*>
	   end;

fun eq5 : <M <=> N> -> <M <-> N>
      = fn <reduce R*> =>
           let
		val <S*> = eq4 <R*>
           in
	        <red S*>
	   end

         | <expand R*> =>
           let
		val <S*> = eq4 <R*>
           in
	        <sym (red S*)>
	   end

         | <C1 || C2> => 
           let
		val <C1'> = eq5 <C1>
		val <C2'> = eq5 <C2>
           in
	        <trans C2' C1'> 
	   end;


fun sym_pconv : <M <=> N> -> <N <=> M>
        = fn <reduce R*> => <expand R*>
           | <expand R*> => <reduce R*>
           | <C1 || C2> =>
             let
		val <C1'> = sym_pconv <C1>
		val <C2'> = sym_pconv <C2>
	     in
		<C2' || C1'>
	     end;

fun eq6 : <M <-> N> -> <M <=> N> 

        = fn <refl> => <reduce id>

           | <sym C1> =>
             let
		val <C1'> = eq6 <C1>
		val <C'> = sym_pconv <C1'>
	     in
		<C'>
	     end

	   | <trans C2 C1> =>
             let
		val <C1'> = eq6 <C1>
		val <C2'> = eq6 <C2>
	     in
		<C1' || C2'>
	     end

	   | <red R*> =>
             let
		val <S*> = eq3 <R*>
	     in
		<reduce S*>
	     end;
      

(* The Church-Rosser theorem for ordinary reduction *)
fun cr_ord : <M <-> M'> -> <N:_> * <M -->* N> * <M' -->* N>
        = fn <C> => 
	     let
		val <C'> = eq6 <C>
		val (<_>, <R*>, <R*'>) = cr <C'>
		val <S*> = eq4 <R*>
		val <S*'> = eq4 <R*'>
	     in
		(<_>, <S*>, <S*'>)
	     end;

(* Examples *)
val testdia = dia <(beta ([x:term] [R4:x => x] ap R4 R4)
                    (ap (lm ([x:term] [R5:x => x] R5)) (lm ([x:term] [R6:x => x] R6))))>
		  <(ap (lm ([x:term] [R7:x => x] ap R7 R7))
                    (beta ([x:term] [R8:x => x] R8) (lm ([x:term] [R9:x => x] R9))))>;

val testa =
     <((beta ([x:term] [R:x => x] ap R R)
            (beta ([x:term] [R:x => x] R) (lm ([x:term] [R:x => x] R))))
       | beta ([x] [R] R) (lm [x] [R] R)
       | id)>;

