(* The HOL Nuprl connection, written in Delphin *)
(* Authors: Carsten Schuermann, Adam Poswolsky *) 

(* use "hol/hol.d" ; (* sig use "hol/hol.elf"; *)
 sig use "hol/axioms.elf";
*)
sig use "hol.elf";
sig use "nuprl/nuprl.elf";
sig use "nuprl/classical.elf";
sig use "nuprl/nuprl-lemmas.elf";
sig use "nuprl/examples.elf"; 
sig use "trans.elf";
sig use "nuprl-axioms.elf"; 


sig <empty : type>;
sig <equal : n-tm -> n-tm -> type>
    <eq_base : equal T T>;


type world1 = (<H':(tm B)#> -> <M:n-tm> * <transtm H' M>);;
type world2 = (<H':tm B> -> <M:n-tm> -> <u:(transtm H' M)#> -> <T:n-tm> * <transtp B T> * <!- M !*! T>);
type world3 = (<U: |- H #> -> <T:n-tm> * <transsen H T> * <M:n-tm> * < !- M !*! T>);
type world4 = ( <H:(tm A)#> -> <transtm H T> -> <transtm H T'> -> <equal T T'>);


params = <n-tm>, <tm B>, <transtm H# M>, <|- H>, < !- M !*! T > ;

fun uniqueType : <transtp B T1> -> <transtp B T2> -> <equal T1 T2>
        = fn <transtpo> <transtpo> => <eq_base>
           | <transtparr D1 D2> <transtparr D1' D2'>
                   => let
                        val <eq1> = uniqueType <D1> <D1'>
                        val <eq2> = uniqueType <D2> <D2'>

                        fun combineEq : <equal T1 T1'> -> <equal T2 T2'> -> <equal (pi T1 [x] T2) (pi T1' [x] T2')>
                                      = fn <eq_base> <eq_base> => <eq_base>
                      in
                        combineEq <eq1> <eq2>
                      end;


fun uniqueApp : <equal T1 T1'> -> <equal T2 T2'> -> <equal (app T1 T2) (app T1' T2')>
              = fn <eq_base> <eq_base> => <eq_base> ;
fun uniqueLam : <{x} equal (T1 x) (T1' x)> -> <equal (lam T1) (lam T1')>
              = fn <[x] eq_base> => <eq_base> ;
fun uniqueEqP : <equal T1 T1'> -> <equal (=p= T1) (=p= T1')>
              = fn <eq_base> => <eq_base> ;
fun uniquev : <equal T1 T2> -> <equal (v T1) (v T2)>
              = fn <eq_base> => <eq_base> ;
fun unique^ : <equal T1 T2> -> <equal (^ T1) (^ T2)>
              = fn <eq_base> => <eq_base> ;
fun uniquePi  : <equal A A'> -> <{x} equal (T x) (T' x)> -> <equal (pi A [x] T x) (pi A' [x] T' x)>
              = fn <eq_base> <[x] eq_base> => <eq_base> ;
fun uniqueSigma  : <equal A A'> -> <{x} equal (T x) (T' x)> -> <equal (sigma A [x] T x) (sigma A' [x] T' x)>
                 = fn <eq_base> <[x] eq_base> => <eq_base> ;
fun uniqueSet : <equal A A'> -> <{x} equal (T x) (T' x)> -> <equal (set A [x] T x) (set A' [x] T' x)>
              = fn <eq_base> <[x] eq_base> => <eq_base> ;
fun uniqueDecide : <equal T T'> -> <{x} equal (L x) (L' x)> -> <{x} equal (R x) (R' x)> 
                      -> <equal (decide T L R) (decide T' L' R')>
                 = fn <eq_base> <[x] eq_base> <[x] eq_base> => <eq_base> ;
fun uniqueArb : <equal A A'> -> <equal (arb A) (arb A')>
              = fn <eq_base> => <eq_base> ;

fun uniqueTerm : world4 -> <transtm H T1> -> <transtm H T2> -> <equal T1 T2>
      = fn W4 => fn <u1#> <u2#> => W4 <X> <u1> <u2>
                  | < trans=> > < trans=> > => <eq_base> 
                  | < trans== TTP> < trans== TTP'> => uniqueEqP (uniqueType <TTP> <TTP'>) 
                  | < trans@ TTM1 TTM2> < trans@ TTM1' TTM2'> =>
                     uniqueApp (uniqueTerm W4 <TTM1> <TTM1'>) (uniqueTerm W4 <TTM2> <TTM2'>)
                  | < trans\ TTM> < trans\ TTM'> =>
                    (case {<x>}{<y>}{<u:transtm x y>} uniqueTerm (W4 with <x> <u> <u> => <eq_base>) <TTM x y u> <TTM' x y u>
                       of {<x>}{<y>}{<u:transtm x y>} <eq1 y> => uniqueLam <eq1>) 
                  | <tc-true> <tc-true> => <eq_base>
                  | <tc-false> <tc-false> => <eq_base>
                  | <tc-neg> <tc-neg> => <eq_base>
                  | <tc-/|\> <tc-/|\> => <eq_base>
                  | <tc-\|/> <tc-\|/> => <eq_base>
                  | <tc-all| TTP> <tc-all| TTP'> =>  
                    let
                       val {<p>} {<x>} <E1 p x> = {<p>} {<x>} unique^ (uniqueApp <eq_base> <eq_base>) 
                       val {<p>}       <E2 p> = {<p>} uniquev (uniquePi (uniqueType <TTP> <TTP'>) <[x] E1 p x>)
                    in uniqueLam <[p] E2 p>
                    end
                  | <tc-ex| TTP> <tc-ex| TTP'> =>  
                    let
                       val {<p>} {<x>} <E1 p x> = {<p>} {<x>} unique^ (uniqueApp <eq_base> <eq_base>) 
                       val {<p>}       <E2 p> = {<p>} uniquev (uniqueSigma (uniqueType <TTP> <TTP'>) <[x] E1 p x>)
                    in uniqueLam <[p] E2 p>
                    end
                  | <tc-the| TTP> <tc-the| TTP'> =>  
                    let
                       val <E> = uniqueType <TTP> <TTP'>
                       val {<p>} {<x>} <E1 p x> = {<p>} {<x>} unique^ (uniqueApp <eq_base> <eq_base>) 
                       val {<p>} {<x>} <E2 p x> = {<p>} {<x>} <eq_base>
                       val {<p>} {<x>} <E3 p x> = {<p>} {<x>} uniqueArb <E>
                       val {<p>}       <E4 p> = {<p>} uniqueDecide (uniqueApp <eq_base> 
                                                        (uniqueSet <E> <[x] E1 p x>)) <[x] E2 p x> <[x] E3 p x>
		    in uniqueLam <[p] E4 p>
		    end
; 
		       
fun uniqueSen : world4 -> <transsen H T1> -> <transsen H T2> -> <equal T1 T2>
    = fn W4 => fn <t-base TTM> <t-base TTM'> => 
	           let
		     val <eq1> = uniqueTerm W4 <TTM> <TTM'>

                     fun combineEq : <equal T1 T1'> -> <equal (^ T1) (^ T1')>
                                   = fn <eq_base> => <eq_base>
		   in
		     combineEq <eq1>
  		   end
	         | <transboolcases> <transboolcases> => <eq_base>
(*	         | <transselect> <transselect> => <eq_base> *)
	         | <transantisym> <transantisym> => <eq_base> ;
;

fun equalProp : <equal T1 T2> -> <!- N !*! T1> -> <!- N !*! T2>
            = fn <eq_base> <D> => <D>;

fun equiv : <transtp A T'>
           -> (<T:n-tm> * <transtp A T> * <!- N !*! T>)
           -> <!- N !*! T'>
    = fn <TTP1> (<T>, <TTP2>, <D>) =>
             let
               val <EQ : equal T T'> = uniqueType <TTP2> <TTP1>
             in
               equalProp <EQ> <D>
             end;

(* Lemma 1 *)
fun lemma0 : <A : tp> -> <N : n-tm> * <transtp A N>  * <!- N !*! uni 1>
  	    = fn <o> => (<boolean> , <transtpo>, <boolean-form>) 
	       | <A arr B> => (case (lemma0 <A>, lemma0 <B>)
	                         of ((<N1>, <S1>, <K1>), (<N2>, <S2>, <K2>)) 
				      => (<pi N1 [x] N2>, <transtparr S1 S2>,
					  <fun-form K1 [_][_] K2>));

(* Lemma 1 *)
fun lemma1 : <A : tp> -> <N : n-tm> * <transtp A N>  
  	    = fn <o> => (<boolean> , <transtpo>) 
	       | <A arr B> => (case (lemma1 <A>, lemma1 <B>)
	                         of ((<N1>, <S1>), (<N2>, <S2>)) 
				      => (<pi N1 [x] N2>, <transtparr S1 S2>));


(* Lemma 2 *)

fun lemma2 : world1 -> <H:tm C> -> <M:n-tm> * <transtm H M>
            = fn W < => > => (< =p=> >, < trans=> >)
  	       | W <true> => (<tt>, <tc-true>)
	       | W <false> => (<ff>, <tc-false>)
	       | W < == : tm (A arr A arr o) > 
	           => (case (lemma1 <A>)
		         of (<N>, <TTP>) => (< =p= N>, < trans== TTP >))
	       | W < H @ G > 
	           => (case (lemma2 W <H>)
		         of (<N1>, <TTM1>) 
			 => (case (lemma2 W <G>)
			       of (<N2>, <TTM2>) 
			       => (< app N1 N2 >, < trans@ TTM1 TTM2 >)))
	       | W < \ H : tm (A arr B) > 
	           => (case (lemma1 <A>, lemma1 <B>) 
                         of ((<N>, <TTP>), (<_>, <TTP2>)) 
	                 => (case ({<x>}{<y>}{<u:transtm x y>} lemma2
				   (W with (<x> => (<y>, <u>))) <H x>)
	       	               of ({<x>}{<y>}{<u>} (<M y>, <TTM x y u>))
			       => (<lam M>,  < trans\ TTM>)))
               | W <neg> => (<lam [x] if x ff tt>, <tc-neg>)
               | W < /|\ > => (<lam [x] lam [y] if x y ff>, < tc-/|\>)
 	       | W < \|/ > => (<lam [x] lam [y] if x tt y>, < tc-\|/>)
	       | W < all| : tm ((A arr o) arr o) > 
	           => (case (lemma1 <A>)
	       	                of (<T>, <TTP>) => (<lam [p] v (pi T [x] ^ (app p x)) >,
						    <tc-all| TTP>))
	       | W < ex| : tm ((A arr o) arr o) > 
	           => (case (lemma1 <A>)
	       	                of (<T>, <TTP>) => (< lam [p] v (sigma T [x] ^ (app p x)) >,
						    <tc-ex| TTP>))
	       | W < the| : tm ((A arr o) arr A) > 
	           => (case (lemma1 <A>)
	       	                of (<T>, <TTP>) => (< lam [p] decide (app inhabited 
	                               (set T ([x] ^ app p x))) ([x] x) ([x] arb T)>,
						    <tc-the| TTP>))
               | W <x#> => (W <x>); 

fun lemma2' : world1 -> <tm C> -> <n-tm> 
             = fn W <M> => let val (<R>, _) = lemma2 W <M> in <R> end;




(* Lemma 3 *)

fun lemma3 : <transtp A T> -> <X1:n-tm> * <!- X1 !*! ((T !*! (uni 1)) n/\ (inh T))>
           = fn <transtpo> 
	        => <_>, < (sig-intro 
		       (ax-intro 
            	 	 (sum-form (unit-form :!- unit !*! (uni 1)) unit-form)) 
	                 (sig-intro (sum-inl unit-intro (unit-form:!- unit !*! (uni 1)))
		            unit-intro))>       
	      | <transtparr TTP1 TTP2> 
 	        => (case (lemma3 <TTP1>, lemma3 <TTP2>) 
		      of ((<_>, <ND1>), (<_>, <ND2>)) 
		      => <_>, <sig-intro 
	                   (ax-intro 
            		     (fun-form 
	            	       (ax-elim (sig-fst ND1)) [x1] [x2] 
		                   ax-elim (sig-fst ND2))) 
              	             (sig-intro (fun-intro (ax-elim (sig-fst ND1)) [y1] [y2] 
	            	       (sig-fst (sig-snd ND2))) unit-intro)>);


(* Lemma 4 *)


fun lemma4i : world1 -> world2 -> <transtm (H:tm A) N> -> <T:n-tm > -> <transtp A T> -> <!- N !*! T> 
	   = fn W1 W2 <TTM> <T> <TTP:transtp A T> =>
	     let val (<T'>, <TTP':transtp A T'>, <ND'>) = lemma4 W1 W2 <TTM>
	     	 val <Eq: equal T' T> = uniqueType <TTP'> <TTP>
		 val <ND> = equalProp <Eq> <ND'>
	     in 
	       <ND>
             end
 
and lemma4 : world1 -> world2 
             -> <transtm (H:tm A) N> -> <T:n-tm> * <transtp A T> * <!- N !*! T> 
	   = fn W1 W2 <u#> => W2 <H> <N> <u>
              | W1 W2 < trans=> > 
	        => <_>, (<transtparr transtpo (transtparr transtpo transtpo)>, 
	            <fun-intro (sum-form (unit-form : !- unit !*! uni 1) 
		  	       (unit-form : !- unit !*! uni 1)) [x1] [u1] 
	   	     fun-intro (sum-form (unit-form : !- unit !*! uni 1) 
			       (unit-form: !- unit !*! uni 1)) [x2] [u2] 
		     boolean-if boolean-form u1 u2 boolean-tt>) 

 
              | W1 W2 < trans== TTP >
	        => let
		     val (<_>, <ND>) = lemma3 <TTP>
		   in
		     (<_>, <transtparr TTP (transtparr TTP transtpo)>, 
			    <fun-intro (ax-elim (n/\-fst ND)) [x1] [u1] 
			     fun-intro (ax-elim (n/\-fst ND)) [x2] [u2]
			       sum-decide ([x3][u3] boolean-form) 
			       (fun-elim inh-intro (equality-form u2 u1 (ax-elim (n/\-fst ND)))) 
				  ([x4][u4] boolean-tt) ([x5][u5] boolean-ff)>)
		   end		     
              | W1 W2 < (trans\ TTM): transtm (\ H : tm (A arr B)) (lam M2) > 
	        => let 
                     val (<A'>, <TTPA>, <_>) = lemma0 <A>
		     val (<B'>, <TTPB>, <_>) = lemma0 <B>
		     val  (<N>, <ND1: !- N !*! ((A' !*! (uni 1)) n/\ (inh A'))>) =
	                   lemma3 <TTPA : transtp A A'>
		     val {<x:tm A>}{<y>}{<ttm>}{<u>} (<(ND2 y u) : !- (M2 y) !*! B' >)
		            = {<x : tm A>}{<y>}{<ttm:transtm x y>}{<u>} 
                                 equiv <TTPB> (lemma4 
	                                   (W1 with (<x> => (<y>, <ttm>)))
                                           (W2 with (<x> <y> <ttm> => (<A'>, <TTPA>, <u>)))
		                            <TTM x y ttm>)
		   in
		     (<pi A' [x] B'>, <transtparr TTPA TTPB>,
		      <(fun-intro (ax-elim (n/\-fst ND1))
			  ND2) : !- (lam M2) !*! (pi A' [x] B')>)
		   end


             | W1 W2 < trans@ (TTM1:transtm (H:tm (B arr A)) _) TTM2 >
                => let
		     val (<_>, <TTP1>, < ND2 >) = lemma4 W1 W2 <TTM2>
		     val (<_>, <TTP2>) = lemma1 <A>
		     val <ND1> = lemma4i W1 W2 <TTM1> <_> <transtparr TTP1 TTP2>
		   in
		     (<_>, <TTP2>, <fun-elim ND1 ND2>)
		   end
	      | W1 W2 <tc-true> => (<_>, <transtpo>, <boolean-tt>)
	      | W1 W2 <tc-false> => (<_>, <transtpo>, <boolean-ff>)
	      | W1 W2 <tc-neg> => (<_>, <transtparr transtpo transtpo>, 
	                     <fun-intro boolean-form ([x] [u] 
			      boolean-if boolean-form u boolean-ff boolean-tt)>)
	      | W1 W2 <tc-/|\> => (<_>, <transtparr transtpo (transtparr transtpo transtpo)>,
	                     <fun-intro boolean-form [x] [u] fun-intro boolean-form [y] [v] 
	  	              boolean-if boolean-form u v boolean-ff>)

	      | W1 W2 <tc-\|/> => (<_>, <transtparr transtpo (transtparr transtpo transtpo) >, 
	                     <fun-intro boolean-form [x] [u] fun-intro boolean-form [y] [v] 
		 	      boolean-if boolean-form u boolean-tt v>)

	      | W1 W2 < tc-all| TTP >
	        => let 
		     val (<_>, <ND>) = lemma3 <TTP>
		   in 
		     (<_>, <transtparr (transtparr TTP transtpo) transtpo>, 
		      <fun-intro (fun-form (ax-elim (n/\-fst ND)) [z][w] boolean-form) 
		      ([x][u] v-form 
		       (fun-form (ax-elim (n/\-fst ND)) 
			  [y] [v] ^-form _ (fun-elim u v)))>)
		   end
	      | W1 W2 < tc-ex| TTP >
	        => let 
		     val (<_>, <ND>) = lemma3 <TTP>
		   in
		     (<_>, <transtparr (transtparr TTP transtpo) transtpo>, 
		      <fun-intro (fun-form (ax-elim (n/\-fst ND)) [z] [w] boolean-form)
		      [x][u] v-form 
		      (sig-form (ax-elim (n/\-fst ND)) 
			 [y] [v] ^-form _ (fun-elim u v))>)
		   end   
	      | W1 W2 < tc-the| TTP >
	        => let 
		     val (<_>, <ND>) = lemma3 <TTP>
		   in (<_>, <transtparr (transtparr TTP transtpo) TTP>, 
		       <fun-intro (fun-form (ax-elim (n/\-fst ND)) [x0] 
				     [u0 : !- _ !*! T] boolean-form) 
		       [x] [u] sum-decide ([x2][u2] ax-elim (n/\-fst ND)) 
		       (fun-elim inh-intro 
			  (set-form (ax-elim (n/\-fst ND)) 
			   ([y][v] ^-form (app x y) (fun-elim u v))))
			  ([y] [v] set-elem ([z][w] boolean-decide ([_] [_] uni-form (+ge1 0ge0)) 
					     (fun-elim u w)
						unit-form
						void-form) v)
			  ([x4] [u4] arb-intro _ ND)>)
		   end;


(* Lemma 5 *)

fun lemma5i : world1 -> world2 -> world3 -> world4 
              -> < |- H > -> <T:n-tm> -> <transsen H T> -> <M:n-tm> * < !- M !*! T> 
	    = fn W1 W2 W3 W4 <HD> <T> <TSEN:transsen H T> =>
	      let val (<T'>, <TSEN':transsen H T'>, <M>, <ND'>) = lemma5 W1 W2 W3 W4 <HD>
	      	 val <Eq: equal T' T> = uniqueSen W4 <TSEN'> <TSEN>
	 	 val <ND> = equalProp <Eq> <ND'>
	      in 
	        (<M>, <ND>)
              end

and lemma5 : world1 -> world2 -> world3 -> world4
             -> < |- H > -> <T:n-tm> * <transsen H T> * <M:n-tm> * < !- M !*! T>
	   = fn W1 W2 W3 W4 <u#> => W3 <u>
              | W1 W2 W3 W4 <bool-cases-ax : |- all (\ [x:tm bool] x === true \/ x === false)>
                => (< ^ (app (lam ([p:n-tm] v (pi boolean ([x:n-tm] ^ app p x))))
		    (lam
		     ([x:n-tm]
		      app
		      (app (lam ([x1:n-tm] lam ([y:n-tm] if x1 tt y)))
		       (app (app (=p= boolean) x) tt))
		      (app (app (=p= boolean) x) ff))))>, 
		    <t-base (trans@ (tc-all| transtpo)
		    (trans\
		     ([x:tm bool] [y:n-tm] [x1:transtm x y]
		      trans@
		      (trans@ tc-\|/
		       (trans@ (trans@ (trans== transtpo) x1) tc-true))
		      (trans@ (trans@ (trans== transtpo) x1) tc-false))))>, 
		    <axiom>, <hol-boolcases-ax>)
              | W1 W2 W3 W4 <imp-antisym-ax>
                => (<^ (app (lam ([p:n-tm] v (pi boolean ([x:n-tm] ^ app p x))))
			(lam
			 ([x:n-tm]
			  app (lam ([p:n-tm] v (pi boolean ([x1:n-tm] ^ app p x1))))
			  (lam
			   ([x1:n-tm]
                            app (app =p=> (app (app =p=> x) x1))
			      (app (app =p=> (app (app =p=> x1) x))
				(app (app (=p= boolean) x) x1)))))))>, 
		    <t-base (trans@ (tc-all| transtpo)
			     (trans\
			      ([x:tm bool] [y:n-tm] [x1:transtm x y]
			       trans@ (tc-all| transtpo)
			       (trans\
				([x2:tm bool] [y1:n-tm] [x3:transtm x2 y1]
				 trans@
				 (trans@ trans=>
				   (trans@ (trans@ trans=> x1) x3))
				   (trans@
				    (trans@ trans=>
				      (trans@ (trans@ trans=> x3) x1))
				      (trans@ (trans@ (trans== transtpo) x1) x3)))))))>,
		    <axiom>, <hol-antisym-ax>)
               | W1 W2 W3 W4 <select-ax H> =>
                 let 
		   val (<T>, <TTP>) = lemma1 <H>
		 in
		   (<^ (app (lam ([p:n-tm] v (pi (pi T ([x:n-tm] boolean))
					      ([x:n-tm] ^ app p x))))
			(lam ([x:n-tm] app
			      (lam ([p:n-tm] v (pi T ([x1:n-tm] ^ app p x1))))
			      (lam ([x1:n-tm] app (app =p=> (app x x1))
				    (app x (app (lam ([p:n-tm]
				decide (app inhabited (set T ([x2:n-tm] ^ app p x2)))
				([x3:n-tm] x3) ([x4:n-tm] arb T))) x)))))))>, 
		    <t-base
		    (trans@ (tc-all| (transtparr TTP transtpo))
		     (trans\
		      ([x5:tm (H arr o)] [y:n-tm] [x1:transtm x5 y]
                       trans@ (tc-all| TTP)
		       (trans\
			([x6:tm H] [y1:n-tm] [x2:transtm x6 y1]
			 trans@ (trans@ trans=> (trans@ x1 x2))
			   (trans@ x1 (trans@ (tc-the| TTP) x1)))))))>, 
		    <axiom>, <hol-select-ax T>)
		 end 
               | W1 W2 W3 W4 <beta : |- (\ (H : tm _ -> tm B)) @ G === (H G)> 
	        => let 
                     val {<x>}{<y>}{<ttm:transtm x y>} (<_>, < TTM1 x y ttm >) = 
		           {<x>}{<y>}{<ttm:transtm x y>} 
			     lemma2 (W1 with (<x> => (<y>, <ttm>))) <H x>
                     val (<_>, <TTM2>) = lemma2 W1 <G:tm _>
		     val  (<N>, <TTP3>) = lemma1 <B>

		     val (<_>, <TTP2>, <ND4>) = lemma4 W1 W2 <TTM2>
		     val {<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! T>} <ND3 y u> = 
		             {<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! T>} lemma4i
		                       (W1 with (<x> => (<y>, <ttm>)))
			               (W2 with (<x> <y> ttm => (<_>, <TTP2>, <u>))) 
				       <TTM1 x y ttm> <N> <TTP3> 
                     val (<_>, <ND1>) = lemma3 <TTP3>
		     val (<_>, <ND2>) = lemma3 <TTP2>
		   in
		      (<_>, 
		       <t-base (trans@ (trans@ (trans== (TTP3)) 
					(trans@ (trans\ TTM1) TTM2))
							   (TTM1 _ _ TTM2))>,
		       <_>,
		       < nall-elim 
			  (nall-elim 
			   (nall-elim
			    (=n=>-elim beta_lemma (ax-elim (n/\-fst ND1))) 
			      (fun-elim (fun-intro (ax-elim (n/\-fst ND2)) ND3) ND4))
			   (ND3 _ ND4)) 
			  (subst ([_][w] equality-form (ND3 N6 ND4) w (ax-elim (n/\-fst ND1)))
			   (fun-beta ND3 ND4)
			      (ax-intro (ND3 N6 ND4)))
		       >)
		   end

	      | W1 W2 W3 W4 <refl : |- (H:tm A) === H> 
                => let 
                     val (<T>, <TTP>, <ND1>) = lemma0 <A>
		     val (<_>, <TTM>) = lemma2 W1 <H>
		     val <ND> = lemma4i W1 W2 <TTM> <T> <TTP> 
		   in
		     (<_>, <t-base (trans@ (trans@ (trans== TTP) TTM) TTM)>, <_>,
		      <nall-elim (nall-elim refl_lemma ND1) ND>)
		   end
              | W1 W2 W3 W4 <sub ([x:tm A] G x) (D1 : |- H1 === H2) (D2 : |- G H1)>
	        => let
                     val {<x>}{<y>}{<ttm:transtm x y>} (<_>, <TTM3 x y ttm>)
		            = {<x>}{<y>}{<ttm:transtm x y>} lemma2 
		                      (W1 with (<x> => (<y>, <ttm>))) <G x>
                     val (<_>, <t-base (trans@ (trans@ (trans== TTP1) TTM1) TTM2)>, 
				<_>, <ND1>) = lemma5 W1 W2 W3 W4 <D1>
		     val (<_>, <ND5>) = lemma5i W1 W2 W3 W4 <D2> <_> <t-base (TTM3 _ _ TTM1)>
		     val (<_>, <ND2>) = lemma3 <TTP1>
		     val <ND3> = lemma4i W1 W2 <TTM1> <_> <TTP1>
		     val <ND4> = lemma4i W1 W2 <TTM2> <_> <TTP1>
                     val {<x>}{<y>}{<ttm>}{<u>} (<_>, <_>, <ND6 y u>) = 
				     {<x>}{<y>}{<ttm>}{<u>} lemma4 
						  (W1 with (<x> => (<y>, <ttm>)))
						  (W2 with (<x> <y> ttm => (<_>, <TTP1>, <u>)))
						      <TTM3 x y ttm>
		   in
		     (<_>,
		      <t-base (TTM3 _ _ TTM2)>,
		      <_>,
		      <subst' ([x][u] u)
		      (fun-beta ([x] [u] ^-form (M x) (ND6 x u)) ND4)
			 (=n=>-elim 
			   (=n=>-elim 
			     (=n=>-elim 
			       (nall-elim 
				(nall-elim 
				 (nall-elim 
				  subst_lemma 
				  (ax-elim (n/\-fst ND2)))
				 ND3) 
				ND4)
			       (fun-intro (ax-elim (n/\-fst ND2)) [x] [u] ^-form (M x) (ND6 x u))) 
			       ND1)
			     (subst ([x] [u] u) 
			      (fun-beta ([x] [u] ^-form (M x) (ND6 x u)) ND3) 
				 ND5))>)
		   end
             | W1 W2 W3 W4 <mp (D1:|- H) (D2 : |- H ==> G)>
	        => let 
		     val (<T1>, <TTM1 : transtm H T1>) = lemma2 W1 <H>
		     val (<T2>, <TTM2:transtm G T2>) = lemma2 W1 <G>
		     val (<_>, <transtpo>, <ND4>) = lemma4 W1 W2 <TTM1>
		     val (<_>,<transtpo>, <ND3 : !- T2 !*! boolean>) = lemma4 W1 W2 <TTM2>
		     val (<_>, <ND1>) = lemma5i W1 W2 W3 W4 <D1> <_> <t-base TTM1>
		     val (<_>, <ND2>) = lemma5i W1 W2 W3 W4 <D2> <_> 
		                             <t-base (trans@ (trans@ trans=> TTM1) TTM2)>
                   in
		     (<_>, <t-base TTM2>, <_>, 
		      <nall-elim (nall-elim (nall-elim 
		           (nall-elim mp_lemma ND4) ND3) ND2) ND1>)
	           end
    	    |  W1 W2 W3 W4 <disch (D : |- H -> |- G)> 
	        => let
		     val (<T1>, <TTM1:transtm H T1>) = lemma2 W1 <H>
		     val (<T2>, <TTM2:transtm G T2>) = lemma2 W1 <G>
		     val {<u: |- H>}{<y>}{<v:!- y !*! ^ T1>} (<_>, <ND y v>) =
		            {<u: |- H>}{<y>}{<v:!- y !*! ^ T1>} 
				      lemma5i (W1 with .) (W2 with .)
				      (W3 with (<u> => (<^ T1>, <t-base TTM1>, <y>, <v>)))
				      (W4 with .)
					<D u> <_> <t-base TTM2>
		     val (<_>, <TTP1>, <ND1>) = lemma4 W1 W2 <TTM1>
		     val (<_>, <TTP2>, <ND2>) = lemma4 W1 W2 <TTM2>
		   in  (<_>, <t-base (trans@ (trans@ trans=> TTM1) TTM2)>, 
			<_>, < =n=>-elim (nall-elim (nall-elim disch_lemma ND1)
					  ND2)
			(=n=>-intro (boolean-if (uni-form (+ge1 0ge0)) 
				     ND1 (ntrue-form)  nfalse-form) ND)>)
		   end
	      | W1 W2 W3 W4 <abs D1 : |- (\ ([x:tm A] H x) : tm (A arr B)) === \ G> 
	        => let
		     val (<TA>, <TTP1:transtp A TA>) = lemma1 <A>
		     val (<TB>, <TTP2:transtp B TB>) = lemma1 <B>
		     val {<x>}{<y>}{<ttm>} (<TH y>, <TTM1 x y ttm>) 
                           = {<x>}{<y>}{<ttm>} lemma2 (W1 with (<x> => (<y>, <ttm>))) <H x>
		     val {<x>}{<y>}{<ttm>} (<TG y>, <TTM2 x y ttm>)
		           = {<x>}{<y>}{<ttm>} lemma2 (W1 with (<x> => (<y>, <ttm>))) <G x>
		     
		     val {<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! _>} <ND3 y u> =
		         {<x>}{<y>}{<ttm:transtm x y>}{<u : !- y !*! _>} 
			     let 
			       val W1' = (W1 with (<x> => (<y>, <ttm>)))
                               val W2' = (W2 with (<x> <y> <ttm> => (<_>, <TTP1>, <u>)))
                             in
                               lemma4i W1' W2' <TTM1 x y ttm> <_> <TTP2>
			     end
		     val {<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! _>} <ND4 y u> =
                         {<x>}{<y>}{<ttm:transtm x y>}{<u : !- y !*! _>} 
		             let 
			       val W1' = (W1 with (<x> => (<y>, <ttm>)))
                               val W2' = (W2 with (<x> <y> <ttm> => (<_>, <TTP1>, <u>)))
                             in
    			       lemma4i W1' W2' <TTM2 x y ttm> <_> <TTP2>
                             end
		     val {<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! _>} (<P5 y>, <ND5 y u>) =
		         {<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! _>} 
			     lemma5i
			       (W1 with (<x> => (<y>, <ttm>)))
			       (W2 with (<x> <y> <ttm> => (<_>, <TTP1>, <u>)))
			       (W3 with .)
			       (W4 with (<x> <ttm> <ttm> => <eq_base>))
			       <D1 x> <_> <t-base (trans@ (trans@ (trans== TTP2) (TTM1 x y ttm))
						          (TTM2 x y ttm))>
		     val (<P1>, <ND1>) = lemma3 <TTP1>
		     val (<P2>, <ND2>) = lemma3 <TTP2>
                   in
		     (<_>, 
		      <t-base (trans@ (trans@ (trans== (transtparr TTP1 TTP2))
				       (trans\ TTM1)) (trans\ TTM2))>, 
		      <_>, 
		      <(=n=>-elim (nall-elim 
				   (nall-elim (nall-elim beta_lemma 
					       (fun-form (ax-elim (n/\-fst ND1)) 
						  ([_][_] ax-elim (n/\-fst ND2))))
				    (fun-intro (ax-elim (n/\-fst ND1)) ND3)) 
				   (fun-intro (ax-elim (n/\-fst ND1)) ND4)) 
			(genax (fun-form (ax-elim (n/\-fst ND1)) [_][_] ax-elim (n/\-fst ND2))
			 (fun-intro (ax-elim (n/\-fst ND1)) ND4)
			    (fun-xi1 
			       ([x][u] ax-elim 
				(=n=>-elim 
				  (nall-elim 
				   (nall-elim (nall-elim 
					       beta_inverse 
					       (ax-elim (n/\-fst ND2))) 
				    (ND3 x u)) 
				   (ND4 x u))
				  (ND5 x u))) 
			       (ax-elim (n/\-fst ND1)))
			       ))>)
                   end
;

(*
val sample : <|- true ==> true> = <disch ([u] u)>;
params = . ;

val test = lemma5 (fn .) (fn .) (fn .) (fn .) sample;
val test = lemma5 (fn .) (fn .) (fn .) (fn .) <imp-antisym-ax>;

val cantor : <|- all (\ [G] ex (\ [F : tm (o arr o)] all (\ [X] not (G @ X === F))))>
           = <alli ([G:tm (o arr o arr o)] 
	      exi (\ [y] not (G @ y @ y)) 
	        (alli [X: tm o] 
		     noti ([u] lemma (eqbetar (fun_cong u)))))>;

*)
(* val nuprlcantor = lemma5 (fn .) (fn .) (fn .) (fn .) cantor; *)
