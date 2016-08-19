(* The HOL Nuprl connection, written in Delphin *)
(* Authors: Carsten Schuermann, Adam Poswolsky *) 

use "hol/hol.d" ; (* sig use "hol/hol.elf"; *)
(* sig use "hol/axioms.elf";
*)
sig use "nuprl/nuprl.elf";
sig use "nuprl/classical.elf";
sig use "nuprl/nuprl-lemmas.elf";
sig use "nuprl/examples.elf"; 
sig use "trans.elf";


type world1 = (<B:tp> -> <H':(tm B)#> -> <M:n-tm> * <transtm H' M>);;
type world2 = (<B:tp> -> <H':tm B> -> <M:n-tm> -> <u:(transtm H' M)#> -> <T:n-tm> * <transtp B T> * <!- M !*! T>);
type world3 = (<H: tm o> -> <U: |- H #> -> <T:n-tm> * <transsen H T> * <M:n-tm> * < !- M !*! T>);



params = <n-tm>, <tm B>, <transtm H M>, <|- H>, < !- M !*! T > ;


fun unique : <transtp A T1> -> <transtp A T2> -> <!- M !*! T1> -> <!- M !*! T2> = fn <_> <_> <x> => <x> ;

(* Lemma 1 *)
fun lemma1 : <A : tp> -> <N : n-tm> * <transtp A N>  
  	    = fn <o> => (<boolean> , <transtpo>) 
	       | <A arr B> => (case (lemma1 <A>, lemma1 <B>)
	                         of ((<N1>, <S1>), (<N2>, <S2>)) 
				      => (<pi N1 [x] N2>, <transtparr S1 S2>));


(* Lemma 2 *)

fun lemma2 : world1 -> <H:tm C> -> <M:n-tm> * <transtm H M>
            = fn W < => > => (< =p=> >, < trans=> >)
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
	           => (case (lemma1 <A>) 
                         of (<N>, <TTP>) 
	                 => (case ({<x>}{<y>}{<u:transtm x y>} lemma2 (W with (<_> x => (<y>, <u>))) <H x>)
	       	               of ({<x>}{<y>}{<u>} (<M y>, <TTM x y u>))
			       => (<lam M>,  < trans\ TTP TTM>)))
  	       | W <true> => (<tt>, <tc-true>)
	       | W <false> => (<ff>, <tc-false>)
               | W <neg> => (<lam [x] if x ff tt>, <tc-neg>)
               | W < /|\ > => (<lam [x] lam [y] if x y ff>, < tc-/|\>)
 	       | W < \|/ > => (<lam [x] lam [y] if x tt y>, < tc-\|/>)
	       | W < all| : tm ((A arr o) arr o) > 
	           => (case (lemma1 <A>)
	       	                of (<T>, <TTP>) => (<lam [p] v (pi T [x] ^ (app p x)) >, <tc-all| TTP>))
	       | W < ex| : tm ((A arr o) arr o) > 
	           => (case (lemma1 <A>)
	       	                of (<T>, <TTP>) => (< lam [p] v (sigma T [x] ^ (app p x)) >, <tc-ex| TTP>))
	       | W < the| : tm ((A arr o) arr A) > 
	           => (case (lemma1 <A>)
	       	                of (<T>, <TTP>) => (< lam [p] decide (app inhabited 
	                               (set T ([x] ^ app p x))) ([x] x) ([x] arb T)>, <tc-the| TTP>))
               | W [<x:(tm A) #>] <x> => (W <A> x); 





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

fun lemma4 : world1 -> world2 
             -> <transtm (H:tm A) N> -> <T:n-tm> * <transtp A T> * <!- N !*! T> 
	   = fn W1 W2 [<u:transtm (H:tm A) N#>] <u> => W2 <A> <H> <N> u
              | W1 W2 < trans=> > 
	        => <_>, (<transtparr transtpo (transtparr transtpo transtpo)>, 
	            <fun-intro (sum-form (unit-form : !- unit !*! uni 1) 
		  	       (unit-form : !- unit !*! uni 1)) [x1] [u1] 
	   	     fun-intro (sum-form (unit-form : !- unit !*! uni 1) 
			       (unit-form: !- unit !*! uni 1)) [x2] [u2] 
		     boolean-if boolean-form u1 u2 boolean-tt>) 

              | W1 W2 < trans== TTP >
	        => (case (lemma3 <TTP>)
		     of (<_>, <ND>)
		     => <_>, (<transtparr TTP (transtparr TTP transtpo)>, 
		         <fun-intro (ax-elim (n/\-fst ND)) [x1] [u1] 
		          fun-intro (ax-elim (n/\-fst ND)) [x2] [u2]
		  	  sum-decide ([x3][u3] boolean-form) 
		  	  (fun-elim inh-intro (equality-form u2 u1 (ax-elim (n/\-fst ND)))) 
		  	  ([x4][u4] boolean-tt) ([x5][u5] boolean-ff)>))
(*
              | W1 W2 < trans\ TTP1 TTM > 
	        => (case (lemma3 <TTP1>) 
 		      of (<_>, <ND1>)
		      => (case ({<x>}{<y>}{<ttm:transtm x y>}{<u>} lemma4 
	                                                           (W1 with (<_> x => (<y>, <ttm>)))
                                                                   (W2 with (<_> <x> <y> ttm => (<_>, <TTP1>, <u>)))
		                                                   <TTM x y ttm>)
		            of ({<x>}{<y>}{<ttm>}{<u>} (<_>, <TTP2>,  <ND2 y u>))
			    => (<_>, <transtparr TTP1 TTP2>, <fun-intro (ax-elim (n/\-fst ND1)) ND2>)))
*)
              | W1 W2 < trans\ TTP1 TTM > 
	        => (case (lemma3 <TTP1>) 
 		      of (<_>, <ND1>)
		      => (case ({<x>}{<y>}{<ttm:transtm x y>}{<u>} lemma4 
	                                                           (W1 with (<_> x => (<y>, <ttm>)))
                                                                   (W2 with (<_> <x> <y> ttm => (<_>, <TTP1>, <u>)))
		                                                   <TTM x y ttm>)
		            of ({<x>}{<y>}{<ttm>}{<u>} (<_>, <TTP2>,  <ND2 y u>))
			    => 
				     (<_>, <transtparr TTP1 TTP2>, <fun-intro (ax-elim (n/\-fst ND1)) ND2>)
				))
	



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
	        => (case (lemma3 <TTP>)
		     of (<_>, <ND>)
		     => (<_>, <transtparr (transtparr TTP transtpo) transtpo>, 
		         <fun-intro (fun-form (ax-elim (n/\-fst ND)) [z][w] boolean-form) 
			   ([x][u] v-form 
		      	     (fun-form (ax-elim (n/\-fst ND)) 
			       [y] [v] ^-form _ (fun-elim u v)))>))
	      | W1 W2 < tc-ex| TTP >
	        => (case (lemma3 <TTP>)
		     of (<_>, <ND>)
		     => (<_>, <transtparr (transtparr TTP transtpo) transtpo>, 
		         <fun-intro (fun-form (ax-elim (n/\-fst ND)) [z] [w] boolean-form)
		   [x][u] v-form 
		   (sig-form (ax-elim (n/\-fst ND)) 
		      [y] [v] ^-form _ (fun-elim u v))>))

	      | W1 W2 < tc-the| TTP >
	        => (case (lemma3 <TTP>)
		     of (<_>, <ND>)
		     => (<_>, <transtparr (transtparr TTP transtpo) TTP>, 
		         <fun-intro (fun-form (ax-elim (n/\-fst ND)) [x0] [u0 : !- _ !*! T] boolean-form) 
		   [x] [u] sum-decide ([x2][u2] ax-elim (n/\-fst ND)) (fun-elim inh-intro 
						 (set-form (ax-elim (n/\-fst ND)) 
						    ([y][v] ^-form (app x y) (fun-elim u v))))
		   ([y] [v] set-elem ([z][w] boolean-decide ([_] [_] uni-form (+ge1 0ge0)) 
					(fun-elim u w)
					unit-form
					void-form) v)
		   ([x4] [u4] arb-intro _ ND)>))

              | W1 W2 < trans@ TTM1 TTM2 >
                => (case (lemma4 W1 W2 <TTM1>, lemma4 W1 W2 <TTM2>) 
		      of ((<_>, < transtparr TTP1 TTP >, < ND1 >), (<_>, <TTP1'>, < ND2' >)) 
		      => let
	 		    val <ND2> = unique <TTP1'> <TTP1> <ND2'>
		         in
			    (<_>, <TTP>, <fun-elim ND1 ND2>)
		         end);
	               

(* Lemma 5 *)

fun lemma5 : world1 -> world2 -> world3
             -> < |- H > -> <T:n-tm> * <transsen H T> * <M:n-tm> * < !- M !*! T>
	   = fn W1 W2 W3 [<u : |- H #>] <u> => W3 <H> u
              | W1 W2 W3 <beta : |- (\ H) @ G === (H G)> 
	        => (case ({<x>}{<y>}{<ttm:transtm x y>} lemma2 (W1 with (<_> x => (<y>, <ttm>))) <H x>)
		      of ({<x>}{<y>}{<ttm:transtm x y>} (<_>, < TTM1 x y ttm >))
		      => (case (lemma2 W1 <G>)
		            of (<_>, <TTM2>)
			    => (case (lemma4 W1 W2 <TTM2>) 
			          of (<_>, <TTP2>, <ND4>) 
			          => (case ({<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! T>} lemma4 
		                                                   (W1 with (<_> x => (<y>, <ttm>)))
						  		   (W2 with (<_> <x> <y> ttm => (<_>, <TTP2>, <u>)))
                                                                   <TTM1 x y ttm>)
			                of ({<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! T>} (<MM>, <TTP1>, <ND3 y u>))
						 	(* To Carsten:  You will get a constraint error if you write "_" instead of MM.
							 *  This is because by specifying MM, we are declaring that it is not dependent
							 *  on "y".  However, I can change the interpretation of "_" in patterns,
							 *  so it declares them before the "y".  But it is more flexible
							 *  this way... but you have to give something a name which you don't care 
							 *  about.  I like the flexibility, but I can change it if you want.
							 *  What do you think?
							 *)
					=> case ((lemma3 <TTP1>), (lemma3 <TTP2>)) 
					     of ((<_>, <ND1>), (<_>, <ND2>)) => 
					        (<_>, 
						 <
						  (t-base (trans@ (trans@ (trans== TTP1) 
						      (trans@ (trans\ TTP2 TTM1) TTM2)) (TTM1 _ _ TTM2)))
                                                 >,
						 <_>,
						 <
						   (nall-elim 
						      (nall-elim 
							 (nall-elim
							    (=n=>-elim beta_lemma (ax-elim (n/\-fst ND1))) 
							    (fun-elim (fun-intro (ax-elim (n/\-fst ND2)) ND3) ND4))
							 (ND3 _ ND4)) 
						      (subst ([_][w] equality-form (ND3 N6 ND4) w (ax-elim (n/\-fst ND1)))
							 (fun-beta ND3 ND4)
								 (ax-intro (ND3 N6 ND4))))
						 >)))))

	      | W1 W2 W3 <refl : |- H === H> 
	        => (case (lemma2 W1 <H>)
		      of (<_>, <TTM>) 
		      => (case (lemma4 W1 W2 <TTM>) 
		            of (<_>, <TTP>, <ND>) 
			    => (<_>, <t-base (trans@ (trans@ (trans== TTP) TTM) TTM)>, <_>,
				   <nall-elim (nall-elim refl_lemma boolean-form) ND>)))
              | W1 W2 W3 <sub ([x:tm A] G x) (D1 : |- H1 === H2) (D2 : |- G H1)>
	        => (case ({<x>}{<y>}{<ttm:transtm x y>} lemma2 (W1 with (<_> x => (<y>, <ttm>))) <G x>)
		      of ({<x>}{<y>}{<ttm:transtm x y>} (<_>, <TTM3 x y ttm>))
		      => (case ((lemma5 W1 W2 W3 <D1>), (lemma5 W1 W2 W3 <D2>)) 
		            of ((<_>, <t-base (trans@ (trans@ (trans== TTP1) TTM1) TTM2)>, <_>, <ND1>),
			        (<_>, <t-base (TTM3 _ _ TTM1)>, <_>, <ND5>))
			    => (case ((lemma3 <TTP1>), (lemma4 W1 W2 <TTM1>), (lemma4 W1 W2 <TTM2>)) 
			          of ((<_>, <ND2>), (<_>, <_>, <ND3>), (<_>, <_>, <ND4>))
				  => (case ({<x>}{<y>}{<ttm>}{<u>} lemma4 
                                                                   (W1 with (<_> x => (<y>, <ttm>)))
						  		   (W2 with (<_> <x> <y> ttm => (<_>, <TTP1>, <u>)))
                                                                   <TTM3 x y ttm>)
				        of ({<x>}{<y>}{<ttm>}{<u>} (<_>, <_>, <ND6 y u>)) 
					=> (<_>,
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
			   		    ND5))>)))))


	      | W1 W2 W3 <abs D1 : |- \ ([x:tm A] H x) === \ G> 
	 	(* ADAM!!! WARNING:  Compare this carefully to meta.elf!! *)
	        => (case (lemma1 <A>) 
		      of (<_>, <TTP1>) 
		      => (case ({<x>}{<y>}{<ttm>} ((lemma2 (W1 with (<_> x => (<y>, <ttm>))) <H x>), (lemma2 (W1 with (<_> x => (<y>, <ttm>))) <G x>)))
		            of ({<x>}{<y>}{<ttm>} ((<_>, <TTM1 x y ttm>), (<_>, <TTM2 x y ttm>)))
			    => (case ({<x>}{<y>}{<ttm:transtm x y>}{<u : !- y !*! _>} 
				         let val W1' = (W1 with (<_> x => (<y>, <ttm>)))
                                             val W2' = (W2 with (<_> <x> <y> ttm => (<_>, <TTP1>, <u>)))
                                          in
                                           ((lemma4 W1' W2' <TTM1 x y ttm>), (lemma4 W1' W2' <TTM2 x y ttm>))
                                          end)
			          of ({<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! _>} ((<_>, <TTP2>, <ND3 y u>), (<_>, <TTP2>, <ND4 y u>)))
				  => (case ({<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! _>} 
                                                                         lemma5 
		                                                            (W1 with (<_> x => (<y>, <ttm>)))
                                                                            (W2 with (<_> <x> <y> ttm => (<_>, <TTP1>, <u>)))
                                                                            (W3 with .)
                                                                         <D1 x>)
				        of ({<x>}{<y>}{<ttm:transtm x y>}{<u: !- y !*! _>} (<_>, <_>, <_>, <ND5 y u>)) 
					=> (case ((lemma3 <TTP1>), (lemma3 <TTP2>))
					      of ((<_>, <ND1>), (<_>, <ND2>))
					      => (<_>, 
					          <t-base (trans@ (trans@ (trans== (transtparr TTP1 TTP2))
				   	             (trans\ TTP1 TTM1)) (trans\ TTP1 TTM2))>, 
						  <_>, 
						  <=n=>-elim (nall-elim 
						    (nall-elim (nall-elim beta_lemma 
					   	        (fun-form (ax-elim (n/\-fst ND1)) 
					      		([y][v] ax-elim (n/\-fst ND2))))
							(fun-intro (ax-elim (n/\-fst ND1)) ND3)) 
			     				(fun-intro (ax-elim (n/\-fst ND1)) ND4)) 
		   					(ax-intro (fun-xi1 
							([x][u] ax-elim 
				   			(=n=>-elim 
				      			(nall-elim 
					 		(nall-elim (nall-elim 
						       	beta_inverse 
						       	(ax-elim (n/\-fst ND2))) 
					    		(ND3 x u)) 
					 		(ND4 x u))
				      			(ND5 x u))) 
							(ax-elim (n/\-fst ND1))))>))))))

    	    |  W1 W2 W3 <disch (D : |- H -> |- G)> 
	        => (case ((lemma2 W1 <H>), (lemma2 W1 <G>)) 
		      of ((<_>, <TTM1>), (<_>, <TTM2>)) 
		      => (case ((lemma4 W1 W2 <TTM1>), (lemma4 W1 W2 <TTM2>)) 
		            of ((<_>, <_>, <ND1>), (<_>, <_>, <ND2>))
			    => (case ({<u: |- H>}{<y>}{<v:!- y !*! ^ T1>} lemma5 (W1 with .) (W2 with .) (W3 with (<H> u => (<^ T1>, <t-base TTM1>, <y>, <v>))) <D u>) 
			          of ({<u: |- H>}{<y>}{<v:!- y !*! ^ T1>} (<_>, <_>, <_>, <ND y v>)) 
				  => (<_>, <t-base (trans@ (trans@ trans=> TTM1) TTM2)>, <_>, < =n=>-elim (nall-elim (nall-elim disch_lemma ND1) ND2)
					    (=n=>-intro (boolean-if (uni-form (+ge1 0ge0)) ND1 (ntrue-form)  nfalse-form) ND)>))))

             | W1 W2 W3 <mp (D1:|- H) (D2 : |- H ==> G)>
	        => (case (lemma2 W1 <H>) 
		      of (<_>, <TTM>) 
		      =>
		      (case (lemma2 W1 <H ==> G>) 
		         of (<_>, <trans@ (trans@ trans=> TTM2) TTM2'>)
		         => (case (lemma4 W1 W2 <TTM>) 
		               of (<_>, <transtpo>, <ND4>)
			       => (case (lemma4 W1 W2 <TTM2'>)
			             of (<_>,<transtpo>, <ND3>)
				     => (case ((lemma5 W1 W2 W3 <D1>), (lemma5 W1 W2 W3 <D2>)) 
			                   of ((<_>, <_>, <_>, <ND1>), 
				               (<_>, <_>, <_>, <ND2>))
				           => (<_>, 
					       <t-base TTM2'>, 
					       <_>, 
				               <nall-elim (nall-elim (nall-elim (nall-elim mp_lemma ND4) ND3) ND2) ND1>))))));


val sample : <|- true ==> true> = <disch ([u] u)>;
params = . ;

val test = lemma5 (fn .) (fn .) (fn .) sample;