(* The delphin programming language operational semantics *)
(* Author: Adam Poswolsky *)

structure DelphinOpsem : DELPHIN_OPSEM = 
  struct
    exception NoSolution
    structure I = IntSyn
    structure D = DelphinIntSyntax

    fun crash() = raise Domain

   fun getElement(1, E::xs) = SOME E
     | getElement(i, _::xs) = if (i > 1) then getElement(i-1, xs) else crash()
     | getElement _ = NONE

    fun getParamList' (I.Null, k) = []
      | getParamList' (I.Decl(G, D.NonInstantiableDec _), k) = k:: (getParamList' (G, k+1))
      | getParamList' (I.Decl(G, _), k) = getParamList' (G, k+1)

    fun getParamList  G = getParamList' (G, 1)

    (* For application, we fill in all pattern variables with logic variables *)
    fun reduceCase Gglobal G (Ctotal as D.Eps (D.NormalDec(_, D.LF(isP, A)), C, fileInfo)) =
            (case (D.whnfP isP)
	      of D.Existential =>  	     
		      let
			val X = I.newEVarPruneNdec (D.coerceCtx G, A)
			(* Should we lower the EVar..    val X' = Whnf.lowerEVar X (* X' is the lowered version *) *)
		        (* Caution:  Make sure to do Whnf before calling lower as it is probably an EClo now.. *)
			val t = D.Dot (D.Prg (D.Quote X), D.id)
		      in
			reduceCase Gglobal G (D.substCase(C, t))
		      end


	      | D.Param =>
		      let 
			(* OLD:  Need to prune away NDecs in G... 
                         *   val X = D.Var (D.BVarLF ((ref NONE, A, D.makeLFParamList G, ref nil), I.id), NONE)
                         *)
			val X = D.Var (D.newParamVarPruneNDecs (Gglobal, G, A), NONE)

			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase Gglobal G (D.substCase(C, t))
		      end

              | D.PVar _ => crash() (* should not get to opsem with any PVars *)
            )

      | reduceCase Gglobal G (Ctotal as D.Eps (D.NormalDec(_, D.Meta(F)), C, fileInfo)) =
		      let
			val X = D.newEVar(F)
			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase Gglobal G (D.substCase(C, t))
		      end
	   (* no more BVarMeta
	      | D.Param =>                   
		      let 
			val X = D.Var (D.BVarMeta ((ref NONE, F), D.id), NONE)
			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase Gglobal G (D.substCase(C, t))
		      end
              | D.PVar _ => crash() (* should not get to opsem with any PVars *)
            *)

      | reduceCase Gglobal G (C as D.NewC _) = C

      | reduceCase Gglobal G (D.PopC (i, C)) = 
	         (case (reduceCase Gglobal (D.popCtx(i, G)) C)  (* Note that you cannot pop to Gglobal.. *)
		    of (D.NewC (_, C', _)) => reduceCase Gglobal G (D.substCase(C', D.shiftTo(i-1, D.id)))
		     | _ => crash() (* not type correct *)
                 )


      | reduceCase Gglobal G (C as D.Match _) = C


                             

    fun eval G E = evalW G (D.whnfE E)
    and evalW G (E as D.Var (D.Fixed _, _)) = E (* Will only occur if i is parameter *)
      | evalW G (E as D.Var _) = E (* will occur in evaluation of patterns in cases *)
      | evalW G (E as D.Quote _) = E (* LF Terms are values *)
      | evalW G (E as D.Unit) = E (* Unit is a value *)
      | evalW G (E as D.Lam (Clist, F, fileInfo)) =  E (* Lam is a value *)

      | evalW G (D.New(D, E, fileInfo)) = D.New(D, eval (I.Decl(G, D.NonInstantiableDec D)) E, fileInfo)

      | evalW G (D.App (Efun, argList)) =  
             let
	       val funVal = eval G Efun
	       val cList = case funVal
		           of D.Lam(cList, _, _) => cList
			    | E => crash()

               (* evaluate the spine to values *)
	       val argsVal = map (fn (vis, fileInfo, S') => eval G S') argList


               (* matchCaseR(C, spine) = (SOME E) or NONE
		* precondition is that C is reduced (no epsilons)
		*)

	       fun matchCaseR (D.Match ((_, E1)::pats, E2), S::Spine) =
		             (let
			       val E1 = eval G E1 (* evaluate the pattern.
						   * needed for patterns that use "pop"
						   *)
			       val _ = UnifyDelphinNoTrail.unifyE(I.Null, D.coerceCtx G, E1, S)
			     in
			       matchCaseR(D.Match(pats, E2), Spine)
			     end
			   handle UnifyDelphinNoTrail.Error _ => NONE
				| NoSolution => NONE)

		 | matchCaseR (D.Match ([], E2), []) = SOME E2 (* match successful! *)
		 | matchCaseR _ = crash() (* badly typed *)

	       fun matchCases [] = raise NoSolution
		 | matchCases (C::cs) = (case (matchCaseR(reduceCase I.Null G C, argsVal))
					   of NONE => matchCases cs
					    | SOME(E) => E)
			 
	     in
	       eval G (matchCases (cList))
	     end

      | evalW G (D.Pair (E1, E2, F)) = D.Pair (eval G E1, eval G E2, F)

      | evalW G (D.ExpList Elist) = D.ExpList (map (fn E => eval G E) Elist)
	                           (* These will typically all be functions (maybe with newW attached)
				    * which means it will not do much work.
				    *)

      | evalW G (D.Proj (E, i)) = (case (eval G E)
	                         of (D.ExpList Elist) => (case (getElement(i, Elist))
				                         of NONE => crash() (* not type correct *)
							  | SOME V => V)
				   | _ => crash() (* not type correct *))

      | evalW G (D.Pop (i, E, fileInfo)) = (case (eval (D.popCtx(i, G)) E)
				   of (D.New(_, V, fileInfo)) => D.substE'(V, D.shiftTo(i-1, D.id))
				     | (D.EVar ((r (* ref NONE *), F), t)) => 
                                              (* This case can occur when evaluating patterns *)
                                              let
						val (newD, newF) = let
						              fun removeNabla (D.Nabla(D, F)) = (D, F)
								| removeNabla _ = crash() (* Error *)
							   in
							     removeNabla (D.whnfF F)
							   end

					        (* Assuming G = G1,x:A[t],G2 
						 * G1,x:A[t] |- (r : {<x:A>}newF) [t] : {<x:A[t]>} newF[dot1 t]
						 * G1 |- t : G*
						 * G* |- r = new x:A.(X : newF)
						 * G1,A[t] |- dot1 t : G*,A
						 *)

						val newBody = D.newEVar(newF)
						val _ = r := SOME(D.New(newD, newBody, NONE))
					      in
						D.substE'(newBody, D.shiftTo(i-1, D.dot1 (t, fileInfo)))
					      end

				     | (D.Lam(Clist, F, fileInfo)) => 
					      let
						fun addPop C = D.PopC(i, C)

						(* precondition:  in whnf *)
						fun removeNewF (D.Nabla(_, F)) = D.FClo(F, I.Shift (i-1))
						  | removeNewF (F as D.FVar _) = crash() (* should be filled in 
											       * before executing
											       * opsem
											       *)
						  | removeNewF _ = crash()
					      in
						D.Lam (map addPop Clist, removeNewF (D.whnfF F), NONE)
					      end
				     | V => crash () (* impossible *)
					      (* D.Pop(i, V, fileInfo) *)

				  )

      | evalW G (E as D.Fix (D, E')) = let
				       val t = D.Dot(D.Prg E, D.id)
				       val E'' = D.substE'(E', t) 
				     in
				       eval G E''
				     end

      | evalW G (E as D.EVar _) = E (* uninstantiated EVar... can occur in
				     * the evaluation of patterns 
				     *) 

      | evalW G (D.EClo _) = crash() (* not in whnf *)



    fun eval0 E = let 
		    val V = SOME(eval (I.Null) E)
		              handle NoSolution => NONE
		  in
		    case V of
		      SOME V => V
		     | _ => raise NoSolution
		  end

end
