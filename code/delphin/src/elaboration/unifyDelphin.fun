(* Delphin Unification *)
(* Author: Adam Poswolsky *)

functor UnifyDelphin (structure Trail : TRAIL
		      structure U  : UNIFY (* LF Unification *))
=  struct
    exception Error of string

    local
      structure D = DelphinIntSyntax
      structure I = IntSyn
      structure W = Whnf


      datatype Action = 
	InstantiateP of D.isParam option ref
      | InstantiateV of D.Visibility option ref
      | InstantiateF of D.Formula option ref
      | InstantiateE of D.Exp option ref
      | Add of (D.Cnstr ref) list ref
      | Solve of (D.Cnstr ref) * D.Cnstr
	
      val globalTrail = Trail.trail () : Action Trail.trail
	
      fun undo (InstantiateP refP) =
	    (refP := NONE)
	| undo (InstantiateV refV) =
	    (refV := NONE)
	| undo (InstantiateF refF) =
	    (refF := NONE)
	| undo (InstantiateE refE) =
	    (refE := NONE)
	| undo (Add (cnstrs as ref(cnstr :: cnstrL))) =
	    (cnstrs := cnstrL)
	| undo (Add (cnstrs as ref([]))) = raise Domain
	| undo (Solve (cnstr, Cnstr)) =
	    (cnstr := Cnstr)

	
      fun reset () = (U.reset() ; Trail.reset globalTrail)
      fun mark () = (U.mark() ; Trail.mark globalTrail)
      
      fun unwind () = (U.unwind(); Trail.unwind (globalTrail, undo))


      fun addConstraint (cnstrs, cnstr) =
          (
            cnstrs := cnstr :: (!cnstrs);
            Trail.log (globalTrail, Add (cnstrs))
          )

      fun solveConstraint (cnstr as ref (Cnstr)) =
          (
            cnstr := D.Solved;
            Trail.log (globalTrail, Solve (cnstr, Cnstr))
          )


      local
	val awakenCnstrs = ref nil : (D.Cnstr ref) list ref
      in
	fun resetAwakenCnstrs () = (awakenCnstrs := nil)
	  
	fun nextCnstr () = 
            case !awakenCnstrs
              of nil => NONE
               | (cnstr :: cnstrL) => 
                   (awakenCnstrs := cnstrL; SOME(cnstr))

	(* Instantiating Vars  *)
	fun instantiatePVar (refP, P) =
            (
              refP := SOME(P);
              Trail.log (globalTrail, InstantiateP (refP))
            )

	fun instantiateVisibleVar (refV, V) =
            (
              refV := SOME(V);
              Trail.log (globalTrail, InstantiateV (refV))
            )

	    
	fun instantiateFVar (refF, F, cnstrL) =
            (
              refF := SOME(F);
              Trail.log (globalTrail, InstantiateF (refF));
              awakenCnstrs := cnstrL @ !awakenCnstrs
            )


	fun instantiateEVar (refE, E) =
            (
              refE := SOME(E);
              Trail.log (globalTrail, InstantiateE (refE))
            )

      end  (* local *)
  


      fun numShifts t =
          let
	    fun countShifts (D.id) = 0
	      | countShifts (D.Shift t) = 1 + (countShifts t)
	      | countShifts _ = raise Error "Delphin Unification Failed:  Non-Shift Substitution"
	  in 
	    if (D.isId t) then 0 else (countShifts t)
	  end

      (* Only inverts a substitution of the form "shift^i id" *)
      fun invertShiftSub 0 = D.id
	| invertShiftSub n = D.Dot(D.Undef, invertShiftSub(n-1))
    
	
       (* strengthen (t, G) = G'

	Invariant:
	If   G'' |- t : G    (* and t strsub *)
        then G' |- t : G  and G' subcontext of G
        *)
      fun strengthen (I.Shift n (* = 0 *), I.Null) = I.Null
	| strengthen (I.Dot (I.Idx k (* k = 1 *), t), I.Decl (G, D)) =
              let 
		val t' = I.comp (t, I.invShift)
	      in
		(* G |- D dec *)
		(* G' |- t' : G *)
		(* G' |- D[t'] dec *)
		I.Decl (strengthen (t', G), I.decSub (D, t'))
	      end
	| strengthen (I.Dot (I.Undef, t), I.Decl (G, D)) = 
	      strengthen (t, G)
	| strengthen (I.Shift n, G) = 
	      strengthen (I.Dot (I.Idx (n+1), I.Shift (n+1)), G)
	| strengthen _ = raise Domain (* invariant violated *)


      (* boolean indicates whether to prune or not *)
      fun LFapplyInv2Exp (true, G, U, ss) = ((U.pruneExp (G, (U, I.id), ss, ref NONE)) handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ))
        | LFapplyInv2Exp (false, G, U, ss) = (U.invertExp (G, (U, I.id), ss, ref NONE)) handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ) | U.NotInvertible => raise Error ("Delphin Unification Failed:  NotInvertible")

      (* applyInv2Formula(b, G0, F, ss, rOccur) = F' where
       * G0 |- F wff
       * G |- ss : G0
       * and G |- F' wff 
       * Applies F to ss making sure it is defined and rOccur doesn't occur
       * NOTE:  ss *IS* an inverted substitution...
       * b is true when we want pruning, false otherwise.
       * Pruning means that we KNOW the solution must exist
       * while non-pruning means it may fail.
       *)
      fun applyInv2Formula (b, G, F, ss, rOccur) = applyInv2FormulaN (b, G, D.whnfF F, ss, rOccur)
      and applyInv2FormulaN (_, G, D.Top, ss, rOccur) = D.Top

	| applyInv2FormulaN (b, G, D.All(visible, D, F), ss, rOccur) = D.All(visible, applyInv2NormalDec(b, G, D, ss, rOccur),
							      applyInv2Formula(b, I.Decl(G, D.coerceDec (D.InstantiableDec D)), F, I.dot1 ss, rOccur))

	| applyInv2FormulaN (b, G, D.Exists(D, F), ss, rOccur) = D.Exists(applyInv2NormalDec(b, G, D, ss, rOccur),
							      applyInv2Formula(b, I.Decl(G, D.coerceDec (D.InstantiableDec D)), F, I.dot1 ss, rOccur))

	| applyInv2FormulaN (b, G, D.Nabla(D, F), ss, rOccur) = D.Nabla(applyInv2NewDec(b, G, D, ss, rOccur),
							      applyInv2Formula(b, I.Decl(G, D.coerceDec (D.NonInstantiableDec D)), F, I.dot1 ss, rOccur))

	| applyInv2FormulaN (b, G, D.FormList Flist, ss, rOccur) = D.FormList (applyInv2FormulaList(b, G, Flist, ss, rOccur))

	| applyInv2FormulaN (b, G, D.FClo _, ss, rOccur) = raise Domain (* not in whnf *)
	| applyInv2FormulaN (false, G, D.FVar ((GX, r, cnstrs), s), ss, rOccur) = 
	    if (rOccur = r) then raise Error "Delphin Unification (Inverting):  Variable occurrence"
	    else if W.isPatSub (s) then
	       let
		 val w = U.weakenSub (G, s, ss)
	       in
		 if W.isId w
		   then D.FVar((GX, r, cnstrs), I.comp(s,ss))
		 else
		   raise Error "Delphin Unification : Not Invertible"
	       end
	    else (* s not patsub *)
	      D.FVar ((GX, r, cnstrs), applyInv2Sub(false, G, s, ss, rOccur))

	| applyInv2FormulaN(true, G, FX as D.FVar ((GX, r, cnstrs), s), ss, rOccur) =
	  if (rOccur = r) then raise Error "Variable occurrence"
	  else if W.isPatSub (s) then
	       let
		 val w = U.weakenSub (G, s, ss)
	       in
		 if W.isId w
		   then D.FVar ((GX, r, cnstrs), I.comp(s,ss))
		 else
		   let
		     val wi = W.invert w
		     val GY = applyInv2Ctx (true, wi, GX, rOccur)
		     val rNew = ref NONE
		     val Yw = D.FVar ((GY, rNew, ref []), w)
		     val _ = instantiateFVar(r, Yw, !cnstrs)
		   in
		     D.FClo(Yw, I.comp(s, ss))
		   end
	       end
	       else (* s not patsub *)
                 (
		   D.FVar ((GX, r, cnstrs), applyInv2Sub(false, G, s, ss, rOccur))
		    handle Error _ => 
		      (* applyInv2Sub may fail.. 
		       * then we just add a constraint *)
		      let 
			val GY = applyInv2Ctx (true, ss, G, rOccur) (* prune or invert???  (true or false)*)
			val rNew = ref NONE
			val cnstrListNew = ref nil
			val Y = D.FVar ((GY, rNew, cnstrListNew), I.id)
			val Y = D.newFVar (GY)
			val newCnstr = ref (D.EqnF (G, FX, D.FClo(Y, W.invert ss)))
			val _ = addConstraint (cnstrs, newCnstr)
			val _ = addConstraint (cnstrListNew, newCnstr)
		      in
			Y
		      end		      
                 )


      and applyInv2Ctx (b, I.Shift n, I.Null, rOccur) = I.Null
	| applyInv2Ctx (b, I.Dot (I.Idx k, t), I.Decl (G, D), rOccur) =
            let 
	      val t' = I.comp (t, I.invShift)
	      val D' = applyInv2Dec (b, G, D, t', rOccur)
	    in
	      I.Decl (applyInv2Ctx (b, t', G, rOccur), D')
	    end
	| applyInv2Ctx (b, I.Dot (I.Undef, t), I.Decl (G, d), rOccur) = 
	    applyInv2Ctx (b, t, G, rOccur)
	| applyInv2Ctx (b, I.Shift n, G, rOccur) = 
	    applyInv2Ctx (b, I.Dot (I.Idx (n+1), I.Shift (n+1)), G, rOccur)
	| applyInv2Ctx _ = raise Domain
	    



      and applyInv2Sub (b, G, s as I.Shift (n), ss, rOccur) =
             if n < I.ctxLength (G) 
	       then applyInv2Sub (b, G, I.Dot (I.Idx (n+1), I.Shift (n+1)), ss, rOccur)
	     else I.comp (s, ss)		(* must be defined *)
	| applyInv2Sub (b, G, I.Dot (I.Idx (n), s'), ss, rOccur) =
	       (case I.bvarSub (n, ss)
		  of I.Undef => raise Error "Delphin Unification : Not ApplyInv2ible"
		| Ft => I.Dot (Ft, applyInv2Sub (b, G, s', ss, rOccur)))
	| applyInv2Sub (b, G, I.Dot (I.Exp (U), s'), ss, rOccur) =
		  I.Dot (I.Exp (LFapplyInv2Exp (b, G, U, ss)),
			 applyInv2Sub (b, G, s', ss, rOccur))
	| applyInv2Sub (b, G, I.Dot (I.Undef, s'), ss, rOccur) = 
		  I.Dot (I.Undef, applyInv2Sub (b, G, s', ss, rOccur))
	| applyInv2Sub _ = raise Domain

      (*
      and applyInv2Dec (b, G, D.InstantiableDec D, ss, rOccur) = D.InstantiableDec (applyInv2NormalDec (b, G, D, ss, rOccur))
	| applyInv2Dec (b, G, D.NonInstantiableDec D, ss, rOccur) = D.NonInstantiableDec (applyInv2NewDec (b, G, D, ss, rOccur))
	*)
      and applyInv2Dec (b, G, I.Dec(name, V), ss, rOccur) = I.Dec(name, LFapplyInv2Exp (b, G, V, ss))
	| applyInv2Dec (b, G, I.NDec, ss, rOccur) = I.NDec
	| applyInv2Dec _ = raise Domain

      and applyInv2NormalDec (b, G, D.NormalDec (sLO, T), ss, rOccur) = D.NormalDec (sLO, applyInv2Types(b, G, T, ss, rOccur))
	
      and applyInv2NewDec (b, G, D.NewDecLF (sO, A), ss, rOccur) = D.NewDecLF(sO, LFapplyInv2Exp(b, G,A,ss))
	| applyInv2NewDec (b, G, D.NewDecMeta (sO, F), ss, rOccur) = D.NewDecMeta(sO, applyInv2Formula(b, G,F,ss,rOccur))
	
      and applyInv2FormulaList(b, G, [], ss, rOccur) = []
	| applyInv2FormulaList(b, G, F::fs, ss, rOccur) = applyInv2Formula(b, G,F,ss,rOccur) :: applyInv2FormulaList(b, G,fs,ss,rOccur)
	
      and applyInv2Types (b, G, D.LF (isP, A), ss, rOccur) = D.LF(isP, LFapplyInv2Exp(b, G,A,ss))
	| applyInv2Types (b, G, D.Meta (isP, F), ss, rOccur) = D.Meta(isP, applyInv2Formula(b, G,F,ss,rOccur))
	

      (* ************************************************************************************************* *)
      (* ************************************************************************************************* *)
      (* applyInv2Exp(G, E, ss, rOccur) applies E to ss where ss is an inverted substitution *)
      (* G is the DOMAIN of ss *)
      fun applyInv2Exp(G, E, ss, rOccur) = (applyInv2ExpN(G, D.whnfE E, ss , rOccur)
					    handle D.SubstFailed => raise Error "Delphin Unification Failed:  Application to Inverted Substitution failed")
      and applyInv2ExpN (G, D.Var B, ss, rOccur) = (D.EClo(D.Var B, ss) 
                      handle D.SubstFailed => raise Error "Delphin Unification Failed:  Application to Inverted Substitution failed")
	| applyInv2ExpN (G, D.Quote M, ss, rOccur) = D.Quote (LFapplyInv2Exp(true, G, M, D.coerceSub ss))
	| applyInv2ExpN (G, D.Unit, ss, rOccur) = D.Unit
	| applyInv2ExpN (G, D.Lam (Clist, F), ss, rOccur) = 
			D.Lam (map (fn C => applyInv2Case(G, C, ss, rOccur)) Clist,
			       applyInv2Formula(true, G, F, D.coerceSub ss, ref NONE))
	| applyInv2ExpN (G, D.New (D, E), ss, rOccur) = 
			D.New (applyInv2NewDec(true, G, D, D.coerceSub ss, ref NONE),
			       applyInv2Exp(I.Decl(G,D.coerceDec(D.NonInstantiableDec D)), E, D.dot1 ss, rOccur))
	| applyInv2ExpN (G, D.App (visible, E1, E2), ss, rOccur) =
			D.App (visible, applyInv2Exp(G, E1, ss, rOccur),
			       applyInv2Exp(G, E2, ss, rOccur))
	| applyInv2ExpN (G, D.Pair (E1, E2, F), ss, rOccur) =
			D.Pair (applyInv2Exp(G, E1, ss, rOccur),
				applyInv2Exp(G, E2, ss, rOccur),
				applyInv2Formula(true, G, F, D.coerceSub ss, ref NONE))

		      | applyInv2ExpN (G, D.ExpList Elist, ss, rOccur) = D.ExpList(map (fn E => applyInv2Exp(G, E, ss, rOccur)) Elist)
	| applyInv2ExpN (G, D.Proj (E, i), ss, rOccur) =
			D.Proj (applyInv2Exp(G, E, ss, rOccur),i)
	| applyInv2ExpN (G, D.Pop(i, E), ss, rOccur) =
			let
			  val (j, t') = D.popSub(i, ss)
			  (* G',j..1 |- ss : G,i..1 By Assumption*)
			  (* G' |- t' : G *)
			  val E' = applyInv2Exp(D.popCtx(i, G), E, t', rOccur)
			in
			  D.Pop(j, E')
			end

	| applyInv2ExpN (G, D.Fix (D, E), ss, rOccur) =
			D.Fix (applyInv2NormalDec(true, G, D, D.coerceSub ss, ref NONE),
			       applyInv2Exp(I.Decl(G,D.coerceDec (D.InstantiableDec D)), E, D.dot1 ss, rOccur))

	| applyInv2ExpN (G, D.EVar (r, t), ss, rOccur) =
			if (r = rOccur) then
			  raise Error "Delphin Unification Failed:  Variable Occurence in applyInv2Exp"
			else D.EVar (r, applyInv2MetaSub(G, t, ss, rOccur))

	| applyInv2ExpN (G, D.EClo _, ss, rOccur) = raise Domain (* not in whnf *)

      (* G |- t : G'  and G'' |- ss : G *)
      and applyInv2MetaSub(G, t, D.Shift ss, rOccur) = D.Shift (applyInv2MetaSub(G, t, ss, rOccur))
	| applyInv2MetaSub(G, D.Dot(D.Undef, t), ss, rOccur) = D.Dot(D.Undef, applyInv2MetaSub(G, t, ss, rOccur))
	| applyInv2MetaSub(G, D.Dot(D.Prg E, t), ss, rOccur) = D.Dot(D.Prg (applyInv2Exp(G, E, ss, rOccur)),
							    applyInv2MetaSub(G, t, ss, rOccur))
	| applyInv2MetaSub(I.Decl(G,_), D.Shift t1, D.Dot(_, ss), rOccur) =
                                                      applyInv2MetaSub(G, t1, ss, rOccur)
	| applyInv2MetaSub(I.Decl(G,_), D.Shift t, id, rOccur) = D.Shift (applyInv2MetaSub(G, t, id, rOccur))
	| applyInv2MetaSub(G, D.id, ss, rOccur) = ss
	| applyInv2MetaSub(I.Null, D.Shift t1, _, rOccur) = raise Domain (* invariant broken *)

      
      and applyInv2Case(G, D.Eps(D,C), ss, rOccur) = D.Eps (applyInv2NormalDec(true, G, D, D.coerceSub ss, ref NONE),
						       applyInv2Case(I.Decl(G,D.coerceDec (D.InstantiableDec D)), C, 
								  D.dot1 ss, rOccur))
	| applyInv2Case(G, D.NewC(D,C), ss, rOccur) = D.NewC (applyInv2NewDec(true, G, D, D.coerceSub ss, ref NONE),
						       applyInv2Case(I.Decl(G,D.coerceDec (D.NonInstantiableDec D)), C,
								  D.dot1 ss, rOccur))
	| applyInv2Case(G, D.PopC(i,C), ss, rOccur) = 
	                let
			  val (j, t') = D.popSub(i, ss)
			  (* G',j..1 |- ss : G,i..1 By Assumption*)
			  (* G' |- t' : G *)
			  val C' = applyInv2Case(D.popCtx(i, G), C, t', rOccur)
			in
			  D.PopC(j, C')
			end

	| applyInv2Case(G, D.Match(E1,E2), ss, rOccur) = D.Match (applyInv2Exp(G, E1, ss, rOccur),
							     applyInv2Exp(G, E2, ss, rOccur))
	| applyInv2Case(G, D.MatchAnd(visible, E1,C), ss, rOccur) = D.MatchAnd (visible, applyInv2Exp(G, E1, ss, rOccur),
								  applyInv2Case(G, C, ss, rOccur))

      (* ************************************************************************************************* *)
      (* ************************************************************************************************* *)

      (* REMOVED.. not needed	 
        (* If T is a type,
         * and we want a new type T', such that T'[s] = T (for any s)
	 * then generalizeType returns such a T'
	 * We need this because we do not have type variables.. just formula variables.
	 *)
      fun generalizeType(G, D.Meta(isP, _)) = D.Meta(isP, D.newFVar(G))
	| generalizeType(G, D.LF(isP, V)) = 
	                let
			  val (A', _ (* Type *)) = Approx.classToApx V
			  val V' = Approx.apxToClass(G, A', Approx.Type, false)
			in
			  D.LF(isP, V')
			end

      fun generalizeNormalDec(G, D.NormalDec (sLO, T)) = D.NormalDec (sLO, generalizeType (G, T))
      fun generalizeNewDec (G, D.NewDecLF (sO, V)) =
	                let
			  val (A', _ (* Type *)) = Approx.classToApx V
			  val V' = Approx.apxToClass(G, A', Approx.Type, false)
			in
			  D.NewDecLF (sO, V')
			end
	| generalizeNewDec (G, D.NewDecMeta (sO, F)) = D.NewDecMeta(sO, D.newFVar(G))
       *)

      fun unifyVisibility (D.Visible, D.Visible) = ()
	| unifyVisibility (D.Implicit, D.Implicit) = ()
	(* Not needed
	| unifyVisibility (D.VisibleVar (r as (ref (SOME V1))), V2) = unifyVisibility (V1, V2)
	| unifyVisibility (D.VisibleVar (r as (ref NONE)), V2) = instantiateVisibleVar(r, V2)
	| unifyVisibility (V2, D.VisibleVar (r as (ref (SOME V1)))) = unifyVisibility (V2, V1)
	| unifyVisibility (V2, D.VisibleVar (r as (ref NONE))) = instantiateVisibleVar(r, V2)
	 *)
	| unifyVisibility _ = raise Error ("Delphin Unification Failed:  Incompatible types (w.r.t. implicitness)")

      fun unifyParam (D.Existential, D.Existential) = ()
	| unifyParam (D.Param, D.Param) = ()
	| unifyParam (D.PVar (r as ref (SOME P)), P2) = unifyParam (P, P2)
	| unifyParam (P2, D.PVar (r as ref (SOME P))) = unifyParam (P2, P)
	| unifyParam (D.PVar (r1 as ref NONE), P2 as D.PVar (r2 as ref NONE)) =  if (r1=r2) then () else instantiatePVar(r1, P2)
	| unifyParam (D.PVar (r1 as ref NONE), P2 as D.Existential) = instantiatePVar(r1, P2)
	| unifyParam (D.PVar (r1 as ref NONE), P2 as D.Param) = instantiatePVar(r1, P2)
	| unifyParam (P2 as D.Existential, D.PVar (r1 as ref NONE)) = instantiatePVar(r1, P2)
	| unifyParam (P2 as D.Param, D.PVar (r1 as ref NONE)) = instantiatePVar(r1, P2)
	| unifyParam _ = raise Error ("Delphin Unification Failed:  Incomaptible types (w.r.t. param status)")


      fun unifyTypes (G, D.LF (P1, A1), D.LF (P2, A2)) =
                   (unifyParam(P1, P2) ; (U.unify (G, (A1, I.id), (A2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s )))
	| unifyTypes (G, D.Meta (P1, F1), D.Meta (P2, F2)) =
		   (unifyParam(P1, P2) ; unifyFormula(G, F1, F2))
	| unifyTypes _ = raise Error ("Delphin Unification Failed:  Incompatible Types (LF vs Meta)")

      and unifyTypeList (G, [], []) = ()
	| unifyTypeList (G, T1::t1list, T2::t2list) = (unifyTypes(G, T1, T2) ; unifyTypeList(G, t1list, t2list))
	| unifyTypeList _ = raise Error "Delphin Unification Failed:  Type Lists incompatible"

      and unifyFormula (G, F1, F2) = unifyFormulaN (G, D.whnfF F1, D.whnfF F2)
      (* unifyFormulaN does not have any top-level instantiated FVars *)
      and unifyFormulaN (G, D.Top, D.Top) = ()
	| unifyFormulaN (G, D.All (visible1, D1, F1), D.All (visible2, D2, F2)) = 
	                                                     (unifyVisibility(visible1, visible2) ;
							      unifyNormalDec(G, D1,D2) ; 
							       unifyFormula(I.Decl(G, D.coerceDec (D.InstantiableDec D1)), F1, F2))
	| unifyFormulaN (G, D.Exists (D1, F1), D.Exists (D2, F2)) = (unifyNormalDec(G, D1,D2) ; 
								     unifyFormula(I.Decl(G, D.coerceDec (D.InstantiableDec D1)), F1, F2))
	| unifyFormulaN (G, D.Nabla (D1, F1), D.Nabla (D2, F2)) = (unifyNewDec(G, D1,D2) ; 
								   unifyFormula(I.Decl(G, D.coerceDec(D.NonInstantiableDec D1)), F1, F2))

	| unifyFormulaN (G, D.FormList [], D.FormList []) = ()
	| unifyFormulaN (G, D.FormList (F1::fs1), D.FormList (F2::fs2)) = (unifyFormula(G, F1, F2) ; unifyFormula(G, D.FormList fs1, D.FormList fs2))
	| unifyFormulaN (G, F1 as D.FVar ((G1, r1, cnstrs1), s1), F2 as D.FVar ((G2, r2, cnstrs2), s2)) =
		    if (r1 = r2) then
		      if (W.isPatSub(s1) andalso W.isPatSub(s2)) then
			    let
			      val s' = U.intersection(s1, s2)
			    in
			      if W.isId s' then ()
			      else 
				(* G |- s1 : GA
				 * G |- s2 : GB
				 * G |- s' : G''
				 *)
				(* WARNING:  I am not sure if this else clause is correct.. -ABP*)
				let val ss' = W.invert s'
				  val G1' = strengthen (ss', G1)
				in
				  instantiateFVar(r1, D.FClo(D.newFVar(G1'), s'), !cnstrs1)
				end
			    end
		      else 
			let
			  val newC = ref (D.EqnF (G, F1, F2))
			in
			  (* ADAM:  I think cnstrs1 and cnstrs2 will always
			   * be equal... but just in case we add to both.
			   * If they are the same, then it won't hurt to have it twice
			   * as it is a reference to the same thing
			   *)
			  (addConstraint (cnstrs1, newC) ; addConstraint (cnstrs2, newC))
			end

		    else
		      if W.isPatSub(s1) then
			let
			  val ss1 = W.invert s1
			  val F2' = applyInv2Formula(true, G, F2, ss1, r1)
			in
			  instantiateFVar(r1, F2', !cnstrs1)
			end
		      else if W.isPatSub(s2) then
			let
			  val ss2 = W.invert s2
			  val F1' = applyInv2Formula(true, G, F1, ss2, r2)
			in
			  instantiateFVar(r2, F1', !cnstrs2)
			end
		      else
			let 
			  val newC = ref (D.EqnF (G, F1, F2))
			  (* In Twelf they only add the constraint to one variable
			   * HOWEVER, we need it in both because
			   * if either side is assigned to "Top", then the other can be 
			   * determined to also be Top 
			   *)
			in
			  (addConstraint (cnstrs1, newC) ; addConstraint (cnstrs2, newC))
			end

        (* Top is "Top" under any substitution *)
	| unifyFormulaN (G, D.FVar ((_, r, cnstrs), _), D.Top) = 
			instantiateFVar(r, D.Top, !cnstrs)

	| unifyFormulaN (G, F1 as D.FVar ((_, r1, cnstrs), s1), F2 (* != D.Top *)) =
		   if (W.isPatSub s1) then
		     let
		       val ss = W.invert s1
		       val F2' = applyInv2Formula(true, G, F2, ss, r1)
		     in
		         instantiateFVar(r1, F2', !cnstrs)
		     end
		   else
		     addConstraint(cnstrs, ref (D.EqnF(G, F1, F2)))



	| unifyFormulaN (G, F1, F2 as D.FVar ((_, r2, cnstrs), s2)) =
		     unifyFormulaN(G, F2, F1) (* We handle the cases when FVar is on the left above *)


	| unifyFormulaN _ = raise Error ("Delphin Unification Failed:  Incompatible Formulas")



      and unifyDec (G, D.InstantiableDec D1, D.InstantiableDec D2) = unifyNormalDec(G, D1, D2)
	| unifyDec (G, D.NonInstantiableDec D1, D.NonInstantiableDec D2) = unifyNewDec(G, D1, D2)
	| unifyDec _ = raise Error ("Delphin Unification Failed:  Incompatible Dec classes (LF vs Meta)")

      and unifyNormalDec (G, D.NormalDec (_, T1), D.NormalDec (_, T2)) = unifyTypes(G, T1, T2)
      and unifyNewDec (G, D.NewDecLF (_, A1), D.NewDecLF(_, A2)) = 
                            (U.unify (G, (A1, I.id), (A2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ))
	| unifyNewDec (G, D.NewDecMeta (_, F1), D.NewDecMeta (_, F2)) = unifyFormula(G, F1, F2)
	| unifyNewDec (G, _, _) = raise Error "Delphin Unificatin Failed:  Incompatible New Decs"

    

      fun unifyExpList (G, [], []) = ()
	| unifyExpList (G, E1::E1list, E2::E2list) = (unifyExp(G, E1, E2) ; unifyExpList(G, E1list, E2list))
	| unifyExpList _ = raise Error "Delphin Unification Failed:  Incompatible Expression Lists"


      and unifyCase(G, D.Eps(D1, C1), D.Eps(D2, C2)) = (unifyNormalDec(G, D1, D2); unifyCase(I.Decl(G, D.coerceDec (D.InstantiableDec D1)), C1, C2))
	| unifyCase(G, D.NewC(D1, C1), D.NewC(D2, C2)) = (unifyNewDec(G, D1, D2); unifyCase(I.Decl(G, D.coerceDec (D.NonInstantiableDec D1)), C1, C2))
	| unifyCase(G, D.PopC(i, C1), D.PopC(j, C2)) = 
	                                            if (i=j) then
				                    unifyCase (D.popCtx(i, G), C1, C2)
						    else raise Error "Delphin Unificatin Failed:  Different Variable Access in Pop"
	| unifyCase(G, D.Match(E1a, E1b), D.Match(E2a, E2b)) = (unifyExp(G, E1a, E2a); unifyExp(G, E1b, E2b))
	| unifyCase(G, D.MatchAnd(visible1, E1a, E1b), D.MatchAnd(visible2, E2a, E2b)) = (unifyVisibility(visible1, visible2) ; 
											  unifyExp(G, E1a, E2a); unifyCase(G, E1b, E2b))
	| unifyCase _ = raise Error "Delphin Unification Failed:  Incompatible Case Statements"



      and unifyCaseList (G, [], []) = ()
	| unifyCaseList (G, C1::C1list, C2::C2list) = (unifyCase(G, C1, C2) ; unifyCaseList (G, C1list, C2list))
	| unifyCaseList _ = raise Error "Delphin Unification Failed:  Incompatible Case Lists"

      (* Precondition:  In whnf.. which is also guaranteed by whnfE. *)
      and unifyBVarsN(G, D.Fixed i, D.Fixed j) = if (i=j) then () else raise Error "Delphin Unification Failed:  Variable Clash"
	| unifyBVarsN(G, D.BVarMeta (r, s), D.Fixed k) = 
		 (case (D.findIndex(k, s))
		    of (SOME k') => (r := (SOME (D.Fixed k')))
		     | _ => raise Error "Bound variable (parameter) clash")
	       
	| unifyBVarsN(G, D.BVarLF (r, s), D.Fixed k) = 
		 (case (Whnf.findIndex(k, s))
		    of (SOME k') => (r := (SOME (I.Fixed k')))
		     | _ => raise Error "Bound variable (parameter) clash")

	| unifyBVarsN(G, B1 as D.Fixed i, B2 as D.BVarMeta (r, s)) = unifyBVarsN(G, B2, B1)
	| unifyBVarsN(G, B1 as D.Fixed k, B2 as D.BVarLF (r, s)) = unifyBVarsN (G, B2, B1)
	| unifyBVarsN(G, D.BVarMeta (r1, s1), D.BVarMeta (r2, s2)) = raise Error "ONLY support Matching for now..."
	| unifyBVarsN(G, D.BVarLF (r1, s1), D.BVarLF (r2, s2)) = raise Error "ONLY support Matching for now..."
	| unifyBVarsN _ = raise Error "Delphin Unification Failed:  BVars Clash"
	

      and  unifyExp (G, E1, E2) = (unifyExpN (G, D.whnfE E1, D.whnfE E2)
				   handle D.SubstFailed => raise Error "Delphin Unification Failed:  UNEXPECTED Failutre of whnf")
				   
      and unifyExpN (G, D.Var B1, D.Var B2) = unifyBVarsN(G, B1, B2)
	| unifyExpN (G, D.Quote M1, D.Quote M2) = (U.unify (G, (M1, I.id), (M2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ))
	| unifyExpN (G, D.Unit, D.Unit) = ()

	| unifyExpN (G, D.Lam (C1list, F1), D.Lam (C2list, F2)) = (unifyCaseList(G, C1list, C2list) ; unifyFormula(G, F1, F2))

	| unifyExpN (G, D.New (D1, E1), D.New (D2,E2)) = (unifyNewDec(G, D1, D2) ;
						       unifyExp(I.Decl(G, D.coerceDec(D.NonInstantiableDec D1)), E1, E2))
	| unifyExpN (G, D.App (visible1, E1, E2), D.App (visible2, E1', E2')) = (unifyVisibility(visible1, visible2) ; 
										 unifyExp(G, E1, E1') ; unifyExp(G, E2, E2'))

	| unifyExpN (G, D.Pair (E1, E2, F), D.Pair (E1', E2', F')) = (unifyExp(G, E1, E1') ; unifyExp(G, E2, E2') ; unifyFormula(G, F, F'))

	| unifyExpN (G, D.ExpList E1list, D.ExpList E2list) = unifyExpList(G, E1list, E2list)
	| unifyExpN (G, D.Proj (E1, i), D.Proj (E1', j)) = 
                              if (i=j) then unifyExp(G, E1, E1') else raise Error "Delphin Unificatin Failed:  Different Variable Access in Projection"

	| unifyExpN (G, D.Pop(i, E1), D.Pop(j, E2)) = if (i=j) then
				                    unifyExp (D.popCtx(i, G), E1, E2)
						    else raise Error "Delphin Unificatin Failed:  Different Variable Access in Pop"

	| unifyExpN (G, D.Fix (D1, E1), D.Fix (D2,E2)) = (unifyNormalDec(G, D1, D2) ;
						       unifyExp(I.Decl(G, D.coerceDec (D.InstantiableDec D1)), E1, E2))

	| unifyExpN (G, D.EVar (r1, t1), E2 as D.EVar (r2, t2)) =
	       let 
		 val s1 = numShifts t1 (* Raises error if t1 is not a shift substitution *)
		 val s2 = numShifts t2 (* Raises error if t2 is not a shift substitution *)
	       in
		 if (r1 = r2) then if (s1=s2) then () else raise Error "Delphin Unification Failure:  Same Meta-Level EVar under different substitution"
		 else if (s1 > s2) then (* r2 = r1[s1-s2] *)
		                        instantiateEVar(r2, D.EVar(r1, D.shiftTo(s1-s2, D.id)))
		      else
			(* r1 = r2[s2-s1] *)
			instantiateEVar(r1, D.EVar(r2, D.shiftTo(s2-s1, D.id)))
	       end
	| unifyExpN (G, D.EVar (r1, t1), E2) =
	       let
		 val s1 = numShifts t1 (* Raises error if t1 is not a shift substitution *)
		 val t1Inv = invertShiftSub(s1)
	         (* G |- t1 : G0 *)
	         (* G0 |- t1Inv : G *)
		 val E2' = applyInv2Exp(G, E2, t1Inv, r1)
	       in
		 instantiateEVar(r1, E2')
	       end


	| unifyExpN (G, E1, D.EVar r2) = unifyExpN(G, D.EVar r2, E1)


	| unifyExpN _ = raise Error "Delphin Unification Failed:  Expressions incompatible"

 
    (* Tie it together to use constraints *)

      fun awakeCnstr (NONE) = ()
	| awakeCnstr (SOME(ref D.Solved)) = awakeCnstr (nextCnstr ())
	| awakeCnstr (SOME(cnstr as ref (D.EqnF (G, F1, F2)))) =
          (solveConstraint cnstr;
           unifyF' (G, F1, F2))

      and unifyF' (G, F1, F2) =
          (unifyFormula (G, F1, F2); awakeCnstr (nextCnstr ()))

      and unifyT' (G, T1, T2) =
          (unifyTypes (G, T1, T2); awakeCnstr (nextCnstr ()))


    in
      fun unifyF (G, F1, F2) = 
	(resetAwakenCnstrs (); unifyF' (G, F1, F2))

      fun unifyT (G, T1, T2) = 
	(resetAwakenCnstrs (); unifyT' (G, T1, T2))


      fun unifyE (G, E1, E2) = unifyExp(G, E1, E2)	
      fun unifyP (P1, P2) = unifyParam(P1, P2)

	
      val reset = reset
      val mark = mark
      val unwind = unwind

    end

  end 