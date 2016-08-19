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
      | InstantiateBLF of I.BoundVar option ref
      | InstantiateBMeta of D.BoundVar option ref
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
	| undo (InstantiateBLF refB) =
	    (refB := NONE)
	| undo (InstantiateBMeta refB) =
	    (refB := NONE)
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

	fun instantiateBVarLF (refB, B, cnstrL) =
            (
              refB := SOME(B);
              Trail.log (globalTrail, InstantiateBLF (refB));
	      awakenCnstrs := cnstrL @ !awakenCnstrs
            )

	fun instantiateBVarMeta (refB, B) =
            (
              refB := SOME(B);
              Trail.log (globalTrail, InstantiateBMeta (refB))
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
      fun LFapplyInv2Exp (true, Gglobal, G, U, ss) = ((U.pruneExp (Gglobal, G, (U, I.id), ss, ref NONE)) handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ))
        | LFapplyInv2Exp (false, Gglobal, G, U, ss) = (U.invertExp (Gglobal, G, (U, I.id), ss, ref NONE)) handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ) | U.NotInvertible => raise Error ("Delphin Unification Failed:  NotInvertible")

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
      fun applyInv2Formula (b, Gglobal, G, F, ss, rOccur) = applyInv2FormulaN (b, Gglobal, G, D.whnfF F, ss, rOccur)
      and applyInv2FormulaN (_, Gglobal, G, D.Top, ss, rOccur) = D.Top

	| applyInv2FormulaN (b, Gglobal, G, D.All(Ds, F), ss, rOccur) = 
	              let
			fun applyInv2Decs ([], G, t) = ([], G, t)
			  | applyInv2Decs ((visibility, D) :: Ds, G, t) = 
			    let
			      val D' = applyInv2NormalDec(b, Gglobal, G, D, t, rOccur)
			      val (Ds', G', t') = applyInv2Decs (Ds, I.Decl(G, D.coerceDec (D.InstantiableDec D)), I.dot1 t)
			    in
			      ((visibility, D') :: Ds', G', t')
			    end
			val (Ds', G', ss') = applyInv2Decs (Ds, G, ss)
		      in	   
			D.All(Ds',
			      applyInv2Formula(b, Gglobal, G', F, ss', rOccur))
		      end


	| applyInv2FormulaN (b, Gglobal, G, D.Exists(D, F), ss, rOccur) = D.Exists(applyInv2NormalDec(b, Gglobal, G, D, ss, rOccur),
							      applyInv2Formula(b, Gglobal, I.Decl(G, D.coerceDec (D.InstantiableDec D)), F, I.dot1 ss, rOccur))

	| applyInv2FormulaN (b, Gglobal, G, D.Nabla(D, F), ss, rOccur) = D.Nabla(applyInv2NewDec(b, Gglobal, G, D, ss, rOccur),
							      applyInv2Formula(b, Gglobal, I.Decl(G, D.coerceDec (D.NonInstantiableDec D)), F, I.dot1 ss, rOccur))

	| applyInv2FormulaN (b, Gglobal, G, D.FormList Flist, ss, rOccur) = D.FormList (applyInv2FormulaList(b, Gglobal, G, Flist, ss, rOccur))

	| applyInv2FormulaN (b, Gglobal, G, D.FClo _, ss, rOccur) = raise Domain (* not in whnf *)
	| applyInv2FormulaN (false, Gglobal, G, D.FVar ((GX, r, cnstrs), s), ss, rOccur) = 
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
	      D.FVar ((GX, r, cnstrs), applyInv2Sub(false, Gglobal, G, s, ss, rOccur))

	| applyInv2FormulaN(true, Gglobal, G, FX as D.FVar ((GX, r, cnstrs), s), ss, rOccur) =
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
		     val GY = applyInv2Ctx (true, Gglobal, wi, GX, rOccur)
		     val rNew = ref NONE
		     val Yw = D.FVar ((GY, rNew, ref []), w)
		     val _ = instantiateFVar(r, Yw, !cnstrs)
		   in
		     D.FClo(Yw, I.comp(s, ss))
		   end
	       end
	       else (* s not patsub *)
                 (
		   D.FVar ((GX, r, cnstrs), applyInv2Sub(false, Gglobal, G, s, ss, rOccur))
		    handle Error _ => 
		      (* applyInv2Sub may fail.. 
		       * then we just add a constraint *)
		      let 
			val GY = applyInv2Ctx (true, Gglobal, ss, G, rOccur) (* prune or invert???  (true or false)*)
			val rNew = ref NONE
			val cnstrListNew = ref nil
			val Y = D.FVar ((GY, rNew, cnstrListNew), I.id)
			val Y = D.newFVar (GY)
			val newCnstr = ref (D.EqnF (Gglobal, G, FX, D.FClo(Y, W.invert ss)))
			val _ = addConstraint (cnstrs, newCnstr)
			val _ = addConstraint (cnstrListNew, newCnstr)
		      in
			Y
		      end		      
                 )


      and applyInv2Ctx (b, Gglobal, I.Shift n, I.Null, rOccur) = I.Null
	| applyInv2Ctx (b, Gglobal, I.Dot (I.Idx k, t), I.Decl (G, D), rOccur) =
            let 
	      val t' = I.comp (t, I.invShift)
	      val D' = applyInv2Dec (b, Gglobal, G, D, t', rOccur)
	    in
	      I.Decl (applyInv2Ctx (b, Gglobal, t', G, rOccur), D')
	    end
	| applyInv2Ctx (b, Gglobal, I.Dot (I.Undef, t), I.Decl (G, d), rOccur) = 
	    applyInv2Ctx (b, Gglobal, t, G, rOccur)
	| applyInv2Ctx (b, Gglobal, I.Shift n, G, rOccur) = 
	    applyInv2Ctx (b, Gglobal, I.Dot (I.Idx (n+1), I.Shift (n+1)), G, rOccur)
	| applyInv2Ctx _ = raise Domain
	    



      and applyInv2Sub (b, Gglobal, G, s as I.Shift (n), ss, rOccur) =
             if n < I.ctxLength (G) 
	       then applyInv2Sub (b, Gglobal, G, I.Dot (I.Idx (n+1), I.Shift (n+1)), ss, rOccur)
	     else I.comp (s, ss)		(* must be defined *)
	| applyInv2Sub (b, Gglobal, G, I.Dot (I.Idx (n), s'), ss, rOccur) =
	       (case I.bvarSub (n, ss)
		  of I.Undef => raise Error "Delphin Unification : Not ApplyInv2ible"
		| Ft => I.Dot (Ft, applyInv2Sub (b, Gglobal, G, s', ss, rOccur)))
	| applyInv2Sub (b, Gglobal, G, I.Dot (I.Exp (U), s'), ss, rOccur) =
		  I.Dot (I.Exp (LFapplyInv2Exp (b, Gglobal, G, U, ss)),
			 applyInv2Sub (b, Gglobal, G, s', ss, rOccur))
	| applyInv2Sub (b, Gglobal, G, I.Dot (I.Undef, s'), ss, rOccur) = 
		  I.Dot (I.Undef, applyInv2Sub (b, Gglobal, G, s', ss, rOccur))
	| applyInv2Sub _ = raise Domain

      (*
      and applyInv2Dec (b, Gglobal, G, D.InstantiableDec D, ss, rOccur) = D.InstantiableDec (applyInv2NormalDec (b, Gglobal, G, D, ss, rOccur))
	| applyInv2Dec (b, Gglobal, G, D.NonInstantiableDec D, ss, rOccur) = D.NonInstantiableDec (applyInv2NewDec (b, Gglobal, G, D, ss, rOccur))
	*)
      and applyInv2Dec (b, Gglobal, G, I.Dec(name, V), ss, rOccur) = I.Dec(name, LFapplyInv2Exp (b, Gglobal, G, V, ss))
	| applyInv2Dec (b, Gglobal, G, I.NDec, ss, rOccur) = I.NDec
	| applyInv2Dec _ = raise Domain

      and applyInv2NormalDec (b, Gglobal, G, D.NormalDec (sLO, T), ss, rOccur) = D.NormalDec (sLO, applyInv2Types(b, Gglobal, G, T, ss, rOccur))
	
      and applyInv2NewDec (b, Gglobal, G, D.NewDecLF (sO, A), ss, rOccur) = D.NewDecLF(sO, LFapplyInv2Exp(b, Gglobal,G,A,ss))
	| applyInv2NewDec (b, Gglobal, G, D.NewDecWorld (sO, W), ss, rOccur) = D.NewDecWorld(sO, W)
	
      and applyInv2FormulaList(b,Gglobal, G, [], ss, rOccur) = []
	| applyInv2FormulaList(b,Gglobal, G, F::fs, ss, rOccur) = applyInv2Formula(b,Gglobal,G,F,ss,rOccur) :: applyInv2FormulaList(b,Gglobal,G,fs,ss,rOccur)
	
      and applyInv2Types (b, Gglobal, G, D.LF (isP, A), ss, rOccur) = D.LF(isP, LFapplyInv2Exp(b, Gglobal,G,A,ss))
	| applyInv2Types (b, Gglobal, G, D.Meta (F), ss, rOccur) = D.Meta(applyInv2Formula(b,Gglobal,G,F,ss,rOccur))
	

      (* ************************************************************************************************* *)
      (* ************************************************************************************************* *)
      (* applyInv2Exp(Gglobal, G, E, ss, rOccur) applies E to ss where ss is an inverted substitution *)
      (* G is the DOMAIN of ss *)
      fun applyInv2Exp(Gglobal, G, E, ss, rOccur) = (applyInv2ExpN(Gglobal, G, D.whnfE E, ss , rOccur)
					    handle D.SubstFailed => raise Error "Delphin Unification Failed:  Application to Inverted Substitution failed")
      and applyInv2ExpN (Gglobal, G, D.Var B, ss, rOccur) = D.whnfE(D.EClo(D.Var B, ss) 
                      handle D.SubstFailed => raise Error "Delphin Unification Failed:  Application to Inverted Substitution failed")
	| applyInv2ExpN (Gglobal, G, D.Quote M, ss, rOccur) = D.Quote (LFapplyInv2Exp(true, Gglobal, G, M, D.coerceSub ss))
	| applyInv2ExpN (Gglobal, G, D.Unit, ss, rOccur) = D.Unit
	| applyInv2ExpN (Gglobal, G, D.Lam (Clist, F, fileInfo), ss, rOccur) = 
			D.Lam (map (fn C => applyInv2Case(Gglobal, G, C, ss, rOccur)) Clist,
			       applyInv2Formula(true, Gglobal, G, F, D.coerceSub ss, ref NONE),
			       fileInfo)
	| applyInv2ExpN (Gglobal, G, D.New (D, E, fileInfo), ss, rOccur) = 
			D.New (applyInv2NewDec(true, Gglobal, G, D, D.coerceSub ss, ref NONE),
			       applyInv2Exp(Gglobal, I.Decl(G,D.coerceDec(D.NonInstantiableDec D)), E, D.dot1 (ss, fileInfo), rOccur), fileInfo)
	| applyInv2ExpN (Gglobal, G, D.App (E1, args), ss, rOccur) =
			D.App (applyInv2Exp(Gglobal, G, E1, ss, rOccur),
			       map (fn (visible, fileInfo, E2) => (visible, fileInfo, applyInv2Exp(Gglobal, G, E2, ss, rOccur))) args)

	| applyInv2ExpN (Gglobal, G, D.Pair (E1, E2, F), ss, rOccur) =
			D.Pair (applyInv2Exp(Gglobal, G, E1, ss, rOccur),
				applyInv2Exp(Gglobal, G, E2, ss, rOccur),
				applyInv2Formula(true, Gglobal, G, F, D.coerceSub ss, ref NONE))

		      | applyInv2ExpN (Gglobal, G, D.ExpList Elist, ss, rOccur) = D.ExpList(map (fn E => applyInv2Exp(Gglobal, G, E, ss, rOccur)) Elist)
	| applyInv2ExpN (Gglobal, G, D.Proj (E, i), ss, rOccur) =
			D.Proj (applyInv2Exp(Gglobal, G, E, ss, rOccur),i)
	| applyInv2ExpN (Gglobal, G, D.Pop(i, E, fileInfo), ss, rOccur) =
			let
			  val (j, t') = D.popSub(i, ss)
			  (* G',j..1 |- ss : G,i..1 By Assumption*)
			  (* G' |- t' : G *)
			  val E' = applyInv2Exp(Gglobal, D.popCtxLF(i, G), E, t', rOccur)
			in
			  D.Pop(j, E', fileInfo)
			end

	| applyInv2ExpN (Gglobal, G, D.Fix (D, E), ss, rOccur) =
			D.Fix (applyInv2NormalDec(true, Gglobal, G, D, D.coerceSub ss, ref NONE),
			       applyInv2Exp(Gglobal, I.Decl(G,D.coerceDec (D.InstantiableDec D)), E, D.dot1 (ss, NONE), rOccur))


	| applyInv2ExpN (Gglobal, G, D.EVar ((r,F), t), ss, rOccur) =
			if (r = rOccur) then
			  raise Error "Delphin Unification Failed:  Variable Occurence in applyInv2Exp"
			else D.EVar ((r,F), applyInv2MetaSub(Gglobal, G, t, ss, rOccur))

	| applyInv2ExpN (Gglobal, G, D.EClo _, ss, rOccur) = raise Domain (* not in whnf *)

      (* G |- t : G'  and G'' |- ss : G *)
      and applyInv2MetaSub(Gglobal, G, t, D.Shift ss, rOccur) = D.Shift (applyInv2MetaSub(Gglobal, G, t, ss, rOccur))
	| applyInv2MetaSub(Gglobal, G, D.Dot(D.Undef, t), ss, rOccur) = D.Dot(D.Undef, applyInv2MetaSub(Gglobal, G, t, ss, rOccur))
	| applyInv2MetaSub(Gglobal, G, D.Dot(D.Prg E, t), ss, rOccur) = D.Dot(D.Prg (applyInv2Exp(Gglobal, G, E, ss, rOccur)),
							    applyInv2MetaSub(Gglobal, G, t, ss, rOccur))
	| applyInv2MetaSub(Gglobal, I.Decl(G,_), D.Shift t1, D.Dot(_, ss), rOccur) =
                                                      applyInv2MetaSub(Gglobal, G, t1, ss, rOccur)
	| applyInv2MetaSub(Gglobal, I.Decl(G,_), D.Shift t, id, rOccur) = D.Shift (applyInv2MetaSub(Gglobal, G, t, id, rOccur))
	| applyInv2MetaSub(Gglobal, G, D.id, ss, rOccur) = ss
	| applyInv2MetaSub(Gglobal, I.Null, D.Shift t1, _, rOccur) = raise Domain (* invariant broken *)

      
      and applyInv2Case(Gglobal, G, D.Eps(D,C,fileInfo), ss, rOccur) = D.Eps (applyInv2NormalDec(true, Gglobal, G, D, D.coerceSub ss, ref NONE),
						       applyInv2Case(Gglobal, I.Decl(G,D.coerceDec (D.InstantiableDec D)), C, 
								  D.dot1 (ss, fileInfo), rOccur), fileInfo)
	| applyInv2Case(Gglobal, G, D.NewC(D,C, fileInfo), ss, rOccur) = D.NewC (applyInv2NewDec(true, Gglobal, G, D, D.coerceSub ss, ref NONE),
						       applyInv2Case(Gglobal, I.Decl(G,D.coerceDec (D.NonInstantiableDec D)), C,
								  D.dot1 (ss, fileInfo), rOccur), fileInfo)
	| applyInv2Case(Gglobal, G, D.PopC(i,C), ss, rOccur) = 
	                let
			  val (j, t') = D.popSub(i, ss)
			  (* G',j..1 |- ss : G,i..1 By Assumption*)
			  (* G' |- t' : G *)
			  val C' = applyInv2Case(Gglobal, D.popCtxLF(i, G), C, t', rOccur)
			in
			  D.PopC(j, C')
			end

	| applyInv2Case(Gglobal, G, D.Match(pats,E2), ss, rOccur) = D.Match (map (fn (visible, E1) => (visible, applyInv2Exp(Gglobal, G, E1, ss, rOccur))) pats,
									     applyInv2Exp(Gglobal, G, E2, ss, rOccur))

      (* ************************************************************************************************* *)
      (* ************************************************************************************************* *)


				
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


      fun unifyTypes (Gglobal, G, D.LF (P1, A1), D.LF (P2, A2)) =
                   (unifyParam(P1, P2) ; (U.unifyG (Gglobal, G, (A1, I.id), (A2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s )))
	| unifyTypes (Gglobal, G, D.Meta (F1), D.Meta (F2)) =
		   (unifyFormula(Gglobal, G, F1, F2))
	| unifyTypes _ = raise Error ("Delphin Unification Failed:  Incompatible Types (LF vs Meta)")

      and unifyTypeList (Gglobal, G, [], []) = ()
	| unifyTypeList (Gglobal, G, T1::t1list, T2::t2list) = (unifyTypes(Gglobal, G, T1, T2) ; unifyTypeList(Gglobal, G, t1list, t2list))
	| unifyTypeList _ = raise Error "Delphin Unification Failed:  Type Lists incompatible"

      and unifyFormula (Gglobal, G, F1, F2) = unifyFormulaN (Gglobal, G, D.whnfF F1, D.whnfF F2)
      (* unifyFormulaN does not have any top-level instantiated FVars *)
      and unifyFormulaN (Gglobal, G, D.Top, D.Top) = ()
	| unifyFormulaN (Gglobal, G, D.All (D1s, F1), D.All (D2s, F2)) = 
	              let
			fun unifyDecs ([], [], G) = G
			  | unifyDecs ((visibility1, D1) :: D1s, (visibility2, D2) :: D2s, G) = 
			          let
				    val _ = unifyVisibility (visibility1, visibility2)
				    val _ = unifyNormalDec(Gglobal, G, D1, D2)
				  in
				    unifyDecs (D1s, D2s, I.Decl(G, D.coerceDec (D.InstantiableDec D1)))
				  end
			  | unifyDecs _ = raise Error ("Delphin Unification Failed:  Incompatible Decs (number of arguments)")

			val G' = unifyDecs (D1s, D2s, G)
		      in
			 unifyFormula(Gglobal, G', F1, F2)
		      end

	| unifyFormulaN (Gglobal, G, D.Exists (D1, F1), D.Exists (D2, F2)) = (unifyNormalDec(Gglobal, G, D1,D2) ; 
								     unifyFormula(Gglobal, I.Decl(G, D.coerceDec (D.InstantiableDec D1)), F1, F2))
	| unifyFormulaN (Gglobal, G, D.Nabla (D1, F1), D.Nabla (D2, F2)) = (unifyNewDec(Gglobal, G, D1,D2) ; 
								   unifyFormula(Gglobal, I.Decl(G, D.coerceDec(D.NonInstantiableDec D1)), F1, F2))

	| unifyFormulaN (Gglobal, G, D.FormList [], D.FormList []) = ()
	| unifyFormulaN (Gglobal, G, D.FormList (F1::fs1), D.FormList (F2::fs2)) = (unifyFormula(Gglobal, G, F1, F2) ; unifyFormula(Gglobal, G, D.FormList fs1, D.FormList fs2))
	| unifyFormulaN (Gglobal, G, F1 as D.FVar ((G1, r1, cnstrs1), s1), F2 as D.FVar ((G2, r2, cnstrs2), s2)) =
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
			  val newC = ref (D.EqnF (Gglobal, G, F1, F2))
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
			  val F2' = applyInv2Formula(true, Gglobal, G, F2, ss1, r1)
			in
			  instantiateFVar(r1, F2', !cnstrs1)
			end
		      else if W.isPatSub(s2) then
			let
			  val ss2 = W.invert s2
			  val F1' = applyInv2Formula(true, Gglobal, G, F1, ss2, r2)
			in
			  instantiateFVar(r2, F1', !cnstrs2)
			end
		      else
			let 
			  val newC = ref (D.EqnF (Gglobal, G, F1, F2))
			  (* In Twelf they only add the constraint to one variable
			   * HOWEVER, we need it in both because
			   * if either side is assigned to "Top", then the other can be 
			   * determined to also be Top 
			   *)
			in
			  (addConstraint (cnstrs1, newC) ; addConstraint (cnstrs2, newC))
			end

        (* Top is "Top" under any substitution *)
	| unifyFormulaN (Gglobal, G, D.FVar ((_, r, cnstrs), _), D.Top) = 
			instantiateFVar(r, D.Top, !cnstrs)

	| unifyFormulaN (Gglobal, G, D.Top, D.FVar ((_, r, cnstrs), _)) = 
			instantiateFVar(r, D.Top, !cnstrs)

	| unifyFormulaN (Gglobal, G, F1 as D.FVar ((_, r1, cnstrs), s1), F2 (* != D.Top *)) =
		   if (W.isPatSub s1) then
		     let
		       val ss = W.invert s1
		       val F2' = applyInv2Formula(true, Gglobal, G, F2, ss, r1)
		     in
		         instantiateFVar(r1, F2', !cnstrs)
		     end
		   else
		     addConstraint(cnstrs, ref (D.EqnF(Gglobal, G, F1, F2)))

	| unifyFormulaN (Gglobal, G, F2 (* != D.Top *), F1 as D.FVar ((_, r1, cnstrs), s1) (* != D.Top *)) =
		   if (W.isPatSub s1) then
		     let
		       val ss = W.invert s1
		       val F2' = applyInv2Formula(true, Gglobal, G, F2, ss, r1)
		     in
		         instantiateFVar(r1, F2', !cnstrs)
		     end
		   else
		     addConstraint(cnstrs, ref (D.EqnF(Gglobal, G, F1, F2)))




	| unifyFormulaN _ = raise Error ("Delphin Unification Failed:  Incompatible Formulas")



      and unifyDec (Gglobal, G, D.InstantiableDec D1, D.InstantiableDec D2) = unifyNormalDec(Gglobal, G, D1, D2)
	| unifyDec (Gglobal, G, D.NonInstantiableDec D1, D.NonInstantiableDec D2) = unifyNewDec(Gglobal, G, D1, D2)
	| unifyDec _ = raise Error ("Delphin Unification Failed:  Incompatible Dec classes (LF vs Meta)")

      and unifyNormalDec (Gglobal, G, D.NormalDec (_, T1), D.NormalDec (_, T2)) = unifyTypes(Gglobal, G, T1, T2)
      and unifyNewDec (Gglobal, G, D.NewDecLF (_, A1), D.NewDecLF(_, A2)) = 
                            (U.unifyG (Gglobal, G, (A1, I.id), (A2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ))
	| unifyNewDec (Gglobal, G, D.NewDecWorld (_, W1), D.NewDecWorld (_, W2)) = 
			          if WorldSubsumption.worldSubsume (W1, W2) andalso WorldSubsumption.worldSubsume (W2, W1)
				    then ()
				  else raise Error ("Delphin Unification Failed:  Incompatible Worlds (not equal)")

	| unifyNewDec (Gglobal, G, _, _) = raise Error "Delphin Unificatin Failed:  Incompatible New Decs"

    

      fun unifyExpList (Gglobal, G, [], []) = ()
	| unifyExpList (Gglobal, G, E1::E1list, E2::E2list) = (unifyExp(Gglobal, G, E1, E2) ; unifyExpList(Gglobal, G, E1list, E2list))
	| unifyExpList _ = raise Error "Delphin Unification Failed:  Incompatible Expression Lists"


      and unifyCase(Gglobal, G, D.Eps(D1, C1, fileInfo1), D.Eps(D2, C2, fileInfo2)) = (unifyNormalDec(Gglobal, G, D1, D2); unifyCase(Gglobal, I.Decl(G, D.coerceDec (D.InstantiableDec D1)), C1, C2))
	| unifyCase(Gglobal, G, D.NewC(D1, C1, fileInfo1), D.NewC(D2, C2, fileInfo2)) = (unifyNewDec(Gglobal, G, D1, D2); unifyCase(Gglobal, I.Decl(G, D.coerceDec (D.NonInstantiableDec D1)), C1, C2))
	| unifyCase(Gglobal, G, D.PopC(i, C1), D.PopC(j, C2)) = 
	                                            if (i=j) then
				                    unifyCase (Gglobal, D.popCtxLF(i, G), C1, C2)
						    else raise Error "Delphin Unificatin Failed:  Different Variable Access in Pop"
	| unifyCase(Gglobal, G, D.Match(patsA, E1b), D.Match(patsB, E2b)) = 
			let
			  fun unifyExps ((visible1, E1a)::patsA, (visible2, E2a)::patsB) = (unifyVisibility(visible1, visible2);
											    unifyExp(Gglobal, G, E1a, E2a);
											    unifyExps(patsA, patsB))
			    | unifyExps ([], []) = ()
			    | unifyExps _ = raise Error ("Delphin Unification Failed:  Incompatible Decs (number of arguments)")
			in
			  (unifyExps(patsA, patsB) ;  unifyExp(Gglobal, G, E1b, E2b))
			end

	| unifyCase _ = raise Error "Delphin Unification Failed:  Incompatible Case Statements"



      and unifyCaseList (Gglobal, G, [], []) = ()
	| unifyCaseList (Gglobal, G, C1::C1list, C2::C2list) = (unifyCase(Gglobal, G, C1, C2) ; unifyCaseList (Gglobal, G, C1list, C2list))
	| unifyCaseList _ = raise Error "Delphin Unification Failed:  Incompatible Case Lists"

      (* Precondition:  In whnf.. which is also guaranteed by whnfE. *)
      and unifyBVarsN(Gglobal, G, D.Fixed i, D.Fixed j) = if (i=j) then () else raise Error "Delphin Unification Failed:  Variable Clash"

	(* removed BVarMeta
	| unifyBVarsN(Gglobal, G, D.BVarMeta ((r, F'), s), D.Fixed k) = raise Domain (* do not handle meta-level parameters yet... *)
	  (*
	       let
		 val F = case (I.ctxLookup(mergeCtx(Gglobal, G), k))
		         of D.Meta(_, F) => F
			  | _ => raise Domain

		 val _ = unifyFormula(G, D.FClo(F, I.Shift k), D.FClo(F', D.coerceSub s))
	       in
		 (case (D.findIndex(k, s))
		    of (SOME k') => instantiateBVarMeta(r, D.Fixed k')
		     | _ => raise Error "Bound variable (parameter) clash")
	       end
	    *)
        
	| unifyBVarsN(Gglobal, G, D.Fixed k, D.BVarMeta ((r, F'), s)) = raise Domain (* do not handle meta-level parameters yet... *)

	| unifyBVarsN(Gglobal, G, D.BVarMeta ((r1, F1), s1), D.BVarMeta ((r2, F2), s2)) = raise Domain (*  raise Error "ONLY support Matching for now..." *)

	*)
	       
	| unifyBVarsN(Gglobal, G, D.BVarLF ((r, A', list,cnstrs), s), D.Fixed k) = 
	       let
		 val B = I.BVarVar ((r, A', list, cnstrs), s)
	       in
		 U.unifyG (Gglobal, G, (I.Root(I.BVar B, I.Nil), I.id), (I.Root(I.BVar (I.Fixed k), I.Nil), I.id))
		    handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s )
	       end

	| unifyBVarsN(Gglobal, G, D.Fixed k, D.BVarLF ((r, A', list,cnstrs), s)) = 
	       let
		 val B = I.BVarVar ((r, A', list, cnstrs), s)
	       in
		 U.unifyG (Gglobal, G, (I.Root(I.BVar B, I.Nil), I.id), (I.Root(I.BVar (I.Fixed k), I.Nil), I.id))
		    handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s )
	       end
	     

	| unifyBVarsN(Gglobal, G, B1 as D.BVarLF ((rA, typeA, listA, cnstrsA), sA), B2 as D.BVarLF ((rB, typeB, listB, cnstrsB), sB)) = (* rA and rB are both ref NONE *)
		    let
		      val B1LF = I.BVarVar((rA, typeA, listA, cnstrsA), sA)
		      val B2LF = I.BVarVar((rB, typeB, listB, cnstrsB), sB)
		    in
		      U.unifyG (Gglobal, G, (I.Root(I.BVar B1LF, I.Nil), I.id), (I.Root(I.BVar B2LF, I.Nil), I.id))
		        handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s )
		    end

	(*
	| unifyBVarsN _ = raise Error "Delphin Unification Failed:  BVars Clash"
	  *)

      and  unifyExp (Gglobal, G, E1, E2) = (unifyExpN (Gglobal, G, D.whnfE E1, D.whnfE E2)
				   handle D.SubstFailed => raise Error "Delphin Unification Failed:  UNEXPECTED Failure of whnf")
				   
      and unifyExpN (Gglobal, G, D.Var (B1, fileInfo1), D.Var (B2, fileInfo2)) = unifyBVarsN(Gglobal, G, B1, B2)

	(* The formal system does not allow us to access a variable of type A using "Var", but the implementation may...
	 * so we need to check if it is equal to what is on the LF level *)
	| unifyExpN (Gglobal, G, D.Var (B1, fileInfo1), E2 as D.Quote _) = 
	      (case (D.coerceBoundVar B1)
		 of(* NONE => raise Error "Delphin Unification Failed:  Incompatible Var"
		  | SOME *) U1 => unifyExp(Gglobal, G, D.Quote U1, E2))

	| unifyExpN (Gglobal, G, E1 as D.Quote _, D.Var (B1, fileInfo1)) = 
	      (case (D.coerceBoundVar B1)
		 of (* NONE => raise Error "Delphin Unification Failed:  Incompatible Var"
		  | SOME *) U1 => unifyExp(Gglobal, G, E1, D.Quote U1))

	| unifyExpN (Gglobal, G, D.Quote M1, D.Quote M2) = (U.unifyG (Gglobal, G, (M1, I.id), (M2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ))
	| unifyExpN (Gglobal, G, D.Unit, D.Unit) = ()

	| unifyExpN (Gglobal, G, D.Lam (C1list, F1, fileInfo1), D.Lam (C2list, F2, fileInfo2)) = (unifyCaseList(Gglobal, G, C1list, C2list) ; unifyFormula(Gglobal, G, F1, F2))

	| unifyExpN (Gglobal, G, D.New (D1, E1, fileInfo1), D.New (D2,E2, fileInfo2)) = (unifyNewDec(Gglobal, G, D1, D2) ;
						       unifyExp(Gglobal, I.Decl(G, D.coerceDec(D.NonInstantiableDec D1)), E1, E2))
	| unifyExpN (Gglobal, G, D.App (E1, args1), D.App (E1', args2)) = 
		 let
		   val _ = unifyExp(Gglobal, G, E1, E1')
		   fun unifyExps ([], []) = ()
		     | unifyExps ((visible, fileInfo, E2)::args1, (visible', fileInfo', E2')::args2) =
		                (unifyVisibility(visible, visible') ; 
				 unifyExp(Gglobal, G, E2, E2') ;
				 unifyExps (args1, args2))
		     | unifyExps _ = raise Error "Delphin Unificatin Failed:  Different number of arguments in application"

		   val _ = unifyExps (args1, args2)
		 in
		   ()
		 end

	| unifyExpN (Gglobal, G, D.Pair (E1, E2, F), D.Pair (E1', E2', F')) = (unifyExp(Gglobal, G, E1, E1') ; unifyExp(Gglobal, G, E2, E2') ; unifyFormula(Gglobal, G, F, F'))

	| unifyExpN (Gglobal, G, D.ExpList E1list, D.ExpList E2list) = unifyExpList(Gglobal, G, E1list, E2list)
	| unifyExpN (Gglobal, G, D.Proj (E1, i), D.Proj (E1', j)) = 
                              if (i=j) then unifyExp(Gglobal, G, E1, E1') else raise Error "Delphin Unificatin Failed:  Different Variable Access in Projection"

	| unifyExpN (Gglobal, G, D.Pop(i, E1, fileInfo1), D.Pop(j, E2, fileInfo2)) = if (i=j) then
				                    unifyExp (Gglobal, D.popCtxLF(i, G), E1, E2)
						    else raise Error "Delphin Unificatin Failed:  Different Variable Access in Pop"

	| unifyExpN (Gglobal, G, D.Fix (D1, E1), D.Fix (D2,E2)) = (unifyNormalDec(Gglobal, G, D1, D2) ;
						       unifyExp(Gglobal, I.Decl(G, D.coerceDec (D.InstantiableDec D1)), E1, E2))


	| unifyExpN (Gglobal, G, D.EVar ((r1,F1), t1), E2 as D.EVar ((r2,F2), t2)) =
	       let 
		 val s1 = numShifts t1 (* Raises error if t1 is not a shift substitution *)
		 val s2 = numShifts t2 (* Raises error if t2 is not a shift substitution *)
	       in
		 if (r1 = r2) then if (s1=s2) then () else raise Error "Delphin Unification Failure:  Same Meta-Level EVar under different substitution"  (* Should add constraints to handle this properly!!! -- ABP *)
		 else if (s1 > s2) then (* r2 = r1[s1-s2] *)
		                        instantiateEVar(r2, D.EVar((r1,F1), D.shiftTo(s1-s2, D.id)))
		      else
			(* r1 = r2[s2-s1] *)
			instantiateEVar(r1, D.EVar((r2,F2), D.shiftTo(s2-s1, D.id)))
	       end
	| unifyExpN (Gglobal, G, D.EVar ((r1,F1), t1), E2) =
	       let
		 val s1 = numShifts t1 (* Raises error if t1 is not a shift substitution *)
		 val t1Inv = invertShiftSub(s1)
	         (* G |- t1 : G0 *)
	         (* G0 |- t1Inv : G *)
		 val E2' = applyInv2Exp(Gglobal, G, E2, t1Inv, r1)
	       in
		 instantiateEVar(r1, E2')
	       end


	| unifyExpN (Gglobal, G, E2, D.EVar ((r1, F1), t1)) = 
	       let
		 val s1 = numShifts t1 (* Raises error if t1 is not a shift substitution *)
		 val t1Inv = invertShiftSub(s1)
	         (* G |- t1 : G0 *)
	         (* G0 |- t1Inv : G *)
		 val E2' = applyInv2Exp(Gglobal, G, E2, t1Inv, r1)
	       in
		 instantiateEVar(r1, E2')
	       end



	| unifyExpN _ = raise Error "Delphin Unification Failed:  Expressions incompatible"

 
    (* Tie it together to use constraints *)

      fun awakeCnstr (NONE) = ()
	| awakeCnstr (SOME(ref D.Solved)) = awakeCnstr (nextCnstr ())
	| awakeCnstr (SOME(cnstr as ref (D.EqnF (Gglobal, G, F1, F2)))) =
          (solveConstraint cnstr;
           unifyF' (Gglobal, G, F1, F2))

      and unifyE' (Gglobal, G, E1, E2) = 
          (unifyExp (Gglobal, G, E1, E2); awakeCnstr (nextCnstr ()))

      and unifyF' (Gglobal, G, F1, F2) =
          (unifyFormula (Gglobal, G, F1, F2); awakeCnstr (nextCnstr ()))

      and unifyT' (Gglobal, G, T1, T2) =
          (unifyTypes (Gglobal, G, T1, T2); awakeCnstr (nextCnstr ()))


    in
      fun unifyF (Gglobal, G, F1, F2) = 
	(resetAwakenCnstrs (); unifyF' (Gglobal, G, F1, F2))

      fun unifyT (Gglobal, G, T1, T2) = 
	(resetAwakenCnstrs (); unifyT' (Gglobal, G, T1, T2))


      fun unifyE (Gglobal, G, E1, E2) = 
	(* E no longer has any constraints attached to it.. so we can optimize
	 * away the cnstrs if we want...
	 *)
	(resetAwakenCnstrs () ; unifyE'(Gglobal, G, E1, E2))

      fun unifyP (P1, P2) = unifyParam(P1, P2)

      fun LFunifiable (Gglobal, G, A1s, A2s) = (U.unifyG (Gglobal, G, A1s, A2s) ; true) handle U.Unify msg => false

      val LFapplyInv2Exp = LFapplyInv2Exp
      val applyInv2Formula = applyInv2Formula
      val applyInv2NormalDec = applyInv2NormalDec

      val reset = reset
      val mark = mark
      val unwind = unwind


      val applyInv2Exp = applyInv2Exp

    end

  end 