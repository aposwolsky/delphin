(* Delphin World Subsumption *)
(* Author: Adam Poswolsky *)

structure WorldSubsumption =
  struct
    structure D = DelphinIntSyntax
    structure I = IntSyn

    fun crash() = raise Domain


    fun possibleSplitOnParam(F) = possibleSplitOnParamW(D.whnfF F)
    and possibleSplitOnParamW(D.All _) = false (* no splitting on functions *)
      | possibleSplitOnParamW(D.Exists(D, F)) = possibleSplitOnParamNormalDec(D) orelse possibleSplitOnParam(F)
      | possibleSplitOnParamW(D.Nabla(D, F)) = possibleSplitOnParam(F)
      | possibleSplitOnParamW(D.FormList []) = false
      | possibleSplitOnParamW(D.FormList (F::Flist)) = possibleSplitOnParam(F) orelse possibleSplitOnParam(D.FormList Flist)
      | possibleSplitOnParamW _ = false

    and possibleSplitOnParamNormalDec(D.NormalDec(_, T)) = possibleSplitOnParamTypes(T)
    and possibleSplitOnParamNormalDecs((vis, D) :: Ds) = (possibleSplitOnParamNormalDec D) orelse (possibleSplitOnParamNormalDecs Ds)
      | possibleSplitOnParamNormalDecs [] = false
    
    and possibleSplitOnParamTypes(D.LF(isP, _)) = (case (D.whnfP isP)
					 of D.Param => true
					   | D.Existential => false
					   | _ => crash() (* no PVars ... *) 
					 )
      | possibleSplitOnParamTypes(D.Meta(F)) = possibleSplitOnParam(F)


    (* createSub (Gglobal, G, Gcodomain) = t 
     * such that Gcodoman |- t : G
     * and t is filled with EVars in context Gcodomain
     * G can only contain LF InstantiableDecs...
     *)		     
    fun createSub(Gglobal, I.Null, Gcodomain) = I.Shift (I.ctxLength Gcodomain)
      | createSub(Gglobal, I.Decl(G, D.InstantiableDec (D.NormalDec(_, D.LF(isP, A)))), Gcodomain) = 
           (case (D.whnfP isP)
	      of D.Existential => 
                   let
		     val t' = createSub (Gglobal, G, Gcodomain)     (* Gcodomain |- t' : G       *)
		                                           (* G |- A : type     *)
		     val A' = I.EClo(A, t')                (* Gcodomain |- A[t'] : type *)
		     val X = I.newEVarPruneNdec(D.coerceCtx Gcodomain, A')
		   in
		     I.Dot (I.Exp X, t')                    (* Gcodomain |- X.t' : G,V   *)
		   end
		| D.Param =>
                   let
		     val t' = createSub (Gglobal, G, Gcodomain)
		     val A' = I.EClo(A, t')  
		     val list = D.makeLFParamList (I.mergeCtx(Gglobal, Gcodomain))
		     val X = D.coerceBoundVar (D.newParamVarPruneNDecs (Gglobal, Gcodomain, A'))
		     (* OLD:  Problem with creating variables in contexts with NDecs...
                              val X = I.Root(I.BVar (I.BVarVar ((ref NONE, A', list, ref nil), I.id)), I.Nil)
                      *)
		   in
		     I.Dot (I.Exp X, t')
		   end
                | _ => crash() )

      | createSub _ = crash() (* broken invariant *)


    fun makeDecCtx I.Null = I.Null
      | makeDecCtx (I.Decl(G, D)) = I.Decl(makeDecCtx G, D.InstantiableDec D)

    (* reduce (Gglobal, G, A, Gevars) = A'
     * where Gevars |- A' : type given that G |- A : type 
     *)
    fun reduce(Gglobal, G, A, Gevars) = I.EClo(A, createSub (Gglobal, G, Gevars))

    fun contains(Gglobal, G, A1, []) = false
      | contains(Gglobal, G, A1, (G',A')::Alist2) =
            (* Gglobal,G |- A1 : type
	     * G' |- A' : type 
	     *)
            let
	      val _ = UnifyTrail.mark()
	      val A2 = reduce(Gglobal, makeDecCtx G',A', G)  (* G |- A' : type *)
	      val b = (UnifyTrail.unifiableG(D.coerceCtx Gglobal, D.coerceCtx G, (A1, I.id), (A2, I.id))) andalso (DelphinAbstract2.hasNoConstraintsExp A1)
	      val _ = UnifyTrail.unwind()
	    in
	      b orelse contains(Gglobal, G, A1, Alist2)
	    end

    (* Determines if a world W supports the extension of A1 
     *)
    fun containInWorld(Gglobal, G, A1, D.Anything) = true
      | containInWorld(Gglobal, G, A1, D.VarList vList) = contains(Gglobal, G, A1, vList)

    (* W1 <= W2 iff a term in W1 can be called in W2
     * which indicates that forall T in W1, it is compatible with W2
     *)
    fun worldSubsume (_, D.Anything) = true
      | worldSubsume (D.Anything, _) = false
      | worldSubsume (D.VarList Alist1, D.VarList Alist2) = 
            let
	      fun subsume([], Alist2) = true
		| subsume((G,A)::Alist1, Alist2) = contains(I.Null, makeDecCtx G, A, Alist2) andalso subsume(Alist1, Alist2)
	    in
	      subsume(Alist1, Alist2)
	    end

 

    (* Precondition:  F has no PVars or FVars *)
    (* canWeakenFormula F = true if and only if a value of F can be weakened over arbitrary parameters.
     * This is an ENHANCEMENT:
     * You can view this as adding an admissible rule.
     * 
     * For example:  If G,u:<A> |- u : <A>, then we want to allow G,u:<A>,G2 |- u : <A> for any
     * arbitrary G2.  This is admissible as we use an eager operational semantics and this property
     * holds for values of <A>.  The alternative would be for the user to write a function of the form:
     *   ([W]<A>) -> <A>, which is possible in the formal system, but not when we disallow the explicit
     *   use of [W] to the programmer... HOWEVER, another alternative is that the user must
     *   OPEN the pair before creating the new parameters...
     * *)
    fun canWeakenFormula (F) = canWeakenFormulaW (D.whnfF F)
    and canWeakenFormulaW ( D.All(Ds, F2)) = false
      | canWeakenFormulaW ( D.Exists(D, F2)) = (canWeakenNormalDec ( D)) andalso (canWeakenFormula ( F2))
      | canWeakenFormulaW ( D.Nabla(D, F2)) = canWeakenFormula( F2) (* WARNING:  doublecheck this one! 
									       * It may be safer to be more conservative
									       * and just return false.. but this is ok 
									       * and more powerful.
									       *)
      | canWeakenFormulaW ( D.Top) = true
      | canWeakenFormulaW ( D.FormList []) = true
      | canWeakenFormulaW ( D.FormList (F::Flist)) = (canWeakenFormula ( F)) andalso canWeakenFormula ( D.FormList Flist)
      | canWeakenFormulaW ( _) = crash() (* violates invariants *)


    and canWeakenType ( D.LF _) = true
      | canWeakenType ( D.Meta(F)) = canWeakenFormula( F)

    and canWeakenNormalDec ( D.NormalDec(_, T)) = canWeakenType ( T)
    and canWeakenNormalDecs ( [])  = true
      | canWeakenNormalDecs ( ((vis,D)::Ds)) = canWeakenNormalDec ( D) andalso canWeakenNormalDecs ( Ds)

    fun compatWorld (W, G, []) = true
      | compatWorld (W, G, (D.NewDecLF(_, A))::listWeakened) = containInWorld(I.Null, G, A, W) andalso compatWorld(W, G, listWeakened)
      | compatWorld (W, G, (D.NewDecWorld(_, W2))::listWeakened) = (worldSubsume (W2, W)) andalso compatWorld(W, G, listWeakened)


(*
    (* Subtyping is also an admissible rule, and maybe someday we will add something like this...
     * BUT we need to think about this carefully! *)
    fun formulasLess(F1, F2) = formulasLessW (D.whnfF F1, D.whnfF F2)
    and formulasLessW(D.Top, D.Top) = true
      | formulasLessW(D.All(D1s, F1), D.All(D2s, F2)) = normalDecsLess(D2s, D1s) andalso formulasLess(F1,F2)
      | formulasLessW(D.Exists(D1, F1), D.Exists(D2, F2)) = normalDecLess(D1, D2) andalso formulasLess(F1, F2)
      | formulasLessW(D.Nabla(D1, F1),  D.Nabla(D2, F2)) = newDecLess(D1, D2) andalso formulasLess(F1, F2)
      | formulasLessW(D.FormList [], D.FormList []) = true
      | formulasLessW(D.FormList (F1::Flist1), D.FormList (F2::Flist2)) = formulasLess(F1,F2) andalso formulasLess(D.FormList Flist1, D.FormList Flist2)
      | formulasLessW _ = crash() (* no more options *)

    and normalDecLess(D.NormalDec (_, T1), D.NormalDec (_, T2)) = typesLess (T1, T2)
    and normalDecsLess([], []) = true
      | normalDecsLess((_,D1)::D1s, (_,D2)::D2s) = normalDecLess(D1, D2) andalso normalDecsLess (D1s, D2s)
      | normalDecsLess _ = crash() (* no more options *)

    and newDecLess (D.NewDecLF _, D.NewDecLF _) = true
      | newDecLess (D.NewDecWorld (_, W1), D.NewDecWorld (_, W2)) = worldSubsume(W2, W1) (* contravariant!!! *)
      | newDecLess _ = crash()

    and typesLess (D.LF _, D.LF _) = true
      | typesLess (D.Meta(_, F1), D.Meta(_, F2)) = formulasLess(F1, F2)
      | typesLess _ = crash()
*)

  end

