(* Delphin World Subsumption *)
(* Author: Adam Poswolsky *)

structure WorldSubsumption =
  struct
    exception Error of string
    structure D = DelphinIntSyntax
    structure I = IntSyn

    fun crash() = raise Domain

    datatype role = Output | Input
    fun swap Output = Input
      | swap Input  = Output


    fun possibleSplitOnParam(F) = possibleSplitOnParamW(D.whnfF F)
    and possibleSplitOnParamW(D.All(_,_,D,F)) = false (* no splitting on functions *)
      | possibleSplitOnParamW(D.Exists(D, F)) = possibleSplitOnParamNormalDec(D) orelse possibleSplitOnParam(F)
      | possibleSplitOnParamW(D.Nabla(D, F)) = possibleSplitOnParam(F)
      | possibleSplitOnParamW(D.FormList []) = false
      | possibleSplitOnParamW(D.FormList (F::Flist)) = possibleSplitOnParam(F) orelse possibleSplitOnParam(D.FormList Flist)
      | possibleSplitOnParamW _ = false

    and possibleSplitOnParamNormalDec(D.NormalDec(_, T)) = possibleSplitOnParamTypes(T)
    
    and possibleSplitOnParamTypes(D.LF(isP, _)) = (case (D.whnfP isP)
					 of D.Param => true
					   | D.Existential => false
					   | _ => crash() (* no PVars ... *) 
					 )
      | possibleSplitOnParamTypes(D.Meta(isP, F)) = (case (D.whnfP isP)
					   of D.Param => true
					    | D.Existential => possibleSplitOnParam(F)
					    | _ => crash() (* no PVars... *)
					 )


      (* isEmpty indicates if it is an empty function we are filling in info for.. *)
    fun fillInWorldFormula(isEmpty, W, F) = fillInWorldFormulaW(isEmpty, W, D.whnfF F)
    and fillInWorldFormulaW(isEmpty, W, F as D.Top) = F
      | fillInWorldFormulaW(isEmpty, W, D.All(visible, _, D, F)) = 
                let
		  val D' = fillInWorldNormalDec (isEmpty, W,D)
		  val F' = fillInWorldFormula(isEmpty, W, F)
		  val W' = if (not isEmpty) andalso (possibleSplitOnParamNormalDec D) then (D.VarList [] (* not weakenable *)) else W
		in
		  D.All(visible, SOME W', D', F')
		end

      | fillInWorldFormulaW(isEmpty, W, D.Exists(D, F)) = D.Exists(fillInWorldNormalDec(isEmpty, W, D), fillInWorldFormula(isEmpty, W, F))
      | fillInWorldFormulaW(isEmpty, W, D.Nabla(D, F)) = D.Nabla(fillInWorldNewDec(isEmpty, W, D), fillInWorldFormula(isEmpty, W, F))
      | fillInWorldFormulaW(isEmpty, W, D.FormList Flist) = D.FormList (map (fn F => fillInWorldFormula(isEmpty, W, F)) Flist)
      | fillInWorldFormulaW(isEmpty, W, D.FVar _) = raise Domain (* no FVars in world checker *)
      | fillInWorldFormulaW(isEmpty, W, D.FClo _) = raise Domain (* not in whnf *)



    and fillInWorldTypes(isEmpty, W, D.Meta (isP, F)) = D.Meta(isP, fillInWorldFormula(isEmpty, W, F))
      | fillInWorldTypes(isEmpty, W, E as D.LF _ ) = E

    and fillInWorldNormalDec(isEmpty, W, D.NormalDec (name, T)) = D.NormalDec (name, fillInWorldTypes(isEmpty, W, T))

    and fillInWorldNewDec(isEmpty, W, D.NewDecMeta(name, F)) = D.NewDecMeta(name, fillInWorldFormula(isEmpty, W, F))
      | fillInWorldNewDec(isEmpty, W, E as D.NewDecLF _) = E

    and fillInWorldExp(W, E) = fillInWorldExpW (W, D.whnfE E)
    and fillInWorldExpW(W, D.Lam (Clist, F, fileInfo)) =
                 let
		   val Clist' = map (fn C => fillInWorldCase(W, C)) Clist
		   val F' = fillInWorldFormula ((List.length(Clist) = 0), W, F)
		 in
		   D.Lam (Clist', F', fileInfo)
		 end
      | fillInWorldExpW(W, D.New(D, E, fileInfo)) =
		 let
		   val D' = fillInWorldNewDec(false, W, D)
		   val E' = fillInWorldExp(W, E)
		 in
		   D.New(D', E', fileInfo)
		 end
      | fillInWorldExpW(W, D.App(visible, E1, E2, fileInfo)) = D.App(visible, fillInWorldExp(W, E1), fillInWorldExp(W, E2), fileInfo)
      | fillInWorldExpW(W, D.Pair(E1, E2, F)) = D.Pair(fillInWorldExp(W, E1), fillInWorldExp(W, E2), fillInWorldFormula(false, W, F))
      | fillInWorldExpW(W, D.ExpList Elist) = D.ExpList (map (fn E => fillInWorldExp(W, E)) Elist)
      | fillInWorldExpW(W, D.Proj(E, i)) = D.Proj(fillInWorldExp(W, E), i)
      | fillInWorldExpW(W, D.Pop(i, E, fileInfo)) = D.Pop(i, fillInWorldExp(W, E), fileInfo)
      | fillInWorldExpW(W, D.Fix(D, E)) = D.Fix(fillInWorldNormalDec (false, W, D), fillInWorldExp(W, E))
      | fillInWorldExpW(W, E) = E

    and fillInWorldCase (W, D.Eps (D, C)) = D.Eps (fillInWorldNormalDec (false, W, D), fillInWorldCase (W, C))
      | fillInWorldCase (W, D.NewC (D, C, fileInfo)) = D.NewC (fillInWorldNewDec (false, W, D), fillInWorldCase (W, C), fileInfo)
(* removed PopC
      | fillInWorldCase (W, D.PopC (i, C)) = D.PopC (i, fillInWorldCase (W, C))
*)
      | fillInWorldCase (W, D.Match (visible, E1, E2)) = D.Match (visible, fillInWorldExp(W, E1), fillInWorldExp(W, E2))
      | fillInWorldCase (W, D.MatchAnd (visible, E, C)) = D.MatchAnd (visible, fillInWorldExp(W, E), fillInWorldCase(W, C))



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
		     val list = D.makeParamList (I.mergeCtx(Gglobal, Gcodomain))
		     val X = I.Root(I.BVar (I.BVarVar ((ref NONE, A', list, ref nil), I.id)), I.Nil)
		   in
		     I.Dot (I.Exp X, t')
		   end
                | _ => crash() )

      | createSub _ = crash() (* broken invariant *)


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
	      val A2 = reduce(Gglobal, G',A', G)  (* G |- A' : type *)
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
		| subsume((G,A)::Alist1, Alist2) = contains(I.Null, G, A, Alist2) andalso subsume(Alist1, Alist2)
	    in
	      subsume(Alist1, Alist2)
	    end


      (* World Checking *)



    (* Precondition:  F has no PVars or FVars *)
    (* canWeakenFormula F = true if and only if formula F can be weakened over a parameter of type A
     * Precondition:  G |- A : type (the G is NOT the context of F)
     *)
    fun canWeakenFormula (G, A, F, role) = canWeakenFormulaW (G, A, D.whnfF F, role)
    and canWeakenFormulaW (G, A, D.All(_, SOME W, D, F2), Output) =
      if containInWorld(I.Null, G, A, W) then
	canWeakenNormalDec(G, A, D, Input) andalso canWeakenFormula(G, A, F2, Output)
      else
	(let
	   (*  World violation for parameters of type A .
	   fun debugAdam() = 
	     (print ("ADAM ADAM missing:  " ^ (Print.expToString(D.coerceCtx G, A) ) ^ "\n\n"))
	   val _ = debugAdam()
	     *)
	 in
	   false
	 end)
	   


      | canWeakenFormulaW (G, A, D.All(_, W, D, F2), Input) =
                       canWeakenNormalDec(G, A, D, Output) andalso canWeakenFormula(G, A, F2, Input)

      | canWeakenFormulaW (G, A, D.Exists(D, F2), role) = (canWeakenNormalDec (G, A, D, role)) andalso (canWeakenFormula (G, A, F2, role))
      | canWeakenFormulaW (G, A, D.Nabla(D, F2), role) = canWeakenFormula(G, A, F2, role)
      | canWeakenFormulaW (G, A, D.Top, role) = true
      | canWeakenFormulaW (G, A, D.FormList [], role) = true
      | canWeakenFormulaW (G, A, D.FormList (F::Flist), role) = (canWeakenFormula (G, A, F, role)) andalso canWeakenFormula (G, A, D.FormList Flist, role)
      | canWeakenFormulaW (G, A, _, role) = crash() (* violates invariants *)




    and canWeakenType (G, A, D.LF _, role) = true
      | canWeakenType (G, A, D.Meta(_, F), role) = canWeakenFormula(G, A, F, role)

    and canWeakenNormalDec (G, A, D.NormalDec(_, T), role) = canWeakenType (G, A, T, role)

    fun canWeakenTypeList (G, T, []) = true
      | canWeakenTypeList (G, T, A::listWeakened) = canWeakenType(G,A,T,Output) andalso canWeakenTypeList(G,T,listWeakened)


    fun formulasLess(F1, F2) = formulasLessW (D.whnfF F1, D.whnfF F2)
    and formulasLessW(D.Top, D.Top) = true
      | formulasLessW(D.All(_, (SOME W1), D1, F1), D.All(_, (SOME W2), D2, F2)) = worldSubsume(W2, W1) andalso normalDecLess(D2, D1) andalso formulasLess(F1,F2)
      | formulasLessW(D.Exists(D1, F1), D.Exists(D2, F2)) = normalDecLess(D1, D2) andalso formulasLess(F1, F2)
      | formulasLessW(D.Nabla(D1, F1),  D.Nabla(D2, F2)) = newDecLess(D1, D2) andalso formulasLess(F1, F2)
      | formulasLessW(D.FormList [], D.FormList []) = true
      | formulasLessW(D.FormList (F1::Flist1), D.FormList (F2::Flist2)) = formulasLess(F1,F2) andalso formulasLess(D.FormList Flist1, D.FormList Flist2)
      | formulasLessW _ = crash() (* no more options *)

    and normalDecLess(D.NormalDec (_, T1), D.NormalDec (_, T2)) = typesLess (T1, T2)
    and newDecLess (D.NewDecLF _, D.NewDecLF _) = true
      | newDecLess (D.NewDecMeta (_, F1), D.NewDecMeta (_, F2)) = formulasLess (F1, F2)
      | newDecLess _ = crash()

    and typesLess (D.LF _, D.LF _) = true
      | typesLess (D.Meta(_, F1), D.Meta(_, F2)) = formulasLess(F1, F2)
      | typesLess _ = crash()


  end

