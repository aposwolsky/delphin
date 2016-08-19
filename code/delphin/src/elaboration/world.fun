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


    fun hasParamInput(F, role) = hasParamInputW(D.whnfF F, role)
    and hasParamInputW(D.All(_,_,D,F), role) = hasParamInputNormalDec(D, swap role) orelse hasParamInput(F, role)
      | hasParamInputW(D.Exists(D, F), role) = hasParamInputNormalDec(D, role) orelse hasParamInput(F, role)
      | hasParamInputW(D.Nabla(D, F), role) = hasParamInput(F, role)
      | hasParamInputW(D.FormList [], role) = false
      | hasParamInputW(D.FormList (F::Flist), role) = hasParamInput(F, role) orelse hasParamInput(D.FormList Flist, role)
      | hasParamInputW _ = false

    and hasParamInputNormalDec(D.NormalDec(_, T), role) = hasParamTypes(T, role)
    
    and hasParamTypes(D.LF(isP, _), Input) = (case (D.whnfP isP)
					 of D.Param => true
					   | D.Existential => false
					   | _ => crash() (* no PVars ... *) 
					 )
      | hasParamTypes(D.LF _, Output) = false
      | hasParamTypes(D.Meta(isP, F), Input) = (case (D.whnfP isP)
					   of D.Param => true
					    | D.Existential => hasParamInput(F, Input)
					    | _ => crash() (* no PVars... *)
					 )

      | hasParamTypes(D.Meta(isP, F), Output) = hasParamInput(F, Output)


      (* OLD
    fun isParam (D.NormalDec(_, D.LF (isP, _))) = (case (D.whnfP isP)
							 of D.Param => true
							  | D.Existential => false
							  | _ => crash() (* no PVars... *)
						        )

      | isParam (D.NormalDec(_, D.Meta(isP, F))) = (case (D.whnfP isP)
							 of D.Param => true
							  | D.Existential => hasParamInput(F, Input)
							  | _ => crash() (* no PVars... *)
						        )

    (* Determine if a function is a "parameter" function, i.e. one that will not be weakened *)
    fun isParamFun F = isParamFunW (D.whnfF F)
    and isParamFunW (D.All (_, _, D, F)) = (isParam D) orelse isParamFun F
      | isParamFunW (D.Nabla(_, F)) = isParamFun F
      | isParamFunW _ = false
   *)
    fun isParamFun F = hasParamInput(F, Output)

    (*
    fun fillInWorldFormula(W, F) = fillInWorldFormulaW(W, D.whnfF F)
    and fillInWorldFormulaW(W, F as D.Top) = F
      | fillInWorldFormulaW(W, D.All(visible, _, D, F)) = 
                let
		  val D' = fillInWorldNormalDec (W,D)
		  val F' = fillInWorldFormula(W, F)
		  val W' = if (isParam D) then (D.NonWeakenable W) else W
		in
		  D.All(visible, SOME W', D', F')
		end

      | fillInWorldFormulaW(W, D.Exists(D, F)) = D.Exists(fillInWorldNormalDec(W, D), fillInWorldFormula(W, F))
      | fillInWorldFormulaW(W, D.Nabla(D, F)) = D.Nabla(fillInWorldNewDec(W, D), fillInWorldFormula(W, F))
      | fillInWorldFormulaW(W, D.FormList Flist) = D.FormList (map (fn F => fillInWorldFormula(W, F)) Flist)
      | fillInWorldFormulaW(W, F) = F
    *)

    fun fillInWorldFormula((D.NonWeakenable W), F) = fillInWorldFormulaW(D.NonWeakenable W, D.whnfF F)

      | fillInWorldFormula(W, F) = if (isParamFun F) then 
                                     fillInWorldFormulaW(D.NonWeakenable W, D.whnfF F)
				   else
				     fillInWorldFormulaW(W, D.whnfF F)

    and fillInWorldFormulaW(W, F as D.Top) = F
      | fillInWorldFormulaW(W, D.All(visible, _, D, F)) = D.All(visible, SOME W, fillInWorldNormalDec(W, D), fillInWorldFormula(W, F))
      | fillInWorldFormulaW(W, D.Exists(D, F)) = D.Exists(fillInWorldNormalDec(W, D), fillInWorldFormula(W, F))
      | fillInWorldFormulaW(W, D.Nabla(D, F)) = D.Nabla(fillInWorldNewDec(W, D), fillInWorldFormula(W, F))
      | fillInWorldFormulaW(W, D.FormList Flist) = D.FormList (map (fn F => fillInWorldFormula(W, F)) Flist)
      | fillInWorldFormulaW(W, F) = F



    and fillInWorldTypes(W, D.Meta (isP, F)) = D.Meta(isP, fillInWorldFormula(W, F))
      | fillInWorldTypes(W, E as D.LF _ ) = E

    and fillInWorldNormalDec(W, D.NormalDec (name, T)) = D.NormalDec (name, fillInWorldTypes(W, T))

    and fillInWorldNewDec(W, D.NewDecMeta(name, F)) = D.NewDecMeta(name, fillInWorldFormula(W, F))
      | fillInWorldNewDec(W, E as D.NewDecLF _) = E

    and fillInWorldExp(W, E) = fillInWorldExpW (W, D.whnfE E)
    and fillInWorldExpW(W, D.Lam (Clist, F, fileInfo)) =
                 let
		   val Clist' = map (fn C => fillInWorldCase(W, C)) Clist
		   val F' = fillInWorldFormula (W, F)
		 in
		   D.Lam (Clist', F', fileInfo)
		 end
      | fillInWorldExpW(W, D.New(D, E, fileInfo)) =
		 let
		   val D' = fillInWorldNewDec(W, D)
		   val E' = fillInWorldExp(W, E)
		 in
		   D.New(D', E', fileInfo)
		 end
      | fillInWorldExpW(W, D.App(visible, E1, E2)) = D.App(visible, fillInWorldExp(W, E1), fillInWorldExp(W, E2))
      | fillInWorldExpW(W, D.Pair(E1, E2, F)) = D.Pair(fillInWorldExp(W, E1), fillInWorldExp(W, E2), fillInWorldFormula(W, F))
      | fillInWorldExpW(W, D.ExpList Elist) = D.ExpList (map (fn E => fillInWorldExp(W, E)) Elist)
      | fillInWorldExpW(W, D.Proj(E, i)) = D.Proj(fillInWorldExp(W, E), i)
      | fillInWorldExpW(W, D.Pop(i, E)) = D.Pop(i, fillInWorldExp(W, E))
      | fillInWorldExpW(W, D.Fix(D, E)) = D.Fix(fillInWorldNormalDec (W, D), fillInWorldExp(W, E))
      | fillInWorldExpW(W, E) = E

    and fillInWorldCase (W, D.Eps (D, C)) = D.Eps (fillInWorldNormalDec (W, D), fillInWorldCase (W, C))
      | fillInWorldCase (W, D.NewC (D, C, fileInfo)) = D.NewC (fillInWorldNewDec (W, D), fillInWorldCase (W, C), fileInfo)
      | fillInWorldCase (W, D.PopC (i, C)) = D.PopC (i, fillInWorldCase (W, C))
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
		     val X = I.Root(I.BVar (I.BVarVar ((ref NONE, A', list), I.id)), I.Nil)
		   in
		     I.Dot (I.Exp X, t')
		   end
                | _ => crash() )

      | createSub _ = crash() (* broken invariant *)

		   
    (* OLD
     * ***
    (* createSub (G, Gevars) = t 
     * such that Gevars |- t : G
     * and t is filled with EVars
     *)		     
    fun createSub(I.Null, Gevars) = I.Shift (I.ctxLength Gevars)
      | createSub(I.Decl(G, I.Dec(_, V)), Gevars) = 
                   let
		     val t' = createSub (G,Gevars)      (* Gevars |- t' : G       *)
		                                        (* G |- V : type     *)
		     val V' = I.EClo(V, t')             (* Gevars |- V[t'] : type *)

		     val X = I.newEVarPruneNdec(Gevars, V')
		   in
		     I.Dot(I.Exp X, t')       (* . |- X.t' : G,V   *)
		   end
      | createSub _ = crash() (* unexpected context for world specification *)
		   *)

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

    (* Determines if a world W supports the extension of A1 *)
    fun containInWorld(Gglobal, G, A1, D.Anything) = true
      | containInWorld(Gglobal, G, A1, D.VarList vList) = contains(Gglobal, G, A1, vList)
      | containInWorld(Gglobal, G, A1, D.NonWeakenable W) = false

    (* W1 <= W2 iff a term in W1 can be called in W2
     * which indicates that forall T in W1, it is compatible with W2
     *)
    fun worldSubsume (_, D.Anything) = true
      | worldSubsume (_, D.NonWeakenable _) = true
      | worldSubsume (D.NonWeakenable W1, W2) = worldSubsume(W1, W2)
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
	(print ("ADAm ADAM missing:  " ^ (Print.expToString(D.coerceCtx G, A) ) ^ "\n\n"); false)


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
      | formulasLessW(D.All(_, SOME W1, D1, F1), D.All(_, SOME W2, D2, F2)) = worldSubsume(W2, W1) andalso normalDecLess(D2, D1) andalso formulasLess(F1,F2)
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


    fun getFormula (D.Meta(_, F)) = D.whnfF F
      | getFormula _ = crash()
 
    (* raises Error if not world correct *)
    fun checkWorld(G, currentWorld, E) = 
      let
	    (* lookup(G, k) = (name, T, listWeakened)
	     *)
	     fun lookup' (k', I.Null, _) = raise Error "Bad Variable Access in checkWorld" 
	       | lookup' (k', I.Decl(G, (D.InstantiableDec (D.NormalDec (SOME [s], T0)))), 1 ) = (SOME s, D.substTypes(T0, I.Shift k'), [])
	       | lookup' (k', I.Decl(G, (D.InstantiableDec (D.NormalDec (_, T0)))), 1 ) = (NONE, D.substTypes(T0, I.Shift k'), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecLF (name, A)))), 1) = (name, D.LF(D.Param, A), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecMeta (name, F)))), 1) = (name, D.Meta(D.Param, F), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecLF (_, A)) )), k) = 
                               let
				 val (name, T, list) = lookup'(k', G, k-1)
			       in
				 (name, T, I.EClo(A, I.Shift (k' - k + 1)) :: list)
			       end

	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecMeta (_, F)) )), k) = 
                               let
				 val (name, T, list) = lookup'(k', G, k-1)
			       in
				 (name, T, list) (* ABP:  WARNING... *)
			       end

	       | lookup' (k', I.Decl(G, (D.InstantiableDec _)), k) = lookup'(k', G, k-1)

	     fun lookup (G, k) = lookup' (k, G, k)


	     fun check (G,E) = checkN (G, D.whnfE E)
	     and checkN (G, D.Var (D.Fixed i, fileInfo)) = 
	                    let
			      val (name, T, listWeakened) = lookup(G, i)
			      val varString = case name 
			                      of NONE => ""
					       | SOME s => ": " ^ s
			    in
			      if canWeakenTypeList(G, T, listWeakened) then T
			      else (
				    case fileInfo
				       of SOME(filename, r) => 
					   raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Violation:  Cannot weaken variable" ^ varString)))
				        | NONE => 
						 raise Error ("Error:  World Violation:  Cannot weaken variable" ^ varString)
                                     )
			    end


	       | checkN (G, D.Var (D.BVarMeta ((_, F), s), fileInfo)) = D.Meta(D.Param, D.FClo(F, D.coerceSub s))
	       | checkN (G, D.Var (D.BVarLF ((_, A, _), s), fileInfo)) = D.LF(D.Param, I.EClo(A, s))
	       | checkN (G, D.Quote M) = 
				let
				  val A = TypeCheck.infer'(D.coerceCtx G, M)
				    handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
				in
				  D.LF(D.Existential, A)
				end

	       | checkN (G, D.Unit) = D.Meta(D.Existential, D.Top)
	       | checkN (G, D.Lam ([], F, fileInfo)) = D.Meta(D.Existential, F)
	       | checkN (G, D.Lam (C::Clist, F, fileInfo)) = (checkCase(G, C) ; check(G, D.Lam(Clist, F, fileInfo)))
	       | checkN (G, D.New (D, E, fileInfo)) = 
				let
				  val T = check(I.Decl(G, (D.NonInstantiableDec D)), E)
				in
				  D.Meta(D.Existential, D.Nabla(D, getFormula T))
				end

	       | checkN (G, D.App (_, E1, E2)) = 
				let
				  val F1 = getFormula(check(G, E1))
				  val T2 = check(G, E2)
				    
				  val (tArg, fWorld, fResult) = case F1 of
				                                D.All(_, SOME w, D.NormalDec(_, T), F) => (T, w, F)
								| _ => crash()
				in
				  (* ABP:  I think we do not need currentWorld! *)
				  if worldSubsume(currentWorld, fWorld) andalso  typesLess(T2, tArg)
				    then
				      D.Meta(D.Existential, D.FClo(fResult, D.coerceSub (D.Dot(D.Prg E2, D.id))))
				    else 
				      (*
					raise Error "World Violation in Application" 
					  *)
				      let 
					fun debugAdam() = () 
					val _ = debugAdam()
					val _ = typesLess(T2,tArg)
				      in
					raise Error "World Violation in Application" 
				      end
					
				end

	       | checkN (G, D.Pair (E1, E2, F)) = 
				let
				  val _ = check(G, E1)
				  val _ = check(G, E2)
				in
				  D.Meta(D.Existential, F)
				end

	       | checkN (G, D.ExpList []) = D.Meta(D.Existential, D.FormList [])
	       | checkN (G, D.ExpList (E::Elist)) = 
				let
				  val F1 = getFormula(check(G, E))
				  val F2 = getFormula(check(G, D.ExpList Elist))
				in
				  case F2 
				    of D.FormList Flist => D.Meta(D.Existential, D.FormList (F1::Flist))
				     | _ => crash()
				end

	       | checkN (G, D.Proj (E, i)) = 
				let
				  val F1 = getFormula(check(G, E))

				  fun getElement(1, x::xs) = x
				    | getElement(i, x::xs) = if i< 1 then crash() else getElement(i-1, xs)
				    | getElement _ = raise Error "Attempted to access bad index"

				in
				  case F1
				    of D.FormList Flist => D.Meta(D.Existential, getElement(i, Flist))
				     | _ => crash() 

				end
	       | checkN (G, D.Pop (i, E)) = 
				let

				  fun popCtx(0, G) = crash()
				    | popCtx(1, I.Decl(G, D.NonInstantiableDec D)) = (G, D)
				    | popCtx(1, I.Decl(G, D.InstantiableDec D)) = raise Error "Delphin Typecheck Error:  Bad Pop"
				    | popCtx(i, I.Decl(G, _)) = popCtx (i-1, G)
				    | popCtx _ = crash()

				  val (D, F) = case getFormula(check(D.popCtx(i, G), E))
				          of D.Nabla(D, F) => (D, F)
					   | _ => crash()

				  val Tshift = D.Meta(D.Existential, D.FClo(F, I.Shift (i-1)))

				  fun getWeakenedElements(x, I.Decl(G, D)) =
				        if (x >= i) then []
					else 
					  let
					    val list' = getWeakenedElements (x+1, G)
					  in
					    case D 
						of D.NonInstantiableDec (D.NewDecLF (_, A)) => I.EClo(A, I.Shift x) :: list'
						 | _ => list'
					  end
				    | getWeakenedElements _ = crash()

				in 
				  if canWeakenTypeList(G, Tshift, getWeakenedElements(1, G)) then
				    Tshift
				  else
				    raise Error ("World Violation in Pop")
				end


	       | checkN (G, D.Fix (D, E)) = 
				let
				  val F = getFormula(check(I.Decl(G, (D.InstantiableDec D)), E))
				in
				  D.Meta(D.Existential, D.FClo(F, I.invShift))
				end

	       | checkN (G, D.EVar ((_, F), s)) = D.Meta(D.Existential, D.FClo(F, D.coerceSub s))
	       | checkN (G, _) = crash() (* not in whnf *)

	     and checkCase (G, D.Eps(D, C)) = checkCase (I.Decl(G, (D.InstantiableDec D)), C)
	       | checkCase (G, D.NewC(D, C, fileInfo)) = checkCase (I.Decl(G, (D.NonInstantiableDec D)), C)
	       | checkCase (G, D.PopC(i, C)) = checkCase(D.popCtx(i, G), C) (* ADAM WARNING:  Are we removing PopC.. if not, fix this.. *)
	       | checkCase (G, D.Match(_, E1, E2)) = (check(G, E1) ; check(G, E2) ; ())
	       | checkCase (G, D.MatchAnd(_,E, C)) = (check(G, E) ; checkCase(G, C) ; ())


      in
	(check (G, E) ; ())
      end
    
  end
