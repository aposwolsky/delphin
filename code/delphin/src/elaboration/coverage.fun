(* Delphin Coverage Checker *)
(* Author: Adam Poswolsky *)
(* Algorithm somewhat based on Twelf Coverage (Twelf's cover.fun) *)

structure DelphinCoverage =
  struct
    exception CoverageError of string

    exception ImpossibleSplit
    exception NotFinitary
    structure I = IntSyn
    structure D = DelphinIntSyntax
    structure U = UnifyDelphinTrail

      
   fun crash() = (print "Fatal Error" ; raise Domain)

   fun removeSideEffects f =
         (let
	   val _ = U.mark()
	   val result = f ()
	   val _ = U.unwind()
	 in
	   result
	 end)
	    handle E => (U.unwind() ; raise E)


   datatype Equation = Eqn of (I.Dec I.Ctx) * (I.Dec I.Ctx) * D.Exp * D.Exp

   datatype Candidates =
       Eqns of Equation list      (* equations to be solved, everything matches so far *)
     | Cands of int list          (* candidates for splitting, matching fails *)
     | Fail                       (* coverage failes without candidates *)


    (* failAdd (k, cands) = cands'
       indicate failure, but add k as splitting candidate
    *)
    fun failAdd (k, Eqns _) = Cands (k::nil) (* no longer matches *)
      | failAdd (k, Cands (ks)) = Cands (k::ks) (* remove duplicates? *)
      | failAdd (k, Fail) = Fail

    (* addEqn (e, cands) = cands'
       indicate possible match if equation e can be solved
    *)
    fun addEqn (e, Eqns (es)) = Eqns (e::es) (* still may match: add equation *)
      | addEqn (e, cands as Cands (ks)) = (* already failed: ignore new constraints *)
          cands
      | addEqn (e, Fail) = Fail		(* already failed without candidates *)


    fun unifiable (Gglobal, G, E1, E2) =
          ((U.unifyE (Gglobal, G, E1, E2) ; true)
	  handle U.Error _ => false)


    (* matchEqns (es) = true 
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *)
    fun matchEqns (nil) = true
      | matchEqns (Eqn (Gglobal, G, E1, E2)::es) = unifiable (Gglobal, G, E1, E2) andalso (matchEqns es)

    (* resolveCands (cands) = cands'
       resolve to one of
	 Eqns(nil) - match successful
	 Fail      - no match, no candidates
	 Cands(ks) - candidates ks
       Effect: instantiate EVars in right-hand sides of equations.
    *)
    fun resolveCands (Eqns (es)) =
        if matchEqns (List.rev es) then (Eqns (nil))
	else Fail
      | resolveCands (Cands (ks)) = Cands (ks)
      | resolveCands (Fail) = Fail


    fun checkConstraints (C', Cands (ks)) = Cands (ks)
      | checkConstraints (C', Fail) = Fail
      | checkConstraints (C', Eqns nil) = 
         if (DelphinAbstract2.hasNoConstraintsCase C') then Eqns (nil) else Fail
      | checkConstraints _ = crash()

    (* Candidate Lists *)
    (*
       Candidate lists record constructors and candidates for each
       constructors or indicate that the coverage goal is matched.
    *)
    datatype CandList =
        Covered				(* covered---no candidates *)
      | CandList of Candidates list     (* cands1,..., candsn *)

    (* addKs (cands, klist) = klist'
       add new constructor to candidate list
    *)
    fun addKs (ccs as Cands(ks), CandList (klist)) = CandList (ccs::klist)
      | addKs (ces as Eqns(nil), CandList (klist)) = Covered
      | addKs (cfl as Fail, CandList (klist)) = CandList (cfl::klist)
      | addKs _ = crash()



    (************************************)
    (*** Selecting Splitting Variable ***)
    (************************************)

    (* insert (k, ksn) = ksn'
       ksn is ordered list of ks (smallest index first) with multiplicities
    *)
    fun insert (k, nil) = ((k, 1)::nil)
      | insert (k, ksn as (k', n')::ksn') =
        (case Int.compare (k, k')
	   of LESS => (k, 1)::ksn
	    | EQUAL => (k', n'+1)::ksn'
	    | GREATER => (k', n')::insert (k, ksn'))

    (* join (ks, ksn) = ksn'
       ksn is as in function insert
    *)
    fun join (nil, ksn) = ksn
      | join (k::ks, ksn) = join (ks, insert (k, ksn))

    (* selectCand (klist) = ksnOpt
       where ksOpt is an indication of coverage (NONE)
       or a list of candidates with multiplicities
    *)
    fun selectCand (Covered) = NONE	(* success: case is covered! *)
      | selectCand (CandList (klist)) = selectCand' (klist, nil)

    and selectCand' (nil, ksn) = SOME(ksn) (* failure: case G,V is not covered! *)
      | selectCand' (Fail::klist, ksn) = (* local failure (clash) and no candidates *)
          selectCand' (klist, ksn)
      | selectCand' (Cands(nil)::klist, ksn) = (* local failure but no candidates *)
	  selectCand' (klist, ksn)
      | selectCand' (Cands(ks)::klist, ksn) = (* found candidates ks <> nil *)
	  selectCand' (klist, join (ks, ksn))
      | selectCand' _ = crash()


    (* Matching *)
    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)

    (* matchExp (Gglobal, G, d, numVars, (U1, s1), (U2, s2), cands) = cands'
       matches U1[s1] (part of coverage goal)
       against U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
	 d is depth, k > d (and k <= d+numVars) means coverage variable

       Invariants:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V
       G = Gc, Gl where d = |Gl|
    *)
    fun fail msg = Fail

    fun revCoerceDec (I.Dec (NONE, A)) = D.InstantiableDec (D.NormalDec (NONE, D.LF(D.Existential, A)))
      | revCoerceDec (I.Dec (SOME s, A)) = D.InstantiableDec (D.NormalDec (SOME [s], D.LF(D.Existential, A)))
      | revCoerceDec _ = crash() (* No blocks/... *)

    fun revCoerceCtx (I.Null) = I.Null
      | revCoerceCtx (I.Decl (G, D)) = I.Decl(revCoerceCtx G, revCoerceDec D)

    fun LFmatchExp (Gglobal, G, d, n, Us1, Us2, cands) =
          LFmatchExpW (Gglobal, G, d, n, Whnf.whnf Us1, Whnf.whnf Us2, cands)

    and LFmatchExpW (Gglobal, G, d, n, Us1 as (I.Root (H1, S1), s1 (* id *)), Us2 as (I.Root (H2, S2), s2 (* id *)), cands) =
        (case (H1, H2)
	   (* No skolem constants, foreign constants, FVars *)
	   of (I.BVar (I.Fixed k1), I.BVar(I.Fixed k2)) =>
	      if (k1 = k2)
		then LFmatchSpine (Gglobal, G, d, n, (S1, s1), (S2, s2), cands)
	      else if (k1 > d) andalso (k1 <= (d + n))
		     then 
		       (*  
			  failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *) 
		       *)
		       case (I.ctxLookup(I.mergeCtx(Gglobal, G), k1))
		                    of (D.InstantiableDec (D.NormalDec (_, D.LF(isP, A)))) => (case D.whnfP isP
											     of D.Param =>  fail ("variable clash")
											      | D.Existential => failAdd (k1-d, cands)
											      | D.PVar _ => crash() )
				     | _ => fail ("variable clash")
				      

		   else fail ("local variable / variable clash") (* otherwise fail with no candidates *)

	    | (I.Const(c1), I.Const(c2)) =>
	      if (c1 = c2) then LFmatchSpine (Gglobal, G, d, n, (S1, s1), (S2, s2), cands)
	      else fail ("constant / constant clash") (* fail with no candidates *)
            | (I.Def (d1), I.Def (d2)) =>
	      if (d1 = d2)		(* because of strictness *)
		then LFmatchSpine (Gglobal, G, d, n, (S1, s1), (S2, s2), cands)
	      else LFmatchExpW (Gglobal, G, d, n, Whnf.expandDef Us1, Whnf.expandDef Us2, cands)
	    | (I.Def (d1), _) => LFmatchExpW (Gglobal, G, d, n, Whnf.expandDef Us1, Us2, cands)
	    | (_, I.Def (d2)) => LFmatchExpW (Gglobal, G, d, n, Us1, Whnf.expandDef Us2, cands)
	    | (I.BVar (I.Fixed k1), I.Const _) =>
	      if (k1 > d) andalso (k1 <= (d + n))
		then 
		  (* failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
		  *)
		  case (I.ctxLookup(I.mergeCtx(Gglobal, G), k1))
		    of (D.InstantiableDec (D.NormalDec (_, D.LF(isP, A)))) => (case D.whnfP isP
										 of D.Param =>  fail ("variable clash")
									       | D.Existential => failAdd (k1-d, cands)
									       | D.PVar _ => crash() )
		     | _ => fail ("variable clash")
		  
	      else fail ("local variable / constant clash") (* otherwise fail with no candidates *)

	    | (I.Const _, I.BVar _) =>
		fail ("constant / local variable clash")
	    | (B1 as I.BVar (I.Fixed k1), B2 as I.BVar(I.BVarVar ((_, Avar, list, cnstrs), s0))) => 
		  (* list contains a list of which elements in the context are parameters..
		   * this is needed for LF since it doesn't have this information, but we can ignore this here..
		   *)
                   let
		     val (Aopt) = 
		       case (I.ctxLookup(I.mergeCtx(Gglobal, G), k1))
		                    of (D.NonInstantiableDec (D.NewDecLF (_,A))) => SOME (I.EClo(A, I.Shift k1))
			             | (D.InstantiableDec (D.NormalDec (_, D.LF(isP, A)))) => (case D.whnfP isP
											     of D.Param =>  SOME (I.EClo(A, I.Shift k1)) 
											      | D.Existential => NONE
											      | D.PVar _ => crash() )
				     | _ => NONE
		   in
		     case Aopt
		       of NONE => (* k1 is existential *)
			        if (k1 > d) andalso (k1 <= (d + n))
				  then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *) 
				else fail ("parameter / local variable clash") (* otherwise fail with no candidates *) 
			| SOME A =>
			          (let
				     val cands' = LFmatchExp(Gglobal, G, d, n, (A, s1), (Avar, I.comp(s0,s2)), cands)
				     (* val b = removeSideEffects (fn () => U.LFunifiable(D.coerceCtx G, (A, s1), (Avar, I.comp(s0, s2)))) *)
				   in
				     case cands'
				       of Fail => fail ("parameter / local variable clash")
					| _ => (addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, D.Quote (I.EClo Us1), D.Quote (I.EClo Us2)), 
							LFmatchSpine (Gglobal, G, d, n, (S1, s1), (S2, s2), cands')))
				   end
				   )
		   end


	    | (I.Const _, I.Proj _) => fail ("constant / block projection clash")
            | (I.Proj _, I.Const _) => fail ("block projection / constant clash")
            | (I.Proj _, I.BVar _) => fail ("block projection / local variable clash")

             (* We can now have BVarVars on the left as we call this procedure when we
	      * check the type to see if it is splittable in the current context 
	      *)
	    | (I.BVar (I.BVarVar _), I.Const _) => fail ("parameter variable / constant clash")


	    | (I.BVar(I.BVarVar ((_, Avar, list, cnstrs), s0)), I.BVar B2) => 
					 (* We can have BVarVars on the left as we call this
					   * procedure when we check the type to see if it is
					   * splittable in the current context.
					   *)

		  (* list contains a list of which elements in the context are parameters..
		   * this is needed for LF since it doesn't have this information, but we can ignore this here..
		   *)
                   let
		     val (Aopt) = case B2
		                  of (I.Fixed k1) => 
				    (case (I.ctxLookup(I.mergeCtx(Gglobal, G), k1))
				      of (D.NonInstantiableDec (D.NewDecLF (_,A))) => SOME (I.EClo(A, I.Shift k1))
				       | (D.InstantiableDec (D.NormalDec (_, D.LF(isP, A)))) => (case D.whnfP isP
											     of D.Param =>  SOME (I.EClo(A, I.Shift k1)) 
											      | D.Existential => NONE
											      | D.PVar _ => crash() )
				       | _ => NONE)
				   | (I.BVarVar ((_, Avar', _, _), s')) => SOME (I.EClo(Avar', s'))
		   in
		     case Aopt
		       of NONE => (* B2 is existential *)
			         (case B2
				   of (I.Fixed k1) => if (k1 > d) andalso (k1 <= (d + n))
							then failAdd(k1-d, cands)
						      else
							fail ("parameter / local variable clash")
				    | _ => crash())
				  
			| SOME A =>
			          (let
				     val cands' = LFmatchExp(Gglobal, G, d, n, (Avar, I.comp(s0,s1)), (A, s2), cands)
				   in
				     case cands'
				       of Fail => fail ("parameter / local variable clash")
					| _ => (addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, D.Quote (I.EClo Us1), D.Quote (I.EClo Us2)), 
							LFmatchSpine (Gglobal, G, d, n, (S1, s1), (S2, s2), cands')))
				   end
				   )
		   end
		   

            (* no other cases should be possible *)
	    | _ => crash () (* ("mistype root or perhaps FVars!!! have not been removed.  ") *)
	    )
      | LFmatchExpW (Gglobal, G, d, n, (I.Lam (D1, U1), s1), (I.Lam (D2, U2), s2), cands) =
	   LFmatchExp (Gglobal, I.Decl (G, revCoerceDec (I.decSub (D1, s1))), d+1, n, (U1, I.dot1 s1), (U2, I.dot1 s2), cands)
      | LFmatchExpW (Gglobal, G, d, n, (I.Lam (D1, U1), s1), (U2, s2), cands) =
	   (* eta-expand *)
	   LFmatchExp (Gglobal, I.Decl (G, revCoerceDec (I.decSub (D1, s1))), d+1, n,
		     (U1, I.dot1 s1),
		     (I.Redex (I.EClo (U2, I.shift),
			       I.App (I.Root (I.BVar (I.Fixed 1), I.Nil), I.Nil)),
		      I.dot1 s2),
		     cands)
      | LFmatchExpW (Gglobal, G, d, n, (U1, s1), (I.Lam (D2, U2), s2), cands) =
	   (* eta-expand *)
	   LFmatchExp (Gglobal, I.Decl (G, revCoerceDec (I.decSub (D2, s2))), d+1, n,
		     (I.Redex (I.EClo (U1, I.shift),
			       I.App (I.Root (I.BVar (I.Fixed 1), I.Nil), I.Nil)),
		      I.dot1 s1),
		     (U2, I.dot1 s2),
		     cands)
      | LFmatchExpW (Gglobal, G, d, n, Us1, Us2 as (I.EVar _, s2), cands) =
	   addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, D.Quote (I.EClo Us1), D.Quote (I.EClo Us2)), cands)

      | LFmatchExpW (Gglobal, G, d, n, (I.Pi ((D1, _), V1), s1), (I.Pi ((D2, _), V2), s2), cands) =
	let 
	  val cands' = LFmatchDec (Gglobal, G, d, n, (D1, s1), (D2, s2), cands)
	in
	  LFmatchExp (Gglobal, I.Decl (G, revCoerceDec (I.decSub(D1, s1))), d+1, n, (V1, I.dot1 s1), (V2, I.dot1 s2), cands')
	end 

      | LFmatchExpW (Gglobal, G, d, n, Us1 as (I.Pi ((_, _), _), _), Us2 as (I.Root (I.Def _, _), _), cands) =
	    LFmatchExp (Gglobal, G, d, n, Us1, Whnf.expandDef Us2, cands)

      | LFmatchExpW (Gglobal, G, d, n, Us1 as (I.Root (I.Def _, _), _), Us2 as (I.Pi ((_, _), _), _), cands) =
	    LFmatchExp (Gglobal, G, d, n, Whnf.expandDef Us1, Us2, cands)



      | LFmatchExpW (Gglobal, G, d, n, (I.Pi _, _), _, cands) = fail "Pi mismatch"
      | LFmatchExpW (Gglobal, G, d, n, _, (I.Pi _, _), cands) = fail "Pi mismatch"

      (* As we now are using LFmatchExp also for checking if something is splittable, we can encounter EVars on the left *)   
      | LFmatchExpW (Gglobal, G, d, n, Us1 as (I.EVar _, s2), Us2, cands) =
	(* ADAM WARNING:  We are using this routine to determine if two types are equal and whether the global context gets in the way.
	 * However, this may succeed with "Eqns" and then the real unification still fail due to a clash with things in the global
	 * context.  Therefore, if this routine return Eqns we need to handle it carefully!
	 * UPDATE (Jan 2008):  We handle these cases by doing an occurs check.
	 *)
	   addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, D.Quote (I.EClo Us1), D.Quote (I.EClo Us2)), cands)
	
      | LFmatchExpW (Gglobal, G, d, n, (I.Uni _, _), (I.Uni _, _), cands) = cands

      (* nothing else should be possible, by invariants *)
      (* No I.FgnExp, and no I.Redex by whnf *)
      | LFmatchExpW _ = crash () (* ("incompatible exp (mistyped)") *)

    and LFmatchDec (Gglobal, G, d, n, (I.Dec (_, V1), s1), (I.Dec (_, V2), s2), cands) =
          LFmatchExp (Gglobal, G, d, n, (V1, s1), (V2, s2), cands)
      | LFmatchDec _ = crash() (* BDec should be impossible here *)

    and LFmatchSpine (Gglobal, G, d, n, (I.Nil, _), (I.Nil, _), cands) = cands
      | LFmatchSpine (Gglobal, G, d, n, (I.SClo (S1, s1'), s1), Ss2, cands) =
          LFmatchSpine (Gglobal, G, d, n, (S1, I.comp (s1', s1)), Ss2, cands)
      | LFmatchSpine (Gglobal, G, d, n, Ss1, (I.SClo (S2, s2'), s2), cands) =
	  LFmatchSpine (Gglobal, G, d, n, Ss1, (S2, I.comp (s2', s2)), cands)
      | LFmatchSpine (Gglobal, G, d, n, (I.App (U1, S1), s1), (I.App (U2, S2), s2), cands) =
	let
	  val cands' = LFmatchExp (Gglobal, G, d, n, (U1, s1), (U2, s2), cands)
	in
	  LFmatchSpine (Gglobal, G, d, n, (S1, s1), (S2, s2), cands')
	end
      | LFmatchSpine _ = crash () (* fail("incompatible spines (mistyped heads)") *)


    fun matchExp(Gglobal, G, d, n, E1, E2, cands) = matchExpW (Gglobal, G, d, n, D.whnfE E1, D.whnfE E2, cands)
    and matchExpW(Gglobal, G, d, n, E1 as D.Var (D.Fixed i, fileInfo1), E2 as D.Var (D.Fixed j, _), cands) = if (i=j) then cands else fail "Incompatible Vars" 
      | matchExpW(Gglobal, G, d, n, E1 as D.Var (D.Fixed i, fileInfo1), E2 as D.Var _ (* BVar *), cands) = addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, E1, E2), cands)
      | matchExpW(Gglobal, G, d, n, D.Var (B1, _), E2 as D.Quote _, cands) =
            (case (D.coerceBoundVar B1)
	       of U1 => matchExp(Gglobal, G, d, n, D.Quote U1, E2, cands)
		(* | NONE => crash() (* B1 must be "Fixed _", so it will not get here *) *)
             )
      | matchExpW(Gglobal, G, d, n, E1 as D.Quote _, E2 as D.Var (B1, _), cands) =
            (case (D.coerceBoundVar B1)
	       of U1 => matchExp(Gglobal, G, d, n, E1, D.Quote U1, cands)
		(* | NONE => crash() (* this means that B1 is meta, which means we have a type error! *) *)
             )

      | matchExpW(Gglobal, G, d, n, D.Quote U1, D.Quote U2, cands) = LFmatchExp(Gglobal, G, d, n, (U1, I.id), (U2, I.id), cands)
      | matchExpW(Gglobal, G, d, n, D.Unit, D.Unit, cands) = cands
      | matchExpW(Gglobal, G, d, n, D.New (D1, E1, _), D.New (D2, E2, _), cands)
	       = matchExp(Gglobal, I.Decl(G, (D.NonInstantiableDec D1)), d+1, n, E1, E2, cands)
      | matchExpW(Gglobal, G, d, n, D.Pair(E1, E2, _), D.Pair(EE1, EE2, _), cands) =
	       matchExp(Gglobal, G, d, n, E2, EE2, matchExp(Gglobal, G, d, n, E1, EE1, cands))
      | matchExpW(Gglobal, G, d, n, E1, E2 as D.EVar _, cands) = addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, E1, E2), cands)
      | matchExpW (Gglobal, G, d, n, E1, E2, cands) = fail "Incompatible Delphin Exps"
	      
    (* matchCaseBranch (context, depth, numSplittableVars, goal, clause) *)
    fun matchPats (Gglobal, G, d, n, [], [], cands) = cands
      | matchPats (Gglobal, G, d, n, (_, E1)::pats1, (_,E2)::pats2, cands) =
            matchPats(Gglobal, G, d, n, pats1, pats2, matchExp(Gglobal, G, d, n, E1, E2, cands))
      | matchPats _ = crash() (* not type correct if different number of pats *)

    fun matchCaseBranch (Gglobal, G, d, n, D.Match(pats1, _ (* Unit *)), D.Match(pats2, _), cands) =
	      matchPats(Gglobal, G, d, n, pats1, pats2, cands)
      | matchCaseBranch (Gglobal, G, d, n, D.NewC(D1, C1, _), D.NewC(D2, C2, _), cands) =
	      matchCaseBranch(Gglobal, I.Decl(G, (D.NonInstantiableDec D1)), d+1, n, C1, C2, cands)
      | matchCaseBranch _ = crash() (* No Eps or PopC in goals or clauses *)



    (* evalPattern E = E'
     * where the pattern E is evaluated to E'.
     * This is only necessary because patterns can be of the form "E \x"
     * and when we instantiate E with a logic variable, we need to reduce this.
     *)
    fun evalPattern E = evalPatternW (D.whnfE E)
    and evalPatternW (D.New(D, E, fileInfo)) = D.New(D, evalPattern E, fileInfo)
      | evalPatternW (D.Pair (E1, E2, F)) = D.Pair (evalPattern E1, evalPattern E2, F)
      | evalPatternW (D.ExpList Elist) =  D.ExpList (map evalPattern Elist) (* note: not possible in pattern *)
      | evalPatternW (D.Pop (i, E, fileInfo)) = 
                             (case (evalPattern E)
				   of (D.New(_, V, fileInfo)) => D.substE'(V, D.shiftTo(i-1, D.id))
				     | (D.EVar ((r (* ref NONE *), F), t)) => 
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

				     | V => crash() (* impossible *)
					      (* D.Pop(i, V, fileInfo) *)

				  )
      | evalPatternW E = E (* other cases are not evaluated *)
     

    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)


    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)

    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) =
	let
	  val w' = weaken (G', a)
	in
	  if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
	end
      | weaken (I.Decl(G', I.NDec), a) = 
	let
	  val w' = weaken (G', a)
	in
	  I.comp (w', I.shift)
	end
      | weaken _ = crash() (* unexpected LF Declaration ... there are no more blocks! *)


    fun generateLF_EVar (Gglobal, Glocal, A, sc) = generateLF_EVarW (Gglobal, Glocal, Whnf.whnf (A, I.id), sc)
    and generateLF_EVarW (Gglobal, Glocal, (I.Pi((D, P), V), s), sc) =
          let
	    val D' = I.decSub (D, s)
	  in
	    generateLF_EVar (Gglobal, I.Decl(Glocal, D'), I.EClo (V, I.dot1 s), fn U => sc (I.Lam(D', U)))
	  end

      | generateLF_EVarW (Gglobal, Glocal, Vs, sc) =
	  let
	    val w = weaken(Glocal, I.targetFam (I.EClo Vs))  (* Glocal |- w :  G'     *)
	    val iw = Whnf.invert w                           (* G'     |- iw : Glocal *)
	    val G' = Whnf.strengthen (iw, Glocal)
	    (* ADAM WARNING:  iw contains Undefs.. so maybe we should do invertExp here instead...
             * -- U.LFapplyInv2Exp (true (* pruning *), Gglobal, Glocal, I.EClo Vs, iw)
	     *    handle U.Error s => raise CoverageError ("VERY UNEPECTED ERROR:  " ^ s)
	     * UPDATE:  It is faster not to do pruning... and as it is subordinate
	     *          it should be safe to have Undefs in there...
	     *          The Twelf version doesn't use pruning here either..
	     *)
	      
	    val X' = I.newEVar (G', I.EClo (I.EClo Vs, iw))  (* G' |- X' : Vs[iw] *)
	    val X = I.EClo (X', w)                            (* Glocal |- X : Vs *)
	  in
	    sc X
	  end





    (* createSub (Gglobal, G) = t 
     * such that . |- t : G
     * and t is filled with EVars in context "."
     * Used to fill in "epsilons", so context only has InstantiableDecs...
     * Gglobal contains the global context of parameters to be used when creating BVarLFs...
     *)		     
    fun createSub(Gglobal, I.Null) = D.id
      | createSub(Gglobal, I.Decl(G, D.InstantiableDec (D.NormalDec(_, D.LF(isP, A))))) = 
          (case (D.whnfP isP)
	     of D.Existential => 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- A : type     *)
		     val A' = I.EClo(A, D.coerceSub t')    (* . |- A[t'] : type *)
		     val X = D.Quote(generateLF_EVar (D.coerceCtx Gglobal, I.Null, A', fn U => U))
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end
              | D.Param => 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- A : type     *)
		     val A' = I.EClo(A, D.coerceSub t')    (* . |- A[t'] : type *)
		     val X = D.Var(D.BVarLF ((ref NONE, A',D.makeLFParamList Gglobal, ref nil), I.id), NONE)
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end
              | _ => crash() )

      | createSub(Gglobal, I.Decl(G, D.InstantiableDec (D.NormalDec(_, D.Meta(F))))) = 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- F : type     *)
		     val F' = D.FClo(F, D.coerceSub t')    (* . |- F[t'] : type *)
		     val X = D.newEVar(F')
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end
            (* When we allowed meta-level parameters...
              | D.Param => 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- F : type     *)
		     val F' = D.FClo(F, D.coerceSub t')    (* . |- A[t'] : type *)
		     val X = D.Var(D.BVarMeta ((ref NONE, F'), D.id), NONE)
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end
             *)


      | createSub _ = crash() (* broken invariant *)


    fun createEVarSpine (Gglobal, G, Vs) = createEVarSpineW (Gglobal, G, Whnf.whnf Vs)
    and createEVarSpineW (Gglobal, G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (Gglobal, G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =  
	let (* Gglobal,G |- V1[s] : L *)
	  val X = generateLF_EVar (Gglobal, G, I.EClo (V1, s), fn U => U)
	  val (S, Vs) = createEVarSpine (Gglobal, G, (V2, I.Dot (I.Exp (X), s)))
	in
	  (I.App (X, S), Vs)
	end
      (* Uni or other cases should be impossible *)
      | createEVarSpineW _ = crash()




(* REMOVED -- ABP.. was used in generateEVar but now Params must ALWAYS be in the empty world...
    (* mayContainInWorld is very similar to WorldSubsumption.containInWorld.
     * The key difference is that if matching A in the world fails due to
     * global variables getting in the way, it will return *true* as
     * it may match during runtime.  In WorldSubsumption it will return false
     * but here *false* tells the coverage checker to ignore something, so it is 
     * not safe in this setting.
     *)

    fun maybeContains(Gglobal, G, A1, []) = false
      | maybeContains(Gglobal, G, A1, (G',A')::Alist2) =
            (* Gglobal,G |- A1 : type
	     * G' |- A' : type 
	     *)
             let
	       (* Note that G MUST ONLY contains NonInstantiable parameters.. not global pattern variables!! *)
	       val A2 = WorldSubsumption.reduce(Gglobal, G', A', G) (* G |- A' : type *)


	       fun getResult () =
		 let
		   val b = case (LFmatchExp(Gglobal, G, I.ctxLength G, I.ctxLength Gglobal, (A1, I.id), (A2, I.id), Eqns (nil)))
		        of (Cands _) => true (* The type may match, but it would require refining a "global" pattern variable.
					      * i.e. a pattern variable from an outer case statement..
					      *)
			 | Fail => false
			 | Eqns _ => U.LFunifiable (D.coerceCtx Gglobal, D.coerceCtx G, (A1, I.id), (A2, I.id))
		 in
		   b
		 end
	     in
	       (removeSideEffects getResult) orelse maybeContains (Gglobal, G, A1, Alist2)
	     end


    fun mayContainInWorld(Gglobal, G, A1, D.Anything) = true
      | mayContainInWorld(Gglobal, G, A1, D.VarList vList) = maybeContains(Gglobal, G, A1, vList)

*)

    (* globalOccursLF (Us, n) = bool
     * Global,G |- Us : wff where |G| = n
     * true if any index inside the Global context occurs free. (i.e. any index > n)
     *)
    fun globalOccursLF (Us, n) = 
      let
	fun occursLF_Exp (p, Us) = occursLF_ExpW (p, Whnf.whnf Us)
	and occursLF_ExpW (_, (I.Uni _, _)) = false
	  | occursLF_ExpW (p, (I.Lam (D, U), s)) =
               occursLF_Dec(p, (D, s))
	       orelse occursLF_Exp (p+1, (U, I.dot1 s))
	  | occursLF_ExpW (p, (I.Pi ((D', _), U), s)) =
	       occursLF_Dec (p, (D', s)) orelse occursLF_Exp (p+1, (U, I.dot1 s))
	  | occursLF_ExpW (p, (I.Root (H, S), _(* id *) )) =
	        (case H
		   of (I.BVar (I.Fixed k')) => 
		     if (k' >= p) then true
		     else occursSpine (p, (S, I.id))
		 | I.BVar (I.BVarVar ((r, A, list, cnstrs), s)) => occursLF_Exp(p, (A, s)) orelse occursSpine(p, (S, I.id))
		 | _ => occursSpine (p, (S, I.id)))
	  | occursLF_ExpW (p, (I.EVar(r, G, A, cnstrs), s)) =
		   (* A makes sense with respect to Gglobal, G *)
		   occursLF_Exp (I.ctxLength G, (A, s))
	  | occursLF_ExpW (p, Us (* anything else *) ) = false (* not in Delphin (i.e. fgnexp) *)

	and occursLF_Dec (p, (I.Dec (_, V), s)) =
		    occursLF_Exp (p, (V, s))
	  | occursLF_Dec _ = crash() (* unexpected dec *)


	and occursSpine (_, (I.Nil, _)) = false
	  | occursSpine (p, (I.App (U, S), s)) = 
		    occursLF_Exp (p, (U, s)) orelse occursSpine (p, (S, s))
	  | occursSpine (p, (I.SClo (S, s'), s)) = occursSpine (p, (S, I.comp(s', s)))
      in
        occursLF_Exp (n+1, Us)
      end



    fun constCasesSig (Gglobal, GX, Vgiven, nil, sc) = []
      | constCasesSig (Gglobal, GX, Vgiven, I.Const(cid)::sgn', sc) =
          let
	    val list' = constCasesSig(Gglobal, GX, Vgiven, sgn', sc)

	    val V' = I.constType cid
	    val (S', Vs') = createEVarSpine (D.coerceCtx Gglobal, GX, (V', I.id))
	    val instantiation = I.Root(I.Const cid, S')

	    fun getResult () =
	      let
		val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
		        of (Cands _) => (raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			 | Fail => false
			 | Eqns _ => if (U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs'))
			             then true
				     else (* It may be possible that it failed due to "global" pattern variables. *)
				           if globalOccursLF ((Vgiven, I.id), I.ctxLength GX) then
					     raise ImpossibleSplit
					   else
					     false (* As the global variables do not appear anywhere,
						    * this would be the same unification problem in the empty context,
						    * so it really does not unify.
						    *)
						   
	      in
		if b then (sc instantiation)@list' else list'
	      end
	  in
	    removeSideEffects getResult
	  end
      | constCasesSig _ = crash()


    fun worldCases (D.Anything, Gglobal, GX, Vgiven, sc) = raise ImpossibleSplit (* Impossible to do coverage if world is Anything!!! *)
      | worldCases (D.VarList [], Gglobal, GX, Vgiven, sc) = []
      | worldCases (D.VarList ((paramCtx, paramType)::varList), Gglobal, GX, Vgiven, sc) =
          let
	    val list = worldCases (D.VarList varList, Gglobal, GX, Vgiven, sc)


	    fun makeDecCtx I.Null = I.Null
	      | makeDecCtx (I.Decl(G, D)) = I.Decl(makeDecCtx G, D.InstantiableDec D)

	    val t = D.coerceSub (createSub (I.mergeCtx(Gglobal, revCoerceCtx GX), makeDecCtx paramCtx)) 
	                          (* . |- t : paramCtx  
                           and Gglobal |- t : Gglobal,paramCtx *)

	    val V = I.EClo(paramType, t) (* V makes sense in ., need to shift by |GX| *)

	    val (S', Vs') = createEVarSpine (D.coerceCtx Gglobal, GX, (V, I.Shift (I.ctxLength GX)))
	     
	    val instantiation = I.Root(I.BVar (I.BVarVar ((ref NONE, V, D.makeLFParamList Gglobal, ref nil), I.Shift (I.ctxLength GX))), S')

	    fun getResult() =
	      let 

		val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
		        of (Cands _) => (raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			 | Fail => false
			 | Eqns _ => if (U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs'))
			             then true
				     else (* It may be possible that it failed due to "global" pattern variables. *)
				           if globalOccursLF ((Vgiven, I.id), I.ctxLength GX) then
					     raise ImpossibleSplit
					   else
					     false (* As the global variables do not appear anywhere,
						    * this would be the same unification problem in the empty context,
						    * so it really does not unify.
						    *)


	      in
		if b then (sc instantiation)@list else list
	      end

	  in
	    removeSideEffects getResult
	  end


    (* Goes through all elements >= k of Gglobal *)
    fun constCasesCtx (Gglobal, GX, Vgiven, 0, sc) = []
      | constCasesCtx (Gglobal, GX, Vgiven, k, sc) =
         (case I.ctxLookup (Gglobal, k)
	    of D.NonInstantiableDec (D.NewDecWorld (_, W)) => 
	         let
		   val list = constCasesCtx (Gglobal, GX, Vgiven, k-1, sc)
		   val list2 = worldCases (W, Gglobal, GX, Vgiven, sc)
		 in
		   list2 @ list
		 end

	     | D.NonInstantiableDec (D.NewDecLF (_, V)) =>  
	         let
		   val list = constCasesCtx (Gglobal, GX, Vgiven, k-1, sc)
		   val V = I.EClo(V, I.Shift (k+ (I.ctxLength GX) ))
		   val (S', Vs') = createEVarSpine (D.coerceCtx Gglobal, GX, (V, I.id))
		   val instantiation = I.Root(I.BVar (I.Fixed k), S')

		   fun getResult () =
		     let
		       val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
			 of (Cands _) => (raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			 | Fail => false
			 | Eqns _ => if (U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs'))
			             then true
				     else (* It may be possible that it failed due to "global" pattern variables. *)
				           if globalOccursLF ((Vgiven, I.id), I.ctxLength GX) then
					     raise ImpossibleSplit
					   else
					     false (* As the global variables do not appear anywhere,
						    * this would be the same unification problem in the empty context,
						    * so it really does not unify.
						    *)

		     in 
		       if b then (sc instantiation)@list else list
		     end

		 in
		   removeSideEffects getResult
		 end
	     | _ => constCasesCtx (Gglobal, GX, Vgiven, k-1, sc))



    fun paramCases (Gglobal, GX, Vgiven, 0, sc) = []
      | paramCases (Gglobal, GX, Vgiven, k, sc) =
          let
	    val list = paramCases (Gglobal, GX, Vgiven, k-1, sc)

	    val V = case  I.ctxDec (GX, k)
	            of I.Dec (_, V) => V
		     | _ => crash() 
	    val (S', Vs') = createEVarSpine (D.coerceCtx Gglobal, GX, (V, I.id))
	    val instantiation = I.Root(I.BVar (I.Fixed k), S')

	    fun getResult () =
	       let

		val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
		        of (Cands _) => (raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			 | Fail => false
			 | Eqns _ => if (U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs'))
			             then true
				     else (* It may be possible that it failed due to "global" pattern variables. *)
				           if globalOccursLF ((Vgiven, I.id), I.ctxLength GX) then
					     raise ImpossibleSplit
					   else
					     false (* As the global variables do not appear anywhere,
						    * this would be the same unification problem in the empty context,
						    * so it really does not unify.
						    *)

	       in 
		 if b then (sc instantiation)@list else list
	       end
	  in
	    removeSideEffects getResult
	  end


    (* Precondition:  Glocal only contains NonInstantiableDecs *)
    (* sc is a continuation executed on EVERY possibility *)
    fun generateEVar (Gglobal, Glocal, D.NormalDec(_, D.LF(isP, A)), sc) = 
         (case (D.whnfP isP)
	    of (D.Existential) => 
                let
		  val M = D.Quote(generateLF_EVar (D.coerceCtx Gglobal, D.coerceCtx Glocal, A, fn U => U))
		in
		  sc M
		end

	     | (D.Param) =>		
		(* For functions over A# we require the world to be empty and test for two cases:
		 *   (1) Variables before Glocal are captured.
		 *   (2) Compatible Variables of type A in Glocal are also captured.
		 * EXCEPTION, if Gglobal does not have any parameters, then case (1) is not necessary
		 *)
		let

		  fun noParams (I.Null) = true
		    | noParams (I.Decl(G, D.NonInstantiableDec (D.NewDecWorld (_, D.VarList [])))) = 
		                            noParams G (* there is
							* a world but 
							* it is empty..
							*)
		    | noParams (I.Decl(G, D.NonInstantiableDec (D.NewDecWorld _))) = false
		    | noParams (I.Decl(G, D.NonInstantiableDec _)) = false
		    | noParams (I.Decl(G, D.InstantiableDec _)) = noParams G


		  val case1 = if (noParams Gglobal) (*NOT necessary: andalso (I.ctxLength Glocal = 0) *)  then [] else
		         (* Case (1)..*)
		         let 
			   val sizeG = I.ctxLength Glocal
			     
			   fun inverse(0) = I.id
			     | inverse(n) = I.Dot(I.Undef, inverse(n-1))
			     
			   val t = inverse sizeG  (*  .  |- t : Glocal *)


			   fun getResult () = 
			     let
			       val Aopt' = SOME(U.LFapplyInv2Exp (true (* pruning on or off??? *), D.coerceCtx Gglobal, D.coerceCtx Glocal, A, t)) (*  EVars are only raised up to Glocal *)
				 handle U.Error _ => NONE
			     in
			       case Aopt' of 
			          NONE => []
				| SOME A' => 
				    let
				      (* Check if this case is impossible! *)
				      fun checkPossibilityWorld W = 
					         let
						   val list = worldCases (W, Gglobal, I.Null, A', (fn U => [true]))
						     handle ImpossibleSplit => [true] (* it is possible it will match *)
						 in
						   (List.length list) > 0
						 end
				      fun checkPossibility 0 = false
					| checkPossibility k =
						 (checkPossibility (k-1)) orelse
						    (case I.ctxLookup (Gglobal, k)
						       of D.NonInstantiableDec (D.NewDecWorld (_, W)) =>
							     checkPossibilityWorld W

							| D.NonInstantiableDec (D.NewDecLF (_, V)) =>
							     let
							       val V = I.EClo(V, I.Shift (k))

							       fun getResult () =
								 (case (LFmatchExp(Gglobal, I.Null, 0, I.ctxLength Gglobal, (A', I.id), 
											    (V, I.id), Eqns (nil)))
								    of (Cands _) => true (* it is possible it will match *)
								      | Fail => false
								      | Eqns _ => if (U.LFunifiable (D.coerceCtx Gglobal, I.Null, (A', I.id), (V, I.id)))
										    then true
										  else 
										    (* It may be possible that it failed due to "global" pattern variables. *)
										    if globalOccursLF ((V, I.id), 0) then
										      true (* it is possible it will match *)
										    else
										      false (* As the global variables do not appear anywhere,
											     * this would be the same unification problem in the empty context,
											     * so it really does not unify.
											     *)
								)
							     in
							       removeSideEffects getResult
							     end

							 | _ => false)

				    in
				      if checkPossibility(I.ctxLength Gglobal) then
					   sc (D.Var (D.BVarLF ((ref NONE, A',D.makeLFParamList Gglobal, ref nil), I.Shift sizeG), NONE))
				      else
					[]
				    end
			     end

			 in
			   removeSideEffects getResult
			 end

		  val case2 = 
		         (* Case (2)..*)
		         let

			   (* matchVars takes a context and tries to match all things in that context *)
			   fun matchVars(I.Null, varNumber) = []
			     | matchVars(I.Decl(G, D.NonInstantiableDec (D.NewDecLF(_, Avar))), varNumber) =
			          let
				    fun getResult () =
				      let 
					val b = U.LFunifiable(D.coerceCtx Gglobal, D.coerceCtx Glocal, (A, I.id), (Avar, I.Shift varNumber)) 
				      in
					if b then sc (D.Var(D.Fixed varNumber, NONE)) else []
				      end

				  in
				    (removeSideEffects getResult) @ (matchVars(G, varNumber+1))
				  end
			     | matchVars (I.Decl(G, _), varNumber) = matchVars(G, varNumber+1)
			 in
			   matchVars(Glocal, 1)
			 end
		in
		  case1 @ case2
		end

            | _ => crash())


      | generateEVar (Gglobal, Glocal, D.NormalDec(_, D.Meta(F)), sc) = 
		(case (D.whnfF F)
		   of D.Top => sc (D.Unit)
		    | D.Exists (D', F') => generateEVar (Gglobal, Glocal, D',
						       fn E1 => generateEVar(Gglobal, Glocal, 
									    D.NormalDec(NONE,D.Meta(D.FClo(F', D.coerceSub (D.Dot(D.Prg E1 , D.id))))),
									    fn E2 => sc (D.Pair (E1, E2, F))))

		    | D.Nabla (D', F') => generateEVar (Gglobal, I.Decl(Glocal, D.NonInstantiableDec D'), 
						      D.NormalDec(NONE, D.Meta(F')),
						      fn E => sc (D.New(D', E, NONE)))
		    | D.FVar _ => crash()
		    | D.FClo _ => crash()
		    | D.FormList _ => crash()
		    | D.All _ =>
		             (* Create a value:  (x \Glocal)
			      * so x has type : Nabla Glocal. F
			      *)
		             let
			       fun raiseType (I.Null, F) = F
				 | raiseType (I.Decl(G, D.NonInstantiableDec D), F) = raiseType(G, D.Nabla(D, F))
				 | raiseType _ = crash() (* broken invariant.. .Glocal only contains NonInstantiableDecs.. *)

			       val X = D.newEVar (raiseType (Glocal, F))

			       (* compute E \G 
				* i.e.  E \(x,y) == (E \x) \y
				*)
			       fun popCtx (I.Null, E) = E 
				 | popCtx (I.Decl(G, D.NonInstantiableDec D), E) = D.Pop(1, popCtx(G, E), NONE)
				 | popCtx _ = crash() (* broken invariant *)
				 
			       val E = popCtx (Glocal, X)
			     in
			       sc E
			     end
			   )



    (* Precondition:  Glocal only contains NonInstantiableDecs *)
    (* sc is a continuation executed on EVERY possibility *)
    (* very similar to generateEVar except it only gets one case..
     * used in convert.fun in creating functions "W with ..."
     *)
    fun generateEVarFirstCase (Gglobal, Glocal, D.NormalDec(_, D.LF(isP, A)), sc) = 
         (case (D.whnfP isP)
	    of (D.Existential) => 
                let
		  val M = D.Quote(generateLF_EVar (D.coerceCtx Gglobal, D.coerceCtx Glocal, A, fn U => U))
		in
		  sc M
		end

	     | (D.Param) =>		
		         (* Case (1)..*)
		         let 
			   val sizeG = I.ctxLength Glocal
			     
			   fun inverse(0) = I.id
			     | inverse(n) = I.Dot(I.Undef, inverse(n-1))
			     
			   val t = inverse sizeG  (*  .  |- t : Glocal *)


			   fun getResult () = 
			     let
			       val Aopt' = SOME(U.LFapplyInv2Exp (true (* pruning on or off??? *), D.coerceCtx Gglobal, D.coerceCtx Glocal, A, t)) (*  EVars are only raised up to Glocal *)
				 handle U.Error _ => NONE
			     in
			       case Aopt' of 
			                   NONE => raise CoverageError "Cannot generate case"
					 | SOME A' => sc (D.Var (D.BVarLF ((ref NONE, A',D.makeLFParamList Gglobal, ref nil), I.Shift sizeG), NONE))
			     end

			 in
			   removeSideEffects getResult
			 end
            | _ => crash())



      | generateEVarFirstCase (Gglobal, Glocal, D.NormalDec(_, D.Meta(F)), sc) = 
		(case (D.whnfF F)
		   of D.Top => sc (D.Unit)
		    | D.Exists (D', F') => generateEVarFirstCase (Gglobal, Glocal, D',
						       fn E1 => generateEVarFirstCase(Gglobal, Glocal, 
									    D.NormalDec(NONE,D.Meta(D.FClo(F', D.coerceSub (D.Dot(D.Prg E1 , D.id))))),
									    fn E2 => sc (D.Pair (E1, E2, F))))

		    | D.Nabla (D', F') => generateEVarFirstCase (Gglobal, I.Decl(Glocal, D.NonInstantiableDec D'), 
						      D.NormalDec(NONE, D.Meta(F')),
						      fn E => sc (D.New(D', E, NONE)))
		    | D.FVar _ => crash()
		    | D.FClo _ => crash()
		    | D.FormList _ => crash()
		    | D.All _ =>
		             (* Create a value:  (x \Glocal)
			      * so x has type : Nabla Glocal. F
			      *)
		             let
			       fun raiseType (I.Null, F) = F
				 | raiseType (I.Decl(G, D.NonInstantiableDec D), F) = raiseType(G, D.Nabla(D, F))
				 | raiseType _ = crash() (* broken invariant.. .Glocal only contains NonInstantiableDecs.. *)

			       val X = D.newEVar (raiseType (Glocal, F))

			       (* compute E \G 
				* i.e.  E \(x,y) == (E \x) \y
				*)
			       fun popCtx (I.Null, E) = E 
				 | popCtx (I.Decl(G, D.NonInstantiableDec D), E) = D.Pop(1, popCtx(G, E), NONE)
				 | popCtx _ = crash() (* broken invariant *)
				 
			       val E = popCtx (Glocal, X)
			     in
			       sc E
			     end
			   )




    (* reduceCase (Gglobal, G, C) = C'
     * where C' is filled in with appropriate EVars such that C' is of the form
     * has no epsilons, pops, and ends with "Unit"
     *)
    fun reduceCase (Gglobal, G, (D.Eps (D.NormalDec(_, D.LF(isP, A)), C, fileInfo))) =
            (case (D.whnfP isP)
	      of D.Existential =>  	     
		      let
			(* val X = I.EVar(ref NONE, D.coerceCtx G, A, ref nil)
			 * This above one would have NDecs 
			 *)
			val X = generateLF_EVar (D.coerceCtx Gglobal, D.coerceCtx G, A, fn U => U)

			val t = D.Dot (D.Prg (D.Quote X), D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)))
		      end


	      | D.Param =>
		      let 
			(* We now make sure we prune away any would-be NDecs from G
                            val X = D.Var (D.BVarLFADAM ((ref NONE, A,D.makeLFParamList (I.mergeCtx(Gglobal, G)), ref nil), I.id), NONE)  
                        *)
			val X = D.Var (D.newParamVarPruneNDecs(Gglobal, G, A), NONE)

			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)))
		      end

              | D.PVar _ => crash() (* should not get to opsem with any PVars *)
            )

      | reduceCase (Gglobal, G, (D.Eps (D.NormalDec(_, D.Meta(F)), C, fileInfo))) =
		      let
			val X = D.newEVar(F)
			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)))
		      end
	  (* no longer have meta-level parameters
	      | D.Param =>                   
		      let 
			val X = D.Var (D.BVarMeta ((ref NONE, F), D.id), NONE)
			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)))
		      end
	  *)

      | reduceCase (Gglobal, G, (D.NewC (D, C, fileInfo))) = D.NewC(D, 
								 reduceCase (Gglobal, I.Decl(G, D.NonInstantiableDec D), C),
								 fileInfo)


      | reduceCase (Gglobal, G, D.Match (pats, _)) = D.Match(map (fn (vis, E) => (vis, evalPattern E)) pats, D.Unit)
      | reduceCase (Gglobal, G, D.PopC _) = crash() (* broken invariant.. no PopCs..removed before calling checkCase *)



    (* matchGoal (G, goal, Clist, klist) = klist' 
     * where "goal" is the coverage goal
     * and Clist is all clauses
     * We add one new list cand for each C to klist to obtain klist'
     *)
    fun matchGoal(G, goal, Clist, Covered) = Covered
      | matchGoal(G, goal, C::Clist, klist) =
            let
	      fun addEps (G, D.Eps(D, C, fileInfo), n) = addEps (I.Decl(G, D.InstantiableDec D), C, n+1)
		| addEps (G, C, n) = (G, C, n)

	      val (G', goal', numVars') = addEps(I.Null, goal, 0)

	      val C0 = D.substCase(C, D.shiftTo(numVars', D.id))  (* G,G' |- C0 is well typed *)
	      val C' = reduceCase(G,G', C0)
	      val cands1 = matchCaseBranch(G, G', 0, numVars', goal', C', Eqns (nil)) 
	      val cands2 = resolveCands cands1
	      val cands3 = checkConstraints(C', cands2)
	    in
	      matchGoal(G, goal, Clist, addKs(cands3, klist))
	    end
      | matchGoal(G, goal, [], klist) = klist







    fun splitEVar (Gglobal, X as I.EVar (_, GX, V, _), sc (* success continuation *) ) =
          let
	    val a = case Whnf.whnf (V, I.id)
	            of (I.Root (I.Const a, _), s) => a
		     | _ => crash()



	    fun newSC U =  (* U makes sense in Gglobal, GX *)
	         let
		   fun getResult () =
		     let
		       val X' = I.EClo(X, I.Shift (I.ctxLength GX))
		       val b = U.LFunifiable (D.coerceCtx Gglobal, GX, (X, I.id), (U, I.id))
		     in
		       if b   then [sc ()]
			      else []
		     end
		 in
		   removeSideEffects getResult
		 end
	    (*
	    fun debugAdam() = 
	        let
		  val _ = print "\nPerforming a split on type:" 
		  val _ = print (Formatter.makestring_fmt (Print.formatExp(I.mergeCtx(D.coerceCtx Gglobal, GX), V)))
		  val _ = print "\n"
		in
		  ()
		end

	    val _ = debugAdam()
	    *)

	    val list1 = constCasesSig (Gglobal, GX, V, Index.lookup a, newSC)
	    val list2 = constCasesCtx (Gglobal, GX, V, I.ctxLength Gglobal, newSC)
	    val list3 = paramCases (Gglobal, GX, V, I.ctxLength GX, newSC)	    
	  in
	    list1 @ list2 @ list3
	  end
      | splitEVar _ = crash()



    (* splitVar (k, G, goal) = SOME (goal list)
                                  or NONE
       where goal list is obtained by splitting kth "epsilon" 
       variable in goal (counting right-to-left).

       returns NONE if splitting variable k fails because of constraints
    *)



    fun splitVar (k, Gglobal, goal) =
        let
	  fun getLocalCtx (G, D.Eps(D, C, fileInfo)) = getLocalCtx (I.Decl(G, D.InstantiableDec D), C)
	    | getLocalCtx (G, C) = (G, C)

	  val (Glocal, goal') = getLocalCtx(I.Null, goal)
	  val t' = createSub(Gglobal, Glocal) (* . |- t' : Glocal, where EVars are created with context "." *)
	                                      (* Therefore, it is also true that Gglobal |- t' : Gglobal,Glocal *)

	    
	  fun getEVar (U, t) = getEVarW (Whnf.whnf (U, t))
	  and getEVarW(I.Lam(_, U), t) = getEVar (U, I.dot1 t)
	    | getEVarW(X as I.EVar _, t) = X
	    | getEVarW _ = crash()

	  fun getEVarFromSub(1, D.Dot(D.Prg (D.Quote E), t)) = SOME (getEVar (E, I.id))
	    | getEVarFromSub(1, D.Dot(D.Prg _, t)) = NONE
	    | getEVarFromSub(n, D.Dot(_, t)) = getEVarFromSub(n-1, t)
	    | getEVarFromSub _ = crash()

	  val goal'' = D.substCase(goal', t')

	in
          (* split on k'th variable, counting from innermost *)
	  case (getEVarFromSub(k, t'))
	    of NONE => NONE
	     | SOME X => 
	      SOME(splitEVar (Gglobal, X, fn () => DelphinAbstract2.abstractCase goal''))
	      handle DelphinAbstract2.LeftOverConstraints => NONE
		   | ImpossibleSplit => NONE
	end

    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)

    (* Finitary Splitting *)
    fun finitary1 (X, k, goal, Gglobal, cands) =
         let

	   (* recursive X = true
	    iff the instantiation of X : {{G}} a @ S contains an
	    EVar Y : {{G'}} b @ S such that a <|= b

	    This means there is no guarantee that X : {{G}} a @ S has only
	    a finite number of instances
	    *)

	   fun recursive (X as I.EVar (ref(SOME(U)), GX, VX, _)) = DelphinAbstract2.isRecursiveOrConstraints(I.targetFam VX, X)
	     | recursive _ = crash()

	   val countOpt = SOME (List.length (splitEVar(Gglobal, X, fn () => if recursive X then raise NotFinitary else DelphinAbstract2.abstractCase goal)))
	     handle ImpossibleSplit => NONE
		  | NotFinitary => NONE
	          | DelphinAbstract2.LeftOverConstraints => NONE

	 in
	   case countOpt 
	     of NONE => cands
	      | SOME n => (k, n)::cands
	 end
	     

	   

      
    fun finitarySplits (D.id, k, goal, Gglobal, cands) = cands
      | finitarySplits (D.Dot(D.Prg (D.Quote U), t), k, goal, Gglobal, cands) =
                let
		  (* EVar was lowered.. so we use this procedure to find it... *)
		  fun getEVar (U, t) = getEVarW (Whnf.whnf (U, t))
		  and getEVarW(I.Lam(_, U), t) = getEVar (U, I.dot1 t)
		    | getEVarW(X as I.EVar _, t) = X
		    | getEVarW _ = crash()

		  val cands' = removeSideEffects (fn () => finitary1 (getEVar (U, I.id), k, goal,  Gglobal, cands))
		in
		  finitarySplits(t, k+1, goal, Gglobal, cands')
		end
				
      | finitarySplits (D.Dot(D.Prg _, t), k, goal, Gglobal, cands) =
                 (* Cannot be split *)
                 finitarySplits(t, k+1, goal, Gglobal, cands)

      | finitarySplits _ = crash() (* impossible *)

    fun finitary(G, goal) =
           let 

	     fun getLocalCtx (G, D.Eps(D, C, fileInfo)) = getLocalCtx (I.Decl(G, D.InstantiableDec D), C)
	       | getLocalCtx (G, C) = (G, C)

	     val (Glocal, goal') = getLocalCtx(I.Null, goal)
	     val t' = createSub(G,Glocal)     (* . |- t' : Glocal, where EVars are created with context "." *)
	                                      (* Therefore, it is also true that G |- t' : G,Glocal *)
	     val goal'' = D.substCase(goal', t')
	   in
	     finitarySplits (t', 1, goal'', G, nil)
	   end






    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)


    fun goalToString(smartInj, printEps, G, goal) = 
          let
	    val _ = PrintDelphinInt.varReset G
	    val C = PrintDelphinInt.convCaseBranch(smartInj, G, goal)
	    val F = PrintDelphinExt.caseBranchToFormat(C, false (* do not print details... (right of "=>" *), printEps  )
	  in
	    Formatter.makestring_fmt F
	  end

    fun goalsToString(smartInj, printEps, G, goals) =
      let
	fun goalsToString'(smartInj, printEps, G, []) = ""
	  | goalsToString'(smartInj, printEps, G, (goal::goals)) = goalToString(smartInj, printEps, G, goal) ^ "\n" ^ goalsToString'(smartInj, printEps, G, goals)

	val leadLine = if printEps then "" 
	               else "NOTE:  To enable printing the types of the pattern variables (epsilons), you must set Delphin.printPatternVars := true\n"
      in
	leadLine ^ (goalsToString'(smartInj, printEps, G, goals))
      end



    (* Get the initial cover goal based on the Formula *)
    (* G is the global context *)
    (* Glocal represents the local parameters that are introduced *)
    (* sc is the success continuation to be applied to EVERY case that results *)
    fun getStartGoal (G, Glocal, F, sc) = getStartGoalW (G, Glocal, D.whnfF F, sc)
    and getStartGoalW (G, Glocal, D.All([(visibility, D)], _), sc) = 
		  generateEVar(G, Glocal, D, fn E => [sc (D.Match([(visibility, E)], D.Unit))])

      | getStartGoalW (G, Glocal, D.All((visibility, D)::Ds, F), sc) = 
		  generateEVar(G, Glocal, D, fn E => getStartGoal(G, Glocal, D.FClo(D.All(Ds, F), I.Dot (D.coerceExp E, I.id)), 
							       fn C => (case C
									  of (D.Match(pats, res)) => sc (D.Match((visibility, E)::pats, res))
									   | _ => crash() (* impossible *) )))

      | getStartGoalW (G, Glocal, D.All([], F), sc) = crash() (* empty list of decs in forall is impossible *)

      | getStartGoalW (G, Glocal, D.Nabla(D, F), sc) = 
		      getStartGoal(G, I.Decl(Glocal, D.NonInstantiableDec D), F, fn C => sc (D.NewC(D, C, NONE)))

      | getStartGoalW (G, Glocal, F, sc) = crash()


    fun cover(G, goal, Clist, missing) =
         let
	   val cands = matchGoal(G, goal, Clist, CandList [])
	   val selection = selectCand cands
	 in
	   split (selection, G, goal, Clist, missing)
	 end
       
    and split(NONE, G, goal, Clist, missing) = missing (* goal is covered! *)
      | split(SOME(nil), G, goal, Clist, missing) = 
           splitWeak(finitary(G, goal), G, goal, Clist, missing)   


      | split(SOME ((k,_)::ksn), G, goal, Clist, missing) =
          (case splitVar (k, G, goal)
	     of SOME(goals) => covers(G, goals, Clist, missing)
	      | NONE => (* splitting variable k generated constraints, so try another *)
	            split(SOME ksn, G, goal, Clist, missing))


    and splitWeak (nil, G, goal, Clist, missing) = goal :: missing
      | splitWeak (ksn, G, goal, Clist, missing) = 
            let
	      (* findMin ((k1,n1),...,(km,nm)) = (ki,ni)
	         where ni is the minimum among the n1,...,nm
	         Invariant: m >= 1
	       *)
	      fun findMin ((k,n)::kns) = findMin'((k,n), kns)
		| findMin _ = crash() 
	      and findMin' ((k0,n0), nil) = (k0,n0)
		| findMin' ((k0,n0), (k',n')::kns) =
		if n' < n0
		  then findMin' ((k',n'), kns)
		else findMin' ((k0,n0), kns)

	    in
              (* commit to the minimal candidate, since no constraints can arise .
	       * NOT TRUE--ABP. I had to change finitary to check that no contraints arise.
	       *)
              split (SOME(findMin ksn::nil), G, goal, Clist, missing)
	    end



    (* check that Clist covers all "goals".  Add missing cases to "missing". 
     * covers(G, goals, Clist, missing) = missing' 
     *)
    and covers(G, [], Clist, missing) = missing
      | covers(G, goal::goals, Clist, missing) =        
          let
	    (*
	    val _ = print "\n\nSTACK OF GOALS = \n"
	    val _ = print (goalsToString(true, G, goals))
	    val _ = print "\nCURRENT GOAL = \n"
	    val _ = print (goalsToString(true, G, [goal]))
	      *)
	  in
           covers(G, goals, Clist, cover (G, goal, Clist, missing))      
	  end

    (* We run the risk of functions not being weakenable whenever the user uses "NewC" (new over cases)
     * We find this desirable for "parameter" functions, but not for others.  
     *
     * Here we check that a list of cases does not use "NewC".... If so, return an error.
     * INVARIANT:  no PopCs exist.
     *)

    fun usesNewC(D.Eps(D, C, fileInfo)) = usesNewC (C)
      | usesNewC(D.NewC(D, C, fileInfo)) = true
      | usesNewC(D.Match (pats, E2)) = false
      | usesNewC(D.PopC _) = crash() (* broken invariant *)

    fun usesNewClist([]) = false
      | usesNewClist(C::Clist) = usesNewC(C) orelse usesNewClist(Clist)



    (* Main Function ... *)
    (* ***************************************************************************************************************** *)
    (* ***************************************************************************************************************** *)

    fun checkCases(smartInj, printEps, G, Clist, F) = 
            let	      
	      (* ABP WARNING:  We need to check that everything in G is named..
	       * otherwise it will print some names as "?" ..
	       *)
	      val G = PrintDelphinInt.ctxName G
			
	      fun initK C = DelphinAbstract2.abstractCase C
		    handle DelphinAbstract2.LeftOverConstraints => raise CoverageError "Cannot get start goal"

	      val goals = getStartGoal (G, I.Null, F, initK)
	      val missing = covers (G, goals, Clist, nil)
	    in
	      case missing 
		        of nil => ()
			 | _ => (raise CoverageError (goalsToString(smartInj, printEps, G, missing)))
	    end


    (* Invariant:  no PopCs *)
    fun checkCaseBody(smartInj, printEps, G, D.Eps(D, C, fileInfo)) = 
                 checkCaseBody(smartInj, printEps, I.Decl(G, D.InstantiableDec D), C)
      | checkCaseBody(smartInj, printEps, G, D.NewC(D, C, fileInfo)) = 
		 checkCaseBody(smartInj, printEps, I.Decl(G, D.NonInstantiableDec D), C)
      | checkCaseBody(smartInj, printEps, G, D.Match(pats, Ebody)) = 
		 checkCovers(smartInj, printEps, G, Ebody)
      | checkCaseBody(smartInj, printEps, G, D.PopC _) = crash() (* broken invariant.. no PopCs..*)


    and checkCovers(smartInj, printEps, G, E) = checkCoversW(smartInj, printEps, G, D.whnfE E)
    and checkCoversW(smartInj, printEps, G, D.Var _) = ()
      | checkCoversW(smartInj, printEps, G, D.Quote _) = ()
      | checkCoversW(smartInj, printEps, G, D.Unit) = ()

      | checkCoversW(smartInj, printEps, G, D.Lam (Clist as (D.PopC(i, _)::_), F, fileInfo)) =
				let
				  fun movePopOutside (D.PopC(j, C')) = if (i = j) then C' else crash() (* broken invariant *)
				    | movePopOutside _ = crash() (* broken invariant *)

				  val Clist' = map movePopOutside Clist

				  fun popCtx(0, G) = crash()
				    | popCtx(1, I.Decl(G, D.NonInstantiableDec D)) = (G, D)
				    | popCtx(1, I.Decl(G, D.InstantiableDec D)) = crash() (* Bad Pop *)
				    | popCtx(i, I.Decl(G, _)) = popCtx (i-1, G)
				    | popCtx _ = crash()

				  val (G', D) = popCtx (i, G)
				  val G'' = D.coerceCtx (I.Decl(G', D.NonInstantiableDec D))
				  val Fnew = D.newFVar(G'')
				  val F' = D.Nabla (D, Fnew)
				  val _ = U.unifyF(I.Null, G'', F, D.FClo(Fnew, I.Shift(i-1)))
				    handle U.Error msg => case fileInfo
				                          of SOME (filename, r) => raise CoverageError (Paths.wrapLoc (Paths.Loc (filename, r), ("CoverageChecker Failed UNEXPECTEDLY (" ^ msg ^ ")"))) (* should never fail! *)
							   | _ => raise CoverageError ("CoverageChecker Failed UNEXPECTEDLY (" ^ msg ^ ")") (* should never fail! *)
				in
				  checkCovers (smartInj, printEps, G,  D.Pop (i, D.Lam (Clist', F', fileInfo), fileInfo))
				end


      | checkCoversW(smartInj, printEps, G, D.Lam (Clist (* and no cases have PopC *), F, fileInfo)) = 
                                        let
					  val _ = (checkCases(smartInj, printEps, G, Clist, F)
                                                   handle CoverageError s => 
							      let 
								val msg = "WARNING:  Match Non-Exhaustive Warning:\n" ^ s ^ "\n"
							      in
								case fileInfo
								  of NONE => raise CoverageError msg
								   | SOME(filename, r) => raise CoverageError (Paths.wrapLoc(Paths.Loc (filename, r), msg))
							      end )
					  val _ = map (fn C => checkCaseBody(smartInj, printEps, G, C)) Clist
					in
					  ()
					end

      | checkCoversW(smartInj, printEps, G, D.New (D, E, _)) = 
				checkCovers(smartInj, printEps, I.Decl(G, D.NonInstantiableDec D), E)

      | checkCoversW(smartInj, printEps, G, D.App (E1, args)) =  
				(checkCovers(smartInj, printEps, G, E1) ; checkCoversArgs(smartInj, printEps, G, args))

      | checkCoversW(smartInj, printEps, G, D.Pair (E1, E2, _)) = 
				(checkCovers(smartInj, printEps, G, E1) ; checkCovers(smartInj, printEps, G, E2))

      | checkCoversW(smartInj, printEps, G, D.ExpList Elist) = 
		       let
			 (* Even if it gets an error, we want to continue on all parts and accumulate the error messages. 
			  * i.e. we want to run the coverage-checker on all mutually recursive functions, even
			  * if one fails.
			  *)
			  fun run([], errorList) = errorList
			    | run(E::Elist, errorList) = 
			         let
				   val errorList' = 
				     (checkCovers(smartInj, printEps, G, E) ; errorList)
				     handle CoverageError s => errorList @ [s]
				 in
				   run(Elist, errorList')
				 end

			  fun listToString [] = ""
			    | listToString (s::ss) = s ^ (listToString ss)
		       in
			 case (run(Elist, []))
			   of [] => ()
			    | sList => raise CoverageError (listToString sList)
		       end

      (* OLD
      | checkCoversW(smartInj, printEps, G, D.ExpList []) = ()

      | checkCoversW(smartInj, printEps, G, D.ExpList (E::Elist)) = 
				(checkCovers(smartInj, printEps, G, E) ; checkCovers(smartInj, printEps, G, D.ExpList Elist))
      *)

      | checkCoversW(smartInj, printEps, G, D.Proj (E, i)) = 
				checkCovers(smartInj, printEps, G, E)

      | checkCoversW(smartInj, printEps, G, D.Pop (i, E, fileInfo)) = 
				checkCovers(smartInj, printEps, D.popCtx(i, G), E)

      | checkCoversW(smartInj, printEps, G, D.Fix (D, E)) = 
				checkCovers(smartInj, printEps, I.Decl(G, D.InstantiableDec D), E)

      | checkCoversW(smartInj, printEps, G, D.EVar r (* ref NONE *)) = ()

      | checkCoversW(smartInj, printEps, G, D.EClo _) = crash() (* impossible by whnf *)



    and checkCoversArgs(smartInj, printEps, G, []) = ()

      | checkCoversArgs(smartInj, printEps, G, (vis, fileInfo, E)::args) = 
                 (checkCovers(smartInj, printEps, G, E) ; checkCoversArgs (smartInj, printEps, G, args))


  end