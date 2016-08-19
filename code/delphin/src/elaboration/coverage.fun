(* Delphin Coverage Checker *)
(* Author: Adam Poswolsky *)
(* Algorithm based on Twelf Coverage (Frank Pfenning & Carsten Schuermann) *)

structure DelphinCoverage =
  struct
    val debug : bool ref = ref true
    exception Error of string
    exception ImpossibleSplit
    exception NotFinitary
    structure I = IntSyn
    structure D = DelphinIntSyntax
    structure U = UnifyDelphinTrail


    fun debugAdam() = ()
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
        (* reversed equations Fri Dec 28 09:39:55 2001 -fp !!! *)
        (* why is this important? --cs !!! *)
        if matchEqns (List.rev es) then (Eqns (nil))
	else Fail
      | resolveCands (Cands (ks)) = Cands (ks)
      | resolveCands (Fail) = Fail


    fun checkConstraints (C', Cands (ks)) = Cands (ks)
      | checkConstraints (C', Fail) = Fail
      | checkConstraints (C', Eqns nil) = 
         if (DelphinAbstract2.hasNoConstraintsCase C') then Eqns (nil) else Fail
      | checkConstraints _ = raise Domain

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
      | revCoerceDec _ = raise Domain (* No blocks/... *)

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
											      | D.PVar _ => raise Domain )
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
									       | D.PVar _ => raise Domain )
		     | _ => fail ("variable clash")
		  
	      else fail ("local variable / constant clash") (* otherwise fail with no candidates *)

	    | (I.Const _, I.BVar _) =>
		fail ("constant / local variable clash")
	    | (B1 as I.BVar (I.Fixed k1), B2 as I.BVar(I.BVarVar ((_, Avar, list), s0))) => 
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
											      | D.PVar _ => raise Domain )
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
            (* no other cases should be possible *)
	    | _ => crash () (* ("mistype root ") *)
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
      | LFmatchExpW (Gglobal, G, d, n, (I.Pi _, _), _, cands) = fail "Pi mismatch"
      | LFmatchExpW (Gglobal, G, d, n, _, (I.Pi _, _), cands) = fail "Pi mismatch"

      (* As we now are using LFmatchExp also for checking if something is splittable, we can encounter EVars on the left *)   
      | LFmatchExpW (Gglobal, G, d, n, Us1 as (I.EVar _, s2), Us2, cands) =
	(* WARNING:  I don't know about this... here I am assuming that some "constraint" won't cause
	 * the EVar to be delayed and later find that it doesn't match due to a "splitting" candidate,
	 * which information would be lost....  Can we get rid of EVars.. this comes up in constcases, paramcases, worldcases...
	 *)
	   addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, D.Quote (I.EClo Us1), D.Quote (I.EClo Us2)), cands)
	

      (* nothing else should be possible, by invariants *)
      (* No I.Uni, I.FgnExp, and no I.Redex by whnf *)
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
    and matchExpW(Gglobal, G, d, n, E1 as D.Var (D.Fixed i, fileInfo1), E2 as D.Var _, cands) = addEqn (Eqn (D.coerceCtx Gglobal, D.coerceCtx G, E1, E2), cands)
      | matchExpW(Gglobal, G, d, n, D.Var (B1, _), E2 as D.Quote _, cands) =
            (case (D.coerceBoundVar B1)
	       of (SOME U1) => matchExp(Gglobal, G, d, n, D.Quote U1, E2, cands)
		| NONE => crash() (* B1 must be "Fixed _", so it will not get here *)
             )
      | matchExpW(Gglobal, G, d, n, E1 as D.Quote _, E2 as D.Var (B1, _), cands) =
            (case (D.coerceBoundVar B1)
	       of (SOME U1) => matchExp(Gglobal, G, d, n, E1, D.Quote U1, cands)
		| NONE => crash() (* this means that B1 is meta, which means we have a type error! *)
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
    fun matchCaseBranch (Gglobal, G, d, n, D.MatchAnd(_, E1, C1), D.MatchAnd(_, E2, C2), cands) =
              matchCaseBranch(Gglobal, G, d, n, C1, C2, matchExp(Gglobal, G, d, n, E1, E2, cands))
      | matchCaseBranch (Gglobal, G, d, n, D.MatchAnd(_, E1, C1), D.Match(_, E2, _ (* D.Unit *)), cands) =
	      (* If clause is not an "MatchAnd" then we do not need to look at C1,
	       * C1 is there as our goals are expanded out as far as possible, but
	       * the clauses do not have to be.
	       *)
	      matchExp(Gglobal, G, d, n, E1, E2, cands)      
      | matchCaseBranch (Gglobal, G, d, n, D.Match(_, E1, _ (* Unit *)), D.Match(_, E2, _), cands) =
	      matchExp(Gglobal, G, d, n, E1, E2, cands)
      | matchCaseBranch (Gglobal, G, d, n, D.NewC(D1, C1, _), D.NewC(D2, C2, _), cands) =
	      matchCaseBranch(Gglobal, I.Decl(G, (D.NonInstantiableDec D1)), d+1, n, C1, C2, cands)
      | matchCaseBranch _ = crash() (* No Eps or PopC in goals or clauses *)



    (* evalPattern E = E'
     * where the pattern E is evaluated to E'.
     * This is only necessary because patterns can be of the form "E \x"
     * and when we instantiate E with a logic variable, we need to reduce this.
     *)
    fun evalPattern E = evalPatternN (D.whnfE E)
    and evalPatternN (D.New(D, E, fileInfo)) = D.New(D, evalPattern E, fileInfo)
      | evalPatternN (D.Pair (E1, E2, F)) = D.Pair (evalPattern E1, evalPattern E2, F)
      | evalPatternN (D.ExpList Elist) =  D.ExpList (map evalPattern Elist) (* note: not possible in pattern *)
      | evalPatternN (D.Pop (i, E)) = 
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
						val newBody = D.EVar ((ref NONE, newF), D.id)
						val _ = r := SOME(D.New(newD, newBody, NONE))
					      in
						D.substE'(newBody, D.shiftTo(i-1, D.dot1 t))
					      end
                                                 
				     | (D.Lam(Clist, F, fileInfo)) => 
					      let
						val shifts = D.shiftTo(i-1, D.id)
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
				     | _ => crash()
				  )
      | evalPatternN E = E (* other cases are not evaluated *)
     

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





    fun generateLF_EVar (Glocal, A, sc) = generateLF_EVarN (Glocal, Whnf.whnf (A, I.id), sc)
    and generateLF_EVarN (Glocal, (I.Pi((D, P), V), s), sc) =
          let
	    val D' = I.decSub (D, s)
	  in
	    generateLF_EVar (I.Decl(Glocal, D'), I.EClo (V, I.dot1 s), fn U => sc (I.Lam(D', U)))
	  end
      | generateLF_EVarN (Glocal, Vs, sc) =
	  let
	    val w = weaken(Glocal, I.targetFam (I.EClo Vs))  (* Glocal |- w :  G'     *)
	    val iw = Whnf.invert w                           (* G'     |- iw : Glocal *)
	    val G' = Whnf.strengthen (iw, Glocal)
	    (* WARNING:  iw contains Undefs.. maybe we should do invertExp here instead... *)
	    val X' = I.newEVar (G', I.EClo (I.EClo Vs, iw))  (* G' |- X' : Vs[iw] *)
	    val X = I.EClo (X', w)                            (* Glocal |- X : Vs *)
	  in
	    sc X
	  end

    (* Precondition:  Glocal only contains NonInstantiableDecs *)
    (* sc is a continuation executed on EVERY possibility *)
    fun generateEVar (getAllCases, world, Gglobal, Glocal, D.NormalDec(_, D.LF(isP, A)), sc) = 
         (case (D.whnfP isP)
	    of D.Existential => 
                let
		  val M = D.Quote(generateLF_EVar (D.coerceCtx Glocal, A, fn U => U))
		in
		  sc M
		end

	     | D.Param =>
		(* For functions over A# we test for two cases:
		 *   (1) Variables before Glocal are captured.
		 *   (2) Compatible Variables of type A in Glocal are also captured.
		 *)
		if WorldSubsumption.containInWorld(Gglobal, Glocal, A, world) then 
		  let
		    val case1 = 
		         (* Case (1)..*)
		         let 
			   val sizeG = I.ctxLength Glocal
			     
			   fun inverse(0) = I.id
			     | inverse(n) = I.Dot(I.Undef, inverse(n-1))
			     
			   val t = inverse sizeG  (*  .  |- t : Glocal *)


			   fun getResult () = 
			     let
			       val Aopt' = SOME(U.LFapplyInv2Exp (true, D.coerceCtx Gglobal, D.coerceCtx Glocal, A, t)) (*  EVars are only raised up to Glocal *)
				 handle U.Error _ => NONE
			     in
			       case Aopt' of 
			                   NONE => []
					 | SOME A' => sc (D.Var (D.BVarLF ((ref NONE, A',D.makeParamList Gglobal), I.Shift sizeG), NONE))
			     end

			 in
			   removeSideEffects getResult
			 end

		    val case2 = if not(getAllCases) then [] else
		         (* Case (2)..*)
		         let
			   (* Try all the parameters in Glocal *)
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
			     | matchVars (I.Decl(G, D.NonInstantiableDec _), varNumber) = matchVars(G, varNumber+1)
			     | matchVars _ = crash()
			   in
			     matchVars(Glocal, 1)
			 end
		  in
		    case1 @ case2
		  end
		else
		  []


            | _ => crash())


      | generateEVar (getAllCases, world, Gglobal, Glocal, D.NormalDec(_, D.Meta(isP, F)), sc) = 
	 (case (D.whnfP isP)
	    of D.Existential => 	     
		(case (D.whnfF F)
		   of D.Top => sc (D.Unit)
		    | D.Exists (D', F') => generateEVar (getAllCases, world, Gglobal, Glocal, D',
						       fn E1 => generateEVar(getAllCases, world, Gglobal, Glocal, 
									    D.NormalDec(NONE,D.Meta(D.Existential, D.FClo(F', D.coerceSub (D.Dot(D.Prg E1 , D.id))))),
									    fn E2 => sc (D.Pair (E1, E2, F))))

		    | D.Nabla (D', F') => generateEVar (getAllCases, world, Gglobal, I.Decl(Glocal, D.NonInstantiableDec D'), 
						      D.NormalDec(NONE, D.Meta(D.Existential, F')),
						      fn E => sc (D.New(D', E, NONE)))
		    | D.FVar _ => raise Domain
		    | D.FClo _ => raise Domain
		    | D.FormList _ => raise Domain
		    | D.All _ =>
		             (* Create a value:  (x \Glocal)
			      * so x has type : Nabla Glocal. F
			      *)
		             let
			       fun raiseType (I.Null, F) = F
				 | raiseType (I.Decl(G, D.NonInstantiableDec D), F) = raiseType(G, D.Nabla(D, F))
				 | raiseType _ = crash() (* broken invariant.. .Glocal only contains NonInstantiableDecs.. *)

			       val X = D.EVar ((ref NONE, raiseType (Glocal, F)), D.id)

			       (* compute E \G 
				* i.e.  E \(x,y) == (E \x) \y
				*)
			       fun popCtx (I.Null, E) = E 
				 | popCtx (I.Decl(G, D.NonInstantiableDec D), E) = D.Pop(1, popCtx(G, E))
				 | popCtx _ = crash() (* broken invariant *)
				 
			       val E = popCtx (Glocal, X)
			     in
			       sc E
			     end
			   )
              | D.Param =>
		   let
		     val case1 = 
		         (* Case (1)..*)
		         let 
			   val Gglobal = D.coerceCtx Gglobal
			   val Glocal = D.coerceCtx Glocal
			   val sizeG = I.ctxLength Glocal
			     
			   fun inverse(0) = I.id
			     | inverse(n) = I.Dot(I.Undef, inverse(n-1))
			     
			   val t = inverse sizeG  (*  .  |- t : Glocal *)

			   fun getResult () =
			     let
			       val Fopt' = SOME(U.applyInv2Formula (true, Gglobal, Glocal, F, t, ref NONE)) (* EVars are only raised up to Glocal  *)
				 handle U.Error _ => NONE
			     in
			       case Fopt' of
			                NONE => []
				      | SOME F' => sc (D.Var (D.BVarMeta ((ref NONE, F'), D.shiftTo(sizeG, D.id)), NONE))
			     end

			 in
			   removeSideEffects getResult
			 end

		     val case2 = if not(getAllCases) then [] else
		         (* Case (2)..*)
		         let
			   (* Try all the parameters in Glocal *)
			   fun matchVars(I.Null, varNumber) = []
			     | matchVars(I.Decl(G, D.NonInstantiableDec (D.NewDecMeta(_, Fvar))), varNumber) =
			          let
				    fun getResult () =
				      let
					val b = (U.unifyF(D.coerceCtx Gglobal, D.coerceCtx Glocal, F, D.FClo (Fvar, I.Shift varNumber)) ; true)
				            handle U.Error _ => false
													 
				      in
					if b then sc (D.Var(D.Fixed varNumber, NONE)) else []
				      end
				  in
				    (removeSideEffects getResult) @ (matchVars(G, varNumber+1))
				  end
			     | matchVars (I.Decl(G, D.NonInstantiableDec _), varNumber) = matchVars(G, varNumber+1)
			     | matchVars _ = crash()
			   in
			     matchVars(Glocal, 1)
			 end
		   in
		     case1 @ case2
		   end
	     | _ => crash() )




    (* reduceCase (Gglobal, G, C) = C'
     * where C' is filled in with appropriate EVars such that C' is of the form
     * has no epsilons, pops, and ends with "Unit"
     *)
    fun reduceCase (Gglobal, G, (D.Eps (D.NormalDec(_, D.LF(isP, A)), C)), goUnderNew) =
            (case (D.whnfP isP)
	      of D.Existential =>  	     
		      let
			(* val X = I.EVar(ref NONE, D.coerceCtx G, A, ref nil)
			 * This above one would have NDecs 
			 *)
			val X = generateLF_EVar (D.coerceCtx G, A, fn U => U)

			val t = D.Dot (D.Prg (D.Quote X), D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)), goUnderNew)
		      end


	      | D.Param =>
		      let 
			val X = D.Var (D.BVarLF ((ref NONE, A, D.makeParamList (I.mergeCtx(Gglobal, G))), I.id), NONE)  
			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)), goUnderNew)
		      end

              | D.PVar _ => crash() (* should not get to opsem with any PVars *)
            )

      | reduceCase (Gglobal, G, (D.Eps (D.NormalDec(_, D.Meta(isP, F)), C)), goUnderNew) =
            (case (D.whnfP isP)
	      of D.Existential =>  	     
		      let
			val X = D.EVar ((ref NONE, F), D.id)
			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)), goUnderNew)
		      end
	      | D.Param =>                   
		      let 
			val X = D.Var (D.BVarMeta ((ref NONE, F), D.id), NONE)
			val t = D.Dot (D.Prg X, D.id)
		      in
			reduceCase (Gglobal, G, (D.substCase(C, t)), goUnderNew)
		      end
              | D.PVar _ => crash() (* should not get to opsem with any PVars *)
            )

      | reduceCase (Gglobal, G, (D.NewC (D, C, fileInfo)), true) = D.NewC(D, 
								 reduceCase (Gglobal, I.Decl(G, D.NonInstantiableDec D), C, true),
								 fileInfo)

      | reduceCase (Gglobal, G, (C as D.NewC _), false) = C

      | reduceCase (Gglobal, G, (D.PopC (i, C)), goUnderNew) = 
	         (case (reduceCase (Gglobal, D.popCtx(i, G), C, false))
		    of (D.NewC (_, C', _)) => reduceCase (Gglobal, G, D.substCase(C', D.shiftTo(i-1, D.id)), goUnderNew)
		     | _ => crash() (* not type correct *)
                 )

      | reduceCase (Gglobal, G, D.Match (visibility, E, _), goUnderNew) = D.Match(visibility, evalPattern E, D.Unit)
      | reduceCase (Gglobal, G, D.MatchAnd (visibility, E, C), goUnderNew) = D.MatchAnd(visibility, evalPattern E, reduceCase (Gglobal, G, C, goUnderNew))



    (* matchGoal (G, goal, Clist, klist) = klist' 
     * where "goal" is the coverage goal
     * and Clist is all clauses
     * We add one new list cand for each C to klist to obtain klist'
     *)
    fun matchGoal(G, goal, Clist, Covered) = Covered
      | matchGoal(G, goal, C::Clist, klist) =
            let
	      fun addEps (G, D.Eps(D, C), n) = addEps (I.Decl(G, D.InstantiableDec D), C, n+1)
		| addEps (G, C, n) = (G, C, n)

	      val (G', goal', numVars') = addEps(I.Null, goal, 0)

	      val C0 = D.substCase(C, D.shiftTo(numVars', D.id))  (* G,G' |- C0 is well typed *)
	      val C' = reduceCase(G,G', C0, true)
	      val cands1 = matchCaseBranch(G, G', 0, numVars', goal', C', Eqns (nil)) 
	      val cands2 = resolveCands cands1
	      val cands3 = checkConstraints(C', cands2)
	    in
	      matchGoal(G, goal, Clist, addKs(cands3, klist))
	    end
      | matchGoal(G, goal, [], klist) = klist

         












    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =  
	let (* Gglobal,G |- V1[s] : L *)
	  val X = generateLF_EVar (G, I.EClo (V1, s), fn U => U)
	  val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
	in
	  (I.App (X, S), Vs)
	end
      (* Uni or other cases should be impossible *)
      | createEVarSpineW _ = crash()

(* replaced by actual match attempt
    fun checkOccurs (Gglobal, GX, V) = 
        let
	    (* If anything pattern variables from Gglobal occur *in* "V", then
	     * this split is disallowed.
	     *)
	    val V' = DelphinAbstract2.raiseType (GX, V)	      
	    val K = DelphinAbstract2.collectExp ((V', I.id), I.Null)
	    val n = I.ctxLength K
	    val V'' = DelphinAbstract2.abstractExp(K, 0, (V', I.Shift n))

	    fun occursExp k = case (DelphinAbstract2.occursInExp (k, V''))
	                          of I.No => false
				   | I.Maybe => true
				   | I.Meta => false
	    fun checkOccurs (I.Null, k) = ()
	      | checkOccurs (I.Decl(G, D.InstantiableDec D), k) = if occursExp k  then raise ImpossibleSplit else checkOccurs(G, k+1)
	      | checkOccurs (I.Decl(G, D.NonInstantiableDec _), k) = checkOccurs(G, k+1)
	in
	    checkOccurs (Gglobal, n+1)
	end
*)


    fun constCasesSig (Gglobal, GX, Vgiven, nil, sc) = []
      | constCasesSig (Gglobal, GX, Vgiven, I.Const(cid)::sgn', sc) =
          let
	    val list' = constCasesSig(Gglobal, GX, Vgiven, sgn', sc)

	    val V' = I.constType cid
	    val (S', Vs') = createEVarSpine (GX, (V', I.id))
	    val instantiation = I.Root(I.Const cid, S')

	    fun getResult () =
	      let
		val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
		        of (Cands _) => (debugAdam() ; raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			 | Fail => false
			 | Eqns _ => U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs')
		  
	      in
		if b then (sc instantiation)@list' else list'
	      end
	  in
	    removeSideEffects getResult
	  end
      | constCasesSig _ = crash()


    (* Goes through all elements >= k of Gglobal *)
    fun constCasesCtx (Gglobal, GX, Vgiven, 0, sc) = []
      | constCasesCtx (Gglobal, GX, Vgiven, k, sc) =
         (case I.ctxLookup (Gglobal, k)
	    of D.NonInstantiableDec (D.NewDecLF (_, V)) =>  
	         let
		   val list = constCasesCtx (Gglobal, GX, Vgiven, k-1, sc)
		   val V = I.EClo(V, I.Shift (k+ (I.ctxLength GX) ))
		   val (S', Vs') = createEVarSpine (GX, (V, I.id))
		   val instantiation = I.Root(I.BVar (I.Fixed k), S')

		   fun getResult () =
		     let
		       val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
			        of (Cands _) => (debugAdam() ; raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			      | Fail => false
			      | Eqns _ => U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs')

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
	    val (S', Vs') = createEVarSpine (GX, (V, I.id))
	    val instantiation = I.Root(I.BVar (I.Fixed k), S')

	    fun getResult () =
	       let
		val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
		        of (Cands _) => (debugAdam() ; raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			 | Fail => false
			 | Eqns _ => U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs')

	       in 
		 if b then (sc instantiation)@list else list
	       end
	  in
	    removeSideEffects getResult
	  end

    fun worldCases (D.Anything, Gglobal, GX, Vgiven, sc) = raise ImpossibleSplit (* Impossible to do coverage if world is Anything!!! *)
      | worldCases (D.VarList [], Gglobal, GX, Vgiven, sc) = []
      | worldCases (D.VarList ((paramCtx, paramType)::varList), Gglobal, GX, Vgiven, sc) =
          let
	    val list = worldCases (D.VarList varList, Gglobal, GX, Vgiven, sc)


	    fun createSub(I.Null) = I.Shift (I.ctxLength GX)   (* GX |- shift^n : . *)
	      | createSub(I.Decl(G, D.InstantiableDec (D.NormalDec(_, D.LF(isP, A))))) = 
	           (case (D.whnfP isP)
		      of D.Existential => 
			let
			  val t' = createSub G                 (* GX |- t' : G       *)
 			                                       (* G |- A : type     *)
			  val A' = I.EClo(A, t')              (* GX |- A[t'] : type *)
			  val X = generateLF_EVar (GX, A', fn U => U)
			in
			  I.Dot(I.Exp X, t')       (* GX |- X.t' : G,V   *)
			end
		    | D.Param => 
			let
			  val t' = createSub G                 (* GX |- t' : G       *)
			                                       (* G |- A : type     *)
			  val A' = I.EClo(A, t')              (* GX |- A[t'] : type *)
			    (* GX is from lowering an EVar, so none of them are params *)
			  val X = I.Root(I.BVar(I.BVarVar ((ref NONE, A',D.makeParamList' (Gglobal, (I.ctxLength GX) + 1)), I.id)), I.Nil)
			in
			  I.Dot(I.Exp X, t')       (* GX |- X.t' : G,V   *)
			end
		    | _ => crash() )
	      | createSub _ = crash()


	    val t = createSub paramCtx 
	    val V = I.EClo(paramType, t)

	    val (S', Vs') = createEVarSpine (GX, (V, I.id))

	    val instantiation = I.Root(I.BVar (I.BVarVar ((ref NONE, V, D.makeParamList Gglobal), I.Shift (I.ctxLength GX))), S')

	    fun getResult() =
	      let 
		val b = case (LFmatchExp(Gglobal, revCoerceCtx GX, I.ctxLength GX, I.ctxLength Gglobal, (Vgiven, I.id), Vs', Eqns (nil)))
		        of (Cands _) => (debugAdam() ; raise ImpossibleSplit) (* The type may match, but it would require refining a "global" pattern variable.
							       * i.e. a pattern variable from an outer case statement..
							       *)
			 | Fail => false
			 | Eqns _ => U.LFunifiable (D.coerceCtx Gglobal, GX, (Vgiven, I.id), Vs')
	      in
		if b then (sc instantiation)@list else list
	      end

	  in
	    removeSideEffects getResult
	  end
      | worldCases (D.NonWeakenable W, Gglobal, GX, Vgiven, sc) = worldCases (W, Gglobal, GX, Vgiven, sc)


    fun splitEVar (world, Gglobal, X as I.EVar (_, GX, V, _), sc (* success continuation *) ) =
          let
	    val a = case Whnf.whnf (V, I.id)
	            of (I.Root (I.Const a, _), s) => a
		     | _ => crash()

	    fun newSC U = 
	         let
		   fun getResult () =
		     let
		       val b = U.LFunifiable (D.coerceCtx Gglobal, I.Null, (X, I.id), (U, I.id))  
		     in
		       if b   then [sc ()]
			      else []
		     end
		 in
		   removeSideEffects getResult
		 end

	    val list1 = constCasesSig (Gglobal, GX, V, Index.lookup a, newSC)
	    val list2 = constCasesCtx (Gglobal, GX, V, I.ctxLength Gglobal, newSC)
	    val list3 = paramCases (Gglobal, GX, V, I.ctxLength GX, newSC)
	    val list4 = worldCases (world, Gglobal, GX, V, newSC)  
	  in
	    list1 @ list2 @ list3 @ list4
	  end
      | splitEVar _ = crash()



    (* splitVar (k, world, G, goal) = SOME (goal list)
                                  or NONE
       where goal list is obtained by splitting kth "epsilon" 
       variable in goal (counting right-to-left).

       returns NONE if splitting variable k fails because of constraints

       world are the worlds defined for current predicate
    *)

    (* createSub (Gglobal, G) = t 
     * such that . |- t : G
     * and t is filled with EVars in context "."
     * Used to fill in "epsilons", so context only has InstantiableDecs...
     *)		     
    fun createSub(Gglobal, I.Null) = D.id
      | createSub(Gglobal, I.Decl(G, D.InstantiableDec (D.NormalDec(_, D.LF(isP, A))))) = 
          (case (D.whnfP isP)
	     of D.Existential => 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- A : type     *)
		     val A' = I.EClo(A, D.coerceSub t')    (* . |- A[t'] : type *)
		     val X = D.Quote(generateLF_EVar (I.Null, A', fn U => U))
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end
              | D.Param => 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- A : type     *)
		     val A' = I.EClo(A, D.coerceSub t')    (* . |- A[t'] : type *)
		     val X = D.Var(D.BVarLF ((ref NONE, A',D.makeParamList Gglobal), I.id), NONE)
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end
              | _ => crash() )

      | createSub(Gglobal, I.Decl(G, D.InstantiableDec (D.NormalDec(_, D.Meta(isP, F))))) = 
	  (case (D.whnfP isP)
	     of D.Existential => 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- F : type     *)
		     val F' = D.FClo(F, D.coerceSub t')    (* . |- F[t'] : type *)
		     val X = D.EVar ((ref NONE, F'), D.id)
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end

              | D.Param => 
                   let
		     val t' = createSub (Gglobal, G)       (* . |- t' : G       *)
		                                           (* G |- F : type     *)
		     val F' = D.FClo(F, D.coerceSub t')    (* . |- A[t'] : type *)
		     val X = D.Var(D.BVarMeta ((ref NONE, F'), D.id), NONE)
		   in
		     D.Dot(D.Prg X, t')       (* . |- X.t' : G,V   *)
		   end
	      | _ => crash() )

      | createSub _ = crash() (* broken invariant *)


    fun splitVar (k, world, Gglobal, goal) =
        let
	  fun getLocalCtx (G, D.Eps(D, C)) = getLocalCtx (I.Decl(G, D.InstantiableDec D), C)
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
	      SOME(splitEVar (world, Gglobal, X, fn () => DelphinAbstract2.abstractCase goal''))
	      handle DelphinAbstract2.LeftOverConstraints => NONE
		   | ImpossibleSplit => NONE
	end

    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)

    (* Finitary Splitting *)
    fun finitary1 (X, k, goal, world, Gglobal, cands) =
         let

	   (* recursive X = true
	    iff the instantiation of X : {{G}} a @ S contains an
	    EVar Y : {{G'}} b @ S such that a <|= b

	    This means there is no guarantee that X : {{G}} a @ S has only
	    a finite number of instances
	    *)

	   fun recursive (X as I.EVar (ref(SOME(U)), GX, VX, _)) = DelphinAbstract2.isRecursiveOrConstraints(I.targetFam VX, X)
	     | recursive _ = crash()

	   val countOpt = SOME (List.length (splitEVar(world, Gglobal, X, fn () => if recursive X then raise NotFinitary else DelphinAbstract2.abstractCase goal)))
	     handle ImpossibleSplit => NONE
		  | NotFinitary => NONE
	          | DelphinAbstract2.LeftOverConstraints => NONE

	 in
	   case countOpt 
	     of NONE => cands
	      | SOME n => (k, n)::cands
	 end
	     

	   

      
    fun finitarySplits (D.id, k, goal, world, Gglobal, cands) = cands
      | finitarySplits (D.Dot(D.Prg (D.Quote U), t), k, goal, world, Gglobal, cands) =
                let
		  (* EVar was lowered.. so we use this procedure to find it... *)
		  fun getEVar (U, t) = getEVarW (Whnf.whnf (U, t))
		  and getEVarW(I.Lam(_, U), t) = getEVar (U, I.dot1 t)
		    | getEVarW(X as I.EVar _, t) = X
		    | getEVarW _ = crash()

		  val cands' = removeSideEffects (fn () => finitary1 (getEVar (U, I.id), k, goal, world, Gglobal, cands))
		in
		  finitarySplits(t, k+1, goal, world, Gglobal, cands')
		end
				
      | finitarySplits (D.Dot(D.Prg _, t), k, goal, world, Gglobal, cands) =
                 (* Cannot be split *)
                 finitarySplits(t, k+1, goal, world, Gglobal, cands)

      | finitarySplits _ = crash() (* impossible *)

    fun finitary(world, G, goal) =
           let 

	     fun getLocalCtx (G, D.Eps(D, C)) = getLocalCtx (I.Decl(G, D.InstantiableDec D), C)
	       | getLocalCtx (G, C) = (G, C)

	     val (Glocal, goal') = getLocalCtx(I.Null, goal)
	     val t' = createSub(G,Glocal)     (* . |- t' : Glocal, where EVars are created with context "." *)
	                                      (* Therefore, it is also true that G |- t' : G,Glocal *)
	     val goal'' = D.substCase(goal', t')
	   in
	     finitarySplits (t', 1, goal'', world, G, nil)
	   end






    (* *************************************************************************************************** *)
    (* *************************************************************************************************** *)


    fun goalToString(smartInj, G, goal) = 
          let
	    val _ = PrintDelphinInt.varReset G
	    val C = PrintDelphinInt.convCaseBranch(smartInj, G, goal)
	    val F = PrintDelphinExt.caseBranchToFormat(C, false (* do not print details... (right of "=>" *)  )
	  in
	    Formatter.makestring_fmt F
	  end

    fun goalsToString(smartInj, G, []) = ""
      | goalsToString(smartInj, G, (goal::goals)) = goalToString(smartInj, G, goal) ^ "\n" ^ goalsToString(smartInj, G, goals)



    fun isFunction(F) = isFunctionN (D.whnfF F)
    and isFunctionN(D.All _) = true
      | isFunctionN(D.Nabla(_, F)) = isFunction F
      | isFunctionN _ = false

    (* Get the initial cover goal based on the Formula *)
    (* G is the global context *)
    (* Glocal represents the local parameters that are introduced *)
    (* sc is the success continuation to be applied to EVERY case that results *)
    fun getStartGoal (world, G, Glocal, F, sc) = getStartGoalN (world, G, Glocal, D.whnfF F, sc)
    and getStartGoalN (world, G, Glocal, D.All(visibility, W, D, F), sc) = 
                if (isFunction F) then
		  generateEVar(true, world, G, Glocal, D, fn E => getStartGoal(world, G, Glocal, D.FClo(F, I.Dot (D.coerceExp E, I.id)), 
							       fn C => sc (D.MatchAnd(visibility, E, C))))
		else 
		  generateEVar(true, world, G, Glocal, D, fn E => [sc (D.Match(visibility, E, D.Unit))])

      | getStartGoalN (world, G, Glocal, D.Nabla(D, F), sc) = 
		      getStartGoal(world, G, I.Decl(Glocal, D.NonInstantiableDec D), F, fn C => sc (D.NewC(D, C, NONE)))

      | getStartGoalN (world, G, Glocal, F, sc) = crash()


    fun cover(world, G, goal, Clist, missing) =
         let
	   val cands = matchGoal(G, goal, Clist, CandList [])
	   val selection = selectCand cands
	 in
	   split (selection, world, G, goal, Clist, missing)
	 end
       
    and split(NONE, world, G, goal, Clist, missing) = missing (* goal is covered! *)
      | split(SOME(nil), world, G, goal, Clist, missing) = 
	    splitWeak(finitary(world, G, goal), world, G, goal, Clist, missing) 

      | split(SOME ((k,_)::ksn), world, G, goal, Clist, missing) =
          (case splitVar (k, world, G, goal)
	     of SOME(goals) => covers(world, G, goals, Clist, missing)
	      | NONE => (* splitting variable k generated constraints, so try another *)
	            split(SOME ksn, world, G, goal, Clist, missing))


    and splitWeak (nil, world, G, goal, Clist, missing) = goal :: missing
      | splitWeak (ksn, world, G, goal, Clist, missing) = 
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
              split (SOME(findMin ksn::nil), world, G, goal, Clist, missing)
	    end



    (* check that Clist covers all "goals".  Add missing cases to "missing". 
     * covers(world, G, goals, Clist, missing) = missing' 
     *)
    and covers(world, G, [], Clist, missing) = missing
      | covers(world, G, goal::goals, Clist, missing) =        
          let
	    (*
	    val _ = print "\n\nSTACK OF GOALS = \n"
	    val _ = print (goalsToString(true, G, goals))
	    val _ = print "\nCURRENT GOAL = \n"
	    val _ = print (goalsToString(true, G, [goal]))
	      *)
	  in
           covers(world, G, goals, Clist, cover (world, G, goal, Clist, missing))      
	  end

    (* We run the risk of functions not being weakenable whenever the user uses "NewC" (new over cases)
     * We find this desirable for "parameter" functions, but not for others.  
     * Therefore, we assume ALL parameter functions are non-weakenable, and all other functions are weakenable.
     *
     * Here we check that the user list of cases does not use "NewC" over non-parameter functions... If so, return an error.
     *)

    fun checkWeaken(G, C, F) = checkWeakenW (G, C, D.whnfF F)
    and checkWeakenW(G, D.Eps(D, C), F) = checkWeaken (I.Decl(G, D.InstantiableDec D), C, D.FClo(F, I.shift))
      | checkWeakenW(G, D.NewC(D, C, fileInfo), D.Nabla(_, F)) = (WorldSubsumption.isParamFun F) (* do we need this??? andalso checkWeaken(I.Decl(G, D.NonInstantiableDec D), C, F) *)
      | checkWeakenW(G, D.PopC (i, C), F) = WorldSubsumption.isParamFun F
      | checkWeakenW(G, D.Match (_, E1, E2), F) = true
      | checkWeakenW(G, D.MatchAnd(_, E, C), D.All(_, _, _, F)) = checkWeaken(G, C, F)
      | checkWeakenW _ = raise Domain (* no other case is possible *)

    fun checkWeakenability(G, [], F) = true
      | checkWeakenability(G, C::Clist, F) = checkWeaken(G, C, F) andalso checkWeakenability(G, Clist, F)



    (* Main Function ... *)
    (* ***************************************************************************************************************** *)
    (* ***************************************************************************************************************** *)

    fun checkCases(smartInj, D.VarList [], G, Clist, F) = () (* always ok *)
      | checkCases(smartInj, world, G, Clist, F) = 
            let	      
	      (* ABP WARNING:  We need to check that everything in G is named..
	       * otherwise it will print some names as "?" ..
	       *)
	      val G = PrintDelphinInt.ctxName G

	      val _ = if (checkWeakenability(G, Clist, F)) then () else raise Error "{<..>} over cases for non-parameter functions not supported."

	      val goals = getStartGoal (world, G, I.Null, F, fn C => DelphinAbstract2.abstractCase C)
	      val missing = covers (world, G, goals, Clist, nil)
	    in
	      case missing 
		        of nil => ()
			 | _ => (raise Error (goalsToString(smartInj, G, missing)))
	    end

    fun checkCaseBody(smartInj, world, G, D.Eps(D, C)) = checkCaseBody(smartInj, world, I.Decl(G, D.InstantiableDec D), C)
      | checkCaseBody(smartInj, world, G, D.NewC(D, C, fileInfo)) = checkCaseBody(smartInj, world, I.Decl(G, D.NonInstantiableDec D), C)
      | checkCaseBody(smartInj, world, G, D.PopC(i, C)) = checkCaseBody(smartInj, world, D.popCtx(i, G), C)
      | checkCaseBody(smartInj, world, G, D.Match(visibility, Epat, Ebody)) = checkCovers(smartInj, world, G, Ebody)
      | checkCaseBody(smartInj, world, G, D.MatchAnd(visibility, Epat, C)) = checkCaseBody(smartInj, world, G, C)


    and checkCovers(smartInj, world, G, E) = checkCoversN(smartInj, world, G, D.whnfE E)
    and checkCoversN(smartInj, world, G, D.Var _) = ()
      | checkCoversN(smartInj, world, G, D.Quote _) = ()
      | checkCoversN(smartInj, world, G, D.Unit) = ()
      | checkCoversN(smartInj, world, G, D.Lam (Clist, F, fileInfo)) = 
                                        let
					  (* ADAM:  Better to get world from F than to pass it around *)
					  val _ = (checkCases(smartInj, world, G, Clist, F)
                                                   handle Error s => 
							      let 
								val msg = "WARNING:  Match Non-Exhaustive Failure:\n" ^ s ^ "\n\n"
							      in
								case fileInfo
								  of NONE => raise Error msg
								   | SOME(filename, r) => raise Error (Paths.wrapLoc(Paths.Loc (filename, r), msg))
							      end )
					  val _ = map (fn C => checkCaseBody(smartInj, world, G, C)) Clist
					in
					  ()
					end

      | checkCoversN(smartInj, world, G, D.New (D, E, _)) = checkCovers(smartInj, world, I.Decl(G, D.NonInstantiableDec D), E)
      | checkCoversN(smartInj, world, G, D.App (_, E1, E2)) =  (checkCovers(smartInj, world, G, E1) ; checkCovers(smartInj, world, G, E2))
      | checkCoversN(smartInj, world, G, D.Pair (E1, E2, _)) = (checkCovers(smartInj, world, G, E1) ; checkCovers(smartInj, world, G, E2))
      | checkCoversN(smartInj, world, G, D.ExpList []) = ()
      | checkCoversN(smartInj, world, G, D.ExpList (E::Elist)) = (checkCovers(smartInj, world, G, E) ; checkCovers(smartInj, world, G, D.ExpList Elist))
      | checkCoversN(smartInj, world, G, D.Proj (E, i)) = checkCovers(smartInj, world, G, E)
      | checkCoversN(smartInj, world, G, D.Pop (i, E)) = checkCovers(smartInj, world, D.popCtx(i, G), E)
      | checkCoversN(smartInj, world, G, D.Fix (D, E)) = checkCovers(smartInj, world, I.Decl(G, D.InstantiableDec D), E)
      | checkCoversN(smartInj, world, G, D.EVar r (* ref NONE *)) = ()
      | checkCoversN(smartInj, world, G, D.EClo _) = crash() (* impossible by whnf *)


  end