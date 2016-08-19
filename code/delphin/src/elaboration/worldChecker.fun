(* Checks if a program is world correct,
 * modifies the expression by adding "Weaken" when necessary.
 * May raise Error!.. Precondition:  no meta-level EVars..
 *
 * Author: Adam Poswolsky
 *)
structure WorldChecker = 
  struct
    exception Error of string
    structure D = DelphinIntSyntax
    structure I = IntSyn
    structure U = UnifyDelphinNoTrail

    fun crash() = raise Domain

    fun getFormula (D.Meta(F)) = D.whnfF F
      | getFormula _ = crash()

    datatype lookupResult 
      = lookupType of D.Types
      | lookupWorld of D.World
 
    (* raises Error if not world correct *)
    fun worldCheck(filename, r, G, E) = 
      let
	 
	     fun generateVarError (fileInfo, name) = 
	         let
		   val varString = case name 
		                    of NONE => ""
				     | SOME s => ": " ^ s

		   val (filename, r) = case fileInfo
		       of SOME(filename, r) => (filename, r)
		        | _ => (filename, r) (* information passed into function *)
		 in
		   raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Subsumption Violation:  Should not weaken variable" ^ varString ^". (Created a parameter incompatible with params declaration!)")))
		 end

	     fun generatePopError (fileInfo, name) = 
	         let
		   val varString = case name 
		                    of NONE => ""
				     | SOME s => ": " ^ s

		   val (filename, r) = case fileInfo
		       of SOME(filename, r) => (filename, r)
		        | _ => (filename, r) (* information passed into function *)
		 in
		   raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Subsumption Violation:  Should not pop variable" ^ varString ^".")))
		 end

	     fun generateCriticalError (fileInfo) = 
	         let
		   val (filename, r) = case fileInfo
		       of SOME(filename, r) => (filename, r)
		        | _ => (filename, r) (* information passed into function *)
		 in
		   raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Checker Error:  Serious and unexpected type error!")))
		 end


	    (* lookup(G, k) = (name, T, listWeakened)
	     *)
	     fun lookup' (k', I.Null, _) = raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("Bad Variable Access in worldCheck")))    
	       | lookup' (k', I.Decl(G, (D.InstantiableDec (D.NormalDec (SOME [s], T0)))), 1 ) = (SOME s, lookupType(D.substTypes(T0, I.Shift k')), [])
	       | lookup' (k', I.Decl(G, (D.InstantiableDec (D.NormalDec (_, T0)))), 1 ) = (NONE, lookupType(D.substTypes(T0, I.Shift k')), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecLF (name, A)))), 1) = (name, lookupType(D.LF(D.Param, I.EClo(A, I.Shift k'))), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecWorld (name, W)))), 1) = (name, lookupWorld(W), [])

	       (* Special case for empty world.. we do not need to add to listWeakened *)
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecWorld (_, D.VarList []) ))), k) = lookup'(k', G, k-1)

	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec D )), k) = 
                               let
				 val (name, T, list) = lookup'(k', G, k-1)
			       in
				 (name, T, (D.substNewDec(D, I.Shift (k' - k + 1)))::list)
			       end

	       | lookup' (k', I.Decl(G, (D.InstantiableDec _)), k) = lookup'(k', G, k-1)

	     fun lookup (G, k) = lookup' (k, G, k)


	     fun check (G,E) = checkN (G, D.whnfE E)


	     and checkN (G, E as D.Var (D.Fixed i, fileInfo)) = 
	                    let
			      val (name, T, listWeakened) = lookup(G, i)

			      val T = case T of lookupType T' => T' | _ => raise generateCriticalError(fileInfo)

			    in
			        if (List.null listWeakened) orelse (WorldSubsumption.canWeakenType T) then ()
				else generateVarError(fileInfo, name)
			    end

	       (* No longer have BVarMeta
	       | checkN (G, D.Var (D.BVarMeta ((_, F), s), fileInfo)) = ...
	       *)
	       | checkN (G, E as D.Var (D.BVarLF ((_, A, _, _), s), fileInfo)) = ()
	       | checkN (G, E as D.Quote M) = ()
	       | checkN (G, E as D.Unit) = ()
	       | checkN (G, E as D.Lam ([], F, fileInfo)) = ()
	       | checkN (G, D.Lam (Clist as (D.PopC(i,_)::_), F, fileInfo)) = 
				let
				  fun movePopOutside (D.PopC(j, C')) = if (i = j) then C' else crash() (* broken invariant *)
				    | movePopOutside _ = raise Domain (* broken invariant *)

				  val Clist' = map movePopOutside Clist

				  fun popCtx(0, G) = crash()
				    | popCtx(1, I.Decl(G, D.NonInstantiableDec D)) = (G, D)
				    | popCtx(1, I.Decl(G, D.InstantiableDec D)) = raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("Delphin WorldChecker Error:  Bad Pop")))
				    | popCtx(i, I.Decl(G, _)) = popCtx (i-1, G)
				    | popCtx _ = crash()

				  val (G', D) = popCtx (i, G)
				  val G'' = D.coerceCtx (I.Decl(G', D.NonInstantiableDec D))
				  val Fnew = D.newFVar(G'')
				  val F' = D.Nabla (D, Fnew)
				  val _ = U.unifyF(I.Null, G'', F, D.FClo(Fnew, I.Shift(i-1)))
				    handle U.Error msg => case fileInfo
				                           of SOME (filename, r) => raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("WorldChecker Failed UNEXPECTEDLY (" ^ msg ^ ")"))) (* should never fail! *)
							    | NONE =>  raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("WorldChecker Failed UNEXPECTEDLY (" ^ msg ^ ")"))) (* should never fail! *)
				in
				  check (G, D.Pop (i, D.Lam (Clist', F', fileInfo), fileInfo))
				end
	       | checkN (G, D.Lam (Clist (* and no cases have PopC *), F, fileInfo)) = 
				(map (fn C => checkCase(G, C)) Clist ; ())

	       | checkN (G, D.New (D, E, fileInfo)) = check(I.Decl(G, (D.NonInstantiableDec D)), E)

	       | checkN (G, D.App (E1, args)) = (map (fn (vis, info, E) => (vis, info, check(G, E))) args ; check (G, E1))

	       | checkN (G, D.Pair (E1, E2, F)) = (check(G, E1) ; check(G, E2))

	       | checkN (G, D.ExpList Elist) = ((map (fn E => check(G, E)) Elist); ())

	       | checkN (G, D.Proj (E, i)) = check(G, E)

	       | checkN (G, D.Pop (i, E, fileInfo)) = 
			     let
			       val (name, Tw, listWeakened) = lookup(G, i)


			       val _ (* E' *) = check(D.popCtx(i, G), E)

			       val T = DelphinTypeCheck.inferType (D.popCtx(i, G), E)
				  handle DelphinTypeCheck.Error s => raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Type-Checking Violation:"  ^ s)))
			       val Wopt = case T of
				               D.Meta F => (case D.whnfF F
							       of D.Nabla (D.NewDecWorld (_, W), F) => SOME W
							     | _ => NONE)
					     | D.LF _ => NONE


			     in
			      case (Wopt, Tw)
				of (NONE, _) => 
				     if (List.null listWeakened) orelse (WorldSubsumption.canWeakenType T)  then ()
				     else generatePopError(fileInfo, name)
				 | (SOME W, lookupWorld W0) => 				     
				     if (WorldSubsumption.worldSubsume(W0, W) andalso  (WorldSubsumption.compatWorld(W,G,listWeakened))) then ()
				     else 
				       (* This pop was added automatically to weaken "E" which should be a Var. *)
				       (case (D.whnfE E)
					  of (D.Var (D.Fixed j, fileInfo)) =>
					          generateVarError(fileInfo, #1 (lookup (D.popCtx(i, G), j)))
					   | _ => generateVarError(fileInfo, NONE))
				 | _ => generateCriticalError(fileInfo)
			     end

			   

	       | checkN (G, D.Fix (D, E)) = check(I.Decl(G, D.InstantiableDec D), E)

	       | checkN (G, E as D.EVar _) = crash() (* UNEXPECTED EVar! *)
	       | checkN (G, _) = crash() (* not in whnf *)

	    (* Invariant:  There are no PopCs!!!  *)
	    (* NOTE:  We do NOT add the "Weaken" rule to patterns!!! *)
             and checkCase (G, D.Eps(D, C, fileInfo)) = checkCase (I.Decl(G, (D.InstantiableDec D)), C)
	       | checkCase (G, D.NewC(D, C, fileInfo)) = checkCase(I.Decl(G, D.NonInstantiableDec D), C)

	       | checkCase (G, D.Match(pats, E2)) = 
	                    (map (fn (vis, E) => (vis, check(G, E))) pats;
			     check(G, E2))

	       | checkCase (G, D.PopC _) = crash() (* invariant (precondition) broken! *)

      in
	(check (G, E))
      end
    
  end
