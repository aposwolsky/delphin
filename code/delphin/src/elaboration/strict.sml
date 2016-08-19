(* Delphin Strictness Checker *)
(* Author: Adam Poswolsky *)

structure DelphinStrictness =
  struct
    exception NotStrictError of string

    structure I = IntSyn
    structure D = DelphinIntSyntax
    structure U = UnifyDelphinTrail

      
   fun crash() = (print "Fatal Error" ; raise Domain)

    (* Strictness... check that all pattern variables occur strict in the pattern *)
    (* **************************************************** *)
    datatype Status =
        ExistentialParam
      | ExistentialNoParam
      | Universal
      
    fun existential (D.LF(isP, A)) = (case (D.whnfP isP)
                                     of D.Param => ExistentialParam
				      | _ => ExistentialNoParam)
      | existential (D.Meta(F)) = ExistentialNoParam

    fun isUniversal Universal = true
      | isUniversal _ = false

    fun isParam (ExistentialParam) = true
      | isParam (ExistentialNoParam) = false
      | isParam (Universal) = crash()
	
    (* unique (k, ks) = B

       Invariant:
       B iff k does not occur in ks
    *)
    fun unique (k, nil) = true
      | unique (k:int, k'::ks) =
          (k <> k') andalso unique (k, ks)

    (* isPattern (G, k, mS) = B
     
       Invariant: 
       B iff k > k' for all k' in mS
	 and for all k in mS: k is universal parameter
         and for all k', k'' in mS: k' <> k''

     *ABP:  the check k > k' is often useless as k represents a pattern variable
	    and those are abstracted to the left of all news...BUT it may be possible for the
	    user to write {<x>}[<e>] and now e cannot use x..
    *)
    fun checkPattern (G, k, args, (I.Nil, s)) = ()
      | checkPattern (G, k, args, (I.SClo (S, s'), s)) = checkPattern (G, k, args, (S, I.comp(s', s)))
      | checkPattern (G, k, args, (I.App (U, S), s)) =
        (let
	   val k' = Whnf.etaContract (I.EClo(U, s))
	 in
	   if (k > k')
             andalso isUniversal (I.ctxLookup (G, k'))
	     andalso unique (k', args) 
	     then checkPattern (G, k, k'::args, (S, s))
	   else raise Whnf.Eta
	 end)

    fun isPattern (G, k, Ss) =
        (checkPattern (G, k, nil, Ss); true)
	handle Whnf.Eta => false



    (* this repeats some code from ../twelf/src/modes/modecheck.fun *)
    (* strictLF_Exp (G, p, Us) = true iff p occurs strict in Us *)
    fun strictLF_Exp (G, p, Us) = strictLF_ExpW (G, p, Whnf.whnf Us)
    and strictLF_ExpW (G, _, (I.Uni _, _)) = false
      | strictLF_ExpW (G, p, (I.Lam (D, U), s)) =
          strictLF_Dec(G, p, (D, s)) (* is this redundant??? *)
	  orelse strictLF_Exp (I.Decl(G, Universal), p+1, (U, I.dot1 s))
      | strictLF_ExpW (G, p, (I.Pi ((D', _), U), s)) =
	  strictLF_Dec (G, p, (D', s)) orelse strictLF_Exp (I.Decl(G, Universal), p+1, (U, I.dot1 s))
      | strictLF_ExpW (G, p, (I.Root (H, S), _(* id *) )) =
	  (case H
	     of (I.BVar (I.Fixed k')) => 	     
	        if (k' = p) then 
		         if isParam (I.ctxLookup(G, k')) then true
			 else isPattern (G, k', (S, I.id))
		else if isUniversal (I.ctxLookup (G, k')) then strictSpine (G, p, (S, I.id))
		     else if isParam (I.ctxLookup (G, k')) then strictSpine (G, p, (S, I.id))
			  else false
              | (I.Const (c)) => strictSpine (G, p, (S, I.id))
	      | (I.Def (d))  => strictSpine (G, p, (S, I.id))
              | (I.FgnConst (cs, conDec)) => strictSpine (G, p, (S, I.id))
	      | _ => false )
      | strictLF_ExpW (G, p, Us (* anything else *) ) = false (* not strict or not in Delphin (i.e. fgnexp) *)

    and strictLF_Dec (D, p, (I.Dec (_, V), s)) =
          strictLF_Exp (D, p, (V, s))
      | strictLF_Dec _ = crash() (* unexpected dec *)


    and strictSpine (_, _, (I.Nil, _)) = false
      | strictSpine (G, p, (I.App (U, S), s)) = 
          strictLF_Exp (G, p, (U, s)) orelse strictSpine (G, p, (S, s))
      | strictSpine (G, p, (I.SClo (S, s'), s)) = strictSpine (G, p, (S, I.comp(s', s)))


    (* check that variable p occurs strict in pattern E with (status) context G *)

    fun strictExp (G, p, E) = strictExpW (G, p, D.whnfE E)
    and strictExpW (G, p, D.Var (D.Fixed i, _)) = (p = i)
      | strictExpW (G, p, D.Var _) = false (* bad pattern but maybe occur? *)
      | strictExpW (G, p, D.Quote U) = strictLF_Exp (G, p, (U, I.id))
      | strictExpW (G, p, D.Unit) = false
      | strictExpW (G, p, D.Lam _) = crash() (* bad pattern *)
      | strictExpW (G, p, D.New (D, E, _)) = strictExp(I.Decl(G, Universal), p+1, E)
      | strictExpW (G, p, D.App _) = crash() (* bad pattern *)
      | strictExpW (G, p, D.Pair (E1, E2, _)) = strictExp(G, p, E1) orelse strictExp(G, p, E2)
      | strictExpW (G, p, D.ExpList _) = crash() (* bad pattern *)
      | strictExpW (G, p, D.Proj _) = crash() (* bad pattern *)
      | strictExpW (G, p, D.Pop (i, E, _)) = 
           let
	     fun popCtx (0, G) = G
	       | popCtx (i, I.Decl(G, D)) = popCtx (i-1, G)
	       | popCtx (i, I.Null) = crash() (* Broken invariant *)
	   in
	       if isUniversal (I.ctxLookup(G, i))
		 then strictExp (popCtx (i, G), p-i, E)
	       else false
	   end
      | strictExpW (G, p, D.Fix _) = crash() (* bad pattern *)
      | strictExpW (G, p, D.EVar _) = crash() (* bad pattern *)
      | strictExpW (G, p, D.EClo _) = crash() (* not in whnf *)

    fun strictExpPats (G, p, []) = false
      | strictExpPats (G, p, (vis,E)::pats) = strictExp(G,p, E) orelse strictExpPats(G, p, pats)

    fun checkStrictPattern (G, pats, [], otherCase) = ()
      | checkStrictPattern (G, pats, ((i, nameOpt, fileInfo) :: varList), otherCase) = 
          if strictExpPats(G, i, pats) then checkStrictPattern(G, pats, varList, otherCase)
	  else
	    let
	      val msg = case nameOpt of
		               SOME [s] => "Non Strict occurrence of variable " ^ s ^ "."
			      | _ => "Non Strict occurrence of variable."
	    in
	      case fileInfo
		of SOME(filename, r) => raise NotStrictError (Paths.wrapLoc (Paths.Loc (filename, r), msg))
		 | NONE => raise NotStrictError msg
	    end


    fun addOne [] = []
      | addOne ((n, nameOpt, fileInfo) :: xs) = (n+1, nameOpt, fileInfo) :: (addOne xs)

    (* G is a local context telling us whether variables are universal/existential
     * the variables in the global context are all considered existential here *)
    fun checkStrict (G, D.Eps (D.NormalDec (nameOpt, T), C, fileInfo), varList) = checkStrict (I.Decl(G, existential T), C, (1, nameOpt, fileInfo) :: (addOne varList))
      | checkStrict (G, D.NewC (D, C, _), varList) = checkStrict (I.Decl(G, Universal), C, addOne varList)
      | checkStrict (G, D.Match (pats, _), varList) = checkStrictPattern(G, pats, varList, NONE)
      | checkStrict (G, D.PopC _, varList) = crash() (* broken invariant.. no PopCs..removed before calling checkCase *)
      
    fun checkStrictList (G, []) = ()
      | checkStrictList (G, C::Clist) = (checkStrict (G, C, []) ; checkStrictList (G, Clist))

    fun globalStatusContext I.Null = I.Null
      | globalStatusContext (I.Decl(G, D.NonInstantiableDec _)) = I.Decl(globalStatusContext G, ExistentialParam)
                                                                                        (* global context is all considered
											 * existential for strictness 
											 * analysis.
											 *)

      | globalStatusContext (I.Decl(G, D.InstantiableDec (D.NormalDec(_, T)))) = I.Decl(globalStatusContext G, existential T) 
                                                                                        (* global context is all considered
											 * existential for strictness 
											 * analysis.
											 *)

    (* Main Function ... *)
    (* ***************************************************************************************************************** *)
    (* ***************************************************************************************************************** *)

    fun checkCases(smartInj, printEps, G, Clist, F) = 
            let	      
	      (* ABP WARNING:  We need to check that everything in G is named..
	       * otherwise it will print some names as "?" ..
	       *)
	      val G = PrintDelphinInt.ctxName G

	      val _ = checkStrictList(globalStatusContext G, Clist) (* raises NotStrictError if not strict *)
	    in
	      ()
	    end


    (* Invariant:  no PopCs *)
    fun checkCaseBody(smartInj, printEps, G, D.Eps(D, C, fileInfo)) = 
                 checkCaseBody(smartInj, printEps, I.Decl(G, D.InstantiableDec D), C)
      | checkCaseBody(smartInj, printEps, G, D.NewC(D, C, fileInfo)) = 
		 checkCaseBody(smartInj, printEps, I.Decl(G, D.NonInstantiableDec D), C)
      | checkCaseBody(smartInj, printEps, G, D.Match(pats, Ebody)) = 
		 check(smartInj, printEps, G, Ebody)
      | checkCaseBody(smartInj, printEps, G, D.PopC _) = crash() (* broken invariant.. no PopCs..*)


    and check(smartInj, printEps, G, E) = checkW(smartInj, printEps, G, D.whnfE E)
    and checkW(smartInj, printEps, G, D.Var _) = ()
      | checkW(smartInj, printEps, G, D.Quote _) = ()
      | checkW(smartInj, printEps, G, D.Unit) = ()

      | checkW(smartInj, printEps, G, D.Lam (Clist as (D.PopC(i, _)::_), F, fileInfo)) =
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
				                          of SOME (filename, r) => raise NotStrictError (Paths.wrapLoc (Paths.Loc (filename, r), ("Strictness Checker Failed UNEXPECTEDLY (" ^ msg ^ ")"))) (* should never fail! *)
							   | _ => raise NotStrictError ("Strictness Checker Failed UNEXPECTEDLY (" ^ msg ^ ")") (* should never fail! *)
				in
				  check (smartInj, printEps, G,  D.Pop (i, D.Lam (Clist', F', fileInfo), fileInfo))
				end


      | checkW(smartInj, printEps, G, D.Lam (Clist (* and no cases have PopC *), F, fileInfo)) = 
                                        let
					  val _ = (checkCases(smartInj, printEps, G, Clist, F)
                                                   handle NotStrictError s =>  
						      (* Too verbose -- ABP
							      let 
								val msg = "Strictness Violation:\n" ^ s ^ "\n"
							      in
								case fileInfo
								  of NONE => raise NotStrictError msg
								   | SOME(filename, r) => raise NotStrictError (Paths.wrapLoc(Paths.Loc (filename, r), msg))
							      end 
                                                      *)
						      raise NotStrictError s)
					  val _ = map (fn C => checkCaseBody(smartInj, printEps, G, C)) Clist
					in
					  ()
					end

      | checkW(smartInj, printEps, G, D.New (D, E, _)) = 
				check(smartInj, printEps, I.Decl(G, D.NonInstantiableDec D), E)

      | checkW(smartInj, printEps, G, D.App (E1, args)) =  
				(check(smartInj, printEps, G, E1) ; checkArgs(smartInj, printEps, G, args))

      | checkW(smartInj, printEps, G, D.Pair (E1, E2, _)) = 
				(check(smartInj, printEps, G, E1) ; check(smartInj, printEps, G, E2))

      | checkW(smartInj, printEps, G, D.ExpList []) = ()

      | checkW(smartInj, printEps, G, D.ExpList (E::Elist)) = 
				(check(smartInj, printEps, G, E) ; check(smartInj, printEps, G, D.ExpList Elist))

      | checkW(smartInj, printEps, G, D.Proj (E, i)) = 
				check(smartInj, printEps, G, E)

      | checkW(smartInj, printEps, G, D.Pop (i, E, fileInfo)) = 
				check(smartInj, printEps, D.popCtx(i, G), E)

      | checkW(smartInj, printEps, G, D.Fix (D, E)) = 
				check(smartInj, printEps, I.Decl(G, D.InstantiableDec D), E)

      | checkW(smartInj, printEps, G, D.EVar _ (* ref NONE *)) = ()

      | checkW(smartInj, printEps, G, D.EClo _) = crash() (* impossible by whnf *)



    and checkArgs(smartInj, printEps, G, []) = ()

      | checkArgs(smartInj, printEps, G, (vis, fileInfo, E)::args) = 
                 (check(smartInj, printEps, G, E) ; checkArgs (smartInj, printEps, G, args))


  end