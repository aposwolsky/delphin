(* Nabla Front-End *)
(* Author:  Adam Poswolsky *)

functor Nabla (structure NablaParser : PARSERR
		 structure Parse : PARSE) : NABLA =
struct

  exception Error of string

  structure I = IntSyn
  structure T = Twelf
  structure N = NablaExtSyntax
  structure N'= NablaIntSyntax (* What we are converting to *)
  structure C = NablaElab
  structure O = NablaOpsem
  structure L = Lexer
  structure LS = Stream    

  local
    val version = "Elphin, Release Version 1.0b, November 2004"
    val debug = ref false

    val prompt = "<E> "


    (* Used for the moveSome algorithm *)
    datatype someType = SomeLF of (string option) * I.Exp
                        | SomeMeta of (string option) * N'.Formula   

   (* checkEOF f = r 
       
      Invariant:
      If   f is the end of stream
      then r is a region
	 
      Side effect: May raise Error
    *)   
    fun checkEOF (LS.Cons ((L.EOF, r), s')) = r 
      | checkEOF (LS.Cons ((t, r), _))  = 
          raise Error  (Paths.wrapLoc(Paths.Loc (C.getFilename(),r),"Unexpected:  Found " ^ L.toString t ^ ".")) 
      | checkEOF _ = raise Domain

    fun getCase s = 
      let
	val c = case (String.explode(s)) 
	        of (c::xs) => c
		 | _ => raise Domain
      in
	if Char.isUpper(c) then L.ID (L.Upper, s) else L.ID (L.Lower, s)
      end

    fun getRegion (LS.Cons ((_, r), _)) = r
      | getRegion _ = raise Domain

         

    fun addToSignature(tokenList) =
      let
	val f = LS.expose (LS.fromList(tokenList))
	(* val f = LS.expose (L.lexStream (TextIO.openString s)) *)
	val (conDec, f') = ParseConDec.parseConDec' (f)
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),getRegion(f)),("Twelf Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val ans = LFparsing.install1 (C.getFilename(), (Parser.ConDec conDec, r2)) 
	val cid = case ans
	          of SOME(cid) => cid
		   | _ => raise Domain
      in
	cid
      end




    fun convertTypeConstant (r, name) = 
      let
	val Paths.Reg(a,b) = r
	val stringR = Paths.Reg(a, a + String.size(name))
      in	
	addToSignature([(getCase(name), stringR)] @  [(L.COLON,r)] @ [(L.TYPE, r)] @ [(L.EOF, r)])
      end


    fun convertObjectConstant (lfdec) = addToSignature(C.lfdecTokens(lfdec)) 

    fun setFixity(tokenList) =
      let
	val f = LS.expose (LS.fromList(tokenList))
	val (fdec, f') = ParseFixity.parseFixity' (f)
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),getRegion(f)),("Twelf Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val _ = LFparsing.install1 (C.getFilename(), (Parser.FixDec fdec, r2)) 
      in
	()
      end

    fun convertInfix ((N.INFIXL (r,n)), s) = setFixity([(L.INFIX, r), (getCase("left"), r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])
      | convertInfix ((N.INFIXR (r,n)), s) = setFixity([(L.INFIX, r), (getCase("right"), r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])
      | convertInfix ((N.NONASSOC (r,n)), s) = setFixity([(L.INFIX, r), (getCase("none"), r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])


    fun abstract(Psi, exp, r) =
      let
	(* val ctxs = [Psi] *)
	(*
        val _ = print "Before Abstraction\n"
	val _ = print (PrintNablaInt.expToString'([Psi], exp))
	val _ = print "\n"
	 *)

	fun append (Psi, I.Null) = Psi
	  | append (Psi, I.Decl (Psi', D)) = I.Decl (append (Psi, Psi'), D)


	val (Psi', exp') = NablaAbstract.abstractNabla Psi exp
	val numAbstracted = I.ctxLength(Psi')
	val originalSize = I.ctxLength(Psi)
	val ctxSize = numAbstracted + originalSize
	val Psi'' = append(Psi, Psi')


	(*
        val _ = print "After Abstraction\n"
	val _ = print ("Number Abstracted = " ^ (Int.toString(numAbstracted)) ^ "\n")
	val _ = print ("Original Size = " ^ (Int.toString(originalSize)) ^ "\n")
	val _ = print (PrintNablaInt.expToString'([append(Psi', Psi)], exp'))
	val _ = print "\n"
	  *)

        (* 
	 * For example,
             Psi = X2,X1
             Psi' = X3
             Makes sense in X3,X2,X1
             Want it to make sense in X2,X1,X3
             Substitution should be 2 3 1

             Psi = X3, X2,X1
             Psi' = X5, X4
             Makes sense in X5, X4, X3,X2,X1
             Want it to make sense in X3, X2,X1,X5, X4
             Substitution should be 3 4 5 1 2 
 
	  exp' makes sense in = Psi' @ Psi
                                Xn.. X(s+1) Xs.. X1

         we want a substitution that takes us from Psi' @ Psi  to Psi@ Psi'
	 we need to go to Xs.. X1, Xn .. X(s+1)
           (n-s+1) .. n .. 1 .. (n-s) .  shift n
	  This requires a renaming substitution over exp'
	 *)
	fun createSub (index, max, tail)  = 
	      if (index < max) 
		then N'.Dot(N'.Idx index, createSub (index+1, max, tail))
	        else if (index = max) 
		     then N'.Dot(N'.Idx index, tail)
		     else tail

 
	val specialSub = createSub(ctxSize-originalSize+1, ctxSize, createSub(1, ctxSize-originalSize, N'.Shift (ctxSize)))

	(*
	val _ = print "Renaming Substitution = "
	val _ = print (PrintNablaInt.subToString' specialSub)
	val _ = print "\n"
	*)

	val exp'' = N'.subst(exp', specialSub)

	(*
        val _ = print "After Abstraction And Reorder\n"
	val _ = print (PrintNablaInt.expToString'([Psi''], exp''))
	val _ = print "\n"
	*)



	(* When we create the somes, their placement will not affect the actual type
	 * however, we want to move them in as far as possible.
	 *)
	val subRemove1st = N'.Dot(N'.Undef, N'.id)
	fun remove1st E = N'.subst(E, subRemove1st)

	val subSwapTwo = N'.Dot(N'.Idx 2, N'.Dot(N'.Idx 1, N'.Shift 2))
	fun swapTwo E = N'.subst(E, subSwapTwo)

	fun occurs x = 
	  case (NablaAbstract.occurs x) 
	    of I.No => false
	     | _ => true

	fun occurs' x = 
	  case (NablaAbstract.occurs' x) 
	    of I.No => false
	     | _ => true

	fun createSomeExp (SomeLF (sO,U), E) = N'.Some(sO, U, E)
	  | createSomeExp (SomeMeta (sO,F), E) = N'.SomeM(sO, F, E)

	fun moveSome(ctxs, _, E as N'.Quote _, lastSol) =  lastSol

	  | moveSome(ctxs, _, E as N'.Fail, lastSol) = lastSol

	  | moveSome(ctxs, S, E as N'.App (E1, E2), lastSol) = 
	          (case (occurs(1, E1), occurs(1, E2))
		    of (true, false) => 
		           let
			     val try1 = createSomeExp(S,E1)
			     val newExp1 = N'.App(try1, remove1st E2)
			     val works1 = ((NablaTypeCheck.inferType(ctxs,newExp1) ; true)
					   handle NablaTypeCheck.Error _ =>  false)
			   in
			     if works1 then N'.App(moveSome(ctxs, S, E1, try1), remove1st E2)
			     else lastSol
			   end

		     | (false, true) =>
			   let
			     val try2 = createSomeExp(S,E2)
			     val newExp2 = N'.App(remove1st E1, try2)
			     val works2 = ((NablaTypeCheck.inferType(ctxs,newExp2) ; true)
					   handle NablaTypeCheck.Error _ =>  false)
			   in
			     if works2 then N'.App(remove1st E1, moveSome(ctxs, S, E2, try2))
			     else lastSol
			   end
		     | _ => lastSol)



	  | moveSome(ctxs, S, E as N'.Pair (E1, E2), lastSol) = 
	          (case (occurs(1, E1), occurs(1, E2))
		    of (true, false) => 
		           let
			     val try1 = createSomeExp(S, E1)
			     val newExp1 = N'.Pair(try1, remove1st E2)
			     val works1 = ((NablaTypeCheck.inferType(ctxs,newExp1) ; true)
					   handle NablaTypeCheck.Error _ =>  false)
			   in
			     if works1 then N'.Pair(moveSome(ctxs, S, E1, try1), remove1st E2)
			     else lastSol
			   end

		     | (false, true) =>
			   let
			     val try2 = createSomeExp(S, E2)
			     val newExp2 = N'.Pair(remove1st E1, try2)
			     val works2 = ((NablaTypeCheck.inferType(ctxs,newExp2) ; true)
					   handle NablaTypeCheck.Error _ =>  false)
			   in
			     if works2 then N'.Pair(remove1st E1, moveSome(ctxs, S, E2, try2))
			     else lastSol
			   end
		     | _ => lastSol)


	  | moveSome(ctxs, S, E as N'.First (E1), lastSol) = 
	          let
		    val try1 = createSomeExp(S, E1)
		    val newExp1 = N'.First(E1)
		    val works1 = ((NablaTypeCheck.inferType(ctxs,newExp1) ; true)
				  handle NablaTypeCheck.Error _ =>  false)
		  in
		    if works1 then N'.First(moveSome(ctxs, S, E1, try1)) 
		              else lastSol
		  end

	  | moveSome(ctxs, S, E as N'.Second (E1), lastSol) = 
	          let
		    val try1 = createSomeExp(S, E1)
		    val newExp1 = N'.Second(E1)
		    val works1 = ((NablaTypeCheck.inferType(ctxs,newExp1) ; true)
				  handle NablaTypeCheck.Error _ =>  false)
		  in
		    if works1 then N'.Second(moveSome(ctxs, S, E1, try1)) 
		              else lastSol
		  end

	  | moveSome(ctxs, _, E as N'.EVar (_, ref NONE, _), lastSol) = lastSol
	  | moveSome(ctxs, S, E as N'.EVar (_, ref (SOME E'), _), lastSol) = moveSome(ctxs, S, E', lastSol)
	  | moveSome(ctxs, _, E as N'.EClo (E1, _), lastSol) = lastSol (* we should not go under EClo?? *)

	  | moveSome(Psi::ctxs, S, E as N'.Some (sO, U, E1), lastSol) = 
		  (* Psi::ctxs |- Some(S).E makes sense *)

		  (* ADAM, CARSTEN:  For dependently type case we need to put F under
		   * substitutions as well *)
	          let
		    val try1 = createSomeExp(S, swapTwo E1)
		    val newExp1 = N'.Some(sO, U, try1 (* under something *))
		    val works1 = ((NablaTypeCheck.inferType(Psi::ctxs,newExp1) ; true)
				  handle NablaTypeCheck.Error s =>  false)

		    val Psi' = I.Decl(Psi, N'.LFDec(I.Dec(NONE, U)))

		  in
		    if works1 then N'.Some(sO, U, moveSome(Psi'::ctxs, S, swapTwo E1, try1)) 
		              else lastSol
		  end


	  | moveSome(Psi::ctxs, S, E as N'.SomeM (sO, F', E1), lastSol) = 
	          let
		    val try1 = createSomeExp(S, swapTwo E1)
		    val newExp1 = N'.SomeM(sO, F', try1)
		    val works1 = ((NablaTypeCheck.inferType(Psi::ctxs,newExp1) ; true)
				  handle NablaTypeCheck.Error _ =>  false)

		    val Psi' = I.Decl(Psi, N'.MetaDec(NONE, F'))
		  in
		    if works1 then N'.SomeM(sO, F', moveSome(Psi'::ctxs, S, swapTwo E1, try1)) 
		              else lastSol
		  end

	  | moveSome(Psi::ctxs, S, E as N'.New (sO, U, E1), lastSol) = 
		  if (occurs'([NONE, SOME 1], E1)) then lastSol
		  else
	          let
		    (* We know some(S).New(U).E1  works..
		     * Originally  (Psi, S) |-> New(U).E1 works
		     *             (Psi, S, U) :: (Psi, S) :: _  |- E1 works
		     *  We want to see if
		     *     New(U).Some(S).E1 works
		     *     (Psi,U)::Psi::_  (someS. E1)
		     *     (Psi,U,S)::Psi::_
		     
		     * we now want to see if New(U).some(S).E1 works.
		     * This is actually the most critical case
		     * we need to examine.
		     *)
		    val try1 = createSomeExp(S, N'.substL(E1,[subSwapTwo, subRemove1st]))
		    val newExp1 = N'.New(sO, U, try1)

		    val works1 = ((NablaTypeCheck.inferType(Psi::ctxs,newExp1) ; true)
				  handle NablaTypeCheck.Error _ =>  false)

		    val Psi' = I.Decl(Psi, N'.LFDec(I.Dec(NONE, U)))


		  in
		    if works1 then N'.New(sO, U, moveSome(Psi'::Psi::ctxs, S, N'.substL(E1,[subSwapTwo, subRemove1st]), try1)) 
		              else lastSol
		  end

	  | moveSome(Psi::ctxs, S, E as N'.Nabla (sO, U, E1), lastSol) = 
	          let
		    val try1 = createSomeExp(S, swapTwo E1)
		    val newExp1 = N'.Nabla(sO, U, try1)
		    val works1 = ((NablaTypeCheck.inferType(Psi::ctxs,newExp1) ; true)
				  handle NablaTypeCheck.Error _ =>  false)

		    val Psi' = I.Decl(Psi, N'.LFDec(I.Dec(NONE, U)))
		  in
		    if works1 then N'.Nabla(sO, U, moveSome(Psi'::ctxs, S, swapTwo E1, try1)) 
		              else lastSol
		  end

	  | moveSome(Psi::ctxs, S, E as N'.Fix (sO, F, E1), lastSol) = 
	          let
		    val try1 = createSomeExp(S, swapTwo E1)
		    val newExp1 = N'.Fix(sO, F, try1)
		    val works1 = ((NablaTypeCheck.inferType(Psi::ctxs,newExp1) ; true)
				  handle NablaTypeCheck.Error _ =>  false)

		    val Psi' = I.Decl(Psi, N'.MetaDec(NONE, F))
		  in
		    if works1 then N'.Fix(sO, F, moveSome(Psi'::ctxs, S, swapTwo E1, try1)) 
		              else lastSol
		  end


	  | moveSome(ctxs, S, E as N'.Case (E1, F, E2), lastSol) = 
	          (case (occurs(1, E1), occurs(1, E2))
		    of (true, false) => lastSol		             
		      (* If it occurs on the left side
		       * it means that it is used in a pattern, so we
		       want it outside
		       *)

		     | (false, true) =>
			   let
			     val try2 = createSomeExp(S, E2)
			     val newExp2 = N'.Case(remove1st E1, F, try2)
			     val works2 = ((NablaTypeCheck.inferType(ctxs,newExp2) ; true)
					   handle NablaTypeCheck.Error _ =>  false)
			   in
			     if works2 then N'.Case(remove1st E1, F, moveSome(ctxs, S, E2, try2))
			     else lastSol
			   end
		     | _ => lastSol)


	  | moveSome(ctxs, S, E as N'.Alt (E1, E2), lastSol) = 
	          (case (occurs(1, E1), occurs(1, E2))
		    of (true, false) => 
		           let
			     val try1 = createSomeExp(S, E1)
			     val newExp1 = N'.Alt(try1, remove1st E2)


			     val works1 = ((NablaTypeCheck.inferType(ctxs,newExp1) ; true)
					   handle NablaTypeCheck.Error s =>  false)
			     
			   in
			     if works1 then N'.Alt(moveSome(ctxs, S, E1, try1), remove1st E2)
			     else lastSol
			   end

		     | (false, true) =>
			   let
			     val try2 = createSomeExp(S, E2)
			     val newExp2 = N'.Alt(remove1st E1, try2)


			     val works2 = ((NablaTypeCheck.inferType(ctxs,newExp2) ; true)
					   handle NablaTypeCheck.Error s =>  (print s ; false))
			   in
			     if works2 then N'.Alt(remove1st E1, moveSome(ctxs, S, E2, try2))
			     else lastSol
			   end
		     | _ => lastSol)


	  | moveSome(Psi::ctxs, S, E as N'.Pop (E1), lastSol) = 
		    (* We know some(S).Pop(E1) works..
		     * we now want to see if Pop (some(S).E1) works.
		     * However, E1 cannot depend on S in this case
		     * so there isn't much to do in this case 
		     * 
		     * Hmmm.. perhaps the strictness checking
		     * can be performed by just checking if the Some
		     * can be eliminated.  It can in this case
		     *)
		     lastSol
		  


	  | moveSome(ctxs, S, E as N'.Var _, lastSol) = lastSol

	  | moveSome _ = raise Domain

	(*
	fun createSomesOld(I.Null, E) = E
	  | createSomesOld(I.Decl(X, N'.LFDec(I.Dec(_,U))), E) = 
	        let
		  val goodExp = N'.Some(U, E, N'.newTVar())
		in
		  createSomesOld(X, goodExp)
		end 
	 *)


	fun createSomes(G, E, 0) = E
	  | createSomes(I.Decl(X, N'.LFDec(I.Dec(sO,U))), E, d) = 
	        let
		  val goodExp = N'.Some(sO, U, E)
		  (*
		  val _ = print "\nBefore-ExpressionInitial\n"
		  val _ = print (PrintNablaInt.expToString'(updateCtxs(ctxs,X), goodExp))
		  val _ = print "\n"
		  val goodExp' = moveSome(updateCtxs(ctxs, X), someLF U, E, goodExp)
		  *)
		  val goodExp' = moveSome([X], SomeLF (sO,U), E, goodExp)

		in
		  createSomes(X, goodExp', d-1)
		end 

	  | createSomes(I.Decl(X, N'.MetaDec(sO, F)), E, d) = 
	        let
		  val sO' = case sO 
		            of SOME [s] => (SOME s)
			     | NONE => NONE
                             | _ => raise Domain
              
		  val goodExp = N'.SomeM(sO', F, E)
		    
		  val goodExp' = moveSome([X], SomeMeta (sO', F), E, goodExp)
		in
		  createSomes(X, goodExp', d-1)
		end 
	  | createSomes _ = raise Domain

	(* val newExp = createSomesOld(Psi'', exp'') *)
	val newExp = createSomes(Psi'', exp'', numAbstracted)


	(* Since we just introduced some TVar's in createSomes, we need to infer
	 * to remove types *)

	val _ = NablaTypeCheck.inferType([Psi], newExp)
	  handle NablaTypeCheck.Error s => 
	    raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),r),s))

	(*
	val _ = print "Final Expression:\n"
	val _ = print (PrintNablaInt.expToString'([Psi], newExp))
	val _ = print "\n"
	*)


	      
      in
	newExp
      end
	
    fun convert(Psi, (N.LFTypeConstant (r,s))) = (convertTypeConstant (r,s) ; NONE)
      | convert(Psi, (N.LFObjectConstant (r, lfdec, infixO))) =
		let
		  val _ = convertObjectConstant (lfdec)
		  val N.LFDec(_, s, _)   = lfdec
		  val _ = case (infixO)
		          of NONE => ()
			   | SOME (i) => convertInfix(i, s)
		in
		  NONE
		end
      | convert(Psi, (E as N.MetaFix L)) =
	    let

	      fun find(x, []) = false
		| find(x, x'::xs) = (x = x') orelse find(x, xs)
	      fun hasDuplicates [] = false
		| hasDuplicates (x::xs) = find(x,xs) orelse hasDuplicates(xs)

	      (* L = [(r, dec, term)]
               * val (N.MetaDec (_, s, _)) = dec
	       *)

	      fun getRegionInfo [(r, dec, term)] = r
		| getRegionInfo ((r,dec,term)::xs) = Paths.join (r, getRegionInfo xs)
		| getRegionInfo _ = raise Domain

	      fun getStringList [(r, N.MetaDec (_, s, _), term)] = [s]
		| getStringList ((r,N.MetaDec (_, s, _),term)::xs) = s::(getStringList xs)
		| getStringList _ = raise Domain

		
	      val L' = C.renameVarsFixList0 L

	      val sList = getStringList L'


	      val r = getRegionInfo L'

	      val _ = if hasDuplicates(sList) then 
		raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(), r), "Duplicate Identifiers defined in mutual recursion\n")) else ()





	      val _ = if !debug then (print "\n-----BEGIN OUTPUT-----\n" ; print (PrintNablaExt.topDecStr (N.MetaFix L')) ; print "\n-----END OUTPUT-----\n") else ()

	      val (Psi', result) = C.convertFixList0(Psi, L')


	      val (sO,form, exp) = case result 
		                of N'.Fix(sO,form, exp) => (sO,form, exp)
				 | _ => raise Domain


	      (* we need to now make sure infer the type and make sure there are no free TVar's *)
	      (* we want to typecheck before abstraction to get rid of TVar's *)

	      (*
	      val _ = print "Expression:\n"
	      val _ = print (PrintNablaInt.expToString'([Psi], result))
	      val _ = print "\n"
	      val _ = print "Formula is:\n"
	      val _ = print (PrintNablaInt.formStr(Psi, N'.getForm(result)))
	      val _ = print "\n"
		*)

	      val form' = NablaTypeCheck.inferType([Psi], result)
		handle NablaTypeCheck.Error s => raise Error 
		                                 (Paths.wrapLoc(Paths.Loc (C.getFilename(), r), s))


	      val _ = if not (UnifyNabla.forEqual(Psi',(form, N'.Shift 1),(form',N'.id))) then raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),r),("Incompatible Types!\nType 1 = " ^ PrintNablaInt.formStr(Psi,form) ^ "\nType 2 = " ^ PrintNablaInt.formStr(Psi',form')))) else ()

	      (* Now we need to check that there are no object type-level EVar's *)
	      val _ = if (NablaAbstract.hasLFTypeEVars([Psi'], exp)) then
		raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(), r), ("Insufficient Type Information")))
		      else ()

	      (* Let's now abstract away *)


  	      val newExp = abstract(Psi', exp, r)




	      (* Note:  since it is a fixpoint, the type will be inferred 
	       * and will check that user specified type matches
	       * but since it is top-level, we need to make the type is closed.
	       *)
	      val formN = if (NormalizeNabla.noFreeVars(form)) then
		          NormalizeNabla.normalizeFor(form)
			    else raise Error 
			      (Paths.wrapLoc(Paths.Loc (C.getFilename(),r),
			      ("Need closed type, but inferred " ^ PrintNablaInt.formStr(Psi,form))))

	      val resultN =  N'.Fix(sO,formN, newExp)
	    in
	      SOME(Psi',sList, resultN, formN)
	    end  

      | convert(Psi, (N.MetaVal (r, term))) =
	    let
	      val nablaExp = C.renameVars0 (term)
	      val _ = if !debug then (print "\n-----BEGIN OUTPUT-----\n" ; print (PrintNablaExt.metaStr (nablaExp)) ; print "\n-----END OUTPUT-----\n") else ()


	      val result = C.convertMeta0 (Psi, nablaExp)


	     (* we need to now make sure infer the type and make sure there are no free TVar's *)
	      (* we want to typecheck before abstraction to get rid of TVar's *)
	      val form = NablaTypeCheck.inferType([Psi], result)
		handle NablaTypeCheck.Error s => raise Error 
		                                 (Paths.wrapLoc(Paths.Loc (C.getFilename(), r), s))


	      (* Now we need to check that there are no object type-level EVar's *)
	      val _ = if (NablaAbstract.hasLFTypeEVars([Psi], result)) then
		raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(), r), ("Insufficient Type Information")))
		      else ()


	      (* Let's now abstract away *)
	      val newExp = abstract(Psi, result, r)

	      val formN =if (NormalizeNabla.noFreeVars(form))
		         then NormalizeNabla.normalizeFor(form)
		         else raise Error 
			  (Paths.wrapLoc(Paths.Loc (C.getFilename(),r),
			      ("Need closed type, but inferred " ^ PrintNablaInt.formStr(Psi,form))))

	      val Psi' = I.Decl(Psi, N'.MetaDec (SOME ["it"], formN))
	    in
	      SOME(Psi', ["it"], newExp, formN)
	    end  

      | convert(Psi, (N.Use _)) = raise Domain


    fun eval(E,F,t) =
      let

	fun checkConstraints NONE = NONE
	  | checkConstraints (SOME E) = if (NablaAbstract.checkConstraints I.Null E) then SOME E
	                                else NONE


	val E' = NormalizeNabla.normalizeExp(E)

        (* it is possible that this *t* contains (no solution) in it and the substitution will
	   result in error *)
	val E''opt = SOME(N'.substExact(E',t)) handle N'.NoSolution => NONE

	  (*
	val _ = print "Final Final Expression:\n"
	val _ = print (PrintNablaInt.expToString'([I.Null], E''))
	val _ = print "\n"
	   *)

      in
	case F
	  of (N'.Imp _) => E''opt
	   | _ => (case E''opt of NONE => NONE
		                | (SOME E'') => checkConstraints(SOME(O.eval0 E'')) handle O.NoSolution => NONE)
      end

    fun spaceString(0) = ""
      | spaceString(x) = " " ^ spaceString(x-1)

    fun solutionToString (s, F, NONE) = s ^ " : " ^ F ^ "\n" ^ spaceString(String.size(s)) 
                                        ^ " = " ^ "(no solutions)" ^ "\n"

      | solutionToString (s, F, SOME(E)) = 
           let
	     val firstLine = s ^ " : " ^ F ^ "\n" 
	     val secondLineHead = spaceString(String.size(s)) ^ " = "
	     (* val expString = PrintNablaInt.expToString'([I.Null], E) *)
	     val expString = PrintNablaInt.expToString(I.Null, E) 

	     (* This Formatter doesn't work as I would expect, so
	      * just offset it manually 
	      *)
	     (*
	     val format = Formatter.HVbox [Formatter.String(secondLineHead), Formatter.String(expString)]
	     val result = firstLine ^ (Formatter.makestring_fmt format) ^ "\n"
	       *)


	     val offset = spaceString(String.size(secondLineHead))
	     fun translator (#"\n") = "\n" ^ offset
	       | translator c = Char.toString(c)
	     val expString' = String.translate translator expString

	     val result = firstLine ^ secondLineHead ^ expString' ^ "\n"

	      
	   in
	     result
	   end

    fun convertAndEvaluate(Psi, t, (N.Use s)) = 
      let
	fun isDelim c = if ((c = #"\"") orelse (c = #" ")) then true else false
	val tokens = String.tokens isDelim s
	val fname = case tokens
	        of [fname] => fname
	         | _ => raise Domain

	val _ = C.reset()
	val _ = C.setFilename(fname)
	val res = (Parse.fparse fname)
	  handle ParseError => raise Error "Error Parsing File\n\n"

	 val _ = if (!debug) then (print "\n-----BEGIN OUTPUT-----\n" ; print (PrintNablaExt.nablaToStr (res)) ; print "\n-----END OUTPUT-----\n") else ()
      in
	convertAndEvaluateList(Psi, t, res)
      end


      | convertAndEvaluate(Psi, t, nablaExt) =
      let
	val error = ref false
	val resultO = convert(Psi, nablaExt)
	   handle Names.Error s => (print (s ^ "\n\n") ; error := true ; NONE)
		| ReconTerm.Error s => (print ( s ^ "\n\n") ; error := true ; NONE)
	        | Error s => (print ( s ^ "\n\n") ; error := true ; NONE)
		| C.Error s => (print ( s ^ "\n\n") ; error := true ; NONE)
		| C.NotImplemented s => (print ("NotImplemented raised: " ^ s ^ "\n\n") ; error := true ; NONE)
      in
	if (!error) then
	  raise Error "Error occurred\n" 
	else
	  case (resultO) 
	    of NONE => (Psi, t)
	     | SOME(Psi',sList,E,F) => 
	           let
		     val V = eval(E,F,t)
		     val t' = N'.Dot(N'.Prg V, t)

                     val numGenerated = length (sList)

		     fun convertFtoList (1, F) = [F]
		       | convertFtoList (k, (N'.And (F1, F2))) = F1::(convertFtoList(k-1, F2))
		       | convertFtoList _ = raise Domain

		     fun convertVtoList (1, X : NablaIntSyntax.Exp option) = [X]
		       | convertVtoList (k, SOME(N'.Pair (V1, V2))) = (SOME(V1))::(convertVtoList(k-1, SOME V2))
		       | convertVtoList _ = raise Domain

		     val fList = convertFtoList (numGenerated, F)
		     val vList = convertVtoList (numGenerated, V)

		     fun printList (s, F, V) = print (solutionToString(s,PrintNablaInt.formStr(Psi,F),V))

		     fun mergeLists ([], [], []) = []
		       | mergeLists (x::xs, y::ys, z::zs) = (x,y,z)::mergeLists(xs,ys,zs)
		       | mergeLists _ = raise Domain

		     val _ = map printList (mergeLists (sList, fList, vList))

		   in
		     (Psi', t')		       
		   end
      end
	  

    and convertAndEvaluateList(Psi, t, []) = (Psi, t)

      | convertAndEvaluateList(Psi, t, x::xs) =
            let
	      val (Psi', t') = convertAndEvaluate(Psi,t,x)
	    in
	      convertAndEvaluateList(Psi', t', xs)
	    end

    fun loadFile s =
      let 
	val _ = Global.chatter := 0
	val _ = Twelf.reset()
	val _ = C.reset()
	val _ = C.setFilename(s)
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
	(* val _ = print ("[Parsing file ...") *)
	val res = (Parse.fparse s)
	  handle ParseError => (print ("Error Parsing File\n\n") ; [])
	(* val _ = print ("[done]\n") *)
	 val _ = if (!debug) then (print "\n-----BEGIN OUTPUT-----\n" ; print (PrintNablaExt.nablaToStr (res)) ; print "\n-----END OUTPUT-----\n") else ()
	val _ = (convertAndEvaluateList(I.Null, N'.Shift 0, res)
	        handle Error s => (print s ; (I.Null, N'.Shift 0)))
      in 
	()
      end

    and top () = 
      let
	val _ = print ("\n" ^ version ^ "\n\n")
	val _ = Global.chatter := 0 
	val _ = Twelf.reset()
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
      in
	loop (ref (I.Null), ref (N'.Shift 0))
      end


    and top' (PsiRef, tRef) =
      let
	val _ = Global.chatter := 0 
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
      in
	loop (PsiRef, tRef)
      end


    and loop (PsiRef, tRef) = 
      let 
	 val _ = C.reset()

         val _ = print prompt
         val res = (Parse.sparse ())
	   handle NablaParser.ParseError => (print ("ERROR(S) Found\n\n") ; [])

	 val _ = if (!debug) then (print "\n-----BEGIN OUTPUT-----\n" ; print (PrintNablaExt.nablaToStr (res)) ; print "\n-----END OUTPUT-----\n") else ()

	val (Psi', t') = (convertAndEvaluateList(!PsiRef, !tRef, res)
	        handle Error s => (print s ; (!PsiRef, !tRef)))

	val _ = (PsiRef := Psi')
	val _ = (tRef := t')
      in 
         loop (PsiRef, tRef)
      end


  in
    val version = version
    val debug = debug
    val loadFile = loadFile
    val top = top
    val top' = top'

  end
end  (* functor NablaTop *)
