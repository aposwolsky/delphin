(* 
 * Used to print Delphin Internal Syntax 
 * Author:  Adam Poswolsky
 *)

(* This proceeds by converting the internal syntax into the external syntax
 * and then using the external printer to print.  Here we need to fill in names
 * for variables and we make sure it is capture avoiding.  
 *
 * Note that once converted to external syntax
 * it is not intended to be converted back into internal syntax.
 *)

structure PrintDelphinInt =
  struct
    structure D = DelphinIntSyntax
    structure D' = DelphinExtSyntax
    structure DP = PrintDelphinExt
    structure I = IntSyn
    structure Fmt = Formatter
    structure Print = Print

    structure Names = Names

    val rDummy = Paths.Reg(~1,~1)

    (* ABP:  Currently FVarsList and EVarsList are NOT USED
     * We just print "_" for both..  If we update this, we should SWITCH
     * from this manual mapping to a "StringTree" table as in recon-term.fun and convert.fun
     *)
    val FVarsList : (((D.Formula option) ref) * string) list ref = ref [] 
    val EVarsList : (((D.Exp option) ref) * string) list ref = ref [] 
     
    fun varReset G =
      (EVarsList := [] ;
       FVarsList := [] ;  
       Names.varReset (D.coerceCtx G))

(*
    fun stringListToString [s] = s
      | stringListToString sL =
            let	      
	      fun toString [] = raise Domain
		| toString [s] = s ^ "]"
		| toString (s::ss) = s ^ ", " ^ (toString ss)
	    in
	      "[" ^ toString sL
	    end
*)

    val takeNonDigits = Substring.takel (not o Char.isDigit)

    (* baseOf (name) = name',
       where name' is the prefix of name not containing a digit
    *)
    fun baseOf (name) = Substring.string (takeNonDigits (Compat.Substring.full name))


    (* returns true if name already exists as a variable name *)
    fun varDefined name =
      let
	fun findName' ([]) = false
	  | findName' ((_,s)::xs) = (s=name) orelse findName' xs
      in
	(findName' (!FVarsList)) orelse (findName' (!EVarsList))
      end

    fun nameInList (name : string, []) = false
      | nameInList (name, s::xs) = (name=s) orelse nameInList(name,xs)

    (* check that name occurs at most once *)
    fun uniqueInList(name : string, []) = true
      | uniqueInList(name, s::xs) = if (name = s)
				      then not(nameInList(name, xs))
				    else uniqueInList(name, xs)


    (* checks if variable with "name" already in context. *)
    fun ctxDefined(I.Null, _) = false
      | ctxDefined (I.Decl (G, D.InstantiableDec (D.NormalDec (SOME sL, _))), name) = 
                  nameInList(name,sL) orelse ctxDefined(G, name)
      | ctxDefined (I.Decl(G, D.NonInstantiableDec (D.NewDecLF (SOME s, _))), name) =
		 s = name orelse ctxDefined(G, name)
      | ctxDefined (I.Decl(G, D.NonInstantiableDec (D.NewDecWorld (SOME s, _))), name) =
		 s = name orelse ctxDefined(G, name)
      | ctxDefined (I.Decl(G, _), name) = ctxDefined(G, name)

   (* returns the index where "name" occurs first *)
      (* Precondition:  it occurs somewhere *)
    fun firstOccurrence (I.Null, name, k) = raise Domain (* it doesn't occur *)
      | firstOccurrence (I.Decl (G, D.InstantiableDec (D.NormalDec (SOME sL, _))), name, k) = 
                  if (nameInList(name,sL)) 
		    then if uniqueInList(name,sL) then k
			 else raise Domain
		                (* name is ambiguous in the mutual recursive
				 * list of functions.. this is
				 *  disallowed in delphin.fun
				 *)
		  else
		    firstOccurrence (G, name, k+1)

      | firstOccurrence (I.Decl(G, D.NonInstantiableDec (D.NewDecLF (SOME s, _))), name, k) =
		    if (s = name) then k 
		    else
		      firstOccurrence (G, name, k+1)

      | firstOccurrence (I.Decl(G, D.NonInstantiableDec (D.NewDecWorld (SOME s, _))), name, k) =
		    if (s = name) then k
		    else
		      firstOccurrence (G, name, k+1)

      | firstOccurrence (I.Decl(G, _), name, k) = firstOccurrence(G, name, k+1)


   (* If lookup(i, G) (or some other lookup) = s
    * then varString(s, i) creates the appropriate
    * string to identify the variable
    *)
   fun varString(G, s, i) = if ((firstOccurrence(G, s, 1) = i) andalso not (varDefined s))
                                  then s
				 else ("%" ^ s ^ "%(#" ^ Int.toString(i) ^")")


    fun getNextName (G, base) =
      (* this just tries all possibilities from base1 ... 
       * this should be optimized at some point...
       *)
      let
	fun getNext(i) =
	     let 
	       val name = base ^ (Int.toString i)
	     in
	       if varDefined name orelse ctxDefined(G, name)
		 then getNext(i+1)
	       else
		 name
	     end
      in
	getNext(1)
      end 

    (* same as getNextName but also checks that name not in "l" *)
    fun getNextName' (l, G, base) =
      let
	fun getNext(i) =
	     let 
	       val name = base ^ (Int.toString i)
	     in
	       if varDefined name orelse ctxDefined(G, name) orelse nameInList(name,l)
		 then getNext(i+1)
	       else
		 name
	     end
      in
	getNext(1)
      end 
      




    fun getFVar (G,x) =
      let 
	fun findVar' (x : D.Formula option ref, []) = NONE
	  | findVar' (x, ((x',s)::xs)) = if (x = x') then SOME s else findVar'(x,xs)
      in
	case findVar' (x, !FVarsList) of
	    SOME s => s
	    | NONE => let
			val s = getNextName(G, "?a") 
			val _ = FVarsList := (x, s) :: !FVarsList
		      in
			s 
		      end
      end

    fun getEVar (G,x)=
      let 
	fun findVar' (x : D.Exp option ref, []) = NONE
	  | findVar' (x, ((x',s)::xs)) = if (x = x') then SOME s else findVar'(x,xs)
      in
	case findVar' (x, !EVarsList) of
	    SOME s => s
	    | NONE => let
			val s = getNextName(G, "X") 
			val _ = EVarsList := (x, s) :: !EVarsList
		      in
			s 
		      end
      end



     (* names variables based on type.  For LF types it calls the LF
      * routines.  However, we must also check this resulting string
      * is unique on the meta-level once it is returned
      *)
    fun getNamesFromType (false (* existential *), G, D.LF(_, A)) = 
		 (case (Names.decName (D.coerceCtx G, I.Dec (NONE, A))) 
		 of (I.Dec (SOME s, A)) => [s]
                  | _ => raise Domain)
      | getNamesFromType (true (* universal *), G, D.LF(_, A)) = 
		 (case (Names.decUName (D.coerceCtx G, I.Dec (NONE, A))) 
		 of (I.Dec (SOME s, A)) => [s]
                  | _ => raise Domain)

      (* Enhancement:  If it is just a pair with top, then get name based on first part *)
      | getNamesFromType (false, G, D.Meta(D.Exists(D.NormalDec(_, D.LF(_, A)), D.Top))) =
		 (case (Names.decName (D.coerceCtx G, I.Dec (NONE, A))) 
		 of (I.Dec (SOME s, A)) => [s]
                  | _ => raise Domain)

      | getNamesFromType (true, G, D.Meta(D.Exists(D.NormalDec(_, D.LF(_, A)), D.Top))) =
		 (case (Names.decUName (D.coerceCtx G, I.Dec (NONE, A))) 
		 of (I.Dec (SOME s, A)) => [s]
                  | _ => raise Domain)

      | getNamesFromType (isUniversal, G, D.Meta(D.FormList Flist)) =
		    let
		      fun getOneName F = (case getNamesFromType(isUniversal, G, D.Meta(F))
					    of [s] => s
					     | _ => raise Domain (* formula can't have more than one name *)
					  )
		    in
		      (map getOneName Flist)
		    end

      | getNamesFromType (false, G, _) = ["U"]
      | getNamesFromType (true, G, _) = ["u"] (* these variables may undergo renaming by newDecName or normalDecName *)
		    

    fun normalDecName (G, D as D.NormalDec (SOME [], T)) = D.NormalDec (NONE, T) (* shouldn't ever occur *)
      | normalDecName (G, D as D.NormalDec (SOME [name], T)) = 
          (* If name = "@???" then it was a generated fresh name in convert.fun and should be changed 
	   * before printing as "@" is a reserved symbol in Delphin.
	   *)
           if (String.isPrefix "@" name) then normalDecName(G, D.NormalDec(NONE, T))
	   else if varDefined name orelse ctxDefined(G, name) 
		  then D.NormalDec(SOME [getNextName(G, baseOf name)], T)
		else D
	       
      | normalDecName (G, D as D.NormalDec (SOME sL, T)) = 
                      let
			fun nameList (l, []) = l
			  | nameList (l, (name::ss)) = 
			      let val name' = if varDefined name orelse ctxDefined(G,name) orelse nameInList(name, l)
						then getNextName'(l, G, baseOf name)
					      else name
			      in
				nameList(l@[name'], ss)
			      end
		      in
			D.NormalDec (SOME (nameList([], sL)), T)
		      end			  
			             

      | normalDecName (G, D.NormalDec (NONE, T)) =
			normalDecName (G, D.NormalDec (SOME (getNamesFromType(false, G, T)), T))






    fun newDecName (G, D as D.NewDecLF (SOME name, A)) = 
          (* If name = "@???" then it was a generated fresh name in convert.fun and should be changed 
	   * before printing as "@" is a reserved symbol in Delphin.
	   *)
          if (String.isPrefix "@" name) then newDecName(G, D.NewDecLF(NONE, A))
	  else
                        if varDefined name orelse ctxDefined(G, name)
			  then D.NewDecLF(SOME (getNextName(G, baseOf name)), A)
			else D

      | newDecName (G, D as D.NewDecWorld (SOME name, W)) =
          (* If name = "@???" then it was a generated fresh name in convert.fun and should be changed 
	   * before printing as "@" is a reserved symbol in Delphin.
	   *)
          if (String.isPrefix "@" name) then newDecName(G, D.NewDecWorld(NONE, W))
	  else

                        if varDefined name orelse ctxDefined(G, name)
			  then D.NewDecWorld(SOME (getNextName(G, baseOf name)), W)
			else D

      | newDecName (G, D as D.NewDecLF (NONE, A)) =
			  let
			    val s = (case (getNamesFromType(true, G, D.LF(D.Existential, A)))
				       of [s] => s
					| _ => raise Domain 
			             )
			  in
			    newDecName (G, D.NewDecLF (SOME s, A))
			  end

      | newDecName (G, D as D.NewDecWorld (NONE, W)) =
			  let
			    val s = "W"
			  in
			    newDecName (G, D.NewDecWorld (SOME s, W))
			  end
			  

    fun decName (G, D.InstantiableDec D) = D.InstantiableDec (normalDecName (G,D))
      | decName (G, D.NonInstantiableDec D) = D.NonInstantiableDec (newDecName (G,D))


    (* convert from internal to external syntax *)
    fun convert_isParam (D.Existential) = D'.Existential
      | convert_isParam (D.Param) = D'.Param
      | convert_isParam (D.PVar (ref (SOME P))) = convert_isParam P
      | convert_isParam (D.PVar (ref NONE)) = D'.OmittedParam


    fun convert_Types (smartInj, G, T) = 
         let
	   val _ = Names.mark()
	   val T' = convert_Types'(smartInj, G, T)
	   val _ = Names.unwind()
	 in
	   T'
	 end

    and convert_Types' (smartInj, G, D.LF (isP, A)) = D'.LF(rDummy, convert_isParam isP, D'.ExplicitLF (Print.formatExp(D.coerceCtx G, A)))
      | convert_Types' (smartInj, G, D.Meta (F)) = D'.Meta(rDummy, convert_Formula (smartInj, G,F))

    and convert_Formula (smartInj, G, F) = 
         let
	   val _ = Names.mark()
	   val F' = convert_FormulaN (smartInj, G, D.whnfF F)
	   val _ = Names.unwind()
	 in
	   F'
	 end

    and convertVisibility (D.Visible) = D'.Visible
      | convertVisibility (D.Implicit) = if (!Print.implicit)
                                         then D'.Visible (* we make everything visible *)
					 else D'.Implicit

    and convert_FormulaN (smartInj, G, D.Top) = D'.Top rDummy

      | convert_FormulaN (smartInj, G, D.All (Ds, F)) = 
                                            let 
					      val (Ds, Ds', G') = convert_NormalDecs (smartInj, G, Ds)
					    in 
					      D'.All (rDummy, Ds', convert_Formula(smartInj, G', F))
					    end
     
      | convert_FormulaN (smartInj, G, D.Exists (D, F)) = 
				(case (smartInj, D, D.whnfF F) of
				  (true, D.NormalDec (_, T as D.LF _), D.Top) => 
                                        (* Since smartInj is on, the name of this dec doesn't matter.. *)
						let
						  val D = D.NormalDec (NONE, T)
						  val D' = D'.NormalDec (rDummy, NONE, convert_Types(true, G, T))
						in
						  D'.Exists (rDummy, D', D'.Top rDummy)
						end				  
				    
				 | (_, _, F') =>
                                            let 
					      val (D, D') = convert_NormalDec (smartInj, G, D)
					    in 
					      D'.Exists (rDummy, D', convert_FormulaN(smartInj, I.Decl(G,D.InstantiableDec D), F'))
					    end
                                )

      | convert_FormulaN (smartInj, G, D.Nabla (D as D.NewDecLF _, F)) = 
                                            let 
					      val (D, D') = convert_NewDec (smartInj, G, D)
					    in 
					      D'.Nabla (rDummy, D', convert_Formula(smartInj, I.Decl(G,D.NonInstantiableDec D), F))
					    end

      | convert_FormulaN (smartInj, G, D.Nabla (D as D.NewDecWorld _, F)) = 
					    (* ignore NewDecWorld as the programmer is not exposed to it.. *)
					      convert_Formula(smartInj, I.Decl(G,D.NonInstantiableDec D), F)

      | convert_FormulaN (smartInj, G, D.FormList _) = D'.OmittedFormula rDummy (* Do not print out ... this is a generalized pair for mutual recursion *)

      | convert_FormulaN (smartInj, G, D.FVar ((_, ref (SOME F), cnstrs), t)) = raise Domain (* It is in whnf *)
      | convert_FormulaN (smartInj, G, D.FClo _) = raise Domain (* It is in whnf *)

      | convert_FormulaN (smartInj, G, D.FVar ((_, r as ref NONE, cnstrs), t)) = D'.OmittedFormula rDummy
					                   (* ADAM NOTE:  When we add polymorphism, 
							    * we will create a new FVar here...
							    * WARNING:  approx.sml converts approx to exact assuming all FVars converted to smae thing
							    *)

					    
    (* convert_..Dec D = (D1, D1') where D1 is D named in internal syntax, and D1' is it in external syntax *)
    and convert_NormalDec (smartInj, G, D) = 
                                   let 
				     val D1 = normalDecName(G, D)
				     val D1' = convertNamed_NormalDec(smartInj, G, D1)
				   in 
				     (D1, D1')
				   end

    and convert_NormalDecs (smartInj, G, []) = ([], [], G)
      | convert_NormalDecs (smartInj, G, (vis, D)::Ds) = 
                   let
		     val vis' = convertVisibility vis
		     val (D, D') = convert_NormalDec (smartInj, G, D)
		     val (resD, resD', G') = convert_NormalDecs (smartInj, I.Decl(G, D.InstantiableDec D), Ds)
		   in
		     ((vis, D) :: resD, (vis', D') :: resD', G')
		   end
		     
			
    (* Precondition:  only called on NewDecLF! *)
    and convert_NewDec (smartInj, G, D as D.NewDecLF _)  = 
                                let 
				  val D1 = newDecName(G, D)
				  val D1' = convertNamed_NewDec(smartInj, G, D1)
				in 
				  (D1, D1')
				end
      | convert_NewDec (smartInj, G, D as D.NewDecWorld _) = raise Domain 			     
     
    (* Precondition:  only called on NewDecLF! *)
    and convertNamed_NewDec (smartInj, G, D.NewDecLF (SOME s, A)) = D'.NewDecLF (rDummy, SOME s, D'.ExplicitLF (Print.formatExp(D.coerceCtx G, A)))
      | convertNamed_NewDec (smartInj, G, D.NewDecWorld (SOME s, W)) = raise Domain (* not available in external syntax *)
      | convertNamed_NewDec _ = raise Domain (* should be named *)
 

    (* Assuming Dec is named in internal syntax, we convert it to external syntax *)
    (* If it is for mutual recursion then we omit printing that *)
    and convertNamed_NormalDec (smartInj, G, D.NormalDec (SOME [s], T)) = D'.NormalDec(rDummy, SOME s, convert_Types(smartInj, G,T))
      | convertNamed_NormalDec (smartInj, G, D.NormalDec (SOME (s::ss), T)) = 
                            let
			      fun strListName [] = "]"
				| strListName (s'::ss') = (", " ^ s')
			      val name = "[" ^ s ^ (strListName ss)
			    in
			      D'.NormalDec(rDummy, SOME name, convert_Types(smartInj, G, T))
			    end

      | convertNamed_NormalDec _ = raise Domain (* not named, but should be by precondition *)
     

   fun lookup (1, I.Decl (G, D.InstantiableDec (D.NormalDec (SOME [s], _)))) =
	       SOME (s)
	       (* if it is a list of names, it should be accessed through Proj *)
     | lookup (1, I.Decl(G, D.NonInstantiableDec (D.NewDecLF (SOME s, _)))) = 
		 SOME (s)
     | lookup (1, I.Decl(G, _)) = NONE (* dec has no useful name *) 
     | lookup (i, I.Decl(G, _)) = if (i > 1) then lookup(i-1, G) else raise Domain
     | lookup _ = raise Domain (* badly typed *) 


   fun getElement(1, E::xs) = SOME E
     | getElement(i, _::xs) = if (i > 1) then getElement(i-1, xs) else raise Domain
     | getElement _ = NONE
     

   fun lookupList (1, j, I.Decl (G, D.InstantiableDec (D.NormalDec (SOME sL, _)))) =
               getElement(j, sL)
     | lookupList (1, j, I.Decl(G, _)) = NONE (* dec has no useful name *) 
     | lookupList (i, j, I.Decl(G, _)) = if (i > 1) then lookupList(i-1, j, G) else raise Domain
     | lookupList _ = raise Domain (* badly typed *)


   fun convFix (smartInj, G, G', D.NormalDec (SOME (s::sL), D.Meta(D.FormList (t::tL))), (E::Elist)) : (Paths.region * D'.NormalDec * D'.Exp) list =
        (* converts fixpoint to external syntax *)
        (* assuming dec is properly named *)
              let
		(* Get first dec *)
		(* val (D, D') = convert_NormalDec (smartInj, G, D.NormalDec (SOME [s], D.Meta(t))) *)
		val D = D.NormalDec (SOME [s], D.Meta(t))
		val D' = convertNamed_NormalDec (smartInj, G, D)
		val _ = Names.mark()   (* I do not think that this scoping of Names is necessary.. but it can't hurt *)
		val E' = convert_Exp(smartInj, false (* not pattern *), G', E)
		val thisFun = (rDummy, D', E')
		val _ = Names.unwind() 
	      in
		thisFun :: (convFix(smartInj, G, G', D.NormalDec (SOME sL, D.Meta(D.FormList tL)), Elist))
	      end

     | convFix (smartInj, _, _, D.NormalDec (SOME [], D.Meta(D.FormList [])), _) = []

     | convFix (smartInj, G, G', D.NormalDec (sLO, D.Meta(F)), Elist) = 
	      convFix(smartInj, G, G', D.NormalDec (sLO, D.Meta(D.FormList [F])), Elist)

	                     

     | convFix _ = raise Domain



   and convCaseBranch' (smartInj, G, D.Eps (D, C, fileInfo)) = 
	                 let 
			   val (D, D') = convert_NormalDec (smartInj, G, D)
			 in 
			   D'.Eps (rDummy, D', convCaseBranch'(smartInj, I.Decl(G,D.InstantiableDec D), C))
			 end
     | convCaseBranch' (smartInj, G, D.NewC (D as D.NewDecLF _, C, fileInfo)) =
	                 let 
			   val (D, D') = convert_NewDec (smartInj, G, D)
			 in 
			   D'.NewC (rDummy, D', convCaseBranch'(smartInj, I.Decl(G,D.NonInstantiableDec D), C))
			 end

     | convCaseBranch' (smartInj, G, D.NewC (D as D.NewDecWorld _, C, fileInfo)) = raise Domain (* impossible.
												 * NewC only over NewDecLF
												 *)

     | convCaseBranch' (smartInj, G, D.PopC (i, C)) =
	                  let
			    val s =  
			      (case (lookup(i,G))
                                  of NONE => "%#" ^ Int.toString(i) ^ "%"
				   | SOME s => varString(G, s, i))
			  in
			    D'.PopC(rDummy, s, convCaseBranch' (smartInj, D.popCtx(i,G), C))
			  end

     | convCaseBranch' (smartInj, G, D.Match (pats, E2)) =
			  let
			    fun convertPat (D'.VarString(r, s)) = D'.PatternString(r, s)
			      | convertPat (D'.Quote(r, A)) = D'.PatternQuote(r, A)
			      | convertPat (D'.Unit r) = D'.PatternUnit r
			      | convertPat (D'.Pair (r, E1, E2)) = D'.PatternPair(r, convertPat E1, convertPat E2)
			      | convertPat (D'.New (r, D, E)) = D'.PatternNew(r, D, convertPat E)
			      | convertPat (D'.Pop (r, s, E)) = D'.PatternPop(r, s, convertPat E)
			      | convertPat (D'.TypeAscribe (r, E, T)) = D'.PatternAscribe (r, convertPat E, T)
			      | convertPat _ = D'.PatternString(rDummy, "BAD_PATTERN_IN_INTERNAL_SYNTAX")


			    fun convertPats [] = []
			      | convertPats ((D.Implicit, E1)::pats) = 
			                  if (!Print.implicit) then
					      convertPat(convert_Exp(smartInj, true (* it is a pattern *), G, E1)) :: (convertPats pats)
					  else
					      convertPats pats

			      | convertPats ((D.Visible, E1)::pats) = convertPat(convert_Exp(smartInj, true (* it is a pattern *), G, E1)) :: (convertPats pats)
			  in
			    D'.Match (false (*not sugar *), rDummy, convertPats(pats), convert_Exp(smartInj, false (* not pattern *), G, E2))
			  end



   and convCaseBranch (smartInj, G, C) = 
	         let
		   val _ = Names.mark() 
		   val result = convCaseBranch' (smartInj, G, C)
		   val _ = Names.unwind()
		 in
		   result
		 end


   and convert_Exp (smartInj, isPattern, G, E) = (convert_ExpW (smartInj, isPattern, G, D.whnfE E)
				       handle D.SubstFailed => raise Domain )


   (* We first handle *special* cases of converting things to "Let" form... *)
   and convert_ExpW (smartInj, isPattern, G, Eorig as D.App(E1, [(D.Visible, fileInfo3, E2)])) =
          (case (D.whnfE E1, D.whnfE E2)
	     of (D.Lam ([D.Eps(_, (D.Match([(D.Visible, D.Var (D.Fixed 1, fileInfo1))], E)), fileInfo1b)], _, fileInfo2),
		 D.Fix (D, Efix)) =>
	                  let 
			    val Elist = (case (D.whnfE Efix)
			                  of (D.ExpList Elist) => Elist
                                           | _ => [Efix])
			    val D1 = normalDecName(G, D)
			    val fix = convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, Elist)
			    val E' = convert_Exp (smartInj, isPattern, I.Decl(G, D.InstantiableDec D1), E)
			  in
			    D'.LetFun (rDummy, fix, E')
			  end

	      | (D.Lam ([D.Eps(D, (D.Match([(D.Visible, D.Var (D.Fixed 1, fileInfo1))], E)), fileInfo1b)], _, fileInfo2),
	         E2) =>
			  let
			    val (D, D') = convert_NormalDec (smartInj, G, D)
			    val E2' = convert_Exp (smartInj, isPattern, G, E2)
			    val E' = convert_Exp (smartInj, isPattern, I.Decl(G, D.InstantiableDec D), E)
			  in
			    case D' of
			      D'.NormalDec(r, SOME s, T) => D'.LetVar(rDummy, D'.PatternAscribe(r, D'.PatternString(r, s), T), E2', E')
			      | _ => raise Domain
			  end
	           
	      | _ => convert_ExpW' (smartInj, isPattern, G, Eorig)
	   )
     | convert_ExpW (smartInj, isPattern, G, E) = convert_ExpW' (smartInj, isPattern, G, E)


   and convert_ExpW' (smartInj, isPattern, G, D.Var (D.Fixed i, fileInfo)) =
              let
		val name =  (case (lookup(i,G))
			       of NONE => ("%#" ^ (Int.toString i) ^ "%") (* variable doesn't have a name *) 
			        | SOME s => varString(G, s, i))

	      in
		case (isPattern, I.ctxLookup(G, i))
		  of (_, D.NonInstantiableDec (D.NewDecLF _)) => (* preferred Delphin syntax is to put this as "<x>" instead osf "x" 
								    * although both are acceptable (when epsilons are explicit) 
								    *)
		                                                 D'.Quote(rDummy, D'.ExplicitLF (Fmt.String name))
		   | (_, D.NonInstantiableDec _) => D'.VarString(rDummy, name)
		   | (_, D.InstantiableDec (D.NormalDec (_, D.Meta _))) => D'.VarString(rDummy, name)
		   | (true, D.InstantiableDec (D.NormalDec (_, D.LF (isP, _)))) =>(case D.whnfP isP
											of D.Param => D'.Quote(rDummy, D'.ExplicitLF (Fmt.String (name ^ "#")))
											 | _ => D'.Quote(rDummy, D'.ExplicitLF (Fmt.String name)))
		   | (_, D.InstantiableDec (D.NormalDec (_, D.LF _))) => D'.Quote(rDummy, D'.ExplicitLF (Fmt.String name))
	      end
		  

     | convert_ExpW' (smartInj, isPattern, G, D.Var B) = D'.VarString(rDummy, "?x(var)?")
			                     (* raise Domain *)
					    (* since it is in whnf, we know it is a variable *)
                                                    

     | convert_ExpW' (smartInj, isPattern, G, D.Quote M) = 
          (let
	    (* We now create a list of indices that we want the LF printer to add "#" to the end of its name.
	     * We want all pattern variables that are parameters to be printed as "x#" instead of "x"
	     * when printing patterns.
	     *)

	    fun getMarks (num, I.Decl(G, D.InstantiableDec (D.NormalDec (_, D.LF (isP, _))))) = 
	           (case D.whnfP isP
		      of D.Param => num :: getMarks(num+1, G)
		       | _ => getMarks(num+1, G)
		    )
	      | getMarks (num, I.Decl(G, _)) = getMarks(num+1, G)
		            (* Note that we do not want NonInstantiableDecs to be printed as "x#" as they are explicitly
			     * created by new and hence do not need this extra information.
			     *)
	      | getMarks (_, I.Null) = [] 
												  
	    val markedList = if isPattern then getMarks (1, G) else []
	    val Mfmt = Print.formatExpMarked(markedList, D.coerceCtx G, M)
	   in
	     D'.Quote(rDummy, D'.ExplicitLF Mfmt)
	   end)


     | convert_ExpW' (smartInj, isPattern, G, D.Unit) = D'.Unit rDummy

     | convert_ExpW' (smartInj, isPattern, G, D.Lam (Clist, F, fileInfo)) = 
	     D'.Lam (rDummy, map (fn C => convCaseBranch(smartInj, G, C)) Clist)



     | convert_ExpW' (smartInj, isPattern, G, D.New (D as D.NewDecLF _, E, fileInfo)) = 
          let 
	    val (D, D') = convert_NewDec (smartInj, G, D)
	  in 
	    D'.New (rDummy, D', convert_Exp(smartInj, isPattern, I.Decl(G,D.NonInstantiableDec D), E))
	  end

     | convert_ExpW' (smartInj, isPattern, G, D.New (D as D.NewDecWorld _, E, fileInfo)) = 
	  (* ignore NewDecWorld as the programmer is not exposed to it.. *)
	  convert_Exp(smartInj, isPattern, I.Decl(G,D.NonInstantiableDec D), E)


     | convert_ExpW' (smartInj, isPattern, G, D.App (E1, args)) =
	     let
	       fun convertArgs [] = []
		 | convertArgs ((D.Visible, fileInfo, E2)::args) = convert_Exp(smartInj, isPattern, G, E2) :: (convertArgs args)
		 | convertArgs ((D.Implicit, fileInfo, E2)::args) = 
			                  if (!Print.implicit) then
					      convert_Exp(smartInj, isPattern, G, E2) :: (convertArgs args)
					  else
					      (convertArgs args)
	     in
	       case (convertArgs args)
		 of [] => convert_Exp(smartInj, isPattern, G, E1)
		  | args' => D'.App(rDummy, convert_Exp(smartInj, isPattern, G, E1), args')
	     end

     | convert_ExpW' (smartInj, isPattern, G, D.Pair(E1, E2, _)) = (case (smartInj, D.whnfE E1, D.whnfE E2)
						      of (true, D.Quote M, D.Unit) => convert_ExpW' (smartInj, isPattern, G, D.Quote M)
						       | (true, D.Var(D.Fixed n, fileInfo), D.Unit) => 
								    let
								      val isLF = case I.ctxLookup(G, n)
									         of D.InstantiableDec (D.NormalDec(_, D.LF _)) => true
										  | D.NonInstantiableDec (D.NewDecLF _) => true
										  | _ => false
								    in
								      if isLF then
									convert_ExpW' (smartInj, isPattern, G, D.Quote (I.Root(I.BVar (I.Fixed n), I.Nil)))
								      else
									D'.Pair (rDummy, convert_Exp(smartInj, isPattern, G, E1), convert_Exp(smartInj, isPattern, G, E2))
								    end
									
						       | _ => D'.Pair (rDummy, convert_Exp(smartInj, isPattern, G, E1), convert_Exp(smartInj, isPattern, G, E2)))


     | convert_ExpW' (smartInj, isPattern, G, D.ExpList Elist) = raise Domain (* We cannot print this out currently..., typically should be under
							* projection which is handled below *)

     | convert_ExpW' (smartInj, isPattern, G, D.Proj (E1, j)) = 
	  (* this projection is for mutual recursion...*)
	  ((case (D.whnfE E1) of

              (D.Fix (D, E)) => (* get jth element of list *)
	                         (* We will convert this to
				  * let fun f1 and fun fn....
                                  *  in fi end 
				 *)
	                          let
				    val Elist = case D.whnfE E
				                of D.ExpList Elist => Elist
						 | _ => raise Domain

				    val D1 = normalDecName(G, D)
				    val sL = case D1 of
				             (D.NormalDec (SOME sL, _)) => sL
					     | _ => raise Domain (* we just named the dec *)
				    val s = case getElement(j, sL)
				            of NONE => raise Domain (* Bad projection *)
					     | SOME s => s
				    val fix = convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, Elist)
				  in
				    D'.LetFun (rDummy, fix, D'.VarString(rDummy, s))
				  end

	   | (D.ExpList Elist) =>  (case getElement(j, Elist)
				            of NONE => raise Domain
					     | SOME E => convert_Exp(smartInj, isPattern, G, E))

				    
           | (D.Var (D.Fixed i, fileInfo)) => (case (lookupList(i, j, G)) of
				  SOME s => D'.VarString (rDummy, varString(G, s, i))
				  | NONE => D'.VarString (rDummy, "Proj(" ^ (Int.toString i) ^"," ^ (Int.toString j) ^ ")"))


	   | E => raise Domain (* cannot print this out... *)
				  
	   ) handle D.SubstFailed => raise Domain)


     | convert_ExpW' (smartInj, isPattern, G, D.Pop (i, E, fileInfo)) = 
	                  let
			    val s =  
			      (case (lookup(i,G))
                                  of NONE => "%#" ^ Int.toString(i) ^ "%"
				   | SOME s => varString(G, s, i))
			  in
			    case (I.ctxLookup (G, i))
			      of (D.NonInstantiableDec (D.NewDecWorld _)) => (* do not print out
										* pop  for world..
										*)
				                                               convert_Exp (smartInj, isPattern, D.popCtx(i,G), E)

			       | _ => D'.Pop(rDummy, s, convert_Exp (smartInj, isPattern, D.popCtx(i,G), E))
			  end

     | convert_ExpW' (smartInj, isPattern, G, D.Fix (D, D.ExpList Elist)) = 
	                          let 
				    val D1 = normalDecName(G, D)
				  in
				    D'.Fix(rDummy, convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, Elist))
				  end

     | convert_ExpW' (smartInj, isPattern, G, D.Fix (D, Efix)) = 
	                          let 
				    val D1 = normalDecName(G, D)
				  in
				    D'.Fix(rDummy, convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, [Efix]))
				  end


     | convert_ExpW' (smartInj, isPattern, G, D.EVar ((r (* ref NONE *),F), t)) = 
				  D'.VarString(rDummy, getEVar(G, r)) (* Note: we ignore printing the substitution here *)

     | convert_ExpW' (smartInj, isPattern, G, D.EClo _) = raise Domain (* not in whnf *)


    fun expToString (G, E, smartInj, isDetailed, printEps) = (varReset G ; Fmt.makestring_fmt(DP.ExpToFormat0(convert_Exp(smartInj, false (* not pattern *), G, E), DP.baseK, isDetailed, printEps)))

     (* G |- E as D.Fix _ 
      * and it is the toplevel, so we do not want to rename the dec
      *)
    fun topFixToString (G, E, smartInj, isDetailed, printEps) = 
      ( case (D.whnfE E)
	  of D.Fix (D, D.ExpList Elist) => let
	                                     val _ = varReset G
					     val C' = D'.Fix(rDummy, convFix (smartInj, G, I.Decl(G, D.InstantiableDec D), D, Elist))
					  in
					    Fmt.makestring_fmt(DP.ExpToFormat0(C', DP.baseK, isDetailed, printEps))
					  end
	   | D.Fix (D, Efix) => let
				 val _ = varReset G
				 val C' = D'.Fix(rDummy, convFix (smartInj, G, I.Decl(G, D.InstantiableDec D), D, [Efix]))
			       in
				 Fmt.makestring_fmt(DP.ExpToFormat0(C', DP.baseK, isDetailed, printEps))
			       end
   	   | _ => raise Domain
      )


    (* User should name the context (using ctxName) before converting to string... *)
    fun typeToString (G, T, smartInj) = (varReset G ; Fmt.makestring_fmt(DP.TypesToFormat0(convert_Types(smartInj, G, T), DP.baseK)))
    fun formToString (G, F, smartInj) = (varReset G ; Fmt.makestring_fmt(DP.FormulaToFormat0(convert_Formula(smartInj, G, F), DP.baseK)))
    fun expToFormat (G, E, smartInj, isDetailed, printEps) = (varReset G ; (DP.ExpToFormat0(convert_Exp(smartInj, false (* not pattern *), G, E), DP.baseK, isDetailed, printEps)))

    fun normalDecToString(G, D, smartInj) = 
                  let
		    val _ = varReset G ; 
		    val (D, D') = convert_NormalDec (smartInj, G, D)
		    val fmt = DP.NormalDecToFormat D'
		  in 
		    Fmt.makestring_fmt fmt
		  end

    (* ctxName G = G'
       
        Invariant:
	|- G == G' ctx
	where some Declaration in G' have been named/renamed
    *)
    fun ctxName (I.Null) = I.Null
      | ctxName (I.Decl (G, D.InstantiableDec D)) = 
        let
	  val G' = ctxName G
	in
	  I.Decl (G', D.InstantiableDec (normalDecName (G', D)))
	end
      | ctxName (I.Decl (G, D.NonInstantiableDec (D as D.NewDecLF _))) =
	let
	  val G' = ctxName G
	in
	  I.Decl (G', D.NonInstantiableDec (newDecName (G', D)))
	end

      | ctxName (I.Decl (G, D.NonInstantiableDec (D as D.NewDecWorld _))) =
	  (* no need to name these as they do not occur in expressions, 
	   * since they are eliminate with var instead of pop.
	   *)
	let
	  val G' = ctxName G
	in
	  I.Decl (G', D.NonInstantiableDec D)
	end
		    
					     

  end

