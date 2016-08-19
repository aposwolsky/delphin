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
     
    fun LFformatExp(G, U) = Print.formatExp(D.coerceCtx G, U)
(* EVars are now NDec free.. so we do not need to strengthen them away...
    fun LFformatExp(G, U) =
        let
	  val G' = D.coerceCtx G
	  val (G0, t) = D.strengthen G'
	     (* G0 |- t : G'  and G0 is NDec free *)
	in
	  Print.formatExp(G0, I.EClo(U, t))
	end
*)

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
      | ctxDefined (I.Decl(G, D.NonInstantiableDec (D.NewDecMeta (SOME s, _))), name) =
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

      | firstOccurrence (I.Decl(G, D.NonInstantiableDec (D.NewDecMeta (SOME s, _))), name, k) =
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
    fun getNamesFromType (G, D.LF(_, A)) = 
		 (case (Names.decName (D.coerceCtx G, I.Dec (NONE, A))) 
		 of (I.Dec (SOME s, A)) => [s]
                  | _ => raise Domain)
      (* Enhancement:  If it is just a pair with top, then get name based on first part *)
      | getNamesFromType (G, D.Meta(_, D.Exists(D.NormalDec(_, D.LF(_, A)), D.Top))) =
		 (case (Names.decName (D.coerceCtx G, I.Dec (NONE, A))) 
		 of (I.Dec (SOME s, A)) => [s]
                  | _ => raise Domain)
      | getNamesFromType (G, D.Meta(_, D.FormList Flist)) =
		    let
		      fun getOneName F = (case getNamesFromType(G, D.Meta(D.Existential, F))
					    of [s] => s
					     | _ => raise Domain (* formula can't have more than one name *)
					  )
		    in
		      (map getOneName Flist)
		    end

      | getNamesFromType (G, _) = ["u"] (* these variables may undergo renaming by newDecName or normalDecName *)
		    

    fun normalDecName (G, D as D.NormalDec (SOME [], T)) = D.NormalDec (NONE, T) (* shouldn't ever occur *)
      | normalDecName (G, D as D.NormalDec (SOME sL, T)) = 
                      let
			fun nameList (l, []) = l
			  | nameList (l, (name::ss)) = 
			      let val name' = if varDefined name orelse ctxDefined(G,name) orelse nameInList(name, l)
						then getNextName'(l, G, baseOf name)
					      else name
			      in
				nameList(l@[name], ss)
			      end
		      in
			D.NormalDec (SOME (nameList([], sL)), T)
		      end			  
			             
                        
      | normalDecName (G, D.NormalDec (NONE, T)) =
			normalDecName (G, D.NormalDec (SOME (getNamesFromType(G, T)), T))






    fun newDecName (G, D as D.NewDecLF (SOME name, A)) = 
                        if varDefined name orelse ctxDefined(G, name)
			  then D.NewDecLF(SOME (getNextName(G, baseOf name)), A)
			else D

      | newDecName (G, D as D.NewDecMeta (SOME name, T)) =
                        if varDefined name orelse ctxDefined(G, name)
			  then D.NewDecMeta(SOME (getNextName(G, baseOf name)), T)
			else D

      | newDecName (G, D as D.NewDecLF (NONE, A)) =
			  let
			    val s = (case (getNamesFromType(G, D.LF(D.Existential, A)))
				       of [s] => s
					| _ => raise Domain 
			             )
			  in
			    newDecName (G, D.NewDecLF (SOME s, A))
			  end

      | newDecName (G, D as D.NewDecMeta (NONE, T)) =
			  let
			    val s = (case (getNamesFromType(G, D.Meta(D.Existential, T)))
				       of [s] => s
					| _ => raise Domain 
			             )
			  in
			    newDecName (G, D.NewDecMeta (SOME s, T))
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

    and convert_Types' (smartInj, G, D.LF (isP, A)) = D'.LF(rDummy, convert_isParam isP, D'.ExplicitLFType (LFformatExp(G, A)))
      | convert_Types' (smartInj, G, D.Meta (isP, F)) = D'.Meta(rDummy, convert_isParam isP, convert_Formula (smartInj, G,F))

    and convert_Formula (smartInj, G, F) = 
         let
	   val _ = Names.mark()
	   val F' = convert_FormulaN (smartInj, G, D.whnfF F)
	   val _ = Names.unwind()
	 in
	   F'
	 end

    and convertVisibility (D.Visible) = D'.Visible
      | convertVisibility (D.Implicit) = D'.Implicit

    and convert_FormulaN (smartInj, G, D.Top) = D'.Top rDummy

      | convert_FormulaN (smartInj, G, D.All (visible, D, F)) = 
                                            let 
					      val (D, D') = convert_NormalDec (smartInj, G, D)
					    in 
					      D'.All (rDummy, convertVisibility visible, D', convert_Formula(smartInj, I.Decl(G,D.InstantiableDec D), F))
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

      | convert_FormulaN (smartInj, G, D.Nabla (D, F)) = 
                                            let 
					      val (D, D') = convert_NewDec (smartInj, G, D)
					    in 
					      D'.Nabla (rDummy, D', convert_Formula(smartInj, I.Decl(G,D.NonInstantiableDec D), F))
					    end

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
				       
    and convert_NewDec (smartInj, G, D)  = 
                                let 
				  val D1 = newDecName(G, D)
				  val D1' = convertNamed_NewDec(smartInj, G, D1)
				in 
				  (D1, D1')
				end
      

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
     
    and convertNamed_NewDec (smartInj, G, D.NewDecLF (SOME s, A)) = D'.NewDecLF (rDummy, SOME s, D'.ExplicitLFType (LFformatExp(G, A)))
      | convertNamed_NewDec (smartInj, G, D.NewDecMeta (SOME s, F)) = D'.NewDecMeta(rDummy, SOME s, convert_Formula(smartInj, G, F))
      | convertNamed_NewDec _ = raise Domain (* should be named *)


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



   fun convFix (smartInj, G, G', D.NormalDec (SOME (s::sL), D.Meta(D.Existential, D.FormList (t::tL))), (E::Elist)) : (Paths.region * D'.NormalDec * D'.Exp) list =
        (* converts fixpoint to external syntax *)
        (* assuming dec is properly named *)
              let
		(* Get first dec *)
		val (D, D') = convert_NormalDec (smartInj, G, D.NormalDec (SOME [s], D.Meta(D.Existential, t)))
		val _ = Names.mark()   (* I do not think that this scoping of Names is necessary.. but it can't hurt *)
		val E' = convert_Exp(smartInj, G', E)
		val thisFun = (rDummy, D', E')
		val _ = Names.unwind() 
	      in
		thisFun :: (convFix(smartInj, G, G', D.NormalDec (SOME sL, D.Meta(D.Existential, D.FormList tL)), Elist))
	      end

     | convFix (smartInj, _, _, D.NormalDec (SOME [], D.Meta(D.Existential, D.FormList [])), _) = []

     | convFix (smartInj, G, G', D.NormalDec (sLO, D.Meta(D.Existential, F)), Elist) = 
                                                      (* fixpoint should be FORCED to be D.FormList, but just in case.. *)
	      convFix(smartInj, G, G', D.NormalDec (sLO, D.Meta(D.Existential, D.FormList [F])), Elist)

	                     

     | convFix _ = raise Domain


   and convert_Exp (smartInj, G, E) = (convert_ExpW (smartInj, G, D.whnfE E)
				       handle D.SubstFailed => raise Domain )
   and convert_ExpW (smartInj, G, D.Var (D.Fixed i)) =
                           (case (lookup(i,G))
                                  of NONE => D'.VarInt (rDummy, i) (* variable doesn't have a name *)
				   | SOME s => D'.VarString(rDummy, varString(G, s, i)))

     | convert_ExpW (smartInj, G, D.Var B) = D'.VarString(rDummy, "???")
			                     (* raise Domain *)
					    (* since it is in whnf, we know it is a variable *)
                                                    
     | convert_ExpW (smartInj, G, D.Quote M) = D'.Quote(rDummy, D'.ExplicitLFTerm (LFformatExp(G, M)))

     | convert_ExpW (smartInj, G, D.Unit) = D'.Unit rDummy

     | convert_ExpW (smartInj, G, D.Lam (Clist, F)) = 
           let
	     fun convCaseBranch' (G, D.Eps (D, C)) = 
	                 let 
			   val (D, D') = convert_NormalDec (smartInj, G, D)
			 in 
			   D'.Eps (rDummy, D', convCaseBranch'(I.Decl(G,D.InstantiableDec D), C))
			 end
	       | convCaseBranch' (G, D.NewC (D, C)) =
	                 let 
			   val (D, D') = convert_NewDec (smartInj, G, D)
			 in 
			   D'.NewC (rDummy, D', convCaseBranch'(I.Decl(G,D.NonInstantiableDec D), C))
			 end

	       | convCaseBranch' (G, D.PopC (i, C)) =
	                  let
			    val s =  
			      (case (lookup(i,G))
                                  of NONE => "%#" ^ Int.toString(i) ^ "%"
				   | SOME s => varString(G, s, i))
			  in
			    D'.PopC(rDummy, s, convCaseBranch' (D.popCtx(i,G), C))
			  end


	       | convCaseBranch' (G, D.Match (E1, E2)) =
			 D'.Match (rDummy, convert_Exp(smartInj, G, E1), convert_Exp(smartInj, G, E2))

	       | convCaseBranch' (G, D.MatchAnd (D.Implicit, E1, C)) = convCaseBranch'(G, C)
	       | convCaseBranch' (G, D.MatchAnd (D.Visible, E1, C)) = D'.MatchAnd (rDummy, convert_Exp(smartInj, G, E1), convCaseBranch'(G, C))

	     fun convCaseBranch (G, C) = 
	         let
		   val _ = Names.mark() 
		   val result = convCaseBranch' (G, C)
		   val _ = Names.unwind()
		 in
		   result
		 end

	   in
	     D'.Lam (rDummy, map (fn C => convCaseBranch(G, C)) Clist)
	   end



     | convert_ExpW (smartInj, G, D.New (D, E)) = 
          let 
	    val (D, D') = convert_NewDec (smartInj, G, D)
	  in 
	    D'.New (rDummy, D', convert_Exp(smartInj, I.Decl(G,D.NonInstantiableDec D), E))
	  end

     | convert_ExpW (smartInj, G, D.App (D.Visible, D.Lam ([D.Eps(_, (D.Match(D.Var (D.Fixed 1), E)))], _), D.Fix (D, D.ExpList Elist))) =
	  let 
	    val D1 = normalDecName(G, D)
	    val fix = convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, Elist)
	    val E' = convert_Exp (smartInj, I.Decl(G, D.InstantiableDec D1), E)
	  in
	    D'.LetFun (rDummy, fix, E')
	  end

     | convert_ExpW (smartInj, G, D.App (D.Visible, D.Lam ([D.Eps(_, (D.Match(D.Var (D.Fixed 1), E)))], _), D.Fix (D, Efix))) =
	  let 
	    val D1 = normalDecName(G, D)
	    val fix = convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, [Efix])
	    val E' = convert_Exp (smartInj, I.Decl(G, D.InstantiableDec D1), E)
	  in
	    D'.LetFun (rDummy, fix, E')
	  end
	  
     | convert_ExpW (smartInj, G, D.App (D.Visible, D.Lam ([D.Eps(D, (D.Match(D.Var (D.Fixed 1), E)))], _), E2)) = 
	  let
	    val (D, D') = convert_NormalDec (smartInj, G, D)
	    val E2' = convert_Exp (smartInj, G, E2)
	    val E' = convert_Exp (smartInj, I.Decl(G, D.InstantiableDec D), E)
	  in
	    (* OLD-- D'.LetVar(rDummy, D', E2', E') *)
	    case D' of
	      D'.NormalDec(r, SOME s, T) => D'.LetVar(rDummy, D'.TypeAscribe(r, D'.VarString(r, s), T), E2', E')
              | _ => raise Domain
	  end

	    
     | convert_ExpW (smartInj, G, D.App (D.Visible, E1, E2)) = D'.App (rDummy, convert_Exp(smartInj, G, E1), convert_Exp(smartInj, G, E2))
     | convert_ExpW (smartInj, G, D.App (D.Implicit, E1, E2)) = convert_Exp(smartInj, G, E1)


     | convert_ExpW (true, G, D.Pair(D.Quote M, D.Unit, _)) = D'.Quote(rDummy, D'.ExplicitLFTerm (LFformatExp(G, M)))

     | convert_ExpW (smartInj, G, D.Pair (E1, E2, _)) = D'.Pair (rDummy, convert_Exp(smartInj, G, E1), convert_Exp(smartInj, G, E2))

     | convert_ExpW (smartInj, G, D.ExpList Elist) = raise Domain (* We cannot print this out currently..., typically should be under
							* projection which is handled below *)

     | convert_ExpW (smartInj, G, D.Proj (E1, j)) = 
	  (* this projection is for mutual recursion...*)
	  ((case (D.whnfE E1) of
            (D.Fix (D, D.ExpList Elist)) => (* get jth element of list *)
	                         (* We will convert this to
				  * let fun f1 and fun fn....
                                  *  in fi end 
				 *)
	                          let 
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
					     | SOME E => convert_Exp(smartInj, G, E))

				    
           | (D.Var (D.Fixed i)) => (case (lookupList(i, j, G)) of
				  SOME s => D'.VarString (rDummy, varString(G, s, i))
				  | NONE => D'.VarString (rDummy, "Proj(" ^ (Int.toString i) ^"," ^ (Int.toString j) ^ ")"))


	   | _ => raise Domain (* cannot print this out... *)
				  
	   ) handle D.SubstFailed => raise Domain)

     | convert_ExpW (smartInj, G, D.Pop (i, E)) = 
	                  let
			    val s =  
			      (case (lookup(i,G))
                                  of NONE => "%#" ^ Int.toString(i) ^ "%"
				   | SOME s => varString(G, s, i))
			  in
			    D'.Pop(rDummy, s, convert_Exp (smartInj, D.popCtx(i,G), E))
			  end

     | convert_ExpW (smartInj, G, D.Fix (D, D.ExpList Elist)) = 
	                          let 
				    val D1 = normalDecName(G, D)
				  in
				    D'.Fix(rDummy, convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, Elist))
				  end

     | convert_ExpW (smartInj, G, D.Fix (D, Efix)) = 
	                          let 
				    val D1 = normalDecName(G, D)
				  in
				    D'.Fix(rDummy, convFix (smartInj, G, I.Decl(G, D.InstantiableDec D1),D1, [Efix]))
				  end

     | convert_ExpW (smartInj, G, D.EVar (r (* ref NONE *), t)) = 
				  D'.VarString(rDummy, getEVar(G, r)) (* Note: we ignore printing the substitution here *)

     | convert_ExpW (smartInj, G, D.EClo _) = raise Domain (* not in whnf *)


    fun expToString (G, E, smartInj, isDetailed) = (varReset G ; Fmt.makestring_fmt(DP.ExpToFormat0(convert_Exp(smartInj, G, E), DP.baseK, isDetailed)))
    fun typeToString (G, T, smartInj) = (varReset G ; Fmt.makestring_fmt(DP.TypesToFormat0(convert_Types(smartInj, G, T), DP.baseK)))

    fun formToString (G, F, smartInj) = (varReset G ; Fmt.makestring_fmt(DP.FormulaToFormat0(convert_Formula(smartInj, G, F), DP.baseK)))

    fun expToFormat (G, E, smartInj, isDetailed) = (varReset G ; (DP.ExpToFormat0(convert_Exp(smartInj, G, E), DP.baseK, isDetailed)))

    fun normalDecToString(G, D, smartInj) = 
                  let
		    val _ = varReset G ; 
		    val (D, D') = convert_NormalDec (smartInj, G, D)
		    val fmt = DP.NormalDecToFormat D'
		  in 
		    Fmt.makestring_fmt fmt
		  end
		    
					     

  end

