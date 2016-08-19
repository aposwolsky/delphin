(* Delphin Elaborator (convert from external to internal syntax) *)
(* Author: Adam Poswolsky *)

structure DelphinElab : DELPHIN_ELABORATOR =
  struct
    exception Error of string
    structure D = DelphinExtSyntax  (* What we are converting from *)
    structure DI = DelphinIntermediateSyntax  (* External Syntax with LF-level filled in *)
    structure DA = DelphinApprox (* Approximate types for Delphin Types *)
    structure D' = DelphinIntSyntax (* What we are converting too *)
    structure I = IntSyn
    structure L = Lexer
    structure LS = Stream
    structure U = UnifyDelphinNoTrail
    val filename = ref "stdIn"
    val globalWorld = ref (D'.Anything)
    val metaSigRef = ref (ref (nil : (string * DA.Formula * D'.Formula) list))  (* for type aliasing *) 
    val nextFreshVar = ref 1 (* Used in conversion of lifted App..*)

    val enableCoverage = ref true (* linked to "enableCoverage" in delphin.fun! *)
                                  (* not affected by reset.. *)


    fun getFreshName () =
      let
	(* Here we create a fresh variable which is guaranteed not to be used.
	 * as "@" is forbidden as an identifier, we simply create vars as "@N"
	 *)
	val i = !nextFreshVar
	val _ = nextFreshVar := i+1
      in
	"@" ^ Int.toString(i)
      end

      
    structure StringTree = StringRedBlackTree
    val patvarApxTable : (string * DA.Formula) StringTree.Table = StringTree.new (0)
    val patvarExactTable : (int*D'.Formula) StringTree.Table = StringTree.new (0) (* int refers to number of variables in context *)
    val patVarCtx : (D'.Dec I.Ctx) ref = ref I.Null

    fun saveApxTables () = StringTree.save patvarApxTable
    fun restoreApxTables (patvarApxT) = StringTree.restore (patvarApxTable, patvarApxT)

    fun saveExactTables () = (!patVarCtx, StringTree.save patvarExactTable)
    fun restoreExactTables (ctx, patvarExactT) = (patVarCtx := ctx ;
						  StringTree.restore (patvarExactTable, patvarExactT))


    fun addPatVarApx (r, name, isUnique ) =
         let
	   val F = DA.FVar (r, ref NONE)
		  
	   (* we may need to rename the Pattern Variable so it doesn't conflict with variables in the context 
	    * or older pattern variables.
	    *)
	   val name' = if isUnique then name else getFreshName()
	 in
	   (* WARNING:  Note that we may be inserting something into the table
	    * with a key that already exists... It should be overriden with this new value,
	    * which is at least the case for StringTree..
	    *)
	   StringTree.insert patvarApxTable (name, (name', F));
	   (DI.PatVar (r, name', name), DA.Meta(r, F))
	 end

    fun getPatVarApx (r, name) =
        (case StringTree.lookup patvarApxTable name
           of SOME (name', F) => (DI.PatVar (r, name', name), DA.Meta(r, F))
            | NONE => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ name ^ " not found!")))

	   

    fun getPatVarFormExact (name) =
      (* For now we just assume the patvar makes sense in the empty context to
       * be consistent with LF
       *)
        (case StringTree.lookup patvarExactTable name
           of SOME (n,F) => (n,F)
            | NONE =>
              let
                val F = D'.newFVar (D'.coerceCtx (!patVarCtx))
		val n = I.ctxLength (!patVarCtx)
              in
                StringTree.insert patvarExactTable (name, (n,F));
                (n,F)
              end)
     
    fun saveData() = (!globalWorld, !filename, 
		      !nextFreshVar,
		      StringTree.save patvarApxTable,
		      StringTree.save patvarExactTable,
		      !patVarCtx)

    fun restoreData(world, file, num, patvarA, patvarE, patvarC) =
                   (globalWorld := world;
		    filename := file ;
		    nextFreshVar := num ;
		    StringTree.restore (patvarApxTable, patvarA) ;
		    StringTree.restore (patvarExactTable, patvarE) ;
		    patVarCtx := patvarC
		    )
		    
    type metaSignature = (string * DelphinApprox.Formula * DelphinIntSyntax.Formula) list

    fun reset(metaSig) = (globalWorld := D'.Anything
			  ; filename := "stdIn" ; nextFreshVar := 1
			  ; StringTree.clear patvarApxTable 
			  ; StringTree.clear patvarExactTable
			  ; patVarCtx := I.Null
			  ; metaSigRef := metaSig)

    fun setFilename(s) = filename := s
    fun setWorld(W) = globalWorld := W
    fun getFilename() = !filename
    fun getWorld() = !globalWorld

    fun typeStr(smartInj, G, T) = (PrintDelphinInt.typeToString(PrintDelphinInt.ctxName G, T, smartInj)
				   handle _ => "*not printable*") (* no reason to crash instead *)


    fun unifyTypes(smartInj, r, s, G, Tdesired, Tactual) =
      let
	fun errorMsg(G, Tdesired, Tactual) =
	  let
	    val firstLine =  "   Expected Type: " ^ typeStr(smartInj, G, Tdesired) 
	    val secondLine = "   Actual   Type: " ^ typeStr(smartInj, G, Tactual)
	  in
	    "\n" ^ firstLine ^ "\n" ^ secondLine ^ "\n"
	  end
	
      in
	(U.unifyT(I.Null, D'.coerceCtx G, Tdesired, Tactual)
	 handle U.Error msg => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), s ^ ": " ^ msg ^ errorMsg(G, Tdesired, Tactual))))
      end
      
    fun unifyApxTypes(smartInj, r, s, Tdesired, Tactual) =
      let
	fun createDetailedMessage() =
	  let
	    val firstLine =  "   Expected Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tdesired))
	    val secondLine = "   Actual   Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tactual))
	  in
	    "\n" ^ firstLine ^ "\n" ^ secondLine ^ "\n"
	  end
      in
	DA.unifyTypes (Tdesired, Tactual)
	       handle DA.ApproxUnify msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), s ^ ": " ^ msg ^ (createDetailedMessage ())))
      end

    fun strOpt2strListOpt NONE = NONE
      | strOpt2strListOpt (SOME s) = SOME [s]


    fun createConstraintsMsg [] = ""
      | createConstraintsMsg ((r, cnstrs) :: cnstrRegL) = 
              let
		val msg = Paths.wrapLoc(Paths.Loc (!filename, r), "Typing ambiguous -- unresolved constraints\n" ^ Print.cnstrsToString cnstrs)
	      in
		msg ^ "\n" ^ (createConstraintsMsg cnstrRegL)
	      end

   (* checkEOF f = r 
       
      Invariant:
      If   f is the end of stream
      then r is a region
	 
      Side effect: May raise Error
    *)   
    fun checkEOF (LS.Cons ((L.EOF, r), s')) = r 
      | checkEOF (LS.Cons ((t, r), _))  = 
          raise Error  (Paths.wrapLoc(Paths.Loc (!filename,r),"Unexpected:  Found " ^ L.toString t ^ ".")) 
      | checkEOF _ = raise Domain

    fun getRegion (LS.Cons ((_, r), _)) = r
      | getRegion _ = raise Domain

    fun tokensToTerm (tokenList) = 
        let 
	  val f = LS.expose (LS.fromList(tokenList))

	  val (t, f') = ParseTerm.parseTerm' f
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc 
					(!filename,getRegion(f)),("LF Parse Error:  " ^ s))) 
	  val r2 = checkEOF f'
        in
	  t
        end


    (* Not used anymore as we allow pattern variables to be upper or lowercase
    fun isCap s =
      let
	val c = case (String.explode(s)) 
	        of (c::xs) => c
		 | _ => raise Domain
      in
	Char.isUpper(c) orelse c = #"@" (* generated by lifted app *)
      end
    *)
      

    (* PRELIMINARY Functions to lookup into a D'.Dec I.Ctx *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   fun findIndex(s, [], n) = NONE
     | findIndex(s:string, (s'::sL), n) = if (s=s') then (SOME n) else findIndex(s, sL, n+1)

   fun getIndex (i, D'.Meta(F)) = getIndexN (i, D'.whnfF F)
     | getIndex _ = raise Domain

   and getIndexN (1, D'.FormList (F::_)) = D'.Meta(F)

     | getIndexN (i, D'.FormList (_::fList)) = getIndexN(i-1, D'.FormList fList)

     | getIndexN _ = raise Domain (* fixpoint not constructed properly if it is a projection without an appropriate list of formulas *)


   datatype lookupResult
     = NoMatch
     | SuccessMatch of DI.Exp * DA.Types
     | PatternVariable of DA.Types



   (* G |- Nab{W}T wff  ==> T
     * (also generalized for mutually recursive fixpoints which have 
     *  the form FormList [Nab{W}T1, ... Nab{W}Tn])
     * such that G |- T wff.
     * else
     * T ==> T
     *)
   fun removeCoverageInfo (T as D'.LF _) = T
     | removeCoverageInfo (T as D'.Meta F) = 
            (case (D'.whnfF F)
	       of (D'.Nabla(D'.NewDecWorld (_, W), F)) => 
		      (* We could also use "applyInv2Formula" but that would be slower...! *)
		      (D'.Meta (D'.FClo(F, I.invShift)))

		| (D'.FormList (Flist as (F2 :: _))) =>
		    (case D'.whnfF F2
		       of (D'.Nabla(D'.NewDecWorld (_, W), _)) => 
			    let
			      fun removeWorld F =
				  (case D'.whnfF F
				     of (D'.Nabla(D'.NewDecWorld _, F')) => D'.FClo(F', I.invShift)
				      | _ => raise Domain (* badly formed fixpoint...*)
				   )

			      val Flist' = map removeWorld Flist
			    in
			      (D'.Meta (D'.FormList Flist'))
			    end
			| _ => (T))
	        | _ => (T)
             )


   fun removeCoverageInfoApx (T as DA.Meta (r,F)) = 
           (case (DA.whnfF F)
	      of (DA.Nabla(_, DA.NewDecWorld _, F')) => DA.Meta (r, F')
	       | (DA.FormList (Flist as (F2 :: _))) =>
		    (case DA.whnfF F2
		       of (DA.Nabla(_, DA.NewDecWorld _, _)) => 
			    let
			      fun removeWorld F =
				  (case DA.whnfF F
				     of (DA.Nabla(_, DA.NewDecWorld _, F')) => F'
				      | _ => raise Domain (* badly formed fixpoint...*)
				   )

			      val Flist' = map removeWorld Flist
			    in
			      (DA.Meta (r, DA.FormList Flist'))
			    end
			| _ => T)
	       | _ => T
           )
     | removeCoverageInfoApx T = T



   fun lookupApxString (r, I.Null, s, k) = NoMatch
     | lookupApxString (r, I.Decl(G, (DA.InstantiableDec (_, DA.NormalDec (_, sLO, T0)))), s, k) = 
                   let
		     fun getIndex (1, DA.Meta(r, DA.FormList (F::_))) = DA.Meta(r, F)
		       | getIndex (i, DA.Meta(r, DA.FormList (_::fList))) = 
		               getIndex(i-1, DA.Meta(r, DA.FormList fList))
		       | getIndex _ = raise Domain

		     fun checkApxVar(s, NONE, T) = NONE
		       | checkApxVar(s : string, SOME [s'], T) = if (s=s') then (SOME (DI.VarInt (r, k), T)) else NONE
		       | checkApxVar(s, SOME sL, T) = (case (findIndex(s, sL, 1))
							    of NONE => NONE
							  | SOME n => SOME(DI.Proj(r, DI.VarInt (r, k), n), getIndex (n, T)))

		   in
		     (case checkApxVar(s, sLO, T0)
			of NONE => lookupApxString(r, G, s, k+1)
		      | SOME Tapx => SuccessMatch Tapx
	             )
		   end

     | lookupApxString (r, I.Decl(G, (DA.NonInstantiableDec (_, DA.NewDecLF (r2, SOME s', A)))), s, k) = 
					  if (s=s') then 
					    SuccessMatch (DI.VarInt (r, k), DA.LF(r2, D'.Param, A))
					  else
					    lookupApxString(r, G, s, k+1)
				
     | lookupApxString (r, I.Decl(G, (DA.NonInstantiableDec (_, DA.NewDecWorld (r2, SOME s', W)))), s, k) = 
					 (* UPDATE:  Even if it has a name, we will NEVER want to access it here... 
					 if (s=s') then 
					   SuccessMatch (DI.VarInt (r, k), DA.Meta(r2, F))
					 else
					   *)
					   lookupApxString(r, G, s, k+1)

     | lookupApxString (r, I.Decl(G, DA.PatternVariable (s', T)), s, k) = 
					   if (s =s') then
					     PatternVariable T
					   else
					     lookupApxString(r, G, s, k) (* count does NOT go up for these. *)
							     

     | lookupApxString (r, I.Decl(G, _), s, k) = 
					   (* Dec has no name *)
					   lookupApxString(r, G, s, k+1)


   fun getName (SOME [s]) = SOME s
     | getName _ = NONE

     

  (* Only used to return approximate types *) 
   fun lookupString (r, I.Null, s, k) = NONE
     | lookupString (r, I.Decl(G, (D'.InstantiableDec (D'.NormalDec (sLO, T0)))), s, k ) = 
                       let
			 fun checkVar(s, NONE, T) = NONE
			   | checkVar(s : string, SOME [s'], T) = if (s=s') then SOME(DI.VarInt (r,k), DA.exact2ApxType T) else NONE
			   | checkVar(s, SOME sL, T) = (case (findIndex(s, sL, 1))
							     of NONE => NONE
							   | SOME n => SOME(DI.Proj(r, DI.VarInt (r,k), n), DA.exact2ApxType (getIndex (n, T))))
		       in	     

				       (case checkVar(s, sLO, T0)
					  of NONE => lookupString(r, G, s, k+1)
					   | SOME (E', T) => SOME (E', T) (* D'.substTypes(T, I.Shift k) *)
					)
		       end
     | lookupString (r, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecLF (SOME s', A)))), s, k) = 
					  if (s=s') then 
					    SOME (DI.VarInt (r,k), DA.exact2ApxType (D'.LF(D'.Param, A))) (* D'.substTypes(D'.LF(D'.Param, A), I.Shift k) *)
					  else
					    lookupString(r, G, s, k+1)

     | lookupString (r, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecWorld (SOME s', W)))), s, k) = 
					 (* ADAM UPDATE:  Even it it has a name, we will never want to access it here..
					 if (s=s') then 
					   SOME (DI.VarInt (r,k), DA.exact2ApxType (D'.Meta(F))) (* D'.substTypes(D'.Meta(F), I.Shift k) *)
					 else
					   *)
					   lookupString(r, G, s, k+1)

     | lookupString (r, I.Decl(G, (D'.NonInstantiableDec _)), s, k) = 
					   (* Dec has no name *)
					   lookupString(r, G, s, k+1)

   (* lookup(r, i, G, k) = (name, T)
    * where T is the type of the variable at index i
    *)
   fun lookupInt (r, i, I.Null, _) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable #" ^ (Int.toString i) ^ " not found!"))
     | lookupInt (r, i, I.Decl(G, (D'.InstantiableDec (D'.NormalDec (name, T0)))), 1 ) = (getName name, D'.substTypes(T0, I.Shift i))
     | lookupInt (r, i, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecLF (name, A)))), 1) = (name, D'.substTypes(D'.LF(D'.Param, A), I.Shift i))
     | lookupInt (r, i, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecWorld (name, W)))), 1) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable #" ^ (Int.toString i) ^ " is a world variable!"))
     | lookupInt (r, i, I.Decl(G, _), k) = lookupInt(r, i, G, k-1)



   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* Our first stage is to convert from the external syntax to the intermediate syntax
    * which goes through the external syntax and fills in all LF parts
    *)
    (* Our reconstruction returns a pair (1, 2)
     * 1 = A "job" to be sent to LF Type Reconstruction Algorithm
     * 2 = A continuation, f, such that we apply f to the result of LF Reconstruction to finish our reconstruction
     *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)

   (* Note that we pass around two contexts
    * D'.Dec I.Ctx  and   DA.dec I.Ctx
    * The actual context under consideration is the concatenation
    * of the two.
    * Note:  this is for the first phase of type reconstruction 
    *)


   fun convertVarString(smartInj, G, ReconG, r, s) (* no patterns allowed *) =
         (case (lookupApxString (r, ReconG, s, 1))
	        of (SuccessMatch (E, Tapx)) => (E, removeCoverageInfoApx Tapx)
		 | PatternVariable T => getPatVarApx (r, s)
	         | NoMatch => (case (lookupString(r, G, s, (DA.ctxLength ReconG)+ 1))
				 of (SOME (E,T)) => (E, removeCoverageInfoApx T)
			          | NONE => getPatVarApx (r, s)))


   fun convertPatVarString(smartInj, G, ReconGglobal, ReconGlocal, r, s)  (* patterns allowed *) =
	    let
	        (* If it is meta-level existential then it is a fresh pattern variable.  However, if it is a parameter, then it does
		 * not stand for a pattern variable.  Typically all LF patterns should be written as <...> and then FVars are created
		 * as appropriate.  However, we allow the "optional" specification of LF parameters without the <..>.  Therefore,
		 * there can be a pattern "fn x <d> => ..." where the "d" is actually dependend upon the x and the x is not fresh.
		 * e.g.. world function in combinator example.
		 *
		 * Of course the preferred Delphin syntax is that all LF things are in <..>, However, we support this syntax so
		 * that if x : A#, then the programmer can formally write:
		 *  x for A#
		 * and <x> for A.
		 *
		 * However, we also do a powerful reconstruction so that if ther user writes <x> it will figure out if it is intended
		 * to be "x : A#" or "<x> : A"...  Thus it is best for ALL LF terms to be written in <..>.
		 *)

	      val sizeLocal = DA.ctxLength ReconGlocal
	      val sizeGlobal = DA.ctxLength ReconGglobal

	      
	      fun isParam isP = case (D'.whnfP isP)
		                  of D'.Param => true
				   | _ => false
				   (* NOTE that the "isP" status should not be ambiguous (PVar) for these situations
				    * as it will likely point to something created by "new"
				    * If the case does arise, then there will be a type error and the
				    * user will need to annotate the type.
				    *)

	      fun isParamTypeOrLF (DA.LF _) = true
		| isParamTypeOrLF (DA.Meta(r, _)) = false
		| isParamTypeOrLF (DA.SmartInj (_, _, DA.InjLF, isP)) = true
		| isParamTypeOrLF (DA.SmartInj (_, _, DA.InjMeta, isP)) = isParam isP
		| isParamTypeOrLF (DA.SmartInj (r, A, DA.InjVar (ref (SOME I)), isP)) = isParamTypeOrLF (DA.SmartInj (r, A, I, isP))
		| isParamTypeOrLF (DA.SmartInj (_, A, DA.InjVar r, isP)) = isParam isP
	                                                   (* What happens if this later gets resolved to be LF????
							    * NOTE:  I don't think it is possible to even encounter DA.SmartInj here..
							    * but just to be safe...
							    *)
			 
	      val (isUnique, Eopt) = 
		         case (lookupApxString (r, ReconGlocal, s, 1))
			   of SuccessMatch (E, T) => (false, SOME(E, removeCoverageInfoApx T)) 
			                            (* If it is in local it refers to a pattern variable already
						     * designated for this case.
						     * ADAM WARNING:
						     * What if the user does something like eps M.  M and M => ...
						     * Now we are allowing it to be the same pattern variable..
						     * This will only match during runtime if both arguments are the same.
						     * ML disallows such patterns.. perhaps we should as well???
						     *)
			     | PatternVariable T => (false, SOME(getPatVarApx(r, s)))
			     | NoMatch => 
			            (case (lookupApxString (r, ReconGglobal, s, sizeLocal + 1))
				       of SuccessMatch (E, T) => if (isParamTypeOrLF T) then (false, SOME(E, removeCoverageInfoApx T)) else (false, NONE)
				       | PatternVariable T => if (isParamTypeOrLF T) then (false, SOME(getPatVarApx(r, s))) else (false, NONE)
				       | NoMatch => (case (lookupString(r, G, s, sizeLocal + sizeGlobal + 1))
						       of SOME (E, T) => if isParamTypeOrLF T then (false, SOME(E, removeCoverageInfoApx T)) else (false, NONE)
						        | NONE => (true (* we do not need to rename the variable *), NONE)))
						    				                       
	    in
	      case Eopt
		of (SOME (E, T)) => (ReconGlocal, E, T)
	         | NONE => let 
			     val (E, T) = addPatVarApx (r, s, isUnique)
			   in
			     (I.Decl(ReconGlocal, DA.PatternVariable (s, T)), E, T)
			   end
	    end



   fun inferTypeApx (smartInj, G, ReconG, D.Quote (r, _)) = 
        if smartInj then
	      DA.SmartInj (r, Approx.newCVar(), DA.InjVar(ref NONE), D'.newPVar()) (* We need to determine if it is meant to be LF or Meta *)
	else
              DA.LF(r, D'.newPVar(), Approx.newCVar())  (* It is LF *)


     | inferTypeApx (smartInj, G, ReconG, D.VarString (r, s)) = 
	    let
	      val (_, T) = convertVarString(smartInj, G, ReconG, r, s)
	    in
	      T
	    end


     | inferTypeApx (smartInj, G, ReconG, D.TypeAscribe (_, E, _)) = 
	     inferTypeApx (smartInj, G, ReconG, E)

     | inferTypeApx (smartInj, G, ReconG, E) = 
	     let 
	       val r = D.getRegExp E
	     in
	       DA.Meta(r, DA.FVar(r, ref NONE))
	     end


   fun inferPatTypeApx (smartInj, G, ReconGglobal, ReconGlocal, D.PatternQuote (r, _)) = 
        if smartInj then
	      (ReconGlocal, DA.SmartInj (r, Approx.newCVar(), DA.InjVar(ref NONE), D'.newPVar())) (* We need to determine if it is meant to be LF or Meta *)
	else
              (ReconGlocal, DA.LF(r, D'.newPVar(), Approx.newCVar()))  (* It is LF *)


     | inferPatTypeApx (smartInj, G, ReconGglobal, ReconGlocal, D.PatternString (r, s)) = 
	    let
	      val (ReconGlocal', _, T) = convertPatVarString(smartInj, G, ReconGglobal, ReconGlocal, r, s)
	    in
	      (ReconGlocal', T)
	    end

     | inferPatTypeApx (smartInj, G, ReconGglobal, ReconGlocal, D.PatternOmitted r) = 
	       (ReconGlocal, DA.Meta(r, DA.FVar(r, ref NONE)))


     | inferPatTypeApx (smartInj, G, ReconGglobal, ReconGlocal, D.PatternAscribe (_, E, _)) = 
	     inferPatTypeApx (smartInj, G, ReconGglobal, ReconGlocal, E)

     | inferPatTypeApx (smartInj, G, ReconGglobal, ReconGlocal, E) = 
	     let 
	       val r = D.getRegPatternExp E
	     in
	       (ReconGlocal, DA.Meta(r, DA.FVar(r, ref NONE)))
	     end

   fun convertIsParam(D.Existential) = D'.Existential
     | convertIsParam(D.Param) = D'.Param
     | convertIsParam(D.OmittedParam) = D'.newPVar()

   fun convertVisibility(D.Implicit) = D'.Implicit
     | convertVisibility(D.Visible) = D'.Visible




   fun countNumArgs (isSugar, D.Eps(r, _, C)) = countNumArgs (isSugar, C)
     | countNumArgs (isSugar, D.NewC(r, _, C)) = countNumArgs (isSugar, C)
     | countNumArgs (isSugar, D.PopC (r, _, C)) = countNumArgs (isSugar, C)
     | countNumArgs (isSugar, D.Match(isSugar', _, pats, _)) = if (isSugar = isSugar') 
			                                                then List.length pats
									else 0
									  
   fun checkAllBranches (isSugar, r, []) = 0 (* no cases *)
     | checkAllBranches (isSugar, r, C::Cs) =
	          let
		    val p = countNumArgs (isSugar, C)
		    fun checkSame [] = true
		      | checkSame (x::xs) = (p = (countNumArgs (isSugar, x))) andalso checkSame xs
		  in
		    if (checkSame Cs) then p
		    else raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "All branches must have the same number of arguments"))
		  end


   (* NOTE:  We only allow Pop up to end of ReconG
    * G contains the fixpoints already processed, so this is acceptable
    *)
   fun lookupNewString (r, I.Null, s, _) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!"))
     (* ABP:  Should we check if the name has been overridden as a non-parameter?... as of now.. no *)
     | lookupNewString (r, I.Decl(ReconG, DA.NonInstantiableDec (_, D as DA.NewDecLF (_, SOME s', _))), s, k) =
	                                    if (s=s') then
					      (k, D)
					    else
					      lookupNewString(r, ReconG, s, k+1)
     | lookupNewString (r, I.Decl(ReconG, DA.NonInstantiableDec (_, D as DA.NewDecWorld (_, SOME s', W))), s, k) =
					    (* ADAM UPDATE:  This is used in "pop" and we do not allow pop to access
					     * world variables....(see intSyntax.sml for justification)
					     
	                                    if (s=s') then
					      (k, D)
					    else
					      *)
					      lookupNewString(r, ReconG, s, k+1)

     | lookupNewString (r, I.Decl(ReconG, DA.NonInstantiableDec _), s, k) = lookupNewString(r, ReconG, s, k+1)

     | lookupNewString (r, I.Decl(ReconG, DA.PatternVariable _), s, k) = lookupNewString(r, ReconG, s, k) (* count does NOT go up *)

     | lookupNewString (r, I.Decl(ReconG, DA.InstantiableDec _), s, k) = lookupNewString(r, ReconG, s, k+1)


   (* removePopC (r, Clist) = SOME E' 
    * if no changes were made, it returns NONE.
    * This routine attempts to move PopC to the outside if possible.
    * This is expecially important for coverage, as it requires all branches to be under
    * the same pops..
    *)
   fun removePopC(smartInj, G, ReconG, r, Clist) =
           let
	     (* PopC causes problems in coverage unless if all cases go under the same pops,
	      * so here we attempt to move the Pop outside
	      * For example,
	      * if we have a function
	      *   fn (p1 => e1) | ((p2 => e2) \x)
	      * we can equivalent convert it to
	      *   (fn {<x>}(p1 => e1) | (p2 => e2)) \x
	      * Now the "\x" is applied to the entire function instead of just one case.
	      *)

	     fun getNewDec(r, s) = let
				     val (i, Dapprox) = lookupNewString (r, ReconG, s, 1)
				   in
				     case Dapprox
				       of DA.NewDecLF _ => (i, s, D.NewDecLF(r, SOME s, D.LFomit r))
					| DA.NewDecWorld (_, _, W) => raise Domain (* this is impossible by lookupNewString *)
					                              (* (i, s, D.NewDecWorld(r, SOME s, W)) *)
				   end
	               
	     fun getMinPop [] = NONE
	       | getMinPop (D.PopC (r, s, C) :: Clist) =
	                                    (case (getMinPop Clist)
					       of NONE => SOME (getNewDec(r, s))
						| SOME (j, sj, Dj) => let
									 val (i, si, Di) = getNewDec(r, s)
								       in
									 if (i <= j) then (SOME (i, si, Di)) else (SOME (j, sj, Dj))
								       end)
	       | getMinPop (_ :: Clist) = getMinPop Clist

	     val movePop = case (getMinPop Clist)
	                   of NONE => NONE
			    | SOME (m, s, Dm) =>
			      (let
				 fun removePop (Corig as D.PopC(_, s', C)) =
				       if (s = s') then C
				       else D.NewC(r, Dm, Corig) (* as we are dealing with the external syntax there is no
								     * reason to apply any substitution to C.
								     *)	
				   |  removePop (Corig) = D.NewC(r, Dm, Corig)
			       in
				 SOME(s, map removePop Clist)
			       end)
	   in
	     case (movePop)
	       of (NONE) => NONE
	        | (SOME(s, Clist')) => SOME(D.Pop(r, s, D.Lam(r, Clist')))
	   end


   fun coerceExp (DI.Quote (_, M, _, DA.InjLF, isP)) = 
          (* It is important that references to a variable are made with "Idx"
	   * as otherwise it will not be detected as a pattern substitution 
	   *)
          (let
	    val n = Whnf.etaContract(M)
	  in
	    I.Idx n
	  end handle Whnf.Eta => I.Exp M)

    | coerceExp (DI.Quote (r, M, A, DA.InjVar (ref (SOME I)), isP)) = coerceExp (DI.Quote(r, M, A, I, isP))
    | coerceExp (DI.VarInt (_, i)) = I.Idx i
    | coerceExp _ = I.Undef


   fun isAllImplicitDecs [] = true
     | isAllImplicitDecs ((D'.Implicit, _)::xs) = isAllImplicitDecs xs
     | isAllImplicitDecs ((D'.Visible, _)::xs) = false


   fun isAllImplicitFApx F = case (DA.whnfF F)
                             of (DA.All(_, Ds, _)) => isAllImplicitDecs Ds
			      | _ => false

   fun isAllImplicitTApx (DA.Meta (_,F)) = isAllImplicitFApx F
     | isAllImplicitTApx _ = false


   fun isAllImplicitF F = case (D'.whnfF F)
                          of (D'.All(Ds, _)) => isAllImplicitDecs Ds
			   | _ => false

   fun isAllImplicitT (D'.LF _) = false
     | isAllImplicitT (D'.Meta F) = isAllImplicitF F

   fun applyImplicit(G, E, T, K) =
     let
             val r = DI.getRegionExp E
	     fun getDecs (F, K) = getDecsW (D'.whnfF F, K)
	     and getDecsW (D'.All((_ (* Implicit *), D'.NormalDec (_, D'.LF(isP, A)))::Ds, F), K) = 
	          let
		    val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
		    val Q = DI.Quote(r, X, A, DA.InjLF, isP)
		    val K' = DelphinAbstract.LFcollectExp(r, NONE, (A, I.id), DelphinAbstract.LFcollectExp (r, NONE, (X, I.id), K, true), true)
		    val t' = I.Dot(coerceExp Q, I.id)
		    val (args', Frest, K'') = getDecs(D'.FClo(D'.All(Ds, F), t'), K')
		  in
		    ((D'.Implicit, Q) :: args', Frest, K'')
		  end
		| getDecsW (D'.All([], F), K) = ([], F, K)
	        | getDecsW _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Bad unexpected error"))



	     fun applyImplicitFun (E, T as D'.LF _, K) = (E, T, K)
	       | applyImplicitFun (E, T as D'.Meta(F), K) = (case (D'.whnfF F)
							     of (D'.All(Ds, _)) => 
							          if (isAllImplicitDecs Ds) then
								    let
								      val (args', F', K') = getDecs (F, K)
								    in
								      applyImplicitFun(DI.App(r, E, args'), D'.Meta(F'), K')
								    end
								  else (E, T, K)
							   | _ => (E, T, K))

     in
       applyImplicitFun(E, T, K)
     end


   fun applyImplicitApprox(T as DA.Meta(r, F)) = 
         (case (DA.whnfF F)
	    of (DA.All(_, Ds, F)) => 
	      if (isAllImplicitDecs Ds) then applyImplicitApprox(DA.Meta(r, F))
	      else T
	     | _ => T)
     | applyImplicitApprox(T) = T




   fun makeForAllApprox(isSugar, smartInj, r, argsType, F) = makeForAllApproxW(isSugar, smartInj, r, argsType, DA.whnfF F)
   and makeForAllApproxW(isSugar, smartInj, r, argsType, F as DA.All _) = F (* nothing to do.. *)
     | makeForAllApproxW(isSugar, smartInj, r, argsType, F) =
              let
		fun createForAll(false, Ds) = DA.All(r, Ds, DA.FVar (r, ref NONE))
		  | createForAll(true (* isSugar *), D::Ds) = DA.All(r, [D], createForAll(true, Ds))
		  | createForAll(true, []) = DA.FVar(r, ref NONE)

		val Ds = map (fn T => (D'.Visible, DA.NormalDec(r, NONE, T))) argsType
		val Fnew = createForAll(isSugar, Ds)

		val _ = unifyApxTypes(smartInj, r, "Type mismatch in creating forall", DA.Meta(r, Fnew), DA.Meta(r, F))
	      in
		Fnew
	      end




   (* convert dec routines return:  
    * 
    * (Drecon, Dapprox, job, f)
    * Where job represents a reconstruction job in the current context
    * and f is a function which takes TWO arguments
    *   (1) The result of the reconstruction of job
    *   (2) The "Dec" returned by Reconstruction of Drecon
    *)
   fun convertNormalDec2Temp (G, ReconG, D.NormalDec (r, sO, D.LF(r2, isP, lftype))) = 
          let
	    val t = tokensToTerm (PrintDelphinExt.lfexpToTokens lftype)
	    val A = Approx.newCVar()
	    val Drecon = ReconTerm.dec (sO, t, SOME A, r) 
	    val isP' = convertIsParam isP
	    val Dapprox = DA.NormalDec (r, strOpt2strListOpt sO, DA.LF(r2, isP', A))


	    fun f (ReconTerm.JNothing, I.Dec(_, V)) = DI.NormalDec (r, sO, DI.LF(r2, isP', V))
	      | f _ = raise Domain

	  in
	    (Drecon, Dapprox, ReconTerm.jnothing, f)
	  end

     | convertNormalDec2Temp (G, ReconG, D.NormalDec (r, sO, D.Meta(r2, F))) =
          let
	    val (Fapprox, job, f1) = convertFormula2Temp(G, ReconG, F)

	    val Drecon = ReconTerm.ndec (sO, r)
	    val Dapprox = DA.NormalDec (r, strOpt2strListOpt sO, DA.Meta(r2, Fapprox))

	    fun f (x, _ (* NDec *)) = DI.NormalDec(r, sO, DI.Meta(r2, f1 x))

	  in
	    (Drecon, Dapprox, job, f)
	  end


   and convertNewDec2Temp (G, ReconG, D.NewDecLF (r, nameOpt, lftype)) =
          let
	    val t = tokensToTerm (PrintDelphinExt.lfexpToTokens lftype)
	    val A = Approx.newCVar()

	    val Drecon = ReconTerm.dec (nameOpt, t, SOME A, r)
	    val Dapprox = DA.NewDecLF (r, nameOpt, A)

	    fun f (ReconTerm.JNothing, I.Dec(_, V)) = DI.NewDecLF (r, nameOpt, V)
	      | f _ = raise Domain

	  in
	    (Drecon, Dapprox, ReconTerm.jnothing, f)
	  end

    (* no NewDecWorld in external syntax
     | convertNewDec2Temp (G, ReconG, D.NewDecWorld (r, nameOpt, W)) =
          let
	    val Drecon = ReconTerm.ndec (nameOpt, r)
	    val Dapprox = DA.NewDecWorld (r, nameOpt, W)

	    fun f (ReconTerm.JNothing) = DI.NewDecWorld(r, nameOpt, W)
	      | f _ = raise Domain
	  in
	    (Drecon, Dapprox, ReconTerm.jnothing, f)
	  end
    *)


   and convertTypes2Temp (G, ReconG, D.LF(r, isP, lftype)) =
         let
	   val t = tokensToTerm (PrintDelphinExt.lfexpToTokens lftype)
	   val A = Approx.newCVar()
	    val isP' = convertIsParam isP
	   val Tapprox = DA.LF(r, isP', A)

	   val job = ReconTerm.jtypeEqualApx (t, A)

	   fun f (ReconTerm.JClass ((U,_), _)) = DI.LF (r, isP', U)
	     | f _ = raise Domain

	 in
	   (Tapprox, job, f)
	 end

     | convertTypes2Temp (G, ReconG, D.Meta(r, F)) =
	 let
	   val (Fapprox, job1, f1) = convertFormula2Temp(G, ReconG, F)
	   fun f x = DI.Meta(r, f1 x)
	 in
	   (DA.Meta(r, Fapprox), job1, f)
	 end


     
   and convertFormula2Temp (G, ReconG, D.Top r) = 
           let
	     fun f (ReconTerm.JNothing) = DI.Top r
	       | f _ = raise Domain
	   in
	     (DA.Top r, ReconTerm.jnothing, f)
	   end
     | convertFormula2Temp (G, ReconG, D.All (r, Ds, F)) =
	   let
	     val decJobs = map (fn (vis, D) => 
	                         let
				   val (Drecon, Dapprox, job1, f1) = convertNormalDec2Temp (G, ReconG, D)
				 in
				   (convertVisibility vis, Drecon, Dapprox, job1, f1)
				 end)
                                Ds

	     fun addDs (G, []) = G
	       | addDs (G, (_, _, Dapprox, _, _)::Ds) = addDs(I.Decl(G, DA.InstantiableDec (r, Dapprox)), Ds)
	                      
	     val (Fapprox, job2, f2) = convertFormula2Temp (G, addDs(ReconG, decJobs), F)

	     fun fDecs ((vis, Drecon, Dapprox, job, f)::xs) (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(I.Decl(_, D), jobResult2))) =
	               let
			 val D'' = f (jobResult1, D)
			 val rest = fDecs xs jobResult2
		       in
			 case rest
			   of DI.All (r, Ds, F) => DI.All (r, (vis, D'')::Ds, F)
			    | _ => raise Domain
		       end
	       | fDecs nil res = DI.All (r, [], f2 res)
	       | fDecs _ _ = raise Domain

	     fun getJob ((_, Drecon, _, jobP, _) :: xs) = ReconTerm.jand(jobP, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), getJob xs))
	       | getJob [] = job2


	     fun getApproxDecs [] = []
	       | getApproxDecs ((vis, _, Dapprox, _, _)::xs) = (vis, Dapprox) :: (getApproxDecs xs)

	     val approxF = (case (getApproxDecs decJobs) of
			      [] => Fapprox
		            | Ds => DA.All (r, Ds, Fapprox))
		      
	   in
	     (approxF, getJob decJobs, fDecs decJobs)
	   end

     | convertFormula2Temp (G, ReconG, D.Exists (r, D, F)) =
	   let
	     val (Drecon, Dapprox, job1, f1) = convertNormalDec2Temp (G, ReconG, D)
	     val (Fapprox, job2, f2) = convertFormula2Temp (G, I.Decl(ReconG, DA.InstantiableDec(r, Dapprox)), F)

	     fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(I.Decl(_, D), jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val F'' = f2 jobResult2
		  in
		    DI.Exists (r, D'', F'')
		  end
	       | f _ = raise Domain
		      
	   in
	     (DA.Exists (r, Dapprox, Fapprox), ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), job2)), f)
	   end


     | convertFormula2Temp (G, ReconG, D.Nabla (r, D, F)) =
	   let
	     val (Drecon, Dapprox, job1, f1) = convertNewDec2Temp (G, ReconG, D)
	     val (Fapprox, job2, f2) = convertFormula2Temp (G, I.Decl(ReconG, DA.NonInstantiableDec(r, Dapprox)), F)

	     fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(I.Decl(_, D), jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val F'' = f2 jobResult2
		  in
		    DI.Nabla (r, D'', F'')
		  end
	       | f _ = raise Domain
		      
	   in
	     (DA.Nabla (r, Dapprox, Fapprox), ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), job2)), f)
	   end

     | convertFormula2Temp (G, ReconG, D.FormulaString (r,name)) =
           let
	     fun f (ReconTerm.JNothing) = DI.FormulaString (r,name)
	       | f _ = raise Domain

	      fun findSig (s:string, []) = NONE
		| findSig (s, (s', FA, _)::mSig) = if (s = s') then (SOME FA) else findSig(s, mSig)

	      val FA = case (findSig (name, !(!metaSigRef)))
		         of SOME FA => FA (* F is closed and EVar free, so it never needs to  undergo any shifts *)
		          | NONE => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type Alias " ^ name ^ " not found!"))
	   in
	     (FA, ReconTerm.jnothing, f)
	   end


     | convertFormula2Temp (G, ReconG, D.OmittedFormula r) =
           let
	     fun f (ReconTerm.JNothing) = DI.OmittedFormula r
	       | f _ = raise Domain
	   in
	     (DA.FVar (r, ref NONE), ReconTerm.jnothing, f)
	   end


   (* Precondition is that G is fully defined and has NO FVars *)

   and convertExp2Temp (smartInj, G, ReconG, D.VarString (r, s), Tresult) = 
           let
	     val (E, T) = convertVarString(smartInj, G, ReconG, r, s)
	     val _ = unifyApxTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", Tresult, T)

	     fun f (ReconTerm.JNothing) = E
	       | f _ = raise Domain
	   in
	     (ReconTerm.jnothing, f)
	   end



     | convertExp2Temp (smartInj, G, ReconG, D.Quote (r, LFterm), Tresult) =
	   let
	     val A = Approx.newCVar()
	     val t = tokensToTerm (PrintDelphinExt.lfexpToTokens LFterm)
	     val I = if smartInj then DA.InjVar(ref NONE) (* We don't know if it is LF or Meta *)
	                    else DA.InjLF (* It is LF *)
	                   
	     val isP = D'.newPVar()
	     val _ = unifyApxTypes(smartInj, r, "Incompatible type", Tresult, DA.SmartInj(r, A, I, isP))

	     val job = ReconTerm.jofApx (t, A)

	     fun f (ReconTerm.JOf ((U, _), (V,_), _)) = DI.Quote (r, U, V, I, isP)
	       | f _ = raise Domain
	   in
	     (job, f)
	   end

     | convertExp2Temp (smartInj, G, ReconG, D.Unit r, Tresult) =	  
	   let
	     val _ = unifyApxTypes(smartInj, r, "() has incompatible type", Tresult, DA.Meta(r, DA.Top r))

	     fun f (ReconTerm.JNothing) = DI.Unit r
	       | f _ = raise Domain
	   in
	     (ReconTerm.jnothing, f)
	   end


     | convertExp2Temp (smartInj, G, ReconG, D.Lam (r, Clist), Tresult) =
	   let
	     val _ = checkAllBranches (false, r, Clist)
	     val isSugar = ((checkAllBranches (true,r,Clist)) > 0) orelse (List.length Clist = 0) (* If there are no cases, then we
											  * make it sugar so that it will expand out all
											  * the arguments and look at it together.
											  *)
	     val updateClist = removePopC(smartInj, G, ReconG, r, Clist) (* Attempts to remove PopC (by moving to the outside if possible) *)

	     val F = DA.FVar(r, ref NONE)
	     val _ = unifyApxTypes(smartInj, r, "Function has incompatible type", Tresult, DA.Meta(r, F))

	     fun moduloAllImplicit F =
	                case (DA.whnfF F)
	                  of (DA.All(_, Ds, F')) => if (isAllImplicitDecs Ds) then moduloAllImplicit F' else F
			   | _ => F

	     val F' = moduloAllImplicit F
	   in
	     case updateClist
	       of NONE => 
		       let
			 fun caseF C =
			   let 
			     val oldTables = saveApxTables() (* Scoping the patvars here IS necessary *)
			     val (job, f) = convertCase2Temp(isSugar, smartInj, G, ReconG, I.Null (* local *), C, DA.Meta(r, F'))
			     val _ = restoreApxTables oldTables
			   in
			     (ReconTerm.jscopeVars job, f)  (* Scope the variables introduced in C so it only applies to that branch *)
			   end
			 
			 val jobFunList = map caseF Clist 
			   
			 fun getJobList [] = ReconTerm.jnothing
			   | getJobList ((job,_)::xs) = ReconTerm.jand(job, getJobList xs)
			   
			 val allJobs = getJobList jobFunList
			   
			 fun f' ((_,f1)::xs) (ReconTerm.JAnd(jobResult1, jobResult2)) = (f1 jobResult1) :: (f' xs jobResult2)
			   | f' [] (ReconTerm.JNothing) = []
			   | f' _ _ = raise Domain
			   
			 fun f x = DI.Lam(isSugar, r, f' jobFunList x, NONE)
		       in
			 (allJobs, f)
		       end
	       | SOME E' => convertExp2Temp(smartInj, G, ReconG, E', DA.Meta(r, F'))
	   end

     | convertExp2Temp (smartInj, G, ReconG, D.New (r, D, E), Tresult) = 
	  let
	    val (Drecon, Dapprox, job1, f1) = convertNewDec2Temp (G, ReconG, D)
	    val F = DA.FVar(r, ref NONE)
	    val inferredType = DA.Meta(r, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type Mismatch", Tresult, inferredType)
	    val (job2, f2) = convertExp2Temp (smartInj, G, I.Decl(ReconG, DA.NonInstantiableDec (r, Dapprox)), E, DA.Meta(r, F))

	    fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx (I.Decl(_, D), jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val E'' = f2 jobResult2
		  in
		    DI.New(r, D'', E'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), job2)) , f)
	  end

     | convertExp2Temp (smartInj, G, ReconG, D.App (r, E1, args), Tresult) = 
	  let
	    val Tstart = DA.Meta (r, DA.FVar (r, ref NONE))
	    val (job1, f1) = convertExp2Temp (smartInj, G, ReconG, E1, Tstart)
	    val Tfun = applyImplicitApprox(Tstart)

	    val funF = case Tfun
	               of (DA.Meta(_, F)) => F
			| _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Expected function type, but got LF"))


	    fun getArgJobs (Es, F) = getArgJobsW (Es, DA.whnfF F)
	    and getArgJobsW (Es, DA.All(r', (D'.Implicit, _)::Ds, F)) = getArgJobs (Es, DA.All(r', Ds, F))

	      | getArgJobsW ((E::Es), DA.All(r', (D'.Visible, DA.NormalDec (_, _, T))::Ds, F)) =
	            let
			(* If we have a function which only has implicit args, then it may need
			 * to be filled in as an argument.  For example, imagine:
			 * D-- val x : <ev_s>
			 * D-- x @ <ev_z>
			 * This is an example where "x" will be a meta-level function only with implicit
			 * arguments.
			 *)
		      val argType = inferTypeApx(smartInj, G, ReconG, E)
		    in
		      if isAllImplicitTApx argType then
			     let
			       val E' = convertExp2Temp(smartInj, G, ReconG, E, argType)
			       val T' = applyImplicitApprox argType
			       val _ = unifyApxTypes(smartInj, r, "Type mismatch", T, T')
			       val (rest, Frest) = getArgJobs (Es, DA.All(r', Ds, F))
			     in
			       (E' :: rest, Frest)
			     end
		      else
			     let
			       val E' = convertExp2Temp(smartInj, G, ReconG, E, T)
			       val (rest, Frest) = getArgJobs (Es, DA.All(r', Ds, F))
			     in
			       (E' :: rest, Frest)
			     end
			       
		    end

	      | getArgJobsW ([], DA.All(r, [], F)) = ([], F)
	      | getArgJobsW (args, DA.All(r, [], F)) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected remaining args"))
	      | getArgJobsW _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Args"))


	    val argsType = map (fn E2 => inferTypeApx(smartInj, G, ReconG, E2)) args
	    val funF = makeForAllApprox(false, smartInj, r, argsType, funF) (* makes funF a Forall *)
	    val (argJobs, Frest) = getArgJobs (args, funF)

	    val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, Frest))

	    fun fArgs ((jobP, fP) :: xs) (ReconTerm.JAnd(jobResult1, jobResult2)) =
	              let
			val E' = fP jobResult1
			val rest = fArgs xs jobResult2
		      in
			(D'.Visible, E') :: rest
		      end
	      | fArgs nil (ReconTerm.JNothing) = []
	      | fArgs _ _ = raise Domain

	    fun getJob ((jobP, fP) :: xs) = ReconTerm.jand(jobP, getJob xs)
	      | getJob [] = ReconTerm.jnothing


	    val (job2, f2) = (getJob argJobs, fArgs argJobs)

	    fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val E1'' = f1 jobResult1
		    val args'' = f2 jobResult2
		  in
		    DI.App(r, E1'', args'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1, job2), f)
	  end

     | convertExp2Temp (smartInj, G, ReconG, D.Pair (r, E1, E2), Tresult) = 
	  let
	     val F = DA.FVar(r, ref NONE)
	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, F))
		       
	     val firstType = inferTypeApx (smartInj, G,ReconG, E1)
	     val D = DA.NormalDec(r, NONE, firstType)
	     val secondF = DA.FVar(r, ref NONE)
	     val pairF = DA.Exists(r, D, secondF)
	     val pairType = DA.Meta(r, pairF)

	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, pairType)

	     val (job1, f1)  = convertExp2Temp(smartInj, G, ReconG, E1, firstType)
	     val (job2, f2)  = convertExp2Temp(smartInj, G, ReconG, E2, DA.Meta(r, secondF))
	    

	     fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val E1'' = f1 jobResult1
		    val E2'' = f2 jobResult2
		  in
		    DI.Pair(r, E1'', E2'')
		  end
	       | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1, job2), f)
	  end

     | convertExp2Temp (smartInj, G, ReconG, D.Pop (r, s, E), Tresult) = 
	  let
	    (* NOTE:  We only allow Pop up to end of ReconG
	     * G contains the fixpoints already processed, so this is acceptable
	     *)
	    val (i, Dapprox) = lookupNewString (r, ReconG, s, 1)
	    val ReconG' = DA.popCtx (i, ReconG) (* IMPORTANT not to use D'.popCtx! as we ignore some parts of this context *)
	    val F = DA.FVar (r, ref NONE)
	    val T = DA.Meta(r, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, F))


	    val (job1, f1) = convertExp2Temp (smartInj, G, ReconG', E, T)
	    fun f (ReconTerm.JPopCtx(_, jobResult)) = DI.Pop(r, i, f1 jobResult)
	      | f _ = raise Domain
	  in
	    (ReconTerm.jpopctx(i, job1), f)
	  end


     | convertExp2Temp (smartInj, G, ReconG, D.Fix (r, funList), Tresult) = raise Domain (* only used in printing *)
       (*
	  let
	    val (_, job1, f1) = convertFunList2Temp(smartInj, G, ReconG, r, funList, Tresult)
	    fun f x = DI.Fix(r, f1 x)
	  in
	    (job1, f)
	  end
      *)

     | convertExp2Temp (smartInj, G, ReconG, D.TypeAscribe (r, E, T), Tresult) = 
	  let
	      val (Tapx, job1, f1) = convertTypes2Temp(G, ReconG, T)

	     (* ENHANCEMENT:  If E is Quote and T is an implicit function,
	      * then first get rid of the implicit arguments...
	      *)
	      val Tapx = applyImplicitApprox Tapx

		
	      val _ = unifyApxTypes (smartInj, r, "Type Ascription doesn't match", Tresult, Tapx)
	      val (job2, f2) = convertExp2Temp(smartInj, G, ReconG, E, Tresult)

	      fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val T'' = f1 jobResult1
		    val E'' = f2 jobResult2
		  in
		    DI.TypeAscribe(r, E'', T'')
		  end
		| f _ = raise Domain
	  in
	    (ReconTerm.jand(job1,job2) , f)
	  end

     | convertExp2Temp (smartInj, G, ReconG, D.Sequence eList, Tresult) = 
	   let
	     fun convertList [(r, e)] = 
	                                let
	                                  val (job, f) = convertExp2Temp(smartInj, G, ReconG, e, Tresult)
					in
					  [(r, job, f)]
					end
	       | convertList ((r,e)::eList) =
					let
					  val T = inferTypeApx(smartInj, G, ReconG, e)
					  val (job, f) = convertExp2Temp(smartInj, G, ReconG, e, T)
					in
					  (r, job, f) :: (convertList eList)
					end
	       | convertList _ = raise Domain

	     val fList = convertList eList

	     fun f' ((r, job1, f1)::fList) (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val E'' = f1 jobResult1
		    val rest = f' fList jobResult2
		  in
		    (r,E'') :: rest
		  end
	       | f' [] (ReconTerm.JNothing) = []
	       | f' _ _ = raise Domain

	     fun getJob ((r, job1, f1) :: fList) = ReconTerm.jand(job1, getJob fList)
	       | getJob [] = ReconTerm.jnothing

	     val job = getJob fList
	     fun f x = DI.Sequence (f' fList x)
	   in
	     (job, f)
	   end

     | convertExp2Temp (smartInj, G, ReconG, D.LiftedApp (r, E1, E2), Tresult) =
	   (* Create a function (fn <F> => fn <E> => <F E>) and apply it to E1 and E2 *)
	   (* or a function (fn <F> => fn <E> => (<F E>,()) if smartInj is false) *)
	   let
	     val Fname = D.LFid (r, false, getFreshName())
	     val Ename = D.LFid (r, false, getFreshName())
	     val result = if smartInj then
	                    D.Quote(r, D.LFapp (r, Fname, Ename))
			  else
	                    D.Pair(r, D.Quote(r, D.LFapp (r, Fname, Ename)), D.Unit r)

	     val function = D.Lam (r, [D.Match(false, r, 
					       [D.PatternQuote(r, Fname)],
					       D.Lam (r, [D.Match(false, r,
								  [D.PatternQuote(r, Ename)], 
								  result)]))])
	     val term = D.App(r, D.App (r, function, [E1]), [E2])
	   in
	     convertExp2Temp (smartInj, G, ReconG, term, Tresult)
	   end

     (* OLD
     | convertExp2Temp (smartInj, G, ReconG, D.LetVar (r, D, E1, E2), Tresult) =
	  let
	    val (Drecon, Dapprox, job1, f1) = convertNormalDec2Temp (G, ReconG, D)
	    val Tapx = case Dapprox
	               of (DA.NormalDec (_, _, T)) => T
			 
	    val (job2, f2) = convertExp2Temp(smartInj, G, ReconG, E1, Tapx)
	    val ReconG' = I.Decl(ReconG, DA.InstantiableDec(r, Dapprox))
	    val (job3, f3) = convertExp2Temp(smartInj, G, ReconG', E2, Tresult)
	      
	    fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JAnd(jobResult2, ReconTerm.JWithCtx(I.Decl(_, D), jobResult3)))) =
	           let
		     val D'' = f1 (jobResult1, D)
		     val E1'' = f2 jobResult2
		     val E2'' = f3 jobResult3
		   in
		     DI.LetVar (r, D'', E1'', E2'')
		   end
	      | f _ = raise Domain
	    
	  in
	    (ReconTerm.jand(job1, ReconTerm.jand(job2, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), job3))), f)
	  end
     *)

     | convertExp2Temp (smartInj, G, ReconG, D.LetVar (r, Pat, E1, E2), Tresult) =
	   convertExp2Temp(smartInj,
			   G,
			   ReconG,
			   D.App(r, D.Lam(r, [D.Match(false, r, [Pat], E2)]), [E1]),
			   Tresult)


     | convertExp2Temp (smartInj, G, ReconG, D.LetFun (r, funList, E), Tresult) =
	  let
	    val Tapx = DA.Meta(r, DA.FVar (r, ref NONE))
	    val (Dapprox, job1, f1) = convertFunList2Temp(smartInj, G, ReconG, r, funList, Tapx)
	    val ReconG' = I.Decl(ReconG, DA.InstantiableDec (r, Dapprox))
	    val Drecon = ReconTerm.ndec (NONE, r)
	    val (job2, f2) = convertExp2Temp(smartInj, G, ReconG', E, Tresult)

	    fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(_, jobResult2))) =
	          let
		    val funList'' = f1 jobResult1
		    val E'' = f2 jobResult2
		  in
		    DI.LetFun(r, funList'', E'')
		  end
	      | f _ = raise Domain
	  in
	    (ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon),job2)) , f)
	  end



     | convertExp2Temp (smartInj, G, ReconG, D.ExtendFun (r, E, Clist), Tresult) =
	       let
		 val _ = checkAllBranches (false, r, Clist)
		 val isSugar = ((checkAllBranches (true,r,Clist)) > 0) orelse (List.length Clist = 0) (* If there are no cases, then we
											  * make it sugar so that it will expand out all
											  * the arguments and look at it together.
											  *)

		 (*
		  (bool represents isSugar)
		  GB |- E : T
		  GB, G2a |- CS : T
                  and first and last elements of G2a are NonInstantiable
		  ------------------------------------------------------
	          GB, G2a, G2b |- ExtendFunWith(E, CS, sizeG2a, sizeG2b, bool, Fopt) : T

	          (D.Formula option) = T (which makes sense in GB)
		 *)

		 fun getWorldFun (D.VarString(r, s)) = SOME(s)
		   | getWorldFun (D.Lam(r, [])) = NONE
		   | getWorldFun (D.TypeAscribe(r, E, T)) = getWorldFun E
		   | getWorldFun _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only extend parameter functions in the context (or empty functions)."))

		 val nameOpt = getWorldFun E

		 fun isEqual(s, NONE) = false
		   | isEqual(s : string, SOME s') = (s = s')

		 fun findParameters (I.Decl(ReconG, DA.NonInstantiableDec (_, DA.NewDecLF (_, SOME s, _))), k) = 
		              if isEqual(s, nameOpt) then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Cannot extend a parameter!"))
			      else
				k :: (findParameters(ReconG, k+1))
		   | findParameters (I.Decl(ReconG, DA.NonInstantiableDec (_, DA.NewDecLF (_, NONE (* no name *), _))), k) = 
				k :: (findParameters(ReconG, k+1))

		   | findParameters (I.Decl(ReconG, DA.NonInstantiableDec (_, DA.NewDecWorld _)), k) = 
				(* name doesn't matter for NewDecWorld...*)
				(findParameters(ReconG, k+1))

		   | findParameters (I.Decl(ReconG, DA.InstantiableDec (_, DA.NormalDec(r, SOME [s], _))), k) = 
                               if isEqual(s, nameOpt) then [] 
			       else findParameters(ReconG, k+1)

		   | findParameters (I.Decl(ReconG, DA.InstantiableDec (_, DA.NormalDec(r, SOME (sList), _))), k) = 
			       (case (List.find (fn x => isEqual(x, nameOpt)) sList)
				  of NONE => findParameters(ReconG, k+1)
				   | SOME _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Cannot extend an already weakenable function!"))
				)

		   | findParameters (I.Decl(ReconG, DA.InstantiableDec _ (* no name *)), k) = findParameters(ReconG, k+1)
		   | findParameters (I.Decl(ReconG, DA.PatternVariable (s, _)), k) = if isEqual(s, nameOpt) then [] 
										     else findParameters(ReconG, k) (* count does not go up *)
		   | findParameters (I.Null, k) = [] (* we extend through everything in ReconG *)

		 val allParams = findParameters(ReconG, 1)

		 val lastParam = case allParams
		             of [] => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Nothing to extend.  Invalid use of 'with'"))
			      | (x::_) => x

		 fun getLast [] = raise Domain
		   | getLast [x] = x
		   | getLast (x::xs) = getLast xs

		 val firstParam = getLast allParams

		 val sizeG2b = lastParam - 1
		 val sizeG2a = firstParam - sizeG2b

		 (* G = GB,G2a, G2b *)
		 (* IMPORTANT not to use D'.popCtx! as we ignore some parts of this context *)
		 val GBG2a = DA.popCtx(sizeG2b, ReconG)
		 val GB = DA.popCtx(sizeG2a+sizeG2b, ReconG)

		 val (job1, f1)  = convertExp2Temp(smartInj, G, GB, E, Tresult)
		 val job1' = ReconTerm.jpopctx(sizeG2a+sizeG2b, job1)
		 fun f1' (ReconTerm.JPopCtx(_, x)) = f1 x
		   | f1' _ = raise Domain

		 fun caseF C =
	          let 
		    val oldTables = saveApxTables() (* Scoping the patvars here IS NOT necessary here as there should
						     * NOT be any pattern variables *)
		    val (job, f) = convertCase2Temp(isSugar, smartInj, G, GBG2a, I.Null, C, Tresult)
		    val _ = restoreApxTables oldTables

		    fun f' (ReconTerm.JPopCtx(_, jobResult)) = f jobResult
		      | f' _ = raise Domain
		  in
		    (* Scope the variables introduced in C so it only applies to that branch *)
		    (ReconTerm.jpopctx(sizeG2b, ReconTerm.jscopeVars job), f')
		  end

		 val jobFunList = map caseF Clist 
		   
		 fun getJobList [] = ReconTerm.jnothing
		   | getJobList ((job,_)::xs) = ReconTerm.jand(job, getJobList xs)

		 val caseJobs = getJobList jobFunList

		 fun f' ((_,f1)::xs) (ReconTerm.JAnd(jobResult1, jobResult2)) = (f1 jobResult1) :: (f' xs jobResult2)
		   | f' [] (ReconTerm.JNothing) = []
		   | f' _ _ = raise Domain



		 fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
		        let
			  val E' = f1' jobResult1		    
			  val Clist' = f' jobFunList jobResult2
			in
			  DI.ExtendFunWith(r, E', Clist', sizeG2a, sizeG2b, isSugar, NONE)
			end
		   | f _ = raise Domain
	       in
		 (ReconTerm.jand(job1', caseJobs), f)
	       end



   and convertFunList2Temp (smartInj, G, ReconG, r, funList, Tresult) =
          let
	    val oldTables = saveApxTables() (* Scoping the patvars here is not necessary, but can't hurt *)
	                                     (* ADAM:  So we should remove this.. but test first... *)
	    val (Dapprox, job, f) = convertFunList2Temp'(smartInj, G, ReconG, r, funList, Tresult)
	    val _ = restoreApxTables oldTables


	    (* Check that we only have fixpoints of functions!.. *)
	    fun isFun F = isFunW (DA.whnfF F)
	    and isFunW (DA.All _) = true
	      | isFunW (DA.Nabla (_, _, F)) = isFun F
	      | isFunW _ = false
	       
	    val _ = (case (DA.whnfT Tresult)
	           of (DA.Meta(_, DA.FormList Flist)) 
		      => let 
			   fun checkFun F = 
			     if (isFun F) then () else
				 let
				   val firstLine = "Expected Function Type\n"
				   val secondLine = "  Actual Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tresult))
				   val s= firstLine ^ secondLine
				 in 
				   raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), s))
				 end
			   val _ = map checkFun Flist
			 in
			   ()
			 end

		    | (DA.Meta(_, F)) => if (isFun F) then () else 
			     let
			       val firstLine = "Expected Function Type\n"
			       val secondLine = "  Actual Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tresult))
			       val s= firstLine ^ secondLine
			     in 
			       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), s))
			     end

		    | _ =>   let
			       val firstLine = "Expected Function Type\n"
			       val secondLine = "  Actual Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tresult))
			       val s= firstLine ^ secondLine
			     in 
			       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), s))
			     end)


	  in
	    (Dapprox, ReconTerm.jscopeVars job, f)
	  end

   and convertFunList2Temp' (smartInj, G, ReconG, r, funList, Tresult) =
           let
	     (* We need to scope the FVars to just this dec for implicit arguments *)
	     fun convertDecWithScope (_,D,_) = 
	          let
		    val (Drecon, Dapprox, job, f) = convertNormalDec2Temp(G, ReconG, D)
		    val _ = (case D
			       of (D.NormalDec (r, _, D.LF _)) => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Fixpoint can only take meta-level decs!"))
			        | _ => ()
				 )
		  in
		    (Drecon, Dapprox, ReconTerm.jscopeVars job, f)
		  end
		    
	     val decList = map convertDecWithScope funList

	     fun decListString [(_, DA.NormalDec(_, SOME [s], _), _, _)] = [s]
	       | decListString ((_, DA.NormalDec(_, SOME [s], _), _, _) :: decs) = s :: (decListString decs)
	       | decListString _ = raise Domain (* badly formed fixpoint *)

	     fun decListFormulas [(_, DA.NormalDec(_, _, DA.Meta(_, F)), _, _)] = [F]
	       | decListFormulas ((_, DA.NormalDec(_, _, DA.Meta(_, F)), _, _) :: decs) = F :: (decListFormulas decs)
	       | decListFormulas _ = raise Domain (* badly formed fixpoint *)


	     fun decListFormula [F] = F
	       | decListFormula Flist = DA.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist

	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, F))

	     val D = DA.NormalDec (r, SOME (decListString decList), DA.Meta(r, F))
	     val ReconG' = I.Decl(ReconG, DA.InstantiableDec (r, D))
	       
	     fun pairFormula ([], []) = []
	       | pairFormula ((_, _, E)::fList, F::formList) = (E, F) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)

	     val expList = map (fn (E,F) => convertExp2Temp(smartInj, G, ReconG', E, DA.Meta(r, F))) expFormList

	     fun fDecs ((_, _, jobD, fD)::decList) (ReconTerm.JAnd(jobResult1, jobResult2)) =
	             let
		       val D1 = fD (jobResult1, I.NDec)
		       val restDecs = fDecs decList jobResult2
		     in
		       D1::restDecs
		     end
	       | fDecs nil (ReconTerm.JNothing) = []
	       | fDecs _ _ = raise Domain

	     fun getDecJob ((_, _, jobD, fD)::decList) = ReconTerm.jand(jobD, getDecJob decList)
	       | getDecJob nil = ReconTerm.jnothing


	     fun fExps ((job, f)::expList) (ReconTerm.JAnd(jobResult1, jobResult2)) =
	            let
		      val E = f jobResult1
		      val restE = fExps expList jobResult2
		    in
		      E :: restE
		    end
	       | fExps nil (ReconTerm.JNothing) = []
	       | fExps _ _ = raise Domain

	     fun getExpJob ((job, f) :: expList) = ReconTerm.jand(job, getExpJob expList)
	       | getExpJob nil = ReconTerm.jnothing

	     (* Function to calculate what the decs are *)
	     val decJob = getDecJob decList
	     val fDec = fDecs decList

	     (* Function to calculate what the Es are *)
	     val expJob = getExpJob expList
	     val fExp = fExps expList

	     fun fMain (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(_, jobResult2))) =
	            let
		      val decs = fDec jobResult1
		      val exps = fExp jobResult2
			
		      fun makeList ((r,_,_)::funList) (D::decs) (E::exps) = (r,D,E) :: (makeList funList decs exps)
			| makeList [] [] [] = []
			| makeList _ _ _ = raise Domain 
		    in
		      makeList funList decs exps
		    end
	       | fMain _ = raise Domain

	     val Drecon = ReconTerm.ndec (NONE, r)
	     val jobMain = ReconTerm.jand(decJob, ReconTerm.jwithctx(I.Decl(I.Null, Drecon),expJob))
	      
	   in
	     (D, jobMain, fMain)
	   end

   and convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternString (r, s), Tresult) = 
           let
	     val (ReconGlocal', E, T) = convertPatVarString(smartInj, G, ReconGglobal, ReconGlocal, r, s)
	     val _ = unifyApxTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", Tresult, T)

	     fun f (ReconTerm.JNothing) = E
	       | f _ = raise Domain
	   in
	     (ReconGlocal', (ReconTerm.jnothing, f))
	   end


     | convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternOmitted r, Tresult) = 	       
	   (* We now do a primitive raising similar to the LF handling of EVars (but much simpler)
	    * If we have something of the form "{<x>}{<u>} _" then the pattern variable we fill in
	    * is "E \x \u" so that it may depend on all parameters in the local context.
	    *)
	   let
	     val Fresult = DA.FVar(r, ref NONE)
	     val _ = unifyApxTypes(smartInj, r, "Omitted variable is of incompatible type", Tresult, DA.Meta(r, Fresult))
	     val name = getFreshName()
	     val E = DI.PatVar (r, name, name) (* NO NEED TO ADD THIS TO TABLE
						* OR to ReconGlocal
						* as it will never occur again...
						*)


	     (* We now build a newTerm of the form E \x1 \x2 \x3 (for all new params in ReconGlocal)
	      * WARNING:
	      * The "approximate" type of newTerm will always be correct.
	      * However, there is a chance we will run into a problem with dependencies and intermixed 
	      * epsilons between news.
	      *
	      * Imagine the following scenario:
	      * new x. eps y. new u (e => ...)
	      * Now the type of e : T[x,y,u]
	      * But if we replace "e" with (e' \x \y)
	      * then the type of e' is Nab{x}Nab{u} T[x,u]
	      * 
	      * So if the type actually depended on the eps "e", this conversion will not suffice.
	      *
	      * EASY FIX for now:  Disallow situations of this case by raising an error here.
	      * This will rarely (if ever) come up as generated patterns will never have that form
	      * and there is no reason to specify patterns that way.
	      * SUGGESTED FUTURE UPDATE:  change grammar to ONLY allow cases of the following form
	      *        pop xs.. (eps ys. new us. (pat => e))
	      *
	      *  Then this error will never come up.
	      *)


	     fun buildPops(I.Null, E, ctr) = E
	       | buildPops(I.Decl(G, DA.InstantiableDec _), E, ctr) = buildPops(G, E, ctr+1)
	       | buildPops(I.Decl(G, DA.PatternVariable _), E, ctr) = buildPops(G, E, ctr) (* do not increase ctr *)
	       | buildPops(I.Decl(G, DA.NonInstantiableDec (r, D as DA.NewDecLF _)), E, ctr) = 
	                             (if (ctr = 1) then
				       buildPops(G, DI.Pop(r, ctr, E), 1 (* reset ctr *) )
				     else
					raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "We do not allow omission with intermixed pattern variables and news.  Create your own pattern (e.g. use a pattern variable)."))
					)
	       | buildPops(I.Decl(G, DA.NonInstantiableDec (r, D as DA.NewDecWorld _)), E, ctr) = buildPops(G, E, ctr+1)


	     val newTerm = buildPops(ReconGlocal, E, 1)



	     fun f (ReconTerm.JNothing) = newTerm
	       | f _ = raise Domain

	   in
	     (ReconGlocal (* no need to update *),
	      (ReconTerm.jnothing, f))
	   end

     | convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternQuote (r, LFterm), Tresult) =
	   let
	     val A = Approx.newCVar()
	     val t = tokensToTerm (PrintDelphinExt.lfexpToTokens LFterm)
	     val I = if smartInj then DA.InjVar(ref NONE) (* We don't know if it is LF or Meta *)
	                    else DA.InjLF (* It is LF *)
	                   
	     val isP = D'.newPVar()
	     val _ = unifyApxTypes(smartInj, r, "Incompatible type", Tresult, DA.SmartInj(r, A, I, isP))

	     val job = ReconTerm.jofApx (t, A)

	     fun f (ReconTerm.JOf ((U, _), (V,_), _)) = DI.Quote (r, U, V, I, isP)
	       | f _ = raise Domain
	   in
	     (ReconGlocal, (job, f))
	   end

     | convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternUnit r, Tresult) =	  
	   let
	     val _ = unifyApxTypes(smartInj, r, "() has incompatible type", Tresult, DA.Meta(r, DA.Top r))

	     fun f (ReconTerm.JNothing) = DI.Unit r
	       | f _ = raise Domain
	   in
	     (ReconGlocal, (ReconTerm.jnothing, f))
	   end


     | convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternNew (r, D, E), Tresult) = 
	  let
	    val (Drecon, Dapprox, job1, f1) = convertNewDec2Temp (G, I.mergeCtx(ReconGglobal, ReconGlocal), D)
	    val F = DA.FVar(r, ref NONE)
	    val inferredType = DA.Meta(r, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type Mismatch", Tresult, inferredType)
	    val ReconGlocal' = I.Decl(ReconGlocal, DA.NonInstantiableDec (r, Dapprox))
	    val (ReconGlocal', (job2, f2)) = convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal', E, DA.Meta(r, F))

	    fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx (I.Decl(_, D), jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val E'' = f2 jobResult2
		  in
		    DI.New(r, D'', E'')
		  end
	      | f _ = raise Domain

	    (* To get the correct ReconGlocal, we need to remove Dapprox.
	     * Therefore, we will move the new pattern variables to the left of Dapprox before removing it.  
	     * This reflects what will happen in the real *abstraction*, as all pattern variables are declared to the left of the pattern.
	     * Note that Dapprox will be the FIRST NonInstantiableDec encountered.
	     *)
	    fun removeDapprox (I.Decl(ReconG, DA.NonInstantiableDec _ (* Dapprox *))) = ReconG
	      | removeDapprox (I.Decl(ReconG, D as DA.PatternVariable _)) = I.Decl(removeDapprox ReconG, D)
	      | removeDapprox (I.Decl(ReconG, DA.InstantiableDec _)) = raise Domain (* impossible *)
	      | removeDapprox I.Null = raise Domain (* impossible *)

	  in
	    (removeDapprox ReconGlocal', (ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), job2)) , f))
	  end


     | convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternPair (r, E1, E2), Tresult) = 
	  let
	     val F = DA.FVar(r, ref NONE)
	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, F))
		       
	     val (ReconGlocal', firstType) = inferPatTypeApx (smartInj, G,ReconGglobal, ReconGlocal,  E1)
	     val D = DA.NormalDec(r, NONE, firstType)
	     val secondF = DA.FVar(r, ref NONE)
	     val pairF = DA.Exists(r, D, secondF)
	     val pairType = DA.Meta(r, pairF)

	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, pairType)

	     val (ReconGlocal', (job1, f1))  = convertPattern2Temp(smartInj, G, ReconGglobal, ReconGlocal',  E1, firstType)
	     val (ReconGlocal', (job2, f2))  = convertPattern2Temp(smartInj, G, ReconGglobal, ReconGlocal',  E2, DA.Meta(r, secondF))
	    

	     fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val E1'' = f1 jobResult1
		    val E2'' = f2 jobResult2
		  in
		    DI.Pair(r, E1'', E2'')
		  end
	       | f _ = raise Domain

	  in
	    (ReconGlocal', (ReconTerm.jand(job1, job2), f))
	  end

     | convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternPop (r, popname, E), Tresult) = 
	  let

	    fun getRest(Glocal, 0) = I.Null
	      | getRest(I.Decl(Glocal, D as DA.NonInstantiableDec _), ctr) = I.Decl(getRest(Glocal, ctr-1), D)
	      | getRest(I.Decl(Glocal, D as DA.InstantiableDec _), ctr) = I.Decl(getRest(Glocal, ctr-1), D)
	      | getRest(I.Decl(Glocal, D as DA.PatternVariable _), ctr) = I.Decl(getRest(Glocal, ctr), D) (* do not decrease ctr *)
	      | getRest(I.Null, _ (* not 0 *)) = raise Domain (* impossible *)
		
	    (* NOTE:  We only allow Pop up to end of ReconGlocal
	     *)
	    val (i, Dapprox) = lookupNewString (r, ReconGlocal, popname, 1)
	    val ReconGlocal' = DA.popCtx(i, ReconGlocal)
	    val Grest' = getRest(ReconGlocal, i)

	    val F = DA.FVar (r, ref NONE)
	    val T = DA.Meta(r, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, F))

	    val (ReconGlocal', (job1, f1)) = convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal', E, T)

	    fun f (ReconTerm.JPopCtx(_, jobResult)) = DI.Pop(r, i, f1 jobResult)
	      | f _ = raise Domain
	  in
	    (I.mergeCtx(ReconGlocal', Grest'), (ReconTerm.jpopctx(i, job1), f))
	  end


     | convertPattern2Temp (smartInj, G, ReconGglobal, ReconGlocal, D.PatternAscribe (r, E, T), Tresult) = 
	  let
	    val (Tapx, job1, f1) = convertTypes2Temp(G, I.mergeCtx(ReconGglobal, ReconGlocal), T)
	    val _ = unifyApxTypes (smartInj, r, "Type Ascription doesn't match", Tresult, Tapx)
	    val (ReconGlocal', (job2, f2)) = convertPattern2Temp(smartInj, G, ReconGglobal, ReconGlocal, E, Tresult)

	    fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val T'' = f1 jobResult1
		    val E'' = f2 jobResult2
		  in
		    DI.TypeAscribe(r, E'', T'')
		  end
	      | f _ = raise Domain
	  in
	    (ReconGlocal', (ReconTerm.jand(job1,job2) , f))
	  end



   and convertCase2Temp (isSugar, smartInj, G, ReconGglobal, ReconGlocal, D.Eps(r, D, C), Tresult) =
          let
	    val (Drecon, Dapprox, job1, f1) = convertNormalDec2Temp (G, I.mergeCtx(ReconGglobal, ReconGlocal), D)
	    val (job2, f2) = convertCase2Temp (isSugar, smartInj, G, ReconGglobal, I.Decl(ReconGlocal, DA.InstantiableDec(r, Dapprox)), C, Tresult)

	    fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(I.Decl(_, D),jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val C'' = f2 jobResult2
		  in
		    DI.Eps(r, D'', C'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon),job2)) , f)
	  end

     | convertCase2Temp (isSugar, smartInj, G, ReconGglobal, ReconGlocal, D.NewC(r, D, C), Tresult) =
	  let
	    val (Drecon, Dapprox, job1, f1) = convertNewDec2Temp (G, I.mergeCtx(ReconGglobal, ReconGlocal), D)
	    val F = DA.FVar(r, ref NONE)
	    val inferredType = DA.Meta(r, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type Mismatch", Tresult, inferredType)

	    val (job2, f2) = convertCase2Temp (isSugar, smartInj, G, ReconGglobal, I.Decl(ReconGlocal, DA.NonInstantiableDec (r, Dapprox)), C, DA.Meta(r, F))

	    fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx (I.Decl(_, D), jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val C'' = f2 jobResult2
		  in
		    DI.NewC (r, D'', C'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), job2)) , f)
	  end


     | convertCase2Temp (isSugar, smartInj, G, ReconGglobal, ReconGlocal, D.PopC(r, s, C), Tresult) =
	  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "We no longer support different pops over different cases and cannot automatically convert this one... fix manually."))

     | convertCase2Temp (isSugar, smartInj, G, ReconGglocal, ReconGlocal, D.Match(_ (* = isSugar *), r, [], E2), Tresult) = raise Domain 
											(* can only exists from conversion from internal to external
											 * as it may be completely implicit 
											 *) 
     | convertCase2Temp (isSugar, smartInj, G, ReconGglobal, ReconGlocal, D.Match(_ (* = isSugar *), r, pats, E2), Tresult) =
	  let
	    val F = case Tresult
	            of DA.Meta(_, F) => F
		     | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Delphin Function cannot have LF type"))
		      

	    fun inferPats (ReconG', []) = (ReconG', [])
	      | inferPats (ReconG', E1::pats) = 
	                let
			  val (ReconG', T') = inferPatTypeApx(smartInj, G, ReconGglobal, ReconG', E1)
			  val (ReconG', pats') = inferPats (ReconG', pats)
			in
			  (ReconG', T' :: pats')
			end

	    val (ReconGlocal', argsTypeApx) = inferPats(ReconGlocal, pats)

	    val F = makeForAllApprox(isSugar, smartInj, r, argsTypeApx, F) (* makes F a Forall ... *)

	    val _ = unifyApxTypes(smartInj, r, "Match has incompatible type", Tresult, DA.Meta(r, F))

	    fun getPatJobs (ReconG', pats, F) = getPatJobsW (ReconG', pats, DA.whnfF F)
	    and getPatJobsW (ReconG', pats, DA.All(r', (D'.Implicit, _)::Ds, F)) = getPatJobs(ReconG', pats, DA.All(r', Ds, F))
	      | getPatJobsW (ReconG', (E::Es), DA.All(r', (D'.Visible, DA.NormalDec (_, _, T))::Ds, F)) = 
	               let
			 val (ReconG', E') = convertPattern2Temp(smartInj, G, ReconGglobal, ReconG', E, T)
			 val (ReconG', Es', Frest) = getPatJobs(ReconG', Es, DA.All(r', Ds, F))
		       in
			 (ReconG', E'::Es', Frest)
		       end
	      | getPatJobsW (ReconG', [], DA.All(_, [], F)) = (ReconG', [], F)
	      | getPatJobsW (ReconG', pats, DA.All(_, [], F)) = getPatJobs(ReconG', pats, F)
	      | getPatJobsW (ReconG', pats, F) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Pats"))

	    fun fPats ((jobP, fP) :: xs) (ReconTerm.JAnd(jobResult1, jobResult2)) =
	               let
			 val E' = fP jobResult1
			 val rest = fPats xs jobResult2
		       in
			 (D'.Visible, E') :: rest
		       end
	      | fPats nil (ReconTerm.JNothing) = []
	      | fPats _ _ = raise Domain

	    fun getJob ((jobP, fP) :: xs) = ReconTerm.jand(jobP, getJob xs)
	      | getJob [] = ReconTerm.jnothing

	    val (ReconGlocal', patJobs, funResult) = getPatJobs (ReconGlocal', pats, F)
	    val (job1, f1) = (getJob patJobs, fPats patJobs)
	       
	    val (job2, f2) = convertExp2Temp (smartInj, G, I.mergeCtx(ReconGglobal, ReconGlocal'), E2, DA.Meta(r, funResult))

	    fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val pats'' = f1 jobResult1
		    val E2'' = f2 jobResult2
		  in
		    DI.Match(r, pats'', E2'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1,job2) , f)
	  end


  (* Here we build up LF Reconstruction job and send it to LF *)
   fun lfReconstruction (G, masterJob, f, r) =
            let
	      val _ = ReconTerm.resetErrors(!filename)
	      val answerJob = ReconTerm.reconWithCtx (D'.coerceCtx G, masterJob)
	      val _ = ReconTerm.checkErrors(r)
	    in
	      f answerJob
	    end
		
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* 
    * Second Phase/Stage:  Update the type information in DelphinIntermediateSyntax before we call abstraction
    * The first phase could only verify that the "approximate types" are correct, we now need to verify
    * that the exact types are correct.
    * It is IMPORTANT to do this BEFORE abstracting pattern variables, as extra EVars would be generated
    * which go away if the type is specified.
    * However, we deduce the implicit types here.
    *
    * Note:  We also do subordination checks here to make sure that no parameters
    *        are created that violate the global subordination relation!
    *
    *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)

   (* Routines to check subordination..
    * Notice that this routines take Declarations/Types
    * Also note that we do NOT need to handle EVars because there are no "type" EVars, 
    *   i.e. all EVars are of the form M : A.
    *)
   fun checkSubordWorld (r, D'.Anything) = ()
     | checkSubordWorld (r, D'.VarList []) = ()
     | checkSubordWorld (r, D'.VarList ((_, V) :: vars)) = 
            let
	      val _ =  Subordinate.respects (V, I.id)
		handle Subordinate.Error s => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), s))
	    in
	      checkSubordWorld (r, D'.VarList vars)
	    end

   fun checkSubordNewDec (DI.NewDecLF (r, _, V)) = (Subordinate.respects (V, I.id)
						    handle Subordinate.Error s => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), s)))
		  
     | checkSubordNewDec (DI.NewDecWorld (r, _, W)) = checkSubordWorld (r, W)
 

   (* Here we check "local" parameters, i.e. if an LF term has type A -> B, then A is a local parameter *)
   fun checkSubordQuote(r, (A,s)) = checkSubordQuoteW (r, Whnf.whnf (A, s))
   and checkSubordQuoteW(r, (I.Pi ((D, _), A), s)) = 
          (case D
	     of I.Dec (_, U) => 
	            let
		      val _ = Subordinate.respects (U, s)
			handle Subordinate.Error s => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), s))
		    in
		      checkSubordQuote (r, (A, I.dot1 s))
		    end

	      | _ =>  (checkSubordQuote (r, (A, I.dot1 s)))
	    )
     | checkSubordQuoteW (r, (V as I.Root (I.Def _, _), s)) =
	       checkSubordQuote(r, (Whnf.expandDef(V, s)))

     | checkSubordQuoteW _ = ()




   fun inferType (G, DI.Quote (r, M, A, DA.InjLF, isP)) = D'.LF(isP, A)

     | inferType (G, DI.Quote (r, M, A, DA.InjMeta, isP)) =  
           D'.Meta(D'.Exists(D'.NormalDec (NONE, D'.LF(isP, A)), D'.Top))

     | inferType (G, DI.Quote (r, M, A, DA.InjVar (ref (SOME I)), isP)) = inferType (G, DI.Quote (r, M, A, I, isP))
     | inferType (G, DI.Quote (region, M, A, DA.InjVar (r as ref NONE), isP)) = 
	      ( (* It can be either LF or Meta, so we pick Meta *)
	       r := SOME (DA.InjMeta) ; 
	       inferType (G, DI.Quote (region, M, A, DA.InjMeta, isP)))



     | inferType (G, DI.VarInt (r, i)) = 
	     let
	       val (_, T) = lookupInt(r, i, G, i)
	     in
	       removeCoverageInfo (T)
	     end

     | inferType (G, DI.TypeAscribe (_, E, _)) = inferType (G, E)

     | inferType (G, _) = 
	     D'.Meta(D'.newFVar(D'.coerceCtx G))
         
   
   (* makeForAll(isSugar, pats,F) = F' 
    * Here we make sure F is a forall type suitable for the given list of patterns 
    * It is necessary to return a new F' that has the form D'.All _
    * Even though we unify it with F, it is no longer safe to use F as it may be delayed due 
    * to constraints!
    * Note that if isSugar is set true, then it will make it a curried function 
    * as it is syntactic sugar that will be expanded out later to represent that.
    *)
   fun makeForAll(isSugar, smartInj, r, G, pats, F) = makeForAllW(isSugar, smartInj, r, G, pats, D'.whnfF F)
   and makeForAllW(isSugar, smartInj, r, G, _, F as D'.All _) = F (* nothing to do.. *)
     | makeForAllW(isSugar, smartInj, r, Ginit, (vis1,E1)::pats, F) =
              let
		val arg1 = inferType(Ginit, E1)		  
		val D1 = D'.NormalDec(NONE, arg1)

		fun eraseIndicesType (G, D'.LF (isP, A)) = 
                       let
			 val (V, U) = Approx.classToApx A
			 val A' = Approx.apxToClass (G, V, U (* Approx.Type *), true)
		       in 
			 D'.LF (isP, A')
		       end
		  | eraseIndicesType (G, D'.Meta (F)) = D'.Meta (D'.newFVar(G))


		fun getTypes(G, Ds, []) = (G, Ds)
		  | getTypes(G, Ds, ((vis,E)::pats)) =
		            let
			      val argI = inferType(Ginit, E) (* E makes sense in Ginit! *)
			      (* The dependencies may not be correct... (as it was refined by previous patterns),
			       * so we need to erase them and put logic variables in its place.
			       *)
			      val argII = eraseIndicesType(D'.coerceCtx G, argI)
			      val Di = D'.NormalDec(NONE, argII)
			    in
			      getTypes(I.Decl(G, D'.InstantiableDec Di), (Ds@[(vis, Di)]), pats)
			    end

		val (G', Ds) = getTypes(I.Decl(Ginit, D'.InstantiableDec D1), [(vis1, D1)], pats)
		val F' = D'.newFVar(D'.coerceCtx G')

		fun createForAll(false, Ds, Fresult) = D'.All(Ds, Fresult)
		  | createForAll(true (* isSugar *), D::Ds, Fresult) = D'.All([D], createForAll(true, Ds, Fresult))
		  | createForAll(true, [], Fresult) = Fresult

		val Fresult = createForAll(isSugar, Ds, F')
		val _ = unifyTypes(smartInj, r, "Function has incompatible type", Ginit, D'.Meta(F), D'.Meta(Fresult))
	      in
		Fresult
	      end
     | makeForAllW(isSugar, smartInj, r, G, [], F) = raise Domain






   fun convertNormalDec (G, DI.NormalDec(r, sO, T)) = 
              let
		fun toList NONE = NONE
		  | toList (SOME s) = SOME [s]
		  
		val sLO = toList sO
		val T' = convertTypes(G, T)
	      in
		D'.NormalDec (sLO, T')
	      end

   and convertNewDec (G, DI.NewDecLF (r, sO, A)) =  D'.NewDecLF(sO, A)
     | convertNewDec (G, DI.NewDecWorld (r, sO, W)) = D'.NewDecWorld(sO, W)


   and convertTypes (G, DI.LF(r, isP, A)) = 
                     let
		       val _ = checkSubordQuote(r, (A, I.id)) (* checks local parameters.. *)
		     in 
		       D'.LF(isP, A)
		     end
     | convertTypes (G, DI.Meta (_, F)) = D'.Meta(convertFormula(G, F))


   and convertFormula (G, DI.Top _) = D'.Top
     | convertFormula (G, DI.All(r, Ds, F)) = 
            let
	      val Ds' = map (fn (vis, D) => (vis, convertNormalDec (G, D))) Ds
	      fun addDs (G, []) = G
		| addDs (G, (_, D)::Ds) = addDs(I.Decl(G, D'.InstantiableDec D), Ds)

	      val F' = convertFormula(addDs (G, Ds'), F)
	    in
	      D'.All(Ds', F')
	    end
     | convertFormula (G, DI.Exists(r, D, F)) = 
            let
	      val D' = convertNormalDec (G, D)
	      val F' = convertFormula(I.Decl(G, D'.InstantiableDec D'), F)
	    in
	      D'.Exists(D', F')
	    end
     | convertFormula (G, DI.Nabla(r, D, F)) = 
            let
	      val D' = convertNewDec (G, D)
	      val _ = checkSubordNewDec D
	      val F' = convertFormula(I.Decl(G, D'.NonInstantiableDec D'), F)
	    in
	      D'.Nabla(D', F')
	    end
     | convertFormula (G, DI.FormulaString (r, name)) = 
	    let
	      fun findSig (s:string, []) = NONE
		| findSig (s, (s', _, F)::mSig) = if (s = s') then (SOME F) else findSig(s, mSig)
	    in
	      case (findSig (name, !(!metaSigRef)))
		of SOME F => F (* F is closed and EVar free, so it never needs to  undergo any shifts *)
		 | NONE => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type Alias " ^ name ^ " not found!"))
	    end
     | convertFormula (G, DI.OmittedFormula _) = D'.newFVar(D'.coerceCtx G)	  

   (* ***************************************************************************************************** *)
   (* updateExp updates LF EVars in the approximate types                                                   *)
   (* it also handles the "implicit" arguments                                                              *)
   (* As we perform abstraction on the types of inner functions, we need to
    * pass around a collection of Vars so we know what should and should not be abstracted   
    *)
   (* ***************************************************************************************************** *)

	    
   fun updateExp (smartInj, G, E as DI.VarInt (r, i), Tresult, K) =
         let
	   val (name, T) = lookupInt(r, i, G, i)
	   val T = removeCoverageInfo (T)

	   val s = case name of 
	            NONE => "#" ^ (Int.toString i)
		   | SOME s => s
	   val _ = unifyTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", G, Tresult, T)
	 in
	   (E, K)
	 end

     | updateExp (smartInj, G, E as DI.Quote (r, M, A, DA.InjLF, isP), Tresult, K) =
		     let	     
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.LF(isP, A))
		       val K' = DelphinAbstract.LFcollectExp(r, NONE, (A, I.id), DelphinAbstract.LFcollectExp (r, NONE, (M, I.id), K, true), true)

		       val _ = checkSubordQuote(r, (A, I.id)) (* checks local parameters.. *)
		     in
		       (E, K')
		     end


     | updateExp (smartInj, G, E as DI.Quote (r, M, A, DA.InjMeta, isP), Tresult, K) =
	             let
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(isP, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(F))
		       val K' = DelphinAbstract.LFcollectExp(r, NONE, (A, I.id), DelphinAbstract.LFcollectExp (r, NONE, (M, I.id), K, true), true)

		       val _ = checkSubordQuote(r, (A, I.id)) (* checks local parameters.. *)
		     in
		       (E, K')
		     end



     | updateExp (smartInj, G, DI.Quote (r, M, A, DA.InjVar(ref (SOME I)), isP), Tresult, K) = updateExp (smartInj, G, DI.Quote(r, M, A, I, isP), Tresult, K)
     | updateExp (smartInj, G, DI.Quote (region, M, A, DA.InjVar(r as ref NONE), isP), Tresult, K) =
	     ( (* It can be either LF or Meta, so we pick Meta *)
	      r := SOME DA.InjMeta ; 
	      updateExp(smartInj, G, DI.Quote(region, M, A, DA.InjMeta, isP), Tresult, K))
	      

     | updateExp (smartInj, G, E as DI.Unit r, Tresult, K) = 
	   let
	     val _ = unifyTypes(smartInj, r, "() has incompatible type", G, Tresult, D'.Meta(D'.Top))
	   in
	     (E, K)
	   end

     | updateExp (smartInj, G, DI.Lam (isSugar, r, Clist, Fopt), Tresult, K) =
	   let
	     val F = case Fopt 
	             of SOME F => F
		      | _ => D'.newFVar(D'.coerceCtx G)

	     val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))
	   in
	     if not(isSugar) andalso (isAllImplicitF F) then
	       let
		 val oldTables = saveExactTables() (* also saves patVarCtx *)
		 val _ = patVarCtx := G
		 val Cimplicit = DI.Match(r, [], DI.Lam(false, r, Clist, NONE))
		 val (C', K') = updateCase(isSugar, smartInj, G, Cimplicit, Tresult, K)
		 val _ = restoreExactTables oldTables (* also restores patVarCtx *)
	       in
		 (DI.Lam (false, r, [C'], SOME F), K (* initial K *))
	       end
	     else
	       let
		 fun caseF C =
		    let
		      val oldTables = saveExactTables() (* also saves patVarCtx *)
		      val _ = patVarCtx := G
		      val (C', K') = updateCase(isSugar, smartInj, G, C, Tresult, K)
		      val _ = restoreExactTables oldTables (* also restores patVarCtx *)
		    in
		      C'
		    end
		  
		 val Clist' = map caseF Clist
	       in
		 (DI.Lam (isSugar, r, Clist', SOME F), K (* initial K *) )
	       end
	   end


     | updateExp (smartInj, G, DI.New(r, D, E), Tresult, K) =
	   let
	     val D' = convertNewDec(G, D)
	     val _ = checkSubordNewDec D 
	     val G' = I.Decl(G, D'.NonInstantiableDec D')
	     val newResult = D'.newFVar(D'.coerceCtx G')
	     val nablaType = D'.Meta(D'.Nabla(D', newResult))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, nablaType)

	     val K1 = DelphinAbstract.collectDelNewDec (NONE, D, K, true)
	     val (E', K2) = updateExp(smartInj, G', E, D'.Meta(newResult), K1)
	   in
	     (DI.New(r, D, E'), K2)
	   end


     | updateExp (smartInj, G, DI.App(r, E1, args), Tresult, K) = 
	   let
	     val Tstart = D'.Meta(D'.newFVar(D'.coerceCtx G))
	     val (E1', K) = updateExp(smartInj, G, E1, Tstart, K)
	     val (E1', Tfun, K) = applyImplicit(G, E1', Tstart, K)

	     val funF = case Tfun
	                of (D'.Meta(F)) => F
			 | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Expected function type, but got LF"))

	     fun processArgs (args, F, K) = processArgsW(args, D'.whnfF F, K)
	     and processArgsW (args, D'.All((D'.Implicit, D'.NormalDec (_, D'.LF(isP, A)))::Ds, F), K) =
	          let
		    val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
		    val Q = DI.Quote(r, X, A, DA.InjLF, isP)
		    val _ = checkSubordQuote(r, (A, I.id)) (* checks local parameters.. *)
		    val K' = DelphinAbstract.LFcollectExp(r, NONE, (A, I.id), DelphinAbstract.LFcollectExp (r, NONE, (X, I.id), K, true), true)
		    val t' = I.Dot(coerceExp Q, I.id)
		    val (args', Frest, K'') = processArgs(args, D'.FClo(D'.All(Ds, F), t'), K')
		  in
		    ((D'.Implicit, Q) :: args', Frest, K'')
		  end
		
	       | processArgsW ((_ (* Visible *),E2)::args, D'.All((D'.Visible, D'.NormalDec (_, T))::Ds, F), K) =
		  let
		    (* If we have a function which only has implicit args, then it may need
		     * to be filled in as an argument.  For example, imagine:
		     * D-- val x : <ev_s>
		     * D-- x @ <ev_z>
		     * This is an example where "x" will be a meta-level function only with implicit
		     * arguments.
		     *)

		    (* T specifies the desired type, but the actual type of E2 may 
		     * be prefaced with a completely implicit function.
		     *)
		    
		    val argType = inferType(G, E2)
		  in
		    if isAllImplicitT argType then
		           let
			     val (E2', K') = updateExp(smartInj, G, E2, argType, K) 
			     val (E2', T', K') = applyImplicit(G, E2', argType, K')
			     val _ = unifyTypes(smartInj, r, "Type mismatch", G, T, T')
			     val t' = I.Dot (coerceExp E2', I.id)
			     val (args', Frest, K'') = processArgs(args, D'.FClo(D'.All(Ds, F), t'), K')
			   in
			     ((D'.Visible, E2') :: args', Frest, K'')
			   end
		    else
		           let
			     val (E2', K') = updateExp(smartInj, G, E2, T, K) 
			     val t' = I.Dot (coerceExp E2', I.id)
			     val (args', Frest, K'') = processArgs(args, D'.FClo(D'.All(Ds, F), t'), K')
			   in
			     ((D'.Visible, E2') :: args', Frest, K'')
			   end
		  end
	       | processArgsW ([], D'.All([], F), K) = ([], F, K)
	       | processArgsW (args, D'.All([], F), K) = 
		  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected remaining args"))
	       | processArgsW _ =  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Args"))

						   
		    
	     val funF = makeForAll(false, smartInj, r, G, args, funF) (* makes funF a Forall ... *)
	     val (args', Frest, K2) = processArgs (args, funF, K)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(Frest))
	   in
	     (DI.App(r, E1', args'), K2)
	   end


     | updateExp (smartInj, G, DI.Pair(r, E1, E2), Tresult, K) = 
	   let
	     val F = D'.newFVar(D'.coerceCtx G)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(F))

		       
	     val firstType = inferType(G, E1)
	     val D = D'.NormalDec(NONE, firstType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val secondF = D'.newFVar(D'.coerceCtx G')
	     val pairF = D'.Exists(D, secondF)
	     val pairType = D'.Meta(pairF)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, pairType)

	     val (E1', K1) = updateExp(smartInj, G, E1, firstType, K)
	     val t = I.Dot(coerceExp E1', I.id)
	     val (E2', K2) = updateExp(smartInj, G, E2, D'.Meta(D'.FClo(secondF, t)), K1)
	   in
	     (DI.Pair(r, E1', E2'), K2)
	   end


     | updateExp (smartInj, G, DI.Proj (r, E, i), Tresult, K) =
	   let
	     val F = D'.newFVar (D'.coerceCtx G)
	     val T = D'.Meta(F)

	     val (E', K') = updateExp (smartInj, G, E, T, K)
	 
             (* F must have been instantiate to a FormList, otherwise we return an error *)
	     val Flist = case (D'.whnfF F)
	                    of (D'.FormList Flist) => Flist
			     | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected Projection (automatic for mutual recursion... this should not happen!"))

	     val _ = if ((List.length Flist) < i)
	             then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Badly formed Projection (automatic for mutual recursion... this should not happen!"))
		     else ()

	     val Tinferred = getIndexN(i, D'.FormList Flist)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tinferred)
	   in
	     (DI.Proj (r, E', i), K')
	   end


     | updateExp (smartInj, G, DI.Pop(r, i, E), Tresult, K) = 
	   let
	     fun popCtx(1, I.Decl(G, D'.NonInstantiableDec (D as D'.NewDecLF _))) = (D, G)
	       | popCtx(1, I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _))) = raise Domain (* do not allow pop on worlds... *)
	       | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
	       | popCtx(0, _) = raise Domain
	       | popCtx _ = raise Domain

	     val (D, G') = popCtx(i, G)

	     val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
	     val T = D'.Meta(D'.Nabla(D, F))
	     val Tshift = D'.Meta(D'.FClo(F, I.Shift (i-1)))

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)

	     val (E', K') = updateExp(smartInj, G', E, T, K)

	   in
	     (DI.Pop(r, i, E'), K')
	   end

     (* not used..     
     | updateExp (smartInj, G, DI.Fix(r, funList), Tresult, K) =  
	   let
	     val (_, funList', K') = updateFunList(smartInj, G, r, funList, Tresult, K)
	   in
	     (DI.Fix(r, funList'), K')
	   end
      *)
	     
     | updateExp (smartInj, G, E as DI.PatVar (r,name, origName), Tresult, K) = 
	   let
	     val (n, F) = getPatVarFormExact (name)


	     val n' = I.ctxLength G
	     val s = if (n' >= n) then I.Shift (n' - n) else raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Pattern Variable " ^ origName ^" out of scope. (did you pop it away?"))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.FClo(F, s)))

	     val (_, K') = DelphinAbstract.transformDelExp (NONE, E, K, true)
	   in
	     (E, K')
	   end


     (* syntactic sugar *)


     | updateExp (smartInj, G, DI.TypeAscribe (r, E as DI.Quote _, T), Tresult, K) = 
	   let
	     (* ENHANCEMENT:  If E is Quote and T is an implicit function,
	      * then first apply the implicit function to some args
	      *)

	     fun applyImplicitFun (T as D'.LF _, K) = (T, K)
	       | applyImplicitFun (D'.Meta(F), K) = let
							 val (F', K') = applyImplicitFunF (F, K)
						       in
							 (D'.Meta(F'), K')
						       end
	     and applyImplicitFunF (F, K) = applyImplicitFunFW (D'.whnfF F, K)
	     and applyImplicitFunFW (D'.All((D'.Implicit, D'.NormalDec (_, D'.LF(isP, A)))::Ds, F), K) = 
	          let
		    val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
		    val Q = DI.Quote(r, X, A, DA.InjLF, isP)
		    val _ = checkSubordQuote(r, (A, I.id)) (* checks local parameters.. *)
		    val K' = DelphinAbstract.LFcollectExp(r, NONE, (A, I.id), DelphinAbstract.LFcollectExp (r, NONE, (X, I.id), K, true), true)
		    val t' = I.Dot(coerceExp Q, I.id)
		  in
		    applyImplicitFunF(D'.FClo(D'.All(Ds, F), t'), K')
		  end
		| applyImplicitFunFW (D'.All((D'.Visible, _)::Ds, F), K) = 
		     raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Ascribed functional type to LF expression."))
		| applyImplicitFunFW (D'.All([], F), K) = applyImplicitFunF (F, K)
	        | applyImplicitFunFW (F, K) = (F, K)


	     val K2 = DelphinAbstract.collectDelTypes(NONE, T, K, true)
	     val (T', K3) = applyImplicitFun (convertTypes(G, T), K2)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, T')
	     val (E', K4) = updateExp(smartInj, G, E, Tresult, K3)
	   in
	     (DI.TypeAscribe (r, E', T), K4)
	   end


     | updateExp (smartInj, G, DI.TypeAscribe (r, E, T), Tresult, K) = 
	   let
	     val T' = convertTypes(G, T) 

	     val K2 = DelphinAbstract.collectDelTypes(NONE, T, K, true)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, T')
	     val (E', K3) = updateExp(smartInj, G, E, Tresult, K2)
	   in
	     (DI.TypeAscribe (r, E', T), K3)
	   end

     | updateExp (smartInj, G, DI.Sequence Elist, Tresult, K) =
	   let
	     val _ = if (List.length Elist < 2) then raise Domain (* List must have at least 2 elements *) else ()

	     fun getRegion [(r, _)] = r
	       | getRegion ((r, _) :: rest) = Paths.join(r, getRegion rest)
	       | getRegion _ = raise Domain

	     val r = getRegion Elist

	     val Fresult = D'.newFVar(D'.coerceCtx G)
	     val _ = unifyTypes(smartInj, r, "Sequence must end with formula type", G, Tresult, D'.Meta(Fresult))

	     fun updateList ([(r, E)], K) = 
	                              let
					val (E', K') = updateExp(smartInj, G, E, Tresult, K)
				      in
					([(r, E')], K')
				      end
	       | updateList (((r, E):: Elist), K) =
				      let
					val T = inferType(G, E)
					val (E', K') = updateExp(smartInj, G, E, T, K)
					val (rest, K'') = updateList (Elist, K')
				      in
					((r, E') ::rest, K'')
				      end
	       | updateList _ = raise Domain (* cannot have an empty list in a sequence *)
	       

	     val (Elist', K') = updateList (Elist, K)

	   in
	     (DI.Sequence Elist', K')
	   end


     | updateExp (smartInj, G, DI.LetFun (r, funList, E), Tresult, K) = 
	   let
	     val (D', funList', K2) = updateFunList(smartInj, G, r, funList, D'.Meta(D'.newFVar (D'.coerceCtx G)), K)

	     val G' = I.Decl(G, D'.InstantiableDec D')
	     val Tshift = D'.substTypes(Tresult, I.shift)

	     val (E', K3) = updateExp(smartInj, I.Decl(G, D'.InstantiableDec D'), E, Tshift, K2)
	   in
	     (DI.LetFun(r, funList', E'), K3)
	   end
     | updateExp (smartInj, G, DI.ExtendFunWith (r, E, Clist, sizeG2a, sizeG2b, isSugar, Fopt), Tresult, K) = 
	   let
		 (*
		  (bool represents isSugar)
		  GB |- E : T
		  GB, G2a |- CS : T
                  and first and last elements of G2a are NonInstantiable
		  ------------------------------------------------------
	          GB, G2a, G2b |- ExtendFunWith(E, CS, sizeG2a, sizeG2b, bool, Fopt) : T

	          (D.Formula option) = T (which makes sense in GB)
		 *)

	     val GB = D'.popCtx(sizeG2a+sizeG2b, G)
	     val GBG2a = D'.popCtx(sizeG2b, G)

	     val Fsave = case Fopt
	                 of SOME F => F
			  | NONE => D'.newFVar(D'.coerceCtx GB)


	     val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.FClo(Fsave, I.Shift(sizeG2a+sizeG2b))))

	     val (E', K2) = updateExp(smartInj, GB, E, D'.Meta(Fsave), K)

	     val _ = if not(isSugar) andalso (isAllImplicitF Fsave) then
	              raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "We only support automatic extension of limited parameter functions."))
	              else
			()
	     fun caseF C =
	       let
		 val oldTables = saveExactTables() (* also saves patVarCtx *)
		 val _ = patVarCtx := GBG2a
		 val (C', _) = updateCase(isSugar, smartInj, GBG2a, C, D'.Meta(D'.FClo(Fsave, I.Shift sizeG2a)), K2)
		 val _ = restoreExactTables oldTables (* also restores patVarCtx *)
	       in
		 C'
	       end

	     val Clist' = map caseF Clist

	   in
	     (DI.ExtendFunWith(r, E', Clist', sizeG2a, sizeG2b, isSugar, SOME Fsave), K2)
	   end



    and updateFunList (smartInj, G, r, funList, Tresult, K) =
          let
	    val oldTables = saveExactTables() (* also saves patVarCtx *)
	    (* Scoping the patvars here is not necessary, but can't hurt *)
	    (* ADAM:  So we should remove this.. but test first... *)
	                                     
	    val _ = patVarCtx := G
	    val result = updateFunList'(smartInj, G, r, funList, Tresult, K)
	    val _ = restoreExactTables oldTables (* also restores patVarCtx *)
	  in
	    result
	  end
      
    and updateFunList' (smartInj, G, r, funList, Tresult, Kinitial) =
	   let
	     (* add implicit types *)
	     fun addImplicit(r,D,E) = (r, DelphinAbstract.addImplicitTypesDec (D, Kinitial), E)
	       handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		    | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg))

	     val funList = map addImplicit funList
	     (* end of addition of implicit types *)


	     val decList  = map (fn (_,D,_) => convertNormalDec(G, D)) funList 
	     fun decListString [D'.NormalDec(SOME [s], _)] = [s]
	       | decListString ((D'.NormalDec(SOME [s], _)) :: decs) = s :: (decListString decs)
	       | decListString _ = raise Domain (* badly formed fixpoint *)

	     fun decListFormulas [D'.NormalDec(_, D'.Meta(F))] = [F]
	       | decListFormulas ((D'.NormalDec(_, D'.Meta(F))) :: decs) = F :: (decListFormulas decs)
	       | decListFormulas _ = raise Domain (* badly formed fixpoint *) 


	     fun decListFormula [F] = F
	       | decListFormula Flist = D'.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(F))


	     val D = D'.NormalDec (SOME (decListString decList), D'.Meta(F))
	     val G' = I.Decl(G, D'.InstantiableDec D)
	       
	     (* We need to shift the formula so it makes sense in G' *)
	     fun pairFormula ([], []) = []
	       | pairFormula ((r, D, E)::fList, F::formList) = (r, D, E, D'.FClo(F,I.shift)) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)


	     val expList = map (fn (r, D, E, F) => (r, D, #1 (updateExp(smartInj, G', E, D'.Meta(F), Kinitial)))) expFormList

	   in
	     (D, expList, Kinitial)
	   end
      


    and updateCase (isSugar, smartInj, G, DI.Eps(r, D, C), Tresult, K) =
                                  let
				    val D' = convertNormalDec(G, D)
				    val K2 = DelphinAbstract.collectDelNormalDec (NONE, D, K, true)
				    val G' = I.Decl(G, D'.InstantiableDec D')
				    val (C', K3) = updateCase(isSugar, smartInj, G', C, D'.substTypes(Tresult, I.shift), K2)
				  in
				    (DI.Eps(r, D, C'), K3)
				  end


      | updateCase (isSugar, smartInj, G, DI.NewC(r, D, C), Tresult, K) =
				  let
				    val D' = convertNewDec (G, D)
				    val _ = checkSubordNewDec D
				    val K2 = DelphinAbstract.collectDelNewDec (NONE, D, K, true)

				    val G' = I.Decl(G, D'.NonInstantiableDec D')
				    val newResult = D'.newFVar(D'.coerceCtx G')
				    val nablaType = D'.Meta(D'.Nabla(D', newResult))
				    val _ = unifyTypes(smartInj, r, "New has incompatible type", G, Tresult, nablaType)

				    val (C', K3) = updateCase(isSugar, smartInj, G', C, D'.Meta(newResult), K2)
				  in
				    (DI.NewC(r, D, C'), K3)
				  end
(* Removed PopC from intermediate syntax
      | updateCase (isSugar, smartInj, G, DI.PopC(r, i, C), Tresult, K) =
				  let
				    fun popCtx(1, I.Decl(G, D'.NonInstantiableDec (D as D'.NewDecLF _))) = (D, G)
				      | popCtx(1, I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _))) = raise Domain
				      | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
				      | popCtx(0, _) = raise Domain
				      | popCtx _ = raise Domain
				      
				    val (D, G') = popCtx(i, G)

				    val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
				    val T = D'.Meta(D'.Nabla(D, F))
				    val Tshift = D'.Meta(D'.FClo(F, I.Shift (i-1)))
				      
				    val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)

				    val oldTables = saveExactTables() (* also saves patVarCtx *)
				    val _ = patVarCtx := G'				     
				    val (C', K2) = updateCase(isSugar, smartInj, G', C, T, K)
				    val _ = restoreExactTables oldTables (* also restores patVarCtx *)
				      
				  in
				    (DI.PopC(r, i, C'), K2)
				  end
*)

      | updateCase (false, smartInj, G, DI.Match(r, pats, E2), Tresult, K) =
				  (* pats may be empty if Tresult is a completely implicit function..
				   * but the result will not be an empty.list of patterns.
				   *)
				  let
				    val F = D'.newFVar(D'.coerceCtx G)
				    val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))


				    fun processPats (pats, F, K) = processPatsW(pats, D'.whnfF F, K)
				    and processPatsW (pats, D'.All((D'.Implicit, D'.NormalDec (_, D'.LF(isP, A)))::Ds, F), K) =
				               let
						 val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
						 val Q = DI.Quote(r, X, A, DA.InjLF, isP)
						 val _ = checkSubordQuote(r, (A, I.id)) (* checks local parameters.. *)

						 val K' = DelphinAbstract.LFcollectExp(r, NONE, (A, I.id), DelphinAbstract.LFcollectExp (r, NONE, (X, I.id), K, true), true)
						 val t' = I.Dot(coerceExp Q, I.id)
						 val (pats', Frest, K'') = processPats(pats, D'.FClo(D'.All(Ds, F), t'), K')

					       in
						 ((D'.Implicit, Q) :: pats', Frest, K'')
					       end

				      | processPatsW ((_ (* Visible *),E1)::pats, D'.All((D'.Visible, D'.NormalDec (_, T))::Ds, F), K) =
					       let
						 val (E1', K') = updateExp(smartInj, G, E1, T, K)
						 val t' = I.Dot (coerceExp E1', I.id)
						 val (pats', Frest, K'') = processPats(pats, D'.FClo(D'.All(Ds, F), t'), K')
					       in
						 ((D'.Visible, E1') :: pats', Frest, K'')
					       end
				      | processPatsW ([], D'.All([], F), K) = ([], F, K)
				      | processPatsW (pats, D'.All([], F), K) = 
					       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected remaining pats"))
						  (* The case for completely implicit functions is handled ahead of time in DI.Lam.
						   *)
				      | processPatsW (pats, F, K) =  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Pats"))

						   

				    val F = makeForAll(false, smartInj, r, G, pats, F) (* makes F a Forall ... *)
				    val (pats', Frest, K2) = processPats (pats, F, K)
				    val (E2', K3) = updateExp(smartInj, G, E2, D'.Meta(Frest), K2)
				  in
				    (DI.Match(r, pats', E2'), K3)
				  end


      | updateCase (true (* isSugar *), smartInj, G, DI.Match(r, pats, E2), Tresult, K) =

				  (* pats may be empty if Tresult is a completely implicit function..
				   * but the result will not be an empty.list of patterns.
				   *)
				  let
				    val F = D'.newFVar(D'.coerceCtx G)
				    val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))


				    fun processPats (pats, F, K) = processPatsW(pats, D'.whnfF F, K)
				    and processPatsW (pats, D'.All((D'.Implicit, D'.NormalDec (_, D'.LF(isP, A)))::Ds, F), K) =
				               let
						 val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
						 val Q = DI.Quote(r, X, A, DA.InjLF, isP)
						 val _ = checkSubordQuote(r, (A, I.id)) (* checks local parameters.. *)

						 val K' = DelphinAbstract.LFcollectExp(r, NONE, (A, I.id), DelphinAbstract.LFcollectExp (r, NONE, (X, I.id), K, true), true)
						 val t' = I.Dot(coerceExp Q, I.id)
						 val (pats', Frest, K'') = processPats(pats, D'.FClo(D'.All(Ds, F), t'), K')

					       in
						 ((D'.Implicit, Q) :: pats', Frest, K'')
					       end

				      | processPatsW ((_ (* Visible *),E1)::pats, D'.All((D'.Visible, D'.NormalDec (_, T))::Ds, F), K) =
					       let
						 val (E1', K') = updateExp(smartInj, G, E1, T, K)
						 val t' = I.Dot (coerceExp E1', I.id)
						 val (pats', Frest, K'') = processPats(pats, D'.FClo(D'.All(Ds, F), t'), K')
					       in
						 ((D'.Visible, E1') :: pats', Frest, K'')
					       end
				      | processPatsW ([], D'.All([], F), K) = ([], F, K)
				      | processPatsW (pats, D'.All([], F), K) = processPats(pats, F, K)
				      | processPatsW (pats, F, K) =  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Pats"))

						   

				    val F = makeForAll(true, smartInj, r, G, pats, F) (* makes F a Forall ... *)
				    val (pats', Frest, K2) = processPats (pats, F, K)
				    val (E2', K3) = updateExp(smartInj, G, E2, D'.Meta(Frest), K2)
				  in
				    (DI.Match(r, pats', E2'), K3)
				  end


   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* 
    * Second-B Phase:  (After Abstraction) Fill in Type information on Lams that abstract erased.
    *    We need this type information to deSugar cases..
    *
    *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)



   fun updateLamsExp (smartInj, G, Eorig as DI.VarInt (r, i), Tresult)  =
         let
	   val (name, T) = lookupInt(r, i, G, i)
	   val T = removeCoverageInfo (T)

	   val s = case name of 
	            NONE => "#" ^ (Int.toString i)
		   | SOME s => s

	   val _ = unifyTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", G, Tresult, T)
	 in
	   Eorig
	 end

     | updateLamsExp (smartInj, G, Eorig as DI.Quote (r, M, A, DA.InjLF, isP), Tresult) =
	 (case (D'.whnfP isP)
	    of D'.Existential => 
		     let	  
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.LF(D'.Existential, A))
		     in
		       Eorig
		     end
	     | D'.Param =>
		     (let
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.LF(D'.Param, A))
		       val n = Whnf.etaContract M
		       val _ = case (I.ctxLookup (G, n))
			       of (D'.InstantiableDec (D'.NormalDec (_, D'.LF (isP, _)))) => 
				                                                let
										  val _ = U.unifyP(isP, D'.Param)
										    handle U.Error msg => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))
										in
										  ()
										end
				|  (D'.NonInstantiableDec (D'.NewDecLF _)) => ()
			        | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))
		     in
			Eorig
		     end handle Whnf.Eta => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Expected Variable.")))
	     | (D'.PVar p) =>
		     let
		       val _ = (p := SOME (D'.Existential))  (* If it is ambiguous.. make it existential... *)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.LF(D'.Existential, A))
		     in
		       Eorig
		     end
         )

		   

     | updateLamsExp (smartInj, G, Eorig as DI.Quote (r, M, A, DA.InjMeta, isP), Tresult) =
	 (case (D'.whnfP isP)
	    of D'.Existential => 
	             let
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(D'.Existential, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(F))
		     in
		       Eorig
		     end

	     | D'.Param =>
		     (let
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(D'.Param, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(F))
		       val n = Whnf.etaContract M
		       val _ = case (I.ctxLookup (G, n))
			       of (D'.InstantiableDec (D'.NormalDec (_, D'.LF (isP, _)))) => 
				                                                let
										  val _ = U.unifyP(isP, D'.Param)
										    handle U.Error msg => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))
										in
										  ()
										end
				|  (D'.NonInstantiableDec (D'.NewDecLF _)) => ()
			        | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))

		     in
		       Eorig
		     end handle Whnf.Eta => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Expected Variable.")))
	     | (D'.PVar p) =>
		     let
		       val _ = (p := SOME (D'.Existential))  (* If it is ambiguous.. make it existential... *)
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(D'.Existential, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(F))
		     in
		       Eorig
		     end
         )


     | updateLamsExp (smartInj, G, DI.Quote (r, M, A, DA.InjVar(ref (SOME I)), isP), Tresult) = updateLamsExp (smartInj, G, DI.Quote(r, M, A, I, isP), Tresult)
     | updateLamsExp (smartInj, G, DI.Quote (region, M, A, DA.InjVar(r as ref NONE), isP), Tresult) =
	     ( (* It can be either LF or Meta, so we pick Meta *)
	      r := SOME DA.InjMeta ;
	      updateLamsExp(smartInj, G, DI.Quote(region, M, A, DA.InjMeta, isP), Tresult))
	      



     | updateLamsExp (smartInj, G, Eorig as DI.Unit r, Tresult) = 
	   let
	     val _ = unifyTypes(smartInj, r, "() has incompatible type", G, Tresult, D'.Meta(D'.Top))
	   in
	     Eorig
	   end

     | updateLamsExp (smartInj, G, DI.Lam (isSugar, r, Clist, Fopt), Tresult) =
	   let
	     val F = case Fopt
	             of SOME F => F
		      | _ => D'.newFVar(D'.coerceCtx G)

	     val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))
	     val Clist' = map (fn C => updateLamsCase(isSugar, smartInj, G, C, Tresult)) Clist
	   in
	     DI.Lam(isSugar, r, Clist', SOME F)
	   end

     | updateLamsExp (smartInj, G, DI.New(r, D, E), Tresult) =
	   let
	     val D' = convertNewDec(G, D)
	     val G' = I.Decl(G, D'.NonInstantiableDec D')
	     val newResult = D'.newFVar(D'.coerceCtx G')
	     val nablaType = D'.Meta(D'.Nabla(D', newResult))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, nablaType)

	     val E' = updateLamsExp(smartInj, G', E, D'.Meta(newResult))
	   in
	     DI.New(r, D, E')
	   end


     | updateLamsExp (smartInj, G, DI.App(r, E1, args), Tresult) = 
	   let
	     val funF = D'.newFVar(D'.coerceCtx G)
	     val E1' = updateLamsExp(smartInj, G, E1, D'.Meta(funF))

	     fun processArgs (args, F) = processArgsW(args, D'.whnfF F)
	     and processArgsW ((vis,E2)::args, D'.All((vis', D'.NormalDec (_, T))::Ds, F)) =
		  let
		    val _ = case (vis, vis')
		        of (D'.Visible, D'.Visible) => ()
		         | (D'.Implicit, D'.Implicit) => ()
			 | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Visibility in Patterns"))

		    val E2' = updateLamsExp(smartInj, G, E2, T)
		    val t' = I.Dot (coerceExp E2', I.id)
		    val (args', Frest) = processArgs(args, D'.FClo(D'.All(Ds, F), t'))
		  in
		    ((vis, E2') :: args', Frest)
		  end
	       | processArgsW ([], D'.All([], F)) = ([], F)
	       | processArgsW (args, D'.All([], F)) = 
		  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected remaining args"))
	       | processArgsW _ =   raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Args"))
						   
		    
	     val funF = makeForAll(false, smartInj, r, G, args, funF) (* makes funF a Forall ... *)
	     val (args', Frest) = processArgs (args, funF)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(Frest))
	   in
	     DI.App(r, E1', args')
	   end

     | updateLamsExp (smartInj, G, DI.Pair(r, E1, E2), Tresult) = 
	   let
	     val F = D'.newFVar(D'.coerceCtx G)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(F))

		       
	     val firstType = inferType(G, E1)
	     val D = D'.NormalDec(NONE, firstType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val secondF = D'.newFVar(D'.coerceCtx G')
	     val pairF = D'.Exists(D, secondF)
	     val pairType = D'.Meta(pairF)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, pairType)

	     val E1' = updateLamsExp(smartInj, G, E1, firstType)
	     val t = I.Dot(coerceExp E1', I.id)
	     val E2' = updateLamsExp(smartInj, G, E2, D'.Meta(D'.FClo(secondF, t)))
	   in
	     DI.Pair(r, E1', E2')
	   end


     | updateLamsExp (smartInj, G, DI.Proj (r, E, i), Tresult) =
	   let
	     val F = D'.newFVar (D'.coerceCtx G)
	     val T = D'.Meta(F)

	     val E' = updateLamsExp (smartInj, G, E, T)
	 
             (* F must have been instantiate to a FormList, otherwise we return an error *)
	     val Flist = case (D'.whnfF F)
	                    of (D'.FormList Flist) => Flist
			     | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected Projection (automatic for mutual recursion... this should not happen!"))

	     val _ = if ((List.length Flist) < i)
	             then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Badly formed Projection (automatic for mutual recursion... this should not happen!"))
		     else ()

	     val Tinferred = getIndexN(i, D'.FormList Flist)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tinferred)
	   in
	     DI.Proj(r, E', i)
	   end

     | updateLamsExp (smartInj, G, DI.Pop(r, i, E), Tresult) = 
	   let
	     fun popCtx(1, I.Decl(G, D'.NonInstantiableDec (D as D'.NewDecLF _))) = (D, G)
	       | popCtx(1, I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _))) = raise Domain
	       | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
	       | popCtx(0, _) = raise Domain
	       | popCtx _ = raise Domain

	     val (D, G') = popCtx(i, G)	       

	     val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
	     val T = D'.Meta(D'.Nabla(D, F))
	     val Tshift = D'.Meta(D'.FClo(F, I.Shift (i-1)))

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)

	     val E' = updateLamsExp(smartInj, G', E, T)
	   in
	     DI.Pop(r, i, E')
	   end

     (* not used 
     | updateLamsExp (smartInj, G, DI.Fix(r, funList), Tresult) =  DI.Fix (r, #2 (updateLamsFunList(smartInj, G, r, funList, Tresult)))
      *)

     | updateLamsExp (smartInj, G, DI.PatVar _, _) = raise Domain (* PatVar should be eliminated by abstraction BEFORE calling this function *)

     (* syntactic sugar *)

     | updateLamsExp (smartInj, G, DI.TypeAscribe (r, E as DI.Quote _, T), Tresult) =
	   let
	     (* ENHANCEMENT:  If E is Quote and T is an implicit function,
	      * then first apply the implicit function to some args
	      *)

	     fun applyImplicitFun (T as D'.LF _) = T
	       | applyImplicitFun (D'.Meta(F)) = D'.Meta(applyImplicitFunF F)

	     and applyImplicitFunF F = applyImplicitFunFW (D'.whnfF F)
	     and applyImplicitFunFW (D'.All((D'.Implicit, D'.NormalDec (_, D'.LF(isP, A)))::Ds, F)) = 
	          let
		    val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
		    val Q = DI.Quote(r, X, A, DA.InjLF, isP)
		    val t' = I.Dot(coerceExp Q, I.id)
		  in
		    applyImplicitFunF(D'.FClo(D'.All(Ds, F), t'))
		  end
		| applyImplicitFunFW (D'.All((D'.Visible, _)::Ds, F)) = 
		     raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Ascribed functional type to LF expression."))
		| applyImplicitFunFW (D'.All([], F)) = applyImplicitFunF F
	        | applyImplicitFunFW F = F


	     val T' = applyImplicitFun (convertTypes(G, T))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, T')
	   in
	     DI.TypeAscribe(r, updateLamsExp(smartInj, G, E, Tresult), T)
	   end


     | updateLamsExp (smartInj, G, DI.TypeAscribe (r, E, T), Tresult) = 
	   let
	     val T' = convertTypes(G, T)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, T')

	   in
	     DI.TypeAscribe(r, updateLamsExp(smartInj, G, E, Tresult), T)
	   end


     | updateLamsExp (smartInj, G, DI.Sequence Elist, Tresult) =
	   let
	     val _ = if (List.length Elist < 2) then raise Domain (* List must have at least 2 elements *) else ()

	     fun getRegion [(r, _)] = r
	       | getRegion ((r, _) :: rest) = Paths.join(r, getRegion rest)
	       | getRegion _ = raise Domain

	     val r = getRegion Elist

	     val Fresult = D'.newFVar(D'.coerceCtx G)
	     val _ = unifyTypes(smartInj, r, "Sequence must end with formula type", G, Tresult, D'.Meta(Fresult))

	     fun updateList ([(r, E)]) = 
	                              let
					val (E') = updateLamsExp(smartInj, G, E, Tresult)
				      in
					([(r, E')])
				      end
	       | updateList (((r, E):: Elist)) =
				      let
					val T = inferType(G, E)
					val (E') = updateLamsExp(smartInj, G, E, T)
					val (rest) = updateList (Elist)
				      in
					((r, E') ::rest)
				      end
	       | updateList _ = raise Domain (* cannot have an empty list in a sequence *)
	       

	     val (Elist') = updateList (Elist)

	   in
	     DI.Sequence Elist'
	   end
	    

     | updateLamsExp (smartInj, G, DI.LetFun (r, funList, E2), Tresult) = 
	   let
	     val (D', funList') = updateLamsFunList(smartInj, G, r, funList, D'.Meta(D'.newFVar (D'.coerceCtx G)))

	     val G' = I.Decl(G, D'.InstantiableDec D')

	     val Tshift = D'.substTypes(Tresult, I.shift)

	     val E2' = updateLamsExp(smartInj, G', E2, Tshift)
	   in
	     DI.LetFun(r, funList', E2')
	   end


     | updateLamsExp (smartInj, G, DI.ExtendFunWith (r, E, Clist, sizeG2a, sizeG2b, isSugar, Fopt), Tresult) =
	   let
		 (*
		  (bool represents isSugar)
		  GB |- E : T
		  GB, G2a |- CS : T
                  and first and last elements of G2a are NonInstantiable
		  ------------------------------------------------------
	          GB, G2a, G2b |- ExtendFunWith(E, CS, sizeG2a, sizeG2b, bool, Fopt) : T

	          (D.Formula option) = T (which makes sense in GB)
		 *)

	     val GB = D'.popCtx(sizeG2a+sizeG2b, G)
	     val GBG2a = D'.popCtx(sizeG2b, G)

	     val Fsave = case Fopt
	                 of SOME F => F
			  | NONE => D'.newFVar(D'.coerceCtx GB)


	     val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.FClo(Fsave, I.Shift(sizeG2a+sizeG2b))))

	     val (E') = updateLamsExp(smartInj, GB, E, D'.Meta(Fsave))

	     val _ = if not(isSugar) andalso (isAllImplicitF Fsave) then
	              raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "We only support automatic extension of limited parameter functions."))
	              else
			()

	     fun caseF C = updateLamsCase(isSugar, smartInj, GBG2a, C, D'.Meta(D'.FClo(Fsave, I.Shift sizeG2a)))
	     val Clist' = map caseF Clist

	   in
	     DI.ExtendFunWith(r, E', Clist', sizeG2a, sizeG2b, isSugar, SOME Fsave)
	   end


    and updateLamsFunList (smartInj, G, r, funList, Tresult) =
	   let
	     val decList  = map (fn (_,D,_) => convertNormalDec(G, D)) funList 
	     fun decListString [D'.NormalDec(SOME [s], _)] = [s]
	       | decListString ((D'.NormalDec(SOME [s], _)) :: decs) = s :: (decListString decs)
	       | decListString _ = raise Domain (* badly formed fixpoint *)

	     fun decListFormulas [D'.NormalDec(_, D'.Meta(F))] = [F]
	       | decListFormulas ((D'.NormalDec(_, D'.Meta(F))) :: decs) = F :: (decListFormulas decs)
	       | decListFormulas _ = raise Domain (* badly formed fixpoint *) 


	     fun decListFormula [F] = F
	       | decListFormula Flist = D'.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(F))


	     val D = D'.NormalDec (SOME (decListString decList), D'.Meta(F))
	     val G' = I.Decl(G, D'.InstantiableDec D)
	       
	     (* We need to shift the formula so it makes sense in G' *)
	     fun pairFormula ([], []) = []
	       | pairFormula ((r, D, E)::fList, F::formList) = (r, D, E, D'.FClo(F,I.shift)) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)

	     val expList = map (fn (r, D, E, F) => (r, D, (updateLamsExp(smartInj, G', E, D'.Meta(F))))) expFormList

	   in
	     (D, expList)
	   end
      


    and updateLamsCase (isSugar, smartInj, G, DI.Eps(r, D, C), Tresult) =
                                  let
				    val D' = convertNormalDec(G, D)
				    val G' = I.Decl(G, D'.InstantiableDec D')
				    val C' = updateLamsCase(isSugar, smartInj, G', C, D'.substTypes(Tresult, I.shift))
				  in
				    DI.Eps(r, D, C')
				  end


      | updateLamsCase (isSugar, smartInj, G, DI.NewC(r, D, C), Tresult) =
				  let
				    val D' = convertNewDec (G, D)
				    val G' = I.Decl(G, D'.NonInstantiableDec D')
				    val newResult = D'.newFVar(D'.coerceCtx G')
				    val nablaType = D'.Meta(D'.Nabla(D', newResult))
				    val _ = unifyTypes(smartInj, r, "New has incompatible type", G, Tresult, nablaType)

				    val C' = updateLamsCase(isSugar, smartInj, G', C, D'.Meta(newResult))
				  in
				    DI.NewC(r, D, C')
				  end

      | updateLamsCase (isSugar, smartInj, G, DI.Match(r, [], E2), Tresult) = raise Domain (* impossible *)

      | updateLamsCase (false, smartInj, G, DI.Match(r, pats, E2), Tresult) =
				  let
				    val F = D'.newFVar(D'.coerceCtx G)
				    val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))


				    fun processPats (pats, F) = processPatsW(pats, D'.whnfF F)
				    and processPatsW ((vis, E1)::pats, D'.All((vis', D'.NormalDec (_, T))::Ds, F)) =
					       let
						 val _ = case (vis, vis')
						           of (D'.Visible, D'.Visible) => ()
							    | (D'.Implicit, D'.Implicit) => ()
							    | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Visibility in Patterns"))

						 val (E1') = updateLamsExp(smartInj, G, E1, T)
						 val t' = I.Dot (coerceExp E1', I.id)
						 val (pats', Frest) = processPats(pats, D'.FClo(D'.All(Ds, F), t'))
					       in
						 ((vis, E1') :: pats', Frest)
					       end
				      | processPatsW ([], D'.All([], F)) = ([], F)
				      | processPatsW (pats, D'.All([], F)) = 
					       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected remaining pats"))
				      | processPatsW (pats, F) =   raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Pats"))

						   
				    val F = makeForAll(false, smartInj, r, G, pats, F) (* makes F a Forall ... *)
				    val (pats', Frest) = processPats (pats, F)
				    val E2' = updateLamsExp(smartInj, G, E2, D'.Meta(Frest))

				  in
				    DI.Match(r, pats', E2')
				  end

      | updateLamsCase (true, smartInj, G, DI.Match(r, pats, E2), Tresult) =
				  let
				    val F = D'.newFVar(D'.coerceCtx G)
				    val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))


				    fun processPats (pats, F) = processPatsW(pats, D'.whnfF F)
				    and processPatsW ((vis,E1)::pats, D'.All((vis', D'.NormalDec (_, T))::Ds, F)) =
					       let
						 val _ = case (vis, vis')
						           of (D'.Visible, D'.Visible) => ()
							    | (D'.Implicit, D'.Implicit) => ()
							    | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Visibility in Patterns"))

						 val (E1') = updateLamsExp(smartInj, G, E1, T)
						 val t' = I.Dot (coerceExp E1', I.id)
						 val (pats', Frest) = processPats(pats, D'.FClo(D'.All(Ds, F), t'))
					       in
						 ((vis, E1') :: pats', Frest)
					       end
				      | processPatsW ([], D'.All([], F)) = ([], F)
				      | processPatsW (pats, D'.All([], F)) = processPats(pats, F)
				      | processPatsW (pats, F) =  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Pats"))

						   

				    val F = makeForAll(true, smartInj, r, G, pats, F) (* makes F a Forall ... *)
				    val (pats', Frest) = processPats (pats, F)
				    val (E2') = updateLamsExp(smartInj, G, E2, D'.Meta(Frest))
				  in
				    DI.Match(r, pats', E2')
				  end


	
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* 
    * Third Phase:  (After Abstraction) Convert from DelphinIntermediateSyntax to DelphinIntSyntax
    *
    *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)


   (* FOR Coverage we add Nabla{W} and New{W} in these next three routines
    * If coverage is disabled, then we DO not add it...
    *)

   fun addWorldT(world, Torig as D'.Meta F) =
          if !enableCoverage then
	    (case (D'.whnfF F)
	       of (D'.FormList list) => D'.Meta 
				      (D'.FormList (map (fn F' => D'.Nabla(D'.NewDecWorld(NONE, world), D'.FClo(F', I.shift))) list))
	         | _ => D'.Meta (D'.Nabla(D'.NewDecWorld(NONE, world), D'.FClo(F, I.shift)))
             )
	  else
	    Torig
     | addWorldT(world, _) = raise Domain (* not a meta-level type *)


   fun addWorldTI(world, Torig as DI.Meta (r,F)) =
          if !enableCoverage then
	    DI.Meta (r, DI.Nabla(r, DI.NewDecWorld(r, NONE, world), DI.substF(F, I.shift)))
	  else
	    Torig
     | addWorldTI(world, _) = raise Domain (* not a meta-level type *)


   fun addWorldD(world, DI.NormalDec(r, names, T)) = DI.NormalDec(r, names, addWorldTI(world, T))

   fun addWorldE(world, E, r) =
         if !enableCoverage then
	     DI.New(r, DI.NewDecWorld(r, NONE, world), DI.substE(E, DI.shift(1)))
	 else
	   E

   fun addWorldflist (world, []) = []
     | addWorldflist (world, ((r, D, E)::flist)) = 
            let
	      val D' = addWorldD(world, D)
	      val E' = addWorldE(world, E, r)
	      val flist' = addWorldflist (world, flist)
	    in
	      ((r, D', E')::flist')
	    end
	    



 (* ExtendFun is an admissible rule that explicitly extends parameter functions.


    GB |- worldFun : T
    and T is a parameter function
    GB, G2a |- CS : T
    and G2a only has NonInstantiableDecs..
      (optionally G2b should have only InstantiableDecs if it is to pass the world checker)
      
    -------------------------------------------------
    GB, G2a, G2b |- ExtendFun(worldFun, CS, sizeG2a, sizeG2b) : T
  *)
   fun createExtendFun (smartInj, r, G, sizeG2a, sizeG2b, worldFun, CS, T (* makes since in Gbefore *)) =
	   let

	     val defaultFileInfo = (SOME(!filename, r))

	     (* G = Gbefore,G2a,G2b *)
	     val Gbefore = D'.popCtx(sizeG2a+sizeG2b, G)
	     val GBG2a = D'.popCtx(sizeG2b, G)
	     fun getCtx(G, 0) = I.Null
	       | getCtx(I.Decl(G, D as D'.NonInstantiableDec (D'.NewDecLF _)), n) = I.Decl(getCtx(G, n-1), D)
	       | getCtx(I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _)), n) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only automatically extend when news are consecutive without world news."))
	               (* This is guaranteed not to happen by only using NewDecWorld at the top-level.
		         * but this function will probably work even with NonDecWorld ..
			 *)
	       | getCtx(I.Decl(G, D'.InstantiableDec _), n) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only automatically extend when news are consecutive."))
	       | getCtx _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Bad specification of automatic pop in ExtendFun.. unexpected error!"))
	       
	     val G2a = getCtx(GBG2a, sizeG2a)

	     (* Gbefore |- T : wff *)

	     fun extendType (I.Null) F = F
	       | extendType (I.Decl(G, D'.InstantiableDec D)) F = raise Domain  (* extendType is only called on G2a *)
	       | extendType (I.Decl(G, D'.NonInstantiableDec D)) F = extendType G (D'.Nabla(D, F))

	     val Fresult = D'.newFVar (D'.coerceCtx (GBG2a))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", GBG2a, 
				D'.substTypes(T, I.Shift (I.ctxLength G2a)), 
				D'.Meta(Fresult))

	     val extendedF = extendType G2a Fresult  (* Gbefore |- F = {G2a} T  *) 
	       
	     val _ = D'.updatePVarsFormula Fresult
	     val _ = if (NormalizeDelphin.hasVarsFor Fresult)
		      then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only extend parameter functions (but type is ambiguous)."))
	             else ()


	     fun isParamFun F = isParamFunW (D'.whnfF F)
	     and isParamFunW (D'.All (Ds, _)) = WorldSubsumption.possibleSplitOnParamNormalDecs (Ds)
	       | isParamFunW (D'.Nabla(_, F)) = false (* Let's disallow this from automatic extension *)
	       | isParamFunW _ = false

	     val _ = if (isParamFun Fresult)
		      then () 
		     else 
		       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only automatically extend limited parameter functions."))

	     fun extendCase (I.Null) C = C
	       | extendCase (I.Decl(G, D'.InstantiableDec D)) C = raise Domain
	                    (* extendCase G (D'.Eps(D, D'.MatchAnd(D'.Visible, D'.Var(D'.Fixed 1, defaultFileInfo), C), defaultFileInfo)) *)
	       | extendCase (I.Decl(G, D'.NonInstantiableDec D)) C = 
	                     extendCase G (D'.NewC(D, C, defaultFileInfo))

	     val Clist' = map (fn C => extendCase G2a C) CS

	     fun createLastBody (varList, Glocal (* Glocal = Ga *)) =
	         let
		   val worldApp = D'.App(worldFun, map (fn E => (D'.Visible,SOME(!filename,r),E)) varList) (* This now represents the function applied *)

		   (* We now need to do ((R => {Glocal}R) worldApp) \Glocal  *)


		   fun weakenE (I.Null, E) = E
		     | weakenE (I.Decl(G, D'.NonInstantiableDec D), E) = weakenE(G, D'.New(D, E, SOME(!filename, r)))
		     | weakenE _ = raise Domain (* broken invariant.. .Glocal only contains NonInstantiableDecs.. *)

		   fun weakenF (I.Null, F) = F
		     | weakenF (I.Decl(G, D'.NonInstantiableDec D), F) = weakenF(G, D'.Nabla(D, F))
		     | weakenF _ = raise Domain (* broken invariant.. .Glocal only contains NonInstantiableDecs.. *)


		   fun getResultFormula (F, l) = getResultFormulaW (D'.whnfF F, l)
		   and getResultFormulaW (D'.All(_::Ds, F), v::l) = getResultFormula (D'.FClo(D'.All(Ds,F), I.Dot(D'.coerceExp v, I.id)), l)
		     | getResultFormulaW (D'.All([], F), []) = F
		     | getResultFormulaW _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexplained Error."))
 
		   fun getResultType (D'.Meta(F), l) = getResultFormula (F, l)
		     | getResultType _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexplained Error."))

		   val resultF = getResultType (T, varList) (* recall T is defined way above *)
		                                            (* Gbefore |- resultF wff *)

		   val caseB = D'.Eps(D'.NormalDec(NONE, D'.Meta(resultF)),
				      D'.Match([(D'.Visible, D'.Var(D'.Fixed 1, defaultFileInfo))], 
					       weakenE (Glocal, D'.Var(D'.Fixed (1 + (I.ctxLength Glocal)), defaultFileInfo))),
				      defaultFileInfo)
		   val caseFun = D'.Lam ([caseB], 
					 D'.All(
						[(D'.Visible, D'.NormalDec(NONE, D'.Meta(resultF)))], 
						weakenF (Glocal, D'.FClo(resultF, I.Shift (I.ctxLength Glocal)))), 
					 SOME(!filename, r))

		   val caseApp = D'.App(caseFun, [(D'.Visible, SOME(!filename, r),worldApp)])

		   fun popCtx (I.Null, E) = E 
		     | popCtx (I.Decl(G, D'.NonInstantiableDec D), E) = D'.Pop(1, popCtx(G, E), SOME(!filename, r))
		     | popCtx _ = raise Domain (* broken invariant *)

		   val finalResult = popCtx (Glocal, caseApp)
		 in
		   finalResult
		 end

	     (* createLastCase is based on "getStartGoal" in coverage.fun *)	   
	     fun createLastCase (Glocal, varList, F, sc) = createLastCaseW (Glocal, varList, D'.whnfF F, sc)
	     and createLastCaseW (Glocal, varList, D'.All([(visibility, D)], F), sc) =
		      DelphinCoverage.generateEVarFirstCase(Gbefore, Glocal, 
						   D, fn E => sc (D'.Match([(visibility, E)], createLastBody(varList@[E],Glocal))))
	       | createLastCaseW (Glocal, varList, D'.All((visibility, D)::Ds, F), sc) =
		      DelphinCoverage.generateEVarFirstCase(Gbefore, Glocal, 
						   D, fn E => createLastCase(Glocal, varList@[E], D'.FClo(D'.All(Ds, F), I.Dot (D'.coerceExp E, I.id)), 
							       fn C => (case C
									  of (D'.Match(pats, res)) => sc (D'.Match((visibility, E)::pats, res))
									   | _ => raise Domain (* impossible *) )))
	       | createLastCaseW (Glocal, varList, D'.All([], F), sc) = raise Domain (* impossible *)
	       | createLastCaseW (Glocal, varList, D'.Nabla(D, F), sc)  =
		      createLastCase (I.Decl(Glocal, D'.NonInstantiableDec D), varList, F, fn C => sc (D'.NewC(D, C, defaultFileInfo)))
	       | createLastCaseW (Global, varList, F, sc) = raise Domain (* badly typed *)
		  

	     (* ABP WARNING:  abstractCase ASSUMES that it will not encounter any FVars and all EVars 
	      * make sense with respect to the same global context.
	      *)
                     
	     val Crest = createLastCase (I.Null, [], extendedF, fn C => DelphinAbstract2.abstractCase C)
	               handle DelphinCoverage.CoverageError s => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Error in WITH:  " ^ s))
	     val extendFun = D'.Lam (Clist'@[Crest], extendedF, SOME(!filename, r))

	     (* Compute (extendFun G2a)
	      * For example (extendFun (x,y,u,v)) = (((extendFun \x) \y) \u) \v
	      *)
	     fun applyExtend (E, I.Null, k) = E
	       | applyExtend (E, I.Decl(G, D'.InstantiableDec D), k) = raise Domain (* should never occur now *)
	                                         (* D'.App (D'.Visible, 
							 applyExtend(E, G, k+1),
							 D'.Var(D'.Fixed k, SOME(!filename, r)),
							 SOME(!filename, r)) 
                                                 *)
                                  
	       | applyExtend (E, I.Decl(G, D'.NonInstantiableDec D), k) = D'.Pop(k,
										 applyExtend(E, G, 1),
										 SOME(!filename, r))
	   in
	     applyExtend (extendFun, G2a, sizeG2b+1)
	   end

    (* deSugarCases removes the MatchSugar *)
                 (* i.e. fn A B C => E
		          | A' B' C' => E'
		  * is syntactic sugar for fn X1 => fn X2 => fn X3 => case (X1 and X2 and X3)
		                                                         of A and B and C => E
									  | A' and B' and C' => E'
                  *)


   fun isFun F = isFunW (D'.whnfF F)
   and isFunW (D'.All _) = true
     | isFunW (D'.Nabla (_, F)) = isFun F
     | isFunW _ = false
     

   fun convert2Formula (r, F) = convert2FormulaW (r, D'.whnfF F)
   and convert2FormulaW (r, D'.Top) = DI.Top r
     | convert2FormulaW (r, D'.All(Ds, F)) = DI.All(r,
						   map (fn(vis, D) => (vis, convert2Normal (r, D))) Ds,
						   convert2Formula (r, F))
     | convert2FormulaW (r, D'.Exists(D, F)) = DI.Exists(r, convert2Normal (r, D), convert2Formula (r, F))
     | convert2FormulaW (r, D'.Nabla(D, F)) = DI.Nabla(r, convert2New (r, D), convert2Formula (r, F))
     | convert2FormulaW (r, _ (* Fvar or FormList *)) = DI.OmittedFormula r
     
   and convert2New (r, D'.NewDecLF(name, A)) = DI.NewDecLF(r, name, A)
     | convert2New (r, D'.NewDecWorld(name, W)) = DI.NewDecWorld(r, name, W)
     
   and convert2Normal (r, D'.NormalDec(names, T)) = DI.NormalDec (r, NONE, convert2Types(r, T))

   and convert2Types (r, D'.LF(isP, A))= DI.LF(r, isP, A)
     | convert2Types (r, D'.Meta F) = DI.Meta(r, convert2Formula (r, F))

   fun deSugarCases'(smartInj, G, r, Clist, Fresult, numPats, numNews) =
        let
	  (* Precondition is that Fresult must be of a functional type.. *)

	  (* Let's first find out the real type of Clist by merging together the Alls.*)
	  fun getType(num, F) = getTypeW(num, D'.whnfF F)
	  and getTypeW(0, F) = raise Domain
	    | getTypeW(n, D'.Nabla(D, F)) = D'.Nabla(D, getType(n, F))
	    | getTypeW(n, D'.All(Ds, F)) =
	          let
		      val num = List.length Ds
		      val _ = if (n < num) then
			        raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))
			      else ()
		  in
		    if (n = num) then D'.All(Ds, F)
		    else
		      case D'.whnfF (getType(n-num, F))
			of D'.All(Ds', F') => D'.All(Ds@Ds', F')
		         | F' => raise Domain
		  end
	    | getTypeW _ = raise Domain

	  val ClistType = getType(numPats, Fresult)


	  fun createPops(0, offset, E) = E
	    | createPops(numPops, offset, E) = DI.Pop(r, offset+1, createPops(numPops-1, 0, E))

	  fun varInt(i, D'.Meta _) = DI.VarInt(r, i)
	    | varInt(i, D'.LF(isP, A)) = DI.Quote(r, I.Root(I.BVar(I.Fixed i), I.Nil), I.EClo(A, I.Shift i), DA.InjLF, isP)

	  fun buildArgs(0, []) = []
	    | buildArgs(index, (vis,D'.NormalDec(name, T))::decs) =  (vis, varInt(index, T)):: (buildArgs (index-1,decs))
	    | buildArgs _ = raise Domain


	  (* We now need to create new xs . fn x1 => ... => fn xn => pop xs. App(Clist, [x1,...,xn]) *)
	  fun buildCurriedFunction (F, numRemaining, Kdecs) = buildCurriedFunctionW (D'.whnfF F, numRemaining, Kdecs)
	  and buildCurriedFunctionW (F, 0, Kdecs) = 
	                  if (numNews > 0) then
			    DI.App(r, createPops(numNews, numPats, DI.Lam(false, r, Clist, SOME ClistType)), buildArgs(numPats, Kdecs))
			  else
			    DI.App(r, DI.substE(DI.Lam(false, r, Clist, SOME ClistType), DI.shift(numPats)),  (buildArgs(numPats, Kdecs)))
	    | buildCurriedFunctionW (D'.Nabla(D, F), numRemaining, Kdecs) = DI.New(r, convert2New (r, D), buildCurriedFunction(F, numRemaining, Kdecs))
	    | buildCurriedFunctionW (D'.All(Ds, F), numRemaining, Kdecs) =
	            let
		      fun createEps [] C = C
			| createEps ((vis, D)::Ds) C = DI.Eps(r, convert2Normal (r, D), createEps Ds C)

		      val num = List.length Ds
		      val _ = if (numRemaining < num) then
			        raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))
			      else ()
		      val args = buildArgs (num, Ds)
		    in
		      DI.Lam(false, 
			     r, 
			     [createEps Ds (DI.Match(r, args, buildCurriedFunction(F, numRemaining - num, Kdecs @ Ds)))],
			     SOME (D'.All(Ds, F)))
		    end
	    | buildCurriedFunctionW (F, _, _) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))

	in
	  (buildCurriedFunction (Fresult, numPats, []))
	end

   fun deSugarCases(smartInj, G, r, [], Fresult) = 
        let
	  (* We are dealing with an empty function, so we maximize the number of patterns we look at together *)

	  fun countNews (numNews, F) = countNewsW (numNews, D'.whnfF F)
	  and countNewsW (numNews, D'.Nabla(D, F)) = countNews(numNews+1, F)
	    | countNewsW (numNews, F) = (numNews, F)

	  val (numNews, F) = countNews(0, Fresult)

	  fun countArgs (numArgs, F) = countArgsW (numArgs, D'.whnfF F)
	  and countArgsW (numArgs, D'.All(Ds, F)) = countArgs(numArgs+(List.length Ds), F)
	    | countArgsW (numArgs, F) = (numArgs, F)

	  val (numPats, F) = countArgs(0, F)
	in
	  if (numPats > 1) then
	    deSugarCases'(smartInj, G, r, [], Fresult, numPats, numNews)
	  else DI.Lam(false, r, [], SOME Fresult)
	end

     | deSugarCases(smartInj, G, r, Clist as (Cfirst :: _) (* not empty *), Fresult) =
        let
	  fun countNumArgs (numNews, DI.Eps(r, _, C)) = countNumArgs (numNews, C)
	    | countNumArgs (numNews, DI.NewC(r, DI.NewDecLF _, C)) = countNumArgs (numNews +1, C)
	    | countNumArgs (numNews, DI.NewC(r, DI.NewDecWorld _, C)) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "We do not support meta-level (world) news in cases."))
	    (* Removed PopC from intermediate syntax
	    | countNumArgs (numNews, DI.PopC (r, i, C)) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "We no longer support different pops over different cases and cannot automatically convert this one... fix manually."))
	     *)
	    | countNumArgs (numNews, DI.Match (_, pats, _)) = (List.length pats, numNews)

	  val (numPats, numNews) = countNumArgs (0, Cfirst)

	 in
	   if isFun Fresult 
	     then if numPats > 1 then
	       deSugarCases'(smartInj, G, r, Clist, Fresult, numPats, numNews)
	       else (* (numPats == 1) *)
		 DI.Lam(false, r, Clist, SOME Fresult)
	   else 
	     raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Cannot desugar case...  ambiguous type!"))
	       (* This may be able to happen if Fresult is a FVar with constraints,
		* but we first do one run updating the types of all Lams (updateLams...), so that if this error happens
		* it is truly an ambiguous type which will never be filled in!
		*)
	 end



   fun deSugarExtend'(smartInj, G, r, worldFun, Clist, sizeG2a, sizeG2b, Fresult, numPats) =
        let
	  (* G = GB,G2a,G2b *)
	  (* GB |- Fresult  wff and Fresult is a function *)

	  (* Let's first find out the real type of Clist by merging together the Alls.*)
	  fun getType(num, F) = getTypeW(num, D'.whnfF F)
	  and getTypeW(0, F) = raise Domain
	    | getTypeW(n, D'.Nabla(D, F)) = D'.Nabla(D, getType(n, F))
	    | getTypeW(n, D'.All(Ds, F)) =
	          let
		      val num = List.length Ds
		      val _ = if (n < num) then
			        raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))
			      else ()
		  in
		    if (n = num) then D'.All(Ds, F)
		    else
		      case D'.whnfF (getType(n-num, F))
			 of D'.All(Ds', F') => D'.All(Ds@Ds', F')
		          | F' => raise Domain
		  end
	    | getTypeW _ = raise Domain

	  val newWorldFunType = getType(numPats, Fresult)


	  fun varInt(i, D'.Meta _) = DI.VarInt(r, i)
	    | varInt(i, D'.LF(isP, A)) = DI.Quote(r, I.Root(I.BVar(I.Fixed i), I.Nil), I.EClo(A, I.Shift i), DA.InjLF, isP)

	  fun buildArgs(0, []) = []
	    | buildArgs(index, (vis,D'.NormalDec(name, T))::decs) =  (vis, varInt(index, T)):: (buildArgs (index-1,decs))
	    | buildArgs _ = raise Domain



	  fun buildApps(E, numPats, Kdecs, F) = buildAppsW(E, numPats, Kdecs, D'.whnfF F)
	  and buildAppsW(E, 0, [], F) = E
	    | buildAppsW(E, numPats, Kdecs, D'.All(Ds, F)) = 
	           let
		      val num = List.length Ds
		      val _ = if (numPats < num) then
			        raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))
			      else ()

		      fun buildIt(0, _, _) = []
		        | buildIt(ctr, index, (vis,D'.NormalDec(name, T))::decs) = 
			           (vis, varInt(index, T)) :: buildIt(ctr-1, index-1, decs)
			| buildIt _ = raise Domain

		      fun remove(0, args) = args
			| remove(n, _::args) = remove(n-1, args)
			| remove _ = raise Domain

		      val args = buildIt(num, numPats, Kdecs)
		      val numPats' = numPats - num
		      val Kdecs' = remove(num, Kdecs)
		   in
		     buildApps(DI.App(r, E, args), numPats', Kdecs', F)
		   end
	    | buildAppsW _ = raise Domain 

	  (* worldFun' = eps x1 x2 x3 . fn [x1, x2, x3] => worldFun x1 x2 x3 *)
	  fun buildNewE (F, numRemaining, Kdecs) = buildNewEW (D'.whnfF F, numRemaining, Kdecs)
	  and buildNewEW (_, 0, Kdecs) = 
	        DI.Match(r, 
			 buildArgs(numPats, Kdecs), 
			 buildApps(DI.substE(worldFun, DI.shift numPats), numPats, Kdecs, Fresult (* we just use the form
												   * of Fresult,
												   * so we do not need 
												   * to apply ay shifts *) ))
	    | buildNewEW (D'.All(Ds, F), numRemaining, Kdecs) =
	            let
		      fun createEps [] C = C
			| createEps ((vis, D)::Ds) C = DI.Eps(r, convert2Normal (r, D), createEps Ds C)

		      val num = List.length Ds
		      val _ = if (numRemaining < num) then
			        raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))
			      else ()
		    in
		      createEps Ds (buildNewE(F, numRemaining-num, Kdecs @ Ds))
		    end
	    | buildNewEW (F, _, _) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))

	  val worldFun' = DI.Lam(false, r, [buildNewE (Fresult, numPats, [])], SOME newWorldFunType)

	  fun buildCurriedFunction (F, numRemaining, Kdecs) = buildCurriedFunctionW (D'.whnfF F, numRemaining, Kdecs)
	  and buildCurriedFunctionW (_, 0, Kdecs) = 
			    DI.App(r, DI.substE(DI.ExtendFunWith(r, 
								 worldFun', 
								 Clist, 
								 sizeG2a, 
								 sizeG2b,
								 false (* not sugar *),
								 SOME newWorldFunType), 
						DI.shift(numPats)), 
				   buildArgs(numPats, Kdecs))
	   (* No news in functions we extend using 'with'
	    | buildCurriedFunctionW (D'.Nabla(D, F), numRemaining, Kdecs) = DI.New(r, convert2New (r, D), buildCurriedFunction(F, numRemaining, Kdecs))
	    *)
	    | buildCurriedFunctionW (D'.All(Ds, F), numRemaining, Kdecs) =
	            let
		      fun createEps [] C = C
			| createEps ((vis, D)::Ds) C = DI.Eps(r, convert2Normal (r, D), createEps Ds C)

		      val num = List.length Ds
		      val _ = if (numRemaining < num) then
			        raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))
			      else ()
		      val args = buildArgs (num, Ds)
		    in
		      DI.Lam(false, 
			     r, 
			     [createEps Ds (DI.Match(r, args, buildCurriedFunction(F, numRemaining - num, Kdecs @ Ds)))],
			     SOME (D'.All(Ds, F)))
		    end
	    | buildCurriedFunctionW (F, _, _) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "UNEXPECTED FATAL ERROR deSugaring"))

	in
	  buildCurriedFunction (D'.FClo(Fresult, I.Shift (sizeG2a + sizeG2b)), numPats, [])
	end

   fun deSugarExtend(smartInj, G, r, E, [], sizeG2a, sizeG2b, Fresult) = 
        let
	  (* G = GB,G2a,G2b *)
	  (* GB |- Fresult  wff *)
	  
	  (* We are dealing with an empty function, so we maximize the number of patterns we look at together *)

	  fun countNews (numNews, F) = countNewsW (numNews, D'.whnfF F)
	  and countNewsW (numNews, D'.Nabla(D, F)) = countNews(numNews+1, F)
	    | countNewsW (numNews, F) = (numNews, F)

	  val (numNews, F) = countNews(0, Fresult)

	  val _ = if numNews > 0 then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Cannot automatically extend this function")) else ()

	  fun countArgs (numArgs, F) = countArgsW (numArgs, D'.whnfF F)
	  and countArgsW (numArgs, D'.All(Ds, F)) = countArgs(numArgs+(List.length Ds), F)
	    | countArgsW (numArgs, F) = (numArgs, F)

	  val (numPats, F) = countArgs(0, F)
	in
	  if (numPats > 1) then
	    (deSugarExtend'(smartInj, G, r, E, [], sizeG2a, sizeG2b, Fresult, numPats))
	  else if (numPats = 1) then
	         DI.ExtendFunWith(r, E, [], sizeG2a, sizeG2b, false, SOME Fresult)
	       else
		 raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Cannot automatically extend this function (unexpected!)"))
	end
     | deSugarExtend(smartInj, G, r, E, Clist as (Cfirst :: _) (* not empty *), sizeG2a, sizeG2b, Fresult) =
        let
	  (* G = GB,G2a,G2b *)
	  (* GB |- Fresult  wff *)

	  fun countNumArgs (numNews, DI.Eps(r, _, C)) = countNumArgs (numNews, C)
	    | countNumArgs (numNews, DI.NewC(r, DI.NewDecLF _, C)) = countNumArgs (numNews +1, C)
	    | countNumArgs (numNews, DI.NewC(r, DI.NewDecWorld _, C)) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "We do not support meta-level (world) news now."))
(* Removed PopC from intermediate syntax
	    | countNumArgs (numNews, DI.PopC (r, i, C)) = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "We no longer support different pops over different cases and cannot automatically convert this one... fix manually."))
*)
	    | countNumArgs (numNews, DI.Match (_, pats, _)) = (List.length pats, numNews)

	  val (numPats, numNews) = countNumArgs (0, Cfirst)


	  val _ = if numNews > 0 then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Cannot automatically extend this function")) else ()

	 in
	   if isFun Fresult
	     then if numPats > 1 then 
	          deSugarExtend'(smartInj, G, r, E, Clist, sizeG2a, sizeG2b, Fresult, numPats)
		  else (* (numPats == 1) *)
		    DI.ExtendFunWith(r, E, Clist, sizeG2a, sizeG2b, false, SOME Fresult)
	   else 
	     raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Cannot desugar 'with'...  ambiguous type!"))
	       (* This may be able to happen if Fresult is a FVar with constraints,
		* but we first do one run updating the types of all Lams (updateLams...), so that if this error happens
		* it is truly an ambiguous type which will never be filled in!
		*)
	 end





   fun convertExp (smartInj, G, DI.VarInt (r, i), Tresult) =
         let
	   val (name, T) = lookupInt(r, i, G, i)
	   val (Wopt, T) = case T of
	                      D'.Meta F => (case D'.whnfF F
					     of D'.Nabla (D'.NewDecWorld (_, W), F) => (SOME W, D'.Meta (D'.FClo(F, I.invShift)))
					      | _ => (NONE, T))
			    | D'.LF _ => (NONE, T)

	   val s = case name of 
	             NONE => "#" ^ (Int.toString i)
		   | SOME s => s
	   val _ = unifyTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", G, Tresult, T)

	 in
	   case Wopt 
	     of NONE => D'.Var (D'.Fixed i, SOME(!filename, r))
	      | SOME W =>
		    let
		      fun findWorldIndex (0, G, num) = NONE
			| findWorldIndex (max, I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _)), num) =
			                 (case (findWorldIndex (max-1, G, num+1))
								   of NONE => SOME num
								    | SOME num' => SOME num')
			| findWorldIndex (max, I.Decl(G, _), num) = (findWorldIndex(max-1, G, num+1))
			| findWorldIndex (max, I.Null, num) = raise Domain (* badly typed... *)
								     
		      val popNum = case (findWorldIndex (i-1, G, 1))
			           of NONE => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), ("Cannot automatically Weaken (add pop)" ^ s)))
				    | SOME n => n

		    in
		      D'.Pop (popNum, D'.Var (D'.Fixed (i-popNum), SOME(!filename, r)), SOME(!filename, r))
		    end

	 end

     | convertExp (smartInj, G, E as DI.Quote (r, M, A, DA.InjLF, isP), Tresult) =
	 (case (D'.whnfP isP)
	    of D'.Existential => 
		     let	  
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.LF(D'.Existential, A))
		     in
		       D'.Quote M
		     end
	     | D'.Param =>
		     (let
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.LF(D'.Param, A))
		       val n = Whnf.etaContract M
		       val _ = case (I.ctxLookup (G, n))
			       of (D'.InstantiableDec (D'.NormalDec (_, D'.LF (isP, _)))) => 
				                                                let
										  val _ = U.unifyP(isP, D'.Param)
										    handle U.Error msg => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))
										in
										  ()
										end
				|  (D'.NonInstantiableDec (D'.NewDecLF _)) => ()
			        | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))
		     in
		       D'.Var (D'.Fixed n, SOME(!filename, r))
		     end handle Whnf.Eta => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Expected Variable.")))
	     | (D'.PVar p) =>
		     let
		       val _ = (p := SOME (D'.Existential))  (* If it is ambiguous.. make it existential... *)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.LF(D'.Existential, A))
		     in
		       D'.Quote M
		     end
         )

		   

     | convertExp (smartInj, G, E as DI.Quote (r, M, A, DA.InjMeta, isP), Tresult) =
	 (case (D'.whnfP isP)
	    of D'.Existential => 
	             let
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(D'.Existential, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(F))
		     in
		       D'.Pair (D'.Quote M, D'.Unit, F)
		     end

	     | D'.Param =>
		     (let
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(D'.Param, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(F))
		       val n = Whnf.etaContract M
		       val _ = case (I.ctxLookup (G, n))
			       of (D'.InstantiableDec (D'.NormalDec (_, D'.LF (isP, _)))) => 
				                                                let
										  val _ = U.unifyP(isP, D'.Param)
										    handle U.Error msg => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))
										in
										  ()
										end
				|  (D'.NonInstantiableDec (D'.NewDecLF _)) => ()
			        | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Types (w.r.t. parameter status)"))

		     in
		       D'.Pair (D'.Var (D'.Fixed n, SOME(!filename, r)), D'.Unit, F)
		     end handle Whnf.Eta => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Expected Variable.")))
	     | (D'.PVar p) =>
		     let
		       val _ = (p := SOME (D'.Existential))  (* If it is ambiguous.. make it existential... *)
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(D'.Existential, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(F))
		     in
		       D'.Pair (D'.Quote M, D'.Unit, F)
		     end
         )


     | convertExp (smartInj, G, DI.Quote (r, M, A, DA.InjVar(ref (SOME I)), isP), Tresult) = convertExp (smartInj, G, DI.Quote(r, M, A, I, isP), Tresult)
     | convertExp (smartInj, G, DI.Quote (region, M, A, DA.InjVar(r as ref NONE), isP), Tresult) =
	     ( (* It can be either LF or Meta, so we pick Meta *)
	      r := SOME DA.InjMeta ;
	      convertExp(smartInj, G, DI.Quote(region, M, A, DA.InjMeta, isP), Tresult))
	      



     | convertExp (smartInj, G, DI.Unit r, Tresult) = 
	   let
	     val _ = unifyTypes(smartInj, r, "() has incompatible type", G, Tresult, D'.Meta(D'.Top))
	   in
	     D'.Unit
	   end

     | convertExp (smartInj, G, DI.Lam (isSugar, r, Clist, Fopt), Tresult) =
	      let
		val F = case Fopt
		        of SOME F => F
			 | _ => D'.newFVar(D'.coerceCtx G)

		val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))

	       (* ENHANCEMENT to improve chances for coverage
	        * If all the cases start with NewC, then move it to the outside.
		*)
		fun removeNew [DI.NewC (_, D, C)] = SOME(D, [C])
		  | removeNew (DI.NewC(_, D, C) :: Clist) =
	                                    (case (removeNew Clist)
					       of NONE => NONE
						| SOME(D, Clist') => SOME(D, C::Clist'))
		  | removeNew _ = NONE
					       

		val moveNew = removeNew Clist
	   in
	     case (moveNew, isSugar)
	       of (SOME(D, Clist'), _) => 
		      let
			val D' = convertNewDec(G, D)
			val G' = I.Decl(G, D'.NonInstantiableDec D')
			val newResult = D'.newFVar(D'.coerceCtx G')
			val nablaType = D'.Meta(D'.Nabla(D', newResult))
			val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, nablaType)
		      in 
			convertExp(smartInj, G, DI.New(r, D, DI.Lam(isSugar, r, Clist', SOME newResult)), Tresult)
		      end

		| (NONE, false) =>
		      let
			val Clist' = map (fn C => convertCase(smartInj, G, C, Tresult)) Clist
		      in
			D'.Lam(Clist', F, SOME(!filename, r))
		      end
		| (NONE, true) =>
			convertExp (smartInj, G, deSugarCases(smartInj, G, r, Clist, F), Tresult)


	   end


     | convertExp (smartInj, G, DI.New(r, D, E), Tresult) =
	   let
	     val D' = convertNewDec(G, D)
	     val G' = I.Decl(G, D'.NonInstantiableDec D')
	     val newResult = D'.newFVar(D'.coerceCtx G')
	     val nablaType = D'.Meta(D'.Nabla(D', newResult))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, nablaType)

	     val E' = convertExp(smartInj, G', E, D'.Meta(newResult))
	   in
	     D'.New(D', E', SOME(!filename, r))
	   end


     | convertExp (smartInj, G, DI.App(r, E1, args), Tresult) = 
	   let
	     val funF = D'.newFVar(D'.coerceCtx G)
	     val E1' = convertExp(smartInj, G, E1, D'.Meta(funF))

	     fun processArgs (args, F) = processArgsW(args, D'.whnfF F)
	     and processArgsW ((vis,E2)::args, D'.All((vis', D'.NormalDec (_, T))::Ds, F)) =
		  let
		    val _ = case (vis, vis')
		        of (D'.Visible, D'.Visible) => ()
		         | (D'.Implicit, D'.Implicit) => ()
			 | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Visibility in Patterns"))

		    val E2' = convertExp(smartInj, G, E2, T)
		    val t' = I.Dot (D'.coerceExp E2', I.id)
		    val (args', Frest) = processArgs(args, D'.FClo(D'.All(Ds, F), t'))
		  in
		    ((vis, SOME(!filename, Paths.join(DI.getRegionExp E1, DI.getRegionExp E2)), E2') :: args', Frest)
		  end
	       | processArgsW ([], D'.All([], F)) = ([], F)
	       | processArgsW (args, D'.All([], F)) = 
		  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected remaining args"))
	       | processArgsW _ =   raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Args"))
						   
		    
	     val funF = makeForAll(false, smartInj, r, G, args, funF) (* makes funF a Forall ... *)
	     val (args', Frest) = processArgs (args, funF)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(Frest))
	   in
	     D'.App(E1', args')
	   end

     | convertExp (smartInj, G, DI.Pair(r, E1, E2), Tresult) = 
	   let
	     val F = D'.newFVar(D'.coerceCtx G)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(F))

		       
	     val firstType = inferType(G, E1)
	     val D = D'.NormalDec(NONE, firstType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val secondF = D'.newFVar(D'.coerceCtx G')
	     val pairF = D'.Exists(D, secondF)
	     val pairType = D'.Meta(pairF)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, pairType)

	     val E1' = convertExp(smartInj, G, E1, firstType)
	     val t = D'.Dot(D'.Prg E1', D'.id)
	     val E2' = convertExp(smartInj, G, E2, D'.Meta(D'.FClo(secondF, D'.coerceSub t)))
	   in
	     D'.Pair(E1', E2', F)
	   end


     | convertExp (smartInj, G, DI.Proj (r, E, i), Tresult) =
	   let
	     val F = D'.newFVar (D'.coerceCtx G)
	     val T = D'.Meta(F)

	     val E' = convertExp (smartInj, G, E, T)
	 
             (* F must have been instantiate to a FormList, otherwise we return an error *)
	     val Flist = case (D'.whnfF F)
	                    of (D'.FormList Flist) => Flist
			     | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected Projection (automatic for mutual recursion... this should not happen!"))

	     val _ = if ((List.length Flist) < i)
	             then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Badly formed Projection (automatic for mutual recursion... this should not happen!"))
		     else ()

	     val Tinferred = getIndexN(i, D'.FormList Flist)


	     val (Wopt, T) = case Tinferred of
	                      D'.Meta F => (case D'.whnfF F
					     of D'.Nabla (D'.NewDecWorld (_, W), F) => (SOME W, D'.Meta (D'.FClo(F, I.invShift)))
					      | _ => (NONE, Tinferred))
			    | D'.LF _ => (NONE, Tinferred)


	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, T)
	   in
	     case Wopt
	       of NONE => D'.Proj (E', i)
		| SOME W =>
		    let
		      fun findWorldIndex (0, G, num) = NONE
			| findWorldIndex (max, I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _)), num) =
			                 (case (findWorldIndex (max-1, G, num+1))
								   of NONE => SOME num
								    | SOME num' => SOME num')
			| findWorldIndex (max, I.Decl(G, _), num) = (findWorldIndex(max-1, G, num+1))
			| findWorldIndex (max, I.Null, num) = raise Domain (* badly typed... *)
			

		      val j = case E
			      of DI.VarInt (_, j) => j
			       | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), ("Badly formed projection")))

		      val popNum = case (findWorldIndex (j-1, G, 1))
			           of NONE => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), ("Cannot automatically Weaken (add pop)")))
				    | SOME n => n

		    in
		      D'.Pop (popNum, D'.Proj(D'.Var (D'.Fixed (j-popNum), SOME(!filename, r)), i), SOME(!filename, r))
		    end
	   end


     | convertExp (smartInj, G, DI.Pop(r, i, E), Tresult) = 
	   let
	     fun popCtx(1, I.Decl(G, D'.NonInstantiableDec (D as D'.NewDecLF _))) = (D, G)
	       | popCtx(1, I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _))) = raise Domain (* do not allow pop on worlds... *)
	       | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
	       | popCtx(0, _) = raise Domain
	       | popCtx _ = raise Domain

	     val (D, G') = popCtx(i, G)	       

	     val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
	     val T = D'.Meta(D'.Nabla(D, F))
	     val Tshift = D'.Meta(D'.FClo(F, I.Shift (i-1)))

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)

	     val E' = convertExp(smartInj, G', E, T)
	   in
	     D'.Pop(i, E', SOME(!filename, r))
	   end

     (* not used 
     | convertExp (smartInj, G, DI.Fix(r, funList), Tresult) =  D'.Fix (convertFunList(smartInj, G, r, funList, Tresult))
     *)
	     
     | convertExp (smartInj, G, DI.PatVar _, _) = raise Domain (* PatVar should be eliminated by abstraction BEFORE calling this function *)

     (* syntactic sugar *)


     | convertExp (smartInj, G, DI.TypeAscribe (r, E as DI.Quote _, T), Tresult) =
	   let
	     (* ENHANCEMENT:  If E is Quote and T is an implicit function,
	      * then first apply the implicit function to some args
	      *)

	     fun applyImplicitFun (T as D'.LF _) = T
	       | applyImplicitFun (D'.Meta(F)) = D'.Meta(applyImplicitFunF F)

	     and applyImplicitFunF F = applyImplicitFunFW (D'.whnfF F)
	     and applyImplicitFunFW (D'.All((D'.Implicit, D'.NormalDec (_, D'.LF(isP, A)))::Ds, F)) = 
	          let
		    val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
		    val Q = DI.Quote(r, X, A, DA.InjLF, isP)
		    val t' = I.Dot(coerceExp Q, I.id)
		  in
		    applyImplicitFunF(D'.FClo(D'.All(Ds, F), t'))
		  end
		| applyImplicitFunFW (D'.All((D'.Visible, _)::Ds, F)) = 
		     raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Ascribed functional type to LF expression."))
		| applyImplicitFunFW (D'.All([], F)) = applyImplicitFunF F
	        | applyImplicitFunFW F = F


	     val T' = applyImplicitFun (convertTypes(G, T))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, T')
	   in
	     convertExp(smartInj, G, E, Tresult)
	   end


     | convertExp (smartInj, G, DI.TypeAscribe (r, E, T), Tresult) = 
	   let
	     val T' = convertTypes(G, T)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, T')

	   in
	     convertExp(smartInj, G, E, Tresult)
	   end


     | convertExp (smartInj, G, DI.Sequence Elist, Tresult) =
	   let
	     val _ = if (List.length Elist < 2) then raise Domain (* List must have at least 2 elements *) else ()

	     fun getRegion [(r, _)] = r
	       | getRegion ((r, _) :: rest) = Paths.join(r, getRegion rest)
	       | getRegion _ = raise Domain

	     val r = getRegion Elist

	     val Fresult = D'.newFVar(D'.coerceCtx G)
	     val _ = unifyTypes(smartInj, r, "Sequence must end with formula type", G, Tresult, D'.Meta(Fresult))

	     fun convertList [(_, E)] = 
	                              let
					val E' = convertExp(smartInj, G, E, Tresult)
				      in
					[(E', Tresult)]
				      end
	       | convertList ((_, E):: Elist) =
				      let
					val T = inferType(G, E)
					val E' = convertExp(smartInj, G, E, T)
					val rest = convertList Elist
				      in
					(E', T) ::rest
				      end
	       | convertList _ = raise Domain (* cannot have an empty list in a sequence *)

	       

	     fun buildFormula [_] = Fresult
	       | buildFormula ((_, T) :: rest) =
	                          let
				    val D = D'.NormalDec(NONE, T)
				    val F = buildFormula rest
				  in
				    D'.All([(D'.Visible, D)], D'.FClo(F, I.shift))
				  end
	       | buildFormula _ = raise Domain

	     fun buildLam [(E, _)] _ = E
	       | buildLam ((E, _)::rest) (F as D'.All([(vis, D)], F')) =
	                          let
				    val E' = buildLam rest F'
				    val C = D'.Eps(D, D'.Match ([(vis, D'.Var (D'.Fixed 1, NONE))], D'.EClo(E', D'.shift)), NONE)
				  in
				    D'.Lam ([C], F, SOME(!filename, r))
				  end
	       | buildLam _ _ = raise Domain


	     fun buildApp (lamExp, [_]) = lamExp
	       | buildApp (lamExp, (E, _)::rest) = buildApp(D'.App(lamExp, [(D'.Visible, SOME(!filename, r), E)]), rest)
	       | buildApp _ = raise Domain

	     val expTypeList = convertList Elist
	     val F = buildFormula expTypeList
	     val function = buildLam expTypeList F

	     val final = buildApp (function, expTypeList)
	   in
	     final
	   end
 
     | convertExp (smartInj, G, DI.LetFun (r, funList, E2), Tresult) = 
	   let
	     val (D', E') = convertFunList(smartInj, G, r, funList, D'.Meta(D'.newFVar (D'.coerceCtx G)))

	     val G' = I.Decl(G, D'.InstantiableDec D')
	     val F = D'.newFVar (D'.coerceCtx G')
	     val Tshift = D'.substTypes(Tresult, I.shift)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G', Tshift, D'.Meta(F))

	     val E2' = convertExp(smartInj, G', E2, Tshift)

	     val fixE = D'.Fix (D', E')


	     val C' = D'.Eps (D', D'.Match ([(D'.Visible, D'.Var (D'.Fixed 1, (SOME(!filename, r))))], E2'), NONE)
	   in
	     D'.App(D'.Lam ([C'],D'.All([(D'.Visible, D')], F), SOME(!filename, r)), [(D'.Visible, SOME(!filename, r), fixE)])
	   end



       | convertExp (smartInj, G, DI.ExtendFunWith (r, E, Clist, sizeG2a, sizeG2b, true (* isSugar *), Fopt), Tresult) =
	   let
	     val GB = D'.popCtx(sizeG2a+sizeG2b, G)

	     val Fresult = case Fopt
	                 of SOME F => F
			  | NONE => D'.newFVar(D'.coerceCtx GB)


	     val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.FClo(Fresult, I.Shift(sizeG2a+sizeG2b))))

	     val Eextend = deSugarExtend(smartInj, G, r, E, Clist, sizeG2a, sizeG2b, Fresult)
	   in
	     convertExp(smartInj, G, Eextend, Tresult)
	   end

       | convertExp (smartInj, G, DI.ExtendFunWith (r, E, Clist, sizeG2a, sizeG2b, false (* not sugar *), Fopt), Tresult) =
	   let
		 (*
		  (bool represents isSugar)
		  GB |- E : T
		  GB, G2a |- CS : T
                  and first and last elements of G2a are NonInstantiable
		  ------------------------------------------------------
	          GB, G2a, G2b |- ExtendFunWith(E, CS, sizeG2a, sizeG2b, bool, Fopt) : T

	          (D.Formula option) = T (which makes sense in GB)
		 *)
	     val GB = D'.popCtx(sizeG2a+sizeG2b, G)
	     val GBG2a = D'.popCtx(sizeG2b, G)

	     val Fresult = case Fopt
	                 of SOME F => F
			  | NONE => D'.newFVar(D'.coerceCtx GB)


	     val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.FClo(Fresult, I.Shift(sizeG2a+sizeG2b))))

	     val E' = convertExp (smartInj, GB, E, D'.Meta(Fresult))
	     val Clist' = map (fn C => convertCase(smartInj, GBG2a, C, D'.Meta(D'.FClo(Fresult, I.Shift sizeG2a)))) Clist
	   in
	     createExtendFun(smartInj, r, G, sizeG2a, sizeG2b, E', Clist', D'.Meta(Fresult))
	   end
	     

    and convertFunList (smartInj, G, r, funList, Tresult) =
	   let
	     val decList  = map (fn (_,D,_) => convertNormalDec(G, D)) funList 
	     fun decListString [D'.NormalDec(SOME [s], _)] = [s]
	       | decListString ((D'.NormalDec(SOME [s], _)) :: decs) = s :: (decListString decs)
	       | decListString _ = raise Domain (* badly formed fixpoint *)

	     fun decListFormulas [D'.NormalDec(_, D'.Meta(F))] = [F]
	       | decListFormulas ((D'.NormalDec(_, D'.Meta(F))) :: decs) = F :: (decListFormulas decs)
	       | decListFormulas _ = raise Domain (* badly formed fixpoint *) 


	     fun decListFormula [F] = F
	       | decListFormula Flist = D'.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(F))


	     val D = D'.NormalDec (SOME (decListString decList), D'.Meta(F))
	     val G' = I.Decl(G, D'.InstantiableDec D)
	       
	     (* We need to shift the formula so it makes sense in G' *)
	     fun pairFormula ([], []) = []
	       | pairFormula ((_, _, E)::fList, F::formList) = (E, D'.FClo(F,I.shift)) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)


	     val expList = map (fn (E,F) => convertExp(smartInj, G', E, D'.Meta(F))) expFormList


	     fun listToExp [E] = E
	       | listToExp Elist = D'.ExpList Elist


	     val E = listToExp expList

	   in
	     (D, E)
	   end
      


    and convertCase (smartInj, G, DI.Eps(r, D, C), Tresult) =
                                  let
				    val D' = convertNormalDec(G, D)
				    val G' = I.Decl(G, D'.InstantiableDec D')
				    val C' = convertCase(smartInj, G', C, D'.substTypes(Tresult, I.shift))
				  in
				    D'.Eps(D', C', SOME(!filename, r))
				  end


      | convertCase (smartInj, G, DI.NewC(r, D, C), Tresult) =
				  let
				    val D' = convertNewDec (G, D)
				    val G' = I.Decl(G, D'.NonInstantiableDec D')
				    val newResult = D'.newFVar(D'.coerceCtx G')
				    val nablaType = D'.Meta(D'.Nabla(D', newResult))
				    val _ = unifyTypes(smartInj, r, "New has incompatible type", G, Tresult, nablaType)

				    val C' = convertCase(smartInj, G', C, D'.Meta(newResult))
				  in
				    D'.NewC(D', C', SOME(!filename, r))
				  end
(* Removed PopC from intermediate syntax
      | convertCase (smartInj, G, DI.PopC(r, i, C), Tresult) =
				  raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "We no longer support different pops over different cases and cannot automatically convert this one... fix manually."))
				  (* no longer have D'.PopC 
				  let
				    fun popCtx(1, I.Decl(G, D'.NonInstantiableDec (D as D'.NewDecLF _))) = (D, G)
				      | popCtx(1, I.Decl(G, D'.NonInstantiableDec (D'.NewDecWorld _))) = raise Domain
				      | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
				      | popCtx(0, _) = raise Domain
				      | popCtx _ = raise Domain
				      
				    val (D, G') = popCtx(i, G)	       

				    val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
				    val T = D'.Meta(D'.Nabla(D, F))
				    val Tshift = D'.Meta(D'.FClo(F, I.Shift (i-1)))

				    val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)
				      
				    val C' = convertCase(smartInj, G', C, T)
				  in
				    D'.PopC(i, C')
				  end
				   *)
*)

      | convertCase (smartInj, G, DI.Match(r, [], E2), Tresult) = raise Domain (* impossible *)

      | convertCase (smartInj, G, DI.Match(r, pats, E2), Tresult) =
				    (* must not be sugar.. it would have been desugared in lam *)
				  let
				    val F = D'.newFVar(D'.coerceCtx G)
				    val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(F))


				    fun processPats (pats, F) = processPatsW(pats, D'.whnfF F)
				    and processPatsW ((vis, E1)::pats, D'.All((vis', D'.NormalDec (_, T))::Ds, F)) =
					       let
						 val _ = case (vis, vis')
						           of (D'.Visible, D'.Visible) => ()
							    | (D'.Implicit, D'.Implicit) => ()
							    | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Visibility in Patterns"))

						 val (E1') = convertExp(smartInj, G, E1, T)
						 val t' = I.Dot (D'.coerceExp E1', I.id)
						 val (pats', Frest) = processPats(pats, D'.FClo(D'.All(Ds, F), t'))
					       in
						 ((vis, E1') :: pats', Frest)
					       end
				      | processPatsW ([], D'.All([], F)) = ([], F)
				      | processPatsW (pats, D'.All([], F)) = 
					       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexpected remaining pats"))
				      | processPatsW (pats, F) =   raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Incompatible Number of Pats"))

						   
				    val F = makeForAll(false, smartInj, r, G, pats, F) (* makes F a Forall ... *)
				    val (pats', Frest) = processPats (pats, F)
				    val E2' = convertExp(smartInj, G, E2, D'.Meta(Frest))

				  in
				    D'.Match(pats', E2')
				  end



  (* ***************************************************************************************************** *)
  (* ***************************************************************************************************** *)
  (* 
   * Putting it together.
   *
   *)
  (* ***************************************************************************************************** *)
  (* ***************************************************************************************************** *)
   (* Checks that all variables in a list are instantiated.. if not, it raises Error *)

   fun convertFormula0 (G, F) =
         let
	   val (_, job, f1) = convertFormula2Temp(G, I.Null, F)
	   val r = D.getRegFormula F
	   val FI  = lfReconstruction(G, job, f1, r)

	   val FI2 = (DelphinAbstract.addImplicitTypesForm (FI, I.Null)
	       handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		    | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg)))

	   val F' = convertFormula(G, FI2)
	   val Fapprox = DA.exact2ApxFormula F'
	 in
	   (Fapprox, F')
	 end

   fun convertMeta0 (smartInj, G, E) =
         let
	   val Tapx = inferTypeApx (smartInj, G, I.Null, E)
	   val (job, f) = convertExp2Temp(smartInj, G, I.Null, E, Tapx)
	   val r = D.getRegExp E
	   val E' = lfReconstruction(G, job, f, r)

	   val Tresult = inferType (G, E')
	   val (E', _) = updateExp(smartInj, G, E', Tresult, I.Null) (* changes approx types to exact types (fills in LF EVars) and fills in InjVars *)
	   val E' = DelphinAbstract.abstractPatVarsExp (r, E', convert2Types (r, Tresult))
	     handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		  | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg))

	   val Tresult = inferType (G, E')  (* abstraction may have changed the type of E' *)
	   val (E') = updateLamsExp(smartInj, G, E', Tresult) (* abstraction removed type information on Lams,
							       * so this puts it back before calling convert.
							       * We need this type information to "deSugar" the
							       * case statements appropriately.
							       *)


	   (* FOR COVERAGE... *)
	   (* COVERAGE:  As this is a fixpoint, we specify that it is weakenable by the specified world.
	    * To do this, we add Nabla{W} to the type as well as add "New{W}" to the term. 
	    * (if coverage is disabled, these procedures don't do anything)
	    *)
	   val Tresult = addWorldT(D'.VarList [] (* empty world *), Tresult)
	   val E' = addWorldE(D'.VarList[] (* empty world *), E', r)
	   (* END FOR COVERAGE... *)


	   val Eresult = convertExp(smartInj, G, E', Tresult)

	   val _ = D'.updatePVarsTypes Tresult
	   val _ = D'.updatePVarsExp Eresult


	 in
	   if ((NormalizeDelphin.hasFVarsExp Eresult) orelse (NormalizeDelphin.hasFVarsTypes Tresult))
	     (* we removed PVars, and we abstracted away LF level FVars  and EVars, so we may now encounter Formula Variables (Meta FVars) *)
	     then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Leftover Variables (ambiguous typing)"))
	   else

	     (Eresult, Tresult)
	 end


   fun convertFixList0 (smartInj, G, funList) = 
         let
	   fun getRegion [] = raise Domain
	     | getRegion [(r,_,_)] = r
	     | getRegion ((r,_,_)::xs) = Paths.join(r, getRegion xs)

	   val r = getRegion funList
	   val Tapx = DA.Meta(r, DA.FVar (r, ref NONE))

	   val (Dapprox, job, f) = convertFunList2Temp(smartInj, G, I.Null, r, funList, Tapx)

	   val funList' = lfReconstruction(G, job, f, r)
	   val T = D'.Meta(D'.newFVar (D'.coerceCtx G))
	   val (_, funList', _) = updateFunList(smartInj, G, r, funList', T, I.Null) (* changes approx types to exact types (fills in LF EVars) *)
	   val funList' = DelphinAbstract.abstractPatVarsFunList (funList')
	     handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		  | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg))

	   val T = D'.Meta(D'.newFVar (D'.coerceCtx G)) (* we can't use old T because abstraction can change the type *)

	   val (_, funList') = updateLamsFunList(smartInj, G, r, funList', T) 
	                                                             (* abstraction removed type information on Lams,
								      * so this puts it back before calling convert.
								      * We need this type information to "deSugar" the
								      * case statements appropriately.
								      *)

	   (* FOR COVERAGE... *)
	   (* COVERAGE:  As this is a fixpoint, we specify that it is weakenable by the specified world.
	    * To do this, we add Nabla{W} to the type as well as add "New{W}" to the term. 
	    * (if coverage is disabled, these procedures don't do anything)
	    *)
	   val funList' = addWorldflist(!globalWorld, funList')
	   val T = addWorldT (!globalWorld, T)
	   (* END FOR COVERAGE... *)


	   val (D', E') = convertFunList (smartInj, G, r, funList', T)

	   (* Instantiate all ambiguous PVars as Existential *)
	   val _ = D'.updatePVarsNormalDec D'
	   val _ = D'.updatePVarsExp E'


	   val result = D'.Fix (D', E')

	 in
	   if (NormalizeDelphin.hasFVarsExp result)
	     (* we removed PVars, and we abstracted away LF level FVars and EVars, so we may now encounter Formula Variables (Meta FVars) *)
	     then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Leftover Variables (ambiguous typing)"))
	   else
	     result
	 end

   (* convertWorldVar W = (G, A')
    * where W is converted into A' and the free variables are captured in G
    * G |- A' : type (without EVars/FVars)
    *)
   fun convertWorld2Temp (ReconG, D.WorldType A) =
         let
	   val r = D.getRegLFExp A
	   val t = tokensToTerm (PrintDelphinExt.lfexpToTokens A)
	   val A = Approx.newCVar()
	   val job = ReconTerm.jtypeEqualApx(t, A) (* this indicates the object is a "type" *)
	   fun f (ReconTerm.JClass ((A, _), _ (* type *))) = DI.WorldType (r, A)
	     | f _ = raise Domain
	 in
	   (job, f)
	 end

     | convertWorld2Temp (ReconG, D.WorldEps(r, D, W)) =
          let
	    val (Drecon, Dapprox, job1, f1) = convertNormalDec2Temp (I.Null (* global G is empty *), ReconG, D)
	    val (job2, f2) = convertWorld2Temp (I.Decl(ReconG, DA.InstantiableDec(r, Dapprox)), W)

	    fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(I.Decl(_, D),jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val C'' = f2 jobResult2
		  in
		    DI.WorldEps(r, D'', C'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon),job2)) , f)
	  end

	   
	     
   fun convertWorldVar W =
         let
	   val r = D.getRegLFExpWorld W
	   val (job, f) = convertWorld2Temp(I.Null, W)
	   val W' = lfReconstruction(I.Null (* global G is emtpy *), job, f, r)

	   val W'' = DelphinAbstract.addSomeVars W'
	             handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
			  | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg))

           (* Precondition:  No EVars.. *)
	   fun occursLF_Exp (p, Us) = occursLF_ExpW (p, Whnf.whnf Us)
	   and occursLF_ExpW (_, (I.Uni _, _)) = false
	     | occursLF_ExpW (p, (I.Lam (D, U), s)) = occursLF_Dec(p, (D, s)) orelse occursLF_Exp (p+1, (U, I.dot1 s))
	     | occursLF_ExpW (p, (I.Pi ((D', _), U), s)) = occursLF_Dec (p, (D', s)) orelse occursLF_Exp (p+1, (U, I.dot1 s))
	     | occursLF_ExpW (p, (I.Root (H, S), _(* id *) )) =
		      (case H
			 of (I.BVar (I.Fixed k')) => 
			          if (k' = p) then true
				  else occursSpine (p, (S, I.id))
		       | I.BVar (I.BVarVar ((r, A, list, cnstrs), s)) => occursLF_Exp(p, (A, s)) orelse occursSpine(p, (S, I.id))
		       | _ => occursSpine (p, (S, I.id)))
	     | occursLF_ExpW (p, (I.EVar(r, G, A, cnstrs), s)) = raise Domain
	     | occursLF_ExpW (p, Us (* anything else *) ) = false (* not in Delphin (i.e. fgnexp) *)

	   and occursLF_Dec (p, (I.Dec (_, V), s)) = occursLF_Exp (p, (V, s))
	     | occursLF_Dec _ = raise Domain (* unexpected dec *)

	   and occursSpine (_, (I.Nil, _)) = false
	     | occursSpine (p, (I.App (U, S), s)) =  occursLF_Exp (p, (U, s)) orelse occursSpine (p, (S, s))
	     | occursSpine (p, (I.SClo (S, s'), s)) = occursSpine (p, (S, I.comp(s', s)))


	    fun makeDecCtx I.Null = I.Null
	      | makeDecCtx (I.Decl(G, D)) = I.Decl(makeDecCtx G, D'.InstantiableDec D)

           (* W'' is of the form eps[...]. <A>.  We want to convert the eps's into a context. *)
	   (* We also check that all SOME variables actually occur free.. if not then raise an error *)
	   (* This "occurs" check will also enforce the invariant that ALL SOME variables are LF (not Meta) *)
	   fun convertWorld (ctxK, DI.WorldEps (_, D, W)) = 
	            let
		      val D' = convertNormalDec (makeDecCtx ctxK, D)
		    in
		      convertWorld (I.Decl(ctxK, D'), W)
		    end
	     | convertWorld (ctxK, DI.WorldType (r, A)) = 
	             let
		       fun getName(SOME [s], _) = s
			 | getName (_, i) = "#" ^ (Int.toString i)

		       fun checkFree(varNum, I.Null) = ()
			 | checkFree(varNum, I.Decl(G, D'.NormalDec(name, _))) =
			          if occursLF_Exp(varNum, (A, I.id)) then checkFree(varNum +1, G)
				  else raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ getName(name, varNum) ^ " does not occur in the type!"))

		       val _ = checkFree(1, ctxK)
		     in
		       (ctxK, A)
		     end
	 in
	   convertWorld (I.Null, W'')
	 end

   fun convertWorld (D.Anything) = D'.Anything
     | convertWorld (D.Variables varList) = D'.VarList (map convertWorldVar varList)

  end