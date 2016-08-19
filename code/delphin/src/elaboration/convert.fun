(* Delphin Elaborator (convert from external to internal syntax) *)
(* Author: Adam Poswolsky *)

structure DelphinElab : DELPHIN_ELABORATOR =
  struct
    exception Error of string
    structure D = DelphinExtSyntax  (* What we are converting from *)
    structure DI = DelphinIntermediateSyntax  (* External Syntax with LF-level filled in *)
    structure DA = DelphinApprox (* Approximate types for Delphin Types *)
    structure D' = DelphinIntSyntax (* What we are converting too *)
    structure T = DelphinTypeCheck
    structure I = IntSyn
    structure L = Lexer
    structure LS = Stream
    structure U = UnifyDelphinNoTrail
    val filename = ref "stdIn"
    val metaSigRef = ref (ref (nil : (string * DA.Formula * D'.Formula) list))  (* for type aliasing *) 
    val numFreshVars = ref 0 (* Used in conversion of lifted App..*)
      
    structure StringTree = StringRedBlackTree
    val patvarApxTable : DA.Formula StringTree.Table = StringTree.new (0)
    val patvarExactTable : (int*D'.Formula) StringTree.Table = StringTree.new (0) (* int refers to number of variables in context *)
    val patVarCtx : (D'.Dec I.Ctx) ref = ref I.Null

    fun saveApxTables () = StringTree.save patvarApxTable
    fun restoreApxTables (patvarApxT) = StringTree.restore (patvarApxTable, patvarApxT)

    fun saveExactTables () = (!patVarCtx, StringTree.save patvarExactTable)
    fun restoreExactTables (ctx, patvarExactT) = (patVarCtx := ctx ;
						  StringTree.restore (patvarExactTable, patvarExactT))

    fun getPatVarFormApx (r, name, true (*allowPatVars*) ) =
        (case StringTree.lookup patvarApxTable name
           of SOME F => F
            | NONE =>
              let
                val F = DA.FVar (r, ref NONE)
              in
                StringTree.insert patvarApxTable (name, F);
                F
              end)
      | getPatVarFormApx (r, name, false) =
        (case StringTree.lookup patvarApxTable name
           of SOME F => F
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
     
    fun saveData() = (!filename, 
		      !numFreshVars,
		      StringTree.save patvarApxTable,
		      StringTree.save patvarExactTable,
		      !patVarCtx)

    fun restoreData(file, num, patvarA, patvarE, patvarC) =
                   (filename := file ;
		    numFreshVars := num ;
		    StringTree.restore (patvarApxTable, patvarA) ;
		    StringTree.restore (patvarExactTable, patvarE) ;
		    patVarCtx := patvarC
		    )
		    
    type metaSignature = (string * DelphinApprox.Formula * DelphinIntSyntax.Formula) list

    fun reset(metaSig) = (filename := "stdIn" ; numFreshVars := 0
			  ; StringTree.clear patvarApxTable 
			  ; StringTree.clear patvarExactTable
			  ; patVarCtx := I.Null
			  ; metaSigRef := metaSig)

    fun setFilename(s) = filename := s
    fun getFilename() = !filename

    fun getFreshName () =
      let
	(* Here we create a fresh variable which is guaranteed not to be used.
	 * this is used in our conversion of lifted application
	 * as "@" is forbidden as an identify, we simply create vars as "@N"
	 *)
	val i = !numFreshVars
	val _ = numFreshVars := i+1
      in
	"@" ^ Int.toString(i)
      end

    fun typeStr(smartInj, G, T) = (PrintDelphinInt.typeToString(G, T, smartInj)
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

   fun getIndex (i, D'.Meta(isP, F)) = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error ("Fixpoint specified to have a parameter type")
		     in
		       getIndexN (i, D'.whnfF F)
		     end
     | getIndex _ = raise Domain

   and getIndexN (1, D'.FormList (F::_)) = D'.Meta(D'.Existential, F)

     | getIndexN (i, D'.FormList (_::fList)) = getIndexN(i-1, D'.FormList fList)

     | getIndexN _ = raise Domain (* fixpoint not constructed properly if it is a projection without an appropriate list of formulas *)



   fun lookupApxString (r, I.Null, s, k) = NONE
     | lookupApxString (r, I.Decl(G, (DA.InstantiableDec (_, DA.NormalDec (_, sLO, T0)))), s, k) = 
                   let
		     fun getIndex (1, DA.Meta(r, _, DA.FormList (F::_))) = DA.Meta(r, D'.Existential (* accessed via projection, so must be existential *), F)
		       | getIndex (i, DA.Meta(r, isP, DA.FormList (_::fList))) = 
		               getIndex(i-1, DA.Meta(r, isP, DA.FormList fList))
		       | getIndex _ = raise Domain

		     fun checkApxVar(s, NONE, T) = NONE
		       | checkApxVar(s : string, SOME [s'], T) = if (s=s') then (SOME (DI.VarInt (r, k), T)) else NONE
		       | checkApxVar(s, SOME sL, T) = (case (findIndex(s, sL, 1))
							    of NONE => NONE
							  | SOME n => SOME(DI.Proj(r, DI.VarInt (r, k), n), getIndex (n, T)))

		   in
		     (case checkApxVar(s, sLO, T0)
			of NONE => lookupApxString(r, G, s, k+1)
		      | SOME Tapx => SOME Tapx
	             )
		   end

     | lookupApxString (r, I.Decl(G, (DA.NonInstantiableDec (_, DA.NewDecLF (r2, SOME s', A)))), s, k) = 
					  if (s=s') then 
					    SOME(DI.VarInt (r, k), DA.LF(r2, D'.Param, A))
					  else
					    lookupApxString(r, G, s, k+1)

     | lookupApxString (r, I.Decl(G, (DA.NonInstantiableDec (_, DA.NewDecMeta (r2, SOME s', F)))), s, k) = 
					 if (s=s') then 
					   SOME(DI.VarInt (r, k), DA.Meta(r2, D'.Param, F))
					 else
					   lookupApxString(r, G, s, k+1)

     | lookupApxString (r, I.Decl(G, _), s, k) = 
					   (* Dec has no name *)
					   lookupApxString(r, G, s, k+1)


   fun getName (SOME [s]) = SOME s
     | getName _ = NONE

   fun apxDec2Type (DA.InstantiableDec (_, DA.NormalDec (_, name, T))) = (getName name, T)
     | apxDec2Type (DA.NonInstantiableDec (_, DA.NewDecLF (r, name, A))) = (name, DA.LF(r, D'.Param, A))
     | apxDec2Type (DA.NonInstantiableDec (_, DA.NewDecMeta (r, name, F))) = (name, DA.Meta(r, D'.Param, F))

     

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

     | lookupString (r, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecMeta (SOME s', F)))), s, k) = 
					 if (s=s') then 
					   SOME (DI.VarInt (r,k), DA.exact2ApxType (D'.Meta(D'.Param, F))) (* D'.substTypes(D'.Meta(D'.Param, F), I.Shift k) *)
					 else
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
     | lookupInt (r, i, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecMeta (name, F)))), 1) = (name, D'.substTypes(D'.Meta(D'.Param, F), I.Shift i))
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

   fun inferTypeApx (smartInj, G, ReconG, D.Quote (r, _), allowPatVars) = 
        if smartInj then
	      DA.SmartInj (r, Approx.newCVar(), DA.InjVar(ref NONE), D'.newPVar()) (* We need to determine if it is meant to be LF or Meta *)
	else
              DA.LF(r, D'.newPVar(), Approx.newCVar())  (* It is LF *)

     | inferTypeApx (smartInj, G, ReconG, D.VarString (r, s), allowPatVars) = 
	     let 
	       val T = case (lookupApxString (r, ReconG, s, 1))
		 of (SOME (_, T)) => T
		  | NONE => (case lookupString(r, G, s, (I.ctxLength ReconG) + 1)
			       of SOME(_, T) => T
				| NONE => 
				     (* We allow pattern variables to be upper or lowercase 
				     if (isCap s) then
				       (* Treat it as a pattern variable *)
				       DA.Meta(r, D.Existential, getPatVarFormApx (r, s))
				     else
				       raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!")))
		                      *)		                      
				     DA.Meta(r, D'.newPVar(), getPatVarFormApx (r, s, allowPatVars))
				      )
	     in 
	       T
	     end

     | inferTypeApx (smartInj, G, ReconG, D.VarInt (r, i), allowPatVars) = 
	     let
	       val n = I.ctxLength ReconG
	       val T = if (i <= n) then
		          case (apxDec2Type (I.ctxLookup(ReconG, i)))
			    of (_, T) => T
		       else
			 case (lookupInt (r, i, G, i-n))
			   of (_, T) => DA.exact2ApxType T
	     in
	       T
	     end

     | inferTypeApx (smartInj, G, ReconG, D.OmittedPat r, allowPatVars) = 
	     if allowPatVars then 
	       DA.Meta(r, D'.newPVar(), DA.FVar(r, ref NONE))
	     else
	       raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Omission not allowed!"))


     | inferTypeApx (smartInj, G, ReconG, D.TypeAscribe (_, E, _), allowPatVars) = 
	     inferTypeApx (smartInj, G, ReconG, E, allowPatVars)

     | inferTypeApx (smartInj, G, ReconG, E, allowPatVars) = 
	     let 
	       val r = D.getRegExp E
	     in
	       DA.Meta(r, D'.Existential, DA.FVar(r, ref NONE))
	     end

   fun convertIsParam(D.Existential) = D'.Existential
     | convertIsParam(D.Param) = D'.Param
     | convertIsParam(D.OmittedParam) = D'.newPVar()

   fun convertVisibility(D.Implicit) = D'.Implicit
     | convertVisibility(D.Visible) = D'.Visible


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
	    val t = tokensToTerm (PrintDelphinExt.lftypeToTokens lftype)
	    val A = Approx.newCVar()
	    val Drecon = ReconTerm.dec (sO, t, SOME A, r) 
	    val isP' = convertIsParam isP
	    val Dapprox = DA.NormalDec (r, strOpt2strListOpt sO, DA.LF(r2, isP', A))


	    fun f (ReconTerm.JNothing, I.Dec(_, V)) = DI.NormalDec (r, sO, DI.LF(r2, isP', V))
	      | f _ = raise Domain

	  in
	    (Drecon, Dapprox, ReconTerm.jnothing, f)
	  end

     | convertNormalDec2Temp (G, ReconG, D.NormalDec (r, sO, D.Meta(r2, isP, F))) =
          let
	    val (Fapprox, job, f1) = convertFormula2Temp(G, ReconG, F)

	    val Drecon = ReconTerm.ndec (sO, r)
	    val isP' = convertIsParam isP
	    val Dapprox = DA.NormalDec (r, strOpt2strListOpt sO, DA.Meta(r2, isP', Fapprox))

	    fun f (x, _ (* NDec *)) = DI.NormalDec(r, sO, DI.Meta(r2, isP', f1 x))

	  in
	    (Drecon, Dapprox, job, f)
	  end


   and convertNewDec2Temp (G, ReconG, D.NewDecLF (r, sO, lftype)) =
          let
	    val t = tokensToTerm (PrintDelphinExt.lftypeToTokens lftype)
	    val A = Approx.newCVar()
	    val Drecon = ReconTerm.dec (sO, t, SOME A, r)
	    val Dapprox = DA.NewDecLF (r, sO, A)

	    fun f (ReconTerm.JNothing, I.Dec(_, V)) = DI.NewDecLF (r, sO, V)
	      | f _ = raise Domain

	  in
	    (Drecon, Dapprox, ReconTerm.jnothing, f)
	  end

     | convertNewDec2Temp (G, ReconG, D.NewDecMeta (r, sO, F)) =
          let
	    val (Fapprox, job, f1) = convertFormula2Temp(G, ReconG, F)

	    val Drecon = ReconTerm.ndec (sO, r)
	    val Dapprox = DA.NewDecMeta (r, sO, Fapprox)

	    fun f (x, _ (* NDec *)) = DI.NewDecMeta(r, sO, f1 x)

	  in
	    (Drecon, Dapprox, job, f)
	  end



   and convertTypes2Temp (G, ReconG, D.LF(r, isP, lftype)) =
         let
	   val t = tokensToTerm (PrintDelphinExt.lftypeToTokens lftype)
	   val A = Approx.newCVar()
	    val isP' = convertIsParam isP
	   val Tapprox = DA.LF(r, isP', A)

	   val job = ReconTerm.jtypeEqualApx (t, A)

	   fun f (ReconTerm.JClass ((U,_), _)) = DI.LF (r, isP', U)
	     | f _ = raise Domain

	 in
	   (Tapprox, job, f)
	 end

     | convertTypes2Temp (G, ReconG, D.Meta(r, isP, F)) =
	 let
	   val (Fapprox, job1, f1) = convertFormula2Temp(G, ReconG, F)
	   val isP' = convertIsParam isP
	   fun f x = DI.Meta(r, isP', f1 x)
	 in
	   (DA.Meta(r, isP', Fapprox), job1, f)
	 end


     
   and convertFormula2Temp (G, ReconG, D.Top r) = 
           let
	     fun f (ReconTerm.JNothing) = DI.Top r
	       | f _ = raise Domain
	   in
	     (DA.Top r, ReconTerm.jnothing, f)
	   end
     | convertFormula2Temp (G, ReconG, D.All (r, visible, D, F)) =
	   let
	     val (Drecon, Dapprox, job1, f1) = convertNormalDec2Temp (G, ReconG, D)
	     val (Fapprox, job2, f2) = convertFormula2Temp (G, I.Decl(ReconG, DA.InstantiableDec(r, Dapprox)), F)
	     val visible' = convertVisibility visible
	     fun f (ReconTerm.JAnd(jobResult1, ReconTerm.JWithCtx(I.Decl(_, D), jobResult2))) =
	          let
		    val D'' = f1 (jobResult1, D)
		    val F'' = f2 jobResult2
		  in
		    DI.All (r, visible', D'', F'')
		  end
	       | f _ = raise Domain

	     val Dapprox = (case visible of
			      D.Visible => DA.All (r, Dapprox, Fapprox)
			    | D.Implicit => Fapprox)
		      
	   in
	     (Dapprox, ReconTerm.jand(job1, ReconTerm.jwithctx(I.Decl(I.Null, Drecon), job2)), f)
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
   and convertExp2Temp (smartInj, G, ReconG, D.VarString (r, s), allowPatVars, Tresult) = 
           let
	     val (E,T) = case (lookupApxString (r, ReconG, s, 1))
	             of (SOME Tapx) => Tapx
		      | NONE => case (lookupString(r, G, s, (I.ctxLength ReconG)+ 1))
		                 of (SOME ET) => ET
				  | NONE => 
				     (* We now allow it to be upper or lowercase
				     if (isCap s) then
				       (* Treat it as a pattern variable *)
				       (DI.PatVar (r, s), DA.Meta(r, D.Existential, getPatVarFormApx (r, s)))
				     else
				       raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!"))
                                      *)
                                     (DI.PatVar (r, s), DA.Meta(r, D'.newPVar(), getPatVarFormApx (r, s, allowPatVars)))

	     val _ = unifyApxTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", Tresult, T)

	     fun f (ReconTerm.JNothing) = E
	       | f _ = raise Domain
	   in
	     (ReconTerm.jnothing, f)
	   end

     | convertExp2Temp (smartInj, G, ReconG, D.OmittedPat r, false, Tresult) = 	       
	    raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Omission not allowed!"))


     | convertExp2Temp (smartInj, G, ReconG, D.OmittedPat r, true, Tresult) = 	       
	      (* ABP:  need to still add support for this
	       *       will need to do "raising" similar to that on LF. (when under new) but this time
	       *       it would add pops...  Let's delay this for now...
	       *       In the meantime we allow omission of the *entire pattern*
	       *       in convertCase2Temp... This should be DELETED when we add raising on meta-level
	       *)
	    raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Omission not allowed (use a pattern variable)!"))


     | convertExp2Temp (smartInj, G, ReconG, D.VarInt (r, i), allowPatVars, Tresult) =
           let
	     val n = I.ctxLength ReconG
	     val (name, T) = if (i <= n) then
	               apxDec2Type (I.ctxLookup(ReconG, i))
		     else
		       case (lookupInt (r, i, G, i-n))
			 of (name, Texact) => (name, DA.exact2ApxType Texact)

	     val s = case name of 
	            NONE => "#" ^ (Int.toString i)
		   | SOME s => s

	     val _ = unifyApxTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", Tresult, T)

	     fun f (ReconTerm.JNothing) = DI.VarInt (r, i)
	       | f _ = raise Domain
	   in
	     (ReconTerm.jnothing, f)
	   end

     | convertExp2Temp (smartInj, G, ReconG, D.Quote (r, LFterm), allowPatVars, Tresult) =
	   let
	     val A = Approx.newCVar()
	     val t = tokensToTerm (PrintDelphinExt.lftermToTokens LFterm)
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

     | convertExp2Temp (smartInj, G, ReconG, D.Unit r, allowPatVars, Tresult) =	  
	   let
	     val _ = unifyApxTypes(smartInj, r, "() has incompatible type", Tresult, DA.Meta(r, D'.Existential, DA.Top r))

	     fun f (ReconTerm.JNothing) = DI.Unit r
	       | f _ = raise Domain
	   in
	     (ReconTerm.jnothing, f)
	   end


     | convertExp2Temp (smartInj, G, ReconG, D.Lam (r, Clist), allowPatVars, Tresult) =
	   let
	     fun caseF C =
	          let 
		    val oldTables = saveApxTables() (* Scoping the patvars here IS necessary *)
		    val (job, f) = convertCase2Temp(smartInj, G, ReconG, C, Tresult)
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

	     fun f x = DI.Lam(r, f' jobFunList x)
	   in
	     (allJobs, f)
	   end

     | convertExp2Temp (smartInj, G, ReconG, D.New (r, D, E), allowPatVars, Tresult) = 
	  let
	    val (Drecon, Dapprox, job1, f1) = convertNewDec2Temp (G, ReconG, D)
	    val F = DA.FVar(r, ref NONE)
	    val inferredType = DA.Meta(r, D'.Existential, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type Mismatch", Tresult, inferredType)
	    val (job2, f2) = convertExp2Temp (smartInj, G, I.Decl(ReconG, DA.NonInstantiableDec (r, Dapprox)), E, allowPatVars, DA.Meta(r, D'.Existential, F))

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

     | convertExp2Temp (smartInj, G, ReconG, D.App (r, E1, E2), allowPatVars, Tresult) = 
	  let
	    val argType = inferTypeApx(smartInj, G, ReconG, E2, allowPatVars)

	    val D = DA.NormalDec(r, NONE, argType)
	    val funResult = DA.FVar (r, ref NONE)
	      
	    val funF = DA.All(r, D, funResult)
	    val funType = DA.Meta(r, D'.Existential, funF)

	    val (job1, f1) = convertExp2Temp(smartInj, G, ReconG, E1, allowPatVars, funType)
	    val (job2, f2) = convertExp2Temp(smartInj, G, ReconG, E2, allowPatVars, argType)

	    val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r,D'.Existential, funResult))

	    fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val E1'' = f1 jobResult1
		    val E2'' = f2 jobResult2
		  in
		    DI.App(r, D'.Visible, E1'', E2'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1, job2), f)
	  end

     | convertExp2Temp (smartInj, G, ReconG, D.Pair (r, E1, E2), allowPatVars, Tresult) = 
	  let
	     val F = DA.FVar(r, ref NONE)
	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, D'.Existential, F))
		       
	     val firstType = inferTypeApx (smartInj, G,ReconG, E1, allowPatVars)
	     val D = DA.NormalDec(r, NONE, firstType)
	     val secondF = DA.FVar(r, ref NONE)
	     val pairF = DA.Exists(r, D, secondF)
	     val pairType = DA.Meta(r, D'.Existential, pairF)

	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, pairType)

	     val (job1, f1)  = convertExp2Temp(smartInj, G, ReconG, E1, allowPatVars, firstType)
	     val (job2, f2)  = convertExp2Temp(smartInj, G, ReconG, E2, allowPatVars, DA.Meta(r, D'.Existential, secondF))
	    

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

     | convertExp2Temp (smartInj, G, ReconG, D.Pop (r, s, E), allowPatVars, Tresult) = 
	  let
	    (* NOTE:  We only allow Pop up to end of ReconG
	     * G contains the fixpoints already processed, so this is acceptable
	     *)
	    fun lookupNewString (I.Null, s, _) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!"))
	      (* ABP:  Should we check if the name has been overridden as a non-parameter?... as of now.. no *)
	      | lookupNewString (I.Decl(ReconG, DA.InstantiableDec _), s, k) = lookupNewString(ReconG, s, k+1)
	      | lookupNewString (I.Decl(ReconG, DA.NonInstantiableDec (_, D as DA.NewDecLF (_, SOME s', _))), s, k) =
	                                    if (s=s') then
					      (k, D)
					    else
					      lookupNewString(ReconG, s, k+1)
	      | lookupNewString (I.Decl(ReconG, DA.NonInstantiableDec (_, D as DA.NewDecMeta (_, SOME s', _))), s, k) =
	                                    if (s=s') then
					      (k, D)
					    else
					      lookupNewString(ReconG, s, k+1)

	      | lookupNewString (I.Decl(ReconG, DA.NonInstantiableDec _), s, k) = lookupNewString(ReconG, s, k+1)

	    val (i, Dapprox) = lookupNewString (ReconG, s, 1)
	    val ReconG' = D'.popCtx (i, ReconG)
	    val F = DA.FVar (r, ref NONE)
	    val T = DA.Meta(r, D'.Existential, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, D'.Existential, F))


	    val (job1, f1) = convertExp2Temp (smartInj, G, ReconG', E, allowPatVars, T)
	    fun f (ReconTerm.JPopCtx(_, jobResult)) = DI.Pop(r, i, f1 jobResult)
	      | f _ = raise Domain
	  in
	    (ReconTerm.jpopctx(i, job1), f)
	  end


     | convertExp2Temp (smartInj, G, ReconG, D.Fix (r, funList), allowPatVars, Tresult) = 
	  let
	    val (_, job1, f1) = convertFunList2Temp(smartInj, G, ReconG, r, funList, Tresult)
	    fun f x = DI.Fix(r, f1 x)
	  in
	    (job1, f)
	  end

     | convertExp2Temp (smartInj, G, ReconG, D.TypeAscribe (r, E, T), allowPatVars, Tresult) = 
	  let
	    val (Tapx, job1, f1) = convertTypes2Temp(G, ReconG, T)
	    val _ = unifyApxTypes (smartInj, r, "Type Ascription doesn't match", Tresult, Tapx)
	    val (job2, f2) = convertExp2Temp(smartInj, G, ReconG, E, allowPatVars, Tresult)

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

     | convertExp2Temp (smartInj, G, ReconG, D.Sequence eList, allowPatVars, Tresult) = 
	   let
	     fun convertList [(r, e)] = 
	                                let
	                                  val (job, f) = convertExp2Temp(smartInj, G, ReconG, e, allowPatVars, Tresult)
					in
					  [(r, job, f)]
					end
	       | convertList ((r,e)::eList) =
					let
					  val T = inferTypeApx(smartInj, G, ReconG, e, allowPatVars)
					  val (job, f) = convertExp2Temp(smartInj, G, ReconG, e, allowPatVars, T)
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

     | convertExp2Temp (smartInj, G, ReconG, D.LiftedApp (r, E1, E2), allowPatVars, Tresult) =
	   (* Create a function (fn <F> => fn <E> => <F E>) and apply it to E1 and E2 *)
	   (* or a function (fn <F> => fn <E> => (<F E>,()) if smartInj is false) *)
	   let
	     val Fname = D.ObjectID (r, false, getFreshName())
	     val Ename = D.ObjectID (r, false, getFreshName())
	     val result = if smartInj then
	                    D.Quote(r, D.LFApp (r, Fname, Ename))
			  else
	                    D.Pair(r, D.Quote(r, D.LFApp (r, Fname, Ename)), D.Unit r)

	     val function = D.Lam (r, [D.Match(r, 
					       D.Quote(r, Fname),
					       D.Lam (r, [D.Match(r,
								  D.Quote(r, Ename), 
								  result)]))])
	     val term = D.App(r, D.App (r, function, E1), E2)
	   in
	     convertExp2Temp (smartInj, G, ReconG, term, allowPatVars, Tresult)
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

     | convertExp2Temp (smartInj, G, ReconG, D.LetVar (r, Pat, E1, E2), allowPatVars, Tresult) =
	   convertExp2Temp(smartInj,
			   G,
			   ReconG,
			   D.App(r, D.Lam(r, [D.Match(r, Pat, E2)]), E1),
			   allowPatVars,
			   Tresult)


     | convertExp2Temp (smartInj, G, ReconG, D.LetFun (r, funList, E), allowPatVars, Tresult) =
	  let
	    val Tapx = DA.Meta(r, D'.Existential, DA.FVar (r, ref NONE))
	    val (Dapprox, job1, f1) = convertFunList2Temp(smartInj, G, ReconG, r, funList, Tapx)
	    val ReconG' = I.Decl(ReconG, DA.InstantiableDec (r, Dapprox))
	    val Drecon = ReconTerm.ndec (NONE, r)
	    val (job2, f2) = convertExp2Temp(smartInj, G, ReconG', E, allowPatVars, Tresult)

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


     | convertExp2Temp (smartInj, G, ReconG, D.ExtendFun (r, E, Clist), allowPatVars, Tresult) =
	  let
	     val (job1, f1)  = convertExp2Temp(smartInj, G, ReconG, E, allowPatVars, Tresult)

	     fun caseF C =
	          let 
		    val oldTables = saveApxTables() (* Scoping the patvars here IS NOT necessary here as there should
						     * NOT be any pattern variables *)
		    val (job, f) = convertCase2Temp(smartInj, G, ReconG, C, Tresult)
		    val _ = restoreApxTables oldTables
		  in
		    (ReconTerm.jscopeVars job, f)  (* Scope the variables introduced in C so it only applies to that branch *)
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
		    val E' = f1 jobResult1
		    val Clist' = f' jobFunList jobResult2
		  in
		    DI.ExtendFun(r, E', Clist')
		  end
	       | f _ = raise Domain
	  in
	    (ReconTerm.jand(job1, caseJobs), f)
	  end



   and convertFunList2Temp (smartInj, G, ReconG, r, funList, Tresult) =
          let
	    val oldTables = saveApxTables() (* Scoping the patvars here is not necessary, but can't hurt *)
	                                     (* ADAM:  So we should remove this.. but test first... *)
	    val (Dapprox, job, f) = convertFunList2Temp'(smartInj, G, ReconG, r, funList, Tresult)
	    val _ = restoreApxTables oldTables
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

	     fun decListFormulas [(_, DA.NormalDec(_, _, DA.Meta(_, _, F)), _, _)] = [F]
	       | decListFormulas ((_, DA.NormalDec(_, _, DA.Meta(_, isP, F)), _, _) :: decs) = F :: (decListFormulas decs)
	       | decListFormulas _ = raise Domain (* badly formed fixpoint *)


	     fun decListFormula [F] = F
	       | decListFormula Flist = DA.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist

	     val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, D'.Existential, F))

	     val D = DA.NormalDec (r, SOME (decListString decList), DA.Meta(r, D'.Existential, F))
	     val ReconG' = I.Decl(ReconG, DA.InstantiableDec (r, D))
	       
	     fun pairFormula ([], []) = []
	       | pairFormula ((_, _, E)::fList, F::formList) = (E, F) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)

	     val expList = map (fn (E,F) => convertExp2Temp(smartInj, G, ReconG', E, false, DA.Meta(r, D'.Existential, F))) expFormList

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





   and convertCase2Temp (smartInj, G, ReconG, D.Eps(r, D, C), Tresult) =
          let
	    val (Drecon, Dapprox, job1, f1) = convertNormalDec2Temp (G, ReconG, D)
	    val (job2, f2) = convertCase2Temp (smartInj, G, I.Decl(ReconG, DA.InstantiableDec(r, Dapprox)), C, Tresult)

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

     | convertCase2Temp (smartInj, G, ReconG, D.NewC(r, D, C), Tresult) =
	  let
	    val (Drecon, Dapprox, job1, f1) = convertNewDec2Temp (G, ReconG, D)
	    val F = DA.FVar(r, ref NONE)
	    val inferredType = DA.Meta(r, D'.Existential, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type Mismatch", Tresult, inferredType)

	    val (job2, f2) = convertCase2Temp (smartInj, G, I.Decl(ReconG, DA.NonInstantiableDec (r, Dapprox)), C, DA.Meta(r, D'.Existential, F))

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


     | convertCase2Temp (smartInj, G, ReconG, D.PopC(r, s, C), Tresult) =
	  let
	    (* NOTE:  We only allow Pop up to end of ReconG
	     * G contains the fixpoints already processed, so this is acceptable
	     *)
	    fun lookupNewString (I.Null, s, _) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!"))
	      (* ABP:  Should we check if the name has been overridden as a non-parameter?... as of now.. no *)
	      | lookupNewString (I.Decl(ReconG, DA.InstantiableDec _), s, k) = lookupNewString(ReconG, s, k+1)
	      | lookupNewString (I.Decl(ReconG, DA.NonInstantiableDec (_, D as DA.NewDecLF (_, SOME s', _))), s, k) =
	                                    if (s=s') then
					      (k, D)
					    else
					      lookupNewString(ReconG, s, k+1)
	      | lookupNewString (I.Decl(ReconG, DA.NonInstantiableDec (_, D as DA.NewDecMeta (_, SOME s', _))), s, k) =
	                                    if (s=s') then
					      (k, D)
					    else
					      lookupNewString(ReconG, s, k+1)

	      | lookupNewString (I.Decl(ReconG, DA.NonInstantiableDec _), s, k) = lookupNewString(ReconG, s, k+1)

	    val (i, Dapprox) = lookupNewString (ReconG, s, 1)
	    val ReconG' = D'.popCtx (i, ReconG)
	    val F = DA.FVar (r, ref NONE)
	    val T = DA.Meta(r, D'.Existential, DA.Nabla(r, Dapprox, F))
	    val _ = unifyApxTypes(smartInj, r, "Type mismatch", Tresult, DA.Meta(r, D'.Existential, F))

	    val oldTables = saveApxTables() (* Scoping the patvars here *)
	    val (job1, f1) = convertCase2Temp (smartInj, G, ReconG', C, T)
	    val _ = restoreApxTables oldTables
	    fun f (ReconTerm.JPopCtx(_, jobResult)) = DI.PopC(r, i, f1 jobResult)
	      | f _ = raise Domain
	  in
	    (ReconTerm.jpopctx(i, ReconTerm.jscopeVars job1), f)
	  end

     (* These next two cases can be removed once we handle raising of meta-level exps *)
     | convertCase2Temp (smartInj, G, ReconG, D.Match(r, D.OmittedPat r2, E2), Tresult) =
	  convertCase2Temp (smartInj, 
			    G, 
			    ReconG, 
			    D.Eps(r, D.NormalDec(r, NONE, D.Meta(r, D.OmittedParam, D.OmittedFormula r)), 
				  D.Match(r, D.VarInt(r2, 1), E2)), 
			    Tresult)


     | convertCase2Temp (smartInj, G, ReconG, D.MatchAnd(r, D.OmittedPat r2, C), Tresult) =
	  convertCase2Temp (smartInj, 
			    G, 
			    ReconG, 
			    D.Eps(r, D.NormalDec(r, NONE, D.Meta(r, D.OmittedParam, D.OmittedFormula r)), 
				  D.MatchAnd(r, D.VarInt(r2, 1), C)), 
			    Tresult)

     | convertCase2Temp (smartInj, G, ReconG, D.Match(r, E1, D.Lam(r2, [C])), Tresult) =
	  (* Enhancement:  User should have entered this as an "and"
	   * since it does not hurt and can only help to make cases exhaustive.
	   *)
	  convertCase2Temp (smartInj, G, ReconG, D.MatchAnd (r, E1, C), Tresult)

     | convertCase2Temp (smartInj, G, ReconG, D.Match(r, E1, E2), Tresult) =
	  let
	    val argTypeApx = inferTypeApx(smartInj, G, ReconG, E1, true)
	    val D = DA.NormalDec(r, NONE, argTypeApx)
	    val ReconG' = I.Decl(ReconG, DA.InstantiableDec (r, D))
	    val funResult = DA.FVar (r, ref NONE)

	    val _ = unifyApxTypes(smartInj, r, "Match has incompatible type", Tresult, DA.Meta(r, D'.Existential, DA.All(r, D, funResult)))

	    val (job1, f1) = convertExp2Temp (smartInj, G, ReconG, E1, true, argTypeApx)
	    val (job2, f2) = convertExp2Temp (smartInj, G, ReconG, E2, false, DA.Meta(r, D'.Existential, funResult))

	    fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val E1'' = f1 jobResult1
		    val E2'' = f2 jobResult2
		  in
		    DI.Match(r, D'.Visible, E1'', E2'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1,job2) , f)
	  end

     | convertCase2Temp (smartInj, G, ReconG, D.MatchAnd(r, E, C), Tresult) =
	  let
	    val argTypeApx = inferTypeApx(smartInj, G, ReconG, E, true)
	    val D = DA.NormalDec(r, NONE, argTypeApx)
	    val ReconG' = I.Decl(ReconG, DA.InstantiableDec (r, D))
	    val funResult = DA.FVar (r, ref NONE)

	    val _ = unifyApxTypes(smartInj, r, "Match has incompatible type", Tresult, DA.Meta(r, D'.Existential, DA.All(r, D, funResult)))

	    val (job1, f1) = convertExp2Temp (smartInj, G, ReconG, E, true, argTypeApx)
	    val (job2, f2) = convertCase2Temp (smartInj, G, ReconG, C, DA.Meta(r, D'.Existential, funResult))

	    fun f (ReconTerm.JAnd(jobResult1, jobResult2)) =
	          let
		    val E'' = f1 jobResult1
		    val C'' = f2 jobResult2
		  in
		    DI.MatchAnd(r, D'.Visible, E'', C'')
		  end
	      | f _ = raise Domain

	  in
	    (ReconTerm.jand(job1,job2) , f)
	  end

     | convertCase2Temp (smartInj, G, ReconG, D.ImplicitMatch _, Tresult) = raise Domain (* only exists from conversion from internal to external *)

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
    *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   fun inferType (G, DI.Quote (r, M, A, DA.InjLF, isP)) = D'.LF(isP, A)

     | inferType (G, DI.Quote (r, M, A, DA.InjMeta, isP)) =  
           D'.Meta(D'.Existential, D'.Exists(D'.NormalDec (NONE, D'.LF(isP, A)), D'.Top))

     | inferType (G, DI.Quote (r, M, A, DA.InjVar (ref (SOME I)), isP)) = inferType (G, DI.Quote (r, M, A, I, isP))
     | inferType (G, DI.Quote (region, M, A, DA.InjVar (r as ref NONE), isP)) = 
	      ( (* It can be either LF or Meta, so we pick Meta *)
	       r := SOME (DA.InjMeta) ; 
	       inferType (G, DI.Quote (region, M, A, DA.InjMeta, isP)))



     | inferType (G, DI.VarInt (r, i)) = 
	     let
	       val (_, T) = lookupInt(r, i, G, i)
	     in
	       T
	     end

     | inferType (G, DI.TypeAscribe (_, E, _)) = inferType (G, E)

     | inferType (G, _) = 
	     D'.Meta(D'.Existential, D'.newFVar(D'.coerceCtx G))
         
    

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
     | convertNewDec (G, DI.NewDecMeta (r, sO, F)) = D'.NewDecMeta(sO, convertFormula(G, F))


   and convertTypes (G, DI.LF(_, isP, A)) = D'.LF(isP, A)
     | convertTypes (G, DI.Meta (_, isP, F)) = D'.Meta(isP, convertFormula(G, F))


   and convertFormula (G, DI.Top _) = D'.Top
     | convertFormula (G, DI.All(r, visible, D, F)) = 
            let
	      val D' = convertNormalDec (G, D)
	      val F' = convertFormula(I.Decl(G, D'.InstantiableDec D'), F)
	    in
	      D'.All(visible, NONE, D', F')
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


  and coerceExp (DI.Quote (_, M, _, DA.InjLF, isP)) = 
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



   fun updateExp (smartInj, G, E as DI.VarInt (r, i), Tresult, K) =
         let
	   val (name, T) = lookupInt(r, i, G, i)
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
		       val K' = DelphinAbstract.LFcollectExp(r, (I.ctxLength G), (A, I.id), DelphinAbstract.LFcollectExp (r, (I.ctxLength G), (M, I.id), K, true), true)
			        (* warning.. depth of (I.ctxLength G) is incorrect (too large but not too small so pop doesn't go negative).. but we don't use this for abstraction.. so this is safe!! *)
		     in
		       (E, K')
		     end


     | updateExp (smartInj, G, E as DI.Quote (r, M, A, DA.InjMeta, isP), Tresult, K) =
	             let
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(isP, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(D'.Existential, F))
		       val K' = DelphinAbstract.LFcollectExp(r, (I.ctxLength G), (A, I.id), DelphinAbstract.LFcollectExp (r, (I.ctxLength G), (M, I.id), K, true), true)
			        (* warning.. depth of (I.ctxLength G) is incorrect (too large but not too small so pop doesn't go negative).. but we don't use this for abstraction.. so this is safe!! *)
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
	     val _ = unifyTypes(smartInj, r, "() has incompatible type", G, Tresult, D'.Meta(D'.Existential, D'.Top))
	   in
	     (E, K)
	   end

     | updateExp (smartInj, G, DI.Lam (r, Clist), Tresult, K) =
	   let
	     val F = D'.newFVar(D'.coerceCtx G)
	     val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.Existential, F))

	     fun caseF C =
	       let
		 val oldTables = saveExactTables() (* also saves patVarCtx *)
		 val _ = patVarCtx := G
		 val (C', K') = updateCase(smartInj, G, C, Tresult, K)
		 val _ = restoreExactTables oldTables (* also restores patVarCtx *)
	       in
		 C'
	       end

	     val Clist' = map caseF Clist
	   in
	     (DI.Lam (r, Clist'), K (* initial K *) )
	   end


     | updateExp (smartInj, G, DI.New(r, D, E), Tresult, K) =
	   let
	     val D' = convertNewDec(G, D)
	     val G' = I.Decl(G, D'.NonInstantiableDec D')
	     val newResult = D'.newFVar(D'.coerceCtx G')
	     val nablaType = D'.Meta(D'.Existential, D'.Nabla(D', newResult))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, nablaType)

	     val K1 = DelphinAbstract.collectDelNewDec ((I.ctxLength G), D, K, true)
	         (* warning.. depth of (I.ctxLength G) is incorrect (too large but not too small so pop doesn't go negative).. but we don't use this for abstraction.. so this is safe!! *)
	     val (E', K2) = updateExp(smartInj, G', E, D'.Meta(D'.Existential, newResult), K1)

	   in
	     (DI.New(r, D, E'), K2)
	   end

     | updateExp (smartInj, G, DI.App(r, D'.Visible, E1, E2), Tresult, K) = 
	   let
	     fun debugAdam() = ()
	     val _ = debugAdam()
	     val funF = D'.newFVar(D'.coerceCtx G)
	     val (E1', K1) = updateExp(smartInj, G, E1, D'.Meta(D'.Existential, funF), K)

	     fun applyImplicit (E, F, maxNum) = applyImplicitW(E, D'.whnfF F, maxNum)
	     and applyImplicitW (E, F, SOME 0) = (E, F)
	       | applyImplicitW (E, D'.All(D'.Implicit, _, D'.NormalDec (_, D'.LF(isP, A)), F), maxNum) =
	                  let
			    val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
			    val Q = DI.Quote(r, X, A, DA.InjLF, isP)
			    val E' = DI.App(r, D'.Implicit, E, Q)
			    val t = I.Dot(coerceExp Q, I.id)
			    val maxNum' = case maxNum of NONE => NONE | (SOME n) => SOME (n-1)
			  in
			    applyImplicit (E', D'.FClo(F, t), maxNum')
			  end
	       | applyImplicitW (E, F, NONE) = (E, F)
	       | applyImplicitW (E, F, SOME n) = raise Domain (* should be SOME 0 if it gets here... *)

	     val (E1implicit, Frest) = applyImplicit (E1', funF, NONE)
	     (* val argType = inferType(G, E2) *)

	     (* If we have a function which only has implicit args, then it may need
	      * to be filled in as an argument.  For example, imagine:
	      * D-- val x : <ev_s>
	      * D-- x @ <ev_z>
	      * This is an example where "x" will be a meta-level function only with implicit
	      * arguments.
	      *)
	     fun addOne NONE = NONE
	       | addOne (SOME n) = SOME (n+1)
	     and countImplicitF F = countImplicitF' (D'.whnfF F)
	     and countImplicitF' (D'.All (D'.Implicit, _, _, F)) = addOne (countImplicitF F)
	       | countImplicitF' (D'.FVar _) = NONE
	       | countImplicitF' _ = SOME 0

	     (* WARNING::: It is *important* that we process E1 first before E2.  
	      * as that can fill in necessary information we need for the type of E2.
	      *)
	     val argType = inferType(G, E2)
	     val (E2', K2) = updateExp(smartInj, G, E2, argType, K1)


	     val (E2', argType) = case argType
	                         of (T as D'.LF _) => (E2', T)
				  | (T as D'.Meta(isP, Farg)) =>
				            (case (countImplicitF Frest, countImplicitF Farg)
					       of (SOME n1, SOME n2) => if (n2 >= n1) then 
						                            let
									      val (E2implicit, FargRest) = applyImplicit (E2', Farg, SOME (n2 - n1))
									    in
									      (E2implicit, D'.Meta(isP, FargRest))
									    end

									else (E2', T)
					        | _ => (E2', T))

	     val D = D'.NormalDec(NONE, argType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val funResult = D'.newFVar(D'.coerceCtx G')

	     val _ = unifyTypes (smartInj, r, "Type mismatch", G, D'.Meta(D'.Existential, Frest), D'.Meta(D'.Existential, D'.All(D'.Visible, NONE, D, funResult)))

	     val t = I.Dot(coerceExp E2', I.id)   (* G |- E2'.id  : G' *)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, D'.FClo(funResult, t)))

	   in
	     (DI.App(r, D'.Visible, E1implicit, E2'), K2)
	   end


     | updateExp (smartInj, G, DI.App(r, D'.Implicit, E1, E2), Tresult, K) = raise Domain (* implicit variables are CREATED by
										       * updateExp.. will not be encountered.
										       *)

     | updateExp (smartInj, G, DI.Pair(r, E1, E2), Tresult, K) = 
	   let
	     val F = D'.newFVar(D'.coerceCtx G)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, F))

		       
	     val firstType = inferType(G, E1)
	     val D = D'.NormalDec(NONE, firstType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val secondF = D'.newFVar(D'.coerceCtx G')
	     val pairF = D'.Exists(D, secondF)
	     val pairType = D'.Meta(D'.Existential, pairF)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, pairType)

	     val (E1', K1) = updateExp(smartInj, G, E1, firstType, K)
	     val t = I.Dot(coerceExp E1', I.id)
	     val (E2', K2) = updateExp(smartInj, G, E2, D'.Meta(D'.Existential, D'.FClo(secondF, t)), K1)
	   in
	     (DI.Pair(r, E1', E2'), K2)
	   end


     | updateExp (smartInj, G, DI.Proj (r, E, i), Tresult, K) =
	   let
	     val F = D'.newFVar (D'.coerceCtx G)
	     val T = D'.Meta(D'.Existential, F)

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
	     fun popCtx(1, I.Decl(G, D'.NonInstantiableDec D)) = (D, G)
	       | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
	       | popCtx(0, _) = raise Domain
	       | popCtx _ = raise Domain

	     val (D, G') = popCtx(i, G)

	     val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
	     val T = D'.Meta(D'.Existential, D'.Nabla(D, F))
	     val Tshift = D'.Meta(D'.Existential, D'.FClo(F, I.Shift (i-1)))

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)

	     val (E', K') = updateExp(smartInj, G', E, T, K)

	   in
	     (DI.Pop(r, i, E'), K')
	   end

     | updateExp (smartInj, G, DI.Fix(r, funList), Tresult, K) =  
	   let
	     val (_, funList', K') = updateFunList(smartInj, G, r, funList, Tresult, K)
	   in
	     (DI.Fix(r, funList'), K')
	   end
	     
     | updateExp (smartInj, G, E as DI.PatVar (r,name), Tresult, K) = 
	   let
	     val (n, F) = getPatVarFormExact (name)
	     val n' = I.ctxLength G
	     val s = if (n' >= n) then I.Shift (n' - n) else raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Pattern Variable " ^ name ^" out of scope. (did you pop it away?"))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, D'.FClo(F, s)))

	     val (_, K') = DelphinAbstract.transformDelExp ((I.ctxLength G), E, K, true)
	          (* warning.. depth of (I.ctxLength G) is incorrect (too large but not too small so pop doesn't go negative).. but we don't use this for abstraction.. so this is safe!! *)
	   in
	     (E, K')
	   end

     (* syntactic sugar *)
     | updateExp (smartInj, G, DI.TypeAscribe (r, E, T), Tresult, K) = 
	   let
	     val T' = convertTypes(G, T)
	     val K2 = DelphinAbstract.collectDelTypes((I.ctxLength G), T, K, true)
	        (* warning.. depth of (I.ctxLength G) is incorrect (too large but not too small so pop doesn't go negative).. but we don't use this for abstraction.. so this is safe!! *)

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
	     val _ = unifyTypes(smartInj, r, "Sequence must end with formula type", G, Tresult, D'.Meta(D'.Existential, Fresult))

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
	     val (D', funList', K2) = updateFunList(smartInj, G, r, funList, D'.Meta(D'.Existential, D'.newFVar (D'.coerceCtx G)), K)

	     val G' = I.Decl(G, D'.InstantiableDec D')
	     val Tshift = D'.substTypes(Tresult, I.shift)

	     val (E', K3) = updateExp(smartInj, I.Decl(G, D'.InstantiableDec D'), E, Tshift, K2)
	   in
	     (DI.LetFun(r, funList', E'), K3)
	   end


     | updateExp (smartInj, G, DI.ExtendFun (r, E, Clist), Tresult, K) = 
	   let
	     val (E', K2) = updateExp(smartInj, G, E, Tresult, K)

	     fun caseF C =
	       let
		 val oldTables = saveExactTables() (* also saves patVarCtx *)
		 val _ = patVarCtx := G
		 val (C', _) = updateCase(smartInj, G, C, Tresult, K2)
		 val _ = restoreExactTables oldTables (* also restores patVarCtx *)
	       in
		 C'
	       end

	     val Clist' = map caseF Clist

	   in
	     (DI.ExtendFun(r, E', Clist'), K2)
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

	     fun decListFormulas [D'.NormalDec(_, D'.Meta(isP, F))] = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Fixpoint specified to have a parameter type"))
		     in
			   [F]
		     end
	       | decListFormulas ((D'.NormalDec(_, D'.Meta(isP, F))) :: decs) = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Fixpoint specified to have a parameter type"))
		     in
			   F :: (decListFormulas decs)
		     end

	       | decListFormulas _ = raise Domain (* badly formed fixpoint *) 


	     fun decListFormula [F] = F
	       | decListFormula Flist = D'.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, F))


	     val D = D'.NormalDec (SOME (decListString decList), D'.Meta(D'.Existential, F))
	     val G' = I.Decl(G, D'.InstantiableDec D)
	       
	     (* We need to shift the formula so it makes sense in G' *)
	     fun pairFormula ([], []) = []
	       | pairFormula ((r, D, E)::fList, F::formList) = (r, D, E, D'.FClo(F,I.shift)) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)


	     val expList = map (fn (r, D, E, F) => (r, D, #1 (updateExp(smartInj, G', E, D'.Meta(D'.Existential, F), Kinitial)))) expFormList

	   in
	     (D, expList, Kinitial)
	   end
      


    and updateCase (smartInj, G, DI.Eps(r, D, C), Tresult, K) =
                                  let
				    val D' = convertNormalDec(G, D)
				    val K2 = DelphinAbstract.collectDelNormalDec ((I.ctxLength G), D, K, true)
				       (* warning.. depth of (I.ctxLength G) is incorrect (too large but not too small so pop doesn't go negative).. but we don't use this for abstraction.. so this is safe!! *)
				    val G' = I.Decl(G, D'.InstantiableDec D')
				    val (C', K3) = updateCase(smartInj, G', C, D'.substTypes(Tresult, I.shift), K2)
				  in
				    (DI.Eps(r, D, C'), K3)
				  end


      | updateCase (smartInj, G, DI.NewC(r, D, C), Tresult, K) =
				  let
				    val D' = convertNewDec (G, D)
				    val K2 = DelphinAbstract.collectDelNewDec ((I.ctxLength G), D, K, true)
				      (* warning.. depth of (I.ctxLength G) is incorrect (too large but not too small so pop doesn't go negative).. but we don't use this for abstraction.. so this is safe!! *)
				    val G' = I.Decl(G, D'.NonInstantiableDec D')
				    val newResult = D'.newFVar(D'.coerceCtx G')
				    val nablaType = D'.Meta(D'.Existential, D'.Nabla(D', newResult))
				    val _ = unifyTypes(smartInj, r, "New has incompatible type", G, Tresult, nablaType)

				    val (C', K3) = updateCase(smartInj, G', C, D'.Meta(D'.Existential, newResult), K2)
				  in
				    (DI.NewC(r, D, C'), K3)
				  end

      | updateCase (smartInj, G, DI.PopC(r, i, C), Tresult, K) =
				  let
				    fun popCtx(1, I.Decl(G, D'.NonInstantiableDec D)) = (D, G)
				      | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
				      | popCtx(0, _) = raise Domain
				      | popCtx _ = raise Domain
				      
				    val (D, G') = popCtx(i, G)

				    val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
				    val T = D'.Meta(D'.Existential, D'.Nabla(D, F))
				    val Tshift = D'.Meta(D'.Existential, D'.FClo(F, I.Shift (i-1)))
				      
				    val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)

				    val oldTables = saveExactTables() (* also saves patVarCtx *)
				    val _ = patVarCtx := G'				     
				    val (C', K2) = updateCase(smartInj, G', C, T, K)
				    val _ = restoreExactTables oldTables (* also restores patVarCtx *)
				      
				  in
				    (DI.PopC(r, i, C'), K2)
				  end


      | updateCase (smartInj, G, DI.Match(r, visible, E1, E2), Tresult, K) =
				  let
				    val F = D'.newFVar(D'.coerceCtx G)
				    val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.Existential, F))

				    fun addImplicit F = addImplicitW(D'.whnfF F)
				    and addImplicitW (D'.All(D'.Implicit, _, D'.NormalDec (_, D'.LF(isP, A)), F)) =
				               let
						 val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
						 val Q = DI.Quote(r, X, A, DA.InjLF, isP)
						 val t = I.Dot(coerceExp Q, I.id)
						 val (Frest, f) = addImplicit(D'.FClo(F, t))
					       in
						 (Frest, (fn C => DI.MatchAnd(r, D'.Implicit, Q, f C)))
					       end
				      | addImplicitW F = (F, fn C => C)

				    val (Frest, impf) = addImplicit F
				    val Tresult = D'.Meta(D'.Existential, Frest)
				    val argType = inferType(G, E1)
				    val D = D'.NormalDec(NONE, argType)

				    val G' = I.Decl(G, D'.InstantiableDec D)
				    val funResult = D'.newFVar(D'.coerceCtx G')
				    val _ = unifyTypes(smartInj, r, "Match has incompatible type", G, Tresult, D'.Meta(D'.Existential, D'.All(visible, NONE, D, funResult)))
				    val (E1', K2) = updateExp(smartInj, G, E1, argType, K)
				    val t = I.Dot (coerceExp E1', I.id)

				    val (E2', K3) = updateExp(smartInj, G, E2, D'.Meta(D'.Existential, D'.FClo(funResult, t)), K2)

				  in
			    (impf (DI.Match(r, visible, E1',  E2')), K3)
				  end

      | updateCase (smartInj, G, DI.MatchAnd(r, visible, E, C), Tresult, K) =
				  let
				    val F = D'.newFVar(D'.coerceCtx G)
				    val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.Existential, F))

				    fun addImplicit F = addImplicitW(D'.whnfF F)
				    and addImplicitW (D'.All(D'.Implicit, _, D'.NormalDec (_, D'.LF(isP, A)), F)) =
				               let
						 val X = Whnf.newLoweredEVar (D'.coerceCtx G, (A, I.id))
						 val Q = DI.Quote(r, X, A, DA.InjLF, isP)
						 val t = I.Dot(coerceExp Q, I.id)
						 val (Frest, f) = addImplicit(D'.FClo(F, t))
					       in
						 (Frest, (fn C => DI.MatchAnd(r, D'.Implicit, Q, f C)))
					       end
				      | addImplicitW F = (F, fn C => C)

				    val (Frest, impf) = addImplicit F
				    val Tresult = D'.Meta(D'.Existential, Frest)


				    val argType = inferType(G, E)
				    val D = D'.NormalDec(NONE, argType)

				    val G' = I.Decl(G, D'.InstantiableDec D)
				    val funResult = D'.newFVar(D'.coerceCtx G')

				    val _ = unifyTypes(smartInj, r, "Match has incompatible type", G, Tresult, D'.Meta(D'.Existential, D'.All(visible, NONE, D, funResult)))

				    val (E', K2) = updateExp(smartInj, G, E, argType, K)
				    val t = I.Dot (coerceExp E', I.id)

				    val (C', K3) = updateCase(smartInj, G, C, D'.Meta(D'.Existential, D'.FClo(funResult, t)), K2)

				  in
				    (impf (DI.MatchAnd(r, visible, E', C')), K3)
				  end


	
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* 
    * Third Phase:  (After Abstraction) Convert from DelphinIntermediateSyntax to DelphinIntSyntax
    *
    *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)




   fun convertExp (smartInj, G, DI.VarInt (r, i), Tresult) =
         let
	   val (name, T) = lookupInt(r, i, G, i)

	   val s = case name of 
	            NONE => "#" ^ (Int.toString i)
		   | SOME s => s

	   val _ = unifyTypes(smartInj, r, "Variable " ^ s ^ " of incompatible type", G, Tresult, T)
	 in
	   D'.Var (D'.Fixed i, SOME(!filename, r))
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
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(D'.Existential, F))
		     in
		       D'.Pair (D'.Quote M, D'.Unit, F)
		     end

	     | D'.Param =>
		     (let
		       val F = D'.Exists(D'.NormalDec (NONE, D'.LF(D'.Param, A)), D'.Top)
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(D'.Existential, F))
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
		       val _ = unifyTypes(smartInj, r, "Incompatible types", G, Tresult, D'.Meta(D'.Existential, F))
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
	     val _ = unifyTypes(smartInj, r, "() has incompatible type", G, Tresult, D'.Meta(D'.Existential, D'.Top))
	   in
	     D'.Unit
	   end

     | convertExp (smartInj, G, DI.Lam (r, Clist), Tresult) =
	   let
	     (* If all the cases start with NewC or with PopC, then move it to the outside. *)
	     fun removeNew [DI.NewC (_, D, C)] = SOME(D, [C])
	       | removeNew (DI.NewC(_, D, C) :: Clist) =
	                                    (case (removeNew Clist)
					       of NONE => NONE
						| SOME(D, Clist') => SOME(D, C::Clist'))
	       | removeNew _ = NONE


	     fun removePop [DI.PopC (_, i, C)] = SOME(i, [C])
	       | removePop (DI.PopC (_, i, C) :: Clist) =
	                                    (case (removePop Clist)
					       of NONE => NONE
						| SOME(j, Clist') => if (i = j) then SOME(i, C::Clist') else NONE)
	       | removePop _ = NONE

	     val moveNew = removeNew Clist
	     val movePop = removePop Clist
	   in
	     case (moveNew, movePop)
	       of (NONE, NONE) => 
		            let
			      val F = D'.newFVar(D'.coerceCtx G)
			      val _ = unifyTypes(smartInj, r, "Function has incompatible type", G, Tresult, D'.Meta(D'.Existential, F))
			      val Clist' = map (fn C => convertCase(smartInj, G, C, Tresult)) Clist
			    in
			      D'.Lam(Clist', F, SOME(!filename, r))
			    end

	        | (SOME(D, Clist'), _) => convertExp (smartInj, G, DI.New(r, D, DI.Lam(r, Clist')), Tresult)
	        | (_, SOME(i, Clist')) => convertExp (smartInj, G, DI.Pop(r, i, DI.Lam(r, Clist')), Tresult)
	   end

     | convertExp (smartInj, G, DI.New(r, D, E), Tresult) =
	   let
	     val D' = convertNewDec(G, D)
	     val G' = I.Decl(G, D'.NonInstantiableDec D')
	     val newResult = D'.newFVar(D'.coerceCtx G')
	     val nablaType = D'.Meta(D'.Existential, D'.Nabla(D', newResult))
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, nablaType)

	     val E' = convertExp(smartInj, G', E, D'.Meta(D'.Existential, newResult))
	   in
	     D'.New(D', E', SOME(!filename, r))
	   end


     | convertExp (smartInj, G, DI.App(r, visible, E1, E2), Tresult) = 
	   let
	     val argType = inferType(G, E2)
	       
	     val D = D'.NormalDec(NONE, argType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val funResult = D'.newFVar(D'.coerceCtx G')



	     val funF = D'.All (visible, NONE, D, funResult)
	     val funType = D'.Meta(D'.Existential, funF)

	     val E1' = convertExp(smartInj, G, E1, funType)

	     val E2' = convertExp(smartInj, G, E2, argType)

	     val t = D'.Dot(D'.Prg E2', D'.id)  (* G |- E2'.id  : G' *)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, D'.FClo(funResult, D'.coerceSub t)))
	   in
	     D'.App(visible, E1', E2')
	   end

     | convertExp (smartInj, G, DI.Pair(r, E1, E2), Tresult) = 
	   let
	     val F = D'.newFVar(D'.coerceCtx G)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, F))

		       
	     val firstType = inferType(G, E1)
	     val D = D'.NormalDec(NONE, firstType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val secondF = D'.newFVar(D'.coerceCtx G')
	     val pairF = D'.Exists(D, secondF)
	     val pairType = D'.Meta(D'.Existential, pairF)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, pairType)

	     val E1' = convertExp(smartInj, G, E1, firstType)
	     val t = D'.Dot(D'.Prg E1', D'.id)
	     val E2' = convertExp(smartInj, G, E2, D'.Meta(D'.Existential, D'.FClo(secondF, D'.coerceSub t)))
	   in
	     D'.Pair(E1', E2', F)
	   end


     | convertExp (smartInj, G, DI.Proj (r, E, i), Tresult) =
	   let
	     val F = D'.newFVar (D'.coerceCtx G)
	     val T = D'.Meta(D'.Existential, F)

	     val E' = convertExp (smartInj, G, E, T)
	 
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
	     D'.Proj(E', i)
	   end


     | convertExp (smartInj, G, DI.Pop(r, i, E), Tresult) = 
	   let
	     fun popCtx(1, I.Decl(G, D'.NonInstantiableDec D)) = (D, G)
	       | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
	       | popCtx(0, _) = raise Domain
	       | popCtx _ = raise Domain

	     val (D, G') = popCtx(i, G)	       

	     val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
	     val T = D'.Meta(D'.Existential, D'.Nabla(D, F))
	     val Tshift = D'.Meta(D'.Existential, D'.FClo(F, I.Shift (i-1)))

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)

	     val E' = convertExp(smartInj, G', E, T)
	   in
	     D'.Pop(i, E')
	   end

     | convertExp (smartInj, G, DI.Fix(r, funList), Tresult) =  D'.Fix (convertFunList(smartInj, G, r, funList, Tresult))
	     
     | convertExp (smartInj, G, DI.PatVar _, _) = raise Domain (* PatVar should be eliminated by abstraction BEFORE calling this function *)

     (* syntactic sugar *)
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
	     val _ = unifyTypes(smartInj, r, "Sequence must end with formula type", G, Tresult, D'.Meta(D'.Existential, Fresult))

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
				    D'.All(D'.Visible, NONE, D, F)
				  end
	       | buildFormula _ = raise Domain

	     fun buildLam [(E, _)] _ = E
	       | buildLam ((E, _)::rest) (F as D'.All(vis, _, D, F')) =
	                          let
				    val C = D'.Eps(D, D'.Match (vis, D'.Var (D'.Fixed 1, NONE), buildLam rest F'))
				  in
				    D'.Lam ([C], F, SOME(!filename, r))
				  end
	       | buildLam _ _ = raise Domain


	     fun buildApp (lamExp, [_]) = lamExp
	       | buildApp (lamExp, (E, T)::rest) = buildApp(D'.App(D'.Visible, lamExp, E), rest)
	       | buildApp _ = raise Domain

	     val expTypeList = convertList Elist
	     val F = buildFormula expTypeList
	     val function = buildLam expTypeList F

	     val final = buildApp (function, expTypeList)
	   in
	     final
	   end

	    

     (* LiftedApp now removed before this stage...
     | convertExp (smartInj, G, DI.LiftedApp(r, E1, A1, E2, A2, Aresult), Tresult) = 
	   let	     
	      (* Type of E1 is Exists(A1,Top)
	       * Type of E2 is Exists(A2,Top)
	       * resulting type is (Aresult, Top)
	       *)
	     val formE1 = D'.Exists(D'.NormalDec(NONE, D'.LF(D'.Existential, A1)), D'.Top)
	     val typeE1 = D'.Meta(D'.Existential, formE1)
	     val formE2 = D'.Exists(D'.NormalDec(NONE, D'.LF(D'.Existential, A2)), D'.Top)
	     val typeE2 = D'.Meta(D'.Existential, formE2)
	     val formResult = D'.Exists(D'.NormalDec(NONE, D'.LF(D'.Existential, Aresult)), D'.Top)
	     val typeResult = D'.Meta(D'.Existential, formResult)
	     val _ = unifyTypes(smartInj, r, "Type mismatch in @", G, Tresult, typeResult)
	     val E1' = convertExp(smartInj, G, E1, typeE1)
	     val E2' = convertExp(smartInj, G, E2, typeE2)

	       
	     (* eps E.(E,()) => eps F.(F,()) => (E F, ()) *)
	     val formCase2 = D'.All(D'.NormalDec(NONE, typeE2), formResult)
	     val formCase1 = D'.All(D'.NormalDec(NONE, typeE1), formCase2)
	     val var1 = D'.Quote (I.Root (I.BVar 1, I.Nil))
	     val var2app1 = D'.Quote (I.Redex (I.Root (I.BVar 2, I.Nil), I.App(I.Root (I.BVar 1, I.Nil), I.Nil)))
	     val C2 = D'.Eps(D'.NormalDec(NONE, D'.LF(D'.Existential, A2)), D'.Match(D'.Pair(var1,D'.Unit,formE2),
										     D'.Pair(var2app1,D'.Unit,formResult)))
	     val C1 = D'.Eps(D'.NormalDec(NONE, D'.LF(D'.Existential, A1)), D'.Match(D'.Pair(var1,D'.Unit,formE1),
										     D'.Lam ([C2], formCase2)))
	   in
	     D'.App(D'.App(D'.Lam ([C1], formCase1), E1'), E2')
	   end
	 *)



     | convertExp (smartInj, G, DI.LetFun (r, funList, E2), Tresult) = 
	   let
	     val (D', E') = convertFunList(smartInj, G, r, funList, D'.Meta(D'.Existential, D'.newFVar (D'.coerceCtx G)))
	     val fixE = D'.Fix (D', E')

	     val G' = I.Decl(G, D'.InstantiableDec D')
	     val F = D'.newFVar (D'.coerceCtx G')
	     val Tshift = D'.substTypes(Tresult, I.shift)

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G', Tshift, D'.Meta(D'.Existential, F))

	     val E2' = convertExp(smartInj, G', E2, Tshift)
	     val C' = D'.Eps (D', D'.Match (D'.Visible, D'.Var (D'.Fixed 1, NONE), E2'))
	   in
	     D'.App(D'.Visible, D'.Lam ([C'],D'.All(D'.Visible, NONE, D', F), SOME(!filename, r)), fixE)
	   end

       | convertExp (smartInj, G, DI.ExtendFun (r, E, Clist), Tresult) =
	   let
	     val E' = convertExp (smartInj, G, E, Tresult)

	     val Fresult = D'.newFVar (D'.coerceCtx G)
	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, Fresult))


	     val n = case E' of
	             D'.Var (D'.Fixed n, _) => n
		     | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only extend parameter functions in the context."))

	     fun findLastParameter (I.Decl(G, D'.NonInstantiableDec D), k, max) = if (k < n) then findLastParameter(G, k+1, k) else max
	       | findLastParameter (I.Decl(G, D'.InstantiableDec _), k, max) = findLastParameter(G, k+1, max)
	       | findLastParameter (I.Null, k, max) = max

	     val m = findLastParameter(G, 1, 0)

	     val T = case (I.ctxLookup(G, n))
	             of D'.InstantiableDec (D'.NormalDec (_, T)) => T
		      | _ => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only extend parameter functions."))
	       
	     (* G = G1,n,...,m+1,G2 *)
	     val T = D'.substTypes(T, I.Shift(n-m)) (* G1,n,...(m+1) |- T : wff *)

	     (*
	      * The new function has type
	      * {G2}T
	      *)
	     fun getG2 (G, 0) = (G, I.Null)
	       | getG2 (I.Decl(G, D), n) = 
	                  let
			    val (G0, G2) = getG2 (G, n-1)
			  in
			    (G0, I.Decl(G2, D))
			  end
	       | getG2 _ = raise Domain

	     val (Gbefore, G2) = getG2 (G, m)

	     fun extendType (I.Null) = (fn F => F)
	       | extendType (I.Decl(G, D'.InstantiableDec D)) = 
	                                   let 
	                                     val f = extendType G
					   in
					     fn F => f (D'.All(D'.Visible, NONE, D, F))
					   end
	       | extendType (I.Decl(G, D'.NonInstantiableDec D)) = 
	                                   let 
	                                     val f = extendType G
					   in
					     fn F => f (D'.Nabla(D, F))
					   end

	     val extendedF = (extendType G2) Fresult  (* G1,n,...,m+1 |- {G2} T  *) 

	     val _ = D'.updatePVarsFormula Fresult
	     val _ = if (NormalizeDelphin.hasVarsFor Fresult)
		      then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only extend parameter functions (but type is ambiguous)."))
	             else ()


	     fun isParamFun F = isParamFunW (D'.whnfF F)
	     and isParamFunW (D'.All (_, _, D, F)) = (WorldSubsumption.hasParamInputNormalDec (D, WorldSubsumption.Input)) orelse isParamFun F
	       | isParamFunW (D'.Nabla(_, F)) = false (* Let's disallow this from automatic extension *)
	       | isParamFunW _ = false

	     val _ = if (isParamFun Fresult)
		      then () 
		     else 
		       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Can only automatically extend limited parameter functions."))

	     fun extendCase (I.Null) = (fn C => C)
	       | extendCase (I.Decl(G, D'.InstantiableDec D)) = 
	                                   let 
	                                     val f = extendCase G
					   in
					     fn C => f (D'.Eps(D, D'.MatchAnd(D'.Visible, D'.Var(D'.Fixed 1, NONE), C)))
					   end
	       | extendCase (I.Decl(G, D'.NonInstantiableDec D)) = 
	                                   let 
	                                     val f = extendCase G
					   in
					     fn C => f (D'.NewC(D, C, NONE))
					   end

	     val Clist' = map (fn C => (extendCase G2) (convertCase(smartInj, G, C, Tresult))) Clist

	     fun createLastBody (varList, Glocal) =
	         let
		   val worldFun = D'.Var(D'.Fixed(n-m), SOME(!filename, r)) 

		   fun removeVarsForG2 (I.Null, l) = l
		     | removeVarsForG2 (I.Decl(G, D'.InstantiableDec _), l) = tl (removeVarsForG2 (G, l))
		     | removeVarsForG2 (I.Decl(G, D'.NonInstantiableDec _), l) = (removeVarsForG2 (G, l))
		   val varList'' = removeVarsForG2 (G2, varList)

		   (* We need to apply worldFun to varList'' *)
		   fun applyVars (E, []) = E
		     | applyVars (E, x::l) = applyVars(D'.App(D'.Visible, E, x), l)

		   val worldApp = applyVars (worldFun, varList'')  (* This now represents the function applied *)

		   (* We now need to do ((R => {Glocal}R) worldApp) \Glocal  *)


		   fun weakenE (I.Null, E) = E
		     | weakenE (I.Decl(G, D'.NonInstantiableDec D), E) = weakenE(G, D'.New(D, E, SOME(!filename, r)))
		     | weakenE _ = raise Domain (* broken invariant.. .Glocal only contains NonInstantiableDecs.. *)

		   fun weakenF (I.Null, F) = F
		     | weakenF (I.Decl(G, D'.NonInstantiableDec D), F) = weakenF(G, D'.Nabla(D, F))
		     | weakenF _ = raise Domain (* broken invariant.. .Glocal only contains NonInstantiableDecs.. *)


		   fun getResultFormula (F, l) = getResultFormulaW (D'.whnfF F, l)
		   and getResultFormulaW (D'.All(_, _, _, F), v::l) = getResultFormula (D'.FClo(F, I.Dot(D'.coerceExp v, I.id)), l)
		     | getResultFormulaW (F, []) = F
		     | getResultFormulaW _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexplained Error."))
 
		   fun getResultType (D'.Meta(_, F), l) = getResultFormula (F, l)
		     | getResultType _ = raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Unexplained Error."))

		   val resultF = getResultType (T, varList'') (* recall T is defined way above *)

		   val caseB = D'.Eps(D'.NormalDec(NONE, D'.Meta(D'.Existential, resultF)),
				      D'.Match(D'.Visible, D'.Var(D'.Fixed 1, NONE), 
					       weakenE (Glocal, D'.Var(D'.Fixed (1 + (I.ctxLength Glocal)), NONE))))
		   val caseFun = D'.Lam ([caseB], 
					 D'.All(D'.Visible, 
						NONE, 
						D'.NormalDec(NONE, D'.Meta(D'.Existential, resultF)), 
						weakenF (Glocal, D'.FClo(resultF, I.Shift (I.ctxLength Glocal)))), 
					 SOME(!filename, r))

		   val caseApp = D'.App(D'.Visible, caseFun, worldApp)

		   fun popCtx (I.Null, E) = E 
		     | popCtx (I.Decl(G, D'.NonInstantiableDec D), E) = D'.Pop(1, popCtx(G, E))
		     | popCtx _ = raise Domain (* broken invariant *)

		   val finalResult = popCtx (Glocal, caseApp)
		 in
		   finalResult
		 end


	     (* createLastCase is based on "getStartGoal" in coverage.fun *)	   
	     fun createLastCase (Glocal, varList, F, sc) = createLastCaseW (Glocal, varList, D'.whnfF F, sc)
	     and createLastCaseW (Glocal, varList, D'.All(visibility, W, D, F), sc) =
	            if (DelphinCoverage.isFunction F) then
		      DelphinCoverage.generateEVar(false, D'.Anything, Gbefore, Glocal, 
						   D, fn E => createLastCase(Glocal, varList@[E], D'.FClo(F, I.Dot (D'.coerceExp E, I.id)), 
							       fn C => sc (D'.MatchAnd(visibility, E, C))))
		    else 
		      DelphinCoverage.generateEVar(false, D'.Anything, Gbefore, Glocal, 
						   D, fn E => [sc (D'.Match(visibility, E, createLastBody(varList@[E],Glocal)))])
	       | createLastCaseW (Glocal, varList, D'.Nabla(D, F), sc)  =
		      createLastCase (I.Decl(Glocal, D'.NonInstantiableDec D), varList, F, fn C => sc (D'.NewC(D, C, NONE)))
	       | createLastCaseW (Global, varList, F, sc) = raise Domain (* badly typed *)
		  

	     (* ABP WARNING:  abstractCase ASSUMES that it will not encounter any FVars and all EVars 
	      * make sense with respect to the same global context.
	      *)
	     val Crest = hd (createLastCase (I.Null, [], extendedF, fn C => DelphinAbstract2.abstractCase C))
	     val extendFun = D'.Lam (Clist'@[Crest], extendedF, SOME(!filename, r))

	     (* Compute (extendFun G2)
	      * For example (extendFun (x,y,u,v)) = (((extendFun x) \y) u) \v
	      *)
	     fun applyExtend (E, I.Null, k) = E
	       | applyExtend (E, I.Decl(G, D'.InstantiableDec D), k) = D'.App (D'.Visible, 
									       applyExtend(E, G, k+1),
									       D'.Var(D'.Fixed k, SOME(!filename, r)))
	       | applyExtend (E, I.Decl(G, D'.NonInstantiableDec D), k) = D'.Pop(k,
										 applyExtend(E, G, 1))
	   in
	     applyExtend (extendFun, G2, 1)
	   end

    and convertFunList (smartInj, G, r, funList, Tresult) =
	   let
	     val decList  = map (fn (_,D,_) => convertNormalDec(G, D)) funList 
	     fun decListString [D'.NormalDec(SOME [s], _)] = [s]
	       | decListString ((D'.NormalDec(SOME [s], _)) :: decs) = s :: (decListString decs)
	       | decListString _ = raise Domain (* badly formed fixpoint *)

	     fun decListFormulas [D'.NormalDec(_, D'.Meta(isP, F))] = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Fixpoint specified to have a parameter type"))
		     in
			   [F]
		     end
	       | decListFormulas ((D'.NormalDec(_, D'.Meta(isP, F))) :: decs) = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Fixpoint specified to have a parameter type"))
		     in
			   F :: (decListFormulas decs)
		     end

	       | decListFormulas _ = raise Domain (* badly formed fixpoint *) 


	     fun decListFormula [F] = F
	       | decListFormula Flist = D'.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist

	     val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, D'.Meta(D'.Existential, F))


	     val D = D'.NormalDec (SOME (decListString decList), D'.Meta(D'.Existential, F))
	     val G' = I.Decl(G, D'.InstantiableDec D)
	       
	     (* We need to shift the formula so it makes sense in G' *)
	     fun pairFormula ([], []) = []
	       | pairFormula ((_, _, E)::fList, F::formList) = (E, D'.FClo(F,I.shift)) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)


	     val expList = map (fn (E,F) => convertExp(smartInj, G', E, D'.Meta(D'.Existential, F))) expFormList


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
				    D'.Eps(D', C')
				  end


      | convertCase (smartInj, G, DI.NewC(r, D, C), Tresult) =
				  let
				    val D' = convertNewDec (G, D)
				    val G' = I.Decl(G, D'.NonInstantiableDec D')
				    val newResult = D'.newFVar(D'.coerceCtx G')
				    val nablaType = D'.Meta(D'.Existential, D'.Nabla(D', newResult))
				    val _ = unifyTypes(smartInj, r, "New has incompatible type", G, Tresult, nablaType)

				    val C' = convertCase(smartInj, G', C, D'.Meta(D'.Existential, newResult))
				  in
				    D'.NewC(D', C', SOME(!filename, r))
				  end

      | convertCase (smartInj, G, DI.PopC(r, i, C), Tresult) =
				  let
				    fun popCtx(1, I.Decl(G, D'.NonInstantiableDec D)) = (D, G)
				      | popCtx(n, I.Decl(G, _)) = popCtx(n-1, G)
				      | popCtx(0, _) = raise Domain
				      | popCtx _ = raise Domain
				      
				    val (D, G') = popCtx(i, G)	       

				    val F = D'.newFVar(D'.coerceCtx(I.Decl(G', D'.NonInstantiableDec D)))
				    val T = D'.Meta(D'.Existential, D'.Nabla(D, F))
				    val Tshift = D'.Meta(D'.Existential, D'.FClo(F, I.Shift (i-1)))

				    val _ = unifyTypes(smartInj, r, "Type mismatch", G, Tresult, Tshift)
				      
				    val C' = convertCase(smartInj, G', C, T)
				  in
				    D'.PopC(i, C')
				  end


      | convertCase (smartInj, G, DI.Match(r, visible, E1, E2), Tresult) =
				  let
				    val argType = inferType(G, E1)
				    val D = D'.NormalDec(NONE, argType)

				    val G' = I.Decl(G, D'.InstantiableDec D)
				    val funResult = D'.newFVar(D'.coerceCtx G')
				    val E1' = convertExp(smartInj, G, E1, argType)

				    val _ = unifyTypes(smartInj, r, "Match has incompatible type", G, Tresult, D'.Meta(D'.Existential, D'.All(visible, NONE, D, funResult)))
				    (* val E1' = convertExp(smartInj, G, E1, argType) *)
				    val t = D'.Dot (D'.Prg E1', D'.id)

				    val E2' = convertExp(smartInj, G, E2, D'.Meta(D'.Existential, D'.FClo(funResult, D'.coerceSub t)))

				  in
				    D'.Match (visible, E1', E2')
				  end

      | convertCase (smartInj, G, DI.MatchAnd(r, visible, E, C), Tresult) =
				  let
				    val argType = inferType(G, E)
				    val D = D'.NormalDec(NONE, argType)

				    val G' = I.Decl(G, D'.InstantiableDec D)
				    val funResult = D'.newFVar(D'.coerceCtx G')

				    val _ = unifyTypes(smartInj, r, "Match has incompatible type", G, Tresult, D'.Meta(D'.Existential, D'.All(visible, NONE, D, funResult)))

				    val E' = convertExp(smartInj, G, E, argType)
				    val t = D'.Dot (D'.Prg E', D'.id)

				    val C' = convertCase(smartInj, G, C, D'.Meta(D'.Existential, D'.FClo(funResult, D'.coerceSub t)))

				  in
				    D'.MatchAnd (visible, E', C')
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
	   val (Fapprox, job, f1) = convertFormula2Temp(G, I.Null, F)
	   val r = D.getRegFormula F
	   val FI  = lfReconstruction(G, job, f1, r)

	   val FI2 = (DelphinAbstract.addImplicitTypesForm (FI, I.Null)
	       handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		    | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg)))

	   val F' = convertFormula(G, FI2)
	 in
	   (Fapprox, F')
	 end

   fun convertMeta0 (smartInj, G, E) =
         let
	   val Tapx = inferTypeApx (smartInj, G, I.Null, E, false)
	   val (job, f) = convertExp2Temp(smartInj, G, I.Null, E, false (* allowPatVars=false *), Tapx)
	   val r = D.getRegExp E
	   val E' = lfReconstruction(G, job, f, r)

	   val Tresult = inferType (G, E')
	   val (E', _) = updateExp(smartInj, G, E', Tresult, I.Null) (* changes approx types to exact types (fills in LF EVars) and fills in InjVars *)
	   val E' = DelphinAbstract.abstractPatVarsExp (r, E', Tresult)
	     handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		  | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg))
	   val Tresult = inferType (G, E')  (* abstraction may have changed the type of E' *)
	   val Eresult = convertExp(smartInj, G, E', Tresult)

	   val _ = D'.updatePVarsTypes Tresult
	   val _ = D'.updatePVarsExp Eresult
	 in
	   if ((NormalizeDelphin.hasFVarsExp Eresult) orelse (NormalizeDelphin.hasFVarsTypes Tresult))
	     (* we removed PVars, and we abstracted away LF level FVars  and EVars, so we may now encounter Formula Variables (Meta FVars) *)
	     then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Leftover Variables (we do not support polymorphism... yet!"))
	   else

	     (Eresult, Tresult)
	 end


   fun convertFixList0 (smartInj, G, funList) = 
         let
	   fun getRegion [] = raise Domain
	     | getRegion [(r,_,_)] = r
	     | getRegion ((r,_,_)::xs) = Paths.join(r, getRegion xs)

	   val r = getRegion funList
	   val Tapx = DA.Meta(r, D'.Existential, DA.FVar (r, ref NONE))

	   val (Dapprox, job, f) = convertFunList2Temp(smartInj, G, I.Null, r, funList, Tapx)

	   fun isFun F = isFunW (DA.whnfF F)
	   and isFunW (DA.All _) = true
	     | isFunW (DA.Nabla (_, _, F)) = isFun F
	     | isFunW _ = false
	       
	   val _ = (case (DA.whnfT Tapx)
	           of (DA.Meta(_,_, DA.FormList Flist)) 
		      => let 
			   fun checkFun F = 
			     if (isFun F) then () else
				 let
				   val firstLine = "Expected Function Type\n"
				   val secondLine = "  Actual Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tapx))
				   val s= firstLine ^ secondLine
				 in 
				   raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), s))
				 end
			   val _ = map checkFun Flist
			 in
			   ()
			 end

		    | (DA.Meta(_,_, F)) => if (isFun F) then () else 
			     let
			       val firstLine = "Expected Function Type\n"
			       val secondLine = "  Actual Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tapx))
			       val s= firstLine ^ secondLine
			     in 
			       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), s))
			     end

		    | _ =>   let
			       val firstLine = "Expected Function Type\n"
			       val secondLine = "  Actual Type: " ^ typeStr(smartInj, I.Null, DA.apx2ExactType(I.Null, Tapx))
			       val s= firstLine ^ secondLine
			     in 
			       raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), s))
			     end)

	   val funList' = lfReconstruction(G, job, f, r)
	   val T = D'.Meta(D'.Existential, D'.newFVar (D'.coerceCtx G))
	   val (_, funList', _) = updateFunList(smartInj, G, r, funList', T, I.Null) (* changes approx types to exact types (fills in LF EVars) *)
	   val funList' = DelphinAbstract.abstractPatVarsFunList (funList')
	     handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		  | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg))
	   val T = D'.Meta(D'.Existential, D'.newFVar (D'.coerceCtx G)) (* we can't use old T because abstraction can change the type *)

	   val (D', E') = convertFunList (smartInj, G, r, funList', T)

	   (* Instantiate all ambiguous PVars as Existential *)
	   val _ = D'.updatePVarsNormalDec D'
	   val _ = D'.updatePVarsExp E'

	   val result = D'.Fix(D', E')
	 in
	   if (NormalizeDelphin.hasFVarsExp result)
	     (* we removed PVars, and we abstracted away LF level FVars and EVars, so we may now encounter Formula Variables (Meta FVars) *)
	     then raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), "Leftover Variables (we do not support polymorphism... yet!"))
	   else
	     D'.Fix(D', E')
	 end

   (* convertWorldVar A = (G, A')
    * where A is converted into A' and the free variables are captured in G
    * . |- A : type (with EVars/FVars)
    * G |- A' type (without EVars/FVars)
    *)
   fun convertWorldVar A =
         let
	   val r = D.getRegLFType A
	   val t = tokensToTerm (PrintDelphinExt.lftypeToTokens A)
	   val A = Approx.newCVar()
	   val job = ReconTerm.jtypeEqualApx (t, A) (* we use this method because it indicates the object is a "type" *)
	   val _ = ReconTerm.resetErrors(!filename)
	   val result = ReconTerm.recon job
	   val _ = ReconTerm.checkErrors(r)
	   val A2 = case result
	             of ReconTerm.JClass ((A, _), _ (* type *)) => A
		      | _ => raise Domain
	 in
	   DelphinAbstract.addSomeVars (r, A2)
	       handle DelphinAbstract.LeftOverConstraints cnstrRegL => raise Error (createConstraintsMsg cnstrRegL)
		    | DelphinAbstract.Error (r, msg) => raise Error (Paths.wrapLoc (Paths.Loc (!filename, r), msg))

	 end

   fun convertWorld (D.Anything) = D'.Anything
     | convertWorld (D.Variables varList) = D'.VarList (map convertWorldVar varList)

  end