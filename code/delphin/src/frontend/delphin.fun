(* Delphin Front-End *)
(* Author:  Adam Poswolsky *)

functor Delphin (structure DelphinParser : PARSERR
		 structure Parse : PARSE) : DELPHIN =
struct

  exception Error of string

  structure I = IntSyn
  structure D = DelphinExtSyntax
  structure D'= DelphinIntSyntax (* What we are converting to *)
  structure C = DelphinElab
  structure O = DelphinOpsem
  structure L = Lexer
  structure LS = Stream    

  local
    val version = "Delphin, Release Version 1.5.0, April 20, 2008"

    val debug = ref false
    val enableCoverage = C.enableCoverage (* default is set in convert.fun to true *)
                                          (* We use an enableCoverage flag in convert.fun
					   * so it will NOT use Nab{W} or New{W} when enableCoverage=false,
					   * This way it corresponds to the base type system.
					   *)
    val enableTermination = ref true
    val stopOnWarning = ref false
    val pageWidth = Formatter.Pagewidth
    val parseDebug = ref false
    val smartInj = ref true
    val printPatternVars = ref false (* makes things look cleaner when they are off.. in my opinion... *)
    val printImplicit = Print.implicit (* Linked to the LF printer, which
					* uses this bool ref to determine
					* whether to print implicit args.
					*)
    val doubleCheck = ref false
    (*
    val tripleCheck = ref false
      *)

    val metaSig = ref (nil : (string * DelphinApprox.Formula * D'.Formula) list)  (* for type aliasing *)

    val prompt = "D-- "

    (* contains information with respect to where we are with respect to
     * the starting directory 
     *)
    val dirPrefix = ref ""
    val startDir = ref (OS.FileSys.getDir())


    fun stop (s) =
      if (!stopOnWarning) then raise Error ("\n" ^ s ^ "\nTo continue with warnings you must set Delphin.stopOnWarning := false") else print ("\n" ^ s ^ "\n\n")
      
    fun chDir(s) =
      (* adds a check if s is empty before changing directory *)
      if (s = "") then ()
      else OS.FileSys.chDir(s)

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

    (* We no longer use case to distinguish behavior of variables...
    fun getCase s = 
      let
	val c = case (String.explode(s)) 
	        of (c::xs) => c
		 | _ => raise Domain
      in
	if Char.isUpper(c) then L.ID (L.Upper, s) else L.ID (L.Lower, s)
      end
    *)

    fun pretendCapital s = L.ID(L.Upper, s)
    fun pretendLower s = L.ID(L.Lower, s)

   

    fun getRegion (LS.Cons ((_, r), _)) = r
      | getRegion _ = raise Domain

         

    fun addToSignature(tokenList) =
      let
	val f = LS.expose (LS.fromList(tokenList))
	(* val f = LS.expose (L.lexStream (TextIO.openString s)) *)
	val (conDec, f') = ParseConDec.parseConDec' (f)
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),getRegion(f)),("LF Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val ans = LFparsing.install1 (C.getFilename(), (Parser.ConDec conDec, r2)) 
	val cid = case ans
	          of SOME(cid) => cid
		   | _ => raise Domain
      in
	cid
      end

    fun addToSignatureAbbrev(tokenList) =
      let
	val f = LS.expose (LS.fromList(tokenList))
	(* val f = LS.expose (L.lexStream (TextIO.openString s)) *)
	val (conDec, f') = ParseConDec.parseConDec' (f)
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),getRegion(f)),("LF Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val ans = LFparsing.install1 (C.getFilename(), (Parser.AbbrevDec conDec, r2)) 
	val cid = case ans
	          of SOME(cid) => cid
		   | _ => raise Domain
      in
	cid
      end

    fun spaceString(0) = ""
      | spaceString(x) = " " ^ spaceString(x-1)


    fun solutionToString (s, T, NONE) = "val " ^ s ^ " : " ^ T ^ "\n" ^ spaceString(String.size(s)) 
                                        ^ " = " ^ "(no solution)" ^ "\n"

      | solutionToString (s, T, SOME(E)) = 
           let
	     val firstLine = "val " ^ s ^ " : " ^ T ^ "\n" 
	     val secondLineHead = spaceString(String.size(s)) ^ " = "

	     val expFormat = PrintDelphinInt.expToFormat(I.Null, E, !smartInj, !debug, !printPatternVars)

	     val format = Formatter.HVbox [Formatter.String(secondLineHead), expFormat]
	     val result = firstLine ^ (Formatter.makestring_fmt format) ^ "\n"
	   in
	     result
	   end


    fun eval E = 
      (SOME(O.eval0 E) handle O.NoSolution => NONE)




    fun convertTypeConstant (r, name, k) = 
      let
	val Paths.Reg(a,b) = r
	val stringR = Paths.Reg(a, a + String.size(name))
      in	
	(* We now will allow capitalized constants as well
	addToSignature([(getCase(name), stringR)] @  [(L.COLON,r)] @ (PrintDelphinExt.kindToTokens(k)) )
	 *)
	addToSignature([(pretendCapital(name), stringR)] @  [(L.COLON,r)] @ (PrintDelphinExt.kindToTokens(k)) )
      end


    fun convertObjectConstant (lfdec) = addToSignature(PrintDelphinExt.lfdecToTokens(lfdec)) 

    fun setNamePref(tokenList) =
      let
	val f = LS.expose (LS.fromList(tokenList))
	val (npref, f') = ParseFixity.parseNamePref' (f)
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),getRegion(f)),("LF Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val _ = LFparsing.install1 (C.getFilename(), (Parser.NamePref npref, r2)) 
      in
	()
      end

    fun setFixity(tokenList) =
      let
	val f = LS.expose (LS.fromList(tokenList))
	val (fdec, f') = ParseFixity.parseFixity' (f)
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),getRegion(f)),("LF Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val _ = LFparsing.install1 (C.getFilename(), (Parser.FixDec fdec, r2)) 
      in
	()
      end

    (*
    fun convertPrec ((D.INFIXL (r,n)), s) = setFixity([(L.INFIX, r), (getCase("left"), r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])
      | convertPrec ((D.INFIXR (r,n)), s) = setFixity([(L.INFIX, r), (getCase("right"), r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])
      | convertPrec ((D.INFIXN (r,n)), s) = setFixity([(L.INFIX, r), (getCase("none"), r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])
      | convertPrec ((D.POSTFIX (r,n)), s) = setFixity([(L.POSTFIX, r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])
      | convertPrec ((D.PREFIX (r,n)), s) = setFixity([(L.PREFIX, r), (getCase(Int.toString(n)), r), (getCase(s), r), (L.EOF, r)])
    *)

    fun convertPrec ((D.INFIXL (r,n)), s) = setFixity([(L.INFIX, r), (pretendLower("left"), r), (pretendLower(Int.toString(n)), r), (pretendLower(s), r), (L.EOF, r)])
      | convertPrec ((D.INFIXR (r,n)), s) = setFixity([(L.INFIX, r), (pretendLower("right"), r), (pretendLower(Int.toString(n)), r), (pretendLower(s), r), (L.EOF, r)])
      | convertPrec ((D.INFIXN (r,n)), s) = setFixity([(L.INFIX, r), (pretendLower("none"), r), (pretendLower(Int.toString(n)), r), (pretendLower(s), r), (L.EOF, r)])
      | convertPrec ((D.POSTFIX (r,n)), s) = setFixity([(L.POSTFIX, r), (pretendLower(Int.toString(n)), r), (pretendLower(s), r), (L.EOF, r)])
      | convertPrec ((D.PREFIX (r,n)), s) = setFixity([(L.PREFIX, r), (pretendLower(Int.toString(n)), r), (pretendLower(s), r), (L.EOF, r)])

    fun convertName (D.OneName (r, s1), sCons) = setNamePref([(L.NAME, r), (pretendLower(sCons), r), (pretendCapital(s1), r), (L.EOF, r)])
      | convertName (D.TwoNames (r, s1, s2), sCons) = setNamePref([(L.NAME, r), (pretendLower(sCons), r), (pretendCapital(s1), r), (pretendLower(s2), r), (L.EOF, r)])


    fun freezeSignature() = 
           let
	     val cids = I.getAllTypeFams()
	   in
	     Subordinate.installFrozen cids
	     handle Subordinate.Error (msg) => raise Error ("LF Error:  " ^ msg)
	   end

    fun convertAndEvaluate(G, t, (D.Use s)) = 
           let
	     val _ = freezeSignature() 
	     fun isDelim c = if ((c = #"\"") orelse (c = #" ")) then true else false
             val tokens = String.tokens isDelim s
	     val s = case tokens
	             of [s] => s
	              | _ => raise Error ("Bad Filename: " ^ s ^ "\n\n")

	     val {dir=dir, file=fname} = OS.Path.splitDirFile s

	     val oldDirPrefix = !dirPrefix
	     val Cold = C.saveData()
	     val Iold = Interface.saveData()
	     val Pold = Paths.getLinesInfo()

	     fun restoreOld() =
				  let
				    val _ = dirPrefix := oldDirPrefix
				    val _ = chDir (!startDir)
				    val _ = chDir (!dirPrefix)
				    val _ = C.restoreData Cold
				    val _ = Interface.restoreData(Iold)
				    val _ = Paths.restoreLinesInfo(Pold)
				  in
				    ()
				  end

	     (* update dirPrefix *)
	     val _ = case (String.explode dir)
	               of [] => ()
		        | (#"/" :: _) => dirPrefix := dir
			| _ => if (!dirPrefix) = "" then dirPrefix := dir
			                     else dirPrefix := (!dirPrefix ^ "/" ^ dir)

	     (* Change directory *)
	     val _ = chDir (!startDir)
	     val newPath = OS.Path.joinDirFile {dir=(!dirPrefix), file=fname}
	     val displayFname = OS.FileSys.realPath (newPath)
	                  handle _ => (restoreOld() ; raise Error ("Bad Filename: " ^ newPath ^ "\n\n"))

	     val _ = (chDir (!dirPrefix))
	                  handle _ => (restoreOld() ; raise Error ("Bad Directory: " ^ (!dirPrefix) ^ "\n\n"))


	     val w = C.getWorld()
	     val _ = C.reset(metaSig)			     
	     val _ = C.setFilename(displayFname)
	     val _ = C.setWorld(w)

	     val res = ((Parse.fparse (displayFname, fname))
			handle DelphinParser.ParseError => (restoreOld() ; raise Error "Error Parsing File\n\n")
			     | _ => (restoreOld() ; raise Error "Error Parsing File\n\n"))

	     val (success, final) = convertAndEvaluateList(G, t, res)

	     val _ = restoreOld()

	   in
	     (success, final)
	   end

	 
       | convertAndEvaluate(G, t, (D.LFUse s)) = 
	   let
	     fun isDelim c = if ((c = #"\"") orelse (c = #" ")) then true else false
             val tokens = String.tokens isDelim s
	     val fname = case tokens
		          of [fname] => fname
			   | _ => (raise Error ("Bad Filename: " ^ s ^ "\n\n"))

	     val {dir=dir, file=fname} = OS.Path.splitDirFile fname

				  
	     val Iold = Interface.saveData()
	     val Pold = Paths.getLinesInfo()
	     val oldDirPrefix = !dirPrefix

	     fun restoreData() =
				  let
				    val _ = dirPrefix := oldDirPrefix
				    val _ = chDir (!startDir)
				    val _ = chDir (!dirPrefix)
				    val _ = Interface.restoreData Iold
				    val _ = Paths.restoreLinesInfo Pold
				  in
				    ()
				  end
	  
	     (* update dirPrefix *)
	     val _ = case (String.explode dir)
	               of [] => ()
		        | (#"/" :: _) => dirPrefix := dir
		        | _ => if (!dirPrefix) = "" then dirPrefix := dir
			       else dirPrefix := (!dirPrefix ^ "/" ^ dir)

	     (* Change directory *)
	     val _ = chDir (!startDir)
	     val newPath = OS.Path.joinDirFile {dir=(!dirPrefix), file=fname}
	     val newfname = OS.FileSys.realPath (newPath)
	                    handle _ => (restoreData() ; raise Error ("Bad Filename: " ^ newPath ^ "\n\n"))


	     val _ = Global.chatter := 0 (* was 3 *)	
	     (* val _ = print ("[Twelf Start] <\n") *)
	     val res = ((Twelf.loadFile newfname)
			handle _ => (restoreData() ; raise Error "Unexpected Twelf Error\n\n") (* All Exceptions should be handled by Twelf *))
	     (* val _ = print "> [Twelf End]\n\n" *)
	     val _ = print "[Twelf File Loaded...]\n\n" 
	     val _ = Global.chatter := 0
	     val _ = restoreData()
	   in
	     (true, (G, t))
	   end
			    

      | convertAndEvaluate (G, t, (D.LFTypeConstant (r,s,k, nameO, precO))) = 
		let
		  val _ = convertTypeConstant (r,s,k)
		  val _ = case (nameO)
		          of NONE => ()
			   | SOME (n) => convertName(n, s)

		  val _ = case (precO)
		          of NONE => ()
			   | SOME (i) => ((*  print (" ") ;*)  convertPrec(i, s))


		  (* DO NOT PRINT
		  val _ = print ";\n" 
		    *)
		in
		  (true, (G, t))
		end


      | convertAndEvaluate (G, t, (D.LFObjectConstant (r, lfdec, precO))) =
		let
		  val _ = convertObjectConstant (lfdec)
		  val D.LFDec(_, sOpt, _)   = lfdec
		  val s = case sOpt of
		             SOME s => s
			     | NONE => raise Domain (* not possible to declare constant without name *)

		  val _ = case (precO)
		          of NONE => ()
			   | SOME (i) => ((*  print (" ") ;*)  convertPrec(i, s))
		  (* DO NOT DO PRINTING
		  val _ = print ";\n"
		    *)
		in
		  (true, (G, t))
		end

      | convertAndEvaluate (G, t, (D.LFDef (r, lfdec, lfterm, false, precO))) =
		let
		  val dectoks = PrintDelphinExt.lfdecToTokens0 lfdec
		  val _ = addToSignature(dectoks @  [(L.EQUAL,r)] @ (PrintDelphinExt.lfexpToTokens(lfterm)) )

		  val D.LFDec(_, sOpt, _) = lfdec
		  val s = case sOpt of
		             SOME s => s
			     | NONE => raise Domain (* not possible to declare constant without name *)

		  val _ = case (precO)
		          of NONE => ()
			   | SOME (i) => ((*  print (" ") ;*)  convertPrec(i, s))
		in	
		  (true, (G, t))
		end


      | convertAndEvaluate (G, t, (D.LFDef (r, lfdec, lfterm, true, precO))) =
		let
		  val dectoks = PrintDelphinExt.lfdecToTokens0 lfdec
		  val _ = addToSignatureAbbrev(dectoks @  [(L.EQUAL,r)] @ (PrintDelphinExt.lfexpToTokens(lfterm)) )

		  val D.LFDec(_, sOpt, _) = lfdec
		  val s = case sOpt of
		             SOME s => s
			     | NONE => raise Domain (* not possible to declare constant without name *)

		  val _ = case (precO)
		          of NONE => ()
			   | SOME (i) => ((*  print (" ") ;*)  convertPrec(i, s))
		in	
		  (true, (G, t))
		end


      | convertAndEvaluate (G, t, D.TypeDef (r, name, F)) = 
           let
	      val resultO = ( SOME(C.convertFormula0 (G, F))
		handle Names.Error s => (raise Error (s ^ "\n\n"))
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n"))
		     | Error s => (raise Error ( s ^ "\n\n"))
		     | C.Error s => (raise Error ( s ^ "\n\n") )
		     | Subordinate.Error s => (raise Error ( s ^ "\n\n") )
(* ABP:  Should we catch all errors? 
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n"))
*)
)

	   in
	       case resultO
		  of NONE => (false, (G, t))
		   | SOME (FA, F') => (print ("[\"" ^ name ^ "\" Added as Type Alias...]\n\n" );
				 (metaSig := (name,FA,F') :: (!metaSig)) ; (true, (G, t)))
	   end


      | convertAndEvaluate (G, t, (E as D.MetaFix L)) =
	    let
	      val _ = freezeSignature()
	      fun find(x:string, []) = false
		| find(x, x'::xs) = (x = x') orelse find(x, xs)

	      fun hasDuplicates [] = false
		| hasDuplicates (x::xs) = find(x,xs) orelse hasDuplicates(xs)

	      fun getRegionInfo [(r, _, _)] = r
		| getRegionInfo ((r,_,_)::xs) = Paths.join (r, getRegionInfo xs)
		| getRegionInfo _ = raise Domain

	      fun getStringList [(r, D.NormalDec (_, SOME s, _), term)] = [s]
		| getStringList ((r,D.NormalDec (_, SOME s, _),term)::xs) = s::(getStringList xs)
		| getStringList _ = raise Domain

		
	      val sList = getStringList L

	      val r = getRegionInfo L

	      val _ = if hasDuplicates(sList) then 
		raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(), r), "Duplicate Identifiers defined in mutual recursion\n")) else ()



	      val _ = if !parseDebug then (print "\n-----BEGIN EXTERNAL SYNTAX-----\n" ; print (PrintDelphinExt.topDecStr (D.MetaFix L, true (* print eps *))) ; print "\n-----END EXTERNAL SYNTAX-----\n") else ()


	      val resultO = (SOME (C.convertFixList0(!smartInj, G, L))
		handle Names.Error s => (raise Error (s ^ "\n\n") )
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n") )
		     | Error s => (raise Error ( s ^ "\n\n") )
		     | C.Error s => (raise Error ( s ^ "\n\n") )
		     | Subordinate.Error s => (raise Error ( s ^ "\n\n") )
			     (* ABP:  Should we catch all errors?
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n"))
			      *)
			     )

	    in
	      (case resultO 
		 of NONE => (false, (G, t))
	          | SOME (result') => 
		           let 
			     val _ = if !parseDebug then (print "\n-----BEGIN INTERNAL SYNTAX (smartInj = false, debug = true, printPatternVars = true)-----\n" ; print (PrintDelphinInt.topFixToString(G, result', false, true, true)) ; print "\n-----END INTERNAL SYNTAX (smartInj = false, debug = true, printPatternVars = true)-----\n\n") else ()

				  
                             (* Strictness *)
			     val _ = DelphinStrictness.check(!smartInj, !printPatternVars, G, result')
			       handle DelphinStrictness.NotStrictError s => raise Error s (* Always quit on strictness error *)
                             
			     (* Coverage Checking *)
			     val _ = if (!enableCoverage) then
			             ((DelphinCoverage.checkCovers(!smartInj, !printPatternVars, G, result') ; ())
				      handle DelphinCoverage.CoverageError s => stop s)
				     else
				       ()

			     (* World Checking *)
			     val _ = if (!enableCoverage) then
			                    (WorldChecker.worldCheck(C.getFilename(), r, G, result')
					       handle WorldChecker.Error s => stop s)
				     else ()

			     val _ = if !parseDebug then (print "\n-----BEGIN INTERNAL SYNTAX (smartInj = false, debug = true, printPatternVars = true)-----\n" ; print (PrintDelphinInt.topFixToString(G, result', false, true, true)) ; print "\n-----END INTERNAL SYNTAX (smartInj = false, debug = true, printPatternVars = true)-----\n\n") else ()


                             (* Type checking *)
			     val _ = if (!doubleCheck) then
			         ((DelphinTypeCheck.inferType(G, result') ; ())
				  handle DelphinTypeCheck.Error s => raise Error ("Doublecheck Failed!  BUG IN DELPHIN!:  " ^ s))
				 else ()


			     (* Termination checking *)
			     val _ = if (!enableTermination) then
			             ((DelphinTermination.check(!debug, !smartInj, !printPatternVars, C.getFilename(), r, G, result') ; ())
				      handle DelphinTermination.Error s => ((stop s)))
				     else
				       ()


			     val Ddomain = (case D'.whnfE(result')
					      of D'.Fix (D, E) => D
					    | _ => raise Domain)

			     val _ = print (PrintDelphinInt.topFixToString(G, result', !smartInj, !debug, !printPatternVars))


			     val V = D'.substE'(result', t)


			     (*
                             (* Type checking *)
			     val _ = if (!tripleCheck) then
			         ((DelphinTypeCheck.inferType(I.Null, V) ; ())
				  handle DelphinTypeCheck.Error s => raise Error ("Triplecheck Failed!  BUG IN DELPHIN!:  " ^ s))
				 else ()
                             *)


			   in
			     (true, 
			        (I.Decl(G, (D'.InstantiableDec Ddomain)), 
				 D'.Dot(D'.Prg V, t)))
			   end
		)
	    end


      | convertAndEvaluate (G, t, (D.MetaVal (r, sO, term))) =
	    let
	      val _ = freezeSignature()
	      val _ = if !parseDebug then (print "\n-----BEGIN EXTERNAL SYNTAX-----\n" ; print (PrintDelphinExt.expToStr (term, true, true (* print pattern vars *))) ; print "\n-----END EXTERNAL SYNTAX-----\n") else ()



	      val resultO = ( SOME(C.convertMeta0 (!smartInj, G, term))
		handle Names.Error s => (raise Error (s ^ "\n\n") )
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n") )
		     | Error s => (raise Error ( s ^ "\n\n") )
		     | C.Error s => (raise Error ( s ^ "\n\n"))
		     | Subordinate.Error s => (raise Error ( s ^ "\n\n"))
(* ABP:  Should we catch all errors?
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n"))
*)
)

	    in
	      (case resultO
		 of NONE => (false, (G, t))
		  | SOME (result', T) => 
	                let

			  val s = (case sO
				     of NONE => "it"
				      | SOME s => s)

			  val Ddomain = D'.NormalDec(SOME [s], T)

			  val _ = if !parseDebug then (print "\n-----BEGIN INTERNAL SYNTAX (smartInj = false, debug = true, printPatternVars = true)-----\n" ; print (PrintDelphinInt.expToString(G, result', false, true, true)) ; print "\n-----END INTERNAL SYNTAX (smartInj = false, debug = true, printPatternVars = true)-----\n\n") else ()
			    


			  (* Strictness *)
			  val _ = DelphinStrictness.check(!smartInj, !printPatternVars, G, result')
			       handle DelphinStrictness.NotStrictError s => raise Error s (* Always quit on strictness error *)
                             
			  (* Coverage Checking *)
			  val _ = if (!enableCoverage) then
			             ((DelphinCoverage.checkCovers(!smartInj, !printPatternVars, G, result') ; ())
				      handle DelphinCoverage.CoverageError s => ((stop s)))
				     else
				       ()

                          (* World Checking *)
                          val _ = if (!enableCoverage) then
			                (WorldChecker.worldCheck(C.getFilename(), r, G, result')
					 handle WorldChecker.Error s => stop s)
				  else ()

				       

			  (* Type checking *)
			  val _ = if (!doubleCheck) then
			         ((DelphinTypeCheck.checkType(G, result', T) ; ())
				  handle DelphinTypeCheck.Error s => raise Error ("Doublecheck Failed!  BUG IN DELPHIN!:  " ^ s))
				  else ()


                          (* Termination checking *)
			  val _ = if (!enableTermination) then
			             ((DelphinTermination.check(!debug, !smartInj, !printPatternVars, C.getFilename(), r, G, result') ; ())
				      handle DelphinTermination.Error s => ((stop s)))
				     else
				       ()


			  val result = D'.substE'(result', t)


                          (*
			  (* Type checking *)
			  val _ = if (!tripleCheck) then
			           ((DelphinTypeCheck.checkType(I.Null, result, D'.substTypes(T, D'.coerceSub t)) ; ())
				    handle DelphinTypeCheck.Error s => raise Error ("Triplecheck Failed!  BUG IN DELPHIN!:  " ^ s))
				 else ()
                          *)

			    
			  val Vopt = eval result

			  val _ = print (solutionToString(s, PrintDelphinInt.typeToString(G, T, !smartInj), Vopt))

			  val _ = case Vopt of 
			           NONE => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),r),"Match Non-Exhaustive Failure"))
				   | _ => ()

			in
			  case Vopt
			      of NONE => (false, (G, t))
				
			       | SOME V' => (true, 
					     (I.Decl(G, (D'.InstantiableDec Ddomain)), 
					      D'.Dot(D'.Prg V', t)))
			end
		)
	    end


      | convertAndEvaluate(G, t, D.WorldDec Wnew) = 
	    let
	      val w = C.convertWorld Wnew
		handle Names.Error s => (raise Error (s ^ "\n\n"))
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n") )
		     | Error s => (raise Error ( s ^ "\n\n"))
		     | C.Error s => (raise Error ( s ^ "\n\n"))
		     | Subordinate.Error s => (raise Error ( s ^ "\n\n"))
			     (* ABP:  Should we catch all errors?
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n") )
			      *)

	      fun checkSubord (D'.Anything) = ()
		| checkSubord (D'.VarList []) = ()
		| checkSubord (D'.VarList ((_, V) :: vars)) = 
		            let
			      val _ =  Subordinate.respects (V, I.id)
				handle Subordinate.Error s => (raise Error ("Cannot set params!:  " ^ s ^ "\n\n"))
			    in
			      checkSubord (D'.VarList vars)
			    end
	      val _ = checkSubord w
	    in
	      (C.setWorld w ; 
	      (true, (G, t)))
	    end

	  

    and convertAndEvaluateList(G, t, []) = (true (* no errors *), (G, t))

      | convertAndEvaluateList(G, t, x::xs) =
            let
	      val (success, (G', t')) = convertAndEvaluate(G,t,x)
	        handle Error s => (print (s ^ "\n\n") ; (false, (G,t)) )
		     | Names.Error s => (print (s ^ "\n\n") ; (false, (G,t)) )
		     | Subordinate.Error s => (print (s ^ "\n\n") ; (false, (G,t)) )
		     | ReconTerm.Error s => (print (s ^ "\n\n") ; (false, (G,t)))
	    in
	      if success then 
		convertAndEvaluateList(G', t', xs)
	      else
		(false, (G', t'))
	    end



    fun loadFile s = (loadFile' s
                      handle (Error s) => print s)
 
    and loadFile' s =
      let 
	val _ = metaSig := nil

	val {dir=dir, file=fname} = OS.Path.splitDirFile s

	val oldDirPrefix = !dirPrefix
	val Cold = C.saveData()
	val Iold = Interface.saveData()
	val Pold = Paths.getLinesInfo()

	fun restoreOld() =
	  let
	    val _ = dirPrefix := oldDirPrefix
	    val _ = chDir (!startDir)
	    val _ = chDir (!dirPrefix)
	    val _ = C.restoreData Cold
	    val _ = Interface.restoreData(Iold)
	    val _ = Paths.restoreLinesInfo(Pold)
	  in
	    ()
	  end

        (* update dirPrefix *)
	val _ = case (String.explode dir)
	        of [] => ()
		 | (#"/" :: _) => dirPrefix := dir
		 | _ => if (!dirPrefix) = "" then dirPrefix := dir
			                     else dirPrefix := (!dirPrefix ^ "/" ^ dir)


	val _ = chDir (!startDir)
	val newPath = OS.Path.joinDirFile {dir=(!dirPrefix), file=fname}
	val displayFname = OS.FileSys.realPath (newPath)
	          handle _ => (restoreOld() ; raise Error ("Bad Filename: " ^ newPath ^ "\n\n"))

	val _ = (chDir (!dirPrefix))
		   handle _ => (restoreOld() ; raise Error ("Bad Directory: " ^ (!dirPrefix) ^ "\n\n"))



	val _ = Global.chatter := 0
	val _ = Twelf.reset()
	val _ = C.reset(metaSig) (* world defaultly set to D'.Anything *)
	val _ = C.setFilename(displayFname)
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
	(* val _ = print ("[Parsing file ...") *)
	val res = ((Parse.fparse (displayFname, fname))
	  handle DelphinParser.ParseError => (print ("Error Parsing File\n\n") ; [])
	       | _ => (print ("Error Parsing File\n\n") ; []))
	(* val _ = print ("[done]\n") *)

	val _ = convertAndEvaluateList(I.Null, D'.id, res)

	val _ = restoreOld()
      in 
	()
      end

    and top () = 
      let
	val _ = dirPrefix := "" (* in case there is a break in the middle *)
	val _ = metaSig := nil
	val _ = C.reset(metaSig) (* world defaultly set to D'.Anything *)
	val _ = print ("\n" ^ version ^ "\n\n")
	val _ = Global.chatter := 0
	val _ = Twelf.reset()
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
      in
	loop (ref (I.Null), ref (D'.id))
      end


    and top' (GRef, tRef) =
      let
	val _ = Global.chatter := 0
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
      in
	loop (GRef, tRef)
      end


    and loop (GRef, tRef) = 
      let 
	 fun invokeParser () =
	   let
	     val res = (Parse.sparse ()
			handle DelphinParser.ParseError => (print ("ERROR(S) Found\n\n") ; []))
	                (* Do not handle LexError so we can exit polySML by sending an exception -- ABP
			 | LexError => (print ("Lex Error\n\n") ; []))
	                *)
	   in
	     res
	   end

         val w = C.getWorld()
	 val _ = C.reset(metaSig)
	 val _ = C.setWorld(w)
         val _ = print prompt


         val res = invokeParser ()


	 fun convertAndEvaluateList'(G, t, []) = (G, t)

	   | convertAndEvaluateList'(G, t, x::xs) =
	            let
		      val (success, (G', t')) = convertAndEvaluate(G,t,x)
		      val _ = (GRef := G')
		      val _ = (tRef := t')
		    in
		      if success then
			convertAndEvaluateList'(G', t', xs)
		      else
			(G', t')
		    end
			handle Error s => (print (s ^ "\n\n") ; (!GRef, !tRef))
			     | Names.Error s => (print (s ^ "\n\n") ; (!GRef, !tRef))
			     | ReconTerm.Error s => (print (s ^ "\n\n") ; (!GRef, !tRef))
			     | Subordinate.Error s => (print (s ^ "\n\n") ; (!GRef, !tRef))



	 val (G', t') = (convertAndEvaluateList'(!GRef, !tRef, res))


      in 
         loop (GRef, tRef)
      end

     
  in
    val version = version
    val debug = debug
    val enableCoverage = enableCoverage
    val enableTermination = enableTermination
    val stopOnWarning = stopOnWarning
    val parseDebug = parseDebug
    val pageWidth = pageWidth
    val smartInj = smartInj
    val printPatternVars = printPatternVars
    val printImplicit = printImplicit
    val doubleCheck = doubleCheck
    val loadFile = loadFile
    val top = top
    val top' = top'

    fun changePath (s) =
      let
        val _ = dirPrefix := ""
	val _ = startDir := s
      in
	()
      end

    fun resetMetaSigAndWorld () =
      let
	val _ = metaSig := nil
	val _ = C.setWorld (D'.Anything)
      in
	()
      end

  end
end  (* functor DelphinTop *)
