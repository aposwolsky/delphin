(* Delphin Front-End *)
(* Author:  Adam Poswolsky *)

functor Delphin (structure DelphinParser : PARSERR
		 structure Parse : PARSE) : DELPHIN =
struct

  exception Error of string

  structure I = IntSyn
  structure T = Twelf
  structure D = DelphinExtSyntax
  structure D'= DelphinIntSyntax (* What we are converting to *)
  structure C = DelphinElab
  structure O = DelphinOpsem
  structure L = Lexer
  structure LS = Stream    

  local
    val version = "Delphin, Release Version 1.3.3, November 01, 2007"

    val debug = ref false
    val enableCoverage = ref false
    val enableWorlds = ref false
    val pageWidth = Formatter.Pagewidth
    val parseDebug = ref false
    val smartInj = ref true

    val metaSig = ref (nil : (string * DelphinApprox.Formula * D'.Formula) list)  (* for type aliasing *)

    val prompt = "D-- "

    (* contains information with respect to where we are with respect to
     * the starting directory 
     *)
    val dirPrefix = ref ""
    val startDir = ref (OS.FileSys.getDir())


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

	     val expFormat = PrintDelphinInt.expToFormat(I.Null, E, !smartInj, !debug)

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

    fun convertAndEvaluate(G, t, w, (D.Use s)) = 
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



	     val _ = C.reset(metaSig)			     
	     val _ = C.setFilename(displayFname)

	     val res = ((Parse.fparse (displayFname, fname))
			handle DelphinParser.ParseError => (restoreOld() ; raise Error "Error Parsing File\n\n")
			     | _ => (restoreOld() ; raise Error "Error Parsing File\n\n"))

	     val final = convertAndEvaluateList(G, t, w, res)
	                 handle _ => raise Domain (* should not throw any exceptions.. caught in convertAndEvaluate *)
	     val _ = restoreOld()

	   in
	     final
	   end

	 
       | convertAndEvaluate(G, t, w, (D.LFUse s)) = 
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
	     (G, t, w)	     
	   end
			    

      | convertAndEvaluate (G, t, w, (D.LFTypeConstant (r,s,k, nameO, precO))) = 
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
		  (G, t, w)
		end


      | convertAndEvaluate (G, t, w, (D.LFObjectConstant (r, lfdec, precO))) =
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
		  (G, t, w)
		end

      | convertAndEvaluate (G, t, w, (D.LFDef (r, lfdec, lfterm, false, precO))) =
		let
		  val dectoks = PrintDelphinExt.lfdecToTokens0 lfdec
		  val _ = addToSignature(dectoks @  [(L.EQUAL,r)] @ (PrintDelphinExt.lftermToTokens(lfterm)) )

		  val D.LFDec(_, sOpt, _) = lfdec
		  val s = case sOpt of
		             SOME s => s
			     | NONE => raise Domain (* not possible to declare constant without name *)

		  val _ = case (precO)
		          of NONE => ()
			   | SOME (i) => ((*  print (" ") ;*)  convertPrec(i, s))
		in	
		  (G, t, w)
		end


      | convertAndEvaluate (G, t, w, (D.LFDef (r, lfdec, lfterm, true, precO))) =
		let
		  val dectoks = PrintDelphinExt.lfdecToTokens0 lfdec
		  val _ = addToSignatureAbbrev(dectoks @  [(L.EQUAL,r)] @ (PrintDelphinExt.lftermToTokens(lfterm)) )

		  val D.LFDec(_, sOpt, _) = lfdec
		  val s = case sOpt of
		             SOME s => s
			     | NONE => raise Domain (* not possible to declare constant without name *)

		  val _ = case (precO)
		          of NONE => ()
			   | SOME (i) => ((*  print (" ") ;*)  convertPrec(i, s))
		in	
		  (G, t, w)
		end


      | convertAndEvaluate (G, t, w, D.TypeDef (r, name, F)) = 
           let
	      val resultO = ( SOME(C.convertFormula0 (G, F))
		handle Names.Error s => (raise Error (s ^ "\n\n"))
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n"))
		     | Error s => (raise Error ( s ^ "\n\n"))
		     | C.Error s => (raise Error ( s ^ "\n\n") )
(* ABP:  Should we catch all errors? 
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n"))
*)
)

	   in
	       case resultO
		  of NONE => (G, t, w)
		   | SOME (FA, F') => (print ("[\"" ^ name ^ "\" Added as Type Alias...]\n\n" );
				 (metaSig := (name,FA,F') :: (!metaSig)) ; (G, t, w))
	   end


      | convertAndEvaluate (G, t, w, (E as D.MetaFix L)) =
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



	      val _ = if !parseDebug then (print "\n-----BEGIN EXTERNAL SYNTAX-----\n" ; print (PrintDelphinExt.topDecStr (D.MetaFix L)) ; print "\n-----END EXTERNAL SYNTAX-----\n") else ()


	      val resultO = (SOME (C.convertFixList0(!smartInj, G, L))
		handle Names.Error s => (raise Error (s ^ "\n\n") )
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n") )
		     | Error s => (raise Error ( s ^ "\n\n") )
		     | C.Error s => (raise Error ( s ^ "\n\n") )
			     (* ABP:  Should we catch all errors?
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n"))
			      *)
			     )

	    in
	      (case resultO 
		 of NONE => (G, t, w)
	          | SOME (result') => 
		           let 
			     (* fill in the world to be the current world "w" *)
			     val result' = WorldSubsumption.fillInWorldExp (w, result')

			     val _ = if !parseDebug then (print "\n-----BEGIN INTERNAL SYNTAX (smartInj = false, debug = true)-----\n" ; print (PrintDelphinInt.topFixToString(G, result', false, true)) ; print "\n-----END INTERNAL SYNTAX (smartInj = false, debug = true)-----\n\n") else ()

			     val Ddomain = (case D'.whnfE(result')
					      of D'.Fix(D, E) => D
					    | _ => raise Domain)
			     val _ = print (PrintDelphinInt.topFixToString(G, result', !smartInj, !debug))
			     val V = D'.substE'(result', t)

                             (* Coverage Checking *)
			     val _ = if (!enableCoverage) then 
			            (DelphinCoverage.checkCovers(!smartInj, w, G, result')
				    handle DelphinCoverage.Error s => ((print (s ^ "\n\n"))))
				     else ()

			     (* World Checking *)
			     val _ = if (!enableWorlds) then
			             (WorldSubsumption.checkWorld(G, w, result')
			                 handle WorldSubsumption.Error s => (print (s ^ "\n\n")))
				     else ()

			   in
			        (I.Decl(G, (D'.InstantiableDec Ddomain)), 
				 D'.Dot(D'.Prg V, t), 
				 w)
			   end
		)
	    end


      | convertAndEvaluate (G, t, w, (D.MetaVal (r, sO, term))) =
	    let
	      val _ = freezeSignature()
	      val _ = if !parseDebug then (print "\n-----BEGIN EXTERNAL SYNTAX-----\n" ; print (PrintDelphinExt.expToStr (term, true)) ; print "\n-----END EXTERNAL SYNTAX-----\n") else ()



	      val resultO = ( SOME(C.convertMeta0 (!smartInj, G, term))
		handle Names.Error s => (raise Error (s ^ "\n\n") )
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n") )
		     | Error s => (raise Error ( s ^ "\n\n") )
		     | C.Error s => (raise Error ( s ^ "\n\n"))
(* ABP:  Should we catch all errors?
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n"))
*)
)

	    in
	      (case resultO
		 of NONE => (G, t, w)
		  | SOME (result', T) => 
	                let
			  (* fill in the world to be the current world "w" *)
			  val result' = WorldSubsumption.fillInWorldExp (w, result')
			  val T = WorldSubsumption.fillInWorldTypes (w, T)

			  val s = (case sO
				     of NONE => "it"
				      | SOME s => s)

			  val Ddomain = D'.NormalDec(SOME [s], T)

			  val _ = if !parseDebug then (print "\n-----BEGIN INTERNAL SYNTAX (smartInj = false, debug = true)-----\n" ; print (PrintDelphinInt.expToString(G, result', false, true)) ; print "\n-----END INTERNAL SYNTAX (smartInj = false, debug = true)-----\n\n") else ()
			    
			  (* Coverage Checking *)
			  val _ = if (!enableCoverage) then
			           (DelphinCoverage.checkCovers(!smartInj, w, G, result')
				   handle DelphinCoverage.Error s => (raise Error (s ^ "\n\n")))
				  else ()

			  (* World Checking *)
			  val _ = if (!enableWorlds) then
			          (WorldSubsumption.checkWorld(G, w, result')
				  handle WorldSubsumption.Error s => (raise Error (s ^ "\n\n")))
				  else
				    ()
			    
			in
			  (* if isWorldCorrect then  *)
			        let
				  val result = D'.substE'(result', t)

				  val Vopt = eval result

				  val _ = print (solutionToString(s, PrintDelphinInt.typeToString(G, T, !smartInj), Vopt))

				  val _ = case Vopt of 
				          NONE => raise Error (Paths.wrapLoc(Paths.Loc (C.getFilename(),r),"Match Non-Exhaustive Failure"))
					   | _ => ()
				in
				  case Vopt
				    of NONE => (G, t, w)

				  | SOME V' => (I.Decl(G, (D'.InstantiableDec Ddomain)), 
						D'.Dot(D'.Prg V', t), 
						w)
				end
			  (* else  (G, t, w)  *)
			end
		)
	    end


      | convertAndEvaluate(G, t, w, D.WorldDec Wnew) = 
	    ((G, t, C.convertWorld Wnew) 
		handle Names.Error s => (raise Error (s ^ "\n\n"))
		     | ReconTerm.Error s => (raise Error ( s ^ "\n\n") )
		     | Error s => (raise Error ( s ^ "\n\n"))
		     | C.Error s => (raise Error ( s ^ "\n\n"))
			     (* ABP:  Should we catch all errors?
		     | _=> (raise Error ( "Error! (ABP:  Add Details)" ^ "\n\n") )
			      *)
			     )

	  

    and convertAndEvaluateList(G, t, w, []) = (G, t, w)

      | convertAndEvaluateList(G, t, w, x::xs) =
            let
	      val (success, (G', t', w')) = (true, convertAndEvaluate(G,t,w,x))
	        handle Error s => (print (s ^ "\n\n") ; (false, (G,t,w)) )
		     | Names.Error s => (print (s ^ "\n\n") ; (false, (G,t,w)) )
		     | ReconTerm.Error s => (print (s ^ "\n\n") ; (false, (G,t,w)))
	    in
	      if success then 
		convertAndEvaluateList(G', t', w', xs)
	      else
		(G', t', w')
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
	val _ = C.reset(metaSig)
	val _ = C.setFilename(displayFname)
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
	(* val _ = print ("[Parsing file ...") *)
	val res = ((Parse.fparse (displayFname, fname))
	  handle DelphinParser.ParseError => (print ("Error Parsing File\n\n") ; [])
	       | _ => (print ("Error Parsing File\n\n") ; []))
	(* val _ = print ("[done]\n") *)

	val _ = ((convertAndEvaluateList(I.Null, D'.id, D'.Anything, res) ; ())
		 handle _ => raise Domain (* should not throw any exceptions *))

	val _ = restoreOld()
      in 
	()
      end

    and top () = 
      let
	val _ = dirPrefix := "" (* in case there is a break in the middle *)
	val _ = metaSig := nil

	val _ = print ("\n" ^ version ^ "\n\n")
	val _ = Global.chatter := 0
	val _ = Twelf.reset()
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
      in
	loop (ref (I.Null), ref (D'.id), ref (D'.Anything))
      end


    and top' (GRef, tRef, wRef) =
      let
	val _ = Global.chatter := 0
	val _ = CSManager.useSolver ("inequality/rationals")
	val _ = CSManager.useSolver ("equality/strings")
      in
	loop (GRef, tRef, wRef)
      end


    and loop (GRef, tRef, wRef) = 
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

	 val _ = C.reset(metaSig)
         val _ = print prompt


         val res = invokeParser ()


	 fun convertAndEvaluateList'(G, t, w, []) = (G, t, w)

	   | convertAndEvaluateList'(G, t, w, x::xs) =
	            let
		      val (G', t', w') = convertAndEvaluate(G,t,w,x)
		      val _ = (GRef := G')
		      val _ = (tRef := t')
		      val _ = (wRef := w')
		    in
		      convertAndEvaluateList'(G', t', w', xs)
		    end
			handle Error s => (print (s ^ "\n\n") ; (!GRef, !tRef, !wRef))
			     | Names.Error s => (print (s ^ "\n\n") ; (!GRef, !tRef, !wRef))
			     | ReconTerm.Error s => (print (s ^ "\n\n") ; (!GRef, !tRef, !wRef))
			     | Subordinate.Error s => (print (s ^ "\n\n") ; (!GRef, !tRef, !wRef))



	 val (G', t', w') = (convertAndEvaluateList'(!GRef, !tRef, !wRef, res)
	        handle _ => raise Domain (* should not raise any exceptions *) )


      in 
         loop (GRef, tRef, wRef)
      end

     
  in
    val version = version
    val debug = debug
    val enableCoverage = enableCoverage
    val enableWorlds = enableWorlds
    val parseDebug = parseDebug
    val pageWidth = pageWidth
    val smartInj = smartInj
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

    fun resetMetaSig () =
      let
	val _ = metaSig := nil
      in
	()
      end

  end
end  (* functor DelphinTop *)
