(* Delphin Elaborator (convert from external to internal syntax) *)
(* Author: Adam Poswolsky *)

structure DelphinElab : DELPHIN_ELABORATOR =
  struct
    exception Error of string
    structure D = DelphinExtSyntax  (* What we are converting from *)
    structure DI = DelphinIntermediateSyntax  (* External Syntax with LF-level filled in *)
    structure D' = DelphinIntSyntax (* What we are converting too *)
    structure T = DelphinTypeCheck
    structure I = IntSyn
    structure L = Lexer
    structure LS = Stream
    structure U = UnifyDelphin
    val filename = ref "stdIn"



    datatype returnType 
      = retLF of I.Exp
      | retDec of I.Dec

    datatype willReturnType
      = willLF of  (ReconTerm.dec I.Ctx) * ReconTerm.term * Paths.region
      | willDec of (ReconTerm.dec I.Ctx) * ReconTerm.dec * Paths.region


    fun reset() = (filename := "stdIn" )
    fun setFilename(s) = filename := s
    fun getFilename() = !filename

    fun typeStr(G, T) = PrintDelphinInt.typeToString(G, T)

    fun errorMsg(G, Tdesired, Tactual) =
      let
	val firstLine =  "   Expected Type: " ^ typeStr(G, Tdesired)
	val secondLine = "   Actual   Type: " ^ typeStr(G, Tactual)
      in
	"\n" ^ firstLine ^ "\n" ^ secondLine ^ "\n"
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


    fun getCase s = 
      let
	val c = case (String.explode(s)) 
	        of (c::xs) => c
		 | _ => raise Domain
      in
	if Char.isUpper(c) then L.ID (L.Upper, s) else L.ID (L.Lower, s)
      end

    (* get rid of extra EOF *)
    and prune([(L.EOF, _)]) = []
      | prune(x::xs) = x::prune(xs)
      | prune _ = raise Domain (* Invariant Violated! *)

    (* If it is more than just an ID, then we put parenthesis around it so LF parses it
     * the same way Delphin did.
     *)

    and optParen (r,(E as [(L.ID _, _)])) = E
      | optParen (r,E) = [(L.LPAREN,r)] @ E @ [(L.RPAREN, r)] 


    and lftypeTokens (D.TypeID (r,s)) = [(getCase s, r), (L.EOF, r)]
      | lftypeTokens (D.TypeApp (r,l1,l2)) = optParen(r, prune(lftypeTokens l1)) @ optParen(r, prune(lftermTokens l2)) @ [(L.EOF, r)]
      | lftypeTokens (D.PiType (r,lfdec, l1)) = [(L.LBRACE,r)] @ prune(lfdecTokens(lfdec)) @ [(L.RBRACE,r)] @ lftypeTokens(l1)
      | lftypeTokens (D.RtArrow (r, l1,l2)) = optParen(r, prune(lftypeTokens(l1))) @ [(L.ARROW,r)] @ optParen(r, prune(lftypeTokens(l2))) @  [(L.EOF, r)]
      | lftypeTokens (D.LtArrow (r, l1,l2)) = optParen(r, prune(lftypeTokens(l1))) @ [(L.BACKARROW,r)] @ optParen(r, prune(lftypeTokens(l2))) @ [(L.EOF, r)]
      | lftypeTokens (D.Omit r) = [(L.UNDERSCORE, r)]@ [(L.EOF, r)]
      | lftypeTokens (D.ExplicitLFType _) = raise Domain (* This is only used for printing.. should not happen here *)


    and lfdecTokens (D.LFDec (r, s,l)) = 
      let
	val Paths.Reg(a,b) = r
	val stringR = Paths.Reg(a, a + String.size(s))
      in
	[(getCase(s), stringR)] @  [(L.COLON,r)] @ lftypeTokens(l)
      end


    and lftermTokens (D.ObjectID (r,s)) = [(getCase s, r), (L.EOF, r)]
      | lftermTokens (D.Fn (r, d, t)) = [(L.LBRACKET,r)] @ prune(lfdecTokens(d)) @ [(L.RBRACKET,r)] @ prune(lftermTokens(t)) @ [(L.EOF, r)]
      | lftermTokens (D.LFApp (r, t1, t2)) = optParen(r,prune(lftermTokens(t1))) @ optParen(r, prune(lftermTokens(t2))) @ [(L.EOF, r)]

      | lftermTokens (D.Of (r,l,t)) =  optParen(r, prune(lftermTokens(l))) @ [(L.COLON,r)] @ optParen(r, prune(lftypeTokens(t))) @ [(L.EOF, r)]
      | lftermTokens (D.ExplicitLFTerm _) = raise Domain (* This is only used for printing.. should not happen here *)


    and kindTokens (D.Type r) = [(L.TYPE,r), (L.EOF, r)]
      | kindTokens (D.PiKind (r, D.LFDec(_, "_", lftype), k)) = prune(lftypeTokens(lftype)) @ [(L.ARROW, r)] @ prune(kindTokens(k)) @ [(L.EOF, r)]
      | kindTokens (D.PiKind (r, lfdec, k)) = [(L.LBRACE, r)] @ prune(lfdecTokens(lfdec)) @ [(L.RBRACE, r)] @ prune(kindTokens(k)) @ [(L.EOF, r)]


   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* Our first stage is to convert from the external syntax to the intermediate syntax
    * which goes through the external syntax and fills in all LF parts
    *)
    (* Our reconstruction returns a pair (1, 2)
     * 1 = A list of "jobs" to be sent to LF Type Reconstruction Algorithm
     * 2 = A continuation, f, such that we apply f to the result of LF Reconstruction to finish our reconstruction
     *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)

   (* Note that we pass around two contexts
    * D'.Dec I.Ctx  and   ReconTerm.dec I.Ctx
    * Note:  this is for the first phase of type reconstruction 
    *)
   fun convertNormalDec2Temp (G, ReconG, D.NormalDec (r, sO, D.LF(r2, isP, lftype))) = 
          let
	    val t = tokensToTerm (lftypeTokens lftype)
	    val D = ReconTerm.dec (sO, t, r) 

	    val jobs = [willDec (ReconG, D, r)]

	    fun f [retDec (I.Dec (_, A))] = DI.NormalDec (r, sO, DI.LF(r2, isP, A))
	      | f _ = raise Domain

	  in
	    (jobs, f, D)
	  end
     | convertNormalDec2Temp (G, ReconG, D.NormalDec (r, sO, D.Meta(r2, isP, F))) =
          let
	    val (jobs1, f1) = convertFormula2Temp(G, ReconG, F)

	    val D = ReconTerm.ndec (sO, r)

	    fun f x = DI.NormalDec(r, sO, DI.Meta(r2, isP, f1 x))

	  in
	    (jobs1, f, D)
	  end

   and convertNewDec2Temp (G, ReconG, D.NewDecLF (r, sO, lftype)) =
          let
	    val t = tokensToTerm (lftypeTokens lftype)

	    val D = ReconTerm.dec (sO, t, r)

	    val jobs = [willDec (ReconG, D, r)]

	    fun f [retDec (I.Dec (_, A))] = DI.NewDecLF (r, sO, A)
	      | f _ = raise Domain

	  in
	    (jobs, f, D)
	  end

     | convertNewDec2Temp (G, ReconG, D.NewDecMeta (r, sO, F)) =
          let
	    val (jobs1, f1) = convertFormula2Temp(G, ReconG, F)

	    val D = ReconTerm.ndec (sO, r)

	    fun f x = DI.NewDecMeta(r, sO, f1 x)

	  in
	    (jobs1, f, D)
	  end



   and convertTypes2Temp (G, ReconG, D.LF(r, isP, lftype)) =
         let
	   val t = tokensToTerm (lftypeTokens lftype)

	   val jobs = [willLF (ReconG, t, r)]

	   fun f [retLF A] = DI.LF(r, isP, A)
	     | f _ = raise Domain
	 in
	   (jobs, f)
	 end
     | convertTypes2Temp (G, ReconG, D.Meta(r, isP, F)) =
	 let
	   val (jobs1, f1) = convertFormula2Temp(G, ReconG, F)
	   fun f x = DI.Meta(r, isP, f1 x)
	 in
	   (jobs1, f)
	 end



     
   and convertFormula2Temp (G, ReconG, D.Top r) = 
           let
	     fun f [] = DI.Top r
	       | f _ = raise Domain
	   in
	     ([], f)
	   end
     | convertFormula2Temp (G, ReconG, D.All (r, D, F)) =
	   let
	     val (jobs1, f1, D') = convertNormalDec2Temp (G, ReconG, D)
	     val (jobs2, f2) = convertFormula2Temp (G, I.Decl(ReconG, D'), F)
	     val size1 = List.length jobs1
	     fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val D'' = f1 x1
		    val F'' = f2 x2
		  in
		    DI.All (r, D'', F'')
		  end
		      
	   in
	     (jobs1@jobs2, f)
	   end

     | convertFormula2Temp (G, ReconG, D.Exists (r, D, F)) =
	   let
	     val (jobs1, f1, D') = convertNormalDec2Temp (G, ReconG, D)
	     val (jobs2, f2) = convertFormula2Temp (G, I.Decl(ReconG, D'), F)
	     val size1 = List.length jobs1
	     fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val D'' = f1 x1
		    val F'' = f2 x2
		  in
		    DI.Exists (r, D'', F'')
		  end
		      
	   in
	     (jobs1@jobs2, f)
	   end

     | convertFormula2Temp (G, ReconG, D.Nabla (r, D, F)) =
	   let
	     val (jobs1, f1, D') = convertNewDec2Temp (G, ReconG, D)
	     val (jobs2, f2) = convertFormula2Temp (G, I.Decl(ReconG, D'), F)
	     val size1 = List.length jobs1
	     fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val D'' = f1 x1
		    val F'' = f2 x2
		  in
		    DI.Nabla (r, D'', F'')
		  end
		      
	   in
	     (jobs1@jobs2, f)
	   end
     | convertFormula2Temp (G, ReconG, D.OmittedFormula r) =
	   let
	     fun f [] = DI.OmittedFormula r
	       | f _ = raise Domain
	   in
	     ([], f)
	   end



   and convertExp2Temp (G, ReconG, D.VarString (r, s)) = 
           let
	     fun f [] = DI.VarString (r, s)
	       | f _ = raise Domain
	   in
	     ([], f)
	   end
     | convertExp2Temp (G, ReconG, D.VarInt (r, i)) =
           let
	     fun f [] = DI.VarInt (r, i)
	       | f _ = raise Domain
	   in
	     ([], f)
	   end

     | convertExp2Temp (G, ReconG, D.Quote (r, LFterm)) =
	   let	     
	     val jobs = [willLF(ReconG, tokensToTerm(lftermTokens(LFterm)), r)]

	     (* The result of this job will be "retLF" *)
	     fun f [retLF M] = DI.Quote (r, M)
	       | f _ = raise Domain
	   in
	     (jobs, f)
	   end

     | convertExp2Temp (G, ReconG, D.Unit r) =
           let
	     fun f [] = DI.Unit r
	       | f _ = raise Domain
	   in
	     ([], f)
	   end

     | convertExp2Temp (G, ReconG, D.Lam (r, Clist)) =
	   let
	     val jobFunList = map (fn C => convertCase2Temp(G, ReconG, C)) Clist

	     fun getJobList [] = []
	       | getJobList ((job,_)::xs) = job @ (getJobList xs)

	     val allJobs = getJobList jobFunList

	     fun f' ((jobs1,f1)::xs) x =
	                                  let
					    val size1= List.length jobs1
					    val x1 = List.take (x, size1)
					    val x2 = List.drop (x, size1)
					    val C' = f1 x1
					    val Clist' = f' xs x2
					  in
					    C' :: Clist'
					  end
	       | f' [] x = []


	     fun f x = DI.Lam(r, f' jobFunList x)
	   in
	     (allJobs, f)
	   end

     | convertExp2Temp (G, ReconG, D.New (r, D, E)) = 
	  let
	    val (jobs1, f1, D') = convertNewDec2Temp (G, ReconG, D)
	    val (jobs2, f2) = convertExp2Temp (G, I.Decl(ReconG, D'), E)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val D'' = f1 x1
		    val E'' = f2 x2
		  in
		    DI.New(r, D'', E'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertExp2Temp (G, ReconG, D.App (r, E1, E2)) = 
	  let
	    val (jobs1, f1) = convertExp2Temp (G, ReconG, E1)
	    val (jobs2, f2) = convertExp2Temp (G, ReconG, E2)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val E1'' = f1 x1
		    val E2'' = f2 x2
		  in
		    DI.App(r, E1'', E2'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertExp2Temp (G, ReconG, D.Pair (r, E1, E2)) = 
	  let
	    val (jobs1, f1) = convertExp2Temp (G, ReconG, E1)
	    val (jobs2, f2) = convertExp2Temp (G, ReconG, E2)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val E1'' = f1 x1
		    val E2'' = f2 x2
		  in
		    DI.Pair(r, E1'', E2'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertExp2Temp (G, ReconG, D.Pop (r, s, E)) = 
	  let
	    (* NOTE:  We only allow Pop up to end of ReconG
	     * G contains the fixpoints already processed, so this is acceptable
	     *)
	    fun lookupString (I.Null, s) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!"))
	      | lookupString (I.Decl(ReconG, D), s) = (case (ReconTerm.getStringOption D)
						    of NONE => lookupString(ReconG, s) + 1
						     | SOME s' => if (s=s') then 1 else lookupString(ReconG, s) + 1)
	    val i = lookupString (ReconG, s)
	    val ReconG' = D'.popCtx (i, ReconG)
	    val (jobs1, f1) = convertExp2Temp (G, ReconG', E)
	    fun f x = DI.Pop(r, s, f1 x)
	  in
	    (jobs1, f)
	  end

     | convertExp2Temp (G, ReconG, D.Fix (r, funList)) = 
	  let
	    val (jobs1, f1) = convertFunList2Temp(G, ReconG, funList)
	    fun f x = DI.Fix(r, f1 x)
	  in
	    (jobs1, f)
	  end

     | convertExp2Temp (G, ReconG, D.TypeAscribe (r, E, T)) = 
	  let
	    val (jobs1, f1) = convertExp2Temp(G, ReconG, E)
	    val (jobs2, f2) = convertTypes2Temp(G, ReconG, T)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val E'' = f1 x1
		    val T'' = f2 x2
		  in
		    DI.TypeAscribe(r, E'', T'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertExp2Temp (G, ReconG, D.Fst (r, E)) =
	  let
	    val (jobs1, f1) = convertExp2Temp(G, ReconG, E)
	    fun f x = DI.Fst (r, f1 x)
	  in
	    (jobs1, f)
	  end

     | convertExp2Temp (G, ReconG, D.Snd (r, E)) = 
	  let
	    val (jobs1, f1) = convertExp2Temp(G, ReconG, E)
	    fun f x = DI.Snd (r, f1 x)
	  in
	    (jobs1, f)
	  end

     | convertExp2Temp (G, ReconG, D.Sequence eList) = 
	   let
	     val jobFunList = map (fn (r,E) => (r, convertExp2Temp(G, ReconG, E))) eList

	     fun getJobList [] = []
	       | getJobList ((_,(job,_))::xs) = job @ (getJobList xs)

	     val allJobs = getJobList jobFunList

	     fun f' ((r, (jobs1,f1))::xs) x =
	                                  let
					    val size1= List.length jobs1
					    val x1 = List.take (x, size1)
					    val x2 = List.drop (x, size1)
					    val E' = f1 x1
					    val Elist' = f' xs x2
					  in
					    (r, E') :: Elist'
					  end
	       | f' [] x = []


	     fun f x = DI.Sequence (f' jobFunList x)
	   in
	     (allJobs, f)
	   end


     | convertExp2Temp (G, ReconG, D.LiftedApp (r, E1, E2)) =
	  let
	    val (jobs1, f1) = convertExp2Temp(G, ReconG, E1)
	    val (jobs2, f2) = convertExp2Temp(G, ReconG, E2)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val E1'' = f1 x1
		    val E2'' = f2 x2
		  in
		    DI.LiftedApp(r, E1'', E2'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertExp2Temp (G, ReconG, D.LetVar (r, D, E1, E2)) =
	  let
	    val (jobs1, f1, D') = convertNormalDec2Temp (G, ReconG, D)
	    val (jobs2, f2) = convertExp2Temp(G, ReconG, E1)
	    val ReconG' = I.Decl(ReconG, D')
	    val (jobs3, f3) = convertExp2Temp(G, ReconG', E2)
	    val size1 = List.length jobs1
	    val size2 = List.length jobs2
	      
	    fun f x =
	      let
		val x1 = List.take(x, size1)
		val xRest = List.drop(x,size1)
		val x2 = List.take(xRest, size2)
		val x3 = List.drop(xRest, size2)
		  
		val D'' = f1 x1
		val E1'' = f2 x2
		val E2'' = f3 x3
	      in
		DI.LetVar (r, D'', E1'', E2'')
	      end
	    
	  in
	    (jobs1@jobs2@jobs3, f)
	  end

     | convertExp2Temp (G, ReconG, D.LetFun (r, funList, E)) =
	  let
	    val (jobs1, f1) = convertFunList2Temp(G, ReconG, funList)
	    val ReconG' = I.Decl(ReconG, ReconTerm.ndec (NONE, r))	      
	    val (jobs2, f2) = convertExp2Temp(G, ReconG, E)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val funList'' = f1 x1
		    val E'' = f2 x2
		  in
		    DI.LetFun(r, funList'', E'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

	   

   and convertFunList2Temp (G, _, []) =
            let
	      fun f [] = []
		| f _ = raise Domain
	    in
	      ([], f)
	    end

     | convertFunList2Temp (G, ReconG, (r, D, E)::funlist) =
	    let
	      val (jobs1, f1, _) = convertNormalDec2Temp (G, ReconG, D)
	      val ReconG' = I.Decl(ReconG, ReconTerm.ndec (NONE, r))
	      val (jobs2, f2) = convertExp2Temp(G, ReconG', E)
	      val (jobs3, f3) = convertFunList2Temp(G, ReconG, funlist)
	      val size1 = List.length jobs1
	      val size2 = List.length jobs2
		
	      fun f x =
		let
		  val x1 = List.take(x, size1)
		  val xRest = List.drop(x,size1)
		  val x2 = List.take(xRest, size2)
		  val x3 = List.drop(xRest, size2)

		  val D'' = f1 x1
		  val E'' = f2 x2
		  val funlist'' = f3 x3
		in
		  (r, D'', E'') :: funlist''
		end

	    in
	      (jobs1@jobs2@jobs3, f)
	    end

           

   and convertCase2Temp (G, ReconG, D.Eps(r, D, C)) =
          let
	    val (jobs1, f1, D') = convertNormalDec2Temp (G, ReconG, D)
	    val (jobs2, f2) = convertCase2Temp (G, I.Decl(ReconG, D'), C)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val D'' = f1 x1
		    val C'' = f2 x2
		  in
		    DI.Eps(r, D'', C'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertCase2Temp (G, ReconG, D.NewC(r, D, C)) =
	  let
	    val (jobs1, f1, D') = convertNewDec2Temp (G, ReconG, D)
	    val (jobs2, f2) = convertCase2Temp (G, I.Decl(ReconG, D'), C)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val D'' = f1 x1
		    val C'' = f2 x2
		  in
		    DI.NewC(r, D'', C'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertCase2Temp (G, ReconG, D.Match(r, E1, E2)) =
	  let
	    val (jobs1, f1) = convertExp2Temp (G, ReconG, E1)
	    val (jobs2, f2) = convertExp2Temp (G, ReconG, E2)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val E1'' = f1 x1
		    val E2'' = f2 x2
		  in
		    DI.Match(r, E1'', E2'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end

     | convertCase2Temp (G, ReconG, D.MatchAnd(r, E, C)) =
	  let
	    val (jobs1, f1) = convertExp2Temp (G, ReconG, E)
	    val (jobs2, f2) = convertCase2Temp (G, ReconG, C)
	    val size1 = List.length jobs1
	    fun f x =
	          let
		    val x1 = List.take (x, size1)
		    val x2 = List.drop (x, size1)
		    val E'' = f1 x1
		    val C'' = f2 x2
		  in
		    DI.MatchAnd(r, E'', C'')
		  end
	  in
	    (jobs1 @ jobs2 , f)
	  end


  (* Here we build up LF Reconstruction job and send it to LF *)
   fun lfReconstruction (G, f, []) = f []
     | lfReconstruction (G, f, jobs) =
            let
	      fun createJob (willLF (ReconG, t, r)) = ReconTerm.jwithctx(ReconG, ReconTerm.jterm t)
		| createJob (willDec (ReconG, D, r)) = ReconTerm.jwithctx(I.Decl(ReconG, D), ReconTerm.jnothing)

	      fun getRegion (willLF (_, _, r)) = r
		| getRegion (willDec (_, _, r)) = r

	      fun getRegionL [x] = getRegion x
		| getRegionL (x::xs) = Paths.join(getRegion x, getRegionL xs)
		| getRegionL _ = raise Domain

	      fun listToAnd [] = ReconTerm.jnothing
		| listToAnd (x::xs) = ReconTerm.jand(x, listToAnd (xs))

	      val jobList = map createJob jobs
	      val masterJob = listToAnd jobList

	      val _ = ReconTerm.resetErrors(!filename)
	      val answerJob = ReconTerm.reconWithCtx (D'.coerceCtx G, masterJob)
	      val _ = ReconTerm.checkErrors(getRegionL jobs)

	      fun getAnswers ([], ReconTerm.JNothing) = []
		| getAnswers ((willLF _)::xs, ReconTerm.JAnd(ReconTerm.JWithCtx(_, ReconTerm.JTerm ((U, _), A, _)), jobs)) =
						   (retLF U) :: (getAnswers (xs, jobs))
		| getAnswers ((willDec _)::xs, ReconTerm.JAnd(ReconTerm.JWithCtx(I.Decl(_, D), ReconTerm.JNothing), jobs)) =
						   (retDec D) :: (getAnswers (xs, jobs))
		| getAnswers _ = raise Domain 

	      val ansL = getAnswers(jobs, answerJob)
	    in
	      f ansL
	    end
		
         

	
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)
   (* 
    * Second Phase:  Convert from DelphinIntermediateSyntax to DelphinIntSyntax
    *
    *)
   (* ***************************************************************************************************** *)
   (* ***************************************************************************************************** *)

   fun findIndex(s, [], n) = NONE
     | findIndex(s:string, (s'::sL), n) = if (s=s') then (SOME n) else findIndex(s, sL, n+1)

   fun getIndex (1, D'.Meta(isP, D'.FormList (F::_))) = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error ("Fixpoint specified to have a parameter type")
		     in
		       D'.Meta(D'.Existential, F)
		     end
     | getIndex (i, D'.Meta(isP, D'.FormList (_::fList))) = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error ("Fixpoint specified to have a parameter type")
		     in
		       getIndex(i-1, D'.Meta(D'.Existential, D'.FormList fList))
		     end

     | getIndex _ = raise Domain (* fixpoint not constructed properly if it is a projection without an appropriate list of formulas *)

   fun checkVar(s, k, NONE, T) = NONE
     | checkVar(s : string, k, SOME [s'], T) = if (s=s') then SOME(D'.Var k, T) else NONE
     | checkVar(s, k, SOME sL, T) = (case (findIndex(s, sL, 1))
				    of NONE => NONE
				      | SOME n => SOME(D'.Proj(D'.Var k, n), getIndex (n, T)))
	      


   fun lookupString (r, I.Null, s, k) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!"))
     | lookupString (r, I.Decl(G, (D'.InstantiableDec (D'.NormalDec (sLO, T0)))), s, k ) = 
				       (case checkVar(s, k, sLO, T0)
					  of NONE => lookupString(r, G, s, k+1)
					   | SOME (E', T) => (E', D'.substTypes(T, I.Shift k))
					)
     | lookupString (r, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecLF (SOME s', A)))), s, k) = 
					  if (s=s') then 
					    (D'.Var k, D'.substTypes(D'.LF(D'.Param, A), I.Shift k))
					  else
					    lookupString(r, G, s, k+1)

     | lookupString (r, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecMeta (SOME s', F)))), s, k) = 
					 if (s=s') then 
					   (D'.Var k, D'.substTypes(D'.Meta(D'.Param, F), I.Shift k))
					 else
					   lookupString(r, G, s, k+1)

     | lookupString (r, I.Decl(G, (D'.NonInstantiableDec _)), s, k) = 
					   (* Dec has no name *)
					   lookupString(r, G, s, k+1)


   fun lookupInt (r, i, I.Null, _) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable #" ^ (Int.toString i) ^ " not found!"))
     | lookupInt (r, i, I.Decl(G, (D'.InstantiableDec (D'.NormalDec (_, T0)))), 1 ) = (D'.Var i, D'.substTypes(T0, I.Shift i))
     | lookupInt (r, i, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecLF (_, A)))), 1) = (D'.Var i, D'.substTypes(D'.LF(D'.Param, A), I.Shift i))
     | lookupInt (r, i, I.Decl(G, (D'.NonInstantiableDec (D'.NewDecMeta (_, F)))), 1) = (D'.Var i, D'.substTypes(D'.Meta(D'.Param, F), I.Shift i))
     | lookupInt (r, i, I.Decl(G, _), k) = lookupInt(r, i, G, k-1)


   (* Only look for NonInstantiableDecs *)
   fun lookupNewString (r, I.Null, s, k) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not found!"))
     | lookupNewString (r, I.Decl(G, (D'.InstantiableDec (D'.NormalDec (sLO, T0)))), s, k ) = 
				       (case checkVar(s, k, sLO, T0)
					  of NONE => lookupNewString(r, G, s, k+1)
					   | SOME (E', T) => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " not a new parameter!"))
					)
     | lookupNewString (r, I.Decl(G, (D'.NonInstantiableDec (D as D'.NewDecLF (SOME s', A)))), s, k) = 
					  if (s=s') then 
					    (k, D)
					  else
					    lookupNewString(r, G, s, k+1)

     | lookupNewString (r, I.Decl(G, (D'.NonInstantiableDec (D as D'.NewDecMeta (SOME s', F)))), s, k) = 
					 if (s=s') then 
					   (k, D)
					 else
					   lookupNewString(r, G, s, k+1)

     | lookupNewString (r, I.Decl(G, (D'.NonInstantiableDec _)), s, k) = 
					   (* Dec has no name *)
					   lookupNewString(r, G, s, k+1)
     


   fun inferType (G, DI.Quote (_, M)) = 
             let
	       val A = TypeCheck.infer'(D'.coerceCtx G, M)
		 handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
		      
	     in
	       D'.LF(D'.Existential, A)
	     end

     | inferType (G, DI.VarString (r, s)) = 
	     let 
	       val (_, T) = lookupString(r, G, s, 1)
	     in
	       T
	     end

     | inferType (G, DI.VarInt (r, i)) = 
	     let
	       val (_, T) = lookupInt(r, i, G, i)
	     in
	       T
	     end

     | inferType (G, DI.TypeAscribe (_, E, _)) = inferType (G, E)

     | inferType (G, _) = 
	     D'.Meta(D'.newPVar(), D'.newFVar(G))

   fun convertIsParam(D.Existential) = D'.Existential
     | convertIsParam(D.Param) = D'.Param
     | convertIsParam(D.OmittedParam) = D'.newPVar()


   fun convertNormalDec (G, DI.NormalDec(r, sO, T)) = 
              let
		fun toList NONE = NONE
		  | toList (SOME s) = SOME [s]
		  
		val sLO = toList sO
		val T' = convertTypes(G, T)
	      in
		D'.NormalDec (sLO, T')
	      end

   and convertNewDec (G, DI.NewDecLF (r, sO, A)) = D'.NewDecLF(sO, A)
     | convertNewDec (G, DI.NewDecMeta (r, sO, F)) = D'.NewDecMeta(sO, convertFormula(G, F))


   and convertTypes (G, DI.LF(_, isP, A)) = D'.LF(convertIsParam isP, A)
     | convertTypes (G, DI.Meta (_, isP, F)) = D'.Meta(convertIsParam isP, convertFormula(G, F))


   and convertFormula (G, DI.Top _) = D'.Top
     | convertFormula (G, DI.All(r, D, F)) = 
            let
	      val D' = convertNormalDec (G, D)
	      val F' = convertFormula(I.Decl(G, D'.InstantiableDec D'), F)
	    in
	      D'.All(D', F')
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
     | convertFormula (G, DI.OmittedFormula _) = D'.newFVar(G)	  

   fun convertExp (G, DI.VarString (r, s), Tresult) =
         let
	   val (E', T) = lookupString(r, G, s, 1)
	   val _ = U.unifyT(G, T, Tresult)
	       handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable " ^ s ^ " of incompatible type: "  ^ msg ^ errorMsg(G, Tresult, T)))
	 in
	   E'
	 end


     | convertExp (G, DI.VarInt (r, i), Tresult) =
         let
	   val (E', T) = lookupInt(r, i, G, i)
	   val _ = U.unifyT(G, T, Tresult)
	       handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Variable #" ^ (Int.toString i) ^ " of incompatible type: " ^ msg ^ errorMsg(G, Tresult, T)))

	 in
	   E'
	 end

     | convertExp (G, DI.Quote (r, M), Tresult) =
	   let
	     val A = TypeCheck.infer'(D'.coerceCtx G, M)
		 handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)

	     val _ = U.unifyT(G, D'.LF(D'.Existential, A), Tresult)
	       handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Incompatible types: " ^ msg ^ errorMsg(G, Tresult, D'.LF(D'.Existential, A))))
		 
	   in
	     D'.Quote M
	   end



     | convertExp (G, DI.Unit r, Tresult) = 
	   let
	     val _ = U.unifyT(G, D'.Meta(D'.Existential,D'.Top), Tresult)
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "() has incompatible type: " ^ msg ^ errorMsg(G, Tresult, D'.Meta(D'.Existential,D'.Top))))

	   in
	     D'.Unit
	   end

     | convertExp (G, DI.Lam (r, Clist), Tresult) =
	   let
	     val F = D'.newFVar(G)
	     val _ = U.unifyT(G, D'.Meta(D'.Existential, F), Tresult)
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Function has incompatible type: " ^ msg ^ errorMsg(G, Tresult, D'.Meta(D'.Existential,F))))
	     val Clist' = map (fn C => convertCase(G, C, Tresult)) Clist

	     fun f x = D'.Lam(Clist', F)
	   in
	     D'.Lam(Clist', F)
	   end

     | convertExp (G, DI.New(r, D, E), Tresult) =
	   let
	     val D' = convertNewDec(G, D)
	     val G' = I.Decl(G, D'.NonInstantiableDec D')
	     val newResult = D'.newFVar(G')
	     val nablaType = D'.Meta(D'.Existential, D'.Nabla(D', newResult))
	     val _ = U.unifyT(G, Tresult, nablaType)
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G, Tresult, nablaType)))

	     val E' = convertExp(G', E, D'.Meta(D'.Existential, newResult))
	   in
	     D'.New(D', E')
	   end


     | convertExp (G, DI.App(r, E1, E2), Tresult) = 
	   let
	     val argType = inferType(G, E2)
	       
	     val D = D'.NormalDec(NONE, argType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val funResult = D'.newFVar(G')



	     val funF = D'.All (D, funResult)
	     val funType = D'.Meta(D'.Existential, funF)

	     val E1' = convertExp(G, E1, funType)

	     val E2' = convertExp(G, E2, argType)

	     val t = D'.Dot(D'.Prg E2', D'.id)  (* G |- E2'.id  : G' *)
	     val _ = U.unifyT(G, Tresult, D'.Meta(D'.Existential, D'.substF(funResult, D'.coerceSub t)))
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G, Tresult, D'.Meta(D'.Existential, D'.substF(funResult, D'.coerceSub t)))))
	   in
	     D'.App(E1', E2')
	   end

     | convertExp (G, DI.Pair(r, E1, E2), Tresult) = 
	   let
	     val F = D'.newFVar(G)

	     val _ = U.unifyT (G, Tresult, D'.Meta(D'.Existential, F))
	       	     handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G, Tresult, D'.Meta(D'.Existential, F))))

		       
	     val firstType = inferType(G, E1)
	     val D = D'.NormalDec(NONE, firstType)
	     val G' = I.Decl(G, D'.InstantiableDec D)
	     val secondF = D'.newFVar(G')
	     val pairF = D'.Exists(D, secondF)
	     val pairType = D'.Meta(D'.Existential, pairF)

	     val _ = U.unifyT (G, Tresult, pairType)
	       	     handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G,Tresult, pairType)))

	     val E1' = convertExp(G, E1, firstType)
	     val t = D'.Dot(D'.Prg E1', D'.id)
	     val E2' = convertExp(G, E2, D'.Meta(D'.Existential, D'.substF(secondF, D'.coerceSub t)))
	   in
	     D'.Pair(E1', E2', F)
	   end

     | convertExp (G, DI.Pop(r, s, E), Tresult) = 
	   let
	     val (i, D) = lookupNewString (r, G, s, 1)
	     val G' = D'.popCtx(i, G)	       
	     val F = D'.newFVar(I.Decl(G', D'.NonInstantiableDec D))
	     val T = D'.Meta(D'.Existential, D'.Nabla(D, F))
	     val Tshift = D'.Meta(D'.Existential, D'.substF(F, I.Shift (i-1)))
	     val _ = U.unifyT(G, Tshift, Tresult)
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G, Tresult, Tshift)))
	     val E' = convertExp(G', E, T)
	   in
	     D'.Pop(i, E')
	   end

     | convertExp (G, DI.Fix(r, funList), Tresult) =  D'.Fix (convertFunList(G, r, funList, Tresult))
	     

     (* syntactic sugar *)
     | convertExp (G, DI.TypeAscribe (r, E, T), Tresult) = 
	   let
	     val T' = convertTypes(G, T)
	     val _ = U.unifyT(G, T', Tresult)
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G, Tresult, T')))
	   in
	     convertExp(G, E, Tresult)
	   end

     | convertExp (G, DI.Fst (r, E), Tresult) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "fst syntactic sugar NOT IMPLEMENTED YET (ADAM)"))
     | convertExp (G, DI.Snd (r, E), Tresult) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "snd syntactic sugar NOT IMPLEMENTED YET (ADAM)"))
     | convertExp (G, DI.Sequence Elist, Tresult) = raise Error ("sequence syntactic sugar NOT IMPLEMENTED YET (ADAM)")
     | convertExp (G, DI.LiftedApp(r, E1, E2), Tresult) = raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "@ syntactic sugar NOT IMPLEMENTED YET (ADAM)"))
     | convertExp (G, DI.LetVar (r, D, E1, E2), Tresult) = 
	   let
	     val C = DI.Eps(r, D, (DI.Match(r, DI.VarInt(r, 1), E2)))
	     val f = DI.Lam(r, [C])
	   in
	     convertExp(G, DI.App(r, f, E1), Tresult)
	   end

     | convertExp (G, DI.LetFun (r, funList, E), Tresult) = 
	   let
	     val (D', E') = convertFunList(G, r, funList, D'.Meta(D'.Existential, D'.newFVar G))
	     val fixE = D'.Fix (D', E')

	     val G' = I.Decl(G, D'.InstantiableDec D')
	     val F = D'.newFVar G'
	     val Tshift = D'.substTypes(Tresult, I.shift)

	     val _ = U.unifyT(G', D'.Meta(D'.Existential, F), Tshift)
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G', Tshift, D'.Meta(D'.Existential, F))))

	     val E' = convertExp(I.Decl(G, D'.InstantiableDec D'), E, Tshift)
	     val C' = D'.Eps (D', D'.Match (D'.Var 1, E'))
	   in
	     D'.App(D'.Lam ([C'],D'.All(D', F)), E')
	   end


    and convertFunList (G, r, funList, Tresult) =
	   let
	     val decList  = map (fn (_,D,_) => convertNormalDec(G, D)) funList
	     fun decListString [D'.NormalDec(SOME [s], _)] = [s]
	       | decListString ((D'.NormalDec(SOME [s], _)) :: decs) = s :: (decListString decs)
	       | decListString _ = raise Domain (* badly formed fixpoint *)

	     fun decListFormulas [D'.NormalDec(_, D'.Meta(isP, F))] = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Fixpoint specified to have a parameter type"))		     in
			   [F]
		     end
	       | decListFormulas ((D'.NormalDec(_, D'.Meta(isP, F))) :: decs) = 
                     let
		       val _ = U.unifyP(isP, D'.Existential)
			 handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Fixpoint specified to have a parameter type"))		     in
			   F :: (decListFormulas decs)
		     end

	       | decListFormulas _ = raise Domain (* badly formed fixpoint *) 


	     fun decListFormula [F] = F
	       | decListFormula Flist = D'.FormList Flist

	     val Flist = decListFormulas decList
	     val F = decListFormula Flist
	     val _ = U.unifyT(G, Tresult, D'.Meta(D'.Existential, F))
	             handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Type mismatch: " ^ msg ^ errorMsg(G, Tresult, D'.Meta(D'.Existential, F))))
	     val D = D'.NormalDec (SOME (decListString decList), D'.Meta(D'.Existential, F))
	     val G' = I.Decl(G, D'.InstantiableDec D)
	       
	     (* We need to shift the formula so it makes sense in G' *)
	     fun pairFormula ([], []) = []
	       | pairFormula ((_, _, E)::fList, F::formList) = (E, D'.substF(F,I.shift)) :: pairFormula(fList, formList)
	       | pairFormula _ = raise Domain (* badly formed fixpoint *)


	     val expFormList = pairFormula (funList, Flist)


	     val expList = map (fn (E,F) => convertExp(G', E, D'.Meta(D'.Existential, F))) expFormList


	     fun listToExp [E] = E
	       | listToExp Elist = D'.ExpList Elist


	     val E = listToExp expList

	   in
	     (D, E)
	   end
      


    and convertCase (G, DI.Eps(r, D, C), Tresult) =
                                  let
				    val D' = convertNormalDec(G, D)
				    val G' = I.Decl(G, D'.InstantiableDec D')
				    val C' = convertCase(G', C, D'.substTypes(Tresult, I.shift))
				  in
				    D'.Eps(D', C')
				  end


      | convertCase (G, DI.NewC(r, D, C), Tresult) =
				  let
				    val D' = convertNewDec (G, D)
				    val G' = I.Decl(G, D'.NonInstantiableDec D')
				    val newResult = D'.newFVar(G')
				    val nablaType = D'.Meta(D'.Existential, D'.Nabla(D', newResult))
				    val _ = U.unifyT(G, Tresult, nablaType)
				      handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "New has incompatible type: " ^ msg ^ errorMsg(G, Tresult, nablaType)))

				    val C' = convertCase(G', C, D'.Meta(D'.Existential, newResult))
				  in
				    D'.NewC(D', C')
				  end

      | convertCase (G, DI.Match(r, E1, E2), Tresult) =
				  let
				    val argType = inferType(G, E1)
				    val D = D'.NormalDec(NONE, argType)

				    val G' = I.Decl(G, D'.InstantiableDec D)
				    val funResult = D'.newFVar(G')

				    val _ = U.unifyT(G, Tresult, D'.Meta(D'.Existential, D'.All(D, funResult)))
				      handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Match has incompatible type: " ^ msg ^ errorMsg(G, Tresult, D'.Meta(D'.Existential, D'.All(D, funResult)))))

				    val E1' = convertExp(G, E1, argType)
				    val t = D'.Dot (D'.Prg E1', D'.id)

				    val E2' = convertExp(G, E2, D'.Meta(D'.Existential, D'.substF(funResult, D'.coerceSub t)))

				  in
				    D'.Match (E1', E2')
				  end

      | convertCase (G, DI.MatchAnd(r, E, C), Tresult) =
				  let
				    val argType = inferType(G, E)
				    val D = D'.NormalDec(NONE, argType)

				    val G' = I.Decl(G, D'.InstantiableDec D)
				    val funResult = D'.newFVar(G')

				    val _ = U.unifyT(G, Tresult, D'.Meta(D'.Existential, D'.All(D, funResult)))
				      handle U.Error msg => raise Error (Paths.wrapLoc(Paths.Loc (!filename, r), "Match has incompatible type: " ^ msg ^ errorMsg(G, Tresult, D'.Meta(D'.Existential, D'.All(D, funResult)))))

				    val E' = convertExp(G, E, argType)
				    val t = D'.Dot (D'.Prg E', D'.id)

				    val C' = convertCase(G, C, D'.Meta(D'.Existential, D'.substF(funResult, D'.coerceSub t)))

				  in
				    D'.MatchAnd (E', C')
				  end


				

  (* ***************************************************************************************************** *)
  (* ***************************************************************************************************** *)
  (* 
   * Putting it together.
   *
   *)
  (* ***************************************************************************************************** *)
  (* ***************************************************************************************************** *)


   fun convertMeta0 (G, E) =
         let
	   val (jobs, f) = convertExp2Temp(G, I.Null, E)
	   val E' = lfReconstruction(G, f, jobs)
	   val T = inferType (G, E')
	 in
	   (convertExp(G, E', T), T)
	 end

      
   fun convertFixList0 (G, funList) =
         let
	   val (jobs, f) = convertFunList2Temp(G, I.Null, funList)
	   val funList' = lfReconstruction(G, f, jobs)
	   val T = D'.Meta(D'.Existential, D'.newFVar G)

	   fun getRegion [] = raise Domain
	     | getRegion [(r,_,_)] = r
	     | getRegion ((r,_,_)::xs) = Paths.join(r, getRegion xs)

	   val r = getRegion funList

	   val (D', E') = convertFunList (G, r, funList', T)

	 in
	   D'.Fix(D', E')
	 end

  end