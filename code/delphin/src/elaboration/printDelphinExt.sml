(* 
 * Used to print Delphin External Syntax 
 * solely for Parser debugging use 
 * Author:  Adam Poswolsky
 *)
structure PrintDelphinExt =
  struct

    structure D = DelphinExtSyntax
    structure Fmt = Formatter
    structure L = Lexer
    (* Precisions chosen to be consistent with order of delphin.grm *)
    val minPrec = 0

    val eqArrowPrec = 35
    val bracketPrec = 40
    val bracePrec = 40

    val colonPrec = 73
    val rtArrowPrec = 76
    val ltArrowPrec = 77
    val withPrec = 79
    val andPrec = 80 (* for "*" ","  "and" *)


    val popPrec = 85
    val fstsndPrec = 85
    val appPrec = 90
    val maxPrec = 100
    datatype Assoc = Left | Right

    fun baseK (x, _) = x

    fun parenlt (prec, prec') fmt = 
      if prec < prec' then fmt else Fmt.Hbox [Fmt.String "(", fmt, Fmt.String ")"]
    fun parenle (prec, prec') fmt = 
      if prec <= prec' then fmt else Fmt.Hbox [Fmt.String "(", fmt, Fmt.String  ")"]

    fun fmtinfix box (Left, prec, ((fmt1, prec1), SOME fmt, (fmt2, prec2))) =
            box [parenle (prec, prec1) fmt1, Fmt.Break, fmt, Fmt.Break, parenlt (prec, prec2) fmt2]
      | fmtinfix box (Right, prec, ((fmt1, prec1), SOME fmt, (fmt2, prec2))) =
	    box [parenlt (prec, prec1) fmt1, Fmt.Break, fmt, Fmt.Break, parenle (prec, prec2) fmt2]
      | fmtinfix box (Left, prec, ((fmt1, prec1), NONE, (fmt2, prec2))) =
            box [parenle (prec, prec1) fmt1, Fmt.Break, parenlt (prec, prec2) fmt2]
      | fmtinfix box (Right, prec, ((fmt1, prec1), NONE, (fmt2, prec2))) =
	    box [parenlt (prec, prec1) fmt1, Fmt.Break, parenle (prec, prec2) fmt2]

    fun fmtprefix (prec, (fmt1, (fmt2, prec2))) =
      Fmt.Hbox [fmt1, Fmt.Break, parenlt (prec, prec2) fmt2]

    (* to handle [x] [y] ... *)
    fun fmtprefix2 (prec, (fmt1, (fmt2, prec2))) =
      Fmt.Hbox [fmt1, Fmt.Break, parenle (prec, prec2) fmt2]

    
    

    (* We now save parenthesis information for LF when parsing (for infix operators)
     * so we do not need to keep track of precedences here..
    OLD
    fun lfdecToFormat (D.LFDec (_,s,A)) = Fmt.HVbox[Fmt.String(s), Fmt.Break, Fmt.String(":"), Fmt.Break, lftypeToFormat0 (A, baseK)]
     
    and lftypeToFormat0 (D.TypeID (_, s), k) = k (Fmt.String s, maxPrec)
      | lftypeToFormat0 (D.TypeApp (_, A, m), k) = 
		   lftypeToFormat0 (A, 
				 fn (fmt1, prec1) => lftermToFormat0 (m, 
				 fn (fmt2, prec2) => k (fmtinfix Fmt.HOVbox (Left, appPrec, ((fmt1, prec1),
									NONE, (fmt2, prec2))),
						       appPrec)))

      | lftypeToFormat0 (D.PiType (_, lfdec, A), k) =
                     let
		       val lfdecFmt = Fmt.HVbox[Fmt.String("{"), lfdecToFormat lfdec, Fmt.String("}")]
		     in
		       lftypeToFormat0 (A,
				      fn (fmt, prec) =>
				      k (fmtprefix2 (bracePrec, (lfdecFmt, (fmt, prec))), bracePrec))
		     end

      | lftypeToFormat0 (D.RtArrow (r, A1, A2), k) =
		     lftypeToFormat0 (A1, 
			fn (fmt1, prec1) => lftypeToFormat0 (A2, 
			fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, rtArrowPrec, ((fmt1, prec1),
						SOME(Fmt.String("->")), (fmt2, prec2))),   rtArrowPrec)))

      | lftypeToFormat0 (D.LtArrow (r, A1, A2), k) =
		     lftypeToFormat0 (A1, 
			 fn (fmt1, prec1) => lftypeToFormat0 (A2, 
			 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Left, ltArrowPrec, ((fmt1, prec1),
						SOME(Fmt.String("<-")), (fmt2, prec2))),   ltArrowPrec)))

      | lftypeToFormat0 (D.Omit _, k) = k (Fmt.String "_", maxPrec)
      | lftypeToFormat0 (D.ExplicitLFType f, k) = k (f, minPrec)

    and lftermToFormat0 (D.ObjectID (_, s), k) = k (Fmt.String s, maxPrec)
      | lftermToFormat0 (D.Fn (_, lfdec, M), k) = 
                     let
		       val lfdecFmt = Fmt.HVbox[Fmt.String("["), lfdecToFormat lfdec, Fmt.String("]")]
		     in
		       lftermToFormat0 (M,
				      fn (fmt, prec) =>
				      k (fmtprefix2 (bracketPrec, (lfdecFmt, (fmt, prec))), bracketPrec))
		     end
      | lftermToFormat0 (D.LFApp (r, M1, M2), k) =
		   lftermToFormat0 (M1, 
			fn (fmt1, prec1) => lftermToFormat0 (M2, 
			fn (fmt2, prec2) => k (fmtinfix Fmt.HOVbox (Left, appPrec, ((fmt1, prec1),
						NONE, (fmt2, prec2))),   appPrec)))
      | lftermToFormat0 (D.Of (r, M, A), k) =
		     lftermToFormat0 (M, 
		        fn (fmt1, prec1) => lftypeToFormat0 (A, 
		        fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, colonPrec, ((fmt1, prec1),
						SOME(Fmt.String(":")), (fmt2, prec2))),   colonPrec)))
      | lftermToFormat0 (D.ExplicitLFTerm f, k) = k (f, minPrec)



    fun kindToFormat0 (D.Type _, k) = k (Fmt.String("type"), maxPrec)

      | kindToFormat0 (D.PiKind (_, lfdec, A), k) = 
                     let
		       val lfdecFmt = Fmt.Hbox[Fmt.String("{"), lfdecToFormat lfdec, Fmt.String("}")]
		     in
		       kindToFormat0 (A,
				      fn (fmt, prec) =>
				      k (fmtprefix2 (maxPrec, (lfdecFmt, (fmt, prec))), bracePrec))
		     end
    *)

    (* We saved paren information when parsing.. so we just use that *)
    fun lfdecToFormat (D.LFDec (_,SOME s,A)) = Fmt.HVbox[Fmt.String(s), Fmt.Break, Fmt.String(":"), Fmt.Break, lftypeToFormat0 (A)]
      | lfdecToFormat (D.LFDec (_,NONE,A)) = Fmt.HVbox[Fmt.String("_"), Fmt.Break, Fmt.String(":"), Fmt.Break, lftypeToFormat0 (A)]
     
    and lftypeToFormat0 (D.TypeID (_, s)) = Fmt.String s
      | lftypeToFormat0 (D.TypeApp (_, A, M)) = 
                    Fmt.HOVbox [lftypeToFormat0 A, Fmt.Break, lftermToFormat0 M]

      | lftypeToFormat0 (D.PiType (_, lfdec, A)) =
                     let
		       val lfdecFmt = Fmt.HVbox[Fmt.String("{"), lfdecToFormat lfdec, Fmt.String("}")]
		     in
		       Fmt.Hbox [lfdecFmt, Fmt.Break, lftypeToFormat0 A]
		     end

      | lftypeToFormat0 (D.RtArrow (r, A1, A2)) =
		     Fmt.HVbox [lftypeToFormat0 A2, Fmt.Break, Fmt.String("->"), Fmt.Break, lftypeToFormat0 A2]

      | lftypeToFormat0 (D.LtArrow (r, A1, A2)) =
		     Fmt.HVbox [lftypeToFormat0 A2, Fmt.Break, Fmt.String("<-"), Fmt.Break, lftypeToFormat0 A2]

      | lftypeToFormat0 (D.OmitType _) = Fmt.String "_"
      | lftypeToFormat0 (D.ParenType (r, A)) = Fmt.Hbox [Fmt.String "(", lftypeToFormat0 A, Fmt.String ")"]
      | lftypeToFormat0 (D.ExplicitLFType f) = f

    and lftermToFormat0 (D.ObjectID (_, false, s)) = Fmt.String s
      | lftermToFormat0 (D.ObjectID (_, true, s)) = Fmt.String (s^"#")
      | lftermToFormat0 (D.Fn (_, lfdec, M)) = 
                     let
		       val lfdecFmt = Fmt.HVbox[Fmt.String("["), lfdecToFormat lfdec, Fmt.String("]")]
		     in
		       Fmt.Hbox [lfdecFmt, Fmt.Break, lftermToFormat0 M]
		     end
      | lftermToFormat0 (D.LFApp (r, M1, M2)) =
                    Fmt.HOVbox [lftermToFormat0 M1, Fmt.Break, lftermToFormat0 M2]

      | lftermToFormat0 (D.Of (r, M, A)) =
                    Fmt.HOVbox [lftermToFormat0 M, Fmt.Break, Fmt.String(":"), Fmt.Break, lftypeToFormat0 A]

      | lftermToFormat0 (D.OmitTerm _) = Fmt.String "_"
      | lftermToFormat0 (D.ParenTerm (r, M)) = Fmt.Hbox [Fmt.String "(", lftermToFormat0 M, Fmt.String ")"]

      | lftermToFormat0 (D.ExplicitLFTerm f) = f



    fun kindToFormat0 (D.Type _) = Fmt.String("type")

      | kindToFormat0 (D.PiKind (_, lfdec, K)) = 
                     let
		       val lfdecFmt = Fmt.Hbox[Fmt.String("{"), lfdecToFormat lfdec, Fmt.String("}")]
		     in
		       Fmt.Hbox [lfdecFmt, Fmt.Break, kindToFormat0 K]
		     end



    (* Convert into Twelf Lexer format... *)

   (* ABP:  July, 07:  No longer check the case of variables.
    *                  We want pattern-variables to be any case
    *                  as well as the declaration of constants
    fun isCap s =
      let
	val c = case (String.explode(s)) 
	        of (c::xs) => c
		 | _ => raise Domain
      in
	Char.isUpper(c) orelse c = #"@" (* generated by lifted app *)
      end
      
    fun getCase s = 
	if (isCap s) then L.ID (L.Upper, s) else L.ID (L.Lower, s)
    *)

    fun pretendCapital s = L.ID(L.Upper, s)
    fun pretendLower s = L.ID(L.Lower, s)


    fun lfdecToTokens0 (D.LFDec (r,SOME s,A)) = 
        let
	  val Paths.Reg(a,b) = r
	  val stringR = Paths.Reg(a, a + String.size(s))
	in
	  (*
	  case A of (D.OmitType _) => [(getCase(s), stringR)]
	          | _ => [(getCase(s), stringR)] @ [(L.COLON,r)] @ lftypeToTokens0(A)
	    *)
	  case A of (D.OmitType _) => [(pretendLower s, stringR)]
	          | _ => [(pretendLower s, stringR)] @ [(L.COLON,r)] @ lftypeToTokens0(A)

	end
      | lfdecToTokens0 (D.LFDec (r,NONE,A)) = 
	   (case A of (D.OmitType _) => [(L.UNDERSCORE, r)]
	          | _ => [(L.UNDERSCORE, r)] @ [(L.COLON,r)] @ lftypeToTokens0(A))


     
    (* As we save Parenthesis information when parsing lf stuff, we don't need to do much here *)
    and lftypeToTokens0 (D.TypeID (r, s)) = (* [(getCase s, r)] *)
                                            [(pretendCapital s, r)]
      | lftypeToTokens0 (D.TypeApp (r, A, M)) = (lftypeToTokens0 A) @ (lftermToTokens0 M)
      | lftypeToTokens0 (D.PiType (r, lfdec, A)) =
                     let
		       val lfdecTok = [(L.LBRACE,r)] @ (lfdecToTokens0 lfdec) @ [(L.RBRACE, r)]
		     in
		       lfdecTok @ (lftypeToTokens0 A)
		     end

      | lftypeToTokens0 (D.RtArrow (r, A1, A2)) =
		     (lftypeToTokens0 A1) @ ((L.ARROW,r) :: (lftypeToTokens0 A2))

      | lftypeToTokens0 (D.LtArrow (r, A1, A2)) =
		     (lftypeToTokens0 A1) @ ((L.BACKARROW,r) :: (lftypeToTokens0 A2))

      | lftypeToTokens0 (D.OmitType r) = [(L.UNDERSCORE, r)]
      | lftypeToTokens0 (D.ParenType (r,A)) = ((L.LPAREN,r) :: (lftypeToTokens0 A)) @ [(L.RPAREN, r)]
      | lftypeToTokens0 (D.ExplicitLFType f) = raise Domain (* should not occur here *)

    and lftermToTokens0 (D.ObjectID (r, false, s)) = (* [(getCase s, r)] *)
                                                     [(pretendCapital s, r)]
      | lftermToTokens0 (D.ObjectID (r, true, s)) = [(L.ID(L.UpperParam, s), r)]
      | lftermToTokens0 (D.Fn (r, lfdec, M)) = 
                     let
		       val lfdecTok = [(L.LBRACKET,r)] @ (lfdecToTokens0 lfdec) @ [(L.RBRACKET, r)]
		     in
		       lfdecTok @ (lftermToTokens0 M)
		     end
      | lftermToTokens0 (D.LFApp (r, M1, M2)) =
		   (lftermToTokens0 M1) @ (lftermToTokens0 M2)

      | lftermToTokens0 (D.Of (r, M, A)) =
		     (lftermToTokens0 M) @ ((L.COLON, r) :: (lftypeToTokens0 A))
      | lftermToTokens0 (D.OmitTerm r) = [(L.UNDERSCORE, r)]
      | lftermToTokens0 (D.ParenTerm (r,M)) = ((L.LPAREN,r) :: (lftermToTokens0 M)) @ [(L.RPAREN, r)]
      | lftermToTokens0 (D.ExplicitLFTerm f) = raise Domain (* should not happen here *)


    fun kindToTokens0 (D.Type r) = [(L.TYPE, r)]

      | kindToTokens0 (D.PiKind (r, lfdec, K)) = 
                     let
		       val lfdecTok = [(L.LBRACE,r)] @ (lfdecToTokens0 lfdec) @ [(L.RBRACE, r)]
		     in
		       lfdecTok @ (kindToTokens0 K)
		     end


    fun lftermToTokens(M) = (lftermToTokens0 M) @ [(L.EOF, D.getRegLFTerm M)]
    fun lftypeToTokens(A) = (lftypeToTokens0 A) @ [(L.EOF, D.getRegLFType A)]
    fun kindToTokens(K) = (kindToTokens0 K) @ [(L.EOF, D.getRegKind K)]
    fun lfdecToTokens(D as D.LFDec (r, _, _)) = lfdecToTokens0(D) @ [(L.EOF, r)]

     (* End of Twelf Lexer Conversion *)
    

      (* Takes a list [A,B,C] and turns it into [A, Break, B, Break, C] *)
    fun addBreaks [] = []
      | addBreaks [F] = [F]
      | addBreaks (F::fs) = F :: Fmt.Break :: addBreaks(fs)


    fun seqListToFmt (nil, isDetailed) = raise Domain (* cannot have empty sequence *)
      | seqListToFmt ([(_,E)], isDetailed) = [ExpToFormat0 (E, baseK, isDetailed)]
      | seqListToFmt (((_,E)::ss), isDetailed) = 
                   let
		     val fmtHd = Fmt.Hbox[ExpToFormat0(E, baseK, isDetailed), Fmt.Break, Fmt.String(";")]
		     val fmtRest = seqListToFmt (ss, isDetailed)
		   in
		     fmtHd :: Fmt.Break :: fmtRest
		   end

    and isParamToString (D.Existential) = ""
      | isParamToString (D.Param) = "#"
      | isParamToString (D.OmittedParam) = ""

    and NormalDecToFormat (D.NormalDec (_, SOME s, D.Meta(_, D.OmittedParam, D.OmittedFormula _))) = Fmt.String(s)
      | NormalDecToFormat (D.NormalDec (_, SOME s, D.LF(_, D.OmittedParam, D.OmitType _))) = Fmt.String("<" ^ s ^">")
      | NormalDecToFormat (D.NormalDec (_, SOME s, D.Meta(_, isP, F))) = Fmt.HVbox[Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Break, FormulaToFormat0 (F, baseK), Fmt.String(isParamToString isP)]
      | NormalDecToFormat (D.NormalDec (_, SOME s, D.LF(_, isP, A))) = Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Break, lftypeToFormat0 (A), Fmt.String((isParamToString isP) ^ ">")]
      | NormalDecToFormat (D.NormalDec (r, NONE, T)) = NormalDecToFormat (D.NormalDec(r, SOME ("???"), T))

    and NewDecToFormat (D.NewDecLF (_, SOME s, D.OmitType _)) = Fmt.String("<" ^ s ^ ">")
      | NewDecToFormat (D.NewDecLF (_, SOME s, A)) = Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Break, lftypeToFormat0 (A), Fmt.String((isParamToString D.Param) ^ ">")]
      | NewDecToFormat (D.NewDecMeta (_, SOME s, D.OmittedFormula _)) = Fmt.String(s)
      | NewDecToFormat (D.NewDecMeta (_, SOME s, F)) = Fmt.HVbox[Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Break, FormulaToFormat0 (F, baseK), Fmt.String(isParamToString D.Param)]
      | NewDecToFormat (D.NewDecLF (r, NONE, A)) = NewDecToFormat (D.NewDecLF (r, SOME "???", A))
      | NewDecToFormat (D.NewDecMeta (r, NONE, F)) = NewDecToFormat (D.NewDecMeta (r, SOME "???", F))



    and TypesToFormat0 (D.LF (_, isP, A), k) = k (Fmt.HVbox[Fmt.String("<"), lftypeToFormat0 (A), Fmt.String(isParamToString isP), Fmt.String(">")], maxPrec)
      | TypesToFormat0 (D.Meta (_, isP, F), k) = Fmt.Hbox[FormulaToFormat0(F, k),Fmt.String(isParamToString isP)]

    and FormulaToFormat0 (D.Top _, k) = k (Fmt.String("unit"), maxPrec)

      | FormulaToFormat0 (D.All (_, D.Visible, D.NormalDec (_, sO, D.LF(_, isP, A)), F), k) = 
	    let	      
	      val dec = (case sO
		         of (SOME s) =>  Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Space, lftypeToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">")]
			  | NONE => Fmt.HVbox[Fmt.String("<"), lftypeToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">")]
			 )
	    in
	      FormulaToFormat0 (F,
			       fn (fmt2, prec2) =>
				        k (fmtinfix Fmt.HVbox (Right, rtArrowPrec, ((dec, maxPrec),
						    SOME(Fmt.String("->")), (fmt2, prec2))),   rtArrowPrec))
	    end

      | FormulaToFormat0 (D.All (_, D.Implicit, D.NormalDec (_, sO, D.LF(_, isP, A)), F), k) = 
	    let	      
	      val dec = (case sO
		         of (SOME s) =>  Fmt.HVbox[Fmt.String("<<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Space, lftypeToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">>")]
			  | NONE => Fmt.HVbox[Fmt.String("<"), lftypeToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">")]
			 )
	    in
	      FormulaToFormat0 (F,
			       fn (fmt2, prec2) =>
				        k (fmtinfix Fmt.HVbox (Right, rtArrowPrec, ((dec, maxPrec),
						    SOME(Fmt.String("->")), (fmt2, prec2))),   rtArrowPrec))
	    end

      | FormulaToFormat0 (D.All (_, D.Visible, D.NormalDec (_, _, D.Meta (_, isP, F1)), F2), k) = 
	    FormulaToFormat0 (F1,
	        fn (fmt1, prec1) =>			      
			      let val (fmt1', prec1') = (case isP 
				                        of D.Param => (Fmt.Hbox[fmt1,Fmt.String("#")], prec1)
							 | _ => (fmt1, prec1)
							 )
			      in
				FormulaToFormat0 (F2,
						  fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, rtArrowPrec, ((fmt1', prec1'),
						    SOME(Fmt.String("->")), (fmt2, prec2))),   rtArrowPrec))
	                      end)

      | FormulaToFormat0 (D.All (_, D.Implicit, D.NormalDec (_, _, D.Meta (_, isP, F1)), F2), k) = raise Domain (* Cannot have meta-level implicit functions *)

      | FormulaToFormat0 (D.Exists(_, D.NormalDec(_, NONE, D.LF(_, isP, lftype)), D.Top _), k) =
               (* This is printed simply as <lftype> or <lftype#> in the output *)
	       (* Note:  if smartInj is "on" it will make sure it is not named, i.e. NONE
		* otherewise, it will name it, so it will not use this syntactic sugar.
		*)
	       (case (isP)
		 of (D.Param) => k (Fmt.Hbox[Fmt.String("<"),lftypeToFormat0 (lftype), Fmt.String("#>")], maxPrec)
		  | _ => k (Fmt.Hbox[Fmt.String("<"),lftypeToFormat0 (lftype), Fmt.String(">")], maxPrec))
	    

      | FormulaToFormat0 (D.Exists (_, D.NormalDec (_, sO, D.LF(_, isP, A)), F), k) = 
	    let	      
	      val dec = (case sO
		         of (SOME s) =>  Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Space, lftypeToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">")]
			  | NONE => Fmt.HVbox[Fmt.String("<"), lftypeToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">")]
			 )
	    in
	      FormulaToFormat0 (F,
			       fn (fmt2, prec2) =>
				        k (fmtinfix Fmt.HVbox (Right, andPrec, ((dec, maxPrec),
						    SOME(Fmt.String("*")), (fmt2, prec2))),   andPrec))
	    end


      | FormulaToFormat0 (D.Exists (_, D.NormalDec (_, _, D.Meta (_, isP, F1)), F2), k) = 
	    FormulaToFormat0 (F1,
	        fn (fmt1, prec1) =>			      
			      let val (fmt1', prec1') = (case isP 
				                        of D.Param => (Fmt.Hbox[fmt1,Fmt.String("#")], prec1)
							 | _ => (fmt1, prec1)
							 )
			      in
				FormulaToFormat0 (F2,
						  fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, andPrec, ((fmt1', prec1'),
						    SOME(Fmt.String("*")), (fmt2, prec2))),   andPrec))
	                      end)


      | FormulaToFormat0 (D.Nabla (_, D, F), k) = 
	  let
	    val decFmt = Fmt.HVbox[Fmt.String("{"), NewDecToFormat D, Fmt.String("}")]
	 in
	   FormulaToFormat0 (F, fn (fmt, prec) => k (fmtprefix2 (bracePrec, (decFmt, (fmt, prec))), bracePrec))
	 end

     (* OLD
      | FormulaToFormat0 (D.Nabla (_, D.NewDecLF (_, sO, A), F), k) =
	    let	      
	      val dec = (case sO
		         of (SOME s) =>  Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Space, lftypeToFormat0 (A, baseK), Fmt.String((isParamToString D.Param)), Fmt.String(">")]
			  | NONE => Fmt.HVbox[Fmt.String("<"), lftypeToFormat0 (A, baseK), Fmt.String((isParamToString D.Param)), Fmt.String(">")]
			 )
	    in
	      FormulaToFormat0 (F,
			       fn (fmt2, prec2) =>
				        k (fmtinfix Fmt.HVbox (Right, rtArrowPrec, ((dec, maxPrec),
						    SOME(Fmt.String("#>")), (fmt2, prec2))),   rtArrowPrec))
	    end


      | FormulaToFormat0 (D.Nabla (_, D.NewDecMeta (_, _, F1), F2), k) =
	    FormulaToFormat0 (F1,
	        fn (fmt1, prec1) =>	
			      let val fmt1' = Fmt.Hbox[fmt1, Fmt.String("#")]
			      in
				FormulaToFormat0 (F2,
						  fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, rtArrowPrec, ((fmt1', prec1),
						    SOME(Fmt.String("#>")), (fmt2, prec2))),   rtArrowPrec))
	                      end)
      *)
	    
      | FormulaToFormat0 (D.FormulaString (_,name), k) = k (Fmt.String(name), maxPrec)
      | FormulaToFormat0 (D.OmittedFormula _, k) = k (Fmt.String("_"), maxPrec)

	    
    and caseBranchToFormat0 (D.Eps (r, D, C), k, isDetailed) = 
         let
	   val decFmt = Fmt.HVbox[Fmt.String("["), NormalDecToFormat D, Fmt.String("]")]
	 in
	   caseBranchToFormat0 (C, fn (fmt, prec) => k (fmtprefix2 (bracketPrec, (decFmt, (fmt, prec))), bracketPrec), isDetailed)
	 end


      | caseBranchToFormat0 (D.NewC (_, D, C), k, isDetailed) = 
	  let
	    val decFmt = Fmt.HVbox[Fmt.String("{"), NewDecToFormat D, Fmt.String("}")]
	 in
	   caseBranchToFormat0 (C, fn (fmt, prec) => k (fmtprefix2 (bracePrec, (decFmt, (fmt, prec))), bracePrec), isDetailed)
	 end

      | caseBranchToFormat0 (D.PopC (_,s, C), k, isDetailed) = 
 	  caseBranchToFormat0 (C, 
			fn (fmt1, prec1) => k (fmtinfix Fmt.HVbox (Left, appPrec, ((fmt1, prec1),
						SOME(Fmt.String("\\")), (Fmt.String s, maxPrec))),   appPrec), isDetailed)


      | caseBranchToFormat0 (D.Match (_, E1, E2), k, true) =
		     ExpToFormat0 (E1, 
			 fn (fmt1, prec1) =>  ExpToFormat0(E2, 
			 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, eqArrowPrec, ((fmt1, prec1),
						SOME(Fmt.String("=>")), (fmt2, prec2))),   eqArrowPrec), true),
				   true)


      | caseBranchToFormat0 (D.Match (_, E1, E2), k, false) =
		     ExpToFormat0 (E1, 
			 fn (fmt1, prec1) =>  k (fmtinfix Fmt.HVbox (Right, eqArrowPrec, ((fmt1, prec1),
						SOME(Fmt.String("=>")), (Fmt.String("..."), maxPrec))),   eqArrowPrec), false)


      | caseBranchToFormat0 (D.ImplicitMatch (_, E), k, true) = ExpToFormat0 (E, k, true)

      | caseBranchToFormat0 (D.ImplicitMatch (_, E), k, false) = k (Fmt.String("..."), maxPrec)


      (*
      | caseBranchToFormat0 (D.MatchAnd (_, E1, C), k, isDetailed) =
		     ExpToFormat0 (E1, 
			 fn (fmt1, prec1) =>  caseBranchToFormat0 (C, 
			 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, andPrec, ((fmt1, prec1),
						SOME(Fmt.String("and")), (fmt2, prec2))),   andPrec),
								   isDetailed), 
				   isDetailed)
     *)

      | caseBranchToFormat0 (D.MatchAnd (_, E1, C), k, isDetailed) =
		     ExpToFormat0 (E1, 
                         (* We choose eqArrowPrec because it will eventually be an eqArrow.			 
			  * i.e.  pat1 pat2 pat3 => E2
			  * In other words, "matchAnd" is a "match" but just without printing an eqArrow.
			  *)
			 fn (fmt1, prec1) =>  caseBranchToFormat0 (C, 
			 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, eqArrowPrec, ((fmt1, prec1),
						NONE, (fmt2, prec2))),  eqArrowPrec),
								   isDetailed), 
				   isDetailed)

	 

    and caseBranchToFormat (C, isDetailed) = caseBranchToFormat0(C, baseK, isDetailed)
    and caseListToFormat ([], isDetailed) = Fmt.String("fn . ") 
      | caseListToFormat ((C:: CS), isDetailed) =
         let 
	   fun caseBranchToFormat' x = Fmt.Hbox [Fmt.String(" |"), Fmt.Break, caseBranchToFormat (x, isDetailed)]
	   val caseListFmt = map caseBranchToFormat' CS
	   val caseFmt = Fmt.Hbox [Fmt.String("fn"), Fmt.Break, caseBranchToFormat (C, isDetailed)] 
	 in   
	   Fmt.Vbox0 0 1 (addBreaks (caseFmt :: caseListFmt))
	 end


    and andsToFmt (nil, _) = Fmt.String("")
      | andsToFmt (((r, dec, E)::xs), isDetailed) = 
          let
	    val decFmt = NormalDecToFormat dec
	    val firstLineFmt = Fmt.HVbox[Fmt.String("and"), Fmt.Space, decFmt, Fmt.String(" = ")]
	    val funFmt = Fmt.Vbox[firstLineFmt, Fmt.Break, ExpToFormat0(E, baseK, isDetailed)]
	    val restFmt = andsToFmt (xs, isDetailed)
	  in
	    Fmt.Vbox0 0 1 ([funFmt , Fmt.Break, Fmt.Break, restFmt])
	  end


    and ExpToFormat0 (D.VarString (_, s), k, isDetailed) = k (Fmt.String s, maxPrec)
      | ExpToFormat0 (D.VarInt (_, i), k, isDetailed) = k (Fmt.String ("%#" ^ (Int.toString i) ^ "%"), maxPrec)
      | ExpToFormat0 (D.OmittedPat _, k, isDetailed) = k (Fmt.String ("_"), maxPrec)
      | ExpToFormat0 (D.Quote (r, M), k, isDetailed) = k (Fmt.Hbox[Fmt.String("<"),lftermToFormat0 (M), Fmt.String(">")], maxPrec)
      | ExpToFormat0 (D.Unit _, k, isDetailed) = k (Fmt.String "()", maxPrec)
      | ExpToFormat0 (D.Lam (r, cList), k, true) = k (caseListToFormat (cList, true), minPrec) 
      | ExpToFormat0 (D.Lam (r, cList), k, false) = k (Fmt.String("fn ...") , minPrec)

      | ExpToFormat0 (D.New (_, D, E), k, isDetailed) = 
	  let
	    val decFmt = Fmt.HVbox[Fmt.String("{"), NewDecToFormat D, Fmt.String("}")]
	 in
	   ExpToFormat0 (E, fn (fmt, prec) => k (fmtprefix2 (bracePrec, (decFmt, (fmt, prec))), bracePrec), isDetailed)
	 end

      | ExpToFormat0 (D.App (r, E1, E2), k, isDetailed) =
		   ExpToFormat0 (E1, 
			fn (fmt1, prec1) => ExpToFormat0 (E2, 
			fn (fmt2, prec2) => k (fmtinfix Fmt.HOVbox (Left, appPrec, ((fmt1, prec1),
						NONE, (fmt2, prec2))),   appPrec), isDetailed), isDetailed)
      
      | ExpToFormat0 (D.Pair (_, E1, E2), k, isDetailed) = 
	    ExpToFormat0 (E1,
	        fn (fmt1, prec1) => ExpToFormat0 (E2,
		fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, andPrec, ((fmt1, prec1),
						SOME(Fmt.String(",")), (fmt2, prec2))),  andPrec), isDetailed), isDetailed)

      (* Changed Syntax 							
      | ExpToFormat0 (D.Pop (_,s, E), k, isDetailed) = 
	  ExpToFormat0 (E,
			     fn (fmt, prec) =>
			       k (fmtprefix (popPrec, (Fmt.String("pop " ^ s), (fmt, prec))), popPrec), isDetailed)
      *)
      | ExpToFormat0 (D.Pop (_,s, E), k, isDetailed) = 
 	  ExpToFormat0 (E, 
			fn (fmt1, prec1) => k (fmtinfix Fmt.HVbox (Left, appPrec, ((fmt1, prec1),
						SOME(Fmt.String("\\")), (Fmt.String s, maxPrec))),   appPrec), isDetailed)


      (* Syntactic Sugar *)
      | ExpToFormat0 (D.TypeAscribe (_, E, T), k, isDetailed) =
          ExpToFormat0 (E, 
		 fn (fmt1, prec1) => TypesToFormat0 (T, 
		 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, colonPrec, ((fmt1, prec1),
						 SOME(Fmt.String(":")), (fmt2, prec2))),   colonPrec)), isDetailed)

     (* Removed due to dependencies								 
      | ExpToFormat0 ((D.Fst (_,E)), k, isDetailed) = 
	  ExpToFormat0 (E,
			     fn (fmt, prec) =>
			       k (fmtprefix (fstsndPrec, (Fmt.String("fst"), (fmt, prec))), fstsndPrec), isDetailed)
      | ExpToFormat0 ((D.Snd (_,E)), k, isDetailed) = 
	  ExpToFormat0 (E,
			     fn (fmt, prec) =>
			       k (fmtprefix (fstsndPrec, (Fmt.String("snd"), (fmt, prec))), fstsndPrec), isDetailed)
      *)
	  
      | ExpToFormat0 (D.Sequence (seqList), k, isDetailed) =
	  let
	    val fmt = Fmt.Hbox [Fmt.String("("),Fmt.Break,
				Fmt.HOVbox(seqListToFmt (seqList, isDetailed)),
				Fmt.Break, Fmt.String(")")]
	  in
	    k (fmt, maxPrec)
	  end

      | ExpToFormat0 (D.LiftedApp (r, E1, E2), k, isDetailed) =
 		   ExpToFormat0 (E1, 
			fn (fmt1, prec1) => ExpToFormat0 (E2, 
			fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Left, appPrec, ((fmt1, prec1),
						SOME(Fmt.String("@")), (fmt2, prec2))),   appPrec), isDetailed), isDetailed)

     			
      (* OLD					 
      | ExpToFormat0 (D.LetVar (r, D, E1, E2), k, isDetailed) = 
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("let val "), NormalDecToFormat D, Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed)]
		     val sndLine = LetFormat (E2, isDetailed)
		   in
		     k (Fmt.Vbox0 0 1 ([fstLine, Fmt.Break, sndLine, Fmt.Break, Fmt.String("end")]), maxPrec)
		   end
      *)
      | ExpToFormat0 (D.LetVar (r, Pat, E1, E2), k, isDetailed) = 
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("let val "), ExpToFormat0(Pat, baseK, isDetailed), Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed)]
		     val sndLine = LetFormat (E2, isDetailed)
		   in
		     k (Fmt.Vbox0 0 1 ([fstLine, Fmt.Break, sndLine, Fmt.Break, Fmt.String("end")]), maxPrec)
		   end




      | ExpToFormat0 (D.LetFun (_, xs, Eresult), k, isDetailed) =
		   let
		     val funFmt' = funFormat (xs, isDetailed)
		     val top = Fmt.Hbox[Fmt.String("let"),Fmt.Break, funFmt']
		     val sndLine = LetFormat (Eresult, isDetailed)
		   in
		     k (Fmt.Vbox0 0 1 ([top, Fmt.Break, sndLine, Fmt.Break, Fmt.String("end")]), maxPrec)
		   end

	    
      | ExpToFormat0 (D.Fix (_, nil), k, isDetailed) = raise Domain (* empty list of function s*)
      | ExpToFormat0 (D.Fix (_, xs), k, isDetailed) = k (funFormat (xs, isDetailed), minPrec)

      | ExpToFormat0 (D.ExtendFun (r, E, cList), k, isDetailed) = 
		   let
                       (* same as caselistToFormat but does not print the "fn" *)
                       fun caseListToFormat2 ([], isDetailed) = Fmt.String(" . ") 
			 | caseListToFormat2 ((C:: CS), isDetailed) =
			         let 
				   fun caseBranchToFormat' x = Fmt.Hbox [Fmt.String(" |"), Fmt.Break, caseBranchToFormat (x, isDetailed)]
				   val caseListFmt = map caseBranchToFormat' CS
				   val caseFmt = Fmt.Hbox [Fmt.String("  "), Fmt.Break, caseBranchToFormat (C, isDetailed)] 
				 in   
				   Fmt.Vbox0 0 1 (addBreaks (caseFmt :: caseListFmt))
				 end
		   in
		     ExpToFormat0 (E, 
				   fn (fmt1, prec1) => k (fmtinfix Fmt.HOVbox (Right, withPrec, ((fmt1, prec1),
									SOME(Fmt.String("with")), (caseListToFormat2 (cList, true), minPrec))),
						       withPrec),
				   isDetailed)
		   end



    (* LetFormat is used to handle embedded lets.
     * Instead of printing let val s = e1 in let val s2 = e2 in e3 end
     * We print it as let val s = e1 val s2 = e2 in e3 end
     *)
    and LetFormat (D.LetVar(r, Pat, E1, E2), isDetailed) =
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("    val "), ExpToFormat0(Pat, baseK, isDetailed), Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed)]

		     val sndLine = LetFormat (E2, isDetailed)
		   in
		     Fmt.Vbox0 0 1 [fstLine, Fmt.Break, sndLine]
		   end
    (* OLD
    and LetFormat (D.LetVar(r, D, E1, E2), isDetailed) =
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("    val "), NormalDecToFormat D, Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed)]

		     val sndLine = LetFormat (E2, isDetailed)
		   in
		     Fmt.Vbox0 0 1 [fstLine, Fmt.Break, sndLine]
		   end
     *)

      | LetFormat (D.LetFun (_, xs, Eresult), isDetailed) =
		   let
		     val funFmt' = funFormat (xs, isDetailed)
		     val fstLine = Fmt.Hbox[Fmt.String("   "),Fmt.Break, funFmt']
		     val sndLine = LetFormat (Eresult, isDetailed)
		   in
		     Fmt.Vbox0 0 1 [fstLine, Fmt.Break, sndLine]
		   end


      | LetFormat (E, isDetailed) = Fmt.Vbox[Fmt.String("in"), Fmt.Break,  ExpToFormat0(E, baseK, isDetailed)]

    and funFormat ([], _) = raise Domain (* empty list of functions *)
      | funFormat (((r,dec,E)::xs), isDetailed) =
               let
		 val decFmt = NormalDecToFormat dec
		 val firstLineFmt = Fmt.HVbox[Fmt.String("fun"), Fmt.Space, decFmt, Fmt.String(" = ")]
		 val funFmt = Fmt.Vbox[firstLineFmt, Fmt.Break, ExpToFormat0(E, baseK, isDetailed)]
		 val restFmt = andsToFmt (xs, isDetailed)
	       in
		 Fmt.Vbox0 0 1 ([funFmt, Fmt.Break, Fmt.Break, restFmt])
	       end


    fun precOptStr NONE = ""
      | precOptStr (SOME (D.INFIXL (_,n))) = " %infix left " ^ Int.toString(n)
      | precOptStr (SOME (D.INFIXR (_,n))) = " %infix right " ^ Int.toString(n)
      | precOptStr (SOME (D.INFIXN (_,n))) = " %infix " ^ Int.toString(n)
      | precOptStr (SOME (D.POSTFIX (_,n))) = " %postfix " ^ Int.toString(n) 
      | precOptStr (SOME (D.PREFIX (_,n))) = " %prefix " ^ Int.toString(n) 

    fun nameOptStr NONE = ""
      | nameOptStr (SOME (D.OneName (_, s))) = " %name " ^ s
      | nameOptStr (SOME (D.TwoNames (_, s1, s2))) = " %name " ^ s1 ^ " " ^ s2

    fun varListToFormat nil = [Fmt.String(".")]
      | varListToFormat [lftype] = [Fmt.String "<", lftypeToFormat0 lftype, Fmt.String ">"]
      | varListToFormat (lftype :: lfs) = 
                   let
		     val fmtHd = Fmt.Hbox[Fmt.String "<", lftypeToFormat0 lftype, Fmt.String ">", Fmt.Break, Fmt.String(",")]
		     val fmtRest = varListToFormat lfs
		   in
		     fmtHd :: Fmt.Break :: fmtRest
		   end

    fun worldToFormat (D.Anything) = Fmt.String("*")
      | worldToFormat (D.Variables [lftype]) = lftypeToFormat0 lftype
      | worldToFormat (D.Variables lfs) = Fmt.HOVbox(varListToFormat lfs)
      

    fun topDecFmt (D.LFTypeConstant (r,s, kind, nameopt, precopt)) = Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), Fmt.String(s), Fmt.Space, 
									       Fmt.String(":"), Fmt.Break,
									       kindToFormat0(kind), Fmt.String(">"),Fmt.String(nameOptStr(nameopt)), 
											Fmt.String(precOptStr(precopt))], 
								     Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.LFObjectConstant (r, lfdec, precopt)) = 
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), lfdecToFormat(lfdec), Fmt.String(">"),
							Fmt.String(precOptStr(precopt))], Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.LFDef (r, lfdec, lfterm, false, precopt)) = 
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), lfdecToFormat(lfdec), Fmt.String(" = "), 
							lftermToFormat0(lfterm), Fmt.String(">"), Fmt.String(precOptStr(precopt))], Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.LFDef (r, lfdec, lfterm, true, precopt)) = 
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), lfdecToFormat(lfdec), Fmt.String(" = "), 
							lftermToFormat0(lfterm), Fmt.String(" %abbrev "), Fmt.String(">"), Fmt.String(precOptStr(precopt))], 
					      Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.TypeDef  (r, name, F)) =
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("type "), Fmt.String(name), Fmt.String(" = "), 
							FormulaToFormat0 (F, baseK)], 
					      Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.WorldDec W) = Fmt.Vbox[Fmt.HVbox[Fmt.String("params = "), 
							worldToFormat W], Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.MetaFix xs) =  funFormat (xs, true)
      | topDecFmt (D.MetaVal (_, NONE, E)) = Fmt.Vbox[Fmt.HVbox[Fmt.String("val it = "),Fmt.Break, ExpToFormat0(E, baseK, true)], 
						      Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.MetaVal (_, SOME s, E)) = Fmt.Vbox[Fmt.HVbox[Fmt.String("val " ^ s ^" = "),Fmt.Break, ExpToFormat0(E, baseK, true)], 
							Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.Use s) = Fmt.Vbox[Fmt.String("use"), Fmt.Space, Fmt.String(s), Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.LFUse s) = Fmt.Vbox[Fmt.String("sig use"), Fmt.Space, Fmt.String(s), Fmt.String(";"), Fmt.Break, Fmt.Break]

    fun topDecStr F = Fmt.makestring_fmt (topDecFmt F)

    fun expToStr (E, isDetailed) = Fmt.makestring_fmt (ExpToFormat0( E, baseK, isDetailed))

    fun delphinToStr [] = ""
      | delphinToStr (x::xs) = topDecStr(x) ^ "\n\n" ^ delphinToStr(xs)

  end