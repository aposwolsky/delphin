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
    fun lfdecToFormat (D.LFDec (_,SOME s,A)) = Fmt.HVbox[Fmt.String(s), Fmt.Break, Fmt.String(":"), Fmt.Break, lfexpToFormat0 (A)]
      | lfdecToFormat (D.LFDec (_,NONE,A)) = Fmt.HVbox[Fmt.String("_"), Fmt.Break, Fmt.String(":"), Fmt.Break, lfexpToFormat0 (A)]
     
    and lfexpToFormat0 (D.LFid (r, false, s)) = Fmt.String s
      | lfexpToFormat0 (D.LFid (r, true, s)) = Fmt.String (s^"#")
      | lfexpToFormat0 (D.LFapp (r, m1, m2)) = Fmt.HOVbox [lfexpToFormat0 m1, Fmt.Break, lfexpToFormat0 m2]
      | lfexpToFormat0 (D.LFpi (r, lfdec, A)) = 
                     let
		       val lfdecFmt = Fmt.HVbox[Fmt.String("{"), lfdecToFormat lfdec, Fmt.String("}")]
		     in
		       Fmt.Hbox [lfdecFmt, Fmt.Break, lfexpToFormat0 A]
		     end

      | lfexpToFormat0 (D.LFrtArrow (r, A1, A2)) = Fmt.HVbox [lfexpToFormat0 A2, Fmt.Break, Fmt.String("->"), Fmt.Break, lfexpToFormat0 A2]
      | lfexpToFormat0 (D.LFltArrow (r, A1, A2)) = Fmt.HVbox [lfexpToFormat0 A2, Fmt.Break, Fmt.String("<-"), Fmt.Break, lfexpToFormat0 A2]
      | lfexpToFormat0 (D.LFomit r) = Fmt.String "_"
      | lfexpToFormat0 (D.LFparen (r, m)) = Fmt.Hbox [Fmt.String "(", lfexpToFormat0 m, Fmt.String ")"]
      | lfexpToFormat0 (D.LFfn (r, lfdec, M)) = 
                     let
		       val lfdecFmt = Fmt.HVbox[Fmt.String("["), lfdecToFormat lfdec, Fmt.String("]")]
		     in
		       Fmt.Hbox [lfdecFmt, Fmt.Break, lfexpToFormat0 M]
		     end

      | lfexpToFormat0 (D.LFof (r, M, A)) = Fmt.HOVbox [lfexpToFormat0 M, Fmt.Break, Fmt.String(":"), Fmt.Break, lfexpToFormat0 A]
      | lfexpToFormat0 (D.ExplicitLF  f) = f



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
	  case A of (D.LFomit _) => [(pretendLower s, stringR)]
	          | _ => [(pretendLower s, stringR)] @ [(L.COLON,r)] @ lfexpToTokens0(A)

	end
      | lfdecToTokens0 (D.LFDec (r,NONE,A)) = 
	   (case A of (D.LFomit _) => [(L.UNDERSCORE, r)]
	          | _ => [(L.UNDERSCORE, r)] @ [(L.COLON,r)] @ lfexpToTokens0(A))

    (* As we save Parenthesis information when parsing lf stuff, we don't need to do much here *)
    and lfexpToTokens0 (D.LFid (r, false, s)) = (* [(getCase s, r)] *)
                                                 [(pretendCapital s, r)]
      | lfexpToTokens0 (D.LFid (r, true, s)) = [(L.ID(L.UpperParam, s), r)]
      | lfexpToTokens0 (D.LFapp (r, m1, m2)) = (lfexpToTokens0 m1) @ (lfexpToTokens0 m2)
      | lfexpToTokens0 (D.LFpi (r, lfdec, A)) = 
                     let
		       val lfdecTok = [(L.LBRACE,r)] @ (lfdecToTokens0 lfdec) @ [(L.RBRACE, r)]
		     in
		       lfdecTok @ (lfexpToTokens0 A)
		     end

      | lfexpToTokens0 (D.LFrtArrow (r, A1, A2)) = (lfexpToTokens0 A1) @ ((L.ARROW,r) :: (lfexpToTokens0 A2))
      | lfexpToTokens0 (D.LFltArrow (r, A1, A2)) = (lfexpToTokens0 A1) @ ((L.BACKARROW,r) :: (lfexpToTokens0 A2))
      | lfexpToTokens0 (D.LFomit r) = [(L.UNDERSCORE, r)]
      | lfexpToTokens0 (D.LFparen (r, m)) = ((L.LPAREN,r) :: (lfexpToTokens0 m)) @ [(L.RPAREN, r)]
      | lfexpToTokens0 (D.LFfn (r, lfdec, M)) = 
                     let
		       val lfdecTok = [(L.LBRACKET,r)] @ (lfdecToTokens0 lfdec) @ [(L.RBRACKET, r)]
		     in
		       lfdecTok @ (lfexpToTokens0 M)
		     end

      | lfexpToTokens0 (D.LFof (r, M, A)) = (lfexpToTokens0 M) @ ((L.COLON, r) :: (lfexpToTokens0 A))
      | lfexpToTokens0 (D.ExplicitLF  f) = raise Domain (* cannot handle this... should not occur *)



    fun kindToTokens0 (D.Type r) = [(L.TYPE, r)]

      | kindToTokens0 (D.PiKind (r, lfdec, K)) = 
                     let
		       val lfdecTok = [(L.LBRACE,r)] @ (lfdecToTokens0 lfdec) @ [(L.RBRACE, r)]
		     in
		       lfdecTok @ (kindToTokens0 K)
		     end


    fun lfexpToTokens(M) = (lfexpToTokens0 M) @ [(L.EOF, D.getRegLFExp M)]
    fun kindToTokens(K) = (kindToTokens0 K) @ [(L.EOF, D.getRegKind K)]
    fun lfdecToTokens(D as D.LFDec (r, _, _)) = lfdecToTokens0(D) @ [(L.EOF, r)]

     (* End of Twelf Lexer Conversion *)
    

      (* Takes a list [A,B,C] and turns it into [A, Break, B, Break, C] *)
    fun addBreaks [] = []
      | addBreaks [F] = [F]
      | addBreaks (F::fs) = F :: Fmt.Break :: addBreaks(fs)


    fun seqListToFmt (nil, isDetailed, printEps) = raise Domain (* cannot have empty sequence *)
      | seqListToFmt ([(_,E)], isDetailed, printEps) = [ExpToFormat0 (E, baseK, isDetailed, printEps)]
      | seqListToFmt (((_,E)::ss), isDetailed, printEps) = 
                   let
		     val fmtHd = Fmt.Hbox[ExpToFormat0(E, baseK, isDetailed, printEps), Fmt.Break, Fmt.String(";")]
		     val fmtRest = seqListToFmt (ss, isDetailed, printEps)
		   in
		     fmtHd :: Fmt.Break :: fmtRest
		   end

    and isParamToString (D.Existential) = ""
      | isParamToString (D.Param) = "#"
      | isParamToString (D.OmittedParam) = ""

    and NormalDecToFormat (D.NormalDec (_, SOME s, D.Meta(_, D.OmittedFormula _))) = Fmt.String(s)
      | NormalDecToFormat (D.NormalDec (_, SOME s, D.LF(_, D.OmittedParam, D.LFomit _))) = Fmt.String("<" ^ s ^">")
      | NormalDecToFormat (D.NormalDec (_, SOME s, D.Meta(_, F))) = Fmt.HVbox[Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Break, FormulaToFormat0 (F, baseK), Fmt.String(isParamToString (* isP *) D.Existential )]
      | NormalDecToFormat (D.NormalDec (_, SOME s, D.LF(_, isP, A))) = Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Break, lfexpToFormat0 (A), Fmt.String((isParamToString isP) ^ ">")]
      | NormalDecToFormat (D.NormalDec (r, NONE, T)) = NormalDecToFormat (D.NormalDec(r, SOME ("???"), T))

    and NewDecToFormat (D.NewDecLF (_, SOME s, D.LFomit _)) = Fmt.String("<" ^ s ^ ">")
      | NewDecToFormat (D.NewDecLF (_, SOME s, A)) = Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Break, lfexpToFormat0 (A), Fmt.String((isParamToString D.Param) ^ ">")]
      (*
	| NewDecToFormat (D.NewDecWorld ...) = ...
       *)
      | NewDecToFormat (D.NewDecLF (r, NONE, A)) = NewDecToFormat (D.NewDecLF (r, SOME "???", A))




    and TypesToFormat0 (D.LF (_, isP, A), k) = k (Fmt.HVbox[Fmt.String("<"), lfexpToFormat0 (A), Fmt.String(isParamToString isP), Fmt.String(">")], maxPrec)
      | TypesToFormat0 (D.Meta (_, F), k) = Fmt.Hbox[FormulaToFormat0(F, k),Fmt.String(isParamToString (* isP *) D.Existential)]

    and FunctionDecsToFormat0 ([], k) = raise Domain 

      | FunctionDecsToFormat0 ((D.NormalDec (_, sO, D.LF(_, isP, A)))::funDecs, k) = 
              let
		val (fmt1, prec1) =  case sO
		                     of (SOME s) => (Fmt.HVbox[Fmt.String("<"), Fmt.String(s), 
							       Fmt.Space, Fmt.String(":"), Fmt.Space, 
							       lfexpToFormat0 (A), Fmt.String((isParamToString isP)), 
							       Fmt.String(">")], maxPrec)
				      | NONE => (Fmt.HVbox[Fmt.String("<"), lfexpToFormat0 (A), 
							   Fmt.String((isParamToString isP)), Fmt.String(">")], maxPrec)
	      in
		case funDecs
		  of [] => k (fmt1, prec1)
		   | _ => FunctionDecsToFormat0 (funDecs,
						 fn (fmt2, prec2) => 
						      k (fmtinfix Fmt.HVbox (Right, andPrec, 
									     ((fmt1, prec1), SOME(Fmt.String("and")), (fmt2, prec2))), 
							 andPrec))
	      end

      (* This OLD code will distinguish implicit arguments using "<<...>>", but we changed it
       * to just omit implicit arguments unless if a flag is set to true, and then it
       * prints out all implicit information.
      
       | FunctionDecsToFormat0 ((visibility, D.NormalDec (_, sO, D.LF(_, isP, A)))::funDecs, k) = 
              let
		(* if it is implicit, we double the inject symbols.. instead of "<...>" we have "<<...>>" *)
		fun maybeDouble(s) = case visibility of
		                    D.Visible => s
				   | D.Implicit => s ^ s

		val (fmt1, prec1) =  case sO
		                     of (SOME s) => (Fmt.HVbox[Fmt.String(maybeDouble "<"), Fmt.String(s), 
							       Fmt.Space, Fmt.String(":"), Fmt.Space, 
							       lfexpToFormat0 (A), Fmt.String((isParamToString isP)), 
							       Fmt.String(maybeDouble ">")], maxPrec)
				      | NONE => (Fmt.HVbox[Fmt.String(maybeDouble "<"), lfexpToFormat0 (A), 
							   Fmt.String((isParamToString isP)), Fmt.String(maybeDouble ">")], maxPrec)
	      in
		case funDecs
		  of [] => k (fmt1, prec1)
		   | _ => FunctionDecsToFormat0 (funDecs,
						 fn (fmt2, prec2) => 
						      k (fmtinfix Fmt.HVbox (Right, andPrec, 
									     ((fmt1, prec1), SOME(Fmt.String("and")), (fmt2, prec2))), 
							 andPrec))
	      end
       *)

      | FunctionDecsToFormat0 ((D.NormalDec (_, _, D.Meta (_, F1)))::funDecs, k) = 
	      FormulaToFormat0 (F1,
				fn (fmt1, prec1) =>
				      let 
					val fmt1' = (* (case isP 
						      of D.Param => (Fmt.Hbox[fmt1,Fmt.String("#")])
						       | _ => fmt1)
						     *)
					             fmt1
				      in
					case funDecs
					  of [] => k (fmt1', prec1)
					   | _ => FunctionDecsToFormat0 (funDecs,
						   fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, andPrec, 
											    ((fmt1', prec1), SOME(Fmt.String("and")), (fmt2, prec2))), 
									andPrec))
				      end)

    
    and FormulaToFormat0 (D.Top _, k) = k (Fmt.String("unit"), maxPrec)

      | FormulaToFormat0 (D.All (_, funDecs, F), k) =

            let
	      fun getExplicit [] = []
		| getExplicit ((D.Visible, D)::ds) = D :: (getExplicit ds)
		| getExplicit ((D.Implicit, _)::ds) = getExplicit ds

	      val explicitFunDecs = getExplicit funDecs
	      val numToPrint = List.length explicitFunDecs
		
	    in
	      if (numToPrint = 0) then      
		                            (* If we change it to print out all implicit arguments,
					     * e.g. marked with << ... >>, then we need to remove this check.
					     * ALSO.. These functions that are "completely" implicit are hard to reason about
					     * in convert.fun . Perhaps they should be disallowed.
					     *)
		FormulaToFormat0 (F, k)
	      else
		FunctionDecsToFormat0 (explicitFunDecs,
	           fn (fmt1, prec1) => let
				      val prec1 = if numToPrint > 1 then minPrec else prec1 
				          (* if there is more
					   * than one dec
					   * then we need to put
					   * in paranethesis.
					   * which is done by setting
					   * prec to minPrec
					   *)
				    in
				      FormulaToFormat0 (F,
						  fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, rtArrowPrec, ((fmt1, prec1),
						    SOME(Fmt.String("->")), (fmt2, prec2))),   rtArrowPrec))
				    end)
	    end

      | FormulaToFormat0 (D.Exists(_, D.NormalDec(_, NONE, D.LF(_, isP, lftype)), D.Top _), k) =
               (* This is printed simply as <lftype> or <lftype#> in the output *)
	       (* Note:  if smartInj is "on" it will make sure it is not named, i.e. NONE
		* otherewise, it will name it, so it will not use this syntactic sugar.
		*)
	       (case (isP)
		 of (D.Param) => k (Fmt.Hbox[Fmt.String("<"),lfexpToFormat0 (lftype), Fmt.String("#>")], maxPrec)
		  | _ => k (Fmt.Hbox[Fmt.String("<"),lfexpToFormat0 (lftype), Fmt.String(">")], maxPrec))
	    

      | FormulaToFormat0 (D.Exists (_, D.NormalDec (_, sO, D.LF(_, isP, A)), F), k) = 
	    let	      
	      val dec = (case sO
		         of (SOME s) =>  Fmt.HVbox[Fmt.String("<"), Fmt.String(s), Fmt.Space, Fmt.String(":"), Fmt.Space, lfexpToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">")]
			  | NONE => Fmt.HVbox[Fmt.String("<"), lfexpToFormat0 (A), Fmt.String((isParamToString isP)), Fmt.String(">")]
			 )
	    in
	      FormulaToFormat0 (F,
			       fn (fmt2, prec2) =>
				        k (fmtinfix Fmt.HVbox (Right, andPrec, ((dec, maxPrec),
						    SOME(Fmt.String("*")), (fmt2, prec2))),   andPrec))
	    end


      | FormulaToFormat0 (D.Exists (_, D.NormalDec (_, _, D.Meta (_, F1)), F2), k) = 
	    FormulaToFormat0 (F1,
	        fn (fmt1, prec1) =>			      
			      let val (fmt1', prec1') = (* (case isP 
				                        of D.Param => (Fmt.Hbox[fmt1,Fmt.String("#")], prec1)
							 | _ => (fmt1, prec1)
							 )
							 *)
				                        (fmt1, prec1)
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


      *)
	    
      | FormulaToFormat0 (D.FormulaString (_,name), k) = k (Fmt.String(name), maxPrec)
      | FormulaToFormat0 (D.OmittedFormula _, k) = k (Fmt.String("_"), maxPrec)

    and isSugarToInfix(true) = NONE (* the syntax for this is just juxtaposition *)
      | isSugarToInfix(false) = SOME(Fmt.String "and")
	    
    and caseBranchToFormat0 (D.Eps (r, D, C), k, isDetailed, printEps) = 
           if printEps then
	         let
		   val decFmt = Fmt.HVbox[Fmt.String("["), NormalDecToFormat D, Fmt.String("]")]
		 in
		   caseBranchToFormat0 (C, fn (fmt, prec) => k (fmtprefix2 (bracketPrec, (decFmt, (fmt, prec))), bracketPrec), isDetailed, printEps)
		 end
	   else	     
	     caseBranchToFormat0 (C, k, isDetailed, printEps)


      | caseBranchToFormat0 (D.NewC (_, D, C), k, isDetailed, printEps) = 
	  let
	    val decFmt = Fmt.HVbox[Fmt.String("{"), NewDecToFormat D, Fmt.String("}")]
	  in
	    caseBranchToFormat0 (C, fn (fmt, prec) => k (fmtprefix2 (bracePrec, (decFmt, (fmt, prec))), bracePrec), isDetailed, printEps)
	 end

      | caseBranchToFormat0 (D.PopC (_,s, C), k, isDetailed, printEps) = 
 	  caseBranchToFormat0 (C, 
			fn (fmt1, prec1) => k (fmtinfix Fmt.HVbox (Left, appPrec, ((fmt1, prec1),
						SOME(Fmt.String("\\")), (Fmt.String s, maxPrec))),   appPrec), isDetailed, printEps)

     (* In the conversion from internal syntax to external syntax it is possible to have an *empty* Match statement if all are implicit,
      * so we handle this first.. 
      *)
      | caseBranchToFormat0 (D.Match (_, _, [], E), k, true, printEps) = ExpToFormat0 (E, k, true, printEps)
      | caseBranchToFormat0 (D.Match (_, _, [], E), k, false, printEps) = k (Fmt.String("..."), maxPrec) 


      | caseBranchToFormat0 (D.Match (isSugar, r, pats (* nonempty *), E2), k, true, printEps) =
		     PatsToFormat0 (isSugarToInfix isSugar, pats, 
			 fn (fmt1, prec1) =>  ExpToFormat0(E2, 
			 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, eqArrowPrec, ((fmt1, prec1),
						SOME(Fmt.String("=>")), (fmt2, prec2))),   eqArrowPrec), true, printEps),
				   true, printEps)


      | caseBranchToFormat0 (D.Match (isSugar, r, pats (* nonempty *), E2), k, false, printEps) =
		     PatsToFormat0 (isSugarToInfix isSugar, pats, 
			 fn (fmt1, prec1) =>  k (fmtinfix Fmt.HVbox (Right, eqArrowPrec, ((fmt1, prec1),
						SOME(Fmt.String("=>")), (Fmt.String("..."), maxPrec))),   eqArrowPrec), false, printEps)


     (* OLD
      | caseBranchToFormat0 (D.MatchAnd (_, E1, C), k, isDetailed, printEps) =
		     ExpToFormat0 (E1, 
                         (* We choose eqArrowPrec because it will eventually be an eqArrow.			 
			  * i.e.  pat1 pat2 pat3 => E2
			  * In other words, "matchAnd" is a "match" but just without printing an eqArrow.
			  *)
			 fn (fmt1, prec1) =>  caseBranchToFormat0 (C, 
			 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, eqArrowPrec, ((fmt1, prec1),
						NONE, (fmt2, prec2))),  eqArrowPrec),
								   isDetailed, printEps), 
				   isDetailed, printEps)
     *)

	 

    and caseBranchToFormat (C, isDetailed, printEps) = caseBranchToFormat0(C, baseK, isDetailed, printEps)
    and caseListToFormat ([], isDetailed, printEps) = Fmt.String("fn . ") 
      | caseListToFormat ((C:: CS), isDetailed, printEps) =
         let 
	   fun caseBranchToFormat' x = Fmt.Hbox [Fmt.String(" |"), Fmt.Break, caseBranchToFormat (x, isDetailed, printEps)]
	   val caseListFmt = map caseBranchToFormat' CS
	   val caseFmt = Fmt.Hbox [Fmt.String("fn"), Fmt.Break, caseBranchToFormat (C, isDetailed, printEps)] 
	 in   
	   Fmt.Vbox0 0 1 (addBreaks (caseFmt :: caseListFmt))
	 end


    and caseListToFormatWithArgs ([], args, isDetailed, printEps) = 
         let
	   val argFmt = ExpsToFormat0(args, baseK, isDetailed, printEps)
	 in
	     Fmt.Hbox [Fmt.String("case"), Fmt.Break, Fmt.String("("), argFmt, Fmt.String(")"), Fmt.Break, Fmt.String("of .")]
	 end

      | caseListToFormatWithArgs ((C:: CS), args, isDetailed, printEps) =
         let 
	   fun caseBranchToFormat' x = Fmt.Hbox [Fmt.String(" |"), Fmt.Break, caseBranchToFormat (x, isDetailed, printEps)]
	   val caseListFmt = map caseBranchToFormat' CS
	   val caseFmt = Fmt.Hbox [Fmt.String("of"), Fmt.Break, caseBranchToFormat (C, isDetailed, printEps)] 
	   val argFmt = ExpsToFormat0(args, baseK, isDetailed, printEps)
	   val argFmt = Fmt.Hbox [Fmt.String("case"), Fmt.Break, Fmt.String("("), argFmt, Fmt.String(")")]
	 in   
	   Fmt.Vbox0 0 1 (addBreaks (argFmt :: caseFmt :: caseListFmt))
	 end


    and andsToFmt (nil, _, _) = Fmt.String("")
      | andsToFmt (((r, dec, E)::xs), isDetailed, printEps) = 
          let
	    val decFmt = NormalDecToFormat dec
	    val firstLineFmt = Fmt.HVbox[Fmt.String("and"), Fmt.Space, decFmt, Fmt.String(" = ")]
	    val funFmt = Fmt.Vbox[firstLineFmt, Fmt.Break, ExpToFormat0(E, baseK, isDetailed, printEps)]
	    val restFmt = andsToFmt (xs, isDetailed, printEps)
	  in
	    Fmt.Vbox0 0 1 ([funFmt , Fmt.Break, Fmt.Break, restFmt])
	  end


    and ExpsToFormat0 ([], k, isDetailed, printEps) = raise Domain (* no empty lists *)
      | ExpsToFormat0 ([E], k, isDetailed, printEps) = ExpToFormat0(E, k, isDetailed, printEps)
      | ExpsToFormat0 (E::Es, k, isDetailed, printEps) = 
               ExpToFormat0(E,
	            fn (fmt1, prec1) => ExpsToFormat0 (Es,
		    fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, andPrec, 
							       ((fmt1, prec1), SOME(Fmt.String("and")), (fmt2, prec2))), 
					   andPrec), isDetailed, printEps), isDetailed, printEps)

    and PatsToFormat0 (infixFmt, [], k, isDetailed, printEps) = raise Domain (* no empty lists *)
      | PatsToFormat0 (infixFmt, [E], k, isDetailed, printEps) = PatternExpToFormat0(E, k, isDetailed, printEps)
      | PatsToFormat0 (infixFmt, E::Es, k, isDetailed, printEps) = 
              (* We choose eqArrowPrec because it will eventually be an eqArrow.			 
	       * i.e.  pat1 pat2 pat3 => E2
	       * In other words, "matchAnd" is a "match" but just without printing an eqArrow.
	       *)
               PatternExpToFormat0(E,
	            fn (fmt1, prec1) => PatsToFormat0 (infixFmt, Es,
		    fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, eqArrowPrec, 
							       ((fmt1, prec1), infixFmt, (fmt2, prec2))), 
					   eqArrowPrec), isDetailed, printEps), isDetailed, printEps)

    and PatternExpToFormat0(P, k, isDetailed, printEps) =
         let
	   fun convertPat (D.PatternString(r, s)) = D.VarString(r, s)
	     | convertPat (D.PatternOmitted r) = D.VarString(r, "_")
	     | convertPat (D.PatternQuote (r, A)) = D.Quote(r, A)
	     | convertPat (D.PatternUnit r) = D.Unit r
	     | convertPat (D.PatternPair (r, E1, E2)) = D.Pair(r, convertPat E1, convertPat E2)
	     | convertPat (D.PatternNew (r, D, E)) = D.New(r, D, convertPat E)
	     | convertPat (D.PatternPop (r, s, E)) = D.Pop(r, s, convertPat E)
	     | convertPat (D.PatternAscribe (r, E, T)) = D.TypeAscribe (r, convertPat E, T)
	 in
	   ExpToFormat0 (convertPat P, k, isDetailed, printEps)
	 end
											       

    and ExpToFormat0 (D.VarString (_, s), k, isDetailed, printEps) = k (Fmt.String s, maxPrec)
      (* | ExpToFormat0 (D.OmittedPat _, k, isDetailed, printEps) = k (Fmt.String ("_"), maxPrec) *)
      | ExpToFormat0 (D.Quote (r, M), k, isDetailed, printEps) = k (Fmt.Hbox[Fmt.String("<"),lfexpToFormat0 (M), Fmt.String(">")], maxPrec)
      | ExpToFormat0 (D.Unit _, k, isDetailed, printEps) = k (Fmt.String "()", maxPrec)

      | ExpToFormat0 (D.Lam (r, [C]), k, isDetailed, printEps) = 
              let
		fun checkImplicitMatch (D.Eps (_, _, C)) = checkImplicitMatch C
		  | checkImplicitMatch (D.NewC (r, D, C)) = 
		         (case (checkImplicitMatch C)
			    of (SOME E) => SOME (D.New(r, D, E))
			     | NONE => NONE)
		  | checkImplicitMatch (D.PopC (r, s, C)) =
		         (case (checkImplicitMatch C)
			    of (SOME E) => SOME (D.Pop(r, s, E))
			     | NONE => NONE)

		  | checkImplicitMatch (D.Match (isSugar, r, [], E)) = SOME E
		  | checkImplicitMatch _ = NONE

	      in
		case (checkImplicitMatch C)
		  of (SOME E) => ExpToFormat0 (E, k, isDetailed, printEps)
		   | NONE => if isDetailed
			       then k (caseListToFormat ([C], true, printEps), minPrec)
			     else k (Fmt.String("fn ..."), minPrec)
	      end

		
      | ExpToFormat0 (D.Lam (r, cList), k, true, printEps) = k (caseListToFormat (cList, true, printEps), minPrec) 
      | ExpToFormat0 (D.Lam (r, cList), k, false, printEps) = k (Fmt.String("fn ...") , minPrec)

      | ExpToFormat0 (D.New (_, D, E), k, isDetailed, printEps) = 
	  let
	    val decFmt = Fmt.HVbox[Fmt.String("{"), NewDecToFormat D, Fmt.String("}")]
	 in
	   ExpToFormat0 (E, fn (fmt, prec) => k (fmtprefix2 (bracePrec, (decFmt, (fmt, prec))), bracePrec), isDetailed, printEps)
	 end

      | ExpToFormat0 (D.App (r, D.Lam(_, Clist), E2s), k, true, printEps) =
	        (* Make this a case statement *)
	        k (caseListToFormatWithArgs (Clist, E2s, true, printEps), minPrec)

      | ExpToFormat0 (D.App (r, E1, E2s), k, isDetailed, printEps) =
		   ExpToFormat0 (E1, 
			fn (fmt1, prec1) => ExpsToFormat0 (E2s, 
			fn (fmt2, prec2) => k (fmtinfix Fmt.HOVbox (Left, appPrec, ((fmt1, prec1),
						NONE, (fmt2, prec2))),   appPrec), isDetailed, printEps), isDetailed, printEps)
      
      | ExpToFormat0 (D.Pair (_, E1, E2), k, isDetailed, printEps) = 
	    ExpToFormat0 (E1,
	        fn (fmt1, prec1) => ExpToFormat0 (E2,
		fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, andPrec, ((fmt1, prec1),
						SOME(Fmt.String(",")), (fmt2, prec2))),  andPrec), isDetailed, printEps), isDetailed, printEps)

      (* Changed Syntax 							
      | ExpToFormat0 (D.Pop (_,s, E), k, isDetailed, printEps) = 
	  ExpToFormat0 (E,
			     fn (fmt, prec) =>
			       k (fmtprefix (popPrec, (Fmt.String("pop " ^ s), (fmt, prec))), popPrec), isDetailed, printEps)
      *)
      | ExpToFormat0 (D.Pop (_,s, E), k, isDetailed, printEps) = 
 	  ExpToFormat0 (E, 
			fn (fmt1, prec1) => k (fmtinfix Fmt.HVbox (Left, appPrec, ((fmt1, prec1),
						SOME(Fmt.String("\\")), (Fmt.String s, maxPrec))),   appPrec), isDetailed, printEps)


      (* Syntactic Sugar *)
      | ExpToFormat0 (D.TypeAscribe (_, E, T), k, isDetailed, printEps) =
          ExpToFormat0 (E, 
		 fn (fmt1, prec1) => TypesToFormat0 (T, 
		 fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Right, colonPrec, ((fmt1, prec1),
						 SOME(Fmt.String(":")), (fmt2, prec2))),   colonPrec)), isDetailed, printEps)

     (* Removed due to dependencies								 
      | ExpToFormat0 ((D.Fst (_,E)), k, isDetailed, printEps) = 
	  ExpToFormat0 (E,
			     fn (fmt, prec) =>
			       k (fmtprefix (fstsndPrec, (Fmt.String("fst"), (fmt, prec))), fstsndPrec), isDetailed, printEps)
      | ExpToFormat0 ((D.Snd (_,E)), k, isDetailed, printEps) = 
	  ExpToFormat0 (E,
			     fn (fmt, prec) =>
			       k (fmtprefix (fstsndPrec, (Fmt.String("snd"), (fmt, prec))), fstsndPrec), isDetailed, printEps)
      *)
	  
      | ExpToFormat0 (D.Sequence (seqList), k, isDetailed, printEps) =
	  let
	    val fmt = Fmt.Hbox [Fmt.String("("),Fmt.Break,
				Fmt.HOVbox(seqListToFmt (seqList, isDetailed, printEps)),
				Fmt.Break, Fmt.String(")")]
	  in
	    k (fmt, maxPrec)
	  end

      | ExpToFormat0 (D.LiftedApp (r, E1, E2), k, isDetailed, printEps) =
 		   ExpToFormat0 (E1, 
			fn (fmt1, prec1) => ExpToFormat0 (E2, 
			fn (fmt2, prec2) => k (fmtinfix Fmt.HVbox (Left, appPrec, ((fmt1, prec1),
						SOME(Fmt.String("@")), (fmt2, prec2))),   appPrec), isDetailed, printEps), isDetailed, printEps)

     			
      (* OLD					 
      | ExpToFormat0 (D.LetVar (r, D, E1, E2), k, isDetailed, printEps) = 
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("let val "), NormalDecToFormat D, Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed, printEps)]
		     val sndLine = LetFormat (E2, isDetailed, printEps)
		   in
		     k (Fmt.Vbox0 0 1 ([fstLine, Fmt.Break, sndLine, Fmt.Break, Fmt.String("end")]), maxPrec)
		   end
      *)
      | ExpToFormat0 (D.LetVar (r, Pat, E1, E2), k, isDetailed, printEps) = 
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("let val "), PatternExpToFormat0(Pat, baseK, isDetailed, printEps), Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed, printEps)]
		     val sndLine = LetFormat (E2, isDetailed, printEps)
		   in
		     k (Fmt.Vbox0 0 1 ([fstLine, Fmt.Break, sndLine, Fmt.Break, Fmt.String("end")]), maxPrec)
		   end




      | ExpToFormat0 (D.LetFun (_, xs, Eresult), k, isDetailed, printEps) =
		   let
		     val funFmt' = funFormat (xs, isDetailed, printEps)
		     val top = Fmt.Hbox[Fmt.String("let"),Fmt.Break, funFmt']
		     val sndLine = LetFormat (Eresult, isDetailed, printEps)
		   in
		     k (Fmt.Vbox0 0 1 ([top, Fmt.Break, sndLine, Fmt.Break, Fmt.String("end")]), maxPrec)
		   end

	    
      | ExpToFormat0 (D.Fix (_, nil), k, isDetailed, printEps) = raise Domain (* empty list of function s*)
      | ExpToFormat0 (D.Fix (_, xs), k, isDetailed, printEps) = k (funFormat (xs, isDetailed, printEps), minPrec)

      | ExpToFormat0 (D.ExtendFun (r, E, cList), k, isDetailed, printEps) = 
		   let
                       (* same as caselistToFormat but does not print the "fn" *)
                       fun caseListToFormat2 ([], isDetailed, printEps) = Fmt.String(" . ") 
			 | caseListToFormat2 ((C:: CS), isDetailed, printEps) =
			         let 
				   fun caseBranchToFormat' x = Fmt.Hbox [Fmt.String(" |"), Fmt.Break, caseBranchToFormat (x, isDetailed, printEps)]
				   val caseListFmt = map caseBranchToFormat' CS
				   val caseFmt = Fmt.Hbox [Fmt.String("  "), Fmt.Break, caseBranchToFormat (C, isDetailed, printEps)] 
				 in   
				   Fmt.Vbox0 0 1 (addBreaks (caseFmt :: caseListFmt))
				 end
		   in
		     ExpToFormat0 (E, 
				   fn (fmt1, prec1) => k (fmtinfix Fmt.HOVbox (Right, withPrec, ((fmt1, prec1),
									SOME(Fmt.String("with")), (caseListToFormat2 (cList, true (* print details *), printEps), minPrec))),
						       withPrec),
				   isDetailed, printEps)
		   end



    (* LetFormat is used to handle embedded lets.
     * Instead of printing let val s = e1 in let val s2 = e2 in e3 end
     * We print it as let val s = e1 val s2 = e2 in e3 end
     *)
    and LetFormat (D.LetVar(r, Pat, E1, E2), isDetailed, printEps) =
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("    val "), PatternExpToFormat0(Pat, baseK, isDetailed, printEps), Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed, printEps)]

		     val sndLine = LetFormat (E2, isDetailed, printEps)
		   in
		     Fmt.Vbox0 0 1 [fstLine, Fmt.Break, sndLine]
		   end
    (* OLD
    and LetFormat (D.LetVar(r, D, E1, E2), isDetailed, printEps) =
		   let 
		     val fstLine = Fmt.HVbox[Fmt.String("    val "), NormalDecToFormat D, Fmt.Break, Fmt.String(" = "), Fmt.Break, ExpToFormat0(E1, baseK, isDetailed, printEps)]

		     val sndLine = LetFormat (E2, isDetailed, printEps)
		   in
		     Fmt.Vbox0 0 1 [fstLine, Fmt.Break, sndLine]
		   end
     *)

      | LetFormat (D.LetFun (_, xs, Eresult), isDetailed, printEps) =
		   let
		     val funFmt' = funFormat (xs, isDetailed, printEps)
		     val fstLine = Fmt.Hbox[Fmt.String("   "),Fmt.Break, funFmt']
		     val sndLine = LetFormat (Eresult, isDetailed, printEps)
		   in
		     Fmt.Vbox0 0 1 [fstLine, Fmt.Break, sndLine]
		   end


      | LetFormat (E, isDetailed, printEps) = Fmt.Vbox[Fmt.String("in"), Fmt.Break,  ExpToFormat0(E, baseK, isDetailed, printEps)]

    and funFormat ([], _, _) = raise Domain (* empty list of functions *)
      | funFormat (((r,dec,E)::xs), isDetailed, printEps) =
               let
		 val decFmt = NormalDecToFormat dec
		 val firstLineFmt = Fmt.HVbox[Fmt.String("fun"), Fmt.Space, decFmt, Fmt.String(" = ")]
		 val funFmt = Fmt.Vbox[firstLineFmt, Fmt.Break, ExpToFormat0(E, baseK, isDetailed, printEps)]
		 val restFmt = andsToFmt (xs, isDetailed, printEps)
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


    fun lfworldToFormat0 (D.WorldType lftype, printEps) = Fmt.Hbox[Fmt.String "<", lfexpToFormat0 lftype, Fmt.String ">"]
      | lfworldToFormat0 (D.WorldEps (r, D, lfworld), false (* printEps *)) = lfworldToFormat0 (lfworld, false)
      | lfworldToFormat0 (D.WorldEps (r, D, lfworld), true (* printEps *)) =
	         let
		   val decFmt = Fmt.HVbox[Fmt.String("["), NormalDecToFormat D, Fmt.String("]")]
		   val restFmt = lfworldToFormat0 (lfworld, true)
		 in
		   Fmt.Hbox [decFmt, Fmt.Break, restFmt]
		 end

    fun varListToFormat (nil, printEps) = [Fmt.String(".")]
      | varListToFormat ([lftype], printEps) = [lfworldToFormat0 (lftype, printEps)]
      | varListToFormat (lftype :: lfs, printEps) = 
                   let
		     val fmtHd = Fmt.Hbox[lfworldToFormat0 (lftype, printEps), Fmt.Break, Fmt.String(",")]
		     val fmtRest = varListToFormat (lfs, printEps)
		   in
		     fmtHd :: Fmt.Break :: fmtRest
		   end


    fun worldToFormat (D.Anything, printEps) = Fmt.String("*")
      | worldToFormat (D.Variables lfs, printEps) = Fmt.HOVbox(varListToFormat (lfs, printEps))

      

    fun topDecFmt (D.LFTypeConstant (r,s, kind, nameopt, precopt), printEps) = 
                                                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), Fmt.String(s), Fmt.Space, 
									       Fmt.String(":"), Fmt.Break,
									       kindToFormat0(kind), Fmt.String(">"),Fmt.String(nameOptStr(nameopt)), 
											Fmt.String(precOptStr(precopt))], 
								     Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.LFObjectConstant (r, lfdec, precopt), printEps) = 
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), lfdecToFormat(lfdec), Fmt.String(">"),
							Fmt.String(precOptStr(precopt))], Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.LFDef (r, lfdec, lfterm, false, precopt), printEps) = 
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), lfdecToFormat(lfdec), Fmt.String(" = "), 
							lfexpToFormat0(lfterm), Fmt.String(">"), Fmt.String(precOptStr(precopt))], Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.LFDef (r, lfdec, lfterm, true, precopt), printEps) = 
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("sig <"), lfdecToFormat(lfdec), Fmt.String(" = "), 
							lfexpToFormat0(lfterm), Fmt.String(" %abbrev "), Fmt.String(">"), Fmt.String(precOptStr(precopt))], 
					      Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.TypeDef  (r, name, F), printEps) =
                                     Fmt.Vbox[Fmt.HVbox[Fmt.String("type "), Fmt.String(name), Fmt.String(" = "), 
							FormulaToFormat0 (F, baseK)], 
					      Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.WorldDec W, printEps) = Fmt.Vbox[Fmt.HVbox[Fmt.String("params = "), 
							worldToFormat (W, printEps)], Fmt.String(";"), Fmt.Break, Fmt.Break]

      | topDecFmt (D.MetaFix xs, printEps) =  funFormat (xs, true, printEps)
      | topDecFmt (D.MetaVal (_, NONE, E), printEps) = Fmt.Vbox[Fmt.HVbox[Fmt.String("val it = "),Fmt.Break, ExpToFormat0(E, baseK, true, printEps)], 
						      Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.MetaVal (_, SOME s, E), printEps) = Fmt.Vbox[Fmt.HVbox[Fmt.String("val " ^ s ^" = "),Fmt.Break, ExpToFormat0(E, baseK, true, printEps)], 
							Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.Use s, printEps) = Fmt.Vbox[Fmt.String("use"), Fmt.Space, Fmt.String(s), Fmt.String(";"), Fmt.Break, Fmt.Break]
      | topDecFmt (D.LFUse s, printEps) = Fmt.Vbox[Fmt.String("sig use"), Fmt.Space, Fmt.String(s), Fmt.String(";"), Fmt.Break, Fmt.Break]

    fun topDecStr F = Fmt.makestring_fmt (topDecFmt F)

    fun expToStr (E, isDetailed, printEps) = Fmt.makestring_fmt (ExpToFormat0( E, baseK, isDetailed, printEps))

    fun delphinToStr [] = ""
      | delphinToStr (x::xs) = topDecStr(x) ^ "\n\n" ^ delphinToStr(xs)

  end