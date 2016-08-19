(* Nabla Elaborator (convert from external to internal syntax) *)
(* Author: Adam Poswolsky *)

structure NablaElab : NABLA_ELABORATOR =
  struct
    exception NotImplemented of string
    exception Error of string
    structure N = NablaExtSyntax
    structure N'= NablaIntSyntax (* What we are converting too *)
    structure T = NablaTypeCheck
    structure I = IntSyn
    structure L = Lexer
    structure LS = Stream
    structure U = UnifyNabla
    val filename = ref "stdIn"


    (* ************************************************************************************ *)
    (* Here we want to rename the variables under Alts so that they are all distinct.       *)
    (* Otherwise, it would expect if you use E for exp, you can't use E for (exp -> exp)    *)
    (* ************************************************************************************ *)

    fun renameVarsFixList (f, [], suffix) = []
      | renameVarsFixList (f, ((r, md, e)::xs), suffix) =
           let
	     val md' = renameVarsMetaDec(f, md, suffix)
	     val e' = renameVars(f, e, suffix)
	   in
	     (* Add a "." to suffix so variables between mutual
	        recursive functions do not accidentally match
             *)
	     (r, md', e')::(renameVarsFixList(f, xs, suffix ^ "."))
	   end

    and renameVars (f, N.MetaID(r, s), suffix) = N.MetaID(r, f s)
      | renameVars (f, N.LFinside(r, u), suffix ) = N.LFinside(r, renameVarsLF(f, u, suffix))
      | renameVars (f, N.Fail(r), suffix ) = N.Fail(r)
      | renameVars (f, N.Pop(r, e), suffix ) = N.Pop(r, renameVars(f, e, suffix))
      | renameVars (f, N.PatMatch(r, e1, e2), suffix ) = 
           let 
	     val f' = addVars(f, e1, suffix)
	   in
	     N.PatMatch(r, renameVars(f', e1, suffix), renameVars(f', e2, suffix))
	   end

      | renameVars (f, N.MetaApp(r, e1, e2), suffix) = 
	   let
	     val e1' = renameVars(f, e1, suffix ^ "L")
	     val e2' = renameVars(f, e2, suffix ^ "R")
	   in
	     N.MetaApp(r, e1', e2')
	   end

      | renameVars (f, N.MetaPair(r, e1, e2), suffix) = 
	   let
	     val e1' = renameVars(f, e1, suffix ^ "L")
	     val e2' = renameVars(f, e2, suffix ^ "R")
	   in
	     N.MetaPair(r, e1', e2')
	   end

      | renameVars (f, N.Bar(r, e1, e2), suffix) = 
	   let
	     val e1' = renameVars(f, e1, suffix ^ "L")
	     val e2' = renameVars(f, e2, suffix ^ "R")
	   in
	     N.Bar(r, e1', e2')
	   end

      | renameVars (f, N.New(r, lfd, e), suffix) = 
	   let
	     val lfd' = renameVarsLFDec(f, lfd, suffix)
	     val e' = renameVars(f, e, suffix)
	   in
	     N.New(r, lfd', e')
	   end

      | renameVars (f, N.Nabla(r, lfd, e), suffix) = 
	   let
	     val lfd' = renameVarsLFDec(f, lfd, suffix)
	     val e' = renameVars(f, e, suffix)
	   in
	     N.Nabla(r, lfd', e')
	   end

      | renameVars (f, N.Eps(r, lfd, e), suffix) = 
	   let
	     val lfd' = renameVarsLFDec(f, lfd, suffix)
	     val e' = renameVars(f, e, suffix)
	   in
	     N.Eps(r, lfd', e')
	   end

      | renameVars (f, N.EpsM(r, md, e), suffix) = 
	   let
	     val md' = renameVarsMetaDec(f, md, suffix)
	     val e' = renameVars(f, e, suffix)
	   in
	     N.EpsM(r, md', e')
	   end

      | renameVars (f, N.Fix(r, md, e), suffix) = 
	   let
	     val md' = renameVarsMetaDec(f, md, suffix)
	     val e' = renameVars(f, e, suffix)
	   in
	     N.Fix(r, md', e')
	   end

      | renameVars (f, N.MetaFirst(r, e), suffix) = N.MetaFirst(r, renameVars(f,e, suffix))
      | renameVars (f, N.MetaSecond(r, e), suffix) = N.MetaSecond(r, renameVars(f,e, suffix))
      | renameVars (f, N.Let(r, md, e1, e2), suffix) = 
	   let
	     val md' = renameVarsMetaDec(f, md, suffix)
	     val e1' = renameVars(f, e1, suffix ^ "L" )
	     val e2' = renameVars(f, e2, suffix ^ "R" )
	   in
	     N.Let(r, md', e1', e2')
	   end

      | renameVars (f, N.LetM(r, lfd, e1, e2), suffix) = 
	   let
	     val lfd' = renameVarsLFDec(f, lfd, suffix)
	     val e1' = renameVars(f, e1, suffix ^ "L" )
	     val e2' = renameVars(f, e2, suffix ^ "R" )
	   in
	     N.LetM(r, lfd', e1', e2')
	   end

      | renameVars (f, N.Case(r, e1, e2), suffix) = 
	   let
	     val e1' = renameVars(f, e1, suffix ^ "L")
	     val e2' = renameVars(f, e2, suffix ^ "R")
	   in
	     N.Case(r, e1', e2')
	   end

      | renameVars (f, N.AppInside(r, e1, e2), suffix) = 
	   let
	     val e1' = renameVars(f, e1, suffix ^ "L")
	     val e2' = renameVars(f, e2, suffix ^ "R")
	   in
	     N.AppInside(r, e1', e2')
	   end

      | renameVars (f, N.PairInside(r, e1, e2), suffix) = 
	   let
	     val e1' = renameVars(f, e1, suffix ^ "L")
	     val e2' = renameVars(f, e2, suffix ^ "R")
	   in
	     N.PairInside(r, e1', e2')
	   end
      | renameVars (f, N.Sequence l, suffix) =
	   let
	     fun f' (r, e) = (r, renameVars (f, e, suffix))
	   in
	     N.Sequence (map f' l)
	   end


    and renameVarsLFDec (f, N.LFDec (r, s, lft), suffix ) = N.LFDec (r, s, renameVarsLFType(f, lft, suffix))
    and renameVarsMetaDec (f, N.MetaDec(r, s, mt), suffix ) = N.MetaDec (r, s, renameVarsMetaType(f, mt, suffix))
    and renameVarsMetaType (f, T, suffix ) = T (* No dependent types *)
    and renameVarsLFType (f, T, suffix ) = T (* No dependent types *)


    and renameVarsLF (f, N.ObjectConstant(r,s), _) = N.ObjectConstant(r, f s)
      | renameVarsLF (f, N.Unit r, _) = N.Unit r
      | renameVarsLF (f, N.Fn (r, lfd, u), suffix) = N.Fn(r, renameVarsLFDec(f, lfd, suffix),
						   renameVarsLF(f, u, suffix))
      | renameVarsLF (f, N.App (r, u1, u2), suffix) = N.App(r, renameVarsLF(f, u1, suffix),
							    renameVarsLF(f, u2, suffix))
      | renameVarsLF (f, N.Pair (r, u1, u2), suffix) = N.Pair(r, renameVarsLF(f, u1, suffix),
							    renameVarsLF(f, u2, suffix))
      | renameVarsLF (f, N.First (r, u), suffix) = N.First(r, renameVarsLF(f, u, suffix))
      | renameVarsLF (f, N.Second (r, u), suffix) = N.Second(r, renameVarsLF(f, u, suffix))

      | renameVarsLF (f, N.Of (r, u, t), suffix) = N.Of(r, renameVarsLF(f, u, suffix),
							    renameVarsLFType(f, t, suffix))

      | renameVarsLF (f, N.Paren (r, u), suffix) = N.Paren(r, renameVarsLF(f, u, suffix))


    and isFVar(x, s) =
      let
	val c = case (String.explode(s))
	        of (c::xs) => c
		 | _ => raise Domain
      in
	(x = s) andalso (Char.isUpper(c))
      end

    (* handles left hand side of matches, returns a function *)
    and addVars (f, N.MetaID(r, s), suffix) = (fn x => if isFVar(x, s) then s ^ suffix else f x)
      | addVars (f, N.LFinside(r, u), suffix ) = addVarsLF(f, u, suffix)
      | addVars (f, N.Pop(r, e), suffix ) = addVars(f, e, suffix)

      | addVars (f, N.MetaPair(r, e1, e2), suffix) = 
	   let
	     val f1 = addVars(f, e1, suffix)
	     val f2 = addVars(f1, e2, suffix)
	   in
	     f2
	   end


      | addVars (f, _, _) = raise Error "Ill-defined pattern"

  
    and addVarsLF (f, N.ObjectConstant(r,s), suffix) = (fn x => if isFVar(x, s) then s ^ suffix else f x)
      | addVarsLF (f, N.Unit r, _) = f
      | addVarsLF (f, N.Fn (r, lfd, u), suffix) = 
	   let
	     val f1 = addVarsLFDec(f, lfd, suffix)
	     val f2 = addVarsLF(f1, u, suffix)
	   in
	     f2
	   end

      | addVarsLF (f, N.App (r, u1, u2), suffix) = 
	   let
	     val f1 = addVarsLF(f, u1, suffix)
	     val f2 = addVarsLF(f1, u2, suffix)
	   in
	     f2
	   end
      | addVarsLF (f, N.Pair (r, u1, u2), suffix) = 
	   let
	     val f1 = addVarsLF(f, u1, suffix)
	     val f2 = addVarsLF(f1, u2, suffix)
	   in
	     f2
	   end

      | addVarsLF (f, N.First (r, u), suffix) = addVarsLF(f, u, suffix)
      | addVarsLF (f, N.Second (r, u), suffix) = addVarsLF(f, u, suffix)

      | addVarsLF (f, N.Of (r, u, t), suffix) = 
	   let
	     val f1 = addVarsLF(f, u, suffix)
	     val f2 = addVarsLFType(f1, t, suffix)
	   in
	     f2
	   end
      | addVarsLF (f, N.Paren (r, u), suffix) = addVarsLF(f, u, suffix)


    and addVarsLFType (f, T, suffix ) = f (* No dependent types *)
    and addVarsLFDec (f, N.LFDec (r, s, lft), suffix ) = 
	   let
	     fun f1 x = if isFVar(x, s) then s ^ suffix else f x
	     val f2 = addVarsLFType(f1, lft, suffix)
	   in
	     f2
	   end


    (* ************************************************************************************ *)
    (* ************************************************************************************ *)



    datatype TempDecs 
      = MetaDecTemp of (string list) option * N'.Formula
      | TermDecTemp of ReconTerm.dec

    datatype returnType 
      = retLF of I.Exp
      | retDec of I.Dec

    datatype willReturnType
      = willLF of (N'.Dec I.Ctx) * (TempDecs I.Ctx) * Paths.region * (L.Token * Paths.region) list * N'.Formula
      | willDec of (N'.Dec I.Ctx) * (TempDecs I.Ctx) * ReconTerm.dec * Paths.region

    fun reset() = filename := "stdIn"
    fun setFilename(s) = filename := s
    fun getFilename() = !filename




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
					(!filename,getRegion(f)),("Twelf Parse Error:  " ^ s))) 
	  val r2 = checkEOF f'
        in
	  t
        end

    fun convertTermToExp (Psi, r, tokenList) =
        let
	  val term = tokensToTerm(tokenList)
	  val _ = ReconTerm.resetErrors(!filename)
	  val ans = ReconTerm.reconWithCtx (N'.coerceCtx Psi, ReconTerm.jterm term)
	  val U = case ans
	          of ReconTerm.JTerm ((U, _), _, _) => U
		   | _ => raise Domain
	  val _ = ReconTerm.checkErrors(r)
	in
	  U
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

    and lftypeTokens (N.TypeConstant (r,s)) = [(getCase s, r), (L.EOF, r)]
      | lftypeTokens (N.RtArrow (r, l1,l2)) = [(L.LPAREN,r)] @ prune(lftypeTokens(l1)) @ [(L.ARROW,r)] @ prune(lftypeTokens(l2)) @ [(L.RPAREN,r)] @ [(L.EOF, r)]
      | lftypeTokens (N.LtArrow (r, l1,l2)) = [(L.LPAREN,r)] @ prune(lftypeTokens(l1)) @ [(L.BACKARROW,r)] @ prune(lftypeTokens(l2)) @ [(L.RPAREN,r)]@ [(L.EOF, r)]
      | lftypeTokens (N.And(_,l1,l2)) = raise NotImplemented "N.And"
      | lftypeTokens (N.UnitType _) = raise NotImplemented "N.UnitType"
      | lftypeTokens (N.Omit r) = [(L.UNDERSCORE, r)]@ [(L.EOF, r)]

    and lfdecTokens (N.LFDec (r, s,l)) = 
      let
	val Paths.Reg(a,b) = r
	val stringR = Paths.Reg(a, a + String.size(s))
      in
	[(getCase(s), stringR)] @  [(L.COLON,r)] @ lftypeTokens(l)
      end

    and lftermTokens (N.ObjectConstant (r,s)) = [(getCase s, r), (L.EOF, r)]
      | lftermTokens (N.Unit _) = raise NotImplemented "N.Unit"
      | lftermTokens (N.Fn (r, d, t)) = [(L.LBRACKET,r)] @ prune(lfdecTokens(d)) @ [(L.RBRACKET,r)] @ prune(lftermTokens(t)) @ [(L.EOF, r)]
      | lftermTokens (N.App (_, t1, t2)) = prune(lftermTokens(t1)) @ lftermTokens(t2)
      | lftermTokens (N.Pair (_, t1, t2)) = raise NotImplemented "N.Pair"
      | lftermTokens (N.First (_,t)) = raise NotImplemented "N.First"
      | lftermTokens (N.Second (_,t)) = raise NotImplemented "N.Second"
      | lftermTokens (N.Of (r,l,t)) = prune(lftermTokens(l)) @ [(L.COLON,r)] @ lftypeTokens(t)
      | lftermTokens (N.Paren (r,t)) = [(L.LPAREN, r)] @ prune(lftermTokens(t)) @ [(L.RPAREN, r), (L.EOF, r)]

    (*
    fun convertLFdec(Psi, lfdec as N.LFDec (r, _, _)) =
      let
	val f = LS.expose (LS.fromList(lfdecTokens(lfdec))) 
	val ((x, yOpt), f') = ParseTerm.parseDec' f
	    handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (!filename,getRegion(f)),("Twelf Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val dec = (case yOpt		
		     of NONE => ReconTerm.dec0 (x, r2)
	              | SOME y => ReconTerm.dec (x, y, r2))
	val _ = ReconTerm.resetErrors(!filename)
	val ans =
	  ReconTerm.reconWithCtx (N'.coerceCtx Psi, ReconTerm.jwithctx (I.Decl(I.Null, dec), ReconTerm.jnothing))
	val _ = ReconTerm.checkErrors(r) 

	val D = case ans
	        of ReconTerm.JWithCtx (I.Decl(I.Null, D as I.Dec(SOME n, E)), ReconTerm.JNothing) => D
		 | _ => raise Domain
      in
	D
      end
     *)

    fun getDec(lfdec) =
      let
	val f = LS.expose (LS.fromList(lfdecTokens(lfdec)))
	val ((x, yOpt), f') = ParseTerm.parseDec' f
	  handle Parsing.Error s => raise Error (Paths.wrapLoc(Paths.Loc (!filename,getRegion(f)),("Twelf Parse Error:  " ^ s))) 
	val r2 = checkEOF f'
	val dec = (case yOpt
		     of NONE => ReconTerm.refdec0 (x, r2)
		      | SOME y => ReconTerm.refdec (x, y, r2))
      in
	dec
      end

    fun getFirst (N'.And(F1, F2)) = F1
      | getFirst (N'.TVar (X as ref NONE)) = 
            let
	      val F1 = N'.newTVar()
	      val F2 = N'.newTVar()
	      val F = N'.And(F1, F2)
	      val _ = (X := SOME(F))
	    in
	      F1
	    end

      | getFirst (N'.TClo(N'.TVar (X as ref NONE), t)) =
            let
	      val F1 = N'.TClo(N'.newTVar(), t)
	      val F2 = N'.TClo(N'.newTVar(), t)
	      val F = N'.And(F1, F2)
	      val _ = (X := SOME(F))
	    in
	      F1
	    end
      | getFirst _ = raise Domain


    fun getSecond (N'.And(F1, F2)) = F2
      | getSecond (N'.TVar (X as ref NONE)) = 
            let
	      val F1 = N'.newTVar()
	      val F2 = N'.newTVar()
	      val F = N'.And(F1, F2)
	      val _ = (X := SOME(F))
	    in
	      F2
	    end

      | getSecond (N'.TClo(N'.TVar (X as ref NONE), t)) =
            let
	      val F1 = N'.TClo(N'.newTVar(), t)
	      val F2 = N'.TClo(N'.newTVar(), t)
	      val F = N'.And(F1, F2)
	      val _ = (X := SOME(F))
	    in
	      F2
	    end
      | getSecond _ = raise Domain

    fun getIndex(s, []) = ~1
      | getIndex(s, x::xs) = if (s = x) then 1 else (1 + getIndex(s,xs))

    fun convertMetaType (Psi, N.LFinsideType (r,LFT)) = 
           let
	     val tokenList = lftypeTokens(LFT) 
	   in
	     N'.Inj(convertTermToExp(Psi, r, tokenList)) 
	   end
      | convertMetaType (Psi, N.Box (_,T)) = N'.Box (convertMetaType (Psi,T))
      | convertMetaType (Psi, N.MetaArrow (_,T1,T2)) = N'.Imp(convertMetaType (Psi,T1), convertMetaType (Psi,T2))
      | convertMetaType (Psi, N.MetaAnd (_,T1,T2)) = N'.And(convertMetaType(Psi,T1), convertMetaType (Psi, T2))
      | convertMetaType (Psi, N.MetaOmit _) = N'.newTVar()

    (* Notice that we just throw out the "Term" versions.. Since there are no dependent types
     * this is ok here, but will cause many problems in the dependently typed system *)
    and mergeCtxs(I.Null, I.Null) = I.Null
      | mergeCtxs(Omega, I.Decl(G, MetaDecTemp (s, F))) = I.Decl(mergeCtxs(Omega, G), N'.MetaDec(s,F))
      | mergeCtxs(Omega, I.Decl(G, TermDecTemp _)) = I.Decl(mergeCtxs(Omega, G), N'.LFDec(I.NDec))
      | mergeCtxs(I.Decl(G, D), I.Null) = I.Decl(mergeCtxs(G,I.Null), D)


    and isUpper s = 
      let
	val c = case (String.explode(s)) 
	        of (c::xs) => c
		 | _ => raise Domain
      in
	(Char.isUpper(c))
      end

    and findRef (s, []) = NONE
      | findRef (s, (E as N'.FVar(s', _))::xs) = 
           if (s = s') then
	     SOME E
	   else 
	     findRef (s, xs)

      | findRef _ = raise Domain (* shouldn't happen *)

    and processFVar(s, NamedVarsRef) =
           (case (findRef (s, !NamedVarsRef))
	     of NONE => 
	          let
		    val newE = N'.newFVar(s, N'.newTVar())
		    val _ = NamedVarsRef := newE :: !NamedVarsRef
		  in
		    newE
		  end

	      | SOME E => E)


    and getIndex (s, [], k) =  NONE
      | getIndex (s, s'::xs, k) = if (s = s') then SOME(k) else getIndex(s, xs, k+1)

    (*
    (A, (B, (C, D)))
    A --> fst
    B --> fst snd 
    C --> fst snd snd
    D --> snd snd snd
     *)

    and buildProj' (1, g, F, _) = (N'.First(g), getFirst(NormalizeNabla.existsNormalizeFor(F)))
      | buildProj' (2, g, F, 2) = (N'.Second(g), getSecond(NormalizeNabla.existsNormalizeFor(F)))
      | buildProj' (i, g, F, k) = buildProj' (i-1, N'.Second(g), 
			getSecond(NormalizeNabla.existsNormalizeFor(F)),  k-1)

    and buildProjection (s, [s'], n, F) = if (s = s') then SOME(N'.Var (n), F) else NONE
      | buildProjection (s, sList, n, F) =
          (case (getIndex(s, sList, 1)) of
	     NONE => NONE
	   |(SOME i) => SOME(buildProj' (i, N'.Var(n), F, length(sList)))
	  )

    and lookup (I.Null, I.Null, NamedVarsRef, n, s) = 
              if isUpper(s) 
		then 
		  let
		    val (E, F) = case (processFVar(s, NamedVarsRef))
		                 of (E as (N'.FVar (_, F))) => (E, F)
				  | _ => raise Domain
		  in
		    (E, F)
		  end
		else 
		  raise Error ("Undeclared constant " ^ s)

      | lookup (Omega, I.Decl (G, TermDecTemp _), NamedVarsRef, n, s) = lookup (Omega, G, NamedVarsRef, n+1, s)
      | lookup (Omega, I.Decl (G, MetaDecTemp (SOME s', F)), NamedVarsRef, n, s) = 
        (case (buildProjection(s, s', n, F))
	  of (SOME EF) => EF 
	   | NONE => lookup(Omega, G, NamedVarsRef, n+1, s))

      | lookup (I.Decl (G, N'.MetaDec (NONE, _)), I.Null, NamedVarsRef, n, s) =  lookup (G, I.Null, NamedVarsRef, n+1, s)
      | lookup (I.Decl (G, N'.LFDec _), I.Null, NamedVarsRef, n, s) =  lookup (G, I.Null, NamedVarsRef, n+1, s)
      | lookup (I.Decl (G, N'.MetaDec (SOME s', F)), I.Null, NamedVarsRef, n, s) = 
        (case (buildProjection(s, s', n, F))
	  of (SOME EF) => EF
	   | NONE => lookup(G, I.Null, NamedVarsRef, n+1, s))

      | lookup _ = raise Domain


(* dead code
    fun getLFtype (Psi, N'.Inj(T)) = T
      | getLFtype (Psi, N'.TClo(N'.TVar (X as ref NONE), t)) =  
	     let
	      val newVar = I.newTypeVar (N'.coerceCtx Psi) 
	      val _ = (X := SOME(N'.Inj(newVar)))
	     in
	      I.EClo(newVar, N'.coerceSub t)
	     end

      | getLFtype (Psi, N'.TVar (X as ref NONE)) = 
	     let
	      val newVar = I.newTypeVar (N'.coerceCtx Psi) 
	      val _ = (X := SOME(N'.Inj(newVar)))
	     in
	      newVar
	     end

      | getLFtype _ = raise Error "Expected LF type, got Meta type"
*)

(* replaced with convertFixList
    fun convertFix(Psi::Omega, Phi::Gamma, NamedVarsRef, N.Fix(r, N.MetaDec(_, s,mType),term), formE) =
	    let
	      val form = convertMetaType(mergeCtxs(Psi,Phi), mType)

	      val _ = (U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (form, N'.id)) 
			      handle U.Error s => raise Error s)

	      val Phi' = I.Decl(Phi, MetaDecTemp(SOME [s], form))

	      val (f0, ts) = convertMeta'(Psi::Omega, Phi'::Gamma, NamedVarsRef, term, N'.substF(form, N'.Shift 1))
	      fun f x = N'.Fix(form, f0 x)

	      (* Since we now pass the type around, it will get an error in the conversion.
	       * no need to infer type!
	       *
	      val form' = T.inferType(Psi'::Omega, exp)  
		handle T.Error s => raise Error (Paths.wrapLoc(Paths.Loc (!filename,r),s))

	      (* Note:  Psi'::Omega |- [Shift 1] : Psi::Omega *)
	      val _ = if not (U.forEqual(Psi',(form, N'.Shift 1),(form',N'.id))) then raise Error (Paths.wrapLoc(Paths.Loc (!filename,r),("Incompatible Types!\nType 1 = " ^ PrintNablaInt.formStr(Psi,form) ^ "\nType 2 = " ^ PrintNablaInt.formStr(Psi',form')))) else ()
		*)
	      val Psi' = I.Decl(Psi, N'.MetaDec(SOME [s], form)) (* just for output to top level *)
	    in
	      (* returns the extended context, which we save if this is a top-level declaration *)
	      (Psi', f, ts)
	    end
      | convertFix _ = raise Domain
*)
    fun convertFix(Omega, Gamma, NamedVarsRef, N.Fix(r, d,t), formE) =
      convertFixList(Omega, Gamma, NamedVarsRef, [(r, d,t)], formE)
      | convertFix _ = raise Domain

    and convertFixList(Psi::Omega, Phi::Gamma, NamedVarsRef, L, formE) =
	    let

	      fun getStringList [(r, N.MetaDec (_, s, mType), term)] = [s]
		| getStringList ((r,N.MetaDec (_, s, mType),term)::xs) = s::(getStringList xs)
		| getStringList _ = raise Domain

	      fun listToString' [] = ""
		| listToString' (x::xs) = "," ^ x ^ (listToString' xs)

	      fun listToString [] = "[]"
		| listToString (x::xs) = "[" ^ x ^ (listToString' xs) ^ "]"

	      val sList = getStringList L


	      fun getRegionInfo [(r, _, _)] = r
		| getRegionInfo ((r,_,_)::xs) = Paths.join (r, getRegionInfo xs)
		| getRegionInfo _ = raise Domain

	      val r = getRegionInfo L

	      val mergeCtxs' = mergeCtxs(Psi,Phi)
	      fun getForms [(r, N.MetaDec (_, s, mType), term)] = convertMetaType(mergeCtxs', mType)
		| getForms ((r, N.MetaDec (_, s, mType), term)::xs) = N'.And(convertMetaType(mergeCtxs', mType), getForms xs)
		| getForms _ = raise Domain

	      fun getTerm [(r, N.MetaDec (_, s, mType), term)] = term
		| getTerm ((r, N.MetaDec (_, s, mType), term)::xs) = N.MetaPair(r, term , getTerm xs)
		| getTerm _ = raise Domain
 
	      val form = getForms L
	      val term = getTerm L

	      val _ = (U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (form, N'.id)) 
			      handle U.Error s => raise Error s)

	      val Phi' = I.Decl(Phi, MetaDecTemp(SOME sList, form))

	      val (f0, ts) = convertMeta'(Psi::Omega, Phi'::Gamma, NamedVarsRef, term, N'.substF(form, N'.Shift 1))
	      fun f x = N'.Fix(SOME(listToString sList),form, f0 x)

	      (* Since we now pass the type around, it will get an error in the conversion.
	       * no need to infer type!
	       *
	      val form' = T.inferType(Psi'::Omega, exp)  
		handle T.Error s => raise Error (Paths.wrapLoc(Paths.Loc (!filename,r),s))

	      (* Note:  Psi'::Omega |- [Shift 1] : Psi::Omega *)
	      val _ = if not (U.forEqual(Psi',(form, N'.Shift 1),(form',N'.id))) then raise Error (Paths.wrapLoc(Paths.Loc (!filename,r),("Incompatible Types!\nType 1 = " ^ PrintNablaInt.formStr(Psi,form) ^ "\nType 2 = " ^ PrintNablaInt.formStr(Psi',form')))) else ()
		*)
	      val Psi' = I.Decl(Psi, N'.MetaDec(SOME sList, form)) (* just for output to top level *)
	    in
	      (* returns the extended context, which we save if this is a top-level declaration *)
	      (Psi', f, ts)
	    end
      | convertFixList _ = raise Domain




    and existsNorm  F = NormalizeNabla.existsNormalizeFor(F)


    and recon (f, []) = f []
      | recon (f, ts) = 
      let
	(* dead code - ABP -- 11/15/04 
	(* Invariant should enforce that all Psi are the same in this list *)
	fun checkNoEVar (I.Uni _) = true
	  | checkNoEVar (I.Pi ((d,_), u)) = checkNoEVarDec(d) andalso checkNoEVar(u) 
	  | checkNoEVar (I.Root (h, s)) = checkNoEVarHead(h) andalso checkNoEVarSpine(s)
	  | checkNoEVar (I.Redex (u, s)) = checkNoEVar(u) andalso checkNoEVarSpine(s)
	  | checkNoEVar (I.Lam (d, u)) = checkNoEVarDec(d) andalso checkNoEVar(u)
	  | checkNoEVar (I.EVar (ref NONE, _, u, _)) = false
	  | checkNoEVar (I.EVar (ref (SOME u0), _, u, _)) = checkNoEVar(u0) andalso checkNoEVar(u)
	  | checkNoEVar (I.EClo(u, t)) = checkNoEVar(u) andalso checkNoEVarSub(t)
	  | checkNoEVar (I.AVar (ref NONE)) = false
	  | checkNoEVar (I.AVar (ref (SOME u))) = checkNoEVar(u)
	  | checkNoEVar (I.FgnExp _) = true 

	and checkNoEVarHead(I.Proj _) = raise Domain
	  | checkNoEVarHead(I.FVar (_, U, t)) = checkNoEVar(U) andalso checkNoEVarSub(t)
	  | checkNoEVarHead(I.FgnConst (_, c)) = checkNoEVarCon(c)
	  | checkNoEVarHead _ = true

	and checkNoEVarSpine(I.Nil) = true
	  | checkNoEVarSpine(I.App (U, S)) = checkNoEVar(U) andalso checkNoEVarSpine(S)
	  | checkNoEVarSpine(I.SClo(S, t)) = checkNoEVarSpine(S) andalso checkNoEVarSub(t)

	and checkNoEVarCon(I.ConDec (_, _, _, _, U, _)) = checkNoEVar(U)
	  | checkNoEVarCon(I.ConDef (_, _, _, U1, U2, _, _)) = checkNoEVar(U1) andalso checkNoEVar(U2)
	  | checkNoEVarCon(I.AbbrevDef(_,_,_,U1,U2,_)) = checkNoEVar(U1) andalso checkNoEVar(U2)
	  | checkNoEVarCon(I.BlockDec _) = raise Domain
	  | checkNoEVarCon(I.SkoDec (_, _, _, U, _)) = checkNoEVar(U)

	and checkNoEVarDec(I.Dec (_, u)) = checkNoEVar(u)
	  | checkNoEVarDec(I.BDec (_, (_, t))) = checkNoEVarSub(t)
	  | checkNoEVarDec _ = true

	and checkNoEVarSub (I.Dot (ft, t)) = checkNoEVarFront(ft) andalso checkNoEVarSub(t)
	  | checkNoEVarSub _ = true

	and checkNoEVarFront (I.Exp U) = checkNoEVar(U)
	  | checkNoEVarFront (I.Block _) = raise Domain (* no blocks *)
	  | checkNoEVarFront _ = true
	  *)

	fun createCtx (r, I.Null) = I.Null
	  | createCtx (r, (I.Decl(Phi, TermDecTemp D))) = I.Decl(createCtx(r,Phi), D)

	  (* Create an empty declaration -- how do we do this
	     I have to add an NDec to recon *)
	  | createCtx (r, (I.Decl(Phi, MetaDecTemp _))) = I.Decl(createCtx(r,Phi), 
								 ReconTerm.ndec r) 

	fun createJob (willLF (Psi, Phi, r, lftoks, formE)) = 
	       let
		 val term = tokensToTerm(lftoks)

		 val A = I.newTypeVar(N'.coerceCtx (mergeCtxs(Psi,Phi)))
		 val _ = (U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (N'.Inj A, N'.id)) 
			      handle U.Error s => raise Error s)

		 (*
		 val noEVar = checkNoEVar A (* NablaAbstract.closedExp(N'.coerceCtx Psi, (A, I.id)) *)
		 val job = if noEVar then ReconTerm.jof'(term, Whnf.normalize(A, I.id)) 
		           else ReconTerm.jterm term
	         *)

		 val job = ReconTerm.jwithctx (createCtx (r, Phi), 
					       ReconTerm.jof'(term, Whnf.normalize(A, I.id)))
	       in
		 job
	       end
	  | createJob (willDec (Psi, Phi, dec, r)) = 
	       let
		 val job = ReconTerm.jwithctx (I.Decl(createCtx(r, Phi), dec), ReconTerm.jnothing)
	       in
		 job
	       end

	fun getRegion (willLF (_, _, r, _, _)) = r
	  | getRegion  (willDec (_, _, _, r)) = r

	fun getRegionL [x] = getRegion(x)
	  | getRegionL (x::xs) = Paths.join(getRegion(x), getRegionL(xs))
	  | getRegionL _ = raise Domain

	fun getPsi ((willLF (Psi, _, _, _, _)) :: _) = Psi
	  | getPsi ((willDec (Psi, _, _, _)) :: _) = Psi
	  | getPsi _ = raise Domain

	fun listToAnd [] = ReconTerm.jnothing
	  | listToAnd (x::xs) = ReconTerm.jand(x, listToAnd(xs))


	(* All Psi's are the same by invariant! 
	 * We can only reconstruct terms in the same context 
	 *)
	val Psi = getPsi ts
	val jobList = map createJob ts
	val masterJob = listToAnd(jobList)

	val _ = ReconTerm.resetErrors(!filename)
	val answerJob = ReconTerm.reconWithCtx (N'.coerceCtx Psi, masterJob)
	val _ = ReconTerm.checkErrors(getRegionL ts)


	fun getAnswers ([], ReconTerm.JNothing) = []
(*
	  | getAnswers (((willLF _) :: xs), ReconTerm.JAnd(ReconTerm.JTerm ((U, _), A, _) , jobs)) 
	             = (retLF U) :: (getAnswers(xs, jobs))
*)

	  | getAnswers (((willLF _) :: xs), ReconTerm.JAnd(ReconTerm.JWithCtx(_, ReconTerm.JOf ((U,_), (_, _), _)), jobs))
	             = (retLF U) :: (getAnswers(xs, jobs))
	  | getAnswers (((willDec _) :: xs), ReconTerm.JAnd(ReconTerm.JWithCtx (I.Decl(_, D as I.Dec(SOME n, E)), ReconTerm.JNothing), jobs)) 
	             = (retDec D) :: (getAnswers(xs, jobs))
	  | getAnswers _ = raise Domain


	val ansL = getAnswers(ts, answerJob)

      in
	f ansL
      end


    (* We have two contexts that exist simultaneously
     * the "real" context is the pairwise merging of ctxs with ctxs'
     *)

    and convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaID (r,s), formE) = 
      let
	(* look it up right away to get type information *)
	val (E,F) = lookup(Psi, Phi, NamedVarsRef, 1, s) handle Error s => (raise Error (Paths.wrapLoc(Paths.Loc (!filename,r),s)))
	val _ = U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (F, N'.id))
	          handle U.Error s => raise Error s

	fun f [] = E
	  | f _ = raise Domain
		   
      in
	(f, [])
      end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.LFinside (r,LFterm), formE) = 
	let
	  fun f [retLF i] = N'.Quote(i)
	    | f _ = raise Domain
	in
	  (f, [willLF (Psi, Phi, r, lftermTokens(LFterm), formE)])
	   (* Need to do convertTermToExp(Psi, r, lftermTokens(LFterm)) to get LF value *)
	end

      | convertMeta'(_, _, _, N.Fail(r), formE) = (fn [] => N'.Fail | _ => raise Domain, [])


      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.Pop (_,term), formE) = 
	let
	  val formE' = N'.newTVar()
	  val t = N'.Shift (I.ctxLength(Psi) + I.ctxLength(Phi) - I.ctxLength(hd(Omega)) 
			    - I.ctxLength(hd(Gamma))  )

          (* Carsten:  this is going to be hard we will need unify on ReconTerms!!! *)
	  val _ = U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (N'.Box(formE'), t))
	          handle U.Error s => raise Error s
		    
	  val (f1,ts1)  = convertMeta'(Omega,Gamma,NamedVarsRef, term, formE')
	  fun f x = N'.Pop(f1 x)

	in
	  (f, ts1)
	end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.PatMatch (_,term1,term2), formE) = 
            let
	      val formE1 = N'.newTVar()
	      val formE2 = N'.newTVar()
	      val _ = U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (N'.Imp(formE1, formE2), N'.id))
	          handle U.Error s => raise Error s

	      val (f1, ts1)  = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term1, formE1)
	      val size1 = List.length(ts1)
	      val (f2, ts2) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term2, formE2)

	      fun f x = 
		let
		  val x1 = List.take(x, size1)
		  val x2 = List.drop(x, size1)
		  val exp1 = f1 x1
		  val exp2 = f2 x2
		in
		  N'.Case(exp1, formE1, exp2)
		end
	    in
	      (f, ts1@ts2)
	    end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaApp (_, term1, term2), formE) = 
            let
	      val newTVar = N'.newTVar()
	      val formE1 = N'.Imp(newTVar, formE)
	      val formE2 = newTVar

	      (* do argument first to see if it instantiates the TVar *)
	      val (f2, ts2) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term2, formE2)
	      val (f1, ts1) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term1, formE1)
	      val size2 = List.length(ts2)


	      fun f x =
		let
		  val x2 = List.take(x, size2)
		  val x1 = List.drop(x, size2)
		  val exp2 = f2 x2
		  val exp1 = f1 x1
		in
		  N'.App(exp1, exp2)
		end
	    in
	      (f, ts2@ts1)
	    end


      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaPair (_, term1, term2), formE) = 
            let
	      val formE1 = N'.newTVar()
	      val formE2 = N'.newTVar()
	      val _ = U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (N'.And(formE1, formE2), N'.id))
	          handle U.Error s => raise Error s

	      val (f1, ts1) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term1, formE1)
	      val size1 = List.length(ts1)
	      val (f2, ts2) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term2, formE2)

	      fun f x =
		let
		  val x1 = List.take(x, size1)
		  val x2 = List.drop(x, size1)
		  val exp1 = f1 x1
		  val exp2 = f2 x2
		in
		  N'.Pair(exp1, exp2)
		end

	    in
	      (f, ts1@ts2)
	    end


      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.Bar (_, term1, term2), formE) = 
            let
	      val (f1, ts1) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term1, formE)
	      val size1 = List.length(ts1)
	      val (f2, ts2) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, term2, formE)

	      fun f x =
		let
		  val x1 = List.take(x, size1)
		  val x2 = List.drop(x, size1)
		  val exp1 = f1 x1
		  val exp2 = f2 x2
		in
		  N'.Alt(exp1, exp2)
		end
	    in
	      (f, ts1@ts2)
	    end



      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.New (_, lfdec as N.LFDec(r, s, _), term), formE) = 
	    let
	      val dec = getDec(lfdec)
	      val Phi' = I.Decl(Phi, TermDecTemp dec)

	      val (f2,ts2) = convertMeta'(Psi::Psi::Omega, Phi'::Phi::Gamma, NamedVarsRef, term, N'.Box(N'.substF(formE, N'.Shift 1)))

	      fun f x =
		let
		  val D = case List.take (x,1)
		            of [retDec D] => D
			     | _ => raise Domain

		  val x2 = List.drop (x, 1)

		  val exp1 = case D of (I.Dec (_, e)) => e 
		                     | _ => raise Domain
		  val exp2 = f2 x2
		in
		  N'.New(SOME s, exp1, exp2)
		end

	    in
	      (f, (willDec (Psi, Phi, dec, r))::ts2)
	    end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.Nabla (_, lfdec as N.LFDec(r, s, _), term), formE) = 
	    let
	      val dec = getDec(lfdec)
	      val Phi' = I.Decl(Phi, TermDecTemp dec)

	      val (f2,ts2) = convertMeta'(Psi::Omega, Phi'::Gamma, NamedVarsRef, term, N'.substF(formE, N'.Shift 1))
	      fun f x =
		let
		  val D = case List.take (x,1) 
		          of [retDec D] => D
			   | _ => raise Domain
		    
		  val x2 = List.drop (x, 1)

		  val exp1 = case D of (I.Dec (_, e)) => e 
		                     | _ => raise Domain
		  val exp2 = f2 x2
		in
		  N'.Nabla(SOME s, exp1, exp2)
		end

	    in
	      (f, (willDec (Psi, Phi, dec, r))::ts2)
	    end




      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.Eps(_, lfdec as N.LFDec(r, s, _), term), formE) =
	    let
	      val dec = getDec(lfdec)
	      val Phi' = I.Decl(Phi, TermDecTemp dec)

	      val (f2,ts2) = convertMeta'(Psi::Omega, Phi'::Gamma, NamedVarsRef, term, N'.substF(formE, N'.Shift 1))
	      fun f x =
		let
		  val D = case List.take (x,1) 
		          of [retDec D] => D
			   | _ => raise Domain

		  val x2 = List.drop (x, 1)

		  val exp1 = case D of (I.Dec (_, e)) => e 
		                     | _ => raise Domain
		  val exp2 = f2 x2
		in
		  N'.Some(SOME s, exp1, exp2)
		end

	    in
	      (f, (willDec (Psi, Phi, dec, r))::ts2)
	    end



      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.EpsM(_, N.MetaDec(_, s,mType), term), formE) =
	    let
	      val form = convertMetaType(mergeCtxs(Psi,Phi), mType)
	      val Phi' = I.Decl(Phi, MetaDecTemp(SOME [s], form))

	      val (f2,ts2) = convertMeta'(Psi::Omega, Phi'::Gamma, NamedVarsRef, term, N'.substF(formE, N'.Shift 1))
	      fun f x = N'.SomeM(SOME s, form, f2 x)

	    in
	      (f, ts2)
	    end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, m as N.Fix (_, dec, term), formE) = 
	    let
	      val (_, f, ts) = convertFix(Psi::Omega, Phi::Gamma, NamedVarsRef, m, formE)
	    in
	      (f, ts)
	    end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaFirst (_,t1), formE) = 
	    let
	      val formE' = N'.And(formE, N'.newTVar())
	      val (f1, ts1) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, t1, formE')

	      fun f x = N'.First (f1 x)
	    in
	      (f, ts1)
	    end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaSecond (_,t1), formE) = 
	    let
	      val formE' = N'.And(N'.newTVar(), formE)
	      val (f1, ts1) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, t1, formE')

	      fun f x = N'.Second (f1 x)
	    in
	      (f, ts1)
	    end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.AppInside (r, t1,t2), formE) = 
	    let
	      val resultType = I.newTypeVar(N'.coerceCtx (mergeCtxs(Psi,Phi)))
	      val _ = (U.unifyFor(mergeCtxs(Psi,Phi), (formE, N'.id), (N'.Inj(resultType), N'.id)) 
		       handle U.Error s => raise Error s)
		
		(* This is wrong context, will really be a problem in dependently typed case! *)
	      val argumentType = I.newTypeVar(N'.coerceCtx (mergeCtxs(Psi,Phi)))
	      val argumentFor = N'.Inj(argumentType)


	      val funType = I.Pi ((I.Dec (NONE, argumentType), I.Maybe) , resultType)
	      val funFor = N'.Inj(funType)


	      val (f2,ts2) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, t2, argumentFor)
	      val (f1,ts1) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, t1, funFor)
	      val size2 = List.length(ts2)

	      fun f x =
		let
	          val x2 = List.take (x, size2)
		  val x1 = List.drop(x, size2)
		  val t2' = f2 x2
		  val t1' = f1 x1

		  val a = N'.Some(NONE, funType, 
			     (N'.Case (N'.Quote (I.Root (I.BVar 1, I.Nil)),
				       N'.newTVar(),
				       N'.Some (NONE, argumentType, 
						(N'.Case (N'.Quote (I.Root (I.BVar 1, I.Nil)), N'.newTVar(), N'.Quote (I.Redex (I.Root (I.BVar 2, I.Nil), I.App(I.Root (I.BVar 1, I.Nil), I.Nil)))))))))
		in
		  N'.App(N'.App(a, t1'), t2')
		end
	    in
	      (f, ts2@ts1)
	    end

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.Let (r, mdec as (N.MetaDec(_,s,_)), t1, t2), f) = 
	            convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaApp(r, N.EpsM(r, mdec, N.PatMatch(r, 
				N.MetaID (r,s),t2)), N.Fix(r, mdec, t1)), f)

      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.LetM (r, lfdec as (N.LFDec(_,s,_)), t1, t2), f) = 
		    convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaApp(r, N.Eps(r, lfdec, N.PatMatch(r, 
				N.LFinside(r, N.ObjectConstant(r,s)),t2)), t1), f)


      | convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.Case (r, t1,t2), f) = convertMeta'(Psi::Omega, Phi::Gamma, NamedVarsRef, N.MetaApp(r, t2, t1), f)
		    
      | convertMeta'(Omega, Gamma, NamedVarsRef, N.Sequence l, f) = 
		    let
		      (* Cannot be empty list by invariant *)
		      fun conv Omega Gamma NamedVarsRef f [(r,e)] = 
			       convertMeta'(Omega, Gamma, NamedVarsRef, e, f)
			| conv Omega Gamma NamedVarsRef f ((r,e)::xs) = 
			       let
				 val (f1, ts1) = convertMeta'(Omega, Gamma, NamedVarsRef, e, N'.newTVar())
				 val size1 = List.length(ts1)
				 val (f2, ts2) = conv Omega Gamma NamedVarsRef f xs
				 val F = N'.newTVar()
				 fun f3 x =
				   let
				     val x1 = List.take (x, size1)
				     val x2 = List.drop(x, size1)
				     val exp1 = f1 x1
				     val exp2 = f2 x2
				   in
				     (* [x] (x |--> convRest) e' *)
				     N'.App(
					    N'.SomeM(NONE, F,
						     N'.Case (N'.Var 1, F, N'.subst(exp2, N'.Shift 1))),
					    exp1)
				   end
			       in
				 (f3, ts1@ts2)
			       end
			| conv _ _ _ _ _ = raise Domain
				   
		    in
		      conv Omega Gamma NamedVarsRef f l 
		    end


      | convertMeta'(_, _, _, N.PairInside (_, t1,t2), _) = raise NotImplemented "PairInside"
		    
      | convertMeta' ([],[],_,_, _) = raise Error "Pop'd off too much!"

      | convertMeta' _ = raise Domain

     fun convertFix0 (Psi, E) = 
       let
	 val (Psi', f, ts) = convertFix ([Psi], [I.Null], ref nil, E, N'.newTVar())
       in
	 (Psi', recon(f, ts))
       end

     fun convertFixList0 (Psi, L) = 
       let
	 val (Psi', f, ts) = convertFixList ([Psi], [I.Null], ref nil, L, N'.newTVar())
       in
	 (Psi', recon(f, ts))
       end


     fun convertMeta0 (Psi, E) = 
       let
	 val (f, ts) = convertMeta' ([Psi], [I.Null], ref nil, E, N'.newTVar()) 
	(* convertMeta' returns a function which takes a list of 
	 * IntSyn.expressions.  The second return argument is the "term" version of those
	 * arguments it wants
	 *)
      in
	recon(f, ts)
      end

     fun renameVarsFixList0 L = renameVarsFixList(fn x => x, L, ".")
     fun renameVars0 E = renameVars(fn x => x, E, ".")


  end