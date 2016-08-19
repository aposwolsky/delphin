(* Delphin Temporary Intermediate Syntax 
 * Used during conversion from external 
 * to internal syntax
 *)
(* Author: Adam Poswolsky *)

structure DelphinIntermediateSyntax = 
struct
structure I = IntSyn
structure D = DelphinIntSyntax
exception SubstFailed

datatype Types
  = LF of Paths.region * D.isParam * I.Exp
  | Meta of Paths.region * Formula (* D.Existential *)

and Formula
  = Top     of Paths.region
  | All     of Paths.region * ((D.Visibility * NormalDec) list) * Formula
  | Exists  of Paths.region * NormalDec * Formula 
  | Nabla   of Paths.region * NewDec * Formula
  | FormulaString of Paths.region * string
  | OmittedFormula of Paths.region 
  

and NormalDec 
  = NormalDec of Paths.region * (string option) * Types

  
and NewDec 
  = NewDecLF of Paths.region * (string option) * I.Exp
  | NewDecWorld of Paths.region * (string option) * D.World

and Dec
  = InstantiableDec of Paths.region * NormalDec    
  | NonInstantiableDec of Paths.region * NewDec


and Exp
  = VarInt    of Paths.region * int 
  | Quote  of Paths.region * I.Exp * I.Exp * DelphinApprox.SmartInj * D.isParam (* (U : V)  *)
  | Unit   of Paths.region
  | Lam    of bool * Paths.region * (CaseBranch list) * (D.Formula option)
                (* bool = true if it is really a "MatchSugar" that needs to be desugared.  *)
		(* bool = false if it is not syntactic sugar *)
                 (* i.e. fn A B C => E
		          | A' B' C' => E'
		  * is syntactic sugar for fn X1 => fn X2 => fn X3 => case (X1 and X2 and X3)
		                                                         of A and B and C => E
									  | A' and B' and C' => E'
		  *)

  | New    of Paths.region * NewDec * Exp
  | App    of Paths.region * Exp * ((D.Visibility * Exp) list)
  | Pair   of Paths.region * Exp * Exp
  | Proj   of Paths.region * Exp * int
  | Pop    of Paths.region * int * Exp
 (* not used...
  | Fix    of Paths.region * (Paths.region * NormalDec * Exp) list 
             (* Not in use from the actual parser.. as embedded fixpoints are introduced with let.
	      * But it is useful to have  for converting internal syntax to external one *)
  *)

  | PatVar of Paths.region * string * string 
            (* second string represents the original name, if it was renamed! *)

  (* Syntactic Sugar *)
  | TypeAscribe of Paths.region * Exp * Types
  | Sequence of (Paths.region * Exp) list
  (* Removed.. now translated before this stage
  | LiftedApp of Paths.region * Exp * I.Exp * Exp * I.Exp  * I.Exp
                            (*  E1    typeE1   E2   typeE2  typeResult *)
  | LetVar of Paths.region * NormalDec * Exp * Exp
  *)
  | LetFun of Paths.region * (Paths.region * NormalDec * Exp) list * Exp

  | ExtendFunWith of Paths.region * Exp * (CaseBranch list) * int * int * bool * (D.Formula option)
             (*
	      * Extends the parameter (world) function E with the cases listed in CS
	      * i.e. it will build a function that will use CS to handle parameters in G2a
	      * and will call E on all other parameters.
	      * In the external syntax you will write:  "extend E with ..."

	      (bool represents isSugar)
	       GB |- E : T
	       GB, G2a |- CS : T
               and first and last elements of G2a are NonInstantiable
		 (for the actual conversion to internal syntax,
		  it will complain unless ALL elements in G2a are NonInstantiable)
	       ------------------------------------------------------
	       GB, G2a, G2b |- ExtendFunWith(E, CS, sizeG2a, sizeG2b) : T

	       (D.Formula option) = T (which makes sense in GB)
              *)





  
               
and CaseBranch
    = Eps of Paths.region * NormalDec * CaseBranch
    | NewC of Paths.region * NewDec * CaseBranch
  (* Removed..   PopC of Paths.region * int * CaseBranch *)
    | Match of Paths.region * ((D.Visibility * Exp) list) * Exp (* patterns => result *)


datatype LFExpWorld
  = WorldEps of Paths.region * NormalDec * LFExpWorld
  | WorldType of Paths.region * I.Exp


(* ********************************************** *)
(* Substitutions (Used in abstract.fun *)
(* We only support pattern substitutions on the intermediate
 * syntax....  we could generalize to more.. but is it necessary? 
 *) 
datatype Sub 
  = Shift of Sub
  | DotIdx of int * Sub (* Just a pattern substitution.. no arbitrary front *)
  | DotUndef of Sub (* Undef. s *)
  | id



(* Functions / Substitution Application *)

fun shift (0) = id
  | shift (i) = Shift (shift(i-1))

fun dot1 (id) = id
  | dot1 t = DotIdx (1, Shift t)

fun substF(Top r, t) = Top r
  | substF(All (r, Ds, F), t) = 
         let
	   fun substDecs ([], t) = ([], t)
	     | substDecs ((visibility, D) :: Ds, t) = 
	           let
		     val (Ds', t') = substDecs (Ds, I.dot1 t)
		   in
		     ((visibility, substNormalDec(D, t)) :: Ds', t')
		   end
	   val (Ds', t') = substDecs (Ds, t)
	 in	   
	   All (r, Ds', substF(F, t'))
	 end

  | substF(Exists (r, D, F), t) = Exists (r, substNormalDec(D, t), substF(F, I.dot1 t))
  | substF(Nabla (r, D, F), t) = Nabla (r, substNewDec(D, t), substF(F, I.dot1 t))
  | substF(FormulaString (r, s), t) = FormulaString(r,s) (* Type Aliases occurs on the top-level, so 
							  * the type referred to by "s" makes sense in the empty context without any EVars *)
  | substF(OmittedFormula r, t) = OmittedFormula r

and substTypes(LF (r, isP, A), t) = LF (r, isP, I.EClo(A, t))
  | substTypes(Meta (r, F), t) = Meta (r, substF(F, t))

and substNormalDec (NormalDec (r, name, T), t) = NormalDec(r, name, substTypes(T,t))
and substNewDec (NewDecLF (r, name, A), t) = NewDecLF (r, name, I.EClo(A, t))
   | substNewDec (NewDecWorld D,t) = NewDecWorld D 

fun substFopt (NONE, t) = NONE
  | substFopt (SOME F, t) = SOME (D.FClo(F, t))

fun coerceSub (id) = I.id
  | coerceSub (Shift t) = I.comp(coerceSub t, I.shift)
  | coerceSub (DotIdx (i, t)) = I.Dot (I.Idx i, coerceSub t)
  | coerceSub (DotUndef t) = I.Dot (I.Undef, coerceSub t)


fun coerceTypes (LF (_, _, A)) = SOME A
  | coerceTypes (Meta _) = NONE

fun coerceDec (InstantiableDec (_, NormalDec (_, sO, T))) = 
              (case (coerceTypes T)
		 of NONE => I.NDec
		  | SOME A => I.Dec(sO, A)
	      )

  | coerceDec (NonInstantiableDec (_, NewDecLF (_, sO, A))) =
		 I.Dec(sO, A)

  | coerceDec (NonInstantiableDec (_, NewDecWorld _)) =
		 I.NDec


(* see intSyntax.sml *)
fun popSub (i, Shift t) =
        let 
	  val (j, t') = popSub (i, t)
	in 
	  (j+1, t')
	end
  | popSub (i, id) = (i, id)
  | popSub (1, DotIdx(1, Shift t)) = (1, t)
  | popSub (1, DotUndef _) = raise SubstFailed
  | popSub (i, DotIdx(_, t)) = popSub(i-1, t)
  | popSub (i, DotUndef(t)) = popSub(i-1, t)


fun substCase (Eps (r, D, C), t) = Eps (r, substNormalDec(D, coerceSub t), substCase(C, dot1 t))
  | substCase (NewC (r, D, C), t) = NewC (r, substNewDec(D, coerceSub t), substCase(C, dot1 t))
(*
  | substCase (PopC (r, i, C), t) = 
                           let val (j, t') = popSub(i, t)
			   in
			     PopC (r, j, substCase(C,t'))
			   end
*)
  | substCase (Match (r, pats, resE), t) = Match (r, map (fn (vis, E) => (vis, substE(E, t))) pats, substE(resE, t))

and substWorld (WorldEps (r, D, W), t) = WorldEps (r, 
						   substNormalDec(D, coerceSub t),
						   substWorld(W, dot1 t))
  | substWorld (WorldType (r, A), t) = WorldType (r, I.EClo(A, coerceSub t))
						   

and substE(E, id) = E
  | substE(VarInt (r,1), DotIdx(j, t)) = VarInt (r, j)
  | substE(VarInt (r,1), DotUndef t) = raise SubstFailed  
  | substE(VarInt (r,i), DotIdx(_, t)) = substE(VarInt (r,(i-1)), t)
  | substE(VarInt (r,i), DotUndef(t)) = substE(VarInt (r,(i-1)), t)
  | substE(VarInt (r,i), Shift id) = VarInt (r, i+1)
  | substE(VarInt (r,i), Shift t) = substE(substE(VarInt (r,i), t), Shift id)
  | substE(Quote (r,M,A, I, isP), t) = 
             let 
	       val t' = coerceSub t
	     in
	       Quote (r, I.EClo(M, t'), I.EClo(A, t'), I, isP)
	     end
  | substE(Unit r, _) = Unit r
  | substE(Lam (isSugar, r, Clist, Fopt), t) = 
                        let
			  val Clist' = map (fn C => substCase(C, t)) Clist
			in
			  Lam (isSugar, r, Clist', substFopt(Fopt, coerceSub t))
			end


  | substE(New (r, D, E), t) = New (r, substNewDec(D, coerceSub t), substE (E, dot1 t))
  | substE(App (r, E1, args), t) = App (r, substE(E1, t), map (fn (visible, E2) => (visible, substE(E2, t))) args)
  | substE(Pair (r, E1, E2), t) = Pair (r, substE(E1, t), substE(E2, t))

  | substE(Proj (r, E,i), t) = Proj(r, substE(E,t), i)
			
  | substE(Pop (r, i, E), t) = 
	   let val (j, t') = popSub(i, t)
	   in
	     Pop (r, j, substE(E,t'))
	   end

 (* not used
  | substE(Fix (r, funList), t) = Fix (r, substFunList(funList, t))
  *)

  | substE(PatVar (r, s, origName), t) = PatVar (r, s, origName)

  | substE(TypeAscribe (r, E, T), t) = TypeAscribe(r, substE(E, t), substTypes(T, coerceSub t))
  | substE(Sequence seqList, t) = 
	   let
	     fun subst' (r,E) = (r, substE(E, t))
	   in
	     Sequence (map subst' seqList)
	   end
(* removed
  | substE(LiftedApp (r, E1, A1, E2, A2, Aresult), t) = LiftedApp(r, substE(E1,t),
								  I.EClo(A1, coerceSub t),
								  substE(E2, t),
								  I.EClo(A2, coerceSub t),
								  I.EClo(Aresult, coerceSub t))

  | substE(LetVar (r, D, E1, E2), t) = LetVar (r, 
					       substNormalDec(D, coerceSub t), 
					       substE(E1, t),
					       substE(E2, dot1 t))
*)
  | substE(LetFun (r, funlist, E2), t) = LetFun (r,
						 substFunList(funlist, t),
						 substE(E2, dot1 t))
								

  | substE(ExtendFunWith (r, E, Clist, sizeG2a, sizeG2b, isSugar, Fopt), t) =   
             (*
	      (bool represents isSugar)
	       GB |- E : T
	       GB, G2a |- CS : T
               and first and last elements of G2a are NonInstantiable
	       ------------------------------------------------------
	       GB, G2a, G2b |- ExtendFunWith(E, CS, sizeG2a, sizeG2b) : T

	       (D.Formula option) = T (which makes sense in GB)
              *)
	   let
	     val (j', t') = popSub(sizeG2b+1, t)
	     val sizeG2b' = j' - 1
	     val t'' = dot1 t' 
	       (* domain of t'' is GB,G2a *)
	     val Clist' = map (fn C => substCase(C, t'')) Clist

	     val (sizeG2a', t3) = popSub(sizeG2a, t'') 
	       (* domain of t3 is GB *)
	     val E' = substE(E, t3)
	     val F' = substFopt(Fopt, coerceSub t3)
	   in
	     ExtendFunWith(r, E', Clist', sizeG2a', sizeG2b', isSugar, Fopt)
	   end


and substFunList ([], t) = []
  | substFunList ((r,D,E)::funlist, t) = (r, substNormalDec(D, coerceSub t), substE(E, dot1 t)) :: substFunList(funlist, t)


(* OLD
(* Applying an inverting substitution *)

(* Only inverts a substitution of the form "shift^i id" *)
fun invertShiftSub 0 = id
  | invertShiftSub n = DotUndef( invertShiftSub(n-1) )

(* applyInv2Exp(Gglobal, G, E, ss, rOccur) applies E to ss where ss is an inverted substitution *)
(* G is the DOMAIN of ss *)
(* May raise SubstFailed *)

fun LFapplyInv2Exp (G, U, ss) = (UnifyNoTrail.invertExp (I.Null, G, (U, I.id), ss, ref NONE)) handle _ => raise SubstFailed

fun applyInv2Formula (G, F as Top r, ss) = F
  | applyInv2Formula (G, All (r, Ds, F), ss) = 
	              let
			fun applyInv2Decs ([], G, t) = ([], G, t)
			  | applyInv2Decs ((visibility, D) :: Ds, G, t) = 
			    let
			      val D' = applyInv2NormalDec(G, D, t)
			      val (Ds', G', t') = applyInv2Decs (Ds, I.Decl(G, coerceDec (InstantiableDec (r,D))), I.dot1 t)
			    in
			      ((visibility, D') :: Ds', G', t')
			    end
			val (Ds', G', ss') = applyInv2Decs (Ds, G, ss)
		      in	   
			All(r, Ds',
			      applyInv2Formula(G', F, ss'))
		      end

  | applyInv2Formula (G, Exists (r, D, F), ss) = Exists (r, applyInv2NormalDec (G, D, ss),
							 applyInv2Formula(I.Decl(G, coerceDec (InstantiableDec (r, D))), F, I.dot1 ss))
  | applyInv2Formula (G, Nabla (r, D, F), ss) = Nabla (r, applyInv2NewDec (G, D, ss),
							 applyInv2Formula(I.Decl(G, coerceDec (NonInstantiableDec (r, D))), F, I.dot1 ss))
  | applyInv2Formula (G, F as FormulaString _, ss) = F
  | applyInv2Formula (G, F as OmittedFormula _, ss) = F

and applyInv2Types (G, LF (r, isP, A), ss) = LF (r, isP, LFapplyInv2Exp (G, A, ss))
  | applyInv2Types (G, Meta (r, F), ss) = Meta (r, applyInv2Formula (G, F, ss))

and applyInv2NormalDec (G, NormalDec(r, name, T), ss) = NormalDec (r, name, applyInv2Types (G, T, ss))
and applyInv2NewDec (G, NewDecLF (r, name, A), ss) = NewDecLF (r, name, LFapplyInv2Exp(G, A, ss))
  | applyInv2NewDec (G, NewDecWorld (r, name, W), ss) = NewDecWorld (r, name, W)

fun applyInv2Exp (G, E as VarInt _, ss) = substE(E, ss) (* may raise SubstFailed *)
  | applyInv2Exp (G, Quote (r, U, A, I, isP), ss) = Quote (r,
							   LFapplyInv2Exp(G, U, coerceSub ss),
							   LFapplyInv2Exp(G, A, coerceSub ss),
							   I,
							   isP)
  | applyInv2Exp (G, E as Unit _, ss) = E
  | applyInv2Exp (G, Lam (isSugar, r, Clist), ss) = Lam (isSugar, r, map (fn C => applyInv2Case(G, C, ss)) Clist)
  | applyInv2Exp (G, New (r, D, E), ss) =  New (r, applyInv2NewDec(G, D, coerceSub ss), 
						applyInv2Exp(I.Decl(G,coerceDec(NonInstantiableDec (r, D))), E, dot1 ss))
  | applyInv2Exp (G, App (r, E1, args), ss) = App (r, 
						   applyInv2Exp(G, E1, ss), 
						   map (fn (visible, E2) => (visible, applyInv2Exp(G, E2, ss))) args)
  | applyInv2Exp (G, Pair (r, E1, E2), ss) = Pair (r, applyInv2Exp(G, E1, ss), applyInv2Exp(G, E2, ss))
  | applyInv2Exp (G, Proj (r, E, i), ss) = Proj (r, applyInv2Exp(G, E, ss),i)
  | applyInv2Exp (G, Pop(r, i, E), ss) =
			let
			  val (j, t') = popSub(i, ss)
			  (* G',j..1 |- ss : G,i..1 By Assumption*)
			  (* G' |- t' : G *)
			  val E' = applyInv2Exp(D.popCtx(i, G), E, t')
			in
			  Pop(r, j, E')
			end

  | applyInv2Exp (G, Fix (r, funlist), ss) = Fix (r, applyInv2FunList (G, funlist, ss))

  | applyInv2Exp (G, E as PatVar _, ss) = E
  | applyInv2Exp (G, TypeAscribe (r, E, T), ss) = TypeAscribe (r, applyInv2Exp (G, E, ss), applyInv2Types(G, T, coerceSub ss))
  | applyInv2Exp (G, Sequence list, ss) = 
		      let
			fun apply (r, E) = (r, applyInv2Exp (G, E, ss))
		      in
			Sequence (map apply list)
		      end
  | applyInv2Exp (G, LetFun (r, funlist, E), ss) = LetFun (r,
							   applyInv2FunList (G, funlist, ss),
							   applyInv2Exp (I.Decl(G, I.NDec), E, dot1 ss))



and applyInv2FunList (G, [], ss) = []
  | applyInv2FunList (G, (r, D, E)::funlist, ss) = (r, applyInv2NormalDec(G, D, coerceSub ss), applyInv2Exp(I.Decl(G, I.NDec), E, dot1 ss)) :: applyInv2FunList (G, funlist, ss)


and applyInv2Case(G, Eps(r,D,C), ss) = Eps (r, applyInv2NormalDec(G, D, coerceSub ss),
					    applyInv2Case(I.Decl(G,coerceDec (InstantiableDec (r, D))), C, dot1 ss))
  | applyInv2Case(G, NewC(r, D,C), ss) = NewC (r, applyInv2NewDec(G, D, coerceSub ss),
					       applyInv2Case(I.Decl(G,coerceDec (NonInstantiableDec (r, D))), C, dot1 ss))
  | applyInv2Case(G, PopC(r,i,C), ss) = 
	                let
			  val (j, t') = popSub(i, ss)
			  (* G',j..1 |- ss : G,i..1 By Assumption*)
			  (* G' |- t' : G *)
			  val C' = applyInv2Case(D.popCtx(i, G), C, t')
			in
			  PopC(r,j, C')
			end

  | applyInv2Case(G, Match(r, pats,E2), ss) = Match (r, 
						     map (fn (visible, E1) => (visible, applyInv2Exp(G, E1, ss))) pats,
						     applyInv2Exp(G, E2, ss))
*)

fun getRegionExp (VarInt (r, _)) = r
  | getRegionExp (Quote (r, _, _, _, _)) = r
  | getRegionExp (Unit r) = r
  | getRegionExp (Lam (_, r, _, _)) = r
  | getRegionExp (New (r, _, _)) = r
  | getRegionExp (App (r, _, _)) = r
  | getRegionExp (Pair (r, _, _)) = r
  | getRegionExp (Proj (r, _, _)) = r
  | getRegionExp (Pop (r, _, _)) = r
  (* not used
  | getRegionExp (Fix (r, _)) = r
  *)
  | getRegionExp (PatVar (r, _, _)) = r
  | getRegionExp (TypeAscribe (r, _, _)) = r
  | getRegionExp (Sequence l) = 
		  let
		    fun getRegL [(r,_)] = r
		      | getRegL ((r,_)::xs) = Paths.join(r, getRegL xs) 
		      | getRegL _ = raise Domain
		  in
		    getRegL l
		  end
  | getRegionExp (LetFun (r, _, _)) = r
  | getRegionExp (ExtendFunWith (r, _, _, _, _, _, _)) = r

fun getRegionW (WorldEps (r, _, _)) = r
  | getRegionW (WorldType (r, _)) = r

fun getRegionC (Eps(r, _, _)) = r
  | getRegionC (NewC(r, _, _)) = r
  | getRegionC (Match(r, _, _)) = r

fun getRegionF (Top r) = r
  | getRegionF (All (r, _, _)) = r
  | getRegionF (Exists (r, _, _)) = r
  | getRegionF (Nabla (r, _, _)) = r
  | getRegionF (FormulaString (r, _)) = r
  | getRegionF (OmittedFormula r) = r


end (* structure DelphinIntermediateSyntax *)