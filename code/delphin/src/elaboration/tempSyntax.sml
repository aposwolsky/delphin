(* Delphin Temporary Intermediate Syntax 
 * Used during conversion from external 
 * to internal syntax
 *)
(* Author: Adam Poswolsky *)

structure DelphinIntermediateSyntax = 
struct
structure I = IntSyn

datatype Types
  = LF of Paths.region * DelphinIntSyntax.isParam * I.Exp
  | Meta of Paths.region * DelphinIntSyntax.isParam * Formula

and Formula
  = Top     of Paths.region
  | All     of Paths.region * DelphinIntSyntax.Visibility * NormalDec * Formula
  | Exists  of Paths.region * NormalDec * Formula 
  | Nabla   of Paths.region * NewDec * Formula
  | FormulaString of Paths.region * string
  | OmittedFormula of Paths.region 
  

and NormalDec 
  = NormalDec of Paths.region * (string option) * Types

  
and NewDec 
  = NewDecLF of Paths.region * (string option) * I.Exp
  | NewDecMeta of Paths.region * (string option) * Formula

and Dec
  = InstantiableDec of Paths.region * NormalDec    
  | NonInstantiableDec of Paths.region * NewDec


and Exp
  = VarInt    of Paths.region * int 
  | Quote  of Paths.region * I.Exp * I.Exp * DelphinApprox.SmartInj * DelphinIntSyntax.isParam (* (U : V)  *)
  | Unit   of Paths.region
  | Lam    of Paths.region * (CaseBranch list)
  | New    of Paths.region * NewDec * Exp
  | App    of Paths.region * DelphinIntSyntax.Visibility * Exp * Exp
  | Pair   of Paths.region * Exp * Exp
  | Proj   of Paths.region * Exp * int
  | Pop    of Paths.region * int * Exp
  | Fix    of Paths.region * (Paths.region * NormalDec * Exp) list 
             (* Not in use from the actual parser.. as embedded fixpoints are introduced with let.
	      * But it is useful to have  for converting internal syntax to external one *)

  | PatVar of Paths.region * string

  (* Syntactic Sugar *)
  | TypeAscribe of Paths.region * Exp * Types
  | Sequence of (Paths.region * Exp) list
  (* Removed.. now translated before this stage
  | LiftedApp of Paths.region * Exp * I.Exp * Exp * I.Exp  * I.Exp
                            (*  E1    typeE1   E2   typeE2  typeResult *)
  | LetVar of Paths.region * NormalDec * Exp * Exp
  *)
  | LetFun of Paths.region * (Paths.region * NormalDec * Exp) list * Exp
  | ExtendFun of Paths.region * Exp * (CaseBranch list)

  
               
and CaseBranch
    = Eps of Paths.region * NormalDec * CaseBranch
    | NewC of Paths.region * NewDec * CaseBranch
    | PopC of Paths.region * int * CaseBranch
    | Match of Paths.region * DelphinIntSyntax.Visibility * Exp * Exp (* pattern => result *)
    | MatchAnd of Paths.region * DelphinIntSyntax.Visibility * Exp * CaseBranch (* pattern => case *)



(* ********************************************** *)
(* Substitutions (Used in abstract.fun *)
(* We only support pattern substitutions on the intermediate
 * syntax....  we could generalize to more.. but is it necessary? 
 *)
datatype Sub 
  = Shift of Sub
  | Dot of int * Sub (* Just a pattern substitution.. no arbitrary front *)
  | id



(* Functions / Substitution Application *)

fun shift (0) = id
  | shift (i) = Shift (shift(i-1))

fun dot1 (id) = id
  | dot1 t = Dot (1, Shift t)

fun substF(Top r, t) = Top r
  | substF(All (r, visible, D, F), t) = All (r, visible, substNormalDec(D, t), substF(F, I.dot1 t))
  | substF(Exists (r, D, F), t) = Exists (r, substNormalDec(D, t), substF(F, I.dot1 t))
  | substF(Nabla (r, D, F), t) = Nabla (r, substNewDec(D, t), substF(F, I.dot1 t))
  | substF(FormulaString (r, s), t) = FormulaString(r,s) (* Type Aliases occurs on the top-level, so 
							  * the type referred to by "s" makes sense in the empty context without any EVars *)
  | substF(OmittedFormula r, t) = OmittedFormula r

and substTypes(LF (r, isP, A), t) = LF (r, isP, I.EClo(A, t))
  | substTypes(Meta (r, isP, F), t) = Meta (r, isP, substF(F, t))

and substNormalDec (NormalDec (r, name, T), t) = NormalDec(r, name, substTypes(T,t))
and substNewDec (NewDecLF (r, name, A), t) = NewDecLF (r, name, I.EClo(A, t))
  | substNewDec (NewDecMeta (r, name, F),t) = NewDecMeta (r, name, substF(F, t))


fun coerceSub (id) = I.id
  | coerceSub (Shift t) = I.comp(coerceSub t, I.shift)
  | coerceSub (Dot (i, t)) = I.Dot (I.Idx i, coerceSub t)

(* see intSyntax.sml *)
fun popSub (i, Shift t) =
        let 
	  val (j, t') = popSub (i, t)
	in 
	  (j+1, t')
	end
  | popSub (i, id) = (i, id)
  | popSub (1, Dot(1, Shift t)) = (1, t)
  | popSub (1, _) = raise Domain (* substitution not well-typed *)
  | popSub (i, Dot(_, t)) = popSub(i-1, t)


fun substCase (Eps (r, D, C), t) = Eps (r, substNormalDec(D, coerceSub t), substCase(C, dot1 t))
  | substCase (NewC (r, D, C), t) = NewC (r, substNewDec(D, coerceSub t), substCase(C, dot1 t))
  | substCase (PopC (r, i, C), t) = 
                           let val (j, t') = popSub(i, t)
			   in
			     PopC (r, j, substCase(C,t'))
			   end
  | substCase (Match (r, visible, patE, resE), t) = Match (r, visible, substE(patE, t), substE(resE, t))
  | substCase (MatchAnd (r, visible, patE, C), t) = MatchAnd (r, visible, substE(patE, t), substCase(C, t))


and substE(E, id) = E
  | substE(VarInt (r,1), Dot(j, t)) = VarInt (r, j)
  (*  | substE(VarInt (r,1), Dot(Undef, t)) = raise SubstFailed  *)
  | substE(VarInt (r,i), Dot(_, t)) = substE(VarInt (r,(i-1)), t)
  | substE(VarInt (r,i), Shift id) = VarInt (r, i+1)
  | substE(VarInt (r,i), Shift t) = substE(substE(VarInt (r,i), t), Shift id)
  | substE(Quote (r,M,A, I, isP), t) = 
             let 
	       val t' = coerceSub t
	     in
	       Quote (r, I.EClo(M, t'), I.EClo(A, t'), I, isP)
	     end

  | substE(Unit r, _) = Unit r
  | substE(Lam (r, Clist), t) = 
                        let
			  val Clist' = map (fn C => substCase(C, t)) Clist
			in
			  Lam (r, Clist')
			end


  | substE(New (r, D, E), t) = New (r, substNewDec(D, coerceSub t), substE (E, dot1 t))
  | substE(App (r, visible, E1, E2), t) = App (r, visible, substE(E1, t), substE(E2, t))
  | substE(Pair (r, E1, E2), t) = Pair (r, substE(E1, t), substE(E2, t))

  | substE(Proj (r, E,i), t) = Proj(r, substE(E,t), i)
			
  | substE(Pop (r, i, E), t) = 
	   let val (j, t') = popSub(i, t)
	   in
	     Pop (r, j, substE(E,t'))
	   end

  | substE(Fix (r, funList), t) = Fix (r, substFunList(funList, t))

  | substE(PatVar (r, s), t) = PatVar (r, s)

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

  | substE(ExtendFun (r, E, Clist), t) = ExtendFun (r,
						    substE(E, t),
						    map (fn C => substCase(C, t)) Clist)
								  


and substFunList ([], t) = []
  | substFunList ((r,D,E)::funlist, t) = (r, substNormalDec(D, coerceSub t), substE(E, dot1 t)) :: substFunList(funlist, t)


end (* structure DelphinIntermediateSyntax *)