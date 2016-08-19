(* Nabla Internal Syntax *)
(* Author: Adam Poswolsky and Carsten Schuermann *)

structure NablaIntSyntax =

struct

  exception NoSolution

  structure I = IntSyn

  datatype Formula
    = Inj of IntSyn.Exp
    | Imp of Formula * Formula
    | Box of Formula
    | And of Formula * Formula
    | TVar of (Formula option) ref
    | TClo of Formula * Sub

  and Exp
    = Quote  of IntSyn.Exp
    | Fail
    | App    of Exp * Exp 
    | Pair   of Exp * Exp 
    | First  of Exp
    | Second of Exp
    | FVar   of string * Formula (* used in abstractin phase *)
    | EVar   of (Dec I.Ctx)
                * (Exp option ref) * Formula 
              (* represents logic variables.
	       * Need the Formula here for use in abstractPsi of abstract.fun
	       *)

    | EClo   of Exp * (Sub list)
    | Some   of (string option) * IntSyn.Exp * Exp 
    | SomeM  of (string option) * Formula * Exp 

    | New    of (string option) * IntSyn.Exp * Exp 
    | Nabla  of (string option) * IntSyn.Exp * Exp 
    | Fix    of (string option) * Formula * Exp 
    | Case   of Exp * Formula * Exp  (* Formula is the type of the first Exp *)
    | Alt    of Exp * Exp 
    | Pop    of Exp 
    | Var    of int 

  and Dec
    = LFDec of IntSyn.Dec              
    (* changed to have a list of strings, to accomodate our mutual recursion
     * If it just has one element then it means it does not need to undergo a projection.
     * ABP -- 9/16/04
     *
     * | MetaDec of string option * Formula  
     *)
    | MetaDec of (string list) option * Formula 
    
  and Sub			(* Substitutions:             *)
    = Shift of int		(* t ::= ^n                   *)
    | Dot of Front * Sub	(*     | F . t                *)
  
  and Front			(* Fronts:                    *)
    = Idx of int		(* F ::= i                    *)
    | Prg of Exp option		(*     | p                    *)
    | Exp of IntSyn.Exp		(*     | U                    *)
    | Undef

  val id = Shift 0


  (* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)
  val invShift = Dot(Undef, id)


    
  (* isId s = B
     
   Invariant:
   If   G |- s: G', s weakensub
       then B holds 
	 iff s = id, G' = G
   *)
  fun isId' (Shift(k), k') = (k = k')
    | isId' (Dot (Idx(n), s'), k') =
         n = k' andalso isId' (s', k'+1)
    | isId' _ = false
  fun isId s = isId' (s, 0)

  fun isIdL [] = true
    | isIdL (x::xs) = (isId x) andalso (isIdL xs)



  fun newTVar() = TVar (ref NONE)
  fun newEVar(G,F) = EVar (G, ref NONE, F)
  fun newFVar(s,F) = FVar (s, F)

  fun coerceCtx I.Null = I.Null
    | coerceCtx (I.Decl (Psi, LFDec D)) = I.Decl (coerceCtx Psi, D)
    | coerceCtx (I.Decl (Psi, MetaDec _)) = I.Decl (coerceCtx Psi, I.NDec) 

  fun revCoerceCtx I.Null = I.Null
    | revCoerceCtx (I.Decl (Psi, D)) = I.Decl (revCoerceCtx Psi, LFDec D)


  fun coerceFront (Idx k) = I.Idx k 
    | coerceFront (Prg _) = I.Undef
    | coerceFront (Exp M) = I.Exp M
    | coerceFront (Undef) = I.Undef


  fun coerceSub (Shift n) = I.Shift n
    | coerceSub (Dot (Ft, t)) = I.Dot (coerceFront Ft, coerceSub t)

  fun decSub (LFDec d, s) = LFDec(I.decSub(d, coerceSub (hd s)))
    | decSub (X as MetaDec _, s) = X (* need to fix for dependent case! *)


  (* isPatSub s = B

     Invariant:
     If    G |- s : G' 
     and   s = n1 .. nm ^k
     then  B iff  n1, .., nm pairwise distinct
             and  ni <= k or ni = _ for all 1 <= i <= m
  *)
  fun isPatSub (Shift(k)) = true
    | isPatSub (Dot (Idx (n), s)) = 
    let fun checkBVar (Shift(k)) = (n <= k)
	  | checkBVar (Dot (Idx (n'), s)) = 
                n <> n' andalso checkBVar (s)
	  | checkBVar (Dot (Undef, s)) =
		checkBVar (s)
	  | checkBVar _ = false
    in
      checkBVar s andalso isPatSub s
    end
    | isPatSub (Dot (Undef, s)) = isPatSub s
    | isPatSub _ = false

  fun isPatSubL [] = true
    | isPatSubL (x::xs) = (isPatSub x) andalso (isPatSubL xs)
    

  (* bvarSub (n, s) = Ft'
      Invariant: 
     If    G |- s : G'    G' |- n : V
     then  Ft' = Ftn         if  s = Ft1 .. Ftn .. ^k
       or  Ft' = ^(n+k)     if  s = Ft1 .. Ftm ^k   and m<n
     and   G |- Ft' : V [s]
  *)
  fun bvarSub (1, Dot(Ft, s)) = Ft
    | bvarSub (n, Dot(Ft, s)) = bvarSub (n-1, s)
    | bvarSub (n, Shift(k))  = Idx (n+k)


  fun dot1 (t as Shift (0)) = t
    | dot1 t = Dot (Idx(1), comp(t, Shift 1))



(*
  and substF (Inj V, t::ts) = Inj (I.EClo (V, coerceSub t))
    | substF (Imp (F1, F2), t::ts) = Imp (substF (F1, t::ts), substF (F2, t::ts))

    (* ADAM:  CARSTEN I WANT THIS TO MAKE SENSE IN THE TOP CONTEXT *)
    | substF (Box F, t::ts) = Box (substF (F, t::ts))
    | substF (And (F1, F2), t::ts) = And (substF(F1,t::ts), substF(F2,t::ts))
    | substF (TVar X', t::ts) = TClo (TVar X', t::ts)
    | substF (TClo (F, tL), t::ts) = TClo(F, compL(tL,t::ts))
    | substF (F, []) = raise Domain
*)
(*
  and substF (Inj V, t) = Inj (I.EClo (V, coerceSub t))
    | substF (Imp (F1, F2), t) = Imp (substF (F1, t), substF (F2, t))
    | substF (Box F, t) = Box (substF (F, t))
    | substF (And (F1, F2), t) = And (substF(F1,t), substF(F2,t))
    | substF (TVar (X as ref NONE), t) = TClo (TVar X, t) 
    | substF (TVar (ref (SOME F)), t) = substF(F,t) 
    | substF (TClo (TVar (ref (SOME F)), t), t') = substF(substF(F, t), t')
    | substF (TClo (F, tL), t) = TClo(F, comp(tL,t))
*)
  and substF (F, T) = F (* No dependent types in this version! *)

  and varSub (1, Dot(Ft, t)) = Ft
    | varSub (n, Dot(Ft, t)) = varSub (n-1, t)
    | varSub (n, Shift(k))  = Idx (n+k)

  and frontSub (Idx  n, t) = varSub (n, t)
    | frontSub (Exp  U, t) = Exp (I.EClo (U, coerceSub t))
    | frontSub (Prg  (SOME P), t) = (Prg (SOME (subst (P, t))))
    | frontSub (Prg NONE, t) = Prg NONE
    | frontSub (Undef, t)  = Undef
    

  and comp (Shift (0), t) = t
    | comp (t, Shift (0)) = t
    | comp (Shift (n), Dot (Ft, t)) = comp (Shift (n-1), t)
    | comp (Shift (n), Shift (m)) = Shift (n+m)
    | comp (Dot (Ft, t), t') = Dot (frontSub (Ft, t'), comp (t, t'))

  and compL (t::ts, t'::ts') = comp(t,t') :: compL(ts, ts')
    | compL (ts, []) = ts
    | compL ([], ts) = ts


  and lfSub(false, M, t) = I.EClo(M, coerceSub t)
    | lfSub(true, M, t) = Whnf.normalize(M, coerceSub t)

  and subst' (b, Quote (M), t::ts) = Quote (lfSub(b, M, t))
    | subst' (b, Fail, _) = Fail
    | subst' (b, App (E1, E2), t::ts) = App (subst' (b, E1, t::ts), subst' (b, E2, t::ts))
    | subst' (b, Pair (E1, E2), t::ts) = Pair (subst' (b, E1,t::ts), subst'(b, E2, t::ts))
    | subst' (b, First(E), t::ts) = First (subst' (b, E, t::ts))
    | subst' (b, Second(E), t::ts) = Second (subst' (b, E, t::ts))
    | subst' (b, EVar (GX, X as ref NONE, F), t::ts) = EClo (EVar (GX, X, substF(F,t)), t::ts)
    | subst' (b, EVar (_, ref (SOME E), _), t::ts) = subst'(b, E, t::ts)
    | subst' (b, FVar (s, F), t::ts) = FVar(s, substF(F,t))

    | subst' (b, EClo (EVar (_, ref (SOME E), _), tL), t::ts) = subst'(b, subst'(b, E, tL), t::ts)
    | subst' (b, EClo (E, tL), t::ts) = EClo(E, compL(tL,t::ts))
    | subst' (b, Some (sO, V, E), t::ts) = Some (sO, lfSub(b, V, t), subst' (b, E, (dot1 t)::ts))
    | subst' (b, SomeM (sO, F, E), t::ts) = SomeM (sO, substF(F, t), subst' (b, E, (dot1 t)::ts))
    | subst' (b, New (sO, V, E), t::ts) = New (sO, lfSub(b, V,t), (subst' (b, E, (dot1 t)::t::ts)))
    | subst' (b, Nabla (sO, V, E), t::ts) = Nabla (sO, lfSub(b, V, t), (subst' (b, E, (dot1 t)::ts)))

    | subst' (b, Fix (sO, F, E), t::ts) = (Fix(sO, substF (F,t), subst' (b, E,(dot1 t)::ts)))
    | subst' (b, Case (E1, F, E2), t::ts) = Case (subst' (b, E1, t::ts), substF(F,t), subst' (b, E2, t::ts))

    | subst' (b, Alt (E1, E2), t::ts) = Alt (subst' (b, E1, t::ts), subst' (b, E2, t::ts))
    | subst' (b, Pop (E), t::ts) = Pop (subst' (b, E, ts))
    | subst' (b, Var (n), t::ts) = 
                                (case varSub (n, t)
				   of (Prg (SOME E)) => E
				 | (Idx i) => Var (i)
				 | (Prg NONE) => raise NoSolution

				   (* Looked up undefined value (or LF Exp) in context *)
				 | _ => raise Domain)

    | subst' (b, E, []) = E


  (* Note:  if subst is called on a substitution which has Prg (NONE) then it will raise
     NoSolution, otherwise no exceptions will ever be raised!
  *)

  and substL(E, ts) = subst'(false, E, ts)
  and subst(E, t) = subst'(false, E, [t])

  and substExact(E, t) = subst'(true, E, [t])



  (*
    (* Takes an Omega,Psi
     * returns a t such that
     *  Omega,Psi |-  t  : Omega
     *)
  fun createShifts [] = raise Domain
    | createShifts [_] = []
    | createShifts (Psi1::Psi2::Omega) =
           let
	     val t = Shift (I.ctxLength(Psi1) - I.ctxLength(Psi2))
	   in
	     t::createShifts(Psi2::Omega)
	   end
  *) 
  fun createID [] = []
    | createID (x::xs) = id :: createID(xs)

  

  (* weakenSub (G1, s, ss) = w'
   
     Invariant:
     If    G |- s : G1       (* s patsub *)
     and   G2 |- ss : G      (* ss strsub *)
     then  G1 |- w' : G1'    (* w' weaksub *)

       and   G2 |- w' o s o ss : G1'  is fully defined
       and   G1' is maximal such
    *)

    fun weakenSub (G, Shift n, ss) =
        if n < I.ctxLength G 
	  then weakenSub (G, Dot (Idx (n+1), Shift (n+1)), ss)
	else id
      | weakenSub (G, Dot (Idx n, s'), ss) =
        (case bvarSub (n, ss)
 	   of Undef => comp (weakenSub (G, s', ss), Shift 1)
	    | Idx _ => dot1 (weakenSub (G, s', ss))
	    (* no other cases, ss is strsub *)
	    | _ => raise Domain)

      | weakenSub (G, Dot (Undef, s'), ss) =
	   comp (weakenSub (G, s', ss), Shift 1)
      | weakenSub _ = raise Domain (* no other case possible *)

    fun weakenSubL (G, [], []) = []
      | weakenSubL (G, x::xs, []) = weakenSubL (G, x::xs, [id])
      | weakenSubL (G, [], x::xs) = weakenSubL (G, [id], x::xs)
      | weakenSubL (G, x::xs, y::ys) = weakenSub(G, x, y) :: weakenSubL(G, xs, ys)

(* REPLACED with more robust inverse below

  (* Invert Sub
   * Psi' |- t: Psi
   * Returns t'
   * such that
   * Psi |- t' : Psi'
   *)

  (* Substitution Properties:
   *   Psi' |-  a o b : Psi
   * then
   *   Psi |- b(-1) o a(-1) : Psi'
   *
   * Proof:
   * By assumption,
   *   PsiA |- a : Psi
   *   Psi' |- b : PsiA
   *   So,  Psi' |- a o b : Psi
   * Therefore,
   *   PsiA |- b(-1) : Psi'
   *   Psi  |- a(-1) : PsiA
   *   So,  Psi  |- b(-1) o a(-1) : Psi'
   *)

  fun invertSub (Shift 0) = Shift 0
    | invertSub (Shift i) = 
         (* Psi, x |- Shift 1 : Psi *)
         (* Psi   |- Undef.id : Psi,x *)
	(* Inverse of Shift 1 is Undef.id *)
        (* Shift i  = Shift 1 o Shift(i-1) *)
        comp(invertSub(Shift(i-1)), Dot(Undef, Shift 0))
    | invertSub (Dot(Undef, Shift 0)) = Shift 1
    | invertSub (Dot(Undef, t)) 
	(* Undef.t = Undef.id o t *)
	(* inverse of Undef.id is Shift 1 *)
	= comp(invertSub(t), Shift 1)

    | invertSub(Dot(Idx 1, t)) = 
	let
	  val t1' = comp(invertSub(t), Shift 1)
	  fun replaceFirstUndef(Dot(Undef, t)) = Dot(Idx 1, t)
	    | replaceFirstUndef t = t
	in
	  replaceFirstUndef(t1')
	end
	
    | invertSub (Dot(Idx i, t)) =
	(*i.t == (1.(t o Shift1)) o (i.id) *)
	let
	  val t1 = Dot(Idx 1, comp(t, Shift 1))
	  val t2 = Dot(Idx i, Shift 0)
	    (* In order for this to make sense,
	     * Idx i must really not be used (i.e. it is equiv. to Undef *)
	  val t2Inv = Shift 1 
	  val t1Inv = invertSub(t1)
	in
	  comp(t2Inv, t1Inv)
	end
	
	
    | invertSub _ = raise Domain (* cannot be inverted *)
*)



    (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id  
    *)
    fun invertSub s =
      let 
	fun lookup (n, Shift _, p) = NONE
	  | lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
	  | lookup (n, Dot (Idx k, s'), p) = 
	      if k = p then SOME n 
	      else lookup (n+1, s', p)
	  | lookup _ = raise Domain (* no other case possible *)
	
	fun invertSub'' (0, si) = si
	  | invertSub'' (p, si) = 
	    (case (lookup (1, s, p))
	       of SOME k => invertSub'' (p-1, Dot (Idx k, si))
	        | NONE => invertSub'' (p-1, Dot (Undef, si)))
	       
	fun invertSub' (n, Shift p) = invertSub'' (p, Shift n)
	  | invertSub' (n, Dot (_, s')) = invertSub' (n+1, s')
      in
	invertSub' (0, s)
      end



  val invertSubL = map invertSub


    (* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G    (* and t strsub *)
       then G' |- t : G  and G' subcontext of G
    *)
    fun strengthen (Shift n (* = 0 *), I.Null) = I.Null
      (* what makes you think k = 1??? *)
      | strengthen (Dot (Idx k (* k = 1 *), t), I.Decl (G, D)) =
        let 
	  val t' = comp (t, invShift)
	in
	  (* G |- D dec *)
          (* G' |- t' : G *)
	  (* G' |- D[t'] dec *)

	  (* fix for dependent case, don't like this [t'] - ADAM *)
          I.Decl (strengthen (t', G), decSub (D, [t']))
	end
      | strengthen (Dot (Undef, t), I.Decl (G, D)) = 
          strengthen (t, G)
      | strengthen (Shift n, G) = 
	  strengthen (Dot (Idx (n+1), Shift (n+1)), G)
      | strengthen _ = raise Domain (* no other case possible *)


end

