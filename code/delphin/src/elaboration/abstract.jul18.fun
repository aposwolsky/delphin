(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga  *)
(* Modified: Adam Poswolsky *)
(* ABP:  Important difference from Twelf is that collection does not collect necessarily
 *       ALL Vars.. only those specified.  Otherwise it remains as a Var
 * Additionally:  raiseX does NOT raise NDecs....!!!
*)

functor DelphinAbstract (structure Whnf    : WHNF
		       structure Constraints : CONSTRAINTS
			 )
  : DELPHINABSTRACT =
struct

    exception Error of Paths.region * string
    exception LeftOverConstraints of (Paths.region * IntSyn.cnstr list) list


    structure I = IntSyn
    structure C = Constraints
    structure D = DelphinIntermediateSyntax

    val Existential = DelphinExtSyntax.Existential
    val Param = DelphinExtSyntax.Param

    (* Intermediate Data Structure *)

    datatype EFLPVar =
      EV of Paths.region * I.Exp			 (* Y ::= X         for  GX |- X : VX   *)
    | FV of Paths.region * string * bool * I.Exp 	 (*     | (F, b, V)        if . |- F : V  *)
                                                         (*              and b is true if it is a parameter *)
    | LV of Paths.region * I.Block                       (*     | L             if . |- L in W  *) 
    | PV of Paths.region * string                        (*     | PatVar (Delphin)              *)


    (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
    fun collectConstraints (I.Null) = nil
      | collectConstraints (I.Decl (G, FV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, LV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, PV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, EV (_, I.EVar (_, _, _, ref nil)))) = collectConstraints G
      | collectConstraints (I.Decl (G, EV (r, I.EVar (_, _, _, ref cnstrL)))) =
               let
		 val constraints = C.simplify cnstrL
	       in
		 case constraints of
		   nil => collectConstraints G
		   | _ => (r, constraints) :: (collectConstraints G)
	       end
      | collectConstraints (I.Decl (G, EV _)) = raise Domain (* A non EVar stored in EV.. *)

    (* checkConstraints (K) = ()
       Effect: raises LeftOverConstraints(C) if K contains unresolved constraints
    *)
    fun checkConstraints (K) =
        let
	  val constraints = collectConstraints K
	  val _ = case constraints
	            of nil => ()
		     | _ => raise LeftOverConstraints (constraints)
	in
	  ()
	end

    (*
       We write {{K}} for the context of K, where EVars, FVars, LVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and FVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or FVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)



    (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
    fun eqEVar (I.EVar (r1, _, _, _)) (EV (_, I.EVar (r2, _, _, _))) = (r1 = r2)
      | eqEVar _ _ = false

    (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
    fun eqFVar (I.FVar (n1, _, _, _)) (FV (_, n2, _,  _)) = (n1 = n2)
      | eqFVar _ _ = false

    (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
    fun eqLVar (I.LVar ((r1, _, _))) (LV (_, I.LVar ((r2, _, _)))) = (r1 = r2)
      | eqLVar _ _ = false

    (* eqPatVar *)
    fun eqPatVar (D.PatVar (_, n1)) (PV (_,n2)) = (n1 = n2)
      | eqPatVar _ _ = false



    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    fun exists P K =
        let fun exists' (I.Null) = false
	      | exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K')
	in
	  exists' K
	end


      
      

    (* this should be non-strict *)
    (* perhaps the whole repeated traversal are now a performance
       bottleneck in PCC applications where logic programming search
       followed by abstraction creates certificates.  such certificates
       are large, so the quadratic algorithm is not really acceptable.
       possible improvement, collect, abstract, then traverse one more
       time to determine status of all variables.
    *)
    (* Wed Aug  6 16:37:57 2003 -fp *)
    (* !!! *)
    fun or (I.Maybe, _) = I.Maybe
      | or (_, I.Maybe) = I.Maybe
      | or (I.Meta, _) = I.Meta
      | or (_, I.Meta) = I.Meta
      | or (I.No, I.No) = I.No
      
    (* occursInExp (k, U) = DP, 

       Invariant:
       If    U in nf 
       then  DP = No      iff k does not occur in U
	     DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
	     DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
    fun occursInExp (k, I.Uni _) = I.No
      | occursInExp (k, I.Pi (DP, V)) = or (occursInDecP (k, DP), occursInExp (k+1, V))
      | occursInExp (k, I.Root (H, S)) = occursInHead (k, H, occursInSpine (k, S))
      | occursInExp (k, I.Lam (D, V)) = or (occursInDec (k, D), occursInExp (k+1, V))
      | occursInExp (k, I.FgnExp csfe) =
	I.FgnExpStd.fold csfe (fn (U, DP) => or (DP, (occursInExp (k, Whnf.normalize (U, I.id))))) I.No

      (* no case for Redex, EVar, EClo *)
      (* ABP:  What is guaranteeing that this is in whnf??? *)	
      | occursInExp _ = I.Maybe (* If it is an EVar.. lets's just say Maybe... *)


    and occursInHead (k, I.BVar (I.Fixed k'), DP) = 
        if (k = k') then I.Maybe
	else DP
      | occursInHead (k, I.Const _, DP) = DP
      | occursInHead (k, I.Def _, DP) = DP
      | occursInHead (k, I.Proj _, DP) = DP   
      | occursInHead (k, I.FgnConst _, DP) = DP
      | occursInHead (k, I.Skonst _, I.No) = I.No
      | occursInHead (k, I.Skonst _, I.Meta) = I.Meta
      | occursInHead (k, I.Skonst _, I.Maybe) = I.Meta
      | occursInHead _ = I.Maybe (* if it is a FVar we just return maybe *)

    and occursInSpine (_, I.Nil) = I.No
      | occursInSpine (k, I.App (U, S)) = or (occursInExp (k, U), occursInSpine (k, S))
      (* no case for SClo *) 
      | occursInSpine _ = I.Maybe (* If it is not needed, it can't hurt.. *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
      | occursInDec (k, I.NDec) = I.No
      | occursInDec _ = raise Domain

    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise 
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    fun piDepend (DPV as ((D, I.No), V)) = I.Pi DPV
      | piDepend (DPV as ((D, I.Meta), V)) = I.Pi DPV
      | piDepend ((D, I.Maybe), V) = 
	  I.Pi ((D, occursInExp (1, V)), V)
	
    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, I.NDec), V) = raise Domain (* raiseType (G, I.EClo(V, I.shift)) *)
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))


    (* collectExpW ((U, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
	     where K'' contains all EVars and FVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)

fun LFcollectExp (reg, (U, s), K, allowVars) =
  (* if allowVars then collect all EVars/FVars,
   * otherewise just check that there are no vars not in K.
   *)
  let
    fun collectExpW ((I.Uni L, s), K) = K
      | collectExpW ((I.Pi ((D, _), V), s), K) =
          collectExp ((V, I.dot1 s), collectDec ((D, s), K))
      | collectExpW ((I.Root (F as I.FVar (name, isP, V, s'), S), s), K) =
	if exists (eqFVar F) K
	  then collectSpine ((S, s), K)
	else (* s' = ^|G| *)
	  if allowVars then
	    collectSpine ((S, s), I.Decl (collectExp ((V, I.id), K), FV (reg, name, isP, V)))
	  else
	    raise Error (reg, "Variable " ^ name ^ " not defined.")
      | collectExpW ((I.Root (I.Proj (L as I.LVar (r, _, (l, t)), i), S), s), K) =
	if exists (eqLVar L) K
	  (* note: don't collect t again below *)
	  (* was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) *)
	  (* Sun Dec 16 10:54:52 2001 -fp !!! *)
	  then collectSpine ((S, s), K)
	else 
	  if allowVars then
	    (* -fp Sun Dec  1 21:12:12 2002 *)
	    collectSpine ((S, s), I.Decl (collectSub (I.comp(t,s), K), LV (reg, L)))
	  else
	    raise Error (reg, "Ambiguous Term (Leftover LVar)")

      | collectExpW ((I.Root (_ , S), s), K) =
	  collectSpine ((S, s), K)
      | collectExpW ((I.Lam (D, U), s), K) =
	  collectExp ((U, I.dot1 s), collectDec ((D, s), K))
      | collectExpW ((X as I.EVar (r, GX, V, cnstrs), s), K) =
	if exists (eqEVar X) K
	  then collectSub(s, K)
	else 
	  if allowVars then
	     let
	       (* val _ = checkEmpty !cnstrs *)
	       val V' = raiseType (GX, V) (* inefficient *)
	       val K' = collectExp ((V', I.id), K)
	     in
	       collectSub(s, I.Decl (K', EV (reg, X)))
	     end
	   else
	     raise Error (reg, "Ambiguous Term (Leftover EVar)")


      | collectExpW ((I.FgnExp csfe, s), K) =
	  I.FgnExpStd.fold csfe (fn (U, K) => collectExp ((U, s), K)) K
      (* No other cases can occur due to whnf invariant *)
      | collectExpW _ = raise Domain

    (* collectExp (G, (U, s), K) = K' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (Us, K) = collectExpW (Whnf.whnf Us, K)

    (* collectSpine ((S, s), K) = K' 

       Invariant: 
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
    and collectSpine ((I.Nil, _), K) = K
      | collectSpine ((I.SClo(S, s'), s), K) = 
          collectSpine ((S, I.comp (s', s)), K)
      | collectSpine ((I.App (U, S), s), K) =
	  collectSpine ((S, s), collectExp ((U, s), K))

    (* collectDec ((x:V, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
    and collectDec ((I.Dec (_, V), s), K) =
          collectExp ((V, s), K)
      | collectDec ((I.BDec (_, (_, t)), s), K) =
	  (* . |- t : Gsome, so do not compose with s *)
	  (* Sat Dec  8 13:28:15 2001 -fp *)
	  collectSub (t, K)

      (* ABP -- added NDec *)
      | collectDec ((I.NDec, s), K) = K
      | collectDec _ = raise Domain

    (*
       Invariant: 
       If    G |- s : G1    
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    and collectSub (I.Shift _, K) = K
      | collectSub (I.Dot (I.Idx _, s), K) = collectSub (s, K)
      | collectSub (I.Dot (I.Exp (U), s), K) =
	  collectSub (s, collectExp ((U, I.id), K))
      | collectSub (I.Dot (I.Block B, s), K) =
	  collectSub (s, collectBlock (B, K))
      | collectSub _ = raise Domain
    (* next case should be impossible *)
    (*
      | collectSub (I.Dot (I.Undef, s), K) =
          collectSub (s, K)
    *)

    (* collectBlock (B, K) where G |- B block *)
    and collectBlock (I.LVar (ref (SOME B), sk , _), K) =
          collectBlock (I.blockSub (B, sk), K)
          (* collectBlock (B, K) *)
          (* correct?? -fp Sun Dec  1 21:15:33 2002 *)
      | collectBlock (L as I.LVar (_, sk, (l, t)), K) = 
        if exists (eqLVar L) K
	  then collectSub (t, K)
	else 
	  if allowVars then
	    I.Decl (collectSub (t, K), LV (reg, L))
	  else
	    raise Error (reg, "Ambiguous Term (Leftover LVar)")

      | collectBlock _ = raise Domain
    (* | collectBlock (I.Bidx _, K) = K *)
    (* should be impossible: Fronts of substitutions are never Bidx *)
    (* Sat Dec  8 13:30:43 2001 -fp *)

  in
    collectExp((U, s), K)
  end



    (* abstractEVar (K, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractEVar (I.Decl (K', EV (_, I.EVar(r',_,_,_))), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then SOME(I.BVar (I.Fixed (depth+1)))
	else abstractEVar (K', depth+1, X)
      | abstractEVar (I.Decl (K', _), depth, X) = 
	  abstractEVar (K', depth+1, X)
      | abstractEVar (I.Null, _, _) = NONE

    (* abstractFVar (K, depth, F) = C'
     
       Invariant:
       If   G |- F : V
       and  F occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractFVar (I.Decl(K', FV (_, n', _, V')), depth, F as I.FVar (n, _, V, s)) = 
	  if n = n' then (I.BVar (I.Fixed (depth+1)))
	  else abstractFVar (K', depth+1, F)
      | abstractFVar (I.Decl(K', _), depth, F) =
  	  abstractFVar (K', depth+1, F)
      | abstractFVar (I.Null, _, F) = F
       
    (* abstractLVar (K, depth, L) = C'
     
       Invariant:
       If   G |- L : V
       and  L occurs in K  at kth position (starting at 1)
       then C' = Bidx (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractLVar (I.Decl(K', LV (_, I.LVar (r', _, _))), depth, L as I.LVar (r, _, _)) = 
	  if r = r' then (I.Bidx (depth+1))
	  else abstractLVar (K', depth+1, L)
      | abstractLVar (I.Decl(K', _), depth, L) =
  	  abstractLVar (K', depth+1, L)
      | abstractLVar (I.Null, _, L) = L


    (* Abstract Delphin (meta-level) pattern variables *)
    fun abstractPatVar (I.Decl(K', PV (_, n1)), depth, P as D.PatVar(r, n2)) =
          if n1 = n2 then D.VarInt(r, depth+1)
	  else abstractPatVar (K', depth+1, P)
      | abstractPatVar (I.Decl(K', _), depth, P) =
	    abstractPatVar (K', depth+1, P)
      | abstractPatVar (I.Null, _, P) = P


    (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G1,{{K}},G2 |- U[s] : V[s] (and in whnf)
       and   K is internal context in dependency order
       and   |G2| = depth
       and   K',K ||- U and K',K ||- V
       then  G1,{{K}},G2 |- U' : V'
       and   K' ||- U' and K' ||- V'
       and   U' is in nf 
    *)
    fun abstractExpW (K, depth, (U as I.Uni (L), s)) = U
      | abstractExpW (K, depth, (I.Pi ((D, P), V), s)) =
          piDepend ((abstractDec (K, depth, (D, s)), P), 
		    abstractExp (K, depth + 1, (V, I.dot1 s)))
      | abstractExpW (K, depth, (I.Root (F as I.FVar _, S), s)) =
	  I.Root (abstractFVar (K, depth, F), 
		  abstractSpine (K, depth, (S, s)))
      | abstractExpW (K, depth, (I.Root (I.Proj (L as I.LVar _, i), S), s)) =
	  I.Root (I.Proj (abstractLVar (K, depth, L), i),  
		  abstractSpine (K, depth, (S, s)))
      | abstractExpW (K, depth, (I.Root (H, S) ,s)) =
	  I.Root (H, abstractSpine (K, depth, (S, s)))   
      | abstractExpW (K, depth, (I.Lam (D, U), s)) =
          I.Lam (abstractDec (K, depth, (D, s)),
		 abstractExp (K, depth + 1, (U, I.dot1 s)))
      | abstractExpW (K, depth, (X as I.EVar _, s)) =
	  let 
	    val Hopt = abstractEVar (K, depth, X)
	  in
	    case Hopt
	      of NONE => I.EClo(X, abstractSubToSub(K, depth, s)) 
	       | SOME H => I.Root(H, abstractSub (K, depth, s, I.Nil))
	  end
      | abstractExpW (K, depth, (I.FgnExp csfe, s)) =
          I.FgnExpStd.Map.apply csfe (fn U => abstractExp (K, depth, (U, s)))
      | abstractExpW _ = raise Domain

    (* abstractExp (K, depth, (U, s)) = U'
     
       same as abstractExpW, but (U,s) need not to be in whnf 
    *)
    and abstractExp (K, depth, Us) = abstractExpW (K, depth, Whnf.whnf Us)

    and abstractSubToSub (K, depth, s as I.Shift _) = s
      | abstractSubToSub (K, depth, I.Dot(I.Idx k, s)) = I.Dot(I.Idx k, abstractSubToSub (K, depth, s))
      | abstractSubToSub (K, depth, I.Dot(I.Exp U, s)) = I.Dot(I.Exp (abstractExp(K, depth, (U, I.id))), abstractSubToSub (K, depth, s))
      | abstractSubToSub (K, depth, I.Dot(I.Block B, s)) = I.Dot(I.Block (abstractBlock(K, depth, (B, I.id))), abstractSubToSub (K, depth, s))
      | abstractSubToSub (K, depth, I.Dot(I.Undef, s)) = I.Dot(I.Undef, abstractSubToSub (K, depth, s))
      
    and abstractBlock (K, depth, B) = raise Domain (* ADAM:  We don't need blocks anymore.. right??? *)

    (* abstractSub (K, depth, s, S) = SS
     *
     * If  G' |- s : GX
     * and G' |- S is a spine of types A1...An
     * and |G'|=depth 
     *
     * then G' |- SS is a spine of types GX A1...An
     *)
     
    and abstractSub (K, depth, I.Shift (k), S) = S
(*	if k < depth
	  then abstractSub (K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S)
	else (* k = depth *) S
*)
      | abstractSub (K, depth, I.Dot (I.Idx (k), s), S) =
	  (* G' |- k.s : GX,A
	   * G' |- S is a spine of types A1...An
	   *
	   * G' |- s : GX
	   * G' |- k@S is a spine of types A,A1...An
	   *)
	  abstractSub (K, depth, s, I.App (I.Root (I.BVar (I.Fixed k), I.Nil), S))
      | abstractSub (K, depth, I.Dot (I.Exp (U), s), S) =
	  abstractSub (K, depth, s, I.App (abstractExp (K, depth, (U, I.id)), S))
      | abstractSub _ = raise Domain
 
    and abstractSpine (K, depth, (I.Nil, _))  = I.Nil 
      | abstractSpine (K, depth, (I.SClo (S, s'), s)) = 
	  abstractSpine (K, depth, (S, I.comp (s', s)))
      | abstractSpine (K, depth, (I.App (U, S), s)) =
	  I.App (abstractExp (K, depth, (U ,s)), 
		 abstractSpine (K, depth, (S, s)))

    and abstractDec (K, depth, (I.Dec (x, V), s)) =
	  I.Dec (x, abstractExp (K, depth, (V, s)))
      | abstractDec (K, depth, (I.NDec, s)) = I.NDec
      | abstractDec _ = raise Domain

    fun abstractSOME (K, I.Shift 0) = (* n = 0 by invariant, check for now *)
          I.Shift (I.ctxLength(K))
      | abstractSOME (K, I.Shift (n)) = (* n > 0 *)
	  I.Shift (I.ctxLength(K))
      | abstractSOME (K, I.Dot (I.Idx k, s)) = 
          I.Dot (I.Idx k, abstractSOME (K, s))
      | abstractSOME (K, I.Dot (I.Exp U, s)) =
	  I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractSOME (K, s))
      | abstractSOME (K, I.Dot (I.Block (L as I.LVar _), s)) =
	  I.Dot (I.Block (abstractLVar (K, 0, L)), abstractSOME (K, s))
      (* I.Block (I.Bidx _) should be impossible as head of substitutions *)
      | abstractSOME _ = raise Domain



    fun abstractKAll (I.Null, F, ~1) = F
      | abstractKAll (I.Null, F, numShifts) = raise Domain (* numShifts should be ~1 *)
      | abstractKAll (I.Decl (K', EV (r, I.EVar (_, GX, VX, _))), F, numShifts) =
        let
          val V' = raiseType (GX, VX) 
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
          (* enforced by reconstruction -kw
	  val _ = checkType V''	*)
	in	 
	  abstractKAll (K', D.All (r, DelphinExtSyntax.Implicit, D.NormalDec(r, NONE, D.LF(r, Existential, V'')), F), numShifts-1)
	end
      | abstractKAll (I.Decl (K', FV (r, name,isP, V')), F, numShifts) =
	let
	  val isP' = if isP then Param else Existential
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
          (* enforced by reconstruction -kw
	  val _ = checkType V'' *)
	in
	  abstractKAll (K', D.All (r, DelphinExtSyntax.Implicit, D.NormalDec(r, SOME name, D.LF(r, isP', V'')), F), numShifts-1)
	end
      | abstractKAll (I.Decl (K', LV (_, I.LVar (r, _, (l, t)))), F, _) = raise Domain (* Can't handle blocks *)
      | abstractKAll (I.Decl (K', PV (r,name)), F, numShifts) = abstractKAll (K', D.All(r, DelphinExtSyntax.Implicit, D.NormalDec(r, SOME name, D.Meta(r, Existential, D.OmittedFormula r)), F), numShifts-1)
      | abstractKAll _ = raise Domain



    fun abstractKdec (K, D.NormalDec(r, sO, D.Meta(r2,isP, F)), numShifts) = D.NormalDec(r, sO, D.Meta(r2, isP, abstractKAll (K, F, numShifts)))
      | abstractKdec _ = raise Domain (* broken invariant *)

    fun abstractKEps (I.Null, C, ~1) = C
      | abstractKEps (I.Null, C, numShifts) = raise Domain (* numShifts should be ~1 *)
      | abstractKEps (I.Decl (K', EV (r, I.EVar (_, GX, VX, _))), C, numShifts) =
        let
          val V' = raiseType (GX, VX) 
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
          (* enforced by reconstruction -kw
	  val _ = checkType V''	*)
	in	 
	  abstractKEps (K', D.Eps (r, D.NormalDec(r, NONE, D.LF(r, Existential, V'')), C), numShifts-1)
	end
      | abstractKEps (I.Decl (K', FV (r, name,isP, V')), C, numShifts) =
	let
	  val isP' = if isP then Param else Existential
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
          (* enforced by reconstruction -kw
	  val _ = checkType V'' *)
	in
	  abstractKEps (K', D.Eps (r, D.NormalDec(r, SOME name, D.LF(r, isP', V'')), C), numShifts-1)
	end
      | abstractKEps (I.Decl (K', LV (_, I.LVar (r, _, (l, t)))), C, _) = raise Domain (* Can't handle blocks *)
      | abstractKEps (I.Decl (K', PV (r,name)), C, numShifts) = abstractKEps (K', D.Eps(r, D.NormalDec(r, SOME name, D.Meta(r, Existential, D.OmittedFormula r)), C), numShifts-1)
      | abstractKEps _ = raise Domain




    (* Abstraction of Delphin Terms 
     * *************************************************************************
     * *************************************************************************
     *)

    (* abstractDelExp(K, depth, E) = E'
     * If G1,{{K}},G2 |- E : T
     * and K',K ||- E
     * then G1,{{K}},G2 |- E' : T'
     * and K' ||- E'
     *)
    and abstractDelExp (K, depth, E as D.VarInt _) = E
      | abstractDelExp (K, depth, D.Quote (r, U, A, I)) = D.Quote (r, abstractExp(K, depth, (U, I.id)), 
								       abstractExp(K, depth, (A, I.id)),
								       I)

      | abstractDelExp (K, depth, E as D.Unit _) = E
      | abstractDelExp (K, depth, D.Lam (r, Clist)) =
              let
		fun abstractC C = abstractDelCaseBranch(K, depth, C)
		val Clist' = map abstractC Clist
	      in
		D.Lam (r, Clist')
	      end

      | abstractDelExp (K, depth, D.New (r, D, E)) = D.New (r, abstractDelNewDec (K, depth, D),
							     abstractDelExp(K, depth+1, E))

      | abstractDelExp (K, depth, D.App (r, visible, E1, E2)) = D.App (r, visible, abstractDelExp(K, depth, E1),
							       abstractDelExp(K, depth, E2))

      | abstractDelExp (K, depth, D.Pair (r, E1, E2)) = D.Pair (r, abstractDelExp(K, depth, E1),
								 abstractDelExp(K, depth, E2))

      | abstractDelExp (K, depth, D.Proj (r, E, i)) = D.Proj(r,
							      abstractDelExp(K, depth, E),
							      i)
	      
      | abstractDelExp (K, depth, D.Pop (r, i, E)) = 
	      if (i > depth) then 
		D.Pop(r, i, E) (* cannot abstract as point of reference is changed too far.  Should never happen by invariant *)
	      else
		D.Pop(r, i, abstractDelExp(K, depth-i, E)) 

      | abstractDelExp (K, depth, D.Fix (r, funList)) = 
		D.Fix (r, abstractDelFunList (K, depth, funList))

      | abstractDelExp (K, depth, P as D.PatVar _) =
	     abstractPatVar(K, depth, P)


      | abstractDelExp (K, depth, D.TypeAscribe (r, E, T)) = 
		D.TypeAscribe(r, abstractDelExp(K, depth, E), abstractDelTypes(K, depth, T))

      | abstractDelExp (K, depth, D.Sequence seqList) =
		let
		  fun abstractSeq (r, E) = (r, abstractDelExp(K, depth, E))
		  val seqList' = map abstractSeq seqList
		in
		  D.Sequence seqList'
		end

   (* removed
      | abstractDelExp (K, depth, D.LiftedApp (r, E1, A1, E2, A2, Aresult)) =
		D.LiftedApp(r, abstractDelExp(K, depth, E1),
			    abstractExp(K, depth, (A1, I.id)),
			    abstractDelExp(K, depth, E2),
			    abstractExp(K, depth, (A2, I.id)),
			    abstractExp(K, depth, (Aresult, I.id)))


      | abstractDelExp (K, depth, D.LetVar (r, D, E1, E2)) = 
		D.LetVar(r, abstractDelNormalDec(K, depth, D), 
			 abstractDelExp(K, depth, E1),
			 abstractDelExp(K, depth+1, E2))
*)

      | abstractDelExp (K, depth, D.LetFun (r, funList, E2)) =
		D.LetFun(r, abstractDelFunList (K, depth, funList),
			 abstractDelExp(K, depth+1, E2))

			    

    and abstractDelFunList (K, depth, []) = []
      | abstractDelFunList (K, depth, (r,D,E)::funList) = 
                (r, abstractDelNormalDec(K, depth, D), abstractDelExp(K, depth+1, E)) ::
		(abstractDelFunList (K, depth, funList))

    and abstractDelCaseBranch (K, depth, D.Eps (r, D, C)) = D.Eps (r, abstractDelNormalDec (K, depth, D),
								abstractDelCaseBranch (K, depth+1, C))

      | abstractDelCaseBranch (K, depth, D.NewC (r, D, C)) = D.NewC (r, abstractDelNewDec (K, depth, D),
							      abstractDelCaseBranch (K, depth+1, C))

      | abstractDelCaseBranch (K, depth, D.PopC (r, i, C)) = 	      
                                             if (i > depth) then 
					       D.PopC(r, i, C) (* cannot abstract as point of reference is changed too far.  
							       Should never happen by invariant *)
					     else
					       D.PopC(r, i, abstractDelCaseBranch(K, depth-i, C))


      | abstractDelCaseBranch (K, depth, D.Match (r, E1, E2)) = D.Match (r, abstractDelExp(K, depth, E1),
								      abstractDelExp(K, depth, E2))

      | abstractDelCaseBranch (K, depth, D.MatchAnd (r, visible, E, C)) = D.MatchAnd (r, visible, abstractDelExp(K, depth, E),
								       abstractDelCaseBranch(K, depth, C))

      
    and abstractDelNormalDec (K, depth, D.NormalDec(r, name, T)) = D.NormalDec(r, name, abstractDelTypes(K, depth, T))
    and abstractDelNewDec (K, depth, D.NewDecLF (r, name, A)) = D.NewDecLF (r, name, abstractExp(K, depth, (A, I.id)))
      | abstractDelNewDec (K, depth, D.NewDecMeta (r, name, F)) = D.NewDecMeta(r, name, abstractDelFormula(K, depth, F))

    and abstractDelTypes (K, depth, D.LF (r, isP, A)) = D.LF(r, isP, abstractExp(K, depth, (A, I.id)))
      | abstractDelTypes (K, depth, D.Meta (r, isP, F)) = D.Meta(r, isP, abstractDelFormula(K, depth, F))

    and abstractDelFormula (K, depth, F as D.Top _) = F
      | abstractDelFormula (K, depth, D.All(r, visible, D, F)) = D.All (r, visible, abstractDelNormalDec(K, depth, D),
							     abstractDelFormula(K, depth+1, F))
      | abstractDelFormula (K, depth, D.Exists(r, D, F)) = D.Exists (r, abstractDelNormalDec(K, depth, D),
								   abstractDelFormula(K, depth+1, F))
      | abstractDelFormula (K, depth, D.Nabla(r, D, F)) = D.Nabla (r, abstractDelNewDec(K, depth, D),
								 abstractDelFormula(K, depth+1, F))

      | abstractDelFormula (K, depth, F as D.OmittedFormula r) = F




    fun ctxRemovePrefix(_, I.Null) = I.Null
      | ctxRemovePrefix(i, G) = 
                   let
		     val n = I.ctxLength G
		   in
		     if (i = n) then I.Null
		     else if (n > i) then 
		       (case G of 
			  I.Decl(G', D) => I.Decl(ctxRemovePrefix(i, G'), D)
			| _ => raise Domain)
		     else raise Domain
		   end
		      
		      
		 
   (* ************************************************************ *)
   (* ************************************************************ *)
   (* Delphin Specific Abstraction *)
   (* ************************************************************ *)
   (* ************************************************************ *)
      
   (* transformDelExp (E, K) = (E', K)
    *
    *  G |- E : T
    *  Precondition:  All Vars in G are contained in K 
    *
    *  (1) Recursively abstracts delphin program (deduces pattern variables) to E'
    *  (2) Left-over EVars/FVars are added to K and result is K' (if allowedVars is false then K = K')
    *)
    fun transformDelExp (E as D.VarInt _, K, allowVars) = (E, K)
      | transformDelExp (E as D.Quote (r,U,A,I), K, allowVars) = (E, 
								   LFcollectExp(r, (A, I.id), 
										LFcollectExp (r,(U, I.id), K, allowVars),
										allowVars))
      | transformDelExp (E as D.Unit _, K, allowVars) = (E, K)
      | transformDelExp (D.Lam (r, Clist), Kinitial, allowVars) = 
              let
		(* Although K is in a correct dependency-order, we prefer all meta-level
		 * types to be at the end.  This way they can depend upon all LF types before them.
		 *)

		(* First we separate out all meta-level parts of K *)
		fun separateK (I.Decl(K, D as PV _), metaK) = separateK(K, I.Decl(metaK, D))
		  | separateK (I.Decl(K, D), metaK) = 
		            let
			      val (Klf, Kmeta) = separateK (K, metaK)
			    in
			      (I.Decl(Klf, D), Kmeta)
			    end
		  | separateK (I.Null, metaK) = (I.Null, metaK)

		fun transformK K =
		       let
			 fun mergeK(K, I.Null) = K
			   | mergeK(K, I.Decl(K2, D)) = I.Decl(mergeK(K, K2), D)

			 val (Klf, Kmeta) = separateK (K, I.Null)
		       in
			 mergeK(Klf, Kmeta)
		       end


		(* This is where the real abstraction happens *)
		(* EVars/FVars are turned into epsilon-bound pattern variables *)

		fun transformC Kinitial (D.Match (r, E1, E2)) =
		      let
			val (E1', K0) = transformDelExp(E1, Kinitial, true)
			val (E2', K) = transformDelExp(E2, K0, false)
			val C' = D.Match(r, E1', E2')
			val K' = ctxRemovePrefix(I.ctxLength Kinitial, K)  (* K = Kinitial,K' *)
			val K' = transformK K' (* Move meta-level to the end *)
			val _ = checkConstraints K'
			val n = I.ctxLength K'
			val C2 = D.substCase(C', D.shift n)
			(* G, {{K'}} |- C2 *)
			val C3 = abstractDelCaseBranch (K', 0, C2)
			val C4 = abstractKEps(K', C3, n-1)
		      in
			C4
		      end

		  | transformC Kinitial (D.MatchAnd(r, visible, E, C)) =
		      let
			val (E', K) = transformDelExp(E, Kinitial, true)
			val C' = D.MatchAnd(r, visible, E', transformC K C)
			val K' = ctxRemovePrefix(I.ctxLength Kinitial, K)  (* K = Kinitial,K' *)
			val K' = transformK K' (* Move meta-level to the end *)
			val _ = checkConstraints K'
			val n = I.ctxLength K'
			val C2 = D.substCase(C', D.shift n)
			(* G, {{K'}} |- C2 *)
			val C3 = abstractDelCaseBranch (K', 0, C2)
			val C4 = abstractKEps(K', C3, n-1)
		      in
			C4
		      end

		  | transformC Kinitial (D.Eps (r, D, C)) = 
		      let
			val K = collectDelNormalDec(D, Kinitial, true)
			val C' = D.Eps(r, D, transformC K C)

			val K' = ctxRemovePrefix(I.ctxLength Kinitial, K)  (* K = Kinitial,K' *)
			val K' = transformK K' (* Move meta-level to the end *)
			val _ = checkConstraints K'
			val n = I.ctxLength K'
			val C2 = D.substCase(C', D.shift n)
			(* G, {{K'}} |- C2 *)
			val C3 = abstractDelCaseBranch (K', 0, C2)
			val C4 = abstractKEps(K', C3, n-1)
		      in
			C4
		      end


		  | transformC Kinitial (D.PopC (r, i, C)) = 
		      let
			val C' = transformC Kinitial C
		      in
			D.PopC(r, i, C')
		      end		      

		  | transformC Kinitial (C as D.NewC _) =
		      let
			(* We want to collect all variables to the LEFT of NewC
			 * so we call transformDelCaseBranch which transforms and collects a list of variables to abstract
			 *)
			val (C', K) = transformDelCaseBranch(C, Kinitial) (* allowVars = true *)
			val K' = ctxRemovePrefix(I.ctxLength Kinitial, K)  (* K = Kinitial,K' *)
			val K' = transformK K' (* Move meta-level to the end *)
			val _ = checkConstraints K'
			val n = I.ctxLength K'
			val C2 = D.substCase(C', D.shift n)
			(* G, {{K'}} |- C2 *)
			val C3 = abstractDelCaseBranch (K', 0, C2)
			val C4 = abstractKEps(K', C3, n-1)
		      in
			C4
		      end
		      


	  (* OLD
		fun transformC C =
		      let
			val (C', K) = transformDelCaseBranch(C, Kinitial) (* allowVars = true *)
			val K' = ctxRemovePrefix(I.ctxLength Kinitial, K)  (* K = Kinitial,K' *)
			val K' = transformK K' (* Move meta-level to the end *)
			val _ = checkConstraints K'
			val n = I.ctxLength K'
			val C2 = D.substCase(C', D.shift n)
			(* G, {{K'}} |- C2 *)
			val C3 = abstractDelCaseBranch (K', 0, C2)
			val C4 = abstractKEps(K', C3, n-1)
		      in
			C4
		      end
            *)		 
		val Clist' = map (transformC Kinitial) Clist
	      in
		(D.Lam (r, Clist'), Kinitial)
	      end

      | transformDelExp (D.New (r, D, E), K, allowVars) = 
	      let 
		val (K1) = collectDelNewDec(D, K, allowVars)
		val (E', K2) = transformDelExp(E, K1, allowVars)
	      in
		(D.New(r, D, E'), K2)
	      end

      | transformDelExp (D.App (r, visible, E1, E2), K, allowVars) = 
	      let
		val (E1', K1) = transformDelExp(E1, K, allowVars)
		val (E2', K2) = transformDelExp(E2, K1, allowVars)
	      in
		(D.App(r, visible, E1', E2'), K2)
	      end

      | transformDelExp (D.Pair (r, E1, E2), K, allowVars) = 
	      let
		val (E1', K1) = transformDelExp(E1, K, allowVars)
		val (E2', K2) = transformDelExp(E2, K1, allowVars)
	      in
		(D.Pair(r, E1', E2'), K2)
	      end


      | transformDelExp (D.Proj (r, E, i), K, allowVars) =
	      let
		val (E', K2) = transformDelExp(E, K, allowVars)
	      in
		(D.Proj (r, E', i), K2)
	      end

      | transformDelExp (D.Pop (r, i, E), K, allowVars) = 
	      let 
		val (E', K2) = transformDelExp(E, K, allowVars) 
	      in
		(D.Pop(r, i, E'), K2)
	      end


      | transformDelExp (D.Fix (r, funList), K, allowVars) = 
	      let
		val (funList', K2) = transformDelFunList (funList, K, allowVars)
	      in
		(D.Fix(r, funList'), K2)
	      end


      | transformDelExp (P as D.PatVar (r, s), K, allowVars) =
	      if (exists (eqPatVar P) K) then
		  (P, K)
	      else if allowVars then
		  (P, I.Decl(K, PV (r, s)))
	      else
		raise Error (r, "Variable " ^ s ^ " not defined.")


      | transformDelExp (D.TypeAscribe (r, E, T), K, allowVars) =
	      let
		val (K2) = collectDelTypes(T, K, allowVars)
		val (E', K3) = transformDelExp(E, K2, allowVars)
	      in
		(D.TypeAscribe(r, E', T), K3)
	      end

      | transformDelExp (D.Sequence seqList, K, allowVars) =
	      let
		fun transformList ([], K) = ([], K)
		  | transformList ((r,E)::seqList, K) =
		          let
			    val (E', K') = transformDelExp(E, K, allowVars)
			    val (seqList', K'') = transformList(seqList, K')
			  in
			    ((r,E') :: seqList', K'')
			  end
		val (seqList', K') = transformList (seqList, K)
	      in
		(D.Sequence seqList', K')
	      end
		     
      (* removed
      | transformDelExp (D.LetVar (r, D, E1, E2), K, allowVars) = 
	      let
		val (K2) = collectDelNormalDec (D, K, allowVars)
		val (E1', K3) = transformDelExp (E1, K2, allowVars)
		val (E2', K4) = transformDelExp (E2, K3, allowVars)
	      in
		(D.LetVar (r, D, E1', E2'), K4)
	      end
       *)

      | transformDelExp (D.LetFun (r, funList, E2), K, allowVars) = 
	      let
		val (funList', K2) = transformDelFunList (funList, K, allowVars)
		val (E2', K3) = transformDelExp (E2, K2, allowVars)
	      in
		(D.LetFun (r, funList', E2'), K3)
	      end


    and transformDelFunList ([], K, allowVars) = ([], K)
      | transformDelFunList ((r,D,E)::funList, Kinitial, allowVars) =
              let
		val K2 = collectDelNormalDec(D, Kinitial, allowVars)
		val _ = if (I.ctxLength K2 > I.ctxLength Kinitial) then raise Error (r, "Vars found in type declaration which should have been removed by updateExp... this is a bug") else ()

		(* Set of Vars is Kinitial *)
		val (E', K3) = transformDelExp(E, Kinitial, allowVars)
		val (funList', K4) = transformDelFunList(funList, K3, allowVars)
	      in
		((r, D, E') :: funList', K4)
	      end

    and transformDelCaseBranch (D.Eps (r, D, C), K) = 
	      let
		val (K2) = collectDelNormalDec(D, K, true)
		val (C', K3) = transformDelCaseBranch(C, K2)
	      in
		(D.Eps(r, D, C'), K3)
	      end

      | transformDelCaseBranch (D.NewC (r, D, C), K) = 
	      let
		val (K2) = collectDelNewDec(D, K, true)
		val (C', K3) = transformDelCaseBranch(C, K2)
	      in
		(D.NewC(r, D, C'), K3)
	      end

      (* Warning!!!: ABP.. Abstraction under PopC needs to be thought out more.... *)
      (* HOWEVER, Can we just disallow PopC in the syntax... we need it for opsem,
       *          but would anyone use PopC instead of "Pop" ???
       *)
      | transformDelCaseBranch (D.PopC (r, i, C), K) = 
	      let 
		val (C', K2) = transformDelCaseBranch(C, K) 
	      in
		(D.PopC(r, i, C'), K2)
	      end



      | transformDelCaseBranch (D.Match (r, E1, E2), K) = 
	      let
		val (E1', K2) = transformDelExp(E1, K, true)
		val (E2', K3) = transformDelExp(E2, K2, false)
	      in
		(D.Match(r, E1', E2'), K3)
	      end

      | transformDelCaseBranch (D.MatchAnd (r, visible, E, C), K) = 
	      let
		val (E', K2) = transformDelExp(E, K, true)
		val (C', K3) = transformDelCaseBranch(C, K2)
	      in
		(D.MatchAnd(r, visible, E', C'), K3)
	      end

      
    and collectDelNormalDec (D.NormalDec(_, _, T), K, allowVars) = collectDelTypes(T, K, allowVars)
    and collectDelNewDec (D.NewDecLF (r, _, A), K, allowVars) = (LFcollectExp (r, (A, I.id), K, allowVars))
      | collectDelNewDec (D.NewDecMeta (_, _, F), K, allowVars) = (collectDelFormula(F, K, allowVars))

    and collectDelTypes (D.LF (r, _, A), K, allowVars) = (LFcollectExp (r, (A, I.id), K, allowVars))
      | collectDelTypes (D.Meta (_, _, F), K, allowVars) = (collectDelFormula(F, K, allowVars))

    and collectDelFormula (D.Top _, K, allowVars) = K
      | collectDelFormula (D.All(r, visible, D, F), K, allowVars) = 
              let
		val K2 = collectDelNormalDec (D, K, allowVars)
		val K3 = collectDelFormula (F, K2, allowVars)
	      in
		K3
	      end

      | collectDelFormula (D.Exists(r, D, F), K, allowVars) = 
              let
		val K2 = collectDelNormalDec (D, K, allowVars)
		val K3 = collectDelFormula (F, K2, allowVars)
	      in
		K3
	      end

      | collectDelFormula (D.Nabla(r, D, F), K, allowVars) = 
              let
		val K2 = collectDelNewDec (D, K, allowVars)
		val K3 = collectDelFormula (F, K2, allowVars)
	      in
		K3
	      end

      | collectDelFormula (D.OmittedFormula _, K, allowVars) = K
       

				


   
    (* Precondition:  G (which E makes sense) has no Vars *)
    fun abstractPatVarsExp (E) =
               let
		 val (E', K (* I.Null *) ) = transformDelExp (E, I.Null, false)
	       in
		 E'
	       end


    fun abstractPatVarsFunList (funList) =
               let
		 val (funList', K (* I.Null *) ) = transformDelFunList (funList, I.Null, false)
	       in
		 funList'
	       end

    fun addImplicitTypesDec D = 
               let
		 val K = collectDelNormalDec(D, I.Null, true)
		 val _ = checkConstraints K
		 val n = I.ctxLength K
		 val D2 = D.substNormalDec(D, I.Shift n)
		 (* G, {{K}} |- D2 *)
		 val D3 = abstractDelNormalDec (K, 0, D2)
		 val Dnew = abstractKdec(K, D3, n-1)
		   
	       in
		 Dnew
	       end


end;  (* functor Abstract *)
