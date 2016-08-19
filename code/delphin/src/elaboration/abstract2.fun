(* **************************************************************************
 * Abstraction on Internal Syntax... Used in coverage...
 * Abstraction of the actual internal syntax is only used in coverage.
 * Therefore, the properties are as follows:
 *  (1) We only abstract "Patterns" (* now convert.fun requries us to abstract a little more... *)
 *  (2) We abstract meta-level EVars and BoundVars
 *  (3) We abstract LF-level EVars and BoundVars (not FVars, LVars, or AVsrs)
 *             (* The "BoundVars" take the place of Blocks (LVars).
                * FVars are removed before getting to this stage.
                * I have no idea what your AVars are.
                *)
 *
 * Author: Adam Poswolsky
 * **************************************************************************
 *)
structure DelphinAbstract2 =
struct
    exception LeftOverConstraints
     
    structure I = IntSyn
    structure C = Constraints
    structure D = DelphinIntSyntax

    datatype Vars =
      LF_EV of I.Exp		
    | Meta_EV of D.Exp
    | BV of D.BoundVar


    fun crash() = raise Domain

    (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
    fun collectConstraints (I.Null) = nil
      | collectConstraints (I.Decl (G, BV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, Meta_EV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, LF_EV (I.EVar (_, _, _, ref nil)))) = collectConstraints G
      | collectConstraints (I.Decl (G, LF_EV (I.EVar (_, _, _, ref cnstrL)))) =
               let
		 val constraints = C.simplify cnstrL
	       in
		 case constraints of
		   nil => collectConstraints G
		   | _ => (constraints) :: (collectConstraints G)
	       end
      | collectConstraints (I.Decl (G, LF_EV _)) = crash() (* A non EVar stored in LF_EV.. *)

    (* checkConstraints (K) = ()
       Effect: raises LeftOverConstraints if K contains unresolved constraints
    *)
    fun checkConstraints (K) =
        let
	  val constraints = collectConstraints K
	  val _ = case constraints
	            of nil => ()
		     | _ => raise LeftOverConstraints 
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
    *)



    (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
    fun eqLF_EVar (I.EVar (r1, _, _, _)) (LF_EV (I.EVar (r2, _, _, _))) = (r1 = r2)
      | eqLF_EVar _ _ = false

    fun eqLF_BVar1 (I.BVarVar ((r1, _, _), _)) (BV (D.BVarLF ((r2, _, _), _))) = (r1 = r2)
      | eqLF_BVar1 _ _ = false


    fun eqLF_BVar2 (D.BVarLF ((r1, _, _), _)) (BV (D.BVarLF ((r2, _, _), _))) = (r1 = r2)
      | eqLF_BVar2 _ _ = false


    fun eqMeta_EVar (D.EVar ((r1, _), _)) (Meta_EV (D.EVar ((r2, _), _)))  = (r1 = r2)
      | eqMeta_EVar _ _ = false


    fun eqMeta_BVar (D.BVarMeta ((r1, _), _)) (BV (D.BVarMeta ((r2, _), _)))  = (r1 = r2)
      | eqMeta_BVar _ _ = false


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
      | occursInHead _ = I.Maybe (* if it is a FVar (or BVarVar) we just return maybe *)

    and occursInSpine (_, I.Nil) = I.No
      | occursInSpine (k, I.App (U, S)) = or (occursInExp (k, U), occursInSpine (k, S))
      (* no case for SClo *) 
      | occursInSpine _ = I.Maybe (* If it is not needed, it can't hurt.. *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
      | occursInDec (k, I.NDec) = I.No
      | occursInDec _ = crash()

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
      | raiseType (I.Decl (G, I.NDec), V) = crash()
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))


    (* collectExpW ((U, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
       and   K' = K, K''
	     where K'' contains all Vars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)


    fun collectExpW ((I.Uni L, s), K) = K
      | collectExpW ((I.Pi ((D, _), V), s), K) =
          collectExp ((V, I.dot1 s), collectDec ((D, s), K))
      | collectExpW ((I.Root (F as I.FVar (name, isP, V, s'), S), s), K) =
	  crash() (* broken invariant.. NO FVars for this abstraction *)

      | collectExpW ((I.Root (I.Proj (L as I.LVar (r, _, (l, t)), i), S), s), K) =
	    crash() (* No more blocks!!! *)

      | collectExpW ((I.Root (I.BVar (B as I.BVarVar ((r,A,list), s0)) , S), s (* id *)), K) =
	      if (exists (eqLF_BVar1 B) K) then
		collectSpine ((S, s), collectSub(s0, K))
	      else
		collectSpine ((S, s), I.Decl (collectSub(s0, collectExp((A, I.id), K)), BV (D.BVarLF ((r,A,list), s0))))

      | collectExpW ((I.Root (_ , S), s), K) =
	  collectSpine ((S, s), K)
      | collectExpW ((I.Lam (D, U), s), K) =
	  collectExp ((U, I.dot1 s), collectDec ((D, s), K))
      | collectExpW ((X as I.EVar (r, GX, V, cnstrs), s), K) =
	if exists (eqLF_EVar X) K
	  then collectSub(s, K)
	else 
	     let
	       (* val _ = checkEmpty !cnstrs *)
	       val V' = raiseType (GX, V) (* inefficient *)
	       val K' = collectExp ((V', I.id), K)
	     in
	       collectSub(s, I.Decl (K', LF_EV X))
	     end

      | collectExpW ((I.FgnExp csfe, s), K) =
	  I.FgnExpStd.fold csfe (fn (U, K) => collectExp ((U, s), K)) K
      (* No other cases can occur due to whnf invariant *)
      | collectExpW _ = crash()

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
      | collectDec ((I.BDec (_, (_, t)), s), K) = crash() (* no more blocks *)

      (* ABP -- added NDec *)
      | collectDec ((I.NDec, s), K) = K
      | collectDec _ = crash()

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
      | collectSub (I.Dot (I.Block B, s), K) = crash() (* no blocks *)
    (* next case is not impossible because we allow ECLo with undefs if we know it doesn't actually use it..
     * maybe we should apply it out to get rid of such undefs..
     *)
      | collectSub (I.Dot (I.Undef, s), K) =
          collectSub (s, K)



    fun getNumShifts (D.Shift t) = (getNumShifts t) + 1
      | getNumShifts (D.id) = 0
      | getNumShifts (D.Dot (D.Prg (D.Var(D.Fixed n, NONE)), t)) = if (getNumShifts t) = n then n else crash() (* not a shift sub *)
      | getNumShifts _ = crash() (* not a shift substitution *)

    fun getNumLFShifts (I.Shift i) = i
      | getNumLFShifts (I.Dot (I.Idx n, t)) = if (getNumLFShifts t) = n then n else crash() (* not a shift sub *)
      | getNumLFShifts _ = crash() (* not a shift sub *)

    (* checkSub(t1, t2) = checks that both t1 and t2 are shift subs. *)
    fun checkSub(s1, s2) =
      let
	val N1 = getNumShifts s1
	val N2 = getNumShifts s2
      in
	()
      end

    fun checkLFSub(s1, s2) =
      let
	val N1 = getNumLFShifts s1
	val N2 = getNumLFShifts s2
      in
	()
      end


    (* abstractEVar (K, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractLF_EVar (I.Decl (K', LF_EV (I.EVar(r',GX,_,_))), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then SOME(I.BVar (I.Fixed (depth+1)), I.ctxLength GX)
	else abstractLF_EVar (K', depth+1, X)
      | abstractLF_EVar (I.Decl (K', _), depth, X) = 
	  abstractLF_EVar (K', depth+1, X)
      | abstractLF_EVar (I.Null, _, _) = NONE


    fun abstractLF_BVar (I.Decl (K', BV (D.BVarLF((r, _,_), s1))), depth, X as I.BVarVar ((r', _,_), s2)) =
        if r = r' then (checkLFSub(s2, s1) ; SOME(depth + 1))
	else abstractLF_BVar (K', depth+1, X)
      | abstractLF_BVar (I.Decl (K', _), depth, X) = 
	  abstractLF_BVar (K', depth+1, X)
      | abstractLF_BVar (I.Null, _, _) = NONE

    fun abstractLF_BVar2 (I.Decl (K', BV (D.BVarLF((r, _,_), s1))), depth, X as D.BVarLF ((r', _,_), s2)) =
        if r = r' then (checkLFSub(s2, s1) ; SOME(depth + 1))
	else abstractLF_BVar2 (K', depth+1, X)
      | abstractLF_BVar2 (I.Decl (K', _), depth, X) = 
	  abstractLF_BVar2 (K', depth+1, X)
      | abstractLF_BVar2 (I.Null, _, _) = NONE

    fun abstractMeta_EVar (I.Decl(K', Meta_EV (D.EVar ((r,_), s1) )), depth, P as D.EVar ((r',_), s2)) =
          if r = r' then (checkSub(s2, s1) ; SOME(depth + 1))
	  else abstractMeta_EVar (K', depth+1, P)
      | abstractMeta_EVar (I.Decl(K', _), depth, P) =
	    abstractMeta_EVar (K', depth+1, P)
      | abstractMeta_EVar (I.Null, _, _) = NONE


    fun abstractMeta_BVar (I.Decl(K', BV (D.BVarMeta ((r,_),s1))), depth, P as D.BVarMeta ((r', _), s2))  =
          if r = r' then (checkSub(s2, s1) ; SOME(depth + 1))
	  else abstractMeta_BVar (K', depth+1, P)
      | abstractMeta_BVar (I.Decl(K', _), depth, P) =
	    abstractMeta_BVar (K', depth+1, P)
      | abstractMeta_BVar (I.Null, _, P) = NONE


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
      | abstractExpW (K, depth, (I.Root (F as I.FVar _, S), s)) = crash() (* no FVars *)
      | abstractExpW (K, depth, (I.Root (I.Proj (L as I.LVar _, i), S), s)) = crash() (* no blocks *)
      | abstractExpW (K, depth, (I.Root (I.BVar (B as I.BVarVar (r0, s0)) , S), s (* id *))) =
	  let 
	    val Hopt = abstractLF_BVar (K, depth, B)
	  in
	    case Hopt
	      of NONE => I.Root (I.BVar (I.BVarVar(r0, abstractSubToSub(K, depth, s0))), abstractSpine(K, depth, (S, s)))
	       | SOME n => I.Root (I.BVar (I.Fixed n), abstractSpine(K, depth, (S, s)))

	  end

      | abstractExpW (K, depth, (I.Root (H, S) ,s)) =
	  I.Root (H, abstractSpine (K, depth, (S, s)))   
      | abstractExpW (K, depth, (I.Lam (D, U), s)) =
          I.Lam (abstractDec (K, depth, (D, s)),
		 abstractExp (K, depth + 1, (U, I.dot1 s)))
      | abstractExpW (K, depth, (X as I.EVar _, s)) =
	  let 
	    val Hopt = abstractLF_EVar (K, depth, X)
	  in
	    case Hopt
	      of NONE => crash()
	                 (* This is used in coverage.. everything should be abstracted away... *)
	                 (* I.EClo(X, abstractSubToSub(K, depth, s))  *)
	       | SOME (H, size) => 
		   let
		     val S = abstractSub (K, depth, s, size, I.Nil)
		   in
		     I.Root (H, S)
		   end
	  end
      | abstractExpW (K, depth, (I.FgnExp csfe, s)) =
          I.FgnExpStd.Map.apply csfe (fn U => abstractExp (K, depth, (U, s)))
      | abstractExpW _ = crash()

    (* abstractExp (K, depth, (U, s)) = U'
     
       same as abstractExpW, but (U,s) need not to be in whnf 
    *)
    and abstractExp (K, depth, Us) = abstractExpW (K, depth, Whnf.whnf Us)

    and abstractSubToSub (K, depth, s as I.Shift _) = s
      | abstractSubToSub (K, depth, I.Dot(I.Idx k, s)) = I.Dot(I.Idx k, abstractSubToSub (K, depth, s))
      | abstractSubToSub (K, depth, I.Dot(I.Exp U, s)) = I.Dot(I.Exp (abstractExp(K, depth, (U, I.id))), abstractSubToSub (K, depth, s))
      | abstractSubToSub (K, depth, I.Dot(I.Block B, s)) = crash() (* no more blocks *)
      | abstractSubToSub (K, depth, I.Dot(I.Undef, s)) = I.Dot(I.Undef, abstractSubToSub (K, depth, s))
      
    (* abstractSub (K, depth, s, sizeGX, S) = SS
     *
     * If  G' |- s : GX
     * and G' |- S is a spine of types A1...An
     * and |GX|=sizeGX
     *
     * then G' |- SS is a spine of types GX A1...An
     *)
     
    and abstractSub (K, depth, _, 0, S) = S
      | abstractSub (K, depth, I.Shift k, size, S) = abstractSub (K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), size, S)
      | abstractSub (K, depth, I.Dot (I.Idx (k), s), size, S) =
	  (* G' |- k.s : GX,A
	   * G' |- S is a spine of types A1...An
	   *
	   * G' |- s : GX
	   * G' |- k@S is a spine of types A,A1...An
	   *)
	  abstractSub (K, depth, s, size-1, I.App (I.Root (I.BVar (I.Fixed k), I.Nil), S))
      | abstractSub (K, depth, I.Dot (I.Exp (U), s), size, S) =
	  abstractSub (K, depth, s, size-1, I.App (abstractExp (K, depth, (U, I.id)), S))
      | abstractSub _ = crash()
 
    and abstractSpine (K, depth, (I.Nil, _))  = I.Nil 
      | abstractSpine (K, depth, (I.SClo (S, s'), s)) = 
	  abstractSpine (K, depth, (S, I.comp (s', s)))
      | abstractSpine (K, depth, (I.App (U, S), s)) =
	  I.App (abstractExp (K, depth, (U ,s)), 
		 abstractSpine (K, depth, (S, s)))

    and abstractDec (K, depth, (I.Dec (x, V), s)) =
	  I.Dec (x, abstractExp (K, depth, (V, s)))
      | abstractDec (K, depth, (I.NDec, s)) = I.NDec
      | abstractDec _ = crash()






    (* abstractKCtx (K, |K|-1) = G 
     * WARNING:: May not be used anymore
     *)
    fun abstractKCtx (I.Null, ~1) = I.Null
      | abstractKCtx (I.Null, numShifts) = crash() (* numShifts should be ~1 *)
      | abstractKCtx (I.Decl (K', LF_EV (I.EVar (_, GX, VX, _))), numShifts) =
        let
          val V' = raiseType (GX, VX) 
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
          (* enforced by reconstruction -kw
	  val _ = checkType V''	*)
	in	 
	  I.Decl(abstractKCtx (K', numShifts-1), D.InstantiableDec (D.NormalDec(NONE, D.LF(D.Existential, V''))))
	end
      | abstractKCtx (I.Decl (K', Meta_EV (D.EVar ((r,F), _))), numShifts) =
        let
          val F' = abstractDelFormula(K', 0, D.FClo(F, I.Shift numShifts))
	in	 
	  I.Decl(abstractKCtx (K', numShifts-1), D.InstantiableDec (D.NormalDec(NONE, D.Meta(D.Existential, F'))))
	end

      | abstractKCtx (I.Decl (K', BV (D.BVarLF ((r, A,list), _))), numShifts) = 
        let
	  val A' = abstractExp (K', 0, (A, I.Shift numShifts))
	in	 
	  I.Decl(abstractKCtx (K', numShifts-1), D.InstantiableDec (D.NormalDec(NONE, D.LF(D.Param, A'))))
	end


      | abstractKCtx (I.Decl (K', BV (D.BVarMeta ((r,F), _))), numShifts) = 
        let
          val F' = abstractDelFormula(K', 0, D.FClo(F, I.Shift numShifts))
	in	 
	  I.Decl(abstractKCtx (K', numShifts-1), D.InstantiableDec (D.NormalDec(NONE, D.Meta(D.Param, F'))))
	end


      | abstractKCtx _ = crash()




    and abstractKEps (I.Null, C, ~1) = C
      | abstractKEps (I.Null, C, numShifts) = crash() (* numShifts should be ~1 *)
      | abstractKEps (I.Decl (K', LF_EV (I.EVar (_, GX, VX, _))), C, numShifts) =
        let
          val V' = raiseType (GX, VX) 
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
          (* enforced by reconstruction -kw
	  val _ = checkType V''	*)
	in	 
	  abstractKEps(K', D.Eps(D.NormalDec(NONE, D.LF(D.Existential, V'')), C), numShifts -1)
	end
      | abstractKEps (I.Decl (K', Meta_EV (D.EVar ((r,F), _))), C, numShifts) =
        let
          val F' = abstractDelFormula(K', 0, D.FClo(F, I.Shift numShifts))
	in
	  abstractKEps(K', D.Eps(D.NormalDec(NONE, D.Meta(D.Existential, F')), C), numShifts -1)
	end

      | abstractKEps (I.Decl (K', BV (D.BVarLF ((r, A,list), _))), C,  numShifts) = 
        let
	  val A' = abstractExp (K', 0, (A, I.Shift numShifts))
	in
	  abstractKEps(K', D.Eps(D.NormalDec(NONE, D.LF(D.Param, A')), C), numShifts -1)
	end


      | abstractKEps (I.Decl (K', BV (D.BVarMeta ((r,F), _))), C, numShifts) = 
        let
          val F' = abstractDelFormula(K', 0, D.FClo(F, I.Shift numShifts))
	in
	  abstractKEps(K', D.Eps(D.NormalDec(NONE, D.Meta(D.Param, F')), C), numShifts -1)
	end


      | abstractKEps _ = crash()




    (* Collection/Abstraction of Delphin Patterns
     * *************************************************************************
     * *************************************************************************
     *)


    and collectDelBoundVarW (E as D.Fixed _, K) = K
      | collectDelBoundVarW (B as D.BVarMeta ((r, F), s), K) = 
          if (exists (eqMeta_BVar B) K) then
	    collectDelSub(s, K)
	  else
	    I.Decl (collectDelSub(s, collectDelFormula(F, K)), BV B)

      | collectDelBoundVarW (B as D.BVarLF ((r, A, list), s), K) = 
          if (exists (eqLF_BVar2 B) K) then
	    collectSub(s, K)
	  else
	    I.Decl (collectSub(s, collectExp((A, I.id), K)), BV B)

    and collectDelSub (D.id, K) = K
      | collectDelSub (D.Shift t, K) = collectDelSub(t, K)
      | collectDelSub (D.Dot(D.Undef, t), K) = collectDelSub(t, K)
      | collectDelSub (D.Dot(D.Prg E, t), K) = collectDelSub(t, collectDelExp(E, K))


    and collectDelExp (E, K) = collectDelExpW (D.whnfE E, K)
    and collectDelExpW (D.Var(B, fileInfo), K) = collectDelBoundVarW(B, K)
      | collectDelExpW (D.Quote U, K) = collectExp((U, I.id), K)
      | collectDelExpW (D.Unit, K) = K
      | collectDelExpW (D.Lam (Clist, F, fileInfo), K) =
                        let
			  val K2 = collectDelFormula(F, K)
			  fun collectC ([], K') = K'
			    | collectC (C::Clist, K') = collectC (Clist, collectDelCaseBranch (C, K'))
			in
			  collectC (Clist, K2)
			end


      | collectDelExpW (D.New (D, E, fileInfo), K) = collectDelExp(E, collectDelNewDec (D, K))
      | collectDelExpW (D.App (visible, E1, E2), K) = collectDelExp(E2, collectDelExp(E1, K))
      | collectDelExpW (D.Pair (E1, E2, F), K) = collectDelExp(E2, collectDelExp(E1, collectDelFormula(F, K)))
      | collectDelExpW (D.ExpList _, K) = crash() (* not a valid pattern *)
      | collectDelExpW (D.Proj _, K) = crash() (* not a valid pattern *)
      | collectDelExpW (D.Pop (i, E), K) = collectDelExp(E, K)
      | collectDelExpW (D.Fix _, K) = crash() (* not a valid pattern *)
      | collectDelExpW (E as D.EVar ((r,F), s), K) =
	if exists (eqMeta_EVar E) K then
	  collectDelSub(s, K)
	else 
	     let
	       val K' = collectDelSub(s, collectDelFormula(F, K))
	     in
	       I.Decl(K', Meta_EV E)
	     end
	      
      | collectDelExpW (D.EClo _, K) = crash() (* not in whnf *)


    and collectDelCaseBranch(D.Eps(D, C), K) = collectDelCaseBranch(C, collectDelNormalDec(D, K))
      | collectDelCaseBranch(D.NewC(D, C, fileInfo), K) = collectDelCaseBranch(C, collectDelNewDec(D, K))
      | collectDelCaseBranch(D.PopC(i, C), K) = crash() (* not a generated pattern *)
      | collectDelCaseBranch(D.Match(visibility, E1, E2), K) = collectDelExp(E2, collectDelExp(E1, K))
      | collectDelCaseBranch(D.MatchAnd(visibility, E, C), K) = collectDelCaseBranch(C, collectDelExp(E, K))

      
    and collectDelNormalDec (D.NormalDec(name, T), K) = collectDelTypes(T, K)
    and collectDelNewDec (D.NewDecLF (name, A), K) = collectExp ((A, I.id), K)
      | collectDelNewDec (D.NewDecMeta (name, F), K) = collectDelFormula (F, K)

    and collectDelTypes (D.LF (isP, A), K) =  collectExp((A, I.id), K)
      | collectDelTypes (D.Meta (isP, F), K) = collectDelFormula(F, K)

    and collectDelFormula (F, K) = collectDelFormulaW(D.whnfF F, K)
    and collectDelFormulaW (F as D.Top, K) = K
      | collectDelFormulaW (D.All(visible, W, D, F), K) = collectDelFormula(F, collectDelNormalDec(D, K))
      | collectDelFormulaW (D.Exists(D, F), K) = collectDelFormula(F, collectDelNormalDec(D, K))
      | collectDelFormulaW (D.Nabla(D, F), K) = collectDelFormula(F, collectDelNewDec(D, K))
      | collectDelFormulaW (D.FormList [], K) = K
      | collectDelFormulaW (D.FormList (F::Flist), K) = collectDelFormula(D.FormList Flist, collectDelFormula(F, K))
      | collectDelFormulaW (D.FVar _, K) = crash() (* should not have any FVars *)
      | collectDelFormulaW (D.FClo _, K) = crash() (* not in whnf *)


    (* abstractDelExp(K, depth, E) = E'
     * If G1,{{K}},G2 |- E : T
     * and K',K ||- E
     * then G1,{{K}},G2 |- E' : T'
     * and K' ||- E'
     *)


    and abstractDelBoundVarW (K, depth, E as D.Fixed _) = E
      | abstractDelBoundVarW (K, depth, B as D.BVarMeta ((r,F), s)) = 
	  let 
	    val Hopt = abstractMeta_BVar (K, depth, B)
	  in
	    case Hopt
	      of NONE => crash() (* why is there a BVar leftover.. *)
	       | SOME n => D.Fixed n
	  end

      | abstractDelBoundVarW (K, depth, B as D.BVarLF (r, s)) = 
	  let 
	    val Hopt = abstractLF_BVar2 (K, depth, B)
	  in
	    case Hopt
	      of NONE => crash() (* why is there a BVar leftover.. *)
	       | SOME n => D.Fixed n
	  end



    and abstractDelExp (K, depth, E) = abstractDelExpW (K, depth, D.whnfE E)
    and abstractDelExpW (K, depth, D.Var(B, fileInfo)) = D.Var (abstractDelBoundVarW(K, depth, B), fileInfo)
      | abstractDelExpW (K, depth, D.Quote U) = D.Quote (abstractExp(K, depth, (U, I.id))) 
      | abstractDelExpW (K, depth, E as D.Unit) = E
      | abstractDelExpW (K, depth, D.Lam (Clist, F, fileInfo)) = 
              let
		fun abstractC C = abstractDelCaseBranch(K, depth, C)
		val Clist' = map abstractC Clist
		val F' = abstractDelFormula(K, depth, F)
	      in
		D.Lam (Clist', F', fileInfo)
	      end

      | abstractDelExpW (K, depth, D.New (D, E, fileInfo)) = D.New (abstractDelNewDec (K, depth, D),
							     abstractDelExp(K, depth+1, E), fileInfo)

      | abstractDelExpW (K, depth, D.App (visible, E1, E2)) = D.App (visible,
								      abstractDelExp(K, depth, E1),
								      abstractDelExp(K, depth, E2))

      | abstractDelExpW (K, depth, D.Pair (E1, E2, F)) = D.Pair (abstractDelExp(K, depth, E1),
								 abstractDelExp(K, depth, E2),
								 abstractDelFormula(K, depth, F))

      | abstractDelExpW (K, depth, D.ExpList _) = crash() (* not a valid pattern *)

      | abstractDelExpW (K, depth, D.Proj _) = crash() (* not a valid pattern *)
	      
      | abstractDelExpW (K, depth, D.Pop (i, E)) = 
	      if (i > depth) then 
		crash() (* cannot abstract as point of reference is changed too far.  Should never happen by invariant *)
	      else
		D.Pop(i, abstractDelExp(K, depth-i, E))

      | abstractDelExpW (K, depth, D.Fix _) = crash() (* not a valid pattern *)

      | abstractDelExpW (K, depth, E as D.EVar ((r,F), s)) =
		let 
		  val Hopt = abstractMeta_EVar (K, depth, E)
		in
	    case Hopt
	      of NONE => crash() (* why is there a BVar leftover.. *)
	       | SOME n => 
		   let

		   in
		     D.Var(D.Fixed n, NONE)
		   end
		end
	      
      | abstractDelExpW (K, depth, D.EClo _) = crash() (* not in whnf *)


    and abstractDelCaseBranch(K, depth, D.Eps(D, C)) = D.Eps(abstractDelNormalDec(K, depth, D),
							     abstractDelCaseBranch(K, depth+1, C))
      | abstractDelCaseBranch(K, depth, D.NewC(D, C, fileInfo)) = D.NewC(abstractDelNewDec(K, depth, D),
									 abstractDelCaseBranch(K, depth+1, C),
									 fileInfo)
      | abstractDelCaseBranch(K, depth, D.PopC(i, C)) = crash() (* not a generated pattern *)
      | abstractDelCaseBranch(K, depth, D.Match(visibility, E1, E2)) = D.Match(visibility, 
									       abstractDelExp(K, depth, E1),
									       abstractDelExp(K, depth, E2))
      | abstractDelCaseBranch(K, depth, D.MatchAnd(visibility, E, C)) = D.MatchAnd(visibility,
										   abstractDelExp(K, depth, E),
										   abstractDelCaseBranch(K, depth, C))

      
    and abstractDelNormalDec (K, depth, D.NormalDec(name, T)) = D.NormalDec(name, abstractDelTypes(K, depth, T))
    and abstractDelNewDec (K, depth, D.NewDecLF (name, A)) = D.NewDecLF (name, abstractExp(K, depth, (A, I.id)))
      | abstractDelNewDec (K, depth, D.NewDecMeta (name, F)) = D.NewDecMeta(name, abstractDelFormula(K, depth, F))

    and abstractDelTypes (K, depth, D.LF (isP, A)) = D.LF(isP, abstractExp(K, depth, (A, I.id)))
      | abstractDelTypes (K, depth, D.Meta (isP, F)) = D.Meta(isP, abstractDelFormula(K, depth, F))

    and abstractDelFormula (K, depth, F) = abstractDelFormulaW(K, depth, D.whnfF F)
    and abstractDelFormulaW (K, depth, F as D.Top) = F
      | abstractDelFormulaW (K, depth, D.All(visible, W, D, F)) = D.All (visible, W, abstractDelNormalDec(K, depth, D),
							     abstractDelFormula(K, depth+1, F))
      | abstractDelFormulaW (K, depth, D.Exists(D, F)) = D.Exists (abstractDelNormalDec(K, depth, D),
								   abstractDelFormula(K, depth+1, F))
      | abstractDelFormulaW (K, depth, D.Nabla(D, F)) = D.Nabla (abstractDelNewDec(K, depth, D),
								 abstractDelFormula(K, depth+1, F))

      | abstractDelFormulaW (K, depth, D.FormList Flist) = D.FormList (map (fn F => abstractDelFormula(K, depth, F)) Flist)
      | abstractDelFormulaW (K, depth, D.FVar _) = crash() (* should not have any FVars *)
      | abstractDelFormulaW (K, depth, D.FClo _) = crash() (* not in whnf *)


    (* Takes one branch and abstracts all variables in it *)
    (* ADAM::  May not be used! *)
    fun getContext (C) =
              let
		val K = collectDelCaseBranch(C, I.Null)

		val _ = checkConstraints K
		val n = I.ctxLength K
		val C' = D.substCase (C, D.shiftTo(n, D.id))
		val Cnew = abstractDelCaseBranch(K, 0, C)
		val G = abstractKCtx(K, n-1)
	      in
		(G, Cnew)
	      end


    fun abstractCase (C) =
              let
		val K = collectDelCaseBranch(C, I.Null)

		val _ = checkConstraints K
		val n = I.ctxLength K
		val C' = D.substCase (C, D.shiftTo(n, D.id))
		val Cnew = abstractDelCaseBranch(K, 0, C')
		val Cfinal = abstractKEps(K, Cnew, n-1)
	      in
		Cfinal
	      end


    fun hasNoConstraintsExp A =
               let
		 val K = collectExp ((A, I.id), I.Null)
		 val b = (checkConstraints K ; true)
		        handle LeftOverConstraints => false
	       in
		 b
	       end

    fun isRecursiveOrConstraints(a, U) =
               let
		 val K = collectExp ((U, I.id), I.Null)
		 fun testVars I.Null = false
		   | testVars (I.Decl(K, LF_EV (I.EVar (_, GY, VY, _)))) = (Subordinate.belowEq (a, I.targetFam VY)) orelse (testVars K)
		   (* Not necessary?
		   | testVars (I.Decl(K, BV (D.BVarLF ((r, VY), _)))) = (Subordinate.belowEq (a, I.targetFam VY)) orelse (testVars K)
		    *)
		   | testVars (I.Decl(K, _)) = testVars K

		 val isRecursive = testVars K

		 val hasConstraints = (checkConstraints K ; false)
		   handle LeftOverContraints => true
	       in
		 isRecursive orelse hasConstraints
	       end

    fun hasNoConstraintsCase C =
               let
		 val K = collectDelCaseBranch (C, I.Null)
		 val b = (checkConstraints K ; true)
		        handle LeftOverConstraints => false
	       in
		 b
	       end


end