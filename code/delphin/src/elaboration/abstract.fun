(* Abstraction *)
(* Author:  Adam Poswolsky *)
(* Based on Twelf Abstraction written by
     Frank Pfenning, Carsten Schuermann, Roberto Virga
*)
(* ABP:  Biggest(important) difference from Twelf is that collection does not collect necessarily
 *       ALL Vars.. only those specified.  Otherwise it remains as a Var
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
    structure D' = DelphinIntSyntax
    val Existential = D'.Existential
    val Param = D'.Param

    fun crash() = raise Domain

    fun addOne(NONE) = NONE
      | addOne(SOME (d1,d2)) = SOME (d1+1, d2+1)
      
    (* subtract but keep >= 0 *)
    (* the "depth" that this represents is only used for an enhancement
     * in abstracting EVars... it is always valid to disable it (turn to NONE)
     *)
    fun subtractPop(NONE, x) = NONE
      | subtractPop(SOME (d1,d2), x) = if (x > d1) orelse (x > d2) 
					 then NONE else SOME (d1 - x, d2-x)

    (* Intermediate Data Structure *)

    datatype EFLPVar =
      EV of Paths.region * I.Exp * (((I.Exp option) * int * (int list)) ref) 	   
                                             (* Y ::= X         for  GX |- X : VX   
					      * The type is saved in an option ref.
					      *)
    | FV of Paths.region * string * (bool ref) * I.Exp 	 (*     | (F, b, V)        if (G) |- F : V  *)
                                                         (*              and b is true if it is a parameter *)
    | LV of Paths.region * I.Block                       (*     | L             if . |- L in W  *) 
    | PV of Paths.region * string * string               (*     | PatVar (Delphin -- (name and original name) )  *)




    (* collectConstraints K = cnstrs
       where cnstrs collects all constraints attached to EVars in K
    *)
    fun collectConstraints (I.Null) = nil
      | collectConstraints (I.Decl (G, FV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, LV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, PV _)) = collectConstraints G
      | collectConstraints (I.Decl (G, EV (_, I.EVar (_, _, _, ref nil), _))) = collectConstraints G
      | collectConstraints (I.Decl (G, EV (r, I.EVar (_, _, _, ref cnstrL), _))) =
               let
		 val constraints = C.simplify cnstrL
	       in
		 case constraints of
		   nil => collectConstraints G
		   | _ => (r, constraints) :: (collectConstraints G)
	       end
      | collectConstraints (I.Decl (G, EV _)) = crash() (* A non EVar stored in EV.. *)

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
    fun eqEVar (I.EVar (r1, _, _, _)) (EV (_, I.EVar (r2, _, _, _), _)) = (r1 = r2)
      | eqEVar _ _ = false

    (* eqFVar F Y = B
       where B iff X and Y represent same variable
    *)
    fun eqFVar (I.FVar (n1, false, _, _)) (FV (_, n2, _,  _)) = (n1 = n2)
      | eqFVar (I.FVar (n1, true, _, _)) (FV (_, n2, b,  _)) = if (n1 = n2) then (b := true ; true) else false
      | eqFVar _ _ = false

    (* eqLVar L Y = B
       where B iff X and Y represent same variable
    *)
    fun eqLVar (I.LVar ((r1, _, _))) (LV (_, I.LVar ((r2, _, _)))) = (r1 = r2)
      | eqLVar _ _ = false

    (* eqPatVar *)
    fun eqPatVar (D.PatVar (_, n1, _)) (PV (_,n2, _)) = (n1 = n2)
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



    (* abstractEVar (K, depth, X) = C'
     
       Invariant:
       If   G |- X : V
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractEVar (I.Decl (K', EV (_, I.EVar(r',GX,VX,_), typeRef)), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then SOME(I.BVar (I.Fixed (depth+1)), GX, VX, typeRef)
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
    fun abstractPatVar (I.Decl(K', PV (_, n1, _)), depth, P as D.PatVar(r, n2, _)) =
          if n1 = n2 then D.VarInt(r, depth+1)
	  else abstractPatVar (K', depth+1, P)
      | abstractPatVar (I.Decl(K', _), depth, P) =
	    abstractPatVar (K', depth+1, P)
      | abstractPatVar (I.Null, _, P) = P

      
      

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




    (* collectExpW ((U, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
	     where K'' contains all EVars and FVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
  (* ENHANCEMENT:  depth is an (int option) indicating how far it is to the global context.  
   * this is only used as an enhancement in abstracting EVars...
   *)


    (* getType (G*,GX, s, V, n) = ({GX}V)[s']
     * where |GX| = n
     * if G*,GX |- V : type
     * and G |- s : GX
     * then s = M1...Mn.s' and G |- s' : G*
     * and G |- ({GX}V)[s'] : type
     *)
    fun getType (GX, s, V, 0) = I.EClo(V, s)
      | getType (GX, I.Shift k, V, size) = getType (GX, I.Dot (I.Idx (k+1), I.Shift(k+1)), V, size)
      | getType (I.Decl(GX, D), I.Dot(Ft, s), V, size) =
	             (* G*,GX,D |- V : type
		      * G*,GX |- Pi(D).V : type
		      * G |- s : GX 
		      *
		      * Recursive call gives us:  ({GX}({D}.V))[s']
		      * And {GX}({D}.V) = {GX,D}V
		      *)
	              getType(GX, s, I.Pi((D, I.Maybe), V), size-1)
      | getType _ = crash() (* broken invariant *)


fun LFcollectExp (reg, depthStart, (U, s), K, allowVars) =
  (* if allowVars then collect all EVars/FVars,
   * otherewise just check that there are no vars not in K.
   *)
  let
    fun collectExpW (depth, (I.Uni L, s), K) = K
      | collectExpW (depth, (I.Pi ((D, _), V), s), K) =
          collectExp (addOne(depth), (V, I.dot1 s), collectDec (depth, (D, s), K))
      | collectExpW (depth, (I.Root (F as I.FVar (name, isP, V, s'), S), s), K) =
	if exists (eqFVar F) K
	  then collectSpine (depth, (S, s), K)
	else (* s' = ^|G| *)
	  if allowVars then
	    collectSpine (depth, (S, s), I.Decl (collectExp (depth, (V, I.id), K), FV (reg, name, ref isP, V)))
	  else
	    raise Error (reg, "Variable " ^ name ^ " not defined.")
      | collectExpW (depth, (I.Root (I.Proj (L as I.LVar (r, _, (l, t)), i), S), s), K) =
	if exists (eqLVar L) K
	  (* note: don't collect t again below *)
	  (* was: collectSpine (G, (S, s), collectSub (I.Null, t, K)) *)
	  (* Sun Dec 16 10:54:52 2001 -fp !!! *)
	  then collectSpine (depth, (S, s), K)
	else 
	  if allowVars then
	    (* -fp Sun Dec  1 21:12:12 2002 *)
	    collectSpine (depth, (S, s), I.Decl (collectSub (depth, I.comp(t,s), K), LV (reg, L)))
	  else
	    raise Error (reg, "Ambiguous Term (Leftover LVar)")

      | collectExpW (depth, (I.Root (_ , S), s), K) =
	  collectSpine (depth, (S, s), K)
      | collectExpW (depth, (I.Lam (D, U), s), K) =
	  collectExp (addOne(depth), (U, I.dot1 s), collectDec (depth, (D, s), K))

      | collectExpW (NONE, (X as I.EVar (r, GX, V, cnstrs), s), K) =

	  let
	    val (infoOpt) = case (abstractEVar (K, 0 (* doesn't matter *), X))
	                         of NONE => NONE
			          | SOME (_, _, _, info) => SOME info
	    val V' = getType(GX, s, V, I.ctxLength GX)
	    val K' = collectExp (NONE, (V', I.id), K)
	  in
	    case infoOpt
	      of NONE (* does not exist *) =>
		   if allowVars then
			  collectSub(NONE, s, I.Decl (K', EV (reg, X, ref (NONE, I.ctxLength GX, []))))
		   else
		     raise Error (reg, "Ambiguous Term (Leftover EVar)")

	       | SOME info => 
		       (info := (NONE, I.ctxLength GX, []) ; collectSub(NONE, s, K'))
	  end


      | collectExpW (SOME (globalDepth, localDepth), (X as I.EVar (r, GX, V, cnstrs), s), K) =
	  let
	    fun fixSub (t as I.Shift _) = t
	      | fixSub (I.Dot(I.Exp U, t)) = 
	           let
		     val nOpt = SOME(Whnf.etaContract U)
		       handle Whnf.Eta => NONE
		   in
		     case nOpt
		       of (SOME n') => (I.Dot (I.Idx n', fixSub t))
		     | _ => I.Dot (I.Exp U, fixSub t)
		   end		
	      | fixSub (I.Dot(Ft, t)) = I.Dot(Ft, fixSub t)


	    val s = fixSub s


	    (* ********************************************************* *)
	    (* Routines to create initial EVAR information *)
	    (* ********************************************************* *)


	    (* checks if the sub only maps elements to global context *)
	    (* and returns a list of the elements it maps to (offset by globalDepth) *)
	    fun checkSub (I.Null, _) = SOME []
	      | checkSub (GX, I.Shift k) = checkSub (GX, I.Dot (I.Idx (k+1), I.Shift (k+1)))
	      | checkSub (I.Decl(GX, _), I.Dot(I.Idx k1, s1))= 
	           if (k1 > localDepth) then
	             (case (checkSub (GX,s1))
			of NONE => NONE
			 | SOME l => SOME ((k1-globalDepth)::l)
		     )
		   else
		     NONE

	      | checkSub _ = NONE


	    fun getSize(I.Null, s, size) = (size, [])
	      | getSize(GX, I.Shift k, size) = getSize (GX, I.Dot (I.Idx (k+1), I.Shift (k+1)), size)
	      | getSize(I.Decl(GX, D), I.Dot (I.Idx k, s), size) = 
	                     if (k > localDepth) then
			       (case (checkSub (GX, s))
				  of NONE => getSize(GX, s, size+1)
				   | SOME(rest) => (size, (k-globalDepth)::rest)
			       )
			     else
			       getSize(GX, s, size+1)
	      | getSize(I.Decl(GX, D), I.Dot (_, s), size) = getSize(GX, s, size+1)



	    (* ********************************************************* *)
	    (* Routines to update EVAR information *)
	    (* ********************************************************* *)


	    fun checkSpine (I.Null, _, _) = SOME []
	      | checkSpine (GX, I.Shift k, spine) = checkSpine (GX, I.Dot (I.Idx (k+1), I.Shift (k+1)), spine)
	      | checkSpine (I.Decl(GX, _), I.Dot(I.Idx k1, s1), (k'::spine))= 
	           if ((k1-globalDepth) = k') then
	             (case (checkSpine (GX,s1, spine))
			of NONE => NONE
			 | SOME l => SOME(k'::l)
		     )
		   else
		     NONE

	      | checkSpine _ = NONE


	    fun updateSize(I.Null, s, size, _) = (size, [])
	      | updateSize(GX, I.Shift k, size, spine) = updateSize (GX, I.Dot (I.Idx (k+1), I.Shift (k+1)), size, spine)
	      | updateSize(I.Decl(GX, D), I.Dot (I.Idx k, s), size, (k' :: spine)) = 
			       if ((k-globalDepth) = k') then
				 (case (checkSpine (GX, s, spine))
				    of NONE => updateSize(GX, s, size+1, spine)
				     | SOME(rest) => (size, k'::rest))
			       else
				 updateSize(GX, s, size+1, spine)
				 
	      | updateSize(I.Decl(GX, D), I.Dot (_, s), size, (_::spine)) = updateSize(GX, s, size+1, spine)
	      | updateSize _ = crash() 


		   
	  in
	    (* Determine the number of elements in GX that we want to abstract..
	     * The ones that point to elements > localDepth would create terms outside the
	     * decidable pattern-fragment in unification.
	     * In other words, the local context GX makes sense in ".", but there
	     * are "global" elements.. so GX = Gglobal,GX'.  Here we determine what GX' is.
	     * However, this same EVar may be ambiguous based on how it is used.. So we use
	     * a reference so we can update the "size" and type.
	     *
	     * For example, without this enhacement, inside the context G,A,B it is possible
	     * we will create G,A,B |- fn [<E:...>] <E A B> => ... <E A B> ...
	     * As "A" and "B" are in the global context, we can replace this with
	     * fn [<E'>]<E'> => ... <E'> ... which now is in the pattern fragment.
	     * So we need to determine what the maximum matching spine is..
	     * For example, if E is used as "E A B"  and as "E A M", then the best
	     * we can do is to collapse it into "E' B" and "E' M".  This is why we use refernces
	     * to update the actual "size" as we see how it is used.
	     *)

	    case (abstractEVar (K, 0 (* doesn't matter *), X))
	     of NONE => 
	         let
		   val (size1, spine1) = getSize (GX, s, 0)
		   val V1 = getType(GX, s, V, size1)
		   val K' = collectExp (SOME (globalDepth, localDepth), (V1, I.id), K)
		 in
		   if allowVars then
			  collectSub(SOME (globalDepth, localDepth), s, 
				     I.Decl (K', EV (reg, X, ref (NONE, size1, spine1))))
		   else
		     raise Error (reg, "Ambiguous Term (Leftover EVar)")
		end

	       | SOME(_, _, _, info as ref(_ (* oldV *), oldSize, oldGlobalSpine)) =>
		 let
		   fun removeElements(G, s, 0) = (s, G)
		     | removeElements(I.Decl(G, _), I.Dot(_, s), n) = removeElements(G, s, n-1)
		     | removeElements(G, I.Shift k, n) = removeElements(G, I.Dot(I.Idx (k+1), I.Shift (k+1)), n)
		     | removeElements _ = crash()

		   val (s', GX') = removeElements(GX, s, oldSize)
		   val (size1, spine1) = updateSize(GX', s', oldSize, oldGlobalSpine)
		   val V1 = getType(GX, s, V, size1)
		   val K' = collectExp (SOME (globalDepth, localDepth), (V1, I.id), K)
		     
		 in
		   (info := (NONE, size1, spine1) ; 
		             collectSub(SOME (globalDepth, localDepth), s, K'))
		 end

	  end


      | collectExpW (depth, (I.FgnExp csfe, s), K) =
	  I.FgnExpStd.fold csfe (fn (U, K) => collectExp (depth, (U, s), K)) K
      (* No other cases can occur due to whnf invariant *)
      | collectExpW _ = crash()

    (* collectExp (depth, (U, s), K) = K' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (depth, Us, K) = collectExpW (depth, Whnf.whnf Us, K)

    (* collectSpine (depth, (S, s), K) = K' 

       Invariant: 
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
    and collectSpine (depth, (I.Nil, _), K) = K
      | collectSpine (depth, (I.SClo(S, s'), s), K) = 
          collectSpine (depth, (S, I.comp (s', s)), K)
      | collectSpine (depth, (I.App (U, S), s), K) =
	  collectSpine (depth, (S, s), collectExp (depth, (U, s), K))

    (* collectDec ((x:V, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
    and collectDec (depth, (I.Dec (_, V), s), K) =
          collectExp (depth, (V, s), K)
      | collectDec (depth, (I.BDec (_, (_, t)), s), K) =
	  (* . |- t : Gsome, so do not compose with s *)
	  (* Sat Dec  8 13:28:15 2001 -fp *)
	  collectSub (depth, t, K)

      (* ABP -- added NDec *)
      | collectDec (depth, (I.NDec, s), K) = K
      | collectDec _ = crash()

    (*
       Invariant: 
       If    G |- s : G1    
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    and collectSub (depth, I.Shift _, K) = K
      | collectSub (depth, I.Dot (I.Idx _, s), K) = collectSub (depth, s, K)
      | collectSub (depth, I.Dot (I.Exp (U), s), K) =
	  collectSub (depth, s, collectExp (depth, (U, I.id), K))
      | collectSub (depth, I.Dot (I.Block B, s), K) =
	  collectSub (depth, s, collectBlock (depth, B, K))
    (* next case is not impossible because we allow ECLo with undefs if we know it doesn't actually use it..
     * maybe we should apply it out to get rid of such undefs..
     *)
      | collectSub (depth, I.Dot (I.Undef, s), K) =
          collectSub (depth, s, K)

    (* collectBlock (B, K) where G |- B block *)
    and collectBlock (depth, I.LVar (ref (SOME B), sk , _), K) =
          collectBlock (depth, I.blockSub (B, sk), K)
          (* collectBlock (B, K) *)
          (* correct?? -fp Sun Dec  1 21:15:33 2002 *)
      | collectBlock (depth, L as I.LVar (_, sk, (l, t)), K) = 
        if exists (eqLVar L) K
	  then collectSub (depth, t, K)
	else 
	  if allowVars then
	    I.Decl (collectSub (depth, t, K), LV (reg, L))
	  else
	    raise Error (reg, "Ambiguous Term (Leftover LVar)")

      | collectBlock _ = crash()
    (* | collectBlock (I.Bidx _, K) = K *)
    (* should be impossible: Fronts of substitutions are never Bidx *)
    (* Sat Dec  8 13:30:43 2001 -fp *)

  in
    collectExp(depthStart, (U, s), K)
  end





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
		    abstractExp (K, depth+1, (V, I.dot1 s)))
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
		 abstractExp (K, depth+1, (U, I.dot1 s)))
      | abstractExpW (K, depth, (X as I.EVar _, sX)) =
	  let 
	    val Hopt = abstractEVar (K, depth, X)
	  in
	    case Hopt
	      of NONE => I.EClo(X, abstractSubToSub(K, depth, sX))

	       | SOME (H, GX, VX, r as ref (Vopt, n, spine)) => 
		   let		
		     val _ = case Vopt of
		             SOME _ => ()
			     | NONE => (* fill in type *)
			               let
					 val str = Whnf.invert (I.Shift (depth + I.ctxLength K) )
					 (* str will bring us from G into the global context where it is actually abstracted 
					  * the " + ctxlength K" is used to adjust that we undergo a shift of that size before 
					  * doing abstraction to make room for the n elements
					  *
					  * We assume that all types in "K" make sense with respect to the same context, and
					  * this fills in the type.  It is necessary to fill in the type here as it needs the
					  * substitution "sX" to fill in information (esp. important when n < size(GX) )
					  *)
					 val V' = getType(GX, I.comp(sX, str), VX, n)
				       in
					 r :=  (SOME V', n, spine)
				       end

		     (* GX = GXglobal,GXlocal
		      * |GXlocal| = n
		      * sX = Mn....M1.s'
		      * G |- Mn..M1.s' : GXglobal,GXlocal
		      * G |- Vopt == ({GXlocal}VX)[s']
		      *)
		     val S = abstractSub (K, depth, sX, n, I.Nil)
		      (*
		       * Assuming GXlocal = B1,...Bn
		       * Then Vopt = ({B1,..Bn}VX)[s']
		       * and S is a spine of types B1[s'] .... Bn[M(n-1)....M1.s']
		       * and more specifically, S = M1 .... Mn.
		       * We now need to show that if  E : Vopt, then
		       * E M1 ... Mn :  VX[Mn...M1.s']
		       * (Proof by induction on n)
		       *)
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
      | abstractSubToSub (K, depth, I.Dot(I.Block B, s)) = I.Dot(I.Block (abstractBlock(K, depth, (B, I.id))), abstractSubToSub (K, depth, s))
      | abstractSubToSub (K, depth, I.Dot(I.Undef, s)) = I.Dot(I.Undef, abstractSubToSub (K, depth, s))
      
    and abstractBlock (K, depth, B) = crash() (* ADAM:  We don't need blocks anymore.. right??? *)



    (* abstractSub (K, depth, s, n, S) = SS
     *
     * If  G' |- Mn...M1.s : G*,A1,...An
     * and G' |- S is a spine of type B1...Bm of the form N1...Nm
     *
     * then G' |-  SS is a spine of types A1[s] ... An[M(n-1)....M1.s] . B1 ... Bm
     * of the form M1 .... Mn. N1 ... Nm
     *)
     
    and abstractSub (K, depth, s, 0, S) = S
      | abstractSub (K, depth, I.Shift k, size, S) = abstractSub (K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), size, S)
      | abstractSub (K, depth, I.Dot (I.Idx (k), s), size, S) =
	    (* G' |- k.s : G*,A1,...An
	     * G' |- S is a spine of types B1 ... Bm of the form N1...Nm
	     *
	     * G' |- s : G*,A1,...A(n-1)
	     * G' |- k@S is a spine of types An[s],B1...Bm of the form k. N1...Nm, where Mn = k
	     *)
	    abstractSub (K, depth, s, size-1, I.App (I.Root (I.BVar (I.Fixed k), I.Nil), S))
      | abstractSub (K, depth, I.Dot (I.Exp (U), s), size, S) =
	  abstractSub (K, depth, s, size-1, I.App (abstractExp (K, depth, (U, I.id)), S))
      | abstractSub _ = crash()

    (*  OLD

    (* abstractSub (K, depth, s, GX, VX, S) = (SS, V', remaining)
     *
     * If  G' |- s : GX
     * and GX |- VX :type
     * and G' |- S : VX[s] (* S is a spine to be applied to a term of type VX[s] *)
     *
     * then G' |-  V' : type
     * and G' |- SS : V' (* SS is a spine to be applied to a term of type V' *)
     * and "remaining" indicates the number of elements in GX that we do not abstract.
     * 
     * UPDATE:  Stops when GX is mapped to elements of the global context.
     *  This is useful as EVars all make sense in the "empty" context, but 
     *  we are not abstracting them all the way to the front.  Note that
     *  we can apply them out, but then we will get patterns that fall out of the
     *  decidable pattern fragment.  Here we are assuming that once an EVar is mapped to
     *  something in the global context, then the rest are also mapped to the global context.
     *  This is due to our formation of EVars.  
     *)
     
    and abstractSub (K, depth, s, I.Null, VX, S) = (S, I.EClo(VX, s), 0)
      | abstractSub (K, depth, I.Shift k, GX, VX, S) = abstractSub (K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), GX, VX, S)
      | abstractSub (K, depth, sub as I.Dot (I.Idx (k), s), I.Decl(GX, D), VX, S) =
          if (k > depth) then
	       (* This would not be in the pattern fragment.. and we don't need it because this index is to the left of where the
		* EVar is being abstracted *)
	         (S, I.EClo(VX, sub), (I.ctxLength GX) + 1)
	  else
	    (* G' |- k.s : GX,A
	     * G' |- S is a spine of types A1...An
	     *
	     * G' |- s : GX
	     * G' |- k@S is a spine of types A,A1...An
	     *)
	    abstractSub (K, depth, s, GX, I.Pi ((D, I.Maybe), VX), I.App (I.Root (I.BVar (I.Fixed k), I.Nil), S))
      | abstractSub (K, depth, I.Dot (I.Exp (U), s), I.Decl(GX, D), VX, S) =
	  abstractSub (K, depth, s, GX, I.Pi ((D, I.Maybe), VX), I.App (abstractExp (K, depth, (U, I.id)), S))
      | abstractSub _ = crash()
	  *)
 
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


    fun addImplicitToF (_, D, D.All (r, Ds, F)) = D.All (r, (D'.Implicit, D) :: Ds, F)
      | addImplicitToF (r, D, F) = D.All (r, [(D'.Implicit, D)], F)                          

    fun abstractKAll (I.Null, F, ~1) = F
      | abstractKAll (I.Null, F, numShifts) = crash() (* numShifts should be ~1 *)
      | abstractKAll (I.Decl (K', EV (r, I.EVar (_, GX, VX, _), ref (SOME (V'), _, _))), F, numShifts) =
        let
	  val r = Paths.join(r, D.getRegionF F)
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in	 
	  abstractKAll (K', addImplicitToF (r, D.NormalDec(r, NONE, D.LF(r, Existential, V'')), F), numShifts-1)
	end
      | abstractKAll (I.Decl (K', FV (r, name,ref isP, V')), F, numShifts) =
	let
	  val r = Paths.join(r, D.getRegionF F)
	  val isP' = if isP then Param else Existential
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in
	  abstractKAll (K', addImplicitToF (r, D.NormalDec(r, SOME name, D.LF(r, isP', V'')), F), numShifts-1)
	end
      | abstractKAll (I.Decl (K', LV (_, I.LVar (r, _, (l, t)))), F, _) = crash() (* Can't handle blocks *)
      | abstractKAll (I.Decl (K', PV (r,name, origName)), F, numShifts) = 
	let
	  val r = Paths.join(r, D.getRegionF F)
	in
	  abstractKAll (K', addImplicitToF (r, D.NormalDec(r, SOME origName, D.Meta(r, D.OmittedFormula r)), F), numShifts-1)
	end

      | abstractKAll _ = crash()


    (* ADAM WARNING:  Region (r) information perhaps should be extended to handle entire block using Paths.join... *)
    fun abstractKEps (I.Null, C, ~1) = C
      | abstractKEps (I.Null, C, numShifts) = crash() (* numShifts should be ~1 *)
      | abstractKEps (I.Decl (K', EV (r, I.EVar (_, GX, VX, _), ref (SOME (V'), _, _))), C, numShifts) =
        let
	  val r = Paths.join(r, D.getRegionC C)
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in	 
	  abstractKEps (K', D.Eps (r, D.NormalDec(r, NONE, D.LF(r, Existential, V'')), C), numShifts-1)
	end
      | abstractKEps (I.Decl (K', FV (r, name,ref isP, V')), C, numShifts) =
	let
	  val r = Paths.join(r, D.getRegionC C)
	  val isP' = if isP then Param else Existential
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in
	  abstractKEps (K', D.Eps (r, D.NormalDec(r, SOME name, D.LF(r, isP', V'')), C), numShifts-1)
	end
      | abstractKEps (I.Decl (K', LV (_, I.LVar (r, _, (l, t)))), C, _) = crash() (* Can't handle blocks *)
      | abstractKEps (I.Decl (K', PV (r,name, origName)), C, numShifts) = 
	let
	  val r = Paths.join(r, D.getRegionC C)
	in
	  abstractKEps (K', D.Eps(r, D.NormalDec(r, SOME origName, D.Meta(r, D.OmittedFormula r)), C), numShifts-1)
	end

      | abstractKEps _ = crash()





 (* NO LONGER USED
    (* ADAM WARNING:  Region (r) information perhaps should be extended to handle entire block using Paths.join... *)

    (* abstractKCtx (K, |K|-1) = G (lf-level context)
     * Precondition:  K does not contain any meta-level decs
     *)
    fun abstractKCtx (I.Null, ~1) = I.Null
      | abstractKCtx (I.Null, numShifts) = crash() (* numShifts should be ~1 *)
      | abstractKCtx (I.Decl (K', EV (r, I.EVar (_, GX, VX, _), ref (V', _, _))), numShifts) =
        let
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in	 
	  I.Decl(abstractKCtx (K', numShifts-1), D'.InstantiableDec (D'.NormalDec(NONE, D'.LF(D'.Existential, V''))))
	end
      | abstractKCtx (I.Decl (K', FV (r, name, ref isP, V')), numShifts) =
	let
	  val isP' = if isP then Param else Existential
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in
	  I.Decl(abstractKCtx (K', numShifts-1), D'.InstantiableDec (D'.NormalDec(NONE, D'.LF(isP', V''))))
	end
      | abstractKCtx (I.Decl (K', LV (_, I.LVar (r, _, (l, t)))), _) = crash() (* Can't handle blocks *)
      | abstractKCtx (I.Decl (K', PV (r,name, origName)), numShifts) = crash() (* this should only be called on world declarations.. so no meta level *)
      | abstractKCtx _ = crash()
*)

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
      | abstractDelExp (K, depth, D.Quote (r, U, A, I, isP)) = D.Quote (r, abstractExp(K, depth, (U, I.id)), 
								       abstractExp(K, depth, (A, I.id)),
								       I, isP)

      | abstractDelExp (K, depth, E as D.Unit _) = E
      | abstractDelExp (K, depth, D.Lam (isSugar, r, Clist, Fopt)) =
          (* ADAM WARNING:  Right now we just ignore Fopt and replace it with NONE.
	   * This is accounted for in convert.fun .  But it would be better to handle
	   * collecting/abstracting Fopt here rather than having to do "update" twice in convert.fun
	   *)
              let
		fun abstractC C = abstractDelCaseBranch(K, depth, C)
		val Clist' = map abstractC Clist
	      in
		D.Lam (isSugar, r, Clist', NONE)
	      end


      | abstractDelExp (K, depth, D.New (r, D, E)) = D.New (r, abstractDelNewDec (K, depth, D),
							     abstractDelExp(K, depth+1, E))

      | abstractDelExp (K, depth, D.App (r, E1, args)) = D.App (r, 
								abstractDelExp(K, depth, E1),
								map (fn (visible, E2) => (visible, abstractDelExp(K, depth, E2))) args)

      | abstractDelExp (K, depth, D.Pair (r, E1, E2)) = D.Pair (r, abstractDelExp(K, depth, E1),
								 abstractDelExp(K, depth, E2))

      | abstractDelExp (K, depth, D.Proj (r, E, i)) = D.Proj(r,
							      abstractDelExp(K, depth, E),
							      i)
	      
      | abstractDelExp (K, depth, D.Pop (r, i, E)) = 
	      if (i > depth) then 
		D.Pop(r, i, E) (* nothing to abstract *)
	      else
		D.Pop(r, i, abstractDelExp(K, depth-i, E)) 

     (* not used
      | abstractDelExp (K, depth, D.Fix (r, funList)) = 
		D.Fix (r, abstractDelFunList (K, depth, funList))
     *)

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


      | abstractDelExp (K, depth, D.ExtendFunWith (r, E, Clist, sizeG2a, sizeG2b, isSugar, Fopt)) =
          (* ADAM WARNING:  Right now we just ignore Fopt and replace it with NONE.
	   * This is accounted for in convert.fun .  But it would be better to handle
	   * collecting/abstracting Fopt here rather than having to do "update" twice in convert.fun
	   *)

		let
		  val E' = if ((sizeG2a + sizeG2b) > depth) then 
				 E (* nothing to abstract *)
			   else
		                 abstractDelExp(K , depth - sizeG2b - sizeG2a, E)


		  val Clist' = if (sizeG2b > depth) then 
				 Clist (* nothing to abstract *)
			       else
		                 map (fn C => abstractDelCaseBranch(K, depth-sizeG2b, C)) Clist
		in
		  D.ExtendFunWith (r, E', Clist', sizeG2a, sizeG2b, isSugar, NONE)
		end
			    

    and abstractDelFunList (K, depth, []) = []
      | abstractDelFunList (K, depth, (r,D,E)::funList) = 
                (r, abstractDelNormalDec(K, depth, D), abstractDelExp(K, depth+1, E)) ::
		(abstractDelFunList (K, depth, funList))

    and abstractDelCaseBranch (K, depth, D.Eps (r, D, C)) = D.Eps (r, abstractDelNormalDec (K, depth, D),
								abstractDelCaseBranch (K, depth+1, C))

      | abstractDelCaseBranch (K, depth, D.NewC (r, D, C)) = D.NewC (r, abstractDelNewDec (K, depth, D),
							      abstractDelCaseBranch (K, depth+1, C))
(* Removed PopC
      | abstractDelCaseBranch (K, depth, D.PopC (r, i, C)) = 	      
                                             if (i > depth) then 
					       D.PopC (r, i, C) (* nothing to abstract *)
					     else
					       D.PopC(r, i, abstractDelCaseBranch(K, depth-i, C))
*)


      | abstractDelCaseBranch (K, depth, D.Match (r, pats, E2)) = D.Match (r, 
									   map (fn (vis, E1) => (vis, abstractDelExp(K, depth, E1))) pats,
									   abstractDelExp(K, depth, E2))


      (* OLD
      | abstractDelCaseBranch (K, depth, D.MatchAnd (r, visible, E, C)) = D.MatchAnd (r, visible, abstractDelExp(K, depth, E),
								       abstractDelCaseBranch(K, depth, C))
       *)
      
    and abstractDelNormalDec (K, depth, D.NormalDec(r, name, T)) = D.NormalDec(r, name, abstractDelTypes(K, depth, T))
    and abstractDelNewDec (K, depth, D.NewDecLF (r, name, A)) = D.NewDecLF (r, name, abstractExp(K, depth, (A, I.id)))
      | abstractDelNewDec (K, depth, D.NewDecWorld (r, name, W)) = D.NewDecWorld(r, name, W)

    and abstractDelTypes (K, depth, D.LF (r, isP, A)) = D.LF(r, isP, abstractExp(K, depth, (A, I.id)))
      | abstractDelTypes (K, depth, D.Meta (r, F)) = D.Meta(r, abstractDelFormula(K, depth, F))

    and abstractDelFormula (K, depth, F as D.Top _) = F
      | abstractDelFormula (K, depth, D.All(r, Ds, F)) = 
            let
	      fun abstract ([], d) = ([], d)
		| abstract ((vis, D)::Ds, d) = 
		     let
		       val D' = abstractDelNormalDec (K, d, D)
		       val (Ds', d') = abstract (Ds, d+1)
		     in
		       ((vis, D') :: Ds', d')
		     end
	      val (Ds', depth') = abstract (Ds, depth)
	    in
	      D.All (r, Ds', abstractDelFormula(K, depth', F))
	    end

      | abstractDelFormula (K, depth, D.Exists(r, D, F)) = D.Exists (r, abstractDelNormalDec(K, depth, D),
								   abstractDelFormula(K, depth+1, F))
      | abstractDelFormula (K, depth, D.Nabla(r, D, F)) = D.Nabla (r, abstractDelNewDec(K, depth, D),
								 abstractDelFormula(K, depth+1, F))
      | abstractDelFormula (K, depth, F as D.FormulaString _) = F (* F makes sense in the empty context without any EVars, so there cannot be anything to abstract *)
      | abstractDelFormula (K, depth, F as D.OmittedFormula _) = F




    fun ctxRemovePrefix(_, I.Null) = I.Null
      | ctxRemovePrefix(i, G) = 
                   let
		     val n = I.ctxLength G
		   in
		     if (i = n) then I.Null
		     else if (n > i) then 
		       (case G of 
			  I.Decl(G', D) => I.Decl(ctxRemovePrefix(i, G'), D)
			| _ => crash())
		     else crash()
		   end
		      
		      
		 
   (* ************************************************************ *)
   (* ************************************************************ *)
   (* Delphin Specific Abstraction *)
   (* ************************************************************ *)
   (* ************************************************************ *)
      
   (* transformDelExp (depth, E, K) = (E', K)
    *
    *  G |- E : T
    *  Precondition:  All Vars in G are contained in K 
    *
    *  (1) Recursively abstracts delphin program (deduces pattern variables) to E'
    *  (2) Left-over EVars/FVars are added to K and result is K' (if allowedVars is false then K = K')
    *)
  (* ENHANCEMENT:  depth is an (int option) indicating how far it is to the global context.  
   * this is only used as an enhancement in abstracting EVars...
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
    fun transformC depth Kinitial (D.Match (r, pats, E2)) =
           let
	     fun transformPats ([], K) = ([], K)
	       | transformPats ((vis, E1)::pats, K) =
	             let
		       val (E1', K') = transformDelExp(depth, E1, K, true)
		       val (pats', K'') = transformPats (pats, K')
		     in
		       ((vis, E1')::pats', K'')
		     end
	     val (pats', K0) = transformPats (pats, Kinitial)
	     val (E2', K) = transformDelExp(depth, E2, K0, false)
	     val C' = D.Match(r, pats', E2')
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


      | transformC depth Kinitial (D.Eps (r, D, C)) = 
	   let
	     val K = collectDelNormalDec(depth, D, Kinitial, true)
	     val C' = D.Eps(r, D, transformC (addOne depth) K C)
	       
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
	 
(* Removed PopC 
      | transformC depth Kinitial (D.PopC (r, i, C)) = 
	   let
	     val C' = transformC (SOME 0)??? Kinitial C (* abstraction occurs under the PopC *)
	   in
	     D.PopC(r, i, C')
	   end		      
*)

       | transformC depth Kinitial (C as D.NewC _) =
	   let
	     (* We want to collect all variables to the LEFT of NewC
	      * so we call transformDelCaseBranch which transforms and collects a list of variables to abstract
	      *)
	     val (C', K) = transformDelCaseBranch(depth, C, Kinitial) (* allowVars = true *)
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

    and transformDelExp (depth, E as D.VarInt _, K, allowVars) = (E, K)
      | transformDelExp (depth, E as D.Quote (r,U,A,I,isP), K, allowVars) = 
           let
	     (* update FVar based on isP if possible... *)
	     val U' = case (D'.whnfP isP, Whnf.whnf (U, I.id))
	              of (D'.Param, (I.Root(I.FVar (n, _, V, s1), S), s2)) => I.EClo (I.Root(I.FVar (n, true (* param *), V, s1), S), s2)
		       | _ => U
	   in
	     (E, LFcollectExp(r, depth, (A, I.id), 
			      LFcollectExp (r, depth, (U', I.id), K, allowVars),
			      allowVars))
	   end

      | transformDelExp (depth, E as D.Unit _, K, allowVars) = (E, K)
      | transformDelExp (depth, D.Lam (isSugar, r, Clist, Fopt), Kinitial, allowVars) = 
	      let
		val depth' = case depth
		             of NONE => NONE
			      | SOME(global, _) => SOME(global, 0)

		val Clist' = map (transformC depth'  Kinitial) Clist 
	      in
		(D.Lam (isSugar, r, Clist', NONE), Kinitial)
	      end

      | transformDelExp (depth, D.New (r, D, E), K, allowVars) = 
	      let 
		val (K1) = collectDelNewDec(depth, D, K, allowVars)
		val (E', K2) = transformDelExp(addOne depth, E, K1, allowVars)
	      in
		(D.New(r, D, E'), K2)
	      end

      | transformDelExp (depth, D.App (r, E1, args), K, allowVars) = 
	      let
		val (E1', K1) = transformDelExp(depth, E1, K, allowVars)
		val (args', K2) = transformDelArgs(depth, args, K1, allowVars)
	      in
		(D.App(r, E1', args'), K2)
	      end

      | transformDelExp (depth, D.Pair (r, E1, E2), K, allowVars) = 
	      let
		val (E1', K1) = transformDelExp(depth, E1, K, allowVars)
		val (E2', K2) = transformDelExp(depth, E2, K1, allowVars)
	      in
		(D.Pair(r, E1', E2'), K2)
	      end

      | transformDelExp (depth, D.Proj (r, E, i), K, allowVars) =
	      let
		val (E', K2) = transformDelExp(depth, E, K, allowVars)
	      in
		(D.Proj (r, E', i), K2)
	      end

      | transformDelExp (depth, D.Pop (r, i, E), K, allowVars) = 
	      let 
		val (E', K2) =  transformDelExp(subtractPop(depth,i), E, K, allowVars) 
	      in
		(D.Pop(r, i, E'), K2)
	      end


     (* not used
      | transformDelExp (depth, D.Fix (r, funList), K, allowVars) = 
	      let
		val (funList', K2) = transformDelFunList (depth, funList, K, allowVars)
	      in
		(D.Fix(r, funList'), K2)
	      end
     *)


      | transformDelExp (depth, P as D.PatVar (r, s, origName), K, allowVars) =
	      if (exists (eqPatVar P) K) then
		  (P, K)
	      else if allowVars then
		  (P, I.Decl(K, PV (r, s, origName)))
	      else
		raise Error (r, "Variable " ^ s ^ " not defined.")


      | transformDelExp (depth, D.TypeAscribe (r, E, T), K, allowVars) =
	      let
		val (K2) = collectDelTypes(depth, T, K, allowVars)
		val (E', K3) = transformDelExp(depth, E, K2, allowVars)
	      in
		(D.TypeAscribe(r, E', T), K3)
	      end

      | transformDelExp (depth, D.Sequence seqList, K, allowVars) =
	      let
		fun transformList ([], K) = ([], K)
		  | transformList ((r,E)::seqList, K) =
		          let
			    val (E', K') = transformDelExp(depth, E, K, allowVars)
			    val (seqList', K'') = transformList(seqList, K')
			  in
			    ((r,E') :: seqList', K'')
			  end
		val (seqList', K') = transformList (seqList, K)
	      in
		(D.Sequence seqList', K')
	      end
		     

      | transformDelExp (depth, D.LetFun (r, funList, E2), K, allowVars) = 
	      let
		val (funList', K2) = transformDelFunList (depth, funList, K, allowVars)
		val (E2', K3) = transformDelExp (addOne depth, E2, K2, allowVars)
	      in
		(D.LetFun (r, funList', E2'), K3)
	      end



      | transformDelExp (depth, D.ExtendFunWith (r, E, Clist, sizeG2a, sizeG2b, isSugar, Fopt ), K, allowVars) = 
	      (* WE INTENSIONALLY THROW OUT Fopt.. *)
	      let
		(* allowVars should be false as this should not occur in a pattern! *)
		val (E', Kinitial) = transformDelExp (subtractPop(depth, sizeG2a+sizeG2b), E, K, allowVars)
		val Clist' = map (transformC (subtractPop(depth, sizeG2b)) Kinitial) Clist
	      in
		(D.ExtendFunWith (r, E', Clist', sizeG2a, sizeG2b, isSugar, NONE), Kinitial)
	      end

    and transformDelArgs (depth, [], K, allowVars) = ([], K)
      | transformDelArgs (depth, (vis, E)::args, K, allowVars) = 
               let
		 val (E', K1) = transformDelExp(depth, E, K, allowVars)
		 val (args', K2) = transformDelArgs(depth, args, K1, allowVars)
	       in
		 ((vis, E')::args', K2)
	       end


    and transformDelFunList (depth, [], K, allowVars) = ([], K)
      | transformDelFunList (depth, (r,D,E)::funList, Kinitial, allowVars) =
              let
		val K2 = collectDelNormalDec(depth, D, Kinitial, allowVars)
		val _ = if (I.ctxLength K2 > I.ctxLength Kinitial) then raise Error (r, "Vars found in type declaration which should have been removed by updateExp... this is a bug") else ()

		(* Set of Vars is Kinitial *)
		val (E', K3) = transformDelExp(addOne depth, E, Kinitial, allowVars)
		val (funList', K4) = transformDelFunList(depth, funList, K3, allowVars)
	      in
		((r, D, E') :: funList', K4)
	      end

    and transformDelCaseBranch (depth, D.Eps (r, D, C), K) = 
	      let
		val (K2) = collectDelNormalDec(depth, D, K, true)
		val (C', K3) = transformDelCaseBranch(addOne depth, C, K2)
	      in
		(D.Eps(r, D, C'), K3)
	      end

      | transformDelCaseBranch (depth, D.NewC (r, D, C), K) = 
	      let
		val (K2) = collectDelNewDec(depth, D, K, true)
		val (C', K3) = transformDelCaseBranch(addOne depth, C, K2)
	      in
		(D.NewC(r, D, C'), K3)
	      end

(* Removed PopC
      (* Warning!!!: ABP.. Abstraction under PopC needs to be thought out more.... *)
      (* HOWEVER, Can we just disallow PopC in the syntax... we need it for opsem,
       *          but would anyone use PopC instead of "Pop" ???
       *)
      | transformDelCaseBranch (depth, D.PopC (r, i, C), K) = 
	      let 
		val (C', K2) = transformDelCaseBranch(subtractPop(depth,i), C, K)
	      in
		(D.PopC(r, i, C'), K2)
	      end
*)



      | transformDelCaseBranch (depth, D.Match (r, pats, E2), K) = 
	      let
		fun transformPats ([], K) = ([], K)
		  | transformPats ((vis, E1)::pats, K) =
			           let
				     val (E1', K') = transformDelExp(depth, E1, K, true)
				     val (pats', K'') = transformPats (pats, K')
				   in
				     ((vis, E1')::pats', K'')
				   end
		val (pats', K2) = transformPats (pats, K)
		val (E2', K3) = transformDelExp(depth, E2, K2, false)
	      in
		(D.Match(r, pats', E2'), K3)
	      end


    (*
      | transformDelCaseBranch (depth, D.MatchAnd (r, visible, E, C), K) = 
	      let
		val (E', K2) = transformDelExp(depth, E, K, true)
		val (C', K3) = transformDelCaseBranch(depth, C, K2)
	      in
		(D.MatchAnd(r, visible, E', C'), K3)
	      end
    *)

      
    and collectDelNormalDec (depth, D.NormalDec(_, _, T), K, allowVars) = collectDelTypes(depth, T, K, allowVars)
    and collectDelNewDec (depth, D.NewDecLF (r, _, A), K, allowVars) = (LFcollectExp (r, depth, (A, I.id), K, allowVars))
      | collectDelNewDec (depth, D.NewDecWorld (_, _, W), K, allowVars) = K

    and collectDelTypes (depth, D.LF (r, _, A), K, allowVars) = (LFcollectExp (r, depth, (A, I.id), K, allowVars))
      | collectDelTypes (depth, D.Meta (_, F), K, allowVars) = (collectDelFormula(depth, F, K, allowVars))

    and collectDelFormula (depth, D.Top _, K, allowVars) = K
      | collectDelFormula (depth, D.All(r, [], F), K, allowVars) = collectDelFormula(depth, F, K, allowVars)
      | collectDelFormula (depth, D.All(r, (visible, D)::Ds, F), K, allowVars) = 
              let
		val K2 = collectDelNormalDec (depth, D, K, allowVars)
		val K3 = collectDelFormula (addOne depth, D.All(r, Ds, F), K2, allowVars)
	      in
		K3
	      end

      | collectDelFormula (depth, D.Exists(r, D, F), K, allowVars) = 
              let
		val K2 = collectDelNormalDec (depth, D, K, allowVars)
		val K3 = collectDelFormula (addOne depth, F, K2, allowVars)
	      in
		K3
	      end

      | collectDelFormula (depth, D.Nabla(r, D, F), K, allowVars) = 
              let
		val K2 = collectDelNewDec (depth, D, K, allowVars)
		val K3 = collectDelFormula (addOne depth, F, K2, allowVars)
	      in
		K3
	      end

      | collectDelFormula (depth, D.FormulaString _, K, allowVars) = K
      | collectDelFormula (depth, D.OmittedFormula _, K, allowVars) = K
       

				


   
    (* Precondition:  G (which E makes sense) has no Vars *)
    fun abstractPatVarsExp (r, E, T as D.LF _) =
           let
	     val (E', K (* I.Null *) ) = transformDelExp (SOME (0,0), E, I.Null, false)
	   in
	     E'
	   end

      | abstractPatVarsExp (r, E, T as D.Meta _) =
           let
	     val K = collectDelTypes(SOME(0,0), T, I.Null, true)
	   in
	      case transformDelExp(SOME (0,0), E, K, false)
	         of (E', I.Null) => E'
		  | (E', Ktotal as I.Decl(_, _)) => 
	           let
		     val implicit = D'.Implicit
		     val n = I.ctxLength Ktotal

		     fun convDecToPattern (n, EV (r, X as I.EVar(_, GX, VX, cnsts), ref (SOME A, _, _))) = D.Quote(r, I.Root(I.BVar(I.Fixed n), I.Nil), I.EClo(A, I.Shift n), DelphinApprox.InjLF, Existential)
	               | convDecToPattern (n, FV (r, s, ref isP, A)) = D.Quote(r, I.Root(I.BVar(I.Fixed n), I.Nil), I.EClo(A, I.Shift n), DelphinApprox.InjLF, Existential)
	               | convDecToPattern (n, PV (r, s, origName)) = D.PatVar(r, s, origName)
	               | convDecToPattern _ = crash() 


		     fun buildC (_, I.Null, pats) = pats
		       | buildC (n, I.Decl(K, D), pats) = buildC (n+1, K, (implicit, convDecToPattern(n, D))::pats)

		     val E' = D.substE(E', D.shift n) (* makes sense now in G, Ktotal *)
		     val E' = abstractDelExp (Ktotal, 0, E')

		     val C = D.Match(r, buildC(1, Ktotal, []), E')
                     (* Need to call Abstract again to make sure we abstract away everything resulting from "buildC" *)
		     (* Note that we NEED to do abstractDelExp BEFORE calling buildC as "convDecToPattern" assumes the type 
		      * is set, which is done in abstraction...
		      *)
		     val C = abstractDelCaseBranch (Ktotal, 0, C) (* gets rid of vars from C *)
		     val C = abstractKEps(Ktotal, C, n-1)

		   in
		     D.Lam(false (* not sugar *), r, [C], NONE)
		   end
	   end
      


    fun abstractPatVarsFunList (funList) =
               let
		 val (funList', K (* I.Null *) ) = transformDelFunList (SOME (0,0), funList, I.Null, false)
	       in
		 funList'
	       end

    (* OLD.. this would just put all implicit arguments to the front..
     * instead we now put them closest to where they belong.
    fun addImplicitTypesForm (F, Kinitial) = 
               let
		 val K' = collectDelFormula(SOME 0, F, Kinitial, true)
		 val K = ctxRemovePrefix(I.ctxLength Kinitial, K') (* K' = Kinitial, K *)
		 val _ = checkConstraints K
		 val n = I.ctxLength K
		 val F2 = D.substF (F, I.Shift n)
		 (* G, {{K}} |- F2 *)
		 val F3 = abstractDelFormula (K, 0, F2)
		 val Fnew = abstractKAll(K, F3, n-1)
	       in
		 Fnew
	       end
     *)


    fun transformDelFormula (depth, F as D.Top _, K, allowVars) = (F, K)
      | transformDelFormula (depth, D.All(r, Ds, F), Kinitial, allowVars) = 
              let
		fun collectList ([], K, d) = (K, d)
		  | collectList ((vis, D)::Ds, K, d) = 
		       let
			 val K' = collectDelNormalDec(d, D, K, allowVars)
		       in
			 collectList (Ds, K', addOne d)
		       end

		val (K', depth') = collectList (Ds, Kinitial, depth)
		val (F', K') = transformDelFormula (depth', F, K', allowVars)
		val F' = D.All(r, Ds, F') 

		(* Now remove everything in K' that was added to Kinitial *)
		val K = ctxRemovePrefix(I.ctxLength Kinitial, K') (* K' = Kinitial, K *)
		val _ = checkConstraints K
		val n = I.ctxLength K
		val F2 = D.substF (F', I.Shift n)
		(* G, {{K}} |- F2 *)
		val F3 = abstractDelFormula (K, 0, F2)
		val Fnew = abstractKAll(K, F3, n-1)
	      in
		(Fnew, Kinitial)
	      end

      | transformDelFormula (depth, D.Exists(r, D, F), K, allowVars) = 
              let
		val K2 = collectDelNormalDec (depth, D, K, allowVars)
		val (F', K3) = transformDelFormula (addOne depth, F, K2, allowVars)
	      in
		(D.Exists(r, D, F'), K3)
	      end

      | transformDelFormula (depth, D.Nabla(r, D, F), K, allowVars) = 
              let
		val K2 = collectDelNewDec (depth, D, K, allowVars)
		val (F', K3) = transformDelFormula (addOne depth, F, K2, allowVars)
	      in
		(D.Nabla(r, D, F'), K3)
	      end

      | transformDelFormula (depth, F as D.FormulaString _, K, allowVars) = (F, K)
      | transformDelFormula (depth, F as D.OmittedFormula _, K, allowVars) = (F, K)


    fun addImplicitTypesForm (F, Kinitial) = 
               let
		 val (F', K') = transformDelFormula(SOME (0,0), F, Kinitial, true)
		 val K = ctxRemovePrefix(I.ctxLength Kinitial, K') (* K' = Kinitial, K *)
		 val _ = checkConstraints K
		 val n = I.ctxLength K
		 val F2 = D.substF (F', I.Shift n)
		 (* G, {{K}} |- F2 *)
		 val F3 = abstractDelFormula (K, 0, F2)
		 val Fnew = abstractKAll(K, F3, n-1)
	       in
		 Fnew
	       end




    fun addImplicitTypesDec (D.NormalDec(r, sO, D.Meta(r2, F)), Kinitial) = D.NormalDec(r, sO, D.Meta(r2, addImplicitTypesForm (F, Kinitial)))
      | addImplicitTypesDec (D.NormalDec(r, sO, D.LF _), Kinitial) = raise Error (r, "Declaration is LF but should be Meta!")


    (* WORLD FUNCTIONS... *)

    fun abstractKEpsWorld (I.Null, C, ~1) = C
      | abstractKEpsWorld (I.Null, C, numShifts) = crash() (* numShifts should be ~1 *)
      | abstractKEpsWorld (I.Decl (K', EV (r, I.EVar (_, GX, VX, _), ref (SOME (V'), _, _))), C, numShifts) =
        let
	  val r = Paths.join(r, D.getRegionW C)
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in	 
	  abstractKEpsWorld (K', D.WorldEps (r, D.NormalDec(r, NONE, D.LF(r, Existential, V'')), C), numShifts-1)
	end
      | abstractKEpsWorld (I.Decl (K', FV (r, name,ref isP, V')), C, numShifts) =
	let
	  val r = Paths.join(r, D.getRegionW C)
	  val isP' = if isP then Param else Existential
	  val V'' = abstractExp (K', 0, (V', I.Shift numShifts))
	in
	  abstractKEpsWorld (K', D.WorldEps (r, D.NormalDec(r, SOME name, D.LF(r, isP', V'')), C), numShifts-1)
	end
      | abstractKEpsWorld (I.Decl (K', LV (_, I.LVar (r, _, (l, t)))), C, _) = crash() (* Can't handle blocks *)
      | abstractKEpsWorld (I.Decl (K', PV (r,name, origName)), C, numShifts) = 
	let
	  val r = Paths.join(r, D.getRegionW C)
	in
	  abstractKEpsWorld (K', D.WorldEps(r, D.NormalDec(r, SOME origName, D.Meta(r, D.OmittedFormula r)), C), numShifts-1)
	end
      | abstractKEpsWorld _ = crash()


    fun abstractDelWorld (K, depth, D.WorldEps (r, D, W)) = D.WorldEps (r, abstractDelNormalDec (K, depth, D),
									abstractDelWorld (K, depth+1, W))

      | abstractDelWorld (K, depth, D.WorldType (r, A)) = D.WorldType(r, abstractExp(K, depth, (A, I.id)))




    (* transformWorld is based on transformC *)
    fun transformWorld Kinitial (D.WorldType (r, A)) =
          let
	    val K = LFcollectExp(r, NONE, (A, I.id), Kinitial, true)
	    val K' = ctxRemovePrefix(I.ctxLength Kinitial, K) (* K = Kinitial,K' *)
	    val _ = checkConstraints K'
	    val n = I.ctxLength K'

	    val A' = abstractExp (K, 0, (A, I.Shift n))
	    val W' = abstractKEpsWorld(K', D.WorldType(r, A'), n-1)
	  in
	    W'
	  end

      | transformWorld Kinitial (D.WorldEps(r, D, W)) =
	   let
	     val K = collectDelNormalDec(NONE, D, Kinitial, true)
	     val W' = D.WorldEps(r, D, transformWorld K W)
	       
	     val K' = ctxRemovePrefix(I.ctxLength Kinitial, K)  (* K = Kinitial,K' *)
	     val _ = checkConstraints K'
	     val n = I.ctxLength K'
	     val W2 = D.substWorld(W', D.shift n)
	     (* {{K'}} |- W2 *)
	     val W3 = abstractDelWorld (K', 0, W2)
	     val W4 = abstractKEpsWorld(K', W3, n-1)
	   in
	     W4
	   end



    fun addSomeVars W = transformWorld (I.Null) W



end;  (* functor Abstract *)
