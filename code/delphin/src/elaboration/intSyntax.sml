(* Delphin Internal Syntax *)
(* Author: Adam Poswolsky *)

structure DelphinIntSyntax =

struct

  type fileInfo = (string * Paths.region) option

  structure I = IntSyn
  exception SubstFailed

  datatype isParam
    = Existential
    | Param
    | PVar of (isParam option) ref


  datatype Visibility 
    = Visible
    | Implicit


  datatype World
    = Anything
    | VarList of ((Dec I.Ctx) * I.Exp) list
              (* Gi |- Ai : type *)
              (* VarList [(Gi,Ai)] *)
    | NonWeakenable of World (* For functions only partially covered... used for parameter functions *)
    

  and Types
    = LF of isParam * I.Exp
    | Meta of isParam * Formula


  and Cnstr =
      Solved
    | EqnF of (I.Dec I.Ctx) * (I.Dec I.Ctx) * Formula * Formula (* Gglobal,G |- F1 == F2 *)

  and Formula
    = Top
    | All     of Visibility * (World option) * NormalDec * Formula
    | Exists  of NormalDec * Formula 
    | Nabla   of NewDec * Formula
    | FormList of (Formula list)  (* Non-dependent pair generalization.. used only as enhancement for mutual recursion *)
    | FVar    of ((I.Dec I.Ctx) * (Formula option) ref * (Cnstr ref) list ref) * I.Sub
             (* Formulas only depend on LF-terms so we include LF-sub only *)
             (* Note that the Context is where the ref was initialized.. NOT the codomain of the sub *)
    | FClo    of Formula * I.Sub (* Enhancement to speed things up *)

  and NormalDec 
    = NormalDec of ((string) list) option * Types
       (* takes a "list" of strings to accomodate mutual recursion 
	* If it just has one element then it means it does not
	* need to undergo a projection.
	*)

  and NewDec 
    = NewDecLF of (string option) * I.Exp
    | NewDecMeta of (string option) * Formula

  and Dec
    = InstantiableDec of NormalDec    
    | NonInstantiableDec of NewDec

  and BoundVar
    = Fixed of int
    | BVarMeta of ((BoundVar option) ref * Formula) * Sub
    | BVarLF of ((I.BoundVar option) ref * I.Exp * (int list)) * I.Sub  (*  (r:A, list) [t] *)

  and Exp
    = Var    of BoundVar * fileInfo (* Either "Fixed i" or a variable  *)
    | Quote  of I.Exp
    | Unit
    | Lam    of (CaseBranch list) * Formula * fileInfo
                      (* we need to save the type of the lam as it is not inferrible *)
                      (* we also save the "filename" and "region" information to print out better messages
		       *)

    | New    of NewDec * Exp * fileInfo (* fileInfo is for error messages as in Lam*)
    | App    of Visibility * Exp * Exp
    | Pair   of Exp * Exp * Formula (* we need to save the type of pair as it is not inferrible *)
    | ExpList of Exp list (* generalization useful for mutual recursion, all must have formula type! *)
    | Proj of Exp * int
       (* Useful for mutual recursion.  Proj (e,j) stands for jth
	* projection of "e".  Projection is ONLY defined
	* if "e" is a fixpoint.
	* This is an optimization to handle mutual recursion...
	*)

    | Pop    of int * Exp (* int >= 1 *)
    | Fix    of NormalDec * Exp (* Note that this Exp will be "ExpList" for mutual recursion.. not a pair *)

    | EVar   of (Exp option ref * Formula) * Sub     (* (X : F) [s] *)
                 (* Meta-level EVars are VERY weak.. 
		  * used to specify epsilon variables
		  * in case analysis, and that is it.
		  * Typically, this substitution will always be "id" when evaluating
		  *)

    | EClo    of Exp * Sub (* Enhancement to speed things up *)

 
  and CaseBranch
    = Eps of NormalDec * CaseBranch
    | NewC of NewDec * CaseBranch * fileInfo
    | PopC of int * CaseBranch
    | Match of Visibility * Exp * Exp (* pattern => result *)
    | MatchAnd of Visibility * Exp * CaseBranch (* pattern and case.. . used to indicate delayed evaluation of case
						 * to look at second case with it
						 * (may be implicit)
						 *)

  and Sub
    = Shift of Sub		
    | Dot of Front * Sub
    (* | emptySub *)
    | id        (* Optimization.. G |- id : G.  
		 * In paper, we have . |- emptySub : .
		 * but this may be more useful...
		 *)

  and Front			(* Fronts:                    *)
    = Prg of Exp 	         (*     | p                    *)
    | Undef                     

  type decCtx = Dec I.Ctx

  (* End of Internal Syntax Specification
   * Now we define functions related to Substitution and such
   *)

    (* Meta vs LF indicates the substitution attached to it.
     * It can still be an LF object with a meta-substitution (although it could be coerced)
     *)
  datatype whnfBVarResult 
    = MetaSub of int * Sub      (* i[s] *)
    | LFSub of int * IntSyn.Sub 
    | VarRef of BoundVar (* Won't be "Fixed" *)
    

  fun coerceBoundVar (Fixed i) = SOME(I.Root (I.BVar (I.Fixed i), I.Nil))
    | coerceBoundVar (BVarLF ((r,A,list), s)) = SOME(I.Root (I.BVar (I.BVarVar ((r,A,list), s)), I.Nil))
    | coerceBoundVar _ = NONE

  fun shiftTo (0, t) = t
    | shiftTo (i, t) = Shift (shiftTo (i-1,t))


  (* ************************************************
   * Substitution Properties
   * ************************************************ *)

  (* G,D |- shift : G *)
  val shift = Shift id


  (* invShift = ^-1 = _.^0
     Invariant:
     G |- ^-1 : G, V     ^-1 is patsub
  *)
  val invShift = Dot(Undef, id)

  (* dot1
     Invariant:
     If G |- t : G'
     then G,A[t] |- dot1 t : G',A
  *)
  fun dot1 (id) = id
    | dot1 t = Dot (Prg (Var (Fixed 1, NONE)), Shift t)


  (* Whnf is designed to make sure it gets rid of instantiated ?Var's
   from top constructor *)

  fun whnfP (PVar (ref (SOME P))) = whnfP P
    | whnfP P = P

  (* removes top instantiate EVars, EClo, and BVars *)
  (* may raise SubstFailed *)
  fun whnfE (EVar ((ref (SOME E),_), t)) = whnfE (substE'(E,t))
    | whnfE (EClo (E, t)) = whnfE (substE'(E, t))
    | whnfE (Var ((Fixed i), fileInfo)) = Var ((Fixed i), fileInfo)
    | whnfE (Var (B, fileInfo)) = 
                     (case whnfBVar (B, id)
			 of (MetaSub (i, s)) => whnfE (bvarSub(i, s))
			  | (LFSub (i, s)) => (case (I.bvarSub(i, s))
						 of (I.Idx k') => Var (Fixed k', fileInfo)
						  | (I.Exp U) => Quote U
						  | I.Block _ => raise Domain
						  | I.Undef => raise SubstFailed
						)
			  | (VarRef B') => Var (B', fileInfo))
    | whnfE E = E

  (* Returns whnfBVarResult *)
  and whnfBVar (Fixed k, s) = MetaSub(k, s)
    | whnfBVar (BVarMeta ((ref (SOME B), _), t), s) = whnfBVar(B, comp(t, s))
    | whnfBVar (BVarMeta ((r as ref NONE, F), t), s) = VarRef (BVarMeta ((r, F (* warning.. not in whnf *) ), comp(t,s)))
    | whnfBVar (BVarLF ((ref (SOME B), _, _), t), s) = (case (Whnf.whnfBVar (B, I.comp(t, coerceSub s)))
						  of (I.Fixed k', s') => LFSub(k', s')
						   | (I.BVarVar((r,A,list),s), _ (* id *)) => VarRef (BVarLF ((r,A,list),s)))
    | whnfBVar (BVarLF ((r as ref NONE, A,list), t), s) = VarRef (BVarLF ((r, A,list), I.comp(t, coerceSub s)))

  (* removes top level FVars and FClo *)
  and whnfF (FVar ((G, ref (SOME F), cnstrs), t)) = whnfF (substF'(F, t)) (* cnstrs should be empty *)
    | whnfF (FClo (F, t)) = whnfF (substF' (F, t))
    | whnfF F = F

  (* substF' takes a meta-level formula under an LF substitution *)
  and substF'(Top, _) = Top
    | substF'(All (visible, W, D, F), t) = All (visible, W, substNormalDec (D, t), FClo(F, I.dot1 t))
    | substF'(Exists (D, F), t) = Exists (substNormalDec (D, t), FClo(F, I.dot1 t))
    | substF'(Nabla (D, F), t) = Nabla (substNewDec (D, t), FClo(F, I.dot1 t))
    | substF'(FormList Flist, t) = FormList (map (fn F => FClo(F, t)) Flist) 
                              (* Note that we do not do shifts as dependencies do not depend on formulas *)
    | substF'(FVar ((G, F, cnstrs), t1), t2) = FVar ((G, F, cnstrs), I.comp(t1, t2))
    | substF'(FClo (F, t1), t2) = FClo (F, I.comp(t1, t2))

  and substTypes(LF (isP, A), t) = LF (isP, I.EClo(A, t))
    | substTypes(Meta (isP, F), t) = Meta (isP, FClo(F, t))



  and substNormalDec (NormalDec (sLO, T), t) = NormalDec (sLO, substTypes(T, t))
  and substNewDec (NewDecLF (sO, A), t) = NewDecLF (sO, I.EClo(A, t))
    | substNewDec (NewDecMeta (sO, F), t) = NewDecMeta (sO, FClo(F, t))

  (* substDec takes a meta-level dec under an LF substitution *)
  and substDec (InstantiableDec D, t) = InstantiableDec (substNormalDec (D, t))
    | substDec (NonInstantiableDec D, t) = NonInstantiableDec (substNewDec (D, t))



  (* Precondition:  E is in whnf *)
  (* This brings meta-level expression to object-level if possible *)

  and coerceExp E = coerceExpN (whnfE E)
  and coerceExpN (Quote M) = 
          (* It is important that references to a variable are made with "Idx"
	   * as otherwise it will not be detected as a pattern substitution 
	   *)
          (let
	    val n = Whnf.etaContract(M)
	  in
	    I.Idx n
	  end handle Whnf.Eta => I.Exp M)

    | coerceExpN (Var (Fixed i, _)) = I.Idx i
	   (* It is possible that this is a meta-variable not accessible
	    * on the LF-level, but there is no harm in putting code their
	    * instead of Undef... it will never access it by invariant
	    *)

    | coerceExpN (Var (B, fileInfo)) = 
	     (case (whnfBVar (B, id))
	       of LFSub(k, s) => I.bvarSub(k, s)
		| MetaSub(k', s) => (coerceExp(bvarSub(k', s)) handle SubstFailed => I.Undef)
	        | VarRef (Fixed _) => raise Domain (* impossible by invariant *)
		| VarRef (BVarMeta _) => I.Undef
		| VarRef (BVarLF ((r,A,list), s)) (* Param Variable *) => I.Exp (I.Root (I.BVar (I.BVarVar ((r,A,list), s)), I.Nil))
                                              (* ABP WARNING:  This MAY break LF invariant that
					       *               All indices are referred to as "Idx"
					       *               When B is eventually instantiated
					       *               It will stay as an I.Exp!
					       *               As this is right now only used 
					       *               in opsem/matching it isn't an issue.
					       *               HOWEVER, we should change I.Idx to take a B also.
					       *)
		 )

    | coerceExpN (EVar ((ref (SOME _), _), _)) = raise Domain (* invariant violated, not in whnf *)
    | coerceExpN (EClo _) = raise Domain (* invariant violated, not in whnf *)
    | coerceExpN _ = I.Undef
    


  and coerceSub (id) = I.id
    | coerceSub (Shift t) = I.comp(coerceSub t, I.shift)
    | coerceSub (Dot (Undef, t)) = I.Dot (I.Undef, coerceSub t)
    | coerceSub (Dot (Prg E, t)) = I.Dot (coerceExp E, coerceSub t)



  (* G1 |- t : G0 
   * G2 |- t2 : G1
   * G2 |- comp(t,t2) : G0 
   * As defined in Definition C.2 *)
  and comp (t, Shift t2) = Shift (comp(t, t2))
    | comp (Dot (Undef, t), t2) = Dot (Undef, comp(t, t2))
    | comp (Dot (Prg E, t), t2) = Dot (Prg (EClo(E,t2)), comp(t, t2))
    | comp (Shift t1, Dot(_, t2)) = comp(t1, t2) 
    (* | comp (EmptySub, t2) = t2 *)
    | comp (Shift t, id) = Shift t
    | comp (id, t2) = t2



  and getIndex E = (case (whnfE(E))
                    of (Var (B, _)) => getIndex' B
		     | _ => NONE
		      )
  and getIndex' (Fixed k) = SOME k
    | getIndex' (B) =
    (case (whnfBVar (B, id))
       of (MetaSub (k, s)) =>
	    ((case bvarSub (k, s)
		of (Var (B', _)) => getIndex' B'
	         | _ => NONE
		  ) handle SubstFailed => NONE)
        | (LFSub (k, s)) =>  
		(case (I.bvarSub(k, s))
		    of I.Idx k' => SOME k'
		  | I.Exp U => (let
				  val n = Whnf.etaContract U
				in
				  SOME n
				end handle Whnf.Eta => NONE)
									    
		  | I.Undef => NONE
		  | I.Block _ => NONE
		  )
	| (VarRef _) => NONE
    )



  (* popSub(i,t) = (j, t')
   * Invariant:  G',j..1 |- t : G,i..1 
   * and i is uninstantiable
   * then
   * G' |- t' : G
   *)
  and popSub(i,Shift t) = 
                  (* G',j..1 |- Shift t : G,i..1  by Assumption *)
                  (* G',j-1..1 |- t : G,i..1 by Inversion *)
		   let val (j,t') = popSub(i, t)
                     (* G' |- t' : G   
		      *)
		   in (j+1, t')
		   end

    | popSub(i, id) =
		   (* G,i..1 |- id : G,i..1 by Assumption *)
		   (i, id)

    | popSub (1, Dot(Prg E, Shift t))
		   (* G'  |- t : G *)
		   (* E must be Var (Fixed 1) *)
		   (* G',1 |- 1.(Shift t) : G,1 *)
		   = let
			val _ = case (getIndex E)
			        of (SOME 1) => ()
				 | _ => raise Domain (* broken invariant *) 
		     in
		       (1, t)
		     end
		   		  
    | popSub (1, Dot(Ft, t)) = raise Domain (* t must be (Shift t') by invariant *)

    | popSub (i, Dot(Ft, t)) =
		   (* G',j..1 |- Ft.t : G,i..1 by Assumption *)
		   (* G',j..1 |- t : G,i-1..1 by Inversion *)
		   (* popSub(i-1, t) = (j,t')        *)
		     (* G' |- t' : G
		      *)
		   popSub(i-1,t)


		   
  and substCase (Eps (D, C), t) = Eps (substNormalDec(D, coerceSub t), substCase(C, dot1 t))
    | substCase (NewC (D, C, fileInfo), t) = NewC (substNewDec(D, coerceSub t), substCase(C, dot1 t), fileInfo)
    | substCase (PopC (i, C), t) = let
                                         val (j, t') = popSub(i, t)
				      in 
					PopC(j, substCase(C, t'))
				      end
    | substCase (Match (visibility, patE, resE), t) = Match (visibility, EClo(patE, t), EClo(resE, t))
    | substCase (MatchAnd (visibility, patE, C), t) = MatchAnd (visibility, EClo(patE, t), substCase(C, t))



  (* Invariant *)
  (* G |- E : A
   * G' |- t : G
   * G' |- substE'(E,t) : A[t]
   *)
  and bvarSub (k, id) = Var (Fixed k, NONE)
    | bvarSub (1, Dot((Prg E), t)) = E
    | bvarSub (1, Dot(Undef, t)) = raise SubstFailed
    | bvarSub (i, Dot(Ft, t)) = bvarSub(i-1, t)
    | bvarSub (i, Shift id) = Var (Fixed (i+1), NONE)
    | bvarSub (i, Shift t) = EClo(bvarSub(i, t), Shift id)
              (* G |- i : A
	       * G',A |- Shift t : G
	       * G' |- t : G
	       * G' |- i[t] : A[t]
	       * G',A |- Shift id : G'
	       * G',A |- i[t][Shift id] : A[t][Shift id]
	       * and [t o (Shift id)] = Shift (t o id) = Shift t
	       *)
	  (* Note that it is the use of "id" that makes sure this is terminating
	   * as (Var i)[shift id] is handled before this case .
	   * Without the "id" optimization, we would have to check of i[t] is i'
	   * if so, just return i'+1, else apply it to the new substitution 
	   *)

  and substE'(E, id) = E
    | substE'(Var (B, fileInfo), t) = (case (whnfBVar (B, t))
			    of (MetaSub (k, s)) => bvarSub(k, s)
			     | (LFSub(k, s)) => 
			              (case (I.bvarSub(k, s)) 
					 of (I.Idx k') => Var (Fixed k', fileInfo)
					  | (I.Exp U) => Quote U
					  | I.Block _ => raise Domain
					  | I.Undef => raise SubstFailed
					   )
                             | (VarRef B') => Var (B', fileInfo))

    | substE'(Quote M, t) = Quote (I.EClo(M, coerceSub t))
    | substE'(Unit, _) = Unit
    | substE'(Lam (Clist, F, fileInfo), t) = 
                        let
			  val Clist' = map (fn C => substCase(C, t)) Clist
			in
			  Lam (Clist', FClo(F, coerceSub t), fileInfo)
			end

    | substE'(New (D, E, fileInfo), t) = New (substNewDec(D, coerceSub t), EClo (E, dot1 t), fileInfo)
    | substE'(App (visible, E1, E2), t) = App (visible, EClo(E1, t), EClo(E2, t))
    | substE'(Pair (E1, E2, F), t) = Pair (EClo(E1, t), EClo(E2, t), FClo(F, coerceSub t))
    | substE'(ExpList Elist, t) = ExpList (map (fn E => EClo(E, t)) Elist)
    | substE'(Proj (E,i), t) = Proj(EClo(E,t), i)
			      
    | substE'(Pop (i, E), t) = 
	   (* G',j..1 |- t : G,i...1  as substitution is well-typed
	    * G |- E : Nab{A}T  by Assumption
	    * popSub(i,t) = (j, t') 
	    * G' |- t' : G       by popSub
	    * G' |- E[t'] : (Nab{A}T)[t']
	    * G',j..1 |- pop j E[t'] : (Nab{A}T)[t'][shift^j id]  by pop rule 
	    * (Nab{A}T)[t'][shift^j id] = (Nab{A}T)[t] since t' <= t (see paper)
	    * 
	    *)
	   let val (j, t') = popSub(i, t)
	   in
	     Pop (j, EClo(E,t'))
	   end

    | substE'(Fix (D, E), t) = Fix (substNormalDec(D, coerceSub t), 
				   EClo (E, dot1 t))


    | substE'(EVar ((r as ref NONE, F), t1), t2) = EVar ((r,F), comp(t1,t2))
	     
    | substE'(EVar ((ref (SOME E),_), t1), t2) = EClo(E, comp(t1,t2))
    | substE'(EClo (E, t1), t2) = EClo (E, comp(t1, t2))
	     

	       

  (* Throw out all elements in context up to i, inclusive *)
  fun popCtx (0, G) = G
    | popCtx (i, I.Decl(G, D)) = popCtx (i-1, G)
    | popCtx (i, I.Null) = raise Domain (* Broken invariant *)

  fun convSLOtoSO NONE = NONE
    | convSLOtoSO (SOME []) = raise Domain
    | convSLOtoSO (SOME [s]) = SOME s
    | convSLOtoSO (SOME sL) =
         let
	   fun toString [] = raise Domain 
	     | toString [s] = s ^ "]"
	     | toString (s::ss) = s ^ ", " ^ (toString ss)
	 in
	   SOME ("[" ^ (toString sL))
	 end

  fun coerceTypes (LF (_, A)) = SOME A
    | coerceTypes (Meta _) = NONE


  fun coerceDec (InstantiableDec (NormalDec (sLO, T))) = 
              (case (coerceTypes T)
		 of NONE => I.NDec
		  | SOME A => I.Dec(convSLOtoSO sLO, A)
	      )

    | coerceDec (NonInstantiableDec (NewDecLF (sO, A))) =
		 I.Dec(sO, A)

    | coerceDec (NonInstantiableDec (NewDecMeta _)) =
		 I.NDec


  fun coerceCtx I.Null = I.Null
    | coerceCtx (I.Decl(G, D)) = I.Decl(coerceCtx G, coerceDec D)

  (* strengthen(G) = (G', t)
   * such that G' is NDec free
   * and (G' |- t: G)
   * Currently only used for PRINTING nicely... get rid of those pesky NDecs..
   *)
  fun strengthen(G) =
        let
	  fun weaken (I.Null) = I.id
	    | weaken (I.Decl (G', I.NDec)) = I.comp (weaken G', I.shift)
	    | weaken (I.Decl (G', D)) = I.dot1 (weaken G')
		      
	  val w = weaken G                      (* G |- w : G' *)
	  val iw = Whnf.invert w                (* G' |- iw : G *)
	  val G' = Whnf.strengthen(iw, G)
	in
          (G', iw)
	end


  (* Is t an identity substitution *)
  fun isId id = true
    | isId (Dot(Prg E, Shift t)) = 
                 let
		   val nOpt = getIndex E
		 in
		   case nOpt of
		     (SOME 1) => isId t
		    | _ => false
		 end
    | isId _ = false


  (* ABP:
   * findIndex(k, s) = SOME k'
   * If G',Ak...A1 |- s : G
   * and there exists an index k' such that k'[s] = k
   * then we return SOME k', else return NONE
   *)
  fun addOne NONE = NONE
    | addOne (SOME i) = SOME (i+1)

  fun findIndex(k, id) = SOME k
    | findIndex(k, Shift t) =
         if (k > 1) then findIndex (k-1, t)
	 else NONE

    | findIndex(k, Dot (Prg E, t)) =
	   let
	     val nOpt = getIndex E
	   in
	     case nOpt
	       of NONE => addOne(findIndex(k, t))
		| (SOME n) => if (n=k) then SOME(1)
		              else addOne(findIndex(k, t))
	   end

    | findIndex(k, Dot(Undef, t)) = addOne(findIndex(k,t))


  (* *********************************************
   * Auxiliary Helpers
   * ****************************************** *)
  fun newPVar() = PVar (ref NONE)
  fun newEVar(F) = EVar ((ref NONE, F), id)
  fun newFVar(G) = FVar ((G, ref NONE, ref nil), I.id)



(* Fill in ambiguous PVars as Existentials *)
  fun updatePVarsIsParam P = updatePVarsIsParamN (whnfP P)
  and updatePVarsIsParamN (PVar (r as ref NONE)) = (r := SOME Existential)
    | updatePVarsIsParamN _ = ()

  fun updatePVarsTypes (LF(isP, _)) = updatePVarsIsParam isP
    | updatePVarsTypes (Meta(isP, F)) = (updatePVarsIsParam isP ; updatePVarsFormula F)

  and updatePVarsNormalDec (NormalDec (_, T)) = updatePVarsTypes T

  and updatePVarsNewDec (NewDecLF _) = ()
    | updatePVarsNewDec (NewDecMeta (_, F)) = updatePVarsFormula F

  and updatePVarsFormula F = updatePVarsFormulaN (whnfF F)
  and updatePVarsFormulaN (Top) = ()
    | updatePVarsFormulaN (All(visible, W, D, F)) = (updatePVarsNormalDec D ; updatePVarsFormula F)
    | updatePVarsFormulaN (Exists(D, F)) = (updatePVarsNormalDec D ; updatePVarsFormula F)
    | updatePVarsFormulaN (Nabla(D, F)) = (updatePVarsNewDec D ; updatePVarsFormula F)
    | updatePVarsFormulaN (FormList Flist) = (map updatePVarsFormula Flist ; ())
    | updatePVarsFormulaN (FVar _) = ()
    | updatePVarsFormulaN (FClo _) = raise Domain (* not in whnf *)


  fun updatePVarsExp E = updatePVarsExpN (whnfE E)
  and updatePVarsExpN (Var _) = ()
    | updatePVarsExpN (Quote _) = ()
    | updatePVarsExpN (Unit) = ()
    | updatePVarsExpN (Lam (Clist, F, fileInfo)) = 
           let
	     val _ = map updatePVarsCaseBranch Clist
	     val _ = updatePVarsFormula F
	   in
	     ()
	   end
    | updatePVarsExpN (New (D, E, fileInfo)) = (updatePVarsNewDec D ; updatePVarsExp E)
    | updatePVarsExpN (App (_, E1, E2)) = (updatePVarsExp E1 ; updatePVarsExp E2)
    | updatePVarsExpN (Pair (E1, E2, F)) = (updatePVarsExp E1 ; updatePVarsExp E2 ; updatePVarsFormula F)
    | updatePVarsExpN (ExpList Elist) = (map updatePVarsExp Elist ; ())
    | updatePVarsExpN (Proj(E, _)) = updatePVarsExp E
    | updatePVarsExpN (Pop(_, E)) = updatePVarsExp E
    | updatePVarsExpN (Fix(D, E)) = (updatePVarsNormalDec D; updatePVarsExp E)
    | updatePVarsExpN (EVar ((_,F), s)) = (updatePVarsFormula F ; updatePVarsSub s)
    | updatePVarsExpN (EClo _) = raise Domain (* not in whnf *)

  and updatePVarsCaseBranch (Eps (D, C)) = (updatePVarsNormalDec D ; updatePVarsCaseBranch C)
    | updatePVarsCaseBranch (NewC (D, C, fileInfo)) = (updatePVarsNewDec D ; updatePVarsCaseBranch C)
    | updatePVarsCaseBranch (PopC (i, C)) = (updatePVarsCaseBranch C)
    | updatePVarsCaseBranch (Match (_, E1, E2)) = (updatePVarsExp E1 ; updatePVarsExp E2)
    | updatePVarsCaseBranch (MatchAnd (_, E, C)) = (updatePVarsExp E ; updatePVarsCaseBranch C)

  and updatePVarsSub (Shift _) = ()
    | updatePVarsSub (Dot(Ft, s)) = (updatePVarsFront Ft ; updatePVarsSub s)
    | updatePVarsSub (id) = ()
    
  and updatePVarsFront (Prg E) = updatePVarsExp E
    | updatePVarsFront (Undef) = ()


  fun makeParamList' (I.Null, k) = []
    | makeParamList' (I.Decl(G, InstantiableDec (NormalDec(_, LF(isP, _)))), k) = 
          (case (whnfP isP)
	     of (Param) => k :: (makeParamList' (G, k+1))
	      | _ => makeParamList' (G, k+1))
    | makeParamList' (I.Decl(G, InstantiableDec (NormalDec(_, Meta(isP, _)))), k) = 
          (case (whnfP isP)
	     of (Param) => k :: (makeParamList' (G, k+1))
	      | _ => makeParamList' (G, k+1))
    | makeParamList' (I.Decl(G, NonInstantiableDec _), k) = 
	     k :: (makeParamList' (G, k+1))
          

  (* get a list of parameters in G *)
  fun makeParamList G = makeParamList' (G, 1)


end

