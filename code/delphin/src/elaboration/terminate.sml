(* Delphin Termination Checker *)
(* Author: Adam Poswolsky *)

structure DelphinTermination =
  struct
    exception Error of string
    structure I = IntSyn
    structure D = DelphinIntSyntax
    structure U = UnifyDelphinTrail
    structure O = DelphinOpsem

    fun crash() = (print "Fatal Error" ; raise Domain)


    (* Main Function ... *)
    (* ***************************************************************************************************************** *)
    (* ***************************************************************************************************************** *)

    (* check(smartInj, printEps, G, E) = ()
     * raises Error if E does not terminate
     * - smartInj and printEps are preferences for *printing* routines that are passed around.
     *
     * Precondition:  Under the ASSUMPTION that everything in G terminates, we check if E 
     *                also terminates...  also assume that the term has no meta-level EVars amd no FVars
     * Output:  raises Error if E does not terminate.
     *)

    (* For termination we change the definiton of Types, so that "D.All" has a list containing EVars
     * representing the input, which must get smaller on recursive calls. 
     *
     * However, rather than change the definition of types, we will represent the new type definition as a pair
     * of (type * TermCriteria) which is just used to encode that Forall has a list of termination criteria.
     * The list will be of the form:  "X1 . X2 . NO "
     *    (i.e. X1 gets smaller 
     *       or X1 stays the same and repeat on "X2 . NO")
     * The list may end in YES for mutual recursion, expressing that function i can call function (i+j) with
     * all equal terms.
     *)

     (* When encountering a pair of types * TermCriteria = (T,term)
      * If G |- T wff
      * then G |- term wff
      *)

    datatype TermCriteria
      = TermApp of D.Exp * TermCriteria  (* list of things to apply *)
                                         (* only visible terms count in order *)
		    
      | TermNew of D.NewDec * TermCriteria (* to encode Nab{x}T *)
      | TermPair of TermCriteria * TermCriteria
      | TermList of TermCriteria list
      | TermYES
      | TermNO

    datatype TermCriteriaDummy
      = TermAppDummy of (D.Visibility * D.Exp * D.Types) list * TermCriteriaDummy
      | TermNewDummy of D.NewDec * TermCriteriaDummy
      | TermPairDummy of TermCriteriaDummy * TermCriteriaDummy
      | TermListDummy of TermCriteriaDummy list
      | TermYESDummy
      | TermNODummy


    (* isIgnored(vis, T) = true iff we will ignore terms of this (visibility * type) in the termination order.
     * We will ignore all implicit arguments as well as all meta-level arguments that contain functions.
     * Or in other words, the ordering is all visible arguments that do not contain meta-level functions.
     *)
    fun hasFun F = hasFunW (D.whnfF F)
    and hasFunW (D.All _) = true
      | hasFunW (D.Nabla (_, F)) = hasFun F
      | hasFunW (D.Exists (D.NormalDec (_, T), F)) = 
                            (case T
			       of (D.LF _) => hasFun F
			         | (D.Meta F') => (hasFun F') orelse (hasFun F)
				 )
      | hasFunW (D.FormList []) = false
      | hasFunW (D.FormList (F::Fs)) = (hasFun F) orelse hasFun (D.FormList Fs)						   
      | hasFunW _ = false

    fun isIgnored(D.Implicit, _) = true
      | isIgnored(D.Visible, D.LF _) = false
      | isIgnored(D.Visible, D.Meta F) = hasFun F


    (* the TermCriteriaDummy contains everything we need to apply out the function, but 
     * based on "isIgnored" we remove implicit arguments from the termination order
     * as well as meta-level types that contain functions.
     *)
    fun removeTermDummy (TermAppDummy ([], term)) = removeTermDummy term
      | removeTermDummy (TermAppDummy ((vis, E, T)::vars, term)) = 
                                        if isIgnored(vis, T) then
					   removeTermDummy(TermAppDummy(vars, term))
					else
					  TermApp(E, removeTermDummy (TermAppDummy(vars, term)))
      | removeTermDummy (TermNewDummy (D, term)) = TermNew(D, removeTermDummy term)
      | removeTermDummy (TermPairDummy (term1, term2)) = TermPair (removeTermDummy term1, removeTermDummy term2)
      | removeTermDummy (TermListDummy termlist) = TermList (map removeTermDummy termlist)
      | removeTermDummy (TermYESDummy) = TermYES
      | removeTermDummy (TermNODummy) = TermNO

    fun setYESTermsType (D.LF _) = TermYES
      | setYESTermsType (D.Meta F) = setYESTermsF F

    and setYESTermsF F = setYESTermsFW (D.whnfF F)
    and setYESTermsFW (D.Top) = TermYES
      | setYESTermsFW (D.All _) = TermYES
      | setYESTermsFW (D.Exists (D, F)) = TermPair (setYESTermsNormalDec D, setYESTermsF F)
      | setYESTermsFW (D.Nabla (D, F)) = TermNew (D, setYESTermsF F)
      | setYESTermsFW (D.FormList Flist) = TermList (map (fn F => setYESTermsF F) Flist)
      | setYESTermsFW (D.FVar _) = crash() (* unexpected *)
      | setYESTermsFW (D.FClo _) = crash() (* not in whnf! *)
     
    and setYESTermsNormalDec (D.NormalDec (_, T)) = setYESTermsType T

    fun setYESTermsDec (D.NonInstantiableDec _) = TermYES
      | setYESTermsDec (D.InstantiableDec D) = setYESTermsNormalDec D



    (* We do not need to add termination information inside the context
     * As Gglobal is assumed to be terminating, and the context only
     * grows by NonInstantiableDecs..
     *
    fun addTermCtx(I.Null) = I.Null
      | addTermCtx(I.Decl(G, D)) = I.Decl(addTermCtx G, (D, setYESTermsDec D)) (* this means it is terminating *)

    fun removeTermCtx(I.Null) = I.Null
      | removeTermCtx(I.Decl(G, (D, term))) = I.Decl(removeTermCtx G, D)

    fun coerceTermCtx G = D.coerceCtx (removeTermCtx G)
    *)

    fun getFormula (D.Meta(F)) = D.whnfF F
      | getFormula _ = crash()

    fun getElement(1, x::xs) = x
      | getElement(i, x::xs) = if i< 1 then crash() else getElement(i-1, xs)
      | getElement _ = raise Error "Delphin Termination Error:  Attempted to access bad index"

    fun unifyTypes(Gglobal, Glocal, T1, T2) = 
         (U.unifyT(D.coerceCtx Gglobal, D.coerceCtx Glocal, T1, T2) handle U.Error s => (raise Error ("Delphin Termination Error (Unify): "^ s)))

    fun isTerm (TermApp _) = false
      | isTerm (TermYES) = true
      | isTerm (TermNO) = false
      | isTerm (TermNew (D, T)) = isTerm T
      | isTerm (TermPair (T1, T2)) = (isTerm T1) andalso (isTerm T2)
      | isTerm (TermList []) = true
      | isTerm (TermList (T::ts)) = (isTerm T) andalso (isTerm (TermList ts))




    datatype Comparison
      = Less
      | Equal
      | Unknown

    (* Comparison Functions ... *)
    (* compare(G, E1, E2) = R  such that E1 R E2
     * where R can be {Less, Equal, Unknown}.
     *
     * G |- E1 wff   G |- E2 wff
     * G only contains NonInstantiableDecs (parameters)
     *)

    fun shiftSub t =
          let
	    fun onlyShifts (D.id) = true
	      | onlyShifts (D.Shift t) = onlyShifts t
	      | onlyShifts t = false
	  in 
	    (D.isId t) orelse (onlyShifts t)
	  end



    (* ************************************************************** *)
    (* ************************************************************** *)
    (* LF Comparison.. based on Twelf's OLD termination checker (terminate.fun)
     * (by Carsten Schuermann, implementing 
     *  implementing [Rohwedder,Pfenning ESOP'96] 
     * 
     *)
    (* ************************************************************** *)

    (* below(worlds, Gglobal, Glocal, A, B) = true if terms of type A can be used in
     *                                        building terms of type B
     *)
    fun below(worlds, Gglobal, Glocal, A, B) = 
      let
	(* Returns true if it can find somewhere where A can be used to build terms of type B *)

	(* We check for subordination violations earlier (in convert.fun), so we can assume
	 * here that all parameters in worlds, Gglobal, Glocal conform to the subordination relation...
	 * OTHERWISE, we would need to dynamically extend the subordination relation here
	 * and this *may* introduce other complications...
	 *)
      in
	Subordinate.below(A, B)
      end


    (* For functions: lt, ltW, ltSpine, eq, le, leW *)
    (* first argument pair (UsVs) must be atomic! *)
    (* For all functions below: (UsVs) may not contain any EVars *)

    (* lt (worlds, Gglobal, Glocal, Q, ((U, s1), (V, s2)), (U', s'), sc) = B
     
       Invariant:
       B holds  iff  
       Everything makes sense with prefix of Gglobal
       and  Glocal |- s1 : Glocal1   Glocal1 |- U : V1
       and  Glocal |- s2 : Glocal2   Glocal2 |- V : L
       and  Glocal |- U[s1] : V [s2] 
       and  Glocal |- s' : Glocal3  Glocal3 |- U' : V'
       and  U[s1] is a strict subterm of U'[s']
       and  V[s2] atomic
       and  only U'[s'] contains EVars
	 (NOTE:  worlds refers to some local worlds we may need to consider in the "below" check)
    *)
    and lt (worlds, Gglobal, Glocal, UsVs, UsVs') = 
          ltW (worlds, Gglobal, Glocal, UsVs, Whnf.whnfEta UsVs')

    and ltW (worlds, Gglobal, Glocal, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs')) = 
	  ltSpine (worlds, Gglobal, Glocal, (Us, Vs), ((S', s'), (I.constType c, I.id)))
      | ltW (worlds, Gglobal, Glocal, (Us, Vs), ((I.Root (I.BVar (I.Fixed n), S'), s'), Vs')) = 
	  let
	    val G' = D.coerceCtx (I.mergeCtx(Gglobal, Glocal))
	    val V' = case (I.ctxDec (G', n))
	             of I.Dec (_, V') => V'
		      | _ => crash()
	  in
	    ltSpine (worlds, Gglobal, Glocal, (Us, Vs), ((S', s'), (V', I.id)))
	  end

      | ltW (worlds, Gglobal, Glocal, (Us, Vs), ((I.Root (I.BVar (I.BVarVar ((r, A, _, _), s0) ), S'), s'), Vs')) =
	  ltSpine(worlds, Gglobal, Glocal, (Us, Vs), ((S', s'), (A, I.comp(s0, s'))))

      | ltW (worlds, Gglobal, Glocal, _, ((I.EVar _, _), _)) = false
      | ltW (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), 
	     ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
	      (I.Pi ((I.Dec (_, V2'), _), V'), s2'))) =
	  (* ADAM WARNING:  This is different from the paper and the Twelf implementation!
	   * as it allows for all possibilities of the Subordination relation!
	   *)
          if not(below (worlds, Gglobal, Glocal, I.targetFam V, I.targetFam V1')) then 
	    let 
		 (* There are no NDecs to worry about in Glocal.. *)
	      val X = I.newEVar (D.coerceCtx Glocal, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	    in
		lt (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), 
		    ((U', I.Dot (I.Exp (X), s1')), 
		     (V', I.Dot (I.Exp (X), s2'))))
	    end
	  else
	    let  
	      (* there are no NDecs.. so we don't need to worry about removing them.. *)
	      val X = I.Root (I.BVar (I.BVarVar ((ref NONE, I.EClo(V1', s1'), D.makeLFParamList (I.mergeCtx(Gglobal, Glocal)), ref nil), I.id)), I.Nil)
	    in
	      lt (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))))
	    end

      | ltW _ = crash()

    and ltSpine (worlds, Gglobal, Glocal, (Us, Vs), (Ss', Vs')) = 
          ltSpineW (worlds, Gglobal, Glocal, (Us, Vs), (Ss', Whnf.whnf Vs')) 

    and ltSpineW (worlds, Gglobal, Glocal, (Us, Vs), ((I.Nil, _), _)) = false
      | ltSpineW (worlds, Gglobal, Glocal, (Us, Vs), ((I.SClo (S, s'), s''), Vs')) =
          ltSpineW (worlds, Gglobal, Glocal, (Us, Vs), ((S, I.comp (s', s'')), Vs'))
      | ltSpineW (worlds, Gglobal, Glocal, (Us, Vs), ((I.App (U', S'), s1'), 
				   (I.Pi ((I.Dec (_, V1'), _), V2'), s2'))) = 
	  le (worlds, Gglobal, Glocal, (Us, Vs), ((U', s1'), (V1', s2'))) orelse 
	  ltSpine (worlds, Gglobal, Glocal, (Us, Vs), 
		   ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))))
      | ltSpineW _ = crash()


    (* eq (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), (U', s'), sc) = B
     
       Invariant:
       B holds  iff  
       Everything makes sense with prefix of Gglobal
            Glocal |- s1 : Glocal1   Glocal1 |- U : V1
       and  Glocal |- s2 : Glocal2   Glocal2 |- V : L
       and  Glocal |- U[s1] : V[s2] 
       and  Glocal |- s' : Glocal3  Glocal3 |- U' : V'
       and  U[s1] is unifiable with to U'[s']
       and  all restrictions in sc are satisfied
       and V[s2] is atomic
       and only U'[s'] contains EVars
	 (NOTE:  worlds refers to some local worlds we may need to consider in the "below" check)
    *)
    and eq (worlds, Gglobal, Glocal, (Us, Vs), (Us', Vs')) = 
        let
	  val _ = U.mark()
	  val b = U.LFunifiable (D.coerceCtx Gglobal, D.coerceCtx Glocal, Vs, Vs')
	          andalso U.LFunifiable (D.coerceCtx Gglobal, D.coerceCtx Glocal, Us, Us')
	  val _ = U.unwind()
	in
	  b
	end

    (* le (worlds, Gglobal, Glocal, Q, ((U, s1), (V, s2)), (U', s'), sc) = B
     
       Invariant:
       B holds  iff  
       Everything makes sense with prefix of Gglobal
       and  Glocal |- s1 : Glocal1   Glocal1 |- U : V1
       and  Glocal |- s2 : Glocal2   Glocal2 |- V : L
       and  Glocal |- U[s1] : V[s2] 
       and  Glocal |- s' : Glocal3  Glocal3 |- U' : V'
       and  U[s1] is a equal to or a subterm of U'[s']
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] is atomic
       and only U'[s'] contains EVars
	 (NOTE:  worlds refers to some local worlds we may need to consider in the "below" check)
    *)
    and le (worlds, Gglobal, Glocal, UsVs, UsVs') = eq (worlds, Gglobal, Glocal, UsVs, UsVs') orelse 
          leW (worlds, Gglobal, Glocal, UsVs, Whnf.whnfEta UsVs')
    and leW (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), 
	     ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
	      (I.Pi ((I.Dec (_, V2'), _), V'), s2'))) =
	if not(below (worlds, Gglobal, Glocal, I.targetFam V, I.targetFam V1')) then
	  let 
	    val X = I.newEVar (D.coerceCtx Glocal, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	  in
		le (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), 
		    ((U', I.Dot (I.Exp (X), s1')), 
		     (V', I.Dot (I.Exp (X), s2'))))
	  end
	else
	  let
	    val X = I.Root (I.BVar (I.BVarVar ((ref NONE, I.EClo(V1', s1'), D.makeLFParamList (I.mergeCtx(Gglobal, Glocal)), ref nil), I.id)), I.Nil)
	  in                         
	      le (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))))
	  end

      | leW (worlds, Gglobal, Glocal, (Us, Vs), (Us', Vs')) = 
	  lt (worlds, Gglobal, Glocal, (Us, Vs), (Us', Vs'))


    (* ltinit (worlds, Gglobal, Glocal, ((U, s1), (V, s2)), ((U', s1'), (V', s2'))) = B'
       
       Invariant:
       B' holds  iff
       All typing makes sense when the context is prefixed with Gglobal
       and  Glocal |- s1 : Glocal1   Glocal1 |- U : V1
       and  Glocal |- s2 : Glocal2   Glocal2 |- V : L
       and  Glocal |- U[s1] : V[s2] 
       and  Glocal |- s1' : Glocal3   Glocal3 |- U' : V1'
       and  Glocal |- s2' : Glocal4   Glocal4 |- V' : L
       and  Glocal |- U'[s1'] : V'[s2']
       and  U[s1] is a strict subterm of U'[s1']
       and only U'[s'] contains EVars
	 (NOTE:  worlds refers to some local worlds we may need to consider in the "below" check)
    *)
    fun ltinit (worlds, Gglobal, Glocal : D.Dec I.Ctx, (Us, Vs), UsVs') = 
          ltinitW (worlds, Gglobal, Glocal, Whnf.whnfEta (Us, Vs), UsVs')

    and ltinitW (worlds, Gglobal, Glocal, (Us, Vs as (I.Root _, _)), UsVs') =
          lt (worlds, Gglobal, Glocal, (Us, Vs), UsVs')
      | ltinitW (worlds, Gglobal, Glocal, ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)), ((U', s1'), (V', s2'))) =
	  let
	    val D' = case I.decSub(D, s2)  (* maybe we should name the dec using Names.decLUName .... *)
	             of I.Dec(name, A) => D.NonInstantiableDec (D.NewDecLF (name, A))
		      | _ => crash()
	  in
	    ltinit (worlds, Gglobal, I.Decl (Glocal, D'), ((U, I.dot1 s1), (V, I.dot1 s2)), 
		  ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))))
	  end
      | ltinitW _ = crash()



    fun conv ((Us, Vs), (Us', Vs')) =
        Conv.conv (Vs, Vs') andalso  
	Conv.conv (Us, Us') 	 

    (* ************************************************************** *)
    (* ************************************************************** *)
    (* *****************END OF LF COMPARISONS *********************** *)



    (* raiseLF(Gglobal, Glocal, M1, M2) = G', (M1s', A1s'), (M2s', A2s'), worlds
     * such that Gglobal, G' |- M1s' : A1s' (and is EVar free)
     * and       Gglobal, G' |- M2s' : A2s' (and is EVar free)
     * and  if M1 < M2 then M1s' < M2s'
     * and  if M1 <= M2 then M1s' <= M2s'
     * and "worlds" contains the world declarations in Glocal
     *
     * In other words, this function removes EVars from M1 and M2
     * and makes it so the term makes sense in Gglobal, G' 
     * where G' contains the collection of EVars
     *)
    fun raiseLF(Gglobal, Glocal, M1, M2) =
           let
	     fun getWorlds (I.Decl(G, D.NonInstantiableDec (D.NewDecWorld (_, W)))) = W :: (getWorlds G)
	       | getWorlds (I.Decl(G, _)) = getWorlds G
	       | getWorlds I.Null = []

	     val localWorlds = getWorlds Glocal

	     (*
	      * First we want to have both terms make sense with respect to Gglobal
	      * by adding appropriate Lam's.
	      *)
	     fun raiseTerm (I.Null, U) = U
	       | raiseTerm (I.Decl (G, I.NDec), U) = 
	                    (* G,Ndec |- U : A
			     * G |- U[invShift] : A[invShift]
			     *)
	                    raiseTerm (G, I.EClo(U, I.invShift))
	       | raiseTerm (I.Decl (G, D), U) = 
			    (* G,A |- U : B *)
			    (* G |- Lam{A}U : Pi{A}B *)
			    raiseTerm (G, I.Lam (D, U))

	     val M1' = raiseTerm(D.coerceCtx Glocal, M1) (* Gglobal |- M1' : A1' *)
	     val M2' = raiseTerm(D.coerceCtx Glocal, M2) (* Gglobal |- M2' : A2 *)


             (* We now need to get rid of all EVars using Abstraction *)
	     val (M1', M2', G') = DelphinAbstract2.abstractComparison(M1', M2')
	       
	     val lfCtx = D.coerceCtx(I.mergeCtx(Gglobal, G'))
	     val A1' = TypeCheck.infer'(lfCtx, M1')
	       handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
	     val A2' = TypeCheck.infer'(lfCtx, M2')
	       handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
	   in
	     (G', ((M1', I.id), (A1', I.id)), ((M2', I.id), (A2', I.id)), localWorlds)
	   end


    fun LFless(Gglobal, Glocal, M1, M2) = 
           let
	     val (G', M1A1', M2A2', worlds) = raiseLF(Gglobal, Glocal, M1, M2)
	     	   in
	     ltinit (worlds, Gglobal, G', M1A1', M2A2')
	   end

    fun LFlessEq (Gglobal, Glocal, M1, M2) = 
           let
	     val (G', M1A1', M2A2', worlds) = raiseLF(Gglobal, Glocal, M1, M2)
	              (*
	                   val (M1', _) = M1A1'
	                   val (M2', _) = M2A2'
			   val G = I.mergeCtx(Gglobal, G')
			   val _ = PrintDelphinInt.varReset G;
	                   val G = PrintDelphinInt.ctxName G
			   val E1s = Formatter.makestring_fmt(PrintDelphinExt.ExpToFormat0(
							PrintDelphinInt.convert_Exp(true, false (* not pattern *), G, D.Quote (I.EClo M1')), 
											   PrintDelphinExt.baseK, false, false))
	      
			   val E2s = Formatter.makestring_fmt(PrintDelphinExt.ExpToFormat0(
							PrintDelphinInt.convert_Exp(true, false (* not pattern *), G, D.Quote (I.EClo M2')), 
											   PrintDelphinExt.baseK, false, false))
			   val _ = print ("ADAM DEBUG:  " ^ E1s ^ " .. comparing to .. " ^ E2s ^"\n")
			   fun debugAdam() = ()
			   val _ = debugAdam()
                       *)

	   in
	     (ltinit(worlds, Gglobal, G', M1A1', M2A2')) orelse conv(M1A1', M2A2')
	   end
			     

    fun check(debug, smartInj, printEps, filename, r, Gglobal, E) =
          (* EVERYTHING including execution takes place with respec to Gglobal,
	   * which represents the top-level so far..
	   *)
           let

	        val errorList : string list ref  = ref []

	        val interactive = ref false; (* only relevant when debug is true *)

	        val evarList : ((D.Exp option ref) * TermCriteria) list ref = ref nil  
		                (* As we are doing a virtual execution of the Delphin program,
				 * we do not want to extend the context with InstantiableDecs .
				 *
				 * Therefore, when going under a fixpoint we will apply the body to a logic
				 * variable which has the TermCriteria saved that we need.
				 *)

		fun newVar (F, term) =
		      let
			val r = ref NONE
			val X = D.EVar ((r, F), D.id)
			val _ = evarList := (r, term) :: !evarList
		      in
			X
		      end

		fun findVar' (r, []) = NONE
		  | findVar' ((r : D.Exp option ref), (r2,term)::rest) =
		                     if (r = r2) then SOME term
				     else findVar'(r, rest)

		fun findVar r = findVar'(r, !evarList)

		fun generateCriticalError(fileInfo, s) =
		  let
		    val msg = "WARNING:  Function may not terminate:\n" ^ s ^ "\n"
		  in
		    case fileInfo
		      of NONE => raise Error (Paths.wrapLoc(Paths.Loc (filename, r), msg))
		    | SOME(filename, r) => raise Error (Paths.wrapLoc(Paths.Loc (filename, r), msg))
		  end 

	        fun generateErrorString(fileInfo, s) =
		  let
		    val msg = "WARNING:  Function may not terminate:\n" ^ s ^ "\n"
		  in
		    case fileInfo
		      of NONE => (Paths.wrapLoc(Paths.Loc (filename, r), msg))
		    | SOME(filename, r) => (Paths.wrapLoc(Paths.Loc (filename, r), msg))
		  end 

		(* addError (b, fileInfo, s) = if b = true, then it adds an error, otherwise does nothing *)
		fun addError(true, fileInfo, s) = (errorList := !errorList @ [generateErrorString(fileInfo, s)])
		  | addError(false, fileInfo, s) = ();


		fun newDecEqual(D.NewDecLF (_, A1), D.NewDecLF (_, A2)) = Conv.conv ((A1, I.id), (A2, I.id))
		  | newDecEqual(D.NewDecWorld (_, W1), D.NewDecWorld(_, W2)) = 
		                                  WorldSubsumption.worldSubsume(W1, W2)
						  andalso WorldSubsumption.worldSubsume(W2, W1)
		  | newDecEqual _ = false

		fun less(Glocal : D.Dec I.Ctx, E1, E2) = lessW(Glocal, D.whnfE E1, D.whnfE E2)
		and lessW(Glocal, D.Quote M1, D.Quote M2) = LFless(Gglobal, Glocal, M1, M2)
		  | lessW(Glocal, E1p as D.Pair(E1', E1s',_), E2p as D.Pair (E2', E2s',_)) = 
		                                     lessEq(Glocal, E1p, E2') orelse lessEq(Glocal, E1p, E2s') 
						     orelse (less(Glocal, E1', E2') andalso lessEq(Glocal, E1s', E2s'))
						     orelse (lessEq(Glocal, E1', E2') andalso less(Glocal, E1s', E2s'))
		  | lessW(Glocal, E1, D.Pair(E2', E2s',_)) = lessEq(Glocal, E1, E2') orelse lessEq(Glocal, E1, E2s')
		  | lessW(Glocal, D.New(D1, E1, _), D.New(D2, E2, _)) = (newDecEqual(D1, D2)
									 andalso
									 (less(I.Decl(Glocal, D.NonInstantiableDec D1), E1, E2)))
		  | lessW _ = false
									
						     
		and lessEq(Glocal, E1, E2) = lessEqW(Glocal, D.whnfE E1, D.whnfE E2)
		and lessEqW (Glocal, D.Var (D.Fixed k1, _), D.Var (D.Fixed k2, _)) = (k1= k2)
		  | lessEqW (Glocal, D.Var (D.BVarLF ((r, A, list, cnstrs), s), _), D.Var (D.BVarLF ((r', A', list', cnstrs'), s'), _)) = 
		             Conv.convB ((I.BVarVar ((r,A, list, cnstrs), s)), (I.BVarVar((r',A', list', cnstrs'), s')))

		  | lessEqW (Glocal, D.Quote M1, D.Quote M2) = LFlessEq(Gglobal, Glocal, M1, M2)
		  | lessEqW (Glocal, D.Unit, D.Unit) = true

		  | lessEqW(Glocal, E1p as D.Pair(E1', E1s',_), E2p as D.Pair (E2', E2s',_)) = 
			                               lessEq(Glocal, E1p, E2') orelse lessEq(Glocal, E1p, E2s') 
						       orelse (lessEq(Glocal, E1', E2') andalso lessEq(Glocal, E1s', E2s'))
						       
		  | lessEqW(Glocal, E1, D.Pair(E2', E2s',_)) = lessEq(Glocal, E1, E2') orelse lessEq(Glocal, E1, E2s')
						       

		  | lessEqW(Glocal, D.New(D1, E1, _), D.New(D2, E2, _)) = (newDecEqual(D1, D2)
									    andalso
									    (lessEq(I.Decl(Glocal, D.NonInstantiableDec D1), E1, E2)))

		  | lessEqW(Glocal, D.EVar ((r1, _), t1), D.EVar ((r2, _), t2)) = 
						       (r1 = r2) andalso (shiftSub t1) andalso (shiftSub t2) 
		                                       (* They should both always be shifts... *)

		  | lessEqW _ = false

                  
      
		fun autoCompare(Glocal : D.Dec I.Ctx, E1, E2) = if less(Glocal, E1, E2) then Less
						  else if lessEq(Glocal, E1, E2) then Equal
						       else Unknown


		fun compare(Glocal : D.Dec I.Ctx, E1, E2, fileInfo) = 
		  if (debug) andalso (!interactive) then
		         let
			   val R = autoCompare(Glocal, E1, E2)
			   val Rstr = case R of
			               Less => " \"<\" "
				     | Equal => " \"=\" "
				     | Unknown => " \"?\" "

			   val G = I.mergeCtx(Gglobal, Glocal)
			   val _ = PrintDelphinInt.varReset G;
			   val E1s = Formatter.makestring_fmt(PrintDelphinExt.ExpToFormat0(
							 PrintDelphinInt.convert_Exp(true, false (* not pattern *), G, E1), 
											   PrintDelphinExt.baseK, false, false))
	      
			   val E2s = Formatter.makestring_fmt(PrintDelphinExt.ExpToFormat0(
							PrintDelphinInt.convert_Exp(true, false (* not pattern *), G, E2), 
											   PrintDelphinExt.baseK, false, false))

	      
			   val (filename, r) = case fileInfo of NONE => (filename, r) | SOME X => X

			   val _ = print (Paths.wrapLoc(Paths.Loc(filename, r), 
							("DEBUG INFO:  Termination Comparison:  " ^ E1s ^ Rstr ^ E2s ^ "\n")))
	                   (* 
                             val _ = print "\n\nDelphin Comparison Checker = YOU\n"
                             val _ = print (E1s ^ "  {<, =, ?} " ^ E2s ^ " -- Specify Comparison:  ");
                           *)
			   val _ = print "-- Specify Comparison: {<, =, ?}  "
			   val result = TextIO.inputLine TextIO.stdIn
			 in
			   case result
			     of NONE => (print "Invalid Response!\n" ; compare(G, E1, E2, fileInfo))
			     | SOME s => if (String.isSubstring "<" s )
					   then Less
					 else if (String.isSubstring "=" s )
						then Equal
					      else if (String.isSubstring "?" s )
						     then Unknown
						   else (print "Invalid Response!\n" ; compare(G, E1, E2, fileInfo))
			 end
		  else if (debug) then

		         let
			   val R = autoCompare(Glocal, E1, E2)
			   val Rstr = case R of
			     Less => " \"<\" "
			   | Equal => " \"=\" "
			   | Unknown => " \"?\" "
			       

			   val G = I.mergeCtx(Gglobal, Glocal)
			   val _ = PrintDelphinInt.varReset G;
			   val E1s = Formatter.makestring_fmt(PrintDelphinExt.ExpToFormat0(
							PrintDelphinInt.convert_Exp(true, false (* not pattern *), G, E1), 
											   PrintDelphinExt.baseK, false, false))
	      
			   val E2s = Formatter.makestring_fmt(PrintDelphinExt.ExpToFormat0(
							PrintDelphinInt.convert_Exp(true, false (* not pattern *), G, E2), 
											   PrintDelphinExt.baseK, false, false))

			   val (filename, r) = case fileInfo of NONE => (filename, r) | SOME X => X

			   val _ = print (Paths.wrapLoc(Paths.Loc(filename, r), 
							("DEBUG INFO:  Termination Comparison:  " ^ E1s ^ Rstr ^ E2s ^ "\n")))
			  (*
			   val _ = print ("DEBUG INFO:  Termination Comparison:  " ^ E1s ^ Rstr ^ E2s ^ "\n");
			   *)
			 in
			   R
			 end
		  else
		    autoCompare(Glocal, E1, E2)




		(* lookup (G, i) = T
		 * where T is the type of the variable at index i (not weakened to context G)
		 *)
		fun lookup (I.Decl(G, (D.InstantiableDec (D.NormalDec (_, T)))), 1) = (T)
		  | lookup (I.Decl(G, (D.NonInstantiableDec (D.NewDecLF (_, A)))), 1) = (D.LF(D.Param, A))
		  | lookup (I.Decl(G, (D.NonInstantiableDec (D.NewDecWorld (_, W)))), 1) = raise Error "Delphin Termination Error:  Attempted to access invalid (world) index"
		  | lookup (I.Decl(G, (D.NonInstantiableDec _)), i) = if i < 1 then crash() else lookup(G, i-1)
		  | lookup (I.Decl(G, (D.InstantiableDec _)), i) = if i < 1 then crash() else lookup(G, i-1)
		  | lookup (I.Null, i) = raise Error "Delphin Termination Error:  Attempted to access invalid index"
		
		fun substTerm(TermApp (E, l), t) = TermApp (D.EClo(E, t), substTerm(l, t)) 
		  | substTerm(TermNew (D, l), t) = TermNew (D.substNewDec (D, D.coerceSub t), substTerm (l, D.dot1 (t, NONE)))
		  | substTerm(TermPair (l1, l2), t) = TermPair (substTerm(l1, t), substTerm (l2, t))
		  | substTerm(TermList (ls), t) = TermList (map (fn E => substTerm(E, t)) ls)
		  | substTerm(TermYES, t) = TermYES
		  | substTerm(TermNO, t) = TermNO

		(* not needed...
		fun substTermDummy(TermAppDummy (Es, l), t) = TermAppDummy (map (fn (vis,E) => (vis, D.EClo(E, t))) Es, substTermDummy(l, t))
		  | substTermDummy(TermNewDummy (D, l), t) = TermNewDummy (D.substNewDec (D, D.coerceSub t), substTermDummy (l, D.dot1 (t, NONE)))
		  | substTermDummy(TermPairDummy (l1, l2), t) = TermPairDummy (substTermDummy(l1, t), substTermDummy (l2, t))
		  | substTermDummy(TermListDummy (ls), t) = TermListDummy (map (fn E => substTermDummy(E, t)) ls)
		  | substTermDummy(TermYESDummy, t) = TermYESDummy
		  | substTermDummy(TermNODummy, t) = TermNODummy
                 *)



		(* terminator (G, E, K) = V
		 *   where V is the result of a virtual execution of E
		 *   where everytime we encounter a fixpoint, we apply it out to dummy arguments.
		 *   ...... raises Error if not terminating...
		 * 
		 *  G |- E : T
		 *  K is a continuation of type: (Value, (Type, TermCriteria)) ->  Value
		 * 
		 *  We use a continuation style approach due to the "App" case where we want to *continue* execution
		 *  in each possible branch.
		 *)

	        fun terminator(Glocal, E, K) = terminatorW(Glocal, D.whnfE E, K) 
		                        handle D.SubstFailed => raise Error ("Delphin Termination Error:  whnf Failed (IMPOSSIBLE!)")


		and terminatorW(Glocal, E as D.Var (D.Fixed i, fileInfo), K) = 
		         (* Will only occur if E is a parameter or E is a variable in Gglobal... *)
		         let
			   val (T) = lookup(I.mergeCtx(Gglobal, Glocal), i)
			   val T' = D.substTypes(T, I.Shift i)
			   (* val term' = substTerm(term, D.shiftTo(i, D.id)) *)
			   val term' = setYESTermsType T' (* this is terminating.. *)

		           (* let's return a new EVar so it won't get stuck if it tries to match against it with a value.. *)
			   val E = newVar(getFormula T', term')
			 in
			   K (E, (T', term'))
			 end

		  | terminatorW(Glocal, E as D.Var (D.BVarLF ((_, A, _, _), s), fileInfo), K) = K (E, (D.LF (D.Param, I.EClo(A, s)), TermYES))
		  | terminatorW(Glocal, E as D.Quote M, K) =
		           let
			     val A = TypeCheck.infer'(I.mergeCtx(D.coerceCtx Gglobal, D.coerceCtx Glocal), M)
			       handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
			   in
			     K (E, (D.LF(D.Existential, A), TermYES))
			   end

		  | terminatorW(Glocal, E as D.Unit, K) = K (E, (D.Meta(D.Top), TermYES))

		  | terminatorW(Glocal, E as D.Lam (Clist, F, fileInfo), K) = K (E, (D.Meta F, setYESTermsF F))
				
		  | terminatorW(Glocal, D.New (D, E, fileInfo), K) = 
			   terminator(I.Decl(Glocal, (D.NonInstantiableDec D)), E,
				      fn (V, (T, term)) =>  K (D.New(D, V, fileInfo), (D.Meta(D.Nabla(D, getFormula T)), TermNew (D, term))))
			    

		  | terminatorW(Glocal, D.App (E1, args), K) =  
	              terminator(Glocal, E1,
			   fn (funVal, (T1, term)) =>
				let
				  val F1 = getFormula T1
				  val (Ds, fResult) = case (D.whnfF F1)
		                               of D.All(Ds, F) => (Ds, F)
					        | _ => raise Error "Delphin Termination Error:  Application to non-functional type"

					       
				  fun checkArgs ((vis,fileInfo,E2)::args, termOrig as TermApp(var, term), (_, D.NormalDec(_, tArg))::Ds, t (* codomain of t is Glocal *)) =
				         if isIgnored(vis, tArg) then
					    checkArgs(args, termOrig, Ds, I.Dot (D.coerceExp E2, t))
					 else
					    (* termination criteria only applies to visible arguments *)
					    (case compare(Glocal, E2, var, fileInfo)
					       of Less => checkArgs(args, TermYES, Ds, I.Dot (D.coerceExp E2, t)) (* it terminates! *)
					        | Equal => (case term
						            of TermNO => 
							      (addError(true, fileInfo, "Argument(s) stay the same (do not get smaller)") ; 
							       (* We added an error, so we now pretend it is terminating and
								* see if we get any other terminatione rrors.. *)
							       checkArgs(args, TermYES, Ds, I.Dot (D.coerceExp E2, t))
								)
							     | _ => checkArgs(args, term, Ds, I.Dot (D.coerceExp E2, t)) (* it may terminate *))
						| Unknown => (addError(true, fileInfo, "Argument does not get smaller") ;
							       (* We added an error, so we now pretend it is terminating and
								* see if we get any other terminatione rrors.. *)
							       checkArgs(args, TermYES, Ds, I.Dot (D.coerceExp E2, t)))
					    )


				    | checkArgs ((vis,fileInfo,E2)::args, term, (_, D.NormalDec(_, tArg))::Ds, t (* codomain of t is Glocal *)) =
					     checkArgs(args, term, Ds, I.Dot (D.coerceExp E2, t))

				    | checkArgs ([], term, [], t) =(t, term)
				    | checkArgs _ = raise Error "Delphin Termination Error:  Incompatible number of args"
					   
				  (* Check that all arguments are terminating! *)
		                  fun evalArgs (vis, fileInfo, E) =
				       let
					 val V = terminator (Glocal, E, 
							     fn (V, (T, term)) => 
							          (addError(not (isTerm term), fileInfo, "Argument is not terminating") ; V))
				       in
					 (vis, fileInfo, V)
				       end

				  val argsVal = map evalArgs args
				  val (t, leftOverTerm) = checkArgs (argsVal, term, Ds, I.id)
 
                                  (* checkArgs may return TermYES, but we now make it into the right form *)
				  val leftOverTerm = case leftOverTerm
				                     of TermYES => setYESTermsF (D.FClo(fResult, t))
						      | _ => leftOverTerm
				in
				  case funVal 
				    of (D.Lam(cList, _, fileInfo)) => 
				          let
					       fun matchCaseR (D.Match ((_, E1)::pats, E2), (_, _, S)::Spine) =
						 (let
						    val E1 = O.eval (Glocal) E1 (* evaluate the pattern.
										 * needed for patterns that use "pop"
										 *)
						    val _ = U.unifyE(D.coerceCtx Gglobal, D.coerceCtx Glocal, E1, S)
						  in
						    matchCaseR(D.Match(pats, E2), Spine)
						  end
						    handle U.Error _ => generateCriticalError(fileInfo, "Termination Checker Virtual Execution failed ")
							 | O.NoSolution _ => generateCriticalError(fileInfo, "Termination Checker Virtual Execution failed "))

						 | matchCaseR (D.Match ([], E2), []) = E2 (* match successful! *)
						 | matchCaseR _ = crash() (* badly typed *)

					       fun matchCases [] = ()
						 | matchCases (C::cs) = 
						       let
							 val _ = U.mark()
							 val E = matchCaseR(O.reduceCase Gglobal (Glocal) C, argsVal)
							 val _ = terminator (Glocal, E, K)
							 val _ = U.unwind()
						       in
							 matchCases cs
						       end
					       val _ = matchCases cList
					  in
					    (* We have no information about what the result is, so we just make it a fresh Var *)
					    (* We do not need to call the continuation as it was called on all branches *)
					    (* 
					     * It appears we are ignoring "leftOverTerm", but it should be YES
					     * as it evaluated to a lambda!
					     *)
					    newVar(D.FClo(fResult, t), leftOverTerm)
					  end

				    
				     | _ => K (newVar(D.FClo(fResult, t), leftOverTerm), (D.Meta(D.FClo(fResult, t)), leftOverTerm))
				end)


		  | terminatorW(Glocal, D.Pair (E1, E2, F), K) = 
		          terminator(Glocal, E1,
				     fn (E1', (firstType, firstTerm))
				     => terminator(Glocal, E2, 
						   fn (E2', (secondType, secondTerm)) =>
						   let
						     val (pairFstT, pairSndF) = case (D.whnfF F)
				                             of (D.Exists(D.NormalDec (_, T), F)) => (T, F)
							      | _ => crash()

						     val t = D.Dot(D.Prg E1, D.id)  (* Glocal |- E1.id  : Glocal,_ *)
						     val _ = unifyTypes(Gglobal, Glocal, firstType, pairFstT)
						     val _ = unifyTypes(Gglobal, Glocal, secondType, D.Meta(D.FClo(pairSndF, D.coerceSub t)))
						   in
						     K (D.Pair (E1', E2', F), (D.Meta(F), TermPair (firstTerm, secondTerm)))
						   end))

		  | terminatorW(Glocal, D.ExpList [], K) = K (D.ExpList [], (D.Meta (D.FormList []), TermList []))
		  | terminatorW(Glocal, D.ExpList (E1::Es), K) =
		          terminator(Glocal, E1,
				     fn (E1', (T1', term'))
				     => terminator(Glocal, D.ExpList Es, 
						   fn (E2, (secondType, secondTerm)) =>
						   let
						     val Es' = case (D.whnfE E2)
						               of (D.ExpList Es') => Es'
								| _ => crash()
								 
						     val F1' = getFormula T1'
						     val Fs' = case (D.whnfF (getFormula secondType))
						                of (D.FormList Fs') => Fs'
								 | _ => crash()

						     val terms' = case secondTerm
						                  of TermList terms' => terms'
								   | _ => crash()
						   in
						     K (D.ExpList (E1'::Es'), (D.Meta(D.FormList (F1'::Fs')), TermList (term' :: terms')))
						   end))

		  | terminatorW(Glocal, D.Proj (E, i), K) = 
			  (terminator(Glocal, E,
				     fn (V, (T1, terms)) =>
				     case (V, D.whnfF(getFormula T1), terms)
				       of (D.ExpList Elist, D.FormList Flist, TermList termL) => K (getElement(i, Elist), (D.Meta (getElement(i, Flist)), getElement(i, termL)))
				        | (V, D.FormList Flist, TermList termL) => K (D.Proj(V, i), (D.Meta(getElement(i, Flist)), getElement(i, termL)))
					| _ => crash()))


		  | terminatorW(Glocal, D.Pop (i, E, fileInfo), K) = 
			      let
				fun popCtx (0, G) = G
				  | popCtx (i, I.Decl(G, D)) = popCtx (i-1, G)
				  | popCtx (i, I.Null) = crash() (* Broken invariant .. cannot pop to Gglobal ...*)
			      in
				terminator(popCtx(i, Glocal), E,
					   fn (V, (T, nabTerm)) =>
					   let
					     val (F, term) = case (D.whnfF (getFormula(T)), nabTerm)
					                      of (D.Nabla(D, F), TermNew (_, term)) => (F, term)
							       | _ => crash()
					     val F' = D.FClo(F, I.Shift (i-1))
					     val term' = substTerm(term, D.shiftTo(i-1, D.id))	
					   in
					     case V 
					       of (D.New (_, V, _)) => K (D.substE'(V, D.shiftTo(i-1, D.id)), (D.Meta F', term'))

					        | (V as D.EVar ((r (* ref NONE *), F), t)) => 
						   (case (findVar r)
						    of NONE =>
						      (* This case can occur when evaluating patterns *)
						      let
							val (newD, newF) = 
							    let
						              fun removeNabla (D.Nabla(D, F)) = (D, F)
								| removeNabla _ = crash() (* Error *)
							    in
							      removeNabla (D.whnfF F)
							    end

							(* Assuming Glocal = G1,x:A[t],G2 
							 * G1,x:A[t] |- (r : {<x:A>}newF) [t] : {<x:A[t]>} newF[dot1 t]
							 * G1 |- t : G*
							 * G* |- r = new x:A.(X : newF)
							 * G1,A[t] |- dot1 t : G*,A
							 *)
						    
							val newBody = D.newEVar(newF)
							val _ = r := SOME(D.New(newD, newBody, NONE))
						      in
							K (D.substE'(newBody, D.shiftTo(i-1, D.dot1 (t, fileInfo))),
							 (D.Meta F', term'))
						      end
						  | SOME _ => 
						      (* We do not know what the result should be, so we just make it a fresh Var *)
						      K (newVar(F', term'), (D.Meta F', term'))
						      )

						| (D.Lam(Clist, F, fileInfo)) => 
						      let
							fun addPop C = D.PopC(i, C)

							(* precondition:  in whnf *)
							fun removeNewF (D.Nabla(_, F)) = D.FClo(F, I.Shift (i-1))
							  | removeNewF (F as D.FVar _) = crash() (* should be filled in 
												  * before checking
												  * termination
												  *)
							  | removeNewF _ = crash()
						      in
							K (D.Lam (map addPop Clist, removeNewF (D.whnfF F), NONE),
							 (D.Meta F', term'))
						      end
						| V => K (newVar(F', term'), (D.Meta F', term'))
						      
					   end)
			      end

		  | terminatorW(Glocal, D.Fix (D as D.NormalDec(_, Tspecified), E), K) =  
			  if not(D.metaVarOccurs(1, E))
			    then (* it is really not a fixpoint.. no recursive calls! *)
			      terminator(Glocal, D.EClo(E, D.invShift), K)
			  else
				(* This is where the real work comes in.. *)
				let
				  (* makeVars (Ds, t)
				   * G' |- t : G0 and G0 |- Ds wff
				   *)
				  fun makeVars (G', [], t) = ([], t)
				    | makeVars (G', ((vis, D.NormalDec(_, D.LF (isP, A))) :: Ds), t)
				         = (case (D.whnfP isP)
				             of D.Existential =>
					             let
						       val X = I.newEVarPruneNdec (D.coerceCtx G', I.EClo(A, D.coerceSub t))
						       val t = D.Dot (D.Prg (D.Quote X), t) (* G' |- t : G0,A *)
						       val (vars, t') = makeVars (G', Ds, t)
						     in
						       ((vis, D.Quote X, D.LF(isP, I.EClo(A, D.coerceSub t)))::vars, t')
						     end
					      | D.Param =>
						     let 
						       val X = D.Var (D.newParamVarPruneNDecs (Gglobal, G', I.EClo(A, D.coerceSub t)), NONE)
						       val t = D.Dot (D.Prg X, t)
						       val (vars, t') = makeVars (G', Ds, t)
						     in
						       ((vis, X, D.LF(isP, I.EClo(A, D.coerceSub t)))::vars, t')
						     end

					      | D.PVar _ => raise Error "Delphin Termination Error:  Unexpected PVar")

				    | makeVars (G', ((vis, D.NormalDec (_, D.Meta F)) :: Ds), t)
				         = let
				               val X = D.newEVar(D.FClo(F, D.coerceSub t))
						    (* OLD:  D.EVar ((ref NONE, F), t)
						     * We want to keep met-level EVars under shift substitutions,
						     * So we will apply the substitution to the type instead.
						     *)
					       val t = D.Dot (D.Prg X, t)
					       val (vars, t') = makeVars (G', Ds, t)
					   in
					     ((vis, X, D.Meta (D.FClo(F, D.coerceSub t)))::vars, t')
					   end


				  fun getTermVars (G, F) = getTermVarsW(G, D.whnfF F)
				  and getTermVarsW (G, D.All (Ds, F)) = 
				           let
					     val (vars, t) = makeVars (G, Ds, D.id)
					     val rest = getTermVars (G, D.FClo(F, D.coerceSub t))
					   in
					     TermAppDummy(vars, rest)
					   end
				    | getTermVarsW (_, F) = 
                                                        if (hasFun F) then 
					                 generateCriticalError(NONE, 
								       "Cannot termination check fixpoints whose output also has functions... (at least not yet...)") 
							 (* COMMENT:  This isn't too difficult.. we would just need to apply out the functions 
							  * in the result as well...
							  * For examples, if foo : T -> unit 
							  * then we just do "foo X" where X is a fresh variable.
							  *
							  * If instead, foo : T -> (unit * (S1 -> S2))
							  * then we should do"
							  *  (1) (_, bar) = foo X
							  *  (2) bar Y
							  * Currently this is not supported.
							  *)
						       else
							 TermNODummy

				  fun generateVars (G, F) = generateVarsW (G, D.whnfF F)
				  and generateVarsW (G, D.Nabla(D, F)) = TermNewDummy (D, generateVars (I.Decl(G, (D.NonInstantiableDec D)), F))
				    | generateVarsW (G, F as D.All _) = (getTermVars (G, F))
				    | generateVarsW (G, D.FormList _) = crash() 
				    | generateVarsW _ = raise Error "Delphin Termination Error:  Badly formed Fixpoint"

				  val FspecifiedList = case (D.whnfF (getFormula Tspecified))
				                         of D.FormList Flist => Flist
							  | F => [F] 

				  val termDummyList = map (fn F => generateVars(Glocal, F)) FspecifiedList
				  val termCriteriaList = map removeTermDummy termDummyList
				  val numFuns = List.length FspecifiedList
				  val singleEntry = (numFuns = 1)


				  (* Check that all functions are of the SAME Nab{G}._ *)
				  fun getShape (TermNew (D, T)) = D.Nabla(D, getShape T)
				    | getShape _ = D.Top

				  fun checkAllCompatible [] = ()
				    | checkAllCompatible [F] =()
				    | checkAllCompatible (F1::F2::Fs) =
				          let
					    val _ = (U.unifyF(D.coerceCtx Gglobal, D.coerceCtx Glocal, F1, F2)
						     handle U.Error s => generateCriticalError(NONE, "Cannot termination check mutually recursive fixpoints that have different {<..>} in the type."))
					  in
					     checkAllCompatible(F1:: Fs)
					  end

				  val _ = checkAllCompatible (map getShape termCriteriaList)

				  fun runFixpoint (i) =
					 if (i > numFuns) then
				           (* done trying all the functions.. now continue with "K" *)
				           (K (D.newEVar (getFormula Tspecified), (Tspecified, setYESTermsType Tspecified)))
					 else
					   (* Try function i *)
				           let
					     val Fspecified = getElement(i, FspecifiedList)
					     val termCriteria = getElement(i, termCriteriaList)
					     val termDummy = getElement(i, termDummyList)

					     (* endYes(desiredTermination-endingInYES,  templateToFollow) *)
					     fun endYes(TermNO, TermApp _) = TermYES
					       | endYes(TermNO, TermNO) = TermYES
					       | endYes(TermApp _, TermNO) = TermYES
					       | endYes(TermApp (E,desired), TermApp (_, template)) = TermApp(E, endYes(desired, template))
					       | endYes(TermNew (D,desired), TermNew (_, template)) = TermNew(D, endYes(desired, template))
					       | endYes(desired, template) = 
					             generateCriticalError(NONE, "Cannot termination check mutually recursive fixpoints that have different {<..>} in the type.")

					     (* endNo(desiredTermination,  templateToFollow) *)
					     fun endNo(TermNO, TermApp _) = TermNO
					       | endNo(TermNO, TermNO) = TermNO
					       | endNo(TermApp _, TermNO) = TermNO
					       | endNo(TermApp (E,desired), TermApp (_, template)) = TermApp(E, endNo(desired, template))
					       | endNo(TermNew (D,desired), TermNew (_, template)) = TermNew(D, endNo(desired, template))
					       | endNo(desired, template) = 
					             generateCriticalError(NONE, "Cannot termination check mutually recursive fixpoints that have different {<..>} in the type.")


				             (* using termination for function i, build up what the other termination criteria's must be *)
				             (* Function i can call Function (i+x) with all equal arguments, but not the reverse. *)
					     fun buildUpTerminationCriteria 0 = []
					       | buildUpTerminationCriteria j = 
					            let
						      val current =
							 if (j > i) then
							          (* it is ok if all arguments are equal *)
							          endYes(termCriteria, getElement(j, termCriteriaList))
							 else if (j = i) then termCriteria
							 else endNo(termCriteria, getElement(j, termCriteriaList))
						    in
						      (buildUpTerminationCriteria (j-1)) @ [current]
						    end

					     val (function, finalF, finalTerm) = 
					          if singleEntry then (E, Fspecified, termCriteria)
						  else (D.Proj(E, i), D.FormList FspecifiedList, TermList (buildUpTerminationCriteria numFuns))

					     val X = newVar (finalF, finalTerm)

					     fun buildAppVars (f, TermNODummy) = f
					       | buildAppVars (f, TermAppDummy(args, term)) = buildAppVars(
									    D.App(f, map (fn (vis, E, T) => (vis, NONE, E)) args),
									    term)
					       | buildAppVars _ = raise Error "Delphin Termination Error: BUG (unexpected)"

					     and buildAppT (TermNewDummy (D, T), numPops) = D.New (D, buildAppT (T, numPops+1), NONE)
					       | buildAppT (term as TermAppDummy _, numPops) = 
					            let
						      fun buildPops 0 = D.EClo(function, D.Dot(D.Prg X, D.id)) 
							(* body of fixpoint, substituting X so it makes sense in Glocal! *)
							| buildPops n = D.Pop(1, buildPops (n-1), NONE)
						    in
						      buildAppVars (buildPops numPops, term)
						    end

					       | buildAppT (TermListDummy vars, _) = crash() 
					       | buildAppT _ = raise Error "Delphin Termination Error: BUG (unexpected)"

					     val execution = buildAppT (termDummy, 0) (* this is the fixpoint applied out.. *)

					     (* Even if it gets an error, we want to continue on all parts and accumulate the error messages. 
					      * i.e. we want to run the termination checker on all mutually recursive functions, even
					      * if one fails.
					      *)
					     val _ =  terminator(Glocal, execution, 
									  fn (V, (_, dead)) => 
									     (addError(not (isTerm dead), NONE, "Fixpoint is not terminating");
									      V))
					   in
					     runFixpoint (i+1)
					   end
				in
				  runFixpoint (1)
				end


		  | terminatorW(Glocal, E as D.EVar ((r (* ref NONE *), F), s), K) = 
				(case (findVar r)
				   of NONE =>				  
				        K (E, (D.Meta (D.FClo(F, D.coerceSub s)), setYESTermsF (D.FClo(F, D.coerceSub s))))
				    | SOME term =>
					K (E, (D.Meta (D.FClo(F, D.coerceSub s)), substTerm(term, s))))

		  | terminatorW(Glocal, D.EClo _, K) = crash() (* impossible by whnf *)


		fun listToString [] = ""
		  | listToString (s::ss) = s ^ "\n" ^ (listToString ss)

	        (* Run the termination checker *)
		val initialK = fn (V, (T, term)) => (addError(not (isTerm term), NONE, "Leftover termination constraints") ; V)
		val _ = terminator(I.Null (* local is empty *), E, initialK )

	   in
	     case (!errorList)
	       of [] => ()
		| sList => raise Error (listToString sList)
	   end
  end