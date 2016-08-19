(* Approximate Language for Delphin Types *)
(* Used for type reconstruction *)

structure DelphinApprox =
  struct
    structure D = DelphinIntSyntax
    structure I = IntSyn


    (* We allow an ambiguity in Delphin syntax.
     * Namely <M> can refer to either M of type A or
     * it can be (M, ()) of type (A * unit)
     *
     * If "smartInj" is on (true), then it will try to infer the correct
     * interpretation, prefering the latter whenever possible.
     * Otherwise, there is no syntactic sugar and <M> has type A
     *)
    datatype SmartInj 
      = InjLF
      | InjMeta
      | InjVar of (SmartInj option ref)
      

    datatype Types
      = LF of Paths.region * D.isParam * Approx.Exp
      | Meta of Paths.region * Formula
      | SmartInj of Paths.region * Approx.Exp * SmartInj * D.isParam
      
    and Formula
      = Top     of Paths.region
      | All     of Paths.region * ((D.Visibility * NormalDec) list) * Formula
      | Exists  of Paths.region * NormalDec * Formula 
      | Nabla   of Paths.region * NewDec * Formula
      | FormList of (Formula list) (* non-dependent pair generalization.. used for mutual recursion *)
      | FVar    of Paths.region * (Formula option ref)

    and NormalDec 
      = NormalDec of Paths.region * (string list) option * Types
  
    and NewDec 
      = NewDecLF of Paths.region * (string option) * Approx.Exp
      | NewDecWorld of Paths.region * (string option) * D.World
      
    and Dec
      = InstantiableDec of Paths.region * NormalDec    
      | NonInstantiableDec of Paths.region * NewDec
      | PatternVariable of string * Types (* this does NOT count towards the 
					   * actual variable number, but it is 
					   * used as a placeholder so we know
					   * the desired scope of pattern variables.
					   *)
				   


    (* This is a "weak" unify which is just used
    * to figure out the type families of all LF terms
    *)
    exception ApproxUnify of string

    fun popCtx (0, G) = G
      | popCtx (i, I.Decl(G, PatternVariable _)) = popCtx (i, G)
      | popCtx (i, I.Decl(G, _)) = popCtx (i-1, G)
      | popCtx (i, I.Null) = raise Domain (* Broken invariant *)


    fun ctxLength G =
      let 
	fun ctxLength' (I.Null, n) = n
	  | ctxLength' (I.Decl(G, PatternVariable _), n)= ctxLength' (G, n)
	  | ctxLength' (I.Decl(G, _), n)= ctxLength' (G, n+1)
      in
	ctxLength' (G, 0)
      end


    fun whnfF (FVar (_, ref (SOME F))) = whnfF F
      | whnfF F = F


    fun whnfT (SmartInj (r, A, InjLF, isP)) = LF(r, isP, A)
      | whnfT (SmartInj (r, A, InjMeta, isP)) = Meta(r, 
						Exists(r, NormalDec (r, NONE, LF(r, isP, A)), Top r))
      | whnfT (SmartInj (r, A, InjVar (ref (SOME I)), isP)) = whnfT(SmartInj(r, A, I, isP))
      | whnfT (Meta (r, F)) = Meta(r, whnfF F)
      | whnfT T = T

    fun occursTypes(r, LF _) = false
      | occursTypes(r, Meta (_, F)) = occursFormula(r, F)
      | occursTypes(r, SmartInj _) = false

    and occursFormula(r, Top _) = false
      | occursFormula(r, All (_, Ds, F)) = occursNormalDecs(r, Ds) orelse occursFormula(r, F)
      | occursFormula(r, Exists (_, D, F)) = occursNormalDec(r, D) orelse occursFormula(r, F)
      | occursFormula(r, Nabla (_, D, F)) = occursNewDec(r, D) orelse occursFormula(r, F)
      | occursFormula(r, FormList Flist) = foldl (fn (F, b) => b orelse occursFormula(r, F)) false Flist
      | occursFormula(r, FVar (_, ref (SOME F))) = occursFormula(r, F)
      | occursFormula(r, FVar (_, r2 as ref NONE)) = (r = r2)
    and occursNormalDec (r, NormalDec (_, _, T)) = occursTypes(r, T)

    and occursNormalDecs (r, []) = false
      | occursNormalDecs (r, ((vis,D)::Ds)) = occursNormalDec (r, D) orelse occursNormalDecs (r, Ds)

    and occursNewDec (r, NewDecLF _) = false
      | occursNewDec (r, NewDecWorld _) = false
      
      
    fun unifyParam (D.Existential, D.Existential) = ()
      | unifyParam (D.Param, D.Param) = ()
      | unifyParam (D.PVar (r as ref (SOME P)), P2) = unifyParam (P, P2)
      | unifyParam (P2, D.PVar (r as ref (SOME P))) = unifyParam (P2, P)
      | unifyParam (D.PVar (r1 as ref NONE), P2 as D.PVar (r2 as ref NONE)) =  if (r1=r2) then () else (r1 := SOME P2)
      | unifyParam (D.PVar (r1 as ref NONE), P2 as D.Existential) = (r1 := SOME P2)
      | unifyParam (D.PVar (r1 as ref NONE), P2 as D.Param) = (r1 := SOME P2)
      | unifyParam (P2 as D.Existential, D.PVar (r1 as ref NONE)) = (r1 := SOME P2) 
      | unifyParam (P2 as D.Param, D.PVar (r1 as ref NONE)) = (r1 := SOME P2)
      | unifyParam _ = raise ApproxUnify ("IsParam Matching Failed")



    fun unifyTypes (T1, T2) = unifyTypesN(whnfT T1, whnfT T2) (* whnfT gets rid of instantiated InjVars and calls whnfF if formula *)
    and unifyTypesN (LF (_, _, A1), LF (_, _, A2)) = (Approx.match (A1, A2)
                                          handle Approx.Unify s =>
					       raise ApproxUnify ("LF Approx. Matching Failed:  " ^ s))
      | unifyTypesN (Meta (_, F1), Meta (_, F2)) = unifyFormulasN (F1, F2)
      | unifyTypesN (SmartInj (_, A1, InjVar (r1 as ref NONE), isP1), SmartInj (_, A2, I as InjVar (r2 as ref NONE), isP2)) =
                                     let
				       val _ = unifyParam(isP1, isP2)
					 
				       val _ = (Approx.match (A1, A2)
                                          handle Approx.Unify s =>
					       raise ApproxUnify ("LF Approx. Matching Failed:  " ^ s))
				     in
				       (if (r1 = r2) then () else r1 := SOME I)
				     end
				       
      | unifyTypesN (T1 as SmartInj (_, A, InjVar (r as ref NONE), isP1), T2 as LF _) = (r := SOME InjLF ; unifyTypes(T1, T2))
      | unifyTypesN (T1 as SmartInj (_, A, InjVar (r as ref NONE), isP1), T2 as Meta _) = (r := SOME InjMeta ; unifyTypes(T1, T2))
      | unifyTypesN (T1 as LF _, T2 as SmartInj (_, A, InjVar (r as ref NONE), isP1)) = (r := SOME InjLF ; unifyTypes(T1, T2))
      | unifyTypesN (T1 as Meta _, T2 as SmartInj (_, A, InjVar (r as ref NONE), isP1)) = (r := SOME InjMeta ; unifyTypes(T1, T2))

      | unifyTypesN _ = raise ApproxUnify ("Approx. Matching Failed:  Incompatible Types (LF vs Meta)")
					  
    and unifyFormulas (F1, F2) = unifyFormulasN (whnfF F1, whnfF F2)
    and unifyFormulasN (Top _, Top _) = ()
      | unifyFormulasN (All (_, D1s, F1), All (_, D2s, F2)) = (unifyNormalDecsList(D1s, D2s) ; unifyFormulas(F1, F2))
      | unifyFormulasN (Exists (_, D1, F1), Exists (_, D2, F2)) = (unifyNormalDecs(D1, D2) ; unifyFormulas(F1, F2))
      | unifyFormulasN (Nabla (_, D1, F1), Nabla (_, D2, F2)) = (unifyNewDecs(D1, D2) ; unifyFormulas(F1, F2))
      | unifyFormulasN (FormList [], FormList []) = ()
      | unifyFormulasN (FormList (F1::fs1), FormList (F2::fs2)) = (unifyFormulas(F1, F2) ; unifyFormulas(FormList fs1, FormList fs2))
      | unifyFormulasN (F1 as FVar (_, r1), F2 as FVar (_, r2)) =
                                            if (r1 = r2) then ()
					    else (r1 := SOME F2)
      | unifyFormulasN (F1 as FVar (_, r1), F2) =
					    if (occursFormula(r1, F2)) then raise ApproxUnify ("Variable Occurrence")
					    else (r1 := SOME F2)
      | unifyFormulasN (F1, F2 as FVar (_, r2)) = 
					    if (occursFormula(r2, F1)) then raise ApproxUnify ("Variable Occurrence")
					    else (r2 := SOME F1)
      | unifyFormulasN _ = raise ApproxUnify ("Approx. Matching Failed: Incompatible Formulas")
      
    and unifyNormalDecs (NormalDec (_, _, T1), NormalDec (_, _, T2)) = unifyTypes(T1, T2)

    and unifyNormalDecsList ([], []) = ()
      | unifyNormalDecsList ((D.Implicit, D1)::D1s, (D.Implicit, D2)::D2s) = unifyNormalDecsList (D1s, D2s)
      | unifyNormalDecsList ((D.Visible, D1)::D1s, (D.Visible, D2)::D2s) = (unifyNormalDecs(D1, D2) ; unifyNormalDecsList (D1s, D2s))
      | unifyNormalDecsList _ = raise ApproxUnify ("Approx. Matching Failed: Incompatible Decs")

    and unifyNewDecs (NewDecLF (_, _, A1), NewDecLF (_, _, A2)) = 
                                      (Approx.match (A1, A2)
                                          handle Approx.Unify s =>
					       raise ApproxUnify ("LF Approx. Matching Failed:  " ^ s))
      | unifyNewDecs (NewDecWorld (_, _, W1), NewDecWorld (_, _, W2)) = 
				      if WorldSubsumption.worldSubsume (W1, W2) andalso WorldSubsumption.worldSubsume (W2, W1)
					then ()
				      else raise ApproxUnify ("World Matching Failed:  Incompatible Worlds (not equal)")
      | unifyNewDecs _ = raise ApproxUnify ("Incompatible New Declarations")


    (* We now need to also convert exact types down to approximate ones     *)
    (* PRECONDITION:  Exact term does NOT contain FVars (formula variables) *)

    val rDummy = Paths.Reg(~1,~1)


    fun exact2ApxType (D.LF (isP, A)) = 
                       let
			 val (V, _) = Approx.classToApx A
		       in 
			 LF (rDummy, isP, V)
		       end
      | exact2ApxType (D.Meta (F)) = Meta (rDummy, exact2ApxFormula F)

    and exact2ApxNormalDec (D.NormalDec (sLO, T)) = NormalDec (rDummy, sLO, exact2ApxType T)

    and exact2ApxNewDec (D.NewDecLF (sO, A)) = 
                       let
			 val (V, _) = Approx.classToApx A
		       in 
			 NewDecLF (rDummy, sO, V)
		       end
      | exact2ApxNewDec (D.NewDecWorld (sO, W)) = NewDecWorld (rDummy, sO, W)
    and exact2ApxFormula F = exact2ApxFormulaN (D.whnfF F)
    and exact2ApxFormulaN (D.Top) = Top rDummy
      | exact2ApxFormulaN (D.All (Ds, F)) = 
           let
	     fun getDecs ((vis, D) :: Ds) = (vis, exact2ApxNormalDec D) :: (getDecs Ds)
	       | getDecs [] = []
	     
	     val Ds' = getDecs Ds
	   in
	     All (rDummy, Ds', exact2ApxFormula F)
	   end
      | exact2ApxFormulaN (D.Exists (D, F)) = Exists (rDummy, exact2ApxNormalDec D, exact2ApxFormula F)
      | exact2ApxFormulaN (D.Nabla (D, F)) = Nabla (rDummy, exact2ApxNewDec D, exact2ApxFormula F)
      | exact2ApxFormulaN (D.FormList Flist) = FormList (map exact2ApxFormula Flist)
      | exact2ApxFormulaN (D.FClo _) = raise Domain (* Not in whnf *)
      | exact2ApxFormulaN (D.FVar _) = raise Domain (* There should also be no FVars *)




    (* convert approx to exact type *)
    (* WARNING:  WE DO NOT KEEP TRACK OF FVARs APPROPRIATELY.
     * THIS CONVERSION IS ONLY INTENDED FOR PRINTING OUT THE RESULT
     * Similarly InjVars are just converted to "LF" as they are only being printed
     *)
    fun apx2ExactType (G, T) = apx2ExactTypeN (G, whnfT T)
    and apx2ExactTypeN (G, LF (_, isP, V)) =
             let
	       val A = Approx.apxToClass (G, V, Approx.Type, true)
	     in
	       D.LF (isP, A)
	     end
      | apx2ExactTypeN (G, Meta (_, F)) = D.Meta (apx2ExactFormulaN (G, F))
      | apx2ExactTypeN (G, SmartInj (r, A, _, isP)) = apx2ExactTypeN (G, LF(r, isP, A))

    (* WARNING:  This is only okay because it is used for printing *)
    and apx2ExactNormalDec (G, NormalDec (_, sLO, T)) = D.NormalDec (sLO, apx2ExactType (G, T))

    and apx2ExactNewDec (G, NewDecLF (_, sO, V)) = 
             let
	       val A = Approx.apxToClass (G, V, Approx.Type, true)
	     in
	       D.NewDecLF(sO, A)
	     end
      | apx2ExactNewDec (G, NewDecWorld (_, sO, W)) = D.NewDecWorld (sO, W)

    and apx2ExactFormula (G, F) = apx2ExactFormulaN (G, whnfF F)
    and apx2ExactFormulaN (G, Top _) = D.Top
      | apx2ExactFormulaN (G, All (_, Ds, F)) = 
               let
		 fun convDecs ([], G) = ([], G)
		   | convDecs ((vis,D) :: Ds, G) = 
	                let
			  val D' = apx2ExactNormalDec (G,D)
			  val (Ds', G') = convDecs (Ds, I.Decl(G, D.coerceDec (D.InstantiableDec D')))
			in
			  ((vis, D') :: Ds', G')
			end
		 val (Ds', G') = convDecs (Ds, G)
	       in
		 D.All(Ds', apx2ExactFormula (G', F))
	       end

      | apx2ExactFormulaN (G, Exists (_, D, F)) = 
               let
		 val D' = apx2ExactNormalDec (G,D)
		 val G' = I.Decl(G, D.coerceDec (D.InstantiableDec D'))
	       in
		 D.Exists(D', apx2ExactFormula (G', F))
	       end

      | apx2ExactFormulaN (G, Nabla (_, D, F)) = 
               let
		 val D' = apx2ExactNewDec (G,D)
		 val G' = I.Decl(G, D.coerceDec (D.NonInstantiableDec D'))
	       in
		 D.Nabla(D', apx2ExactFormula (G', F))
	       end

      | apx2ExactFormulaN (G, FormList Flist) = 
               let
		 val Flist' = map (fn F => apx2ExactFormula(G, F)) Flist
	       in
		 D.FormList(Flist')
	       end


      | apx2ExactFormulaN (G, FVar _) = D.newFVar(G)  (* ADAM:  Do we need to keep track of them.. 
						       * instead of just making a new one 
						       * right now this is only used to print out
						       * the approximate type.. so it doesn't matter.
						       * if we do USE this resulting conversion, then we need to keep a map
						       *)





  
  end