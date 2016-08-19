(* Delphin Unification *)
(* Author: Adam Poswolsky *)

structure UnifyDelphin = 

  struct
    structure D = DelphinIntSyntax
    structure I = IntSyn
    structure U = UnifyTrail
    structure W = Whnf
    exception Error of string

    (* We need to be able to mark and unwind unifications *)
    datatype MarkType = MarkP of D.isParam option ref
                      | MarkF of D.Formula option ref
                      | MarkE of D.Exp option ref


    (* Unification of Expressions *)
    val markList : MarkType list list ref = ref ([[]]) (* list of lists *)
    fun mark() = (U.mark() ; markList := ([] :: !markList)) (* Add new list of updated refs *)

    fun addMark(X) = 
	    case (!markList)
	      of (top::rst) =>
		      let
			val top' = (X::top)
			val _ = (markList := top'::rst)
		      in
			()
		      end

	       | _ => raise Domain


    fun addMarkP(X) = addMark (MarkP X)
    fun addMarkF(X) = addMark (MarkF X) 
    fun addMarkE(X) = addMark (MarkE X)
    

    fun unwind() =
          let
	    val _ = U.unwind()
	    fun unwind'([]) = ()
	      | unwind'((MarkP x)::xs) = (x := NONE ; (unwind'(xs)))
	      | unwind'((MarkF x)::xs) = (x := NONE ; (unwind'(xs)))
	      | unwind'((MarkE x)::xs) = (x := NONE ; (unwind'(xs)))

	    val (top, rst) = case !markList
	                     of (top::rst) => (top,rst)
			      | _ => raise Domain
	    val _ = unwind'(top)
	    val _ = markList := rst
	  in
	    ()
	  end



    fun assignPVar(X, P) =
      let	     
	val _ = addMarkP(X)
      in 
	X := SOME P
      end

    fun assignFVar(X, F) =
      let	     
	val _ = addMarkF(X)
      in 
	X := SOME F
      end

    fun assignEVar(X, E) =
      let	     
	val _ = addMarkE(X)
      in 
	X := SOME E
      end

    (* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G    (* and t strsub *)
       then G' |- t : G  and G' subcontext of G
    *)
    fun strengthen (I.Shift n (* = 0 *), I.Null) = I.Null
      | strengthen (I.Dot (I.Idx k (* k = 1 *), t), I.Decl (G, D)) =
        let 
	  val t' = I.comp (t, I.invShift)
	in
	  (* G |- D dec *)
          (* G' |- t' : G *)
	  (* G' |- D[t'] dec *)
          I.Decl (strengthen (t', G), D.substDec (D, t'))
	end
      | strengthen (I.Dot (I.Undef, t), I.Decl (G, D)) = 
          strengthen (t, G)
      | strengthen (I.Shift n, G) = 
	  strengthen (I.Dot (I.Idx (n+1), I.Shift (n+1)), G)
      | strengthen _ = raise Domain (* invariant violated *)


    fun LFinvertExp (G, (U, s), ss) = (U.invertExp (D.coerceCtx G, (U, s), ss, ref NONE)) handle U.Unify s => raise Error ("Delphin Unification (Invert) Failed: " ^ s )

    (* invertFormula(G, (F, s), ss, rOccur) = F' where
     * G0 |- F wff
     * G |- s : G0
     * G1 |- ss : G
     * and G1 |- F' wff 
     * Applies F to s and ss making sure it is defined and rOccur doesn't occur
     *)
    fun invertFormula (G, (F, s), ss, rOccur) = invertFormulaN (G, (D.whnfF F, s), ss, rOccur)
    and invertFormulaN (G, (D.Top, s), ss, rOccur) = D.Top
      | invertFormulaN (G, (D.All(D, F), s), ss, rOccur) = D.All(invertNormalDec(G, (D, s), ss, rOccur),
							      invertFormula(I.Decl(G, D.InstantiableDec (D.substNormalDec(D, s))), (F, I.dot1 s), I.dot1 ss, rOccur))
      | invertFormulaN (G, (D.Exists(D, F), s), ss, rOccur) = D.Exists(invertNormalDec(G, (D, s), ss, rOccur),
							      invertFormula(I.Decl(G, D.InstantiableDec (D.substNormalDec(D, s))), (F, I.dot1 s), I.dot1 ss, rOccur))
      | invertFormulaN (G, (D.Nabla(D, F), s), ss, rOccur) = D.Nabla(invertNewDec(G, (D, s), ss, rOccur),
							      invertFormula(I.Decl(G, D.NonInstantiableDec (D.substNewDec(D, s))), (F, I.dot1 s), I.dot1 ss, rOccur))
      | invertFormulaN (G, (D.FVar ((GX, r), s0), s1), ss, rOccur) = 
          let
	    val s = I.comp(s0, s1)
	  in
	    if (rOccur = r) then raise Error "Delphin Unification (Inverting):  Variable occurrence"
	    else if W.isPatSub (s) then
	       let
		 val w = U.weakenSub (D.coerceCtx G, s, ss)
	       in
		 if W.isId w
		   then D.FVar((GX, r), I.comp(s,ss))
		 else
		   raise Error "Delphin Unification : Not Invertible"
	       end
	    else (* s not patsub *)
	      D.FVar ((GX, r), invertSub(G, s, ss, rOccur))
	  end

    and invertSub (G, s as I.Shift (n), ss, rOccur) =
        if n < I.ctxLength (G) 
	  then invertSub (G, I.Dot (I.Idx (n+1), I.Shift (n+1)), ss, rOccur)
	else I.comp (s, ss)		(* must be defined *)
      | invertSub (G, I.Dot (I.Idx (n), s'), ss, rOccur) =
	(case I.bvarSub (n, ss)
	   of I.Undef => raise Error "Delphin Unification : Not Invertible"
	    | Ft => I.Dot (Ft, invertSub (G, s', ss, rOccur)))
      | invertSub (G, I.Dot (I.Exp (U), s'), ss, rOccur) =
	  I.Dot (I.Exp (LFinvertExp (G, (U, I.id), ss)),
	       invertSub (G, s', ss, rOccur))
      | invertSub (G, I.Dot (I.Undef, s'), ss, rOccur) = 
	       I.Dot (I.Undef, invertSub (G, s', ss, rOccur))
      | invertSub _ = raise Domain


    and invertDec (G, (D.InstantiableDec D, s), ss, rOccur) = D.InstantiableDec (invertNormalDec (G, (D, s), ss, rOccur))
      | invertDec (G, (D.NonInstantiableDec D, s), ss, rOccur) = D.NonInstantiableDec (invertNewDec (G, (D, s), ss, rOccur))

    and invertNormalDec (G, (D.NormalDec (sLO, Tlist), s), ss, rOccur) = D.NormalDec (sLO, invertTypeList(G, (Tlist, s), ss, rOccur))
      
    and invertNewDec (G, (D.NewDecLF (sO, A), s), ss, rOccur) = D.NewDecLF(sO, LFinvertExp(G,(A,s),ss))
      | invertNewDec (G, (D.NewDecMeta (sO, F), s), ss, rOccur) = D.NewDecMeta(sO, invertFormula(G,(F,s),ss,rOccur))

    and invertTypeList(G, ([], s), ss, rOccur) = []
      | invertTypeList(G, (T::ts, s), ss, rOccur) = invertTypes(G,(T,s),ss,rOccur) :: invertTypeList(G,(ts,s),ss,rOccur)

    and invertTypes (G, (D.LF (isP, A), s), ss, rOccur) = D.LF(isP, LFinvertExp(G,(A,s),ss))
      | invertTypes (G, (D.Meta (isP, F), s), ss, rOccur) = D.Meta(isP, invertFormula(G,(F,s),ss,rOccur))



    (* ***************************************************************** *)
    (* ***************************************************************** *)


    fun unifyParam (D.Existential, D.Existential) = ()
      | unifyParam (D.Param, D.Param) = ()
      | unifyParam (D.PVar (r as ref (SOME P)), P2) = unifyParam (P, P2)
      | unifyParam (D.PVar (r as ref NONE), P2) = assignPVar (r, P2)
      | unifyParam (P2, D.PVar (r as ref (SOME P))) = unifyParam (P2, P)
      | unifyParam (P2, D.PVar (r as ref NONE)) = assignPVar (r, P2)
      | unifyParam _ = raise Error ("Delphin Unification Failed:  Incomaptible types (w.r.t. param status)")


    fun unifyTypes (G, D.LF (P1, A1), D.LF (P2, A2)) =
                   (unifyParam(P1, P2) ; (U.unify (D.coerceCtx G, (A1, I.id), (A2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s )))
      | unifyTypes (G, D.Meta (P1, F1), D.Meta (P2, F2)) =
		   (unifyParam(P1, P2) ; unifyFormula(G, F1, F2))
      | unifyTypes _ = raise Error ("Delphin Unification Failed:  Incompatible Types (LF vs Meta)")

    and unifyTypeList (G, [], []) = ()
      | unifyTypeList (G, T1::t1list, T2::t2list) = (unifyTypes(G, T1, T2) ; unifyTypeList(G, t1list, t2list))
      | unifyTypeList _ = raise Error "Delphin Unification Failed:  Type Lists incompatible"

    and unifyFormula (G, F1, F2) = unifyFormulaN (G, D.whnfF F1, D.whnfF F2)
      (* unifyFormulaN does not have any top-level instantiated FVars *)
    and unifyFormulaN (G, D.Top, D.Top) = ()
      | unifyFormulaN (G, D.All (D1, F1), D.All (D2, F2)) = (unifyNormalDec(G, D1,D2) ; 
							    unifyFormula(I.Decl(G, D.InstantiableDec D1), F1, F2))
      | unifyFormulaN (G, D.Exists (D1, F1), D.Exists (D2, F2)) = (unifyNormalDec(G, D1,D2) ; 
							    unifyFormula(I.Decl(G, D.InstantiableDec D1), F1, F2))
      | unifyFormulaN (G, D.Nabla (D1, F1), D.Nabla (D2, F2)) = (unifyNewDec(G, D1,D2) ; 
							    unifyFormula(I.Decl(G, D.NonInstantiableDec D1), F1, F2))

      | unifyFormulaN (G, F1 as D.FVar ((G1, r1), s1), F2 as D.FVar ((G2, r2), s2)) =
		    if (r1 = r2) then
		      if (W.isPatSub(s1) andalso W.isPatSub(s2)) then
			let
			  val s' = U.intersection(s1, s2)
			in
			  if W.isId s' then ()
			  else 
			    (* G |- s1 : GA
			     * G |- s2 : GB
			     * G |- s' : G''
			     *)
			  (* WARNING:  I am not sure if this else clause is correct.. -ABP*)
			    let val ss' = W.invert s'
			        val G1' = strengthen (ss', G1)
			    in
			      assignFVar(r1, D.newFVar(G1'))
			    end
			end
		      else raise Error "Delphin Unification Failure:  Non-pattern substitution"
		    else
		      if W.isPatSub(s1) then
			let
			  val ss = W.invert s1
			  val F2' = invertFormula(G, (F2, I.id), ss, r1)
			in
			  assignFVar(r1, F2')
			end
		      else if W.isPatSub(s2) then
			let
			  val ss = W.invert s2
			  val F1' = invertFormula(G, (F1, I.id), ss, r2)
			in
			  assignFVar(r2, F1')
			end
		      else
			raise Error "Delphin Unification Failure:  Non-pattern substitution"
			  
      | unifyFormulaN (G, D.FVar ((_, r1), s1), F2) =
		   if (W.isPatSub s1) then
		     let
		       val ss = W.invert s1
		       val F2' = invertFormula(G, (F2, I.id), ss, r1)
		     in
			 assignFVar(r1, F2')
		     end
		   else
		     raise Error "Delphin Unification Failure:  Non-pattern substitution"

      | unifyFormulaN (G, F1, D.FVar ((_, r2), s2)) =
		   if (W.isPatSub s2) then
		     let
		       val ss = W.invert s2
		       val F1' = invertFormula(G, (F1, I.id), ss, r2)
		     in
			 assignFVar(r2, F1')
		     end
		   else
		     raise Error "Delphin Unification Failure:  Non-pattern substitution"


      | unifyFormulaN _ = raise Error ("Delphin Unification Failed:  Incompatible Formulas")



    and unifyDec (G, D.InstantiableDec D1, D.InstantiableDec D2) = unifyNormalDec(G, D1, D2)
      | unifyDec (G, D.NonInstantiableDec D1, D.NonInstantiableDec D2) = unifyNewDec(G, D1, D2)
      | unifyDec _ = raise Error ("Delphin Unification Failed:  Incompatible Dec classes (LF vs Meta)")

    and unifyNormalDec (G, D.NormalDec (_, Tlist), D.NormalDec (_, Tlist2)) = unifyTypeList(G, Tlist, Tlist2)
    and unifyNewDec (G, D.NewDecLF (_, A1), D.NewDecLF(_, A2)) = 
                            (U.unify (D.coerceCtx G, (A1, I.id), (A2, I.id))
                                  handle U.Unify s => raise Error ("Delphin Unification Failed: " ^ s ))
      | unifyNewDec (G, D.NewDecMeta (_, F1), D.NewDecMeta (_, F2)) = unifyFormula(G, F1, F2)
      | unifyNewDec (G, _, _) = raise Error "Delphin Unificatin Failed:  Incompatible New Decs"

    

    fun unifyExp (G, E1, E2) = unifyExpN (G, D.whnfE E1, D.whnfE E2)
    and unifyExpList (G, [], []) = ()
      | unifyExpList (G, E1::E1list, E2::E2list) = (unifyExp(G, E1, E2) ; unifyExpList(G, E1list, E2list))
      | unifyExpList _ = raise Error "Delphin Unification Failed:  Incompatible Expression Lists"

    and unifyCase(G, D.CaseBranch (iList1, epsList1, patList1, E1), D.CaseBranch (iList2, epsList2, patList2, E2)) =
                  let
		    (* NOTE:  we assume epsList makes sense in EMPTY context *)
		    (* here we return the resulting context the patList makes sense in *)
		    fun unifyDecList (G, [], []) = G
		      | unifyDecList (G, D1::D1rst, D2::D2rst) = (unifyNormalDec(G, D1, D2) ; 
								  unifyDecList (I.Decl(G, D.InstantiableDec D1), D1rst, D2rst))
		      | unifyDecList _ = raise Error "Delphin Unification Failed:  Incompatible eps lists"

		    fun mergeContext(G, I.Null) = G
		      | mergeContext(G, I.Decl(G', D)) = I.Decl(mergeContext(G, G'), D)

		    fun addEpsToContext(G, Geps, []) = mergeContext(G, Geps)
		      | addEpsToContext(G, Geps, (i::is)) = addEpsToContext(D.popCtx(i,G), Geps, is)
		  in
		    if (iList1 = iList2) 
		      then let val Geps = unifyDecList(G, epsList1, epsList2)
			       val _ = unifyExpList(Geps, patList1, patList2)
			       val _ = unifyExp(addEpsToContext(G,Geps,iList1), E1, E2)
			   in
			     ()
			   end
		    else
		      raise Error "Delphin Unification Failed:  Incompatible pop lists in cases"
		  end


    and unifyCaseList (G, [], []) = ()
      | unifyCaseList (G, C1::C1list, C2::C2list) = (unifyCase(G, C1, C2) ; unifyCaseList (G, C1list, C2list))
      | unifyCaseList _ = raise Error "Delphin Unification Failed:  Incompatible Case Lists"

    and unifyExpN (G, D.Var i, D.Var j) = if (i=j) then () else raise Error "Delphin Unificatin Failed:  Different Variable Access"
      | unifyExpN (G, D.Unit, D.Unit) = ()
      | unifyExpN (G, D.Lam (D1, E1), D.Lam (D2,E2)) = (unifyNormalDec(G, D1, D2) ;
						       unifyExp(I.Decl(G, D.InstantiableDec D1), E1, E2))

      | unifyExpN (G, D.New (D1, E1), D.New (D2,E2)) = (unifyNewDec(G, D1, D2) ;
						       unifyExp(I.Decl(G, D.NonInstantiableDec D1), E1, E2))
      | unifyExpN (G, D.App (E1, E2), D.App (E1', E2')) = (unifyExp(G, E1, E1') ; unifyExp(G, E2, E2'))

      | unifyExpN (G, D.Pair (E1, E2), D.Pair (E1', E2')) = (unifyExp(G, E1, E1') ; unifyExp(G, E2, E2'))
      | unifyExpN (G, D.Proj (E1, i), D.Proj (E1', j)) = 
                              if (i=j) then unifyExp(G, E1, E1') else raise Error "Delphin Unificatin Failed:  Different Variable Access in Projection"

      | unifyExpN (G, D.Pop(i, E1), D.Pop(j, E2)) = if (i=j) then
				                    unifyExp (D.popCtx(i, G), E1, E2)
						    else raise Error "Delphin Unificatin Failed:  Different Variable Access in Pop"

      | unifyExpN (G, D.Fix (D1, E1list), D.Fix (D2,E2list)) = (unifyNormalDec(G, D1, D2) ;
						       unifyExpList(I.Decl(G, D.InstantiableDec D1), E1list, E2list))
      | unifyExpN (G, D.Case (E1list, C1list), D.Case (E2list, C2list)) =
						      (unifyExpList(G, E1list, E2list) ;
						       unifyCaseList(G, C1list, C2list))

(*
      | unifyExpN (G, D.EVar (G1, r1, i1, F1), D.EVar (G2, r2, i2, F2)) =
	       (* recall that i1 = shift .... id  (i1 times) *)
		    if (r1 = r2) then
		      if (i1 = i2) then ()
			else raise Error "Delphin Unification Failure:  Same EVar under incompatible subs"
		    else
		      let
			val ss = invertShift i1
		      in
			assignEVar(r1, ADAM)
		      end

      | unifyFormulaN (G, D.EVar (_, r1, i1, F1), E2) =
		   if (W.isPatSub s1) then
		     let
		       val ss = W.invert s1
		     in
		       if occursF(r1, F2) then
			 raise Error "Delphin Unification Failure:  Variable Occurrence"
		       else
			 assignFVar(r1, D.substF(F2, ss))
		     end
		   else
		     raise Error "Delphin Unification Failure:  Non-pattern substitution"

      | unifyFormulaN (G, F1, D.FVar (_, r2, s2)) =
		   if (W.isPatSub s2) then
		     let
		       val ss = W.invert s2
		     in
		       if occursF(r2, F1) then
			 raise Error "Delphin Unification Failure:  Variable Occurrence"
		       else
			 assignFVar(r2, D.substF(F1, ss))
		     end
		   else
		     raise Error "Delphin Unification Failure:  Non-pattern substitution"

*)


      | unifyExpN _ = raise Error "Delphin Unificatino Failed:  Expressions incompatible"



  end 