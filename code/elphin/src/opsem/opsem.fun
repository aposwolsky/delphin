(* The nabla programming language operational semantics *)
(* Author: Adam Poswolsky and Carsten Schuermann *)

structure NablaOpsem : NABLA_OPSEM = 
  struct
    exception NoSolution
    structure I = IntSyn
    structure N = NablaIntSyntax

    fun isFun(N.Inj _) = false
      | isFun(N.Imp _) = true
      | isFun(N.Box F) = isFun(F)
      | isFun(N.And _) = false
      | isFun _ = raise Domain (* Should not have any TVar's or TClo's *)


    fun merge(SOME ans1, SOME ans2) = SOME(N.Alt(ans1, ans2))
      | merge(SOME ans1, NONE) = SOME ans1
      | merge(NONE, SOME ans2) = SOME ans2
      | merge(NONE, NONE) = NONE

      
    fun try (I.Null, i, k) = NONE
      | try (I.Decl (G, (I.Dec (_, V))), i, k) = merge(k i V, try (G, i+1, k))
      | try _ = raise Domain


    fun eval G (E as N.Quote _) = E

      | eval G (N.Fail) = raise NoSolution

      | eval G (N.App (E1, E2)) =  
             let
	       fun evalResult(Eresult) =
		 let
		   val evalResult = eval G Eresult

		   (* ADAM: Perform some check that it can be normalized first??? *)
		   (* It MUST be normalized, or unwind will undo the bindings!!! *)
		   val evalResult' = NormalizeNabla.normalizeExp evalResult
		 in
		   evalResult'
		 end

	       fun match(G, E1, E2, fFinal) = 
		 (UnifyNabla.unifyExp(N.revCoerceCtx G, (E1, []), (E2, [])) ; fFinal())
		 handle UnifyNabla.Error _ => NONE

	       fun eval'' (E1', (N.Alt (X,Y)), E2') = merge( eval'' (E1', X, E2'),
							       eval'' (E1', Y, E2'))
		 | eval'' (E1', X, E2') = 
		    let
		      (*
		      val _ = print "Begin Match!\n"
		      val _ = print (PrintNablaInt.expToString'([N.revCoerceCtx G], E1'));
		      val _ = print "\nMatching With:\n"
		      val _ = print (PrintNablaInt.expToString'([N.revCoerceCtx G], X));
			*)
		      val _ = UnifyNabla.mark ()
		      val ans = match(G, E1', X, fn () => (SOME(evalResult(E2')) 
				                         handle NoSolution => NONE) )
		
		      val _ = UnifyNabla.unwind()
		    in
		      ans
		    end

	       fun eval' (N.Alt (E1',E2')) E2 = merge(eval' E1' E2, eval' E2' E2)
		 | eval' (N.Case (E1', _, E2')) E2 = eval'' (E1', E2, E2')
		 (* Need to finish this case *)
		 | eval' (N.EVar  (_, X as ref NONE, F)) E2 = raise Domain
		 | eval' _ _ = raise Domain


	       fun getForm (N.Alt (E1',E2')) = getForm(E1')
		 | getForm (N.Case (E1', F, E2')) = F	
		 | getForm (N.EVar (_, _, F)) = F (* Free EVar *)
		 | getForm (N.EClo (N.EVar(_, _, F), t)) = N.substF(F, hd t)
		 | getForm _ = raise Domain


	       val E1' = eval G E1

		 (* BUG?  When we evaluate E2 and it gets to a Pair (or Box)
		  * Should we evaluate the stuff under the pair?
		  * Should it depend whether we are matching against
		  * logic variable.  In that case, we just assign it?
		  * THIS IS AN ISSUE THAT MUST BE LOOKED AT!
		  *)

	       val E2' = if (isFun(getForm(E1'))) then E2 else (eval G E2)
	       val result = eval' E1' E2'
	     in
	       case result 
		 of NONE => raise NoSolution
		  | SOME V => V
	     end


      | eval G (E as N.Pair _) = E

      | eval G (N.First (E)) =
	     let
	       fun f (N.Pair (E1, E2)) = eval G E1
		 | f (N.Alt(E1, E2)) = 
		     let
		       val V1 = SOME(f E1) handle NoSolution => NONE
		       val V2 = SOME(f E2) handle NoSolution => NONE
		     in
		       (case (merge (V1, V2)) of
			  SOME V => V
			  | NONE => raise NoSolution)
		     end
		 | f _ = raise Domain (* E needs to evaluate to a pair *)
	     in
	       f (eval G E)
	     end
	     

      | eval G (N.Second (E)) =
	     let
	       fun f (N.Pair (E1, E2)) = eval G E2
		 | f (N.Alt(E1, E2)) = 
		     let
		       val V1 = SOME(f E1) handle NoSolution => NONE
		       val V2 = SOME(f E2) handle NoSolution => NONE
		     in
		       (case (merge (V1, V2)) of
			  SOME V => V
			  | NONE => raise NoSolution)
		     end
		 | f _ = raise Domain (* E needs to evaluate to a pair *)
	     in
	       f (eval G E)
	     end


      | eval G (N.EVar (_, ref (SOME E), _)) = eval G E

      | eval G (E as N.EVar (_, ref NONE, _)) = E (* raise Domain (* strictness violated! *) *)

      | eval G (N.EClo((N.EVar (_, ref (SOME E), _)),t)) = eval G (N.substL(E,t))
      | eval G (E as N.EClo((N.EVar (_, ref NONE, _)), t)) = E (* raise Domain (* uninitiated EVar *) *)


      | eval G (N.EClo (E, t)) = eval G (N.substL(E,t))

      | eval G (E' as N.Some (_, V, E)) = 
	     let
	       val X = I.newEVar (G, V)
	     in 
	       eval G (N.subst (E, N.Dot (N.Exp X, N.id)))
	     end

      | eval G (E' as N.SomeM (_, F, E)) = 
	     let
	       val X = N.newEVar(N.revCoerceCtx G,F)
	     in 
	       eval G (N.subst (E, N.Dot (N.Prg (SOME X), N.id)))
	     end


      | eval G (E' as N.New (_, V, E)) = 
	     let
	       fun f (N.Pop (E')) = eval G E'
		 | f (N.Alt(E1, E2)) = 
		     let
		       val V1 = SOME(f E1) handle NoSolution => NONE
		       val V2 = SOME(f E2) handle NoSolution => NONE
		     in
		       (case (merge (V1, V2)) of
			  SOME V => V
			  | NONE => raise NoSolution)
		     end
		 | f _ = raise Domain (* E needs to evaluate to a pair *)
	     in
	       f (eval (I.Decl (G, (I.Dec (NONE, V)))) E)
	     end


      | eval G (E' as N.Nabla (_, V, E)) = 
	       let
		 val answer = 
		   try (G, 1, fn i => fn V' => 
			   if (UnifyTrail.unifiable(G, (V, I.id), (V', I.Shift i))) 
			     then (SOME(eval G (N.subst (E, N.Dot (N.Idx i, N.id))))
			          handle NoSolution => NONE )
			     else NONE)
	       in
		 case answer 
		   of NONE => raise NoSolution
		    | SOME(V) => V
	       end


      | eval G (N.Fix (sO, F, E)) = 
		    (* Should we make fixpoints lazy as well? *)
		    let
		      val t = N.Dot (N.Prg (SOME (N.Fix (sO, F, E))), N.id)
		      val E' = N.subst (E, t)
		      (*
		      val _ = print (PrintNablaInt.expToString'([I.Null], E'))
		      val _ = print "\n"
		      *)
		    in
		      eval G E'
		    end

      | eval G (E as N.Case _) = E

      | eval G (N.Alt (E1, E2)) = 
	    let
	      val E1' = SOME(eval G E1) handle NoSolution => NONE
	      val E2' = SOME(eval G E2) handle NoSolution => NONE
	      val E3 = merge(E1', E2')
	    in
	      case E3 of
		NONE => raise NoSolution
	       | SOME V => V
	    end

      | eval (I.Decl(G, _)) (E as N.Pop _) = E
      | eval (I.Null) (N.Pop _) = raise Domain

      (* By Invariant we only evaluate closed expressions *)
      | eval G (N.Var k) = raise Domain

      | eval G _ = raise Domain

    fun eval0 E = eval (I.Null) E


end
