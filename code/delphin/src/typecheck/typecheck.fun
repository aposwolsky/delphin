(* Delphin Type Checker *)
(* Author: Adam Poswolsky *)

structure DelphinTypeCheck : DELPHIN_TYPECHECK = 
  struct
    structure I = IntSyn
    structure D = DelphinIntSyntax
    structure U = UnifyDelphinNoTrail
    exception Error of string
   

    fun lookup (I.Decl(G, D.InstantiableDec (D.NormalDec (_, T))), 1) = T
      | lookup (I.Decl(G, D.NonInstantiableDec (D.NewDecLF (_, A))), 1) = D.LF(D.Param, A)
      | lookup (I.Decl(G, D.NonInstantiableDec (D.NewDecMeta (_, F))), 1) = D.Meta(D.Param, F)
      | lookup (I.Decl(G, _), i) = if i < 1 then raise Domain else lookup(G, i-1)
      | lookup (I.Null, i) = raise Error "Attempted to access invalid index"

    fun getElement(1, x::xs) = x
      | getElement(i, x::xs) = if i< 1 then raise Domain else getElement(i-1, xs)
      | getElement _ = raise Error "Attempted to access bad index"

    (* unifies the two types *)
    fun unifyTypes(G, T1, T2) = 
         (U.unifyT(D.coerceCtx G, T1, T2) handle U.Error s => raise Error ("Delphin Typecheck Error (Unify): "^ s))

    fun inferType (G, E) = (inferTypeW (G, D.whnfE E) handle D.SubstFailed => raise Error ("Typecheck Error:  whnf Failed (IMPOSSIBLE!)"))
    and inferTypeW (G, D.Quote M) =
              let
		val A = TypeCheck.infer'(D.coerceCtx G, M)
		  handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
	      in
		D.LF(D.Existential, A)
	      end

      | inferTypeW (G, D.Var (D.Fixed i)) = D.substTypes(lookup(G, i), I.Shift i)

      | inferTypeW (G, E) = 
	      (* E is a Formula (param or existential) *)
	      let 
		val T = D.Meta(D.newPVar(), D.newFVar(D.coerceCtx G))
		val _ = checkType(G, E, T)
	      in		      
		T
	      end

    and checkCaseType (G, D.Eps(D, C), Tresult) = 
              let
		val G' = I.Decl(G, D.InstantiableDec D)
	      in
		checkCaseType(G', C, D.substTypes(Tresult, I.shift))
	      end

      | checkCaseType (G, D.NewC(D, C), Tresult) = 
              let
		val G' = I.Decl(G, D.NonInstantiableDec D)
		val newResult = D.newFVar(D.coerceCtx G')
		val nablaType = D.Meta(D.Existential, D.Nabla(D, newResult))
		val _ = unifyTypes(G, Tresult, nablaType)
	      in
		checkCaseType(G', C, D.Meta(D.Existential, newResult))
	      end
	    
      | checkCaseType (G, D.PopC(i, C), Tresult) = 
	       let
		 fun popCtx(0, G) = raise Domain
		   | popCtx(1, I.Decl(G, D.NonInstantiableDec D)) = (G, D)
		   | popCtx(1, I.Decl(G, D.InstantiableDec D)) = raise Error "Delphin Typecheck Error:  Bad Pop"
		   | popCtx(i, I.Decl(G, _)) = popCtx (i-1, G)
		   | popCtx _ = raise Domain

		 val (G', D) = popCtx(i, G)
		 val F = D.newFVar(D.coerceCtx(I.Decl(G', D.NonInstantiableDec D)))
		 val T = D.Meta(D.Existential, D.Nabla(D, F))
		 val Tshift = D.Meta(D.Existential, D.FClo(F, I.Shift (i-1)))
		 val _ = unifyTypes(G, Tshift, Tresult)
	       in
		 checkCaseType(G', C, T)
	       end


      | checkCaseType (G, D.Match(E1, E2), Tresult) =
	      let
		val argType = inferType(G, E1)
		val D = D.NormalDec(NONE, argType)
		val G' = I.Decl(G, D.InstantiableDec D)
		val funResult = D.newFVar(D.coerceCtx G')
		val t = D.Dot(D.Prg E1, D.id) (* G |- E1.id : G' *)
		val _ = unifyTypes(G, Tresult, D.Meta(D.Existential, D.All(D.Visible, D, funResult)))
	      in
		checkType(G, E2, D.Meta(D.Existential, (D.FClo(funResult, D.coerceSub t))))
	      end

      | checkCaseType (G, D.MatchAnd(visible, E1, C), Tresult) =
	      let
		val argType = inferType(G, E1)
		val D = D.NormalDec(NONE, argType)
		val G' = I.Decl(G, D.InstantiableDec D)
		val funResult = D.newFVar(D.coerceCtx G')
		val t = D.Dot(D.Prg E1, D.id) (* G |- E1.id : G' *)
		val _ = unifyTypes(G, Tresult, D.Meta(D.Existential, D.All(visible, D, funResult)))
	      in
		checkCaseType(G, C, D.Meta(D.Existential, (D.FClo(funResult, D.coerceSub t))))
	      end

    and checkType (G, E, Tresult) = checkTypeW (G, D.whnfE E, Tresult) handle D.SubstFailed => raise Error ("Typecheck Error:  whnf Failed (IMPOSSIBLE!)")
    and checkTypeW (G, D.Var (D.Fixed i), Tresult) = unifyTypes(G, D.substTypes(lookup(G, i),I.Shift i), Tresult)
      | checkTypeW (G, D.Var _, Tresult) = () (* BoundVars.. *)
      | checkTypeW (G, D.Quote M, Tresult)  =
               let
		 val A = TypeCheck.infer'(D.coerceCtx G, M)
		   handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
	       in
		 unifyTypes(G, Tresult, D.LF(D.Existential, A))
	       end

      | checkTypeW (G, D.Unit, Tresult) = unifyTypes(G, Tresult, D.Meta(D.Existential, D.Top))

      | checkTypeW (G, D.Lam (Clist, F), Tresult) = 
	       let
		 val _ = unifyTypes (G, Tresult, D.Meta(D.Existential, F))
		 val _ = map (fn C => checkCaseType(G, C, Tresult)) Clist
	       in
		 ()
	       end


      | checkTypeW (G, D.New (D, E), Tresult) =
	       let 
		 val G' = I.Decl(G,D.NonInstantiableDec D)
		 val newResult = D.newFVar(D.coerceCtx G')
		 val nablaType = D.Meta(D.Existential, D.Nabla(D, newResult))
		 val _ = unifyTypes(G, Tresult, nablaType)
	       in
		 checkType(G', E, D.Meta(D.Existential, newResult))
	       end


      | checkTypeW (G, D.App (visible, E1, E2), Tresult) = 
	       let
		 val argType = inferType(G, E2)

		 val D = D.NormalDec(NONE, argType)
		 val G' = I.Decl(G, D.InstantiableDec D)
		 val funResult = D.newFVar(D.coerceCtx G')

		 val t = D.Dot(D.Prg E2, D.id)  (* G |- E2.id  : G' *)
		 val _ = unifyTypes(G, Tresult, D.Meta(D.Existential, D.FClo(funResult, D.coerceSub t)))

		 val funF = D.All (visible, D, funResult)
		 val funType = D.Meta(D.Existential, funF)
	       in
		 checkType(G, E1, funType)
	       end


      | checkTypeW (G, D.Pair (E1, E2, F), Tresult) = 
	       let
		 val _ = unifyTypes (G, Tresult, D.Meta(D.Existential, F))

		 val firstType = inferType(G, E1)

		 val D = D.NormalDec(NONE, firstType)
		 val G' = I.Decl(G, D.InstantiableDec D)
		 val secondF = D.newFVar(D.coerceCtx G')
		 val pairF = D.Exists(D, secondF)
		 val pairType = D.Meta(D.Existential, pairF)
		 val _ = unifyTypes(G, Tresult, pairType)

		 val t = D.Dot(D.Prg E1, D.id)  (* G |- E1.id  : G' *)
	       in
		 checkType(G, E2, D.Meta(D.Existential, D.FClo(secondF, D.coerceSub t)))
	       end

      | checkTypeW (G, D.ExpList Elist, Tresult) =
	       (* All elements of Elist must have a Meta type (formula *)
	       let
		 val Flist = map (fn E => D.newFVar(D.coerceCtx G)) Elist
		 val _ = unifyTypes(G, D.Meta(D.Existential, D.FormList Flist), Tresult)
		 fun check([], []) = ()
		   | check(E::es, F::fs) = (checkType(G, E, D.Meta(D.Existential, F)) ; check(es, fs))
		   | check _ = raise Domain
	       in
		 check(Elist, Flist)
	       end

      | checkTypeW (G, D.Proj (E, i), Tresult) = 
	       let
		 val newF = D.newFVar(D.coerceCtx G)
		 val _ = checkType(G, E, D.Meta(D.Existential, newF))
	       in
		 case (D.whnfF newF)
		   of (D.FormList Flist) => 
		                         let
					   val F = getElement(i, Flist)
					 in
					   unifyTypes(G, Tresult, D.Meta(D.Existential, F))
					 end
		    | _ => raise Error "Delphin Typecheck Error: Bad Projection"
	       end


      | checkTypeW (G, D.Pop(i, E), Tresult) = 
	       let
		 fun popCtx(0, G) = raise Domain
		   | popCtx(1, I.Decl(G, D.NonInstantiableDec D)) = (G, D)
		   | popCtx(1, I.Decl(G, D.InstantiableDec D)) = raise Error "Delphin Typecheck Error:  Bad Pop"
		   | popCtx(i, I.Decl(G, _)) = popCtx (i-1, G)
		   | popCtx _ = raise Domain

		 val (G', D) = popCtx(i, G)
		 val F = D.newFVar(D.coerceCtx(I.Decl(G', D.NonInstantiableDec D)))
		 val T = D.Meta(D.Existential, D.Nabla(D, F))
		 val Tshift = D.Meta(D.Existential, D.FClo(F, I.Shift (i-1)))
		 val _ = unifyTypes(G, Tshift, Tresult)
	       in
		 checkType(G', E, T)
	       end


      | checkTypeW (G, D.Fix (D as D.NormalDec (_, T as D.Meta(D.Existential, D.FormList Flist)), D.ExpList Elist), Tresult) = 
	       let
		 val _ = unifyTypes(G, T, Tresult)
		 val G' = I.Decl(G, D.InstantiableDec D)
		 val tsShift = map (fn F => D.Meta(D.Existential,D.FClo(F, I.shift))) Flist  (* ts that make sense in G' *)

		 fun checkList ([], []) = ()
		   | checkList (T::ts, E::es) = checkType(G', E, T)
		   | checkList _ = raise Error "Improperly formed fixpoint"
	       in
		 checkList (tsShift, Elist)
	       end

      | checkTypeW (G, D.Fix (D as D.NormalDec (_, T as D.Meta(D.Existential, F1)), E1), Tresult) = 
	       let
		 val _ = unifyTypes(G, T, Tresult)
		 val G' = I.Decl(G, D.InstantiableDec D)
		 val tShift = D.Meta(D.Existential,D.FClo(F1, I.shift))
	       in
		 checkType(G', E1, tShift)
	       end

      | checkTypeW (G, D.Fix _, _) = raise Error "Improperly constructed fixpoint"


      | checkTypeW (G, D.EVar _, Tresult) = ()
      | checkTypeW (G, D.EClo _, Tresult) = raise Domain (* not in whnf *)



	
  end