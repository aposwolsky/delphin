(* Delphin Type Checker *)
(*
 * NOTE:  This DOES not check world subsumption (use world checker for that).
 *)
(* Author: Adam Poswolsky *)

structure DelphinTypeCheck : DELPHIN_TYPECHECK = 
  struct
    structure I = IntSyn
    structure D = DelphinIntSyntax
    structure U = UnifyDelphinNoTrail
    exception Error of string
   

    fun fatalError() = raise Error "Delphin TypeCheck Error:  Fatal (very ill-formed term)"

    (* lookup (G, i) = T
     * where T is the type of the variable at index i (not weakened to context G)
     *)
    fun lookup (I.Decl(G, (D.InstantiableDec (D.NormalDec (_, T)))), 1) = T
      | lookup (I.Decl(G, (D.NonInstantiableDec (D.NewDecLF (_, A)))), 1) = D.LF(D.Param, A)
      | lookup (I.Decl(G, (D.NonInstantiableDec (D.NewDecWorld (_, W)))), 1) = raise Error "Delphin TypeCheck Error:  Attempted to access invalid (world) index"
      | lookup (I.Decl(G, (D.NonInstantiableDec _)), i) = if i < 1 then fatalError() else lookup(G, i-1)
      | lookup (I.Decl(G, (D.InstantiableDec _)), i) = if i < 1 then fatalError() else lookup(G, i-1)
      | lookup (I.Null, i) = raise Error "Delphin TypeCheck Error:  Attempted to access invalid index"

    fun getElement(1, x::xs) = x
      | getElement(i, x::xs) = if i< 1 then fatalError() else getElement(i-1, xs)
      | getElement _ = raise Error "Delphin TypeCheck Error:  Attempted to access bad index"

    (* unifies the two types *)
    fun unifyTypes(G, T1, T2) = 
         (U.unifyT(I.Null, D.coerceCtx G, T1, T2) handle U.Error s => (raise Error ("Delphin Typecheck Error (Unify): "^ s)))

    fun unifyF(G, F1, F2) = 
         (U.unifyF(I.Null, D.coerceCtx G, F1, F2) handle U.Error s => (raise Error ("Delphin Typecheck Error (Unify): "^ s)))


    fun getFormula (D.Meta(F)) = D.whnfF F
      | getFormula _ = fatalError()


    fun checkCaseType (G, D.Eps(D, C, fileInfo), Fresult) = 
              let
		val G' = I.Decl(G, (D.InstantiableDec D))
	      in
		checkCaseType(G', C, D.FClo(Fresult, I.shift))
	      end

      | checkCaseType (G, D.NewC(D, C, fileInfo), Fresult) = 
              let
		val G' = I.Decl(G, D.NonInstantiableDec D)
		val newResult = D.newFVar(D.coerceCtx G')
		val _ = unifyF(G, Fresult, D.Nabla(D, newResult))
	      in
		checkCaseType(G', C, newResult)
	      end

      | checkCaseType (G, D.PopC(i, C), Fresult) = 
	       let
		 val Gpop = D.popCtx(i, G)
		 val Fpop = D.newFVar(D.coerceCtx Gpop)
		 val _ = checkCaseType(Gpop, C, Fpop)
		 val (D, F) = case (D.whnfF Fpop)
		                of D.Nabla(D, F) => (D, F)
			         | _ => fatalError()

		 val F' = D.FClo(F, I.Shift (i-1))
		 val _ = unifyF(G, F', Fresult)
	       in 
		 ()
	       end


      | checkCaseType (G, D.Match(pats, E2), F) = 
	       let		       
		 val (Ds, resF) = case (D.whnfF F)
		                     of (D.All (Ds, res)) => (Ds, res)
				       | _ => fatalError() (* bad type *)

		   (* ADAM WARNING:  We do not check that the visibility matches.. should we?? *)
		 fun checkPats([], [], t) = t
		   | checkPats((_, E1)::pats, (_, D.NormalDec(_, argT))::Ds, t (* codomain of t is G *) ) = 
		           (unifyTypes(G, inferType(G, E1), D.substTypes(argT, t)) ;
			    checkPats(pats, Ds, I.Dot (D.coerceExp E1, t)))
		   | checkPats _ = raise Error "Delphin TypeCheck Error:  Match has incorrect number of arguments"

		 val t = checkPats (pats, Ds, I.id)
		   
		 val resT' = inferType(G, E2)
		 val _ = unifyTypes(G, resT', D.Meta(D.FClo(resF, t)))
	       in
		 ()
	       end

    and inferType (G, E) = inferTypeW (G, D.whnfE E) handle D.SubstFailed => raise Error ("Delphin Typecheck Error:  whnf Failed (IMPOSSIBLE!)")
    and inferTypeW (G, D.Var (D.Fixed i, fileInfo)) = D.substTypes(lookup(G, i), I.Shift i)

      | inferTypeW (G, D.Var (D.BVarLF ((_, A, _, _), s), fileInfo)) = D.LF (D.Param, I.EClo(A, s))
      (* removed BVarMeta
      | inferTypeW (G, D.Var (D.BVarMeta ((_, F), s), fileInfo)) = D.Meta (D.Param, D.FClo(F, D.coerceSub s))
       *)
      | inferTypeW (G, D.Quote M)  =
               let
		 val A = TypeCheck.infer'(D.coerceCtx G, M)
		   handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
	       in
		 D.LF(D.Existential, A)
	       end

      | inferTypeW (G, D.Unit) = D.Meta(D.Top)

      | inferTypeW (G, D.Lam (Clist, F, fileInfo)) = 
	       let
		 val _ = map (fn C => checkCaseType(G, C, F)) Clist
	       in
		 D.Meta(F)
	       end


      | inferTypeW (G, D.New (D, E, fileInfo)) =
	       let 
		 val G' = I.Decl(G,D.NonInstantiableDec D)
		 val T = inferType(G', E)
	       in
		 D.Meta(D.Nabla(D, getFormula T))
	       end


      | inferTypeW (G, D.App (E1, args)) = 
	       let
		 val F1 = getFormula(inferType(G, E1))
		 val (Ds, fResult) = case (D.whnfF F1)
		                               of D.All(Ds, F) => (Ds, F)
					        | _ => raise Error "Delphin TypeCheck Error:  Application to non-functional type"

		 fun checkArgs ((_,fileInfo,E2)::args, (_, D.NormalDec(_, tArg))::Ds, t (* codomain of t is G *)) =
		           let
			     val T2 = inferType(G, E2)
			     val _ = unifyTypes(G, T2, D.substTypes(tArg, t))
			   in
			     checkArgs(args, Ds, I.Dot (D.coerceExp E2, t))
			   end
		   | checkArgs ([], [], t) = t
		   | checkArgs _ = raise Error "Delphin TypeCheck Error:  Incompatible number of args"

		 val t = checkArgs (args, Ds, I.id)

	       in
		 D.Meta(D.FClo(fResult, t))
	       end


      | inferTypeW (G, D.Pair (E1, E2, F)) = 
	       let
		 val firstType = inferType(G, E1)
		 val secondType = inferType(G, E2)


		 val (pairFstT, pairSndF) = case (D.whnfF F)
		                              of (D.Exists(D.NormalDec (_, T), F)) => (T, F)
					       | _ => fatalError()

		 val t = D.Dot(D.Prg E1, D.id)  (* G |- E1.id  : G' *)
		 val _ = unifyTypes(G, firstType, pairFstT)
		 val _ = unifyTypes(G, secondType, D.Meta(D.FClo(pairSndF, D.coerceSub t)))
	       in
		 D.Meta(F)
	       end

      | inferTypeW (G, D.ExpList []) = D.Meta(D.FormList [])
      | inferTypeW (G, D.ExpList (E::Elist)) =
	       (* All elements of Elist must have a Meta type (formula *)
	       let
		 val F1 = getFormula(inferType(G, E))
		 val F2 = getFormula(inferType(G, D.ExpList Elist))
	       in
		 case (D.whnfF F2)
		   of D.FormList Flist => D.Meta(D.FormList (F1::Flist))
		    | _ => raise Error "Delphin Typecheck Error: Bad List Type"
	       end

      | inferTypeW (G, D.Proj (E, i)) = 
	       let
		 val F1 = getFormula(inferType(G, E))

	       in
		 case (D.whnfF F1)
		   of (D.FormList Flist) => D.Meta(getElement(i, Flist))
		    | _ => raise Error "Delphin Typecheck Error: Bad Projection"
	       end


      | inferTypeW (G, D.Pop(i, E, fileInfo)) = 
	       let		
		 val (D, F) = case (D.whnfF (getFormula(inferType(D.popCtx(i, G), E))))
		                of D.Nabla(D, F) => (D, F)
			         | _ => fatalError()

		 val F' = D.FClo(F, I.Shift (i-1))
	       in 
		 D.Meta F'
	       end

      | inferTypeW (G, D.Fix (D, E)) = 
	       let
		 val (D.NormalDec (_, Tspecified)) = D 
		 val G' = I.Decl(G, (D.InstantiableDec D))
		 val Tactual = inferType(G', E)

		 val _ = unifyTypes(G, Tactual, D.substTypes(Tspecified, I.shift))
	       in
		 Tspecified
	       end


      | inferTypeW (G, D.EVar ((_, F), s)) = D.Meta(D.FClo(F, D.coerceSub s))
      | inferTypeW (G, D.EClo _) = fatalError() (* not in whnf *)


    fun checkType (G, E, T) = unifyTypes(G, inferType (G, E), T)


	
  end