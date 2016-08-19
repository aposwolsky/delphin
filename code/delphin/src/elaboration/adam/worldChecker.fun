structure WorldChecker = 
  struct
    exception Error of string
    structure D = DelphinIntSyntax
    structure I = IntSyn
    structure U = UnifyDelphinNoTrail

    fun crash() = raise Domain

    fun getFormula (D.Meta(_, F)) = D.whnfF F
      | getFormula _ = crash()
 
    (* raises Error if not world correct *)
    fun checkWorld(G, currentWorld, E) = 
      let
	    (* lookup(G, k) = (name, T, listWeakened)
	     *)
	     fun lookup' (k', I.Null, _) = raise Error "Bad Variable Access in checkWorld" 
	       | lookup' (k', I.Decl(G, (D.InstantiableDec (D.NormalDec (SOME [s], T0)))), 1 ) = (SOME s, D.substTypes(T0, I.Shift k'), [])
	       | lookup' (k', I.Decl(G, (D.InstantiableDec (D.NormalDec (_, T0)))), 1 ) = (NONE, D.substTypes(T0, I.Shift k'), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecLF (name, A)))), 1) = (name, D.LF(D.Param, A), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecMeta (name, F)))), 1) = (name, D.Meta(D.Param, F), [])
	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecLF (_, A)) )), k) = 
                               let
				 val (name, T, list) = lookup'(k', G, k-1)
			       in
				 (name, T, I.EClo(A, I.Shift (k' - k + 1)) :: list)
			       end

	       | lookup' (k', I.Decl(G, (D.NonInstantiableDec (D.NewDecMeta (_, F)) )), k) = 
                               let
				 val (name, T, list) = lookup'(k', G, k-1)
			       in
				 (name, T, list) (* ABP:  WARNING... *)
			       end

	       | lookup' (k', I.Decl(G, (D.InstantiableDec _)), k) = lookup'(k', G, k-1)

	     fun lookup (G, k) = lookup' (k, G, k)


	     fun check (G,E) = checkN (G, D.whnfE E)
	     and checkN (G, D.Var (D.Fixed i, fileInfo)) = 
	                    let
			      val (name, T, listWeakened) = lookup(G, i)
			      val varString = case name 
			                      of NONE => ""
					       | SOME s => ": " ^ s
			    in
			      if WorldSubsumption.canWeakenTypeList(G, T, listWeakened) then T
			      else (
				    case fileInfo
				       of SOME(filename, r) => 
					   raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Violation:  Cannot weaken variable" ^ varString)))
				        | NONE => 
						 raise Error ("Error: World Violation:  Cannot weaken variable" ^ varString)
                                     )
			    end


	       | checkN (G, D.Var (D.BVarMeta ((_, F), s), fileInfo)) = D.Meta(D.Param, D.FClo(F, D.coerceSub s))
	       | checkN (G, D.Var (D.BVarLF ((_, A, _, _), s), fileInfo)) = D.LF(D.Param, I.EClo(A, s))
	       | checkN (G, D.Quote M) = 
				let
				  val A = TypeCheck.infer'(D.coerceCtx G, M)
				    handle TypeCheck.Error s => raise Error ("LF TypeCheck Error: " ^ s)
				in
				  D.LF(D.Existential, A)
				end

	       | checkN (G, D.Unit) = D.Meta(D.Existential, D.Top)
	       | checkN (G, D.Lam ([], F, fileInfo)) = D.Meta(D.Existential, F)
	       | checkN (G, D.Lam (C::Clist, F, fileInfo)) = (checkCase(G, C, F) ; check(G, D.Lam(Clist, F, fileInfo)))
	       | checkN (G, D.New (D, E, fileInfo)) = 
				let
				  val T = check(I.Decl(G, (D.NonInstantiableDec D)), E)
				in
				  D.Meta(D.Existential, D.Nabla(D, getFormula T))
				end

	       | checkN (G, D.App (_, E1, E2, fileInfo)) = 
				let
				  val F1 = getFormula(check(G, E1))
				  val T2 = check(G, E2)
				    
				  val (tArg, fWorld, fResult) = case F1 of
				                                D.All(_, (SOME w), D.NormalDec(_, T), F) => (T, w, F)
								| _ => crash()
				in
				  if WorldSubsumption.typesLess(T2, tArg)
				    then
				      D.Meta(D.Existential, D.FClo(fResult, D.coerceSub (D.Dot(D.Prg E2, D.id))))
				    else 
				      let
					fun debugAdam () = ()
					val _ = debugAdam()
				      in 
					case fileInfo
					  of SOME(filename, r) => 
					    raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Violation in Application")))
				            | NONE => 
					      raise Error ("Error : World Violation in Application")
				      end
				end

	       | checkN (G, D.Pair (E1, E2, F)) = 
				let
				  val firstType = check(G, E1)
				  val secondType = check(G, E2)

				  val (pairFstT, pairSndF) = case (D.whnfF F)
				                             of (D.Exists(D.NormalDec (_, T), F)) => (T, F)
							      | _ => crash()

				  val t = D.coerceSub (D.Dot(D.Prg E1, D.id))
				  val _ = U.unifyT (true, I.Null, D.coerceCtx G, firstType, pairFstT)
				    handle U.Error msg => raise Error ("Error:  Incompatible Worlds (" ^ msg ^ ")")
				  val _ = U.unifyT (true, I.Null, D.coerceCtx G, secondType, D.Meta(D.Existential, D.FClo(pairSndF, t)))
				    handle U.Error msg => raise Error ("Error:  Incompatible Worlds (" ^ msg ^ ")")
				    
				in
				  D.Meta(D.Existential, F)
				end

	       | checkN (G, D.ExpList []) = D.Meta(D.Existential, D.FormList [])
	       | checkN (G, D.ExpList (E::Elist)) = 
				let
				  val F1 = getFormula(check(G, E))
				  val F2 = getFormula(check(G, D.ExpList Elist))
				in
				  case F2 
				    of D.FormList Flist => D.Meta(D.Existential, D.FormList (F1::Flist))
				     | _ => crash()
				end

	       | checkN (G, D.Proj (E, i)) = 
				let
				  val F1 = getFormula(check(G, E))

				  fun getElement(1, x::xs) = x
				    | getElement(i, x::xs) = if i< 1 then crash() else getElement(i-1, xs)
				    | getElement _ = raise Error "Attempted to access bad index"

				in
				  case F1
				    of D.FormList Flist => D.Meta(D.Existential, getElement(i, Flist))
				     | _ => crash() 

				end
	       | checkN (G, D.Pop (i, E, fileInfo)) = 
				let

				  fun popCtx(0, G) = crash()
				    | popCtx(1, I.Decl(G, D.NonInstantiableDec D)) = (G, D)
				    | popCtx(1, I.Decl(G, D.InstantiableDec D)) = raise Error "Delphin Typecheck Error:  Bad Pop"
				    | popCtx(i, I.Decl(G, _)) = popCtx (i-1, G)
				    | popCtx _ = crash()

				  val (D, F) = case getFormula(check(D.popCtx(i, G), E))
				          of D.Nabla(D, F) => (D, F)
					   | _ => crash()

				  val Tshift = D.Meta(D.Existential, D.FClo(F, I.Shift (i-1)))

				  fun getWeakenedElements(x, I.Decl(G, D)) =
				        if (x >= i) then []
					else 
					  let
					    val list' = getWeakenedElements (x+1, G)
					  in
					    case D 
						of D.NonInstantiableDec (D.NewDecLF (_, A)) => I.EClo(A, I.Shift x) :: list'
						 | _ => list'
					  end
				    | getWeakenedElements _ = crash()

				in 
				  if WorldSubsumption.canWeakenTypeList(G, Tshift, getWeakenedElements(1, G)) then
				    Tshift
				  else
				      case fileInfo
				       of SOME(filename, r) => 
					   raise Error (Paths.wrapLoc (Paths.Loc (filename, r), ("World Violation in Pop")))
				        | NONE => 
						 raise Error ("Error: World Violation in Pop")
				end


	       | checkN (G, D.Fix (D, E)) = 
				let
				  val F = getFormula(check(I.Decl(G, (D.InstantiableDec D)), E))
				in
				  D.Meta(D.Existential, D.FClo(F, I.invShift))
				end

	       | checkN (G, D.EVar ((_, F), s)) = D.Meta(D.Existential, D.FClo(F, D.coerceSub s))
	       | checkN (G, _) = crash() (* not in whnf *)

	     and checkCase (G, D.Eps(D, C), F) = checkCase (I.Decl(G, (D.InstantiableDec D)), C, D.FClo(F, I.shift)) (* BUG *)
	       | checkCase (G, D.NewC(D, C, fileInfo), F) = 
	             let
		       val G' = I.Decl(G, D.NonInstantiableDec D)
		       val newResult = D.newFVar(D.coerceCtx G')
		       val nablaType = D.Nabla(D, newResult)
		       val _ = U.unifyF(true, I.Null, D.coerceCtx G, F, nablaType)
			 handle U.Error msg => raise Error ("Error:  Incompatible Worlds (" ^ msg ^ ")")
		     in
		       checkCase(G', C, newResult)
		     end

	       | checkCase (G, D.Match(_, E1, E2), F) = 
		     let
		       val (argT, resF) = case (D.whnfF F)
			                of (D.All (_, _, D.NormalDec(_, arg), res)) => (arg, res)
					 | _ => crash() (* bad type *)
		       val argT' = check(G, E1)
		       val _ = U.unifyT(true, I.Null, D.coerceCtx G, argT, argT')
			 handle U.Error msg => raise Error ("Error:  Incompatible Worlds (" ^ msg ^ ")")

		       val resT' = check(G, E2)
		       val t = D.coerceSub (D.Dot(D.Prg E1, D.id))
		       val _ = U.unifyT(true, I.Null, D.coerceCtx G, D.Meta(D.Existential, D.FClo(resF, t)), resT')
			 handle U.Error msg => raise Error ("Error:  Incompatible Worlds (" ^ msg ^ ")")

		     in
		       ()
		     end
	       | checkCase (G, D.MatchAnd(_,E, C), F) = 
		     let
		       val (argT, resF) = case (D.whnfF F)
			                of (D.All (_, _, D.NormalDec(_, arg), res)) => (arg, res)
					 | _ => crash() (* bad type *)
		       val argT' = check(G, E)
		       val t = D.coerceSub (D.Dot(D.Prg E, D.id))
		       val _ = U.unifyT(true, I.Null, D.coerceCtx G, argT, argT')
			 handle U.Error msg => raise Error ("Error:  Incompatible Worlds (" ^ msg ^ ")")

		       val resT' = checkCase(G, C, D.FClo(resF, t))
		     in
		       ()
		     end


      in
	(check (G, E) ; ())
      end
    
  end
