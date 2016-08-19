(* Nabla Type Checker *)
(* Author: Adam Poswolsky *)

structure NablaTypeCheck : NABLA_TYPECHECK = 
  struct
    structure I = IntSyn
    structure N = NablaIntSyntax
    structure U = UnifyNabla
    exception Error of string

    fun getCtxIndex (1, I.Decl(G, N.MetaDec (_, F))) = F
      | getCtxIndex (1, _) = raise Error "Unexpected object in declaration."
      | getCtxIndex (n, I.Decl(G, _)) = getCtxIndex(n-1, G)
      | getCtxIndex _ = raise Error "Cannot get the appropriate index"
	   

    fun inferType(Psi::Omega, N.Quote(e)) = 
              let
		val A = TypeCheckLF.infer'(N.coerceCtx Psi, e)
		  handle TypeCheckLF.Error s => raise Error ("Twelf TypeCheck Error: " ^ s)

(* For Type Reconstruction.. need to be terms
		val term = ReconTerm.evar ("hi", Paths.Reg(~1,~1))
		val A = (case (ReconTerm.reconWithCtx (N.coerceCtx Psi, ReconTerm.jterm term))
	          of ReconTerm.JTerm ((_, _), A, _) => A
		  | _ => raise Error ("Twelf Type Reconstruction Error"))
*)
		val ans = N.Inj(A)
		(* val ids = N.createID(Psi::Omega) *)
	      in
		ans
	      end

      | inferType(Psi::Omega, N.Fail) = N.newTVar()

      | inferType(Psi::Omega, N.App(m1,m2)) = 
              let
		val f2 = NormalizeNabla.existsNormalizeFor(inferType(Psi::Omega, m2))
		(* Must do f2 first!, or it may make f1 not "exists normalized" *)

		val f1 = NormalizeNabla.existsNormalizeFor(inferType(Psi::Omega, m1))
		val ids = N.createID(Psi::Omega)
		val ans = 
		  case f1
		    of N.TVar(X as ref NONE) => 
		      let
			val newTVar = N.newTVar()
			val _ = (X := SOME(N.Imp(f2, newTVar)))
		      in
			newTVar
		      end
				
		  | N.TClo(N.TVar(X as ref NONE),t) => 
		      let
			val newTVar = N.newTVar()
			val _ = U.unifyFor(Psi, (f1, N.id), (N.Imp(f2, newTVar), N.id))
			  handle U.Error s => raise Error s
		      in
			newTVar
		      end
		  
		  | N.Imp(f1a,f1b) => 
		      if UnifyNabla.forEqual(Psi, (f2, N.id), (f1a, N.id)) 
			 then f1b
		         else raise Error ("Incompatible Type\nExpected: " ^ 
					   PrintNablaInt.formStr(Psi,f1a) ^ "\nActual: " ^ 
					PrintNablaInt.formStr(Psi,f2))
		  | _ => raise Error ("Type Inference Failed\n Expected Arrow Type, got: " ^ 
				      PrintNablaInt.formStr(Psi,f1))
			   
	      in
		ans
	      end

      | inferType(Psi::Omega, N.Pair(e1,e2)) = 
	      let
		val ans = N.And (inferType(Psi::Omega, e1), 
				 inferType(Psi::Omega, e2) )

		val ids = N.createID(Psi::Omega)
	      in
		ans
	      end
		  

      | inferType(Psi::Omega, N.First(e)) =
	      let
		val t = NormalizeNabla.existsNormalizeFor(inferType(Psi::Omega, e))
		val ans = case t 		          
		         of N.And(t1,t2) => t1
			  | N.TVar (X as ref NONE) =>
			       let
				 val newTVar1 = N.newTVar()
				 val newTVar2 = N.newTVar()
				 val _ = (X := SOME(N.And(newTVar1, newTVar2)))
			       in
				 newTVar1
			       end
			   | N.TClo(N.TVar (X as ref NONE), t) =>
			       let
				 val newTVar1 = N.newTVar()
				 val newTVar2 = N.newTVar()
				 val _ = (X := SOME(N.And(newTVar1, newTVar2)))
			       in
				 N.substF(newTVar1, t)
			       end
			  | _ => raise Error ("Type Inference Failed\n Expected And Type, got: " ^
					      PrintNablaInt.formStr(Psi, t))
		val ids = N.createID(Psi::Omega)
	      in
		ans
	      end

      | inferType(Psi::Omega, N.Second(e)) =
	      let
		val t = NormalizeNabla.existsNormalizeFor(inferType(Psi::Omega, e))

		val ans = case t 		          
		         of N.And(t1,t2) => t2
			  | N.TVar (X as ref NONE) =>
			       let
				 val newTVar1 = N.newTVar()
				 val newTVar2 = N.newTVar()
				 val _ = (X := SOME(N.And(newTVar1, newTVar2)))
			       in
				 newTVar2
			       end
			   | N.TClo(N.TVar (X as ref NONE), t) =>
			       let
				 val newTVar1 = N.newTVar()
				 val newTVar2 = N.newTVar()
				 val _ = (X := SOME(N.And(newTVar1, newTVar2)))
			       in
				 N.substF(newTVar2, t)
			       end
			  | _ => raise Error ("Type Inference Failed\n Expected And Type, got: " ^
					      PrintNablaInt.formStr(Psi, t))

		val ids = N.createID(Psi::Omega)
	      in
		ans
	      end

      | inferType(Psi::Omega, N.FVar (_, F)) = F 

      | inferType(Psi::Omega, N.EVar (_, ref NONE, F)) = F 

      | inferType(Psi::Omega, N.EVar (_, ref (SOME E), F)) = 
	      let
		val F' = inferType(Psi::Omega, E)
		val _ = U.unifyFor(Psi, (F, N.id), (F', N.id)) handle U.Error s => raise Error s
	      in
		F'
	      end


      | inferType(Psi::Omega, N.EClo (N.EVar (_, X as ref NONE, F), t)) = N.substF(F, hd(t))
      | inferType(Psi::Omega, N.EClo (N.EVar (_, ref (SOME E), _), t)) = 
	      inferType(Psi::Omega, N.substL(E,t))

      | inferType(Psi::Omega, N.EClo (E, t)) = inferType(Psi::Omega, N.substL(E, t))

      | inferType(Psi::Omega, N.Some(_,e,m)) =
	      let
 		 val D = I.Dec (NONE, e)
		 val Psi' = I.Decl(Psi, N.LFDec D)
		 val ans = inferType(Psi'::Omega, m)
		 val ids = N.createID(Psi'::Omega)
		 val shift = case ids
		             of (x::xs) => N.comp(x, N.Shift 1) :: xs
			      | _ => raise Domain
	      in
		 ans
	      end

      | inferType(Psi::Omega, N.SomeM(_,f,m)) =
	      let
		 val Psi' = I.Decl(Psi, N.MetaDec (NONE, f))
		 val ans = inferType(Psi'::Omega, m)
		 val ids = N.createID(Psi'::Omega)
		 val shift = case ids
		             of (x::xs) => N.comp(x, N.Shift 1) :: xs
			      | _ => raise Domain
	      in
		 ans
	      end

      | inferType(Psi::Omega, N.New(_,e,m)) = 
	      let
 		 val D = I.Dec (NONE, e)
		 val Psi' = I.Decl(Psi, N.LFDec D)
		 val f' = NormalizeNabla.existsNormalizeFor(inferType(Psi'::Psi::Omega, m))
		 val ans =
		   case f'
		     of N.Box(f) => f
		      | N.TVar (X as ref NONE) =>
		          let
			    val newTVar = N.newTVar()
			    val _ = (X := SOME(N.Box(newTVar)))
			  in
			    newTVar
			  end
		      | N.TClo(N.TVar (X as ref NONE), t) =>
			  let
			    val newTVar = N.newTVar()
			    val _ = U.unifyFor(Psi', (f', N.id), (N.Box(newTVar), N.id))  handle U.Error s => raise Error s
			  in
			    newTVar
			  end

		      | _ => raise Error ("Expected Box type, got type: " ^ 
				       PrintNablaInt.formStr(Psi', f'))

		 val ids = N.createID(Psi'::Psi::Omega)
		 (* val t = N.createShifts(Psi'::Psi::Omega) *)
		 (*  Psi'::Psi::Omega  |- t : Psi::Omega *)
		   
	      in
		ans
	      end

      | inferType(Psi::Omega, N.Nabla(_,e,m)) = 
	      let
 		 val D = I.Dec (NONE, e)
		 val Psi' = I.Decl(Psi, N.LFDec D)

		 val ans = inferType(Psi'::Omega, m)
		 val ids = N.createID(Psi'::Omega)
		 val shift = case ids
		             of (x::xs) => N.comp(x, N.Shift 1) :: xs
			      | _ => raise Domain

	      in
		 ans
	      end

      | inferType(Psi::Omega, N.Fix(_,f,m)) =  
	      let
		 val Psi' = I.Decl(Psi, N.MetaDec(NONE, f))
		 val f' = inferType(Psi'::Omega, m)

		 val ids = N.createID(Psi'::Omega)
		 val shift = case ids
		             of (x::xs) => N.comp(x, N.Shift 1) :: xs
			      | _ => raise Domain
	      in
		if UnifyNabla.forEqual(Psi', (f, N.Shift 1), (f', N.id)) 
		  (* It seems to be getting an error in this unification *)
		  then (f)
		  else raise Error ("Type does not match!\nType 1 = " ^ 
				       PrintNablaInt.formStr(Psi,f) ^ "\nType 2 = " ^ 
				       PrintNablaInt.formStr(Psi',f'))


	      end


      | inferType(Psi::Omega, N.Case(m1,F,m2)) = 
	      let
		val f1 = inferType(Psi::Omega, m1)
		val f2 = inferType(Psi::Omega, m2)
		val ans = N.Imp(f1,f2)
		val ids = N.createID(Psi::Omega)
		val _ = U.unifyFor(Psi, (F, N.id), (f1, N.id)) handle U.Error s => raise Error s
	      in
		ans
	      end


      | inferType(Psi::Omega, N.Alt(m1,m2)) = 
	      let
		val f1 = inferType(Psi::Omega, m1)
		val f2 = inferType(Psi::Omega, m2)
		val ids = N.createID(Psi::Omega)
		   
		val ans =
		  if UnifyNabla.forEqual(Psi,(f1,N.id),(f2,N.id)) 
		    then f1 
		    else raise Error ("Type does not match!\nType 1 = " ^ 
				      PrintNablaInt.formStr(Psi,f1) ^ "\nType 2 = " ^ 
				      PrintNablaInt.formStr(Psi,f2))
	      in
		ans
	      end

      | inferType(Psi::Omega, N.Pop(m)) = 
	      let

		val ans = N.Box (inferType(Omega,m))

		val ids = N.createID(Psi::Omega)
		(* val t = N.createShifts(Psi::Omega) *)
		 (*  Psi::Omega  |- t : Omega *)
	      in
		ans
	      end


      | inferType(Psi::Omega, N.Var(n)) = 
	      let
		val ans = getCtxIndex(n, Psi)
		val ids = N.createID(Psi::Omega)
	      in
		ans
	      end

      | inferType([], _) = raise Error "Pop'd off too many stacks!"


  end