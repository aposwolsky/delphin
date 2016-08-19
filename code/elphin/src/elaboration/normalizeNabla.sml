(* Nabla Normalize *)
(* Author: Adam Poswolsky *)

structure NormalizeNabla = 

  struct
    structure N = NablaIntSyntax
    structure I = IntSyn

    (* Whnf is designed to make sure it gets rid of TClo's! and instantiated TVar's
       from top constructor *)
    fun whnfFor (N.TVar (ref (SOME F)), s) = whnfFor (F, s)
      | whnfFor (N.TClo (F,t), s) = whnfFor (F, N.comp(t, s))
      | whnfFor (E, s) = (E, s)

    fun whnfExp (N.EVar (_, ref (SOME E), _), s) = whnfExp (E, s)
      | whnfExp (N.EClo (E, t), s) = whnfExp (E, N.compL(t, s))
      | whnfExp (E, s) = (E, s)


    (* Gets rid of instantiated TVar's *)
    and existsNormalizeFor (N.Inj E) = N.Inj E
      | existsNormalizeFor (N.Imp (F1,F2)) = N.Imp (existsNormalizeFor F1, existsNormalizeFor F2)
      | existsNormalizeFor (N.Box F) = N.Box (existsNormalizeFor F)
      | existsNormalizeFor (N.And (F1, F2)) = N.And (existsNormalizeFor F1, existsNormalizeFor F2)
      | existsNormalizeFor (N.TVar (ref (SOME F))) = existsNormalizeFor (F)
      | existsNormalizeFor (X as N.TVar (ref NONE)) = X 
      | existsNormalizeFor (X as N.TClo(N.TVar (ref NONE), t)) = X
      | existsNormalizeFor (N.TClo(N.TVar (ref (SOME F)), t)) = existsNormalizeFor (N.substF(F,t))
      | existsNormalizeFor (N.TClo (F,t)) = existsNormalizeFor (N.substF(F,t))

    (* Gets rid of all TVar's *)
    fun normalizeFor (N.Inj E) = N.Inj E
      | normalizeFor (N.Imp (F1,F2)) = N.Imp (normalizeFor F1, normalizeFor F2)
      | normalizeFor (N.Box F) = N.Box (normalizeFor F)
      | normalizeFor (N.And (F1, F2)) = N.And (normalizeFor F1, normalizeFor F2)
      | normalizeFor (N.TVar (ref (SOME F))) = normalizeFor (F)
      | normalizeFor (N.TVar (ref NONE)) = raise Domain
      | normalizeFor (N.TClo (N.TVar (ref NONE), t)) = raise Domain
      | normalizeFor (N.TClo (N.TVar (ref (SOME F)), t)) = normalizeFor(N.substF(F,t))
      | normalizeFor (N.TClo (F, t)) = normalizeFor (N.substF(F,t))


    fun noFreeVars (N.Inj E) = true
      | noFreeVars (N.Imp (F1,F2)) = (noFreeVars F1) andalso (noFreeVars F2)
      | noFreeVars (N.Box F) = noFreeVars F
      | noFreeVars (N.And (F1, F2)) = (noFreeVars F1) andalso (noFreeVars F2)
      | noFreeVars (N.TVar (ref (SOME F))) = noFreeVars (F)
      | noFreeVars (N.TVar (ref NONE)) = false
      | noFreeVars (N.TClo (N.TVar (ref NONE), t)) = false
      | noFreeVars (N.TClo (N.TVar (ref (SOME F)), t)) = noFreeVars (N.substF(F,t))
      | noFreeVars (N.TClo (F, t)) = noFreeVars (N.substF(F,t))


    fun normalizeExp (N.Quote (U)) =  N.Quote (Whnf.normalize (U, I.id))
      | normalizeExp (N.Fail) = N.Fail
      | normalizeExp (N.App (E1, E2)) = N.App (normalizeExp E1,normalizeExp E2) 
      | normalizeExp (N.Pair (E1, E2)) = N.Pair (normalizeExp E1, normalizeExp E2)
      | normalizeExp (N.First (E)) = N.First (normalizeExp E)
      | normalizeExp (N.Second (E)) = N.Second (normalizeExp E)
      | normalizeExp (N.EVar (_, ref (SOME E), _)) = normalizeExp (E)
      | normalizeExp (N.FVar (s, F)) = raise Domain  (*?shouldn't occur by invariant *)
      | normalizeExp (E as N.EVar (_, ref NONE, _)) = E (* raise Domain (* uninitiated EVar *) *)
      | normalizeExp (E as N.EClo (N.EVar (_, ref NONE, _), t)) = E (* raise Domain  *)
      | normalizeExp (N.EClo (N.EVar (_, ref (SOME E), _), t)) = normalizeExp (N.substL(E, t))
      | normalizeExp (N.EClo (E, t)) = normalizeExp (N.substL(E,t))
      | normalizeExp (N.Some (sO,U, E)) = N.Some (sO,Whnf.normalize (U, I.id), normalizeExp E)
      | normalizeExp (N.SomeM (sO,F, E)) = N.SomeM (sO,normalizeFor F, normalizeExp E)
      | normalizeExp (N.New (sO,U, E)) = N.New (sO,Whnf.normalize (U, I.id), normalizeExp E)
      | normalizeExp (N.Nabla (sO,U, E)) = N.Nabla (sO,Whnf.normalize (U, I.id), normalizeExp E)
      | normalizeExp (N.Fix (sO,F,E)) = N.Fix (sO,normalizeFor F, normalizeExp E) 
                                               (* fix in dependent case 
								--cs *)
      | normalizeExp (N.Case (E1, F, E2)) = N.Case (normalizeExp E1, 
						    normalizeFor F, normalizeExp E2)
      | normalizeExp (N.Alt (E1, E2)) = N.Alt (normalizeExp E1, normalizeExp E2)
      | normalizeExp (N.Pop (E)) = N.Pop (normalizeExp E)
      | normalizeExp (E as N.Var _) = E


  end 