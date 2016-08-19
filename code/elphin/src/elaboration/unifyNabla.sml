(* Nabla Unification *)
(* Author: Adam Poswolsky *)

structure UnifyNabla = 

  struct
    structure N = NablaIntSyntax
    structure I = IntSyn
    structure U = UnifyTrail
    exception Error of string

    (* We need to be able to mark and unwind unifications *)
    datatype MarkType = MarkE of N.Exp option ref
                      | MarkF of N.Formula option ref

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

    fun addMarkE(X) = addMark (MarkE X)
    fun addMarkF(X) = addMark (MarkF X)

    fun unwind() =
          let
	    val _ = U.unwind()
	    fun unwind'([]) = ()
	      | unwind'((MarkE x)::xs) = (x := NONE ; (unwind'(xs)))
	      | unwind'((MarkF x)::xs) = (x := NONE ; (unwind'(xs)))
	    val (top, rst) = case !markList
	                     of (top::rst) => (top,rst)
			      | _ => raise Domain
	    val _ = unwind'(top)
	    val _ = markList := rst
	  in
	    ()
	  end

    fun assignEVar(X, E) =
      let	     
	val _ = addMarkE(X)
      in 
	X := SOME E
      end

    fun assignTVar(X, F) =
      let	     
	val _ = addMarkF(X)
      in 
	X := SOME F
      end

    fun LFinvertExp X = (U.invertExp X) handle U.NotInvertible => raise Error ("Unification Failed: NotInvertible" )
    fun LFpruneExp X = (U.pruneExp X) handle U.Unify s => raise Error ("Unification Failed: " ^ s )



    (* intersection (s1, s2) = s'
       s' = s1 /\ s2 (see JICSLP'96)
       
       Invariant: 
       If   G |- s1 : G'    s1 patsub
       and  G |- s2 : G'    s2 patsub
       then G |- s' : G'' for some G''  
       and  s' patsub
    *)
    fun intersection (N.Dot (N.Idx (k1), s1), N.Dot (N.Idx (k2), s2)) = 
 	  if (k1 = k2) then N.dot1 (intersection (s1, s2))
	  else N.comp (intersection (s1, s2), N.Shift(1))
      | intersection (s1 as N.Dot _, N.Shift (n2)) =
	  intersection (s1, N.Dot (N.Idx (n2+1), N.Shift (n2+1)))
      | intersection (N.Shift (n1), s2 as N.Dot _) = 
	  intersection (N.Dot (N.Idx (n1+1), N.Shift (n1+1)), s2)
      | intersection (N.Shift _ , N.Shift _) = N.id
        (* both substitutions are the same number of shifts by invariant *)
      (* all other cases impossible for pattern substitutions *)
      | intersection _ = raise Domain

    fun intersectionL ([], X) = intersectionL ([N.id], X)
      | intersectionL (X, []) = intersectionL (X, [N.id])
      | intersectionL (x::xs, y::ys) = intersection(x,y) :: intersectionL(xs,ys)




    fun pruneSub (G, s as N.Shift (n), ss, rOccur) =
        if n < I.ctxLength (G) 
	  then pruneSub (G, N.Dot (N.Idx (n+1), N.Shift (n+1)), ss, rOccur)
	else N.comp (s, ss)		(* must be defined *)
      | pruneSub (G, N.Dot (N.Idx (n), s'), ss, rOccur) =
	(case N.bvarSub (n, ss)
	   of N.Undef => raise Error "Unify Failed: NotInvertible"
	    | Ft => N.Dot (Ft, pruneSub (G, s', ss, rOccur)))
      | pruneSub (G, N.Dot (N.Prg (SOME P), s'), ss, rOccur) =
	   (* is it correct to make one element lists.. no - ABP *)
	   N.Dot (N.Prg (SOME (pruneExp (false, G, (P, [N.id]), [ss], rOccur))),
	       pruneSub (G, s', ss, rOccur))
      (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
      (* By invariant, all EVars X[s] are such that s is defined everywhere *)
      (* Pruning establishes and maintains this invariant *)
      | pruneSub _ = raise Domain (* substitution is Prg or Undef *)

    and pruneSubL (G, [], [], rOccur) = []
      | pruneSubL (G, x::xs, [], rOccur) = pruneSubL(G, x::xs, [N.id], rOccur)
      | pruneSubL (G, [], x::xs, rOccur) = pruneSubL(G, [N.id], x::xs, rOccur)
      | pruneSubL (G, x::xs, y::ys, rOccur) = pruneSub(G, x, y, rOccur) :: pruneSubL(G, xs, ys, rOccur)


    and pruneDec (b, G, (N.LFDec (I.Dec (name, V)), s), ss, rOccur) =
          if b then
	    N.LFDec (I.Dec (name, LFpruneExp(N.coerceCtx G, (V, N.coerceSub (hd s)), N.coerceSub (hd ss), ref NONE)  ))
	  else
	    N.LFDec (I.Dec (name, LFinvertExp(N.coerceCtx G, (V, N.coerceSub (hd s)), N.coerceSub (hd ss), ref NONE)  ))

      | pruneDec (b, G, (N.MetaDec (sLo, F), s), ss, rOccur) = N.MetaDec (sLo, F) (* fix in dependent case! *)
      | pruneDec _ = raise Domain

    and pruneFor (G, Fs, ss, rOccur) = pruneForW (G, NormalizeNabla.whnfFor Fs, ss, rOccur)
    and pruneForW (Psi, (N.Inj U, s), ss, rOccur) =
            (* ADAM *)
            (* N.Inj(I.EClo(I.EClo(U, N.coerceSub (s)), N.coerceSub (ss))) *)
   	     N.Inj(LFpruneExp(N.coerceCtx Psi, (U, N.coerceSub (s)), N.coerceSub (ss), ref NONE))

      | pruneForW (Psi, (N.Imp (F1, F2), s), ss, rOccur) =
	    N.Imp (pruneFor (Psi, (F1, s), ss, rOccur),
		   pruneFor (Psi, (F2, s), ss, rOccur))
      | pruneForW (Psi, (N.Box F, s), ss, rOccur) =
	    N.Box (pruneFor (Psi, (F, s), ss, rOccur))
      | pruneForW (Psi, (N.And (F1, F2), s), ss, rOccur) =
	    N.And (pruneFor (Psi, (F1, s), ss, rOccur),
		   pruneFor (Psi, (F2, s), ss, rOccur))
      | pruneForW (Psi, (X as N.TVar (r as ref NONE), s), ss, rOccur) =
	  if (rOccur = r) then raise Error "Cannot Unify: Variable occurrence"
	  else  N.TClo(X, N.comp (s,ss))
      | pruneForW _ = raise Domain
	         


    (* prune (b, G, (U, s), ss, rOccur) = U[s][ss]

       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Error if U[s][ss] does not exist, or rOccur occurs in U[s]

       * Does not do pruning if b is false
               does NOT prune EVars in U[s] according to ss; fails instead
    *)

    and pruneExp (b, G, (N.Quote U, s), ss, rOccur) =
            (* ADAM *)
             (* N.Quote(I.EClo(I.EClo(U, N.coerceSub (hd s)), N.coerceSub (hd ss))) *)
        if b then
	  N.Quote(LFpruneExp(N.coerceCtx G, (U, N.coerceSub (hd s)), N.coerceSub (hd ss), ref NONE))
	else
	  N.Quote(LFinvertExp(N.coerceCtx G, (U, N.coerceSub (hd s)), N.coerceSub (hd ss), ref NONE))
		       


      | pruneExp (b, G, (N.Fail, s), ss, rOccur) =
	    N.Fail
      | pruneExp (b, G, (N.App (E1, E2), s), ss, rOccur) =
	    N.App(pruneExp (b, G, (E1, s), ss, rOccur),
		  pruneExp (b, G, (E2, s), ss, rOccur))
      | pruneExp (b, G, (N.Pair (E1, E2), s), ss, rOccur) =
	    N.Pair(pruneExp (b, G, (E1, s), ss, rOccur),
		  pruneExp (b, G, (E2, s), ss, rOccur))

      | pruneExp (b, G, (N.First E1, s), ss, rOccur) =
	    N.First(pruneExp (b, G, (E1, s), ss, rOccur))
      | pruneExp (b, G, (N.Second E1, s), ss, rOccur) =
	    N.Second(pruneExp (b, G, (E1, s), ss, rOccur))


      | pruneExp (b, G, (X as N.EVar (_, ref (SOME E), _), s), ss, rOccur) =
	    pruneExp (b, G, (E, s), ss, rOccur)

      (* r is ref NONE ... *)
      | pruneExp (false, G, (X as N.EVar (GX, r, _), s), ss, rOccur) =
	  if (rOccur = r) then raise Error "Unify Failed: NotInvertible"
	  else if N.isPatSubL (s) then
	       let
		 val w = N.weakenSubL (G, s, ss)
	       in
		 if N.isIdL w
		   then N.EClo (X, N.compL (s, ss))
		 else raise Error "Unify Failed: NotInvertible"
	       end
	       else (* s not patsub *)
		 (* pruneExp may raise NotInvertible *)
		 N.EClo (X, pruneSubL (G, s, ss, rOccur))

      (* r is ref NONE ... *)
      | pruneExp (true, G, (X as N.EVar (GX, r, F), s), ss, rOccur) =
	  (* this will be a mess for dependently-typed case *)
	  if (rOccur = r) then raise Error "Cannot Unify: Variable occurrence"
	  else if N.isPatSubL (s) then
	       let
		 val w = N.weakenSubL (G, s, ss)
	       in
		 if N.isIdL w
		   then N.EClo (X, N.compL (s, ss))
		 else
		  
		   raise Error "I didn't implement this case yet!"

(*
		     (* This is going to be complicated! *)
		     
		   let
		     val wi = N.invertSubL w
		     val F' = pruneFor (GX, (F, N.id), hd(wi), ref NONE) (* need to check for rOccur as an expression occurs *)
		     val GY = GX (* this doesn't work! pruneCtxL (wi, GX, rOccur) *)
		     val Y = N.newEVar (GY, F')
		     val Yw = N.EClo (Y, w)
		     val _ = assignEVar (r, Yw)
		   in
		     N.EClo (Yw, N.compL (s, ss))
		   end
*)		    

	       end
	       else (* s not patsub *)
                 (
		   N.EClo (X, pruneSubL (G, s, ss, rOccur))
		 )


      | pruneExp (b, G, (N.EClo(X as N.EVar _, t1'), s), ss, rOccur) =
		 pruneExp (b, G, (X, N.compL(t1', s)), ss, rOccur)

      | pruneExp (b, G, (N.EClo (E, sL), s), ss, rOccur) =
		 pruneExp (b, G, (N.substL(E, sL), s), ss, rOccur)


      | pruneExp (b, G, (N.Some (sO, U, E), s), ss, rOccur) = 
            let
	      val dec = N.LFDec (I.Dec (NONE, U))
	      val invDec = pruneDec(b, G, (dec, s), ss, rOccur)
	      val G' = I.Decl (G, N.decSub(dec, s))
	      val U' = case invDec
		       of (N.LFDec (I.Dec (_, U'))) => U'
			| _ => raise Domain
	    in
	      N.Some (sO, U',
		      pruneExp(b, G', (E, (N.dot1 (hd s))::(tl s)), (N.dot1 (hd ss)) :: (tl ss), rOccur))
	    end

      | pruneExp (b, G, (N.SomeM (sO, F, E), s), ss, rOccur) = 
            let
	      fun conv NONE = NONE
		| conv (SOME s) = SOME ([s])

	      fun revConv NONE = NONE
		| revConv (SOME [s]) = SOME s
		| revConv _ = raise Domain

	      val dec = N.MetaDec (conv sO, F)
	      val invDec = pruneDec(b, G, (dec, s), ss, rOccur)
	      val G' = I.Decl (G, N.decSub(dec, s))
	      val (sOL', F') = case invDec
		               of (N.MetaDec (sOL', F')) => (sOL', F')
				| _ => raise Domain
	      val sO' = revConv sOL'
	    in
	      N.SomeM (sO', F', 
		      pruneExp(b, G', (E, (N.dot1 (hd s))::(tl s)), (N.dot1 (hd ss)) :: (tl ss), rOccur))
	    end

      | pruneExp (b, G, (N.New (sO, U, E), s), ss, rOccur) = 
            let
	      val dec = N.LFDec (I.Dec (NONE, U))
	      val invDec = pruneDec(b, G, (dec, s), ss, rOccur)
	      val G' = I.Decl (G, N.decSub(dec, s))
	      val U' = case invDec of
		           (N.LFDec (I.Dec (_, U'))) => U'
			 | _ => raise Domain
	    in
	      N.New (sO, U',
		      pruneExp(b, G', (E, (N.dot1 (hd s))::s), (N.dot1 (hd ss)) :: ss, rOccur))
	    end

      | pruneExp (b, G, (N.Nabla (sO, U, E), s), ss, rOccur) = 
            let
	      val dec = N.LFDec (I.Dec (NONE, U))
	      val invDec = pruneDec(b, G, (dec, s), ss, rOccur)
	      val G' = I.Decl (G, N.decSub(dec, s))
	      val U' = case invDec 
		       of (N.LFDec (I.Dec (_, U'))) => U'
			| _ => raise Domain
	    in
	      N.Nabla (sO, U',
		      pruneExp(b, G', (E, (N.dot1 (hd s))::(tl s)), (N.dot1 (hd ss)) :: (tl ss), rOccur))
	    end


      | pruneExp (b, G, (N.Fix (sO, F, E), s), ss, rOccur) = 
            let
	      fun conv NONE = NONE
		| conv (SOME s) = SOME ([s])

	      fun revConv NONE = NONE
		| revConv (SOME [s]) = SOME s
		| revConv _ = raise Domain

	      val dec = N.MetaDec (conv sO, F)
	      val invDec = pruneDec(b, G, (dec, s), ss, rOccur)
	      val G' = I.Decl (G, N.decSub(dec, s))
	      val (sOL', F') = case invDec
		                 of (N.MetaDec (sOL', F')) => (sOL', F')
				  | _ => raise Domain
	      val sO' = revConv sOL'
	    in
	      N.Fix (sO', F', 
		      pruneExp(b, G', (E, (N.dot1 (hd s))::(tl s)), (N.dot1 (hd ss)) :: (tl ss), rOccur))
	    end


      | pruneExp (b, G, (N.Case (E1, F, E2), s), ss, rOccur) = 
	    (* must fix for dependent case *)
	    N.Case(pruneExp (b, G, (E1, s), ss, rOccur), F,
		  pruneExp (b, G, (E2, s), ss, rOccur))


      | pruneExp (b, G, (N.Alt (E1, E2), s), ss, rOccur) = 
	    N.Alt(pruneExp (b, G, (E1, s), ss, rOccur),
		  pruneExp (b, G, (E2, s), ss, rOccur))


      | pruneExp (b, G, (N.Pop E, _::sl), _::ssl, rOccur) = 
	    N.Pop(pruneExp (b, G, (E, sl), ssl, rOccur))

      | pruneExp (b, G, (N.Pop _, _), _, _) = raise Domain (* Pop'd off too much *)

      | pruneExp (b, G, (N.Var n, s), ss, rOccur) = 
                                (case N.varSub (n, (hd s))
				   of (N.Prg (SOME E)) => (* pruneExp (b, G, (E, N.id), ss, rOccur) *)
				                        N.substL(E, ss)
				 | (N.Idx i) => 
				     (* 
				     pruneExp(b, G, (N.Var (i), N.id), ss, rOccur)
				     *)
				     N.substL(N.Var i, ss)

				   (* Looked up no solution, undefined value (or LF Exp) in context *)
				 | _ => raise Domain)
      | pruneExp _ = raise Domain

(*
    and pruneCtx (N.Shift n, I.Null, rOccur) = I.Null
      | pruneCtx (N.Dot (N.Idx k, t), I.Decl (G, D), rOccur) =
        let 
	  val t' = N.comp (t, N.invShift)
	  val D' = pruneDec (G, (D, [N.id]), [t'], rOccur)
	in
          I.Decl (pruneCtx (t', G, rOccur), D')
	end
      | pruneCtx (N.Dot (N.Undef, t), I.Decl (G, d), rOccur) = 
          pruneCtx (t, G, rOccur)
      | pruneCtx (N.Shift n, G, rOccur) = 
	  pruneCtx (N.Dot (N.Idx (n+1), N.Shift (n+1)), G, rOccur)
      (* The substitution can't be of any other form??? *)

   (* what do I do here!! *)
    and pruneCtxL (t::ts, G, rOccur) = pruneCtx(t,G,rOccur)
*)

    (* ******************************************** *)
    (* TVar *)
    (* ******************************************** *)

    (* dead code 
    fun occursTVarExp (X, N.Quote _) = false
      | occursTVarExp (X, N.Fail) = false
      | occursTVarExp (X, N.App(E1, E2)) = occursTVarExp(X, E1) orelse
                                              occursTVarExp(X, E2) 
      | occursTVarExp (X, N.Pair(E1, E2)) = occursTVarExp(X, E1) orelse
                                               occursTVarExp(X, E2) 
      | occursTVarExp (X, N.First(E)) = occursTVarExp(X, E) 
      | occursTVarExp (X, N.Second(E)) = occursTVarExp(X, E) 
      | occursTVarExp (X, N.EVar(_, ref (SOME E), F)) = occursTVarExp(X, E) orelse
					             occursTVarFor(X, F)
      | occursTVarExp (X, N.EVar(_, ref NONE, F)) = occursTVarFor(X, F)
						     
      | occursTVarExp (X, N.EClo(E, tL)) = occursTVarExp(X, E) orelse
				          (foldl (fn (t, b) => b orelse occursTVarSub(X,t))
					         false tL)
      | occursTVarExp (X, N.Some(_, _, E)) = occursTVarExp(X, E) 
      | occursTVarExp (X, N.SomeM(_, F1, E)) = occursTVarFor(X, F1) orelse 
					     occursTVarExp(X, E)
      | occursTVarExp (X, N.New(_, _, E))  = occursTVarExp(X, E)
      | occursTVarExp (X, N.Nabla(_, _, E)) = occursTVarExp(X, E)
      | occursTVarExp (X, N.Fix(_, F, E)) = occursTVarFor(X, F) orelse occursTVarExp(X, E)
      | occursTVarExp (X, N.Case(E1, F, E2)) = occursTVarExp(X, E1) orelse
                                               occursTVarFor(X, F) orelse
					       occursTVarExp(X, E2)
					       
      | occursTVarExp (X, N.Alt (E1, E2)) = occursTVarExp(X, E1) orelse
                                               occursTVarExp(X, E2) 
      | occursTVarExp (X, N.Pop (E)) = occursTVarExp(X, E) 
      | occursTVarExp (X, N.Var _) = false


    and occursTVarSub(X, N.Shift _) = false
      | occursTVarSub(X, N.Dot(N.Prg (SOME E), t)) = occursTVarExp(X,E) orelse
                                              occursTVarSub(X, t)
      | occursTVarSub(X, N.Dot(_, t)) = occursTVarSub(X, t)


    and occursTVarFor(X, N.Inj _) = false
      | occursTVarFor(X, N.Imp(F1, F2)) = occursTVarFor(X, F1) orelse 
                                          occursTVarFor(X, F2)
      | occursTVarFor(X, N.Box(F)) = occursTVarFor(X, F)
      | occursTVarFor(X, N.And(F1, F2)) = occursTVarFor(X, F1) orelse
					  occursTVarFor(X, F2)
      | occursTVarFor(X, N.TVar (Y as ref NONE)) = (X = Y)
      | occursTVarFor(X, N.TVar (Y as ref (SOME F))) = occursTVarFor(X, F)
      | occursTVarFor(X, N.TClo (F, t)) = occursTVarFor(X, F) orelse
					  occursTVarSub(X, t)
					  
    (* ******************************************** *)
    (* EVar *)
    (* ******************************************** *)

    fun occursEVarExp (X, N.Quote _) = false
      | occursEVarExp (X, N.Fail) = false
      | occursEVarExp (X, N.App(E1, E2)) = occursEVarExp(X, E1) orelse
                                              occursEVarExp(X, E2)
      | occursEVarExp (X, N.Pair(E1, E2)) = occursEVarExp(X, E1) orelse
                                               occursEVarExp(X, E2)
      | occursEVarExp (X, N.First(E)) = occursEVarExp(X, E) 
      | occursEVarExp (X, N.Second(E)) = occursEVarExp(X, E)
      | occursEVarExp (X, N.EVar(_, Y as ref (SOME E), _)) = occursEVarExp(X, E)
      | occursEVarExp (X, N.EVar(_, Y as ref NONE, _)) = (X = Y)
      | occursEVarExp (X, N.EClo(E, tL)) = occursEVarExp(X, E) orelse
				          (foldl (fn (t, b) => b orelse occursEVarSub(X,t))
					         false tL)
      | occursEVarExp (X, N.Some(_, _, E)) = occursEVarExp(X, E)
      | occursEVarExp (X, N.SomeM(_, _, E)) = occursEVarExp(X, E)
      | occursEVarExp (X, N.New(_, _, E))  = occursEVarExp(X, E)
      | occursEVarExp (X, N.Nabla(_, _, E)) = occursEVarExp(X, E)
      | occursEVarExp (X, N.Fix(_, _, E)) = occursEVarExp(X, E)
      | occursEVarExp (X, N.Case(E1, _, E2)) = occursEVarExp(X, E1) orelse
                                               occursEVarExp(X, E2)
      | occursEVarExp (X, N.Alt (E1, E2)) = occursEVarExp(X, E1) orelse
                                               occursEVarExp(X, E2)
      | occursEVarExp (X, N.Pop (E)) = occursEVarExp(X, E)
      | occursEVarExp (X, N.Var _) = false


    and occursEVarSub (X, N.Shift _) = false
      | occursEVarSub (X, N.Dot(N.Prg (SOME E), t)) = occursEVarExp(X, E) orelse occursEVarSub(X, t)
      | occursEVarSub (X, N.Dot(_, t)) = occursEVarSub(X, t)


    and occursEVarSubL (X, []) = false
      | occursEVarSubL (X, t::ts) = occursEVarSub(X, t) orelse occursEVarSubL(X, ts)

    *)

    (* ***************************************************************** *)
    (* ***************************************************************** *)

    (* unifyFor (Psi, (F1, t1), (F2, t2)) 
     * means we are trying to unify
     * Psi |- F1[t1]
     * with
     * Psi |- F2[t2]
     * 
     * Requirements:  if there are TVar's, then 
     *                t1 and t2 should be invertible to guarantee this works.
     *                The substitutions bound to the TVar should also be invertible.
     *)

    fun unifyFor (Psi, Fs1, Fs2) = unifyForW (Psi, NormalizeNabla.whnfFor Fs1, 
					      NormalizeNabla.whnfFor Fs2)
    and unifyForW (Psi, (F1 as N.TVar (X as ref NONE), t1), (F2 as N.TVar (X2 as ref NONE), t2)) =
	  if X = X2 then 
	    if N.isPatSub(t1) then 
	      if N.isPatSub(t2) then
		let
		  val s' = intersection (t1,t2)
		in
		  (* without the next optimization, bugs/hangs/sources.cfg
		     would gets into an apparent infinite loop
		     Fri Sep  5 20:23:27 2003 -fp 
                     Let's see if this is still true! -abp
		  *)
		  if N.isId s' (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
		    then () (* X[s] = X[s] *)
		  else assignTVar(X, N.TClo(N.newTVar(), s'))
		end
	      else raise Error "Cannot Unify Formulas (not without constraints)"
	    else raise Error "Cannot Unify Formulas (not without constraints)"
	  else
	    if N.isPatSub(t1) then 
	      let
		val t1Inv = N.invertSub t1
		val U2' = pruneFor (Psi, (F2, t2), t1Inv, X)
	      in
		assignTVar(X, U2')
	      end
	    else if N.isPatSub(t2) then 
	      let
		val t2Inv = N.invertSub t2
		val U1' = pruneFor (Psi, (F1, t1), t2Inv, X2)
	      in
		assignTVar(X, U1')

	      end
	    else
	      raise Error "Cannot unify (perhaps add constraints)"

    |  unifyForW (Psi, (N.TVar (X as ref NONE), t1), (F, t2)) =
	(******* OLD CODE ****
	     (*
	      * Here we want to assign X such that
	      * X[t1]  == F[t2]
	      * 
	      * So, X == F[t2][t1Inv]
	      *)
	     val t1Inv = N.invertSub(t1)
	     val t' = N.comp(t2, t1Inv)
	   in
	     (X := SOME (N.substF(F, t'))) 
	   end

	 **** END OLD CODE ***)
           if N.isPatSub(t1) then
	     let val t1Inv = N.invertSub t1
	         val F' = pruneFor (Psi, (F, t2), t1Inv, X)
	     in
	         assignTVar(X, F')
	     end
	   else
	     raise Error "Cannot unify (perhaps add constraints)"


      | unifyForW (Psi, (F, t2), (N.TVar (X as ref NONE), t1)) =
           if N.isPatSub(t1) then
	     let val t1Inv = N.invertSub t1
	         val F' = pruneFor (Psi, (F, t2), t1Inv, X) 
	     in
	         assignTVar(X, F')
	     end
	   else
	     raise Error "Cannot unify (perhaps add constraints)"


      | unifyForW (Psi, (N.Inj E1, t1), (N.Inj E2, t2)) = 
	   (U.unify (N.coerceCtx Psi, (E1, N.coerceSub(t1)), (E2, N.coerceSub(t2)))
                                  handle U.Unify s => raise Error ("Unification Failed: " ^ s ))

      | unifyForW (Psi, (N.Imp (F1, F2), t1), (N.Imp (F1', F2'), t2)) = 
	   (unifyFor(Psi, (F1,t1), (F1',t2)) ; 
	    unifyFor(Psi, (F2,t1), (F2',t2)))


      | unifyForW (Psi, (N.Box F1, t1), (N.Box F2, t2)) = (unifyFor (Psi, (F1,t1), (F2,t2)) )

      | unifyForW (Psi, (N.And (F1, F2), t1), (N.And (F1', F2'), t2)) = 
	   (unifyFor(Psi, (F1,t1), (F1',t2)) ; 
	    unifyFor(Psi, (F2,t1), (F2',t2)))

      | unifyForW (Psi, _, _) = raise Error "Unification Failed:  Formulas do not match"

    fun forEqual (Psi, (F1,t1), (F2,t2)) = (unifyFor (Psi, (F1, t1), (F2, t2)) ; true) handle Error s => false


    (* ***************************************************************** *)
    (* ***************************************************************** *)
  


    fun unifyExp (G, Es1, Es2) = unifyExpW (G, NormalizeNabla.whnfExp Es1,
					    NormalizeNabla.whnfExp Es2)

(*
    fun unifyExp (G, Es1, Es2) = 
      let fun conv (E, t) = "(" ^ PrintNablaInt.expToString'([G], E) ^ ", " 
	                    ^ PrintNablaInt.subListToString'(t) ^ ")" 
	           
	  val Es1' = NormalizeNabla.whnfExp Es1
	  val Es2' = NormalizeNabla.whnfExp Es2
	  val _ = print "Begin Match!\n"
	  val _ = print (conv Es1)
	  val _ = print "\nMatching With:\n"
	  val _ = print (conv Es2)
	  val _ = print "\nTranslates into:\n"
	  val _ = print "Begin Match!\n"
	  val _ = print (conv Es1')
	  val _ = print "\nMatching With:\n"
	  val _ = print (conv Es2')

      in unifyExpW(G, Es1', Es2')
      end
*)

    and unifyExpW (G, (E1, []), Es2) = unifyExpW (G, (E1, [N.id]), Es2)
      | unifyExpW (G, Es1, (E2, [])) = unifyExpW (G, Es1, (E2, [N.id]))
      | unifyExpW (G, (E1 as N.EVar (G1, X as ref NONE, F), t1), (E2 as N.EVar (G2, X2 as ref NONE, F2), t2)) =
	  if X = X2 then 
	    if N.isPatSubL(t1) then 
	      if N.isPatSubL(t2) then
		let
		  val s' = intersectionL (t1,t2)
		in
		  (* without the next optimization, bugs/hangs/sources.cfg
		     would gets into an apparent infinite loop
		     Fri Sep  5 20:23:27 2003 -fp 
                     Let's see if this is still true! -abp
		  *)
		  if N.isIdL s' (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
		    then () (* X[s] = X[s] *)
		  else
		    let val ss' = N.invertSubL(s')
		        val F' = N.TClo(F, hd(ss'))
			val G1' = N.strengthen (hd(ss'), G1)
		    in
		      (*
		      (assignEVar(X, (N.EClo(N.newEVar(G, F), s'))))
		       *)
		      assignEVar(X, (N.EClo(N.newEVar(G1', F'), s')))
		    end
		end
	      else raise Error "Cannot Unify Expressions (not without constraints)"
	    else raise Error "Cannot Unify Expressions (not without constraints)"
	  else
	    if N.isPatSubL(t1) then 
	      let
		val t1Inv = N.invertSubL t1
		val E2' = pruneExp (true, G, (E2, t2), t1Inv, X)
	      in
		assignEVar(X, E2')
	      end

	    else if N.isPatSubL(t2) then 
	      let
		val t2Inv = N.invertSubL t2
		val E1' = pruneExp (true, G, (E1, t1), t2Inv, X2)
	      in
		assignEVar(X2, E1')
	      end
	    else
	      raise Error "Cannot unify (perhaps add constraints)"


      | unifyExpW (G, (N.EVar (_, X as ref NONE, F1), t1), (E, t2)) =
	   (* -- OLD CODE *****
           let
	     (* Is it safe to assume that typechecker makes sure it matches? -- I think YES *)
	     (*
	      * X[t1] == E[t2]
	      * So, X == E[t2][t1Inv]
	      *)
	     val t1Inv = N.invertSubL(t1)
	     val t' = N.compL(t2, t1Inv)
	     val _ = addMark(X)
	   in
	     (X := SOME (N.substL(E, t')))
	   end
	  **** END OF OLD CODE ***)

           if N.isPatSubL(t1) then
	     let val t1Inv = N.invertSubL t1
	         val E' = pruneExp (true, G, (E, t2), t1Inv, X)
	     in
	         assignEVar(X, E')
	     end
	   else
	     raise Error "Cannot unify (perhaps add constraints)"


      | unifyExpW (G, (E, t2), (N.EVar (_, X as ref NONE, F1), t1)) =

           if N.isPatSubL(t1) then
	     let val t1Inv = N.invertSubL t1
	         val E' = pruneExp (true, G, (E, t2), t1Inv, X)
	     in
	         assignEVar(X, E')
	     end
	   else
	     raise Error "Cannot unify (perhaps add constraints)"

      | unifyExpW (G, (N.FVar (s1, _), t1), (N.FVar (s2, _), t2)) =
	       if (s1 = s2) then ()
		 else raise Error ("FVar's do not match")


      | unifyExpW (G, (N.Quote(U1), t1), (N.Quote(U2), t2)) = 
           (U.unify(N.coerceCtx G, (U1, N.coerceSub (hd t1)), (U2, N.coerceSub (hd t2)))
	   handle U.Unify s => raise Error ("LF Unify: " ^ s))

      | unifyExpW (G, (N.Fail, _), (N.Fail, _)) = ()

      | unifyExpW (G, (N.App(E1, E2), t1), (N.App(E1', E2'), t2)) =
	   (unifyExp(G, (E1, t1), (E1', t2)) ; unifyExp(G, (E2, t1), (E2', t2)))

      | unifyExpW (G, (N.Pair(E1, E2), t1), (N.Pair(E1', E2'), t2)) =
	   (unifyExp(G, (E1, t1), (E1', t2)) ; unifyExp(G, (E2, t1), (E2', t2)))

      | unifyExpW (G, (N.First (E1), t1), (N.First (E2), t2)) =
	   unifyExp (G, (E1, t1), (E2, t2))

      | unifyExpW (G, (N.Second (E1), t1), (N.Second (E2), t2)) =
	   unifyExp (G, (E1, t1), (E2, t2))

      | unifyExpW (G, (N.Some(_,U1, E1), t1::ts1), (N.Some(_,U2, E2), t2::ts2)) =
           ((U.unify(N.coerceCtx G, (U1, N.coerceSub t1), (U2, N.coerceSub t2))
	   handle U.Unify s => raise Error ("LF Unify: " ^ s));
	    unifyExp (G, (E1, ((N.dot1 t1)::ts1)), (E2, (N.dot1 t2)::ts2)))

      | unifyExpW (G, (N.SomeM(_,F1, E1), t1::ts1), (N.SomeM(_,F2, E2), t2::ts2)) =
	   (* Formula's are all closed (substituted in) *)
	   (unifyFor(I.Null, (F1, t1), (F2, t2)) ;
	    unifyExp(G, (E1, (N.dot1 t1)::ts1), (E2, (N.dot1 t2)::ts2)))

      | unifyExpW (G, (N.New(_,U1, E1), t1::ts1), (N.New(_,U2, E2), t2::ts2)) =
           ((U.unify(N.coerceCtx G, (U1, N.coerceSub t1), (U2, N.coerceSub t2))
	   handle U.Unify s => raise Error ("LF Unify: " ^ s));
	    unifyExp (I.Decl(G, N.LFDec(I.Dec (NONE, U1))), (E1, (N.dot1 t1)::t1::ts1), (E2, (N.dot1 t2)::t2::ts2)))

      | unifyExpW (G, (N.Nabla(_,U1, E1), t1::ts1), (N.Nabla(_,U2, E2), t2::ts2)) =
           ((U.unify(N.coerceCtx G, (U1, N.coerceSub t1), (U2, N.coerceSub t2))
	   handle U.Unify s => raise Error ("LF Unify: " ^ s));
	    unifyExp (G, (E1, (N.dot1 t1)::ts1), (E2, (N.dot1 t2)::ts2)))

      | unifyExpW (G, (N.Fix(_,F1, E1), t1::ts1), (N.Fix(_,F2, E2), t2::ts2)) =
	   (* Formula's are all closed (substituted in) *)
	   (unifyFor(I.Null, (F1, t1), (F2, t2)) ;
	    unifyExp(G, (E1, (N.dot1 t1)::ts1), (E2, (N.dot1 t2)::ts2)))

      | unifyExpW (G, (N.Case(E1, _, E2), t1), (N.Case(E1', _, E2'), t2)) = 
	   (unifyExp(G, (E1, t1), (E1', t2)) ; unifyExp(G, (E2, t1), (E2', t2)))

      | unifyExpW (G, (N.Alt(E1, E2), t1), (N.Alt(E1', E2'), t2)) = 
	   (unifyExp(G, (E1, t1), (E1', t2)) ; unifyExp(G, (E2, t1), (E2', t2)))

      | unifyExpW (I.Decl(G,_), (N.Pop (E1), t1::ts1), (N.Pop (E2), t2::ts2)) =
	   unifyExp (G, (E1, ts1), (E2, ts2))

      | unifyExpW (G, (N.Var (i1), t1::ts1), (N.Var (i2), t2::ts2)) =
	   (case (N.varSub(i1,t1), N.varSub(i2,t2))
	     of (N.Idx x1, N.Idx x2) => if (x1=x2) then ()
	                            else raise Error "Unification Failed:  Idx's don't match."
	      | (N.Prg (SOME E1), N.Prg (SOME E2)) => unifyExp (G, (E1, []), (E2, []))
              | (N.Prg NONE, N.Prg NONE) => ()	 
	      | (N.Exp U1, N.Exp U2) => 
			 (U.unify(N.coerceCtx G, (U1, I.id), (U2, I.id))
			  handle U.Unify s => raise Error ("LF Unify: " ^ s))

	      | (N.Undef, N.Undef) => ()
	      | _ => raise Error "Unification Failed:  Var's do not match.")


      | unifyExpW _ = raise Error "Unification Failed:  Expressions don't match."

  end 