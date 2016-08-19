(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Carsten Schuermann, Larry Greenfield, 
             Roberto Virga, Brigitte Pientka *)

functor Compile ((*! structure IntSyn' : INTSYN !*)
                 (*! structure CompSyn' : COMPSYN !*)
		 (*! sharing CompSyn'.IntSyn = IntSyn' !*)
		 structure Whnf : WHNF
		 (*! sharing Whnf.IntSyn = IntSyn' !*)
 		 structure TypeCheck : TYPECHECK
		 (*! sharing TypeCheck.IntSyn = IntSyn' !*)

		    (* CPrint currently unused *)
		 structure CPrint : CPRINT 
		 (*! sharing CPrint.IntSyn = IntSyn' !*)
		 (*! sharing CPrint.CompSyn = CompSyn' !*)

		   (* CPrint currently unused *)
		 structure Print : PRINT 
		 (*! sharing Print.IntSyn = IntSyn' !*)

		 structure Names : NAMES
		 (*! sharing Names.IntSyn = IntSyn' !*)
		   )
  : COMPILE =
struct

  (* FIX: need to associate errors with occurrences -kw *)
  exception Error of string

  local
    structure I = IntSyn
    structure T = Tomega
    structure C = CompSyn
  in

    fun notCS (I.FromCS) = false
      | notCS _ = true

    datatype Duplicates = BVAR of int | FGN | DEF of int

    val optimize = ref true  

    (* isConstraint(H) = B
       where B iff H is a constant with constraint status
    *)
    fun isConstraint (I.Const (c)) =
          (case I.constStatus (c)
             of (I.Constraint _) => true
              | _ => false)
      | isConstraint H = false

    (* head (A) = H, the head of V

       Invariants:
       G |- A : type, A enf
       A = H @ S
    *)
    fun head (I.Root(h, _)) = h
      | head (I.Pi (_, A)) = head(A)


  fun seen (i, Vars) =
        List.exists (fn (d, x) => (x = i)) Vars
     
  (* etaSpine (S, n) = true

   iff S is a spine n;n-1;..;1;nil
         
   no permutations or eta-expansion of arguments are allowed
   *)

  fun etaSpine (I.Nil, n) = (n=0)
    | etaSpine (I.App(I.Root(I.BVar (I.Fixed k), I.Nil), S), n) = 
       (k = n andalso etaSpine(S, n-1))
    | etaSpine (I.App(A, S), n) = false

  (* collectHead (h, K, Vars, depth) = (K', Vars', replaced)
     adds to K and Vars as in collectExp and collectSpine
   *)
  fun collectHead(h as I.BVar (I.Fixed k), S, K, Vars, depth) = 
       (* check if k is in Vars *)
       (if (k > depth) then 
	   (* check if h is an eta-expanded variable *)
	   (if etaSpine(S, depth) then
	      (if seen (k-depth, Vars) then 
		 (((depth, BVAR(k-depth))::K), Vars, true)
	       else 
		 (K, ((depth, k-depth)::Vars), false))
	    else 
	      (((depth, BVAR(k-depth))::K), Vars, true)) 
	 else 
	   (* h is a locally bound variable and need not be collected *)
	   (K, Vars, false))
     | collectHead (_, _, K, Vars, depth) = (K, Vars, false)

   (* collectExp (U, K, Vars, depth) = (K', Vars')
      collectSpine (S, K, Vars, depth) = (K', Vars')

      Vars' - Vars = all variables seen in U or S
      K' - K = expressions in U or S to be replaced

      U, S in NF

      for each new variable (d, k-d) for depth wrt locally bound variables
   *)
   fun collectSpine(I.Nil, K, Vars, depth) = (K, Vars)
     | collectSpine(I.App(U, S), K, Vars, depth) = 
       let 
	 val (K', Vars') = collectExp(U, K, Vars, depth)
       in 
	 collectSpine(S, K', Vars', depth)
       end

   and collectExp (I.Root(h as I.BVar (I.Fixed k), S), K, Vars, depth) =   
       let
	 val (K', Vars', replaced) = collectHead (h, S, K, Vars, depth)
       in 	   
	 if replaced
	   then (K', Vars')
	 else 
	   collectSpine (S, K', Vars', depth)
       end
     | collectExp (U as I.Root(I.Def k, S), K, Vars, depth) = 
       ((depth, DEF k)::K, Vars)
     (* h is either const, skonst or def *)
     | collectExp (I.Root(h, S), K, Vars, depth) =   
         collectSpine (S, K, Vars, depth)
     (* should be impossible, Mon Apr 15 14:55:15 2002 -fp *)
     (* | collectExp (I.Uni(L), K, Vars, depth) = (K, Vars) *)
     | collectExp (I.Lam(D, U), K, Vars, depth) = 
	 (* don't collect D, since it is ignored in unification *)
	 collectExp (U, K, Vars, depth+1)
     | collectExp (I.FgnExp (cs, fe), K, Vars, depth) = 
	 ((depth, FGN)::K, Vars)
     (* no EVars, since U in NF *)

  (* shiftHead (H, depth, total) = H'
     shiftExp (U, depth, total) = U'
     shiftSpine (S, depth, total) = S'

     where each variable k > depth is shifted by +total

     Invariants: U is NF, S is in NF
  *)
  fun shiftHead ((h as I.BVar (I.Fixed k)), depth, total) = 
      (if k > depth then
	 I.BVar(I.Fixed (k + total))
       else 
	 I.BVar(I.Fixed k))
    | shiftHead ((h as I.Const k), depth, total) = h
    | shiftHead ((h as I.Def k), depth, total) = h
    | shiftHead ((h as I.NSDef k), depth, total) = h
    | shiftHead ((h as I.FgnConst k), depth, total) = h
    | shiftHead ((h as I.Skonst k) , depth, total) = h


  fun shiftExp (I.Root(h, S), depth, total) = 
	I.Root(shiftHead(h, depth, total), shiftSpine(S, depth, total))
    | shiftExp (I.Uni(L), _, _) = I.Uni(L)
    | shiftExp (I.Lam(D, U), depth, total) = 
	I.Lam(shiftDec(D, depth, total), shiftExp(U, depth+1, total))
    | shiftExp (I.Pi((D, P), U), depth, total) =
	I.Pi((shiftDec(D, depth, total), P), shiftExp (U, depth+1, total))
    | shiftExp (I.FgnExp csfe, depth, total) = 
	(* calling normalize here because U may not be normal *)
	(* this is overkill and could be very expensive for deeply nested foreign exps *)
	(* Tue Apr  2 12:10:24 2002 -fp -bp *)
	I.FgnExpStd.Map.apply csfe (fn U => shiftExp(Whnf.normalize (U, I.id), depth, total))
  and shiftSpine (I.Nil, _, _) = I.Nil
    | shiftSpine (I.App(U, S), depth, total) = 
        I.App(shiftExp(U, depth, total), shiftSpine(S, depth, total))
  and shiftDec (I.Dec(x, V), depth, total) =
        I.Dec(x, shiftExp (V, depth, total))

  (* linearHead (Gl, h, S, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

   if G0, Gl |- h @ S and 
      h is a duplicate (i.e. it is either not fully applied pattern
       or it has already occured and is an element of Vars)

      |Gl| = depth, Gl is local context of BVars
   then 
      h' is a new variable standing for a new AVar
      M = Root(h, S) where each variable in G0 is shifted by total
      N = Root(h', I.Nil)

   and
      Eqn accumulates residual equation UnifyEq(Gl, M, N)
  *)
   fun linearHead(G, h as I.BVar(I.Fixed k), S, left, Vars, depth, total) = 
       if k > depth then 
	 (if etaSpine(S, depth) then
	    (if (seen (k-depth, Vars)) then 
	       (left-1, Vars, I.BVar(I.Fixed (left + depth)), true)
	     else
	       (left, ((depth, k-depth)::Vars), I.BVar (I.Fixed (k + total)), false))
	  else 
	    (left-1, Vars, I.BVar(I.Fixed (left + depth)), true))
       else 
	 (left, Vars, h, false)
     | linearHead(G, (h as I.Const k), S, left, Vars, depth, total) = 
	 (left, Vars, h, false)
     (*
     | linearHead(G, (h as I.NSDef k), s, S, left, Vars, depth, total) = 
	 (left, Vars, h, false)
     *)
     | linearHead(G, (h as I.FgnConst(k, ConDec)), S, left, Vars, depth, total) = 
	 (left, Vars, h, false)

     | linearHead(G, (h as I.Skonst k) , S, left, Vars, depth, total) = 
	 (left, Vars, h, false)
     (* Def cannot occur *)

  (* linearExp (Gl, U, left, Vars, depth, total, eqns) = (left', Vars', N, Eqn)

     call linearHead on every embedded root
  
     left' = left - #replaced expressions in U
     Vars' = all BVars in G0 seen in U
     N = copy of U with replaced expressions
     Eqn = residual equations

     "For any U', U = U' iff (N = U' and Eqn)"
  *)
   fun linearExp (Gl, U as I.Root(h as I.Def k, S), left, Vars, depth, total, eqns) = 
       let
	 val N = I.Root(I.BVar(I.Fixed (left + depth)), I.Nil)
	 val U' = shiftExp(U, depth, total)  
       in
	 (left-1, Vars, N, C.UnifyEq(Gl, U', N, eqns))
       end 
     | linearExp (Gl, U as I.Root(h, S), left, Vars, depth, total, eqns) = 
       let
	 val (left', Vars', h', replaced) =  linearHead (Gl, h, S, left, Vars, depth, total)
       in 
	 if replaced then 
	   let 
	     val N = I.Root(h', I.Nil)
	     val U' = shiftExp (U, depth, total)
	   in
	     (left', Vars, N, C.UnifyEq(Gl, U', N, eqns))
	   end
	 else (* h = h' not replaced *)
	   let
	     val (left'', Vars'', S', eqns') =
	         linearSpine (Gl, S, left', Vars', depth, total, eqns)
	   in 
	     (left'',  Vars'', I.Root(h', S'), eqns')
	   end 
       end 
     (* should be impossible  Mon Apr 15 14:54:42 2002 -fp *)
     (*
     | linearExp (Gl, U as I.Uni(L), left, Vars, depth, total, eqns) = 
         (left, Vars, I.Uni(L), eqns)
     *)

     | linearExp (Gl, I.Lam(D, U), left, Vars, depth, total, eqns) = 
       let
	 val D' = shiftDec(D, depth, total)
	 val (left', Vars', U', eqns') = linearExp (I.Decl(Gl, D'), U, left, Vars, 
						    depth+1, total, eqns)
       in 
	 (left', Vars', I.Lam(D', U'), eqns')
       end
   | linearExp (Gl, U as I.FgnExp (cs, ops), left, Vars, depth, total, eqns) = 
       let 
	 val N = I.Root(I.BVar(I.Fixed (left + depth)), I.Nil)
	 val U' = shiftExp(U, depth, total)  
       in
	 (left-1, Vars, N, C.UnifyEq(Gl, U', N, eqns))
       end 

   and linearSpine(Gl, I.Nil, left, Vars, depth, total, eqns) = (left, Vars, I.Nil, eqns)
     | linearSpine(Gl, I.App(U, S), left, Vars, depth, total, eqns) = 
       let 
	 val (left', Vars',  U',eqns') = linearExp(Gl, U, left, Vars, depth, total,eqns)
	 val (left'', Vars'', S', eqns'') = linearSpine(Gl, S, left', Vars', depth, total, eqns')
       in 
	 (left'', Vars'', I.App(U', S'), eqns'')
       end
     (* SClo(S, s') cannot occur *)

     
  (*  compileHead (G, R as I.Root (h, S)) = r

       r is residual goal
       if G |- R and R might not be linear 
        
       then 
                      
           G |- H ResGoal  and H is linear 
       and of the form 
           (Axists(_ , Axists( _, ....., Axists( _, Assign (E, AuxG)))))
  *)
    fun compileHead (G, R as I.Root (h, S)) = 
        let
	  val (K, _) =  collectExp (R, nil, nil, 0)
	  val left = List.length K
	  val (left', _, R', Eqs) = linearExp(I.Null, R, left, nil, 0, left, C.Trivial)

	  fun convertKRes (ResG, nil, 0) = ResG
	    | convertKRes (ResG, ((d,k)::K), i) = 
	      (C.Axists(I.ADec (SOME("A"^Int.toString i), d), convertKRes (ResG, K, i-1)))

	  val r = convertKRes(C.Assign(R', Eqs), List.rev K, left)
	in 
	     r
	end

  (* compileGoalN  fromCS A => g
     if A is a type interpreted as a subgoal in a clause and g is its
     compiled form.  No optimization is performed.

     Invariants:
     If G |- A : type,  A enf
        A has no existential type variables
     then G |- A ~> g  (A compiles to goal g)
     and  G |- g  goal

     Note: we don't accept objects that may introduce assumptions of
     constraint types, unless fromCS = true (the object come from a
     Constraint Solver module.
  *)
  fun compileGoalN fromCS (G, R as I.Root _) =
      (* A = H @ S *)
        C.Atom (R)
    | compileGoalN fromCS (G, I.Pi((I.Dec(_,A1), I.No), A2)) =
      (* A = A1 -> A2 *)
      let
	val Ha1 = I.targetHead A1
      in
	(* A1 is used to build the proof term, Ha1 for indexing *)
	(* never optimize when compiling local assumptions *)
	C.Impl (compileClauseN fromCS false (G, A1), A1, Ha1, 
		compileGoalN fromCS (I.Decl(G, I.Dec(NONE, A1)), A2))
      end
    | compileGoalN fromCS (G, I.Pi((D as I.Dec (_, A1), I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
       if notCS fromCS andalso isConstraint (head (A1))
       then raise Error "Constraint appears in dynamic clause position"
       else C.All (D, compileGoalN fromCS (I.Decl(G, D), A2))
  (*  compileGoalN _ should not arise by invariants *)


  (* compileClauseN A => G
     if A is a type interpreted as a clause and G is its compiled form.

     Some optimization is attempted if so flagged.

     Invariants:
     If G |- A : type, A enf
        A has no existential type variables
     then G |- A ~> r  (A compiles to residual goal r)
     and  G |- r  resgoal
  *)

  and compileClauseN fromCS opt (G, R as I.Root (h, S)) =      
      if opt andalso !optimize then
	compileHead(G, R) (* C.Eq(R) *)
      else    
        if notCS fromCS andalso isConstraint (h)
        then raise Error "Constraint appears in dynamic clause position"
        else C.Eq(R)
    | compileClauseN fromCS opt (G, I.Pi((D as (I.Dec(_,A1)),I.No), A2)) =
      (* A = A1 -> A2 *)
	C.And (compileClauseN fromCS opt (I.Decl(G, D), A2), A1, 
	       compileGoalN fromCS (G, A1))
    | compileClauseN fromCS opt (G, I.Pi((D as (I.Dec(_,A1)),I.Meta), A2)) =
      (* A = {x: A1} A2, x  meta variable occuring in A2 *)
	C.In (compileClauseN fromCS opt (I.Decl(G, D), A2), A1, 
		compileGoalN fromCS (G, A1))
    | compileClauseN fromCS opt (G, I.Pi((D,I.Maybe), A2)) =
      (* A = {x:A1} A2 *)
        C.Exists (D, compileClauseN fromCS opt (I.Decl(G, D), A2))
    (*  compileClauseN _ should not arise by invariants *)

  fun compileClause opt (G, A) = 
        compileClauseN I.Ordinary opt (G, Whnf.normalize (A, I.id))
  fun compileGoal (G, A) = compileGoalN I.Ordinary (G, Whnf.normalize (A, I.id))

  (* compileCtx G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compileCtx opt G =
      let
        fun compileBlock (nil, s, (n, i)) = nil
	  | compileBlock (I.Dec (_, V) :: Vs, t, (n, i)) =  
	    let 
	      val Vt = I.EClo (V, t)
	    in
	      (compileClause opt (G, Vt), I.id, I.targetHead Vt)
	      :: compileBlock (Vs, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx n, i), I.Nil)), t), (n, i+1))
	    end
	fun compileCtx' (I.Null) = I.Null
	  | compileCtx' (I.Decl (G, I.Dec (_, A))) =
	    let 
	      val Ha = I.targetHead A
	    in
	      I.Decl (compileCtx' G, CompSyn.Dec (compileClause opt (G, A), I.id, Ha))
	    end
	  | compileCtx' (I.Decl (G, I.BDec (_, (c, s)))) =
	    let
	      val (G, L)= I.constBlock c
	      val dpool = compileCtx' G
	      val n = I.ctxLength dpool   (* this is inefficient! -cs *)
	    in
	      I.Decl (dpool, CompSyn.BDec (compileBlock (L, s, (n, 1))))
	    end
    
	    
      in
	C.DProg (G, compileCtx' G)
      end

  (* compile G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compilePsi opt Psi =
      let
        fun compileBlock (nil, s, (n, i)) = nil
	  | compileBlock (I.Dec (_, V) :: Vs, t, (n, i)) =  
	    let 
	      val Vt = I.EClo (V, t)
	    in
	      (compileClause opt (T.coerceCtx Psi, Vt), I.id, I.targetHead Vt)
	      :: compileBlock (Vs, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx n, i), I.Nil)), t), (n, i+1))
	    end
	fun compileCtx' (I.Null) = I.Null
	  | compileCtx' (I.Decl (G, I.Dec (_, A))) =
	    let 
	      val Ha = I.targetHead A
	    in
	      I.Decl (compileCtx' G, CompSyn.Dec (compileClause opt (G, A), I.id, Ha))
	    end
	  | compileCtx' (I.Decl (G, I.BDec (_, (c, s)))) =
	    let
	      val (G, L)= I.constBlock c
	      val dpool = compileCtx' G
	      val n = I.ctxLength dpool   (* this is inefficient! -cs *)
	    in
	      I.Decl (dpool, CompSyn.BDec (compileBlock (L, s, (n, 1))))
	    end
    	fun compilePsi' (I.Null) = I.Null
	  | compilePsi' (I.Decl (Psi, T.UDec (I.Dec (_, A)))) =
	    let 
	      val Ha = I.targetHead A
	    in
	      I.Decl (compilePsi' Psi, CompSyn.Dec (compileClause opt (T.coerceCtx Psi, A), I.id, Ha))
	    end
	  | compilePsi' (I.Decl (Psi, T.UDec (I.BDec (_, (c, s))))) =
	    let
	      val (G, L)= I.constBlock c
	      val dpool = compileCtx' G
	      val n = I.ctxLength dpool   (* this is inefficient! -cs *)
	    in
	      I.Decl (dpool, CompSyn.BDec (compileBlock (L, s, (n, 1))))
	    end
	  | compilePsi' (I.Decl (Psi, T.PDec _)) =
	    I.Decl (compilePsi' Psi, CompSyn.PDec)
	      
    
	    
      in
	C.DProg (T.coerceCtx Psi, compilePsi' Psi)
      end




(* dead code? -- cs 
  (* compileCtx' G = (G, dPool)

     Invariants:
     If |- G ctx,
     then |- G ~> dPool  (context G compile to clause pool dPool)
     and  |- dPool  dpool
  *)
  fun compileCtx' opt (G, B) =
      let 
	fun compileCtx'' (I.Null, I.Null) = I.Null
	  | compileCtx'' (I.Decl (G, D as I.Dec (_, A)),
			 I.Decl (B, T)) =
	    let 
	      val Ha = I.targetHead A
	    in
	      I.Decl (compileCtx'' (G, B), C.Dec (compileClause opt (G, A), I.id, Ha))
	    end
      in
	C.DProg (G, compileCtx'' (G, B))
      end

*)
  (* compileConDec (a, condec) = ()
     Effect: install compiled form of condec in program table.
             No effect if condec has no operational meaning
  *)
  (* Defined constants are currently not compiled *)
  fun compileConDec fromCS (a, I.ConDec(_, _, _, _, A, I.Type)) =
        C.sProgInstall (a, C.SClause (compileClauseN fromCS true (I.Null, A)))
    | compileConDec fromCS (a, I.SkoDec(_, _, _, A, I.Type)) =
        C.sProgInstall (a, C.SClause (compileClauseN fromCS true (I.Null, A)))
    | compileConDec I.Clause (a, I.ConDef(_, _, _, _, A, I.Type, _)) =
	C.sProgInstall (a, C.SClause (compileClauseN I.Clause true (I.Null, A)))
    | compileConDec _ _ = ()

  fun install fromCS (cid) = compileConDec fromCS (cid, I.sgnLookup cid)

  end  (* local open ... *)
end; (* functor Compile *)

