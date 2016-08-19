(* 
 * Used to print Nabla Internal Syntax 
 * Author:  Adam Poswolsky
 *)
structure PrintNablaInt =
  struct

    structure N = NablaIntSyntax
    structure I = IntSyn


    fun subToString' (N.Shift k) = "Shift " ^ (Int.toString k)
      | subToString' (N.Dot (N.Idx k, t)) = "Idx " ^ (Int.toString k) ^ " . " ^ subToString'(t)
      | subToString' (N.Dot (N.Prg _, t)) = "Prg" ^ " . " ^ subToString'(t)
      | subToString' (N.Dot (N.Exp _, t)) = "Exp" ^ " . " ^ subToString'(t)
      | subToString' (N.Dot (N.Undef, t)) = "Undef" ^ " . " ^ subToString'(t)

    fun subListToString'' [] = ""
      | subListToString'' (x::xs) = ", (" ^ (subToString' x) ^ ")" ^ (subListToString'' xs)

    fun subListToString' [] = "[]"
      | subListToString' (x::xs) = "[" ^ "(" ^ (subToString' x) ^ ")" ^ (subListToString'' xs) ^ "]"

    fun formStr (Psi, N.Inj e) = ("<" ^ Print.expToString(N.coerceCtx Psi, e) ^ ">")
      | formStr (Psi, N.Imp (f1,f2)) = "(" ^ formStr(Psi, f1) ^ " -> " ^ formStr(Psi, f2) ^ ")"
      | formStr (Psi, N.Box f) = "Box(" ^ formStr(Psi, f) ^ ")"
      | formStr (Psi, N.And (f1, f2)) = "(" ^ formStr(Psi,f1) ^ " * " ^ formStr(Psi,f2) ^ ")"
      | formStr (Psi, N.TVar (ref (SOME F))) = (formStr(Psi, F))
      | formStr (Psi, N.TVar (ref NONE)) = "_" (* Corresponds to an omitted type *)
      | formStr (Psi, N.TClo (N.TVar (ref NONE), t)) = "TClo(_, " ^  subToString' t ^ ")"
      | formStr (Psi, N.TClo (N.TVar (ref (SOME F1)), t)) = formStr(Psi, N.substF(F1, t))
      | formStr (Psi, N.TClo (F, tL)) =  (formStr(Psi, N.substF(F,tL)) )


    (* ****************************************
     Print Routines to output values
     * ************************************** *)

    fun expToString (G, E) = 
      let
	val numEvars = ref 0
	val evarList = ref []

	fun findEvar (x, []) = NONE
	  | findEvar (x, ((x',s)::xs)) = if (x=x') then SOME s else findEvar (x,xs)

	fun getEvar(x) = 
	  case findEvar(x, !evarList) of
	    SOME x => x
	    | NONE => let
	                val _ = numEvars := !numEvars + 1 ;
			val s = "?" ^ Int.toString(!numEvars) ^ "?"
			val _ = evarList := (x, s) :: !evarList
		      in
			s
		      end

	fun expToString0 (G, N.Quote (e)) = "<" ^ Print.expToString(G, e) ^ ">"
	  | expToString0 (G, N.Fail) = "fail"
	  | expToString0 (G, N.App _) = "*"
	  | expToString0 (G, N.Pair (e1,e2)) = "(" ^ expToString0(G,e1) ^ ", " ^ 
                                                expToString0(G,e2) ^ ")"
	  | expToString0 (G, N.First _) = "*"
	  | expToString0 (G, N.Second _) = "*"
	  | expToString0 (G, N.FVar (s, _)) = s
	  | expToString0 (G, N.EVar (_, X as ref NONE, _)) = getEvar(X)
	  | expToString0 (G, N.EVar _) = "*EVAR*"
	  | expToString0 (G, N.EClo _) = "*"
	  | expToString0 (G, N.Some _) = "*"
	  | expToString0 (G, N.SomeM _) = "*"
	  | expToString0 (G, N.New _) = "*"
	  | expToString0 (G, N.Nabla _) = "*"
	  | expToString0 (G, N.Fix (_,F,E)) = "*"
	  | expToString0 (G, N.Case _) = "*"
	  | expToString0 (G, N.Alt (e1,e2)) = expToString0(G,e1) ^ 
						" | " ^ expToString0(G,e2)
	  | expToString0 (G, N.Pop (e)) = "N.Pop " ^ "(" 
						^ expToString0(G, e) ^ ")"
	  | expToString0 (G, N.Var _) = "*"
      in
	expToString0(G, E)
      end





    fun expToString' (G, E) = 
      let 

	val numEvars = ref 0
	val evarList = ref []

	val numVars = ref 0

	fun findEvar (x, []) = NONE
	  | findEvar (x, ((x',s)::xs)) = if (x=x') then SOME s else findEvar (x,xs)

	fun getEvar(x) = 
	  case findEvar(x, !evarList) of
	    SOME x => x
	    | NONE => let
	                val _ = numEvars := !numEvars + 1 ;
			val s = "?" ^ Int.toString(!numEvars) ^ "?"
			val _ = evarList := (x, s) :: !evarList
		      in
			s
		      end

	fun f (NONE) = 
  	       let val _ = numVars := !numVars + 1
		 val s = Int.toString(!numVars)
		 val y = "%V" ^ s ^ "%"
	       in
		 y
	       end
	  | f (SOME s) = s
	
	fun listToString' [] = ""
	  | listToString' (x::xs) = ", " ^ x ^ (listToString' xs)
	fun listToString [] = "[]" 
	  | listToString (x::xs) = "[" ^ x ^ (listToString' xs) ^ "]"

	fun (* lookup(1, I.Decl(Psi, N.MetaDec(SOME(sList), _))) = listToString sList *)
	  lookup(1, I.Decl(Psi, N.MetaDec(SOME([s]), _))) = s
	  | lookup(1, I.Decl(Psi, N.MetaDec(NONE, _))) = "?"
	  | lookup(i, I.Decl(Psi, _)) = lookup(i-1, Psi)
	  | lookup _ = raise Domain

	  (*
	fun lookup (i, _) = "Var " ^ (Int.toString(i))
	   *)


	fun expToString'' (G, N.Quote (e)) = "<" ^ Print.expToString(N.coerceCtx (hd(G)), e) ^ ">"
	  | expToString'' (G, N.Fail) = "fail"
	  | expToString'' (G, N.App (e1,e2)) = "App(" ^ expToString''(G,e1) ^ ", " ^ 
                                          expToString''(G,e2) ^ ")"
	  | expToString'' (G, N.Pair (e1,e2)) = "Pair(" ^ expToString''(G,e1) ^ ", " ^ 
                                          expToString''(G,e2) ^ ")"
	  | expToString'' (G, N.First (e)) = "First(" ^ expToString''(G,e) ^ ")"
	  | expToString'' (G, N.Second (e)) = "Second(" ^ expToString''(G,e) ^ ")"
	  | expToString'' (G, N.EVar (_, X as ref NONE, _)) = getEvar(X)
	  | expToString'' (G, N.FVar (s, _)) = s
	  | expToString'' (G, N.EVar (_, ref (SOME E), _)) = expToString''(G, E)
	  | expToString'' (G, N.EClo (E, tList)) = "ECLO(" ^ expToString''(G, E) ^ ", "
					            ^ subListToString' tList ^ ")"
	  | expToString'' (G, N.Some (sO, U,E)) = 
					  let val newS = f (sO) in
					  "Some(" ^ newS ^ " : " ^ Print.expToString(N.coerceCtx (hd(G)), U)
					   ^  ", " ^ 
                                          expToString''(I.Decl(hd(G), N.LFDec(I.Dec( SOME(newS),U)))::tl(G),E) ^ ")"
					  end
	  | expToString'' (G, N.SomeM (sO, F,E)) = 
					  let val newS = f (sO) in
					  "SomeM(" ^ newS 
					   ^  ", " ^ 
                                          expToString''(I.Decl(hd(G), N.MetaDec(SOME([newS]),F))::tl(G),E) ^ ")"
					  end

	  | expToString'' (G, N.New (sO, U,E)) = 
					  let val newS = f (sO) in
					  "New(" ^ newS ^ " : " ^ Print.expToString(N.coerceCtx (hd(G)), U)
					   ^  ", " ^ 
                                          expToString''(I.Decl(hd(G), N.LFDec(I.Dec( SOME(newS),U)))::hd(G)::tl(G),E) ^ ")"
					  end

	  | expToString'' (G, N.Nabla (sO, U,E)) = 
					  let val newS = f (sO) in
					  "Nabla(" ^ newS ^ " : " ^ Print.expToString(N.coerceCtx (hd(G)), U)
					   ^  ", " ^ 
                                          expToString''(I.Decl(hd(G), N.LFDec(I.Dec( SOME(newS),U)))::hd(G)::tl(G),E) ^ ")"
					  end

	  | expToString'' (G, N.Fix (sO, F,E)) = 
					  let val newS = f (sO) in
					  "Fix(" ^ newS 
					   ^  ", " ^ 
                                          expToString''(I.Decl(hd(G), N.MetaDec(SOME([newS]),F))::tl(G),E) ^ ")"
					  end

	  | expToString'' (G, N.Case (e1,_,e2)) = "Case(" ^ expToString''(G,e1) ^ ", " ^ 
                                          expToString''(G,e2) ^ ")"

	  | expToString'' (G, N.Alt (e1,e2)) = expToString''(G,e1) ^ " | " ^ expToString''(G,e2)
	  | expToString'' (G::Gs, N.Pop (e)) = "N.Pop " ^ "(" ^ expToString''(Gs, e) ^ ")"
	  | expToString'' (G, N.Var (i)) = lookup(i, hd(G))
	  | expToString'' _ = raise Domain

      in
	expToString'' (G, E)
      end

  end