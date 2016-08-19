(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao, Adam Poswolsky *)

functor Tomega (structure Whnf : WHNF
		structure Conv : CONV) : TOMEGA = 
struct
  exception Error of string 

  type label = int      
  type lemma = int 

  datatype Worlds = Worlds of IntSyn.cid list

  datatype Quantifier = Implicit | Explicit

  datatype For  			(* Formulas                   *)
  = World of Worlds * For               (* F ::= World l1...ln. F     *)  
  | All of (Dec * Quantifier) * For	(*     | All LD. F            *)
  | Ex  of (IntSyn.Dec * Quantifier) * For
					(*     | Ex  D. F             *)
  | True				(*     | T                    *)
  | And of For * For                    (*     | F1 ^ F2              *)
  | FClo of For * Sub			(*     | F [t]                *)
  | FVar of (Dec IntSyn.Ctx * For option ref)
					(*     | F (G)                *)

  and Dec =			        (* Declaration:               *)
    UDec of IntSyn.Dec                  (* D ::= x:A                  *)
  | PDec of string option * For         (*     | xx :: F              *)

  and Prg =				(* Programs:                  *)
    Box of Worlds * Prg                 (*     | box W. P             *)
  | Lam of Dec * Prg	 	        (*     | lam LD. P            *)
  | New of Prg                          (*     | new P                *)
  | Choose of Prg                       (*     | choose P             *)
  | PairExp of IntSyn.Exp * Prg         (*     | <M, P>               *)
  | PairBlock of IntSyn.Block * Prg     (*     | <rho, P>             *) 
  | PairPrg of Prg * Prg                (*     | <P1, P2>             *)
  | Unit				(*     | <>                   *)
  | Redex of Prg * Spine
  | Rec of Dec * Prg			(*     | mu xx. P             *)
  | Case of Cases                       (*     | case t of O          *)
  | PClo of Prg * Sub			(*     | P [t]                *)
  | Let of Dec * Prg * Prg              (*     | let D = P1 in P2     *)
  | EVar of (Dec IntSyn.Ctx * Prg option ref * For)
					(*     | E (G, F)             *)
  | Const of lemma                      (* P ::= cc                   *)
  | Var of int                          (*     | xx                   *)

  and Spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | AppExp of IntSyn.Exp * Spine        (*     | P U                  *) 
  | AppBlock of IntSyn.Block * Spine    (*     | P rho                *)
  | AppPrg of Prg * Spine               (*     | P1 P2                *)
  | SClo of Spine * Sub                 (*     | S [t]                *) 
 
  and Sub =				(* t ::=                      *)
    Shift of int			(*       ^n                   *)
  | Dot of Front * Sub			(*     | F . t                *)
      
  and Front =				(* F ::=                      *)
    Idx of int  			(*     | i                    *)
  | Prg of Prg				(*     | p                    *)
  | Exp of IntSyn.Exp			(*     | U                    *)
  | Block of IntSyn.Block		(*     | _x                   *)
  | Undef                               (*     | _                    *)

  and Cases =				(* Cases                      *)
    Cases of (Dec IntSyn.Ctx * Sub * Prg) list
                                        (* C ::= (Psi' |> s |-> P)    *)

  datatype ConDec =			(* ConDec                     *)
    ForDec of string * For		(* CD ::= f :: F              *)
  | ValDec of string * Prg * For	(*      | f == P              *)

  exception NoMatch

  local
    structure I = IntSyn
    val maxLemma = Global.maxCid
    val lemmaArray = Array.array (maxLemma+1, ForDec ("", True)) 
                   : ConDec Array.array
    val nextLemma = ref 0

    fun lemmaLookup lemma = Array.sub (lemmaArray, lemma)
    fun lemmaAdd (lemmaDec) = 
        let
	  val lemma = !nextLemma
	in
	  if lemma > maxLemma
	    then raise Error ("Global signature size " ^ Int.toString (maxLemma+1) ^ " exceeded")
	  else (Array.update (lemmaArray, lemma, lemmaDec) ;
		nextLemma := lemma + 1;
		lemma)
	end
    fun lemmaSize () = (!nextLemma)
    fun lemmaDef lemma = 
        case (lemmaLookup lemma) 
	  of ValDec (_, P, _) => P
    fun lemmaFor lemma = 
        case (lemmaLookup lemma)
	  of ForDec (_, F) => F
	   | ValDec (_, _, F) => F

    fun lemmaName s = lemmaName' (!nextLemma) s
    and lemmaName' ~1 s = raise Error "Function name not found"
      | lemmaName' n s = 
        (case lemmaLookup n
	   of ForDec (s', F) => if s=s' then n 
			       else lemmaName' (n-1) s 
	    | ValDec (s', P, F) => if s=s' then n 
				   else lemmaName' (n-1) s)
	   (* not very efficient, improve !!! *)


    (* coerceFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)
    fun coerceFront (Idx k) = I.Idx k 
      | coerceFront (Prg P) = I.Undef
      | coerceFront (Exp M) = I.Exp M
      | coerceFront (Block B) = I.Block B
      | coerceFront (Undef) = I.Undef
    (* --Yu Liao Why cases: Block, Undef aren't defined *)

    (* embedFront F = F'

       Invariant:
       If    Psi |- F front
       and   G = mu G. G \in Psi
       then  G   |- F' front
    *)
    fun embedFront (I.Idx k) = Idx k 
      | embedFront (I.Exp U) = Exp U
      | embedFront (I.Block B) = Block B
      | embedFront (I.Undef) = Undef


    (* coerceSub t = s
     
       Invariant: 
       If    Psi |- t : Psi'
       then  G   |- s : G'  
       where G = mu G. G \in Psi
       and   G' = mu G. G \in Psi'
    *)
    fun coerceSub (Shift n) = I.Shift n
      | coerceSub (Dot (Ft, t)) = 
          I.Dot (coerceFront Ft, coerceSub t)

    fun embedSub (I.Shift n) = Shift n
      | embedSub (I.Dot (Ft, s)) = 
          Dot (embedFront Ft, embedSub s)


    (* Definition: 
       |- Psi ctx[block] holds iff Psi = _x_1 : (L1, t1), ... _x_n : (Ln, tn)
    *)
	  
    fun revCoerceFront (I.Idx k) = Idx k
      | revCoerceFront (I.Exp M) = Exp M
      | revCoerceFront (I.Block b) = Block b
      | revCoerceFront I.Undef = Undef


    (* revCoerceSub t = s 
    coerce substitution in LF level t ==> s in Tomega level *)
    fun revCoerceSub (I.Shift n) = Shift n
      | revCoerceSub (I.Dot (Ft, t)) = Dot(revCoerceFront Ft, revCoerceSub t)

  
    (* Invariant Yu? *)
    fun revCoerceCtx I.Null = I.Null
      | revCoerceCtx (I.Decl (Psi, D as I.BDec (_, (L, t)))) = 
          I.Decl (revCoerceCtx (Psi), UDec D)



    val id = Shift 0

    (* dotEta (Ft, s) = s'
       
       Invariant: 
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
    fun dotEta (Ft as Idx _, s) = Dot (Ft, s)
      | dotEta (Ft as Exp (U), s) =
	let
	  val Ft' = Idx (Whnf.etaContract U)
		   handle Eta => Ft
	in
	  Dot (Ft', s)
	end
      | dotEta (Ft as Undef, s) = Dot (Ft, s)


    (* embedCtx G = Psi

       Invariant:  
       If   G is an LF ctx
       then Psi is G, embedded into Tomega
    *)
    fun embedCtx I.Null = I.Null
      | embedCtx (I.Decl (G, D)) = 
          I.Decl (embedCtx G, UDec D)


    (* bvarSub (n, t) = Ft'
   
       Invariant: 
       If    Psi |- t : Psi'    Psi' |- n :: F
       then  Ft' = Ftn          if  t = Ft1 .. Ftn .. ^k
         or  Ft' = ^(n+k)       if  t = Ft1 .. Ftm ^k   and m<n
       and   Psi |- Ft' :: F [t]
    *)
    fun varSub (1, Dot(Ft, t)) = Ft
      | varSub (n, Dot(Ft, t)) = varSub (n-1, t)
      | varSub (n, Shift(k))  = Idx (n+k)


    (* decSub (x::F, t) = D'

       Invariant:
       If   Psi  |- t : Psi'    Psi' |- F formula
       then D' = x:F[t]
       and  Psi  |- F[t] formula
    *)
    fun decSub (PDec (x, F), t) = PDec (x, FClo (F, t))
      | decSub (UDec D, t) = UDec (I.decSub (D, coerceSub t))


    (* frontSub (Ft, t) = Ft' 
     
       Invariant:
       If   Psi |- Ft :: F
       and  Psi' |- t :: Psi
       then Ft' = Ft[t]
       and  Psi' |- Ft' :: F[t]
    *)
    and frontSub (Idx (n), t) = varSub (n, t)
      | frontSub (Exp (U), t) = Exp (I.EClo (U, coerceSub t))
      | frontSub (Prg (P), t) = Prg (PClo (P, t))
      | frontSub (Block B, t) = Block (I.blockSub (B, coerceSub t))
     (* Block case is missing --cs *)


    (* comp (t1, t2) = t

       Invariant:
       If   Psi'' |- t2 :: Psi'
       and  Psi' |- t1 :: Psi
       then t = t1 o t2
       and  Psi'' |- t1 o t2 :: Psi'
    *)
    and comp (Shift (0), t) = t
      | comp (t, Shift (0)) = t
      | comp (Shift (n), Dot (Ft, t)) = comp (Shift (n-1), t)
      | comp (Shift (n), Shift (m)) = Shift (n+m)
      | comp (Dot (Ft, t), t') = Dot (frontSub (Ft, t'), comp (t, t'))
   



    (* dot1 (t) = t'

       Invariant:
       If   G |- t : G'
       then t' = 1. (t o ^)
       and  for all V t.t.  G' |- V : L
            G, V[t] |- t' : G', V 

       If t patsub then t' patsub
    *)
    fun dot1 (t as Shift (0)) = t
      | dot1 t = Dot (Idx(1), comp(t, Shift 1))

    val id = Shift 0
    val shift = Shift 1

    (* weakenSub (Psi) = w

       Invariant:
       If   Psi is a context
       then G is embed Psi
       and  Psi |- w : G
    *)
    fun weakenSub (I.Null) = id
      | weakenSub (I.Decl (Psi, D as UDec _)) =
	  dot1 (weakenSub Psi)
      | weakenSub (I.Decl (Psi, D as PDec _)) =
	  comp (weakenSub Psi, shift)



    (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id  
    *)
    fun invertSub s =
      let 
	(* returns NONE if not found *)
	fun getFrontIndex (Idx k) = SOME(k)
	  | getFrontIndex (Prg P) = getPrgIndex(P)
	  | getFrontIndex (Exp U) = getExpIndex(U)
	  | getFrontIndex (Block B) = getBlockIndex(B)
	  | getFrontIndex (Undef) = NONE
	  

	(* getPrgIndex returns NONE if it is not an index *)
	and getPrgIndex (Redex (Var k, Nil )) = SOME(k)
	  | getPrgIndex (Redex (P, Nil)) = getPrgIndex(P)
	  
	  (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
	  | getPrgIndex (PClo (P,t)) = 
	       (case getPrgIndex(P) of
		  NONE => NONE
		| SOME i => getFrontIndex (varSub (i, t)))		
	  | getPrgIndex _ = NONE

	(* getExpIndex returns NONE if it is not an index *)
	and getExpIndex (I.Root (I.BVar B, I.Nil)) = 
	         (case (Whnf.whnfBVar (B, I.id))
		      of (I.Fixed k, s) =>
			 (case I.bvarSub (k, s)
			    of (I.Idx k') => SOME k'
			     | I.Exp U => getExpIndex U
			     | _ => NONE
			  )
	               | _ => NONE (* if it is a BVarVar we don't have an explicit index to return *)
                   )

	  | getExpIndex (I.Redex (U, I.Nil)) = getExpIndex(U)
	  | getExpIndex (I.EClo (U, t)) =
	       (case getExpIndex(U) of
		  NONE => NONE
		| SOME i => getFrontIndex (revCoerceFront(I.bvarSub(i, t))))
	    
	  | getExpIndex (U as I.Lam (I.Dec (_, U1), U2)) = (SOME ( Whnf.etaContract(U) )  handle Whnf.Eta => NONE)
	  | getExpIndex _ = NONE

	(* getBlockIndex returns NONE if it is not an index *)
	and getBlockIndex (I.Bidx k) = SOME(k)
	  | getBlockIndex _ = NONE


	fun lookup (n, Shift _, p) = NONE
	  | lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
	  | lookup (n, Dot (Idx k, s'), p) = 
	    if k = p then SOME n 
	    else lookup (n+1, s', p)

	(* Suggested by ABP 
	 * If you do not want this, remove the getFrontIndex and other 
	  | lookup (n, Dot (Ft, s'), p) =
	      (case getFrontIndex(Ft) of
		 NONE => lookup (n+1, s', p)
	       | SOME k => if (k=p) then SOME n else lookup (n+1, s', p))
        *)
	
	fun invertSub'' (0, si) = si
	  | invertSub'' (p, si) = 
	    (case (lookup (1, s, p))
	       of SOME k => invertSub'' (p-1, Dot (Idx k, si))
	        | NONE => invertSub'' (p-1, Dot (Undef, si)))
	       
	fun invertSub' (n, Shift p) = invertSub'' (p, Shift n)
	  | invertSub' (n, Dot (_, s')) = invertSub' (n+1, s')
      in
	invertSub' (0, s)
      end
  
    
    (* coerceCtx (Psi) = G

       Invariant:
       If   |- Psi ctx[block] 
       then |- G lf-ctx[block]
       and  |- Psi == G
    *) 
    fun coerceCtx I.Null = I.Null
      | coerceCtx (I.Decl (Psi, UDec D)) = 
          I.Decl (coerceCtx Psi, D)
      | coerceCtx (I.Decl (Psi, PDec _)) = 
	  I.Decl (coerceCtx Psi, I.NDec) 

    

    (* coerceCtx (Psi) = (G, s)

       Invariant:
       If   |- Psi ctx[block] 
       then |- G lf-ctx[block]
       and  |- Psi == G
       and  G |- s : Psi
    *) 
    fun strengthenCtx Psi = 
        let 
	  val w = weakenSub Psi
	  val s = invertSub w
	in
	  (coerceCtx Psi, w, s)
	end

    (* convFor ((F1, t1), (F2, t2)) = B

       Invariant:
       If   G |- t1 : G1
       and  G1 |- F1 : formula     
       and  G |- t2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)

    fun convFor ((True, _), (True, _)) = true
      | convFor ((All ((D1, _), F1), t1),
		 (All ((D2, _), F2), t2)) =
          convDec ((D1, t1), (D2, t2))
          andalso convFor ((F1, dot1 t1), (F2, dot1 t2))
      | convFor ((Ex ((D1, _), F1), t1), 
		 (Ex ((D2, _), F2), t2)) = 
	  Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
	  andalso convFor ((F1, dot1 t1), (F2, dot1 t2))
      | convFor ((And (F1, F1'), t1), (And (F2, F2'), t2)) =
	  convFor ((F1, t1), (F2, t2))
	  andalso convFor ((F1', t1), (F2', t2))
      | convFor _ = false
    and convDec ((UDec D1, t1), (UDec D2, t2)) = 
          Conv.convDec ((D1, coerceSub t1), (D2, coerceSub t2))
      | convDec ((PDec (_, F1), t1), (PDec (_, F2), t2)) =
	  convFor ((F1, t1), (F2, t2))


  (* newEVar (G, V) = newEVarCnstr (G, V, nil) *)
  fun newEVar (Psi, F) = EVar(Psi, ref NONE, F)

  fun exists (x, []) = false 
    | exists (x, y :: W2) = (x = y) orelse exists (x, W2)

  fun subset ([], _) = true
    | subset (x :: W1, W2) = exists (x, W2) andalso subset (W1, W2)

  fun eqWorlds (Worlds W1, Worlds W2) = 
      subset (W1, W2) andalso subset (W2, W1)


  (* ctxDec (G, k) = x:V
     Invariant: 
     If      |G| >= k, where |G| is size of G,
     then    G |- k : V  and  G |- V : L
  *)
    fun ctxDec (G, k) =
      let (* ctxDec' (G'', k') = x:V
	     where G |- ^(k-k') : G'', 1 <= k' <= k
           *)
	fun ctxDec' (I.Decl (G', UDec (I.Dec(x, V'))), 1) = UDec (I.Dec(x, I.EClo (V', I.Shift (k))))
	  | ctxDec' (I.Decl (G', UDec (I.BDec (l, (c, s)))), 1) = UDec (I.BDec (l, (c, I.comp (s, I.Shift (k)))))
	  | ctxDec' (I.Decl (G', PDec (x, F)), 1) = PDec(x, FClo (F, Shift(k)))
	  | ctxDec' (I.Decl (G', _), k') = ctxDec' (G', k'-1)
	 (* ctxDec' (Null, k')  should not occur by invariant *)
      in
	ctxDec' (G, k)
      end


     (* mkInst (n) = iota

        Invariant:
        iota = n.n-1....1
     *)
    fun mkInst (0) = nil
      | mkInst (n) = I.Root (I.BVar (I.Fixed n), I.Nil) :: mkInst (n-1)

    
    (* deblockify G = (G', t')
     
       Invariant:
       If   |- G ctx
       then G' |- t' : G 
    *)
    fun deblockify  (I.Null) = (I.Null, id)
      | deblockify  (I.Decl (G, I.BDec (x, (c, s)))) = 
        let
	  val (G', t') = deblockify  G
					(* G' |- t' : G *)
          val (_, L) = I.constBlock c
	  val n = List.length L
	  val G'' = append (G', (L, I.comp (s, coerceSub t')))
					(* G'' = G', V1 ... Vn *)
	  val t'' = comp (t', Shift n)
					(* G'' |- t'' : G *)
	  val I = I.Inst (mkInst n)
					(* I = (n, n-1 ... 1)  *)
	  val t''' = Dot (Block I, t'')
					(* G'' |- t''' : G, x:(c,s) *)
	in 
          (G'', t''')
	end
    and append (G', (nil, s)) = G'
      | append (G', (D :: L, s)) = 
          append (I.Decl (G', I.decSub (D, s)), (L, I.dot1 s))


    (* forSub (F, t) = F'
     
       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- F' = F[t] for
    *)
    fun forSub (All ((D, Q), F), t) = 
          All ((decSub (D, t), Q),  
		 forSub (F, dot1 t)) 
      | forSub (Ex ((D, Q), F), t) = 
	  Ex ((I.decSub (D, coerceSub t), Q),
		 forSub (F, dot1 t))
      | forSub (And (F1, F2), t) =
	  And (forSub (F1, t), 
		 forSub (F2, t))
      | forSub (FClo (F, t1), t2) = 
	  forSub (F, comp (t1, t2))
      | forSub (World (W, F), t) =
	  World (W, forSub (F, t))
      | forSub (True, _) = True


    (* whnfFor (F, t) = (F', t')
     
       Invariant:
       If    Psi |- F for
       and   Psi' |- t : Psi
       then  Psi' |- t' : Psi''
       and   Psi'' |- F' :for
       and   Psi' |- F'[t'] = F[t] for
    *)
    fun whnfFor (Ft as (All (D, _), t)) = Ft
      | whnfFor (Ft as (Ex (D, F), t)) = Ft 
      | whnfFor (Ft as (And (F1, F2), t)) = Ft
      | whnfFor (FClo (F, t1), t2) = 
	  whnfFor (F, comp (t1, t2))
      | whnfFor (Ft as (World (W, F), t)) = Ft
      | whnfFor (Ft as (True, _)) = Ft



    (* normalizePrg (P, t) = (P', t')
     
       Invariant:
       If   Psi' |- V :: F
       and  Psi' |- V value
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F' 
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)

    fun normalizePrg (Var n, t) = 
        (case varSub (n, t) 
	   of (Prg P) => P
	   | (Idx _) => raise Domain
	   | (Exp _) => raise Domain
	   | (Block _) => raise Domain
	   | (Undef) => raise Domain
	     )
      |  normalizePrg (PairExp (U, P'), t) = 
	  PairExp (Whnf.normalize (U, coerceSub t), normalizePrg (P', t))
      | normalizePrg (PairBlock (B, P'), t) = 
	  PairBlock (I.blockSub (B, coerceSub t), normalizePrg (P', t))
      | normalizePrg (PairPrg (P1, P2), t) =
          PairPrg (normalizePrg (P1, t), normalizePrg (P2, t))
      | normalizePrg (Unit, _) = Unit
      | normalizePrg (EVar (_, ref (SOME P), _), t) = PClo(P, t)
      | normalizePrg (P as EVar _, t) = PClo(P,t) 
      | normalizePrg (PClo (P, t), t') = normalizePrg (P, comp (t, t'))

    and normalizeSpine (Nil, t) = Nil
      | normalizeSpine (AppExp (U, S), t) =
         AppExp (Whnf.normalize (U, coerceSub t), normalizeSpine (S, t)) 
      | normalizeSpine (AppPrg (P, S), t) =
          AppPrg (normalizePrg (P, t), normalizeSpine (S, t))
      | normalizeSpine (AppBlock (B, S), t) =
          AppBlock (I.blockSub (B, coerceSub t), normalizeSpine (S, t))
      | normalizeSpine (SClo (S, t1), t2) =
	  normalizeSpine (S, comp (t1, t2))

    fun normalizeSub (s as Shift n) = s
      | normalizeSub (Dot (Prg P, s)) =
          Dot (Prg (normalizePrg (P, id)), normalizeSub s)
      | normalizeSub (Dot (Exp E, s)) =
	  Dot (Exp (Whnf.normalize (E, I.id)), normalizeSub s)
      | normalizeSub (Dot (Block k, s)) = 
	  Dot (Block k, normalizeSub s)
      | normalizeSub (Dot (Idx k, s)) = 
	  Dot (Idx k, normalizeSub s)



  in 
    val lemmaLookup = lemmaLookup 
    val lemmaAdd = lemmaAdd
    val lemmaSize = lemmaSize
    val lemmaDef = lemmaDef
    val lemmaName = lemmaName
    val lemmaFor = lemmaFor

    val coerceSub = coerceSub
    val coerceCtx = coerceCtx
    val strengthenCtx = strengthenCtx
    val embedCtx = embedCtx
    val id = id
    val shift = shift
    val comp = comp
    val dot1 = dot1
    val varSub = varSub
    val decSub = decSub
    val weakenSub = weakenSub
    val invertSub = invertSub
    val ctxDec = ctxDec
    val forSub = forSub
    val whnfFor = whnfFor
    val normalizePrg = normalizePrg
    val normalizeSub = normalizeSub
      
    val id = id
    val dotEta = dotEta
    val convFor = convFor
    val newEVar = newEVar

(* Below are added by Yu Liao *)
    val embedSub = embedSub
    val eqWorlds = eqWorlds
    val ctxDec = ctxDec 
    val revCoerceSub = revCoerceSub
    val revCoerceCtx = revCoerceCtx

(* Added referenced by ABP *)
    val coerceFront = coerceFront
    val revCoerceFront = revCoerceFront
    val deblockify = deblockify

  end
end;  (* functor FunSyn *)
