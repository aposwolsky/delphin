(* Gaussian-Elimination Equation Solver *)
(* Author: Roberto Virga *)

functor CSEqField (structure Field : FIELD
                   (*! structure IntSyn : INTSYN !*)
                   structure Whnf : WHNF
		   (*! sharing Whnf.IntSyn = IntSyn !*)
                   structure Unify : UNIFY
		   (*! sharing Unify.IntSyn = IntSyn !*)
                   (*! structure CSManager : CS_MANAGER !*)
		   (*! sharing CSManager.IntSyn = IntSyn !*)
		       )
 : CS_EQ_FIELD =
struct
  (*! structure CSManager = CSManager !*)

  structure Field = Field
  (*! structure IntSyn = IntSyn !*)

  type 'a mset = 'a list                 (* MultiSet                   *)

  datatype Sum =                         (* Sum :                      *)
    Sum of Field.number * Mon mset       (* Sum ::= m + M1 + ...       *)

  and Mon =                              (* Monomials:                 *)
    Mon of Field.number * (IntSyn.Exp * IntSyn.Sub) mset
                                         (* Mon ::= n * U1[s1] * ...   *)

  (* A monomial (n * U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) the coefficient n is different from zero;
       (b) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)

  local
    open IntSyn
    open Field

    structure FX = CSManager.Fixity
    structure MS = ModeSyn (* CSManager.ModeSyn *)

    exception MyIntsynRep of Sum        (* FgnExp representation for this domain *)

    fun extractSum (MyIntsynRep sum) = sum
      | extractSum fe = raise (UnexpectedFgnExp fe)

    (* constraint solver ID of this module *)
    val myID = ref ~1 : csid ref

    (* constant ID of the type family constant "number" *)
    val numberID = ref ~1 : cid ref

    fun number () = Root (Const (!numberID), Nil)

    (* constant ID's of the object constants defined by this module *)
    val unaryMinusID  = ref ~1 : cid ref  (* ~ : number -> number           *)
    val plusID        = ref ~1 : cid ref  (* + : number -> number -> number *)
    val minusID       = ref ~1 : cid ref  (* - : number -> number -> number *)
    val timesID       = ref ~1 : cid ref  (* * : number -> number -> number *)

    fun unaryMinusExp (U) = Root (Const (!unaryMinusID), App (U, Nil))
    fun plusExp (U, V)    = Root (Const (!plusID), App (U, App (V, Nil)))
    fun minusExp (U, V)   = Root (Const (!minusID), App (U, App (V, Nil)))
    fun timesExp (U, V)   = Root (Const (!timesID), App (U, App (V, Nil)))

    fun numberConDec (d) = ConDec (toString (d), NONE, 0, Normal, number (), Type)
    fun numberExp (d) = Root (FgnConst (!myID, numberConDec (d)), Nil)

    (* parseNumber str = SOME(conDec) or NONE

       Invariant: 
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
    fun parseNumber string =
          (case fromString (string)
             of SOME(d) => SOME(numberConDec (d))
              | NONE => NONE)

    (* solveNumber k = SOME(U)

       Invariant: 
       U is the term obtained applying the foreign constant
       corresponding to the number k to an empty spine
    *)
    fun solveNumber (G, S, k) = SOME(numberExp (fromInt k))

    (* findMset eq (x, L) =
         SOME (y, L') if there exists y such that eq (x, y)
                         and L ~ (y :: L') (multiset equality)
         NONE if there is no y in L such that eq (x, y)
    *)
    fun findMSet eq (x, L) =
          let
            fun findMSet' (tried, nil) = NONE
              | findMSet' (tried, y :: L) =
                  if eq(x, y) then SOME(y, tried @ L)
                  else findMSet' (y :: tried, L)
          in
            findMSet' (nil, L)
          end

    (* equalMset eq (L, L') = true iff L ~ L' (multiset equality) *)
    fun equalMSet eq =
          let
              fun equalMSet' (nil, nil) = true
                | equalMSet' (x :: L1', L2) =
                    (case (findMSet eq (x, L2))
                       of SOME (y, L2') => (equalMSet' (L1', L2'))
                        | NONE => false)
                | equalMSet' _ = false
            in
              equalMSet'
            end
      
    (* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *)
    fun toExp (Sum (m, nil)) = numberExp m
      | toExp (Sum (m, [mon])) =
          if (m = zero) then toExpMon mon
          else plusExp (toExp (Sum (m, nil)), toExpMon mon)
      | toExp (Sum (m, monLL as (mon :: monL))) =
          plusExp (toExp (Sum (m, monL)), toExpMon mon)

    (* toExpMon mon = U

       Invariant:
       If mon is normal
       G |- U : V and U is the Twelf syntax conversion of mon
    *)
    and toExpMon (Mon (n, nil)) = numberExp n
      | toExpMon (Mon (n, [Us])) =
          if (n = one) then toExpEClo Us
          else timesExp (toExpMon (Mon (n, nil)), toExpEClo Us)
      | toExpMon (Mon (n, Us :: UsL)) =
          timesExp (toExpMon (Mon (n, UsL)), toExpEClo Us)

    (* toExpEClo (U,s) = U

       Invariant: 
       G |- U : V and U is the Twelf syntax conversion of Us
    *)
    and toExpEClo (U, Shift (0)) = U
      | toExpEClo Us = EClo Us

    (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)
    fun compatibleMon (Mon (_, UsL1), Mon (_, UsL2)) =
          equalMSet (fn (Us1, Us2) => sameExpW (Us1, Us2)) (UsL1, UsL2)

    (* sameExpW ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1)  in whnf
       and  G |- s2 : G2    G2 |- U2 : V2    (U2,s2)  in whnf
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    and sameExpW (Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
          (case (H1, H2) of
	     (BVar(Fixed k1), BVar(Fixed k2)) => 
	       (k1 = k2) andalso sameSpine ((S1, s1), (S2, s2))
	   | (FVar (n1,_,_,_), FVar (n2,_,_,_)) =>
	       (n1 = n2) andalso sameSpine ((S1, s1), (S2, s2))
           | _ => false)
      | sameExpW (Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
		  Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
         (r1 = r2) andalso sameSub (s1, s2)
      | sameExpW _ = false

    (* sameExp ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1
       and  G |- s2 : G2    G2 |- U2 : V2
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    and sameExp (Us1, Us2) = sameExpW (Whnf.whnf Us1, Whnf.whnf Us2)

    (* sameSpine (S1, S2) = T

       Invariant:
       If   G |- S1 : V > W
       and  G |- S2 : V > W
       then T only if S1 = S2 (as spines)
    *)
    and sameSpine ((Nil, s1), (Nil, s2)) = true
      | sameSpine ((SClo (S1, s1'), s1), Ss2) =
          sameSpine ((S1, comp (s1', s1)), Ss2)
      | sameSpine (Ss1, (SClo (S2, s2'), s2)) =
          sameSpine (Ss1, (S2, comp (s2', s2)))
      | sameSpine ((App (U1, S1), s1), (App (U2, S2), s2)) =
          sameExp ((U1, s1), (U2, s2))
            andalso sameSpine ((S1, s1), (S2, s2))
      | sameSpine _ = false

    (* sameSub (s1, s2) = T

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then T only if s1 = s2 (as substitutions)
    *)
    and sameSub (Shift _, Shift _) = true
      | sameSub (Dot (Idx (k1), s1), Dot (Idx (k2), s2)) =
          (k1 = k2) andalso sameSub (s1, s2)
      | sameSub (s1 as Dot (Idx _, _), Shift (k2)) =
          sameSub (s1, Dot (Idx (Int.+(k2,1)), Shift (Int.+(k2,1))))
      | sameSub (Shift (k1), s2 as Dot (Idx _, _)) =
          sameSub (Dot (Idx (Int.+(k1,1)), Shift (Int.+(k1,1))), s2)
      | sameSub _ = false

    (* plusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 + sum2
    *)
    fun plusSum (Sum (m1, nil), Sum (m2, monL2)) =
          Sum (m1 + m2, monL2)
      | plusSum (Sum (m1, monL1), Sum (m2, nil)) =
          Sum (m1 + m2, monL1)
      | plusSum (Sum (m1, mon1 :: monL1), Sum (m2, monL2)) =
          plusSumMon (plusSum (Sum (m1, monL1), Sum (m2, monL2)), mon1)

    (* plusSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 + mon2
    *)
    and plusSumMon (Sum (m, nil), mon) = Sum (m, [mon])
      | plusSumMon (Sum (m, monL), mon as Mon (n, UsL)) =
          (case (findMSet compatibleMon (mon, monL))
             of SOME (Mon (n', _), monL') =>
                  let
                    val n'' = n + n'
                  in
                    if (n'' = zero) then Sum (m, monL')
                    else Sum (m, (Mon (n'', UsL)) :: monL')
                  end
              | NONE =>
                  Sum (m, mon :: monL))

    (* timesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 * sum2
    *)
    fun timesSum (Sum (m1, nil), Sum (m2, nil)) =
          Sum (m1 * m2, nil)
      | timesSum (Sum (m1, mon1 :: monL1), sum2) =
          plusSum (timesSumMon (sum2, mon1), timesSum (Sum (m1, monL1), sum2))
      | timesSum (sum1, Sum (m2, mon2 :: monL2)) =
          plusSum (timesSumMon (sum1, mon2), timesSum (sum1, Sum (m2, monL2)))

    (* timesSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 * mon2
    *)
    and timesSumMon (Sum (m, nil), Mon (n, UsL)) =
          let
            val n' = m * n
          in
            if (n' = zero) then Sum (n', nil)
            else Sum (zero, [Mon (n', UsL)])
          end
      | timesSumMon (Sum (m, (Mon (n', UsL')) :: monL), mon as Mon (n, UsL)) =
          let
            val n'' = n * n'
            val UsL'' = UsL @ UsL'
            val Sum (m', monL') = timesSumMon (Sum (m, monL), mon)
          in
            Sum (m', (Mon (n'', UsL'')) :: monL')
          end

    (* unaryMinusSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = ~1 * sum
    *)
    fun unaryMinusSum (sum) =
          timesSum (Sum (~one, nil), sum)

    (* minusSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 - sum2
    *)
    fun minusSum (sum1, sum2) =
          plusSum (sum1, unaryMinusSum (sum2))

    (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
    fun fromExpW (Us as (FgnExp (cs, fe), _)) =
          if (cs = !myID)
          then normalizeSum (extractSum fe)
          else Sum (zero, [Mon (one, [Us])])
      | fromExpW (Us as (Root (FgnConst (cs, conDec), _), _)) =
          if (cs = !myID)
          then (case (fromString (conDecName (conDec)))
                  of SOME(m) => Sum (m, nil))
          else Sum (zero, [Mon (one, [Us])])
      | fromExpW (Us as (Root (Def(d), _), _)) =
          fromExpW (Whnf.expandDef (Us))
      | fromExpW Us =
          Sum (zero, [Mon (one, [Us])])

    (* fromExp (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
    and fromExp Us =
          fromExpW (Whnf.whnf Us)

    (* normalizeSum sum = sum', where sum' normal and sum' = sum *)
    and normalizeSum (sum as (Sum (m, nil))) = sum
      | normalizeSum (Sum (m, [mon])) =
          plusSum (Sum (m, nil), normalizeMon mon)
      | normalizeSum (Sum (m, mon :: monL)) =
          plusSum (normalizeMon mon, normalizeSum (Sum (m, monL)))

    (* normalizeMon mon = mon', where mon' normal and mon' = mon *)
    and normalizeMon (mon as (Mon (n, nil))) = Sum (n, nil)
      | normalizeMon (Mon (n, [Us])) =
          timesSum (Sum (n, nil), fromExp Us)
      | normalizeMon (mon as (Mon (n, Us :: UsL))) =
          timesSum (fromExp Us, normalizeMon (Mon (n, UsL)))

    (* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)
    and mapSum (f, Sum (m, monL)) =
          Sum (m, List.map (fn mon => mapMon (f, mon)) monL)
    
    (* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *)
    and mapMon (f, Mon (n, UsL)) =
          Mon (n, List.map (fn Us => Whnf.whnf (f (EClo Us), id)) UsL)

    (* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for each i *)
    fun appSum (f, Sum (m, monL)) =
	List.app (fn mon => appMon (f, mon)) monL

    (* appMon (f, n * (U1, s1) + ... ) = () and f (Ui[si]) for each i *)
    and appMon (f, Mon (n, UsL)) =
	List.app (fn Us => f (EClo Us)) UsL

    (* findMon f (G, sum) =
         SOME(x) if f(M) = SOME(x) for some monomial M in sum
         NONE    if f(M) = NONE for all monomials M in sum
    *)
    fun findMon f (G, Sum(m, monL)) =
          let
            fun findMon' (nil, monL2) = NONE
              | findMon' (mon :: monL1, monL2) =
                  (case (f (G, mon, Sum(m, monL1 @ monL2)))
                     of (result as SOME _) => result
                      | NONE => findMon' (monL1, mon :: monL2))
          in
            findMon' (monL, nil)
          end

    (* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)
    fun unifySum (G, sum1, sum2) =
          let
            fun invertMon (G, Mon (n, [(LHS as EVar (r, _, _, _), s)]), sum) =
                  if Whnf.isPatSub s
                  then
                    let
                      val ss = Whnf.invert s
                      val RHS = toFgn (timesSum (Sum (~ (inverse n), nil),
                                                 sum))
                    in
                      if Unify.invertible (G, (RHS, id), ss, r)
                      then SOME (G, LHS, RHS, ss)
                      else NONE
                    end
                  else NONE
              | invertMon _ = NONE
          in
            case minusSum (sum2, sum1)
              of Sum (m, nil) => if (m = zero) then Succeed nil else Fail
               | sum => 
                  (
                    case findMon invertMon (G, sum)
                      of SOME assignment => 
                           Succeed [Assign assignment]
                       | NONE => 
                           let
                             val U = toFgn sum
                             val cnstr = ref (Eqn (G, U, numberExp (zero)))
                           in 
                             Succeed [Delay (U, cnstr)]
                           end
                  )
          end   

    (* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
    and toFgn (sum as Sum (m, nil)) = toExp (sum)
      | toFgn (sum as Sum (m, monL)) = FgnExp (!myID, MyIntsynRep sum)

    (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then U is the Twelf syntax conversion of sum
    *)
    fun toInternal (MyIntsynRep sum) () = toExp (normalizeSum sum)
      | toInternal fe () = raise (UnexpectedFgnExp fe)

    (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep sum)   sum : normal
       and
         f sum = f (m + mon1 + ... + monN) =
               = m + f (m1 * Us1 * ... * UsM) + ...
               = m + (m1 * (f Us1) * ... * f (UsM))
               = sum'           sum' : normal
       then
         U' is a foreign expression representing sum'
    *)
    fun map (MyIntsynRep sum) f = toFgn (normalizeSum (mapSum (f,sum)))
      | map fe _ = raise (UnexpectedFgnExp fe)

    (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep sum)     sum : normal
       and
          sum = m + mon1 + ... monN
          where moni = mi * Usi1 * ... UsiMi
       then f is applied to each Usij
         (since sum : normal, each Usij is in whnf)
    *)
    fun app (MyIntsynRep sum) f = appSum (f, sum)
      | app fe _ = raise (UnexpectedFgnExp fe)

    fun equalTo (MyIntsynRep sum) U2 = 
	(case minusSum (normalizeSum sum, (fromExp (U2, id))) 
          of Sum(m, nil) => (m = zero) 
           | _ => false)
      | equalTo fe _ = raise (UnexpectedFgnExp fe)

    fun unifyWith (MyIntsynRep sum) (G, U2) = unifySum (G, normalizeSum sum, (fromExp (U2, id)))
      | unifyWith fe _ = raise (UnexpectedFgnExp fe)

    fun installFgnExpOps () = let
	val csid = !myID
	val _ = FgnExpStd.ToInternal.install (csid, toInternal)
	val _ = FgnExpStd.Map.install (csid, map)
	val _ = FgnExpStd.App.install (csid, app)
	val _ = FgnExpStd.UnifyWith.install (csid, unifyWith)
	val _ = FgnExpStd.EqualTo.install (csid, equalTo)
    in
	()
    end


    fun makeFgn (arity, opExp) (S) =
          let
            fun makeParams 0 = Nil
              | makeParams n =
                  App (Root(BVar (Fixed n), Nil), makeParams (Int.-(n,1)))
            fun makeLam E 0 = E
              | makeLam E n = 
                  Lam (Dec (NONE, number()), makeLam E (Int.-(n,1)))
            fun expand ((Nil, s), arity) =
                  (makeParams arity, arity)
              | expand ((App (U, S), s), arity) =
                  let
                    val (S', arity') = expand ((S, s), (Int.-(arity,1)))
                  in
                    (App (EClo (U, comp (s, Shift (arity'))), S'), arity')
                  end 
              | expand ((SClo (S, s'), s), arity) =
                  expand ((S, comp (s', s)), arity)
            val (S', arity') = expand ((S, id), arity)
          in
            makeLam (toFgn (opExp S')) arity'
          end

    fun makeFgnUnary opSum =
          makeFgn (1,
            fn (App (U, Nil)) =>
               opSum (fromExp (U, id)))

    fun makeFgnBinary opSum =
          makeFgn (2, 
            fn (App (U1, App (U2, Nil))) =>
              opSum (fromExp (U1, id), fromExp (U2, id)))

    fun arrow (U, V) = Pi ((Dec (NONE, U), No), V)

    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
    fun init (cs, installF) =
          (
            myID := cs;

            numberID := 
              installF (ConDec (Field.name, NONE, 0,
                                Constraint (!myID, solveNumber),
                                Uni (Type), Kind),
                        NONE, [MS.Mnil]);

            unaryMinusID :=
              installF (ConDec ("~", NONE, 0,
                                Foreign (!myID, makeFgnUnary unaryMinusSum),
                                arrow (number (), number ()),
                                Type),
                        SOME(FX.Prefix (FX.maxPrec)),
                        nil);

            plusID :=
              installF (ConDec ("+", NONE, 0,
                                Foreign (!myID, makeFgnBinary plusSum),
                                arrow (number (), arrow (number (), number ())),
                                Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        nil);

            minusID :=
              installF (ConDec ("-", NONE, 0,
                                  Foreign (!myID, makeFgnBinary minusSum),
                                  arrow (number (),
                                         arrow (number (), number ())),
                                  Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        nil);

            timesID :=
              installF (ConDec ("*", NONE, 0,
                                  Foreign (!myID, makeFgnBinary timesSum),
                                  arrow (number (),
                                         arrow (number (), number ())),
                                  Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        nil);

	    installFgnExpOps () ;

            ()
          )
  in
    val solver =
          {
            name = ("equality/" ^ Field.name ^ "s"),
            keywords = "arithmetic,equality",
            needs = ["Unify"],

            fgnConst = SOME({parse = parseNumber}),

            init = init,

            reset  = (fn () => ()),
            mark   = (fn () => ()),
            unwind = (fn () => ())
          }

    val fromExp = fromExp
    val toExp = toExp
    val normalize = normalizeSum

    val compatibleMon = compatibleMon

    val number = number
    
    fun unaryMinus U = toFgn (unaryMinusSum (fromExp (U, id)))
    fun plus (U, V) = toFgn (plusSum (fromExp (U ,id), fromExp (V, id)))
    fun minus (U, V) = toFgn (minusSum (fromExp (U, id), fromExp (V, id)))
    fun times (U, V) = toFgn (timesSum (fromExp (U, id), fromExp (V, id)))

    val constant = numberExp
  end (* local *)
end  (* functor CSEqField *)
