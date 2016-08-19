(* 
 * Used to print Nabla External Syntax 
 * solely for Parser debugging use 
 * Author:  Adam Poswolsky
 *)
structure PrintNablaExt =
  struct

    structure N = NablaExtSyntax

    fun nablaToStr [] = ""
      | nablaToStr (x::xs) = topDecStr(x) ^ "\n\n" ^ nablaToStr(xs)

    and topDecStr (N.LFTypeConstant (r,s)) = "<" ^ s ^ " : type>"
      | topDecStr (N.LFObjectConstant (r, lfdec, infixopt)) = "<" ^ lfdecStr(lfdec) ^ infixOptStr(infixopt) ^ ">"
      | topDecStr (N.MetaFix []) = ""
      | topDecStr (N.MetaFix ((_, d, t)::xs)) = "fix " ^ metadecStr(d) ^ "\n = " ^ metaStr(t) ^ "\n\n" ^ topDecStr(N.MetaFix xs)
      | topDecStr (N.MetaVal (_, t)) = "it = \n = " ^ metaStr(t) 
      | topDecStr (N.Use s) = "use " ^ s ^ ";\n\n"

    and lfdecStr (N.LFDec (_,s,l)) = s ^ " : " ^ lftypeStr(l)

    and lftypeStr (N.TypeConstant (_,s)) = s
      | lftypeStr (N.RtArrow (_,l1,l2)) = "(" ^ lftypeStr(l1) ^ " -> " ^ lftypeStr(l2) ^ ")"
      | lftypeStr (N.LtArrow (_,l1,l2)) = "(" ^ lftypeStr(l1) ^ " <- " ^ lftypeStr(l2) ^ ")"
      | lftypeStr (N.And(_,l1,l2)) = "(" ^ lftypeStr(l1) ^ " * " ^ lftypeStr(l2) ^ ")"
      | lftypeStr (N.UnitType _) = "unit"
      | lftypeStr (N.Omit _) = "_"


    and lftermStr (N.ObjectConstant (_,s)) = s
      | lftermStr (N.Unit _) = ""
      | lftermStr (N.Fn (_, d, t)) = "[" ^ lfdecStr(d) ^ "]" ^ lftermStr(t)
      | lftermStr (N.App (_, t1, t2)) = lftermStr(t1) ^ " " ^ lftermStr(t2)
      | lftermStr (N.Pair (_, t1, t2)) = lftermStr(t1) ^ "," ^ lftermStr(t2) 
      | lftermStr (N.First (_,t)) = "first " ^ lftermStr(t)
      | lftermStr (N.Second (_,t)) = "second " ^ lftermStr(t)
      | lftermStr (N.Of(_, l, t)) = lftermStr(l) ^ " : " ^ lftypeStr(t)
      | lftermStr (N.Paren (_,t)) = "(" ^ lftermStr(t) ^ ")"

    and infixOptStr NONE = ""
      | infixOptStr (SOME (N.INFIXL (_,n))) = "(*INFIX LEFT " ^ Int.toString(n) ^ "*)"
      | infixOptStr (SOME (N.INFIXR (_,n))) = "(*INFIX RIGHT " ^ Int.toString(n) ^ "*)"
      | infixOptStr (SOME (N.NONASSOC (_,n))) = "(*INFIX " ^ Int.toString(n) ^ "*)"

    and metadecStr(N.MetaDec(_, s, t)) = "(" ^ s ^ " : " ^ metatypeStr(t) ^ ")"

    and metatypeStr (N.LFinsideType (_,l)) = "(" ^ "<" ^ lftypeStr(l) ^ ">" ^ ")"
      | metatypeStr (N.Box (_,t)) = "(" ^ "[]" ^ metatypeStr(t) ^ ")"
      | metatypeStr (N.MetaArrow (_, t1, t2)) = "(" ^ metatypeStr(t1) ^ " -> " ^ metatypeStr(t2) ^")"
      | metatypeStr (N.MetaAnd (_, t1, t2)) = "(" ^ metatypeStr(t1) ^ " * " ^ metatypeStr(t2) ^")"
      | metatypeStr (N.MetaOmit _) = "_"

    and metaStr (N.MetaID (r,s)) = s
      | metaStr (N.LFinside (r,l)) = "<" ^ lftermStr(l) ^ ">"
      | metaStr (N.Fail (r)) = "fail"
      | metaStr (N.Pop (_,t)) = "(" ^ "pop " ^ metaStr(t) ^ ")"
      | metaStr (N.PatMatch (_, t1,t2)) = "(" ^ metaStr(t1) ^ " |--> " ^ metaStr(t2) ^ ")"
      | metaStr (N.MetaApp (_, t1, t2)) = "(" ^ metaStr(t1) ^ " " ^ metaStr(t2) ^ ")"
      | metaStr (N.MetaPair (_, t1, t2)) = "(" ^ metaStr(t1) ^ "," ^ metaStr(t2) ^ ")"
      | metaStr (N.Bar (_, t1,t2)) = "(" ^ metaStr(t1) ^ "\n | " ^ metaStr(t2) ^ ")"
      | metaStr (N.New (_, d, t)) = "(" ^ "{" ^ lfdecStr(d) ^ "}" ^ metaStr(t) ^ ")"
      | metaStr (N.Nabla (_, d, t)) = "(" ^ "{{" ^ lfdecStr(d) ^ "}}" ^ metaStr(t) ^ ")"
      | metaStr (N.Eps (r, d, t)) = "(" ^ "[" ^ lfdecStr(d) ^ "]" ^ metaStr(t) ^ ")"
      | metaStr (N.EpsM (_, d, t)) = "(" ^ "[" ^ metadecStr(d) ^ "]" ^ metaStr(t) ^ ")"
      | metaStr (N.Fix (_, d, t)) = "fix " ^ metadecStr(d) ^ "\n = " ^ metaStr(t) 
      | metaStr (N.MetaFirst (_, t)) = "first " ^ metaStr(t) 
      | metaStr (N.MetaSecond (_, t)) = "second " ^ metaStr(t) 
      (* Syntactic Sugar *)
      | metaStr (N.Let (_, d1, t1, t2)) = "(" ^ "let " ^ metadecStr(d1) ^ " = " ^ metaStr(t1) ^ " in\n " ^ metaStr(t2) ^ ")"
      | metaStr (N.LetM (_, l, t1, t2)) = "(" ^ "let <" ^ lfdecStr(l) ^ "> = " ^ metaStr(t1) ^ " in\n " ^ metaStr(t2) ^ ")"
      | metaStr (N.Case (_, t1, t2)) = "(" ^ "case " ^ metaStr(t1) ^ " of " ^ metaStr(t2) ^ ")"
      | metaStr (N.AppInside (_, t1, t2)) = "(" ^ metaStr(t1) ^ " @ " ^ metaStr(t2) ^ ")"
      | metaStr (N.PairInside (_, t1, t2)) = "(" ^ metaStr(t1) ^ " & " ^ metaStr(t2) ^ ")"
      | metaStr (N.Sequence ((_,t1)::seqL)) = "(" ^ metaStr(t1) ^ metaStrSeqL(seqL) ^ ")"
      | metaStr _ = raise Domain
     
    and metaStrSeqL [] = ""
      | metaStrSeqL ((_,x)::xs) = "; " ^ metaStr(x) ^ metaStrSeqL(xs)


  end