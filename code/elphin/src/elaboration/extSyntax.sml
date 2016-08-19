(* Nabla Internal Syntax *)
(* Author: Adam Poswolsky *)

structure NablaExtSyntax = 

struct

datatype TopDec 
    = LFTypeConstant of Paths.region * string (* id : type *)
    | LFObjectConstant of Paths.region * LFDec * (Infix option)

    (* changed it to take a list, since all functions are mutually recursive *)
    (* Parser will still just parse it as one element list
     * and will be merged together in nabla.fun
     *)
    | MetaFix of (Paths.region * MetaDec * MetaTerm) list
    | MetaVal of Paths.region * MetaTerm (* it = ... *)
    | Use of string

and LFDec 
  = LFDec of Paths.region * string * LFType

(* Note that both the declaration of type constants and 
 * objects of specific types are mixed together
 *)
and LFType
  = TypeConstant of Paths.region * string
  | RtArrow of Paths.region * LFType * LFType
  | LtArrow of Paths.region * LFType * LFType
  | And of Paths.region * LFType * LFType
  | UnitType of Paths.region
  | Omit of Paths.region

and LFTerm 
  = ObjectConstant of Paths.region * string
  | Unit of Paths.region
  | Fn of Paths.region * LFDec * LFTerm
  | App of Paths.region * LFTerm * LFTerm
  | Pair of Paths.region * LFTerm * LFTerm
  | First of Paths.region * LFTerm
  | Second of Paths.region * LFTerm
  | Of of Paths.region * LFTerm * LFType
  | Paren of Paths.region * LFTerm (* So we pass the infix stuff to Twelf *)

and Infix
  = INFIXL of Paths.region * int
  | INFIXR of Paths.region * int
  | NONASSOC of Paths.region * int

and MetaDec 
  = MetaDec of Paths.region * string * MetaType

and MetaType
  = LFinsideType of Paths.region * LFType
  | Box of Paths.region * MetaType
  | MetaArrow of Paths.region * MetaType * MetaType
  | MetaAnd of Paths.region * MetaType * MetaType
  | MetaOmit of Paths.region

and MetaTerm 
  = MetaID of Paths.region * string
  | Fail of Paths.region
  | LFinside of Paths.region * LFTerm
  | Pop of Paths.region * MetaTerm
  | PatMatch of Paths.region * MetaTerm * MetaTerm
  | MetaApp of Paths.region * MetaTerm * MetaTerm
  | MetaPair of Paths.region * MetaTerm * MetaTerm
  | Bar of Paths.region * MetaTerm * MetaTerm
  | New of Paths.region * LFDec * MetaTerm
  | Nabla of Paths.region * LFDec * MetaTerm
  | Eps of Paths.region * LFDec * MetaTerm
  | EpsM of Paths.region * MetaDec * MetaTerm
  | Fix of Paths.region * MetaDec * MetaTerm
  | MetaFirst of Paths.region * MetaTerm
  | MetaSecond of Paths.region * MetaTerm
  (* Syntactic Sugar *)
  | Let of Paths.region * MetaDec * MetaTerm * MetaTerm (* Will be interpreted as fix point *)
  | LetM of Paths.region * LFDec * MetaTerm * MetaTerm (* let <e> = ... *)

  | Case of Paths.region * MetaTerm * MetaTerm
  | AppInside of Paths.region * MetaTerm * MetaTerm
  | PairInside of Paths.region * MetaTerm * MetaTerm
  | Sequence of (Paths.region * MetaTerm) list

type NablaProgram = TopDec list


fun getRegMetaDec(MetaDec (r, _, _)) = r

fun getRegMetaType(LFinsideType (r, _)) = r
  | getRegMetaType(Box (r, _)) = r
  | getRegMetaType(MetaArrow (r, _, _)) = r
  | getRegMetaType(MetaAnd (r, _, _)) = r
  | getRegMetaType(MetaOmit r) = r

fun getRegL [(r,_)] = r
  | getRegL ((r,_)::xs) = Paths.join(r, getRegL xs) 
  | getRegL _ = raise Domain

fun getRegMetaTerm (MetaID (r, _)) = r
  | getRegMetaTerm (Fail (r)) = r
  | getRegMetaTerm (LFinside(r,_)) = r
  | getRegMetaTerm (Pop(r,_)) = r
  | getRegMetaTerm (PatMatch(r,_,_)) = r
  | getRegMetaTerm (MetaApp(r,_,_)) = r
  | getRegMetaTerm (MetaPair(r,_,_)) = r
  | getRegMetaTerm (Bar(r,_,_)) = r
  | getRegMetaTerm (New(r,_,_)) = r
  | getRegMetaTerm (Nabla(r,_,_)) = r
  | getRegMetaTerm (Eps(r,_,_)) = r
  | getRegMetaTerm (EpsM(r,_,_)) = r
  | getRegMetaTerm (Fix(r,_,_)) = r
  | getRegMetaTerm (MetaFirst(r,_)) = r
  | getRegMetaTerm (MetaSecond(r,_)) = r
  | getRegMetaTerm (Let(r,_,_,_)) = r
  | getRegMetaTerm (LetM(r,_,_,_)) = r
  | getRegMetaTerm (Case(r,_,_)) = r
  | getRegMetaTerm (AppInside(r,_,_)) = r
  | getRegMetaTerm (PairInside(r,_,_)) = r
  | getRegMetaTerm (Sequence(l)) = getRegL l



fun getRegLFType(TypeConstant(r,_)) = r
  | getRegLFType(RtArrow(r,_,_)) = r
  | getRegLFType(LtArrow(r,_,_)) = r
  | getRegLFType(And(r,_,_)) = r
  | getRegLFType(UnitType r) = r
  | getRegLFType(Omit r) = r


fun getRegLFTerm(ObjectConstant(r,_)) = r
  | getRegLFTerm(Unit r) = r
  | getRegLFTerm(Fn(r,_,_)) = r
  | getRegLFTerm(App(r,_,_)) = r
  | getRegLFTerm(Pair(r,_,_)) = r
  | getRegLFTerm(First(r,_)) = r
  | getRegLFTerm(Second(r,_)) = r
  | getRegLFTerm(Of(r,_,_)) = r
  | getRegLFTerm(Paren(r,_)) = r


end (* structure NablaExtSyntax *)