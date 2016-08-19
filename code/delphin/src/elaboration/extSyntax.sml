(* Delphin External Syntax *)
(* Author: Adam Poswolsky *)

structure DelphinExtSyntax = 
struct

datatype Visibility
    = Implicit
    | Visible

datatype TopDec
    = LFTypeConstant of Paths.region * string * Kind * (Name option) * (Prec option) (* i.e. a : K *)
    | LFObjectConstant of Paths.region * LFDec * (Prec option)
    | LFDefinition of Paths.region * LFDec * LFTerm * bool * (Prec option)
                                                            (* true if it is an abbreviation,
						              false if it is a definition
						            *)
    | TypeDefinition of Paths.region * string * Formula
    | MetaFix of (Paths.region * NormalDec * Exp) list
    | MetaVal of Paths.region * (string option) * Exp (* it = ... *)
    | Use of string
    | LFUse of string

and Kind
  = Type of Paths.region
  | PiKind of Paths.region * LFDec * Kind

and LFDec 
  = LFDec of Paths.region * (string option) * LFType


and LFType
  = TypeID of Paths.region * string
  | TypeApp of Paths.region * LFType * LFTerm
  | PiType of Paths.region * LFDec * LFType
  | RtArrow of Paths.region * LFType * LFType
  | LtArrow of Paths.region * LFType * LFType
  | OmitType of Paths.region
  | ParenType of Paths.region * LFType (* keep track of parenthesis for infix operators *)
  | ExplicitLFType of Formatter.format (* used only for printing internal syntax *)

and LFTerm 
  = ObjectID of Paths.region * bool * string (* bool is true when it is a parameter X# .. only makes sense in pattern *)
  | Fn of Paths.region * LFDec * LFTerm
  | LFApp of Paths.region * LFTerm * LFTerm
  | Of of Paths.region * LFTerm * LFType
  | OmitTerm of Paths.region
  | ParenTerm of Paths.region  * LFTerm (* keep track of parenthesis for infix operators 
					 * for instance
					 * (A ar B) ar C 
					 * here "ar" is an infix operator, but if we don't save parenthesis it is saved as
					 * LFApp(LFApp(LFApp(LFApp(A,ar), B),ar), C)
					 * which would just be converted to
					 * A ar B ar C  as application is left-associative
					 *)
  | ExplicitLFTerm of Formatter.format (* used only for printing internal syntax *)

and Prec
  = INFIXL of Paths.region * int
  | INFIXR of Paths.region * int
  | INFIXN of Paths.region * int
  | POSTFIX of Paths.region * int
  | PREFIX of Paths.region * int

and Name
  = OneName of Paths.region * string
  | TwoNames of Paths.region * string * string

and isParam
  = Existential
  | Param
  | OmittedParam

and Types
  = LF of Paths.region * isParam * LFType
  | Meta of Paths.region * isParam * Formula

and Formula
  = Top     of Paths.region
  | All     of Paths.region * Visibility * NormalDec * Formula
  | Exists  of Paths.region * NormalDec * Formula 
  | Nabla   of Paths.region * NewDec * Formula
  | FormulaString of Paths.region * string
  | OmittedFormula of Paths.region 


and NormalDec 
  = NormalDec of Paths.region * (string option) * Types

  
and NewDec 
  = NewDecLF of Paths.region * (string option) * LFType
  | NewDecMeta of Paths.region * (string option) * Formula

and Dec
  = InstantiableDec of Paths.region * NormalDec    
  | NonInstantiableDec of Paths.region * NewDec


and Exp
  = VarString   of Paths.region * string
  | VarInt      of Paths.region * int (* to aid in conversion, we allow debruijn indices *)
  | OmittedPat  of Paths.region
  | Quote       of Paths.region * LFTerm
  | Unit        of Paths.region
  | Lam         of Paths.region * (CaseBranch list)
  | New         of Paths.region * NewDec * Exp
  | App         of Paths.region * Exp * Exp
  | Pair        of Paths.region * Exp * Exp
  | Pop         of Paths.region * string * Exp
  | Fix         of Paths.region * (Paths.region * NormalDec * Exp) list
                     (* Not in use from the actual parser.. as embedded fixpoints are introduced with let.
	              * But it is useful to have  for converting internal syntax to external one *)

  (* Syntactic Sugar *)
  | TypeAscribe  of Paths.region * Exp * Types
  (* Removed due to dependencies
  | Fst of Paths.region * Exp
  | Snd of Paths.region * Exp
    *)
  | Sequence    of (Paths.region * Exp) list
  | LiftedApp   of Paths.region * Exp * Exp
  (* OLD .. now we have more versatile let
  | LetVar      of Paths.region * NormalDec * Exp * Exp
   *)
  | LetVar      of Paths.region * Exp (* pattern *) * Exp * Exp
  | LetFun      of Paths.region * (Paths.region * NormalDec * Exp) list * Exp

  
               
and CaseBranch
    = Eps of Paths.region * NormalDec * CaseBranch
    | NewC of Paths.region * NewDec * CaseBranch
    | PopC of Paths.region * string * CaseBranch
    | Match of Paths.region * Exp * Exp (* pattern => result *)
    | MatchAnd of Paths.region * Exp * CaseBranch (* pattern => case *)




type DelphinProgram = TopDec list


(* Functions to extract region information *)
fun getRegL [(r,_)] = r
  | getRegL ((r,_)::xs) = Paths.join(r, getRegL xs) 
  | getRegL _ = raise Domain

fun getRegKind (Type r) = r
  | getRegKind (PiKind (r,_,_)) = r

fun getRegLFType(TypeID(r,_)) = r
  | getRegLFType(TypeApp(r,_,_)) = r
  | getRegLFType(PiType(r,_,_)) = r
  | getRegLFType(RtArrow(r,_,_)) = r
  | getRegLFType(LtArrow(r,_,_)) = r
  | getRegLFType(OmitType r) = r
  | getRegLFType(ParenType (r, _)) = r
  | getRegLFType(ExplicitLFType _) = raise Domain (* should not be parsed *)


fun getRegLFTerm(ObjectID(r,_, _)) = r
  | getRegLFTerm(Fn(r,_,_)) = r
  | getRegLFTerm(LFApp(r,_,_)) = r
  | getRegLFTerm(Of(r,_,_)) = r
  | getRegLFTerm(OmitTerm r) = r
  | getRegLFTerm(ParenTerm (r, _)) = r
  | getRegLFTerm(ExplicitLFTerm _) = raise Domain (* should not be parsed *)


fun getRegTypes (LF (r,_, _)) = r
  | getRegTypes (Meta (r,_,_)) = r

fun getRegFormula (Top r) = r
  | getRegFormula (All (r,_,_,_)) = r
  | getRegFormula (Exists (r,_,_)) = r
  | getRegFormula (Nabla (r,_,_)) = r
  | getRegFormula (FormulaString (r,_)) = r
  | getRegFormula (OmittedFormula r) = r

fun getRegLFDec (LFDec(r, _, _)) = r

fun getRegDec (InstantiableDec (r, _)) = r
  | getRegDec (NonInstantiableDec (r, _)) = r

fun getRegExp (VarString (r, _)) = r
  | getRegExp (VarInt (r, _)) = r
  | getRegExp (OmittedPat r) = r
  | getRegExp (Quote (r, _)) = r
  | getRegExp (Unit r) = r
  | getRegExp (Lam (r, _)) = r
  | getRegExp (New (r, _, _)) = r
  | getRegExp (App (r, _, _)) = r
  | getRegExp (Pair (r, _, _)) = r
  | getRegExp (Pop (r, _, _)) = r
  | getRegExp (Fix (r, _)) = r
  | getRegExp (TypeAscribe (r, _, _)) = r
  (* Removed due to dependencies
  | getRegExp (Fst (r, _)) = r
  | getRegExp (Snd (r, _)) = r
    *)
  | getRegExp (Sequence l) = getRegL l
  | getRegExp (LiftedApp (r, _, _)) = r
  | getRegExp (LetVar (r, _, _, _)) = r
  | getRegExp (LetFun (r, _, _)) = r

fun getRegCaseBranch (Eps (r, _, _)) = r
  | getRegCaseBranch (NewC (r, _, _)) = r
  | getRegCaseBranch (PopC (r, _, _)) = r
  | getRegCaseBranch (Match (r, _, _)) = r
  | getRegCaseBranch (MatchAnd (r, _, _)) = r


fun getRegNormalDec (NormalDec (r, _ , _)) = r
fun getRegNewDec (NewDecLF (r, _, _)) = r
  | getRegNewDec (NewDecMeta (r, _, _)) = r

end (* structure DelphinExtSyntax *)