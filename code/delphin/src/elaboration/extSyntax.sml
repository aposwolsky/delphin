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
    | LFDef            of Paths.region * LFDec * LFExp * bool * (Prec option)
                                                            (* true if it is an abbreviation,
						              false if it is a definition
						            *)
    | TypeDef           of Paths.region * string * Formula
    | MetaFix of (Paths.region * NormalDec * Exp) list
    | MetaVal of Paths.region * (string option) * Exp (* it = ... *)
    | Use of string
    | LFUse of string
    | WorldDec of WorldDeclaration

and WorldDeclaration 
    = Anything
    | Variables of LFExpWorld list

and Kind
  = Type of Paths.region
  | PiKind of Paths.region * LFDec * Kind

and LFDec 
  = LFDec of Paths.region * (string option) * LFExp

and LFExp
  = LFid of Paths.region * bool * string (* bool is true when it is a param *)
  | LFapp of Paths.region * LFExp * LFExp
  | LFpi of Paths.region * LFDec * LFExp
  | LFrtArrow of Paths.region * LFExp * LFExp
  | LFltArrow of Paths.region * LFExp * LFExp
  | LFfn of Paths.region * LFDec * LFExp
  | LFof of Paths.region * LFExp * LFExp
  | LFomit of Paths.region
  | LFparen of Paths.region * LFExp (* keep track of parenthesis for infix operators *)
  | ExplicitLF of Formatter.format (* used only for printing internal syntax *)
                                   (* for instance    (A ar B) ar C          *)

and LFExpWorld 
  = WorldEps of Paths.region * NormalDec * LFExpWorld
  | WorldType of LFExp


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
  = LF of Paths.region * isParam * LFExp
  | Meta of Paths.region * Formula (* Existential *)

and Formula
  = Top     of Paths.region
  | All     of Paths.region * ((Visibility * NormalDec) list) * Formula
  | Exists  of Paths.region * NormalDec * Formula 
  | Nabla   of Paths.region * NewDec * Formula
  | FormulaString of Paths.region * string
  | OmittedFormula of Paths.region 


and NormalDec 
  = NormalDec of Paths.region * (string option) * Types

  
and NewDec 
  = NewDecLF of Paths.region * (string option) * LFExp
  (* Not available to the programmer...
    | NewDecWorld of Paths.region * (string option) * WorldDeclaration
    *)

and Dec
  = InstantiableDec of Paths.region * NormalDec    
  | NonInstantiableDec of Paths.region * NewDec


and Exp
  = VarString   of Paths.region * string
  | Quote       of Paths.region * LFExp
  | Unit        of Paths.region
  | Lam         of Paths.region * (CaseBranch list)
  | New         of Paths.region * NewDec * Exp
  | App         of Paths.region * Exp * (Exp list)
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
  | LetVar      of Paths.region * PatternExp * Exp * Exp
  | LetFun      of Paths.region * (Paths.region * NormalDec * Exp) list * Exp
  | ExtendFun   of Paths.region * Exp * (CaseBranch list)

and PatternExp
  = PatternString of Paths.region * string
  | PatternOmitted of Paths.region
  | PatternQuote of Paths.region * LFExp
  | PatternUnit of Paths.region
  | PatternPair of Paths.region * PatternExp * PatternExp
  | PatternNew of Paths.region * NewDec * PatternExp
  | PatternPop of Paths.region * string * PatternExp
  | PatternAscribe of Paths.region * PatternExp * Types

  
               
and CaseBranch
    = Eps of Paths.region * NormalDec * CaseBranch
    | NewC of Paths.region * NewDec * CaseBranch
    | PopC of Paths.region * string * CaseBranch
    | Match of bool * Paths.region * (PatternExp list) * Exp (* patterns => result *)
         (* bool is true if it is really syntactic sugar 
	  * otherwise, it is false. *)
                 (* i.e. fn A B C => E
		          | A' B' C' => E'
		  * is syntactic sugar for fn X1 => fn X2 => fn X3 => case (X1 and X2 and X3)
		                                                         of A and B and C => E
									  | A' and B' and C' => E'
		   ** List should always have size >=2 if bool is true
		  *)




type DelphinProgram = TopDec list


(* Functions to extract region information *)
fun getRegL [(r,_)] = r
  | getRegL ((r,_)::xs) = Paths.join(r, getRegL xs) 
  | getRegL _ = raise Domain

fun getRegKind (Type r) = r
  | getRegKind (PiKind (r,_,_)) = r

fun getRegLFExp(LFid (r, _, _)) = r
  | getRegLFExp(LFapp(r, _, _)) = r
  | getRegLFExp(LFpi (r, _, _)) = r
  | getRegLFExp(LFrtArrow (r, _, _)) = r
  | getRegLFExp(LFltArrow (r, _, _)) = r
  | getRegLFExp(LFfn (r, _, _)) = r
  | getRegLFExp(LFof (r, _, _)) = r
  | getRegLFExp(LFomit r) = r
  | getRegLFExp(LFparen (r, _)) = r
  | getRegLFExp(ExplicitLF _) = raise Domain (* should not be parsed *)

fun getRegLFExpWorld (WorldEps (r, _, _)) = r
  | getRegLFExpWorld (WorldType E) = getRegLFExp E



fun getRegTypes (LF (r,_, _)) = r
  | getRegTypes (Meta (r,_)) = r

fun getRegFormula (Top r) = r
  | getRegFormula (All (r,_,_)) = r
  | getRegFormula (Exists (r,_,_)) = r
  | getRegFormula (Nabla (r,_,_)) = r
  | getRegFormula (FormulaString (r,_)) = r
  | getRegFormula (OmittedFormula r) = r

fun getRegLFDec (LFDec(r, _, _)) = r

fun getRegDec (InstantiableDec (r, _)) = r
  | getRegDec (NonInstantiableDec (r, _)) = r

fun getRegExp (VarString (r, _)) = r
  (* | getRegExp (OmittedPat r) = r *)
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
  | getRegExp (ExtendFun (r, _, _)) = r

fun getRegCaseBranch (Eps (r, _, _)) = r
  | getRegCaseBranch (NewC (r, _, _)) = r
  | getRegCaseBranch (PopC (r, _, _)) = r
  | getRegCaseBranch (Match (_, r, _, _)) = r

fun getRegPatternExp(PatternString (r, _)) = r
  | getRegPatternExp(PatternOmitted r) = r
  | getRegPatternExp(PatternQuote (r, _)) = r
  | getRegPatternExp(PatternUnit r) = r
  | getRegPatternExp(PatternPair (r, _, _)) = r
  | getRegPatternExp(PatternNew (r, _, _)) = r
  | getRegPatternExp(PatternPop (r, _, _)) = r
  | getRegPatternExp(PatternAscribe (r, _, _)) = r


fun getRegNormalDec (NormalDec (r, _ , _)) = r
fun getRegNewDec (NewDecLF (r, _, _)) = r
  (* Not available any longer to programmer..
  | getRegNewDec (NewDecWorld (r, _, _)) = r
   *)

end (* structure DelphinExtSyntax *)