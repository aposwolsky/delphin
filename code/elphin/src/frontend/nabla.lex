(* Lexer for Nabla *)
(* Author:  Adam Poswolsky and Carsten Schuermann *)

structure Tokens = Tokens
structure Interface = Interface

type pos = Interface.pos

type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val numOpeningComments = ref 0 
val toPos = Interface.intToPos

(* The twelf printer for Regions will add 1 since it counts from 0
 * so this is to just adjust 
 *)
fun toReg(a,b) = Paths.Reg(a-1,b-1)

(*
 * This function is called when we hit EOF
 *)
fun eof () = 
    let 
	val pos = hd(!Interface.linePos) 
    in 
    (
     if (!numOpeningComments > 0) then
        Interface.error (("unclosed comment at eof."), pos, pos)
      else ()
      ;
      numOpeningComments := 0;
     (* If we reset, then the parser errors are messed up, it
        must be reset before not after.
      Interface.reset();
       *)
     Tokens.EOF(pos,pos))
    end


%% 

%s COMMENT INFIXPRAGMA;

%header (functor NablaLexFun(structure Tokens : Nabla_TOKENS
                               structure Interface : INTERFACE));

ws = [\t \ ];

uidenchar  =  [+*A-Za-z0-9!$/\^+'?"~];
uiden      = {uidenchar}+;
otheruidenhead = ("type" | "fst" | "snd" )+;
otheruiden = ({otheruidenhead}({uidenchar})+)
             | (
               (([-][^>\ \n\t]))
               )({uidenchar})*;

digits     = [0-9]+;
%%
<INITIAL,COMMENT,INFIXPRAGMA>{ws}+          
                                => (continue());
<INITIAL,COMMENT,INFIXPRAGMA>\n             
                                => (Paths.newLine(yypos) ; Interface.incLineNum(yypos); continue());
<INITIAL>("use")(" "+)("\"")(.+)("\"")
                                => (Tokens.USE(substring(yytext, 4, 
                                  size(yytext)-4), 
                                  toPos yypos, toPos(yypos + size(yytext)-1)));
<INITIAL>"(*INFIX"              => (YYBEGIN INFIXPRAGMA; continue());

<INFIXPRAGMA>"LEFT"             => (Tokens.INFIXL(toReg(yypos, yypos + 3), toPos yypos,toPos (yypos+3)));
<INFIXPRAGMA>"RIGHT"            => (Tokens.INFIXR(toReg(yypos, yypos + 4), toPos yypos,toPos (yypos+4)));
<INFIXPRAGMA>{digits}           => (Tokens.DIGITS((toReg(yypos, yypos + size(yytext)-1), valOf (Int.fromString(yytext))),
                                    toPos yypos,toPos (yypos + size(yytext)-1)));
<INFIXPRAGMA>.                  => (Interface.error ("ignoring bad character " ^ yytext, toPos yypos, toPos(yypos)); continue());
<INFIXPRAGMA>"*)"               => ( YYBEGIN INITIAL ; continue() );
<INITIAL>"(*"                   => (numOpeningComments := 1 ; 
                                    YYBEGIN COMMENT; 
                                    continue());
<COMMENT>"(*"                   => (numOpeningComments := !numOpeningComments + 1;
                                    continue());
<COMMENT>"*)"                   => (
                                    numOpeningComments := !numOpeningComments - 1;
                                    if (!numOpeningComments = 0) then 
                                      ( YYBEGIN INITIAL ; continue() )
                                    else
                                      continue()
                                   );
<COMMENT>.                      => (continue());
<INITIAL>{otheruiden}           => (Tokens.ID((toReg(yypos, yypos + size(yytext)-1), yytext),toPos yypos,toPos (yypos + size(yytext)-1)));
<INITIAL>"@"                    => (Tokens.AT(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"fail"                  => (Tokens.FAIL(toReg(yypos, yypos+4), toPos yypos,toPos (yypos+4)));
<INITIAL>"and"                  => (Tokens.FUNAND(toReg(yypos, yypos+2), toPos yypos,toPos (yypos+2)));
<INITIAL>"&"                    => (Tokens.AND(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"***"                  => (Tokens.TIMES(toReg(yypos, yypos+2), toPos yypos,toPos (yypos+2)));
<INITIAL>","                    => (Tokens.COMMA(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"->"                   => (Tokens.RTARROW(toReg(yypos, yypos + 1), toPos yypos, toPos(yypos+1)));
<INITIAL>"<-"                   => (Tokens.LTARROW(toReg(yypos, yypos + 1), toPos yypos, toPos(yypos+1)));
<INITIAL>"|-->"                 => (Tokens.MATCH(toReg(yypos, yypos + 3), toPos yypos, toPos(yypos+3)));
<INITIAL>":"                    => (Tokens.COLON(toReg(yypos, yypos), toPos yypos,toPos(yypos)));
<INITIAL>"="                    => (Tokens.EQUAL(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"|"                    => (Tokens.BAR(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"type"                 => (Tokens.TYPE(toReg(yypos, yypos + 3), toPos yypos, toPos(yypos +3)));
<INITIAL>";"                    => (Tokens.SEMICOLON(toReg(yypos, yypos), toPos yypos, toPos(yypos )));
<INITIAL>"fix"                  => (Tokens.FIX(toReg(yypos, yypos + 2), toPos yypos,toPos (yypos+2)));
<INITIAL>"fst"                  => (Tokens.FIRST(toReg(yypos, yypos + 2), toPos yypos,toPos (yypos+2)));
<INITIAL>"snd"                  => (Tokens.SECOND(toReg(yypos, yypos + 2), toPos yypos,toPos (yypos+2)));
<INITIAL>"unit"                 => (Tokens.UNIT_TYPE(toReg(yypos, yypos + 3), toPos yypos, toPos (yypos+3)));
<INITIAL>"case"                 => (Tokens.CASE(toReg(yypos, yypos + 3), toPos yypos,toPos (yypos+3)));
<INITIAL>"of"                   => (Tokens.OF(toReg(yypos, yypos + 1), toPos yypos,toPos (yypos+1)));
<INITIAL>"pop"                  => (Tokens.POP(toReg(yypos, yypos + 2), toPos yypos,toPos (yypos +2)));
<INITIAL>"let"                  => (Tokens.LET(toReg(yypos, yypos + 2), toPos yypos,toPos (yypos+2)));
<INITIAL>"in"                   => (Tokens.IN(toReg(yypos, yypos + 1), toPos yypos,toPos (yypos+1)));
<INITIAL>"<"                    => (Tokens.LTANGLE(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>">"                    => (Tokens.RTANGLE(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"("                    => (Tokens.LTPAREN(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>")"                    => (Tokens.RTPAREN(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"["                    => (Tokens.LTBRACKET(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"]"                    => (Tokens.RTBRACKET(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"{"                    => (Tokens.LTBRACE(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"}"                    => (Tokens.RTBRACE(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>"_"                    => (Tokens.UNDERSCORE(toReg(yypos, yypos), toPos yypos,toPos (yypos)));
<INITIAL>{uiden}                => (Tokens.ID((toReg(yypos, yypos + size(yytext)-1), yytext),toPos yypos,toPos (yypos+size(yytext)-1)));
<INITIAL>.                      => (Interface.error ("ignoring bad character " ^ yytext,
                                    toPos yypos, toPos (yypos)); continue());
