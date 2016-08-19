(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log: join.sml,v $
 * Revision 1.1  2007/03/30 13:20:00  adam-lf
 * Added Delphin Implementation to CVS
 *
 * Revision 1.1  2004/11/25 05:39:52  adam-lf
 * Changed Nabla to Delphin.  Checked in first version.
 *
 * Revision 1.1  2004/07/29 08:46:40  adam-lf
 * Checked in initial version
 *
 * Revision 1.1  2004/07/02 18:47:54  adam-lf
 * Checked in Parser
 *
 * Revision 1.2  2003/08/25 16:55:34  carsten_lf
 * Merged Version with tomega checked in
 *
 * Revision 1.1.2.1  2003/01/14 22:46:39  carsten_lf
 * delphin frontend added
 *
 * Revision 1.1  2001/11/12 23:23:09  carsten
 * mlyacc hack included
 *
 * Revision 1.1.1.1  1999/12/03 19:59:22  dbm
 * Import of 110.0.6 src
 *
 * Revision 1.1.1.1  1997/01/14 01:38:04  george
 *   Version 109.24
 *
 * Revision 1.1.1.1  1996/01/31  16:01:42  george
 * Version 109
 * 
 *)

(* functor Join creates a user parser by putting together a Lexer structure,
   an LrValues structure, and a polymorphic parser structure.  Note that
   the Lexer and LrValues structure must share the type pos (i.e. the type
   of line numbers), the type svalues for semantic values, and the type
   of tokens.
*)

functor Join(structure Lex : LEXERR
	     structure ParserData: PARSER_DATA
	     structure LrParser : LR_PARSER
	     sharing ParserData.LrTable = LrParser.LrTable
	     sharing ParserData.Token = LrParser.Token
	     sharing type Lex.UserDeclarations.svalue = ParserData.svalue
	     sharing type Lex.UserDeclarations.pos = ParserData.pos
	     sharing type Lex.UserDeclarations.token = ParserData.Token.token)
		 : PARSERR =
struct
    structure Token = ParserData.Token
    structure Streamm = LrParser.Streamm
 
    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue
    val makeLexer = LrParser.Streamm.streamify o Lex.makeLexer
    val parse = fn (lookahead,lexer,error,arg) =>
	(fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
	        lexer=lexer,
		lookahead=lookahead,
		saction = ParserData.Actions.actions,
		arg=arg,
		void= ParserData.Actions.void,
	        ec = {is_keyword = ParserData.EC.is_keyword,
		      noShift = ParserData.EC.noShift,
		      preferred_change = ParserData.EC.preferred_change,
		      errtermvalue = ParserData.EC.errtermvalue,
		      error=error,
		      showTerminal = ParserData.EC.showTerminal,
		      terms = ParserData.EC.terms}}
      )
     val sameToken = Token.sameToken
end

(* functor JoinWithArg creates a variant of the parser structure produced 
   above.  In this case, the makeLexer take an additional argument before
   yielding a value of type unit -> (svalue,pos) token
 *)

functor JoinWithArg(structure Lex : ARG_LEXER
	     structure ParserData: PARSER_DATA
	     structure LrParser : LR_PARSER
	     sharing ParserData.LrTable = LrParser.LrTable
	     sharing ParserData.Token = LrParser.Token
	     sharing type Lex.UserDeclarations.svalue = ParserData.svalue
	     sharing type Lex.UserDeclarations.pos = ParserData.pos
	     sharing type Lex.UserDeclarations.token = ParserData.Token.token)
		 : ARG_PARSER  =
struct
    structure Token = ParserData.Token
    structure Streamm = LrParser.Streamm

    exception ParseError = LrParser.ParseError

    type arg = ParserData.arg
    type lexarg = Lex.UserDeclarations.arg
    type pos = ParserData.pos
    type result = ParserData.result
    type svalue = ParserData.svalue

    val makeLexer = fn s => fn arg =>
		 LrParser.Streamm.streamify (Lex.makeLexer s arg)
    val parse = fn (lookahead,lexer,error,arg) =>
	(fn (a,b) => (ParserData.Actions.extract a,b))
     (LrParser.parse {table = ParserData.table,
	        lexer=lexer,
		lookahead=lookahead,
		saction = ParserData.Actions.actions,
		arg=arg,
		void= ParserData.Actions.void,
	        ec = {is_keyword = ParserData.EC.is_keyword,
		      noShift = ParserData.EC.noShift,
		      preferred_change = ParserData.EC.preferred_change,
		      errtermvalue = ParserData.EC.errtermvalue,
		      error=error,
		      showTerminal = ParserData.EC.showTerminal,
		      terms = ParserData.EC.terms}}
      )
    val sameToken = Token.sameToken
end;
