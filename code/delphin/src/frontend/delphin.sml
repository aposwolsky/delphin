(* Delphin Front End Interface *)

structure DelphinLrVals : Delphin_LRVALS = 
   DelphinLrValsFun (structure Token = LrParser.Token);

structure DelphinLex : LEXERR =
   DelphinLexFun (structure Tokens = DelphinLrVals.Tokens
                  structure Interface = Interface);

structure DelphinParser : PARSERR =
   Join (structure ParserData = DelphinLrVals.ParserData
         structure Lex = DelphinLex
         structure LrParser = LrParser);

structure Parse : PARSE =
   Parse ( structure DelphinExtSyntax = DelphinExtSyntax 
          structure Interface = Interface
          structure Parserr = DelphinParser
          structure Tokens = DelphinLrVals.Tokens);


structure Delphin = 
  Delphin ( structure Parse = Parse
	   structure DelphinParser = DelphinParser);