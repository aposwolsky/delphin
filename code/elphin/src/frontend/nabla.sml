(* Nabla Front End Interface *)

structure NablaLrVals : Nabla_LRVALS = 
   NablaLrValsFun (structure Token = LrParser.Token);

structure NablaLex : LEXERR =
   NablaLexFun (structure Tokens = NablaLrVals.Tokens
                  structure Interface = Interface);

structure NablaParser : PARSERR =
   Join (structure ParserData = NablaLrVals.ParserData
         structure Lex = NablaLex
         structure LrParser = LrParser);

structure Parse : PARSE =
   Parse ( structure NablaExtSyntax = NablaExtSyntax 
          structure Interface = Interface
          structure Parserr = NablaParser
          structure Tokens = NablaLrVals.Tokens);


structure Nabla = 
  Nabla ( structure Parse = Parse
	   structure NablaParser = NablaParser);