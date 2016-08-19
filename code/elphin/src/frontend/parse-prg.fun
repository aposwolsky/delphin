(* The Parser *)

functor Parse  (
                structure Interface : INTERFACE
                structure Parserr : PARSERR 
		  where type result = NablaExtSyntax.NablaProgram 
		  sharing type Parserr.arg = Interface.arg
		  sharing type Parserr.pos = Interface.pos
		  
                structure Tokens : Nabla_TOKENS
                     sharing type Tokens.token = Parserr.Token.token
                     sharing type Tokens.svalue = Parserr.svalue) : PARSE =

struct

structure Interface = Interface
structure Parserr = Parserr
structure Tokens = Tokens
structure Streamm = Parserr.Streamm
structure Token = Parserr.Token

(* Given a lexer, invoke parser *)
fun invoke lexstream =
   Parserr.parse(0, lexstream, Interface.error, Interface.nothing)



(* Parse a named input file *)
fun fparse fname =
   let val _ = Interface.reset()
       val _ = Interface.fnameOpt := SOME(fname)
       val _ = Paths.resetLines()
       val _ = Paths.newLine(1)

       fun process(OS.SysErr (s, _)) = s
	 | process(Subscript) =  "Subscript Exception"
	 | process(IO.BlockingNotSupported) =  "Blocking Not Supported"
	 | process(IO.RandomAccessNotSupported) =  "Random Access Not Supported"
	 | process(IO.NonblockingNotSupported) =  "Nonblocking Not Supported"
	 | process(IO.TerminatedStream) = "Terminated Stream"
	 | process(IO.ClosedStream) =  "Closed Stream"
	 | process _ = "Unknown Error Occurred"

       val infile = TextIO.openIn(fname)
	 handle IO.Io{function, name, cause} => (print ("Cannot open " ^ name ^ ": " ^ process(cause) ^ ".\n"); raise Domain )

       val lexer = Parserr.makeLexer 
	           (fn _ => TextIO.inputAll infile) 
       val dummyEOF = Tokens.EOF(Interface.noPos, Interface.noPos)
       fun loop lexer = 
           let val (result, lexer) = invoke lexer
               val (nextToken, lexer) = Parserr.Streamm.get lexer
           in 
              if Parserr.sameToken(nextToken, dummyEOF) 
                 then result
              else loop lexer
           end
   in loop lexer
   end


fun sparse () =
  let 
    val _ = Interface.reset()
    val _ = Paths.resetLines()
    val _ = Paths.newLine(1)
      
    fun inputToSemi _ =
      let
	
	fun trimFront' ([]) = []
	  | trimFront' (x::xs) = if Char.isSpace(x) then trimFront'(xs)
				 else x::xs

	fun trim (s) =
	  let 
	      val charList = String.explode(s)
	      val charList' = trimFront' charList
	      val charList'' = List.rev (trimFront' (List.rev charList'))
	  in
	    String.implode(charList'')
	  end



	fun lastCharSemi (s) = 
	  (case trimFront'((List.rev (String.explode s)))
	      of (#";" :: _) => true
	       | _ => false)

	  
	fun getInput (s) = 
	  let 
	    val s' = TextIO.inputN (TextIO.stdIn, 1)
	    val newS = s ^ s'
	    val endParse = lastCharSemi(newS) 

	    val moreInput = case (TextIO.canInput(TextIO.stdIn, 1))
	                    of NONE => false
			     | SOME X => if (X = 0) then false else true

	  in
	    case (endParse, moreInput)
	      of (true, false) => (newS)
	       | (true,  true) => (newS) (* (getInput newS) *)
	       | (false,  true) => (getInput newS)
	       | (false, false) => (if (trim(newS) = "") then "" 
				   else (print "--> " ; getInput newS))
	  end
      in
	getInput("")
      end
    
    (* OLD WAY -- required pressing Ctrl+D
    val infile = TextIO.openString (TextIO.inputAll (TextIO.stdIn)) 
    val lexer = Parserr.makeLexer (fn _ => TextIO.inputLine infile) 
    *)
    val lexer = Parserr.makeLexer (inputToSemi)  
    val dummyEOF = Tokens.EOF(Interface.noPos, Interface.noPos)
    val dummySEMI = Tokens.SEMICOLON(Paths.Reg(~1,~1),Interface.noPos, Interface.noPos)

    fun loop lexer =
      let
	  val (result, lexer) = invoke lexer
          val (nextToken, lexer) = Streamm.get lexer
       in 
              if (Parserr.sameToken(nextToken, dummyEOF) orelse
		 Parserr.sameToken(nextToken, dummySEMI))
                 then result
	      else loop lexer
		     
       end
   in loop lexer
   end


end  (* functor Parse *)
