(* The Parser *)

functor Parse  (
                structure Interface : INTERFACE
                structure Parserr : PARSERR 
		  where type result = DelphinExtSyntax.DelphinProgram 
		  sharing type Parserr.arg = Interface.arg
		  sharing type Parserr.pos = Interface.pos
		  
                structure Tokens : Delphin_TOKENS
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
fun fparse (displayName, fname) =
   let 
       val _ = Interface.reset()
       val _ = Interface.fnameOpt := SOME(displayName)
       val _ = Paths.resetLines()
       val _ = Paths.newLine(1)

       fun process(OS.SysErr (s, _)) = s
	 | process(Subscript) =  "Subscript Exception"
	 | process(IO.BlockingNotSupported) =  "Blocking Not Supported"
	 | process(IO.RandomAccessNotSupported) =  "Random Access Not Supported"
	 | process(IO.NonblockingNotSupported) =  "Nonblocking Not Supported"
	 | process(IO.ClosedStream) =  "Closed Stream"
	 (* IO.TerminatedStream doesn't exist in PolyML 5.0
	 | process(IO.TerminatedStream) = "Terminated Stream"
	 | process _ = "Unknown Error Occurred"
	  *)
	 | process _ = "Unknown Error Occurred (Possible Terminated Stream)"


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
   in 
     loop lexer
   end


fun sparse () =
  let 
    val _ = Interface.reset()
    val _ = Paths.resetLines()
    val _ = Paths.newLine(1)

    (* Gets input up to first semicolon (w.r.t. balanced parenthesis) *)
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


	fun balancedParen cList =
	  let
	    fun calcBalance (n, []) = n
	      | calcBalance (n, (#"(")::cList) = calcBalance (n+1, cList)
	      | calcBalance (n, (#")")::cList) = calcBalance (n-1, cList)
	      | calcBalance (n, _::cList) = calcBalance (n, cList)
	  in
	    if (calcBalance (0, cList) > 0) then false else true
	  end

	fun notInComment cList =
	  let
	    fun calcBalance (n, []) = n
	      | calcBalance (n, (#"(")::(#"*"):: cList) = calcBalance (n+1, cList)
	      | calcBalance (n, (#"*")::(#")")::cList) = calcBalance (n-1, cList)
	      | calcBalance (n, _::cList) = calcBalance (n, cList)
	  in
	    if (calcBalance (0, cList) > 0) then false else true
	  end

	fun lastCharSemi (cList) = 
	  (case trimFront'((List.rev (cList)))
	      of (#";" :: _) => true
	       | _ => false)

	(* If there are two semicolons in a row, then we also stop parsing even if parenthesis are not balanced *)
	fun lastTwoSemi (cList) =
	  let
	    val cRev = List.rev cList
	  in
	    (case trimFront'(cRev)
	      of (#";" :: cRev') => (case trimFront'(cRev') 
				       of (#";" :: _) => true
					| _ => false)      
	       | _ => false)
	  end
	  

	fun getInput (s) = 
	  let 
	    val s' = TextIO.inputN (TextIO.stdIn, 1)
	    val newS = s ^ s'
	    val newSlist = String.explode newS

	    val endParse = ((lastCharSemi newSlist) andalso (balancedParen newSlist)) orelse ((lastTwoSemi newSlist) andalso (notInComment newSlist))

	    (* ABP:  Bug in SML/NJ:
	     *    This was causing Delphin to simply crash
	     *    when outputting a lot of data.
	     *    By chance, I tried disabling things to do with
	     *    TextIO and disabling this stops it from crashing.
	     *    Before it would do "TextIO.canInput" on every character, but now only for newlines
	     *
	     * val moreInput = case (TextIO.canInput(TextIO.stdIn, 1))
	                    of NONE => false
			     | SOME X => if (X = 0) then false else true
	     *)

	    fun printContinuePrompt(lastChar) =
	        let
		  fun printIt () = print ("--> ")
		in
		   if (lastChar = "\n") then 
                        (* print "--> " *)
		        case (TextIO.canInput(TextIO.stdIn, 1))
			  of NONE => printIt()
			   | SOME X => if (X = 0) then printIt() else ()
		   else
		     ()
		end


	  in
	    case (endParse)
	      of (true) => (newS)
	       | (false) => (if (trim(newS) = "") then ""
				   else (printContinuePrompt(s') ; getInput newS))
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
   in 
     loop lexer
   end


end  (* functor Parse *)
