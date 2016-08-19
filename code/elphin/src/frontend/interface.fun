(* Interface for error reporting  syntax *)

structure Interface : INTERFACE =
struct
  
  type arg = unit   
  val nothing = ()

  type pos = int

  val noPos = 0

  val fnameOpt : string option ref = ref NONE

  val lineNum = ref 1
  val linePos = ref [1]

  fun reset() = (fnameOpt:=NONE;
		 lineNum:=1;
		 linePos:=[1])

  fun intToPos(i) = i
  fun incLineNum(i) = (lineNum := !lineNum + 1 ; linePos := i :: !linePos)
  fun add' (p,x) = p + x

  fun getErrorPrefix() = case (!fnameOpt) 
                           of NONE => "Line "
                            | SOME(fname) => fname ^ ":" 

  fun toString(pos) =
    let 
      fun look(p, a::rest, n) =
          if a<p then
	    Int.toString n ^ "." ^ Int.toString(p-a)
	  else
	    look(p, rest, n-1)

	| look _ = raise Domain (* list should never be empty *)
    in
      look(pos, !linePos, !lineNum)
    end

  fun error (errmsg, pos, _) =
    let fun look(p,a::rest,n) =
              if a<p then
		TextIO.output (TextIO.stdOut, 
			       (getErrorPrefix() ^ Int.toString n ^ "." ^ Int.toString(p-a) ^ " Error"))
	      else 
		look(p, rest, n-1)
	  | look _ = TextIO.output (TextIO.stdOut, "0.0")
    in
      look(pos,!linePos,!lineNum);
      TextIO.output (TextIO.stdOut, (": " ^ errmsg ^ "\n"))
    end
    
    
end   (* structure INTERFACE  *)