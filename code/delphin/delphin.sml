(* comment out first line if undefined in your version of SMLofNJ *)
(* call sml-cm with @SMLdebug=/dev/null instead *)


SMLofNJ.Internals.GC.messages false;
CM.make "src/sources.cm";

structure Server =
struct

  val ContextRef : DelphinIntSyntax.decCtx ref = ref IntSyn.Null
  val subRef = ref (DelphinIntSyntax.id)

  fun server (name, _) =
    let
      val _ = print ("\n" ^ Delphin.version ^ "\n\n")

      fun interrupt'(k) = 
	let
	  val _ = print "\ninterrupt!  Quit?[Y/N]:  " 
	  val ioOpt = TextIO.inputLine TextIO.stdIn;
	  val ioCap = (case ioOpt of
	               SOME io => String.implode(map (Char.toUpper) (String.explode(io)))
		       | NONE => "N")
	    

	  val _ = case ioCap
	           of ("Y\n") => (print "\nExiting Delphin.\n\n" ; 
				OS.Process.exit(OS.Process.success))
		 | ("YES\n") => (print "\nExiting Delphin.\n\n" ; 
			       OS.Process.exit(OS.Process.success))
		 | _ => print "continuing Delphin...\n\n"
	in
	  k
	end

      fun interrupt(k) = interrupt'(k) handle _ => interrupt(k)

      (* Instead we will have it repeat *)
      fun interruptLoop (loop:unit -> unit) =
	(SMLofNJ.Cont.callcc
	 (fn k => (Signals.setHandler (Signals.sigINT,
				       Signals.HANDLER (fn _ => interrupt k));
		   ()));
	 loop ())
	
      (* update dirPrefix and startDir
       * to current directory, as "delphin"
       * can be run from a directory different
       * from the compiled path..
       *)
      val _ = Delphin.changePath (OS.FileSys.getDir())
      val _ = Delphin.resetMetaSigAndWorld ()

      val _ = Delphin.initTop'();
      val _ = interruptLoop (fn () => Delphin.top'(ContextRef, subRef)) 


    in
      OS.Process.success
    end
end;


SMLofNJ.exportFn ("bin/.heap/delphin", Server.server);
