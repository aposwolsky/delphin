(* comment out first line if undefined in your version of SMLofNJ *)
(* call sml-cm with @SMLdebug=/dev/null instead *)


SMLofNJ.Internals.GC.messages false;
CM.make "sources.cm";

structure Server =
struct

  val PsiRef : NablaIntSyntax.Dec IntSyn.Ctx ref = ref IntSyn.Null
  val tRef = ref (NablaIntSyntax.Shift 0)

  fun server (name, _) =
    let
      val _ = print ("\n" ^ Nabla.version ^ "\n\n")

      fun interrupt(k) = 
	let
	  val _ = print "\ninterrupt!  Quit?[Y/N]:  " 
	  val ioOpt = TextIO.inputLine TextIO.stdIn;
          val ioCap = (case ioOpt of
                       SOME io => String.implode(map (Char.toUpper) (String.explode(io)))
                       | NONE => "N")	    

	  val _ = case ioCap
	           of "Y\n" => (print "\nExiting Elphin.\n\n" ; 
				OS.Process.exit(OS.Process.success))
		 | "YES\n" => (print "\nExiting Elphin.\n\n" ; 
			       OS.Process.exit(OS.Process.success))
		 | _ => print "continuing Elphin...\n\n"
	in
	  k
	end

      (* Instead we will have it repeat *)
      fun interruptLoop (loop:unit -> unit) =
	(SMLofNJ.Cont.callcc
	 (fn k => (Signals.setHandler (Signals.sigINT,
				       Signals.HANDLER (fn _ => interrupt k));
		   ()));
	 loop ())

      val _ = interruptLoop (fn () => Nabla.top'(PsiRef, tRef)) 


    in
      OS.Process.success
    end
end;


SMLofNJ.exportFn ("bin/.heap/elphin", Server.server);
