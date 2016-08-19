(* Delphin utilities to Parse LF statements *)
(* Author: Adam Poswolsky *)
(* Credits:  Based very very heavily on twelf.fun *)


structure LFparsing =
   struct

     structure I = IntSyn
       
    (* During elaboration of a signature expression, each constant
       that that the user declares is added to this table.  At top level,
       however, the reference holds NONE (in particular, shadowing is
       allowed).
    *)
    val context : Names.namespace option ref = ref NONE
      (* ADAM:  This isn't used... at least not yet. do we need it?  *)

    (* Twelf adds a "." at the end of some strings.. this just removes it *)
    fun  removeDot s =
      let
	val size = String.size s
	val endStr = String.substring(s, size-1, 1)
	val restStr = String.substring(s, 0, size-1)
      in
	if (endStr = ".") then restStr else s
      end


    fun installConst fromCS (cid, fileNameocOpt) =
        let
          val _ = Origins.installOrigin (cid, fileNameocOpt)
          val _ = Index.install fromCS (IntSyn.Const cid)
          val _ = IndexSkolem.install fromCS (IntSyn.Const cid)
          val _ = (Timers.time Timers.compiling Compile.install) fromCS cid
          val _ = (Timers.time Timers.subordinate Subordinate.install) cid
          val _ = (Timers.time Timers.subordinate Subordinate.installDef) cid
        in
          ()
        end

    (* installConDec fromCS (conDec, ocOpt)
       installs the constant declaration conDec which originates at ocOpt
       in various global tables, including the global signature.
       Note: if fromCS = FromCS then the declaration comes from a Constraint
       Solver and some limitations on the types are lifted.
    *)
    fun installConDec fromCS (conDec, fileNameocOpt as (fileName, ocOpt), r) =
	let
	  val _ = (Timers.time Timers.modes ModeCheck.checkD) (conDec, fileName, ocOpt)

	  (* ABP:  Check freeze before adding it to the signature *)
	  val _ = (case conDec 
	          of I.ConDec (name, _, _, _, _, _) => 
		                (case I.targetFamOpt (I.conDecType conDec)
				   of SOME a => Subordinate.checkFreeze(name, a)
				    | _ => ())
		   | I.SkoDec (name, _, _, _, _) => 
		                (case I.targetFamOpt (I.conDecType conDec)
				   of SOME a => Subordinate.checkFreeze(name, a)
				    | _ => ())
		   | _ => ())
	       handle Subordinate.Error msg => raise Subordinate.Error (Paths.wrapLoc(Paths.Loc (fileName,r),msg))

	  val cid = IntSyn.sgnAdd conDec
	  val _ = (case (fromCS, !context)
		     of (IntSyn.Ordinary, SOME namespace) => Names.insertConst (namespace, cid)
		      | (IntSyn.Clause, SOME namespace) => Names.insertConst (namespace, cid)
		      | _ => ())
	          handle Names.Error msg =>
		    raise Names.Error (Paths.wrapLoc(Paths.Loc (fileName,r),msg))
	  val _ = Names.installConstName cid
	  val _ = installConst fromCS (cid, fileNameocOpt)
	  val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
	in 
	  cid
	end

    fun installBlockDec fromCS (conDec, fileNameocOpt as (fileName, ocOpt), r) =
	let
	  val cid = IntSyn.sgnAdd conDec
	  val _ = (case (fromCS, !context)
		     of (IntSyn.Ordinary, SOME namespace) => Names.insertConst (namespace, cid)
		        (* (Clause, _) should be impossible *)
		      | _ => ())
	           handle Names.Error msg =>
		     raise Names.Error (Paths.wrapLoc(Paths.Loc (fileName,r),msg))
	  val _ = Names.installConstName cid
	  val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
	in 
	  cid
	end




    fun constraintsMsg (cnstrL) =
        "Typing ambiguous -- unresolved constraints\n" ^ Print.cnstrsToString cnstrL

    (* install1 (decl) = ()
       Installs one declaration
       Effects: global state
                may raise standard exceptions
    *)
    fun install1 (fileName, (Parser.ConDec condec, r)) =
        (* Constant declarations c : V, c : V = U plus variations *)
        (let
	   val (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName,r), false)
	   fun icd (SOME (conDec as IntSyn.BlockDec _)) = 
	       let
		 (* allocate new cid. *)
		 val cid = installBlockDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
	       in
		 SOME(cid)
	       end
	     | icd (SOME (conDec)) =
	       let
		 (* names are assigned in ReconConDec *)
		 (* val conDec' = nameConDec (conDec) *)
		 (* should print here, not in ReconConDec *)
		 (* allocate new cid after checking modes! *)
		 val cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
	       (* DO NOT PRINT -- ABP 
		 val s = Print.conDecToString(conDec)
		 val _ = print ("cons <" ^ removeDot(s) ^ ">")
		*)
		 fun getName (I.ConDec(s, _, _, _, _, _)) = s
		   | getName (I.ConDef (s, _, _, _, _, _, _)) = s
		   | getName _ = "ABP: (not implemented)"

		 val _ = print ("[\"" ^ (getName conDec) ^ "\" Added to Signature...]\n\n" )
	       in
		 SOME(cid)
	       end
	     | icd (NONE) = (* anonymous definition for type-checking *)
	         (NONE)

	 in
	   icd optConDec
	 end
	 handle Constraints.Error (eqns) =>
	        raise ReconTerm.Error (Paths.wrapLoc(Paths.Loc (fileName,r),constraintsMsg eqns)))


      | install1 (fileName, (Parser.AbbrevDec condec, r)) =
        (* Abbreviations %abbrev c = U and %abbrev c : V = U *)
        (let
	  val (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName,r), true)
	  fun icd (SOME(conDec)) =
	      let
		  (* names are assigned in ReconConDec *)
		  (* val conDec' = nameConDec (conDec) *)
		  (* should print here, not in ReconConDec *)
		  (* allocate new cid after checking modes! *)
		  val cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)

		  fun getName (I.AbbrevDef (s, _, _, _, _, _)) = s
		    | getName _ = "ABP: (not implemented)"

		  val _ = print ("[\"" ^ (getName conDec) ^ "\" Added to Signature...]\n\n" )

	      in
		SOME(cid)
	      end
	    | icd (NONE) = (* anonymous definition for type-checking *)
	        NONE
	in
	  icd optConDec
	end
        handle Constraints.Error (eqns) =>
	       raise ReconTerm.Error (Paths.wrapLoc(Paths.Loc (fileName,r),constraintsMsg eqns)))



      (* Fixity declaration for operator precedence parsing *)
      | install1 (fileName, (Parser.FixDec ((qid,r),fixity), _)) =
        (case Names.constLookup qid
           of NONE => raise Names.Error ("Undeclared identifier "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ " in fixity declaration")
            | SOME cid => 
	         let
		   val _ = Names.installFixity (cid, fixity)
		   (* DO NOT PRINT
		   val _ = print (Names.Fixity.toString fixity)
		     *)
		 in
		   NONE
		 end
	 handle Names.Error (msg) => raise Names.Error (Paths.wrapLoc(Paths.Loc (fileName,r),msg)))

      (* Name preference declaration for printing *)
      | install1 (fileName, (Parser.NamePref ((qid,r), namePref), _)) =
        (case Names.constLookup qid
           of NONE => raise Names.Error ("Undeclared identifier "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ " in name preference")
            | SOME cid => (Names.installNamePref (cid, namePref) ; NONE)
	 handle Names.Error (msg) => raise Names.Error (Paths.wrapLoc(Paths.Loc (fileName,r),msg)))


      | install1 (filename, P) = raise Domain



   end