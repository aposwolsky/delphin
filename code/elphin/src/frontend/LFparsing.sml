(* Nabla utilities to Parse LF statements *)
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
	  val cid = IntSyn.sgnAdd conDec
	  val _ = (case (fromCS, !context)
		     of (IntSyn.Ordinary, SOME namespace) => Names.insertConst (namespace, cid)
		      | (IntSyn.Clause, SOME namespace) => Names.insertConst (namespace, cid)
		      | _ => ())
	          handle Names.Error msg =>
		    raise Names.Error (Paths.wrap (r, msg))
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
		     raise Names.Error (Paths.wrap (r, msg))
	  val _ = Names.installConstName cid
	  val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
	in 
	  cid
	end


    fun installStrDec (strdec, module, r, isDef) =
        let
          fun installAction (data as (cid, _)) =
              (installConst IntSyn.Ordinary data;
	       if !Global.chatter >= 4
                 then print (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n")
               else ())


          val _ = ModSyn.installStruct (strdec, module, !context,
                                        installAction, isDef)
                  handle Names.Error msg =>
                           raise Names.Error (Paths.wrap (r, msg))
        in
          ()
        end

    fun includeSig (module, r, isDef) =
        let
          fun installAction (data as (cid, _)) =
              (installConst IntSyn.Ordinary data;
	       if !Global.chatter >= 4
                 then print (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n")
               else ())

          val _ = ModSyn.installSig (module, !context,
                                     installAction, isDef)
                  handle Names.Error msg =>
                           raise Names.Error (Paths.wrap (r, msg))
        in
          ()
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
	       in
		 SOME(cid)
	       end
	     | icd (NONE) = (* anonymous definition for type-checking *)
	         (NONE)

	 in
	   icd optConDec
	 end
	 handle Constraints.Error (eqns) =>
	        raise ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))


      (* Fixity declaration for operator precedence parsing *)
      | install1 (fileName, (Parser.FixDec ((qid,r),fixity), _)) =
        (case Names.constLookup qid
           of NONE => raise Names.Error ("Undeclared identifier "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ " in fixity declaration")
            | SOME cid => (Names.installFixity (cid, fixity);
                           if !Global.chatter >= 3
                             then (print ((if !Global.chatter >= 4 then "%" else "")
                                         ^ Names.Fixity.toString fixity ^ " "
                                         ^ Names.qidToString (Names.constQid cid) ^ ".\n") ; NONE)
                           else (NONE))
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))

      (* Name preference declaration for printing *)
      | install1 (fileName, (Parser.NamePref ((qid,r), namePref), _)) =
        (case Names.constLookup qid
           of NONE => raise Names.Error ("Undeclared identifier "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ " in name preference")
            | SOME cid => (Names.installNamePref (cid, namePref) ; NONE)
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))


      | install1 _ = raise Domain



   end