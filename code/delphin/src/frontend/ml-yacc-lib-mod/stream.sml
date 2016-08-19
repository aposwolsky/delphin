(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi 
 *
 * $Log: stream.sml,v $
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
 * Revision 1.2  1997/08/26 19:18:55  jhr
 *   Replaced used of "abstraction" with ":>".
 *
# Revision 1.1.1.1  1997/01/14  01:38:04  george
#   Version 109.24
#
 * Revision 1.1.1.1  1996/01/31  16:01:43  george
 * Version 109
 * 
 *)

(* Stream: a structure implementing a lazy stream.  The signature STREAM
   is found in base.sig *)

structure Streamm :> STREAMM =
struct
   datatype 'a str = EVAL of 'a * 'a str ref | UNEVAL of (unit->'a)

   type 'a stream = 'a str ref

   fun get(ref(EVAL t)) = t
     | get(s as ref(UNEVAL f)) = 
	    let val t = (f(), ref(UNEVAL f)) in s := EVAL t; t end

   fun streamify f = ref(UNEVAL f)
   fun cons(a,s) = ref(EVAL(a,s))

end;
