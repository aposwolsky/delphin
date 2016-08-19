(* Cut Elimination in Intuitionistic Sequent Calculus
 * Author: Adam Poswolsky, Based on Twelf code by Frank Pfenning
 *)

use "int-admit.d" ;

(* Notice that in the Twelf variant we needed to create another 
 * type family "conc*" which had cut in it.  However, here we
 * can use Nabla to specify that we just consider "conc"
 * extended with a "cut" constructor.
 *) 

fun ce : ({<cut : {A}{C}conc A -> (hyp A -> conc C) -> conc C #>} <conc A>) -> <conc A>
   = fn {<cut>} <cut A C (D1 cut) (D2 cut)> =>
                                          (case (ce ({<cut>} <D1 cut>))
                                          of <D1'> => case ({<h>} ce ({<cut>} <D2 cut h>))
                                                       of {<h>} <D2' h> => ca <D1'> <D2'>)
      | {<cut>} <axiom H> => <axiom H>

      | {<cut>} <andr (D1 cut) (D2 cut)> =>
                                let
                                   val <D1'> = ce ({<cut>} <D1 cut>)
                                   val <D2'> = ce ({<cut>} <D2 cut>)
                                in
                                   <andr D1' D2'>
                                end

      | {<cut>} <andl1 (D1 cut) H> =>
                               (case {<h1>} ce ({<cut>}<D1 cut h1>)
                                  of {<h1>}<D1' h1> => <andl1 D1' H>)

      | {<cut>} <andl2 (D2 cut) H> =>
                               (case {<h2>} ce ({<cut>}<D2 cut h2>)
                                  of {<h2>}<D2' h2> => <andl1 D2' H>)


      | {<cut>} <impr (D1 cut)> => (case {<h>} ce ({<cut>} <D1 cut h>)
                                      of {<h>} <D1' h> => <impr D1'>)
      
      | {<cut>} <impl (D1 cut) (D2 cut) H> =>
                                  (case ce ({<cut>}<D1 cut>)
                                     of <D1'> => case {<h>} ce ({<cut>} <D2 cut h>)
                                                   of {<h>} <D2' h> => <impl D1' D2' H>)


      | {<cut>} <orr1 (D1 cut)> =>
                               (case (ce ({<cut>}<D1 cut>))
                                  of <D1'> => <orr1 D1'>)

      | {<cut>} <orr2 (D2 cut)> =>
                               (case (ce ({<cut>}<D2 cut>))
                                  of <D2'> => <orr2 D2'>)

      | {<cut>} <orl (D1 cut) (D2 cut) H> =>
                                let
                                   val {<h1>}<D1' h1> = {<h1>} ce ({<cut>} <D1 cut h1>)
                                   val {<h2>}<D2' h2> = {<h2>} ce ({<cut>} <D2 cut h2>)
                                in
                                   <orl D1' D2' H>
                                end

      | {<cut>} <notr (D1 cut)> =>
                              (case {<p:o #>}{<h1 : hyp A>} ce ({<cut>} <D1 cut p h1>)
                                  of {<p>}{<h1>}<D1' p h1> => <notr D1'>)


      | {<cut>} <notl (D1 cut) H> =>
                               (case (ce ({<cut>}<D1 cut>))
                                  of <D1'> => <notl D1' H>)

      | {<cut>} <truer>           => <truer>

      | {<cut>} <falsel H>        => <falsel H>

      | {<cut>} <forallr (D1 cut)> =>
                              (case {<a:i #>} ce ({<cut>} <D1 cut a>)
                                  of {<a>}<D1' a> => <forallr D1'>)

      | {<cut>} <foralll T (D1 cut) H> =>
                              (case {<h1>} ce ({<cut>} <D1 cut h1>)
                                  of {<h1>}<D1' h1> => <foralll T D1' H>)

      | {<cut>} <existsr T (D1 cut)> =>
                              (case (ce ({<cut>} <D1 cut>))
                                  of <D1'> => <existsr T D1'>)

      | {<cut>} <existsl (D1 cut) H> =>
                              (case {<a:i #>}{<h1: hyp (A1 a) #>}  ce ({<cut>} <D1 cut a h1>)
                                  of {<a>}{<h1>} <D1' a h1> => <existsl D1' H>);

