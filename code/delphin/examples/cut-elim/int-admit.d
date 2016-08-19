(* Admissibility of Cut in Intuitionistic Sequent Calculus
 * Author: Adam Poswolsky, Based on Twelf code by Frank Pfenning
 *)

sig use "formulas.elf" ;
sig use "int.elf" ;

params = <hyp A>, <o>, <i> ;

fun ca : <A:o> -> <conc A> -> <hyp A -> conc C> -> <conc C> =
(* First argument (A:o) is made explicit so it appears in the
 * termination ordering.  We will just use "_" for this argument
 * as it is always inferable.
 *)

 (* Axiom Conversions *)
  fn <_> <axiom H>    <E>       => <E H>

   | <_> <D>          <axiom>   => <D>

 (* Essential Conversions *)
   | <_> <andr D1 D2> <[h:hyp (A1 and A2)] andl1 (E1 h) h> 
                  => (case {<h1:hyp A1 #>} ca <_> <andr D1 D2> <[h] E1 h h1>
                      of {<h1:hyp A1 #>} <E1' h1> => ca <_> <D1> <E1'>)

   | <_> <andr D1 D2> <[h:hyp (A1 and A2)] andl2 (E2 h) h>
                  => (case {<h2:hyp A2 #>} ca <_> <andr D1 D2> <[h] E2 h h2>
                      of {<h1:hyp A2 #>} <E2' h1> => ca <_> <D2> <E2'>)

   | <_> <impr D2>     <[h] impl (E1 h) (E2 h) h> 
                  => (case (ca <_> <impr D2> <E1>)
                        of <E1'> => case ({<h2>} ca <_> <impr D2> <[h] E2 h h2>)
                                   of   {<h2>}<E2' h2> => ca <_> (ca <_> <E1'> <D2>) <E2'>)

   | <_> <orr1 D1>     <[h] orl (E1 h) (E2 h) h>
                  => (case {<h1>} ca <_> <orr1 D1> <[h] E1 h h1>
                      of {<h1>} <E1' h1> => ca <_> <D1> <E1'>)

   | <_> <orr2 D2>     <[h] orl (E1 h) (E2 h) h>
                  => (case {<h2>} ca <_> <orr2 D2> <[h] E2 h h2>
                      of {<h2>} <E2' h2> => ca <_> <D2> <E2'>)

   | <_> <notr D1>     <[h] notl (E1 h) h>
                  => let
                        val <F1> = ca <_> <notr D1> <E1>
                     in
                        case {<p:o#>} ca <_> <F1> <[h1] D1 p h1>
                        of {<p>}<F2 p> => <F2 C>
                     end

   | <_> <forallr D1>  <[h:hyp (forall A1)] foralll T (E1 h) h>
                  => (case {<h2 : hyp (A1 T) #>} ca <_> <forallr D1> <[h] E1 h h2>
                         of {<h2>}<E1' h2> => ca <_> <D1 T> <E1'>)

   | <_> <existsr T D1> <[h:hyp (exists A1)] existsl (E1 h) h>
                  => (case {<a:i #>}{<h1:hyp (A1 a) #>} ca <_> <existsr T D1> <[h] E1 h a h1>
                      of {<a>}{<h1>}<E1' a h1> => ca <_> <D1> <E1' T>)


 (* Left Commutative Conversions *)

   | <_> <andl1 D1 H>   <E> => (case {<h1>} ca <_> <D1 h1> <E>
                              of {<h1>} <D1' h1> => <andl1 D1' H>)

   | <_> <andl2 D2 H>   <E> => (case {<h2>} ca <_> <D2 h2> <E>
                              of {<h2>} <D2' h2> => <andl2 D2' H>)

   | <_> <impl D1 D2 H> <E> => (case ({<h2>} ca <_> <D2 h2> <E>)
                              of {<h2>}<D2' h2> => <impl D1 D2' H>)

   | <_> <orl D1 D2 H>  <E> => let
                              val {<h1>}<D1' h1> = {<h1>}ca <_> <D1 h1> <E>
                              val {<h2>}<D2' h2> = {<h2>}ca <_> <D2 h2> <E>
                           in
                              <orl D1' D2' H>
                           end

   | <_> <notl D1 H>    <E> => <notl D1 H>

   | <_> <falsel H>     <E> => <falsel H>

   | <_> <foralll T D1 H> <E> => (case {<h>} ca <_> <D1 h> <E>
                                of {<h>}<D1' h> => <foralll T D1' H>)

   | <_> <existsl D1 H> <E> => (case {<a:i #>}{<h: hyp (B1 a) #>} ca <_> <D1 a h> <E>
                              of {<a>}{<h>}<D1' a h> => <existsl D1' H>)

 (* Right Commutative Conversions *)

   | <_> <D> <[h] axiom H1> => <axiom H1>

   | <_> <D> <[h] andr (E1 h) (E2 h)> => 
                               let
                                  val <E1'> = ca <_> <D> <E1>
                                  val <E2'> = ca <_> <D> <E2>
                               in
                                  <andr E1' E2'>
                               end

   | <_> <D> <[h] andl1 (E1 h) H> => (case {<h1>}ca <_> <D> <[h] E1 h h1>
                                     of {<h1>}<E1' h1> => <andl1 E1' H>)


   | <_> <D> <[h] andl2 (E2 h) H> => (case {<h2>}ca <_> <D> <[h] E2 h h2>
                                     of {<h2>}<E2' h2> => <andl2 E2' H>)


   | <_> <D> <[h] impr (E2 h)> => (case ({<h2>} ca <_> <D> <[h] E2 h h2>)
                                     of {<h2>} <E2' h2> => <impr E2'>)

   | <_> <D> <[h] impl (E1 h) (E2 h) H> =>
                                (case (ca <_> <D> <E1>)
                                  of <E1'> => case ({<h2>} ca <_> <D> <[h] E2 h h2>)
                                                of {<h2>}<E2' h2> => <impl E1' E2' H>)

   | <_> <D> <[h] orr1 (E1 h)> => 
                           let
                              val <E1'> = ca <_> <D> <E1>
                           in
                              <orr1 E1'>
                           end

   | <_> <D> <[h] orr2 (E2 h)> => 
                           let
                              val <E2'> = ca <_> <D> <E2>
                           in
                              <orr2 E2'>
                           end

   | <_> <D> <[h] orl (E1 h) (E2 h) H> => 
                           let
                              val {<h1>}<E1' h1> = {<h1>}ca <_> <D> <[h] E1 h h1>
                              val {<h2>}<E2' h2> = {<h2>}ca <_> <D> <[h] E2 h h2>
                           in
                              <orl E1' E2' H>
                           end
   | <_> <D> <[h] notr (E1 h)> =>
                           (case {<p: o#>}{<h1:hyp B1>} ca <_> <D> <[h] E1 h p h1>
                               of {<p>}{<h1>}<E1' p h1> => <notr E1'>)
   | <_> <D> <[h] notl (E1 h) H> =>
                           let
                              val <E1'> = ca <_> <D> <E1>
                           in
                              <notl E1' H>
                           end

   | <_> <D> <[h] truer>       => <truer>
   
   | <_> <D> <[h] falsel H>    => <falsel H>
 
   | <_> <D> <[h] forallr (E1 h)> =>
                          (case {<a:i #>} ca <_> <D>  <[h] E1 h a>
                             of {<a>}<E1' a> => <forallr E1'>)

   | <_> <D> <[h] foralll T (E1 h) H> =>
                          (case {<h1>} ca <_> <D> <[h] E1 h h1>
                             of {<h1>}<E1' h1> => <foralll T E1' H>)

   | <_> <D> <[h] existsr T (E1 h)> =>
                          (case ca <_> <D> <E1>
                             of <E1'> => <existsr T E1'>)

   | <_> <D> <[h] existsl (E1 h) H> =>
                          (case {<a:i #>} {<h1 :hyp (B1 a)>} ca <_> <D> <[h] E1 h a h1>
                             of {<a>}{<h1>}<E1' a h1> => <existsl E1' H>);

