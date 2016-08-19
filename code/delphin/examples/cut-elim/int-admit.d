(* Admissibility of Cut in Intuitionistic Sequent Calculus
 * Author: Adam Poswolsky, Based on Twelf code by Frank Pfenning
 *)

sig use "formulas.elf" ;
sig use "int.elf" ;

fun ca : <conc A> -> <hyp A -> conc C> -> <conc C> =

 (* Axiom Conversions *)
  fn <axiom H>    <E>       => <E H>

   | <D>          <axiom>   => <D>

 (* Essential Conversions *)
   | <andr D1 D2> <[h:hyp (A1 and A2)] andl1 (E1 h) h> 
                  => (case {<h1:hyp A1 #>} ca <andr D1 D2> <[h] E1 h h1>
                      of {<h1:hyp A1 #>} <E1' h1> => ca <D1> <E1'>)

   | <andr D1 D2> <[h:hyp (A1 and A2)] andl2 (E2 h) h>
                  => (case {<h2:hyp A2 #>} ca <andr D1 D2> <[h] E2 h h2>
                      of {<h1:hyp A2 #>} <E2' h2> => ca <D2> <E2'>)

   | <impr D2>     <[h] impl (E1 h) (E2 h) h> 
                  => (case (ca <impr D2> <E1>)
                        of <E1'> => case ({<h2>} ca <impr D2> <[h] E2 h h2>)
                                   of   {<h2>}<E2' h2> => ca (ca <E1'> <D2>) <E2'>)

   | <orr1 D1>     <[h] orl (E1 h) (E2 h) h>
                  => (case {<h1>} ca <orr1 D1> <[h] E1 h h1>
                      of {<h1>} <E1' h1> => ca <D1> <E1'>)

   | <orr2 D2>     <[h] orl (E1 h) (E2 h) h>
                  => (case {<h2>} ca <orr2 D2> <[h] E2 h h2>
                      of {<h2>} <E2' h2> => ca <D2> <E2'>)

   | <notr D1>     <[h] notl (E1 h) h>
                  => let
                        val <F1> = ca <notr D1> <E1>
                     in
                        case {<p:o#>} ca <F1> <[h1] D1 p h1>
                        of {<p>}<F2 p> => <F2 C>
                     end

   | <forallr D1>  <[h:hyp (forall A1)] foralll T (E1 h) h>
                  => (case {<h2 : hyp (A1 T) #>} ca <forallr D1> <[h] E1 h h2>
                         of {<h2>}<E1' h2> => ca <D1 T> <E1'>)

   | <existsr T D1> <[h:hyp (exists A1)] existsl (E1 h) h>
                  => (case {<a:i #>}{<h1:hyp (A1 a) #>} ca <existsr T D1> <[h] E1 h a h1>
                      of {<a>}{<h1>}<E1' a h1> => ca <D1> <E1' T>)


 (* Left Commutative Conversions *)

   | <andl1 D1 H>   <E> => (case {<h1>} ca <D1 h1> <E>
                              of {<h1>} <D1' h1> => <andl1 D1' H>)

   | <andl2 D2 H>   <E> => (case {<h2>} ca <D2 h2> <E>
                              of {<h2>} <D2' h2> => <andl2 D2' H>)

   | <impl D1 D2 H> <E> => (case ({<h2>} ca <D2 h2> <E>)
                              of {<h2>}<D2' h2> => <impl D1 D2' H>)

   | <orl D1 D2 H>  <E> => let
                              val {<h1>}<D1' h1> = {<h1>}ca <D1 h1> <E>
                              val {<h2>}<D2' h2> = {<h2>}ca <D2 h2> <E>
                           in
                              <orl D1' D2' H>
                           end

   | <notl D1 H>    <E> => <notl D1 H>

   | <falsel H>     <E> => <falsel H>

   | <foralll T D1 H> <E> => (case {<h>} ca <D1 h> <E>
                                of {<h>}<D1' h> => <foralll T D1' H>)

   | <existsl D1 H> <E> => (case {<a:i #>}{<h: hyp (B1 a) #>} ca <D1 a h> <E>
                              of {<a>}{<h>}<D1' a h> => <existsl D1' H>)

 (* Right Commutative Conversions *)

   | <D> <[h] axiom H1> => <axiom H1>

   | <D> <[h] andr (E1 h) (E2 h)> => 
                               let
                                  val <E1'> = ca <D> <E1>
                                  val <E2'> = ca <D> <E2>
                               in
                                  <andr E1' E2'>
                               end

   | <D> <[h] andl1 (E1 h) H> => (case {<h1>}ca <D> <[h] E1 h h1>
                                     of {<h1>}<E1' h1> => <andl1 E1' H>)


   | <D> <[h] andl2 (E2 h) H> => (case {<h2>}ca <D> <[h] E2 h h2>
                                     of {<h2>}<E2' h2> => <andl2 E2' H>)


   | <D> <[h] impr (E2 h)> => (case ({<h2>} ca <D> <[h] E2 h h2>)
                                     of {<h2>} <E2' h2> => <impr E2'>)

   | <D> <[h] impl (E1 h) (E2 h) H> =>
                                (case (ca <D> <E1>)
                                  of <E1'> => case ({<h2>} ca <D> <[h] E2 h h2>)
                                                of {<h2>}<E2' h2> => <impl E1' E2' H>)

   | <D> <[h] orr1 (E1 h)> => 
                           let
                              val <E1'> = ca <D> <E1>
                           in
                              <orr1 E1'>
                           end

   | <D> <[h] orr2 (E2 h)> => 
                           let
                              val <E2'> = ca <D> <E2>
                           in
                              <orr2 E2'>
                           end

   | <D> <[h] orl (E1 h) (E2 h) H> => 
                           let
                              val {<h1>}<E1' h1> = {<h1>}ca <D> <[h] E1 h h1>
                              val {<h2>}<E2' h2> = {<h2>}ca <D> <[h] E2 h h2>
                           in
                              <orl E1' E2' H>
                           end
   | <D> <[h] notr (E1 h)> =>
                           (case {<p: o#>}{<h1:hyp B1>} ca <D> <[h] E1 h p h1>
                               of {<p>}{<h1>}<E1' p h1> => <notr E1'>)
   | <D> <[h] notl (E1 h) H> =>
                           let
                              val <E1'> = ca <D> <E1>
                           in
                              <notl E1' H>
                           end

   | <D> <[h] truer>       => <truer>
   
   | <D> <[h] falsel H>    => <falsel H>
 
   | <D> <[h] forallr (E1 h)> =>
                          (case {<a:i #>} ca <D>  <[h] E1 h a>
                             of {<a>}<E1' a> => <forallr E1'>)

   | <D> <[h] foralll T (E1 h) H> =>
                          (case {<h1>} ca <D> <[h] E1 h h1>
                             of {<h1>}<E1' h1> => <foralll T E1' H>)

   | <D> <[h] existsr T (E1 h)> =>
                          (case ca <D> <E1>
                             of <E1'> => <existsr T E1'>)

   | <D> <[h] existsl (E1 h) H> =>
                          (case {<a:i #>} {<h1 :hyp (B1 a)>} ca <D> <[h] E1 h a h1>
                             of {<a>}{<h1>}<E1' a h1> => <existsl E1' H>);

