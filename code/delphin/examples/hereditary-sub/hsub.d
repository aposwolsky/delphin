(*
%%% Intrinsically total hereditary substitution and identity
%%% on expressions in spine form
%%% 
%%% Author: Frank Pfenning
%%% March 2008
*)

sig use "hsub.elf";

params = <hd B2>;

fun subtm : <A:tp> -> <ord (succ zero)> -> <tm A> -> <hd A -> tm B> -> <tm B>
  = fn <A> <s z> <U> <[h] lm [h2] V1 h h2>
       => (case ({<h2:hd B2>} subtm <A> <(s z)> <U> <[h] V1 h h2>)
             of ({<h2:hd B2>} <V1' h2>) => <lm [h2] V1' h2>)
     | <A> <s z> <U> <[h] rt h (S h)>
       => (case (subsp <A> <s z> <U> <[h] S h>)
             of <S'> => reduce <A> <z> <U> <S'>)
     | <A> <s z> <U> <[h] rt H (S h)>
       => (case (subsp <A> <s z> <U> <[h] S h>)
             of <S'> => <rt H S'>)

and subsp : <A:tp> -> <ord (succ zero)> -> <tm A> -> <hd A -> sp B i> -> <sp B i>
  = fn <A> <s z> <U> <[h] ap (V h) (S h)>
       => <ap> @ (subtm <A> <s z> <U> <[h] V h>)
               @ (subsp <A> <s z> <U> <[h] S h>)
     | <A> <s z> <U> <[h] nl>
       => <nl>

and reduce : <A:tp> -> <ord (zero)> -> <tm A> -> <sp A i> -> <tm i>
  = fn <B => A> <z> <lm [h] U h> <ap V S>
       => (case (subtm <B> <s z> <V> <[h] U h>)
             of <U'> => reduce <A> <z> <U'> <S>)
     | <i> <z> <U> <nl> => <U>
;

fun eta : <A:tp> -> <sp A i -> tm i> -> <tm A>
  = fn <i> <[t] V t> => <V nl>
     | <A => B> <[t] V t> =>
       (case ({<h:hd A>} eta <A> <[t] rt h t>)
          of ({<h:hd A>} <U h>) =>
	  (case ({<h:hd A>} eta <B> <[t] V (ap (U h) t)>)
             of ({<h:hd A>} <U' h>) => <lm [h] U' h>))
;

(* testing *)
val run1 = subtm <i => i> <s z>
           <lm [x] rt x nl>
	   <[h] lm [y] rt h (ap (rt y nl) nl)>
;
val run2 = {<h:hd (i => i)>} eta <i => i> <[t] rt h t>
;
