(* Merge sort *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<nat : type>
	<z : nat>
	<s : nat -> nat>;

sig	<list : type>
	<nil  : list>
	<cons : nat -> list -> list> ;

sig	<bool : type>
	<true : bool>
	<false: bool>;

fun append = fn <nil> <L>      => <L>
              | <cons X L> <K> => <cons X> @ (append <L> <K>) ;

val l1 = <cons (s z) (cons (s (s (s (s (s z))))) (cons (s (s (s z))) 
	(cons (s (s (s z))) nil)))> ;

fun lt : <nat> -> <nat> -> <bool> =
   fn <z>  <s Y> => <true>
   | <s X> <s Y> => lt <X> <Y>
   | <X>   <z>   => <false> ;

fun split : <nat> -> <list> -> <list> -> <list> -> _ = 
      fn <P>  <nil>     <L>  <R>   => (<L> , <R>) 
      | <P> <cons Q S>  <L>  <R>   => 
	  (case (lt <Q> <P>) of 
	   <true> => split <P> <S> <cons Q L> <R>
          | <false> => split <P> <S> <L> <cons Q R>) ; 

fun sort : <list> ->  <list> = 
     fn <nil>     => <nil>
     | <cons P S> => 
  	case (split <P> <S> <nil> <nil>)
           of ((M1,M2) => append (sort M1) (<cons P> @ (sort M2))) ; 


val l2  = sort l1;


