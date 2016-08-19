(* Merge sort *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<nat : type>
<z : nat>
<s : nat -> nat>

<list : type>
<nil  : list>
<cons : nat -> list -> list> 

<bool : type>
<true : bool>
<false: bool>

append = <nil> |--> <L> |--> <L>
       | <cons X L> |--> <K> |--> <cons X> @ (append <L> <K>) ;

l1 = <cons (s z) (cons (s (s (s (s (s z))))) (cons (s (s (s z))) 
	(cons (s (s (s z))) nil)))> ;

lt : <nat> -> <nat> -> <bool>
   = <z> |--> <s Y> |--> <true>
   | <s X> |--> <s Y> |--> lt <X> <Y>
   | <X> |--> <z> |--> <false> ;

split : <nat> -> <list> -> <list> -> <list> -> _ 
      = <P> |--> <nil> |--> <L> |--> <R> |--> (<L> , <R>) 
      | <P> |--> <cons Q S> |--> <L> |--> <R> |--> 
	  case (lt <Q> <P>) of 
	  ( <true> |--> split <P> <S> <cons Q L> <R>
          | <false> |--> split <P> <S> <L> <cons Q R>) ; 

sort : <list> ->  <list>
     = <nil> |--> <nil>
     | <cons P S> |--> 
  	case (split <P> <S> <nil> <nil>)
           of (M |--> append (sort (fst M)) (<cons P> @ (sort (snd M)))) ; 


l2  = sort l1;


