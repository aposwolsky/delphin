sig	<nat : type>
	<z   : nat>
	<s   : (nat -> nat)>;

fun acker : <nat> -> <nat>  -> < nat> =
 fn <z> <y>    => <s  y>
 | <s x> <z>   => acker  <x> <s  z>
 | <s x> <s y> => acker  <x> (acker  <s  x> <y>) ;

val a0 = acker <s (s z)> <s (s z)>;
val a1 : <nat>
   = acker <s (s (s z))> <s (s z)> ;
val a2 : <nat>
   = acker <s (s (s z))> <s (s (s (s z)))> ;

fun add  : <rational> -> <rational> -> <rational>
      = fn <x> => fn <y> => <x + y> ;


fun comp  : <rational> -> <rational> -> <rational>
      = fn <x> => fn <y> => add (<10 * x>) <y> ;


fun number : <string> -> <rational> =
      fn <"">      => <0>
      | <S ++ "0"> => comp (number <S>) <0>
      | <S ++ "1"> => comp (number <S>) <1>
      | <S ++ "2"> => comp (number <S>) <2> 
      | <S ++ "3"> => comp (number <S>) <3> 
      | <S ++ "4"> => comp (number <S>) <4> 
      | <S ++ "5"> => comp (number <S>) <5> 
      | <S ++ "6"> => comp (number <S>) <6> 
      | <S ++ "7"> => comp (number <S>) <7> 
      | <S ++ "8"> => comp (number <S>) <8>
      | <S ++ "9"> => comp (number <S>) <9> ;

val x : <rational>
  = number <"202"> ;	

fun nat2rat : <nat> -> <rational> =
        fn <z> => <0>
 	| ([<x:nat>] <s x> => add (nat2rat <x>) <1> );

val ratacker1 : <rational>
          = nat2rat a1 ;
(*
val ratacker2 : <rational>
          = nat2rat a2 ;
*)
(* 
val a3 : <rational>
   = nat2rat (acker <s (s (s (s z)))> <s z>) ;

*)