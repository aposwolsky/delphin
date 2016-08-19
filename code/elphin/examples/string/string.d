(* Sample string functions *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

comp  = <X> |--> <Y> |--> <10 * X + Y> ;

toRational : <string> -> <rational>
  = <""> |--> <0>
  | <S ++ "0"> |--> comp (toRational <S>) <0>
  | <S ++ "1"> |--> comp (toRational <S>) <1>
  | <S ++ "2"> |--> comp (toRational <S>) <2> 
  | <S ++ "3"> |--> comp (toRational <S>) <3> 
  | <S ++ "4"> |--> comp (toRational <S>) <4> 
  | <S ++ "5"> |--> comp (toRational <S>) <5> 
  | <S ++ "6"> |--> comp (toRational <S>) <6> 
  | <S ++ "7"> |--> comp (toRational <S>) <7> 
  | <S ++ "8"> |--> comp (toRational <S>) <8>
  | <S ++ "9"> |--> comp (toRational <S>) <9> ;

x = toRational <"55321297">;


(* We cannot yet write the reverse function, because we only have rationals as constraint domain *)

