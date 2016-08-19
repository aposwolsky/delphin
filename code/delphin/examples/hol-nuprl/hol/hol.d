sig
< tp : type >
< arr : tp -> tp -> tp  > %infix right 10
< o  : tp >

(* Terms *)
< tm : tp -> type > 
< =>: tm (o arr o arr o) > 
< == : tm (A arr A arr o) >
< @ : tm (A arr B) -> tm A -> tm B > 	%infix left 15

< \ : (tm A -> tm B) -> tm (A arr B)> 

< ==> = [H:tm o] [G:tm o] => @ H @ G >	%infix right 13

< === = [H:tm A] [G:tm A] == @ H @ G >	%infix left 14


(* Derivability *)

< |-    : tm o -> type>			%prefix 10

< mp    : |- H -> |- H ==> G -> |- G >

< disch : (|- H -> |- G) -> |- H ==> G >

< refl  : |- H === H > 

< beta  : |- (\ H) @ G === (H G) >

< sub   : {G:tm A -> tm o} |- H1 === H2 -> |- G H1 -> |- G H2 > 

< abs   : |- \ H === \ G 
	 <- ({x} |- H x === G x) >

(* Booleans *)

< bool  = o >

< true  : tm bool = (\ [x : tm bool] x) === (\ [x: tm bool] x) >

< all|  : tm ((A arr bool) arr bool)
      = \ [P:tm (A arr bool)] P === \ [x] true>

< all   = [P] all| @ P >
< false : tm bool = all (\ [P] P) >
< neg   : tm (bool arr bool) = \ [P:tm bool] P ==> false >

< /|\   : tm (bool arr bool arr bool)
      = \ [P:tm bool] \ [Q:tm bool] all (\ [R:tm bool] (P ==> Q ==> R) ==> R)>
< /\    = [P] [Q] /|\ @ P @ Q>		%infix right 12
< \|/   : tm (bool arr bool arr bool)	
      = \ [P:tm bool] \ [Q:tm bool] all (\ [R:tm bool] (P ==> R) ==> (Q ==> R) ==> R) > 
< \/    = [P] [Q] \|/ @ P @ Q>		%infix right 11
< the|  : tm ((A arr bool) arr A)> 
< the   = [P] the| @ P> 
< ex|   : tm ((A arr bool) arr bool) 
      = \ [P:tm (A arr bool)] P @ (the (\ [x] P @ x))>
< ex    = [P] ex| @ P>
;


