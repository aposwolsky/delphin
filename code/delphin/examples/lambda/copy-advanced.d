(* Copying lambda expressions *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig 	<exp  : type>;
sig     <eq : exp -> exp -> type> ;

sig     <dummy : (exp -> exp) -> (eq U V -> eq U V) -> type> ;
	(* this is necessary just to state that 
	 * we want the subordination relation to allow exp
	 * to occur in exp and eq to occur in eq.
	 * We do not actually use "dummy" anywhere.
	 * And perhaps other syntax can be developed.
	 *)

params = <exp>;


fun extend : {<app  : exp -> exp -> exp>}
	    {<lam  : (exp -> exp) -> exp>}
            {<eq_app : {E1} {E2} {F1} {F2} eq E1 F1 -> eq E2 F2 -> eq (app E1 E2) (app F1 F2)>}
            {<eq_lam : {E} {F} ({x}eq x x -> eq (E x) (F x)) -> eq (lam E) (lam F)>}

            (<f:exp#> -> <eq f f>) -> {<x:exp#>}{<u:eq x x#>} (<f:exp#> -> <eq f f>) =

     {<app>}{<lam>}{<eq_app>}{<eq_lam>}
     fn W => fn {<x>} {<u>} (x => <u>)  
          | [<e:exp#>] {<x>} {<u>} (e => (let
					   val result = W e
					 in
					   {<x>}{<u>} result
					 end) \x \u);


fun eqfun : {<app  : exp -> exp -> exp>}
	    {<lam  : (exp -> exp) -> exp>}
            {<eq_app : {E1} {E2} {F1} {F2} eq E1 F1 -> eq E2 F2 -> eq (app E1 E2) (app F1 F2)>}
            {<eq_lam : {E} {F} ({x}eq x x -> eq (E x) (F x)) -> eq (lam E) (lam F)>}
	    (<f:exp#> -> <eq f f>) -> <e:exp> -> <eq e e> =     
     {<app>}{<lam>}{<eq_app>}{<eq_lam>}
     fn W =>
       (fn <app E1 E2> => (case (((eqfun \app \lam \eq_app \eq_lam) W <E1>), ((eqfun \app \lam \eq_app \eq_lam) W <E2>))
                                of (<D1>, <D2>) => <eq_app _ _ _ _ D1 D2>)
         | <lam E> => (case ({<x>}{<u>} (eqfun \app \lam \eq_app \eq_lam) (((extend \app \lam \eq_app \eq_lam) W) \x \u) <E x>)
                            of ({<x>}{<u>} <D x u>) => <eq_lam _ _ D>)

         | [<x:exp#>] <x> => W x) ;

val eq'1  = {<app>}{<lam>}{<eq_app>}{<eq_lam>} (eqfun \app \lam \eq_app \eq_lam) (fn .) <lam [x] x>;
val eq'2  = {<app>}{<lam>}{<eq_app>}{<eq_lam>} (eqfun \app \lam \eq_app \eq_lam) (fn .) <lam [x] app x x>;
val eq'3  = {<app>}{<lam>}{<eq_app>}{<eq_lam>} (eqfun \app \lam \eq_app \eq_lam) (fn .) <app (lam [x] x) (lam [x] x)>;
val eq'4  = {<app>}{<lam>}{<eq_app>}{<eq_lam>} (eqfun \app \lam \eq_app \eq_lam) (fn .) <lam [x] lam [y] x>;
