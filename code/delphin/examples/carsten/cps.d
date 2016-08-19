(* Translation into cps form *)
(* Author: Carsten Schuermann *)

sig
  < exp : type >
  < app : exp -> exp -> exp >
  < lam : (exp -> exp) -> exp >
  < s = lam [x] lam [y] lam [z] app (app x z) (app y z)>
  < k = lam [x] lam [y] x>;

fun cps : (<e:exp #> -> <exp>) -> <exp> -> <exp> = 
  fn W => 
  (fn <app E1 E2> => (case ((cps W <E1>), (cps W <E2>))
                                of (<C1>, <C2>) => <lam [k] app C1 (lam [m] app C2 
	     	         	     	     (lam [n] (app (app m n) k)))>)
   | <lam E> => (case ({<x>} cps ((fn {<x>} (x => <lam [k] app k x>)  
                                          | [<e:exp#>] {<x>} (e => ({<x>} W e) \x)) \x) <E x>)
                            of ({<x>} <C x>) => <lam [k] app k (lam [x] C x)>)
   | [<x:exp#>] <x> => W x) ;


val example1 = cps (fn .) <lam [x] app x x>;
val example2 = cps (fn .) <app (app s k) k>;
