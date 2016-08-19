(* Sample programs related to first-order logic *)
(* Author: Carsten Schuermann, Adam Poswolsky *)

<o : type>
<i : type>
<eq : i -> i -> o>
<imp : o -> o -> o>
<forall : (i -> o) -> o>

plus : <rational> -> <rational> -> <rational>
 = <X> |--> <Y> |--> <X + Y> ;

cnteq : <o> -> <rational> 
 = <eq X Y> |--> <1>
 | <imp F1 F2> |--> plus (cnteq <F1>) (cnteq <F2>)
 | <forall F> |--> {t:i} case (cnteq <F t>) of
     (<N> |--> pop <N>) ;


c1 = cnteq <forall [x] eq x x> ;
c2 = cnteq <forall [x] forall [y] imp (eq x y) (eq y x)> ;
c3 = cnteq <forall [x] forall [y] forall [z]
              imp (eq x y) (imp (eq y z) (eq x z))> ;


