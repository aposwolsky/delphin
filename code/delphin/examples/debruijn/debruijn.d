(* Debruijn expressions *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig	<exp  : type>
	<app  : exp -> exp -> exp>
	<lam  : (exp -> exp) -> exp>;

sig	<db   : type>
	<v    : rational -> db>
	<l    : db -> db>
	<a    : db -> db -> db>;

(* ******************************************* *)
(* Conversion using payload-carrying parameters *)
(* ******************************************* *)

fun db-Payload : <exp> -> <rational> -> <db> =
   fn [<x#>] <x M> => (fn <N> => <v (N + (~ M))> )
   | <app E1 E2>   => (fn <N> =>  <a> @ (db-Payload <E1> <N>) 
                                    @ (db-Payload <E2> <N>))
   | <lam E> => (fn <N> =>  
        case {<x:rational -> exp #>} (db-Payload <E (x (N + 1))> <N + 1>) of
            ({<x>}<F> => <l F>)) ;

fun db-Payload-trans : <exp> -> <db> =
 fn <E> => db-Payload <E> <1> ;

val db'1  = db-Payload-trans <lam [x] x> ;
val db'2  = db-Payload-trans <lam [x] app x x> ;
val db'3  = db-Payload-trans  <app (lam [x] x) (lam [x] x)>;
val db'4  = db-Payload-trans  <lam [x] lam [y] x>;


(* ******************************************* *)
(* Conversion using delphin function saving 
 * mapping of parameters *)
(* ******************************************* *)
type world = (<x:exp#> -> <rational>)


fun extend : world -> <rational> -> {<x:exp#>}world =
    fn W <n> => fn {<x#>} (x => <n>)
                 | [<x'>]{<x#>} (x' => (let val R = W x'
                                           in {<x>} R
                                        end) \x);

fun db : world -> <exp> -> <rational> -> <db> =
   fn W => 
     (fn [<x#>] <x> => let 
                         val <M> = W x 
                       in 
                         (fn <N> => <v (N + (~ M))> )
                       end
       | <app E1 E2> => (fn <N> =>  <a> @ (db W <E1> <N>) 
                                   @ (db W <E2> <N>))
       | <lam E> => (fn <N> =>  
          case {<x:exp #>} (db ((extend W <N + 1>) \x) <E x> <N + 1>) of
            ({<x>}<F> => <l F>))) ;

fun db-trans : <exp> -> <db> =
 fn <E> => db (fn .) <E> <1> ;

val db'1  = db-trans <lam [x] x> ;
val db'2  = db-trans <lam [x] app x x> ;
val db'3  = db-trans  <app (lam [x] x) (lam [x] x)>;
val db'4  = db-trans  <lam [x] lam [y] x>;
