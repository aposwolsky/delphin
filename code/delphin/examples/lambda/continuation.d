(* Continuation Semantics *)
(* Author: Adam Poswolsky, Carsten Schuermann, Jeffrey Sarnat *)

sig <exp  : type>
    <cont : type>
    <num  : rational -> exp>
    <plus : exp -> exp -> exp>
    <mult : exp -> exp -> exp>
    <app  : exp -> exp -> exp>
    <lam  : (exp -> exp) -> exp>
    <callcc : (cont -> exp) -> exp>
    <throw  : cont -> exp -> exp>;

fun init : <exp> -> (<cont> -> <exp> -> <exp>) -> <exp> 
     = fn <X> L => <X> ;

fun eval : <exp> -> (<exp> -> (<cont> -> <exp> -> <exp>) -> <exp>) -> (<cont> -> <exp> -> <exp>) -> <exp> =
    fn <app E1 E2> K => eval <E1> (fn <lam X1> => eval <E2> (fn <V> => eval <X1 V> K)) 
     | <lam E> K     =>  K <lam E> 
     | <num N> K     =>  K <num N>  
     | <plus E1 E2> K  => eval <E1> (fn <num N1> => eval <E2> (fn <num N2> => K <num (N1 + N2)>)) 
     | <mult E1 E2> K => eval <E1> (fn <num N1> => eval <E2> (fn <num N2> => K <num (N1 * N2)>)) 
     | <callcc E>   K => (fn L =>  (case {<k:cont#>} (eval <E k> K (fn <k> <X> => K <X> L
                                                                     | <K'> <X> => L <K'> <X>)) 
                                     of ({<k>}X => X)))
     | [<k#>] <throw k E>  K => eval <E> (fn <X> => fn L' => L' <k> <X>)
 ;


fun eval' = fn <E> => eval <E> init (fn .);
 
val eval'1 = eval' <lam [x] x>;
val eval'2 = eval' <lam [x] app x x>;
val eval'3 = eval' <app (lam [x] x) (lam [x] x)>;
val eval'4 = eval' <lam [x] lam [y] x>;
val eval'5 = eval' <mult (num 6) (num 7)>;
val eval'6 = eval' <callcc [k] plus (num 2) (throw k (mult (num 3) (num 4)))>;
val eval'7 = eval' <callcc [k] throw k (plus (throw k (num 7)) (num 1) )>;
val eval'8 = eval' <app (callcc [k] lam [x] throw k x) (lam [x] x)> ;

