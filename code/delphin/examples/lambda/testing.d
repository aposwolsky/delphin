(* Testing properties about lambda expressions *)
(* Author: Adam Poswolsky, Carsten Schuermann *)

sig  <exp : type>
     <app : exp -> exp -> exp>
     <lam : (exp -> exp) -> exp>;

sig  <bool : type>
     <true : bool>
     <false : bool>;

params = <exp> ;


fun not : <bool> -> <bool> 
 = fn <true>  => <false>
    | <false> => <true> ;
 
fun or : <bool> -> <bool> -> <bool> 
 = fn <true> <true>   =>  <true>
    | <true> <false>  =>  <true>
    | <false> <true>  =>  <true>
    | <false> <false> =>  <false> ;

fun conj : <bool> -> <bool> -> <bool> 
 = fn <true> <B>  => <B>
    | <false> <B> => <false> ;

fun const : <exp -> exp> -> <bool> 
= fn [<y#>] <[x:exp] y> =>  <true>
   | <[x:exp] x> =>  <false>
   | <[x:exp] app (E1 x) (E2 x)> => conj (const <[x:exp] E1 x>) (const <[x:exp] E2 x>)
   | <[x:exp] lam [y:exp] E x y> => case ({<y:exp#>} const <[x:exp] E x y>) of ({<y>}<B> => <B>) ;

val c1  = const <[x:exp] x>;
val c2  = const <[x:exp] app x x>;
val c3  = const <[x:exp] app (lam [y:exp] y) (lam [y:exp] y)>;
val c4  = const <[x:exp] lam [y] x>;
	
params = .;

fun betatest : <exp> -> < bool> 
 = fn <lam F>     =>  <false>
    | <app E1 _> =>  case <E1> of <lam F>  =>  <true>
                                 | <app _ _> => <false> ;

val b1  = betatest <lam [x] x>;
val b2  = betatest <lam [x] app x x>;
val b3  = betatest <app (lam [x] x) (lam [x] x)>;
val b4  = betatest <lam [x] lam [y] x>;


fun idtest : <exp -> exp> -> <bool> 
 = fn <[x:exp] x> => <true>
    | [<y#>] <[x:exp] y> => <false>
    | <[x:exp] app (E1 x) (E2 x)> => <false>
    | <[x:exp] lam [y:exp] E x y> => <false> ;

val i1  = idtest <[x:exp] x>; 
val i2  = idtest <[x:exp] app x x>;
val i3  = idtest <[x:exp] app (lam [y:exp] y) (lam [y:exp] x)>;
val i4  = idtest <[x:exp] lam [y:exp] x>;


fun etatest : <exp> -> < bool> 
 = fn <lam E> => ( case <E> of <[x:exp] lam [y:exp] E' x y> => <false>
                            | <[x:exp] app (E1' x) (E2' x)> => conj (const <E1'>) (idtest <E2'>)
			    | <[x:exp] x> => <false>)
    | <app E1 E2> => <false> ;

val e1 = etatest <lam [x:exp] x>;
val e2 = etatest <lam [x:exp] app x x>;
val e3 = etatest <app (lam [x:exp] x) (lam [x:exp] x)>;
val e4 = etatest <lam [x:exp] lam [y:exp] x>;
val e4 = etatest <lam [x:exp] lam [y:exp] x>;