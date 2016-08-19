(*
% Test for copy theorem
% Author: Adam Poswolsky (converted from cp.elf by Carsten Schuermann)
*)

sig <exp : type>
    <app : exp -> exp -> exp>
    <lam : (exp -> exp) -> exp>
    <callcc : ((exp -> exp) -> exp) -> exp>
    <reset  : (((exp -> exp) -> exp) -> exp) -> exp>;

sig <exp' : type>
    <app' : exp' -> exp' -> exp'>
    <lam' : (exp' -> exp') -> exp'>
    <callcc' : ((exp' -> exp') -> exp') -> exp'>
    <reset'  : (((exp' -> exp') -> exp') -> exp') -> exp'>;

type expWorld1 = <x:exp#> -> <exp'>;
type expWorld2 = <c:exp -> exp#> -> <exp' -> exp'>;
type expWorld3 = <c:(exp -> exp) -> exp#> -> <(exp' -> exp') -> exp'>;

fun extend : expWorld1 -> {<x:exp>}{<y:exp'>}expWorld1
   = fn W => (fn {<x:exp#>}{<y:exp'#>} (x => <y>)
               | [<x'#>] {<x>}{<y>} (x' => (pop y pop x 
                                            let val R = W x'
                                                in {<x>}{<y>}R
                                                end)));


fun extend2 : expWorld2 -> {<c:exp -> exp>}{<d:exp' -> exp'>}expWorld2
   = fn W => (fn {<x#>}{<y#>} (x => <y>)
               | [<x'#>] {<x>}{<y>} (x' => (pop y pop x 
                                            let val R = W x'
                                                in {<x>}{<y>}R
                                                end)));

fun extend3 : expWorld3 -> {<c:(exp -> exp ) -> exp>}{<d:(exp' -> exp') -> exp'>}expWorld3
   = fn W => (fn {<x#>}{<y#>} (x => <y>)
               | [<x'#>] {<x>}{<y>} (x' => (pop y pop x 
                                            let val R = W x'
                                                in {<x>}{<y>}R
                                                end)));

fun cp : expWorld1 -> expWorld2 -> expWorld3 -> <exp> -> <exp'>
   = fn [<x:exp#>] W1 W2 W3 <x> => W1 x
      | [<c:exp -> exp#>][<x:exp#>] W1 W2 W3 <c x> => (W2 c) @ (W1 x)
      | [<c:(exp -> exp) -> exp#>][<f:(exp -> exp)#>] W1 W2 W3 <c f> => (W3 c) @ (W2 f) 
      | W1 W2 W3 <app D1 D2> =>
                    let val <E1> = cp W1 W2 W3 <D1>
                        val <E2> = cp W1 W2 W3 <D2>
                    in
                        <app' E1 E2>
                    end

      | W1 W2 W3 <lam [x:exp] D x> =>
                     (case ({<x>}{<y>} cp ((extend W1) \x \y) W2 W3 <D x>)
                         of {<x>}{<y>}<E y> => <lam' ([y:exp'] E y)>)


      | W1 W2 W3 <callcc [c:exp -> exp] E c> =>
                     (case ({<c:exp -> exp>}{<d:exp' -> exp'>}
                             cp W1 ((extend2 W2) \c \d) W3 <E c>)
                        of {<c>}{<d>} <F d> => <callcc' [d:exp' -> exp'] F d>)

      | W1 W2 W3 <reset [c: (exp -> exp) -> exp] E c> =>
                     (case ({<c:(exp -> exp) -> exp>}{<d:(exp' -> exp') -> exp'>}
                             cp W1 W2 ((extend3 W3) \c \d) <E c>)
                        of {<c>}{<d>} <F d> => <reset' [d: (exp' -> exp') -> exp'] F d>);
