(* Carsten Schuermann *)
(* Some little examples *)

sig <nat : type>
    <z : nat>
    <s : nat -> nat>
    <exp : type>
    <lam : (exp -> exp) -> exp>
    <app : exp -> exp -> exp>;

fun binary : <nat> -> <x:exp#> -> <exp>
           = fn <z> => (fn [<x:exp#>] x => <x>)
	      | <s N> => (fn [<x:exp#>] x =>
	            <app> @ (binary <N> x) @ (binary <N> x));

val result1 = {<x:exp>} binary <s (s (s (s (s z))))> x;

fun inc : <E:exp#>*<nat> -> <E:exp#>*<nat> =
    fn [<x:exp#>] (x, <N>) => (x, <s N>);

fun find : (<E1:exp#> -> <E2:exp#>*unit) -> <E1:exp#> -> <E2:exp#>*<nat> 
         = fn W => fn [<x:exp#>] x 
	      => (case W x
	            of ( x, () ) => (x, <z>)
	             | [<y:exp#>] ( y, () ) => inc (find W y));


val result = {<a:exp#>} {<b:exp#>} {<c:exp#>}
                  let
                      fun W : <E:exp#> -> <E:exp#>*unit
                            = fn a => (b,())
                               | b => (c,())
			       | c => (c,()) (* RATHER than have an option, it just stops when it maps to itself *)
	          in
		      find W a
                  end;

