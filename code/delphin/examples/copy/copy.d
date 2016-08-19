(* Equivalence of single and double eigenvariable 
 * definitions of copy. 
 * Author: Adam Poswolsky
 * Based on a similar proof in Abella by Andrew Gacek (http://abella.cs.umn.edu/examples/copy.html)
 *
 * Here we take two definitions of copy and show they are equivalent.
 *)

sig <exp : type> %name E x
    <app : exp -> exp -> exp>
    <lam : (exp -> exp) -> exp>;

sig <copy : exp -> exp -> type>
    <cp_app : copy E1 F1 -> copy E2 F2 -> copy (app E1 E2) (app F1 F2)>
    <cp_lam : ({x} copy x x -> copy (E x) (F x)) 
               -> copy (lam [x] E x) (lam [x] F x)>;

sig <copy2 : exp -> exp -> type>
    <cp_app2 : copy2 E1 F1 -> copy2 E2 F2 -> copy2 (app E1 E2) (app F1 F2)>
    <cp_lam2 : ({x}{y} copy2 x y -> copy2 (E x) (F y)) 
               -> copy2 (lam [x] E x) (lam [x] F x)>;

params = <exp>, <copy (x#) (y#)>, <copy2 (x#) (y#)>;
(* All of our functions handle parameters of the above types.. *)


(* We first show that copy implies copy2 *)

fun copy2_align : <{x} copy2 x x -> copy2 (E x) (F x)>
                 -> <{x}{y} copy2 x y -> copy2 (E x) (F y)> 
   = fn <[x][d] cp_app2 (D1 x d) (D2 x d)> 
                 => 
                    let
		      val <D1'> = copy2_align <D1>
		      val <D2'> = copy2_align <D2>
		    in
		      <[x][y][d] cp_app2 (D1' x y d) (D2' x y d)>
		    end

      | <[x][d] cp_lam2 [x2][y2][d2] (D x d x2 y2 d2)>
                   => (case {<x2>}{<y2>}{<d2 : copy2 x2 y2>} copy2_align <[x][d] D x d x2 y2 d2>
                        of {<x2>}{<y2>}{<d2>} <[x][y][d] D' x y d x2 y2 d2>
                                      => <[x][y][d] cp_lam2 [x2][y2][d2] (D' x y d x2 y2 d2)>)

      | <[x][d:copy2 x x] d> => <[x][y][d:copy2 x y] d> 

      | <[x][d] (u#)> => <[x][y][d] u> (* parameter case *)   ;


type ctxProp1 = <(copy x y)#> -> <copy2 x y>; (* every copy parameter in the context
					       * also has a copy2 parameter in the context
					       * with the same mapping
                                               *)
fun copy_to_copy2 : ctxProp1 -> <copy E F> -> <copy2 E F>
    = fn W <cp_app D1 D2> => 
             let
	       val <D1'> = copy_to_copy2 W <D1>
	       val <D2'> = copy_to_copy2 W <D2>
	     in
	       <cp_app2 D1' D2'>
	     end

       | W <cp_lam [x][d] D x d> => 
	     (case ({<x>}{<d:copy x x>}{<d2:copy2 x x>} 
                        copy_to_copy2 (W with <d> => <d2>) <D x d>)
	       of {<x>}{<d>}{<d2>} <D' x d2> => 
		    let
		      val <D''> = copy2_align <D'>
		    in
		      <cp_lam2 D''>
		    end)

       | W <d#> => W <d> (* in the base case we apply the parameter function *) ;



(* We now show that copy2 implies copy *)

fun copy_align : <{x}{y} copy x y -> copy (E x) (F y)>
                 -> <{x} copy x x -> copy (E x) (F x)> 
   = fn <[x][y][d] cp_app (D1 x y d) (D2 x y d)> 
                 => 
                    let
		      val <D1'> = copy_align <D1>
		      val <D2'> = copy_align <D2>
		    in
		      <[x][d] cp_app (D1' x d) (D2' x d)>
		    end

      | <[x][y][d] cp_lam [x2][d2] (D x y d x2 d2)>
                   => (case {<x2>}{<d2>} copy_align <[x][y][d] D x y d x2 d2>
                        of  {<x2>}{<d2>} <[x][d] D' x d x2 d2>
                                      => <[x][d] cp_lam [x2][d2] (D' x d x2 d2)>)

      | <[x][y][d:copy x y] d> => <[x][d:copy x x] d> 
      | <[x][y][d] (u#)> => <[x][d] u> (* parameter case *)   ;


type ctxProp2 = <(copy2 x y)#> -> <copy x y>; (* every copy2 parameter in the context
					       * also has a copy parameter in the context
					       * with the same mapping
                                               *)

fun copy2_to_copy : ctxProp2  -> <copy2 E F> -> <copy E F>
    = fn W <cp_app2 D1 D2> => 
             let
	       val <D1'> = copy2_to_copy W <D1>
	       val <D2'> = copy2_to_copy W <D2>
	     in
	       <cp_app D1' D2'>
	     end

       | W <cp_lam2 [x][y][d] D x y d> => 
	     (case ({<x>}{<y>}{<d:copy2 x y>}{<d2:copy x y>} 
                        copy2_to_copy (W with <d> => <d2>) <D x y d>)
	       of {<x>}{<y>}{<d>}{<d2>} <D' x y d2> => 
		    let
		      val <D''> = copy_align <D'>
		    in
		      <cp_lam D''>
		    end)

       | W <d#> => W <d> (* in the base case we apply the parameter function *) ;

