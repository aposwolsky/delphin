sig
<o : type> 
<ar : o -> o -> o> %infix right 10
<nd : o -> type>
<impi : (nd A -> nd B) -> nd (A ar B)> 
<impe : nd (A ar B) -> nd A -> nd B> 
<comb : o -> type> 
<k : comb (A ar B ar A)>
<s : comb ((A ar B ar C) ar (A ar B) ar A ar C) > 
<mp : comb (A ar B) -> comb A -> comb B> ;

fun ba : <A:o> -> <B:o> -> <comb A -> comb B> -> <comb (A ar B)> = fn . ;
fun convert : <D:nd A> -> <comb A> =
      fn <impi D'> => (case ({<d>}{<u>} convert <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <_> <_> <D''>);


fun convert : <<A : o>> -> <D:nd A> -> <comb A> =
      fn <impi D'> => (case ({<d>}{<u>} convert <D' d>)
	                                       of ({<d>}{<u>} <D'' u>) => ba <_> <_> <D''>);



fun convert : <<A : o>> -> <D : nd A> -> <comb A> = 
   fn [<X1 : o>] [<X2 : o>] [<D' : nd X1 -> nd X2>] (<impi ([x:nd X1] D' x)> =>
                                                        (fn [<D'' : comb X1 -> comb X2>] ({<d : nd X1#>} {<u : comb X1#>} <D'' u> =>
                                                                                             ba <X1> <X2> <[x:comb X1] D'' x>))
                                                           ({<d : nd X1#>} {<u : comb X1#>} convert <D' d>));

fun convert : <A : o> -> <D : nd A> -> <comb A> = 
   fn [<X1 : o>] [<X2 : o>] [<D' : nd X1 -> nd X2>] (<_> and <impi ([x:nd X1] D' x)> =>
                                                        (fn [<D'' : comb X1 -> comb X2>] ({<d : nd X1#>} {<u : comb X1#>} <D'' u> =>
                                                                                             ba <X1> <X2> <[x:comb X1] D'' x>))
                                                           ({<d : nd X1#>} {<u : comb X1#>} convert <_> <D' d>)) ;


