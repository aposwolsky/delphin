sig use "test.elf";

fun plus : <nat> -> <nat> -> <nat> * unit
 = fn <z> => (fn [<n:nat>] <n> => (<n>, ()))
    | [<n1 : nat>]<s n1> => fn [<n2:nat>] <n2> => 
	        case ((plus <n1> <n2>) : <nat> * unit)
	        of [<n3:nat>]((<n3>,()) : <nat> * unit) => ((<s n3>, ()) : <nat> * unit);
