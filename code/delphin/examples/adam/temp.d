(* Natural Numbers *)
sig <nat : type>
    <z : nat>;

(* this works!, but it doesn't when we separate it otu..
val adam =
	let fun plus = fn <N> => <N>
          in plus <z>
         end       ;
*)


fun plus = fn () => ();
val adam = plus () ;
