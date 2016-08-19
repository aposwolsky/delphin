(* Dummy Unsafe Structure
 * For use in compiling output of ml-lex
 * using Poly/ML
 * (Only necessary for older versions of ml-lex it seems)
 *)

structure Unsafe =
  struct
    structure Vector = Vector
    structure CharVector = CharVector
  end
