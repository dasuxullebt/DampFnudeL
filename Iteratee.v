Inductive Payload (el : Set) : Set :=
| Chunk : list el -> Payload el
| EOF : Payload el.

Inductive Iteratee (el o err : Set) (ret : Set) : Set :=
| Done : ret -> Iteratee el o err ret
| Continue : option err ->
             (Payload el o -> (Iteratee el o err ret * Payload el o)%type) ->
             Iteratee el o err ret.

Function Enumerator (el o err ret : Set) :=
  Iteratee el o err ret -> Iteratee el o err ret.


(*
Iteratees

Iteratees are an approach of stateful streamed I/O which tries to combine the ease of use of lazy I/O and the correctness of monadic I/O. In our Deflate implementation, we try to use them as a replacement of our formerly used concept of strong decidability. The reason is that strong decidability relies on lazy I/O, but in our efforts to minimize the trusted codebase and optimize the code, we want to extract to OCaml rather than Haskell.
*)