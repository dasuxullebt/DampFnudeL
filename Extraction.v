Require Import Ascii.
Require Import String.
(*Require Import Coq.Vectors.Fin.*)
Require Import Coq.Vectors.Vector.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Init.Nat.

Require Import Shorthand.

Extraction Language Haskell.

(** Strings *)

Extract Inductive ascii => "Data.Char.Char" ["Extraction.makechar"] "Extraction.charrec".

Extract Inductive string => "[Data.Char.Char]" ["[]" "(:)"] "Extraction.stringrec".

(** Several simple types mapped to Haskell-standard-types *)

Extract Inductive prod => "(,)" ["(,)"] "Extraction.prodrec".
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".

Extract Inductive option => "Data.Maybe.Maybe" [ "Data.Maybe.Just" "Data.Maybe.Nothing" ].

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"] "Extraction.sumboolrec".

Extract Inductive sumor => "Data.Maybe.Maybe" [ "Data.Maybe.Just" "Data.Maybe.Nothing" ]
                                              "Extraction.sumorrec".

Extract Inductive comparison => "Extraction.Cmp" ["Extraction.Eq" "Extraction.Lt" "Extraction.Gt"]
                                                 "Extraction.cmprec".


(** Fin is just nat with an index that is not relevant *)
Extract Inductive fin => "Extraction.Fin" [ "Extraction.fin1" "Extraction.fins" ] "Extraction.finrec".

(** Constants for nat *)

Extract Inductive nat => "Prelude.Int" ["0" "Extraction.natinc"] "Extraction.natrec".

Extract Constant lt_eq_lt_dec => "Extraction.lt_eq_lt_dec".

Extract Constant le_lt_dec => "(Prelude.<=)".

Extract Constant nat_compare => "Extraction.nat_compare".

Extract Constant plus => "(Prelude.+)".

Extract Constant mult => "(Prelude.*)".

Extract Constant minus => "Extraction.natminus".

Extract Constant pow => "(Prelude.^)".

Extract Inductive list => "[]" [ "[]" "(\ a b -> a : b)" ]
                               "(\ n c l -> case l of { [] -> n [] ; (b : bs) -> c b bs })".

Extract Inductive vec => "Extraction.Vec" ["Extraction.vecNil" "Extraction.vecCons"] "Extraction.vecRec".

(* Extraction "EfficientDecompress/EfficientDecompress.hs" DeflateTest. *)
