Require Import Coq.Lists.List. (* nth_error *)
Require Import Coq.Arith.Compare_dec. (* lt_dec *)

(* Memoized Course of Value induction *)

Definition COV_Form (A:nat->Type) := (forall (n:nat), (forall (m:nat), m<n -> A(m))->A(n)) -> forall (n:nat), A(n).
Axiom COV : forall A, COV_Form A.

(* Immutable Arrays from Haskell *)

Axiom ListArray : Set -> Set.

Axiom l2a : forall {A : Set}, list A -> ListArray A.

Axiom alen : forall {A : Set}, ListArray A -> nat.

Axiom alen_l2a : forall {A : Set} (l : list A), alen (l2a l) = length l.
      
Axiom anth_error : forall {A : Set}, ListArray A -> nat -> option A.

Axiom anth_nth : forall {A : Set} (l : list A) (n : nat),
    anth_error (l2a l) n = nth_error l n.

Extraction Language Haskell.
Extract Constant COV => "cov".
Extract Constant ListArray "a" => "Array Int a".
Extract Constant l2a => "listToArray".
Extract Constant alen => "arrayLen".
Extract Constant anth_error => "maybeArrayNth".