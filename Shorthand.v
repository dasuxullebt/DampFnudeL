Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.NArith.BinNatDef.
Require Import String.
Require Import Coq.Arith.Compare_dec. (* nat_compare *)

Notation vec := Vector.t.
Notation LB := (list bool).
Notation ll := List.length.
Notation lb := (ll (A:=bool)).

Notation Bnil := (nil (A := bool)).
Notation VecLB := (vec LB).

Notation Byte := (vec bool 8).

Notation LByte := (list Byte).

Notation Vnth := Vector.nth.

Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.
Notation Vmap := Vector.map.

Notation fin_rect2 := Fin.rect2.
Notation FS_inj := Fin.FS_inj.
Notation fin := Fin.t.
Notation FinLR := Fin.L_R.
Notation FinFS := Fin.FS.
Notation FinF1 := Fin.F1.

(** The n-th element of the given vector is the given element. This is so we can 
use natural numbers instead of Fin.t as indices *)
(* TODO: This should be obsolete when we use maps *)
Inductive Vnth_is {A : Type} : forall (n : nat), nat -> vec A n -> A -> Prop :=
| vnthIsZero : forall a n b, Vnth_is (S n) 0 (Vcons _ a _ b) a
| vnthIsCons : forall a n m x b, Vnth_is n m b a -> Vnth_is (S n) (S m) (Vcons _ 
x _ b) a.

Fixpoint Vnth_err {A : Type} {n : nat} (v : vec A n) (m : nat) : option A :=
  match nat_compare m n as nc return (nat_compare m n = nc -> _) with
    | Eq => fun _ => None
    | Gt => fun _ => None
    | Lt => fun eq =>
              Some (Vnth v (Fin.of_nat_lt (nat_compare_Lt_lt _ _ eq)))
  end eq_refl.

Function pi2 {A B} (x : A) (y : B) := y.

Fixpoint blstring (l : LB) : string :=
  match l with
    | nil => ""%string
    | (b :: L) =>
      ((match b with
          | false => "0"%string
          | true => "1"%string
        end) ++ blstring L)%string
  end.

(** From http://poleiro.info/posts/2013-04-03-parse-errors-as-type-errors.html *)

Definition forceOption A Err (o : option A) (err : Err) : match o with
                                                            | Some _ => A
                                                            | None => Err
                                                          end :=
  match o with
    | Some a => a
    | None => err
  end.

Inductive parseError := ParseError.

Fixpoint strToNat (strn : string) : option nat :=
  (fix rc str n :=
   match str with
     | EmptyString => Some n
     | String "0" str => rc str ((10 * n) + 0)
     | String "1" str => rc str ((10 * n) + 1)
     | String "2" str => rc str ((10 * n) + 2)
     | String "3" str => rc str ((10 * n) + 3)
     | String "4" str => rc str ((10 * n) + 4)
     | String "5" str => rc str ((10 * n) + 5)
     | String "6" str => rc str ((10 * n) + 6)
     | String "7" str => rc str ((10 * n) + 7)
     | String "8" str => rc str ((10 * n) + 8)
     | String "9" str => rc str ((10 * n) + 9)
     | _ => None
   end) strn 0.

Definition d (s : string) :=
  forceOption nat parseError (strToNat s) ParseError.

Example e1 : (d"22" : nat) = 22.
Proof. reflexivity. Qed.

Example e3 : (d"1O" : parseError) = ParseError.
Proof. reflexivity. Qed.
