Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import NArith.
Require Import Omega.
Require Import Program.

Require Import Transports.
Require Import Shorthand.
Require Import Combi.

(* TODO: can this be prop? *)
(** Convert a binary number (boolean list) into a nat, interpret it ad least-significant-bit-first *)
Inductive LSBnat : LB -> nat -> Set :=
| nilLSBnat : LSBnat nil 0
| zeroLSBnat : forall a b, LSBnat a b -> LSBnat (false :: a) (b+b)
| oneLSBnat : forall a b, LSBnat a b -> LSBnat (true :: a) (1+b+b).

Theorem LSBnat_unique : forall l m n, LSBnat l m -> LSBnat l n -> m = n.
Proof.
  induction l.
  destruct m.
  destruct n.
  auto.
  intros ? Q.
  inversion Q.
  destruct n.
  intro Q.
  inversion Q.
  intro Q.
  inversion Q.

  intros m n.
  destruct a.
  intros Q R.
  inversion Q.
  inversion R.
  auto.
  intros Q R.
  inversion Q.
  inversion R.
  auto.
Qed.

Fixpoint ListToNat (l : LB) : nat :=
  match l with
    | nil => 0
    | (true :: l) => let b := ListToNat l in 1 + b + b
    | (false :: l) => let b := ListToNat l in b + b
  end.

Theorem ListToNat_correct : forall l, LSBnat l (ListToNat l).
Proof.
  induction l.
  compute.
  constructor.
  destruct a.
  constructor.
  auto.
  constructor.
  auto.
Qed.

Function ByteToNat (b : Byte) := ListToNat (to_list b).

Theorem lsb_power : forall lsbn n, LSBnat lsbn n -> n < (2 ^ (ll lsbn)).
Proof.
  intros lsbn n L.
  induction L.
  auto.
  replace (2 ^ (ll (false :: a))) with ((2 ^ (ll a)) + (2 ^ (ll a))).
  omega.
  compute.
  auto.
  replace (2 ^ (ll (true :: a))) with ((2 ^ (ll a)) + (2 ^ (ll a))).
  omega.
  compute.
  auto.
Defined.

Definition ByteToFin256_ : forall n, Byte -> fin (256 + n).
Proof.
  intro n.
  refine (fun b => @Fin.of_nat_lt (ByteToNat b) (256 + n) _).
  assert (ByteToNat b < 256).
  unfold ByteToNat.
  replace 256 with (2 ^ lb (to_list b)).
  apply lsb_power.
  apply ListToNat_correct.
  rewrite -> to_list_length.
  reflexivity.
  omega.
Defined.

Definition ByteToFin256 := ByteToFin256_ 0.

Definition ByteToFin288 := ByteToFin256_ (288 - 256).  

Lemma LSBnat_left_unique : forall l1 l2 m,
                               ll l1 = ll l2 ->
                               LSBnat l1 m -> LSBnat l2 m ->
                               l1 = l2.
Proof.
  induction l1.
  intros l2 m len.
  destruct l2.
  auto.
  inversion len.

  intros.
  destruct l2.
  inversion H.
  destruct a.
  destruct b.
  inversion H0.
  inversion H1.
  f_equal.
  apply (IHl1 l2 b).
  compute.
  compute in H.
  omega.
  trivial.
  assert (BB0 : b = b0).
  omega.
  rewrite -> BB0.
  trivial.
  inversion H0.
  inversion H1.
  omega.
  destruct b.
  inversion H0.
  inversion H1.
  omega.
  inversion H0.
  inversion H1.
  f_equal.
  apply (IHl1 l2 b).
  compute.
  compute in H.
  omega.
  trivial.
  replace b with b0.
  trivial.
  omega.
Qed.

Lemma ListToNat_inj : forall l1 l2, ll l1 = ll l2 -> ListToNat l1 = ListToNat l2 -> l1 = l2.
Proof.
  intros.
  apply (LSBnat_left_unique l1 l2 (ListToNat l1)).
  trivial.
  apply ListToNat_correct.
  rewrite -> H0.
  apply ListToNat_correct.
Qed.

Lemma ByteToNat_inj : forall b1 b2, ByteToNat b1 = ByteToNat b2 -> b1 = b2.
Proof.
  intros.
  apply to_list_inj.
  apply ListToNat_inj.
  rewrite -> to_list_length.
  rewrite -> to_list_length.
  reflexivity.
  apply H.
Qed.  

(* TODO : nach LSB.v *)
Lemma ByteToNatMax : forall n, ByteToNat n < 256.
Proof.
  intro n.
  unfold ByteToNat.
  assert (g1 : ListToNat (to_list n) < 2 ^ ll (to_list n)).
  apply lsb_power.
  apply ListToNat_correct.
  assert (g2 : ll (to_list n) = 8).
  apply to_list_length.
  rewrite -> g2 in g1.
  exact g1.
Qed.

Lemma NatToList : forall (l m : nat), m < 2 ^ l -> {L : LB & LSBnat L m & ll L = l }.
Proof.
  induction l.
  intros m mle.
  destruct m.
  exists Bnil.
  constructor.
  reflexivity.
  compute in mle.
  omega.
  intros m mle.
  set (m2 := m mod 2).
  set (md := m / 2).
  assert (M : m = 2 * md + m2).
  apply div_mod.
  omega.
  assert (mxl2l : md < 2 ^ l).
  assert (K : 2 ^ (S l) = 2 * (2 ^ l)).
  reflexivity.
  rewrite -> K in mle.
  omega.
  destruct (IHl md mxl2l) as [L' lsbn lbL].

  assert (m2 < 2).
  unfold m2.
  apply (mod_bound_pos m 2).
  omega.
  omega.

  destruct m2.
  exists (false :: L').
  rewrite -> M.
  replace (2 * md + 0) with (md + md).
  constructor.
  exact lsbn.
  omega.
  unfold ll.
  unfold ll in lbL.
  omega.

  destruct m2.
  exists (true :: L').
  rewrite -> M.
  replace (2 * md + 1) with (1 + md + md).
  constructor.
  exact lsbn.
  omega.
  unfold ll.
  unfold ll in lbL.
  omega.

  omega.
Qed.

Lemma NatToByte : forall m, m < 256 -> {b : Byte | ByteToNat b = m}.
Proof.
  intros m H.
  destruct (NatToList 8 m) as [A B C].
  auto.
  exists (vec_id C (of_list A)).
  unfold ByteToNat.
  dependent destruction C.
  rewrite -> vec_id_destroy.
  rewrite -> to_list_of_list_opp.
  assert (B' : LSBnat A (ListToNat A)).
  apply ListToNat_correct.
  apply (LSBnat_unique A).
  exact B'.
  exact B.
Qed.
