Require Import Coq.Logic.Decidable.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.QArith.
Require Import Coq.PArith.BinPos.
Require Import Coq.Arith.Arith.
Require Import Coq.Vectors.Vector.
Require Import NPeano.
Require Import Coq.Init.Logic.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Mergesort.
Require Import Coq.Structures.Orders.
Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.EqdepFacts.

Notation vec := Vector.t.
Notation Vnil := Vector.nil.
Notation Vcons := Vector.cons.
Notation Vmap := VectorDef.map.

Notation fin_rect2 := Fin.rect2.
Notation FS_inj := Fin.FS_inj.
Notation fin := Fin.t.
Notation FinLR := Fin.L_R.
Notation FinFS := Fin.FS.
Notation FinF1 := Fin.F1.


Notation LB := (list bool).
Notation VecLB := (Vector.t LB).
Notation Vnth := VectorDef.nth.
Notation ll := List.length.

Lemma dec_in_dec : forall {n} {A} (e : vec A n) (Q : A -> Prop) ,
                     (forall a, (Q a + (Q a -> False))) -> {n | Q (Vnth e n)} + ({n | Q (Vnth e n)} -> False).
Proof.
  intros n A e Q dc.
  dependent induction e.
  apply inr.
  intros nex.
  elim nex.
  intros x.
  inversion x.

  elim (dc h).
  intros Qh.
  apply inl.
  exists (FinF1(n:=n)).
  compute. auto.
  intros nQh.
  assert (prev : {n : fin n | Q (Vnth e n)} + ({n : fin n | Q (Vnth e n)} -> False)).
  apply IHe.
  apply dc.
  elim prev.
  intros n0ex.
  elim n0ex.
  intros x qex.
  apply inl.
  exists (FinFS x).
  replace (Vnth (Vcons A h n e) (FinFS x)) with (Vnth e x).
  apply qex.
  reflexivity.
  intros nexn0.
  apply inr.
  intros nexn0n.
  elim nexn0n.
  intros x qx.
  dependent induction x.
  contradict nQh.
  apply qx.
  contradict nexn0.
  exists x.
  apply qx.
Qed.

Inductive lex : list bool -> list bool -> Prop :=
  | nil_lex : forall a, lex nil a
  | car_lex : forall a b, lex (false :: a) (true :: b)
  | cdr_lex : forall a b c, lex a b -> lex (c :: a) (c :: b).

Lemma vec_identity : forall {m}, {vc : vec _ m | forall q, Vnth vc q = q}.
Admitted.

Lemma dec_lex: forall a b, (lex a b) + (~ lex a b).
Admitted.


Lemma forall_notexists : forall {A} (Q : A -> Prop),
                           (forall a, Q a + ~ Q a) ->
                           ({a | ~ Q a} -> False) -> forall a, Q a.
Proof.
  intros A Q H H0 a.
  elim (H a).
  trivial.
  intros nQa.
  assert (cdct : {a | ~ Q a}).
  exists a.
  apply nQa.
  contradict H0.
  auto.
Qed.

Lemma dec_in_dec_all : forall {n} {A} (e : vec A n) (Q : A -> Prop) ,
                         (forall a, (Q a + (Q a -> False))) -> (forall n, Q (Vnth e n)) + ((forall n, Q (Vnth e n)) -> False).
Proof.
  intros.
  assert (dc: {n | ~ Q (Vnth e n)} + ({n | ~ Q (Vnth e n)} -> False)).
  apply (dec_in_dec _ (fun n => ~ Q n)).
  intros a.
  elim (H a).
  intros Qa.
  apply inr. auto.
  intros nQa.
  auto.
  elim dc.
  intros ex.
  apply inr.
  intros fa.
  elim ex.
  intros x nQ.
  apply nQ.
  apply fa.
  intros nex.
  apply inl.
  apply forall_notexists.
  intros a.
  apply H.
  apply nex.
Qed.

Lemma min_dec_ex : forall {n} (e : vec LB n) (Q : LB -> Prop),
                     (forall a, (Q a + (Q a -> False))) -> {n | Q (Vnth e n)} ->
                     {m | Q (Vnth e m) /\ forall n, Q (Vnth e n) -> lex (Vnth e m) (Vnth e n)}.
Proof.
  intros n e Q Qdec n0_ex.
  assert (dc : {m | Q (Vnth e m) /\ forall n, Q (Vnth e n) -> lex (Vnth e m) (Vnth e n)} +
               {m | Q (Vnth e m) /\ forall n, Q (Vnth e n) -> lex (Vnth e m) (Vnth e n)} -> False).
  assert (dec : forall a : LB,
                  (Q a /\ (forall n0 : fin n, Q (Vnth e n0) -> lex a (Vnth e n0))) +
                  (Q a /\ (forall n0 : fin n, Q (Vnth e n0) -> lex a (Vnth e n0)) -> False)).
  assert (vi : {vc : vec (fin n) n | forall q, Vnth vc q = q}).
  apply vec_identity.
  elim vi.
  intros vc vcqq.
  intros a.
  elim (Qdec a).
  intros Qa.
  assert (dec2 : (forall n0 : fin n, Q (Vnth e n0) -> lex a (Vnth e n0)) +
                 (forall n0 : fin n, Q (Vnth e n0) -> lex a (Vnth e n0)) -> False).
  assert (dec3 : (forall n0 : fin n, Q (Vnth e (Vnth vc n0)) -> lex a (Vnth e (Vnth vc n0))) +
                 (forall n0 : fin n, Q (Vnth e (Vnth vc n0)) -> lex a (Vnth e (Vnth vc n0))) -> False).
  assert (dec4 : (forall a0 : fin n,
                    ((Q (Vnth e (Vnth vc a0)) -> lex a (Vnth e (Vnth vc a0))) +
                     ((Q (Vnth e (Vnth vc a0)) -> lex a (Vnth e (Vnth vc a0))) -> False)))).
  intros a0.
  elim (Qdec (Vnth e (Vnth vc a0))).
  intros Qa0.
  elim (dec_lex a (Vnth e (Vnth vc a0))).
  intros lx.
  apply inl.
  trivial.
  intros nlx.
  apply inr.
  intros R.
  assert (contr : lex a (Vnth e (Vnth vc a0))).
  apply R. apply Qa0.
  contradict nlx.
  trivial.
  intros nQa0.
  apply inl.
  intros Qa0.
  contradict nQa0.
  trivial.
  apply (dec_in_dec_all vc _ dec4).