(* TODO: Source: https://gist.github.com/wilcoxjay/88f64f6c2d8574263ef6 jwz *)

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import Coq.Arith.Compare_dec.

Module M := FMapAVL.Make(Nat_as_OT).

Function ForallHashTable_ {A} (Q : A -> Prop) (h : M.t A) :=
  forall k v, M.MapsTo k v h -> Q v.


Lemma ForallHashTableEmpty_ : forall {A} (Q : A -> Prop),
                                ForallHashTable_ Q (M.empty _).
Proof.
  intros ? ? ? ? mapsto.
  inversion mapsto.
Qed.

Lemma add_MapsTo : 
  forall A k (v : A) k' v' h, 
    M.Raw.MapsTo k v (M.Raw.add k' v' h) -> 
    (k = k' /\ v = v') \/ M.Raw.MapsTo k v h.
Proof.
  induction h; simpl; intros.
  - inversion H; subst; auto.
  - destruct (Nat_as_OT.compare k' k0) eqn:?;
    try match goal with 
    | [ H : M.Raw.MapsTo _ _ (M.Raw.bal _ _ _ _) |- _ ] => 
      apply M.Raw.Proofs.bal_mapsto in H; 
        unfold M.Raw.create in H
    end; 
      inversion H; subst; clear H; intuition.
Qed.

Lemma add_MapsTo_ : 
  forall A k (v : A) k' v' h, 
    M.MapsTo k v (M.add k' v' h) -> 
    (k = k' /\ v = v') \/ M.MapsTo k v h.
Proof.
  intros A k v k' v' h.
  unfold M.MapsTo.
  intro mt.
  apply add_MapsTo.
  auto.
Qed.

Lemma ForallHashTableAdd_ : forall {A} (Q : A -> Prop) (h : M.t A)
                                   k a,
                              Q a -> ForallHashTable_ Q h ->
                              ForallHashTable_ Q (M.add k a h).
Proof.
  intros A Q h k a Qa Qh.
  intros k2 a2.
  intro Hadd.
  apply add_MapsTo_ in Hadd.
  intuition.
  - subst. auto.
  - eapply Qh. eauto.
Qed.
