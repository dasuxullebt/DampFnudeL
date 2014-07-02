Require Import DeflateNotations.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.QArith.Qfield.

Local Open Scope nat.

Definition prefix (a b : list bool) : Prop :=
  exists c, a ++ c = b.

Lemma prefix_le : forall a b, prefix a b -> (ll a <= ll b).
Proof.
  induction a as [|a a0 IHa].
  intros b H.
  firstorder.
  induction b as [|b b0 IHb].
  intros H.
  inversion H as [x H0].
  inversion H0.
  intros H.
  replace (ll (_ :: a0)) with (S (ll a0)).
  replace (ll (_ :: b0)) with (S (ll b0)).
  apply le_n_S.
  apply IHa.
  inversion H as [x H0].
  inversion H0.
  exists x.
  reflexivity.
  auto.
  auto.
Defined.

Lemma prefix_trans : forall a b c, prefix a b -> prefix b c -> prefix a c.
Proof.
  intros a b c H H0.
  inversion H.
  inversion H0.
  exists (x ++ x0).
  replace (a ++ x ++ x0) with ((a ++ x) ++ x0).
  replace (a ++ x) with b.
  trivial.
  apply eq_sym.
  apply Coq.Lists.List.app_assoc.
Defined.

Lemma prefix_cdr : forall a b l m, prefix (a :: l) (b :: m) -> prefix l m.
Proof.
  intros a b l m H.
  inversion H as [x H0].
  inversion H0.
  exists x.
  trivial.
Defined.

Lemma prefix_cons : forall a b c, prefix a b -> prefix (c :: a) (c :: b).
Proof.
  intros a b c.
  destruct a as [|a1 a2].
  intros _. 
  exists b.                 
  reflexivity.
  destruct b as [|b1 b2].
  intros contr.
  inversion contr as [x H].
  inversion H.

  intros inv.
  inversion inv as [x H].
  inversion H.
  exists x.
  reflexivity.
Defined.

Lemma prefix_nnil : forall (n : LB) i, ~ prefix (i :: n) nil.
Proof.
  intros ? ? Q.
  inversion Q as [? H].
  inversion H.
Defined.

(* TODO: Doesn't really fit in here *)
Lemma nnil_ll : forall a, (ll a <> 0)%nat -> a <> Bnil.
Proof.
  intros a neq.
  induction a.
  contradict neq.
  reflexivity.
  intros Q.
  inversion Q.
Defined.

Lemma nil_ll : forall a, (ll a = 0)%nat -> a = Bnil.
Proof.
  intros a eq.
  induction a.
  reflexivity.
  inversion eq.
Defined.

Lemma prefix_ll_eq : forall m n, prefix m n /\ ll m = ll n -> m = n.
Proof.
  intros m n und.
  destruct und as [[x eq] lleq].
  assert (llmx : ll m + ll x = ll n).
  rewrite <- eq.
  symmetry.
  apply app_length.
  assert (llxn : ll x = 0).
  firstorder.
  assert (xnil : x = nil).
  apply nil_ll.
  auto.
  replace m with (m ++ nil).
  rewrite <- xnil.
  auto.
  apply app_nil_r.
Defined.

Lemma prefix_dec : forall a b, (prefix a b + ~ prefix a b)%type.
Proof.
  refine (fix f a b :=
            match (a, b) as R return (_ = (a, b) -> _) with
                | (nil, _) => fun eq =>  _
                | ((xa :: a'), nil) => fun eq => _
                | ((xa :: a'), (xb :: b')) => fun eq => _
            end eq_refl).
  inversion eq.
  apply inl.
  exists b.
  auto.
  inversion eq.
  apply inr.
  apply prefix_nnil.
  elim (bool_dec xa xb).
  intros xa_eq_xb.
  inversion eq.
  rewrite -> xa_eq_xb.
  destruct (f a' b') as [pab | npab].
  apply inl.
  apply prefix_cons.
  apply pab.
  apply inr.
  contradict npab.
  apply (prefix_cdr xb xb).
  apply npab.
  intros xa_neq_xb.
  apply inr.
  inversion eq.
  intros pref.
  inversion pref as [x H].
  inversion H.
  contradict xa_neq_xb.
  auto.
Defined.

Lemma prefix_common : forall a b c, prefix a c -> prefix b c ->
                                    (prefix a b + prefix b a).
Proof.
  refine (fix pc a b c ac bc :=
            match (a, b, c) as A return ((a, b, c) = A -> _) with
              | (nil, b, _) => fun eq => _
              | (xa :: xA, nil, _) => fun eq => _
              | (xa :: nil, xb :: xB, _) => fun eq => _
              | (xa :: ya :: xA, xb :: nil, _) => fun eq => _
              | (xa :: ya :: xA, xb :: yb :: xB, nil) => fun eq => _
              | (xa :: ya :: xA, xb :: yb :: xB, xc :: nil) => fun eq => _
              | (xa :: ya :: xA, xb :: yb :: xB, xc :: yc :: xC) => fun eq => _
            end eq_refl).
  inversion eq.
  apply inl.
  exists b.
  auto.
  inversion eq.
  apply inr.
  exists (xa :: Bnil).
  apply app_nil_l.

  inversion eq.
  apply inl.
  exists xB.
  inversion ac.
  inversion bc.

  rewrite <- H3 in H.
  rewrite -> H0 in H.
  rewrite -> H1 in H.
  inversion H.
  reflexivity.

  apply inr.
  inversion eq.
  exists (xa :: b0 :: l2).
  apply app_nil_l.

  inversion eq.
  apply inr.
  inversion ac.
  inversion bc.
  rewrite <- H3 in H.
  rewrite -> H0 in H.
  rewrite -> H1 in H.
  inversion H.
  exists (ya :: xA).
  reflexivity.

  inversion eq.
  inversion ac.
  rewrite -> H0 in H.
  rewrite -> H2 in H.
  inversion H.
  inversion eq.
  inversion ac.
  rewrite -> H2 in H.
  rewrite -> H0 in H.
  inversion H.

  inversion eq.
  assert (rec : prefix xA xB + prefix xB xA).
  apply pc with xC.
  inversion ac.
  rewrite -> H0 in H.
  rewrite -> H2 in H.
  inversion H.
  exists x.
  reflexivity.
  inversion bc.
  rewrite -> H1 in H.
  rewrite -> H2 in H.
  inversion H.
  exists x.
  reflexivity.
  inversion ac.
  inversion bc.
  rewrite <- H3 in H.
  rewrite -> H0 in H.
  rewrite -> H1 in H.
  inversion H.
  elim rec.
  intros preab.
  apply inl.
  inversion preab.
  exists x1.
  rewrite <- H4.
  reflexivity.
  intros preba.
  apply inr.
  inversion preba.
  exists x1.
  rewrite <- H4.
  reflexivity.
Defined.