Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.QArith.Qfield.
Require Import Lex.
Require Import Prefix.
Require Import DeflateNotations.
Require Import Program.

Local Open Scope nat.

Fixpoint repeat (n : nat) (b : bool) : LB :=
  match n with
      | 0 => nil
      | S n' => b :: (repeat n' b)
  end.


Lemma rep_length : forall n b, ll (repeat n b) = n.
Proof.
  intros n b.
  induction n.
  compute.
  auto.
  replace (repeat (S n) b) with (b :: (repeat n b)).
  replace (Datatypes.length (b :: repeat n b)) with (S (Datatypes.length (repeat n b))).
  replace (Datatypes.length (repeat n b)) with n.
  auto.
  auto.
  auto.
Qed.

Lemma repeat_add : forall n m b, (repeat n b) ++ (repeat m b) = (repeat (n + m) b).
Proof.
  induction n.
  intros m b.
  compute.
  auto.
  intros m b.
  replace (S n + m) with (S (n + m)).
  replace (repeat (S (n + m)) b) with (b :: repeat (n + m) b).
  replace (repeat (S n) b) with (b :: repeat n b).
  replace (repeat (n + m) b) with (repeat n b ++ repeat m b).
  auto.
  apply IHn.
  auto.
  auto.
  auto.
Qed.


Lemma repeat_S : forall l n b, prefix l (repeat n b) -> prefix l (repeat (S n) b).
Proof.
  induction n.
  intros b H.
  replace l with (nil : list bool).
  compute.
  exists (b :: nil).
  auto.
  assert (ll l <= 0).
  replace 0 with (ll (repeat 0 b)).
  apply prefix_le.
  apply H.
  auto.
  induction l.
  auto.
  contradict H0.
  replace (ll (a :: l)) with (S (ll l)).
  apply le_Sn_O.
  auto.
  intros b H.
  replace (repeat (S (S n)) b) with ((repeat (S n) b) ++ (repeat 1 b)).
  apply prefix_trans with (repeat (S n) b).
  trivial.
  exists (repeat 1 b).
  auto.
  replace (S (S n)) with ((S n) + 1).
  apply repeat_add.
  replace (S n + 1) with (1 + S n).
  auto.
  apply plus_comm.
Qed.

Lemma repeat_inc : forall l n m b, prefix l (repeat n b) -> m >= n -> prefix l (repeat m b).
Proof.
  intros l n m b H H0.
  assert (m = n + (m - n)).
  apply le_plus_minus.
  trivial.
  replace m with (n + (m - n)).
  replace (repeat (n + (m - n)) b) with ((repeat n b) ++ (repeat (m - n) b)).
  inversion H.
  replace (repeat n b) with (l ++ x).
  replace ((l ++ x) ++ repeat (m - n) b) with (l ++ x ++ repeat (m - n) b).
  exists (x ++ repeat (m - n) b).
  auto.
  apply Coq.Lists.List.app_assoc.
  apply repeat_add.
Qed.

Lemma repeat_cdr : forall a b l n,  prefix (a :: l) (repeat n b) -> prefix l (repeat n b).
Proof.
  induction n.
  intros H.
  contradict H.
  intros H.
  inversion H.
  inversion H0.
  intros H.
  apply repeat_S.
  inversion H.
  exists x.
  inversion H0.
  auto.
Qed.

Lemma rep_prefix : forall b l, (exists n, prefix l (repeat n b)) ->
                               l = repeat (ll l) b.
Proof.
induction l.
intros H.
compute.
auto.
intros H.
inversion H.
inversion H0.
inversion H1.
replace (ll (a :: l)) with (S (ll l)).
replace (repeat (S (ll l)) b) with (b :: repeat (ll l) b).
replace a with b.
f_equal.
apply IHl.
exists x.
apply (repeat_cdr a).
exists x0.
trivial.
assert (exists y, x = S y).
assert (x > 0).
apply not_le.
intros Q.
contradict H3.
replace x with 0.
intros Q2.
inversion Q2.
apply le_n_0_eq.
trivial.
induction x.
contradict H2.
intros Q.
inversion Q.
exists x.
auto.
inversion H2.
assert (a :: l ++ x0 = b :: (repeat x1 b)).
replace (b :: (repeat x1 b)) with (repeat x b).
trivial.
replace x with (S x1).
auto.
inversion H5.
auto.
auto.
auto.
Qed.

Lemma rep_prefix_1 : forall n l, l <> nil -> prefix l (false :: (repeat n true)) ->
                                 l = false :: (repeat (pred (ll l)) true).
Proof.
intros n l H H0.
induction l. 
contradict H.
auto.
inversion H0.
inversion H1.
f_equal.
apply rep_prefix.
exists n.
exists x.
trivial.
Qed.

Lemma prefix_repeat : forall a b n, prefix a (repeat n b) -> a = repeat (ll a) b.
Proof.
  intros a b n H.
  induction a.
  auto.
  replace (ll (a :: a0)) with (S (ll a0)).
  replace (repeat (S (ll a0)) b) with (b :: repeat (ll a0) b).
  induction a.
  induction b.
  f_equal.
  apply IHa.
  apply (repeat_cdr true).
  trivial.
  contradict H.
  intros Q.
  induction n.
  inversion Q.
  inversion H.
  contradict Q.
  replace (repeat (S n) false) with (false :: repeat n false).
  intros Q.
  inversion Q.
  inversion H.
  auto.
  induction b.
  contradict H.
  intros Q.
  induction n.
  inversion Q.
  inversion H.
  contradict Q.
  replace (repeat (S n) true) with (true :: repeat n true).
  intros Q.
  inversion Q.
  inversion H.
  auto.
  f_equal.
  apply IHa.
  apply (repeat_cdr false).
  trivial.
  auto.
  auto.
Qed.

Lemma lex_0_x : forall x, lex (repeat (ll x) false) x.
Proof.
  induction x.
  apply nil_lex.
  induction a.
  replace (repeat (ll (true :: x)) false) with
  (false :: repeat (ll x) false).
  apply car_lex.
  replace (repeat (ll (true :: x)) false) with
  (false :: repeat (ll x) false).
  auto.
  compute.
  auto.
  replace (repeat (ll (false :: x)) false) with
  (false :: repeat (ll x) false).
  apply cdr_lex.
  apply IHx.
  auto.
Qed.

Lemma lex_1_is_1 : forall l, lex (repeat (ll l) true) l -> l = (repeat (ll l) true).
Proof.
  induction l.
  auto.
  intros lx.
  induction a.
  assert (lxx : lex (repeat (ll l) true) l).
  apply (lex_cdr _ _ true).
  apply lx.
  rewrite -> IHl.
  replace (ll (true :: repeat (ll l) true)) with (S (ll (repeat (ll l) true))).
  rewrite -> rep_length.
  auto.
  auto.
  auto.
  inversion lx.
Qed.

Lemma lex_1_prefix : forall n b,
                       lex (repeat n true) b -> prefix (repeat n true) b.
Proof.
  induction n.
  intros b bb.
  exists b.
  auto.
  destruct b.
  intros contr.
  inversion contr.
  intros lex1.
  inversion lex1.
  assert (H4:prefix (repeat n true) b0).
  apply IHn.
  rewrite <- H2 in lex1.
  apply (lex_cdr _ _ true).
  apply lex1.
  elim H4.
  intros x k.
  exists x.
  rewrite <- k.
  auto.
Qed.

Lemma prefix_ext : forall a b c,
                     prefix a (b ++ c) -> ~ prefix a b -> prefix b a.
Proof.
  intros a b c pf1 pf2.
  refine ((fix f x y z
               (qf1 : prefix x (y ++ z))
               (qf2 : ~ prefix x y) : prefix y x :=
             match x as k return (x = k -> _) with
               | [] => fun eq => _
               | x' :: x'' =>
                 fun eq => 
                   match y as kk return (y = kk -> _) with
                     | [] => fun eq => _
                     | y' :: y'' => _
                   end eq_refl
             end eq_refl) a b c pf1 pf2).
  destruct y.
  exists Bnil.
  auto.
  contradict qf2.
  rewrite -> eq.
  exists (b0 :: y).
  auto.
  exists (x' :: x'').
  rewrite -> eq.
  auto.
  intros eq2.
  rewrite -> eq in qf1.
  rewrite -> eq2 in qf1.
  rewrite -> eq2.
  inversion qf1.
  inversion H.
  assert (pref : prefix y'' x'').
  apply (f _ _ z).
  exists x0.
  auto.
  contradict qf2.
  elim qf2.
  intros r rr.
  exists r.
  rewrite -> eq.
  rewrite -> eq2.
  rewrite <- rr.
  rewrite -> H1.
  auto.
  elim pref.
  intros x1 x1x.
  exists x1.
  rewrite <- x1x.
  auto.
Qed.

Lemma lex_0_is_prefix : forall d n, lex d (repeat n false) -> prefix d (repeat n false).
Proof.
  refine (fix f d n lx :=
            match d as e return (d = e -> _) with
                | nil => _
                | (x :: r) =>
                  match n as m return (n = m -> _) with
                      | 0%nat => fun eq => _
                      | (S n) => fun eq => _
                  end eq_refl
            end eq_refl).
  exists (repeat n false).
  auto.
  rewrite H.
  auto.
  intros deq.
  contradict lx.
  rewrite deq.
  rewrite eq.
  apply nnil_lex.
  intros deq.  
  rewrite deq.
  assert (lx' : lex (x :: r) (repeat (S n) false)).
  rewrite <- deq.
  rewrite <- eq.
  auto.
  inversion lx'.
  assert (pref : prefix r (repeat n false)).
  apply f.
  auto.
  elim pref.
  intros x0 quak.
  exists x0.
  replace ((false :: r) ++ x0) with (false :: (r ++ x0)).
  rewrite -> quak.
  reflexivity.
  auto.
Qed.  

Lemma prefix_antisym : forall (a b : LB), prefix a b -> prefix b a -> a = b.
Proof.
  refine (fix f a b :=
            match (a, b) as R return (R = (a, b) -> _) with
                | (nil, nil) => fun eq => _
                | (xa :: a', nil) => fun eq => _
                | (nil, xb :: b') => fun eq => _
                | (xa :: a', xb :: b') => fun eq => _
            end eq_refl).
inversion eq.
reflexivity.
inversion eq.
intros _ Q.
contradict Q.
apply prefix_nnil.
inversion eq.
intros Q.
contradict Q.
apply prefix_nnil.
inversion eq.
intros pab pba.
elim (bool_dec xa xb).
intros xa_eq_xb.
rewrite -> xa_eq_xb.
f_equal.
apply f.
apply (prefix_cdr xa xb).
apply pab.
apply (prefix_cdr xb xa).
apply pba.
intros xa_neq_xb.
inversion pab.
inversion H.
contradict xa_neq_xb.
auto.
Qed.

Lemma prefix_app : forall (a b c : LB),
                     prefix a (b ++ c) ->
                     (ll a <= ll b)%nat -> prefix a b.
Proof.
  induction a.
  intros b c pref ll_.
  exists b.
  auto.
  intros b c pref ll_.
  destruct b.
  inversion ll_.
  inversion pref.
  inversion H.
  apply prefix_cons.
  apply (IHa _ c).
  exists x.
  apply H2.
  apply le_S_n.
  replace (S (ll a0)) with (ll (a :: a0)).
  replace (S (ll b0)) with (ll (b :: b0)).
  apply ll_.
  auto.
  auto.
Qed.

Lemma max_common_prefix : forall (a b : LB), {c | (prefix c a) /\ (prefix c b) /\
                                                  forall d, prefix d a -> prefix d b -> prefix d c}.
Proof.
  refine (fix f a b := 
            match a with
                | nil => _
                | (xa :: a') =>
                  match b with
                      | nil => _
                      | (xb :: b') => _
                  end
            end).
exists Bnil.
split.
exists Bnil.
auto.
split.
exists b.
auto.
intros d pb db.
apply pb.
exists Bnil.
split.
exists (xa :: a').
auto.
split.
exists Bnil.
auto.
intros d da db.
apply db.
elim (bool_dec xa xb).
intros xa_eq_xb.
elim (f a' b').
intros x x_ex.
elim x_ex.
intros xa' xex2.
elim xex2.
intros xb' xex3.
exists (xb :: x).
split.
rewrite -> xa_eq_xb.
apply prefix_cons.
apply xa'.
split.
apply prefix_cons.
apply xb'.
intros d.
destruct d.
intros _ _.
exists (xb :: x).
auto.
intros pda pdb.
inversion pdb.
inversion H.
apply prefix_cons.
apply xex3.
apply (prefix_cdr b0 xa).
apply pda.
apply (prefix_cdr b0 xb).
apply pdb.
exists Bnil.
split.
exists (xa :: a').
auto.
split.
exists (xb :: b').
auto.
intros d.
intros pda pdb.
induction d.
exists Bnil.
auto.
inversion pda.
inversion H.
inversion pdb.
inversion H0.
rewrite <- H4 in b0.
rewrite <- H1 in b0.
contradict b0.
reflexivity.
Qed.
