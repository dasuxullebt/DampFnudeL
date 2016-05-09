Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.QArith.Qfield.
Require Import Lex.
Require Import Prefix.
Require Import Shorthand.

Local Open Scope nat.

(*Fixpoint repeat (n : nat) (b : bool) : LB :=
  match n with
      | 0 => nil
      | S n' => b :: (repeat n' b)
  end.

Todo: merge with repeat.v *)
Fixpoint repeat {A} (n : nat) (a : A) : list A :=
  match n with
    | 0 => nil
    | (S n) => a :: repeat n a
  end.

Lemma rep_length : forall {A} n (b : A), ll (repeat n b) = n.
Proof.
  intros A n b.
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

Lemma repeat_add : forall {A} n m (b : A), (repeat n b) ++ (repeat m b) = (repeat (n + m) b).
Proof.
  intro A.
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

Lemma repeat_S : forall {A} l n (b : A), prefix l (repeat n b) -> prefix l (repeat (S n) b).
Proof.
  intro A.
  induction n.
  intros b H.
  replace l with (nil : list A).
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

Lemma repeat_inc : forall {A} l n m (b : A),
                     prefix l (repeat n b) -> m >= n -> prefix l (repeat m b).
Proof.
  intros A l n m b H H0.
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

Lemma repeat_cdr : forall {A} (a : A) b l n,  prefix (a :: l) (repeat n b) -> prefix l (repeat n b).
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

Lemma rep_prefix : forall {A} (b : A) l, (exists n, prefix l (repeat n b)) ->
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

Lemma rep_prefix_1 : forall {A} (a b : A) n l, l <> nil -> prefix l (a :: (repeat n b)) ->
                                               l = a :: (repeat (pred (ll l)) b).
Proof.
intros A a b n l H H0.
induction l.
contradict H.
auto.
inversion H0 as [H1 H2].
inversion H2.
f_equal.
replace (ll (a :: l)) with (S (ll l)).
unfold pred.
apply rep_prefix.
exists n.
exists H1.
trivial.
reflexivity.
Qed.

Lemma prefix_repeat : forall {A} a (b : A) n, prefix a (repeat n b) -> a = repeat (ll a) b.
Proof.
  intro A.
  induction a.
  intro b.
  induction n.
  auto.
  auto.
  intro b.
  destruct n as [|n].
  intro Q.  
  destruct Q as [pr1 pr2].
  compute in pr2.
  inversion pr2.
  intros Q.
  destruct Q as [pr1 pr2].
  inversion pr2 as [ab].
  compute in pr2.
  compute.
  f_equal.
  apply IHa with n.
  exists pr1.
  trivial.
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

Lemma prefix_ext : forall {A} (a b c : list A),
                     prefix a (b ++ c) -> ~ prefix a b -> prefix b a.
Proof.
  intros A a b c pf1 pf2.
  refine ((fix f x y z
               (qf1 : prefix x (y ++ z))
               (qf2 : ~ prefix x y) : prefix y x :=
             match x as k return (x = k -> _) with
               | nil => fun eq => _
               | x' :: x'' =>
                 fun eq => 
                   match y as kk return (y = kk -> _) with
                     | nil => fun eq => _
                     | y' :: y'' => _
                   end eq_refl
             end eq_refl) a b c pf1 pf2).
  destruct y.
  exists (nil (A:=A)).
  auto.
  contradict qf2.
  rewrite -> eq.
  exists (a0 :: y).
  auto.
  exists (x' :: x'').
  auto.
  intros eq2.
  rewrite -> eq in qf1.
  rewrite -> eq2 in qf1.
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
  rewrite -> H.
  auto.
  intros deq.
  contradict lx.
  rewrite deq.
  rewrite eq.
  apply nnil_lex.
  intros deq.
  rewrite deq.
  assert (lx' : lex (x :: r) (repeat (S n0) false)).
  rewrite <- deq.
  rewrite <- eq.
  auto.
  inversion lx'.
  assert (pref : prefix r (repeat n0 false)).
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

(* TODO: geht allgemeiner *)
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


(* TODO: geht allgemeiner *)
Lemma max_common_prefix : forall (a b : LB), {c | (prefix c a) /\ (prefix c b) /\
                                                  forall d, prefix d a -> prefix d b -> prefix d c}.
Proof.
  intros aq bq.
  refine ((fix f a b := 
            match a as A return (a = A -> _) with
                | nil => fun eq => _
                | (xa :: a') =>
                  fun eq =>
                  match b as B return (b = B -> _) with
                      | nil => fun eq2 => _
                      | (xb :: b') => fun eq2 => _
                  end eq_refl
            end eq_refl) aq bq).
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

Lemma repeat_forall : forall {A} n (Q : A -> Prop) a,
                        Q a -> Forall Q (repeat n a).
Proof.
  intros A.
  induction n.
  constructor.
  intros Q a Qa.
  constructor.
  exact Qa.
  apply IHn.
  exact Qa.
Qed.

Lemma repeat_map : forall {A B : Set} (c : A) (f : A -> B) n,
                     map f (repeat n c) = repeat n (f c).
Proof.
  intros A B c f.
  induction n as [|n IHn].
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.
