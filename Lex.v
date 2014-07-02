Require Import DeflateNotations.
Require Import Coq.Lists.List.

Inductive lex : list bool -> list bool -> Prop :=
  | nil_lex : forall a, lex nil a
  | car_lex : forall a b, lex (false :: a) (true :: b)
  | cdr_lex : forall a b c, lex a b -> lex (c :: a) (c :: b).

Lemma nnil_lex :  forall b l, ~ lex (b :: l) nil.
Proof.
  intros b l.
  induction l.
  induction b.
  intros H.
  inversion H.
  intros H.
  inversion H.
  intros H.
  inversion H.
Defined.

Lemma dec_lex: forall a b, (lex a b) + (~ lex a b).
Proof.
  induction a.
  intros b.
  apply inl.
  apply nil_lex.
  induction b.
  apply inr.
  apply nnil_lex.
  induction (IHa b).
  induction a.
  induction a1.
  apply inl.
  apply cdr_lex.
  apply a2.
  apply inr.
  intros q.
  inversion q.
  induction a1.
  apply inl.
  apply car_lex.
  apply inl.
  apply cdr_lex.
  apply a2.
  induction a.
  induction a1.
  apply inr.
  contradict b0.
  inversion  b0.
  trivial.
  apply inr.
  intros.
  intros U.
  inversion U.
  induction a1.
  apply inl.
  apply car_lex.
  apply inr.
  intros q.
  inversion q.
  auto.
Defined.

Lemma lex_cdr : forall a b i, lex (i :: a) (i :: b) -> lex a b.
Proof.
  intros a b i H.  
  inversion H.
  trivial.
Defined.

Lemma lex_refl : forall a, lex a a.
Proof.
  induction a.
  apply nil_lex.
  apply cdr_lex.
  auto.
Defined.

Lemma lex_nil_is_nil : forall c, lex c nil -> c = nil.
Proof.
  induction c.
  auto.
  intros H.
  contradict H.
  apply nnil_lex.
Defined.

Definition lex_trans : forall a b c (lab : lex a b) (lbc : lex b c), lex a c.
refine (fix f (a b c : list bool) : lex a b -> lex b c -> lex a c :=
          match b with
              | nil => _
              | false :: b' => match a with
                                   | nil => _
                                   | false :: a' => match c with
                                                        | nil => _
                                                        | false :: c' => _
                                                        | true :: c' => _
                                                    end
                                   | true :: a' => _
                               end
              | true :: b' => match a with
                                   | nil => _
                                   | false :: a' => match c with
                                                        | nil => _
                                                        | false :: c' => _
                                                        | true :: c' => _
                                                    end
                                   | true :: a' => match c with
                                                       | nil => _
                                                       | false :: c' => _
                                                       | true :: c' => _
                                                   end
                               end
          end
 ).

intros.
assert(a = nil).
apply lex_nil_is_nil.
trivial.
rewrite H1.
trivial.

intros.
apply nil_lex.
intros.
contradict H0.
apply nnil_lex.

intros.
inversion H.
inversion H0.
apply cdr_lex.
apply (f a' b' c').
auto.
auto.

intros.
inversion H0.

intros.
inversion H0.

intros.
apply car_lex.

intros.
inversion H0.

intros.
apply nil_lex.
intros.
inversion H.

intros.
inversion H0.

intros.
apply car_lex.

intros.
inversion H.
inversion H0.
apply cdr_lex.
apply (f _ b').
auto.
auto.
Defined.

Definition lex_antisym : forall a b, lex a b /\ lex b a -> a = b.
refine (fix f a b : lex a b /\ lex b a -> a = b :=
          match a with
              | nil => _
              | true :: a' => match b with
                                | nil => _
                                | false :: b' => _
                                | true :: b' => _
                              end
              | false :: a' => match b with
                                 | nil => _
                                 | false :: b' => _
                                 | true :: b' => _
                               end
          end).
intros.
elim H.
intros.
apply eq_sym.
apply lex_nil_is_nil.
trivial.
intros.
induction H.
inversion H.
intros.
induction H.
assert(a' = b').
apply f.
split.
apply (lex_cdr _ _ true).
trivial.
apply (lex_cdr _ _ true).
trivial.
rewrite H1.
auto.

intros.
induction H.
inversion H.
intros.
induction H.
inversion H.
intros.
induction H.
inversion H0.

intros.
induction H.
assert(a'=b').
apply f.
split.
apply (lex_cdr _ _ false).
trivial.
apply (lex_cdr _ _ false).
trivial.
rewrite H1.
auto.
Defined.

Definition lex_total : forall a b, lex a b + lex b a.
refine (fix f a b : lex a b + lex b a :=
          match a with
              | nil => _
              | x :: a' => match b with
                               | nil => _
                               | y :: b' => _
                           end
          end).

apply inl.
apply nil_lex.

apply inr.
apply nil_lex.

induction x.
induction y.
assert (lex a' b' + lex b' a').
apply f.
induction H.
apply inl.
apply cdr_lex.
trivial.
apply inr.
apply cdr_lex.
trivial.
apply inr.
apply car_lex.
induction y.
apply inl.
apply car_lex.
assert (lex a' b' + lex b' a').
apply f.
induction H.
apply inl.
apply cdr_lex.
trivial.
apply inr.
apply cdr_lex.
trivial.
Defined.

Lemma lex_total_lemma : forall a b, ~ lex a b -> lex b a.
Proof.
  intros.
  assert (lex a b + lex b a).
  apply lex_total.
  induction H0.
  contradict a0.
  trivial.
  trivial.
Defined.

Lemma lex_apprm : forall a b c, lex (a ++ b) (a ++ c) -> lex b c.
Proof.
  induction a.
  intros b c.
  unfold app.
  auto.
  intros b c lx.
  replace ((a :: a0) ++ b) with (a :: a0 ++ b) in lx.
  replace ((a :: a0) ++ c) with (a :: a0 ++ c) in lx.
  apply IHa.
  apply (lex_cdr _ _ a).
  apply lx.
  auto.
  auto.
Defined.
