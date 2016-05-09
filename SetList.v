Require Import Coq.Sorting.Sorted.
Require Import List.
Require Import Combi.

(** A simple "set" implementation with sorted lists. This is only to
make sets "unique". It is of poor algorithmic quality, and meant
mainly as a first step for later refinement. We use it in our
`DecompressWithPheap` file *)

Record chain (elts : Set)
  := mkChain {
   cmp : elts -> elts -> Prop;
   dec : forall a b, {cmp a b} + {~ cmp a b};
   total : forall a b, {cmp a b} + {cmp b a};
   refl : forall a, cmp a a;
   antisym : forall a b, cmp a b -> cmp b a -> a = b;
   trans : forall a b c, cmp a b -> cmp b c -> cmp a c
  }.

Arguments cmp [_] _ _ _.
Arguments dec [_] _ _ _.
Arguments total [_] _ _ _.
Arguments refl [_] _ _.
Arguments antisym [_] _ _ _ _ _.
Arguments trans [_] _ _ _ _ _ _.

Lemma chain_neq : forall {elts : Set} (c : chain elts) (a b : elts),
                    (~ cmp c a b) -> a <> b.
Proof.
  intros elts c a b cm Q.
  contradict cm.
  rewrite -> Q.
  apply (refl c).
Qed.

Lemma chain_dec : forall {elts : Set} (c : chain elts) (a b : elts),
                    {a = b} + {a <> b}.
Proof.
  intros.
  destruct (dec c a b) as [ab | nab] eqn:abe.
  + destruct (dec c b a) as [ba | nba] eqn:bae.
    - apply left.
      apply (antisym c); trivial.
    - apply right.
      intro Q.
      symmetry in Q.
      revert Q.
      apply (chain_neq c).
      trivial.
  + apply right.
    apply (chain_neq c).
    trivial.
Qed.  

Record listset (elts : Set) (c : chain elts)
  := mkListset {
  content : list elts;
  content_sorted : Sorted (cmp c) content;
  content_dup_free : dflist content
  }.

Arguments content [_] [_] _.
Arguments content_sorted [_] [_] _.
Arguments content_dup_free [_] [_] _.

Definition listset_in {elts : Set} {c : chain elts} (e : elts) (ls : listset elts c) :=
  In e (content ls).

Fixpoint list_push {elts : Set} {c : chain elts}
  (e : elts) (l : list elts) :=
  match l with
    | nil => e :: nil
    | x :: l_ => match (dec c e x) with
                  | left _ => match (dec c x e) with
                                 | left _ => x :: l_ (* x = e *)
                                 | right _ => e :: x :: l_
                              end
                  | right _ =>  x :: @list_push _ c e l_
                 end
  end.

Lemma list_push_df : forall {elts : Set} {c : chain elts} {e : elts} {l : list elts},
                       Sorted (cmp c) l -> dflist l -> dflist (@list_push elts c e l).
Proof.
  intros elts c e.
  induction l as [|lx l IHl].
  constructor.
  constructor.
  intro Q.
  inversion Q.
  intros srt dfx.
  simpl.
  destruct (dec c e lx) as [elx | nelx].
  destruct (dec c lx e) as [lxe | nlxe].
  trivial.
  constructor.
  trivial.
  destruct srt.
  auto.
  

Lemma list_push_spec_1 : forall {elts : Set} {c : chain elts} {e : elts} {l : list elts},
                           In e (@list_push elts c e l).
Proof.
  intros elts c e l.
  revert e.
  induction l as [|a l IHl].
  intro e.
  constructor.
  reflexivity.

  intro e.
  simpl.
  destruct (dec c e a).
  + destruct (dec c a e).
    constructor.
    apply (antisym c); trivial.
    constructor.
    reflexivity.
  + constructor 2.
    apply IHl.
Qed.

Lemma list_push_spec_2 : forall {elts : Set} {c : chain elts} (d e : elts) (l : list elts),
                           In d l -> In d (@list_push elts c e l).
Proof.
  intros elts c d e l.
  induction l as [|a l IHl].
  intro Q.
  inversion Q.
  intro indal.
  simpl.
  destruct (dec c e a) as [y|n].
  destruct (dec c a e) as [y2|n2].
  trivial.
  constructor 2.
  trivial.
  destruct indal as [da | nda].
  rewrite <- da.
  constructor.
  reflexivity.

  constructor 2.
  apply IHl.
  trivial.
Qed.

Lemma list_push_spec : forall {elts : Set} {c : chain elts} (d e : elts) (l : list elts),
                         In d (@list_push elts c e l) <-> (d = e \/ In d l).
Proof.
  intros elts c d e l.
  split.
  induction l as [|a l IHl].
  simpl.
  intros [? | ?]; auto.
  simpl.

  destruct (dec c e a) as [ea | nea] eqn:eae.
  destruct (dec c a e) as [ae | nae] eqn:aee.
  intros [de | in_]; auto.
  intros [de | [da | in_]]; auto.
  intros [da | inlp]; firstorder.

  intros [de | indl].
  rewrite <- de.
  apply list_push_spec_1.
  apply list_push_spec_2.
  trivial.
Qed.

Lemma list_push_sorted : forall {elts : Set} {c : chain elts} (e : elts) (l : list elts),
                           Sorted (cmp c) l -> Sorted (cmp c) (@list_push elts c e l).
Proof.
  intros elts c e l.
  revert e.
  induction l as [|a l IHl].
  intros e cm.
  simpl.
  constructor.
  trivial.
  constructor.

  destruct l as [|b l].
  + intros e cm.
    simpl.
    destruct (dec c e a) as [ea | nea] eqn:eae.
    - destruct (dec c a e) as [ae | nae] eqn:aee.
      * trivial.
      * repeat constructor.
        exact ea.
    - repeat constructor.
      destruct (total c a e) as [cae | cea].
      exact cae.
      contradict cea.
      trivial.
  + intros e cm.
    simpl.
    simpl in IHl.
    destruct (dec c e a) as [ea | nea].
    - destruct (dec c a e) as [ae | nae].
      * trivial.
      * constructor.
        exact cm.
        constructor.
        exact ea.
    - constructor.    
      apply IHl.
      inversion cm.
      trivial.
      destruct (dec c e b) as [eb | neb].
      destruct (dec c b e) as [be | nbe].
      replace b with e.
      constructor.
      destruct (total c a e).
      trivial.
      contradict nea.
      trivial.
      apply (antisym c e b); trivial.

      constructor.
      destruct (total c a e).
      trivial.
      contradict nea.
      trivial.
      constructor.
      inversion cm.
      match goal with
        | X : HdRel _ _ (b :: l) |- _ => inversion X; trivial
      end.
Qed.

Definition listset_push {elts : Set} {c : chain elts} (e : elts) (l : listset elts c) : listset elts c.
Proof.
  refine (mkListset elts c (list_push e (content l)) _).
  apply list_push_sorted.
  apply (content_sorted l).
Defined.

Lemma listset_ext_2 : forall {elts : Set} {c : chain elts} (l m : list elts),
                        Sorted (cmp c) l -> Sorted (cmp c) m ->
                        (forall x, In x l <-> In x m) -> l = m.
Proof.
  intros elts c.
  induction l as [|lx l IHl].
  destruct m as [|mx m].
  reflexivity.
  intros ? ? Q.
  assert (K : In mx nil).
  apply Q.
  constructor.
  reflexivity.
  inversion K.

  destruct m as [|mx m].
  intros ? ? Q.
  assert (K : In lx nil).
  apply Q.
  constructor.
  reflexivity.
  inversion K.

  destruct l as [| lxx l].
  destruct m as [| mxx m].
  (* one-element case: *)
  intros ? ? ext.
  assert (K : In mx (lx :: nil)).
  apply ext.
  constructor.
  reflexivity.
  destruct K as [K | K].
  rewrite -> K.
  reflexivity.
  inversion K.



Theorem listset_ext : forall {elts : Set} {c : chain elts} (l m : listset elts c),
                        (forall x, listset_in x l <-> listset_in x m) <-> l = m.
Proof.
  intros elts c l m.
  split.
  