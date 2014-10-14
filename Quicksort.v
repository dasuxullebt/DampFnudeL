Require Import Coq.Lists.List.
Require Import Coq.Sorting.Sorted.
Require Import ZArith.

Lemma split_accto_pivot : forall {A : Set}
                                 (ord : A -> A -> Prop)
                                 (total : forall a b, {ord a b} + {ord b a})
                                 pivot list,
                            {pre : Datatypes.list A & { post |
                             (forall x, In x pre -> ord x pivot) /\
                             (forall x, In x post -> ord pivot x) /\
                             (forall x, In x list <->
                                        In x pre \/ In x post) /\
                             (length pre + length post = length list)}}.
Proof.
  intros ? ? ? pivot list; induction list as [|a ? IHlist];
  [exists nil,nil;firstorder
  |destruct IHlist as [pre [post ?]];
   destruct (total pivot a);
   [exists pre,(a::post)|exists (a::pre),post]; firstorder subst; auto;
   simpl; omega].
Defined.

Lemma quicksort_conc_lemma : forall {A : Set}
                                    (ord : A -> A -> Prop)
                                    a b c,
                               Sorted ord a -> Sorted ord (b :: c) -> (forall x, In x a -> ord x b) -> Sorted ord (a ++ (b :: c)).
Proof.
  intros A ord a b c H H0 H1.
  induction a as [|a a0 IHa];
  auto.
  apply Sorted_cons. 
  apply IHa.
  inversion H.
  auto.
  intros x inx.
  apply H1.
  apply in_cons.
  apply inx.
  destruct a0 as [|a0].
  apply HdRel_cons.
  apply H1.
  apply in_eq.
  apply HdRel_cons.
  inversion H.
  inversion H5.
  auto.
Defined.

Theorem quicksort : forall {A : Set}
                           (ord : A -> A -> Prop)
                           (total : forall a b, {ord a b} + {ord b a})
                           L,
                      {L' | (forall x, In x L <-> In x L') /\ Sorted ord L'}.
Proof.
  intros A ord total L.
  refine ((fix f n L (lenc : length L <= n) : {L' | (forall x, In x L <-> In x L') /\ Sorted ord L'} :=
             match n as m return (m = n -> _) with
               | 0 => fun eq => _
               | S m' => fun eq => _
             end eq_refl) (length L) L _).
  rewrite <- eq in lenc.
  destruct L.
  exists nil.
  split.
  intros a.
  split.
  trivial.
  trivial.
  apply Sorted_nil.
  contradict lenc.
  unfold length.
  intros Q.
  inversion Q.

  destruct L.
  exists nil.
  split.
  intros x.
  split.
  trivial.
  trivial.
  apply Sorted_nil.
  assert (X : {pre : Datatypes.list A & { post |
                   (forall x, In x pre -> ord x a) /\
                   (forall x, In x post -> ord a x) /\
                   (forall x, In x L <->
                              In x pre \/ In x post) /\
                   (length pre + length post = length L)}}).
  apply split_accto_pivot.
  apply total.
  destruct X as [pre [post [B [B0 [B1 B2]]]]].
  assert (X0 : {post' : list A | (forall x : A, In x post <-> In x post') /\ Sorted ord post'}).
  apply (f m').
  apply Le.le_S_n.
  apply Le.le_trans with (length (a :: L)).
  replace (length (a :: L)) with (S (length L)).
  rewrite <- B2.
  auto.
  assert (tmp1 : S (length pre + length post) = length pre + S (length post)).
  auto.
  rewrite -> tmp1.
  omega.
  auto.
  rewrite -> eq.
  auto.
  destruct X0 as [post' [X2 X3]].
  assert (Y0 : {pre' : list A | (forall x : A, In x pre <-> In x pre') /\ Sorted ord pre'}).
  apply (f m').
  apply Le.le_S_n.
  apply Le.le_trans with (length (a :: L)).
  apply Le.le_trans with (length (a :: L)).
  replace (length (a :: L)) with (S (length L)).
  rewrite <- B2.
  omega.
  auto.
  auto.
  rewrite -> eq.
  auto.
  destruct Y0 as [pre' [Y2 Y3]].
  exists (pre' ++ (a :: post')).
  split.
  split.
  intros inxal.
  inversion inxal.
  apply in_or_app.
  apply or_intror.
  rewrite <- H.
  apply in_eq.
  assert (H0 : In x pre \/ In x post).
  apply B1.
  apply H.
  destruct H0 as [H1 | H1].
  apply in_or_app.
  apply or_introl.
  apply Y2.
  apply H1.
  apply in_or_app.
  apply or_intror.
  apply in_cons.
  apply X2.
  apply H1.

  intros inx.

  assert (inx' : In x pre' \/ In x (a :: post')).
  apply in_app_or.
  apply inx.
  destruct inx' as [inxpre' | inxpost'].
  assert (inxpre : In x pre).
  apply Y2.
  apply inxpre'.
  apply in_cons.
  apply B1.
  auto.

  inversion inxpost'.
  rewrite <- H.
  apply in_eq.
  apply in_cons.
  assert (inxpost : In x post).
  apply X2.
  apply H.
  apply B1.
  auto.
  apply quicksort_conc_lemma.
  apply Y3.
  apply Sorted_cons.
  apply X3.
  destruct post'.
  apply HdRel_nil.
  apply HdRel_cons.
  apply B0.
  apply X2.
  apply in_eq.
  intros x inxpre'.
  apply B.
  apply Y2.
  apply inxpre'.
  auto.
Defined.