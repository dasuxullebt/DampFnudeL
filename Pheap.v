(** Implementation of a pairing heap in Coq.
  * (C) 2015 Christoph-Simon Senjak
  *   Require Import String.
  *   Eval compute in ("css" ++ "@" ++ "uxul" ++ "." ++ "de")%string.
  * See LICENSE for licensing information.
  **)

Require Import Coq.Init.Wf.
Require Import Program.
Require Import List.
Require Import Omega.
(*Require Import Combi.*)

Fixpoint foldlist {A B} (null : B) (f : A -> B -> B) (l : list A) : B :=
  match l with
      | [] => null
      | a :: r => f a (foldlist null f r)
  end.

(* PHEAPDEF1 *)
Inductive pheap A : Type :=
| Empty : pheap A
| Heap : A -> list (pheap A) -> pheap A.

Arguments Empty [_].
Arguments Heap [_] _ _.
(* PHEAPDEF2 *)
			   
Inductive pheap_in {A} : A -> pheap A -> Prop :=
| H_in : forall a l, pheap_in a (Heap a l)
| L_in : forall a b h l, In h l -> pheap_in a h -> pheap_in a (Heap b l).

Definition pheap_subseteq {A} a b := forall (x : A), pheap_in x a -> pheap_in x b.

Definition pheap_subsetneq {A} a b := @pheap_subseteq A a b /\ exists x, pheap_in x b /\ ~ pheap_in x a.

(* EXTEQ1 *)
Definition pheap_ext_eq {A} a b :=
    @pheap_subseteq A a b /\ @pheap_subseteq A b a.
(* EXTEQ2 *)

Lemma not_in_empty : forall {A} (b : A), ~ pheap_in b Empty.
Proof.
  intros A b phi.
  inversion phi.
Qed.

(* PHEAPCORRECT1 *)
Inductive pheap_correct {A} (cmp : A -> A -> bool) : pheap A -> Prop :=
| E_correct : pheap_correct cmp Empty
| H_correct : forall b l, Forall (pheap_correct cmp) l ->
                          (forall c, pheap_in c (Heap b l)
			             -> cmp b c = true) ->
                          pheap_correct cmp (Heap b l).
(* PHEAPCORRECT2 *)

Definition find_min {A} (h : pheap A) : option A :=
  match h with
    | Empty => None
    | Heap a _ => Some a
  end.


(* CMP1 *)
Definition cmp_ordering {A} (cmp : A -> A -> bool) :=
  (forall a, cmp a a = true) /\
  (forall a b c, cmp a b = true -> cmp b c = true -> cmp a c = true) /\
  (forall a b, cmp a b = true -> cmp b a = true -> a = b) /\
  (forall a b, cmp a b = true \/ cmp b a = true).
(* CMP2 *)

(* FINDMINSPEC1 *)
Lemma find_min_spec : forall {A} (b : A) cmp h,
                           cmp_ordering cmp ->
                           pheap_correct cmp h ->
                           pheap_in b h ->
                           exists a,
                             Some a = find_min h /\
                             cmp a b = true.
(* FINDMINSPEC2 *)			     
Proof.
  intros A b cmp h [refl [trans [antisym comp]]] corr b_in.

  inversion corr as [| B C D E G];
    [ contradict b_in;
      replace h with (@Empty A);
      apply not_in_empty
    | exists B;
      split;
      [ auto
      | apply E;
        rewrite -> G;
        auto ]].
Qed.

Function merge {A} (cmp : A -> A -> bool) (g h : pheap A) :=
  match g with
    | Empty => h
    | Heap a g2 =>
      match h with
        | Empty => g
        | Heap b h2 =>
          match cmp a b with
            | true => Heap a (h :: g2)
            | false => Heap b (g :: h2) 
          end
      end
  end.

(* MERGESPEC1 *)
Lemma merge_spec : forall {A} cmp (b : A) g h,
                     (pheap_in b g \/ pheap_in b h) <->
                     pheap_in b (merge cmp g h).
(* MERGESPEC2 *)
Proof.
  intros A cmp b g h.
  split.
  intro bgh.
  destruct bgh as [bg | bh].  
  destruct bg as [g' g''|B C D].
  destruct h as [|h' h''].
  simpl.
  econstructor.
  simpl.
  destruct (cmp g' h').
  econstructor.
  econstructor.
  econstructor.
  eauto.
  econstructor.
  destruct h as [|h' h''] eqn:hd.
  simpl.
  econstructor.
  eauto.
  eauto.
  simpl.
  destruct (cmp C h') eqn:ch.
  eapply L_in.
  apply in_cons.
  eauto.
  eauto.

  eapply L_in.
  eapply in_eq.
  eapply L_in.
  eauto.
  eauto.

  (* TODO: without copypaste *)
  destruct bh as [h' h''|B C D].
  destruct g as [|g' g''].
  simpl.
  econstructor.
  simpl.
  destruct (cmp g' h').
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  destruct g as [|g' g''] eqn:gd.
  simpl.
  econstructor.
  eauto.
  eauto.
  simpl.
  destruct (cmp g' C) eqn:gc.
  eapply L_in.
  apply in_eq.
  econstructor.
  eauto.
  eauto.

  eapply L_in.
  apply in_cons.
  eauto.
  eauto.

  intro phbgh.
  destruct g as [|g' g''].
  simpl in phbgh.
  auto.

  destruct h as [|h' h''].
  simpl in phbgh.
  auto.

  simpl in phbgh.
  destruct (cmp g' h') eqn:gh.
  inversion phbgh.
  apply or_introl.
  constructor.

  match goal with
    | Q : In h _ |- _ => inversion Q
  end.
  match goal with
    | Q : Heap h' h'' = h, R : pheap_in _ h |- _ => rewrite <- Q in R; auto
  end.

  apply or_introl.
  eapply L_in.
  eauto.
  eauto.
  
  inversion phbgh.
  apply or_intror.
  econstructor.

  match goal with
    | Q : In h _ |- _ => inversion Q
  end.
  match goal with
    | Q : Heap g' g'' = h, R : pheap_in _ h |- _ => rewrite <- Q in R; auto
  end.
  
  apply or_intror.
  eapply L_in.
  eauto.
  eauto.
Qed.

Lemma merge_correct : forall {A} cmp (g h : pheap A),
                        cmp_ordering cmp ->
                        pheap_correct cmp g ->
                        pheap_correct cmp h ->
                        pheap_correct cmp (merge cmp g h).
Proof.
  intros A cmp g h [refl [trans [antisym comp]]] cor_g cor_h.
  destruct g as [|g' g''].
  auto.
  destruct h as [|h' h''].
  auto.
  simpl.
  destruct (cmp g' h') eqn:gh.
  apply H_correct.
  apply Forall_cons.
  auto.

  inversion cor_g as [|x l corr_g' ing [xg' lg'']]; auto.

  intros c cin;
  inversion cin as [a l ac [cg' lhp]|a b php lphp inph phc ac [bg' lhp]];
  [ auto
  | inversion inph as [X | X];
    [ rewrite <- X in phc;
      inversion phc as [d lpa dc [ch' lpah'']|
                        d e pha lpa inh'' phin dc [eh' phah'']];
      [ auto
      | apply (trans g' h' c);
        [ auto
        | inversion cor_h as [|x l corr_h' ing [xh' lh'']];
          apply ing; econstructor; eauto ]]
    | inversion phc as [d lpa dc [ch' lpah'']|
                        d e pha lpa inh'' phin dc [eh' phah'']];
      ( inversion cor_g as [|x l corr_g' ing [xg' lg'']];
        [ apply ing;
          econstructor;
          eauto ] ) ]].

  constructor;
    [ constructor; [auto | inversion cor_h; auto]
    | assert (cmphg : cmp h' g' = true);
      [  destruct (comp h' g') as [|Y];
        [ trivial
        | rewrite -> Y in gh; inversion gh]  
       | intros c cin;
         inversion cin as [a l ac [cg' lhp]|a b php lphp inph phc ac [bg' lhp]];
         [ auto
         | inversion inph as [X | X];
           [ rewrite <- X in phc;
             inversion phc as [d lpa dc [ch' lpah'']|
                               d e pha lpa inh'' phin dc [eh' phah'']];
             [ auto
             | apply (trans h' g' c);
               [ auto
               | inversion cor_g as [|x l corr_g' ing [xg' lg'']];
                 [ apply ing; econstructor; eauto ]]]
           | inversion cor_h as [|x l corr_h' ing [xh' lh'']];
             apply ing; econstructor; eauto ]]]].
Qed.

Function insert {A} (cmp : A -> A -> bool) (b : A) (h : pheap A) :=
  merge cmp (Heap b nil) h.

(* INSERTSPEC1 *)
Lemma insert_spec :
  forall {A} (cmp : A -> A -> bool) (a b : A) (h : pheap A),
    cmp_ordering cmp ->
    (pheap_in a (insert cmp b h) <-> (a = b \/ pheap_in a h)).
(* INSERTSPEC2 *)
Proof.
  intros ? ? a b ? ord.
  split;
    [ intro ain;
      destruct (proj2 (merge_spec cmp a (Heap b nil) h) ain) as [X | X];
      [ apply or_introl;
        inversion X;
        [ reflexivity
        | match goal with | Q : In _ nil |- _ => inversion Q end ]
      | auto ]
    | intro x;
      assert (k : pheap_in a (Heap b nil) \/ pheap_in a h);
      [ destruct x as [ab | ah];
        [ apply or_introl;
          rewrite -> ab;
          constructor
        | auto ]
      | apply merge_spec;
        auto ]].
Qed.  

Lemma insert_correct :
  forall {A} (cmp : A -> A -> bool) (b : A) (h : pheap A),
    cmp_ordering cmp ->
    pheap_correct cmp h ->
    pheap_correct cmp (insert cmp b h).
Proof.
  intros ? ? ? ? ord ?.
  apply merge_correct.
  auto.
  econstructor.
  econstructor.
  intros c cin.
  inversion cin.
  destruct ord.
  auto.
  match goal with
    | Q : In _ nil |- _ => inversion Q
  end.
  auto.
Qed.  

Fixpoint merge_pairs {A} (cmp : A -> A -> bool) (l : list (pheap A)) :=
  match l with
    | nil => Empty
    | (a :: nil) => a
    | (a :: b :: l') => merge cmp (merge cmp a b) (merge_pairs cmp l')
  end.

Functional Scheme merge_pairs_ind := Induction for merge_pairs Sort Prop.

Lemma merge_pairs_correct :
  forall {A} (cmp : A -> A -> bool) (l : list (pheap A)),
    cmp_ordering cmp ->
    Forall (pheap_correct cmp) l -> pheap_correct cmp (merge_pairs cmp l).
Proof.
  intros A cmp l cmpo.
  revert l.
  refine (fix f l All :=
            match l as L return (l=L->_) with
              | nil => fun eq => _
              | (a :: nil) => fun eq => _
              | (a :: b :: l') => fun eq => _
            end eq_refl);
    [ simpl;
      constructor
    | idtac
    | idtac ].

  simpl.
  rewrite -> eq in All.
  inversion All.
  auto.

  rewrite -> eq in All.
  inversion All.
  match goal with
    | H : Forall (pheap_correct cmp) (b :: l') |- _ =>
      inversion H
  end.
  simpl.
  eapply merge_correct.
  auto.
  eapply merge_correct.
  auto.
  auto.
  auto.
  apply f.
  auto.
Qed.

Lemma merge_pairs_lemma :
  forall {A} (cmp : A -> A -> bool) (l : list (pheap A)) b,
    Exists (pheap_in b) l -> pheap_in b (merge_pairs cmp l).
Proof.
  intros A cmp.
  
  refine (fix f l b x :=
            match l as L return l=L->_ with
              | nil => fun eq => _
              | (a :: nil) => fun eq => _
              | (a :: b :: l') => fun eq => _
            end eq_refl);
    [ rewrite -> eq in x;
      inversion x
    | simpl;
      rewrite -> eq in x;
      inversion x;
      [ auto
      | match goal with | X : Exists _ nil |- _ => inversion X end ]
    | idtac].
  
  simpl;
  erewrite <- merge_spec;
  erewrite <- merge_spec;
  rewrite -> eq in x.

  
  inversion x;
  [ auto
  | match goal with | X : Exists _ (?B :: l') |- _ => inversion X end;
    auto;
    apply or_intror;
    apply f;
    auto ].
Qed.

Lemma merge_pairs_lemma_2 :
  forall {A} (cmp : A -> A -> bool) (l : list (pheap A)) b,
   pheap_in b (merge_pairs cmp l) -> Exists (pheap_in b) l.
Proof.
  intros A cmp l b.

  functional induction (merge_pairs cmp l).

  intro Q.
  inversion Q.

  intro Q.
  constructor.
  trivial.

  intro phi.
  destruct (proj2 (merge_spec _ _ _ _) phi) as [B | B].
  destruct (proj2 (merge_spec _ _ _ _) B) as [C | C].
  constructor.
  trivial.

  constructor 2.
  constructor.
  trivial.

  constructor 2.
  constructor 2.
  apply IHp.
  exact B.
Qed.

Function delete_min {A} (cmp : A -> A -> bool) (h : pheap A) :=
  match h with
    | Empty => None
    | Heap a b => Some (merge_pairs cmp b)
  end.

Lemma delete_min_spec_2 : forall {A} cmp (g : pheap A),
                            None = delete_min cmp g -> g = Empty.
Proof.
  intros A cmp g none.
  destruct g.
  reflexivity.
  inversion none.
Qed.

Function find_and_delete_min {A} (cmp : A -> A -> bool) (h : pheap A) :=
  match h with
    | Empty => None
    | Heap a b => Some (a, merge_pairs cmp b)
  end.

Lemma find_and_delete_min_spec_1 :
  forall {A} (cmp : A -> A -> bool) (h : pheap A),
    find_and_delete_min cmp h = None <-> find_min h = None.
Proof.
  intros a cmp h.
  split.
  destruct h.
  reflexivity.
  simpl.
  intro Q; inversion Q.
  destruct h.
  simpl.
  reflexivity.
  intro Q; inversion Q.
Qed.

Lemma find_and_delete_min_spec_2 :
  forall {A} (cmp : A -> A -> bool) (h : pheap A) a b,
    find_and_delete_min cmp h = Some (a, b) <-> (find_min h = Some a /\ delete_min cmp h = Some b).
Proof.
  intros A cmp h a b.
  split.
  destruct h.
  intro Q; inversion Q.
  simpl.
  intro Q.
  inversion Q.
  auto.

  destruct h.
  intros [Q ?].
  inversion Q.
  simpl.
  intros [Q R].
  inversion Q as [Q_].
  inversion R as [R_].
  reflexivity.
Qed.


Lemma cmp_eqdec : forall {A} (cmp : A -> A -> bool),
                    cmp_ordering cmp ->
                    forall (a b : A), {a = b} + {a <> b}.
Proof.
  intros A cmp [refl [trans [antisym comp]]].
  intros a b.
  destruct (cmp a b) eqn:ab.
  destruct (cmp b a) eqn:ba.
  apply left.
  apply antisym; auto.
  apply right.
  intro Q.
  rewrite -> Q in ba.
  rewrite -> refl in ba.
  inversion ba.
  apply right.
  intro Q.
  rewrite -> Q in ab.
  rewrite -> refl in ab.
  inversion ab.
Qed.

Lemma delete_min_spec_1 : forall {A} (cmp : A -> A -> bool) g h,
                            cmp_ordering cmp ->
                            pheap_correct cmp h ->
                            Some g = delete_min cmp h ->
                            forall b, pheap_in b h ->
                                      (pheap_in b g \/ Some b = find_min h).
Proof.
  intros A cmp g h ord cor_ha gdm b hin.

  destruct h as [|a l].
  inversion hin.
  destruct (cmp_eqdec cmp ord a b) as [abeq | abneq];
    [ rewrite -> abeq; auto | idtac ].

  apply or_introl.
  inversion gdm.
  inversion hin.
  contradict abneq.
  auto.

  apply merge_pairs_lemma.
  apply Exists_exists.
  eexists; split; eauto.
Qed.

Lemma delete_min_correct : forall {A} cmp (g h : pheap A),
                        cmp_ordering cmp ->
                        pheap_correct cmp h ->
                        Some g = delete_min cmp h ->
                        pheap_correct cmp g.
Proof.
  intros A cmp g h ord ch gh.
  destruct h.
  inversion gh.
  inversion gh.
  apply merge_pairs_correct.
  auto.
  inversion ch.
  auto.
Qed.

(** Numbers for recursion *)
Fixpoint pheap_num {A} (h : pheap A) : nat :=
  match h with
    | Empty => 0
    | Heap _ l =>
      foldlist 1 plus (map pheap_num l)
  end.

Lemma pheap_num_merge : forall {A} cmp (g h : pheap A),
                          pheap_num (merge cmp g h) = pheap_num g + pheap_num h.
Proof.
  intros A cmp g h.
  destruct g as [|ag g].
  reflexivity.
  destruct h as [|ah h].
  simpl.
  omega.
  simpl.
  destruct (cmp ag ah).
  simpl.
  omega.
  simpl.
  reflexivity.
Qed.

Lemma pheap_num_merge_pairs : forall {A} cmp (l : list (pheap A)),
                                foldlist 0 plus (map pheap_num l) = pheap_num (merge_pairs cmp l).
Proof.
  intros A cmp.
  refine (fix f l :=
            match l as L return (L=l->_) with
              | nil => fun eqL => _
              | x :: nil => fun eqL => _
              | x :: y :: l' => fun eqL => _
            end eq_refl);
    [ reflexivity
    | simpl; omega
    | simpl;
      rewrite -> pheap_num_merge;
      rewrite -> pheap_num_merge;
      rewrite -> f;
      omega ].
Qed.

Lemma deletemin_num :
  forall {A} cmp (h k : pheap A), delete_min cmp h = Some k -> pheap_num k + 1 = pheap_num h.
Proof.
  intros A cmp h k dm.
  destruct h.
  inversion dm.
  simpl in dm.
  inversion dm as [dm2].
  rewrite <- pheap_num_merge_pairs.
  simpl.
  revert l k dm dm2.
  induction l as [|x l IHl].
  reflexivity.
  intros.
  simpl.
  erewrite <- IHl.
  omega.
  reflexivity.
  reflexivity.
Qed.

(*Lemma pheap_in_dec : forall {A} (cmp : A -> A -> bool) h,
                       cmp_ordering cmp ->
                       pheap_correct cmp h ->
                       forall b, pheap_in b h + (pheap_in b h -> False).
Proof.
  intros A cmp h_ ord cor_ b.

  refine ((fix f h cor (n : nat) (nle : pheap_num h <= n) {struct n} 
           : pheap_in b h + (pheap_in b h -> False) := _) h_ cor_ (pheap_num h_) _).

  destruct h as [|a l];
  [ apply inr; intro Q; inversion Q
  | destruct (cmp_eqdec cmp ord a b) as [abeq | abneq];
    [ apply inl;
      rewrite -> abeq;
      constructor
    | assert (G : let x := {h | In h l /\ pheap_in b h} in
                  x + (x -> False));
      [
      | destruct G as [[h [inhl inbh]] | no];
        [ apply inl; econstructor 2; [exact inhl | trivial]
        | apply inr;
          intro Q; inversion Q;
          [ apply abneq;
            symmetry;
            trivial
          | contradict no;
            exists h;
            auto ]]]]].

  assert (eaa1 : Forall (pheap_correct cmp) l).
  inversion cor.
  trivial.

  assert (eaa2 : Forall (fun x => pheap_num x < n) l).
  assert (Q : forall x, In x l -> pheap_num x < pheap_num (Heap a l));
    [ apply Forall_forall;
      apply pheap_num_sub
    | apply Forall_forall;
      intros x xl;
      assert (pheap_num x < pheap_num (Heap a l));
      [apply (Q x xl) | omega]].

  refine ((fix e l_
                     (corl_ : Forall (pheap_correct cmp) l_)
                     (ltL_ : Forall (fun x => pheap_num x < n) l_) {struct l_}
                 : let x := {h | In h l_ /\ pheap_in b h} in x + (x -> False) :=
                   match l_ as L return (l_ = L -> _) with
                     | [] => fun eqL => _
                     | l1 :: l2 => fun eqL => _
                   end eq_refl) l eaa1 eaa2);
        [ apply inr;
          intros [h [Q ?]];
          inversion Q
        | destruct n as [|n];
          [ assert (pheap_num (Heap a l) > 0); [ apply pheap_num_gt_0 | omega ]
          | ]].

  assert (fa1 : pheap_correct cmp l1).
  rewrite -> eqL in corl_.
  inversion corl_.
  trivial.

  edestruct (f l1 fa1 n) as [isin | notin];
    [ rewrite -> eqL in ltL_;
      inversion ltL_;
      assert (X : pheap_num l1 <= n); [omega | exact X]
    | apply inl;
      exists l1;
      split;
      [ constructor;
        reflexivity
      | exact isin ]
    | ].

  assert (ea1 : Forall (pheap_correct cmp) l2).
  rewrite -> eqL in corl_;
    inversion corl_;
    auto.

  assert (ea2 : Forall (fun x : pheap A => pheap_num x < S n) l2).
  rewrite -> eqL in ltL_;
    inversion ltL_;
    auto.

  set (E := e l2 ea1 ea2).
  simpl in E.

  destruct E as [[h [inhl2 in2]] | no];
    [apply inl;
      exists h;
      split; [ constructor 2; trivial | trivial ]
    | apply inr;
      intros [h [inh php]];
      inversion inh as [l1h | l2h];
      [ contradict notin;
        rewrite -> l1h;
        trivial
      | contradict no;
        exists h;
        split;
        trivial ]].

  omega.
Defined.*)

(** Some Lemmas for Orderings *)
Function LexCmp {A B : Set}
         (cmpA : A -> A -> bool)
         (cmpB : B -> B -> bool)
         (x y : (A * B)) : bool :=
  if cmpA (fst x) (fst y)
  then if cmpA (fst y) (fst x) (* equality *)
       then cmpB (snd x) (snd y)
       else true
  else false.

Lemma LexOrd : forall {A B : Set}
                      (cmpA : A -> A -> bool)
                      (cmpB : B -> B -> bool),
                 cmp_ordering cmpA ->
                 cmp_ordering cmpB ->
                 cmp_ordering (LexCmp cmpA cmpB).
Proof.
  intros A B cmpA cmpB
         [arefl [atrans [aantisym acomplete]]]
         [brefl [btrans [bantisym bcomplete]]].
  split.

  intros [a b].
  compute.
  rewrite -> arefl.
  apply brefl.

  split.
  intros [xa xb] [ya yb] [za zb].
  unfold LexCmp.
  simpl.
  intros cmpx cmpy.

  destruct (cmpA xa ya) eqn:cxya;
  [ destruct (cmpA ya za) eqn:cyza;
    [ rewrite -> (atrans xa ya za cxya cyza);
      destruct (cmpA za xa) eqn:czxa;
      [ rewrite -> (atrans ya za xa cyza czxa) in cmpx;
        rewrite -> (atrans za xa ya czxa cxya) in cmpy;
        apply (btrans _ _ _ cmpx cmpy)
      | reflexivity ]
    | inversion cmpy ]
  | inversion cmpx ].

  split.
  intros [xa xb] [ya yb].
  unfold LexCmp.
  simpl.
  intros Q R.
  destruct (cmpA xa ya) eqn:cxya.
  destruct (cmpA ya xa) eqn:cyxa.
  rewrite -> (aantisym _ _ cxya cyxa).
  rewrite -> (bantisym _ _ Q R).
  reflexivity.
  inversion R.
  inversion Q.

  intros [xa xb] [ya yb].
  unfold LexCmp.
  simpl.

  destruct (cmpA xa ya) eqn:cxya.
  destruct (cmpA ya xa) eqn:cyxa.
  apply bcomplete.
  auto.
  destruct (acomplete ya xa) as [A1 | A1].
  rewrite -> A1.
  auto.
  rewrite -> A1 in cxya.
  inversion cxya.
Qed.

(** delete min or leave empty *)
Function x_delete_min {A} cmp (h : pheap A) :=
  match delete_min cmp h with
    | None => Empty
    | Some a => a
  end.


(** this function is only for proving 
Fixpoint pheap_to_list_ {A} (cmp : A -> A -> bool) (ph : pheap A) (l : list A) (m : nat) :=
  match m with
    | 0 => l
    | S m_ => match find_and_delete_min cmp ph with
                | None => l
                | Some (a, b) => pheap_to_list_ cmp b (a :: l) m_
              end
  end. *)

Lemma wf_deletemin : forall {A} (cmp : A -> A -> bool), well_founded (fun b a => delete_min cmp a = Some b).
Proof.
  intros A cmp.
  unfold well_founded.
  intro a_.
  refine ((fix f a (n : nat) (m : pheap_num a <= n) {struct n}
           : Acc (fun b a : pheap A => delete_min cmp a = Some b) a :=
             match n as N return (n=N->_) with
               | 0 => fun eqN => _
               | S n_ => fun eqN => _
             end eq_refl) a_ (pheap_num a_) _).
  destruct a.
  constructor.
  intros y dm.
  inversion dm.
  rewrite -> eqN in m.
  simpl in m.
  contradict m.
  induction (map pheap_num l); simpl; omega.

  constructor.
  intros y dmy.
  apply (f _ n_).
  assert (D : pheap_num y + 1 = pheap_num a).
  eapply deletemin_num.
  exact dmy.
  omega.
  omega.
Qed.

(* noncomputational decidability [yields a slow algorithm] *)
Lemma pheap_in_dec_nc : forall {A} (cmp : A -> A -> bool) g,
                          cmp_ordering cmp ->
                          pheap_correct cmp g ->
                          forall b, pheap_in b g \/ (pheap_in b g -> False).
Proof.
  intros A cmp g ord corr b.
  induction (wf_deletemin cmp g).
  destruct x.

  apply or_intror.
  intro Q.
  inversion Q.

  destruct (cmp_eqdec cmp ord a b) as [abeq | abneq].
  apply or_introl.
  rewrite -> abeq.
  constructor.

  edestruct (H0).
  reflexivity.
  apply merge_pairs_correct.
  exact ord.
  inversion corr.
  trivial.

  apply or_introl.

  apply merge_pairs_lemma_2 in H1.
  apply Exists_exists in H1.
  destruct H1 as [x [inxl phbx]].
  econstructor 2.
  exact inxl.
  exact phbx.

  apply or_intror.
  intro Q.
  inversion Q.
  apply abneq.
  symmetry.
  trivial.

  contradict H1.
  apply merge_pairs_lemma.
  apply Exists_exists.
  exists h.
  auto.
Qed.

Lemma pheap_in_weaken : forall {A} (cmp : A -> A -> bool) g h,
                            cmp_ordering cmp ->
                            pheap_correct cmp h ->
                            Some g = delete_min cmp h ->
                            forall x, pheap_in x g -> pheap_in x h.
Proof.
  intros A cmp g h ord pc gdm b b_in_g.
  destruct h as [|a l].
  inversion gdm.

  destruct (cmp_eqdec cmp ord a b) as [abeq | abneq].
  rewrite -> abeq.
  constructor.

  simpl in gdm.
  inversion gdm as [gdm_].
  rewrite -> gdm_ in b_in_g.
  apply merge_pairs_lemma_2 in b_in_g.
  apply Exists_exists in b_in_g.
  destruct b_in_g as [x [xl bx]].
  econstructor 2.
  exact xl.
  exact bx.
Qed.
