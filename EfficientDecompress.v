Require Import EncodingRelation.
Require Import EncodingRelationProperties.
Require Import Shorthand.
Require Import Backreferences.
Require Import Combi.
Require Import StrongDec.

Require Import Ascii.
Require Import String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Program.
Require Import List.
Import ListNotations.

Inductive ExpList (A : Set) : Set :=
| Enil : ExpList A
| Econs1 : A -> ExpList (A * A) -> ExpList A
| Econs2 : A -> A -> ExpList (A * A) -> ExpList A.

Arguments Enil [_].
Arguments Econs1 [_] _ _.
Arguments Econs2 [_] _ _ _.

Inductive EDepair {A : Set}  : list (A * A) -> list A -> Prop :=
| EDnil : EDepair nil nil
| EDCons : forall a b LD L, EDepair L LD -> EDepair ((a, b) :: L) (a :: b :: LD).

Lemma EDepairNth : forall {A} L LD n Q, @EDepair A L LD -> (nth (2 * n) LD Q, nth (2 * n + 1) LD Q) = nth n L (Q, Q).
Proof.
  intros A L LD n;
  revert n L LD;
  induction n as [|n IHn];
    [ intros ? ? ? edep;
      dependent destruction edep; [reflexivity | reflexivity]
    | intros L LD Q edep;
      dependent destruction edep; 
      [ reflexivity
      | replace (nth (2 * S n) (a :: b :: LD) Q) with (nth (2 * n) LD Q);
        [ replace (nth (2 * S n + 1) (a :: b :: LD) Q) with (nth (2 * n + 1) LD Q);
          [ apply IHn; exact edep
          | replace (2 * S n + 1) with (S (S (2 * n + 1))); [reflexivity | omega]]
        | replace (2 * S n) with (S (S (2 * n))); [reflexivity | omega]]]].
Qed.

(* notice: we utilize lazyness! *)
Fixpoint depair {A : Set} (l : list (A * A)) : list A :=
  match l with
    | nil => nil
    | ((a, b) :: l') => a :: b :: depair l'
  end.

Lemma depair_EDepair : forall {A} l, @EDepair A l (depair l).
Proof.
  intros A.
  induction l as [|[a b] l IHl].
  constructor.
  constructor.
  exact IHl.
Qed.

Inductive EReflects {A : Set} : ExpList A -> list A -> Prop :=
| ERnil : EReflects Enil nil
| ERcons1 : forall (E : ExpList (A * A)) (L : list (A*A)) (LD : list A) (a : A), @EReflects (A * A) E L -> EDepair L LD -> EReflects (Econs1 a E) (a :: LD)
| ERcons2 : forall (E : ExpList (A * A)) (L : list (A*A)) (LD : list A) (a b : A), @EReflects (A * A) E L -> EDepair L LD -> EReflects (Econs2 a b E) (a :: b :: LD).

Fixpoint EtoL {A : Set} (e : ExpList A) : list A :=
  match e with
    | Enil => nil
    | Econs1 a e' => a :: depair (EtoL e')
    | Econs2 a b e' => a :: b :: depair (EtoL e')
  end.

Lemma EtoL_EReflects : forall {A} e, @EReflects A e (EtoL e).
Proof.
  intros A.
  induction e as [|? a e IHe|? a b e IHe].
  constructor.
  replace (EtoL (Econs1 a e)) with (a :: depair (EtoL e)).
  apply (ERcons1 _ (EtoL e)).
  trivial.
  apply depair_EDepair.
  reflexivity.

  replace (EtoL (Econs2 a b e)) with (a :: b :: depair (EtoL e)).
  apply (ERcons2 _ (EtoL e)).
  trivial.
  apply depair_EDepair.
  reflexivity.
Qed.

Fixpoint Elen {A : Set} (x : ExpList A) {struct x} : nat :=
  match x with
    | Enil => 0
    | Econs1 _ x' => 1 + 2 * Elen x'
    | Econs2 _ _ x' => 2 + 2 * Elen x'
  end.

Fixpoint Enth {A : Set} (n : nat) (x : ExpList A) (default : A) {struct x} : A :=
  match x with
    | Enil => default
    | Econs1 a x' => match n with
                       | 0 => a
                       | (S n') => match Enth (n' / 2) x' (default, default) with
                                     | (a, b) => match n' mod 2 with
                                                   | 0 => a
                                                   | _ => b
                                                 end
                                   end
                     end
    | Econs2 a b x' => match n with
                         | 0 => a
                         | 1 => b
                         | (S (S n')) => match Enth (n' / 2) x' (default, default) with
                                           | (a, b) => match n' mod 2 with
                                                         | 0 => a
                                                         | _ => b
                                                       end
                                         end
                       end
  end.

Lemma ElenEnth : forall {A : Set} (x : ExpList A) (a b : A) n,
                   a <> b -> n < Elen x -> Enth n x a = Enth n x b.
Proof.
  intro A;
  induction x as [| ? a x IHx | ? a b x IHx];
    intros a0 b0 n neq nelen;
    [ inversion nelen | idtac | destruct n; [reflexivity | idtac] ];
  (destruct n;
    [ reflexivity
    | simpl;
      assert (K1 : n = 2 * (n / 2) + n mod 2);
      [ apply div_mod; omega
      | assert (K2 : n mod 2 < 2);
        [ apply mod_bound_pos; [ omega | omega ]
        | assert (K4 : n / 2 < Elen x);
          [solve [assert (K3 : Elen (Econs2 a b x) = S ( S ( 2 * Elen x )));
                   [ reflexivity | omega]
                 | assert (K3 : Elen (Econs1 a x) = S ( 2 * Elen x ));
                   [reflexivity | omega]]
          | rewrite -> (IHx (a0, a0) (b0, b0));
            [ reflexivity
            | intro Q;
              contradict neq;
              inversion Q;
              reflexivity
            | auto ]]]]]).
Qed.

Lemma Enth_nth : forall {A : Set} (x : ExpList A) (a : A) (n : nat), Enth n x a = nth n (EtoL x) a.
Proof.
  intros A.
  induction x as [| ? a x IHx | ? a b x IHx]. 
  intros a n.
  destruct n; [reflexivity | reflexivity].

  intros a0 n.
  destruct n; [reflexivity | idtac].

  assert (k : Enth (S n) (Econs1 a x) a0 = match Enth (n / 2) x (a0, a0) with
                                             | (a, b) => match n mod 2 with
                                                           | 0 => a
                                                           | _ => b
                                                         end
                                           end).
  reflexivity.
  
  destruct (n mod 2) eqn:nm2.
  rewrite -> k.
  rewrite -> IHx.
  rewrite <- (EDepairNth (EtoL x) (depair (EtoL x))).
  assert (l : EtoL (Econs1 a x) = a :: depair (EtoL x)).
  reflexivity.
  rewrite -> l.
  assert (m : 2 * (n / 2) = n).
  assert (m : 2 * (n / 2) + n mod 2 = n).
  symmetry.
  apply div_mod.
  omega.
  omega.
  rewrite -> m.
  reflexivity.
  apply depair_EDepair.

  rewrite -> k.
  rewrite -> IHx.
  assert (l : EtoL (Econs1 a x) = a :: depair (EtoL x)).
  reflexivity.
  rewrite -> l.
  rewrite <- (EDepairNth (EtoL x) (depair (EtoL x))).
  assert (m : 2 * (n / 2) + 1 = n).
  assert (m : 2 * (n / 2) + n mod 2 = n).
  symmetry.
  apply div_mod.
  omega.
  assert (n mod 2 < 2).
  apply mod_bound_pos.
  omega.
  omega.
  omega.
  rewrite -> m.
  reflexivity.
  apply depair_EDepair.

  intros a0 n.
  destruct n; [reflexivity | destruct n; [reflexivity | idtac]].

  assert (k : Enth (S (S n)) (Econs2 a b x) a0 = match Enth (n / 2) x (a0, a0) with
                                                   | (a, b) => match n mod 2 with
                                                                 | 0 => a
                                                                 | _ => b
                                                               end
                                                 end).
  reflexivity.
  
  destruct (n mod 2) eqn:nm2.
  rewrite -> k.
  rewrite -> IHx.
  rewrite <- (EDepairNth (EtoL x) (depair (EtoL x))).
  assert (l : EtoL (Econs2 a b x) = a :: b :: depair (EtoL x)).
  reflexivity.
  rewrite -> l.
  assert (m : 2 * (n / 2) = n).
  assert (m : 2 * (n / 2) + n mod 2 = n).
  symmetry.
  apply div_mod.
  omega.
  omega.
  rewrite -> m.
  reflexivity.
  apply depair_EDepair.

  rewrite -> k.
  rewrite -> IHx.
  assert (l : EtoL (Econs2 a b x) = a :: b :: depair (EtoL x)).
  reflexivity.
  rewrite -> l.
  rewrite <- (EDepairNth (EtoL x) (depair (EtoL x))).
  assert (m : 2 * (n / 2) + 1 = n).
  assert (m : 2 * (n / 2) + n mod 2 = n).
  symmetry.
  apply div_mod.
  omega.
  assert (n mod 2 < 2).
  apply mod_bound_pos.
  omega.
  omega.
  omega.
  rewrite -> m.
  reflexivity.
  apply depair_EDepair.
Qed.

Fixpoint Econs {A : Set} (a : A) (x : ExpList A) {struct x} : ExpList A :=
  match x with
    | Enil => Econs1 a Enil
    | Econs1 b x' => Econs2 a b x'
    | Econs2 b c x' => Econs1 a (Econs (b, c) x')
  end.

Lemma EconsL : forall {A : Set} (a : A) x, EtoL (Econs a x) = a :: EtoL x.
Proof.
  intros A a x.
  revert x a.
  induction x as [| ? a x IHx| ? a b x IHx].

  reflexivity.

  intro b.
  reflexivity.

  intro c.
  assert (k : Econs c (Econs2 a b x) = Econs1 c (Econs (a, b) x)).
  reflexivity.
  rewrite -> k.
  assert (EtoL (Econs1 c (Econs (a, b) x)) = c :: depair (EtoL (Econs (a, b) x))).
  rewrite -> IHx.
  simpl.
  rewrite -> IHx.
  reflexivity.
  simpl.
  rewrite -> IHx.
  reflexivity.
Qed.

Lemma depairlen : forall {A : Set} l, ll (@depair A l) = 2 * ll l.
Proof.
  intros A.
  induction l as [|[a b] l IHl];
    [ reflexivity
    | simpl;
      rewrite -> IHl;
      omega].
Qed.

Lemma ElenLen : forall {A : Set} (x : ExpList A), Elen x = ll (EtoL x).
Proof.
  intro A;
  induction x as [| ? a x IHx| ? a b x IHx];
    (reflexivity
       || (simpl;
           rewrite -> depairlen;
           rewrite <- IHx;
           omega)).
Qed.

Inductive BufferedList (A : Set) (maxbuf : nat) : Set :=
| mkBufferedList : forall
                     (cbuf : nat)
                     (bb1 bb2 : ExpList A)
                     (l : list A -> list A),
                     BufferedList A maxbuf.

Arguments mkBufferedList [_] _ _ _ _ _.

Definition blCorrectL {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf) :=
  match bl with
    | mkBufferedList _ _ _ l => forall l', l l' = (l []) ++ l'
  end.

Definition blCorrectB {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf) :=
  match bl with
    | mkBufferedList cbuf bb1 bb2 l =>
      1 <= maxbuf /\
      cbuf <= maxbuf /\
      ll (EtoL bb1) = cbuf /\
      ll (EtoL bb2) <= maxbuf /\
      (ll (EtoL bb2) < maxbuf -> l [] = [])
  end.

Definition nilBL (A : Set) (maxbuf : nat) : BufferedList A (S maxbuf) :=
  mkBufferedList (S maxbuf) 0 Enil Enil (fun x => x).

Lemma blclNil : forall {A : Set} {maxbuf : nat}, blCorrectL (nilBL A maxbuf).
Proof.
  intros A m.
  compute.
  auto.
Qed.

Lemma blcbNil : forall {A : Set} {maxbuf : nat}, blCorrectB (nilBL A maxbuf).
Proof.
  intros A m.
  compute.
  firstorder.
Qed.

Function pushBL {A : Set} {maxbuf : nat} (a : A) (bl : BufferedList A maxbuf) : BufferedList A maxbuf :=
  match bl with
    | mkBufferedList cbuf bb1 bb2 l =>
      match nat_compare cbuf maxbuf with
        | Lt => mkBufferedList maxbuf (S cbuf) (Econs a bb1) bb2 l
        | _ => mkBufferedList maxbuf 1 (Econs a Enil) bb1
                              (fun x => l ((rev (EtoL bb2)) ++ x))
      end
  end.

Lemma blclPush : forall {A : Set} {maxbuf : nat} (a : A) (bl : BufferedList A maxbuf),
                  blCorrectL bl -> blCorrectL (pushBL a bl).
Proof.
  intros A maxbuf a bl blc.
  destruct bl as [cbuf bb1 bb2 l].
  unfold pushBL.
  destruct (nat_compare cbuf maxbuf).
  unfold blCorrectL.
  unfold blCorrectL in blc.
  intro l'.
  rewrite -> (blc (rev (EtoL bb2) ++ l')).
  rewrite -> (blc (rev (EtoL bb2) ++ [])).
  rewrite -> app_nil_r.
  rewrite -> app_assoc.
  reflexivity.

  unfold blCorrectL.
  unfold blCorrectL in blc.
  trivial.
  
  unfold blCorrectL.
  unfold blCorrectL in blc.
  intro l'.
  rewrite -> (blc (rev (EtoL bb2) ++ l')).
  rewrite -> (blc (rev (EtoL bb2) ++ [])).
  rewrite -> app_nil_r.
  rewrite -> app_assoc.
  reflexivity.
Qed.

Lemma blcbPush : forall {A : Set} {maxbuf : nat} (a : A) (bl : BufferedList A maxbuf),
                  blCorrectB bl -> blCorrectB (pushBL a bl).
  intros A maxbuf a bl blc.
  destruct bl as [cbuf bb1 bb2 l].
  unfold pushBL.
  destruct (nat_compare cbuf maxbuf) eqn:nc.
  unfold blCorrectB.
  unfold blCorrectB in blc.
  destruct blc as [? [? [blc ?]]].

  assert (ll (EtoL bb1) = maxbuf).
  rewrite -> blc.
  apply nat_compare_eq.
  trivial.

  split. trivial.
  split. trivial.

  split.
  reflexivity.
  split.
  omega.
  omega.

  unfold blCorrectB.
  unfold blCorrectB in blc.
  destruct blc as [b1 [b2 [b3 [b4 b5]]]].

  assert (C : cbuf < maxbuf).
  apply nat_compare_lt.
  trivial.

  split. trivial.
  split. omega.

  split.
  rewrite -> EconsL.
  compute.
  compute in b3.
  auto.
  auto.

  unfold blCorrectB in blc.
  assert (cbuf > maxbuf).
  apply nat_compare_gt.
  trivial.
  omega.
Qed.

Function thawBL {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf) : list A :=
  match bl with
    | mkBufferedList cbuf bb1 bb2 l => l ((rev (EtoL bb2)) ++ (rev (EtoL bb1)))
  end.

Lemma thawBLpush : forall {A : Set} {maxbuf : nat}
                          (bl : BufferedList A maxbuf) (a : A),
                     blCorrectL bl ->
                     thawBL (pushBL a bl) = (thawBL bl) ++ [a].
Proof.
  intros A maxbuf bl a blc.
  destruct bl as [cbuf bb1 bb2 l].
  unfold pushBL.

  destruct (nat_compare cbuf maxbuf).
  unfold thawBL.
  rewrite -> blc.
  rewrite -> (blc (rev (EtoL bb2) ++ rev (EtoL bb1))).
  rewrite -> EconsL.
  rewrite -> cons_rev_1.
  repeat (rewrite -> app_assoc).
  rewrite -> app_nil_r.
  reflexivity.

  unfold thawBL.
  rewrite -> blc.
  rewrite -> (blc (rev (EtoL bb2) ++ rev (EtoL bb1))).
  rewrite -> EconsL.
  rewrite -> cons_rev_1.
  repeat (rewrite -> app_assoc).
  reflexivity.

  unfold thawBL.
  rewrite -> blc.
  rewrite -> (blc (rev (EtoL bb2) ++ rev (EtoL bb1))).
  rewrite -> EconsL.
  rewrite -> cons_rev_1.
  repeat (rewrite -> app_assoc).
  rewrite -> app_nil_r.
  reflexivity.
Qed.

Fixpoint unThawBL_ {A : Set} {m} l : BufferedList A (S m) :=
  match l with
    | [] => nilBL A m
    | x :: l_ => pushBL x (unThawBL_ l_)
  end.

Function unThawBL {A : Set} {m} l : BufferedList A (S m) := unThawBL_ (rev l).

Lemma thawUnThawCorrect : forall {A : Set} {m} l, blCorrectL (@unThawBL A m l).
Proof.
  intros A m.
  apply (rev_ind (fun l => blCorrectL (unThawBL l))).
  apply blclNil.
  intros x l IHl.
  unfold unThawBL.
  rewrite -> rev_app_distr.
  simpl.
  apply blclPush.
  exact IHl.
Qed.

Lemma thawUnThawBL : forall {A : Set} {m} l, l = thawBL (@unThawBL A m l).
Proof.
  intros A m.
  apply (rev_ind (fun l => l = thawBL (unThawBL l))).
  reflexivity.
  intros x l IHl.
  unfold unThawBL.
  rewrite -> rev_app_distr.
  simpl.
  rewrite -> thawBLpush.
  unfold unThawBL in IHl.
  rewrite <- IHl.
  reflexivity.
  apply thawUnThawCorrect.
Qed.

Function nL {A : Set} {maxbuf : nat} (d : nat) (bl : BufferedList A maxbuf) (default : A) : A :=
  match bl with
    | mkBufferedList cbuf bb1 bb2 l =>
      match nat_compare d cbuf with
        | Lt => Enth d bb1 default
        | _ => Enth (d - cbuf) bb2 default
      end
  end.

Lemma nLnth : forall {A : Set} {maxbuf : nat}
                     (d : nat) (bl : BufferedList A maxbuf) (default : A),
                blCorrectL bl -> blCorrectB bl ->
                d < maxbuf -> nL d bl default = nth d (rev (thawBL bl)) default.
Proof.
  intros A m d bl.
  elim bl.
  intros cbuf bb1 bb2 l default cl [mg1 [clm [lb1cb [lb2m lb2l]]]] dm.
  unfold blCorrectL in cl.
  unfold nL.

  destruct (nat_compare d cbuf) eqn:ncdc;
    (( assert (d < cbuf);
       [ apply nat_compare_lt;
         exact ncdc
       | unfold thawBL;
         rewrite -> cl;
         rewrite <- rev_app_distr;
         rewrite -> rev_app_distr;
         rewrite -> rev_involutive;
         rewrite -> app_nth1;
         [ rewrite -> app_nth1;
           [ apply Enth_nth
           | omega ]
         | rewrite -> app_length;
           omega ]])
       ||
       (unfold thawBL;
        rewrite -> cl;
        rewrite <- rev_app_distr;
        rewrite -> rev_app_distr;
        rewrite -> rev_involutive;
        destruct (lt_dec d (ll (EtoL bb1 ++ EtoL bb2))) as [l0 | l0];
        [ rewrite -> (app_nth1 _ _ _ l0);
          rewrite -> app_nth2;
          [ rewrite -> lb1cb; apply Enth_nth
          | rewrite -> lb1cb;
            solve [ assert (d > cbuf);
                    [ apply nat_compare_gt; trivial | omega]
                  | assert (d = cbuf);
                    [ apply nat_compare_eq; trivial | omega]]]
        | assert (lnil : l [] = []);
          [ apply lb2l;
            rewrite -> app_length in l0;
            omega
          | rewrite -> lnil;
            rewrite -> app_nil_r;
            rewrite -> Enth_nth;
            rewrite -> nth_overflow;
            [ rewrite -> nth_overflow;
              [ reflexivity | omega ]
            | rewrite -> app_length in l0;
              omega]]])).
Qed.
  

(* TODO: this belongs somewhere else *)
Lemma nthNthLast : forall {A : Set} (l : list A) (a b : A) (n : nat),
                     nth n (rev l) a = b -> n < ll l ->
                     nthLast (S n) l b.
Proof.
  intros A.
  apply (rev_ind (fun l => forall (a b : A) (n : nat),
   nth n (rev l) a = b -> n < ll l -> nthLast (S n) l b)).

  simpl. intros. omega.

  intros x l IHl.
  intros a b n nthn nll.
  rewrite -> rev_app_distr in nthn.
  destruct n as [|n].
  simpl in nthn.
  rewrite <- nthn.
  apply (makeNthLast l [] x).

  assert (Q : nthLast (S n) l b).
  eapply IHl.
  simpl in nthn.
  exact nthn.
  rewrite -> app_length in nll.
  simpl in nll.
  omega.
  inversion Q as [B C D E F G].
  assert (K1 : S (S (ll C)) = S (ll (C ++ [x]))).
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> K1.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  constructor.
Qed.

(* TODO: this belongs somewhere else *)
Lemma nthLastNth : forall {A : Set} (l : list A) (a b : A) (n : nat),
                     nthLast (S n) l b -> nth n (rev l) a = b.
Proof.
  intros A l a b n nlst.
  inversion nlst.
  rewrite -> rev_nth.
  rewrite -> app_length.
  simpl.
  assert (K0 : ll L + S (ll M) - S (ll M) = ll L).
  omega.
  rewrite -> K0.
  assert (K1 : b :: M = [b] ++ M).
  reflexivity.
  rewrite -> K1.
  rewrite -> app_assoc.
  rewrite -> app_nth1.
  assert (K2 : ll L = ll (L ++ [b]) - 1).
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> K2.
  rewrite <- rev_nth.
  rewrite -> rev_app_distr.
  reflexivity.
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> app_length.
  simpl.
  omega.
Qed.

Lemma nthLastNL : forall {A : Set} {maxbuf : nat} (b : BufferedList A maxbuf) n q r,
                    blCorrectL b -> blCorrectB b -> (n < maxbuf) ->
                    nthLast (S n) (thawBL b) r ->
                    nL n b q = r.
Proof.
  intros A m b n q r cL cB nm nl.
  assert (R : nth n (rev (thawBL b)) q = r).
  apply nthLastNth.
  exact nl.
  rewrite <- R.
  apply nLnth.
  trivial.
  trivial.
  trivial.
Qed.

Lemma nLnthLast : forall {A : Set} {maxbuf : nat} (b : BufferedList A maxbuf) n q r,
                    n < maxbuf -> n < ll (thawBL b) ->
                    blCorrectL b -> blCorrectB b ->
                    nL n b q = r ->
                    nthLast (S n) (thawBL b) r. 
Proof.
  intros A m b n q r nm nt cL cB nl.
  eapply nthNthLast.
  rewrite <- nLnth.
  exact nl.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

Fixpoint SingleBackRef
         {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf)
         (default : A) (len dist : nat) {struct len} :=
  match len with
    | 0 => bl
    | (S len') => SingleBackRef (pushBL (nL dist bl default) bl) default len' dist
  end.

Fixpoint SingleBackRefThawed
         {A : Set} (L : list A) (default : A) (len dist : nat) {struct len} :=
  match len with
    | 0 => L
    | (S len') => SingleBackRefThawed (L ++ [nth dist (rev L) default]) default len' dist
  end.

Lemma SingleBackRefThawedInsideOut :
  forall {A : Set} (L : list A) (default : A) (len dist : nat),
    SingleBackRefThawed L default (S len) dist =
    SingleBackRefThawed L default len dist ++
                        [nth dist (rev (SingleBackRefThawed L default len dist)) default].
Proof.
  intros A L dflt l.
  revert l L dflt.

  induction l;
    [ firstorder | ].

  intros L dflt dist.
  simpl.
  rewrite <- IHl.
  simpl.
  reflexivity.
Qed.

Lemma SingleBackRefThawedCorrect :
  forall {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf)
         (default : A) (len dist : nat),
    blCorrectL bl -> blCorrectB bl -> dist < maxbuf -> 
    SingleBackRefThawed (thawBL bl) default len dist =
    thawBL (SingleBackRef bl default len dist).
Proof.
  intros A m bl default l d.
  revert l d bl default.
  induction l as [|l IHl].

  reflexivity.

  intros.
  simpl.
  rewrite <- IHl.
  rewrite -> thawBLpush.
  rewrite -> nLnth.
  reflexivity.
  auto.
  auto.
  auto.
  auto.
  apply blclPush.
  auto.
  apply blcbPush.
  auto.
  auto.
Qed.

Lemma SingleBackRefCorrectL : forall {A} {m} l d (bl : BufferedList A m) dflt,
                                blCorrectL bl ->
                                blCorrectL (SingleBackRef bl dflt l d).
Proof.
  intros A m;
  induction l as [|l IHl];
  [ unfold SingleBackRef;
    trivial |].

  intros d bl dflt blc.
  simpl.
  apply IHl.
  apply blclPush.
  trivial.
Qed.

Lemma SingleBackRefCorrectB : forall {A} {m} l d (bl : BufferedList A m) dflt,
                                blCorrectB bl ->
                                blCorrectB (SingleBackRef bl dflt l d).
Proof.
  intros A m;
  induction l as [|l IHl];
  [ unfold SingleBackRef;
    trivial |].

  intros d bl dflt blc.
  simpl.
  apply IHl.
  apply blcbPush.
  trivial.
Qed.

Lemma SingleBackRefThawedMono :
  forall {A : Set} (L : list A) l d dflt, d < ll L ->  d < ll (SingleBackRefThawed L dflt l d).
Proof.
  intros A L l.
  revert l L.
  induction l as [| l IHl].

  firstorder.

  intros L d dlft dll.
  rewrite -> SingleBackRefThawedInsideOut.
  rewrite -> app_length.
  assert (d < ll (SingleBackRefThawed L dlft l d)).
  apply IHl.
  exact dll.
  omega.
Qed.

Lemma SingleBackRefCorrect' :
  forall {A : Set} l d (b : list A) dflt,
    d < ll b ->
    ResolveBackReference l (S d) b (SingleBackRefThawed b dflt l d).
Proof.
  intros A.
  induction l as [|l IHl];
    [ intros;
      constructor
    | ].

  intros.
  rewrite -> SingleBackRefThawedInsideOut.
  constructor.
  apply IHl.
  auto.
  auto.
  auto.
  auto.
  eapply nthNthLast.
  reflexivity.
  apply SingleBackRefThawedMono.
  trivial.
Qed.

Lemma SingleBackRefCorrect :
  forall {A} {m} l d (bl : BufferedList A m) dflt,
    blCorrectL bl -> blCorrectB bl ->
    d < ll (thawBL bl) ->
    d < m ->
    ResolveBackReference l (S d) (thawBL bl) (thawBL (SingleBackRef bl dflt l d)).
Proof.
  intros A m l d bl dflt blcl blcb dllt dm.
  rewrite <- SingleBackRefThawedCorrect.
  apply SingleBackRefCorrect'.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

Fixpoint BackRefs {A : Set} {m : nat}
         (swbr : SequenceWithBackRefs A)
         (bl : BufferedList A m)
         (q : A) {struct swbr} : BufferedList A m :=
  match swbr with
    | [] => bl
    | (inl c :: swbr') => BackRefs swbr' (pushBL c bl) q
    | (inr (l, d) :: swbr') => BackRefs swbr' (SingleBackRef bl q l (d - 1)) q
  end.

Fixpoint BackRefsThawed {A : Set}
         (swbr : SequenceWithBackRefs A)
         (bl : list A) (q : A) {struct swbr} : list A :=
  match swbr with
    | [] => bl
    | (inl c :: swbr') => BackRefsThawed swbr' (bl ++ [c]) q
    | (inr (l, d) :: swbr') =>
      BackRefsThawed swbr' (SingleBackRefThawed bl q l (d - 1)) q
  end.

Lemma BackRefsThawedCorrect :
  forall {A : Set} (minlen maxlen mindist maxdist : nat)
         (swbr : SequenceWithBackRefs A)
         (bl : BufferedList A maxdist) (q : A),
    BackRefsBounded minlen maxlen (S mindist) maxdist swbr ->
    blCorrectL bl ->
    blCorrectB bl ->
    thawBL (BackRefs swbr bl q) = BackRefsThawed swbr (thawBL bl) q.
Proof.
  intros A minlen maxlen mindist maxdist swbr.
  induction swbr as [| [a | [l d]] swbr IHswbr].

  firstorder.

  intros bl q brb blcl blcb.
  simpl.
  rewrite -> IHswbr.
  rewrite -> thawBLpush.
  reflexivity.
  trivial.
  inversion brb.
  trivial.
  apply blclPush.
  trivial.
  apply blcbPush.
  trivial.

  intros bl q brb blcl blcb.
  simpl.
  rewrite -> SingleBackRefThawedCorrect.
  rewrite -> IHswbr.
  reflexivity.
  inversion brb.
  trivial.
  apply SingleBackRefCorrectL.
  trivial.
  apply SingleBackRefCorrectB.
  trivial.
  trivial.
  trivial.

  compute in brb.

  inversion brb as [|? ? B].
  inversion B.
  omega.
Qed.

Lemma rbr_nil : forall {A} l d out, @ResolveBackReference A l d [] out -> out = [].
Proof.
  intro A;
  induction l as [|l IHl];
  [ intros ? ? rbr; inversion rbr; reflexivity
  | intros ? ? rbr;
    inversion rbr as [|B C D E F G H I J K L];
    assert (M : E = []);
    [ eapply IHl;
      exact G
    | rewrite -> M in H;
      inversion H as [N O P Q R S];
      destruct N; inversion R]].
Qed.

(* TODO: nach Backreferences.v *)
Lemma nthlast_ineq : forall {A} d inp x, @nthLast A d inp x -> ll inp >= d.
Proof.
  intros A d inp x nl.
  inversion nl.
  rewrite -> app_length.
  omega.
Qed.

(* TODO: nach Backreferences.v *)
Lemma rbr_ineq' : forall {A} l d inp out, @ResolveBackReference A l d inp out -> l = 0 \/ ll inp >= d.
Proof.
  intros A.
  induction l as [|l IHl].
  firstorder.

  intros d inp out rbr.
  apply or_intror.

  destruct l.
  inversion rbr.
  match goal with
    | Q : ResolveBackReference 0 _ _ _ |- _ => inversion Q
  end.
  eapply nthlast_ineq.
  eauto.

  inversion rbr.
  edestruct IHl.
  eauto.
  match goal with
    | Q : S _ = 0 |- _ => inversion Q
  end.
  trivial.
Qed.
  
Lemma rbr_ineq : forall {A} l d inp out, @ResolveBackReference A (S l) d inp out -> ll inp >= d.
Proof.
  intros A l d inp out rbr.
  destruct (rbr_ineq' (S l) d inp out rbr) as [Q | T].
  inversion Q.
  exact T.
Qed.

Inductive BackRefsOk {A : Set} : SequenceWithBackRefs A -> Prop :=
| BackRefsOkNil : BackRefsOk []
| BackRefsOkCons : forall c swbr, BackRefsOk swbr -> BackRefsOk (swbr ++ [inl c])
| BackRefsOkBr0 : forall d swbr, BackRefsOk swbr -> BackRefsOk (swbr ++ [inr (0, d)])
| BackRefsOkBr : forall l d swbr, BackRefsOk swbr -> 0 < d -> d <= brlen swbr -> BackRefsOk (swbr ++ [inr (S l, d)]).

Lemma BackRefsOkDec_ : forall {A : Set} (swbr1 swbr2 : SequenceWithBackRefs A),
                         BackRefsOk (swbr1 ++ swbr2) -> BackRefsOk swbr1.
Proof.
  intros A swbr1 swbr2.
  revert swbr2 swbr1.
  apply (rev_ind (fun swbr2 => forall swbr1, BackRefsOk (swbr1 ++ swbr2) -> BackRefsOk swbr1)).

  intro swbr1.
  rewrite -> app_nil_r.
  auto.

  intros a swbr2 IH2 swbr1 ok.
  rewrite -> app_assoc in ok.
  destruct a as [a | [a b]].
  apply IH2.
  inversion ok as [B | B C D E | B C D E | B C D E F G H].
  destruct (swbr1 ++ swbr2); inversion B.
  apply app_ll_r in E.
  destruct E as [E1 E2].
  rewrite <- E1.
  exact D.
  reflexivity.

  apply app_ll_r in E.
  destruct E as [E1 E2].
  inversion E2.
  reflexivity.

  apply app_ll_r in H.
  destruct H as [H1 H2].
  inversion H2.
  reflexivity.

  inversion ok as [B | B C D E | B C D E | B C D E F G H].
  destruct (swbr1 ++ swbr2); inversion B.
  apply app_ll_r in E.
  destruct E as [E1 E2].
  inversion E2.
  reflexivity.

  apply IH2.
  apply app_ll_r in E.
  destruct E as [E1 E2].
  rewrite <- E1.
  exact D.
  reflexivity.

  apply IH2.
  apply app_ll_r in H.
  destruct H as [H1 H2].
  rewrite <- H1.
  exact E.
  reflexivity.
Qed.

Lemma BackRefsOkDec : forall {A : Set} (swbr : SequenceWithBackRefs A),
                        BackRefsOk swbr + ~ BackRefsOk swbr.
Proof.
  intros A swbr.
  refine ((fix f todo done n
               (inv1 : n = brlen done)
               (inv2 : BackRefsOk done)
           : BackRefsOk (done ++ todo) + ~ BackRefsOk (done ++ todo)
           := _) swbr [] 0 _ _).
  destruct todo as [|t todo].
  rewrite -> app_nil_r.
  apply inl.
  exact inv2.

  replace (done ++ t :: todo) with (done ++ [t] ++ todo).
  rewrite -> app_assoc.
  destruct t as [t | [l d]].
  apply (f _ _ (S n)).
  rewrite -> app_brlen.
  simpl.
  omega.
  constructor.
  exact inv2.

  destruct l.
  apply (f _ _ n).
  rewrite -> app_brlen.
  simpl.
  omega.
  constructor.
  exact inv2.

  destruct (lt_dec 0 d) as [l0d | g0d].
  destruct (le_dec d n) as [ldn | gdn].
  apply (f _ _ (n + S l)).
  rewrite -> app_brlen.
  simpl.
  omega.
  constructor.
  exact inv2.
  exact l0d.
  omega.

  apply inr.
  intro Q.
  apply BackRefsOkDec_ in Q.
  inversion Q as [B | B C D E | B C D E | B C D E F G H].
  destruct done; inversion B.
  apply app_ll_r in E.
  destruct E as [E1 E2].
  inversion E2.
  reflexivity.
  apply app_ll_r in E.
  destruct E as [E1 E2].
  inversion E2.
  reflexivity.
  apply app_ll_r in H.
  destruct H as [H1 H2].
  inversion H2.
  rewrite -> H1 in G.
  omega.
  reflexivity.

  apply inr.
  intro Q.
  apply BackRefsOkDec_ in Q.
  inversion Q as [B | B C D E | B C D E | B C D E F G H].
  destruct done; inversion B.
  apply app_ll_r in E.
  destruct E as [E1 E2].
  inversion E2.
  reflexivity.
  apply app_ll_r in E.
  destruct E as [E1 E2].
  inversion E2.
  reflexivity.
  apply app_ll_r in H.
  destruct H as [H1 H2].
  inversion H2.
  omega.
  reflexivity.

  reflexivity.
  reflexivity.
  constructor.
Defined.

Lemma RBR_Ok : forall {A} swbr l, @ResolveBackReferences A swbr l -> BackRefsOk swbr.
Proof.
  intros A swbr l rbr;
  dependent induction rbr;
  [ constructor
  | constructor;
    auto
  | destruct len;
    [ constructor ; auto
    | constructor;
      [ auto
      | match goal with
          | Q : ResolveBackReference _ _ _ _ |- _ =>
            inversion Q;
              match goal with
                | R : nthLast _ _ _ |- _ =>
                  inversion R; simpl; omega
              end
        end
      |  match goal with
           | Q : ResolveBackReference (S _) _ _ _ |- _ => inversion Q
         end; erewrite <- rbrs_brlen; [ | eauto ];
         assert (ll b >= dist);
         [ eapply rbr_ineq;
           eauto
         | omega ]]]].
Qed.

Lemma BRsThawInsideOut : forall {A : Set} a (c : A) b q,
                           BackRefsThawed (a ++ [inl c]) b q = BackRefsThawed a b q ++ [c].
Proof.
  intros A.
  induction a as [| x a IHa].
  firstorder.

  intros c b q.
  destruct x as [xa | [xl xd]].

  simpl.
  rewrite -> IHa.
  reflexivity.

  simpl.
  rewrite -> IHa.
  reflexivity.
Qed.

Lemma BRsThawNullLen : forall {A : Set} a d b (q : A),
                         BackRefsThawed (a ++ [inr (0, d)]) b q = BackRefsThawed a b q.
Proof.
  intros A;
  induction a as [|[?|[? ?]] ? IHa]; (firstorder || (simpl; apply IHa)).
Qed.

Lemma BRsThawInsideOut2 : forall {A : Set}
                                 a x l (q : A),
                            BackRefsThawed (a ++ [x]) l q =
                            BackRefsThawed [x] (BackRefsThawed a l q) q.
Proof.
  intros A.
  induction a as [|[a' | [l' d']] a IHa];
    (firstorder ||
     intros x l q;
     simpl;
     rewrite -> IHa;
     simpl;
     reflexivity).
Qed.

Lemma BackRefsCorrect' :
  forall {A : Set} (Adec : forall x y : A, {x = y} + {x <> y})
         (minlen maxlen mindist maxdist : nat) swbr q (l : list A),
    BackRefsBounded (S minlen) maxlen mindist maxdist swbr ->
    (ResolveBackReferences swbr l <-> (BackRefsOk swbr /\
                                       (BackRefsThawed swbr [] q) = l)).
Proof.
  intros A Adec minlen maxlen mindist maxdist swbr q l brb.

  split;
  [ intro rbr;
    split;
    [ eapply RBR_Ok; eauto
    | revert swbr l brb rbr;
      apply (rev_ind (fun swbr => forall (l : list A),
                                    BackRefsBounded (S minlen) maxlen mindist maxdist swbr ->
                                    ResolveBackReferences swbr l -> BackRefsThawed swbr [] q = l));
        [ intros l brb rbr;
          simpl;
          inversion rbr;
          (reflexivity || match goal with
                            | Q : ?R ++ [_] = [] |- _ => destruct R; inversion Q
                          end)
        | intros x l IH bl brb rbr;
          inversion rbr;
          [ simpl; reflexivity
          | assert (K : a = l);
            [ eapply (app_ll_r a [_] l [_]);
              eauto
            | rewrite -> BRsThawInsideOut;
              rewrite -> K;
              erewrite -> IH;
              [ reflexivity
              | apply (forall_app l [x] _);
                auto
              | rewrite <- K;
                auto]]
          | assert (K : a = l);
            [ eapply (app_ll_r a [_] l [_]); eauto
            | rewrite -> BRsThawInsideOut2;
              simpl;
              rewrite -> K;
              rewrite -> (IH b);
              [ destruct len;
                [ simpl;
                  match goal with | H : _ |- _ => inversion H; solve [reflexivity] end
                | destruct dist;
                  [ match goal with
                      | H1 : _ |- _ => inversion H1;
                                      match goal with
                                        | H2 : _ |- _ => solve [inversion H2]
                                      end
                    end
                  | assert (ResolveBackReference (S len) (S dist) b (SingleBackRefThawed b q (S len) dist));
                    [ apply SingleBackRefCorrect';
                      assert (ll b >= S dist);
                      [ eapply rbr_ineq;
                        eauto
                      | omega ]
                    | eapply ResolveBackReferenceUnique;
                      [ replace (S dist - 1) with dist; [ eauto | omega]
                      | auto ]]]]
              | apply (forall_app _ _ _ brb)
              | rewrite <- K;
                auto]]]]] | ].

  (* Part 2: <- *)

  revert swbr q l brb.
  apply (rev_ind (fun swbr => forall (q : A) (l : list A),
                                BackRefsBounded (S minlen) maxlen mindist maxdist swbr ->
                                BackRefsOk swbr /\ BackRefsThawed swbr [] q = l ->
                                ResolveBackReferences swbr l));
  [ intros q l brb [bro brtl];
    simpl in brtl;
    rewrite <- brtl;
    constructor
  | ].

  intros x l IH q l0 brb [bro brtl].
  destruct x as [x | [x y]].
  rewrite -> BRsThawInsideOut in brtl.
  rewrite <- brtl.
  constructor.
  eapply IH.
  apply (forall_app _ _ _ brb).
  firstorder.

  inversion bro;
  match goal with
    | H : [] = ?A ++ [_] |- _ => destruct A; inversion H
    | A : BackRefsOk ?W, B : ?W ++ [?X] = l ++ [?Y] |- _ =>
      assert (K : W = l); [ apply (app_ll_r W [X] l [Y]); [auto | auto] | rewrite <- K; exact A]
    | B : ?W ++ [inr ?X] = l ++ [inl ?Y] |- _ =>
      assert (K1 : inr X = inl Y);
        [ assert (K2 : [inr X] = [inl Y]);
          [ eapply app_ll_r; [ eauto | auto ]
          | inversion K2 ]
        | inversion K1 ]
  end.

  inversion bro;
  match goal with
    | H : [] = ?A ++ [_] |- _ => destruct A; inversion H
    | A : BackRefsOk ?W, B : ?W ++ [?X] = l ++ [?Y] |- _ =>
      assert (K : W = l); [ apply (app_ll_r W [X] l [Y]); [auto | auto] | rewrite <- K; exact A]
    | B : ?W ++ [inr ?X] = l ++ [inl ?Y] |- _ =>
      assert (K1 : inr X = inl Y);
        [ assert (K2 : [inr X] = [inl Y]);
          [ eapply app_ll_r; [ eauto | auto ]
          | inversion K2 ]
        | inversion K1 ]
    | B : ?W ++ [inl ?X] = l ++ [inr ?Y] |- _ =>
      assert (K1 : inl X = inr Y);
        [ assert (K2 : [inl X] = [inr Y]);
          [ eapply app_ll_r; [ eauto | auto ]
          | inversion K2 ]
        | inversion K1 ]
    | _ => idtac
  end.

  match goal with
    | H : _ ++ [inr _] = _ ++ [inr _] |- _ => rewrite -> H
  end.
  econstructor.
  eapply IH.
  apply (forall_app _ _ _ brb).
  firstorder.
  inversion bro;
  match goal with
    | H : [] = ?A ++ [_] |- _ => destruct A; inversion H
    | A : BackRefsOk ?W, B : ?W ++ [?X] = l ++ [?Y] |- _ =>
      assert (K : W = l); [ apply (app_ll_r W [X] l [Y]); [auto | auto] | rewrite <- K; exact A]
    | B : ?W ++ [inr ?X] = l ++ [inl ?Y] |- _ =>
      assert (K1 : inr X = inl Y);
        [ assert (K2 : [inr X] = [inl Y]);
          [ eapply app_ll_r; [ eauto | auto ]
          | inversion K2 ]
        | inversion K1 ]
    | B : ?W ++ [inl ?X] = l ++ [inr ?Y] |- _ =>
      assert (K1 : inl X = inr Y);
        [ assert (K2 : [inl X] = [inr Y]);
          [ eapply app_ll_r; [ eauto | auto ]
          | inversion K2 ]
        | inversion K1 ]
  end.


  match goal with
    | H : _ ++ [inr (0, ?d)] = l ++ [inr (x, y)] |- _ =>
      assert (K : inr A (0, d) = inr A (x, y));
        [ assert (K' : [inr A (0, d)] = [inr A (x, y)]);
          [ eapply app_ll_r; [ eauto | auto ]
          | inversion K'; 
            reflexivity ]
        | inversion K as [[X0 YD]];
          rewrite <- X0 in brtl;
          rewrite -> BRsThawNullLen in brtl;
          rewrite <- brtl;
          constructor ]
  end.

  match goal with
    | H : _ ++ [inr (S ?l1, ?d)] = l ++ [inr (x, y)] |- _ =>
      assert (K : inr A (S l1, d) = inr A (x, y));
        [ assert (K' : [inr A (S l1, d)] = [inr A (x, y)]);
          [ eapply app_ll_r; [ eauto | auto ]
          | inversion K';
            reflexivity ]
        | inversion K as [[XK YK]];
          rewrite <- YK;
          rewrite -> H]
  end.

  eapply ResolveRef.
  eapply IH.
  apply (forall_app _ _ _ brb).
  firstorder.

  match goal with
    | H : ?swbr ++ [inr (S ?l1, ?d)] = l ++ [inr (x, y)] |- _ =>
      replace l with swbr; [ trivial | apply (app_ll_r _ _ _ _ H); auto]
  end.

  rewrite -> BRsThawInsideOut2 in brtl.
  rewrite <- brtl.
  simpl.

  destruct y; [omega | ].
  simpl.
  replace (y - 0) with y; [ | omega].
  apply SingleBackRefCorrect'.

  assert (R : ResolveBackReferences l (BackRefsThawed l [] q)).
  eapply IH.
  apply (forall_app _ _ _ brb).
  split.
  replace l with swbr; [trivial |
                        apply (app_ll_r _ _ _ _ H);
                          auto].


  reflexivity.
  assert (K2 : ll (BackRefsThawed l [] q) = brlen l).
  apply (rbrs_brlen).
  exact R.
  rewrite -> K2.
  replace l with swbr; [trivial |
                        apply (app_ll_r _ _ _ _ H);
                          auto].
  omega.
Qed.

Lemma BackRefsCorrect :
  forall {A : Set} (Adec : forall x y : A, {x = y} + {x <> y})
         (minlen maxlen mindist maxdist : nat) swbr q (bl : BufferedList A (S maxdist)),
    BackRefsBounded (S minlen) maxlen (S mindist) (S maxdist) swbr ->
    (ResolveBackReferences swbr (thawBL bl) <-> (BackRefsOk swbr /\
                                                thawBL (BackRefs swbr (nilBL A maxdist) q) = thawBL bl)).
Proof.
  intros A Adec minlen maxlen mindist maxdist swbr q bl brb.

  erewrite -> BackRefsThawedCorrect.
  eapply BackRefsCorrect'.
  eauto.
  eauto.
  eauto.
  apply blclNil.
  apply blcbNil.
Qed.

(* TODO: elsewhere *)
Lemma byte_eq_dec : forall (x y : Byte), {x = y} + {x <> y}.
Proof.
  intros x y.
  destruct (vec_eq_dec x y Bool.bool_dec); auto.
Defined.

Lemma DeflateStrongDec : StrongDec DeflateEncodes.
Proof.
  intro l.
  destruct (ManyBlocksStrongDec 0 l) as [[swbr [l' [l'' [lapp mb]]]] | [reason no]].
  destruct (BackRefsOkDec swbr) as [brok | brnok].
  apply inl.
  exists (thawBL (@BackRefs Byte (d"32768") swbr (nilBL _ _) (Bvector.Bvect_false _))).
  exists l'.
  exists l''.
  split.
  exact lapp.
  econstructor 1.
  exact mb.
  assert (brb : BackRefsBounded (S 2) 258 (S 0) (S (d"32767")) swbr).
  eapply ManyBlocksBounded.
  exact mb.
  apply (BackRefsCorrect byte_eq_dec _ _ _ _ swbr (Bvector.Bvect_false _) _ brb).
  split.
  exact brok.
  reflexivity.

  apply inr.
  split.
  exact "Backreference beyond the big bang."%string.
  intros [a [l'0 [l''0 [l'app denc]]]].
  inversion denc as [swbr' mb' rbr'].
  contradict brnok.
  eapply BackRefsCorrect.
  exact byte_eq_dec.
  exact (Bvector.Bvect_false _).
  eapply ManyBlocksBounded.
  exact mb.
  erewrite -> thawUnThawBL in rbr'.
  rewrite -> lapp in l'app.
  destruct (ManyBlocksStrongUnique 0 swbr swbr' l' l'' l'0 l''0 l'app mb mb') as [K1 K2].
  rewrite <- K1 in rbr'.
  exact rbr'.

  apply inr.
  split.
  exact reason.
  intros [a [l' [l'' [lapp de]]]].
  inversion de.
  contradict no.
  eexists.
  exists l'.
  exists l''.
  split.
  trivial.
  eauto.
Qed.

Definition EfficientDeflate (l : LB) : sum LByte string.
Proof.
  destruct (DeflateStrongDec l) as [[a ?] | [reason ?]].
  apply inl.
  exact a.
  apply inr.
  exact reason.
Defined.

Extraction Language Haskell.

(** Strings *)

Extract Inductive ascii => "Data.Char.Char" ["Extraction.makechar"] "Extraction.charrec".

Extract Inductive string => "[Data.Char.Char]" ["[]" "(:)"] "Extraction.stringrec".

(** Several simple types mapped to Haskell-standard-types *)

Extract Inductive prod => "(,)" ["(,)"] "Extraction.prodrec".
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".

Extract Inductive option => "Data.Maybe.Maybe" [ "Data.Maybe.Just" "Data.Maybe.Nothing" ].

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"] "Extraction.sumboolrec".

Extract Inductive sumor => "Data.Maybe.Maybe" [ "Data.Maybe.Just" "Data.Maybe.Nothing" ]
                                              "Extraction.sumorrec".

Extract Inductive comparison => "Extraction.Cmp" ["Extraction.Eq" "Extraction.Lt" "Extraction.Gt"]
                                                 "Extraction.cmprec".


(** Fin is just nat with an index that is not relevant *)
Extract Inductive fin => "Extraction.Fin" [ "Extraction.fin1" "Extraction.fins" ] "Extraction.finrec".

(** Constants for nat *)

Extract Inductive nat => "Prelude.Int" ["0" "Extraction.natinc"] "Extraction.natrec".

Extract Constant lt_eq_lt_dec => "Extraction.lt_eq_lt_dec".

Extract Constant le_lt_dec => "(Prelude.<=)".

Extract Constant nat_compare => "Extraction.nat_compare".

Extract Constant plus => "(Prelude.+)".

Extract Constant mult => "(Prelude.*)".

Extract Constant minus => "Extraction.natminus".

Extract Constant pow => "(Prelude.^)".

Extract Inductive list => "[]" [ "[]" "(\ a b -> a : b)" ]
                               "(\ n c l -> case l of { [] -> n [] ; (b : bs) -> c b bs })".

Extract Inductive vec => "Extraction.Vec" ["Extraction.vecNil" "Extraction.vecCons"] "Extraction.vecRec".

Extraction "EfficientDecompress/EfficientDecompress.hs" EfficientDeflate.
