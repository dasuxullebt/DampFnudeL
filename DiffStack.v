Require Import EncodingRelation.
Require Import EncodingRelationProperties.
Require Import Shorthand.
Require Import Backreferences.
Require Import Combi.
Require Import StrongDec.
Require Import Extraction.

Require Import Omega.
Require Import Ascii.
Require Import String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Program.
Require Import List.
Import ListNotations.

(* DS1A *)
Axiom DiffStack : Set -> Set.
(* DS1B *)

(* DS2A *)
Axiom DSNil : forall (A : Set), DiffStack A.
Arguments DSNil [_].
(* DS2B *)

(* DS3A *)
Axiom DSPush : forall (A : Set) (a : A) (ds : DiffStack A), DiffStack A.
Arguments DSPush [_].
(* DS3B *)

(* DSNTH1 *)
Axiom DSNth : forall (A : Set) (n : nat)
              (ds : DiffStack A) (default : A), A * DiffStack A.
Arguments DSNth [_].
(* DSNTH2 *)

(* FAKELINEAR1 *)
Axiom DSNthFakeLinear : forall {A : Set} n ds d,
    snd (@DSNth A n ds d) = ds.
(* FAKELINEAR2 *)

(* DSTOL1 *)								 
Axiom DStoL : forall (A : Set) (ds : DiffStack A), list A * DiffStack A.
Arguments DStoL [_].
(* DSTOL2 *)
									 
Axiom DStoLFakeLinear : forall {A : Set} ds, snd (@DStoL A ds) = ds.

Axiom DStoR : forall (A : Set) (ds : DiffStack A), list A * DiffStack A.
Arguments DStoR [_].

Axiom DStoRFakeLinear : forall {A : Set} ds, snd (@DStoR A ds) = ds.

Axiom DStoLR : forall (A : Set) (ds : DiffStack A),
    fst (DStoR ds) = (rev (fst (DStoL ds))).

Axiom ResetDS : forall (A : Set) (ds : DiffStack A), DiffStack A.
Arguments ResetDS [_].

Axiom ResetDSisNil : forall (A : Set) (ds : DiffStack A),
    DSNil = ResetDS ds.

(* LST1 *)
Axiom NilNil : forall (A : Set), DStoL (@DSNil A) = ([], DSNil).

Axiom PushLst : forall (A : Set) (a : A) b,
    fst (DStoL (DSPush a b)) = a :: fst (DStoL b).

Axiom DSNth_nth : forall {A : Set} (x : DiffStack A) (a : A) (n : nat),
    fst (DSNth n x a) = nth n (fst (DStoL x)) a.
(* LST2 *)
									 
Lemma depair : forall {A B : Set} (x : A * B),
    x = (fst x, snd x).
Proof.    
  intros.
  destruct x.
  reflexivity.
Qed.

Ltac dpr X :=
    replace X with (fst X, snd X);
    [| rewrite <- depair;
       reflexivity].

Inductive BufferedList (A : Set) (maxbuf : nat) : Set :=
| mkBufferedList : forall
                     (cbuf : nat)
                     (bb1 bb2 : DiffStack A)
                     (l : list A -> list A),
                     BufferedList A maxbuf.

Arguments mkBufferedList [_] [_] _ _ _ _.

Definition nilBL (A : Set) (maxbuf : nat) : BufferedList A (S maxbuf) :=
  @mkBufferedList A (S maxbuf) 0 DSNil DSNil (fun x => x).

Function pushBL {A : Set} {maxbuf : nat} (a : A) (bl : BufferedList A maxbuf) : BufferedList A maxbuf :=
  match bl with
    | mkBufferedList cbuf bb1 bb2 l =>
      match nat_compare cbuf maxbuf with
      | Lt =>
        let bb1_ := DSPush a bb1
        in @mkBufferedList A maxbuf (S cbuf) bb1_ bb2 l
      | _ =>
        let (to_r, bb2_1) := (DStoR bb2) in
        let bb2_2 := ResetDS bb2_1 in
        let bb2_3 := DSPush a bb2_2 in
        @mkBufferedList A maxbuf 1 (bb2_3) bb1
                              (fun x => l (to_r ++ x))
      end
  end.

Function thawBL {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf) :
  (list A * BufferedList A maxbuf) :=
  match bl with
  | @mkBufferedList _ _ cbuf bb1 bb2 l =>
    let (l1, bb1_) := DStoR bb1 in
    let (l2, bb2_) := DStoR bb2 in
    (l (l2 ++ l1), mkBufferedList cbuf bb1_ bb2_ l)
  end.

Fixpoint unThawBL_ {A : Set} {m} l : BufferedList A (S m) :=
  match l with
    | [] => nilBL A m
    | x :: l_ => pushBL x (unThawBL_ l_)
  end.

Function unThawBL {A : Set} {m} l : BufferedList A (S m) := unThawBL_ (rev l).

Function nL {A : Set} {maxbuf : nat} (d : nat) (bl : BufferedList A maxbuf) (default : A) :
  A * BufferedList A maxbuf :=
  match bl with
    | mkBufferedList cbuf bb1 bb2 l =>
      match nat_compare d cbuf with
      | Lt =>
        let (nt, bb1_) := DSNth d bb1 default in
        (nt, mkBufferedList cbuf bb1_ bb2 l)
      | _ =>
        let (nt, bb2_) := DSNth (d - cbuf) bb2 default in
        (nt, mkBufferedList cbuf bb1 bb2_ l)
      end
  end.

Lemma nLFakeLinear : forall {A : Set} maxbuf d (bl : BufferedList A maxbuf) (def : A),
    bl = snd (@nL A maxbuf d bl def).
Proof.
  intros.
  destruct bl.
  simpl.
  destruct (d ?= cbuf) eqn:dcbuf.  
  + dpr (DSNth (d - cbuf) bb2 def).
    simpl.
    rewrite -> DSNthFakeLinear.
    reflexivity.
  + dpr (DSNth d bb1 def).
    simpl.
    rewrite -> DSNthFakeLinear.
    reflexivity.
  + dpr (DSNth (d - cbuf) bb2 def).
    simpl.
    rewrite -> DSNthFakeLinear.
    reflexivity.
Qed.
    
Fixpoint SingleBackRef
         {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf)
         (default : A) (len dist : nat) {struct len} :=
  match len with
    | 0 => bl
    | (S len') =>
      let (nl, bl_) := nL dist bl default in
      SingleBackRef (pushBL nl bl_) default len' dist
  end.

Fixpoint SingleBackRefThawed
         {A : Set} (L : list A) (default : A) (len dist : nat) {struct len} :=
  match len with
    | 0 => L
    | (S len') => SingleBackRefThawed (L ++ [nth dist (rev L) default]) default len' dist
  end.

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

Definition blCorrectL {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf) :=
  match bl with
    | mkBufferedList _ _ _ l => forall l', l l' = (l []) ++ l'
  end.

Definition blCorrectB {A : Set} {maxbuf : nat} (bl : BufferedList A maxbuf) :=
  match bl with
    | mkBufferedList cbuf bb1 bb2 l =>
      1 <= maxbuf /\
      cbuf <= maxbuf /\
      ll (fst (DStoL bb1)) = cbuf /\
      ll (fst (DStoL bb2)) <= maxbuf /\
      (ll (fst (DStoL bb2)) < maxbuf -> l [] = [])
  end.

Lemma blclNil : forall {A : Set} {maxbuf : nat}, blCorrectL (nilBL A maxbuf).
Proof.
  intros A m.
  compute.
  auto.
Qed.

Lemma blcbNil : forall {A : Set} {maxbuf : nat}, blCorrectB (nilBL A maxbuf).
Proof.
  intros;
  compute; firstorder; rewrite -> NilNil; omega.
Qed.

Lemma blclPush : forall {A : Set} {maxbuf : nat} (a : A) (bl : BufferedList A maxbuf),
                  blCorrectL bl -> blCorrectL (pushBL a bl).
Proof.
  intros A maxbuf a bl blc.
  destruct bl as [cbuf bb1 bb2 l].
  unfold pushBL.
  destruct (nat_compare cbuf maxbuf).


  replace (DStoR bb2) with (fst (DStoR bb2), snd (DStoR bb2));
    [| rewrite <- depair;
       reflexivity].
  
  unfold blCorrectL.
  unfold blCorrectL in blc.

  intro l'.
  rewrite -> DStoLR.
  rewrite -> (blc (rev (_ (_ bb2)) ++ l')).
  rewrite -> (blc (rev (_ (_ bb2)) ++ [])).
  rewrite -> app_nil_r.
  rewrite -> app_assoc.
  reflexivity.

  unfold blCorrectL.
  unfold blCorrectL in blc.
  trivial.
  
  unfold blCorrectL.
  unfold blCorrectL in blc.

  replace (DStoR bb2) with (fst (DStoR bb2), snd (DStoR bb2));
    [| rewrite <- depair;
       reflexivity].
  
  intro l'.
  rewrite -> DStoLR.  
  rewrite -> (blc (rev (_ (_ bb2)) ++ l')).
  rewrite -> (blc (rev (_ (_ bb2)) ++ [])).
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

  assert (ll (fst (DStoL bb1)) = maxbuf).
  rewrite -> blc.
  apply nat_compare_eq.
  trivial.

  dpr (DStoR bb2).
  
  split. trivial.
  split. trivial.

  split.
  rewrite -> PushLst.
  rewrite <- ResetDSisNil.
  rewrite -> NilNil.
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
  rewrite -> PushLst.
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

Lemma thawBLpush : forall {A : Set} {maxbuf : nat}
                          (bl : BufferedList A maxbuf) (a : A),
                     blCorrectL bl ->
                     fst (thawBL (pushBL a bl))
                     = fst (thawBL bl) ++ [a].
Proof.
  intros A maxbuf bl a blc.
  destruct bl as [cbuf bb1 bb2 l].
  unfold pushBL.

  destruct (nat_compare cbuf maxbuf).
  unfold thawBL.

  dpr (DStoR bb2).
  dpr (DStoR bb1).
  dpr (DStoR (DSPush a (ResetDS bb2))).
  dpr (DStoR (DSPush a (ResetDS (snd (DStoR bb2))))).
  
  rewrite -> DStoLR.
  rewrite -> blc.
  rewrite -> (blc (rev (fst (DStoL bb2)) ++ (fst (DStoR bb1)))).
  rewrite -> DStoLR.
  rewrite -> DStoLR.
  rewrite -> PushLst.
  rewrite <- ResetDSisNil.
  rewrite -> NilNil.
  rewrite -> cons_rev_1.
  repeat (rewrite -> app_assoc).
  rewrite -> app_nil_r.
  reflexivity.

  unfold thawBL.

  dpr (DStoR bb2).
  dpr (DStoR bb1).
  dpr (DStoR (DSPush a bb1)).
  rewrite -> blc.
  rewrite -> DStoLR.
  rewrite -> DStoLR.
  rewrite -> DStoLR.
  rewrite -> (blc (rev (fst (DStoL bb2)) ++ rev (fst (DStoL bb1)))).
  rewrite -> PushLst.
  rewrite -> cons_rev_1.
  repeat (rewrite -> app_assoc).
  reflexivity.

  unfold thawBL.

  dpr (DStoR bb2).
  dpr (DStoR (DSPush a (ResetDS bb2))).
  dpr (DStoR bb1).
  dpr (DStoR (DSPush a (ResetDS (snd (DStoR bb2))))).
  rewrite -> DStoLR.
  rewrite -> blc.
  rewrite -> DStoLR.
  rewrite -> (blc (rev (fst (DStoL bb2)) ++ rev (fst (DStoL bb1)))).
  rewrite -> DStoLR.
  rewrite -> PushLst.
  rewrite <- ResetDSisNil.
  rewrite -> NilNil.
  rewrite -> cons_rev_1.
  repeat (rewrite -> app_assoc).
  rewrite -> app_nil_r.
  reflexivity.
Qed.

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

Lemma thawUnThawBL : forall {A : Set} {m} l, l = fst (thawBL (@unThawBL A m l)).
Proof.
  intros A m.
  apply (rev_ind (fun l => l = fst (thawBL (unThawBL l)))).
  simpl.
  dpr (DStoR (@DSNil A)).
  rewrite -> DStoLR.
  rewrite -> NilNil.
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

Lemma nLnth : forall {A : Set} {maxbuf : nat}
                     (d : nat) (bl : BufferedList A maxbuf) (default : A),
                blCorrectL bl -> blCorrectB bl ->
                d < maxbuf -> fst (nL d bl default) = nth d (rev (fst (thawBL bl))) default.
Proof.
  intros A m d bl.
  elim bl.
  intros cbuf bb1 bb2 l default cl [mg1 [clm [lb1cb [lb2m lb2l]]]] dm.
  unfold blCorrectL in cl.
  unfold nL.
  
  destruct (nat_compare d cbuf) eqn:ncdc.
  - dpr (DSNth (d - cbuf) bb2 default).
    unfold thawBL.
    dpr (DStoR bb1).
    dpr (DStoR bb2).
    rewrite -> cl.
    rewrite -> DStoLR.
    rewrite -> DStoLR.
    simpl.
    rewrite <- rev_app_distr.
    rewrite -> rev_app_distr.
    rewrite -> rev_involutive.
    destruct (lt_dec d (ll (fst (DStoL bb1) ++ fst (DStoL bb2)))) as [l0 | l0].
    + rewrite -> (app_nth1 _ _ _ l0).
      rewrite -> app_nth2.
      * rewrite -> lb1cb.
        apply DSNth_nth.
      * rewrite -> lb1cb.
        solve [ assert (d > cbuf);
                    [ apply nat_compare_gt; trivial | omega]
                  | assert (d = cbuf);
                    [ apply nat_compare_eq; trivial | omega]].
    + assert (lnil : l [] = []).
      * apply lb2l.
        rewrite -> app_length in l0.
        omega.
      * rewrite -> lnil.
        rewrite -> app_nil_r.
        rewrite -> DSNth_nth.
        rewrite -> nth_overflow.
        -- rewrite -> nth_overflow.
           ++ reflexivity.
           ++ omega.
        -- rewrite -> app_length in l0.
           omega.
  - assert (d < cbuf).
    + apply nat_compare_lt.
      exact ncdc.
    + unfold thawBL.
      dpr (DSNth d bb1 default).
      dpr (DStoR bb1).
      dpr (DStoR bb2).
      rewrite -> DStoLR.
      rewrite -> DStoLR.
      simpl.
      rewrite -> cl.
      rewrite <- rev_app_distr.
      rewrite -> rev_app_distr.
      rewrite -> rev_involutive.
      rewrite -> app_nth1.
      * rewrite -> app_nth1.
        apply DSNth_nth.
        omega.
      * rewrite -> app_length.
        omega.
  - dpr (DSNth (d - cbuf) bb2 default).
    unfold thawBL.
    dpr (DStoR bb1).
    dpr (DStoR bb2).
    rewrite -> DStoLR.
    rewrite -> DStoLR.
    rewrite -> cl.
    simpl.
    rewrite <- rev_app_distr.
    rewrite -> rev_app_distr.
    rewrite -> rev_involutive.
    destruct (lt_dec d (ll (fst (DStoL bb1) ++ fst (DStoL bb2)))) as [l0 | l0].
    + rewrite -> (app_nth1 _ _ _ l0).
      rewrite -> app_nth2.
      * rewrite -> lb1cb.
        apply DSNth_nth.
      * rewrite -> lb1cb.

        solve [ assert (d > cbuf);
                    [ apply nat_compare_gt; trivial | omega]
                  | assert (d = cbuf);
                    [ apply nat_compare_eq; trivial | omega]].
    + assert (lnil : l [] = []).
      * apply lb2l.
        rewrite -> app_length in l0.
        omega.
      * rewrite -> lnil.
        rewrite -> app_nil_r.
        rewrite -> DSNth_nth.
        rewrite -> nth_overflow.
        -- rewrite -> nth_overflow.
           ++ reflexivity.
           ++ omega.
        -- rewrite -> app_length in l0.
           omega.
Qed.

Lemma nthLastNL : forall {A : Set} {maxbuf : nat} (b : BufferedList A maxbuf) n q r,
                    blCorrectL b -> blCorrectB b -> (n < maxbuf) ->
                    nthLast (S n) (fst (thawBL b)) r ->
                    fst (nL n b q) = r.
Proof.
  intros A m b n q r cL cB nm nl.
  assert (R : nth n (rev (fst (thawBL b))) q = r).
  apply nthLastNth.
  exact nl.
  rewrite <- R.
  apply nLnth.
  trivial.
  trivial.
  trivial.
Qed.

Lemma nLnthLast : forall {A : Set} {maxbuf : nat} (b : BufferedList A maxbuf) n q r,
                    n < maxbuf -> n < ll (fst (thawBL b)) ->
                    blCorrectL b -> blCorrectB b ->
                    fst (nL n b q) = r ->
                    nthLast (S n) (fst (thawBL b)) r.
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
    SingleBackRefThawed (fst (thawBL bl)) default len dist =
    fst (thawBL (SingleBackRef bl default len dist)).
Proof.
  intros A m bl default l d.
  revert l d bl default.
  induction l as [|l IHl].

  reflexivity.

  intros.
  simpl.
  dpr (nL d bl default).
  rewrite <- IHl.
  rewrite -> thawBLpush.
  rewrite -> nLnth.
  rewrite <- nLFakeLinear.
  reflexivity.
  auto.
  auto.
  auto.
  rewrite <- nLFakeLinear.
  auto.
  rewrite <- nLFakeLinear.
  apply blclPush.
  auto.
  rewrite <- nLFakeLinear.
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
  dpr (nL d bl dflt).
  apply IHl.
  apply blclPush.
  rewrite <- nLFakeLinear.
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
  dpr (nL d bl dflt).
  apply IHl.
  apply blcbPush.
  rewrite <- nLFakeLinear.
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
    d < ll (fst (thawBL bl)) ->
    d < m ->
    ResolveBackReference l (S d) (fst (thawBL bl)) (fst (thawBL (SingleBackRef bl dflt l d))).
Proof.
  intros A m l d bl dflt blcl blcb dllt dm.
  rewrite <- SingleBackRefThawedCorrect.
  apply SingleBackRefCorrect'.
  trivial.
  trivial.
  trivial.
  trivial.
Qed.

Lemma BackRefsThawedCorrect :
  forall {A : Set} (minlen maxlen mindist maxdist : nat)
         (swbr : SequenceWithBackRefs A)
         (bl : BufferedList A maxdist) (q : A),
    BackRefsBounded minlen maxlen (S mindist) maxdist swbr ->
    blCorrectL bl ->
    blCorrectB bl ->
    fst (thawBL (BackRefs swbr bl q))
    = BackRefsThawed swbr (fst (thawBL bl)) q.
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
    (ResolveBackReferences swbr (fst (thawBL bl)) <-> (BackRefsOk swbr /\
                                               (fst (thawBL (BackRefs swbr (nilBL A maxdist) q))) = fst (thawBL bl))).
Proof.
  intros A Adec minlen maxlen mindist maxdist swbr q bl brb.

  erewrite -> BackRefsThawedCorrect.
  simpl.
  dpr (DStoR (@DSNil A)).
  rewrite -> DStoLR.
  rewrite -> NilNil.
  simpl.
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
  exists (fst (thawBL (@BackRefs Byte (d"32768") swbr (nilBL _ _) (Bvector.Bvect_false _)))).
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

Unset Extraction Optimize.
Unset Extraction AutoInline.

(* XC1 *)
Extract Constant DiffStack "q" => "DiffStackT.DiffStack q".
Extract Constant DSPush => "DiffStackT.push".
Extract Constant DSNth => "DiffStackT.nth".
Extract Constant DSNil => "DiffStackT.newDiffStack".
Extract Constant DStoL => "DiffStackT.toList".
Extract Constant DStoR => "DiffStackT.toReverseList".
Extract Constant ResetDS => "DiffStackT.reset".
(* XC2 *)

Extraction "DiffStack.hs" EfficientDeflate.
