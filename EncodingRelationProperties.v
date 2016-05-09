(** This file contains the naive implementation of a decompression
algorithm for deflate streams. It is extremely slow and memory
consuming, and was mainly made to test the specification against small
datasets. It is *not* meant for actual usage. *)

Require Import CpdtTactics.

Require Import Coq.Logic.Decidable.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.Numbers.NatInt.NZOrder.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.Div2.

Require Import Coq.NArith.BinNatDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.PArith.BinPos.
Require Import NArith.
Require Import Coq.QArith.QArith_base.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Program.

Require Import Shorthand.
Require Import DeflateCoding.
Require Import KraftVec.
Require Import KraftList.
Require Import Combi.
Require Import Transports.
Require Import Prefix.
Require Import LSB.
Require Import Repeat.
Require Import Backreferences.
Require Import StrongDec.
Require Import EncodingRelation.

Local Open Scope nat_scope.

Lemma nBitsEq : forall l m n, nBits n l m <-> (l = m /\ ll l = n).
Proof.
  intros l m n.
  revert l m.
  induction n.
  intros l m.
  split.
  intro nb.
  inversion nb.
  crush.
  intros [lm lb].
  destruct l.
  crush.
  constructor.
  reflexivity.
  reflexivity.
  inversion lb.

  intros l m.
  split.
  intro nb.
  split.
  inversion nb.
  match goal with
    | K : OneBit _ _ |- _ => inversion K
  end.
  simpl.
  f_equal.
  apply IHn.
  trivial.
  inversion nb.
  simpl.
  f_equal.
  apply (proj1 (IHn br ar)).
  trivial.

  intros [lm lb].
  destruct l.
  inversion lb.
  replace (b :: l) with ([b] ++ l) in lm ; [|reflexivity].
  rewrite <- lm.
  constructor.
  constructor.
  apply IHn.
  crush.
Qed.

Lemma OneByteEq : forall (b : Byte), OneByte (inl b) (to_list b).
Proof.
  intro b.
  apply AppCombineF.
  unfold nBitsVec.
  apply nBitsEq.
  split.  
  reflexivity.
  apply to_list_length.
Qed.

(* Old definition of nBytesDirect. *)
Inductive nBytesDirect_old : nat -> SequenceWithBackRefs Byte -> LB -> Prop :=
| nBytesDirect0 : nBytesDirect_old 0 nil nil
| nBytesDirectS : forall n a b bools thebyte,
                    nBytesDirect_old n a b -> bools = to_list thebyte ->
                    nBytesDirect_old (S n) ((inl thebyte) :: a) (bools ++ b).

(* Old definition of nBytesDirect is equivalent to new one. *)
Goal forall n swbr lb, nBytesDirect n swbr lb <-> nBytesDirect_old n swbr lb.
Proof.
  induction n as [|n IHn].
  + intros swbr lb.
    split.
    - intro nbd.
      inversion nbd.
      crush.
      constructor.
    - intro nbdo.
      inversion nbdo.
      constructor.
      reflexivity.
      reflexivity.
  + intros swbr lb.
    split.
    - intro nbd.
      unfold nBytesDirect in nbd.
      inversion nbd as [A B C D E F G H].
      inversion E as [I J K L M [N_ N] O P].
      constructor.
      apply IHn.
      apply F.
      unfold nBitsVec in M.
      rewrite -> (proj1 (proj1 (nBitsEq _ _ _) M)).
      rewrite -> N.
      rewrite -> app_nil_r.
      reflexivity.
    - intro nbdo.
      inversion nbdo.
      constructor.
      crush.
      apply AppCombineF.
      unfold nBitsVec.
      apply nBitsEq.
      crush.
      apply to_list_length.
      apply IHn.
      trivial.
Qed.

(* old definition of readBitsLSB *)
Inductive readBitsLSB_old (length : nat) : nat -> LB -> Prop :=
| mkRBLSB : forall l n, ll l = length -> LSBnat l n -> readBitsLSB_old length n l.

Goal forall length n lb, readBitsLSB length n lb <-> readBitsLSB_old length n lb.
Proof.
  intros length n lb.
  split.
  intro rbl.
  inversion rbl.
  constructor.
  match goal with
    | K : nTimesCons _ _ _ _, L : _ /\ _ = Bnil |- _ =>
      destruct L as [L_ L];
      apply nBitsEq in K;
        destruct K as [A B];
        rewrite <- A;
        rewrite -> L;
        rewrite -> app_nil_r;
        trivial
  end.
  match goal with
    | K : nTimesCons _ _ _ _, L : _ /\ _ = Bnil |- _ =>
      destruct L as [L_ L];
      apply nBitsEq in K;
        destruct K as [A B];
        rewrite <- A;
        rewrite -> L;
        rewrite -> app_nil_r;
        apply ListToNat_correct
  end.
  intro rblo.
  inversion rblo.
  replace n with (ListToNat lb).
  apply AppCombineF.
  apply nBitsEq.
  crush.
  eapply LSBnat_unique.
  apply ListToNat_correct.
  trivial.
Qed.

(** Plausibility check: *)
Goal nBytesDirect 3 [ inl (of_list [false; false; false; false; false; false; false; false]);
                      inl (of_list [false; false; false; false; false; false; false; true]);
                      inl (of_list [false; false; false; false; false; false; true; false]) ]
     [false; false; false; false; false; false; false; false;
      false; false; false; false; false; false; false; true;
      false; false; false; false; false; false; true; false].
Proof.
  replace [false; false; false; false; false; false; false; false;
           false; false; false; false; false; false; false; true;
           false; false; false; false; false; false; true; false]
  with ([false; false; false; false; false; false; false; false]
          ++ [false; false; false; false; false; false; false; true]
          ++ [false; false; false; false; false; false; true; false]
          ++ []); [|reflexivity].
  constructor.
  apply AppCombineF.
  apply nBitsEq.
  crush.
  constructor.
  apply AppCombineF.
  apply nBitsEq.
  crush.
  constructor.
  apply AppCombineF.
  apply nBitsEq.
  crush.
  constructor.
  reflexivity.
  reflexivity.
Qed.

(** Lemmata to convince us that the definition is correct *)

(** There can never be a back reference *)

Goal forall n L S x, nBytesDirect n S L -> ~ In (inr x) S.
Proof.
  induction n.
  intros L S x H.
  inversion H as [A B].
  rewrite -> A.
  auto.

  intros L S x H.
  inversion H as [A B C D E F G J].
  intros [QQ | QQQ].
  inversion E.
  crush.

  eapply IHn.
  exact F.
  exact QQQ.
Qed.

Theorem nBytesInputLength : forall n L S,
                              nBytesDirect n L S -> ll S = 8 * n.
Proof.
  induction n.
  intros L S H.
  inversion H.
  crush.

  intros L S nbd.
  inversion nbd as [A B C D E F G H].
  rewrite -> app_length.
  rewrite -> (IHn _ _ F).
  inversion E as [J K M N O [P_ P] Q R].
  rewrite -> app_length.
  rewrite -> P.
  apply nBitsEq in O.
  destruct O as [O T].
  rewrite <- O.
  rewrite -> to_list_length.
  simpl.
  omega.
Defined.

Lemma OneBitStrongUnique : StrongUnique OneBit.
Proof.
  intros a b la las lb lbs apps oa ob.
  destruct a.
  destruct b.
  inversion oa.
  inversion ob.
  auto.
  inversion oa as [Aa Ba Ca].
  inversion ob as [Ab Bb Cb].
  rewrite <- Ca in apps.
  rewrite <- Cb in apps.
  crush.

  destruct b.
  inversion oa as [Aa Ba Ca].
  inversion ob as [Ab Bb Cb].
  rewrite <- Ca in apps.
  rewrite <- Cb in apps.
  crush.
  inversion oa.
  inversion ob.
  auto.
Qed.

Lemma OneBitStrongDec : StrongDec OneBit.
Proof.
  intro l.
  destruct l.
  apply inr.
  split.
  exact "OneBit_ShortRead"%string.
  intros [a [l' [l'' [lapp oba]]]].
  destruct l'.
  inversion oba.
  crush.
  apply inl.
  exists b.
  exists [b].
  exists l.
  crush.
  constructor.
Defined.

Lemma nBitsStrongDecStrongUnique : forall n, StrongDec (nBits n) * StrongUnique (nBits n).
Proof.
  intro n. 
  apply nTimesStrongDecStrongUnique.
  exact "nBits"%string.
  apply OneBitStrongUnique.
  apply OneBitStrongDec.
Defined.

Lemma nBitsVecStongDecStrongUnique : forall n, StrongDec (nBitsVec n) * StrongUnique (nBitsVec n).
Proof.
  intro n.
  split.
  intro l.
  destruct (fst (nBitsStrongDecStrongUnique n) l) as [[a [l' [l'' [lapp nb]]]]|[reason no]].
  apply inl.
  rewrite <- (proj2 (proj1 (nBitsEq _ _ _) nb)).
  exists (of_list a).
  exists l'.
  exists l''.
  split.
  trivial.
  unfold nBitsVec.
  rewrite -> to_list_of_list_opp.
  rewrite -> (proj2 (proj1 (nBitsEq _ _ _) nb)).
  exact nb.

  apply inr.
  split.
  exact "nBitsVec"%string.
  intros [a [l' [l'' [lapp nbv]]]].
  apply no.
  unfold nBitsVec in nbv.
  exists (to_list a).
  exists l'.
  exists l''.
  auto.

  intros a b la las lb lbs apps nba nbb.
  destruct (snd (nBitsStrongDecStrongUnique n) (to_list a) (to_list b) la las lb lbs apps).
  trivial.
  trivial.
  split.
  apply to_list_inj.
  trivial.
  trivial.
Qed.

Lemma OneByteStrongDecStrongUnique : StrongDec OneByte * StrongUnique OneByte.
Proof.
  split.
  apply CombineStrongDecStrongUnique.
  apply nBitsVecStongDecStrongUnique.
  apply nBitsVecStongDecStrongUnique.
  intro q.
  split.
  apply nullStrongUnique.
  apply nullStrongDec.

  apply CombineStrongDecStrongUnique.
  apply nBitsVecStongDecStrongUnique.
  apply nBitsVecStongDecStrongUnique.
  intro q.
  split.
  apply nullStrongUnique.
  apply nullStrongDec.
Defined.

Theorem nBytesDirectStrongDecStrongUnique :
  forall n, StrongDec (nBytesDirect n) * StrongUnique (nBytesDirect n).
Proof.
  intros n.
  apply nTimesStrongDecStrongUnique.
  exact "nBytes"%string.
  apply OneByteStrongDecStrongUnique.
  apply OneByteStrongDecStrongUnique.
Defined.  

(* For compatibility *)
Theorem nBytesDirectStrongUnique : forall n, StrongUnique (nBytesDirect n).
Proof.
  apply nBytesDirectStrongDecStrongUnique.
Qed.

Lemma readBitsLSBStrongDecStrongUnique :
  forall length,  StrongDec (readBitsLSB length) * StrongUnique (readBitsLSB length).
Proof.
  intro length.
  split.
  apply CombineStrongDecStrongUnique.
  apply nTimesStrongDecStrongUnique.
  exact "readBitsLSB"%string.
  apply OneBitStrongUnique.
  apply OneBitStrongDec.
  apply nTimesStrongDecStrongUnique.
  exact "readBitsLSB"%string.
  apply OneBitStrongUnique.
  apply OneBitStrongDec.

  intro Q.
  split.
  apply nullStrongUnique.
  apply nullStrongDec.
  apply CombineStrongDecStrongUnique.
  apply nTimesStrongDecStrongUnique.
  exact "readBitsLSB"%string.
  apply OneBitStrongUnique.
  apply OneBitStrongDec.
  apply nTimesStrongDecStrongUnique.
  exact "readBitsLSB"%string.
  apply OneBitStrongUnique.
  apply OneBitStrongDec.

  intro Q.
  split.
  apply nullStrongUnique.
  apply nullStrongDec.
Defined.

(* For Backward Compatibility *)
Lemma readBitsLSBStrongUnique : forall length, StrongUnique (readBitsLSB length).
Proof.
  apply readBitsLSBStrongDecStrongUnique.
Defined.
Lemma readBitsLSBStrongDec : forall length, StrongDec (readBitsLSB length).
Proof.
  apply readBitsLSBStrongDecStrongUnique.
Defined.

Theorem nBytesDirectStrongDec : forall n, StrongDec (nBytesDirect n).
Proof.
  apply nBytesDirectStrongDecStrongUnique. 
Defined.

Theorem UncompressedBlockDirectStrongUniqueStrongDec : StrongUnique UncompressedBlockDirect * StrongDec UncompressedBlockDirect.
Proof.
  apply CombineStrongDecStrongUnique.
  apply readBitsLSBStrongUnique.
  apply readBitsLSBStrongDec.
  intro len.
  apply CombineStrongDecStrongUnique.
  apply readBitsLSBStrongUnique.
  apply readBitsLSBStrongDec.
  intro nlen.
  split.
  apply AndStrongUnique.
  apply nBytesDirectStrongUnique.
  apply AndStrongDec.
  destruct (eq_nat_dec (len + nlen) (2 ^ 16 - 1)) as [e|e].
  auto.
  apply inr.
  split.
  exact "In UncompressedBlockDirectStrongUniqueStrongDec: Header Checksum failed."%string.
  auto.
  apply nBytesDirectStrongDec.
Defined.

Lemma CLCHeaderRaw_inplen : forall (hclen : nat) (input : LB) (output : list nat),
                              CLCHeaderRaw hclen input output -> ll input = 3 * hclen.
Proof.
  induction hclen.
  intros input output clch.
  inversion clch.
  auto.

  intros input output clch.
  inversion clch.
  rewrite -> app_length.
  rewrite -> H1.
  rewrite -> (IHhclen i o).
  omega.
  trivial.
Defined.

Lemma CLCHeaderRawUnique : forall hclen input output1 output2, CLCHeaderRaw hclen input output1 -> CLCHeaderRaw hclen input output2 -> output1 = output2.
Proof.  
  induction hclen.
  intros input output1 output2 clch1 clch2.
  inversion clch1.
  inversion clch2.
  reflexivity.

  intros input output1 output2 clch1 clch2.
  inversion clch1 as [|hc1 inp1 outp1 n1 i1 o1 j1 m1 A1 B1 C1].
  inversion clch2 as [|hc2 inp2 outp2 n2 i2 o2 j2 m2 A2 B2 C2].

  destruct (app_ll i1 inp1 i2 inp2) as [ie inpe].
  rewrite -> B2.
  rewrite -> B1.
  reflexivity.
  rewrite -> j2.
  rewrite -> j1.
  reflexivity.

  assert (oo  : outp1 = outp2).
  apply (IHhclen inp1).
  trivial.
  rewrite -> inpe.
  trivial.
  rewrite -> oo.
  f_equal.
  apply (LSBnat_unique i1).
  trivial.
  rewrite -> ie.
  trivial.
Defined.

Theorem CLCHeaderRawParse : forall m l, {o : list nat & {l' : LB & {l'' | l = l' ++ l'' /\ CLCHeaderRaw m l' o}}}
                                        + (string * ({o : list nat & {l' : LB & {l'' | l = l' ++ l'' /\ CLCHeaderRaw m l' o}}} -> False)).
Proof.
  induction m.

  intro l.
  apply inl.
  exists (nil(A:=nat)).
  exists Bnil.
  exists l.
  split.
  auto.
  constructor.

  intro l.
  destruct (slice_list 3 l) as [[l1 [l2 [l1l2 lll1]]]|no].
  destruct (IHm l2) as [[o [l' [l'' [l2app clch]]]]|[reason IHmNo]].
  apply inl.
  exists ((ListToNat l1) :: o).
  exists (l1 ++ l').
  exists l''.
  split.
  rewrite <- app_assoc.
  rewrite <- l2app.
  auto.
  constructor.
  trivial.
  trivial.
  apply ListToNat_correct.

  apply inr.
  split.
  exact reason.
  intro Q.
  destruct Q as [o [l' [l'' [lapp clch]]]].
  inversion clch. (* TODO *)
  contradict IHmNo.
  exists o0.
  exists i.
  exists l''.
  split.
  apply (app_ll l1 l2 m0 (i ++ l'')).
  rewrite -> app_assoc.
  rewrite -> H3.
  rewrite <- lapp.
  auto.
  rewrite -> lll1.
  auto.
  trivial.

  apply inr.
  split.
  exact "In CLCHeaderRawParse: not enough bits."%string.
  intro Q.
  destruct Q as [o [l' [l'' [lapp clch]]]].
  inversion clch. (* TODO *)
  contradict no.
  exists m0.
  exists (i ++ l'').
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  auto.
  trivial.
Defined.

Lemma CLCHeaderPaddedUnique : forall hclen input output1 output2,
                               CLCHeaderPadded hclen input output1 ->
                               CLCHeaderPadded hclen input output2 ->
                               output1 = output2.
Proof.
  intros hclen input output1 output2 clchp1 clchp2.
  inversion clchp1 as [m1 o1 A1 B1 C1].
  inversion clchp2 as [m2 o2 A2 B2 C2].
  assert (oo : o1 = o2).
  apply (CLCHeaderRawUnique hclen input).
  trivial.
  trivial.
  rewrite -> oo in B1.  
  assert (mm : m1 = m2).
  assert (llo1 : 19 = ll o2 + m1).
  rewrite <- C1.
  rewrite <- (rep_length m1 0).
  rewrite <- app_length.
  rewrite <- B1.
  reflexivity.
  assert (llo2 : 19 = ll o2 + m2).
  rewrite <- C2.
  rewrite <- (rep_length m2 0).
  rewrite <- app_length.
  rewrite <- B2.
  reflexivity.
  omega.
  rewrite -> B1.
  rewrite -> B2.
  rewrite -> mm.
  reflexivity.
Defined.

Lemma CLCHeaderPaddedParse_1 : forall m i l, CLCHeaderRaw m i l -> ll l = m.
Proof.
  induction m.
  intros i l clch.
  inversion clch.
  reflexivity.
  intros i l clch.
  inversion clch.
  unfold ll.
  f_equal.
  unfold ll in IHm.
  rewrite -> (IHm i0). (* todo *)
  trivial.
  trivial.
Defined.

Theorem CLCHeaderPaddedParse : forall m l, {o : list nat & {l' : LB & {l'' | l = l' ++ l'' /\ CLCHeaderPadded m l' o}}}
                                           + (string * ({o : list nat & {l' : LB & {l'' | l = l' ++ l'' /\ CLCHeaderPadded m l' o}}} -> False)).
Proof.
  intros m l.

  destruct (nat_compare m 20) eqn:ncm.

  assert (M : m = 20).
  apply nat_compare_eq.
  trivial.

  rewrite -> M.

  apply inr.
  split.
  exact "In CLCHeaderPaddedParse: m = 20. THIS SHOULD BE IMPOSSIBLE!"%string.
  intro Q.
  destruct Q as [o [l' [l'' [lapp clchp]]]].
  inversion clchp. (* TODO *)

  assert (LL : ll output1 = 20).
  apply (CLCHeaderPaddedParse_1 _ l').
  trivial.
  rewrite -> H0 in H1.
  rewrite -> app_length in H1.
  omega.

  assert (M : m < 20).
  apply nat_compare_lt.
  trivial.

  destruct (CLCHeaderRawParse m l) as [[o[l'[l''[lapp clch]]]]|[reason no]].
  apply inl.
  exists (o ++ repeat (19 - m) 0).
  exists l'.
  exists l''.
  split.
  trivial.
  apply (makeCLCHeaderPadded m l' (o ++ repeat (19 - m) 0) (19 - m) o).
  trivial.
  trivial.
  rewrite -> app_length.
  rewrite -> rep_length.
  rewrite -> (CLCHeaderPaddedParse_1 m l').
  omega.
  trivial.
  trivial.

  apply inr.
  split.
  exact ("In CLCHeaderPaddedParse: " ++ reason)%string.
  intro Q.
  destruct Q as [o [l' [l'' [lapp clchp]]]].
  inversion clchp. (* TODO *)
  contradict no.
  exists output1.
  exists l'.
  exists l''.
  auto.

  (* TODO: this is similar to the m = 20 case *)
  assert (M : m > 20).
  apply nat_compare_gt.
  trivial.

  apply inr.
  split.
  exact "In CLCHeaderPaddedParse: m > 20. THIS SHOULD BE IMPOSSIBLE!"%string.
  intro Q.
  destruct Q as [o [l' [l'' [lapp clchp]]]].
  inversion clchp. (* TODO *)
  rewrite -> H0 in H1.
  rewrite -> app_length in H1.
  rewrite -> (CLCHeaderPaddedParse_1 m l') in H1.
  omega.
  trivial.
Defined.


Lemma list_nat_ineq_nth_error : forall (l1 l2 : list nat), l1 <> l2 -> {m | nth_error l1 m <> nth_error l2 m}.
Proof.
  induction l1 as [|l1a l1b].

  destruct l2.
  intro Q.
  contradict Q.
  reflexivity.

  intro neq.
  exists 0.
  intro Q.
  inversion Q.

  destruct l2 as [|l2a l2b].
  intro neq.
  exists 0.
  intro Q.
  inversion Q.

  intro neq.
  destruct (eq_nat_dec l1a l2a).
  assert (nneq : l1b <> l2b).
  intro Q.
  contradict neq.
  rewrite -> e.
  rewrite -> Q.
  reflexivity.

  destruct (IHl1b l2b nneq) as [m nnneq].
  exists (S m).
  compute.
  compute in nnneq.
  trivial.

  exists 0.
  compute.
  intro Q.
  contradict n.
  inversion Q.
  reflexivity.
Defined.

(* TODO: Rename this, it is also used in CLCHeaderPermutedUnique *)
Lemma CLCHeaderParse_1 : forall hclen input output, CLCHeaderPermuted hclen input output -> ll output = 19.
Proof.
  intros hclen input output clch.
  inversion clch.
  inversion H.

  do 19 (destruct output1; [inversion H3 | idtac]).
  destruct output1.

  set (H' := H0 2).

  do 19 (destruct output; [inversion H'|idtac]).

  destruct output.
  reflexivity.

  set (H'' := H0 19).
  compute in H''.
  inversion H''.

  inversion H3.
Defined.

Lemma ntherror_max : forall {A} (l : list A) (n : nat),
                       ll l <= n -> nth_error l n = error.
Proof.
  intro A.
  induction l. 

  destruct n.
  auto.
  auto.

  destruct n.
  intro Q.
  inversion Q.

  intro lll'.
  assert (lll : ll l <= n).
  compute in lll'.
  compute.
  omega.
  unfold nth_error.
  unfold nth_error in IHl.
  rewrite -> (IHl n lll).
  reflexivity.
Defined.

Lemma CLCHeaderPermutedUnique : forall hclen input output1 output2,
                                  CLCHeaderPermuted hclen input output1 ->
                                  CLCHeaderPermuted hclen input output2 ->
                                  output1 = output2.
Proof.
  intros hclen input output1 output2 clch1 clch2.
  inversion clch1 as [o1 A1 B1].
  inversion clch2 as [o2 A2 B2].
  assert (oo : o1 = o2).
  apply (CLCHeaderPaddedUnique hclen input).
  trivial.
  trivial.
  rewrite -> oo in B1.
  destruct (list_eq_dec eq_nat_dec output1 output2) as [y | n].
  trivial.
  assert (C : forall m, nth_error output1 (nth m HCLensNat 19) = nth_error output2 (nth m HCLensNat 19)).
  intro m.
  rewrite -> B1.
  rewrite -> B2.
  reflexivity.
  destruct (list_nat_ineq_nth_error output1 output2 n) as [m mn].
  assert (out1len : ll output1 = 19).
  apply (CLCHeaderParse_1 hclen input).
  trivial.
  assert (out2len : ll output2 = 19).
  apply (CLCHeaderParse_1 hclen input).
  trivial.

  (* TODO: shorter *)
  contradict mn.
  unfold HCLensNat in C.
  destruct m.
  apply (C 3).
  destruct m.
  apply (C 17).
  destruct m.
  apply (C 15).
  destruct m.
  apply (C 13).
  destruct m.
  apply (C 11).
  destruct m.
  apply (C 9).
  destruct m.
  apply (C 7).
  destruct m.
  apply (C 5).
  destruct m.
  apply (C 4).
  destruct m.
  apply (C 6).
  destruct m.
  apply (C 8).
  destruct m.
  apply (C 10).
  destruct m.
  apply (C 12).
  destruct m.
  apply (C 14).
  destruct m.
  apply (C 16).
  destruct m.
  apply (C 18).
  destruct m.
  apply (C 0).
  destruct m.
  apply (C 1).
  destruct m.
  apply (C 2).

  rewrite -> ntherror_max.
  rewrite -> ntherror_max.
  reflexivity.
  omega.
  omega.
Defined.

Theorem CLCHeaderPermutedParse_1 : forall (l' : list nat), (ll l' = 19) -> {l | ll l' = ll l /\ forall m, nth_error l (nth m HCLensNat 19) = nth_error l' m}.
Proof.
  intros l ll.

  exists (map (fun n => nth n l 19) [3; 17; 15; 13; 11; 9; 7; 5; 4; 6; 8; 10; 12; 14; 16; 18; 0; 1; 2]).

  do 19 (destruct l; [inversion ll|idtac]).
  destruct l.
  split.
  reflexivity.
  do 20 (destruct m; [reflexivity|idtac]).
  reflexivity.
  inversion ll.
Defined.

Theorem CLCHeaderPermutedParse : forall m l, {o : list nat & {l' : LB & {l'' | l = l' ++ l'' /\ CLCHeaderPermuted m l' o}}}
                                             + (string * ({o : list nat & {l' : LB & {l'' | l = l' ++ l'' /\ CLCHeaderPermuted m l' o}}} -> False)).
Proof.
  intros m l.
  destruct (CLCHeaderPaddedParse m l) as [[o[l'[l''[lapp clchp]]]]|[reason no]].
  apply inl.
  assert (olen : ll o = 19).
  inversion clchp.
  trivial.
  destruct (CLCHeaderPermutedParse_1 o olen) as [x [llxo all]].
  exists x.
  exists l'.
  exists l''.
  split.
  trivial.
  apply (makeCLCHeaderPermuted m l' x o).
  trivial.
  trivial.

  apply inr.
  split.
  exact ("In CLCHeaderPermutedParse: " ++ reason)%string.
  intro Q.
  destruct Q as [o [l' [l'' [lapp clchp]]]].
  inversion clchp.
  contradict no.
  exists output1.
  exists l'.
  exists l''.
  split.
  trivial.
  trivial.
Defined.


Theorem CLCHeaderStrongUnique : forall hclen, StrongUnique (CLCHeader hclen).
Proof.
  intros hclen output1 output2 input1 rest1 input2 rest2 H H0 H1.
  inversion H0.
  inversion H1.
  inversion H2.
  inversion H4.
  inversion H6.
  inversion H8.
  assert (ll input1 = ll input2).
  rewrite -> (CLCHeaderRaw_inplen hclen input2 output5).
  apply (CLCHeaderRaw_inplen _ _ output4).
  trivial.
  trivial.
  destruct (app_ll input1 rest1 input2 rest2) as [inps rests].
  trivial.
  trivial.
  assert (cooks : cooked = cooked0).
  apply (CLCHeaderPermutedUnique hclen input1).
  trivial.
  rewrite -> inps.
  trivial.
  split.
  rewrite <- cooks in H5.
  apply uniqueness.
  destruct H3.
  destruct H5.
  rewrite -> e.
  rewrite -> e0.
  assert (EQ : eq = eq0).
  apply proof_irrelevance.
  rewrite -> EQ.
  reflexivity.
  firstorder.
Defined.

Theorem CLCHeaderStrongDec : forall hclen, StrongDec (CLCHeader hclen).
Proof.
  intros m l.

  destruct (CLCHeaderPermutedParse m l) as [[o [l' [l'' [lapp clchp]]]]|[reason no]].
  assert (H : ll o = 19).
  inversion clchp.
  apply (CLCHeaderParse_1 m l').
  trivial.

  destruct (Qle_bool (kraft_nvec (of_list o)) 1%Q) eqn:kleb.
  assert (kle : ((kraft_nvec (of_list o)) <= 1)%Q).
  apply Qle_bool_iff.
  trivial.
  apply inl.
  destruct (existence (ll o) (of_list o) kle) as [x e].

  do 19 (dependent destruction o; [inversion H | idtac]).
  dependent destruction o.

  compute in x.
  exists x.
  exists l'.
  exists l''.
  split.
  trivial.

  (* TODO: GROSS!!! *)
  apply (makeCLCHeader m x _ [n; n0; n1; n2; n3; n4; n5; n6; n7; n8; n9; n10; n11; n12; n13; n14; n15; n16; n17]).
  trivial.
  apply (makeCodingOfSequence [n; n0; n1; n2; n3; n4; n5; n6; n7; n8; n9; n10; n11; n12; n13; n14; n15; n16; n17] x eq_refl).
  auto.

  inversion H.

  (* the cases remain where it does *not* work: *)

  (* Qle_bool (kraft_nvec (of_list o)) 1 = false -- but we know kraft's inequality must hold *)
  apply inr.

  split.
  exact ("In CLCHeaderStrongDec: CLC Header does not satisfy Kraft's Inequality. (" ++ blstring l)%string.
  intro Q.
  destruct Q as [o0 [l'0 [l''0 [lapp0 clch]]]].
  inversion clch as [cooked H0 H1].
  destruct (app_ll l' l'' l'0 l''0) as [lheads ltails].
  rewrite <- lapp.
  trivial.
  inversion clchp. (* TODO *)
  inversion H2.
  rewrite -> (CLCHeaderRaw_inplen m l' output0).
  inversion H0. inversion H7.
  rewrite -> (CLCHeaderRaw_inplen m l'0 output3).
  reflexivity.
  trivial.
  trivial.
  assert (coook : cooked = o).
  apply (CLCHeaderPermutedUnique m l').
  rewrite -> lheads.
  trivial.
  trivial.

  assert (contra : (kraft_nvec (of_list o) <= 1)%Q).
  assert (contra' : kraft_d o0 == kraft_nvec (of_list o)).
  inversion H1.

  destruct o0 as [Co0 pfo0 llo0 ceo0 deno0].
  unfold kraft_d.
  unfold C.
  unfold cd in H2.
  unfold C in H2.
  unfold kraft_vec.
  unfold kraft_nvec.
  rewrite -> H2.
  rewrite <- coook.
  rewrite -> vec_id_map.
  rewrite -> vec_id_fold.
  reflexivity.
  rewrite <- contra'.
  apply kraft_ineq.
  assert (Qle_bool (kraft_nvec (of_list o)) 1 = true).
  apply Qle_bool_iff.
  trivial.
  rewrite -> H2 in kleb.
  inversion kleb.

  (* No permuted header *)
  apply inr.
  split.
  exact ("In CLCHeaderStrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [o [l' [l'' [lapp clch]]]].
  inversion clch. (* TODO *)
  contradict no.
  exists cooked.
  exists l'.
  exists l''.
  auto.
Defined.

Theorem CompressedWithExtraBitsStrongUnique : forall {m} coding mincode xbitnums bases maxs,
                                              StrongUnique (CompressedWithExtraBits (m:=m) coding mincode xbitnums bases maxs).
Proof.
  intros m coding mincode xbitnums bases maxs a b la las lb lbs apps cweb1 cweb2.
  inversion cweb1 as [base extra code max xbitnum bbits xbits H H0 H1 H1_ H2 H3 H3_ H4 H5].  
  inversion cweb2 as [base0 extra0 code0 max0 xbitnum0 bbits0 xbits0 H6 H7 H8 H8_ H9 H10 H10_ H11 H12].
  assert (codes : code = code0).
  assert (mincode + code = mincode + code0).
  apply (dc_StrongUnique coding (mincode + code) (mincode + code0) bbits (xbits ++ las) bbits0 (xbits0 ++ lbs)).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> H12.
  rewrite -> H5.
  trivial.
  trivial.
  trivial.
  omega.
  rewrite <- codes in H7.
  rewrite -> H0 in H7.
  inversion H7.
  rewrite <- codes in H6.
  assert (bbitss : bbits = bbits0).
  destruct H as [X1 X2].
  destruct (vnth_is_correct _ _ _ X1) as [xa ea].
  destruct H6 as [Y1 Y2].
  destruct (vnth_is_correct _ _ _ Y1) as [ya da].
  assert (ON : (of_nat_lt xa) = (of_nat_lt ya)).
  apply of_nat_ext.
  rewrite <- ON in da.
  rewrite -> da in ea.
  auto.
  assert (lalb : bbits ++ xbits = bbits0 ++ xbits0).
  apply (app_ll _ las _ lbs).
  rewrite -> H12.
  rewrite -> H5.
  trivial.
  rewrite -> app_length.
  rewrite -> app_length.
  rewrite -> H9.
  rewrite -> H2.
  rewrite -> bbitss.
  rewrite -> H14.
  reflexivity.
  split.
  rewrite <- codes in H8.
  rewrite -> H1 in H8.
  inversion H8.
  assert(extra = extra0).
  assert (xbitss : xbits = xbits0).
  apply (app_ll bbits xbits bbits0 xbits0).
  trivial.
  rewrite -> bbitss.
  reflexivity.
  apply (LSBnat_unique xbits).
  trivial.
  rewrite -> xbitss.
  trivial.
  omega.
  trivial.
Defined.

Theorem CompressedWithExtraBitsStrongDec: forall {m} coding mincode xbitnums bases maxs,
                                            StrongDec (CompressedWithExtraBits (m:=m) coding mincode xbitnums bases maxs).
Proof.
  intros m coding mincode xbitnums bases maxs l.
  destruct (dc_StrongDec coding l) as [[a [l' [l'' [lapp dce]]]]|[reason no]].
  destruct (le_dec mincode a) as [mle | ale].
  assert (minc : mincode + (a - mincode) = a).
  omega.
  rewrite <- minc in dce.
  destruct (nth_error xbitnums (a - mincode)) as [xbitnum |] eqn:xbe.
  destruct (nth_error bases (a - mincode)) as [base |] eqn:bse.
  destruct (nth_error maxs (a - mincode)) as [max |] eqn:mxe.
  destruct (slice_list xbitnum l'') as [[l1 [l2 [l1app lbl1]]]|no].
  destruct (le_dec (base + ListToNat l1) max) as [le_max | gt_max].
  apply inl.
  exists (base + ListToNat l1).
  exists (l' ++ l1).
  exists l2.
  split.
  rewrite <- app_assoc.
  rewrite -> l1app.
  trivial.
  apply (complength _ _ _ _ _ _ _ (a - mincode) max xbitnum).
  trivial.
  trivial.
  trivial.
  trivial.
  trivial.
  apply ListToNat_correct.
  exact le_max.

  apply inr.
  split.
  exact "In CompressedWithExtraBitsStrongDec: Encoded point above maximum."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cweb]]]].
  inversion cweb as [A1 B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1 M1 N1 O1 P1].
  destruct (dc_StrongUnique coding (mincode + (a - mincode)) (mincode + C1) l' l'' F1 (G1 ++ l''0)) as [Q R];
    [ rewrite -> app_assoc;
      rewrite -> P1;
      rewrite <- l'app;
      auto
    | trivial
    | trivial
    | idtac ].

  destruct (app_ll_r G1 l''0 l1 l2) as [S T].
  apply app_inv_head with F1.
  rewrite -> app_assoc.
  rewrite -> P1.
  rewrite -> l1app.
  rewrite <- R.
  rewrite <- l'app.
  trivial.

  assert (N : (lb F1 + lb G1) + lb l''0 = (lb l' + lb l1) + lb l2).
  rewrite <- app_length.
  rewrite -> P1.
  rewrite <- app_length.
  rewrite <- l'app.
  rewrite <- plus_assoc.  
  rewrite <- app_length.
  rewrite -> l1app.
  rewrite <- app_length.
  f_equal.
  auto.
  assert (c1max : C1 = a - mincode).
  omega.
  rewrite -> c1max in I1.
  rewrite -> xbe in I1.
  inversion I1 as [E1xbe].
  rewrite -> R in N.
  abstract(omega).

  assert (B1 = ListToNat l1).
  eapply LSBnat_unique.
  apply M1.
  rewrite -> S.
  apply ListToNat_correct.
  assert (c1max : C1 = a - mincode).
  omega.
  rewrite -> c1max in J1.
  rewrite -> bse in J1.
  inversion J1.
  rewrite -> c1max in K1.
  rewrite -> mxe in K1.
  inversion K1.
  omega.

  apply inr.
  split.
  exact "In CompressedWithExtraBitsStrongDec: Not enough suffix bits."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cweb]]]].
  inversion cweb.
  contradict no.
  exists xbits.
  exists l''0.

  assert (ON' : code = a - mincode).
  destruct (eq_nat_dec (mincode + code) (mincode + (a - mincode))).
  omega.
  destruct (prefix_common bbits l' l).
  exists (xbits ++ l''0).
  rewrite -> app_assoc.
  rewrite -> H7.
  auto.
  exists l''.
  auto.
  contradict p.
  apply (prefix_free' coding (mincode + code) (mincode + (a - mincode))).
  trivial.
  trivial.
  trivial.
  contradict p.
  apply (prefix_free' coding (mincode + (a - mincode))  (mincode + code)).
  auto.
  trivial.
  trivial.
  assert (later : lb xbits = xbitnum).
  rewrite <- ON' in xbe.
  rewrite -> xbe in H0.
  inversion H0.
  trivial.
  split.
  assert (bbits = l').
  rewrite <- ON' in dce.
  destruct dce as [X1 X2].
  destruct H as [Y1 Y2].
  destruct (vnth_is_correct _ _ _ X1) as [xa ea].
  destruct (vnth_is_correct _ _ _ Y1) as [ya da].
  assert (ON : (of_nat_lt xa) = (of_nat_lt ya)).
  apply of_nat_ext.
  rewrite -> ON in ea.
  rewrite -> ea in da.
  auto.
  apply (app_ll bbits _ l' _).
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H7.
  auto.
  rewrite <- H8.
  reflexivity.
  exact later.

  apply inr.
  split.
  exact "In CompressedWithExtraBitsStrongDec: Max-array-index too large."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cweb]]]].
  inversion cweb as [A B C D E F G H I J K L M N O P].
  destruct (dc_StrongUnique coding (mincode + (a - mincode)) (mincode + C) l' l'' F (G ++ l''0)).
  rewrite -> app_assoc.
  rewrite -> P.
  rewrite <- lapp.
  auto.
  trivial.
  trivial.
  assert (aC : a - mincode = C).
  omega.
  rewrite <- aC in K.
  rewrite -> mxe in K.
  inversion K.  

  apply inr.
  split.
  exact "In CompressedWithExtraBitsStrongDec: Base-array-index too large."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cweb]]]].
  inversion cweb.
  destruct (eq_nat_dec (a - mincode) code) as [eeq|eneq].
  rewrite -> eeq in bse.
  rewrite -> bse in H1.
  inversion H1.
  destruct (prefix_common bbits l' l) as [p|p].
  exists (xbits ++ l''0).
  rewrite -> app_assoc.
  rewrite -> H7.
  auto.
  exists l''.
  auto.
  contradict p.
  apply (prefix_free' coding (mincode + code) (mincode + (a - mincode))).
  omega.
  trivial.
  trivial.
  contradict p.
  apply (prefix_free' coding (mincode + (a - mincode)) (mincode + code)).
  omega.
  trivial.
  trivial.

  apply inr.
  split.
  exact "In CompressedWithExtraBitsStrongDec: Bitnum-array-index too large."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cweb]]]].
  inversion cweb.
  destruct (eq_nat_dec code (a - mincode)) as [e|e].
  rewrite <- e in xbe.
  rewrite -> xbe in H0.
  inversion H0.
  destruct (prefix_common bbits l' l) as [p|p].
  exists (xbits ++ l''0).
  rewrite -> app_assoc.
  rewrite -> H7.
  auto.
  exists l''.
  auto.
  contradict p.
  apply (prefix_free' coding (mincode + code) (mincode + (a - mincode))).
  omega.
  trivial.
  trivial.
  contradict p.
  apply (prefix_free' coding (mincode + (a - mincode)) (mincode + code)).
  omega.
  trivial.
  trivial.

  (* ~ mincode <= a *)
  apply inr.
  split.
  exact "In CompressedWithExtraBitsStrongDec: Decoded character is smaller that minimal allowed character."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cweb]]]].
  inversion cweb.
  destruct (eq_nat_dec a (mincode + code)) as [e|e].
  omega.
  destruct (prefix_common bbits l' l) as [p|p].
  exists (xbits ++ l''0).
  rewrite -> app_assoc.
  rewrite -> H7.
  auto.
  exists l''.
  auto.
  contradict p.
  apply (prefix_free' coding (mincode + code) a).
  auto.
  trivial.
  trivial.
  contradict p.
  apply (prefix_free' coding a (mincode + code)).
  auto.
  trivial.
  trivial.

  (* {a : nat & {l' : LB & {l'' : LB | l = l' ++ l'' /\ dc_enc coding a l'}}} -> False *)
  apply inr.
  split.
  exact ("In CompressedWithExtraBitsStrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp cweb]]]].
  inversion cweb.
  contradict no.
  exists (mincode + code).
  exists bbits.
  exists (xbits ++ l'').
  split.
  rewrite -> app_assoc.
  rewrite -> H7.
  trivial.
  trivial.
Defined.

Lemma CommonCodeLengthsSWBRlen : forall clc n inp out,
                                   CommonCodeLengthsSWBR clc n out inp ->
                                   n = brlen out.
Proof.
  intros clc n inp out cswbr.
  induction cswbr.
  reflexivity.
  simpl.
  omega.
  simpl.
  omega.
  simpl.
  omega.
  simpl.
  omega.
Qed.

Lemma CommonCodeLengthsSWBRStrongDec : forall clc n, StrongDec (CommonCodeLengthsSWBR clc n).
Proof.
  intros clc n_ l_.
  refine ((fix f l n m (mge : n <= m) {struct m} :
             {a : SequenceWithBackRefs nat &
                                       {l' : LB &
                                                {l'' : LB | l = l' ++ l'' /\ CommonCodeLengthsSWBR clc n a l'}}} +
             string *
             ({a : SequenceWithBackRefs nat &
                                        {l' : LB &
                                                 {l'' : LB | l = l' ++ l'' /\ CommonCodeLengthsSWBR clc n a l'}}} ->
              False)
           := _) l_ n_ n_ (le_refl n_)).

  destruct n.
  apply inl.
  exists (nil (A:=(nat+nat*nat))).
  exists Bnil.
  exists l.
  split.
  reflexivity.
  constructor.
  destruct m.
  omega.

  destruct (CompressedWithExtraBitsStrongDec clc 16 [2] [3] [6] l) as [[a [l' [l'' [lapp cweb]]]]|[reason16 no16]].
  destruct (le_dec a (S n)) as [a_le_n|a_nle_n].
  assert (mge' : S n - a <= m).
  inversion cweb as [base extra code max xbitnum bbits xbits H H0 H1 H1_ H2 H3 H4 H4_ H5].
  destruct code.
  inversion H1.
  omega.
  destruct code.
  inversion H0.
  inversion H0.
  destruct (f l'' (S n - a) m mge') as [[a0 [l'0 [l''0 [l'app ccls]]]]|[reason no_f]].
  apply inl.
  exists (inr (a, 1) :: a0).
  exists (l' ++ l'0).
  exists l''0.
  split.
  rewrite <- app_assoc.
  rewrite <- l'app.
  trivial.
  replace (S n) with (S n - a + a).
  apply cswbr16.
  trivial.
  trivial.
  omega.

  apply inr.
  split.
  exact reason.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app ccls]]]].
  destruct ccls.
  contradict no_f.
  exists (nil (A:=nat+nat*nat)).
  exists Bnil.
  exists l''.
  split.
  reflexivity.
  constructor.

  destruct cweb.
  destruct (dc_StrongUnique clc (16 + code) m0 bbits (xbits ++ l'') input (lb1 ++ l''0)).
  rewrite -> app_assoc.
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  trivial.
  trivial.
  omega.

  contradict no_f.
  destruct (CompressedWithExtraBitsStrongUnique clc 16 [2] [3] [6] a m0 l' l'' input (lb1 ++ l''0)) as [eq1 eq2].
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  trivial.
  trivial.
  exists brs.
  exists lb1.
  exists l''0.
  split.
  apply (app_ll l' _ input _).
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  f_equal.
  trivial.
  replace (n0 + m0 - a) with n0.
  trivial.
  omega.

  destruct cweb as [base extra code max xbitnum bbits xbits H2 H2_ H3 H4 H5 H5_].
  destruct H as [base0 extra0 code0 max0 xbitnum0 bbits0 xbits0 H7_ H8 H10 H10_].
  destruct (dc_StrongUnique clc (16 + code) (17 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  
  destruct code.
  omega.
  destruct code.
  inversion H3.
  inversion H3.

  destruct cweb.
  destruct H.
  destruct (dc_StrongUnique clc (16 + code) (18 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H3.
  inversion H3.

  apply inr.
  split.
  exact ("In CommonCodeLengthsSWBRStrongDec: Code 16 would produce more codes than hlit+hdist allow. (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app ccls]]]].
  inversion ccls.
  destruct cweb.
  destruct (dc_StrongUnique clc (16 + code) m0 bbits (xbits ++ l'') input (lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite -> H4.
  rewrite <- l'app.
  auto.
  trivial.
  trivial.
  omega.

  destruct (CompressedWithExtraBitsStrongUnique clc 16 [2] [3] [6] a m0 l' l'' input (lb1 ++ l''0)) as [eq1 eq2].
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  omega.

  destruct cweb.
  destruct H1.
  destruct (dc_StrongUnique clc (16 + code) (17 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)).
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H5.
  inversion H5.

  destruct cweb.
  destruct H1.
  destruct (dc_StrongUnique clc (16 + code) (18 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)).
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H5.
  inversion H5.

  destruct (CompressedWithExtraBitsStrongDec clc 17 [3] [3-1] [10-1] l) as [[a [l' [l'' [lapp cweb]]]]|[reason17 no17]].
  destruct (le_dec (S a) (S n)) as [a_le_n|a_nle_n].
  assert (mge' : S n - S a <= m).
  inversion cweb.
  destruct code.
  inversion H1.
  omega.
  destruct code.
  inversion H0.
  inversion H0.
  destruct (f l'' (S n - S a) m mge') as [[a0 [l'0 [l''0 [l'app ccls]]]]|[reason no_f]].
  apply inl.
  exists (inl 0 :: inr (a, 1) :: a0).
  exists (l' ++ l'0).
  exists l''0.
  split.
  rewrite <- app_assoc.
  rewrite <- l'app.
  trivial.
  replace (S n) with (S n - S a + a + 1).
  apply cswbr17.
  trivial.
  trivial.
  omega.

  apply inr.
  split.
  exact reason.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app ccls]]]].
  destruct ccls.
  contradict no_f.
  exists (nil (A:=nat+nat*nat)).
  exists Bnil.
  exists l''.
  split.
  reflexivity.
  constructor.

  destruct cweb.
  destruct (dc_StrongUnique clc (17 + code) m0 bbits (xbits ++ l'') input (lb1 ++ l''0)).
  rewrite -> app_assoc.
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  trivial.
  trivial.
  omega.

  destruct cweb.
  destruct H.
  destruct (dc_StrongUnique clc (17 + code) (16 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H7.
  inversion H7.

  contradict no_f.
  destruct (CompressedWithExtraBitsStrongUnique clc 17 [3] [3-1] [10-1] a m0 l' l'' input (lb1 ++ l''0)) as [eq1 eq2].
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  trivial.
  trivial.
  exists brs.
  exists lb1.
  exists l''0.
  split.
  apply (app_ll l' _ input _).
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  f_equal.
  trivial.
  replace (n0 + m0 + 1 - S a) with n0.
  trivial.
  omega.

  destruct cweb.
  destruct H.
  destruct (dc_StrongUnique clc (17 + code) (18 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H1.
  inversion H1.

  apply inr.
  split.
  exact ("In CommonCodeLengthsSWBRStrongDec: Code 17 would produce more codes than hlit+hdist allow. (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app ccls]]]].
  inversion ccls.
  destruct cweb.
  destruct (dc_StrongUnique clc (17 + code) m0 bbits (xbits ++ l'') input (lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite -> H4.
  rewrite <- l'app.
  auto.
  trivial.
  trivial.
  omega.

  destruct cweb.
  destruct H1.
  destruct (dc_StrongUnique clc (17 + code) (16 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)).
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H11.
  inversion H11.

  destruct (CompressedWithExtraBitsStrongUnique clc 17 [3] [3-1] [10-1] a m0 l' l'' input (lb1 ++ l''0)) as [eq1 eq2].
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  omega.

  destruct cweb.
  destruct H1.
  destruct (dc_StrongUnique clc (17 + code) (18 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)).
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H5.
  inversion H5.

  destruct (CompressedWithExtraBitsStrongDec clc 18 [7] [11-1] [138-1] l) as [[a [l' [l'' [lapp cweb]]]]|[reason18 no18]].
  destruct (le_dec (S a) (S n)) as [a_le_n|a_nle_n].
  assert (mge' : S n - S a <= m).
  inversion cweb.
  destruct code.
  inversion H1.
  omega.
  destruct code.
  inversion H0.
  inversion H0.
  destruct (f l'' (S n - S a) m mge') as [[a0 [l'0 [l''0 [l'app ccls]]]]|[reason no_f]].
  apply inl.
  exists (inl 0 :: inr (a, 1) :: a0).
  exists (l' ++ l'0).
  exists l''0.
  split.
  rewrite <- app_assoc.
  rewrite <- l'app.
  trivial.
  replace (S n) with (S n - S a + a + 1).
  apply cswbr18.
  trivial.
  trivial.
  omega.

  apply inr.
  split.
  exact reason.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app ccls]]]].
  destruct ccls.
  contradict no_f.
  exists (nil (A:=nat+nat*nat)).
  exists Bnil.
  exists l''.
  split.
  reflexivity.
  constructor.

  destruct cweb.
  destruct (dc_StrongUnique clc (18 + code) m0 bbits (xbits ++ l'') input (lb1 ++ l''0)).
  rewrite -> app_assoc.
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  trivial.
  trivial.
  omega.

  destruct cweb.
  destruct H.
  destruct (dc_StrongUnique clc (18 + code) (16 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H7.
  inversion H7.

  destruct cweb.
  destruct H.
  destruct (dc_StrongUnique clc (18 + code) (17 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H7.
  inversion H7.

  contradict no_f.
  destruct (CompressedWithExtraBitsStrongUnique clc 18 [7] [11-1] [138-1] a m0 l' l'' input (lb1 ++ l''0)) as [eq1 eq2].
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  trivial.
  trivial.
  exists brs.
  exists lb1.
  exists l''0.
  split.
  apply (app_ll l' _ input _).
  rewrite <- lapp.
  rewrite -> app_assoc.
  trivial.
  f_equal.
  trivial.
  replace (n0 + m0 + 1 - S a) with n0.
  trivial.
  omega.

  apply inr.
  split.
  exact ("In CommonCodeLengthsSWBRStrongDec: Code 18 would produce more codes than hlit+hdist allow. (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app ccls]]]].
  inversion ccls.
  destruct cweb.
  destruct (dc_StrongUnique clc (18 + code) m0 bbits (xbits ++ l'') input (lb1 ++ l''0)) as [eq1 eq2].
  repeat rewrite -> app_assoc.
  rewrite -> H4.
  rewrite <- l'app.
  auto.
  trivial.
  trivial.
  omega.

  destruct cweb.
  destruct H1.
  destruct (dc_StrongUnique clc (18 + code) (16 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)).
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H11.
  inversion H11.

  destruct cweb.
  destruct H1.
  destruct (dc_StrongUnique clc (18 + code) (17 + code0) bbits (xbits ++ l'') bbits0 (xbits0 ++ lb1 ++ l''0)).
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H11.
  inversion H11.

  destruct (CompressedWithExtraBitsStrongUnique clc 18 [7] [11-1] [138-1] a m0 l' l'' input (lb1 ++ l''0)) as [eq1 eq2].
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  omega.

  destruct (dc_StrongDec clc l) as [[a [l' [l'' [lapp dce]]]]|[reason no]].
  destruct (eq_nat_dec a 16) as [a_is_16|a_isnt_16].
  destruct (slice_list 2 l'') as [[l1 [l2 [l1app l1ll]]]|no].
  contradict no16.
  exists (3 + ListToNat l1).
  exists (l' ++ l1).
  exists l2.
  split.
  rewrite <- app_assoc.
  rewrite -> l1app.
  trivial.
  eapply (complength _ _ _ _ _ 3 (ListToNat l1) 0 6 2 l' l1).
  rewrite -> a_is_16 in dce.
  auto.
  reflexivity.
  reflexivity.
  trivial.
  trivial.
  apply ListToNat_correct.
  assert (ListToNat l1 < 4).
  replace 4 with (2 ^ lb l1).
  eapply lsb_power.
  apply ListToNat_correct.
  rewrite -> l1ll.
  reflexivity.
  omega.
  
  apply inr.
  split.
  exact ("dc_enc fail in CommonCodeLengthsSWBRStrongDec[16]: THIS SHOULD NEVER HAPPEN! (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cls]]]].
  inversion cls.
  destruct (dc_StrongUnique clc a m0 l' l'' input (lb1 ++ l''0)).
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  rewrite -> app_assoc.
  rewrite -> H4.
  trivial.
  trivial.
  trivial.
  omega.
  contradict no16.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  contradict no17.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  contradict no18.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.

  destruct (eq_nat_dec a 17) as [a_is_17|a_isnt_17].
  destruct (slice_list 3 l'') as [[l1 [l2 [l1app l1ll]]]|no].
  contradict no17.
  exists (3 - 1 + ListToNat l1).
  exists (l' ++ l1).
  exists l2.
  split.
  rewrite <- app_assoc.
  rewrite -> l1app.
  trivial.
  apply (complength _ _ _ _ _ (3 - 1) (ListToNat l1) 0 (10 - 1) 3 l' l1).
  rewrite -> a_is_17 in dce.
  auto.
  reflexivity.
  reflexivity.
  reflexivity.
  trivial.
  apply ListToNat_correct.
  assert (ListToNat l1 < 8).
  replace 8 with (2 ^ (lb l1)).
  apply lsb_power.
  apply ListToNat_correct.
  rewrite -> l1ll.
  reflexivity.
  omega.

  apply inr.
  split.
  exact ("dc_enc fail in CommonCodeLengthsSWBRStrongDec[17]: THIS SHOULD NEVER HAPPEN! (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cls]]]].
  inversion cls.
  destruct (dc_StrongUnique clc a m0 l' l'' input (lb1 ++ l''0)).
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  rewrite -> app_assoc.
  rewrite -> H4.
  trivial.
  trivial.
  trivial.
  omega.
  contradict no16.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  contradict no17.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  contradict no18.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.

  destruct (eq_nat_dec a 18) as [a_is_18|a_isnt_18].
  destruct (slice_list 7 l'') as [[l1 [l2 [l1app l1ll]]]|no].
  contradict no18.
  exists (11 - 1 + ListToNat l1).
  exists (l' ++ l1).
  exists l2.
  split.
  rewrite <- app_assoc.
  rewrite -> l1app.
  trivial.
  apply (complength _ _ _ _ _ (11 - 1) (ListToNat l1) 0 (138 - 1) 7 l' l1).
  rewrite -> a_is_18 in dce.
  auto.
  reflexivity.
  reflexivity.
  reflexivity.
  trivial.
  apply ListToNat_correct.
  assert (ListToNat l1 < 128).
  replace 128 with (2 ^ lb l1).
  apply lsb_power.
  apply ListToNat_correct.
  rewrite -> l1ll.
  reflexivity.
  omega.

  apply inr.
  split.
  exact ("dc_enc fail in CommonCodeLengthsSWBRStrongDec[18]: THIS SHOULD NEVER HAPPEN! (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cls]]]].
  inversion cls.
  destruct (dc_StrongUnique clc a m0 l' l'' input (lb1 ++ l''0)).
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  rewrite -> app_assoc.
  rewrite -> H4.
  trivial.
  trivial.
  trivial.
  omega.
  contradict no16.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  contradict no17.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  contradict no18.
  exists m0.
  exists input.
  exists (lb1 ++ l''0).
  split.
  rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.

  assert (a < 19).
  apply (dc_max clc a l').
  trivial.

  (* ok. now we need to show a < 16 *)
  assert (a_lt_16 : a < 16).
  omega.
  destruct (f l'' n m) as [[a0 [l'0 [l''0 [l'app clsw]]]]|[reason no_f]].
  omega.
  apply inl.
  exists (inl a :: a0).
  exists (l' ++ l'0).
  exists l''0.
  split.
  rewrite <- app_assoc.
  rewrite <- l'app.
  trivial.
  replace (S n) with (n + 1).
  constructor.
  trivial.
  trivial.
  trivial.
  omega.

  apply inr.
  split.
  apply reason.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cswbr]]]].
  inversion cswbr.
  contradict no_f.
  exists brs.
  exists lb1.
  exists l''0.
  split.
  apply (app_ll l' _ input _).
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H5.
  trivial.
  destruct (dc_StrongUnique clc a m0 l' l'' input (lb1 ++ l''0)).
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H5.
  trivial.
  trivial.
  trivial.
  f_equal.
  trivial.
  replace n with n0.
  trivial.
  omega.
  destruct H2.
  destruct (dc_StrongUnique clc a (16 + code) l' l'' bbits (xbits ++ lb1 ++ l''0)).
  rewrite <- lapp.
  repeat rewrite -> app_assoc.
  rewrite -> H4.
  trivial.
  trivial.
  trivial.
  omega.
  destruct H2.
  destruct (dc_StrongUnique clc a (17 + code) l' l'' bbits (xbits ++ lb1 ++ l''0)).
  rewrite <- lapp.
  repeat rewrite -> app_assoc.
  rewrite -> H4.
  trivial.
  trivial.
  trivial.
  omega.
  destruct H2.
  destruct (dc_StrongUnique clc a (18 + code) l' l'' bbits (xbits ++ lb1 ++ l''0)).
  rewrite <- lapp.
  repeat rewrite -> app_assoc.
  rewrite -> H4.
  trivial.
  trivial.
  trivial.
  omega.

  apply inr.
  split.
  exact ("In CommonCodeLengthsSWBRStrongDec[<16]: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [l'app cswbr]]]].
  inversion cswbr.
  contradict no.
  exists m0.
  exists input.
  exists (lb1 ++ l'').
  split.
  rewrite -> app_assoc.
  rewrite -> H4.
  trivial.
  trivial.

  destruct H1.
  contradict no.
  exists (16 + code).
  exists bbits.
  exists (xbits ++ lb1 ++ l'').
  split.
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  destruct H1.
  contradict no.
  exists (17 + code).
  exists bbits.
  exists (xbits ++ lb1 ++ l'').
  split.
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
  destruct H1.
  contradict no.
  exists (18 + code).
  exists bbits.
  exists (xbits ++ lb1 ++ l'').
  split.
  repeat rewrite -> app_assoc.
  rewrite -> H3.
  trivial.
  trivial.
Defined.

Lemma CommonCodeLengthsSWBRStrongUnique : forall clc n, StrongUnique (CommonCodeLengthsSWBR clc n).
Proof.
  intros clc n_.
  refine ((fix f n m0 (le : n <= m0) {struct m0} : StrongUnique (CommonCodeLengthsSWBR clc n) := _) n_ n_ (le_refl n_)).

  intros a b la las lb lbs apps csa csb.
  inversion csa.
  inversion csb.
  auto.
  omega.
  replace m with 0 in H3.
  inversion H3.
  destruct code.
  inversion H10.
  omega.
  destruct code.
  inversion H10.
  inversion H10.
  omega.
  replace m with 0 in H3.
  inversion H3.
  destruct code.
  inversion H10.
  omega.
  destruct code.
  inversion H10.
  inversion H10.
  omega.
  replace m with 0 in H3.
  inversion H3.
  destruct code.
  inversion H10.
  omega.
  destruct code.
  inversion H10.
  inversion H10.
  omega.

  inversion csb.
  omega.
  destruct (dc_StrongUnique clc m1 m input0 (lb0 ++ lbs) input (lb1 ++ las)).
  repeat rewrite -> app_assoc.
  rewrite -> H10.
  rewrite -> H4.
  auto.
  trivial.
  trivial.
  destruct m0.
  omega.
  assert (le' : n0 <= m0).
  omega.
  destruct (f n0 m0 le' brs0 brs lb0 lbs lb1 las) as [A B].
  apply (app_ll input0 _ input _).
  repeat rewrite -> app_assoc.
  rewrite -> H10.
  rewrite -> H4.
  auto.
  rewrite -> H12.
  reflexivity.
  replace n0 with n1.
  trivial.
  omega.
  trivial.
  rewrite -> A.
  rewrite -> B.
  rewrite -> H12.
  rewrite -> H11.
  auto.

  destruct H6.
  destruct (dc_StrongUnique clc m (16 + code) input (lb1 ++ las) bbits (xbits ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H9.
  rewrite -> H4.
  auto.
  trivial.
  trivial.
  omega.
  destruct H6.
  destruct (dc_StrongUnique clc m (17 + code) input (lb1 ++ las) bbits (xbits ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H9.
  rewrite -> H4.
  auto.
  trivial.
  trivial.
  omega.
  destruct H6.
  destruct (dc_StrongUnique clc m (18 + code) input (lb1 ++ las) bbits (xbits ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H9.
  rewrite -> H4.
  auto.
  trivial.
  trivial.
  omega.

  destruct m0.
  replace m with 0 in H0.
  inversion H0.
  destruct code.
  inversion H7.
  omega.
  destruct code.
  inversion H6.
  inversion H6.
  omega.

  inversion csb.
  replace m with 0 in H0.
  inversion H0.
  destruct code.
  inversion H10.
  omega.
  destruct code.
  inversion H9.
  inversion H9.
  omega.

  destruct H0.
  destruct (dc_StrongUnique clc (16 + code) m1 bbits (xbits ++ lb1 ++ las) input0 (lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H9.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  omega.

  destruct (CompressedWithExtraBitsStrongUnique clc 16 [2] [3] [6] m m1 input (lb1 ++ las) input0 (lb0 ++ lbs)) as [web1 web2].
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.

  destruct m.
  replace m1 with 0 in H5.
  inversion H5.
  destruct code.
  inversion H12.
  omega.
  destruct code.
  inversion H12.
  inversion H12.

  assert (le' : n0 <= m0).
  omega.
  destruct (f n0 m0 le' brs brs0 lb1 las lb0 lbs) as [H9 H10].
  apply (app_ll input _ input0 _).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  auto.
  f_equal.
  auto.
  trivial.
  replace n0 with n1.
  trivial.
  omega.

  rewrite -> web1.
  rewrite -> web2.
  rewrite -> H9.
  rewrite -> H10.

  auto.

  destruct H0.
  destruct H5.
  destruct (dc_StrongUnique clc (16 + code) (17 + code0) bbits (xbits ++ lb1 ++ las) bbits0 (xbits0 ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H9.
  inversion H9.

  destruct H0.
  destruct H5.
  destruct (dc_StrongUnique clc (16 + code) (18 + code0) bbits (xbits ++ lb1 ++ las) bbits0 (xbits0 ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H9.
  inversion H9.

  inversion csb.
  replace m with 0 in H0.
  inversion H0.
  destruct code.
  inversion H10.
  omega.
  destruct code.
  inversion H9.
  inversion H9.
  omega.

  destruct H0.
  destruct (dc_StrongUnique clc (17 + code) m1 bbits (xbits ++ lb1 ++ las) input0 (lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H9.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  omega.

  destruct H0.
  destruct H5.
  destruct (dc_StrongUnique clc (17 + code) (16 + code0) bbits (xbits ++ lb1 ++ las) bbits0 (xbits0 ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H15.
  inversion H15.

  destruct (CompressedWithExtraBitsStrongUnique clc 17 [3] [3-1] [10-1] m m1 input (lb1 ++ las) input0 (lb0 ++ lbs)) as [web1 web2].
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.

  destruct m0.
  omega.
  destruct m.
  replace m1 with 0 in H5.
  inversion H5.
  destruct code.
  inversion H12.
  omega.
  destruct code.
  inversion H12.
  inversion H12.

  assert (le' : n0 <= m0).
  omega.
  destruct (f n0 m0 le' brs brs0 lb1 las lb0 lbs) as [H9 H10].
  apply (app_ll input _ input0 _).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  auto.
  f_equal.
  auto.
  trivial.
  replace n0 with n1.
  trivial.
  omega.

  rewrite -> web1.
  rewrite -> web2.
  rewrite -> H9.
  rewrite -> H10.

  auto.

  destruct H0.
  destruct H5.
  destruct (dc_StrongUnique clc (17 + code) (18 + code0) bbits (xbits ++ lb1 ++ las) bbits0 (xbits0 ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  destruct code.
  omega.
  destruct code.
  inversion H9.
  inversion H9.

  inversion csb.
  replace m with 0 in H0.
  inversion H0.
  destruct code.
  inversion H10.
  omega.
  destruct code.
  inversion H9.
  inversion H9.
  omega.

  destruct H0.
  destruct (dc_StrongUnique clc (18 + code) m1 bbits (xbits ++ lb1 ++ las) input0 (lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H9.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  omega.

  destruct H0.
  destruct H5.
  destruct (dc_StrongUnique clc (18 + code) (16 + code0) bbits (xbits ++ lb1 ++ las) bbits0 (xbits0 ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H15.
  inversion H15.

  destruct H0.
  destruct H5.
  destruct (dc_StrongUnique clc (18 + code) (17 + code0) bbits (xbits ++ lb1 ++ las) bbits0 (xbits0 ++ lb0 ++ lbs)).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.
  destruct code0.
  omega.
  destruct code0.
  inversion H15.
  inversion H15.

  destruct (CompressedWithExtraBitsStrongUnique clc 18 [7] [11-1] [138 - 1] m m1 input (lb1 ++ las) input0 (lb0 ++ lbs)) as [web1 web2].
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  trivial.
  trivial.
  trivial.

  destruct m0.
  omega.
  destruct m.
  replace m1 with 0 in H5.
  inversion H5.
  destruct code.
  inversion H12.
  omega.
  destruct code.
  inversion H12.
  inversion H12.

  assert (le' : n0 <= m0).
  omega.
  destruct (f n0 m0 le' brs brs0 lb1 las lb0 lbs) as [H9 H10].
  apply (app_ll input _ input0 _).
  repeat rewrite -> app_assoc.
  rewrite -> H8.
  rewrite -> H3.
  auto.
  f_equal.
  auto.
  trivial.
  replace n0 with n1.
  trivial.
  omega.

  rewrite -> web1.
  rewrite -> web2.
  rewrite -> H9.
  rewrite -> H10.

  auto.
Defined.

Lemma CommonCodeLengthsNlen : forall clc n output input,
                                CommonCodeLengthsN clc n output input ->
                                ll output = n.
Proof.
  intros clc n output input H.
  destruct H as [C H H0].
  assert (H1 : ll output = brlen C).
  apply rbrs_brlen.
  trivial.
  rewrite -> H1.
  symmetry.
  apply (CommonCodeLengthsSWBRlen clc _ input).
  trivial.
Qed.


Lemma CommonCodeLengthsNStrongDec : forall (clc : deflateCoding 19) (n : nat), StrongDec (CommonCodeLengthsN clc n).
Proof.
  intros clc n l.
  destruct (CommonCodeLengthsSWBRStrongDec clc n l) as [[a [l' [l'' [lapp cclswbr]]]]|[reason no]].
  destruct (ResolveBackReferencesDec a) as [[out rbr]|no].
  apply inl.
  exists out.
  exists l'.
  exists l''.
  split.
  trivial.
  exact (ccl clc n out l' a cclswbr rbr).  
  apply inr.
  split.
  exact "In CommonCodeLengthsNStrongDec: Illegal Back-Reference."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app cclN]]]].
  inversion cclN.
  contradict no.
  assert (Ca : C = a).
  apply (CommonCodeLengthsSWBRStrongUnique clc n C a l'0 l''0 l' l'').
  rewrite <- l'app.
  trivial.
  trivial.
  trivial.
  rewrite -> Ca in H0.
  exists a0.
  trivial.

  apply inr.
  split.
  exact ("In CommonCodeLengthsNStrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp cclN]]]].
  inversion cclN.
  contradict no.
  exists C.
  exists l'.
  exists l''.
  firstorder.
Defined.

Lemma CommonCodeLengthsNStrongUnique : forall (clc : deflateCoding 19) (n : nat), StrongUnique (CommonCodeLengthsN clc n).
Proof.
  intros clc n a b la las lb lbs apps ccla cclb.
  inversion ccla.
  inversion cclb.
  assert (X : C = C0 /\ la = lb).
  apply (CommonCodeLengthsSWBRStrongUnique clc n C C0 la las lb lbs).
  trivial.
  trivial.
  trivial.
  destruct X as [cc0 ab].
  split.
  apply (ResolveBackReferencesUnique C a b).
  trivial.
  rewrite -> cc0.
  trivial.
  trivial.
Defined.

Lemma SplitCodeLengthsStrongUnique : forall clc hlit hdist, StrongUnique (fun x => SplitCodeLengths clc hlit hdist (fst x) (snd x)).
Proof.
  intros clc hlit hdist a b la las lb lbs apps scla sclb.
  inversion scla.
  inversion sclb.

  destruct (CommonCodeLengthsNStrongUnique clc (hlit + hdist) (litlenL ++ distL) (litlenL0 ++ distL0) la las lb lbs apps) as [A B].
  trivial.
  trivial.
  destruct (app_ll litlenL distL litlenL0 distL0 A) as [C D].
  rewrite -> H.
  auto.
  split.
  destruct a as [a1 a2].
  destruct b as [b1 b2].
  unfold fst in H6.
  unfold fst in H1.
  assert (X : a1 = b1).
  apply to_list_inj.
  rewrite -> H1.
  rewrite -> H6.
  rewrite -> C.
  assert (E : lm = lm0).
  assert (ll litlenL + lm = 288).
  rewrite <- (to_list_length a1).
  replace lm with (ll (repeat lm 0)).
  rewrite <- app_length.
  rewrite <- H1.
  reflexivity.
  apply rep_length.
  assert (ll litlenL0 + lm0 = 288).
  rewrite <- (to_list_length b1).
  replace lm0 with (ll (repeat lm0 0)).
  rewrite <- app_length.
  rewrite <- H6.
  reflexivity.
  apply rep_length.
  omega.

  rewrite -> E.
  reflexivity.

  assert (Y : a2 = b2).
  apply to_list_inj.
  unfold snd in H2.
  rewrite -> H2.
  unfold snd in H7.
  rewrite -> H7.
  assert (G : ld = ld0).
  assert (ll distL + ld = 32).
  rewrite <- (to_list_length a2).
  replace ld with (ll (repeat ld 0)).
  rewrite <- app_length.
  rewrite <- H2.
  reflexivity.
  apply rep_length.
  assert (ll distL0 + ld0 = 32).
  rewrite <- (to_list_length b2).
  replace ld0 with (ll (repeat ld0 0)).
  rewrite <- app_length.
  rewrite <- H7.
  reflexivity.
  apply rep_length.
  omega.
  rewrite -> D.
  rewrite -> G.
  reflexivity.
  rewrite -> X.
  rewrite -> Y.
  reflexivity.
  exact B.
Defined.

Lemma SplitCodeLengthsStrongDec : forall clc hlit hdist, StrongDec (fun x => SplitCodeLengths clc hlit hdist (fst x) (snd x)).
Proof.
  intros clc hlit hdist l.
  destruct (le_dec hlit 288) as [hlit_le_288 | hlit_nle_288].
  destruct (le_dec hdist 32) as [dist_le_32 | dist_nle_32].

  destruct (CommonCodeLengthsNStrongDec clc (hlit + hdist) l) as [[a [l' [l'' [lapp ccn]]]]|[reason noccn]].
  assert (lens : ll a = hlit + hdist).
  apply (CommonCodeLengthsNlen clc (hlit + hdist) a l' ccn).
  assert (hlitl : hlit <= ll a).
  omega.
  destruct (slice_list_le _ _ hlitl) as [l1 [l2 [l1app slc]]].
  set (litlen' := of_list (l1 ++ repeat (288 - hlit) 0)).
  assert (litleneq : ll (l1 ++ repeat (288 - hlit) 0) = 288).
  rewrite -> app_length.
  rewrite -> slc.
  rewrite -> rep_length.
  omega.
  set (dist' := of_list (l2 ++ repeat (32 - hdist) 0)).
  assert (disteq : ll (l2 ++ repeat (32 - hdist) 0) = 32).
  rewrite -> app_length.
  assert (slc' : ll l2 = hdist).
  rewrite <- l1app in lens.
  rewrite -> app_length in lens.
  omega.
  rewrite -> slc'.
  rewrite -> rep_length.
  omega.
  apply inl.
  exists (vec_id litleneq litlen', vec_id disteq dist').
  exists l'.
  exists l''.
  split.
  trivial.
  unfold fst.
  unfold snd.
  apply (makeSplitCodeLengths _ _ _ _ _ _ l1 l2 (288 - hlit) (32 - hdist)).
  trivial.
  trivial.
  rewrite <- l1app in lens.
  rewrite -> app_length in lens.
  omega.
  unfold litlen'.
  dependent destruction litleneq.
  rewrite -> vec_id_destroy.
  rewrite -> to_list_of_list_opp.
  rewrite -> app_length.
  rewrite -> rep_length.
  rewrite -> slc.
  replace (hlit + (288 - hlit) - hlit) with (288 - hlit).
  reflexivity.
  omega.
  unfold dist'.
  dependent destruction disteq.
  rewrite -> vec_id_destroy.
  rewrite -> to_list_of_list_opp.
  rewrite -> app_length.
  rewrite -> rep_length.
  replace (ll l2 + (32 - hdist) - hdist) with (32 - hdist).
  reflexivity.
  rewrite <- l1app in lens.
  rewrite -> app_length in lens.
  omega.
  rewrite -> l1app.
  trivial.

  apply inr.
  split.
  exact ("In SplitCodeLengthsStrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp scl]]]].
  inversion scl.
  contradict noccn.
  exists (litlenL ++ distL).
  exists l'.
  exists l''.
  split.
  trivial.
  trivial.

  apply inr.
  split.
  exact ("In SplitCodeLengthsStrongDec: dist is not <= 32 : THIS SHOULD NEVER HAPPEN! (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp scl]]]].
  inversion scl.
  assert (ll (to_list (snd a)) = hdist + ld).
  rewrite -> H2.
  rewrite <- H0.
  rewrite -> app_length.
  rewrite -> rep_length.
  reflexivity.
  rewrite -> to_list_length in H4.
  omega.
  apply inr.
  split.
  exact ("In SplitCodeLengthsStrongDec: hlit is not <= 32 : THIS SHOULD NEVER HAPPEN! (" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp scl]]]].
  inversion scl.
  assert (ll (to_list (fst a)) = hlit + lm).
  rewrite -> H1.
  rewrite <- H.
  rewrite -> app_length.
  rewrite -> rep_length.
  reflexivity.
  rewrite -> to_list_length in H4.
  omega.
Qed.

Theorem LitLenDistStrongUnique : forall clc hlit hdist,
                                 StrongUnique (fun l => LitLenDist clc hlit hdist (fst l) (snd l)).
Proof.
  intros clc hlit hdist a b l1 l1s l2 l2s apps H0 H1.
  destruct a as [litlen1 dist1].
  destruct b as [litlen2 dist2].
  unfold fst in H0.
  unfold snd in H0.
  unfold fst in H1.
  unfold snd in H1.
  inversion H0.
  inversion H1.
  destruct (SplitCodeLengthsStrongUnique clc hlit hdist
                                       ((Vmap lb (C 288 litlen1)),(Vmap lb (C 32 dist1)))
                                       ((Vmap lb (C 288 litlen2)),(Vmap lb (C 32 dist2))) l1 l1s l2 l2s).
  trivial.
  unfold fst.
  unfold snd.
  trivial.
  unfold fst.
  unfold snd.
  trivial.
  inversion H3.
  split.
  assert (X : litlen1 = litlen2).
  apply uniqueness.
  auto.
  assert (Y : dist1 = dist2).
  apply uniqueness.
  auto.
  rewrite -> X.
  rewrite -> Y.
  reflexivity.
  trivial.
Defined.

Theorem LitLenDistStrongDec : forall clc hlit hdist, StrongDec (fun x => LitLenDist clc hlit hdist (fst x) (snd x)).
Proof.
  intros clc hlit dist l.
  destruct (SplitCodeLengthsStrongDec clc hlit dist l) as [[a [l' [l'' [lapp scl]]]]|[reason no]].
  destruct ((Qlt_le_dec 1 (kraft_nvec (fst a)))%Q).

  apply inr.
  split.
  exact ("In LitLenDistStrongDec: Lit/Len code lengths do not satisfy kraft's inequality.(" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app litlendist]]]].
  inversion litlendist.
  assert (L : Vmap lb (C _ (fst a0)) = fst a).
  destruct (SplitCodeLengthsStrongUnique clc hlit dist
                                    ((Vmap lb (C 288 (fst a0))), (Vmap lb (C 32 (snd a0))))
                                    ((fst a), (snd a))
                                    l'0 l''0 l' l'').
  rewrite <- l'app.
  trivial.
  exact H.
  exact scl.
  inversion H0.
  reflexivity.
  assert (Q : (1 >= kraft_nvec (fst a))%Q).
  rewrite <- L.
  apply kraft_ineq.
  exact (Qlt_not_le _ _ q Q).

  destruct ((Qlt_le_dec 1 (kraft_nvec (snd a)))%Q).
  apply inr.
  split.
  exact ("In LitLenDistStrongDec: Distance code lengths do not satisfy kraft's inequality.(" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app litlendist]]]].
  assert (L : Vmap lb (C _ (snd a0)) = snd a).
  destruct (SplitCodeLengthsStrongUnique clc hlit dist
                                    ((Vmap lb (C 288 (fst a0))), (Vmap lb (C 32 (snd a0))))
                                    ((fst a), (snd a))
                                    l'0 l''0 l' l'').
  rewrite <- l'app.
  trivial.
  inversion litlendist.
  exact H.
  exact scl.
  inversion H.
  reflexivity.
  assert (Q : (1 >= kraft_nvec (snd a))%Q).
  rewrite <- L.
  apply kraft_ineq.
  exact (Qlt_not_le _ _ q0 Q).
  apply inl.
  destruct (existence _ _ q) as [D1 M1].
  destruct (existence _ _ q0) as [D2 M2].
  exists (D1, D2).
  exists l'.
  exists l''.
  split.
  trivial.
  constructor.
  unfold fst.
  unfold snd.
  rewrite <- M1.
  rewrite <- M2.
  trivial.

  apply inr.
  split.
  exact ("In LitLenDistStrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp litlendist]]]].
  contradict no.
  inversion litlendist.
  exists ((Vmap lb (C 288 (fst a))), (Vmap lb (C 32 (snd a)))).
  exists l'.
  exists l''.
  split.
  trivial.
  exact H.
Defined.

(* TODO : use this in the above proofs, where the same situation frequently occurs *)
Lemma prefix_lemma : forall {m} (coding : deflateCoding m) a b c x y,
                       dc_enc coding a x -> dc_enc coding b y -> prefix x c -> prefix y c -> a = b /\ x = y.
Proof.
  intros.
  destruct (eq_nat_dec a b).
  split.
  exact e.
  rewrite -> e in H.
  destruct H.
  destruct H0.
  destruct (vnth_is_correct _ _ _ H) as [K L].
  destruct (vnth_is_correct _ _ _ H0) as [M N].
  assert (KM : of_nat_lt M = of_nat_lt K).
  apply of_nat_ext.
  rewrite <- KM in L.
  rewrite -> L in N.
  exact N.
  destruct (prefix_common x y c H1 H2).
  contradict p.
  apply (prefix_free' coding a b).
  exact n.
  exact H.
  exact H0.
  contradict p.
  apply (prefix_free' coding b a).
  auto.
  exact H0.
  exact H.
Defined.

Theorem CompressedSWBRStrongUnique : forall litlen dist, StrongUnique (CompressedSWBR litlen dist).
Proof.
  intros litlen dist a b la las lb lbs apps cswbr1 cswbr2.
  revert b lb cswbr2 las lbs apps.
  dependent induction cswbr1.
  intros b lb cswbr2.
  dependent destruction cswbr2.
  intros las lbs apps.
  split.
  reflexivity.
  apply (dc_StrongUnique litlen 256 256 l las l0 lbs).
  trivial.
  trivial.
  trivial.

  intros las lbs apps.
  destruct (prefix_lemma litlen 256 (ByteToNat n) (l ++ las) l l0) as [K1 K2].
  trivial.
  trivial.
  exists las.
  reflexivity.
  exists (prev_lb ++ lbs).
  rewrite -> app_assoc.
  auto.
  assert (K3 : ByteToNat n < 256).
  apply ByteToNatMax.
  omega.

  intros las lbs apps.
  dependent destruction H0.
  destruct (prefix_lemma litlen 256 (257 + code) (l ++ las) l bbits) as [K1 K2].
  trivial.
  trivial.
  exists las.
  reflexivity.
  exists (xbits ++ dbits ++ prev_lb ++ lbs).
  rewrite -> apps.
  repeat (rewrite <- app_assoc; try reflexivity).
  abstract(omega).

  intros b lb cswbr2.
  dependent destruction cswbr2.
  intros las lbs apps.
  destruct (prefix_lemma litlen 256 (ByteToNat n) ((l ++ prev_lb) ++ las) l0 l) as [K1 K2].
  exact H0.
  exact H.
  rewrite -> apps.
  exists lbs.
  reflexivity.
  exists (prev_lb ++ las).
  apply app_assoc.
  assert (K3 : ByteToNat n < 256).
  apply ByteToNatMax.
  omega.

  intros las lbs apps.
  destruct (prefix_lemma litlen (ByteToNat n) (ByteToNat n0) ((l ++ prev_lb) ++ las) l l0) as [K1 K2].
  trivial.
  trivial.
  exists (prev_lb ++ las).
  apply app_assoc.
  rewrite -> apps.
  exists (prev_lb0 ++ lbs).
  apply app_assoc.

  assert (preveq : prev_lb = prev_lb0).
  apply (IHcswbr1 prev_swbr0 prev_lb0 cswbr2 las lbs).
  apply (app_ll l _ l0 _).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  exact apps.
  rewrite -> K2.
  reflexivity.
  rewrite -> preveq.
  rewrite -> K2.
  assert (K1' : n = n0).
  apply ByteToNat_inj.
  trivial.
  rewrite -> K1'.
  split.
  f_equal.
  destruct (IHcswbr1 prev_swbr0 prev_lb0 cswbr2 las lbs) as [H1 H2].
  apply (app_ll l _ l0 _).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  trivial.
  rewrite -> K2.
  reflexivity.
  exact H1.
  reflexivity.

  dependent destruction H0.
  intros las lbs apps.
  destruct (prefix_lemma litlen (257 + code) (ByteToNat n) ((l ++ prev_lb) ++ las) bbits l) as [K1 K2].
  trivial.
  trivial.
  rewrite -> apps.
  exists (xbits ++ dbits ++ prev_lb0 ++ lbs).
  repeat (rewrite -> app_assoc; try reflexivity).
  exists (prev_lb ++ las).
  apply app_assoc.
  assert (ByteToNat n < 256).
  apply ByteToNatMax.
  omega.

  dependent destruction H.
  intros b lb swbr.
  dependent destruction swbr.
  intros las lbs apps.
  destruct (prefix_lemma litlen (257 + code) 256 (l ++ lbs) bbits l) as [K1 K2].
  trivial.
  trivial.
  rewrite <- apps.
  exists (xbits ++ dbits ++ prev_lb ++ las).
  repeat (rewrite -> app_assoc; try reflexivity).
  exists lbs.
  reflexivity.
  omega.

  intros las lbs apps.
  destruct (prefix_lemma litlen (257 + code) (ByteToNat n) ((l ++ prev_lb0) ++ lbs) bbits l) as [K1 K2].
  trivial.
  trivial.
  rewrite <- apps.
  exists (xbits ++ dbits ++ prev_lb ++ las).
  repeat (rewrite -> app_assoc; try reflexivity).
  exists (prev_lb0 ++ lbs).
  apply app_assoc.
  assert (K3 : ByteToNat n < 256).
  apply ByteToNatMax.
  omega.

  intros las lbs apps.
  dependent destruction H7.
  destruct (prefix_lemma litlen (257 + code0) (257 + code) (((bbits ++ xbits) ++ dbits ++ prev_lb) ++ las) bbits0 bbits) as [R A].
  trivial.
  trivial.
  rewrite -> apps.
  exists (xbits0 ++ dbits0 ++ prev_lb0 ++ lbs).
  repeat (rewrite -> app_assoc; try reflexivity).  
  exists (xbits ++ dbits ++ prev_lb ++ las).
  repeat (rewrite -> app_assoc; try reflexivity).
  assert (A' : xbits ++ dbits ++ prev_lb ++ las = xbits0 ++ dbits0 ++ prev_lb0 ++ lbs).
  apply (app_ll bbits _ bbits0 _).
  repeat (try rewrite -> app_assoc in apps; try rewrite -> app_assoc; try exact apps).
  rewrite -> A.
  reflexivity.
  assert (B : xbits = xbits0).
  apply (app_ll _ (dbits ++ prev_lb ++ las) _ (dbits0 ++ prev_lb0 ++ lbs)).
  exact A'.
  assert (R' : code0 = code).
  omega.
  rewrite -> R' in H8.
  rewrite -> H0 in H8.
  inversion H8.
  rewrite -> H11.
  rewrite -> H3.
  exact H16.
  assert (B' : dbits ++ prev_lb ++ las = dbits0 ++ prev_lb0 ++ lbs).
  apply (app_ll xbits _ xbits0 _).
  exact A'.
  rewrite -> B.
  reflexivity.
  unfold CompressedDist in H14.
  unfold CompressedDist in H6.
  destruct (CompressedWithExtraBitsStrongUnique dist 0 distCodeExtraBits distCodeBase distCodeMax d d0 dbits (prev_lb ++ las) dbits0 (prev_lb0 ++ lbs)) as [H11_ C].
  exact B'.
  trivial.
  trivial.
  assert (C' : prev_lb ++ las = prev_lb0 ++ lbs).
  apply (app_ll dbits _ dbits0 _).
  exact B'.
  rewrite -> C.
  reflexivity.
  destruct (IHcswbr1 prev_swbr0 prev_lb0 swbr las lbs C') as [E D].
  rewrite -> A.
  rewrite -> B.
  rewrite -> C.
  rewrite -> D.
  rewrite -> E.
  rewrite -> H11_.
  split.

  assert (cc : code0 = code).
  omega.
  rewrite <- cc in H1.
  rewrite -> H1 in H9.
  inversion H9.
  assert (G : extra = extra0).
  apply (LSBnat_unique xbits).
  trivial.
  rewrite -> B.
  trivial.
  rewrite -> G.
  reflexivity.
  reflexivity.
Defined.

Theorem CompressedSWBRStrongDec: forall litlen dist, StrongDec (CompressedSWBR litlen dist).
Proof.
  intros litlen dist l'.
  refine ((fix f l n (ge : n >= ll l) {struct n} := _) l' (ll l') _).

  destruct (dc_StrongDec litlen l) as [[a [l1 [l1b [lapp dce]]]]|[reason no]].
  destruct (nat_compare a 256) eqn:nc.

  apply inl.
  exists (nil(A:=Byte+nat*nat)).
  exists l1.
  exists l1b.
  split.
  trivial.
  constructor.
  replace a with 256 in dce.
  trivial.
  symmetry.
  apply nat_compare_eq.
  trivial.

  destruct n.
  destruct dce.
  rewrite -> lapp in ge.
  destruct l1.
  contradict H0.
  reflexivity.
  compute in ge.
  omega.

  assert (ale : a < 256).
  apply nat_compare_lt.
  exact nc.
  destruct (f l1b n) as [s|[freason no]].
  destruct l1.
  destruct dce.
  contradict H0.
  reflexivity.
  rewrite -> lapp in ge.
  rewrite -> app_length in ge.
  unfold ll in ge.
  unfold ll.
  omega.
  destruct s as [a0 [l'0 [l'' [l1bapp cswbr]]]].
  apply inl.
  destruct (NatToByte a ale) as [abyte alsb].
  exists (inl abyte :: a0).
  exists (l1 ++ l'0).
  exists l''.
  split.
  rewrite <- app_assoc.
  rewrite <- l1bapp.
  trivial.
  constructor.
  rewrite -> alsb.
  trivial.
  trivial.

  apply inr.
  split.
  exact freason.
  intro Q.
  destruct Q as [a0 [l'0 [l'' [l1bapp cswbr]]]].
  inversion cswbr.
  destruct (prefix_lemma litlen a 256 l l1 l'0) as [R A].
  trivial.
  trivial.
  exists l1b.
  auto.
  exists l''.
  auto.
  omega.

  contradict no.
  exists prev_swbr.
  exists prev_lb.
  exists l''.
  split.
  apply (app_ll l1 _ l0 _).
  rewrite -> app_assoc.
  rewrite -> H2.
  rewrite <- l1bapp.
  auto.
  destruct (prefix_lemma litlen a (ByteToNat n0) l l1 l0) as [R A].
  trivial.
  trivial.
  exists l1b.
  auto.
  exists (prev_lb ++ l'').
  rewrite -> app_assoc.
  rewrite -> H2.
  auto.
  rewrite -> A.
  reflexivity.
  trivial.

  inversion H0.
  destruct (prefix_lemma litlen a (257 + code) l l1 bbits) as [R A].
  trivial.
  trivial.
  exists l1b.
  auto.
  exists (xbits ++ dbits ++ prev_lb ++ l'').
  repeat (try rewrite -> app_assoc).
  rewrite -> H12.
  repeat (try rewrite -> app_assoc in H3).
  rewrite -> H3.
  auto.
  omega.

  assert (agt : a > 256).
  apply nat_compare_gt.
  exact nc.

  destruct (CompressedWithExtraBitsStrongDec litlen 257 repeatCodeExtraBits repeatCodeBase repeatCodeMax l) as [[len [l'0 [l'' [l'app cweb1]]]]|[reason no]].
  destruct (CompressedWithExtraBitsStrongDec dist 0 distCodeExtraBits distCodeBase distCodeMax l'') as [[dst [l'1 [l''1 [l''app cweb2]]]]|[reason no]].
  destruct n.
  destruct dce.
  rewrite -> lapp in ge.
  destruct l1.
  contradict H0.
  reflexivity.
  compute in ge.
  omega.
  assert (n >= lb l''1).
  rewrite -> l'app in ge.
  rewrite -> l''app in ge.
  inversion cweb1 as [base extra code max xbitnum bbits xbits H H0 H1 H1_ H2 H3 H3_ H4 H5].
  rewrite <- H5 in ge.
  rewrite <- app_assoc in ge.
  destruct H.
  destruct bbits.
  contradict H6.
  reflexivity.
  assert (S n >= S (lb bbits) + lb xbits + lb l'1 + lb l''1).
  replace (S (lb bbits)) with (lb (b :: bbits)).
  rewrite <- app_length.
  rewrite <- app_length.
  rewrite <- app_length.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  exact ge.
  reflexivity.
  omega.
  destruct (f l''1 n) as [s | [freason no]].
  trivial.
  destruct s as [a0 [l'2 [l''0 [lapp2 cswbr3]]]].
  apply inl.
  exists (inr (len, dst) :: a0).
  exists (l'0 ++ l'1 ++ l'2).
  exists (l''0).
  split.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  rewrite <- lapp2.
  rewrite <- l''app.
  trivial.
  constructor.
  trivial.
  trivial.
  trivial.

  apply inr.
  split.
  exact freason.
  intro Q.
  destruct Q as [a0 [l'2 [l''0 [lapp2 cswbr]]]].
  inversion cswbr.
  inversion cweb1.
  destruct (prefix_lemma litlen a 256 l l1 l'2) as [R A].
  trivial.
  trivial.
  exists l1b.
  auto.
  exists l''0.
  auto.
  omega.

  destruct (prefix_lemma litlen a (ByteToNat n0) l l1 l0) as [R A].
  trivial.
  trivial.
  exists l1b.
  auto.
  exists (prev_lb ++ l''0).
  rewrite -> app_assoc.
  rewrite -> H3.
  auto.
  assert (ByteToNat n0 < 256).
  apply ByteToNatMax.
  omega.

  contradict no.
  exists prev_swbr.
  exists prev_lb.
  exists (l''0).
  split.
  apply (app_ll (l'0 ++ l'1) _ (lbits ++ dbits) _).
  rewrite <- app_assoc.
  rewrite <- l''app.
  rewrite <- l'app.
  rewrite -> app_assoc.
  rewrite -> app_assoc in H4.
  rewrite -> H4.
  trivial.
  assert (L_eq : l'0 = lbits).
  unfold CompressedLength in H1.
  apply (CompressedWithExtraBitsStrongUnique litlen 257 repeatCodeExtraBits repeatCodeBase repeatCodeMax len l0 l'0 l'' lbits (dbits ++ prev_lb ++ l''0)).
  rewrite -> app_assoc in H4.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> H4.
  rewrite <- lapp2.
  auto.
  trivial.
  trivial.
  assert (R_eq : l'' = dbits ++ prev_lb ++ l''0).
  apply (app_ll l'0 _ lbits _).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> app_assoc in H4.
  rewrite -> H4.
  rewrite <- lapp2.
  auto.
  rewrite -> L_eq.
  reflexivity.
  assert (D_eq : l'1 = dbits).
  unfold CompressedDist in H2.
  apply (CompressedWithExtraBitsStrongUnique dist 0 distCodeExtraBits distCodeBase distCodeMax dst d l'1 l''1 dbits (prev_lb ++ l''0)).
  rewrite <- l''app.
  trivial.
  trivial.
  trivial.
  rewrite -> L_eq.
  rewrite -> D_eq.
  reflexivity.
  trivial.

  apply inr.
  split.
  exact ("In CompressedSWBRStrongDec, while parsing distance code: " ++ reason)%string.
  intro Q.
  destruct Q as [a0 [l'1 [l''0 [lapp2 cswbr]]]].
  inversion cswbr.
  destruct (prefix_lemma litlen a 256 l l1 l'1) as [R A].
  trivial.
  trivial.
  exists l1b.
  auto.
  exists l''0.
  auto.
  omega.

  destruct (prefix_lemma litlen a (ByteToNat n0) l l1 l0) as [R A].
  trivial.
  trivial.
  exists l1b.
  auto.
  exists (prev_lb ++ l''0).
  rewrite -> app_assoc.
  rewrite -> H2.
  auto.
  assert (ByteToNat n0 < 256).
  apply ByteToNatMax.
  omega.

  contradict no.
  exists d.
  exists dbits.
  exists (prev_lb ++ l''0).
  split.
  apply (app_ll l'0 _ lbits _).
  rewrite <- l'app.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> app_assoc in H3.
  rewrite -> H3.
  trivial.
  replace l'0 with lbits.
  reflexivity.
  apply (CompressedWithExtraBitsStrongUnique litlen 257 repeatCodeExtraBits repeatCodeBase repeatCodeMax l0 len lbits (dbits ++ prev_lb ++ l''0) l'0 l'').
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> app_assoc in H3.
  rewrite -> H3.
  rewrite <- lapp2.
  trivial.
  trivial.
  trivial.
  trivial.

  apply inr.
  split.
  exact ("In CompressedSWBRStrongDec, while parsing repeat code: " ++ reason)%string.
  intro Q.
  destruct Q as [a0 [l'0 [l'' [lapp2 cswbr]]]].
  inversion cswbr.
  destruct (prefix_lemma litlen a 256 l l1 l'0).
  trivial.
  trivial.
  exists l1b.
  auto.
  exists l''.
  auto.
  omega.

  destruct (prefix_lemma litlen a (ByteToNat n0) l l1 l0).
  trivial.
  trivial.
  exists l1b.
  auto.
  exists (prev_lb ++ l'').
  rewrite -> app_assoc.
  rewrite -> H2.
  auto.
  assert (ByteToNat n0 < 256).
  apply ByteToNatMax.
  omega.

  contradict no.
  exists l0.
  exists lbits.
  exists (dbits ++ prev_lb ++ l'').
  split.
  repeat (try rewrite -> app_assoc).
  rewrite -> app_assoc in H3.
  rewrite -> H3.
  auto.
  trivial.

  apply inr.
  split.
  exact ("In CompressedSWBRStrongDec, while parsing literal code: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l'0 [l'' [lapp cswbr]]]].
  inversion cswbr.
  contradict no.
  exists 256.
  exists l'0.
  exists l''.
  firstorder.

  contradict no.
  exists (ByteToNat n0).
  exists l0.
  exists (prev_lb ++ l'').
  split.
  rewrite -> app_assoc.
  rewrite -> H2.
  auto.
  trivial.

  inversion H0 as [base extra code max xbitnum bbits xbits H4 H5 H6 H6_ H7 H8 H8_ H9].
  contradict no.
  exists (257 + code).
  exists bbits.
  exists (xbits ++ dbits ++ prev_lb ++ l'').
  split.
  repeat (try rewrite -> app_assoc).
  rewrite -> H10.
  rewrite -> app_assoc in H3.
  rewrite -> H3.
  trivial.
  trivial.
  omega.
Defined.


Theorem DynamicallyCompressedHeaderStrongUniqueStrongDec :
  StrongUnique DynamicallyCompressedHeader * StrongDec DynamicallyCompressedHeader.
Proof.
  apply CombineStrongDecStrongUnique.
  apply readBitsLSBStrongUnique.
  apply readBitsLSBStrongDec.
  intro bq.
  apply CombineStrongDecStrongUnique.
  apply readBitsLSBStrongUnique.
  apply readBitsLSBStrongDec.
  intro bq0.
  apply CombineStrongDecStrongUnique.
  apply readBitsLSBStrongUnique.
  apply readBitsLSBStrongDec.
  intro bq1.
  apply CombineStrongDecStrongUnique.
  apply CLCHeaderStrongUnique.
  apply CLCHeaderStrongDec.
  intro bq2.
  split.
  apply LitLenDistStrongUnique.
  apply LitLenDistStrongDec.
Defined.

Theorem DynamicallyCompressedBlockStrongUniqueStrongDec :
  StrongUnique DynamicallyCompressedBlock * StrongDec DynamicallyCompressedBlock.
Proof.
  apply CombineStrongDecStrongUnique.
  apply DynamicallyCompressedHeaderStrongUniqueStrongDec.
  apply DynamicallyCompressedHeaderStrongUniqueStrongDec.
  intro bq.
  split.
  apply CompressedSWBRStrongUnique.
  apply CompressedSWBRStrongDec.
Defined.


Theorem StaticallyCompressedBlockStrongUnique : StrongUnique StaticallyCompressedBlock.
Proof.
  intros a b la las lb lbs apps scba scbb.
  inversion scba.
  inversion scbb.
  apply (CompressedSWBRStrongUnique fixed_lit_code fixed_dist_code a b la las lb lbs).
  trivial.
  trivial.
  trivial.
Defined.

Theorem StaticallyCompressedBlockStrongDec : StrongDec StaticallyCompressedBlock.
Proof.
  intro l.
  destruct (CompressedSWBRStrongDec fixed_lit_code fixed_dist_code l) as [[a [l' [l'' [lapp cswbr]]]]|[reason no]].
  apply inl.
  exists a.
  exists l'.
  exists l''.
  split.
  trivial.
  constructor.
  trivial.
  apply inr.
  split.
  exact ("In StaticallyCompressedBlockStrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp scb]]]].
  inversion scb.
  contradict no.
  exists a.
  exists l'.
  exists l''.
  split.
  trivial.
  trivial.
Defined.

Theorem OneBlockWithPaddingStrongUnique : forall n, StrongUnique (fun out => OneBlockWithPadding out n).
Proof.
  intros n a b la las lb lbs apps wua wub.
  inversion wua.
  inversion wub.
  destruct (fst DynamicallyCompressedBlockStrongUniqueStrongDec a b dcb las dcb0 lbs) as [H5 H6].
  apply (app_ll [false; true] _ [false; true] _).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  replace ([false; true] ++ dcb) with la.
  replace ([false; true] ++ dcb0) with lb.
  trivial.
  reflexivity.
  trivial.
  trivial.
  split.
  trivial.
  rewrite -> H6.
  reflexivity.

  rewrite <- H1 in apps.
  rewrite <- H4 in apps.
  inversion apps.

  rewrite <- H1 in apps.
  rewrite <- H6 in apps.
  inversion apps.

  inversion wub.
  rewrite <- H1 in apps.
  rewrite <- H4 in apps.
  inversion apps.

  destruct (StaticallyCompressedBlockStrongUnique a b scb las scb0 lbs) as [scbs gcbs].
  apply (app_ll [true; false] _ [true; false] _).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  replace ([true; false] ++ scb) with la.
  replace ([true; false] ++ scb0) with lb.
  trivial.
  reflexivity.
  trivial.
  trivial.
  split.
  trivial.
  rewrite -> gcbs.
  trivial.
  rewrite <- H6 in apps.
  rewrite <- H1 in apps.
  inversion apps.
  inversion wub.

  rewrite <- H3 in apps.
  rewrite <- H6 in apps.
  inversion apps.

  rewrite <- H3 in apps.
  rewrite <- H6 in apps.
  inversion apps.

  assert (pads : pad = pad0).
  apply (app_ll _ (ucb ++ las) _ (ucb0 ++ lbs)).
  apply (cons_inj (a:=false) (c:=false)).
  apply (cons_inj (a:=false) (c:=false)).
  repeat (try rewrite -> app_comm_cons).
  repeat (try rewrite -> app_assoc).
  repeat (try rewrite -> app_comm_cons in H3).
  repeat (try rewrite -> app_comm_cons in H8).
  rewrite -> H8.
  rewrite -> H3.
  trivial.

  replace (ll (_ :: _ :: pad)) with (S (S (ll pad))) in H0.
  replace (ll (_ :: _ :: pad0)) with (S (S (ll pad0))) in H5.
  omega.
  reflexivity.
  reflexivity.
  destruct (fst UncompressedBlockDirectStrongUniqueStrongDec a b ucb las ucb0 lbs) as [H9 H10].
  apply (app_ll (false :: false :: pad) _ (false :: false :: pad0)).
  rewrite -> app_comm_cons in H8.
  rewrite -> app_comm_cons in H8.
  rewrite -> app_comm_cons in H3.
  rewrite -> app_comm_cons in H3.
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> H3.
  rewrite -> H8.
  trivial.
  rewrite -> pads.
  reflexivity.
  trivial.
  trivial.
  split.
  trivial.
  rewrite -> H10.
  rewrite -> pads.
  reflexivity.
Defined.

Lemma DivisionByEightLemma : forall n,
                               {m : nat & {o : nat | o < 8 /\ n + o = 8 * m}}.
Proof.
  intro n.
  assert (H : n = 8 * (n / 8) + n mod 8).
  apply div_mod.
  omega.
  destruct (eq_nat_dec (n mod 8) 0).
  exists (n / 8).
  exists 0.
  split.
  omega.
  omega.
  exists (n / 8 + 1).
  exists (8 - n mod 8).
  split.
  assert (n mod 8 < 8).
  apply mod_bound_pos.
  omega.
  omega.
  omega.
  assert (n mod 8 < 8).
  apply mod_bound_pos.
  omega.
  omega.
  omega.
Defined.

Theorem OneBlockWithPaddingStrongDec : forall n, StrongDec (fun out => OneBlockWithPadding out n).
Proof.
  intros n l.
  destruct l as [| b l].
  apply inr.
  split.
  exact "In OneBlockWithPaddingStrongDec: not enough header bits."%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp phail]]]].
  inversion phail.
  destruct l'.
  inversion H1.
  inversion lapp.
  destruct l'.
  inversion H1.
  inversion lapp.
  destruct l'.
  inversion H3.
  inversion lapp.

  destruct l as [|b0 l].
  apply inr.
  split.
  exact "In OneBlockWithPaddingStrongDec: not enough header bits."%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp phail]]]].
  inversion phail.
  destruct l'.
  inversion H1.
  destruct l'.
  inversion H1.
  inversion lapp.
  destruct l'.
  inversion H1.
  destruct l'.
  inversion H1.
  inversion lapp.
  destruct l'.
  inversion H3.
  destruct l'.
  inversion H3.
  inversion lapp.

  destruct b.
  destruct b0.

  (* true true *)
  apply inr.
  split.
  exact ("In OneBlockWithPaddingStrongDec: header bits [true; true] not allowed.(" ++ blstring l ++ ")")%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp phail]]]].
  inversion phail.
  destruct l'.
  inversion H1.
  destruct l'.
  inversion H1.
  inversion lapp.
  rewrite <- H3 in H1.
  rewrite <- H4 in H1.
  inversion H1.
  destruct l'.
  inversion H1.
  destruct l'.
  inversion H1.
  inversion lapp.
  rewrite <- H3 in H1.
  rewrite <- H4 in H1.
  inversion H1.
  destruct l'.
  inversion H3.
  destruct l'.
  inversion H3.
  inversion lapp.
  rewrite <- H5 in H3.
  rewrite <- H6 in H3.
  inversion H3.

  (* true false - statically compressed block - CONTRARY TO THE STANDARD *)
  destruct (StaticallyCompressedBlockStrongDec l) as [[a [l' [l'' [lapp scba]]]]|[reason no]].
  apply inl.
  exists a.
  exists (true :: false :: l').
  exists l''.
  split.
  rewrite -> lapp.
  reflexivity.
  constructor.
  exact scba.

  apply inr.
  split.
  exact ("In OneBlockWithPaddingStrongDec while parsing statically compressed block:" ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp obwp]]]].
  inversion obwp.
  rewrite <- H1 in lapp.
  inversion lapp.
  contradict no.
  exists a.
  exists scb.
  exists l''.
  split.
  rewrite <- H1 in lapp.
  inversion lapp.
  reflexivity.
  trivial.
  rewrite <- H3 in lapp.
  inversion lapp.

  destruct b0.

  (* false true - dynamically compressed block *)
  destruct (snd DynamicallyCompressedBlockStrongUniqueStrongDec l) as [[a [l' [l'' [lapp dcba]]]]|[reason no]].
  apply inl.
  exists a.
  exists (false :: true :: l').
  exists l''.
  split.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  rewrite <- lapp.
  reflexivity.
  constructor.
  trivial.

  apply inr.
  split.
  exact ("In OneBlockWithPaddingStrongDec while parsing dynamically compressed block:" ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp obwp]]]].
  inversion obwp.
  contradict no.
  exists a.
  exists dcb.
  exists l''.
  split.
  rewrite <- H1 in lapp.
  inversion lapp.
  reflexivity.
  trivial.

  rewrite <- H1 in lapp.
  inversion lapp.
  rewrite <- H3 in lapp.
  inversion lapp.

  (* false false - uncompressed block *)
  destruct (DivisionByEightLemma (n + 2)) as [m [o [ole eql]]].
  destruct (slice_list o l) as [[l1 [l2 [lapp ll1]]]|no].
  destruct (snd UncompressedBlockDirectStrongUniqueStrongDec l2) as [[a [l' [l'' [l2app ucbd]]]]|[reason no]].
  apply inl.
  exists a.
  exists (false :: false :: l1 ++ l').
  exists l''.
  split.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  rewrite <- app_assoc.
  rewrite <- l2app.
  rewrite -> lapp.
  reflexivity.
  apply (obwpUCB _ _ n m).
  trivial.
  replace (lb (false :: false :: l1)) with (S (S (lb l1))).
  rewrite -> ll1.
  omega.
  reflexivity.
  omega.

  apply inr.
  split.
  exact ("In OneBlockWithPaddingStrongDec while parsing uncompressed block (after padding):" ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [l'app obwp]]]].
  inversion obwp.
  rewrite <- H1 in l'app.
  inversion l'app.
  rewrite <- H1 in l'app.
  inversion l'app.
  contradict no.
  exists a.
  exists ucb.
  exists l''.
  split.
  apply (app_ll (false :: false :: l1) _ (false :: false :: pad) _).
  rewrite -> app_assoc.
  rewrite -> app_comm_cons in H3.
  rewrite -> app_comm_cons in H3.
  rewrite -> H3.
  rewrite <- app_comm_cons.
  rewrite <- app_comm_cons.
  rewrite -> lapp.
  trivial.
  replace (lb (false :: false :: pad)) with (S (S (lb pad))) in H0.
  replace (lb (false :: false :: pad)) with (S (S (lb pad))).
  replace (lb (false :: false :: l1)) with (S (S (lb l1))).
  omega.
  reflexivity.
  reflexivity.
  reflexivity.
  trivial.

  apply inr.
  split.
  exact "In OneBlockWithPaddingStrongDec while parsing statically compressed block: not enough padding-bits"%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp obwp]]]].
  inversion obwp.
  rewrite <- H1 in lapp.
  inversion lapp.
  rewrite <- H1 in lapp.
  inversion lapp.
  contradict no.
  exists pad.
  exists (ucb ++ l'').
  split.
  apply (app_ll [false; false] _ [false; false] _).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> app_comm_cons in H3.
  rewrite -> app_comm_cons in H3.
  replace (([false; false] ++ pad) ++ ucb) with l'.
  auto.
  auto.
  replace (lb (_ :: _ :: pad)) with (S (S (lb pad))) in H0.
  omega.
  reflexivity.
Defined.

Theorem ManyBlocksStrongUnique : forall n, StrongUnique (ManyBlocks n).
Proof.
  intros n a b la las lb lbs apps mba mbb.
  revert b lb lbs apps mbb.
  induction mba.
  intros b lb lbs apps mbb.
  destruct mbb.
  destruct (OneBlockWithPaddingStrongUnique (n + 1) out out0 inp las inp0 lbs) as [A B].
  inversion apps. 
  reflexivity.
  trivial.
  trivial.
  split.
  trivial.
  f_equal.
  trivial.
  inversion apps.

  intros b lb lbs apps mbb.
  destruct mbb.
  inversion apps.
  destruct (OneBlockWithPaddingStrongUnique (n + 1) out1 out0 inp1 (inp2 ++ las) inp0 (inp3 ++ lbs)) as [A B].
  rewrite -> app_comm_cons in apps.
  rewrite <- app_assoc in apps.
  rewrite -> app_comm_cons in apps.
  rewrite <- app_assoc in apps.
  rewrite <- app_comm_cons in apps.
  rewrite <- app_comm_cons in apps.
  inversion apps.
  reflexivity.
  trivial.
  trivial.
  assert (K : inp2 ++ las = inp3 ++ lbs).
  apply (app_ll (false :: inp1) _ (false :: inp0) _ ).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> app_comm_cons in apps.
  trivial.
  rewrite -> B.
  reflexivity.
  rewrite <- B in mbb.
  destruct (IHmba _ _ lbs K mbb) as [C D].
  rewrite -> A.
  rewrite -> B.
  rewrite -> C.
  rewrite -> D.
  auto.
Defined.

Theorem ManyBlocksStrongDec' : forall n, StrongDec (ManyBlocks n).
Proof.
  intros n_ l_.
  refine ((fix f n l m (eq : ll l <= m) {struct m} := _) n_ l_ (ll l_) _).

  destruct l as [|b l].
  apply inr.
  split.
  exact "In ManyBlocksStrongDec': input is empty."%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp mb]]]].
  destruct l'.
  inversion mb.
  inversion lapp.

  destruct (OneBlockWithPaddingStrongDec (n + 1) l) as [[a [l' [l'' [lapp obwp]]]]|[reason no]].
  destruct b.

  (* b = true : last block *)
  apply inl.
  exists a.
  exists (true :: l').
  exists l''.
  split.
  rewrite <- app_comm_cons.
  rewrite <- lapp.
  reflexivity.
  constructor.
  trivial.

  (* b = false : not last block *)
  destruct m.
  compute in eq.
  omega.
  assert (lm : ll l'' <= m).
  destruct l'.
  inversion obwp.
  assert (S(lb l') + lb l'' <= m).
  replace (S (lb l')) with (lb (b :: l')).
  rewrite <- app_length.
  rewrite <- lapp.
  compute.
  compute in eq.
  omega.
  reflexivity.
  omega.
  destruct (f (n + 1 + ll l') l'' m lm) as [[a0 [l'0 [l''0 [l''app mbx]]]]|[freason no]].
  apply inl.
  exists (a ++ a0).
  exists (false :: l' ++ l'0).
  exists l''0.
  split.
  rewrite -> lapp.
  rewrite -> l''app.
  rewrite -> app_comm_cons.
  rewrite -> app_comm_cons.
  rewrite -> app_assoc.
  reflexivity.
  constructor.
  trivial.
  trivial.

  apply inr.
  split.
  exact freason.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app mb]]]].
  inversion mb.
  rewrite <- H2 in l'app.
  inversion l'app.

  contradict no.
  exists out2.
  exists inp2.
  exists l''0.
  destruct (OneBlockWithPaddingStrongUnique (n+1) a out1 l' l'' inp1 (inp2 ++ l''0)).
  rewrite <- lapp.
  rewrite <- H3 in l'app.
  inversion l'app.
  symmetry.
  apply app_assoc.
  trivial.
  trivial.

  split.
  apply (app_ll (false :: l') _ (false :: inp1) _).
  rewrite -> app_assoc.
  rewrite -> app_comm_cons in H3.
  rewrite -> H3.
  rewrite <- l'app.
  rewrite <- app_comm_cons.
  f_equal.
  auto.
  rewrite -> H5.
  reflexivity.
  rewrite -> H5.
  trivial.

  apply inr.
  split.
  exact ("In ManyBlocksStrongDec': " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [blapp mb]]]].
  inversion mb.
  contradict no.
  exists a.
  exists inp.
  exists l''.
  split.
  apply (app_ll [b] _ [true]).
  rewrite -> app_assoc.
  replace ([true] ++ inp) with l'.
  auto.
  reflexivity.
  trivial.
  contradict no.
  exists out1.
  exists inp1.
  exists (inp2 ++ l'').
  split.
  apply (app_ll [b] _ [false]).
  rewrite -> app_assoc.
  replace ([false] ++ inp1) with (false :: inp1).
  rewrite -> app_comm_cons in H3.
  rewrite -> app_assoc.
  rewrite -> H3.
  compute.
  compute in blapp.
  trivial.
  auto.
  reflexivity.
  trivial.
  omega.
Defined.

(** TODO: trying to postpone the concatenation to the end *)
Inductive ManyBlocks' : nat -> list (SequenceWithBackRefs Byte) -> LB -> Prop :=
| lastBlock' : forall n inp out, OneBlockWithPadding out (n + 1) inp -> ManyBlocks' n [out] (true :: inp)
| middleBlock' : forall n inp1 inp2 out1 out2,
    OneBlockWithPadding out1 (n + 1) inp1 ->
    ManyBlocks' (n + 1 + ll inp1) out2 inp2 ->
    ManyBlocks' n (out1 :: out2) (false :: inp1 ++ inp2).

Lemma ManyBlocks'StrongUnique : forall n, StrongUnique (ManyBlocks' n).
Proof.
  intro n.
  apply StrongUniqueLemma.
  split.

  intros a b l mba.
  revert b.
  dependent induction mba.
  intros b mb.
  inversion mb.
  f_equal.
  apply (OneBlockWithPaddingStrongUnique (n + 1) _ _ inp [] inp [] eq_refl).
  trivial.
  trivial.

  intros b mb'.
  inversion mb'.
  destruct (OneBlockWithPaddingStrongUnique (n + 1) out1 out0 inp1 inp2 inp0 inp3) as [K1 K2].
  auto.
  trivial.
  trivial.

  rewrite -> K1.
  destruct (app_ll inp0 inp3 inp1 inp2) as [K3 K4].
  trivial.
  rewrite -> K2.
  reflexivity.

  rewrite -> (IHmba out3).
  reflexivity.
  rewrite <- K4.
  rewrite <- K3.
  trivial.

  intros a b l l' mba.
  revert l' b.
  dependent induction mba.
  intros l' b mbb.
  dependent destruction mbb.
  destruct (OneBlockWithPaddingStrongUnique (n + 1) out out0 inp l' (inp ++ l') []).
  symmetry.
  apply app_nil_r.
  trivial.
  trivial.
  destruct (app_ll inp [] inp l').
  rewrite -> app_nil_r.
  trivial.
  reflexivity.
  auto.

  intros l' b mbb.
  dependent destruction mbb.

  destruct (OneBlockWithPaddingStrongUnique (n + 1) out1 out0 inp1 (inp2 ++ l') inp0 inp3) as [O1 O2].
  rewrite -> app_assoc.
  auto.
  auto.
  auto.
  eapply IHmba.
  destruct (app_ll inp0 inp3 inp1 (inp2 ++ l')) as [N1 N2].
  rewrite -> app_assoc.
  auto.
  f_equal.
  auto.
  rewrite <- N2.
  rewrite <- N1.
  apply mbb.
Qed.

Lemma ManyBlocks'StrongDec : forall n, StrongDec (ManyBlocks' n).
Proof.
  intros n l_.
  revert n.

  refine ((fix rc l m (ml : ll l <= m) {struct m} := _) l_ (ll l_) (le_refl (ll l_))).

  intro n.

  destruct l as [|endp l].
  apply inr.
  split.
  exact ("In ManyBlocks'StrongDec: Got empty input sequence.")%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp mb']]]].
  destruct l'.
  inversion mb'.
  inversion lapp.

  destruct m.
  compute in ml.
  omega.

  destruct (OneBlockWithPaddingStrongDec (n + 1) l) as [[a [l' [l'' [lapp obwp]]]]|[reason no]].
  destruct endp.
  apply inl.
  exists [a].
  exists (true :: l').
  exists l''.
  split.
  rewrite -> lapp.
  rewrite -> app_comm_cons.
  reflexivity.
  constructor.
  exact obwp.

  assert (ml' : lb l'' <= m).
  rewrite -> lapp in ml.
  rewrite -> app_comm_cons in ml.
  rewrite -> app_length in ml.
  replace (lb (_ :: _)) with (S (lb l')) in ml.
  omega.
  reflexivity.
  destruct (rc l'' m ml' (n + 1 + ll l')) as [[a0 [l'0 [l''0 [l'app mb']]]]|[reason no]].
  apply inl.
  exists (a :: a0).
  exists (false :: l' ++ l'0).
  exists l''0.
  split.
  rewrite -> lapp.
  rewrite -> l'app.
  rewrite -> app_assoc.
  rewrite -> app_comm_cons.
  reflexivity.
  constructor.
  trivial.
  trivial.

  apply inr.
  split.
  exact reason.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [xapp xmb]]]].
  inversion xmb as [A B C D E F G| A B C D E F G H I J].

  rewrite <- G in xapp.
  inversion xapp.


  destruct (OneBlockWithPaddingStrongUnique (n + 1) a D l' l'' B (C ++ l''0)) as [K L].
  rewrite <- lapp.
  rewrite <- J in xapp.
  rewrite <- app_comm_cons in xapp.
  inversion xapp.
  symmetry.
  apply app_assoc.
  trivial.
  trivial.
  contradict no.
  exists E.
  exists C.
  exists l''0.
  split.
  apply (app_ll (false :: l') _ (false :: B) _).
  rewrite -> app_comm_cons in J.
  rewrite -> app_assoc.
  rewrite -> J.
  rewrite <- app_comm_cons.
  rewrite <- lapp.
  rewrite <- xapp.
  reflexivity.
  rewrite -> L.
  reflexivity.
  rewrite -> L.
  trivial.

  apply inr.
  split.
  exact ("In ManyBlocks'StrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp mb]]]].
  dependent destruction mb.
  contradict no.
  exists out.
  exists inp.
  exists l''.
  split.
  inversion lapp.
  reflexivity.
  trivial.
  contradict no.
  exists out1.
  exists inp1. 
  exists (inp2 ++ l'').
  split.
  rewrite <- app_comm_cons in lapp.
  rewrite -> app_assoc.
  inversion lapp.
  reflexivity.
  trivial.
Qed.

Lemma MBMBD : forall l n lb, ManyBlocks' n l lb -> ManyBlocks n (foldlist [] (@app (Byte + nat*nat)) l) lb.
Proof.
  induction l.
  intros n lb mb.
  inversion mb.
  intros n lb mb.
  inversion mb.
  constructor.
  unfold foldlist.
  rewrite -> app_nil_r.
  trivial.
  constructor.
  auto.
  apply IHl.
  auto.
Qed.

Lemma MBDMB : forall l n lb, ManyBlocks n l lb -> exists l', ManyBlocks' n l' lb.
Proof.
  intros l n lb mb.
  induction mb.
  exists [out].
  constructor.
  trivial.

  destruct IHmb as [l' mb'].
  exists (out1 :: l').
  constructor.
  trivial.
  trivial.
Qed.

Theorem ManyBlocksStrongDec : forall n, StrongDec (ManyBlocks n).
Proof.
  intros n l.
  destruct (ManyBlocks'StrongDec n l).
  apply inl.
  destruct s as [a [l' [l'' [lapp mb]]]].
  exists (foldlist [] (@app (Byte + nat*nat)) a).
  exists l'.
  exists l''.
  split.
  trivial.
  apply MBMBD.
  trivial.

  apply inr.
  destruct p as [reason no].
  split.
  exact reason.
  intro Q.
  destruct Q as [a [l' [l'' [lapp mb]]]].
  destruct (MBDMB _ _ _ mb) as [l_ H].
  contradict no.
  exists l_.
  exists l'.
  exists l''.
  split.
  apply lapp.
  auto.
Defined.

Theorem DeflateEncodesStrongUnique : StrongUnique DeflateEncodes.
Proof.
  intros a b la las lb lbs apps dea deb.
  inversion dea.
  inversion deb.
  destruct (ManyBlocksStrongUnique 0 swbr swbr0 la las lb lbs apps) as [A B].
  trivial.
  trivial.
  split.
  apply (ResolveBackReferencesUnique swbr).
  trivial.
  rewrite -> A.
  trivial.
  exact B.
Defined.

Theorem DeflateEncodesStrongDec : StrongDec DeflateEncodes.
Proof.
  intro l.
  destruct (ManyBlocksStrongDec 0 l) as [[a [l' [l'' [lapp mb]]]]|[reason no]].
  destruct (ResolveBackReferencesDec a) as [[output rbr]| no].
  apply inl.
  exists output.
  exists l'.
  exists l''.
  split.
  trivial.
  apply (deflateEncodes _ _ a mb rbr).

  apply inr.
  split.
  exact "In DeflateEncodesStrongDec: Illegal back-reference."%string.
  intro Q.
  destruct Q as [a0 [l'0 [l''0 [l'app denc]]]].
  inversion denc.
  contradict no.
  exists a0.
  destruct (ManyBlocksStrongUnique 0 a swbr l' l'' l'0 l''0) as [A B].
  rewrite <- lapp.
  trivial.
  trivial.
  trivial.
  rewrite -> A.
  trivial.

  apply inr.
  split.
  exact ("In DeflateEncodesStrongDec: " ++ reason)%string.
  intro Q.
  destruct Q as [a [l' [l'' [lapp dce]]]].
  inversion dce.
  contradict no.
  exists swbr.
  exists l'.
  exists l''.
  auto.
Defined.

(*Definition DeflateTest (l : LB) :  sum (list LB) string.
  destruct (DeflateEncodesStrongDec l) as [[o [l' [l'' ?]]]|[reason ?]].
  apply (inl (map to_list o)).
  apply (inr reason).
Defined.*)

(* TODO: This would not be necessary if we changed the definition of
strToNat in Shorthand.v, and we should do so and merge this into the
dissertation text *)

Fixpoint strToNat_' (str : string) (n : nat) : option nat :=
  match str with
    | EmptyString => Some n
    | String "0" str => strToNat_' str ((10 * n) + 0)
    | String "1" str => strToNat_' str ((10 * n) + 1)
    | String "2" str => strToNat_' str ((10 * n) + 2)
    | String "3" str => strToNat_' str ((10 * n) + 3)
    | String "4" str => strToNat_' str ((10 * n) + 4)
    | String "5" str => strToNat_' str ((10 * n) + 5)
    | String "6" str => strToNat_' str ((10 * n) + 6)
    | String "7" str => strToNat_' str ((10 * n) + 7)
    | String "8" str => strToNat_' str ((10 * n) + 8)
    | String "9" str => strToNat_' str ((10 * n) + 9)
    | _ => None
  end.

Functional Scheme strToNat_'_ind := Induction for strToNat_' Sort Prop.

Function strToNat' (str : string) := strToNat_' str 0.

Lemma strToNat__ : forall str, strToNat' str = strToNat str.
Proof.
  induction str; [reflexivity | compute; reflexivity].
Qed.

Fixpoint strToZ_ (str : string) (n : Z) : option Z :=
   match str with
     | EmptyString => Some n
     | String "0" str => strToZ_ str ((10 * n) + 0)
     | String "1" str => strToZ_ str ((10 * n) + 1)
     | String "2" str => strToZ_ str ((10 * n) + 2)
     | String "3" str => strToZ_ str ((10 * n) + 3)
     | String "4" str => strToZ_ str ((10 * n) + 4)
     | String "5" str => strToZ_ str ((10 * n) + 5)
     | String "6" str => strToZ_ str ((10 * n) + 6)
     | String "7" str => strToZ_ str ((10 * n) + 7)
     | String "8" str => strToZ_ str ((10 * n) + 8)
     | String "9" str => strToZ_ str ((10 * n) + 9)
     | _ => None
   end.

Function strToZ (strn : string) : option Z := strToZ_ strn 0.

Definition D (s : string) :=
  forceOption Z parseError (strToZ s) ParseError.

Lemma dD_ : forall (strn : string) n m, strToNat_' strn n = Some m ->
                                        Some (Z.of_nat m) = strToZ_ strn (Z.of_nat n).
Proof.
  induction strn as [|chr strn IHstrn].

  intros n m eq.
  inversion eq.
  reflexivity.

  intros n m eq.

  (* berzerk *)
  destruct chr as [b0 b1 b2 b3 b4 b5 b6 b7].
  destruct b0.
  destruct b1.
  destruct b2.
  destruct b3.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 7 *)
  assert (Q : strToZ_ (String "7" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 7)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b3.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 3 *)
  assert (Q : strToZ_ (String "3" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 3)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b2.
  destruct b3.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 5 *)
  assert (Q : strToZ_ (String "5" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 5)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b3.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 9 *)
  assert (Q : strToZ_ (String "9" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 9)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 1 *)
  assert (Q : strToZ_ (String "1" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 1)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b1.
  destruct b2.
  destruct b3.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 6 *)
  assert (Q : strToZ_ (String "6" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 6)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b3.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 2 *)
  assert (Q : strToZ_ (String "2" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 2)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b2.
  destruct b3.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 4 *)
  assert (Q : strToZ_ (String "4" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 4)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b3.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 8 *)
  assert (Q : strToZ_ (String "8" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 8)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
  destruct b4.
  destruct b5.
  destruct b6.
  inversion eq.
  destruct b7.
  inversion eq.

  (* 0 *)
  assert (Q : strToZ_ (String "0" strn) (Z.of_nat n) = strToZ_ strn (Z.of_nat (10 * n + 0)));
  [ repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | ].
  rewrite -> Q.
  apply IHstrn.
  apply eq.

  inversion eq.
  inversion eq.
Qed.

Lemma dD : forall (strn : string) n, strToNat strn = Some n -> Some (Z.of_nat n) = strToZ strn.
Proof.
  intros strn n eq.
  rewrite <- strToNat__ in eq.
  unfold strToNat' in eq.
  unfold strToZ.
  replace (0%Z) with (Z.of_nat 0); [ | reflexivity].

  apply dD_.
  trivial.
Qed.

Definition distCodeBase' :=
  [ D"1"     ; D"2"     ; D"3"     ; D"4"     ;
    D"5"     ; D"7"     ; D"9"     ; D"13"    ;
    D"17"    ; D"25"    ; D"33"    ; D"49"    ;
    D"65"    ; D"97"    ; D"129"   ; D"193"   ;
    D"257"   ; D"385"   ; D"513"   ; D"769"   ;
    D"1025"  ; D"1537"  ; D"2049"  ; D"3073"  ;
    D"4097"  ; D"6145"  ; D"8193"  ; D"12289" ;
    D"16385" ; D"24577" ].

Definition distCodeMax' :=
  [ D"1"     ; D"2"     ; D"3"     ; D"4"     ;
    D"6"     ; D"8"     ; D"12"    ; D"16"    ;
    D"24"    ; D"32"    ; D"48"    ; D"64"    ;
    D"96"    ; D"128"   ; D"192"   ; D"256"   ;
    D"384"   ; D"512"   ; D"768"   ; D"1024"  ;
    D"1536"  ; D"2048"  ; D"3072"  ; D"4096"  ;
    D"6144"  ; D"8192"  ; D"12288" ; D"16384" ;
    D"24576" ; D"32768" ].

Lemma distCodeBase'correct : map Z.of_nat distCodeBase = distCodeBase'.
Proof.
  unfold distCodeBase.
  unfold map.
  unfold d.
  unfold forceOption.
  unfold strToNat.

  repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul).
  reflexivity.
Qed.

Lemma distCodeMax'correct : map Z.of_nat distCodeMax = distCodeMax'.
Proof.
  unfold distCodeMax.
  unfold map.
  unfold d.
  unfold forceOption.
  unfold strToNat.

  repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul).
  reflexivity.
Qed.

Lemma LitLenBounded : forall litlen l lbits,
                        CompressedLength litlen l lbits -> 3 <= l <= 258.
Proof.
  intros litlen l lbits cl.
  inversion cl as [A B C D E F G H I J K L M N O P].
  unfold repeatCodeBase in J.
  unfold repeatCodeMax in K.

  repeat (destruct C as [|C];
          [ compute in J;
            compute in K;
            inversion J;
            inversion K;
            abstract omega |
            (solve [inversion J] || idtac)]).
Qed.

(* TODO: Woanders. *)
Function oapp {A B} (f : A -> B) (g : option A) := match g with | None => None | Some a => Some (f a) end.

Lemma nth_error_oapp : forall {A B} (f : A -> B) n l, oapp f (nth_error l n) = nth_error (map f l) n.
Proof.
  intros A B f n l.
  revert f n.
  induction l.
  intros f n.
  destruct n; reflexivity.
  intros f n.
  destruct n.
  reflexivity.
  apply IHl.
Qed.

Lemma DistBounded : forall denc dist dbits,
                      CompressedDist denc dist dbits -> 1 <= dist <= d "32768".
Proof.
  intros denc dist dbits cd.
  inversion cd as [A B C D_ E F G H I J K L M N O P].
  assert (B0 : (Z.of_nat B >= 0)%Z).
  omega.

  assert (Cb : oapp Z.of_nat (nth_error distCodeBase C) = nth_error distCodeBase' C).
  rewrite <- distCodeBase'correct.
  apply nth_error_oapp.

  rewrite -> J in Cb.
  simpl in Cb.
  
  assert (Cm : oapp Z.of_nat (nth_error distCodeMax C) = nth_error distCodeMax' C).
  rewrite <- distCodeMax'correct.
  apply nth_error_oapp.

  rewrite -> K in Cm.
  simpl in Cm.

  assert (Max : Z.of_nat (d "32768") = D "32768"%string).
  unfold d.
  unfold D.
  unfold forceOption.
  unfold strToNat.
  unfold strToZ.
  unfold strToZ_.
  repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul).
  reflexivity.

  assert (1%Z <= (Z.of_nat A) + (Z.of_nat B) <= Z.of_nat (d "32768"))%Z.
  rewrite -> Max.

  repeat (destruct C as [|C];
         [ inversion Cb as [Cb_];
           rewrite -> Cb_;
           inversion Cm as [Cm_];
           unfold D in Cm_;
           unfold forceOption in Cm_;
           unfold strToZ in Cm_;
           unfold strToZ_ in Cm_;
           unfold D;
           unfold forceOption;
           unfold strToZ;
           unfold strToZ_;
           abstract omega | ]).

  destruct C as [|C].
  inversion Cm as [Cm_].  
  assert (D "24576" <= D "32768")%Z; [intro Q; inversion Q|].
  assert (Z.of_nat A + Z.of_nat B <= Z.of_nat D_)%Z.
  omega.
  split.
  inversion Cb as [Cb_].
  rewrite -> Cb_.
  assert (1 <= D "16385")%Z; [intro Q; inversion Q|].
  omega.
  omega.

  destruct C as [|C].
  inversion Cm as [Cm_].
  split.
  inversion Cb as [Cb_].
  rewrite -> Cb_.
  assert (1 <= D "24577")%Z; [intro Q; inversion Q|].
  omega.
  omega.

  destruct C as [|C].
  inversion Cm as [Cm_].
  inversion Cm.
  omega.
Qed.

Lemma CompressedSwbrBounded : forall litlen dist swbr l,
                                CompressedSWBR litlen dist swbr l ->
                                BackRefsBounded 3 258 1 (d"32768") swbr.
Proof.
  intros litlen dist.

  induction swbr.
  intros.
  constructor.

  intros l cswbr.
  destruct a as [a | [a b]].
  constructor.
  constructor.
  inversion cswbr as [|? l2 ? ? ? R|].
  apply (IHswbr l2).
  exact R.

  constructor.
  inversion cswbr.

  match goal with
    | K : CompressedDist _ _ _ |- _ => apply DistBounded in K
  end.
  match goal with
    | K : CompressedLength _ _ _ |- _ => apply LitLenBounded in K
  end.
  constructor; omega.
  inversion cswbr.
  eapply IHswbr.
  match goal with
    | K : CompressedSWBR _ _ swbr _ |- _ => exact K
  end.
Qed.

Lemma DynamicallyCompressedBlockBounded
: forall swbr l, DynamicallyCompressedBlock swbr l ->
                 BackRefsBounded 3 258 1 (d"32768") swbr.
Proof.
  intros swbr l dcb.
  inversion dcb.
  match goal with
    | K : pi2 _ _ = swbr |- _ => compute in K; rewrite <- K
  end.
  eapply CompressedSwbrBounded.
  eauto.
Qed.

Lemma StaticallyCompressedBlockBounded
: forall swbr l, StaticallyCompressedBlock swbr l ->
                 BackRefsBounded 3 258 1 (d"32768") swbr.
Proof.
  intros swbr l scb.
  inversion scb.
  eapply CompressedSwbrBounded.
  eauto.
Qed.

Lemma nBytesDirectBounded : forall n l swbr, nBytesDirect n swbr l -> 
                                             BackRefsBounded 3 258 1 (d"32768") swbr.
Proof.
  (********************)
  induction n.
  intros l swbr nbd.
  inversion nbd as [A B].
  rewrite -> A.
  constructor.

  intros l swbr nbd.
  inversion nbd as [k t c d A].
  
  
  inversion A.
  constructor.
  constructor.
  eapply IHn.
  eauto.
Qed.

Lemma UncompressedBlockDirectBounded
: forall swbr l, UncompressedBlockDirect swbr l -> BackRefsBounded 3 258 1 (d"32768") swbr.
Proof.
  intros swbr l ucb.
  inversion ucb.
  match goal with
    | K : pi2 _ _ = swbr |- _ => compute in K; rewrite <- K
  end.

  match goal with
    | K : ((readBitsLSB 16) >>= _) _ _ |- _ => inversion K
  end.

  match goal with
    | K : _ /\ nBytesDirect _ ?A _,
      L : pi2 _ ?A = _ |- _ =>
      destruct K as [K1 K2];
        eapply nBytesDirectBounded;
        compute in L; rewrite <- L; eauto
  end.
Qed.

Lemma OneBlockWithPaddingBounded
: forall swbr n l, OneBlockWithPadding swbr n l ->
                   BackRefsBounded 3 258 1 (d"32768") swbr.
Proof.
  intros swbr n l obwp.
  inversion obwp.
  eapply DynamicallyCompressedBlockBounded.
  eauto.
  eapply StaticallyCompressedBlockBounded.
  eauto.
  eapply UncompressedBlockDirectBounded.
  eauto.
Qed.

Lemma ManyBlocksBounded : forall n swbr l,
                            ManyBlocks n swbr l ->
                            BackRefsBounded 3 258 1 (d"32768") swbr.
Proof.
  intros n swbr l mb.
  induction mb.
  eapply OneBlockWithPaddingBounded.
  eauto.
  apply app_forall.
  eapply OneBlockWithPaddingBounded.
  eauto.
  auto.
Qed.