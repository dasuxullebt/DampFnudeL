Require Import Program.
Require Import ZArith.
Require Import List.
Import ListNotations.

Require Import Shorthand.
Require Import Combi.
Require Import Repeat.
Require Import Pheap.
Require Import Backreferences.
Require Import LSB.
 
Function natcmp n m := match nat_compare n m with
                           | Gt => false
                           | _ => true
                       end.

Lemma natcmp_le : forall n m, natcmp n m = true <-> n <= m.
Proof.
  intros n m.
  split.

  unfold natcmp.
  destruct (nat_compare n m) eqn:ncm.
  apply nat_compare_eq_iff in ncm.
  omega.
  apply nat_compare_lt in ncm.
  omega.
  intro Q; inversion Q.
  intro nm.
  unfold natcmp.
  destruct (nat_compare n m) eqn:ncm.
  auto.
  auto.
  apply nat_compare_gt in ncm.
  omega.
Qed.

Lemma natcmp_cmp : cmp_ordering natcmp.
Proof.
  split.
  intro a.
  apply natcmp_le.
  omega.

  split.
  intros a b c A B.
  apply natcmp_le in A.
  apply natcmp_le in B.
  apply natcmp_le.
  omega.

  split.
  intros a b A B.
  apply natcmp_le in A.
  apply natcmp_le in B.
  omega.

  intros a b.
  assert (A : a <= b \/ b <= a).
  omega.
  destruct A as [B | B];
    apply natcmp_le in B;
    auto.
Qed.

Definition NatPairCmp := LexCmp natcmp natcmp.

Lemma NatPairCmp_cmp : cmp_ordering NatPairCmp.
Proof.
  apply LexOrd; apply natcmp_cmp.
Qed.

Fixpoint ReadAhead {A : Set} (n maxdist : nat) (swbr : SequenceWithBackRefs A) (php : pheap (nat * nat)) :=
  match maxdist with
    | 0 => (swbr, php)
    | (S m) => match swbr with
                 | [] => (swbr, php)
                 | inl _ :: r => ReadAhead (S n) m r php
                 | inr (_, d) :: r => ReadAhead (S n) m r (insert NatPairCmp (n - d, n) php)
               end
  end.

Fixpoint SlowResolveBRB (n : nat) (rev_done : LByte) (todo : SequenceWithBackRefs Byte) :=
  match todo with
    | [] => Some (rev rev_done)
    | inl b :: r => SlowResolveBRB (S n) (b :: rev_done) r
    | inr (_, d) :: r =>
      match nth_error rev_done (d - 1) with
        | None => None
        | Some rd =>  SlowResolveBRB (S n) (rd :: rev_done) r
      end
  end.

Lemma SlowResolveBRBCorrect_2 :
  forall n m todo1 todo2 rd,
    SlowResolveBRB n rd todo1 = None ->
    SlowResolveBRB m rd (todo1 ++ todo2) = None.
Proof.
  intros n m todo1.
  revert todo1 n m.
  induction todo1 as [|t1 todo1 IHt1].
  intros n m todo2 rd brbn.
  inversion brbn.
  intros n m todo2 rd brb1.
  rewrite <- app_comm_cons.
  simpl.
  simpl in brb1.
  destruct t1.
  eapply IHt1.
  eauto.

  destruct p.
  destruct (nth_error rd (n1 - 1)) eqn:nerr.
  eapply IHt1.
  eauto.
  reflexivity.
Qed.

Lemma SlowResolveBRBCorrect_1 :
  forall n rd todo1 todo2 k,
    SlowResolveBRB n rd todo1 = Some k ->
    SlowResolveBRB n rd (todo1 ++ todo2) =
    SlowResolveBRB (n + ll todo1) (rev k) todo2.
Proof.
  intros n rd todo1.
  revert n rd.
  induction todo1 as [|t todo1 IHtodo1].

  intros n rd todo2 k H.
  simpl in H.
  inversion H.
  rewrite -> rev_involutive.
  simpl.
  replace (n + 0) with n.
  reflexivity.
  omega.

  intros n rd todo2 k somek.
  destruct t as [t | [l d]].
  simpl in somek.
  simpl.
  replace (n + S (ll todo1)) with ((S n) + ll todo1); [ | omega].
  apply IHtodo1.
  exact somek.

  simpl in somek.
  simpl.
  destruct (nth_error rd (d-1)) eqn:nerr.
  replace (n + S (ll todo1)) with ((S n) + ll todo1); [ | omega].
  apply IHtodo1.
  exact somek.
  inversion somek.
Qed.

Lemma SlowResolveBRBCorrect :
  forall mnd mxd inp out,
    mnd > 0 ->
    BackRefsBounded 1 1 mnd mxd inp ->
    (ResolveBackReferences inp out <-> SlowResolveBRB 0 [] inp = Some out).
Proof.
  intros mnd mxd inp out mndz brb.
  split.

  revert inp out brb.
  apply (rev_ind (fun inp => forall (out : LByte),
                               BackRefsBounded 1 1 mnd mxd inp ->
                               ResolveBackReferences inp out -> SlowResolveBRB 0 [] inp = Some out));
    [ intros out brb rbrs;
      inversion rbrs as [|A B C D E F|A B C D E F G H I];
      [ reflexivity
      | destruct A; inversion E
      | destruct A; inversion H ]
    |].

intros x l IH out brb rbr.
inversion rbr;
[reflexivity
| rewrite -> (SlowResolveBRBCorrect_1 _ _ _ _ b);
  [ simpl;
    rewrite -> rev_involutive;
    reflexivity
  | assert (al : a = l);
    [ eapply (app_inj_tail a l);
      eauto
    | rewrite -> al;
      apply IH;
      [ apply forall_app in brb;
        firstorder
      | rewrite <- al;
        trivial ]]]
 | ].

 rewrite -> (SlowResolveBRBCorrect_1 _ _ _ _ b).

 destruct (nth_error (rev b) (dist - 1)) eqn:nerr.
 simpl.
 rewrite -> nerr.
 rewrite -> rev_involutive.
 match goal with
   | H : a ++ [inr (len, dist)] = l ++ [x] |- _ =>
     apply app_inj_tail in H; destruct H as [al xld]
 end.

 (* TODO: less sloppy here. NAMES!!!1! *)

 assert (len1 : len = 1).
 rewrite <- xld in brb.
 apply forall_app in brb.
 destruct brb as [brb1 brb2].
 inversion brb2.
 inversion H4.
 omega.

 rewrite -> len1 in H1.
 inversion H1.
 inversion H3.
 f_equal.
 f_equal.
 f_equal.

 assert (E : dist - 1 < ll output1).
 inversion H4.
 rewrite -> app_length.
 simpl.
 omega.
 eapply nthLastNth in H4.
 eapply nth_error_nth in nerr.
 rewrite -> H11 in nerr.
 rewrite -> rev_nth in nerr.
 assert (dist >= 1).
 rewrite <- xld in brb.
 apply forall_app in brb.
 destruct brb as [brb1 brb2].
 inversion brb2.
 inversion H13.
 omega.
 replace (ll output1 - S (dist - 1)) with (ll output1 - dist) in nerr; [ | omega].
 rewrite <- nerr.
 rewrite <- H4.
 reflexivity.
 exact E.



 apply app_inj_tail in H.
 destruct H as [al xld].
 assert (len1 : len = 1).
 rewrite <- xld in brb.
 apply forall_app in brb.
 destruct brb as [brb1 brb2].
 inversion brb2.
 inversion H4.
 omega.

 rewrite -> len1 in H1.
 inversion H1 as [|A B C D E F G H I J K].
 inversion F.
 inversion G.
 rewrite -> H6 in nerr.
 rewrite <- H7 in nerr.
 rewrite -> rev_app_distr in nerr.
 rewrite <- nth_extend in nerr.
 simpl in nerr.
 simpl in H3.
 rewrite <- H3 in nerr.
 rewrite <- rev_length in nerr.
 replace (S (ll (rev M)) - 1) with (ll (rev M)) in nerr; [|omega].
 erewrite -> (proj2 (nth_split _ _ _) _) in nerr.
 inversion nerr.

 rewrite -> rev_length.
 simpl.
 simpl in H3.
 omega.

 apply app_inj_tail in H.
 destruct H as [K1 K2].
 rewrite -> K1.
 apply IH.
 apply forall_app in brb.
 firstorder.
 rewrite <- K1.
 trivial.

 (* phew. first direction. now second one. *)
  revert inp out brb.
  apply (rev_ind
           (fun inp => forall (out : LByte),
                         BackRefsBounded 1 1 mnd mxd inp ->
                         SlowResolveBRB 0 [] inp = Some out -> ResolveBackReferences inp out));
  [ intros ? ? sr;
    inversion sr;
    constructor
  | ].

  intros x l IH out brb srb.
  destruct (SlowResolveBRB 0 [] l) as [|] eqn:srbq.
  erewrite -> SlowResolveBRBCorrect_1 in srb.

  destruct x as [c | [len dist]]; [ | ].
  simpl in srb.
  rewrite -> rev_involutive in srb.
  inversion srb.
  constructor.
  apply IH.
  apply forall_app in brb.
  firstorder.
  reflexivity.
  destruct (nth_error (rev l0) (dist -1)) as [|] eqn:nerr.
  simpl in srb.
  rewrite -> nerr in srb.
  rewrite -> rev_involutive in srb.
  inversion srb.
  econstructor.
  apply IH.
  apply forall_app in brb.
  firstorder.
  reflexivity.

  assert (len1dist1 : len = 1 /\ dist > 0).
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  inversion brb2 as [|A B C D [E F]].
  inversion C.
  omega.

  rewrite -> (proj1 len1dist1).
  constructor.
  constructor.
  destruct dist.
  omega.
  eapply nthNthLast.
  apply nth_split in nerr.
  destruct nerr as [l' [l'' [l'dist rl0app]]].
  assert (LL : ll l0 = ll (l' ++ [t] ++ l'')).
  rewrite <- rev_length.
  f_equal.
  exact rl0app.
  rewrite -> LL.
  rewrite -> app_length.
  simpl.
  omega.
  rewrite <- rev_nth.
  apply nth_error_nth.
  replace dist with (S dist - 1); [ | omega].
  trivial.
  rewrite <- rev_length.
  eapply nth_error_lt.
  replace dist with (S dist - 1); [ | omega].
  eauto.

  simpl in srb.
  rewrite -> nerr in srb.
  inversion srb.

  trivial.

  eapply SlowResolveBRBCorrect_2 in srbq.
  erewrite -> srbq in srb.
  inversion srb.

Grab Existential Variables.
apply NullByte.
exists (rev M) (@nil Byte).
rewrite -> app_nil_r.
split; reflexivity.
apply NullByte.
Qed.

Record CopyPosition : Set :=
  mkCopyPosition {
      source : nat;
      sdestination : nat
    }.

Function CPpair a := (source a, sdestination a).

(** Boilerplate ... *)
Function CPunpair a := {| source := fst a; sdestination := snd a |}.

Lemma CPpair_inj : forall x, CPpair (CPunpair x) = x.
Proof.
  intros.
  destruct x.
  compute.
  reflexivity.
Qed.

Lemma CPunpair_inj : forall x, CPunpair (CPpair x) = x.
Proof.
  intros.
  destruct x.
  compute.
  reflexivity.
Qed.

Function CPcmp a b := (LexCmp natcmp natcmp) (CPpair a) (CPpair b).

Lemma cmpCPcmp : cmp_ordering CPcmp.
Proof.
  split.
  intro a.
  apply NatPairCmp_cmp.
  split.
  intros a b c.
  apply NatPairCmp_cmp.
  split.
  intros a b.
  unfold CPcmp.
  intros A B.
  assert (cpx : CPpair a = CPpair b).
  apply NatPairCmp_cmp; auto.
  replace a with (CPunpair (CPpair a)).
  replace b with (CPunpair (CPpair b)).
  f_equal.
  exact cpx.
  apply CPunpair_inj.
  apply CPunpair_inj.

  intros a b.
  apply NatPairCmp_cmp.
Qed.

Record BufferedCopy : Set :=
  mkBufferedCopy {
      cdestination : nat;
      content : Byte
   }.

Function BCpair a := (cdestination a, ByteToNat (content a)).

Lemma BCpair_inj : forall a b, BCpair a = BCpair b -> a = b.
Proof.
  intros [a1 a2] [b1 b2].
  unfold BCpair.
  simpl.
  intro Q.
  inversion Q as [[Q1 Q2]].
  apply ByteToNat_inj in Q2.
  rewrite -> Q2.
  reflexivity.
Qed.

Function BCcmp a b := (LexCmp natcmp natcmp) (BCpair a) (BCpair b).

Lemma cmpBCcmp : cmp_ordering BCcmp.
Proof.
  split.
  intro a.
  apply NatPairCmp_cmp.


  split.
  intros a b c.
  apply NatPairCmp_cmp.

  split.
  intros a b A B.
  apply BCpair_inj.
  apply NatPairCmp_cmp.
  auto.
  auto.

  intros a b.
  apply NatPairCmp_cmp.
Qed.  

(** collect all destinations of current/given source *)

Lemma collectN : forall n (cp1 : pheap CopyPosition),
                   pheap_correct CPcmp cp1 ->
                   (forall x, pheap_in x cp1 -> source x >= n) ->
                   { l : list nat &
                   { cp2 : pheap CopyPosition |
                     pheap_correct CPcmp cp2 /\
                     (forall x, pheap_in x cp2 <-> (source x > n /\ pheap_in x cp1)) /\
                     (forall d, pheap_in {| source := n; sdestination := d |} cp1 <-> In d l) }}.
Proof.
  intros n cp1.
  refine ((fix f cp_ (acc : Acc (fun b a => delete_min CPcmp a = Some b) cp_) {struct acc} :
             pheap_correct CPcmp cp_ ->
             (forall x : CopyPosition, pheap_in x cp_ -> source x >= n) ->
             {l : list nat &
             {cp2 : pheap CopyPosition |
              pheap_correct CPcmp cp2 /\
              (forall x : CopyPosition,
                 pheap_in x cp2 <-> source x > n /\ pheap_in x cp_) /\
              (forall d : nat,
                 pheap_in {| source := n; sdestination := d |} cp_ <-> In d l)}} :=
             match find_min cp_ as fm return (fm = find_min cp_ -> _) with
               | None => fun eqFM => _ (* case 1 *)
               | Some {| source := src; sdestination := dst |} =>
                 fun eqFM =>
                   match delete_min CPcmp cp_ as dm return (dm = delete_min CPcmp cp_ -> _) with
                     | None => fun eqDM => _ (* case 2 (absurd) *)
                     | Some cp_2 =>
                       fun eqDM =>
                         match nat_compare src n as N return (nat_compare src n = N -> _) with
                           | Eq => fun eqN => _ (* case 3 *)
                           | Lt => fun eqN => _ (* case 4 (absurd) *)
                           | Gt => fun eqN => _ (* case 5 *)
                         end eq_refl
                   end eq_refl
             end eq_refl) cp1 (wf_deletemin _ _));
    [ (* case 3 *)
      intros correct_cp_ in_ge_n;
      assert (recstep : {l : list nat &
                                  {cp2 : pheap CopyPosition |
                                   pheap_correct CPcmp cp2 /\
                                   (forall x : CopyPosition,
                                      pheap_in x cp2 <-> source x > n /\ pheap_in x cp_2) /\
                                   (forall d : nat,
                                      pheap_in {| source := n; sdestination := d |} cp_2 <-> In d l)}});
        [ apply f;
          [ apply acc; symmetry; trivial
          | eapply delete_min_correct;
            [ apply cmpCPcmp
            | apply correct_cp_
            | exact eqDM ]
          | intros x xpi;
            apply in_ge_n;
            eapply pheap_in_weaken;
            [ exact cmpCPcmp
            | exact correct_cp_
            | exact eqDM
            | exact xpi ]]
        | destruct recstep as [l [cp2 [corr_cp2 [in_cond_1 in_cond_2]]]];
          exists (dst :: l);
          exists cp2;
          split;
          [ trivial
          | split;
            [ intros x;
              split;
              [ intro phi;
                split;
                [ apply in_cond_1;
                  exact phi
                | eapply pheap_in_weaken;
                  [ apply cmpCPcmp
                  | exact correct_cp_
                  | exact eqDM
                  | apply in_cond_1;
                    exact phi ]]
              | intros [x_gt_n ph_x_cp];
                apply in_cond_1;
                split;
                [exact x_gt_n
                | destruct (delete_min_spec_1 CPcmp cp_2 cp_ cmpCPcmp correct_cp_ eqDM x ph_x_cp) as [t | t];
                  [ exact t
                  | rewrite <- eqFM in t;
                    inversion t as [T];
                    rewrite -> T in x_gt_n;
                    simpl in x_gt_n;
                    apply nat_compare_eq_iff in eqN;
                    omega ]]]
            | intros d;
              split;
              [ intros phi;
                destruct (delete_min_spec_1 CPcmp cp_2 cp_ cmpCPcmp correct_cp_ eqDM _ phi) as [t | t];
                [ constructor 2;
                  apply in_cond_2;
                  exact t
                | rewrite <- eqFM in t;
                  inversion t;
                  constructor;
                  reflexivity ]
              | intros ind;
                inversion ind as [X | X];
                [ rewrite <- X;
                  apply nat_compare_eq_iff in eqN;
                  rewrite <- eqN;
                  destruct cp_;
                  [ inversion eqFM
                  | inversion eqFM;
                    constructor ]
                | eapply pheap_in_weaken;
                  [ apply cmpCPcmp
                  | exact correct_cp_
                  | exact eqDM
                  | apply in_cond_2;
                    exact X ]]]]]]
    | (* case 4 *)
      apply nat_compare_lt in eqN;
      intros ? ltn;
      contradict eqN;
      destruct cp_;
      [ inversion eqFM
      | inversion eqFM as [eqFM_];
        rewrite <- eqFM_ in ltn;
        assert (src >= n);
        [ apply (ltn {| source := src; sdestination := dst |});
          constructor
        | omega ]]
    | (* case 5 *)
      intros corr phi;
      apply nat_compare_gt in eqN;
      exists (@nil nat);
      exists cp_;
      split;
        [ exact corr
        | split;
          [ intro x;
            split;
            [ intro phi2;
              split;
              [ destruct (find_min_spec x CPcmp cp_ cmpCPcmp corr phi2) as [a [fma cmpa]];
                rewrite <- eqFM in fma;
                inversion fma as [fma_];
                rewrite -> fma_ in cmpa;
                destruct x as [xs xd];
                simpl;
                unfold CPcmp in cmpa;
                unfold CPpair in cmpa;
                simpl in cmpa;
                destruct (nat_compare src xs) eqn:nc;
                [ apply nat_compare_eq_iff in nc;
                  omega
                | apply nat_compare_lt in nc;
                  omega
                | unfold LexCmp in cmpa;
                  simpl in cmpa;
                  unfold natcmp in cmpa;
                  rewrite -> nc in cmpa;
                  inversion cmpa ]
              | exact phi2]
            | firstorder ]
          | intro d;
            split;
            [ intro phi2;
              destruct (find_min_spec _ CPcmp cp_ cmpCPcmp corr phi2) as [a [fma cmpa]];
              rewrite <- eqFM in fma;
              inversion fma as [fma_];
              rewrite -> fma_ in cmpa;
              unfold CPcmp in cmpa;
              unfold CPpair in cmpa;
              simpl in cmpa;
              unfold LexCmp in cmpa;
              unfold natcmp in cmpa;
              simpl in cmpa;
              apply nat_compare_gt in eqN;
              rewrite -> eqN in cmpa;
              inversion cmpa
            | intro Q;
              inversion Q ]]]
      | (* case 2 *)
        destruct cp_;
        [ inversion eqFM | inversion eqDM ]
      | (* case 1 *)
        destruct cp_;
        [ intros;
          exists (@nil nat);
          exists (@Empty CopyPosition);
          split;
          [ constructor
          | split;
            [ intros;
              split;
              [ intro Q; inversion Q
              | intros [? Q]; inversion Q ]
            | intros;
              split; intro Q; inversion Q ]]
        | inversion eqFM]].
Defined.

Lemma addN : forall (b : Byte) (l : list nat) (bc1 : pheap BufferedCopy),
               pheap_correct BCcmp bc1 ->
               {bc2 : pheap BufferedCopy |
                pheap_correct BCcmp bc2 /\
                (forall x, pheap_in x bc2 <-> (pheap_in x bc1 \/
                                               (In (cdestination x) l /\ content x = b)))}.
Proof.
  intro b.
  induction l as [|d l IHl].
  intros bc1 pc1.
  exists bc1.
  split.
  trivial.
  intro x.
  split.
  firstorder.
  intros [phi | [Q ?]].
  trivial.
  inversion Q.
  intros bc1 pc1.
  destruct (IHl bc1) as [bc2 [corr allx]].
  trivial.
  exists (insert BCcmp {| content := b; cdestination := d |} bc2).
  split.
  apply insert_correct.
  apply cmpBCcmp.
  exact corr.
  intro x.
  split.
  intro inins.
  apply insert_spec in inins.
  destruct inins as [xeq | xin].
  apply or_intror.
  split.
  constructor.
  rewrite -> xeq.
  reflexivity.
  rewrite -> xeq.
  reflexivity.
  apply allx in xin.
  destruct xin as [xin | [xl xc]].
  auto.
  apply or_intror.
  split.
  constructor 2.
  exact xl.
  exact xc.
  apply cmpBCcmp.

  intro k.
  apply insert_spec.
  apply cmpBCcmp.
  destruct k as [k | [k1 k2]].
  apply or_intror.
  apply allx.
  auto.

  inversion k1 as [k3 | k3].
  apply or_introl.
  destruct x.
  rewrite -> k3.
  rewrite <- k2.
  reflexivity.

  apply or_intror.
  apply allx.
  apply or_intror.
  auto.
Defined.

Lemma addContentL : forall n b (cp1 : pheap CopyPosition) (bc1 : pheap BufferedCopy),
                      pheap_correct CPcmp cp1 ->
                      pheap_correct BCcmp bc1 ->
                      (forall x, pheap_in x cp1 -> source x >= n) ->
                      {cp2 : pheap CopyPosition &
                      {bc2 : pheap BufferedCopy |
                       pheap_correct CPcmp cp2 /\
                       pheap_correct BCcmp bc2 /\
                       (forall x, pheap_in x cp2 <-> (source x > n /\ pheap_in x cp1)) /\
                       (forall x, pheap_in x bc2 <-> (pheap_in x bc1 \/
                                                      (pheap_in {| sdestination := cdestination x;
                                                                   source := n |} cp1 /\
                                                       content x = b)))}}.
Proof.
  intros n b cp1 bc1 corrc corrb nle.
  destruct (collectN n cp1 corrc nle) as [l [cp2 [corrc2 [inc2 dl]]]].
  destruct (addN b l bc1 corrb) as [bc2 [corrb2 inb2]].
  exists cp2.
  exists bc2.
  split.
  trivial.
  split.
  trivial.
  split.
  trivial.
  intro x.
  split.
  intro phi.
  apply inb2 in phi.
  destruct phi as [phi | [phi1 phi2]].
  auto.
  apply or_intror.
  split.
  apply dl.
  trivial.
  trivial.
  intro phi.
  apply inb2.
  destruct phi as [phi | [phi1 phi2]].
  auto.
  apply or_intror.
  split.
  apply dl.
  trivial.
  trivial.
Qed.

Function proceed_read_ahead (m : nat) (ra : pheap CopyPosition) (todo : SequenceWithBackRefs Byte) :=
  match todo with
    | [] => Some (S m, ra, [])
    | inl _ :: r => Some (S m, ra, r)
    | inr (_, d) :: r => match nat_compare d m with
                           | Lt =>
                             Some (S m, insert CPcmp (mkCopyPosition m (m - d)) ra, r)
                           | _ => None
                         end
  end.

Fixpoint prepare_read_ahead_ (maxdist m : nat) (ra : pheap CopyPosition) (todo : SequenceWithBackRefs Byte) :=
  match maxdist with
    | 0 => Some (m, ra, todo)
    | (S md) => match proceed_read_ahead m ra todo with
                  | None => None
                  | Some (m_, ra_, todo_) =>
                    prepare_read_ahead_ md m_ ra_ todo_
                end
  end.

Function prepare_read_ahead maxdist todo := prepare_read_ahead_ maxdist 0 Empty todo.

Require Import String.
Fixpoint take_ {A} (n : nat) (l : list A) :=
  match n with
    | 0 => []
    | S n_ => match l with
                | [] => []
                | x :: l_ => x :: take_ n_ l_
              end
  end.

Fixpoint drop_ {A} (n : nat) (l : list A) :=
  match n with
    | 0 => l
    | S n_ => match l with
                | [] => []
                | x :: l_ => drop_ n_ l_
              end
  end.

Lemma drop_nnil_length : forall {A} (k : A) l m n,
                           k :: l = drop_ n m ->
                           ll m > n.
Proof.
  intros A k l m n.
  revert l m n k.
  induction l as [|ly l IHl].

  induction m as [|my m IHm].
  intros ? ? dr; destruct n; inversion dr.

  intros n k dr.
  destruct n as [|n].
  simpl; omega.
  simpl.
  assert (ll m > n).
  eapply IHm.
  exact dr.
  omega.

  induction m as [|my m IHm].
  intros ? ? q; destruct n; inversion q.
  intros n k dr.
  destruct n as [|n].
  simpl; omega.
  assert (ll m > n).
  eapply IHm.
  exact dr.
  simpl; omega.
Qed.

Lemma take_length : forall {A} (l : list A) n,
                      ll l > n -> ll (take_ n l) = n.
Proof.
  intros A.
  induction l as [|ly l IHl].
  intros ? Q; simpl in Q; omega.
  intros n dr.
  destruct n.
  simpl; reflexivity.
  simpl.
  assert (ll (take_ n l) = n).
  apply IHl.
  simpl in dr; omega.
  omega.
Qed.

Lemma takedrop_lemma : forall {A} (l : list A) n, l = take_ n l ++ drop_ n l.
Proof.
  intro A.
  induction l as [|a l IHl].
  destruct n; reflexivity.

  destruct n as [|n].
  reflexivity.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.

Lemma drop_single : forall {A} (k l : list A) a n, a :: l = drop_ n k -> l = drop_ (S n) k.
Proof.
  intros A k l a n.
  revert k n l a.
  induction k as [|x k IHk].
  intro n.
  destruct n.
  intros l a Q.
  inversion Q.
  intros l a Q.
  inversion Q.

  intros n l a eq.
  simpl.
  destruct n.
  inversion eq.
  reflexivity.

  eapply IHk.
  simpl in eq.
  exact eq.
Qed.

Lemma drop_nth_error : forall {A} (b : A) l m n, b :: l = drop_ n m -> nth_error m n = Some b.
Proof.
  intros A b l m n.
  revert l n m b.
  induction l as [|ly l IHl].
  intros n m.
  revert n.
  induction m as [|my m IHm].
  intros n b q.
  destruct n; inversion q.
  intros n b q.
  destruct n as [|n].
  inversion q.
  reflexivity.
  simpl.
  apply IHm.
  exact q.

  intros n m.
  revert n.
  induction m as [|my m IHm].
  intros n b q.
  destruct n; inversion q.
  intros n b q.
  destruct n as [|n].
  inversion q.
  reflexivity.
  simpl.
  apply IHm.
  exact q.
Qed.  

Definition pointsTo {A} (input : SequenceWithBackRefs A) (src dst : nat) :=
  src < dst /\ nth_error input dst = Some (inr (1, dst - src)).

Lemma pointsTo_bound
: forall {A} (input : SequenceWithBackRefs A) src dst,
    pointsTo input src dst -> dst < ll input.
Proof.
  intros A input src dst [p0 p1].
  eapply nth_error_lt.
  exact p1.
Qed.

Lemma pointsTo_dst_unique
: forall {A} (input : SequenceWithBackRefs A) (src1 src2 dst : nat),
    pointsTo input src1 dst -> pointsTo input src2 dst -> src1 = src2.
Proof.
  intros A input src1 src2 dst pto1 pto2.
  destruct pto1 as [pto1a pto1b].
  destruct pto2 as [pto2a pto2b].
  rewrite -> pto2b in pto1b.
  inversion pto1b.
  omega.
Qed.

Lemma drop_nil : forall {A} m (l : list A), [] = drop_ m l -> m >= ll l.
Proof.
  intros A.
  induction m.
  intro l.
  simpl.
  intro lx.
  rewrite <- lx.
  simpl.
  omega.

  intro l.
  destruct l as [|x l].
  simpl.
  omega.
  simpl.
  intro lx.
  apply IHm in lx.
  omega.
Qed.


Lemma nth_error_last : forall {A} l (x : A), nth_error (l ++ [x]) (ll l) = Some x.
Proof.
  intros A.
  induction l.
  intros x.
  reflexivity.
  simpl.
  apply IHl.
Qed.

(* TODO: combi.v I guess *)
Lemma Forall_nth_error : forall {A} l n (m : A) Q,
    nth_error l n = Some m -> Forall Q l -> Q m.
Proof.
  intros A l n m Q.
  revert l n m.
  induction l as [|b l IHl].
  destruct n; intros m mis; inversion mis.

  destruct n as [|n].
  intros m mis qis.
  inversion mis as [qm].
  rewrite <- qm.
  inversion qis.
  trivial.

  intros m mis qis.
  simpl in mis.
  eapply IHl.
  exact mis.
  inversion qis.
  trivial.
Qed.

Lemma BackRefsNo : forall mindist maxdist n d
                          (input : SequenceWithBackRefs Byte)
                          (output : LByte),
                          BackRefsBounded 1 1 mindist maxdist input ->
                          ResolveBackReferences input output ->
                          nth_error input n = Some (inr (1, d)) ->
                          d <= n.
Proof.
  intros mnd mxd n d input.
  revert input d n mxd mnd.
  apply (rev_ind (fun input => forall (d n mxd mnd : nat)
                                      (output : LByte),
                      BackRefsBounded 1 1 mnd mxd input ->
                      ResolveBackReferences input output ->
                      nth_error input n = Some (inr (1, d)) -> d <= n)).
  intros d n mxd mnd output brb rbr Q.
  destruct n; inversion Q.

  intros x l IHl d n mxd mnd output brb rbr nerr.
  destruct (nat_compare n (ll l)) eqn:e.
  apply nat_compare_eq_iff in e.
  
  assert (xi : x = inr (1, d));
  [ rewrite -> e in nerr;
    rewrite -> nth_error_last in nerr;
    inversion nerr;
    reflexivity
  | ].

  rewrite -> xi in rbr.  
  inversion rbr as [A B | A B C D E F | A B C D E F G H I].
  destruct l; inversion A.

  destruct (app_ll_r _ _ _ _ E) as [K1 K2];
  [ reflexivity
  | inversion K2 ].

  destruct (app_ll_r _ _ _ _ H) as [K1 K2];
  [ reflexivity
  | inversion K2 as [[q r]]].

  rewrite -> q in G.
  rewrite -> r in G.
  inversion G.
  inversion H1.
  inversion H2. (* TODO *)
  rewrite -> e.

  assert (LLB : ll l = ll B).
  eapply BackRefsLengthOneLength.
  apply forall_app in brb.
  destruct brb as [brbl brbd].
  exact brbl.
  rewrite <- K1.
  exact F.

  rewrite -> LLB.
  rewrite -> H9.
  rewrite <- H10.
  rewrite -> app_length.
  simpl.
  omega.

  apply nat_compare_lt in e.
  inversion rbr as [A B | A B C D E F | A B C D E F G H I].
  destruct l; inversion A.

  destruct (app_ll_r _ _ _ _ E) as [K1 K2];
  [ reflexivity
  | inversion K2 as [q]].
  apply (IHl d n mxd mnd B).
  apply forall_app in brb.
  destruct brb as [brbl brbd].
  trivial.
  rewrite <- K1.
  trivial.

  erewrite -> nth_extend.
  exact nerr.
  trivial.  
  
  destruct (app_ll_r _ _ _ _ H) as [K1 K2];
  [ reflexivity
  | inversion K2 as [q]].

  apply forall_app in brb.
  destruct brb as [brbl brbd].
  rewrite <- q in brbd.
  inversion brbd.
  inversion H2. (* TODO *)
  assert (D1 : D = 1); [ omega | ].
  rewrite -> D1 in G.
  inversion G.
  inversion H11.

  apply (IHl _ _ mxd mnd B).
  exact brbl.
  rewrite <- K1.
  trivial.

  erewrite -> nth_extend.
  exact nerr.
  trivial.

  apply nat_compare_gt in e.
  apply nth_error_lt in nerr.
  rewrite -> app_length in nerr.
  simpl in nerr.
  omega.
Qed.

Lemma RefinedResolveBRB_ : forall mindist maxdist (input : SequenceWithBackRefs Byte),
    mindist > 0 ->
    mindist < maxdist ->
                            BackRefsBounded 1 1 mindist maxdist input ->
                            {output : LByte | ResolveBackReferences input output} + ({output : LByte | ResolveBackReferences input output} -> False).
Proof.
  intros mnd mxd input_orig mn0 mnx brb.

  refine ((fix f
               (input inputRA : SequenceWithBackRefs Byte) (n m : nat)
               (output : LByte)
               (readAhead : pheap CopyPosition)
               (backBuffer : pheap BufferedCopy)
               (orig1 : input = drop_ n input_orig)
               (orig2 : inputRA = drop_ m input_orig)
               (m_size : m = min (n + mxd + 1) (ll input_orig))
               (out_brb : ResolveBackReferences (take_ n input_orig) (rev output))
               (readAheadCorrect : pheap_correct CPcmp readAhead)
               (readAheadContainsAll : 
                  forall src dst, (n <= src < m /\ n <= dst < m /\ pointsTo input_orig src dst) <->
                                  pheap_in {| source := src; sdestination := dst |} readAhead)
               (readAheadContainsSpcl :
                  forall dst, pointsTo input_orig n dst ->
                              pheap_in {| source := n; sdestination := dst |} readAhead)
               (backBufferCorrect : pheap_correct BCcmp backBuffer)
               (backBufferContains : forall dst b,
                                       (exists src,
                                          src < n <= dst /\
                                          pointsTo input_orig src dst /\
                                          nth_error (rev output) src = Some b) <->
                                       pheap_in {| content := b; cdestination := dst |} backBuffer)
               {struct input}
           : ({output : LByte | ResolveBackReferences input_orig output} +
              ({output : LByte | ResolveBackReferences input_orig output} -> False))
           := _) input_orig _ 0 _ [] _ Empty _ _ _ _ _ _ _ _ _).

  destruct input as [|i input];
  [ apply inl;
    exists (rev output);
    rewrite -> (takedrop_lemma input_orig n);
    rewrite <- orig1;
    rewrite -> app_nil_r;
    exact out_brb
  | ].

  assert (inlen : ll input_orig > n);
  [ eapply drop_nnil_length; exact orig1
  | assert (outlen : ll (rev output) = n);
    [ replace n with (ll (take_ n input_orig));
      [ symmetry;
        rewrite -> (takedrop_lemma input_orig n) in brb;
        apply forall_app in brb;
        destruct brb as [brb0 brb1];
        apply (BackRefsLengthOneLength _ _ _ _ brb0 out_brb)
      | apply take_length;
        eapply drop_nnil_length;
        exact orig1 ]
    | destruct i as [b | [l d]]; [ | ]]].

  assert (aclarg : forall x, pheap_in x readAhead -> source x >= n);
  [ intros [src dst] phi;
    apply readAheadContainsAll in phi;
    apply phi
  | ].

  destruct (addContentL n b readAhead backBuffer readAheadCorrect backBufferCorrect aclarg)
    as [cp2 [bc2 [cp2corr [bc2corr [cp2comp bc2comp]]]]]; [ ].

  destruct inputRA as [|ra inputRA];
  [ apply (f input [] (S n) m (b :: output) cp2 bc2);
    [ apply drop_single in orig1;
      exact orig1
    | exact orig2
    | assert (K : m >= ll input_orig);
      [ apply drop_nil;
        exact orig2
      | assert(m <= ll input_orig);
        [ rewrite -> m_size;
          apply Min.le_min_r
        | symmetry;
          assert (meq : m = ll input_orig);
          [ omega
          | rewrite -> meq;
            apply Min.min_r;
            assert (m <= n + mxd + 1);
            [ apply NPeano.Nat.min_l_iff;
              rewrite <- meq in m_size;
              symmetry;
              rewrite -> Min.min_comm;
              exact m_size
            |  omega ]]]]
      | replace (take_ (S n) input_orig) with (take_ n input_orig ++ [inl b]);
        [ simpl;
          constructor;
          exact out_brb
        | assert (xeq : (take_ n input_orig ++ [inl b]) ++ drop_ (S n) input_orig = take_ (S n) input_orig ++ drop_ (S n) input_orig);
          [ assert (orig1' : input = drop_ (S n) input_orig);
            [ apply drop_single in orig1;
              exact orig1
            | rewrite <- app_assoc;
              rewrite <- takedrop_lemma;
              rewrite <- orig1';
              simpl;
              rewrite -> orig1;
              rewrite <- takedrop_lemma;
              reflexivity]
          | apply (app_ll_r (take_ n input_orig ++ [inl b]) (drop_ (S n) input_orig)
                            (take_ (S n) input_orig) (drop_ (S n) input_orig) xeq eq_refl)]]
      | exact cp2corr
      | intros src dst; (* readAheadContainsAll *)
        split;
        [ intros [nsm [ndm pt]];
          apply cp2comp;
          simpl;
          split;
          [ omega
          | apply readAheadContainsAll;
            split;
            [ omega | split; [ omega | exact pt]]]
        | intro phi;
          split;
          [ split;
            [ assert (n < src);
              [ replace src with (source {| source := src; sdestination := dst |});
                [ apply cp2comp;
                  exact phi;
                  omega
                | reflexivity]
              | omega ]
            | replace src with (source {| source := src; sdestination := dst |});
              [ destruct (proj2 (readAheadContainsAll src dst));
                [ apply cp2comp;
                  exact phi
                | simpl;
                  omega ]
              | reflexivity]]
          | split;
            [ split;
              [ apply cp2comp in phi;
                destruct phi as [phi1 phi2];
                apply readAheadContainsAll in phi2;
                destruct phi2 as [phi2a [phi2b [phi2c phi2d]]];
                omega
              | apply cp2comp in phi;
                destruct phi as [phi1 phi2];
                apply readAheadContainsAll in phi2; 
                omega ]
            | apply readAheadContainsAll;
              apply cp2comp;
              exact phi ]]]
      | intros dst pto; (* readAheadContainsSpcl - this is the special case, where we have to prove that it is sufficient to know the rest of the list. *)
        apply cp2comp;
        split;
        [ simpl; omega
        | apply readAheadContainsAll;
          split;
          [ split;
            [ omega
            | assert (m >= ll input_orig);
              [ apply drop_nil;
                exact orig2
              | assert (dst < ll input_orig);
                [ eapply pointsTo_bound;
                  exact pto
                | destruct pto;
                  omega ]]]
          | split;
            [ split;
              [ destruct pto;
                omega
              | assert (m >= ll input_orig);
                [ apply drop_nil;
                  exact orig2
                | assert (dst < ll input_orig);
                  [ eapply pointsTo_bound;
                    exact pto
                  | omega ]]]
            | exact pto ]]]
      | exact bc2corr
      | (* backBufferContains *)
      intros dst b_;
        split;
        [ intros [src [eqns [pto nerr]]];
          apply bc2comp;
          destruct (eq_nat_dec src n) as [src_eq_n | src_neq_n];
          [ apply or_intror;
            simpl;
            split;
            [ apply readAheadContainsAll;
              assert (m >= ll input_orig);
              [ apply drop_nil;
                exact orig2
              | assert (dst < ll input_orig);
                [ eapply pointsTo_bound;
                  exact pto
                | split;
                  [ omega
                  | split;
                    [ omega
                    | rewrite <- src_eq_n; exact pto ]]]]
            | simpl in nerr;
              rewrite -> src_eq_n in nerr;
              rewrite <- outlen in nerr;
              rewrite -> nth_error_last in nerr;
              inversion nerr;
              reflexivity ]
          | apply or_introl;
            apply backBufferContains;
            exists src;
            split;
            [ omega
            | split;
              [ exact pto
              | simpl in nerr;
                rewrite <- nth_extend in nerr;
                [ exact nerr | omega ]]]]
        | intro phi;
          (* TODO NOTE : this part has to change in the other case: we're proving that n < dst *)
          assert (ndst : n < dst);
          [ apply bc2comp in phi;
            simpl in phi;
            destruct phi as [phi | [phi1 phi2]];
            [ destruct (proj2 (backBufferContains dst b_) phi) as [src [[sn nd] [pto nerr]]];
              destruct (eq_nat_dec n dst) as [eq_ | eq_];
              [ destruct pto as [pto1 pto2];
                rewrite <- eq_ in pto2;
                rewrite -> (drop_nth_error _ _ _ _ orig1) in pto2;
                inversion pto2
              | omega ]
            | apply readAheadContainsAll in phi1;
              destruct phi1 as [? [? [? ?]]];
              trivial ]
          | destruct (pheap_in_dec_nc BCcmp backBuffer cmpBCcmp backBufferCorrect
                                      {| cdestination := dst; content := b_ |}) as [inbb | nibb];
            [ destruct (proj2 (backBufferContains _ _) inbb) as [src [[sn nd] [pto nerr]]];
              exists src;
              split;
              [ omega
              | split;
                [ exact pto
                | simpl;
                  rewrite <- nth_extend;
                  [ exact nerr
                  | omega ]]]
            | exists n;
              apply bc2comp in phi;
              simpl in phi;
              destruct phi as [phi | phi];
              [ firstorder
              | destruct phi as [phi1 phi2];
                apply readAheadContainsAll in phi1;
                split;
                [ omega
                | split;
                  [ firstorder
                  | simpl;
                    rewrite <- outlen;
                    rewrite -> nth_error_last;
                    rewrite -> phi2;
                    reflexivity]]]]]]]
  | ].
  
  destruct ra as [ra | [ral rad]];
  [ assert (readAheadContainsAll_ :
            forall src dst : nat,
              S n <= src < S m /\ S n <= dst < S m /\
              pointsTo input_orig src dst <->
              pheap_in {| source := src; sdestination := dst |} cp2);
    [ intros src dst;
      (** in our case, dst != S m, because the first element of 
          readAhead was not a backreference **)
      split;
      [ intros [nsm [ndm pt]];
        apply cp2comp;
        simpl;
        split;
        [ omega
        | apply readAheadContainsAll;
          split;
          [ destruct pt; omega
          | split;
            [ destruct pt as [pt1 pt2];
              split;
              [ omega
              | destruct (eq_nat_dec dst m) as [eq_ | neq_];
                [ rewrite -> eq_ in pt2;
                  rewrite -> (drop_nth_error _ _ _ _ orig2) in pt2;
                  inversion pt2
                | omega ]]
            | exact pt]]]
      | intro phi;
        split;
        [ split;
          [ assert (n < src);
            [ replace src with (source {| source := src; sdestination := dst |});
              [ apply cp2comp;
                exact phi;
                omega
              | reflexivity]
            | omega ]
          | replace src with (source {| source := src; sdestination := dst |});
            [ destruct (proj2 (readAheadContainsAll src dst));
              [ apply cp2comp;
                exact phi
              | simpl;
                omega ]
            | reflexivity]]
        | split;
          [ split;
            [ apply cp2comp in phi;
              destruct phi as [phi1 phi2];
              apply readAheadContainsAll in phi2;
              destruct phi2 as [phi2a [phi2b [phi2c phi2d]]];
              omega
            | apply cp2comp in phi;
              destruct phi as [phi1 phi2];
              apply readAheadContainsAll in phi2; 
              omega ]
          | apply readAheadContainsAll;
            apply cp2comp;
            exact phi ]]]
    | assert (mnxd : m = n + mxd + 1);
      [ assert (mll : m < ll input_orig);
        [ apply drop_nth_error in orig2;
          apply nth_error_lt in orig2;
          exact orig2
        | destruct (Min.min_dec (n + mxd + 1) (ll input_orig)) as [e|e];
          [ rewrite -> e in m_size;
            exact m_size
          | omega ]]
      | apply (f input inputRA (S n) (S m) (b :: output) cp2 bc2);
  [ apply drop_single in orig1;
    exact orig1
  | apply drop_single in orig2;
    exact orig2
  | (* m_size *)   
    assert (mllo : m < ll input_orig);
    [ eapply nth_error_lt;
      eapply drop_nth_error;
      exact orig2
    | destruct (Min.min_dec (n + mxd + 1) (ll input_orig)) as [lft | rgt];
      [ rewrite <- m_size in lft;
        rewrite -> lft;
        replace (S (n + mxd + 1)) with (S n + mxd + 1);
        [ assert (S n + mxd + 1 <= ll input_orig);
          [ replace (S n + mxd + 1) with (S (n + mxd + 1));
            [ rewrite <- lft;
              omega
            | omega]
          | symmetry;
            apply Min.min_l;
            trivial ]
        | omega]
      | rewrite <- m_size in rgt;
        omega ]]
  | replace (take_ (S n) input_orig) with (take_ n input_orig ++ [inl b]);
    [ simpl;
      constructor;
      exact out_brb
    | assert (xeq : (take_ n input_orig ++ [inl b]) ++ drop_ (S n) input_orig = take_ (S n) input_orig ++ drop_ (S n) input_orig);
      [ assert (orig1' : input = drop_ (S n) input_orig);
        [ apply drop_single in orig1;
          exact orig1
        | rewrite <- app_assoc;
          rewrite <- takedrop_lemma;
          rewrite <- orig1';
          simpl;
          rewrite -> orig1;
          rewrite <- takedrop_lemma;
          reflexivity]
      | apply (app_ll_r (take_ n input_orig ++ [inl b]) (drop_ (S n) input_orig)
                        (take_ (S n) input_orig) (drop_ (S n) input_orig) xeq eq_refl)]]
  | exact cp2corr
  | exact readAheadContainsAll_
  | (* readAheadContainsSpcl *)
  intros dst pto;

    (* if dst < m, we are done. dst = m cannot happen, because the
    m-th element of input_orig is not a backreference in our case. dst
    > m cannot happen, because m = n + mxd, because m < ll input_orig,
    because orig2. *)

    assert (smnxd : S m = S n + mxd + 1);
    [ omega
    | apply readAheadContainsAll_;
      split;
      [ omega
      | split;
        [ destruct pto as [pt0 pt1];
          set (X := Forall_nth_error _ _ _ _ pt1 brb);
          inversion X;
          omega
        | exact pto ]]]
  | exact bc2corr
  | (* backBufferContains *)
  intros dst b_;
    split;
    [ intros [src [eqns [pto nerr]]];
      apply bc2comp;
      destruct (eq_nat_dec src n) as [src_eq_n | src_neq_n];
      [ apply or_intror;
        simpl;
        split;
        [ apply readAheadContainsAll;
          split;
          [ omega
          | split;
            [ destruct pto as [pt0 pt1];
              set (X := Forall_nth_error _ _ _ _ pt1 brb);
              inversion X;
              omega
            | rewrite <- src_eq_n;
              exact pto ]]
        | simpl in nerr;
          rewrite -> src_eq_n in nerr;
          rewrite <- outlen in nerr;
          rewrite -> nth_error_last in nerr;
          inversion nerr;
          trivial ]
      | simpl;
        apply or_introl;
        apply backBufferContains;
        exists src;
        split;
        [ omega
        | split;
          [ exact pto
          | simpl in nerr;
            erewrite -> nth_extend;
            [ exact nerr
            | omega ]]]]
    | intro phi;
      (* NOTE : this part has to change in the other case: we're proving that n < dst *)
      assert (ndst : n < dst);
      [ apply bc2comp in phi;
        simpl in phi;
        destruct phi as [phi | [phi1 phi2]];
        [ destruct (proj2 (backBufferContains dst b_) phi) as [src [[sn nd] [pto nerr]]];
          destruct (eq_nat_dec n dst) as [eq_ | eq_];
          [ destruct pto as [pto1 pto2];
            rewrite <- eq_ in pto2;
            rewrite -> (drop_nth_error _ _ _ _ orig1) in pto2;
            inversion pto2
          | omega ]
        | apply readAheadContainsAll in phi1;
          destruct phi1 as [? [? [? ?]]];
          trivial ]
      | destruct (pheap_in_dec_nc BCcmp backBuffer cmpBCcmp backBufferCorrect
                                  {| cdestination := dst; content := b_ |}) as [inbb | nibb];
        [ destruct (proj2 (backBufferContains _ _) inbb) as [src [[sn nd] [pto nerr]]];
          exists src;
          split;
          [ omega
          | split;
            [ exact pto
            | simpl;
              rewrite <- nth_extend;
              [ exact nerr
              | omega ]]]
        | exists n;
          apply bc2comp in phi;
          simpl in phi;
          destruct phi as [phi | phi];
          [ firstorder
          | destruct phi as [phi1 phi2];
            apply readAheadContainsAll in phi1;
            split;
            [ omega
            | split;
              [ firstorder
              | simpl;
                rewrite <- outlen;
                rewrite -> nth_error_last;
                rewrite -> phi2;
                reflexivity]]]]]]]]]
  | ].
  
  (** this is the only part in the recursion step where an actual
  error can occur: it might be that the source of the new
  backreference is smaller than n; but because of BackRefsBounded,
  this can only mean that n = ll input_orig >= m - rad *)

  assert (X1 : nth_error input_orig m = Some (inr (ral, rad))).
  apply (drop_nth_error _ inputRA).
  exact orig2.


  destruct (le_dec rad m) as [xm_rad | xm_rad];
  [

    (* TODOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO *)




  | apply inr;
    intros [o rbr];
    contradict xm_rad;
    assert (R : ral = 1);
    [ set (Y1 := Forall_nth_error _ _ _ _ X1 brb);
      inversion Y1;
      abstract(omega)
    | rewrite -> R in X1;
      apply (BackRefsNo _ _ _ _ input_orig o brb rbr X1) ]].
  
  
  (*assert (n < m - rad).
  assert (pointsTo input_orig (m - rad) m).
  split;
  [ inversion Y1;
    assert (n < m);
    [ destruct (Min.min_dec (n + mxd + 1) (ll input_orig)) as [e|e];
      [ rewrite -> e in m_size;
        rewrite -> m_size;
        omega
      | rewrite -> e in m_size;
        rewrite -> m_size;
        trivial ]
    | omega ]
  | ].
  

  assert (m - (m - rad) = rad).
  omega.
  admit. **************************************************TODOOOOO*****



  destruct (Min.min_dec (n + mxd + 1) (ll input_orig)) as [e_contr|e];
  [ rewrite -> e_contr in m_size;
    destruct (le_dec (S n) (m - rad)) as [m_rad | m_rad];
    [


    | rewrite -> m_size in m_rad;
      contradict m_rad;
      inversion Y1;
      omega ]
  | ]. *)

  (*destruct (le_dec (S n) (m - rad)) as [m_rad | m_rad]; [admit | ].*)
  
  set (cp3 := insert CPcmp {| source := m - rad ; sdestination := m |} cp2).
  assert (readAheadContainsAll_ :
            forall src dst : nat,
              S n <= src < S m /\ S n <= dst < S m /\
              pointsTo input_orig src dst <->
              pheap_in {| source := src; sdestination := dst |} cp3); [ | ].
  intros src dst;
  split;
  [ intros [nsm [ndm pt]];
    unfold cp3;
    apply insert_spec;
    [ exact cmpCPcmp
    | destruct (eq_nat_dec dst m) as [e|e];
      [ apply or_introl;
        destruct pt as [pt0 pt1];
        assert (R : rad = dst - src);
        [ rewrite -> e in pt1;
          rewrite -> (drop_nth_error _ _ _ _ orig2) in pt1;
          inversion pt1;
          omega
        | assert (R2 : src = m - rad);
          [ set (X := Forall_nth_error _ _ _ _ pt1 brb);
            inversion X;
            omega
          | rewrite -> R2;
            rewrite -> e;
            reflexivity ]]
      | apply or_intror;
        apply cp2comp;
        simpl;
        split;
        [ omega
        | apply readAheadContainsAll;
          split;
          [ destruct pt; omega
          | split;
            [ destruct pt as [pt1 pt2];
              omega
            | trivial ]]]]]
  | ].

  intro c3.
  unfold cp3 in c3.
  apply insert_spec in c3.
  destruct c3 as [sd | nsd].
  inversion sd as [[sd1 sd2]].




  (********* PHAIL HERE ***********)

  

  split.

  [ inversion sd as [[sd1 sd2]];
    split;
    [ abstract(omega)
    | split;
      [ abstract(omega)
      | split;
        [ inversion Y1;
          abstract(omega)
        | replace (m - (m - rad)) with rad;
          [ rewrite -> X1;
            replace ral with 1;
            [ reflexivity
            | inversion Y1;
              omega]
          | inversion Y1;
            abstract(omega)]]]]
    | ].

  apply cp2comp in nsd.
  simpl in nsd.
  destruct nsd as [nsd1 nsd2].
  apply readAheadContainsAll in nsd2.
  destruct nsd2 as [nsd2a [nsd2b nsd2c]].
  split.
  abstract(omega).
  split.
  destruct nsd2c.
  abstract(omega).
  exact nsd2c.

  exact cmpCPcmp.


  admit. (*********************TODOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO**********)


  apply inr.

  admit. (*********************TODOOOOOOOOOOOOOOOOOOOOOOOOOOOOOO**********)
  
  destruct (le_dec (S n) (m - rad)) as [m_rad | m_rad].
  admit. (*********************TODOOOOOOOOOOOOOOOOOOOO Copypaste **********)

  rewrite -> e in m_size.

  rewrite -> m_size in m_rad;
    contradict m_rad;
    inversion Y1.
  assert (ll input_orig <= n + mxd + 1).
  rewrite <- e.
  apply Min.le_min_l.

  omega.
  
  assert (n + rad >= ll input_orig).
  omega.
  assert (S n > ll input_orig - rad).
  omega.


(* NOTE TO SELF: hier müssen wir fallunterscheiden. es könnte an dieser stelle eine zu lange backreference entstehen. müssen wir sogar schon weiter oben. *)

  
  assert (R : rad = dst - src);
        [ rewrite -> e in pt1;
          rewrite -> (drop_nth_error _ _ _ _ orig2) in pt1;
          inversion pt1;
          omega
        | assert (R2 : src = m - rad);
          [ set (X := Forall_nth_error _ _ _ _ pt1 brb);
            inversion X;
            omega
          | ]].
  
  (******************************)


Lemma BackRefLemma2 : forall {A : Set} (mnd mxd : nat)
                             (input : SequenceWithBackRefs A) (output : list A),
                        mnd > 0 ->
                        BackRefsBounded 1 1 mnd mxd input ->
                        (forall n k, nth_error input n = Some (inr (1, k)) ->
                                     nth_error output n = nth_error output (n - k)) ->
                        (forall n k, nth_error input n = Some (inl k) ->
                                     nth_error output n = Some k) ->
                        ll input = ll output ->
                        ResolveBackReferences input output.
Proof.
  intros A mnd mxd.
  apply (rev_ind (fun input => forall (output : list A),
                                 mnd > 0 ->
                                 BackRefsBounded 1 1 mnd mxd input ->
                                 (forall n k : nat,
                                    nth_error input n = Some (inr (1, k)) ->
                                    nth_error output n = nth_error output (n - k)) ->
                                 (forall n k, nth_error input n = Some (inl k) ->
                                              nth_error output n = Some k) ->
                                 ll input = ll output ->
                                 ResolveBackReferences input output)).
  intros output mg0 brb allr alll ls.
  destruct output as [|a l].
  constructor.
  inversion ls.

  intros x l IHl output mg0 brb allr alll ls.
  destruct (list_tail_destruct output) as [o0 | [on [om oa]]].
  rewrite -> o0 in ls.
  rewrite -> app_length in ls.
  simpl in ls.
  omega.
  rewrite -> oa.
  rewrite -> oa in alll.
  rewrite -> oa in allr.
  rewrite -> oa in ls.
  destruct x as [x | [xl xd]].
  assert (ls2 : ll l = ll on).
  rewrite -> app_length in ls.
  rewrite -> app_length in ls.
  simpl in ls.
  omega.

  assert (omx : om = x).
  assert (omsome : nth_error (on ++ [om]) (ll on) = Some x).
  rewrite <- ls2.
  apply alll.
  apply nth_error_last.
  rewrite -> nth_error_last in omsome.
  inversion omsome.
  reflexivity.

  rewrite <- omx.
  constructor.
  apply IHl.
  exact mg0.
  apply forall_app in brb.
  destruct brb.
  auto.

  intros n k nerr.

  assert (nll : n < ll l).
  eapply nth_error_lt.
  exact nerr.

  rewrite -> (nth_extend on [om]).
  rewrite -> (nth_extend on [om]).
  apply allr.
  rewrite <- (nth_extend l [inl x]).
  exact nerr.
  exact nll.
  omega.
  omega.

  intros n k nerr.
  assert (nll : n < ll l).
  eapply nth_error_lt.
  exact nerr.
  rewrite -> (nth_extend on [om]).
  apply alll.
  rewrite <- (nth_extend l [inl x]).
  exact nerr.
  exact nll.
  omega.
  exact ls2.

  assert (xl1 : xl = 1).
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  inversion brb2.
  match goal with
    | X : BackRefBounded _ _ _ _ _ |- _ => inversion H1; omega
  end.

  assert (xd1 : xd >= 1).
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  inversion brb2.
  match goal with
    | X : BackRefBounded _ _ _ _ _ |- _ => inversion H1; omega
  end.

  assert (rbr : ResolveBackReference 1 xd on (on ++ [om])).
  constructor.
  constructor.
  destruct xd.
  omega.
  eapply nthNthLast. *)


Fixpoint RefinedResolveBRB_
         (n m : nat) (rev_done : LByte)
         (todo todo_ : SequenceWithBackRefs Byte) 
         (readAhead : pheap CopyPosition)
         (backBuffer : pheap BufferedCopy)
  := match todo with
       | [] => Some (rev rev_done)
       | inl b :: r =>
         let (ra2, bb2) := addContent n b readAhead backBuffer
         in match proceed_read_ahead m ra2 todo_ with
              | None => None
              | Some (m_, ra_, todo__) => 
                RefinedResolveBRB_ (S n) m_ (b :: rev_done) r todo__ ra_ bb2
            end
       | inr (_, d) :: r =>
         match find_min backBuffer with
           | None => None
           | Some c =>
             (* assert: cdestination c = n *)
             let b := content c in
             let bb := x_delete_min BCcmp backBuffer in
             let (ra2, bb2) := addContent n b readAhead bb
             in match proceed_read_ahead m ra2 todo_ with
                  | None => None
                  | Some (m_, ra_, todo__) =>
                    RefinedResolveBRB_ (S n) m_ (b :: rev_done) r todo__ ra_ bb2
                end
         end
     end.

Function RefinedResolveBRB (maxdist : nat) (swbr : SequenceWithBackRefs Byte) :=
  match prepare_read_ahead maxdist swbr with
    | None => None
    | Some (m, readAhead, todo_) =>
      RefinedResolveBRB_ 0 m [] swbr todo_ readAhead Empty
  end.

(* TODO: combi.v *)
Fixpoint drop {A} (n : nat) (l : list A) :=
  match n with
    | 0 => l
    | (S n_) => match l with
                  | [] => l
                  | _ :: l_ => drop n_ l_
                end
  end.

(* TODO: combi.v *)
Lemma drop_nil : forall {A} l n (x : A),
                   drop n (x :: l) = [] -> drop n l = [].
Proof.
  induction l.
  intros; destruct n; reflexivity.

  intros n x drp.
  destruct n.
  inversion drp.
  simpl.
  simpl in drp.
  eapply IHl.
  eauto.
Qed.

Theorem RefinedResolveBRB_correct_ :
  forall mnd mxd todo,
    mnd > 0 ->
    BackRefsBounded 1 1 mnd mxd todo ->
    SlowResolveBRB 0 [] todo = RefinedResolveBRB mxd todo.
Proof.
  intros mnd mxd todo mg0 brb.
  unfold RefinedResolveBRB.
  destruct (prepare_read_ahead mxd todo) as [[[m ra] todo_]|] eqn:pra;
    [ | (* this case contradicts brb *) ].
  refine ((fix f todoA nA mA done_revA raA bbA todo_A 
               (inv_td : todo_A = drop mxd todoA)
               (inv_ra : forall bx d, bx < mxd ->
                                      nth_error todoA bx = Some (inr (1, d)) ->
                                      d <= bx -> 
                                      pheap_in (mkCopyPosition (nA + bx - d) (nA + bx)) raA)
               (inv_bb : forall bx d, 1 <= bx < mxd ->
                                      nth_error todoA bx = Some (inr (1, d)) ->
                                      d >= bx -> 
                                      pheap_in (mkBufferedCopy (nA + bx) (nth (d - bx) done_revA NullByte)) bbA)
              : SlowResolveBRB nA done_revA todoA = RefinedResolveBRB_ nA mA done_revA todoA todo_A raA bbA := _) todo 0 m [] ra Empty todo_ _ _ _).

  destruct todoA as [|tA todoA];
    [ reflexivity |
      destruct tA as [t | [l d]]; [ | ]].

  simpl.
  destruct (addContent nA t raA bbA) as [ra2 bb2] eqn:ac.
  destruct todo_A as [|t_A todo_A]; [ | ].
  simpl.
  apply f;
  [ symmetry;
    eapply drop_nil;
    eauto
  | | ].

  intros bx d bxmxd nerr dbx.
  unfold addContent in ac.