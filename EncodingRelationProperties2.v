Require Import StrongDec.
Require Import EncodingRelation.
Require Import EncodingRelationProperties.
Require Import Shorthand.
Require Import Combi.
Require Import DeflateCoding.
Require Import LSB.

Require Import Omega.
Require Import String.
Require Import List.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.Compare_dec.
Import ListNotations.

Lemma SD_imp_SSD :
  forall {A B} (nilval : A) (R : A -> list B -> Prop),
    StrongDec R ->  StreamableStrongDec string R.
Proof.
  intros A B n R sd l.
  destruct (sd l) as [[a [l' [l'' [lapp ral]]]] | [reason no]].
  + exists a.
    exists l'.
    exists l''.
    exists None.
    firstorder.
  + exists n.
    exists [].
    exists l.
    exists (Some reason).
    split.
    - reflexivity.
    - split.
      * intro.
        discriminate.
      * intros Q b k' k'' app rbk.
        apply no.
        exists b.
        exists k'.
        exists k''.
        auto.
Defined.

Lemma SSD_imp_SD : forall {A B} (R : A -> list B -> Prop),
    StreamableStrongDec string R -> StrongDec R.
Proof.
  intros A B R ssd l.
  destruct (ssd l) as [x [l' [l'' [e [lapp [none nnone]]]]]].
  destruct e as [en | es].
  + apply inr.
    split.
    - exact en.
    - intro N.
      destruct N as [a [k' [k'' [kapp rak]]]].
      eapply nnone.
      * intro Q.
        inversion Q.
      * exact kapp.
      * exact rak.
  + apply inl.
    exists x.
    exists l'.
    exists l''.
    split.
    - exact lapp.
    - apply none.
      reflexivity.
Defined.

(* ONEBITSSD1 *)
Lemma OneBitSSD : StreamableStrongDec string OneBit.
Proof.
  apply (SD_imp_SSD false).
  apply OneBitStrongDec.
Defined.
(* ONEBITSSD2 *)

Lemma nBitsSSD : forall n, StreamableStrongDec string (nBits n).
Proof.
  intro n.
  apply nTimesStreamableStrongDecStrongUnique.
  apply OneBitStrongUnique.
  apply OneBitSSD.
Defined.

Fixpoint falseVec (n : nat) : vec bool n :=
  match n with
  | 0 => Vnil
  | (S n_) => Vcons false _ (falseVec n_)
  end.

(* we need this function to maintain lazyness -- so we do not have to
call nBitsSSD and evaluate the error before being able to return
something *)

Fixpoint falseFilled (n : nat) (l : list bool) : vec bool n :=
  match n with
  | 0 => Vnil
  | (S n_) => match l with
              | [] => Vcons false _ (falseFilled n_ [])
              | x :: l_ => Vcons x _ (falseFilled n_ l_)
              end
  end.

Lemma falseFilledEq : forall l, falseFilled (ll l) l = Vector.of_list l.
Proof.
  induction l as [|x l IHl].
  + reflexivity.
  + simpl.
    rewrite -> IHl.
    reflexivity.
Qed.
    
Lemma nBitsVecSSD : forall n, StreamableStrongDec string (nBitsVec n).
Proof.
  intros n l.
  destruct (nBitsSSD n l) as [x [l' [l'' [e [lapp [nocase yescase]]]]]].
  exists (falseFilled _ x).
  exists l'.
  exists l''.
  destruct e as [no | yes] eqn:eeq.
  + exists (Some ("In nBitsVecSSD: " ++ no)%string).
    split.
    - exact lapp.
    - split.
      * intro Q.
        discriminate.
      * intros Q b k' k'' kapp nbv.
        eapply yescase.
        discriminate.
        exact kapp.
        exact nbv.
  + assert (nxl : nBits n x l').
    - apply nocase.
      reflexivity.
    - assert (nlb : n = lb x).
      * symmetry.
        eapply nBitsEq.
        exact nxl.
      * rewrite -> nlb.
        exists None.
        split.
        -- exact lapp.
        -- split.
           ** intro Q.
              unfold nBitsVec.
              rewrite -> falseFilledEq.
              rewrite -> Vector.to_list_of_list_opp.
              rewrite <- nlb.
              exact nxl.
           ** intro Q.
              contradict Q.
              reflexivity.
Defined.

(** etrans : E -> E is for transforming the error (for example, add a
stack frame to a stack trace, or some prefix to a string) *)

Theorem CombineSSDSU : forall {A BQ BR BS E}
                            (Q : BQ -> list A -> Prop)
                            (R : BQ -> BR -> list A -> Prop)
                            (c : BQ -> BR -> BS)
                            (etrans : E -> E),
    StrongUnique Q -> StreamableStrongDec E Q ->
    (forall bq, StreamableStrongDec E (R bq)) ->
    StreamableStrongDec E (Q >>[ c ]= R).
Proof.
  intros A BQ BR BS E Q R c etrans SUQ SSDEQ SSDER l.
  destruct (SSDEQ l) as [bq [l' [l'' [e [lapp [nonecase somecase]]]]]].
  destruct (SSDER bq l'') as [br [l2 [l3 [e2 [lapp2 [nonecase2 somecase2]]]]]].
  exists (c bq br).
  exists (l' ++ l2).
  exists l3.
  destruct e as [yes |] eqn:eeq.
  + exists (Some (etrans yes)).
    split.
    - rewrite <- app_assoc.
      rewrite <- lapp2.
      trivial.
    - split.
      * intro N.
        inversion N.
      * intros N b k' k'' kapp rel.
        inversion rel as [S T U V W X Y Z].
        eapply (somecase _ S U (V ++ k'')).
        ++ rewrite -> app_assoc.
           rewrite -> Z.
           trivial.
        ++ trivial.
 + destruct e2 as [yes |] eqn:e2eq.
   exists (Some (etrans yes)).
   split.
   - rewrite <- app_assoc.
     rewrite <- lapp2.
     trivial.
   - split.
     * intro bumm.
       discriminate.
     * intros bumm b k' k'' kapp rel.
       inversion rel as [S T U V W X Y Z].
       destruct (SUQ bq S l' l'' U (V ++ k'')) as [bqS l'U].
       -- rewrite -> app_assoc.
          rewrite -> Z.
          rewrite <- lapp.
          trivial.
       -- apply nonecase.
          reflexivity.
       -- exact W.
       -- eapply (somecase2 _ T V k'').
          apply (app_ll l' l'' U (V ++ k'')).
          ++ rewrite -> app_assoc.
             rewrite -> Z.
             rewrite <- lapp.
             trivial.             
          ++ f_equal.
             trivial.
          ++ idtac.
             rewrite -> bqS.
             trivial.
   - exists None.
     split.
     * rewrite <- app_assoc.
       rewrite <- lapp2.
       trivial.
     * split.
       ++ intro q.
          constructor.
          -- apply nonecase.
             reflexivity.
          -- apply nonecase2.
             reflexivity.
       ++ intro q.
          contradict q.
          reflexivity.

Grab Existential Variables.
intro q.
discriminate.
intro q.
discriminate.
Defined.

Lemma nullSSD : forall {A B E} (null : A),
    StreamableStrongDec E (fun n L => n = null /\ L = @nil B).
Proof.
  intros A B E n l.
  exists n.
  exists [].
  exists l.
  exists None.
  split.
  reflexivity.
  split.
  auto.
  intro Q.
  contradict Q.
  reflexivity.
Defined.
  
Lemma OneByteSSD : StreamableStrongDec string OneByte.
Proof.
  apply CombineSSDSU.
  exact (fun e => "In OneByteSSD: " ++ e)%string.
  apply nBitsVecStrongDecStrongUnique.
  apply nBitsVecSSD.
  intro b.
  apply nullSSD.
Defined.

Lemma nBytesDirectSSD : forall n, StreamableStrongDec string (nBytesDirect n).
Proof.
  intro n.
  apply nTimesStreamableStrongDecStrongUnique.
  apply OneByteStrongDecStrongUnique.
  apply OneByteSSD.
Defined.


Lemma readBitsLSBSSD : forall len, StreamableStrongDec string (readBitsLSB len).
Proof.
  intro len.
  * apply CombineSSDSU.
    + exact (fun e => "In readBitsLSBSSD: " ++ e)%string.
    + eapply nTimesStreamableStrongDecStrongUnique.
      - apply OneBitStrongUnique.
      - apply OneBitSSD.
    + eapply nTimesStreamableStrongDecStrongUnique.
      - apply OneBitStrongUnique.
      - apply OneBitSSD.
    + intro l.
      apply nullSSD.
Defined.

Lemma AndSSD
  : forall A B E (Q : Prop) (null : A)
           (rel : A -> list B -> Prop),
    (Q + (E * ~ Q)) ->
    StreamableStrongDec E rel ->
    StreamableStrongDec E (fun a b => Q /\ rel a b).
Proof.
  intros A B E Q null rel qdec ssdr.
  intro l.
  destruct qdec as [q | [e nq]].
  + destruct (ssdr l) as [x [l' [l'' [e [lapp [nonecase somecase]]]]]].
    exists x.
    exists l'.
    exists l''.
    exists e.
    split.
    - exact lapp.
    - split.
      * split.
        ++ exact q.
        ++ apply nonecase.
           trivial.
      * intros enone b k' k'' kapp [qq relbk].
        eapply somecase.
        trivial.
        exact kapp.
        exact relbk.
  + exists null.
    exists [].
    exists l.
    exists (Some e).
    split.
    reflexivity.
    split.
    intro R.
    discriminate.
    intros R b k' k'' kapp [q r].
    exact (nq q).
Defined.
    
Lemma UncompressedBlockDirectSSD
  : StreamableStrongDec string UncompressedBlockDirect.
Proof.
  apply CombineSSDSU.
  + exact (fun e => "In UncompressedBlockDirectSSD: " ++ e)%string.
  + apply readBitsLSBStrongUnique.
  + apply readBitsLSBSSD.
  + intro bq.
    apply CombineSSDSU.
    - exact (fun e => "In UncompressedBlockDirectSSD: " ++ e)%string.
    - apply readBitsLSBStrongUnique.
    - apply readBitsLSBSSD.
    - intro br.
      apply AndSSD.
      exact [].
      destruct (eq_nat_dec (bq + br) (NPeano.Nat.pow 2 16 - 1)).
      auto.
      apply inr.
      split.
      exact ("In UncompressedBlockDirectSSD: Header bits of " ++
             "uncompressed blocks are not complement of each other.")%string.
      trivial.
      apply nBytesDirectSSD.
Defined.

(* TODO: This does not consume too much stack space, and we have to
save lots of stuff for permutation anyway, so it is not worthwile to
cleanly port this to SSD. *)

Lemma CLCHeaderSSD
  : forall hclen, StreamableStrongDec string (CLCHeader hclen).
Proof.
  intro hclen.
  apply SD_imp_SSD.
  apply nullCoding.
  apply CLCHeaderStrongDec.
Defined.

Theorem CompressedWithExtraBitsSSD
  : forall {m} coding mincode xbitnums bases maxs,
    StreamableStrongDec
      string  (CompressedWithExtraBits
                 (m:=m) coding mincode xbitnums bases maxs).
Proof.
  intros.
  apply (SD_imp_SSD 0).
  apply CompressedWithExtraBitsStrongDec.
Defined.

Theorem LitLenDistSSD
  : forall clc hlit hdist,
    StreamableStrongDec string
      (fun x => LitLenDist clc hlit hdist (fst x) (snd x)).
Proof.
  intros.
  apply SD_imp_SSD.
  split; apply nullCoding.
  apply LitLenDistStrongDec.
Defined.

(* TODO: This is inefficient *)

Theorem dc_SSD
  : forall {m} (dc : deflateCoding m),
    StreamableStrongDec string (dc_enc dc).
Proof.
  intros.
  apply (SD_imp_SSD 0).
  apply dc_StrongDec.
Defined.

Theorem CWEB_SSD : forall {m} coding mincode xbitnums bases maxs,
    StreamableStrongDec
      string
      (CompressedWithExtraBits
         (m:=m) coding mincode xbitnums bases maxs).
Proof.
  intros.
  apply (SD_imp_SSD 0).
  apply CompressedWithExtraBitsStrongDec.
Qed.

(*
Theorem CompressedSWBR_SSD
  : forall litlen dist,
    StreamableStrongDec string (CompressedSWBR litlen dist).
Proof.
  intros litlen dist.
  assert (su : StrongUnique (CompressedSWBR litlen dist)).
  apply CompressedSWBRStrongUnique.
  refine (fix ph l {measure ll l} := _).
  
  destruct (dc_SSD litlen l) as
      [n [l1 [l2 [[e|] [lapp12 [noncase yescase]]]]]].
  - (* error case *)
    exists [].
    exists [].
    exists l.
    exists (Some e).
    split.
    auto.
    split.
    intro Q.
    inversion Q.

    intros _q b k' k'' kapp cswbr.
    inversion cswbr.
    + eapply yescase.
      auto.
      exact kapp.
      eauto.
    + eapply yescase.
      auto.
      match goal with
      | Y : l = k' ++ k'', X : _ ++ _ = k' |- _ => 
        rewrite <- X in Y
      end.
      rewrite <- app_assoc in kapp.
      exact kapp.
      eauto.
    + match goal with
      | Y : CompressedLength _ _ _ |- _ =>
        inversion Y
      end.
      eapply yescase.
      auto.
      match goal with
      | Y : ?A ++ _ ++ _ = k',
        X : _ ++ _ = ?A
        |- _ =>
        rewrite <- X in Y;
        rewrite <- app_assoc in Y;
        rewrite <- Y in kapp
      end.
      rewrite <- app_assoc in kapp.
      exact kapp.
      eauto.
  - destruct (nat_compare n 256) eqn:nc.
    (* success case *)
    + exists [].
      (* end case *)
      exists l1.
      exists l2.
      exists None.
      split.
      trivial.
      split.
      intro q.
      constructor.
      apply nat_compare_eq in nc.
      rewrite -> nc in noncase.
      apply noncase.
      trivial.
      auto.
    + apply nat_compare_lt in nc.
      (* case n < 256 -> normal character *)
      destruct (NatToByte n nc) as [nbyte nlsb].
      destruct (ph l2) as [x [l' [l'' [e [l2app r]]]]].
      exists (inl nbyte :: x).
      exists (l1 ++ l').
      exists l''.
      destruct e as [e|].
      * exists (Some e). (* there was an error in the sub-case *)
        split.
        -- rewrite <- app_assoc.
           rewrite <- l2app.
           trivial.
        -- split.
           ++ intro q.
              inversion q.
           ++ intros q b k' k'' kapp cswbr.
              (* no other interpretation of our l', l'' is possible *)
              inversion cswbr.
              ** assert (Q : 256 = n).
                 apply (dc_StrongUnique litlen 256 n k' k'' l1 (l' ++ l'')).
                 rewrite <- kapp.
                 rewrite <- l2app.
                 auto.
                 auto.
                 auto.
                 omega.
              ** idtac.
                 
                 
                 eapply r.
                 --- auto.
                 --- idtac.
                     exact l2app.
                 --- idtac.
                     
                     
  - exists None.
        split.
        ++ rewrite <- app_assoc.
           rewrite <- l2app.
           trivial.
        ++ split.
           intro _q.
           constructor.
           rewrite -> nlsb.
           apply noncase.
           exact _q.
           apply r.
           exact _q.
           intro q.
           contradict q.
           reflexivity.
        * apply nat_compare_gt in nc.
          *)