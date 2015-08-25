Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Omega.
Require Import Program.
Import ListNotations.

Require Import Combi.
Require Import Shorthand.
Require Import LSB.
Require Import String.

(** A list with backreferences. Every element is either a direct byte,
or a pair of numbers, the first component being the length, the second
component being the distance. We do not use an own inductive
definition here to be able to use list functions. *)

Function SequenceWithBackRefs A := (list (A + (nat * nat))%type).

Fixpoint brlen {A} (l : SequenceWithBackRefs A) : nat :=
  match l with
    | nil => 0
    | inl _ :: l' => S (brlen l')
    | inr (n, _) :: l' => n + brlen l'
  end.

Lemma app_brlen : forall {A} (a b : SequenceWithBackRefs A),
                    brlen (a ++ b) = brlen a + brlen b.
Proof.
  intro A.
  induction a as [|a0 a].
  auto.
  destruct a0 as [a0 | [a0 a1]].
  intro b.
  rewrite <- app_comm_cons.
  simpl.
  f_equal.
  apply IHa.
  intro b.
  rewrite <- app_comm_cons.
  simpl.
  rewrite -> IHa.
  omega.
Qed.

Inductive nthLast {A : Set} : forall (n : nat) (L : list A) (a : A), Prop :=
| makeNthLast : forall L M a, nthLast (ll (a :: M)) (L ++ a :: M) a.

(** Example *)
Goal nthLast 1 [0; 1; 2] 2.
Proof.
  apply (makeNthLast [0; 1] []).
Qed.

Lemma nthNthLast_1 : forall {A : Set} d l q (m : A),
                       nthLast d l m -> nthLast d (q :: l) m.
Proof.
  intros A d l q m nl.
  inversion nl as [B C D E G H].
  rewrite -> app_comm_cons.
  constructor.
Qed.

Lemma nthNthLast_2 : forall {A : Set} d l q (m : A),
                       nthLast d l m -> nthLast (S d) (l ++ [q]) m.
Proof.
  intros A d l q m nl.
  inversion nl as [B C D E G H].
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  replace (S (ll (m :: C))) with (ll (m :: C ++ [q])).
  constructor.

  rewrite -> app_comm_cons.
  rewrite -> app_length.
  simpl.
  omega.
Qed.

Lemma nthNthLast : forall {A : Set} d l q (m : A),
                     S d <= ll l -> nth (ll l - (S d)) l q = m -> nthLast (S d) l m.
Proof.
  intros A.

  induction d;
  [ apply (rev_ind (fun l => forall (q m : A),
                               1 <= ll l -> nth (ll l - 1) l q = m -> nthLast 1 l m));
    [ intros q m lm ln;
      inversion lm
    | intros x l IHl q m l1 ln;
      rewrite <- rev_nth in ln;
      [ rewrite -> rev_app_distr in ln;
        simpl in ln;
        rewrite -> ln;
        apply (makeNthLast l [] m)
      | rewrite -> app_length;
        simpl;
        omega ]]
  | apply (rev_ind (fun l =>
                      forall (q m : A),
                        S (S d) <= ll l -> nth (ll l - S (S d)) l q = m -> nthLast (S (S d)) l m));
  [ intros q m ssd ln;
    simpl in ssd;
    omega
  | intros x l IHl q m l1 ln;
    apply nthNthLast_2;
    eapply IHd;
    [ rewrite -> app_length in l1;
      simpl in l1;
      omega
    | rewrite -> app_nth1 in ln;
      [ rewrite -> app_length in ln;
        simpl in ln;
        replace (ll l + 1 - S (S d)) with (ll l - S d) in ln; [exact ln | omega]
      | rewrite -> app_length;
        simpl;
        rewrite -> app_length in l1;
        simpl in l1;
        omega ]]]].
Qed.

Lemma nthLastNth : forall {A : Set} d l (m : A), nthLast d l m -> forall q, nth (ll l - d) l q = m.
Proof.
  intros A d l m n.
  inversion n as [b c e G H J].
  replace (ll (b ++ m :: c) - ll (m :: c)) with (ll b);
  [ revert b c e J d G l n H;
    induction b;
    [ reflexivity
    | intros c e eeq d ld l n Q q;
      destruct l as [|x l];
      [ inversion Q
      | assert (lcdr : b ++ m :: c = l);
        [ rewrite <- eeq;
          inversion Q;
          auto
        | eapply (IHb _ m _ d _ l);
          [ rewrite <- ld;
            rewrite -> eeq;
            rewrite <- lcdr;
            constructor
          | exact lcdr ]]]]
  | rewrite -> app_length;
    omega ].

Grab Existential Variables.
simpl.
simpl in ld.
trivial.

reflexivity.
Qed.


Theorem resolveNthLast : forall {A : Set} (n : nat) (L : list A),
                           {a | nthLast n L a} + ({a | nthLast n L a} -> False).
Proof.
  intros A n L.
  set (l := ll L).
  destruct (le_dec n l) as [n_le_l | n_nle_l].
  destruct (slice_list_le (l - n) L) as [l1 [l2 [lapp lll]]].
  unfold l.
  unfold l in n_le_l.
  omega.

  assert (ll2 : ll l2 = n).
  assert (lladd : ll l1 + ll l2 = l).
  unfold l.
  rewrite <- lapp.
  symmetry.
  apply app_length.
  omega.

  destruct l2 as [|a l2].

  apply inr.
  intro Q.
  destruct Q as [a nla].
  compute in ll2.
  rewrite <- ll2 in nla.
  inversion nla.

  apply inl.
  exists a.
  rewrite <- ll2.
  rewrite <- lapp.
  constructor.

  assert (n_g_l : n > l).
  omega.
  apply inr.
  intro Q.
  destruct Q as [a nla].
  inversion nla as [B C D E F G].
  assert (l = (ll B) + n).
  rewrite <- E.
  unfold l.
  rewrite <- F.
  apply app_length.
  omega.
Qed.

Theorem nthLastUnique : forall {A : Set} n L (a b : A), nthLast n L a -> nthLast n L b -> a = b.
Proof.
  intros A.
  induction n.
  intros L a b nla.
  inversion nla.

  destruct n.
  intros L a b nla nlb.
  inversion nla. (* TODO *)
  destruct M.
  inversion nlb.
  destruct M.
  rewrite -> H5 in H4.
  rewrite -> H2 in H1.
  rewrite <- H1 in H4.
  symmetry.
  apply (app_inj_tail L1 L0).
  trivial.
  inversion H3.
  inversion H0.

  intros L a b nla nlb.
  inversion nla.
  inversion nlb.

  assert (ll L0 + S (S n) = ll L).
  rewrite <- H0.
  replace (S (ll M)) with (ll (a0 :: M)).
  rewrite <- H1.
  symmetry.
  apply app_length.
  reflexivity.

  assert (ll L1 + S (S n) = ll L).
  rewrite <- H3.
  replace (S (ll M0)) with (ll (a1 :: M0)).
  rewrite <- H4.
  symmetry.
  apply app_length.
  reflexivity.

  assert (ll L0 = ll L1).
  omega.

  assert (a0 :: M = a1 :: M0).
  apply (app_ll L0 (a0 :: M) L1 (a1 :: M0)).
  rewrite -> H4.
  auto.
  trivial.
  rewrite -> H5 in H8.
  rewrite -> H2 in H8.
  inversion H8.
  reflexivity.
Qed.

Inductive ResolveBackReference {A : Set} : forall (len dist : nat) (input output : list A), Prop :=
| rbrZero : forall dist input, ResolveBackReference 0 dist input input
| rbrSucc : forall n dist input output1 X,
              ResolveBackReference n dist input output1 ->
              nthLast dist output1 X ->
              ResolveBackReference (S n) dist input (output1 ++ [X]).

Lemma rbr_brlen : forall {A : Set} (len dist : nat) (input output : list A),
                    ResolveBackReference len dist input output ->
                    ll output = ll input + brlen [inr A (len, dist)].
Proof.
  intros A len. 
  induction len.
  intros dist input output rbr.
  inversion rbr.
  simpl.
  omega.
  intros dist input output rbr.
  inversion rbr.
  rewrite -> app_length.
  simpl.
  rewrite -> (IHlen dist input).
  simpl.
  omega.
  trivial.
Qed.

(** Example from RFC Page 10 with X = 1 and Y = 2*)
Goal ResolveBackReference 5 2 [1; 2] [1; 2;  1; 2; 1; 2; 1] (** = [1; 2] ++ [1; 2; 1; 2; 1] *).
Proof.
  apply (rbrSucc 4 2 [1; 2] [1; 2; 1; 2; 1; 2] 1).
  apply (rbrSucc 3 2 [1; 2] [1; 2; 1; 2; 1] 2).
  apply (rbrSucc 2 2 [1; 2] [1; 2; 1; 2] 1).
  apply (rbrSucc 1 2 [1; 2] [1; 2; 1] 2).
  apply (rbrSucc 0 2 [1; 2] [1; 2] 1).
  apply rbrZero.
  apply (makeNthLast [] [2]).
  apply (makeNthLast [1] [1]).
  apply (makeNthLast [1; 2] [2]).
  apply (makeNthLast [1; 2; 1] [1]).
  apply (makeNthLast [1; 2; 1; 2] [2]).
Qed.

Theorem ResolveBackReferenceUnique : forall {A : Set} (len dist : nat) (input : list A) output1 output2,
                                       ResolveBackReference len dist input output1 ->
                                       ResolveBackReference len dist input output2 ->
                                       output1 = output2.
Proof.
  intros A.
  induction len.
  intros dist input output1 output2 rbr1 rbr2.
  inversion rbr1 as [B C D E F G|B C D E F G H I J K L].
  inversion rbr2 as [B1 C1 D1 E1 F1 G1|B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1].
  rewrite <- G1.
  auto.

  intros dist input output1 output2 rbr1 rbr2.
  inversion rbr1 as [B C D E F G|B C D E F G H I J K L].
  inversion rbr2 as [B1 C1 D1 E1 F1 G1|B1 C1 D1 E1 F1 G1 H1 I1 J1 K1 L1].
  assert (Eeq : E = E1).
  apply (IHlen dist input).
  trivial.
  trivial.
  rewrite <- Eeq.
  rewrite -> Eeq in H.
  assert (Feq : F = F1).
  apply (nthLastUnique dist E1).
  trivial.
  trivial.
  rewrite <- Feq.
  reflexivity.
Qed.

(*Theorem resolveNthLast' : forall {A : Set} (n : nat) (L : list A),
                            {a | nthLast n (rev L) a} + ({a | nthLast n (rev L) a} -> False).
Proof.
  intros A n L.
  destruct n.
  apply inr.
  intro Q.
  destruct Q as [a nl].
  inversion nl.
  destruct (slice_list n L) as [[l1 [l2 [lapp l1l]]]|no].
  destruct l2 as [|l2a l2].
  apply inr.
  intro Q.
  destruct Q as [a nl].
  inversion nl.

  assert (K : rev (L0 ++ a0 :: M) = L).
  rewrite <- rev_involutive.
  f_equal.
  auto.

  rewrite <- lapp in K.
  rewrite -> rev_app_distr in K.
  rewrite -> cons_rev_1 in K.
  destruct (app_ll (rev M) ([a0] ++ rev L0) l1 []) as [K1 K2].
  rewrite -> app_assoc.
  exact K.
  rewrite -> rev_length.
  rewrite -> l1l.
  trivial.
  inversion K2.

  apply inl.
  exists l2a.
  replace (rev L) with ((rev l2) ++ l2a :: rev l1).
  replace (S n) with (ll (l2a :: rev l1)).
  apply (makeNthLast (rev l2) (rev l1) l2a).
  replace (ll (_ :: rev l1)) with (S (ll (rev l1))).
  f_equal.
  rewrite -> rev_length.
  exact l1l.
  reflexivity.
  rewrite <- lapp.
  rewrite -> rev_app_distr.
  rewrite -> cons_rev_1.
  rewrite <- app_assoc.
  reflexivity.

  apply inr.
  intro Q.
  destruct Q as [a nl].
  inversion nl.
  contradict no.
  exists (rev M).
  exists (rev (L0 ++ [a0])).
  split.
  rewrite <- rev_app_distr.
  rewrite <- app_assoc.
  rewrite <- rev_involutive.
  f_equal.
  auto.
  rewrite -> rev_length.
  trivial.
Defined.

Theorem ResolveBackReferenceDec' : forall {A : Set} (len dist : nat) (input : list A), 
                                     {output | ResolveBackReference len dist (rev input) (rev output)} +
                                     ({output | ResolveBackReference len dist (rev input) (rev output)} -> False).
Proof.
  intro A.
  induction len.
  intros dist input.
  apply inl.
  exists input.
  constructor.
  intros dist input.
  destruct (IHlen dist input) as [[o rbr]|no].
  destruct (resolveNthLast' dist o) as [[a nl]|no].
  apply inl.
  exists (a :: o).
  rewrite -> cons_rev_1.
  constructor.
  exact rbr.
  exact nl.

  apply inr.
  intro Q.
  destruct Q as [o' rbr'].
  inversion rbr'.
  contradict no.
  assert (K : rev o = output1).
  apply (ResolveBackReferenceUnique _ _ _ _ _ rbr H1).
  rewrite -> K.
  exists X.
  auto.

  apply inr.
  intro Q.
  destruct Q as [o rbr].
  inversion rbr.
  contradict no.
  exists (rev output1).
  rewrite -> rev_involutive.
  auto.
Defined.*)

Theorem ResolveBackReferenceDec : forall {A : Set} (len dist : nat) (input : list A), 
                                    {output | ResolveBackReference len dist input output} +
                                    ({output | ResolveBackReference len dist input output} -> False).
Proof.
  intros A.
  induction len as [|len].
  intros dist input.
  apply inl.
  exists input.
  constructor.

  intros dist input.
  destruct (IHlen dist input) as [[b rbrb]|no].
  destruct (resolveNthLast dist b) as [[a nla]|no].
  apply inl.
  exists (b ++ [a]).
  constructor.
  trivial.
  trivial.

  apply inr.
  intro Q.
  destruct Q as [out rbr].
  inversion rbr.
  assert (K : b = output1).
  apply (ResolveBackReferenceUnique len dist input).
  trivial.
  trivial.
  contradict no.
  exists X.
  rewrite -> K.
  trivial.

  apply inr.
  intro Q.
  destruct Q as [o r].
  inversion r.
  contradict no.
  exists output1.
  trivial.
Qed.

Inductive ResolveBackReferences {A : Set} : forall (input : SequenceWithBackRefs A) (output : list A), Prop :=
| ResolveNil : ResolveBackReferences (A:=A) nil nil
| ResolveByte : forall a b (c : A), ResolveBackReferences a b ->
                                    ResolveBackReferences (a ++ [inl c]) (b ++ [c])
| ResolveRef : forall a (b c : list A) len dist, ResolveBackReferences a b ->
                                                 ResolveBackReference len dist b c ->
                                                 ResolveBackReferences (a ++ [inr (len, dist)]) c.

Lemma rbrs_brlen : forall {A : Set} input (output : list A),
                     ResolveBackReferences input output ->
                     ll output = brlen input.
Proof.
  intro A.
  apply (rev_ind (fun input =>
                    forall (output : list A),
                    ResolveBackReferences input output -> ll output = brlen input)).
  intros output rbrs.
  inversion rbrs.
  reflexivity.
  destruct a.
  inversion H.
  inversion H.
  destruct a.
  inversion H.
  inversion H.

  intros x l H output H0.
  inversion H0.
  destruct l.
  reflexivity.
  inversion H2.

  rewrite -> app_brlen.
  rewrite -> app_length.
  simpl.
  f_equal.
  destruct (app_ll_r a [inl c] l [x]) as [H4 H5].
  trivial.
  reflexivity.
  rewrite -> H4.
  apply H.
  rewrite <- H4.
  trivial.

  rewrite -> app_brlen.
  destruct (app_ll_r a [inr (len, dist)] l [x]) as [H6 H7].
  trivial.
  reflexivity.
  rewrite -> H6.
  rewrite <- (H b).
  apply rbr_brlen.
  trivial.
  rewrite <- H6.
  trivial.
Qed.

Theorem ResolveBackReferencesUnique : forall {A : Set} (input : SequenceWithBackRefs A) output1 output2,
                                        ResolveBackReferences input output1 ->
                                        ResolveBackReferences input output2 ->
                                        output1 = output2.
Proof.
  intros A input output1 output2 rbr1.
  revert output2.
  dependent induction rbr1.
  intros o2 rbr2.
  inversion rbr2.
  reflexivity.
  destruct a.
  inversion H.
  inversion H.
  destruct a.
  inversion H.
  inversion H.

  intros o2 rbr2.
  inversion rbr2.
  destruct a.
  inversion H0.
  inversion H0.
  destruct (app_inj_tail a a0 (inl c) (inl c0)) as [aa0 cccc0].
  auto.
  inversion cccc0.
  assert (B : b = b0).
  apply IHrbr1.
  rewrite -> aa0.
  trivial.
  rewrite -> B.
  reflexivity.

  destruct (app_inj_tail a0 a (inr A (len, dist)) (inl c)) as [? cfail].
  trivial.
  inversion cfail.

  intros o2 rbr.
  inversion rbr.
  destruct a.
  inversion H1.
  inversion H1.
  destruct (app_inj_tail a0 a (inl c0) (inr A (len, dist))) as [? cfail].
  trivial.
  inversion cfail.

  destruct (app_inj_tail a0 a (inr (len0, dist0)) (inr (len, dist))) as [a0a inr0inr].
  trivial.
  inversion inr0inr as [[len0len dist0dist]].
  assert (K : b = b0).
  apply IHrbr1.
  rewrite <- a0a.
  trivial.
  apply (ResolveBackReferenceUnique len dist b).
  trivial.
  rewrite <- len0len.
  rewrite <- dist0dist.
  rewrite -> K.
  trivial.
Qed.

(** code that was more efficient before we used intrinsics ...

Theorem ResolveBackReferencesDec' : forall {A : Set} (input : SequenceWithBackRefs A),
                                      {output | ResolveBackReferences (rev input) (rev output)} +
                                      ({output | ResolveBackReferences (rev input) (rev output)} -> False).
Proof.
  intro A.
  induction input as [| a input].
  apply inl.
  exists (@nil A).
  constructor.

  destruct IHinput as [[o' rbr']|no].
  destruct a as [a | [len dist]].
  apply inl.
  exists (a :: o').
  rewrite -> cons_rev_1.
  rewrite -> cons_rev_1.
  constructor.
  auto.
  
  destruct (ResolveBackReferenceDec' len dist o') as [[newout Newout]|no].
  apply inl.
  exists newout.
  rewrite -> cons_rev_1.
  apply (ResolveRef (rev input) (rev o') (rev newout) len dist).
  trivial.
  trivial.

  apply inr.
  intro Q.
  destruct Q as [output rbr].
  rewrite -> cons_rev_1 in rbr.
  inversion rbr.
  destruct (rev input).
  inversion H0.
  inversion H0.
  destruct (app_ll_r a [inl c] (rev input) [inr (len, dist)]) as [K1 K2].
  auto.
  auto.
  inversion K2.
  contradict no.
  exists output.
  destruct (app_ll_r a [inr (len0, dist0)] (rev input) [inr (len, dist)]) as [K1 K2].
  auto.
  auto.
  inversion K2 as [[K3 K4]].
  rewrite <- K3.
  rewrite <- K4.
  rewrite -> K1 in H0.
  rewrite <- (ResolveBackReferencesUnique _ _ _ H0 rbr').
  auto.

  apply inr.
  intro Q.
  destruct Q as [output rbr'].
  rewrite -> cons_rev_1 in rbr'.
  inversion rbr'.
  destruct (rev input).
  inversion H0.
  inversion H0.
  contradict no.
  destruct (app_ll_r a0 [inl c] (rev input) [a]) as [K1 K2].
  auto.
  auto.
  exists (rev b).
  rewrite <- K1.
  rewrite -> rev_involutive.
  auto.
  contradict no.
  destruct (app_ll_r a0 [inr (len, dist)] (rev input) [a]) as [K1 K2].
  auto.
  auto.
  exists (rev b).
  rewrite <- K1.
  rewrite -> rev_involutive.
  auto.
Defined.

Theorem ResolveBackReferencesDec : forall {A : Set} (input : SequenceWithBackRefs A),
                                     {output | ResolveBackReferences input output} +
                                     ({output | ResolveBackReferences input output} -> False).
Proof.
  intros A input.
  destruct (ResolveBackReferencesDec' (rev input)) as [[output' rbr']|no].
  apply inl.
  rewrite -> rev_involutive in rbr'.
  exists (rev output').
  exact rbr'.

  apply inr.
  intro Q.
  destruct Q as [output rbr].
  contradict no.
  exists (rev output).
  rewrite -> rev_involutive.
  rewrite -> rev_involutive.
  exact rbr.
Defined. *)
Theorem ResolveBackReferencesDec : forall {A : Set} (input : SequenceWithBackRefs A),
                                     {output | ResolveBackReferences input output} +
                                     ({output | ResolveBackReferences input output} -> False).
Proof.
  intros A.
  apply rev_ind_computational.
  apply inl.
  exists (nil (A:=A)).
  constructor.
  intros x l X.
  destruct X as [[o rbr]|no].
  destruct x as [direct | [len dist]].
  apply inl.
  exists (o ++ [direct]).
  constructor.
  trivial.
  destruct (ResolveBackReferenceDec len dist o) as [[newout Newout] | no].
  apply inl.
  exists newout.
  apply (ResolveRef _ o).
  trivial.
  trivial.

  apply inr.
  intro Q.
  destruct Q as [o2 rbr2].
  inversion rbr2.
  destruct l.
  inversion H0.
  inversion H0.
  destruct (app_inj_tail a l (inl c) (inr (len, dist))) as [? cfail].
  trivial.
  inversion cfail.

  contradict no.
  destruct (app_inj_tail a l (inr (len0, dist0)) (inr (len, dist))) as [agood cgood].
  trivial.
  inversion cgood as [[lengood distgood]].
  exists o2.
  rewrite <- lengood.
  rewrite <- distgood.
  replace o with b.
  trivial.
  apply (ResolveBackReferencesUnique a).
  trivial.
  rewrite -> agood.
  trivial.

  apply inr.
  intro Q.
  destruct Q as [o r].
  inversion r.
  destruct l.
  inversion H0.
  inversion H0.
  contradict no.
  exists b.
  replace l with a.
  trivial.
  apply (app_inj_tail a l (inl c) x).
  trivial.
  contradict no.
  exists b.
  replace l with a.
  trivial.
  apply (app_inj_tail a l (inr (len, dist)) x).
  trivial.
Qed.

Inductive BackRefBounded {A} (minlen maxlen mindist maxdist : nat) : (A + (nat * nat))%type -> Prop :=
| brbL : forall a, BackRefBounded minlen maxlen mindist maxdist (inl a)
| brbR : forall l d, minlen <= l -> l <= maxlen -> mindist <= d -> d <= maxdist -> BackRefBounded minlen maxlen mindist maxdist (inr (l, d)).

Definition BackRefsBounded {A : Set} (minlen maxlen mindist maxdist : nat) := Forall (@BackRefBounded A minlen maxlen mindist maxdist).

Lemma RBRFirstArg : forall {A : Set} l h d d' (x : A),
                      nthLast h d x ->
                      ResolveBackReference l h (d ++ [x]) d' -> ResolveBackReference (S l) h d d'.
Proof.
  intros A.
  induction l.

  intros h d d' x nl rb.
  inversion rb.
  constructor.
  constructor.
  trivial.

  intros h d d' x nl rb.
  inversion rb.
  constructor.
  apply (IHl _ _ _ x).
  auto.
  auto.
  auto.
Defined.
