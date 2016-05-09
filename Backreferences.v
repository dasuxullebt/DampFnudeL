Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Lists.List.
Require Import Omega.
Require Import Program.
Import ListNotations.

Require Import Combi.
Require Import Shorthand.
Require Import LSB.
Require Import String.
Require Import Repeat.
Require Import ArrayInduction.

(** A list with backreferences. Every element is either a direct byte,
or a pair of numbers, the first component being the length, the second
component being the distance. We do not use an own inductive
definition here to be able to use list functions. *)

(* SWBR1 *)
Function SequenceWithBackRefs A := (list (A+(nat*nat))%type).
(* SWBR2 *)
				   
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

(* NTHLAST1 *)				     
Inductive nthLast {A : Set}
 : forall (n : nat) (L : list A) (a : A), Prop :=
| makeNthLast : forall L M a, nthLast (ll (a :: M)) (L ++ a :: M) a.
(* NTHLAST2 *)
				     
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

(* EXAMPLE1 *)
(** Example from RFC Page 10 with X = 1 and Y = 2*)
Goal ResolveBackReference 5 2 [1; 2] [1; 2;  1; 2; 1; 2; 1]
                         (** = [1; 2] ++ [1; 2; 1; 2; 1] *).
(* EXAMPLE2 *)
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

(* backreferences without lengths *)

(** Step 1: (len, dist) -> dist, dist, ... n times *)

(* BACKREFSLENGHTONE1 *)
Fixpoint BackRefsLengthOne {A : Set}
         (swbr : SequenceWithBackRefs A) :=
  match swbr with
    | [] => []
    | (inl x :: r) => inl x :: BackRefsLengthOne r
    | (inr (l, d) :: r) => repeat l (inr d) ++
                                  (BackRefsLengthOne r)
  end.
(* BACKREFSLENGHTONE2 *)

Functional Scheme BackRefsLengthOne_ind := Induction for BackRefsLengthOne Sort Prop.

Function BackRefsLengthOneMap {A : Set} (l : list (A + nat)%type) :=
  match l with
    | [] => []
    | inl x :: r => inl x :: BackRefsLengthOneMap r
    | inr d :: r => inr (1, d) :: BackRefsLengthOneMap r
  end.

Lemma BackRefsLengthOneApp :
  forall {A : Set} (a b : SequenceWithBackRefs A),
    BackRefsLengthOne (a ++ b) =
    BackRefsLengthOne a ++ BackRefsLengthOne b.
Proof.
  intros A a.
  induction a as [|x a IHa];
  [ auto
  |].
  destruct x as [x | [l d]];
  [ intro b;
    simpl;
    rewrite -> IHa;
    reflexivity
  | intro b;
    simpl;
    rewrite <- app_assoc;
    rewrite -> IHa;
    reflexivity ].
Qed.

Lemma BackRefsLengthOneCorrect'' :
  forall {X : Set} l d A B (C : X),
    (ResolveBackReference l d A B /\
     ResolveBackReference 1 d B (B ++ [C])) <->
    ResolveBackReference (S l) d A (B ++ [C]).
Proof.
  intros X l d A B C.
  split.
  intros [D E]. 
  revert l d A B C D E.  
  induction l.

  intros d A B C rbr0 rbr1.
  inversion rbr0.
  trivial.
  
  intros d A B C rbrsl rbr1.
  constructor.
  trivial.
  inversion rbr1 as [| D E F G H I J K L M N].
  destruct (app_ll_r G [H] B [C] N) as [O P]; [reflexivity | ].
  inversion P as [Q].
  rewrite <- Q.
  rewrite -> O in J.
  trivial.

  intro rbrsl.
  inversion rbrsl as [| D E F G H I J K L M N].
  split.
  destruct (app_ll_r G [H] B [C] N) as [O P]; [reflexivity | ].
  rewrite -> O in I.
  trivial.
  constructor.
  destruct (app_ll_r G [H] B [C] N) as [O P]; [reflexivity | ].
  rewrite -> O.
  constructor.
  trivial.  
Qed.

Lemma BackRefsLengthOneCorrect' :
  forall {A : Set} a len dist (l : list A),
    ResolveBackReferences (a ++ [inr (len, dist)]) l ->
    ResolveBackReferences (a ++ (repeat len (inr (1, dist)))) l.
Proof.
  intros A a len.
  induction len as [|len IHlen].
  
  intros dist l rbr.
  inversion rbr as [B C|B C D E F G|B C D E F G H I J].
  destruct a; inversion B.
  destruct (app_ll_r _ _ _ _ F) as [H I]; [reflexivity | ].
  inversion I.
  
  destruct (app_ll_r _ _ _ _ I) as [K L]; [reflexivity | ].
  inversion L as [[M N]].
  rewrite -> M in H.
  rewrite -> N in H.
  inversion H as [O P Q R S T|].
  rewrite <- T.
  simpl.
  rewrite -> app_nil_r.
  rewrite <- K.
  trivial.

  intros dist l rbr.
  inversion rbr as [B C|B C D E F G|B C D E F G H I J].
  destruct a; inversion B.
  destruct (app_ll_r _ _ _ _ F) as [I J]; [reflexivity | ].
  inversion J.

  destruct (app_ll_r _ _ _ _ I) as [K L]; [reflexivity | ].
  inversion L as [[M N]].
  rewrite -> M in H.
  rewrite -> N in H.
  inversion H as [|O P Q R S T U V W X Y].

  replace (Datatypes.S len) with (len + 1); [ | omega].
  rewrite <- repeat_add.
  simpl.

  rewrite -> app_assoc.
  econstructor.
  apply IHlen.
  replace [inr A (len, dist)] with ([] ++ [inr A (len, dist)]).
  eapply ResolveRef.
  rewrite <- K.
  exact G.
  exact T.
  reflexivity. 

  constructor.
  constructor.
  trivial.
Qed.


Lemma BackRefsLengthOneCorrect :
  forall {A : Set} (l : list A) swbr,
    ResolveBackReferences swbr l ->
    ResolveBackReferences (map (fun x =>
                                  match x with
                                    | inl c => inl c
                                    | inr d => inr (1, d)
                                  end) (BackRefsLengthOne swbr)) l.
Proof.
  intros A l c.
  revert c l.
  apply (rev_ind (fun c => forall (l : list A),
                             ResolveBackReferences c l ->
                             ResolveBackReferences (map (fun x =>
                                                           match x with
                                                             | inl c => inl c
                                                             | inr d => inr (1, d)
                                                           end) 
                                                        (BackRefsLengthOne c)) l));
  [ intros l rbrl;
    inversion rbrl;
    solve
      [ constructor
      | match goal with
          | A : ?a ++ [?c] = [] |- _ => destruct a; inversion A
        end ]
  | ].
  intros x c IHc l rbrl.  
  inversion rbrl as [|B C D E F G|].
  + constructor.
  + rewrite -> BackRefsLengthOneApp.
    rewrite -> map_app.
    simpl.
    constructor.
    assert (K : B = c /\ [inl D] = [x]);
    [ apply app_ll_r; [trivial | reflexivity]
    | destruct K as [K1 K2];
      rewrite -> K1;
      apply IHc;
      rewrite <- K1;
      trivial ].
  + rewrite -> BackRefsLengthOneApp.
    rewrite -> map_app.
    simpl.
    rewrite -> app_nil_r.
    rewrite -> repeat_map.
    apply BackRefsLengthOneCorrect'.
    destruct (app_ll_r _ _ _ _ H).
    reflexivity.
  
    econstructor.
    rewrite -> H3. (* TODO *)
    apply IHc.
    rewrite <- H3.
    apply H0.
    trivial.
Qed.

Fixpoint BackRefsLengthOne_ {A : Set}
         (swbr : SequenceWithBackRefs A) :=
  match swbr with
    | [] => []
    | (inl x :: r) => inl x :: BackRefsLengthOne_ r
    | (inr (l, d) :: r) => repeat l (inr (1, d)) ++ (BackRefsLengthOne_ r)
  end.

Functional Scheme BackRefsLengthOne__ind := Induction for BackRefsLengthOne_ Sort Prop.

Lemma BackRefsLengthOne_Lemma : forall {A : Set} (swbr : SequenceWithBackRefs A),
                                  BackRefsLengthOne_ swbr =
                                  (map (fun x =>
                                          match x with
                                            | inl c => inl c
                                            | inr d => inr (1, d)
                                          end) (BackRefsLengthOne swbr)).
Proof.
  intro A.
  induction swbr as [|[c | [l d]] swbr IH].
  + reflexivity.
  + simpl.
    rewrite -> IH.
    reflexivity.
  + simpl.
    rewrite -> map_app.
    rewrite -> repeat_map.
    rewrite -> IH.
    reflexivity.
Qed.

Lemma BackRefsLengthOneBounded :
  forall {A : Set} (swbr : SequenceWithBackRefs A)
         minlen maxlen mindist maxdist,
    BackRefsBounded minlen maxlen mindist maxdist swbr ->
    BackRefsBounded 1 1 mindist maxdist (map (fun x =>
                                          match x with
                                            | inl c => inl c
                                            | inr d => inr (1, d)
                                          end) (BackRefsLengthOne swbr)).
Proof.
  intros A swbr minlen maxlen mindist maxdist brb.
  rewrite <- BackRefsLengthOne_Lemma.
  functional induction (BackRefsLengthOne_ swbr).
  constructor.
  constructor.
  constructor.
  apply IHl.
  inversion brb.
  trivial.
  apply app_forall.
  apply repeat_forall.
  constructor.
  omega.
  omega.
  inversion brb.
  inversion H1. (* TODO *)
  auto.
  inversion brb.
  inversion H1.
  auto.
  apply IHl.
  inversion brb.
  auto.
Qed.

Lemma BackRefsLengthOneLength_ :
  forall {A : Set} (swbr : SequenceWithBackRefs A) mnd mxd,
    BackRefsBounded 1 1 mnd mxd swbr ->
    brlen swbr = ll swbr.
Proof.
  induction swbr as [| a swbr IHswbr].
  intros.
  reflexivity.
  intros mnd mxd brb.
  destruct a as [a | [b c]].
  simpl.
  f_equal.
  apply (IHswbr mnd mxd).
  inversion brb.
  trivial.

  inversion brb.
  match goal with
    | Quak : BackRefBounded 1 1 mnd mxd (inr (b, c)) |- _ => inversion Quak
  end.
  replace b with 1; [ | omega].
  simpl.
  f_equal.
  eapply IHswbr.
  match goal with
    | Quak : Forall (BackRefBounded 1 1 mnd mxd) swbr |- _ => exact Quak
  end.
Qed.

Lemma BackRefsLengthOneLength :
  forall {A : Set} (swbr : SequenceWithBackRefs A) l mnd mxd,
    BackRefsBounded 1 1 mnd mxd swbr ->
    ResolveBackReferences swbr l ->
    ll swbr = ll l.
Proof.
  intros A swbr l mnd mxd brb rbr.
  erewrite <- BackRefsLengthOneLength_.
  erewrite -> rbrs_brlen.
  reflexivity.
  trivial.
  exact brb.
Qed.

(* TODO: This proof is so extremely gross :( *)
Lemma BackRefLemma : forall {A : Set} (n k mnd mxd : nat)
                            (input : SequenceWithBackRefs A) (output : list A),
                       BackRefsBounded 1 1 mnd mxd input ->
                       ResolveBackReferences input output ->
                       nth_error input n = Some (inr (1, k)) ->
                       nth_error output n = nth_error output (n - k).
Proof.
  intros a n k mnd mxd input output brb rbr nerr.
  assert (Loutput : ll input = ll output);
  [ eapply BackRefsLengthOneLength; eauto
  | ].

  destruct (proj1 (nth_split _ _ _) nerr) as [o' [o'' [olen oapp]]].

  revert o'' n k mnd mxd input output brb rbr nerr Loutput o' olen oapp.
  apply (rev_ind (fun o'' => forall (n k mnd mxd : nat)
     (input : SequenceWithBackRefs a) (output : list a),
   BackRefsBounded 1 1 mnd mxd input ->
   ResolveBackReferences input output ->
   nth_error input n = Some (inr (1, k)) ->
   ll input = ll output ->
   forall o' : list (a + nat * nat),
   ll o' = n ->
   input = o' ++ [inr (1, k)] ++ o'' ->
   nth_error output n = nth_error output (n - k))).

  intros n k mnd mxd input output brb rbr nerr Loutput o' olen oapp.
  rewrite -> app_nil_r in oapp.
  rewrite -> oapp in rbr.
  inversion rbr as [ |A B C D E F|A B C D E F G H I];
  [ rewrite -> nth_error_nil;
    symmetry; apply nth_error_nil
  | apply app_inj_tail in E;
    destruct E as [? E];
    inversion E
  | ].
  assert (D1 : D = 1); (* TODO: MAKE THIS PROOF NAME INDEPENDENT !!!1! *)
  [ rewrite <- H in oapp;
    rewrite -> oapp in brb;
    unfold BackRefsBounded in brb;
    apply forall_app in brb;
    destruct brb as [brb1 brb2];
    inversion brb2;
    [ match goal with
        | K : BackRefBounded 1 1 mnd mxd (inr (D, E)) |- _ => inversion K
      end;
      omega ]
  | ].
  rewrite -> D1 in G.
  inversion G.
  inversion H2.
  rewrite (proj2 (nth_split _ n X)); [ | ].
  symmetry.
  eapply (proj2 (nth_split _ (n - k) X)); [ ].
  exists L.
  exists (M ++ [X]).
  split; [ | ].
  replace k with E; [ | ].
  assert (ll output = S (ll (L ++ a0 :: M))).
  rewrite <- H5.
  rewrite -> app_length.
  simpl.
  rewrite <- H7.
  omega.
  rewrite -> app_length in H9.
  rewrite <- Loutput in H9.
  rewrite -> oapp in H9.
  rewrite -> app_length in H9.
  rewrite olen in H9.
  simpl in H9.
  simpl in H6.
  rewrite -> H6 in H9.
  omega.
  apply app_inj_tail in H.
  destruct H.
  inversion H9.
  reflexivity.

  simpl.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  reflexivity.

  exists (L ++ X :: M) (@nil a).
  split.
  assert (ll output = S (ll (L ++ a0 :: M))).
  rewrite <- H5.
  rewrite -> app_length.
  simpl.
  rewrite <- H7.
  omega.

  rewrite <- Loutput in H9.
  rewrite -> oapp in H9.
  rewrite -> app_length in H9.
  simpl in H9.
  rewrite -> olen in H9.
  rewrite -> H8 in H9.
  omega.
  rewrite -> app_nil_r.
  reflexivity.

  (* induction step *)
  intros x l IHl n k mnd mxd input output brb rbr nerr Loutput o' llo inp.
  rewrite -> inp in rbr.
  repeat (rewrite -> app_assoc in rbr).
  inversion rbr.

  (* inversion rbr, step 1 *)

  rewrite -> nth_error_nil.
  symmetry.
  apply nth_error_nil.

  (* inversion rbr, step 2 *)

  replace (nth_error (b ++ [c]) n) with (nth_error b n).
  replace (nth_error (b ++ [c]) (n - k)) with (nth_error b (n - k)).
  eapply IHl.
  rewrite -> inp in brb.
  repeat (rewrite -> app_assoc in brb).
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  apply brb1.
  inversion rbr.
  apply app_inj_tail in H.
  rewrite <- (proj1 H).
  exact H0.
  apply app_inj_tail in H.
  rewrite <- (proj1 H).
  exact H0.
  apply app_inj_tail in H.
  rewrite <- (proj1 H).
  exact H0.
  
  apply (proj2 (nth_split _ _ _)).
  exists o' l.
  split.
  trivial.
  symmetry.
  apply app_assoc.

  assert (K : ll (((o' ++ [inr (1, k)]) ++ l) ++ [x]) = ll (b ++ [c])).
  rewrite -> H1.
  repeat (rewrite -> app_assoc in inp).
  rewrite <- inp.
  exact Loutput.
  rewrite -> app_length in K.
  replace (ll (b ++ [c])) with (ll b + 1) in K.
  simpl in K.
  omega.
  rewrite -> app_length.
  reflexivity.
  exact llo.
  symmetry.
  apply app_assoc.
  apply nth_extend.
  assert (ll b + 1 = ll input).
  rewrite -> Loutput.
  rewrite <- H1.
  rewrite -> app_length.
  reflexivity.
  assert (ll input >= S (S n)).
  rewrite -> inp.
  rewrite -> app_length.
  rewrite -> app_length.
  rewrite -> app_length.
  simpl.
  omega.
  omega.

  apply nth_extend.
  assert (ll b + 1 = ll input).
  rewrite -> Loutput.
  rewrite <- H1.
  rewrite -> app_length.
  reflexivity.
  rewrite -> inp in H2.
  rewrite -> app_length in H2.
  rewrite -> llo in H2.
  rewrite -> app_length in H2.
  rewrite -> app_length in H2.
  simpl in H2.
  omega.

  (* inversion rbr, step 3 *)

  assert (L1: len = 1).
  apply app_inj_tail in H.
  rewrite -> inp in brb.
  rewrite <- (proj2 H) in brb.
  repeat (rewrite -> app_assoc in brb).
  apply forall_app in brb.
  destruct brb as [? brb2].
  inversion brb2.
  inversion H6.
  omega.

  rewrite -> L1 in H1.
  inversion H1.

  replace (nth_error (output1 ++ [X]) n) with (nth_error output1 n).
  replace (nth_error (output1 ++ [X]) (n - k)) with (nth_error output1 (n - k)).
  eapply IHl.
  rewrite -> inp in brb.
  repeat (rewrite -> app_assoc in brb).
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  apply brb1.

  apply app_inj_tail in H.
  destruct H.
  rewrite <- H.
  inversion H4.
  rewrite <- H13.
  trivial.

  apply (proj2 (nth_split _ _ _)).
  exists o' l.
  split.
  trivial.
  symmetry.
  apply app_assoc.

  assert (K : ll (((o' ++ [inr (1, k)]) ++ l) ++ [x]) = ll (output1 ++ [X])).
  repeat (rewrite -> app_assoc in inp).
  rewrite <- inp.
  rewrite -> H8.
  exact Loutput.
  rewrite -> app_length in K.
  replace (ll (output1 ++ [X])) with (ll output1 + 1) in K.
  simpl in K.
  omega.
  rewrite -> app_length.
  reflexivity.
  exact llo.
  symmetry.
  apply app_assoc.
  apply nth_extend.

  assert (ll output1 + 1 = ll input).
  rewrite -> Loutput.
  rewrite <- H8.
  rewrite -> app_length.
  reflexivity.
  assert (ll input >= S (S n)).
  rewrite -> inp.
  rewrite -> app_length.
  rewrite -> app_length.
  rewrite -> app_length.
  simpl.
  omega.
  omega.

  apply nth_extend.
  assert (ll output1 + 1 = ll input).
  rewrite -> Loutput.
  rewrite <- H8.
  rewrite -> app_length.
  reflexivity.
  rewrite -> inp in H9.
  rewrite -> app_length in H9.
  rewrite -> llo in H9.
  rewrite -> app_length in H9.
  rewrite -> app_length in H9.
  simpl in H9.
  omega.
Qed.

(* TODO: woanders *)

Lemma nth_error_last : forall {A : Set} (l : list A) (o : A),
    nth_error (l ++ [o]) (ll l) = Some o.
Proof.
  intro A.
  induction l as [|x l IHl].
  + reflexivity.
  + intro a.
    simpl.
    apply IHl.
Qed.
    
Lemma BackRefLemma2 : forall {A : Set} (a : A) (n mnd mxd : nat)
                             (input : SequenceWithBackRefs A) (output : list A),
    BackRefsBounded 1 1 mnd mxd input ->
    ResolveBackReferences input output ->
    nth_error input n = Some (inl a) ->
    nth_error output n = Some a.
Proof.
  intros A a n mnd mxd input output brb rbr nerr;
  destruct (proj1 (nth_split _ _ _) nerr) as [o' [o'' [olen oapp]]];
  revert o'' a n mnd mxd input output brb rbr nerr o' olen oapp;
  apply (rev_ind (fun (o'' : list (A + nat * nat)) =>
                    forall (a : A) (n mnd mxd : nat)
                           (input : SequenceWithBackRefs A) (output : list A),
                      BackRefsBounded 1 1 mnd mxd input ->
                      ResolveBackReferences input output ->
                      nth_error input n = Some (inl a) ->
                      forall o' : list (A + nat * nat),
                        ll o' = n -> input = o' ++ [inl a] ++ o'' ->
                        nth_error output n = Some a));
  [ (* o'' = [] *)
    intros a n mnd mxd input output brb rbr nerr o' llo' inpo';
    assert (L : ll input = ll output);
      [ eapply BackRefsLengthOneLength; eauto
      |  simpl in inpo';
        rewrite -> inpo' in rbr;
        inversion rbr as [|B C D E F G|B C D E F G H I J];
        [ destruct o';
          match goal with
          | H : [] = _ ++ _ |- _ => inversion H
          end
        | assert (K : nth_error (C ++ [D]) n = Some D);
          [ rewrite -> inpo' in L;
            rewrite <- G in L;
            rewrite -> app_length in L;
            rewrite -> app_length in L;
            simpl in L;
            assert (KK : n = ll C);
            [ omega
            | rewrite -> KK;
              apply nth_error_last ]
          | rewrite -> K;
            f_equal;
            assert (FF : rev (B ++ [inl D]) = rev (o' ++ [inl a]));
            [ f_equal;
              trivial
            | rewrite -> rev_app_distr in FF;
              rewrite -> rev_app_distr in FF;
              simpl in FF;
              inversion FF;
              reflexivity ]]
        | assert (K : rev (B ++ [inr (E, F)]) = rev (o' ++ [inl a]));
          [ f_equal;
            trivial
          | rewrite -> rev_app_distr in K;
            rewrite -> rev_app_distr in K;
            inversion K]]]
    | intros x l IHl a n mnd mxd input output brb rbr nerr o' llo inpo';
      assert (KK : ll input = ll output);
      [ eapply BackRefsLengthOneLength; eauto
      | rewrite -> inpo' in rbr;
        rewrite -> app_assoc in rbr;
        rewrite -> app_assoc in rbr;
        inversion rbr as [B C|B C D E F G|B C D E F G H I J];
        [ assert (BB : rev [] = rev (((o' ++ [inl a]) ++ l) ++ [x]));
          [ f_equal;
            trivial
          | rewrite -> rev_app_distr in BB;
            inversion BB ]
        | assert (K : n < ll C);
          [ rewrite -> inpo' in KK;
            rewrite -> app_length in KK;
            rewrite -> app_length in KK;
            rewrite -> app_length in KK;
            rewrite <- G in KK;
            rewrite -> app_length in KK;
            simpl in KK;
            omega
          | rewrite <- nth_extend;
            [ eapply IHl;
              [ rewrite -> inpo' in brb;
                rewrite -> app_assoc in brb;
                rewrite -> app_assoc in brb;
                apply forall_app in brb;
                apply (proj1 brb)
              | rewrite <- G in rbr;
                inversion rbr as [H I|H I J L M N|H I J L M N O P Q];
                [ destruct C; inversion I
                | apply app_inj_tail in F;
                  rewrite <- (proj1 F);
                  trivial
                | apply app_inj_tail in F; (* TODO: duplicate code *)
                  rewrite <- (proj1 F);
                  trivial ]
              | assert (L : nth_error (o' ++ [inl a]) n = Some (inl a));
                [ rewrite <- llo;
                  apply nth_error_last
                | rewrite <- nth_extend;
                  [ exact L
                  | rewrite -> app_length;
                    simpl;
                    omega ]]
              | eauto
              | symmetry;
                apply app_assoc ]
            | exact K ]]
        | assert (E1 : E = 1);
          [ apply app_inj_tail in I;
            rewrite -> inpo' in brb;
            rewrite <- (proj2 I) in brb;
            repeat rewrite -> app_assoc in brb;
            apply forall_app in brb;
            destruct brb as [brb1 brb2];
            inversion brb2 as [|K L M];
            inversion M;
            omega
          | rewrite -> E1 in H;
            inversion H as [|K L M N O P Q R S T U];
            rewrite <- nth_extend;
            [ eapply (IHl a n mnd mxd B N);
              [ rewrite -> inpo' in brb;
                repeat rewrite -> app_assoc in brb;
                rewrite <- I in brb;
                apply forall_app in brb;
                apply brb
              | inversion P as [V W X Y Z Ä|];
                rewrite <- Ä;
                trivial
              | erewrite -> nth_extend;
                [ rewrite -> inpo' in nerr;
                  repeat rewrite -> app_assoc in nerr;
                  rewrite <- I in nerr;
                  apply nerr
                | assert (LL : ll input = ll (B ++ [inr (E, F)]));
                  [ f_equal;
                    rewrite -> I;
                    repeat rewrite <- app_assoc;
                    trivial
                  | rewrite -> inpo' in LL;
                    repeat rewrite -> app_length in LL;
                    simpl in LL;
                    omega ]]
              | exact llo
              | apply app_inj_tail in I;
                rewrite -> app_assoc;
                apply (proj1 I) ]
            | rewrite -> inpo' in KK;
              rewrite <- U in KK;
              repeat rewrite -> app_length in KK;
              simpl in KK;
              omega ]]]]].
Qed.

Lemma BackRefLemma3_ :
  forall {A : Set} l d input (output : list A),
    l > 0 -> ResolveBackReference l d input output -> d < ll output.
Proof.
  intros A l d input.
  revert input l d.
  apply (rev_ind (fun input =>
                    forall (l d : nat) (output : list A),
                      l > 0 -> ResolveBackReference l d input output ->
                      d < ll output)).
  intros l d output l0 rbr.
  inversion rbr as [B C D E | B C D E F G H I J].
  omega.
  inversion H. 
  simpl.
  rewrite -> app_length.
  rewrite -> app_length.
  simpl.
  omega.

  intros x input IHinput l d output l0 rbr.
  inversion rbr as [B C D E | B C D E F G H I J].
  omega.

  inversion H.
  rewrite -> app_length.
  rewrite -> app_length.
  simpl.
  omega.
Qed.  
  
Lemma BackRefLemma3 : forall {A : Set} (n l k mnd mxd : nat)
                            (input : SequenceWithBackRefs A) (output : list A),
    ResolveBackReferences input output ->
    BackRefsBounded 1 1 mnd mxd input ->
    nth_error input n = Some (inr (l, k)) ->
    k <= n.
Proof.
  intros A n l k mnd mxd input output rbr brb nerr.
  destruct (proj1 (nth_split _ _ _) nerr) as [o' [o'' [olen oapp]]].

  revert o'' o' input n l k mnd mxd olen oapp output rbr brb nerr.
  apply (rev_ind (fun o'' => 
                    forall (o' : list (A + nat * nat))
                           (input : SequenceWithBackRefs A)
                           (n l k mnd mxd : nat),
                      ll o' = n ->
                      input = o' ++ [inr (l, k)] ++ o'' ->
                      forall output : list A,
                        ResolveBackReferences input output ->
                        BackRefsBounded 1 1 mnd mxd input ->
                        nth_error input n = Some (inr (l, k)) -> k <= n)); [|].

  intros o' input olen l k mnd mxd llo inputapp output rbr brb nerr.
  simpl in inputapp.
  rewrite -> inputapp in rbr.
  inversion rbr as [B C|B C D E F G|B C D E dist F G H I].
  destruct o'; inversion B.

  apply app_inj_tail in F.
  destruct F as [F1 F2]. inversion F2.

  apply app_inj_tail in H.
  destruct H as [Q R].
  inversion R as [[X Y]].
  rewrite -> X in G.
  rewrite -> Y in G.
  apply BackRefLemma3_ in G.
  assert (ÿ : ll input = ll output).
  eapply BackRefsLengthOneLength.
  exact brb.
  rewrite <- inputapp in rbr.
  exact rbr.

  rewrite -> inputapp in ÿ.
  rewrite -> app_length in ÿ.
  simpl in ÿ.
  omega.
  rewrite -> inputapp in brb.
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  inversion brb2.
  match goal with
  | K : BackRefBounded 1 1 mnd mxd _ |- _ => inversion K
  end.
  omega.

  intros x input IHinput.
  intros o' input0 n l k mnd mxd llo in0app output rbr brb nerr.

  rewrite -> in0app in rbr.
  inversion rbr as [K L|K L M N O P|K L M N O P Q R S].
  destruct o'; inversion K.
  rewrite -> app_comm_cons in O.
  rewrite -> app_assoc in O.
  apply app_inj_tail in O.
  destruct O as [O1 O2].
  rewrite -> O1 in N.

  eapply IHinput.
  exact llo.
  exact O1.
  rewrite -> O1.
  exact N.

  rewrite -> in0app in brb.
  rewrite -> app_assoc in brb.
  rewrite -> app_assoc in brb.
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  rewrite <- app_assoc in brb1.
  simpl in brb1.
  rewrite <- O1 in brb1.
  apply brb1.
  replace (o' ++ [inr (l, k)] ++ input ++ [x])
  with ((o' ++ [inr (l, k)] ++ input) ++ [x])
    in in0app.
  simpl in in0app.
  rewrite <- O1 in in0app.
  erewrite -> nth_extend.
  rewrite -> in0app in nerr.
  eauto.
  rewrite -> O1.
  rewrite -> app_length.
  simpl.
  omega.
  repeat rewrite -> app_assoc.
  reflexivity.

  
  eapply IHinput.
  exact llo.
  rewrite -> app_comm_cons in R.
  rewrite -> app_assoc in R.
  apply app_inj_tail in R.
  destruct R as [R1 R2].
  exact R1.
  eauto.
  rewrite -> in0app in brb.
  repeat rewrite -> app_assoc in brb.
  rewrite -> app_comm_cons in R.
  replace (inr (l, k) :: input)
  with ([inr (l, k)] ++ input) in R; [|reflexivity].
  rewrite <- app_assoc in R.
  repeat rewrite -> app_assoc in R.
  rewrite <- R in brb.
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  exact brb1.

  erewrite -> nth_extend.
  rewrite -> in0app in nerr.
  rewrite -> app_comm_cons in R.
  replace (inr (l, k) :: input)
  with ([inr (l, k)] ++ input) in R; [|reflexivity].
  repeat rewrite <- app_assoc in R.  
  rewrite <- R in nerr.
  eauto.

  rewrite -> app_comm_cons in R.
  rewrite -> app_assoc in R.
  apply app_inj_tail in R.
  destruct R as [R1 R2].  
  rewrite -> R1.
  rewrite -> app_length.
  simpl.
  omega.
Qed.  

Lemma BackRefsBoundedLemma :
  forall {A : Set} (n l d mnd mxd : nat)
         (input : SequenceWithBackRefs A),
    BackRefsBounded 1 1 mnd mxd input ->
    nth_error input n = Some (inr (l, d)) ->
    l = 1.
Proof.
  intros A n l d mnd mxd input.
  revert input n l d mnd mxd.
  induction input as [|a input IHinput].
  intros n l d mnd mxd B C.
  destruct n; inversion C.

  intros n l d mnd mxd brb nerr.
  destruct n.
  destruct a.
  inversion nerr.
  destruct p. (* TODO *)
  inversion nerr.
  inversion brb.
  inversion H3. (* TODO *)
  omega.

  simpl in nerr.
  eapply IHinput.
  inversion brb.
  eauto.
  eauto.
Qed.

Lemma BackRefsBoundedLemma2 :
  forall {A : Set} (n l d mnd mxd : nat)
         (input : SequenceWithBackRefs A),
    BackRefsBounded 1 1 mnd mxd input ->
    nth_error input n = Some (inr (l, d)) ->
    mnd <= d <= mxd.
Proof.
  intros A n l d mnd mxd input.
  revert input n l d mnd mxd.
  induction input as [|a input IHinput].
  intros n l d mnd mxd B C.
  destruct n; inversion C.

  intros n l d mnd mxd brb nerr.
  destruct n.
  destruct a.
  inversion nerr.
  destruct p. (* TODO *)
  inversion nerr.
  inversion brb.
  inversion H3. (* TODO *)
  omega.

  simpl in nerr.
  eapply IHinput.
  inversion brb.
  eauto.
  eauto.
Qed.

Definition F {A : Set} (a : ListArray (A + (nat * nat))%type) (n : nat) :=
  { m : option A |
    forall (mnd mxd : nat) (k : SequenceWithBackRefs A) (l : list A),
      a = l2a k ->
      BackRefsBounded 1 1 (S mnd) mxd k ->
      ResolveBackReferences k l ->
      m = nth_error l n }.

(* TODO: Woanders *)
Lemma nth_error_none :
  forall {A : Set} (l : list A) n,
    nth_error l n = None <-> n >= ll l.
Proof.
  intros A.
  induction l.
  intros n.
  split.

  intros nnone.
  simpl.
  omega.

  intros ?.
  destruct n; reflexivity.
  
  intros n.
  split.
  intros nnone.
  destruct n.
  inversion nnone.
  simpl.
  assert (n >= ll l).
  apply IHl.
  simpl in nnone.
  auto.
  omega.

  intros nll.
  destruct n.
  inversion nll.
  simpl.
  apply IHl.
  simpl in nll.
  omega.  
Qed.  

Lemma F_rec : forall {A : Set} (a : ListArray (A + (nat * nat))%type),
    (forall (n:nat), (forall (m:nat), m<n -> F a m )->F a n).
Proof.
  unfold F.
  intros A a n rec.
  destruct (anth_error a n) as [[byte | [l d]] | no] eqn:anerr.
  + exists (Some byte).
    intros mnd mxd k l B C D.
    symmetry.
    eapply BackRefLemma2.
    eauto.
    eauto.
    rewrite -> B in anerr.
    rewrite -> anth_nth in anerr.
    auto.
  + destruct (le_dec d n).
    - destruct (le_dec 1 d).
      destruct (rec (n - d)) as [x e].
      omega.
      exists x.
      intros mnd mxd k l2 B C D.
      erewrite -> BackRefLemma.
      eapply e.
      eauto.
      eauto.
      trivial.
      eauto.
      trivial.
      rewrite -> B in anerr.
      rewrite -> anth_nth in anerr.
      assert (K : l = 1).
      eapply BackRefsBoundedLemma.
      exact C.
      exact anerr.
      rewrite <- K.
      trivial.
      assert (K : d = 0).
      omega.
      exists (@None A).
      intros mnd mxd k l1 al brb rbr.
      rewrite -> al in anerr.
      rewrite -> anth_nth in anerr.
      eapply (BackRefsBoundedLemma2 _ _ _ (S mnd) mxd) in anerr.
      omega.
      exact brb.
    - exists (@None A).
      intros mnd mxd k l0 al brb rbr.
      rewrite -> al in anerr.
      rewrite -> anth_nth in anerr.
      eapply (BackRefLemma3 _ _ _ _ _ _ _ rbr) in anerr.
      omega.
      eauto.
  + exists (@None A).
    intros mnd mxd k l al brb rbr.
    assert (K : ll k = ll l).
    eapply BackRefsLengthOneLength.
    exact brb.
    exact rbr.
    rewrite -> al in anerr.
    rewrite anth_nth in anerr.
    apply nth_error_none in anerr.
    rewrite -> K in anerr.
    symmetry.
    apply nth_error_none.
    exact anerr.
Qed.
  
Fixpoint correctSWBR1 {A : Set}
         (n : nat) (swbr : SequenceWithBackRefs A) : bool :=
  match swbr with
  | [] => true
  | inl d :: r => correctSWBR1 (S n) r
  | inr (_, d) :: r => match le_dec d n with
                       | left _  => correctSWBR1 (S n) r
                       | right _ => false
                       end
  end.

Lemma correctSWBRapp : forall {A : Set}
                              (swbr1 swbr2 : SequenceWithBackRefs A)
                              n,
    correctSWBR1 n (swbr1 ++ swbr2) =
    andb (correctSWBR1 n swbr1) (correctSWBR1 (n + ll swbr1) swbr2).
Proof.
  intros A.
  induction swbr1 as [|a swbr1 IHswbr1].
  intros swbr2 n.
  simpl.
  replace (n + 0) with n; [|omega].
  reflexivity.

  intros swbr2 n.
  rewrite <- app_comm_cons.
  simpl.
  rewrite -> IHswbr1.
  simpl.

  destruct a.
  replace (S (n + ll swbr1)) with (n + S (ll swbr1)); [|omega].
  reflexivity.
  
  destruct p.
  destruct (le_dec n1 n).
  
  replace (S (n + ll swbr1)) with (n + (S (ll swbr1))); [|omega].
  reflexivity.

  reflexivity.
Qed.  

(* TODO: Woanders *)

Lemma nonnull_lemma : forall {A : Set} (x : A) L dist,
    nth_error (x :: L) (ll (x :: L) - S dist) <> None.
Proof.
  intros A x L dist Q.
  apply nth_error_none in Q.
  simpl in Q.
  omega.
Qed.
  
Lemma correctSWBR1dst :
  forall {A : Set} len dist n,
    correctSWBR1 n [@inr A _ (len, dist)] = true -> dist <= n.
Proof.
  intros A len dist n corr.
  simpl in corr.
  destruct (le_dec dist n).
  trivial.
  firstorder.
Qed.
  
Lemma swbr_correct_exists : forall {A : Set}
                                   (null : A)
                                   (swbr : SequenceWithBackRefs A)
                                   mnd mxd,
    BackRefsBounded 1 1 (S mnd) mxd swbr ->
    correctSWBR1 0 swbr = true -> exists l, ResolveBackReferences swbr l.
Proof.
  intros A null.
  apply (rev_ind (fun swbr => forall (mnd mxd : nat),
                      BackRefsBounded 1 1 (S mnd) mxd swbr ->
                      correctSWBR1 0 swbr = true ->
                      exists l : list A, ResolveBackReferences swbr l)).
  exists (@nil A).
  constructor.

  intros x l IHl mnd mxd.
  rewrite -> correctSWBRapp.
  intros brb ndp.
  apply Bool.andb_true_iff in ndp.
  destruct ndp as [nd1 nd2].
  eapply IHl in nd1.
  destruct nd1 as [L LL].
  destruct x as [byte | [len dist]].

  exists (L ++ [byte]).
  constructor.
  exact LL.

  assert (KM : len = 1 /\ dist >= 1).
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  inversion brb2.
  match goal with
  | H : BackRefBounded 1 1 _ _ _ |- _ => inversion H
  end.
  omega.
  destruct KM as [K M].
  
  destruct (nth_error L (ll L - dist)) as [isthere | isnthere] eqn:isq.
  
  exists (L ++ [isthere]).
  econstructor.
  exact LL.
  rewrite -> K.
  constructor.
  constructor.

  destruct dist.
  omega.  
  apply (nthNthLast _ _ null).
  eapply correctSWBR1dst.
  replace (ll L) with (ll l).
  exact nd2.
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  eapply BackRefsLengthOneLength.
  exact brb1.
  exact LL.

  apply nth_error_nth.
  exact isq.

  destruct dist.
  omega.
  destruct L.
  inversion LL as [Q|B C D E F G|B C D E F G H I J].
  rewrite <- Q in nd2.
  inversion nd2.

  destruct C; inversion G.
  
  assert (Quark : ll l = ll (@nil A)).
  eapply BackRefsLengthOneLength.
  apply forall_app in brb.
  destruct brb as [brb1 brb2].
  exact brb1.
  trivial.
  destruct l.
  destruct B; inversion I.
  inversion Quark.
  
  contradict isq.
  apply nonnull_lemma.

  apply forall_app in brb.
  destruct brb as [brb1 brb2].  
  exact brb1.
Qed.  

Fixpoint funToListRev {A : Set} (n : nat) (f : nat -> A) : list A :=
  match n with
  | 0    => []
  | S n_ => f n_ :: funToListRev n_ f
  end.
  
Lemma funToListRev_length :
  forall {A : Set} (f : nat -> A) n, ll (funToListRev n f) = n.
Proof.
  intros A f.
  induction n as [|n IHn].
  reflexivity.
  simpl.
  omega.
Qed.
  
Function funToList {A : Set} (n : nat) (f : nat -> A) : list A :=
  rev (funToListRev n f).  

Lemma funToList_length : 
  forall {A : Set} (f : nat -> A) n, ll (funToList n f) = n.
Proof.
  intros A f n.
  unfold funToList.
  rewrite -> rev_length.
  apply funToListRev_length.
Qed.

Lemma funToListRev_correct :
  forall {A : Set} n m (f : nat -> A),
    m < n -> nth_error (funToListRev n f) (n - m - 1) = Some (f m).
Proof.
  intros A.
  induction n as [|n IHn].
  + intros.
    omega.
  + destruct n as [|n].
    - intros m f m1.
      destruct m as [|m].
      reflexivity.
      omega.
    - intros m f mn.
      destruct m as [|m].
      * rewrite <- IHn.
        simpl.        
        replace (n - 0) with n; [|omega].
        reflexivity.
        omega.
      * destruct (le_dec n m).
        replace (S (S n) - S m - 1) with 0; [|omega].
        simpl.
        destruct (eq_nat_dec n m) as [e | ne].
        rewrite -> e.
        reflexivity.
        omega.
        
        rewrite <- IHn.
        replace (S (S n) - S m - 1) with (S (n - m - 1)); [|omega].
        reflexivity.
        omega.
Qed.

(* TODO: Woanders *)
Lemma rev_nth_error :
  forall (A : Set) (l : list A) (n : nat),
    n < ll l -> nth_error (rev l) n = nth_error l (ll l - S n).
Proof.
  intro A.
  induction l as [|x l IHl].
  intros n nll.
  simpl in nll.
  omega.

  intros n nll.
  simpl.
  destruct (eq_nat_dec n (ll l)) as [e | ne].  
  replace (ll l - n) with 0; [|omega].
  simpl.
  rewrite -> e.
  rewrite <- rev_length.
  rewrite -> nth_error_last.
  reflexivity.

  simpl in nll.
  replace (ll l - n) with (S (ll l - S n)); [|omega].
  simpl.
  rewrite <- nth_extend.
  apply IHl.
  omega.
  rewrite -> rev_length.
  omega.
Qed.

(* TODO: woanders *)

Lemma exists_fn :
  forall {B} (A : nat -> B -> Prop) (f : forall n, {m : B | A n m})
         n, A n (proj1_sig (f n)).
Proof.
  intros.
  apply proj2_sig.
Qed.

Lemma F_rec_correct :
  forall {A : Set} (C : SequenceWithBackRefs A) (D : list A) mnd mxd n (lln : n < ll C),
    BackRefsBounded 1 1 (S mnd) mxd C ->
    ResolveBackReferences C D ->
    proj1_sig (COV _ (F_rec (l2a C)) n) =
    nth_error D n.
Proof.  
  intros A C D mnd mxd n lln brb rbr.
  set (a := l2a C).
  eapply proj2_sig.
  
  destruct (COV (F (l2a C)) (F_rec (l2a C)) n) as [x e] eqn:q.
  unfold a.
  exists x.
  rewrite -> q.
  eapply e.
  reflexivity.
  exact brb.  
  exact rbr.
Qed.
  
Lemma funToList_correct :
  forall {A : Set} n m (f : nat -> A),
    m < n -> nth_error (funToList n f) m = Some (f m).
Proof.
  unfold funToList.
  intros A n m f mn.
  rewrite -> rev_nth_error.
  rewrite -> funToListRev_length.
  replace (n - S m) with (n - m - 1); [|omega].
  apply funToListRev_correct.
  trivial.
  rewrite -> funToListRev_length.
  trivial.
Qed.

Theorem ResolveBackReferencesDec'
  : forall {A : Set} (null : A) (input : SequenceWithBackRefs A) mnd mxd,
    BackRefsBounded 1 1 (S mnd) mxd input -> 
    {output | ResolveBackReferences input output} +
    ({output | ResolveBackReferences input output} -> False).
Proof.
  intros A null input mnd mxd brb.
  destruct (correctSWBR1 0 input) as [corr |] eqn:coreq.
  assert (K : exists l, ResolveBackReferences input l);
    [ eapply (swbr_correct_exists null); eauto | eauto ].
  apply inl.  
  set (D := l2a input).
  set (len := ll input).
  set (E := COV (F D) (F_rec D)).
  set (F := fun n => proj1_sig (E n)).
  set (G := funToList len F).
  set (H := map (fun x => match x with
                          | None => null
                          | Some a => a
                          end) G).
  exists H.
  destruct K as [xK kK].
  set (I := F_rec_correct input H).

(************************************************************)
  
Function doResolution {A : Set} (B : SequenceWithBackRefs A)
  : option (forall n, F (l2a (BackRefsLengthOne_ B)) n) :=
  let C := BackRefsLengthOne_ B in
  let LC := ll C in
  let D := l2a C in
  let E := COV (F D) (F_rec D) in
  match correctSWBR1 0 C with
  | false => None
  | true => Some E
  end.
