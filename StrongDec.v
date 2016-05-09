Require Import Coq.Lists.List.
Require Import Program.

Require Import Shorthand.
Require Import Prefix.
Require Import Combi.
Require Import String.

Definition StrongDec {A B} (R : A -> list B -> Prop) :=
  forall (l : list B),
    {a : A & {l' : list B & {l'' : list B | l = l' ++ l'' /\ R a l'}}} +
    (string * ({a : A & {l' : list B & {l'' : list B | l = l' ++ l'' /\ R a l'}}} -> False)).

Definition StrongUnique {A B} (R : A -> list B -> Prop) :=
  forall a b la las lb lbs, la ++ las = lb ++ lbs -> R a la -> R b lb -> a = b /\ la = lb.

Lemma StrongUniqueLemma :  forall {A B} (R : A -> list B -> Prop),
                             StrongUnique R <-> 
                             ((forall a b l, R a l -> R b l -> a = b) /\ forall a b l l', R a l -> R b (l ++ l') -> l' = nil).
Proof.
  intros A B R.
  split.
  intro uniq.
  split.
  intros a b l ra rb.
  apply (uniq a b l nil l nil eq_refl ra rb).
  intros a b l l' ra rb.
  destruct (uniq a b l l' (l ++ l') nil) as [K1 K2].
  symmetry.
  apply app_nil_r.
  trivial.
  trivial.
  destruct (app_ll l nil l l') as [K3 K4].
  rewrite -> app_nil_r.
  exact K2.
  reflexivity.
  auto.

  intros Q a b la las lb lbs apps ra rb.
  destruct Q as [uniq prf].

  destruct (prefix_common la lb (la ++ las)) as [pxs | pxs].
  exists las.
  reflexivity.
  exists lbs.
  auto.
  destruct pxs as [pr x].
  assert (prn : pr = nil).
  apply (prf a b la pr ra).
  rewrite -> x.
  trivial.
  assert (y : la = lb).
  rewrite <- x.
  rewrite -> prn.
  symmetry.
  apply app_nil_r.
  split.
  rewrite <- y in rb.
  apply (uniq _ _ la).
  trivial.
  trivial.
  trivial.

  destruct pxs as [pr x].
  assert (prn : pr = nil).
  apply (prf b a lb pr rb).
  rewrite -> x.
  trivial.
  assert (y : la = lb).
  rewrite <- x.
  rewrite -> prn.
  apply app_nil_r.
  split.
  rewrite -> y in ra.
  apply (uniq _ _ lb).
  trivial.
  trivial.
  trivial.
Qed.

(* COMBINE1 *)
Inductive Combine {A BQ BR BS}
 (Q : BQ -> list A -> Prop)
 (R : BQ -> BR -> list A -> Prop)
 (c : BQ -> BR -> BS) : BS -> list A -> Prop :=
| doCombine : forall bq br aq ar,
   Q bq aq -> R bq br ar ->
     Combine Q R c (c bq br) (aq ++ ar).

Notation "A >>[ B ]= C" := (Combine A C B) (at level 0).
Notation "A >>= B" := (Combine A B pi2) (at level 0).
(* COMBINE2 *)
	   
Theorem CombineStrongDecStrongUnique : forall {A BQ BR BS}
                                            (Q : BQ -> list A -> Prop) (R : BQ -> BR -> list A -> Prop) (c : BQ -> BR -> BS),
                                       StrongUnique Q -> StrongDec Q ->
                                       (forall bq, StrongUnique (R bq) * StrongDec (R bq)) ->
                                       StrongUnique (Q >>[ c ]= R) * StrongDec (Q >>[ c ]= R).
Proof.
  intros A BQ BR BS Q R c wuQ sdQ wusdR.
  split.
  intros q r lq lqs lr lrs apps Q_ R_.
  inversion Q_.
  inversion R_.
  destruct (wuQ bq bq0 aq (ar ++ lqs) aq0 (ar0 ++ lrs)) as [bqs aqs].
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> H6.
  rewrite -> H2.
  trivial.
  trivial.
  trivial.
  destruct (wusdR bq) as [wuR sdR].
  destruct (wuR br br0 ar lqs ar0 lrs) as [brs ars].
  apply (app_ll aq _ aq0 _).
  rewrite -> app_assoc.
  rewrite -> app_assoc.
  rewrite -> H6.
  rewrite -> H2.
  auto.
  rewrite -> aqs.
  reflexivity.
  trivial.
  rewrite -> bqs.
  trivial.
  split.
  rewrite -> bqs.
  rewrite -> brs.
  reflexivity.
  rewrite -> aqs.
  rewrite -> ars.
  reflexivity.

  intro l.
  destruct (sdQ l) as [[bq [l' [l'' [lapp qal]]]]|[reason no]].
  destruct (wusdR bq) as [wuR sdR].
  destruct (sdR l'') as [[br [l'0 [l''0 [l'app ral]]]]|[reason no]].
  apply inl.
  exists (c bq br).
  exists (l' ++ l'0).
  exists (l''0).
  split.
  rewrite <- app_assoc.
  rewrite <- l'app.
  trivial.
  constructor.
  trivial.
  trivial.

  apply inr.
  split.
  apply reason.
  intro F.
  destruct F as [bs [l'0 [l''0 [l'app combi]]]].
  inversion combi.
  contradict no.
  exists br.
  exists ar.
  exists (l''0).
  destruct (wuQ bq bq0 l' l'' aq (ar ++ l''0)) as [bqs laq].
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H2.
  trivial.
  trivial.
  trivial.
  split.
  apply (app_ll l' _ aq _).
  rewrite <- lapp.
  rewrite -> app_assoc.
  rewrite -> H2.
  trivial.
  rewrite -> laq.
  reflexivity.
  rewrite -> bqs.
  trivial.

  apply inr.
  split.
  apply reason.
  intro F.
  destruct F as [bs [l' [l'' [lapp combi]]]].
  inversion combi.
  contradict no.
  exists bq.
  exists aq.
  exists (ar ++ l'').
  split.
  rewrite -> app_assoc.
  rewrite -> H2.
  trivial.
  trivial.
Qed.

Lemma nullStrongUnique : forall {A B} (null : A), StrongUnique (fun n L => n = null /\ L = @nil B).
Proof.
  intros A B null.
  apply StrongUniqueLemma.
  split.
  intros a b l cond1 cond2.
  destruct cond1 as [cond1 ?].
  destruct cond2 as [cond2 ?].
  rewrite -> cond2.
  exact cond1.
  intros a b l l' ? cond2.
  destruct cond2 as [? cond2].
  destruct l'.
  reflexivity.
  destruct l.
  inversion cond2.
  inversion cond2.
Qed.

Lemma nullStrongDec : forall {A B} (null : A), StrongDec (fun n L => n = null /\ L = @nil B).
Proof.
  intros A B null l.
  apply inl.
  exists null.
  exists (@nil B).
  exists l.
  auto.
Qed.

(* NTIMES1 *)
Fixpoint nTimes {A B C} (n : nat) (null : C)
                        (comb : A -> C -> C)
                        (rel : A -> list B -> Prop)
: C -> list B -> Prop :=
  match n with
    | 0 => fun c L => c = null /\ L = nil
    | (S n') => rel >>[ comb ]= fun _ =>
                (nTimes n' null comb rel)
  end.
(* NTIMES2 *)

Theorem nTimesStrongDecStrongUnique : forall {A B C} (err : string) (null : C) (comb : A -> C -> C) (R : A -> list B -> Prop),
                               StrongUnique R -> StrongDec R -> forall n,
                                                                  (StrongDec (nTimes n null comb R) * StrongUnique (nTimes n null comb R)).
Proof.
  intros A B C s null comb R uniq dec.
  induction n.
  split.
  apply nullStrongDec.
  apply nullStrongUnique.
  split.
  apply CombineStrongDecStrongUnique.
  exact uniq.
  exact dec.

  intro Q.
  split.
  apply IHn.
  apply IHn.
  
  apply CombineStrongDecStrongUnique.
  exact uniq.
  exact dec.

  intro Q.
  split.
  apply IHn.
  apply IHn.
Defined.

(* NTIMESSPEC1 *)
Definition nTimesApp {A B} (n : nat)
  (rel : list A -> list B -> Prop) :=
  nTimes n nil (@app A) rel.
				     
Definition nTimesCons {A B} (n : nat)
  (rel : A -> list B -> Prop) :=
  nTimes n nil (@cons A) rel.
(* NTIMESSPEC2 *)

Lemma AndStrongUnique : forall A B Q (rel : A -> list B -> Prop),
                          StrongUnique rel ->
                          StrongUnique (fun a b => Q /\ rel a b).
Proof.
  intros A B Q rel surel a b la las lb lbs apps paa pab.
  destruct paa as [aa1 aa2].
  destruct pab as [bb1 bb2].
  exact (surel a b la las lb lbs apps aa2 bb2).
Defined.

Lemma AndStrongDec : forall A B (Q : Prop) (rel : A -> list B -> Prop),
                       (Q + (string * ~ Q)) ->
                       StrongDec rel ->
                       StrongDec (fun a b => Q /\ rel a b).
Proof.
  intros A B Q rel qdec sdrel l.
  destruct qdec as [q | [reason nq]].
  destruct (sdrel l) as [[a [l' [l'' [lapp lrel]]]]|[reason no]].
  apply inl.
  exists a.
  exists l'.
  exists l''.
  split.
  exact lapp.
  split.
  exact q.
  exact lrel.
  apply inr.
  split.
  exact reason.
  intro R.
  destruct R as [a [l' [l'' [lapp [qe re]]]]].
  contradict no.
  exists a.
  exists l'.
  exists l''.
  auto.
  apply inr.
  split.
  exact reason.
  intro R.
  contradict nq.
  destruct R as [? [? [? [? [q ?]]]]].
  exact q.
Defined.

Definition AppCombine {A BQ BR : Set }
  (Q : BQ -> list A -> Prop)
  (f : BQ -> BR) : BR -> list A -> Prop :=
  Combine Q (fun n (m : unit) L => m = () /\ L = @nil A)
            (fun a b => f a).

Lemma AppCombineF : forall
                      {A BQ BR : Set}
                      (a : BQ) (b : list A) (R : BQ -> list A -> Prop)
                      (f : BQ -> BR), R a b -> AppCombine R f (f a) b.
Proof.
  intros A BQ BR a b R f rab.
  unfold AppCombine.
  replace b with (b ++ []).
  apply (doCombine R (fun (_ : BQ) (m : ()) (L : list A) => m = () /\ L = []) (fun a b => f a) _ ()).
  apply rab.
  auto.
  apply app_nil_r.
Qed.
