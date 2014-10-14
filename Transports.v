Require Import Coq.Init.Logic.
Require Import Coq.Vectors.Vector.
Require Import Program.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Structures.Orders.
Require Import DeflateNotations.
Require Import Coq.Vectors.Fin.
Require Import Omega.

Lemma vec_0_nil : forall {A} (v : vec A 0%nat), v = Vnil A.
Proof.
  intros A v.
  dependent induction v.
  reflexivity.
Defined.

Definition fin_1_is_1 : forall (n : fin 1), n = Fin.F1.
Proof.
  dependent destruction n.
  reflexivity.
  contradict n1.
  intros H.
  inversion H.
Defined.

Local Open Scope nat_scope.

Definition lastfin : forall n, fin (S n). 
refine (fix f n : fin (S n) :=
          match n with
            | 0 => Fin.F1
            | (S n') => Fin.FS (f n')
          end).
Defined.

Theorem ex_predfin : forall {m} (n : fin (S m)),
                          n <> lastfin m ->
                          { n' : fin m | n = FinLR 1 n' }.
Proof.
  intros m n neq.
  dependent induction m.
  contradict neq.
  compute. apply fin_1_is_1.
  dependent induction n.
  exists (FinF1 (n := m)).
  reflexivity.
  assert (E : {n' : fin m | n1 = FinLR 1 n'}).
  apply IHm.
  contradict neq.
  assert (lfe : lastfin (S m) = FinFS (lastfin m)).
  reflexivity.
  rewrite -> lfe.
  rewrite <- neq.
  reflexivity.
  elim E.
  intros x eq.
  rewrite -> eq.
  exists (FinFS x).
  reflexivity.
Defined.

Function predfin {m} (n : fin (S m)) (neq : n <> lastfin m) :=
  proj1_sig (ex_predfin n neq).  

Definition eq_fin_dec {n} : forall (i j : fin n), {i = j} + {i <> j}.
Proof.
 refine (fin_rect2
           (fun n (i j : fin n) => { i = j } + { i <> j })
           (fun _ => left _)
           (fun _ _ => right _)
           (fun _ _ => right _)
           (fun _ _ _ H => if H then left _ else right _)).
 auto.
 intros Q.
 inversion Q.
 intros Q.
 inversion Q.
 rewrite e.
 auto.
 contradict n1.
 apply FS_inj.
 trivial.
Defined.

Notation f_nat := Fin.to_nat.

Definition f_le {m} (a b : Fin.t m) : Prop := ` (f_nat a) <= ` (f_nat b).

Definition fin_id {a b} (eq : a = b) (fa : fin a) : fin b.
refine (match a as c return (a = c -> _) with
            | 0 => (fun _ => _)
            | (S n) => (fun _ => _)
        end eq_refl).
contradict fa.
rewrite e.
intros Q.
inversion Q.
rewrite <- eq.
apply fa.
Defined.

Lemma f_nat_id : forall {n m} a (eq : n = m), ` (f_nat a) = ` (f_nat (fin_id eq a)).
Proof.
  intros n m a eq.
  refine (match eq with
            | eq_refl => _
          end).
  induction a.
  reflexivity.
  compute. auto.
Defined.

Lemma succ_inj : forall (a b : nat), a = b -> S a = S b.
Proof.
  intros a b e.
  rewrite -> e.
  reflexivity.
Defined.

Lemma fin_id_succ {a b} (eq : a = b) c : fin_id (succ_inj a b eq) (FinFS c) = FinFS (fin_id eq c).
Proof.
  refine (match eq with
              | eq_refl => _
          end).
  induction c.
  auto. auto.
Defined.

Lemma fin_id_destroy : forall {n} (q : fin n), fin_id eq_refl q = q.
Proof.
  intros n.  
  dependent induction q.
  auto.
  auto.
Defined.

Lemma fin_id_injective {a b} (eq : a = b) c d : fin_id eq c = fin_id eq d -> c = d.
Proof.
  dependent destruction eq.
  rewrite -> fin_id_destroy.
  rewrite -> fin_id_destroy.
  auto.
Defined.

Definition vec_id {A} {a b} (eq : a = b) : vec A a -> vec A b.
rewrite -> eq.
trivial.
Defined.

Lemma vec_id_destroy {A} {n : nat} (B : vec A n) : vec_id eq_refl B = B.
Proof.
  compute.
  reflexivity.
Defined.

Lemma vec_id_map {A B} {n m} (eq : n = m) (v : vec A n) (f : A -> B) : Vmap f (vec_id eq v) = vec_id eq (Vmap f v).
Proof.
  dependent destruction eq.
  rewrite -> vec_id_destroy.
  rewrite -> vec_id_destroy.
  reflexivity.
Defined.

Lemma fin_id_inv {n m} (eq : n = m) (qe : m = n) (b : fin m) : fin_id eq (fin_id qe b) = b.
Proof.
  dependent destruction eq.
  replace qe with (eq_refl n).
  rewrite -> fin_id_destroy.
  rewrite -> fin_id_destroy.
  reflexivity.
  apply proof_irrelevance.
Defined.

Lemma vec_id_inv {A} {a b} (eq : a = b) (qe : b = a) (B : vec A _) : vec_id eq (vec_id qe B) = B.
Proof.
  dependent destruction eq.
  replace qe with (eq_refl a).
  replace (vec_id eq_refl B) with B.
  replace (vec_id eq_refl B) with B.
  reflexivity.
  apply vec_id_destroy.
  apply vec_id_destroy.
  apply proof_irrelevance.
Defined.

Theorem fin_nforall_ex : forall {n} {B : fin n -> Prop},
                           (forall a, {B a} + {~ B a}) ->
                           (~ forall a, ~ B a) -> {a | B a}.
Proof.
  induction n.
  intros B H H0.
  contradict H0.
  intros a.
  inversion a.
  intros B Bdec nfa.
  elim (Bdec FinF1).
  intros B1.
  exists (FinF1(n:=n)).
  apply B1.
  intros nB1.
  assert(H:{a : fin n | B (FinFS a)}).
  apply IHn.
  intros a.
  apply Bdec.  
  contradict nfa.
  intros a.
  dependent destruction a.
  apply nB1.
  apply nfa.
  elim H.
  intros a a_ex.
  exists (FinFS a).
  apply a_ex.
Defined.
Lemma forall_notexists : forall {A} (Q : A -> Prop),
                           (forall a, Q a + ~ Q a) ->
                           ({a | ~ Q a} -> False) -> forall a, Q a.
Proof.
  intros A Q H H0 a.
  elim (H a).
  trivial.
  intros nQa.
  assert (cdct : {a | ~ Q a}).
  exists a.
  apply nQa.
  contradict H0.
  auto.
Defined.

Lemma VecIdLemma : forall {A} {n m} (eq : n = m) (v : vec A n) q, (Vnth (vec_id eq v) q) = Vnth v (fin_id (symmetry eq) q).
intros A n m eq v q.
dependent destruction eq.
rewrite -> vec_id_destroy.
replace (symmetry eq_refl) with (eq_refl n).
rewrite -> fin_id_destroy.
reflexivity.
apply proof_irrelevance.
Defined.

Lemma FinFS_succ_alt : forall {n} (x : fin n), (` (f_nat (FinFS x)) = S (` (f_nat x))).
Proof.
  intros.
  simpl.
  destruct (Fin.to_nat x).
  auto.
Defined.

(* Todo: This should go to Transports.v *)
Lemma of_nat_lt_inj : forall {o n m} (q : (n < o)%nat) (r : (m < o)%nat), of_nat_lt q = of_nat_lt r -> n = m.
Proof.
  induction o.
  intros n m q.
  inversion q.
  induction n.
  induction m.
  auto.
  intros q r quiek.
  inversion quiek.
  induction m.
  intros q r quiek.
  inversion quiek.
  intros q r on.
  f_equal.
  assert (q' : (n < o)%nat).
  omega.
  assert (r' : (m < o)%nat).
  omega.
  apply (IHo _ _ q' r').
  simpl in on.
  replace (lt_S_n n o q) with q' in on.
  replace (lt_S_n m o r) with r' in on.
  apply FS_inj.
  apply on.
  apply proof_irrelevance.
  apply proof_irrelevance.
Defined.
