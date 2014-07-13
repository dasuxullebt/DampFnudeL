Require Import Coq.Logic.Decidable.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qfield.
Require Import Coq.PArith.BinPos.
Require Import Coq.Arith.Arith.
Require Import Coq.Vectors.Vector.
Require Import NPeano.
Require Import Coq.Init.Logic.
Require Import Coq.Lists.List.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Program.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Structures.Orders.
Require Import Coq.Logic.JMeq.
Require Import Coq.Logic.EqdepFacts.
Require Import DeflateNotations.
Require Import Quicksort.
Require Import Lex.
Require Import Transports.
Require Import Prefix.
Require Import Repeat.
Require Import Combi.
Require Import KraftList.
Require Import KraftVec.
Require Import DeflateCoding.

Local Open Scope nat.

Fixpoint xrepeat {A : Set} (n : nat) (a : A) :=
  match n with
    | 0 => []
    | (S n') => a :: xrepeat n' a
  end.

Definition vector_for_fixed_code : vec nat 288 := of_list ((xrepeat 144 8) ++ (xrepeat (255 - 143) 9) ++ (xrepeat (279 - 255) 7) ++ (xrepeat (287 - 279) 8)).

Definition fixed_code : { D : deflateCoding | {eq : M D = 288 |
                                               vector_for_fixed_code =
                                               (Vmap (ll(A:=bool)) (vec_id(A:=LB) eq (C D)))}}.
Proof.
apply existance.
compute.
intros Q.
inversion Q.
Defined.

Definition fc1 := to_list (n:=(M (proj1_sig fixed_code))) (C (proj1_sig fixed_code)).

Extraction Language Haskell.

Recursive Extraction fc1. (* Fails *)

Definition quicksort_nat (L : list nat) : list nat.
assert({L' | (forall x, In x L <-> In x L') /\ Sorted le L'}).
apply quicksort.
apply le_ge_dec.
elim H.
auto.
Defined.

Recursive Extraction quicksort_nat.


(*
Eval compute in fc1.

(* TODO: option ? *)
Inductive Maybe {A : Type} : Type :=
| Just : A -> Maybe
| Nothing : Maybe.

Function compress (D : deflateCoding) (L : list (fin (M D))) : Maybe :=
  match L with
    | [] => Just []
    | x :: L' =>
      match (cd D x) with
        | [] => Nothing
        | l => match (compress D L') with
                 | Nothing => Nothing
                 | Just k => Just (l ++ k)
               end
      end
  end.

Lemma compress_prefix : forall (D : deflateCoding) (L : list (fin (M D))) (m : fin (M D)) (c : LB),
                          compress D (m :: L) = Just c -> prefix (cd D m) c.
Proof.
  intros D L m c H.
  unfold compress in H.
  destruct (cd D m).
  inversion H.
  fold compress in H.
  destruct (compress D L).
  inversion H.
  exists l0.
  reflexivity.
  inversion H.
Qed.

Theorem compress_injective : forall (D : deflateCoding) (L M : list (fin (M D))),
                               compress D L = compress D M -> ((compress D L = Nothing) + (L = M))%type.
Proof.
  intros D.
  refine (fix m L M cleq :=
            match L as L' return (L = L' -> _) with
              | [] => fun eq => _
              | l :: L2 => fun eq =>
                match M as M' return (M = M' -> _) with
                  | [] => fun eq2 => _
                  | m :: M2 => fun eq2 => _
                end eq_refl
            end eq_refl).

  rewrite -> eq in cleq.
  unfold compress in cleq.
  destruct M.
  apply inr.
  auto.
  destruct (cd D t).
  inversion cleq.
  fold compress in cleq.
  destruct (compress D M).
  inversion cleq.
  inversion cleq.

  rewrite -> eq2 in cleq.
  unfold compress in cleq.
  destruct L.
  apply inr.
  auto.
  destruct (cd D t).
  inversion cleq.
  fold compress in cleq.
  destruct (compress D L).
  inversion cleq.
  inversion cleq.


  rewrite -> eq.
  rewrite -> eq2.
  destruct (cd D l) eqn:cddl.
  unfold compress.
  rewrite -> cddl.
  auto.

  elim (eq_fin_dec l m).
  intros l_eq_m.
  assert (ind : (compress D L2 = Nothing) + (L2 = M2)).
  apply m0.
  rewrite -> eq in cleq.
  rewrite -> eq2 in cleq.
  unfold compress in cleq.
  rewrite -> cddl in cleq.
  rewrite -> l_eq_m in cddl.
  rewrite -> cddl in cleq.
  fold compress in cleq.
  destruct (compress D L2).
  destruct (compress D M2).
  inversion cleq.
  f_equal.
  apply app_inv_head with l0.
  auto.
  inversion cleq.
  destruct (compress D M2).
  inversion cleq.
  reflexivity.
  elim ind.
  intros nothing.
  apply inl.
  unfold compress.
  fold compress.
  rewrite -> nothing.
  destruct (cd D l).
  reflexivity.
  reflexivity.
  intros L2_eq_M2.
  apply inr.
  rewrite -> L2_eq_M2.
  rewrite -> l_eq_m.
  reflexivity.

  intros l_neq_m.
  destruct (compress D L) eqn:cdl.
  assert (prefL : prefix (cd D l) l1).
  apply compress_prefix with L2.
  rewrite <- eq.
  auto.
  destruct (compress D M) eqn:cdm.
  assert (prefM : prefix (cd D m) l2).
  apply compress_prefix with M2.
  rewrite <- eq2.
  auto.
  assert (l_eq : l1 = l2).
  inversion cleq.
  auto.
  rewrite -> l_eq in prefL.
  assert (contr : prefix (cd D l) (cd D m) + prefix (cd D m) (cd D l)).
  apply prefix_common with l2.
  apply prefL.
  apply prefM.
  elim contr.
  intros plm.
  assert (H:(cd D l = Bnil) + (~ prefix (cd D l) (cd D m))).
  apply prefix_free.
  auto.
  elim H.
  intros isnil.
  rewrite -> cddl in isnil.
  inversion isnil.
  intros npref.
  contradict plm.
  auto.
  intros pml.
  assert (H:(cd D m = Bnil) + (~ prefix (cd D m) (cd D l))).
  apply prefix_free.
  auto.
  elim H.
  intros cddmnil.
  rewrite -> eq2 in cdm.
  unfold compress in cdm.
  rewrite -> cddmnil in cdm.
  inversion cdm.
  intros npref.
  contradict pml.
  auto.

  inversion cleq.  
  apply inl.
  rewrite <- eq.
  auto.
Qed.

Function drop {A} (n : nat) (L : list A) :=
  match L with
    | [] => []
    | x :: L' =>
      match n return list A with
        | 0 => x :: L'
        | (S n') => drop n' L'
      end
  end.

Lemma simple_decompress_hack : forall l c,
                                 prefix l c -> l ++ drop (ll l) c = c.
Proof.
  refine (fix f l c lc := 
            match c as C return (c = C -> _) with
              | nil => fun eq => _
              | c' :: c'' => fun eq => _
            end eq_refl).
  inversion lc as [x H].
  rewrite -> eq in H.
  destruct l.
  reflexivity.
  inversion H.

  destruct l as [|b l].
  reflexivity.
  assert (l ++ drop (ll l) c'' = c'').
  apply f.
  rewrite -> eq in lc.
  inversion lc as [x H].
  inversion H.
  exists x.
  reflexivity.
  replace (drop (ll (b :: l)) (c' :: c'')) with (drop (ll l) c'').
  replace (c' :: c'') with (c' :: (l ++ drop (ll l) c'')).
  inversion lc as [? H0].
  rewrite -> eq in H0.
  inversion H0.
  reflexivity.
  rewrite -> H.
  reflexivity.
  reflexivity.
Qed.
  
Theorem simple_decompress : forall (D : deflateCoding) (L : LB),
                              {C | compress D C = Just L} +
                              ({C | compress D C = Just L} -> False).
Proof.
  intros D L.
  refine ((fix sd (n : nat) (O : LB) (le : ll O <= n) :=
             match n as N return (n = N -> _) with
               | 0 => fun eq => _
               | S n' => fun eq => _
             end eq_refl) (ll L) L _).

  destruct O as [|m O].
  apply inl.
  exists (nil(A:=fin(M D))).
  reflexivity.
  contradict le.
  unfold ll.
  rewrite -> eq.
  omega.

  set (c := (fun x => x <> Bnil /\ prefix x O)).
  assert (maypref : {n : fin (M D) & c (Vnth (C D) n)} + ({n : fin (M D) & c (Vnth (C D) n)} -> False)).
  apply dec_in_dec_set.
  intros a.
  destruct a as [|a' a''].
  apply inr.
  intros cnil.
  destruct cnil as [nnil ?].
  contradict nnil.
  reflexivity.
  destruct (prefix_dec (a' :: a'') O) as [ispref | isntpref].
  apply inl.
  split.
  intros q.
  inversion q.
  auto.
  apply inr.
  intros ca.
  destruct ca.
  contradict isntpref.
  auto.
  destruct maypref as [[n'' c''] | hasntpref].
  set (O' := drop (ll (cd D n'')) O).
  assert (Hack : cd D n'' ++ O' = O).
  apply simple_decompress_hack.
  apply c''.
  destruct (sd n' O') as [[C Ceq] | H].
  assert (tmp1 : ll (cd D n'') + ll O' = ll O).
  rewrite <- app_length.
  rewrite -> Hack.
  reflexivity.
  assert (tmp2 : ll O' = ll O - ll (cd D n'')).
  omega.
  rewrite -> tmp2.
  assert (tmp3 : ll (cd D n'') > 0).
  destruct (cd D n'').
  inversion c'' as [H ?].
  contradict H.
  reflexivity.
  unfold ll.
  omega.
  omega.
  apply inl.
  exists (n'' :: C).
  unfold compress.
  fold compress.
  rewrite -> Ceq.
  destruct (cd D n'') eqn:cddnnil.
  destruct c'' as [isnil ?].
  contradict isnil.
  auto.
  rewrite <- Hack.
  reflexivity.

  apply inr.
  intros H2.
  destruct H2 as [C cC].

  destruct (compress D C) as [l|] eqn:cdc.
  inversion cC as [cC'].

  destruct C as [|t C].
  unfold compress in cdc.
  rewrite -> cC' in cdc.
  rewrite <- Hack in cdc.
  inversion cdc as [H1].
  destruct (cd D n'').
  destruct c'' as [nnil ?].
  contradict nnil.
  reflexivity.
  inversion H1.

  assert (prf : prefix (cd D t) O).
  inversion cdc as [H1].
  destruct (cd D t).
  inversion H1.
  destruct (compress D C) as [l1 | l2] eqn:cdc2.
  exists l1.
  rewrite <- cC'.
  inversion H1.
  reflexivity.
  inversion H1.

  assert (H8 : t = n'').
  destruct (eq_fin_dec t n'').
  auto.

  assert (H7 : prefix (cd D t) (cd D n'') + prefix (cd D n'') (cd D t)).
  apply prefix_common with O.
  auto.
  apply c''.
  destruct H7 as [tn | nt].
  assert (contr : (cd D t = nil) + (~ prefix (cd D t) (cd D n''))).
  apply prefix_free.
  auto.
  destruct contr as [m | ?].
  unfold compress in cdc.
  rewrite -> m in cdc.
  inversion cdc.
  contradict tn.
  auto.
  (* TODO : duplicate code *)
  assert (contr : (cd D n'' = nil) + (~ prefix (cd D n'') (cd D t))).
  apply prefix_free.
  auto.
  destruct contr as [m | ?].
  contradict m.
  apply c''.
  contradict nt.
  auto.

  contradict H.
  exists C.
  rewrite -> H8 in cdc.
  rewrite -> cC' in cdc.
  rewrite <- Hack in cdc.
  inversion cdc as [H0].
  destruct (cd D n'').
  inversion H0.
  destruct (compress D C).
  inversion H0 as [H1].
  f_equal.
  apply app_inv_head with l0.
  auto.
  inversion H0.
  inversion cC.

  destruct O as [|o O2] eqn:oeq.
  apply inl.
  exists(nil(A:=fin(M D))).
  reflexivity.

  apply inr.
  intros has.
  destruct has as [[|c' C] cC].
  inversion cC.
  inversion cC as [H0].
  destruct (cd D c') as [|b l] eqn:cddc.
  inversion H0.
  destruct (compress D C).
  contradict hasntpref.
  exists c'.
  rewrite -> cddc.
  split.
  intros Q.
  inversion Q.
  exists l0.
  inversion H0.
  auto.
  inversion H0.

  auto.
Qed.

Lemma zeroVec : forall (n : nat), {c : vec nat n | forall q, Vnth c q = 0}.
Proof.
  induction n.
  exists (Vnil nat).
  intros q.
  inversion q.
  destruct IHn as [x s].
  exists (Vcons _ 0 _ x).
  intros q.
  dependent induction q.
  reflexivity.
  apply s.
Qed.

Inductive ExNum {A} (Q : A -> Prop) : nat -> list A -> Prop :=
| xn_nil : forall a, ExNum Q a []
| xn_cons : forall b n L, Q b -> ExNum Q n L -> ExNum Q (S n) (b :: L)
| xn_neq : forall b n L, ~ (Q b) -> ExNum Q n L -> ExNum Q n (b :: L).


Lemma exnum_calc {A} : forall (Q : A -> Prop) L,
                         (forall a, ({Q a}+{~ Q a})%type) ->
                         {n | ExNum Q n L}.
Proof.
  intros Q L qdec.
  revert L.
  induction L as [|? ? IHL].
  exists 0.
  apply xn_nil.
  destruct IHL as [n xn].
  destruct (qdec a) as [aeqn | aneqn].
  exists (S n).
  apply xn_cons.
  apply aeqn.
  apply xn.
  exists n.
  apply xn_neq.
  apply aneqn.
  apply xn.
Qed.

Fixpoint count {A} (Q : A -> Prop) L (dec : forall a, ({Q a}+{~ Q a})%type) :=
  match L with
    | [] => 0
    | x :: L' =>
      match (dec x) with
        | in_left => S (count Q L' dec)
        | in_right => count Q L' dec
      end
  end.

Lemma count_correct {A} : forall (L : list A) Q dc, ExNum Q (count Q L dc) L.
Proof.
  intros L Q dc.
  induction L as [|a L IHL].
  apply xn_nil.
  destruct (dc a) eqn:dca.
  replace (count Q (a :: L) dc) with (S (count Q L dc)).
  apply xn_cons.
  auto.
  auto.
  unfold count.
  rewrite -> dca.
  reflexivity.
  replace (count Q (a :: L) dc) with (count Q L dc).
  apply xn_neq.
  auto.
  auto.
  unfold count.
  rewrite -> dca.
  reflexivity.
Qed.

Definition finsum {n} := fold (n:=n) 0 plus.

Fixpoint componentwise {n} {A B C} (f : A -> B -> C) (x : vec A n) (y : vec B n) : vec C n.
Proof.
  dependent induction n.
  apply Vnil.
  dependent destruction x.
  dependent destruction y.
  assert (rc : vec C n).
  apply (componentwise _ _ _ _ f x y).
  apply (Vcons _ (f h h0) _ rc).
Defined.

Lemma lsum_inc {n} : forall m a g,
                       finsum (` (array_set (n:=n) g m (a + (Vnth g m)))) =
                       a + finsum g.
Proof.
  induction n as [| n IHn].
  intros m.
  inversion m.
  intros m a g.
  destruct (eq_fin_dec m FinF1) as [efd | nefd].
  rewrite -> efd.
  dependent destruction g.
  assert (H:` (array_set (Vcons nat h n g) FinF1 (a + h)) = Vcons nat (a + h) n g).
  apply eq_nth_iff.
  intros p1 p2 eq.
  rewrite -> eq.
  dependent destruction p2.
  apply (proj2_sig (array_set (Vcons nat h n g) FinF1 (a + h))).
  reflexivity.
  apply (proj2_sig (array_set (Vcons nat h n g) FinF1 (a + h))).
  intros Q.
  inversion Q.
  assert(tmp2:Vnth (Vcons nat h n g) FinF1 = h).
  reflexivity.
  rewrite -> tmp2.
  rewrite -> H.  
  assert (tmp3 : finsum (Vcons nat (a + h) n g) = (a + h) + finsum g).
  reflexivity.
  rewrite -> tmp3.
  rewrite <- plus_assoc.
  reflexivity.
  dependent destruction m.
  contradict nefd.
  reflexivity.
  dependent destruction g.
  assert (tmp1 : ` (array_set (Vcons nat h n g) (FinFS m)
                              (a + Vnth (Vcons nat h n g) (FinFS m))) =
                 Vcons nat h n (` (array_set g m
                                             (a + Vnth g m)))).
  apply eq_nth_iff.
  intros p1 p2 eq.
  rewrite -> eq.
  dependent induction p2.
  replace (Vnth (Vcons nat h n (` (array_set g m (a + Vnth g m)))) FinF1) with h.
  apply (proj2_sig (array_set (Vcons nat h n g) (FinFS m)
         (a + Vnth (Vcons nat h n g) (FinFS m)))).
  intros Q.
  inversion Q.
  auto.
  destruct (eq_fin_dec m p2) as [m_eq | m_neq].
  rewrite <- m_eq.
  assert (tmp1:Vnth
            (`
               (array_set (Vcons nat h n g) (FinFS m)
                          (a + Vnth (Vcons nat h n g) (FinFS m)))) (FinFS m) =
          (a + Vnth (Vcons nat h n g) (FinFS m))).
  apply (proj2_sig (array_set (Vcons nat h n g) (FinFS m)
                              (a + Vnth (Vcons nat h n g) (FinFS m)))).
  reflexivity.
  rewrite -> tmp1.
  assert (tmp2:Vnth (Vcons nat h n (` (array_set g m (a + Vnth g m)))) (FinFS m) =
          Vnth (` (array_set g m (a + Vnth g m))) m).
  auto.
  rewrite -> tmp2.
  symmetry.
  apply (proj2_sig (array_set g m (a + Vnth g m))).
  reflexivity.

  assert (tmp1 : Vnth
                   (`
                      (array_set (Vcons nat h n g) (FinFS m)
                                 (a + Vnth (Vcons nat h n g) (FinFS m)))) (FinFS p2) =
                 Vnth g p2).
  apply (proj2_sig (array_set (Vcons nat h n g) (FinFS m)
                                 (a + Vnth (Vcons nat h n g) (FinFS m)))).
  contradict m_neq.
  apply Fin.FS_inj.
  auto.
  rewrite -> tmp1.
  symmetry.
  apply (proj2_sig (array_set g m (a + Vnth g m))).
  auto.
  rewrite -> tmp1.
  assert (tmp2 : finsum (Vcons nat h n (` (array_set g m (a + Vnth g m)))) =
                 h + finsum (` (array_set g m (a + Vnth g m)))).
  auto.
  rewrite -> tmp2.
  rewrite -> IHn.
  replace (finsum (Vcons nat h n g)) with (h + finsum g).
  omega.
  reflexivity.
Qed.

Fixpoint simple_zero_vec (n : nat) :=
  match n with
    | 0 => Vnil nat
    | (S n') => Vcons _ 0 _ (simple_zero_vec n')
  end.

Lemma compwise_nth : forall {A C} {m} n (f : A->A->C) (q r:vec A m), Vnth (componentwise f q r) n = f (Vnth q n) (Vnth r n).
Proof.
  intros A C m n f q r.
  dependent induction n.
  dependent destruction q.
  dependent destruction r.
  auto.
  dependent destruction q.
  dependent destruction r.
  replace (Vnth (Vcons A h n q) (FinFS n0)) with (Vnth q n0).
  replace (Vnth (Vcons A h0 n r) (FinFS n0)) with (Vnth r n0).
  rewrite <- IHn.
  auto.
  auto.
  auto.
Qed.

Lemma compwise_zero_mult {n} : forall (f : vec nat n),
                                 componentwise mult f (simple_zero_vec n) = (simple_zero_vec n).
Proof.
  intros f.
  dependent induction n.
  auto.
  replace (simple_zero_vec (S n)) with (Vcons _ 0 _ (simple_zero_vec n)).
  dependent destruction f.
  replace (componentwise _ _ _) with (Vcons _ (h * 0) _ (componentwise mult f (simple_zero_vec n))).
  rewrite -> IHn.
  replace (h * 0) with 0.
  reflexivity.
  omega.
  auto.
  auto.
Qed.

Lemma zero_sum_is_zero {n} : finsum (simple_zero_vec n) = 0.
Proof.
  induction n.
  auto.
  replace (finsum _) with (0 + (finsum (simple_zero_vec n))).
  rewrite -> IHn.
  omega.
  auto.
Qed.

Lemma lsum {n} : forall (l : list (fin n)),
                   {g : vec nat n|forall (f : vec nat n),
                    foldlist 0 plus (map (Vnth f) l) =
                    finsum (componentwise mult f g)}.
Proof.
  intros l.
  induction l as [|a l' IHl].
  exists (simple_zero_vec n).

  intros f.
  rewrite -> compwise_zero_mult.
  rewrite -> zero_sum_is_zero.
  auto.

  destruct IHl as [g geq].
  destruct (array_set g a (S (Vnth g a))) as [g' g'eq].
  exists g'.
  intros f.
  replace (foldlist 0 plus (map (Vnth f) (a :: l'))) with (Vnth f a + foldlist 0 plus (map (Vnth f) l')).

  assert (cws : (componentwise mult f g') = ` (array_set (componentwise mult f g) a (Vnth f a + Vnth (componentwise mult f g) a))).
  apply eq_nth_iff.
  intros p1 p2 peq.
  rewrite -> peq.
  destruct (eq_fin_dec p2 a) as [p2_eq_a | p2_neq_a].
  rewrite -> p2_eq_a.
  rewrite -> compwise_nth.
  replace (Vnth (` (array_set (componentwise mult f g) a
                              (Vnth f a + Vnth (componentwise mult f g) a))) a)
  with
  (Vnth f a + Vnth (componentwise mult f g) a).
  replace (Vnth g' a) with (S (Vnth g a)).
  rewrite -> compwise_nth.
  replace (S _) with (1 + Vnth g a).
  rewrite -> mult_plus_distr_l.
  omega.
  auto.
  symmetry.
  apply g'eq.
  reflexivity.
  symmetry.
  apply (proj2_sig (array_set (componentwise mult f g) a
                                 (Vnth f a + Vnth (componentwise mult f g) a))).
  reflexivity.
  rewrite -> compwise_nth.
  rewrite -> ((proj2 (proj2_sig (array_set (componentwise mult f g) a
                                   (Vnth f a + Vnth (componentwise mult f g) a)) p2))).
  rewrite -> compwise_nth.
  rewrite -> (proj2 (g'eq p2)).
  reflexivity.
  auto.
  auto.

  rewrite -> geq.
  rewrite -> cws.
  symmetry.
  apply lsum_inc.
  auto.
Qed.

Lemma lsum_counts {n} : forall (l : list (fin n)),
                          forall m, ExNum (fun x => m = x) (Vnth (` (lsum l)) m) l.
Proof.
  intros l m.
  assert (xn : ExNum (fun x : fin n => m = x) (foldlist 0 plus (map (fun x => if eq_fin_dec m x then 1 else 0) l)) l).
  induction l.
  apply xn_nil.
  assert (tmp1 : map (fun x : fin n => if eq_fin_dec m x then 1 else 0) (a :: l) =
                 (if eq_fin_dec m a then 1 else 0) :: map (fun x : fin n => if eq_fin_dec m x then 1 else 0) l).
  auto.
  destruct (eq_fin_dec m a) as [m_eq_a | m_neq_a] eqn:nea.
  rewrite -> tmp1.
  unfold foldlist.
  apply xn_cons.
  auto.
  apply IHl.
  rewrite -> tmp1.
  unfold foldlist.
  rewrite -> plus_O_n.
  apply xn_neq.
  auto.
  apply IHl.
  assert (ls : (Vnth (` (lsum l)) m) =
               (foldlist 0 plus
                         (map (fun x : fin n => if eq_fin_dec m x then 1 else 0) l))).
  induction l.
  destruct (eq_nat_dec (Vnth (` (lsum [ ])) m) 0) as [isz | noz].
  rewrite -> isz.
  auto.*)