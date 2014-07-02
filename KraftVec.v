Require Import Coq.Vectors.Vector.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qfield.
Require Import Coq.PArith.BinPos.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import NPeano.
Require Import Program.

Require Import DeflateNotations.
Require Import Prefix.
Require Import Combi.
Require Import KraftList.
Require Import Transports.

(* mostly boilerplate *)

Local Open Scope Q_scope.

Function kraft_nvec {n} (vn : vec nat n) : Q :=
  fold 0 Qplus (Vmap (fun d =>
                        match d with
                          | 0%nat => 0%Q
                          | d' => 1 # (e2 d')
                        end) vn).

Function kraft_vec {n} (vc : vec LB n) : Q :=
  kraft_nvec (Vmap (ll(A:=bool)) vc).

Fixpoint list_of_nonnil_codes {n} (v : vec LB n) : list LB :=
  match v with
    | Vnil _ => nil
    | (Vcons _ h _ v') =>
      match h with
        | nil => list_of_nonnil_codes v'
        | h' => h' :: list_of_nonnil_codes v'
      end
  end.

Lemma list_of_nonnil_codes_does_not_contain_nil :
  forall {n} (a : LB) (v : vec LB n),
    In a (list_of_nonnil_codes v) -> a <> nil.
Proof.
  intros n a v H isnil.
  dependent induction n.
  assert (H0 : v = Vnil _).
  apply vec_0_nil.
  rewrite -> H0 in H.
  inversion H.
  dependent destruction v.
  elim (list_eq_dec bool_dec a h).
  intros a_eq_h.  
  replace (list_of_nonnil_codes (Vcons LB h n v))
  with (list_of_nonnil_codes v) in H.
  apply (IHn a v).
  apply H.
  apply isnil.
  rewrite <- a_eq_h.
  rewrite -> isnil.
  reflexivity.
  intros a_neq_h.
  assert (inor : h = a \/ (In a (list_of_nonnil_codes v))).
  apply in_inv.
  assert (calc : h :: list_of_nonnil_codes v = list_of_nonnil_codes (Vcons LB h n v)).
  destruct h.
  contradict a_neq_h.
  apply isnil.
  reflexivity.
  rewrite -> calc.
  apply H.
  elim inor.
  intros h_eq_a.
  contradict a_neq_h.
  symmetry.
  apply h_eq_a.
  intros incdr.
  apply (IHn a v).
  apply incdr.
  apply isnil.
Defined.

Lemma list_of_nonnil_codes_contains_everything' :
  forall {n} (a : LB) (v : vec LB n) na, Vnth v na = a -> a <> Bnil ->
                                         In a (list_of_nonnil_codes v).
Proof.
  induction n.
  intros q r na.
  inversion na.
  intros a v na eq nnil.
  dependent destruction v.
  dependent destruction na.
  assert (H : h = a).
  apply eq.
  rewrite -> H.
  destruct a.
  contradict nnil.
  reflexivity.
  apply in_eq.
  destruct h.
  apply (IHn _ _ na).
  auto.
  auto.
  apply in_cons.
  apply (IHn _ _ na).
  auto.
  auto.
Defined.  

Lemma list_of_nonnil_codes_contains_everything :
  forall {n} (a : LB) (v : vec LB n),
    In a (list_of_nonnil_codes v) -> {na | Vnth v na = a}.
Proof.
  intros n a v i.
  induction n.
  dependent destruction v.
  inversion i.
  dependent destruction v.
  elim (list_eq_dec bool_dec a h).
  intros a_eq_h.
  exists(FinF1(n:=n)).
  rewrite -> a_eq_h.
  reflexivity.
  intros a_neq_h.
  assert(ind:{na : fin n | Vnth v na = a}).
  apply IHn.
  assert (inv:h = a \/ In a (list_of_nonnil_codes v)).
  destruct h.
  apply or_intror.
  apply i.
  apply in_inv.
  apply i.
  elim inv.
  intros h_eq_a.
  contradict a_neq_h.
  symmetry.
  apply h_eq_a.
  trivial.
  elim ind.
  intros x xu.
  exists (FinFS x).
  apply xu.
Defined.

Lemma list_of_nonnil_codes_is_dup_free' :
  forall {n} (v : vec LB n),
    (forall a b, a <> b -> ((Vnth v a) = nil) + ~ (prefix (Vnth v a) (Vnth v b))) ->
    dflist (list_of_nonnil_codes v).
Proof.
  intros n v pf.
  dependent induction v.
  apply dflist_nil.
  destruct h.
  apply IHv.
  intros a b neq.
  apply (pf (FinFS a) (FinFS b)).
  contradict neq.
  apply FS_inj.
  apply neq.
  assert (tmp1 : 
            list_of_nonnil_codes (Vcons LB (b :: h) n v) =
            (b :: h) :: list_of_nonnil_codes v).
  reflexivity.
  rewrite -> tmp1.
  apply dflist_cons.
  apply IHv.
  intros a b0 neq.
  apply (pf (FinFS a) (FinFS b0)).
  contradict neq.
  apply FS_inj.
  apply neq.
  intros isin.
  assert (cont : {na | Vnth v na = (b :: h)}).
  apply list_of_nonnil_codes_contains_everything.
  apply isin.
  elim cont.
  intros na nan.
  assert (ispref:prefix (Vnth (Vcons LB (b :: h) n v) (FinFS na)) (Vnth (Vcons LB (b :: h) n v) FinF1)).
  exists Bnil.
  replace (Vnth (Vcons LB (b :: h) n v) (FinFS na)) with (Vnth v na).
  rewrite -> nan.
  replace (Vnth (Vcons LB (b :: h) n v) FinF1) with (b :: h).
  apply app_nil_r.
  reflexivity.
  reflexivity.
  assert (contr: ((Vnth (Vcons LB (b :: h) n v) (FinFS na)) = Bnil) + ~ prefix (Vnth (Vcons LB (b :: h) n v) (FinFS na))
                                                                        (Vnth (Vcons LB (b :: h) n v) FinF1)).
  apply pf.
  intros Q.
  inversion Q.
  elim contr.
  intros Q.
  inversion Q.
  rewrite -> nan in H0.
  inversion H0.
  contradict ispref.
  apply ispref.
Defined.

Lemma list_of_nonnil_codes_is_prefix_free' :
  forall {n} (v : vec LB n),
    (forall a b, a <> b -> ((Vnth v a) = nil) +
                           ~ (prefix (Vnth v a) (Vnth v b))) ->
    pflist (list_of_nonnil_codes v).
Proof.
  unfold pflist.
  intros n v pf a b H H0 H1 H2.
  assert (xna : {na | Vnth v na = a}).
  apply list_of_nonnil_codes_contains_everything.
  apply H.
  elim xna.
  intros na cdna.
  assert (xnb : {nb | Vnth v nb = b}).
  apply list_of_nonnil_codes_contains_everything.
  apply H0.
  elim xnb.
  intros nb cdnb.
  assert (cpf : (a = nil) + ~ (prefix a b)).
  rewrite <- cdna.
  rewrite <- cdnb.
  apply pf.
  contradict H1.
  rewrite <- cdna.
  rewrite <- cdnb.
  rewrite -> H1.
  reflexivity.
  elim cpf.
  apply (list_of_nonnil_codes_does_not_contain_nil a v H).
  contradict H2.
  apply H2.
Defined.

Lemma kraft_list_is_kraft_vec :
  forall {n} (v : vec LB n),
    kraft_list (list_of_nonnil_codes v) ==
    kraft_vec v.
Proof.
  intros n v.
  dependent induction n.
  dependent destruction v.
  reflexivity.
  dependent destruction v.
  destruct h.
  replace (list_of_nonnil_codes (Vcons LB Bnil n v)) with (list_of_nonnil_codes v).
  assert (tmp1 : kraft_vec (Vcons LB Bnil n v) == kraft_vec v).
  replace (kraft_vec (Vcons LB Bnil n v)) with (0 + kraft_vec v).
  ring.
  reflexivity.
  rewrite -> tmp1.
  apply IHn.
  reflexivity.
  assert (tmp1:kraft_list (list_of_nonnil_codes (Vcons LB (b :: h) n v)) =
               (1 # (e2 (ll (b :: h)))) + kraft_list (list_of_nonnil_codes v)).
  reflexivity.
  rewrite -> tmp1.
  assert (tmp2:kraft_vec (Vcons LB (b :: h) n v) = (1 # (e2 (ll (b :: h)))) + (kraft_vec v)).
  reflexivity.
  rewrite -> tmp2.
  rewrite -> IHn.
  reflexivity.
Defined.

Lemma kraft_nvec_positive : forall {n} (vn : vec nat n), kraft_nvec vn >= 0.
Proof.
  induction vn.
  replace (kraft_nvec (Vnil nat)) with 0.
  compute.
  intros Q.
  inversion Q.
  auto.
  elim (eq_nat_dec h 0%nat).
  intros h_0.
  rewrite -> h_0.
  assert (H : kraft_nvec (Vcons nat 0%nat n vn) = Qplus 0 (kraft_nvec vn)).
  assert (H1 : kraft_nvec (Vcons nat 0%nat n vn) = Qplus 0 (fold 0 Qplus (Vmap (fun d =>
                                                                                  match d with
                                                                                    | 0%nat => 0%Q
                                                                                    | d' => 1 # (e2 d')
                                                                                  end) vn))).
  auto.
  assert (H2 : kraft_nvec vn = fold 0 Qplus (Vmap (fun d =>
                                                     match d with
                                                       | 0%nat => 0%Q
                                                       | d' => 1 # (e2 d')
                                                     end) vn)).
  auto.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
  rewrite -> H.
  assert (H' : 0 + 0 <= 0 + kraft_nvec vn).
  apply Qplus_le_compat.
  compute.
  intros Q.
  inversion Q.
  auto.
  auto.
  intros h_neq_0.
  induction h.
  contradict h_neq_0.
  auto.
  assert (H : kraft_nvec (Vcons nat (S h) n vn) = Qplus (1 # (e2 (S h))) (kraft_nvec vn)).
  assert (H1 : kraft_nvec (Vcons nat (S h) n vn) = Qplus (1 # (e2 (S h))) (fold 0 Qplus (Vmap (fun d =>
                                                                                                 match d with
                                                                                                   | 0%nat => 0%Q
                                                                                                   | d' => 1 # (e2 d')
                                                                                                 end) vn))).
  auto.
  assert (H2 : kraft_nvec vn = fold 0 Qplus (Vmap (fun d =>
                                                     match d with
                                                       | 0%nat => 0%Q
                                                       | d' => 1 # (e2 d')
                                                     end) vn)).
  auto.
  rewrite -> H1.
  rewrite <- H2.
  reflexivity.
  rewrite -> H.
  replace 0 with (Qplus 0 0).
  apply Qplus_le_compat.
  assert (H0 : 1 # e2 (S h) = / (Zpos (e2 (S h)) # 1)).
  auto.
  rewrite -> H0.
  apply Qinv_le_0_compat.
  compute.
  intros Q.
  inversion Q.
  auto.
  auto.
Defined.

Lemma kraft_nvec_inc : forall n (v1 v2 : vec nat n) (q : fin n) (r : nat),
                         (forall (b : fin n),
                            (b = q -> (Vnth v1 b = 0%nat 
                                       /\ Vnth v2 b = (S r))) /\
                            (b <> q -> Vnth v2 b = Vnth v1 b)) ->
                         kraft_nvec v2 == (1 # (e2 (S r))) + kraft_nvec v1.
Proof.
  dependent induction n.
  intros v1 v2 q.
  inversion q.
  intros v1 v2 q r eq.
  dependent destruction v1.
  dependent destruction v2.
  dependent induction q.
  assert (h_eq_0 : h = 0%nat).
  replace h with (Vnth (Vcons nat h n v1) FinF1).
  apply (proj1 (eq FinF1) eq_refl).
  auto.
  rewrite -> h_eq_0.
  assert (h0_eq_sr : h0 = S r).
  replace h0 with (Vnth (Vcons nat h0 n v2) FinF1).
  apply (proj1 (eq FinF1) eq_refl).
  auto.
  rewrite -> h0_eq_sr.
  replace (kraft_nvec (Vcons nat (S r) n v2)) with ((1 # e2 (S r)) + kraft_nvec v2).
  replace (kraft_nvec (Vcons nat 0%nat n v1)) with (0 + kraft_nvec v1).
  replace v2 with v1.
  rewrite -> Qplus_assoc.
  rewrite -> Qplus_0_r.
  reflexivity.
  apply eq_nth_iff.
  intros p1 p2 peq.
  rewrite -> peq.
  replace (Vnth v1 p2) with (Vnth (Vcons nat h n v1) (FinFS p2)).
  replace (Vnth v2 p2) with (Vnth (Vcons nat h0 n v2) (FinFS p2)).
  assert (neq : FinFS p2 <> FinF1).
  intros Q.
  inversion Q.
  symmetry.
  apply (proj2 (eq (FinFS p2)) neq).
  auto.
  auto.
  auto.
  auto.

  assert(rec : kraft_nvec v2 == (1 # e2 (S r)) + kraft_nvec v1).
  apply (IHn _ _ q).
  intros b.
  elim (eq_fin_dec b q).
  intros b_eq_q.
  assert (fbq : FinFS b = FinFS q).
  f_equal.
  auto.
  elim (proj1 (eq (FinFS b)) fbq).
  intros H H0.
  split.
  auto.
  intros b_neq_q.
  contradict b_eq_q.
  auto.
  intros b_neq_q.
  assert (fbq : FinFS b <> FinFS q).
  contradict b_neq_q.
  apply FS_inj.
  auto.
  split.
  intros b_eq_q.
  contradict b_eq_q.
  auto.
  intros b_neq_q_2.
  apply (proj2 (eq (FinFS b)) fbq).
  assert (h_eq_h0 : h0 = h).
  assert (ffq : FinF1 <> FinFS q).
  intros Q.
  inversion Q.
  apply (proj2 (eq FinF1) ffq).
  rewrite <- h_eq_h0.
  replace (kraft_nvec (Vcons nat h0 n v2)) with ((fun d =>
                                                    match d with
                                                      | 0%nat => 0%Q
                                                      | d' => 1 # (e2 d')
                                                    end) h0 + kraft_nvec v2).
  replace (kraft_nvec (Vcons nat h0 n v1)) with ((fun d =>
                                                    match d with
                                                      | 0%nat => 0%Q
                                                      | d' => 1 # (e2 d')
                                                    end) h0 + kraft_nvec v1).
  rewrite -> rec.
  field.
  auto.
  auto.
Defined.

Lemma kraft_nvec_le : forall n (v1 v2 : vec nat n),
                        (forall (q : fin n), (Vnth v1 q = Vnth v2 q) \/ (Vnth v1 q = 0%nat)) -> kraft_nvec v1 <= kraft_nvec v2.
Proof.
  intros n v1 v2 imp.
  dependent induction n.
  replace v1 with (Vnil nat).
  replace (kraft_nvec (Vnil nat)) with 0.
  apply kraft_nvec_positive.
  auto.
  symmetry.
  apply vec_0_nil.

  dependent destruction v1.
  dependent destruction v2.
  assert (h' : h = h0 \/ h = 0%nat).
  replace h with (Vnth (Vcons nat h n v1) FinF1).
  replace h0 with (Vnth (Vcons nat h0 n v2) FinF1).
  apply imp.
  auto.
  auto.
  elim (eq_nat_dec h0 0%nat).
  intros h0_eq_0.
  assert (h_eq_0 : h = 0%nat).
  elim h'.
  intros h_eq_h0.
  rewrite -> h_eq_h0.
  auto.
  auto.
  rewrite -> h_eq_0.
  rewrite -> h0_eq_0.
  replace (kraft_nvec (Vcons nat 0%nat n v1)) with (0 + kraft_nvec v1).
  replace (kraft_nvec (Vcons nat h0 n v2)) with (0 + kraft_nvec v2).
  apply Qplus_le_compat.
  compute.
  intros Q.
  inversion Q.
  apply IHn.
  intros q.
  elim (imp (FinFS q)).
  intros eq.
  apply or_introl.
  auto.
  intros zer.
  apply or_intror.
  auto.
  rewrite -> h0_eq_0.
  compute.
  auto.
  auto.
  intros h0_neq_0.
  elim h'.
  intros h_eq_h0.
  rewrite -> h_eq_h0.
  induction h0.
  contradict h0_neq_0.
  auto.
  replace (kraft_nvec (Vcons nat (S h0) n v1)) with ((1 # (e2 (S h0))) + kraft_nvec v1).
  replace (kraft_nvec (Vcons nat (S h0) n v2)) with ((1 # (e2 (S h0))) + kraft_nvec v2).
  apply Qplus_le_compat.
  apply Qle_refl.
  apply IHn.
  intros q.
  elim (imp (FinFS q)).
  auto.
  auto.
  compute.
  auto.
  compute.
  auto.
  intros h_eq_0.
  induction h0.
  contradict h0_neq_0.
  auto.
  rewrite -> h_eq_0.
  replace (kraft_nvec (Vcons nat 0%nat n v1)) with (0 + kraft_nvec v1).
  replace (kraft_nvec (Vcons nat (S h0) n v2)) with ((1 # e2 (S h0)) + kraft_nvec v2).
  apply Qplus_le_compat.
  replace (1 # e2 (S h0)) with (/ ((Zpos (e2 (S h0))) # 1)).
  apply Qinv_le_0_compat.
  compute.
  intros Q.
  inversion Q.
  auto.
  apply IHn.
  intros q.
  elim (imp (FinFS q)).
  auto.
  auto.
  compute.
  auto.
  compute.
  auto.
Defined.

Lemma nvec_id : forall {n m} (eq : n = m) q, kraft_nvec q = kraft_nvec (vec_id eq q).
Proof.
  intros n m eq q.
  dependent destruction eq.
  rewrite -> vec_id_destroy.
  reflexivity.
Defined.

