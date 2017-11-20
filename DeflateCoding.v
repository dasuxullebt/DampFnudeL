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
Require Import String.

Require Import Shorthand.
Require Import Quicksort.
Require Import Lex.
Require Import Transports.
Require Import Prefix.
Require Import Repeat.
Require Import Combi.
Require Import KraftList.
Require Import KraftVec.
Require Import StrongDec.

Local Open Scope nat_scope.

(*Record deflateCoding (M : nat) : Set :=
  mkDeflateCoding {
      (* M : nat ; (* alphabet [0, M[ *) *)
      C : VecLB M ;
      prefix_free : forall a b, a <> b -> ((Vnth C a) = nil) + ~ (prefix (Vnth C a) (Vnth C b)) ;
      length_lex : forall a b, ll (Vnth C a) < ll (Vnth C b) -> lex (Vnth C a) (Vnth C b) ;
      char_enc : forall a b, ll (Vnth C a) = ll (Vnth C b) -> (f_le a b) -> lex (Vnth C a) (Vnth C b) ;
      dense : forall a c, c <> nil -> lex c (Vnth C a) -> ll c = ll (Vnth C a)
                          -> exists b, (~ (Vnth C b) = nil) /\ (prefix (Vnth C b) c)
  }.*)

Record deflateCoding (M : nat) : Set :=
  mkDeflateCoding {
      (* M : nat ; (* alphabet [0, M[ *) *)
      C : VecLB M ;
      prefix_free : forall a b, a <> b -> ((Vnth C a) <> nil) -> ~ (prefix (Vnth C a) (Vnth C b)) ;
      length_lex : forall a b, ll (Vnth C a) < ll (Vnth C b) -> lex (Vnth C a) (Vnth C b) ;
      char_enc : forall a b, ll (Vnth C a) = ll (Vnth C b) -> (f_le a b) -> lex (Vnth C a) (Vnth C b) ;
      dense : forall a c, c <> nil -> lex c (Vnth C a) -> ll c = ll (Vnth C a)
                          -> exists b, (~ (Vnth C b) = nil) /\ (prefix (Vnth C b) c)
  }.

Lemma prefix_free_set_inv :
  forall {M} (c : VecLB M),
    (forall a b, a <> b -> ((Vnth c a) = nil) + ~ (prefix (Vnth c a) (Vnth c b))) ->
    forall a b, a <> b -> ((Vnth c a) <> nil) -> ~ (prefix (Vnth c a) (Vnth c b)).
Proof.
  intros M c H a b H0 H1.
  destruct (H a b H0).
  contradict H1.
  trivial.
  trivial.
Qed.

Lemma prefix_free_to_set :
  forall {M} (c : VecLB M),
    (forall a b, a <> b -> ((Vnth c a) <> nil) -> ~ (prefix (Vnth c a) (Vnth c b))) ->
    forall a b, a <> b -> ((Vnth c a) = nil) + ~ (prefix (Vnth c a) (Vnth c b)).
Proof.
  intros M c H a b H0.
  destruct (list_eq_dec bool_dec (Vnth c a) Bnil).
  auto.
  apply inr.
  apply H.
  trivial.
  trivial.
Qed.

Theorem prefix_free_set : forall M (D : deflateCoding M) a b,
                            a <> b -> ((Vnth (C M D) a) = nil) + ~ (prefix (Vnth (C M D) a) (Vnth (C M D) b)).
Proof.
  intros M D. 
  exact (prefix_free_to_set (C M D) (prefix_free M D)).
Qed.

Theorem deflateCodingEq : forall {M} (D E : deflateCoding M), C M D = C M E -> D = E.
Proof.
  intros M D E eq.
  dependent destruction D.
  dependent destruction E.
  compute in eq.
  dependent induction eq.
  assert (pf : prefix_free0 = prefix_free1).
  apply proof_irrelevance.
  assert (lxl : length_lex0 = length_lex1).
  apply proof_irrelevance.
  assert (ce : char_enc0 = char_enc1).
  apply proof_irrelevance.
  assert (den : dense0 = dense1).
  apply proof_irrelevance.
  rewrite -> pf.
  rewrite -> lxl.
  rewrite -> ce.
  rewrite -> den.
  reflexivity.
Qed.

Function cd {m : nat} (D : deflateCoding m) a := (Vnth (C m D) a).

(** "deflate coding encodes" *)
Definition dc_enc {m : nat} (dc : deflateCoding m) (n : nat) (l : LB) : Prop :=
  (Vnth_is m n (C m dc) l /\ (l <> nil)).

Lemma Vnth_max : forall {m : nat} (v : VecLB m) n l, Vnth_is m n v l -> n < m.
Proof.
  intros m v n l vni.
  dependent induction vni.
  omega.
  omega.
Qed.

Lemma dc_max : forall {m : nat} (dc : deflateCoding m) n l, dc_enc dc n l -> n < m.
Proof.
  intros m dc n l dce.
  destruct dce as [dce1 dce2].
  apply (Vnth_max (C m dc) n l).
  trivial.
Qed.

Lemma dc_injective {m : nat} (D : deflateCoding m) a b : cd D a <> nil -> cd D a = cd D b -> a = b.
Proof.
  intros nnil cdeq.
  assert (EQD : {a = b} + {a <> b}).
  apply eq_fin_dec.
  induction EQD.
  trivial.
  assert (H : (cd D a = nil) + ~ prefix (cd D a) (cd D b)).
  apply (prefix_free_set m D).
  trivial.
  induction H.
  contradict nnil.
  trivial.
  contradict b1.
  rewrite -> cdeq.
  exists (nil : LB).
  apply app_nil_r.
Defined.

Lemma minofitslen_dec : forall {m : nat} (E : deflateCoding m) x,
                          {n | ll (cd E n) = ll (cd E x) /\ lex (cd E n) (cd E x)} +
                          ({n | ll (cd E n) = ll (cd E x) /\ lex (cd E n) (cd E x)}->False).
Proof.
  intros m E x.
  apply (dec_in_dec (C m E) (fun N => ll N = ll (cd E x) /\ lex N (cd E x))).
  intros a.
  elim (eq_nat_dec (ll a) (ll (cd E x))).
  intros ll_eq.
  elim (dec_lex a (cd E x)).
  intros lex_ax.
  apply inl.
  split. auto. auto.
  intros nlex.
  apply inr.
  intros wedge.
  elim wedge.
  intros X Y.
  apply nlex.
  auto.
  intros ll_neq.
  apply inr.
  intros wedge.
  elim wedge.
  intros X Y.
  apply ll_neq.
  auto.
Defined.

Lemma exdiff_vector : forall {m : nat} (V1 V2 : vec LB m),
                        {n | Vnth V1 n <> Vnth V2 n} +
                        ({n | Vnth V1 n <> Vnth V2 n}->False).
Proof.
  induction m.

  intros; apply inr; intro Q; destruct Q as [n ?]; inversion n.

  dependent destruction V1.
  dependent destruction V2.
  destruct (IHm V1 V2) as [[n w] | y].
  apply inl.
  exists (FinFS n).
  auto.

  destruct (list_eq_dec bool_dec h h0) as [leq | lneq].
  apply inr.
  intro Q.
  destruct Q as [n2 w].
  dependent destruction n2.
  apply (w leq).

  contradict y.
  exists n2.
  apply w.

  apply inl.
  exists (FinF1 (n:=m)).
  auto.
Qed.

(** Inequality of codings is decidable *)
Lemma exdiff : forall {m : nat} (D E : deflateCoding m),
                 {n | cd D n <> cd E n} +
                 ({n | cd D n <> cd E n}->False).
Proof.
  intros m D E.
  apply (exdiff_vector (C m D) (C m E)).
Qed.

Theorem uniqueness : forall {m : nat} (D E : deflateCoding m),
                     (Vmap lb (C m D)) = (Vmap lb (C m E)) -> D = E.
intros m D E eqv.
assert (uniqueness' : C m D = C m E).

(* small lemmata we need later *)
assert (lemma1 : forall b, lb (cd D b) = lb (cd E b)).
intro b.
replace (ll (cd D b)) with (Vnth (Vmap lb (C m D)) b).
replace (ll (cd E b)) with (Vnth (Vmap lb (C m E)) b).
rewrite -> eqv.
reflexivity.
apply nth_map; reflexivity.
apply nth_map; reflexivity.

assert (declemma : forall a : fin m,
                     (cd D a <> cd E a) +
                     (cd D a <> cd E a -> False)).
intro a.
destruct (list_eq_dec bool_dec (cd D a) (cd E a)) as [A | NA].
firstorder.
firstorder.

(* we now know that either there is a difference between the codings,
or there is not. the latter case will be rather trivial, but we need
to falsify the first one. *)

destruct (exdiff D E) as [ex_diff | nex_diff].
(* hard case: there exists some difference *)

(* there exist lex-minimal elements where the difference occurs *)
destruct (min_dec_ex (C m D) (fun n => cd D n <> cd E n) declemma ex_diff) as [minD [minD1 minD2]].
destruct (min_dec_ex (C m E) (fun n => cd D n <> cd E n) declemma ex_diff) as [minE [minE1 minE2]].

(* the lengths of these minima are equal: *)
assert(leneq:ll (cd D minD) = ll (cd E minE)).
destruct (eq_nat_dec (ll (cd D minD)) (ll (cd E minE))) as [? | neq].
trivial.
destruct (not_eq _ _ neq) as [llt | lgt].
assert (llex : lex (cd E minD) (cd E minE)).
apply length_lex.
replace (Vnth (C m E) minD) with (cd E minD).
replace (Vnth (C m D) minE) with (cd D minE).
rewrite <- lemma1.
apply llt.
auto.
auto.

assert(H:cd E minD = cd E minE).
apply lex_antisym.
split.
apply llex.
apply minE2.
apply minD1.
rewrite -> lemma1.
rewrite -> H.
reflexivity.

assert (llex : lex (cd D minE) (cd D minD)).
apply length_lex.
replace (Vnth (C m D) minD) with (cd D minD).
replace (Vnth (C m D) minE) with (cd D minE).
rewrite -> lemma1.
apply lgt.
auto.
auto.

assert(H: cd D minE = cd D minD).
apply lex_antisym.
split.
apply llex.
apply minD2.
apply minE1.
rewrite <- lemma1.
rewrite <- H.
reflexivity.

(* cd E minE <> Bnil, cd D (... minD) <> Bnil *)

destruct (list_eq_dec bool_dec (cd E minE) nil) as [eq | nnil_E].
assert (Q : cd D minE = nil).
apply nil_ll.
rewrite -> lemma1.
rewrite -> eq.
reflexivity.
assert (Q2 : cd E minE = cd D minE).
rewrite -> eq.
rewrite <- Q.
reflexivity.
contradict minE1.
auto.

destruct (list_eq_dec bool_dec (cd D minD) nil) as [eq | nnil_D].
assert (Q : cd E minD = nil).
apply nil_ll.
rewrite <- lemma1.
rewrite -> eq.
reflexivity.
assert (Q2 : cd E minD = cd D minD).
rewrite -> eq.
rewrite <- Q.
reflexivity.
contradict minD1.
auto.

(* minD = minE *)

assert (minEq : minD = minE).
elim (eq_fin_dec minD minE).
auto.

intros neq.
assert (f_nat_neq : ` (f_nat minD) <> ` (f_nat minE)).
contradict neq.
apply to_nat_inj.
auto.
assert (gt_or_lt : (` (f_nat minD) < ` (f_nat minE))%nat \/ (` (f_nat minD) > ` (f_nat minE))%nat).
apply not_eq.
apply f_nat_neq.
elim gt_or_lt.
intros d_lt_e.
assert (contr : lex (cd E minD) (cd E minE)).
apply char_enc.
replace (lb (Vnth (C m E) minD)) with (lb (cd D minD)). (* D is intended *)
replace (Vnth (C m E) minE) with (cd E minE).
auto.
auto.
replace (lb (Vnth (C m E) minD)) with (lb (cd E minD)).
apply lemma1.
auto.
apply lt_le_weak.
apply d_lt_e.
apply (dc_injective E).
apply nnil_ll.
rewrite <- lemma1.
contradict nnil_D.
apply nil_ll.
auto.
apply lex_antisym.
split.
trivial.
apply minE2.
trivial.

intros e_lt_d.
assert (contr : lex (cd D minE) (cd D minD)).
apply char_enc.
replace (lb (Vnth (C m D) minE)) with (lb (cd E minE)).
replace (lb (Vnth (C m D) minD)) with (lb (cd D minD)).
auto.
auto.
replace (Vnth (C m D) minE) with (cd D minE).
symmetry.
apply lemma1.
auto.
apply lt_le_weak.
apply e_lt_d.
apply (dc_injective D).
apply nnil_D.
apply lex_antisym.
split.
apply minD2.
auto.
auto.

(* now I know that minD=minE. two cases remain. *)

elim (lex_total (cd D minD) (cd E minE)).
intros lexDE.
assert (S:exists b, (cd E b <> nil) /\ (prefix (cd E b) (cd D minD))).
apply (dense m E minE). auto. auto. auto.
elim S.
intros b QQ.
elim QQ.
intros nnil pref.
elim (eq_fin_dec b minD).
intros b_eq_minD.
assert (contr : cd E minE = cd D minD).
apply prefix_ll_eq.
split.
rewrite <- minEq.
rewrite -> b_eq_minD in pref.
apply pref.
symmetry.
apply leneq.
contradict minE1.
symmetry.
rewrite -> minEq in contr.
apply contr.

intros b_neq_minD.
elim (list_eq_dec bool_dec (cd E b) (cd D b)).
intros eq.
rewrite -> eq in pref.
assert (pf : ((cd D b = Bnil) + ~ prefix (cd D b) (cd D minD))%type).
apply prefix_free_set.
auto.
elim pf.
intros isnil.
contradict nnil.
apply nil_ll.
rewrite <- lemma1.
rewrite -> isnil.
reflexivity.
intros npref.
contradict pref.
apply npref.
intros neq.
assert (lx : lex (cd E minE) (cd E b)).
apply minE2.
contradict neq.
symmetry.
apply neq.
assert (lx2 : lex (cd E b) (cd E minE)).
apply (lex_trans _ (cd D minD)).
apply prefix_lex.
apply pref.
apply lexDE.
contradict b_neq_minD.
rewrite -> minEq.
apply (dc_injective E).
apply nnil.
apply lex_antisym.
split.
apply lx2.
apply lx.

(* same again ... *)
intros lexED.
assert (S:exists b, (cd D b <> nil) /\ (prefix (cd D b) (cd E minE))).
apply (dense m D minD). auto. auto. auto.
elim S.
intros b QQ.
elim QQ.
intros nnil pref.
elim (eq_fin_dec b minE).
intros b_eq_minE.

assert (contr : cd D minD = cd E minE).
apply prefix_ll_eq.
split.
rewrite -> minEq.
rewrite -> b_eq_minE in pref.
apply pref.
apply leneq.
contradict minD1.
rewrite <- minEq in contr.
apply contr.
intros b_neq_minE.
elim (list_eq_dec bool_dec (cd E b) (cd D b)).
intros eq.
rewrite <- eq in pref.
assert (pf : ((cd E b = Bnil) + ~ prefix (cd E b) (cd E minE))%type).
apply prefix_free_set.
trivial.
elim pf.
intros isnil.
contradict nnil.
rewrite <- eq.
apply isnil.
intros npref.
contradict pref.
apply npref.

intros neq.
assert (lx : lex (cd D minD) (cd D b)).
apply minD2.
auto.

assert (lx2 : lex (cd D b) (cd D minD)).
apply (lex_trans _ (cd E minE)).
apply prefix_lex.
apply pref.
apply lexED.
contradict b_neq_minE.
rewrite <- minEq.
apply (dc_injective D).
apply nnil.
apply lex_antisym.
split.
apply lx2.
apply lx.

(* w00t ... now we're just a double negation away ... *)
assert (alleq : forall n, cd D n = cd E n).
intro n.
elim (list_eq_dec bool_dec (cd D n) (cd E n)).
auto.
intros neq.
contradict nex_diff.
exists n.
trivial.
apply eq_nth_iff.
intros p1 p2 eq.
rewrite -> eq.
apply alleq.
apply deflateCodingEq.
trivial.
Qed.

Lemma nullCoding : forall (n : nat), {d : deflateCoding n | forall q, cd d q = Bnil}.
intro n.
assert (H : {c : VecLB n | forall q, Vnth c q = Bnil}).
apply nullVec.
destruct H as [c c_ex].
assert(prefix_free : forall a b, a <> b -> ((Vnth c a) <> nil) -> ~ (prefix (Vnth c a) (Vnth c b))).
assert(prefix_free_set : forall a b, a <> b -> ((Vnth c a) = nil) + ~ (prefix (Vnth c a) (Vnth c b))).
intros a b neq.
apply inl.
apply c_ex.
apply prefix_free_set_inv.
trivial.
assert(length_lex : forall a b, (ll (Vnth c a) < ll (Vnth c b))%nat -> lex (Vnth c a) (Vnth c b)).
intros a b lllt.
contradict lllt.
rewrite -> c_ex.
rewrite -> c_ex.
apply lt_irrefl.
assert(char_enc : forall a b, ll (Vnth c a) = ll (Vnth c b) -> (f_le a b) -> lex (Vnth c a) (Vnth c b)).
intros a b _ _.
rewrite -> c_ex.
apply nil_lex.
assert(dense : forall a d, d <> nil -> lex d (Vnth c a) -> ll d = ll (Vnth c a)
                           -> exists b, (~ (Vnth c b) = nil) /\ (prefix (Vnth c b) d)).
intros a d H0 H1 H2.
contradict H0.
apply nil_ll.
rewrite -> c_ex in H2.
apply H2.
set (C' := mkDeflateCoding n c prefix_free length_lex char_enc dense).
exists C'.
auto.
Defined.

Local Open Scope Q.

Function kraft_d {n : nat} (D : deflateCoding n) : Q := kraft_vec (C n D).

Lemma list_of_nonnil_codes_is_dup_free :
  forall {m} D, dflist (list_of_nonnil_codes (C m D)).
Proof.
  intros m D.
  apply list_of_nonnil_codes_is_dup_free'.
  apply (prefix_free_set m D).
Defined.

Lemma list_of_nonnil_codes_is_prefix_free :
  forall {m} (D : deflateCoding m),
    pflist (list_of_nonnil_codes (C m D)).
Proof.
  intros m D.
  apply list_of_nonnil_codes_is_prefix_free'.
  apply (prefix_free_set m D).
Defined.

Lemma kraft_list_is_kraft_d :
  forall {m} D, kraft_list (list_of_nonnil_codes (C m D)) == kraft_d D.
Proof.
  intros m D.
  apply kraft_list_is_kraft_vec.
Defined.

Theorem kraft_ineq : forall {m} D, kraft_d (n:=m) D <= 1.
  intros m D.
  rewrite <- kraft_list_is_kraft_d.
  apply kraft_pflist.
  apply list_of_nonnil_codes_is_dup_free.
  apply list_of_nonnil_codes_is_prefix_free.
Defined.

Lemma extended_kraft_ineq_1 : forall n, ((S n) > n)%nat.
Proof.
  intros.
  omega.
Defined.

Theorem extended_kraft_ineq : forall {m} D, kraft_d (n:=m) D == 1 <-> exists d, cd D d <> [] /\ cd D d = repeat (ll (cd D d)) true.
Proof.
  intros m D.
  destruct D as [C0 pf' ll0 ce0 de0].
  assert (pf0 : forall a b : fin m,
                  a <> b -> (Vnth C0 a = Bnil) + ~ prefix (Vnth C0 a) (Vnth C0 b)).
  apply prefix_free_to_set.
  trivial.
  dependent induction m.
  split.
  unfold kraft_d.
  unfold C.
  dependent destruction C0.
  unfold kraft_vec.
  unfold kraft_nvec.  
  unfold Vmap.
  unfold fold.
  intros contr.
  inversion contr.
  unfold kraft_d.
  unfold C.
  intros nex.
  elim nex.
  intros x.
  inversion x.
  unfold kraft_d.
  unfold C.
  split.
  intros kraft_1.
  assert (nfa : ~ forall d, ~ (Vnth C0 d <> [] /\ (Vnth C0 d) = repeat (ll (Vnth C0 d)) true)).
  intros fall.
  assert (xmax : { n : fin (S m) | forall n', (ll (Vnth C0 n') <= ll (Vnth C0 n))%nat}).
  apply lenmax.
  elim xmax.
  intros max maxfall.
  set (c := Vcons (repeat (S (S (ll (Vnth C0 max)))) true) (S m) C0).
  assert (pfx : forall a b, a <> b -> ((Vnth c a) = nil) + ~ (prefix (Vnth c a) (Vnth c b))).
  intros a b neq.
  elim (list_eq_dec bool_dec (Vnth c a) nil).
  auto.
  intros ca_nnil.
  dependent destruction a.
  dependent destruction b.
  contradict neq.
  reflexivity.
  apply inr.
  assert (tmp1 : Vnth c FinF1 = repeat (S (S (ll (Vnth C0 max)))) true).
  reflexivity.
  rewrite -> tmp1.
  assert (tmp2 : Vnth c (FinFS b) = Vnth C0 b). 
  reflexivity.
  rewrite -> tmp2.
  intros contr.
  assert (contr2 : (ll (repeat (S (S (ll (Vnth C0 max)))) true) <= ll (Vnth C0 b))%nat).
  apply prefix_le.
  apply contr.
  rewrite -> rep_length in contr2.
  assert (contr3 : (S (S (ll (Vnth C0 max))) <= ll (Vnth C0 max))%nat).
  apply (le_trans _ (ll (Vnth C0 b))).
  apply contr2.
  apply maxfall.
  destruct (ll (Vnth C0 max)).
  inversion contr3.
  contradict contr3.
  apply lt_not_le.
  apply (lt_trans _ (S (S n))).
  apply extended_kraft_ineq_1.
  apply extended_kraft_ineq_1.

  dependent destruction b.
  apply inr.
  assert (tmp1 : Vnth c FinF1 = repeat (S (S (ll (Vnth C0 max)))) true).
  reflexivity.
  rewrite -> tmp1.
  assert (tmp2 : Vnth c (FinFS a) = Vnth C0 a).
  reflexivity.
  rewrite -> tmp2.
  intro pref.
  assert(contr:Vnth C0 a=repeat (ll (Vnth C0 a)) true).
  apply (prefix_repeat _ _ (S (S (ll (Vnth C0 max))))).
  apply pref.
  assert (contr2 : Vnth C0 a <> Bnil /\ Vnth C0 a = repeat (ll (Vnth C0 a)) true).
  split.
  auto.
  auto.
  contradict contr2.
  apply fall.
  apply pf0.
  contradict neq.
  f_equal.
  apply neq.

  assert (k' : kraft_vec c <= 1).
  rewrite <- kraft_list_is_kraft_vec.
  apply kraft_pflist.
  apply dflist_cons.
  apply list_of_nonnil_codes_is_dup_free'.
  intros a b a_neq_b.
  apply (pfx (FinFS a) (FinFS b)).
  contradict a_neq_b.
  apply FS_inj.
  apply a_neq_b.
  intros isin.
  assert(xna : {na | Vnth C0 na = (repeat (S (S (ll (Vnth C0 max)))) true)}).
  apply list_of_nonnil_codes_contains_everything.
  apply isin.
  elim xna.
  intros x.
  intros e.
  assert (plonq : ll (Vnth C0 x) = (S (S (ll (Vnth C0 max))))).
  rewrite -> e.
  apply rep_length.
  rewrite <- plonq in e.
  assert (e2 : Vnth C0 x <> Bnil).
  apply nnil_ll.
  intros is0.
  rewrite -> is0 in plonq.
  inversion plonq.
  assert (contr : Vnth C0 x <> Bnil /\ Vnth C0 x = repeat (ll (Vnth C0 x)) true).
  auto.
  contradict contr.
  apply fall.
  apply list_of_nonnil_codes_is_prefix_free'.
  auto.
  assert (tmp1:kraft_vec c=(1 # (e2 (ll (repeat (S (S (ll (Vnth C0 max)))) true))))+kraft_vec C0).
  reflexivity.
  rewrite -> tmp1 in k'.
  contradict k'.
  apply Qlt_not_le.
  assert (tmp2 : 1 == 0 + 1).
  ring.
  rewrite -> tmp2.
  apply Qplus_lt_le_compat.
  induction (ll (repeat (S (S (ll (Vnth C0 max)))) true)).
  compute.
  reflexivity.
  compute.
  reflexivity.
  apply Qle_lteq.
  apply or_intror.
  rewrite -> kraft_1.
  reflexivity.
  assert (xd : {d | Vnth C0 d <> Bnil /\ Vnth C0 d = repeat (ll (Vnth C0 d)) true}).
  apply fin_nforall_ex.
  intros a.
  elim (list_eq_dec bool_dec (Vnth C0 a) Bnil).
  intros isnil.
  apply right.
  intros Q.
  elim Q.
  intros Q' Q''.
  contradict Q'.
  auto.
  intros nnil.
  elim (list_eq_dec bool_dec (Vnth C0 a) (repeat (ll (Vnth C0 a)) true)).
  intros eql.
  apply left.
  auto.
  intros neq.
  apply right.
  intros Q.
  elim Q.
  intros Q' Q''.
  contradict neq.
  auto.
  auto.
  elim xd.
  intros x x_e.
  exists x.
  apply x_e.

  intros exd.
  elim exd.
  intros d d_x.
  elim d_x.
  intros d_x_1 d_x_2.
  rewrite <- kraft_list_is_kraft_vec.
  apply kraft_pflist_sharp.
  apply list_of_nonnil_codes_is_dup_free'.
  apply pf0.
  apply list_of_nonnil_codes_is_prefix_free'.
  apply pf0.
  intros m0 df pf.
  destruct m0.
  assert (H : prefix Bnil (Vnth C0 d)).
  exists (Vnth C0 d).
  apply app_nil_l.
  contradict H.
  apply pf.
  apply in_eq.
  apply in_cons.
  apply (list_of_nonnil_codes_contains_everything' _ _ d).
  reflexivity.
  apply d_x_1.
  auto.
  elim (lex_total (b :: m0) (Vnth C0 d)).
  intros lbd.
  elim (lexcut (b :: m0) (Vnth C0 d) lbd).
  intros xx. 
  elim xx.
  intros x xxx.
  elim xxx.
  intros xxxx xxxxx.
  assert (xbl : exists bl, (~ (Vnth C0 bl) = nil) /\ (prefix (Vnth C0 bl) ((b :: m0) ++ x))).
  apply (de0 d).
  intros Q.
  inversion Q.
  auto.
  auto.
  elim xbl.
  intros x0 x0_ex.
  elim x0_ex.
  intros x0_ex_1 x0_ex_2.
  elim (list_eq_dec bool_dec (Vnth C0 x0) (b :: m0)).
  intros eql.
  inversion df.
  contradict H2.
  rewrite <- eql.
  apply (list_of_nonnil_codes_contains_everything' _ _ x0).
  reflexivity.
  auto.

  intros x0neq.
  elim (prefix_dec (Vnth C0 x0) (b :: m0)).
  intros prbm.
  contradict prbm.
  apply pf.
  apply in_cons.
  apply (list_of_nonnil_codes_contains_everything' _ _ x0).
  reflexivity.
  auto.
  apply in_eq.
  auto.
  intros npref.
  assert (pref : prefix (b :: m0) (Vnth C0 x0)).
  apply (prefix_ext _ _ x).
  auto.
  auto.
  contradict pref.
  apply pf.
  apply in_eq.
  apply in_cons.
  apply (list_of_nonnil_codes_contains_everything' _ _ x0).
  reflexivity.
  auto.
  auto.


  intros xx.
  elim xx.
  intros x xxx.
  elim xxx.
  intros xxxx xxxxx.
  elim xxxxx.
  intros xxxxxx xxxxxxx.

  assert (xbl : exists bl, (~ (Vnth C0 bl) = nil) /\ (prefix (Vnth C0 bl) x)).
  apply (de0 d).
  apply nnil_ll.
  rewrite -> xxxx.
  contradict d_x_1.
  apply nil_ll.
  apply d_x_1.
  auto.
  auto.
  elim xbl.
  intros bl blx.
  elim blx.
  intros blx1 blx2.
  assert (blx3 : prefix (Vnth C0 bl) (b :: m0)).
  apply (prefix_trans _ x).
  auto.
  auto.
  contradict blx3.
  apply pf.
  apply in_cons.
  apply (list_of_nonnil_codes_contains_everything' _ _ bl).
  reflexivity.
  auto.
  apply in_eq.
  intros eq.
  inversion df.
  contradict H2.
  rewrite <- eq.
  apply (list_of_nonnil_codes_contains_everything' _ _ bl).
  reflexivity.
  auto.

  intros ldm.
  assert (pref : prefix (Vnth C0 d) (b :: m0)).
  unfold cd in d_x_2.
  unfold C in d_x_2.
  rewrite -> d_x_2.
  apply lex_1_prefix.
  rewrite <- d_x_2.
  apply ldm.
  contradict pref.
  apply pf.
  apply in_cons.
  apply (list_of_nonnil_codes_contains_everything' _ _ d).
  reflexivity.
  auto.
  apply in_eq.
  inversion df.
  contradict H2.
  rewrite <- H2.
  apply (list_of_nonnil_codes_contains_everything' _ _ d).
  reflexivity.
  auto.
Qed.

Inductive mys {n} : (fin n * nat) -> (fin n * nat) -> Prop :=
| f_lt : forall m q o, ((proj1_sig (Fin.to_nat q)) < (proj1_sig (Fin.to_nat (m:=n) o)))%nat -> mys (q, m) (o, m)
| s_lt : forall m1 m2 n1 n2, (m1 < m2)%nat -> mys (n1, m1) (n2, m2).

Lemma mys_trans : forall {n} (a b c : fin n * nat),
                    mys a b -> mys b c -> mys a c.
intros n a b c. 
elim a.
intros a1 a2.
elim b.
intros b1 b2.
elim c.
intros c1 c2.
intros ms1 ms2.
inversion ms1.
inversion ms2.
apply f_lt.
apply (lt_trans _ (` (f_nat b1))).
auto.
auto.
apply s_lt.
apply H5.
inversion ms2.
rewrite <- H8.
apply s_lt.
apply H0.
apply s_lt.
apply (lt_trans _ b2).
apply H0.
apply H5.
Defined.

Definition mys_decidable {n} : forall (a b : fin n * nat), (mys a b) + (~ mys a b).
intros a b.
elim a.
intros a0 b0.
elim b.
intros a1 b1.
elim (lt_dec (proj1_sig (Fin.to_nat a0)) (proj1_sig (Fin.to_nat a1))).
intros a0_lt_a1.
  elim (eq_nat_dec b0 b1).
   intros b0_eq_b1.
    apply inl.
    rewrite -> b0_eq_b1.
    apply f_lt.
    trivial.
  intros b0_neq_b1.
    elim (lt_dec b0 b1).
    intros b0_lt_b1.
      apply inl.
      apply s_lt.
      trivial.
    intros b0_nlt_b1.
      apply inr.
      intros Q.
      inversion Q.
      contradict b0_neq_b1.
      trivial.
      contradict b0_nlt_b1.
      trivial.
  intros a0_nlt_a1.
    elim (lt_dec b0 b1).
    intros b0_lt_b1.
      apply inl.
      apply s_lt.
      trivial.
    intros b0_nlt_b1.
      apply inr.
      intros Q.
      inversion Q.
      contradict a0_nlt_a1.
      trivial.
      contradict b0_nlt_b1.
      trivial.
Defined.

Fixpoint dec_mys {n} (a b : fin n * nat) : bool :=
  match (mys_decidable a b) with
      | inl _ => true
      | inr _ => false
  end.

Lemma mys_total : forall {n} (a b : fin n * nat), (a = b) + (mys a b) + (mys b a).
Proof.
  intros n a b.
  elim a.
  intros a0 a1.
  elim b.
  intros b0 b1.
  elim (lt_eq_lt_dec a1 b1).
  intros quak.
  elim quak.
  intros a1_lt_b1.
  apply inl.
  apply inr.
  apply s_lt.
  apply a1_lt_b1.
  intros a1_eq_b1.
  elim (eq_fin_dec a0 b0).
  intros a0_eq_b0.
  apply inl.
  apply inl.
  rewrite -> a0_eq_b0.
  rewrite -> a1_eq_b1.
  reflexivity.
  intros a0_neq_b0.
  elim (lt_eq_lt_dec (` (Fin.to_nat a0)) (` (Fin.to_nat b0))).
  intros quak2.
  elim quak2.
  intros a0_lt_b0.
  apply inl.
  apply inr.
  rewrite -> a1_eq_b1.
  apply f_lt.
  apply a0_lt_b0.
  intros eq.
  contradict a0_neq_b0.
  apply to_nat_inj.
  apply eq.
  intros b0_lt_a0.
  apply inr.
  rewrite -> a1_eq_b1.
  apply f_lt.
  apply b0_lt_a0.

  intros b1_lt_a1.
  apply inr.
  apply s_lt.
  apply b1_lt_a1.
Defined.

Lemma sorting_rmdup : forall n L, Sorted (fun x y => ((x = y) \/ (mys (n:=n) x y))%type) L ->
                                  Sorted mys (rmdup L).
Proof.
  intros n L.
  induction L.
  intros _.
  apply Sorted_nil.
  intros mss.

  destruct L.
  apply Sorted_cons.
  apply Sorted_nil.
  apply HdRel_nil.

  induction (pair_dec _ a p) eqn:pd.
  assert (tmp1 : rmdup (a :: p :: L) = rmdup (p :: L)).
  apply (rmdup_lemma_1 _ _ _ pd).
  rewrite -> tmp1.
  apply IHL.
  inversion mss.
  auto.
  assert (tmp1 : rmdup (a :: p :: L) = a :: rmdup (p :: L)).
  apply (rmdup_lemma_2 _ _ _ pd).
  rewrite -> tmp1.
  inversion mss.
  apply Sorted_cons.
  apply IHL.
  auto.
  inversion H2.
  elim H4.
  intros a_eq_p.
  contradict pd.
  auto.
  intros mys_ap.
  elim (rmdup_lemma_3 p L).
  intros K keq.
  rewrite -> keq.
  apply HdRel_cons.
  apply mys_ap.
Defined.

Theorem sorting : forall {n} (L : list (fin n * nat)),
                    {L' | StronglySorted mys L' /\ forall x, In x L <-> In x L'}.
  Proof.
    intros n L.
    assert (xL : {L' | (forall x, In x L <-> In x L') /\ Sorted (fun x y => ((x = y) \/ (mys x y))%type) L'}).
    apply Quicksort.quicksort.
    intros a b.

    elim (mys_total a b).
    intros eq_mysab.
    elim eq_mysab.
    intros a_eq_b.
    apply left.
    apply or_introl.
    apply a_eq_b.
    intros mysab.
    apply left.
    apply or_intror.
    apply mysab.
    intros mysba.
    apply right.
    apply or_intror.
    apply mysba.

    elim xL.
    intros L' L'x.
    elim L'x.
    intros sL' rL'.
    exists (rmdup L').
    split.
    apply Sorted_StronglySorted.
    intros x y z xy yz.
    apply (mys_trans _ y).
    apply xy.
    apply yz.
    apply sorting_rmdup.
    apply rL'.
    intros x.
    split.
    intros inxL.
    apply (rmdup_eq _ L' x).
    apply sL'.
    apply inxL.
    intros inrmdup.
    apply sL'.
    apply rmdup_eq.
    apply inrmdup.
Defined.

Lemma existence_sorting_S : forall {A} a (b : A) c f,
                              StronglySorted f ((rev (b :: a)) ++ c) -> StronglySorted (fun x y => f y x) (b :: a).
Proof.
intros A a b c f H.
assert (r : StronglySorted f (rev (b :: a)) /\ StronglySorted f c).
apply sorting_app.
apply H.
elim r.
intros r1 _.
replace (b :: a) with (rev (rev (b :: a))).
apply sorting_rev.
apply r1.
apply rev_involutive.
Defined.

Lemma existence_disjunction_lemma : forall A B, A \/ B -> ~ A -> B.
Proof.
  intros A B vel notA.
  elim vel.
  intros a.
  contradict a.
  apply notA.
  auto.
Defined.

Lemma existence_sorting_In : forall {A} a b c (f : A -> A -> Prop), StronglySorted f (a :: b) -> In c b -> f a c.
Proof.
  intros A a. 
  induction b.
  intros c f sortd inn.
  inversion inn.
  intros c f sss.
  inversion sss.
  inversion H1.
  apply Forall_forall.
  auto.
Defined.

Lemma existence_sorting_In_split : forall {A} a b c d (f : A -> A ->
Prop), StronglySorted f (a ++ b) -> In c a -> In d b -> f c d.
Proof.
  intros A a b c d f H ca cb.
  induction a.
  inversion ca.
  assert (H' : StronglySorted f (a :: (a0 ++ b))).
  auto.
  inversion H'.
  elim ca.
  intros a_eq_c.
  rewrite <- a_eq_c.
  assert (H4 : Forall (f a) b).
  apply (proj2 (forall_app a0 b (f a) H3)).
  apply (forall_In b).
  apply H4.
  apply cb.
  intros in_c_a0.
  apply IHa.
  auto.
  auto.
Defined.

(* LXL1 *)
Lemma existence_lex_lemma : forall a m p, lex p m -> prefix a m ->
                                     ~ prefix a p -> lex p a.
Proof.
  refine (fix f a m p :=
            match (a, m, p) as R return ((a, m, p) = R -> _) with
              | (nil, _, _) => fun eq => _
              | (xa :: a', nil, _) => fun eq => _
              | (xa :: a', xm :: m', nil) => fun eq => _
              | (xa :: a', xm :: m', xp :: p') => fun eq => _
            end eq_refl).
(* LXL2 *)
inversion eq.
intros _ _ npref.
contradict npref.
eexists.
apply app_nil_l.
inversion eq.
intros _ npref.
inversion npref.
inversion H.
inversion eq.
intros.
apply nil_lex.
inversion eq.
intros lpm pam npap.
induction xa.
induction xm.
induction xp.
apply cdr_lex.
apply (f _ m').
apply (lex_cdr _ _ true).
apply lpm.
elim pam.
intros x H.
exists x.
inversion H.
reflexivity.
contradict npap.
apply prefix_cons.
apply npap.
apply car_lex.
induction xp.
inversion lpm.
apply car_lex.
induction xm.
induction xp.
inversion pam.
inversion H.
inversion pam.
inversion H.
induction xp.
inversion lpm.
apply cdr_lex.
apply (f _ m').
apply (lex_cdr _ _ false).
apply lpm.
inversion pam.
inversion H.
exists x.
reflexivity.
contradict npap.
inversion npap.
exists x.
replace ((false :: a') ++ x) with (false :: (a' ++ x)).
rewrite -> H.
reflexivity.
reflexivity.
Defined.


Lemma existence : forall n (f : vec nat n),
                    kraft_nvec f <= 1 ->
                    { D : deflateCoding n | f = (Vmap lb (C n D))}.
intros n f kraft.
assert (assc : { L | forall m o, In (m, o) L <-> Vnth f m = o }).
apply assoc_lemma.
elim assc.
intros L' L'_asc.
elim (sorting L').
intros L Lwedge.
elim Lwedge.
intros Lsorted LinL'.
assert (Lasc : forall m o, In (m, o) L <-> Vnth f m = o).
intros m o.
split.
intros imol.
apply L'_asc.
apply LinL'.
apply imol.
intros vfmo.
apply LinL'.
apply L'_asc.
apply vfmo.

destruct (nullCoding n) as [mdn allnil].

refine ((fix complicated (R0 S0 L0 : list (fin n * nat))
             x (xeq : x = f) (* TODO: Hack *)
             (Lasc0 : forall m o, In (m, o) L0 <-> Vnth x m = o)
             (sL : StronglySorted mys L0)
             (sR : StronglySorted mys R0)
             (sS : StronglySorted (fun x y => mys y x) S0)
             (c : deflateCoding n)
             (inv1 : forall q,
                       (~ In (q, ll (cd c q)) S0) ->
                       (cd c q = []) /\ In (q, Vnth x q) R0)
             (inv2 : L0 = (List.rev S0) ++ R0)
             (inv3 : (S0 = nil) + (forall q, lex (cd c q) (cd c (fst (car (q, 0%nat) S0)))))
         := 
           match R0 as R' return (R0 = R' -> _) with
             | nil => fun eq => _
             | (n0, 0%nat) :: R' => fun eq => _
             | (n0, S m) :: R' => fun eq =>
                                   match S0 as S' return (S0 = S' -> _) with
                                       | nil => fun eq2 => _
                                       | (p1, 0%nat) :: S'' => fun eq2 => _
                                       | (p1, S ms) :: S'' => fun eq2 => _
                                   end eq_refl
           end eq_refl) L [] L f eq_refl Lasc Lsorted Lsorted _ mdn _ _ _).

(* R = nil *)

exists c.
apply eq_nth_iff.
intros p1 p2 peq.
rewrite -> peq.

assert (fdec : forall x1 y : fin n * nat, {x1 = y} + {x1 <> y}).
intros x0 y.
elim x0.
elim y.
intros a b a0 b0.
elim (eq_fin_dec a a0).
intros a_eq_a0.
elim (eq_nat_dec b b0).
intros b_eq_b0.
rewrite -> a_eq_a0.
rewrite -> b_eq_b0.
auto.
intros b_neq_b0.
apply right.
intros Q.
inversion Q.
contradict b_neq_b0.
symmetry.
trivial.
intros a_neq_a0.
apply right.
intros Q.
inversion Q.
contradict a_neq_a0.
symmetry.
trivial.

apply Lasc0.
rewrite -> inv2.
rewrite -> eq.
rewrite app_nil_r.
apply in_rev.
rewrite rev_involutive.
assert (dc:{In(p2,(Vnth(Vmap lb (C _ c))p2))S0}+{~In(p2,(Vnth(Vmap lb (C _ c))p2))S0}).
apply in_dec.
apply fdec.
elim dc.
trivial.
intros Q.
assert (In (p2, Vnth x p2) R0).
apply inv1.
assert (H:Vnth (Vmap lb (C _ c)) p2 = ll (Vnth (C _ c) p2)).
apply nth_map. reflexivity.
unfold cd.
rewrite <- H.
apply Q.
contradict H.
rewrite -> eq.
intros Q2.
inversion Q2.

(* R = (n, 0%nat) :: R' *)
assert (exD' : {D' | x = Vmap lb (C n D')}).
assert (sR' : StronglySorted mys R').
inversion sR.
contradict eq.
rewrite <- H.
intros Q.
inversion Q.
assert (R'l : R' = l).
eapply cons_inj.
rewrite -> eq in H1.
symmetry.
apply H1.

rewrite -> R'l.
auto.
assert (inv2' : L0 = (rev ((n0, 0%nat)::S0)) ++ R').
rewrite -> inv2.
rewrite -> eq.
symmetry.
apply cons_rev.
assert(inv1':forall q : fin n,
               ~ In (q, ll (cd c q)) ((n0, 0%nat) :: S0) ->
               cd c q = Bnil /\ In (q, Vnth x q) R').
intros q nin.
assert (old : cd c q = Bnil /\ In (q, Vnth x q) R0).
apply inv1.
contradict nin.
apply in_cons.
apply nin.
split.
apply old.
elim old.
intros old1 old2.
assert (old3 : In (q, Vnth x q) ((n0, 0%nat) :: R')).
rewrite <- eq.
auto.
inversion old3.
contradict nin.
rewrite -> old1.
unfold ll.
inversion H.
apply in_eq.
apply H.
assert (sS' : StronglySorted (fun x y => mys y x) ((n0, 0%nat) :: S0)).
apply (existence_sorting_S _ (n0,0%nat) R').
rewrite <- inv2'.
apply sL.
assert (inv3' : (((n0, 0%nat) :: S0 = []) +
                 (forall q : fin n,
                    lex (cd c q)
                        (cd c (fst (car (q, 0%nat) ((n0, 0%nat) :: S0))))))).
apply inr.
intro q.
assert (allnull : forall q : fin n, cd c q = Bnil).
intros q0.
assert (indec : {In (q0, ll (cd c q0)) S0} + {~ In (q0, ll (cd c q0)) S0}).
apply in_dec.
apply pair_dec.
elim indec.
intros inS.
assert (mys (q0, ll (cd c q0)) (n0, 0%nat)).
apply (existence_sorting_In _ S0 _ (fun x y => mys y x)).
apply sS'.
apply inS.
inversion H.
apply nil_ll.
apply H4.
inversion H1.
intros ninS.
apply inv1.
apply ninS.
rewrite -> allnull.
apply nil_lex.
apply (complicated R' ((n0, 0%nat)::S0) L0 x xeq Lasc0 sL sR' sS' c inv1' inv2' inv3').
apply exD'.

(* R = (n, Datatypes.S m) :: R', S = [ ] -- nasty side case *)

(* TODO: with similar lemmata from the next case, this proof should become much shorter *)

assert (ex_c' : {c' | forall q, ((q = n0) -> Vnth c' q = repeat (Datatypes.S m) false) /\ ((q <> n0) -> Vnth c' q =
                                                                                                        cd c q)}).
apply array_set.
elim ex_c'.
intros c' c'x.
assert (c_prefix_free : forall a b, a <> b -> ((Vnth c' a) = nil) + ~ (prefix (Vnth c' a) (Vnth c' b))).
intros a b aneqb.
elim (eq_fin_dec a n0).
intros a_eq_n.
rewrite -> a_eq_n.
apply inr.
replace (Vnth c' b) with Bnil.
replace (Vnth c' n0) with (repeat (Datatypes.S m) false).
apply prefix_nnil.
symmetry.
apply c'x.
reflexivity.
replace (Vnth c' b) with (cd c b).
symmetry.
apply inv1.
rewrite -> eq2.
auto.
symmetry.
apply c'x.
rewrite <- a_eq_n.
contradict aneqb.
symmetry. auto.
intros a_neq_n.
apply inl.
replace (Vnth c' a) with (cd c a).
apply inv1.
rewrite -> eq2.
auto. symmetry.
apply c'x.
auto.
assert (c_length_lex : forall a b, (ll (Vnth c' a) < ll (Vnth c' b))%nat -> lex (Vnth c' a) (Vnth c' b)).
intros a b lllt.
elim (eq_fin_dec b n0).
intros b_eq_n.
rewrite -> b_eq_n.
elim (eq_fin_dec a n0).
intros a_eq_n.
rewrite -> a_eq_n.
apply lex_refl.
intros a_neq_n.
replace (Vnth c' a) with Bnil.
apply nil_lex.
replace (Vnth c' a) with (cd c a).
symmetry.
apply inv1.
rewrite -> eq2.
auto.
symmetry.
apply c'x.
auto.
intros b_neq_n.
elim (eq_fin_dec a n0).
intros a_eq_n.
contradict lllt.
replace (Vnth c' b) with Bnil.
replace (Vnth c' a) with (repeat (Datatypes.S m) false).
replace (ll (repeat (Datatypes.S m) false)) with (Datatypes.S m).
compute. intros Q. inversion Q.
symmetry.
apply rep_length.
symmetry.
apply c'x.
auto.
replace (Vnth c' b) with (cd c b).
symmetry.
apply inv1.
rewrite -> eq2.
auto.
symmetry.
apply c'x.
auto.
intros a_neq_n.
replace (Vnth c' a) with Bnil.
apply nil_lex.
replace (Vnth c' a) with (cd c a).
symmetry.
apply inv1.
rewrite -> eq2.
auto.
symmetry.
apply c'x.
auto.
assert (c_char_enc : forall a b, ll (Vnth c' a) = ll (Vnth c' b) -> (f_le a b) -> lex (Vnth c' a) (Vnth c' b)).
intros a b lleq fle.
elim (eq_fin_dec a n0).
intros a_eq_n.
assert (b_eq_n : b = n0).
elim (eq_fin_dec b n0).
auto.
intros b_neq_n.
apply (dc_injective c).
apply nnil_ll.
replace (cd c b) with (Vnth c' b).
contradict lleq.
rewrite -> lleq.
replace (Vnth c' a) with (repeat (Datatypes.S m) false).
rewrite -> rep_length.
intros Q. inversion Q.
symmetry.
apply c'x.
auto.
apply c'x.
auto.
replace (cd c n0) with Bnil.
replace (cd c b) with Bnil.
reflexivity.
symmetry.
apply inv1.
rewrite -> eq2.
auto.
symmetry.
apply inv1.
rewrite -> eq2.
auto.
rewrite -> a_eq_n.
rewrite -> b_eq_n.
apply lex_refl.
intros a_neq_n.
assert (vcanil : Vnth c' a = Bnil).
replace (Vnth c' a) with (cd c a).
apply inv1.
rewrite -> eq2.
auto.
symmetry.
apply c'x.
auto.
rewrite -> vcanil.
apply nil_lex.
assert (c_dense : forall a d, d <> nil -> lex d (Vnth c' a) -> ll d = ll (Vnth c' a)
                          -> exists b, (~ (Vnth c' b) = nil) /\ (prefix (Vnth c' b) d)).
intros a d nnil lxdca lld_eq_llca.
elim (eq_fin_dec a n0).
intros a_eq_n.
exists n0.
split.
replace (Vnth c' n0) with (repeat (Datatypes.S m) false).
apply nnil_ll.
rewrite -> rep_length.
intros Q.
inversion Q.
symmetry.
apply c'x.
auto.
assert (deq : d = Vnth c' n0).
apply prefix_ll_eq.
split.
assert (vcneq : Vnth c' n0 = repeat (Datatypes.S m) false).
apply c'x.
reflexivity.
rewrite -> vcneq.
apply lex_0_is_prefix.
rewrite <- vcneq.
rewrite <- a_eq_n.
apply lxdca.
rewrite <- a_eq_n.
apply lld_eq_llca.
rewrite <- deq.
exists Bnil.
apply app_nil_r.

intros a_neq_n.
assert (dnil : d = Bnil).
apply lex_nil_is_nil.
replace Bnil with (Vnth c' a).
auto.
replace (Vnth c' a) with (cd c a).
apply inv1.
rewrite -> eq2.
auto.
symmetry.
apply c'x.
auto.
contradict nnil.
auto.
assert (sR' : StronglySorted mys R').
inversion sR.
contradict eq.
rewrite <- H.
intros Q.
inversion Q.
assert (R'l : R' = l).
apply (cons_inj(c:=a)(a:=(n0,Datatypes.S m))).
rewrite -> H1.
auto.
rewrite -> R'l.
auto.
assert (inv2' : L0 = (rev ((n0,Datatypes.S m)::S0)) ++ R').
rewrite -> inv2.
rewrite -> eq.
symmetry.
apply cons_rev.
set (C' := mkDeflateCoding
             n c' (prefix_free_set_inv _ c_prefix_free) c_length_lex c_char_enc c_dense).
assert(inv1':forall q : fin n,
               ~ In (q, ll (cd C' q)) ((n0,Datatypes.S m) :: S0) ->
               cd C' q = Bnil /\ In (q, Vnth x q) R').
rewrite -> eq2.
intros q nin.
split.
replace (C n C') with c'.
assert (eql : Vnth c' q = cd c q).
apply c'x.
contradict nin.
rewrite -> nin.
assert (eql2 : cd C' n0 = repeat (Datatypes.S m) false).
replace (C n C') with c'.
apply c'x.
reflexivity.
auto.
rewrite -> eql2.
rewrite -> rep_length.
apply in_eq.
assert (h : cd c q = Bnil).
apply inv1.
rewrite -> eq2.
intros Q. inversion Q.
rewrite <- h.
apply eql.
auto.
assert (in_r : In (q, Vnth x q) ((n0, Datatypes.S m)::R')).
rewrite <- eq.
apply inv1.
rewrite -> eq2.
auto.
elim in_r.
intros nemesis.
inversion nemesis.
contradict nin.
replace (cd C' q) with (repeat (Datatypes.S m) false).
rewrite -> rep_length.
rewrite -> H0.
apply in_eq.
symmetry.
replace (C n C') with c'.
apply c'x.
symmetry.
auto.
auto.
auto.
assert (sS' : StronglySorted (fun x y : fin n * nat => mys y x)
                             ((n0, Datatypes.S m) :: S0)).
rewrite -> eq2.
apply SSorted_cons.
apply SSorted_nil.
auto.
assert (inv3' : (((n0, Datatypes.S m) :: S0 = [ ]) +
                 (forall q : fin n,
                    lex (cd C' q)
                        (cd C'
                              (fst (car (q, 0%nat) ((n0, Datatypes.S m) :: S0))))))%type).
apply inr.
intros q.
unfold car.
unfold fst.
assert (qq : cd C' n0 = repeat (Datatypes.S m) false).
apply c'x.
reflexivity.
rewrite -> qq.
elim (eq_fin_dec q n0).
intros q_eq_n.
rewrite -> q_eq_n.
rewrite -> qq.
apply lex_refl.
intros q_neq_n.
replace (cd C' q) with Bnil.
apply nil_lex.
symmetry.
replace (cd C' q) with (cd c q).
apply inv1.
rewrite -> eq2.
intros Q.
inversion Q.
symmetry.
apply c'x.
apply q_neq_n.
apply (complicated R' ((n0, Datatypes.S m) :: S0) L0 x xeq Lasc0 sL sR' sS' C' inv1' inv2' inv3').

(* S = (p, 0%nat) :: S'' - should be pretty similar *)

assert (inv2' : L0 = (rev ((n0, Datatypes.S m) :: S0)) ++ R').
symmetry.
rewrite -> inv2.
rewrite -> eq.
apply cons_rev.

assert (sS' : StronglySorted (fun x y => mys y x) ((n0, Datatypes.S m) :: S0)).
apply (existence_sorting_S _ _ R').
rewrite <- inv2'.
auto.

assert (lemma1 : forall p q, In (p, q) S'' -> q = 0%nat).
intros p2 q inp2q.
assert (H:(fun x y => mys y x) (p1, 0%nat) (p2, q)).
apply (existence_sorting_In (p1, 0%nat)  S'' (p2, q)).
rewrite <- eq2.
apply sS.
auto.
inversion H.
reflexivity.
inversion H1.

assert (ex_c' : {c' | forall q, ((q = n0) -> Vnth c' q = repeat (Datatypes.S m) false) /\ ((q <> n0) -> Vnth c' q =
                                                                                                      cd c q)}).
apply array_set.
elim ex_c'.
intros c' c'x.

assert (lemma2 : forall a, a <> n0 -> Vnth c' a = Bnil).
intros a a_neq_n.
elim (list_eq_dec bool_dec (Vnth c' a) Bnil).
auto.
intros nnil.
assert (inq:{In (a, ll (Vnth c' a)) S''}+{~ In (a,ll (Vnth c' a)) S''}).
apply in_dec.
apply pair_dec.
elim inq.
intros isin.
apply nil_ll.
apply (lemma1 a).
apply isin.
intros nin.
assert (vcaisvcma : Vnth c' a = cd c a).
apply c'x.
apply a_neq_n.
rewrite -> vcaisvcma.
apply inv1.
rewrite -> eq2.
contradict nin.
elim nin.
intros wrongity.
inversion wrongity.
contradict H1.
contradict nnil.
apply nil_ll.
rewrite -> vcaisvcma.
auto.
rewrite -> vcaisvcma.
auto.

assert(lemma3 : Vnth c' n0 = repeat (Datatypes.S m) false).
apply c'x.
reflexivity.

assert (c_prefix_free : forall a b, a <> b -> ((Vnth c' a) = nil) + ~ (prefix (Vnth c' a) (Vnth c' b))).
intros a b aneqb.
elim (eq_fin_dec a n0).
intros a_eq_n.
rewrite -> a_eq_n.
apply inr.
rewrite -> (lemma2 b).
rewrite -> lemma3.
apply prefix_nnil.
rewrite <- a_eq_n.
auto.
intros a_neq_n.
apply inl.
apply lemma2.
auto.

assert (c_length_lex : forall a b, (ll (Vnth c' a) < ll (Vnth c' b))%nat -> lex (Vnth c' a) (Vnth c' b)).
intros a b lllt.
elim (eq_fin_dec b n0).
intros b_eq_n.
rewrite -> b_eq_n.
elim (eq_fin_dec a n0).
intros a_eq_n.
rewrite -> a_eq_n.
apply lex_refl.
intros a_neq_n.
rewrite -> (lemma2 a a_neq_n).
apply nil_lex.
intros b_neq_n.
elim (eq_fin_dec a n0).
intros a_eq_n.
contradict lllt.
rewrite -> (lemma2 b b_neq_n).
rewrite -> a_eq_n.
rewrite -> lemma3.
rewrite -> rep_length.
intros Q.
inversion Q.
intros a_neq_n.
rewrite -> (lemma2 a a_neq_n).
apply nil_lex.

assert (c_char_enc : forall a b, ll (Vnth c' a) = ll (Vnth c' b) -> (f_le a b) -> lex (Vnth c' a) (Vnth c' b)).
intros a b lleq fle.
elim (eq_fin_dec a n0).
intros a_eq_n.
assert (b_eq_n : b = n0).
elim (eq_fin_dec b n0).
auto.
intros b_neq_n.
contradict lleq.
rewrite -> a_eq_n.
rewrite -> lemma3.
rewrite -> (lemma2 b b_neq_n).
compute.
intros Q.
inversion Q.
rewrite -> a_eq_n.
rewrite -> b_eq_n.
apply lex_refl.

intros a_neq_n.
rewrite -> (lemma2 a a_neq_n).
apply nil_lex.

assert (c_dense : forall a d, d <> nil -> lex d (Vnth c' a) -> ll d = ll (Vnth c' a)
                          -> exists b, (~ (Vnth c' b) = nil) /\ (prefix (Vnth c' b) d)).
intros a d nnil lxdca lld_eq_llca.
elim (eq_fin_dec a n0).
intros a_eq_n.
exists n0.
split.
rewrite -> lemma3.
compute.
intros Q.
inversion Q.
assert (deq : d = Vnth c' n0).
apply prefix_ll_eq.
split.
rewrite -> lemma3.
apply lex_0_is_prefix.
rewrite <- lemma3.
rewrite <- a_eq_n.
apply lxdca.
rewrite <- a_eq_n.
apply lld_eq_llca.
rewrite <- deq.
exists Bnil.
apply app_nil_r.

intros a_neq_n.
assert (dnil : d = Bnil).
apply lex_nil_is_nil.
rewrite <- (lemma2 a).
auto.
auto.
contradict nnil.
auto.
assert (sR' : StronglySorted mys R').
inversion sR.
contradict eq.
rewrite <- H.
intros Q.
inversion Q.
assert (R'l : R' = l).
apply (cons_inj(c:=a)(a:=(n0,Datatypes.S m))).
rewrite -> H1.
auto.
rewrite -> R'l.
auto.

set (C' := mkDeflateCoding
             n c' (prefix_free_set_inv _ c_prefix_free) c_length_lex c_char_enc c_dense).
assert(inv1':forall q : fin n,
               ~ In (q, ll (cd C' q)) ((n0,Datatypes.S m) :: S0) ->
               cd C' q = Bnil /\ In (q, Vnth x q) R').

rewrite -> eq2.
intros q nin.
split.
replace (C n C') with c'.
unfold cd.
rewrite -> lemma2.
reflexivity.
contradict nin.
rewrite -> nin.
assert (eql2 : cd C' n0 = repeat (Datatypes.S m) false).
replace (C n C') with c'.
apply c'x.
reflexivity.
auto.
rewrite -> eql2.
rewrite -> rep_length.
apply in_eq.
auto.

assert (q_neq_n : q <> n0).
contradict nin.
rewrite -> nin.
unfold cd.
replace (C n C') with c'.
rewrite -> lemma3.
rewrite -> rep_length.
apply in_eq.
auto.

assert (app_or : In (q, Vnth x q) (rev ((n0, Datatypes.S m) :: S0)) \/ In (q, Vnth x q) R').
apply in_app_or.
rewrite <- inv2'.
apply (Lasc0 q (Vnth x q)).
reflexivity.
elim app_or.
intros inS.
assert (inS' : In (q, Vnth x q) ((n0, Datatypes.S m) :: S0)).
apply in_rev.
auto.
contradict nin.
unfold cd.
replace (C n C') with c'.
apply in_invert.
apply or_intror.

assert (inSS : In (q, Vnth x q) ((p1, 0%nat)::S'')).
rewrite <- eq2.
elim (in_inv inS').
intros eqfail.
inversion eqfail.
contradict q_neq_n.
auto.
auto.
assert (vz : Vnth x q = 0%nat).
elim (eq_nat_dec  (Vnth x q) 0%nat).
auto.
intros vzneq.
assert (inSSS : In (q, Vnth x q) S'').
elim (in_inv inSS).
intros eqfail.
inversion eqfail.
contradict vzneq.
auto.
auto.
assert (msqn : mys (q, Vnth x q) (p1, 0%nat)).
assert (sSSS : StronglySorted (fun x y : fin n * nat => mys y x) ((p1, 0%nat) :: S'')).
rewrite <- eq2.
auto.
apply (existence_sorting_In (p1, 0%nat) S'' (q, Vnth x q) (fun x y => mys y x) sSSS inSSS).
inversion msqn.
auto.
inversion H0.
rewrite -> lemma2.
unfold ll.
elim(eq_fin_dec p1 q).
intros a.
rewrite -> a.
apply in_eq.
intros.
apply in_invert.
apply or_intror.
elim (in_inv inSS).
intros peqq.
inversion peqq.
contradict b.
auto.
rewrite -> vz.
auto.
auto.
auto.
auto.
assert (inv3' : (((n0, Datatypes.S m) :: S0 = [ ]) +
                 (forall q : fin n,
                    lex (cd C' q)
                        (cd C'
                              (fst (car (q, 0%nat) ((n0, Datatypes.S m) :: S0))))))%type).
apply inr.
intros q.
unfold car.
unfold fst.
elim (eq_fin_dec q n0).
intros q_eq_n.
rewrite -> q_eq_n.
apply lex_refl.
intros q_neq_n.
replace (cd C' q) with Bnil.
apply nil_lex.
symmetry.
unfold cd.
replace (C n C') with c'.
apply lemma2.
apply q_neq_n.
reflexivity.
apply (complicated R' ((n0, Datatypes.S m) :: S0) L0 x xeq Lasc0 sL sR' sS' C' inv1' inv2' inv3').

(* final lap :3 - S = (p, Datatypes.S ms) :: S'', R = (n, Datatypes.S m) :: R'' *)

assert (lemma1 : forall n q r, ~ (In (n, q) S0 /\ In (n, r) R0)).
intros n3 q r und.
elim und.
intros NQ NR.
assert (NQ' : In (n3, q) L0).
rewrite -> inv2.
apply in_or_app.
apply or_introl.
apply in_rev.
rewrite -> rev_involutive.
apply NQ.
assert (NR' : In (n3, r) L0).
rewrite -> inv2.
apply in_or_app.
apply or_intror.
apply NR.
assert (NQX : Vnth x n3 = q).
apply Lasc0.
auto.
assert (NRX : Vnth x n3 = r).
apply Lasc0.
auto.
assert (q_eq_r : q = r).
rewrite <- NQX.
rewrite -> NRX.
reflexivity.
assert (sRx : StronglySorted mys ((p1, Datatypes.S ms) :: R0)).
apply (sorting_app (rev S'')).
replace (rev S'' ++ (p1, Datatypes.S ms) :: R0) with ((rev S'' ++ [(p1, Datatypes.S ms)]) ++ R0).
replace (rev S'' ++ [(p1, Datatypes.S ms)]) with (rev ((p1, Datatypes.S ms) :: S'')).
rewrite <- eq2.
rewrite <- inv2.
apply sL.
apply cons_rev_1.
rewrite <- app_assoc.
auto.
assert (H : mys (p1, Datatypes.S ms) (n3, r)).
apply (existence_sorting_In _ R0).
apply sRx.
apply NR.
assert (H1 : mys (p1, Datatypes.S ms) (n0, Datatypes.S m)).
apply (existence_sorting_In _ R0).
apply sRx.
rewrite -> eq.
apply in_eq.
assert (sSx : StronglySorted mys (rev ((n0, Datatypes.S m) :: S0))).
apply (sorting_app _ R').
rewrite -> cons_rev_1.
rewrite <- app_assoc.
replace ([(n0, Datatypes.S m)] ++ R') with ((n0, Datatypes.S m) :: R').
rewrite <- eq.
rewrite <- inv2.
apply sL.
auto.
assert (mys (n3, q) (n0, Datatypes.S m)).
apply (existence_sorting_In_split (rev S0) [(n0, Datatypes.S m)]).
rewrite <- cons_rev_1.
apply sSx.
apply in_rev.
rewrite -> rev_involutive.
apply NQ.
apply in_eq.
assert (mys (n3, q) (p1, Datatypes.S ms)).
apply (existence_sorting_In _ S'' _ (fun x y => mys y x)).
rewrite <- eq2.
auto.
apply (existence_disjunction_lemma ((p1, Datatypes.S ms) = (n3, q))).
apply in_inv.
rewrite <- eq2.
apply NQ.
intros Q.
contradict H.
rewrite -> Q.
intros Q2.
inversion Q2.
contradict H2.
apply lt_irrefl.
contradict H2.
rewrite -> q_eq_r.
apply lt_irrefl.

inversion H.
inversion H2.
assert ((` (f_nat n3) < ` (f_nat n3))%nat).
apply (lt_trans _ (` (f_nat p1))).
auto.
auto.
contradict H13.
apply lt_irrefl.
contradict H9.
rewrite -> H7.
rewrite -> q_eq_r.
apply lt_irrefl.
inversion H2.
contradict H4.
rewrite <- H12.
rewrite -> q_eq_r.
apply lt_irrefl.
assert (h : (q < r) % nat).
apply (lt_trans _ (Datatypes.S ms)).
auto.
auto.
contradict h.
rewrite -> q_eq_r.
apply lt_irrefl.

(* todo: lemma *)
assert ({m : LB | (cd c p1) <> m /\ ll (cd c p1) = ll m /\ lex (cd c p1) m
                            /\ forall n, (cd c p1) <> n -> ll (cd c p1) = ll n ->
                                         lex (cd c p1) n -> lex m n}).
apply lex_inc.
elim (list_eq_dec bool_dec (cd c  p1) (repeat (ll (cd c p1))true)).
intros eql.
assert (kdc1 : kraft_d c == 1).
apply extended_kraft_ineq.
exists p1.
split.
apply nnil_ll.
assert (ll_S : ll (cd c p1) = Datatypes.S ms).
assert (inS : In (p1, ll (cd c p1)) S0).
assert (indec : {In (p1, ll (cd c p1)) S0} + {~In (p1, ll (cd c p1)) S0}).
apply in_dec.
apply pair_dec.
elim indec.
trivial.
intros nin.
assert(contr : In (p1, Vnth x p1) R0).
apply inv1.
apply nin.
assert (contr2 : In (p1, Datatypes.S ms) S0 /\ In (p1, Vnth x p1) R0).
split.
rewrite -> eq2.
apply in_eq.
apply contr.
contradict contr2.
apply lemma1.
assert (inL : In (p1, ll (cd c p1)) L0).
rewrite -> inv2.
apply in_or_app.
apply or_introl.
apply in_rev.
rewrite -> rev_involutive.
apply inS.
assert (vxp : Vnth x p1 = ll (cd c p1)).
apply Lasc0.
apply inL.
assert (inL2 : In (p1, Datatypes.S ms) L0).
rewrite -> inv2.
apply in_or_app.
apply or_introl.
apply in_rev.
rewrite -> rev_involutive.
rewrite -> eq2.
apply in_eq.
rewrite <- vxp.
apply Lasc0.
apply inL2.
rewrite -> ll_S.
auto.
apply eql.
(* now there should be a contradiction, since the sum of L cannot satisfy the kraft inequality anymore (kraft_f  *)
assert (ungl : kraft_d c <= kraft_nvec x).
unfold kraft_d.
unfold kraft_vec.
apply kraft_nvec_le.
intros q.
assert (indec : {In (q, ll (cd c q)) S0} + {~ In (q, ll (cd c q)) S0}).
apply in_dec.
apply pair_dec.
elim indec.
intros inS.
assert (inL : In (q, ll (cd c q)) L0).
rewrite -> inv2.
apply in_or_app.
apply or_introl.
apply in_rev.
rewrite -> rev_involutive.
auto.
apply or_introl.
symmetry.
apply Lasc0.
rewrite -> (nth_map _ (C n c) q q eq_refl).
auto.

intros notin.
assert (H : cd c q = Bnil /\ In (q, Vnth x q) R0).
apply inv1.
auto.
elim H.
intros isnil inR.
apply or_intror.
rewrite -> (nth_map _ _ q q).
replace (Vnth (C n c) q) with (cd c q).
rewrite -> isnil.
auto.
auto.
reflexivity.

assert (H : {c_ext | forall q, ((q = n0) -> Vnth c_ext q = Datatypes.S m) /\ ((q <> n0) -> Vnth c_ext q = Vnth (Vmap lb (C n c)) q)}).
apply array_set.
elim H.
intros c_ext c_ext_b.
assert (ungl2 : kraft_nvec c_ext <= kraft_nvec x).
apply kraft_nvec_le.
intros q.
elim (eq_fin_dec q n0).
intros q_eq_n.
apply or_introl.
replace (Vnth c_ext q) with (Datatypes.S m).
replace (Vnth x q) with (Datatypes.S m).
reflexivity.
symmetry.
apply Lasc0.
rewrite -> inv2.
apply in_or_app.
apply or_intror.
rewrite -> eq.
rewrite q_eq_n.
apply in_eq.
symmetry.
apply c_ext_b.
auto.
intros q_neq_n.
assert (H0 : Vnth c_ext q = Vnth (Vmap lb (C n c)) q).
apply c_ext_b.
auto.
rewrite -> H0.
assert (indec : {In (q, ll (cd c q)) S0} + {~ In (q, ll (cd c q)) S0}).
apply in_dec.
apply pair_dec.
elim indec.
intros inS.
assert (inL : In (q, ll (cd c q)) L0).
rewrite -> inv2.
apply in_or_app.
apply or_introl.
apply in_rev.
rewrite -> rev_involutive.
auto.
apply or_introl.
symmetry.
apply Lasc0.
rewrite -> (nth_map _ _ q q).
auto.
auto.
intros notin.
assert (H1 : cd c q = Bnil /\ In (q, Vnth x q) R0).
apply inv1.
auto.
elim H1.
intros isnil inR.
apply or_intror.
rewrite -> (nth_map _ _ q q).
replace (Vnth (C n c) q) with (cd c q).
rewrite -> isnil.
auto.
auto.
reflexivity.
assert (gl3 : kraft_nvec c_ext == (1 # e2 (Datatypes.S m)) + kraft_nvec (Vmap lb (C n c))).
apply (kraft_nvec_inc _ _ _ n0).
intros b.
split.
intros b_eq_n.
split.
rewrite (nth_map _ _ b b).
assert (hlp : cd c b = Bnil).
apply inv1.
rewrite -> b_eq_n.
intros isinS.
assert (isinR : In (n0, Datatypes.S m) R0).
rewrite -> eq.
apply in_eq.
assert (isinSandR : In (n0, ll (cd c n0)) S0 /\ In (n0, Datatypes.S m) R0).
auto.
contradict isinSandR.
apply lemma1.
replace (Vnth (C n c) b) with (cd c b).
rewrite -> hlp.
auto.
auto.
reflexivity.
apply c_ext_b.
auto.
intros b_neq_n.
apply c_ext_b.
auto.

assert (gl4 : kraft_nvec (Vmap lb (C n c)) = kraft_d c).
unfold kraft_d.
unfold kraft_vec.
reflexivity.
assert (gl5 : kraft_nvec c_ext == (1 # e2 (Datatypes.S m)) + 1).
rewrite <- kdc1.
rewrite <- gl4.
apply gl3.
assert (gl6 : kraft_nvec x >= (1 # e2 (Datatypes.S m)) + 1).
rewrite <- gl5.
auto.
assert (gl7 : 1 < (1 # e2 (Datatypes.S m)) + 1).
rewrite <- (Qplus_0_l 1).
apply Qplus_lt_le_compat.
replace (1 # e2 (Datatypes.S m)) with (/ ((Zpos (e2 (Datatypes.S m))) # 1)).
apply Qinv_lt_0_compat.
compute.
reflexivity.
auto.
apply Qle_refl.
assert (gl8 : 1 < kraft_nvec x).
apply (Qlt_le_trans _ ((1 # e2 (Datatypes.S m)) + 1)).
auto.
auto.
rewrite xeq in gl8.
contradict kraft.
apply Qlt_not_le.
apply gl8.
trivial.

(* w00h00t *)
destruct H as [m0 m0_ex].

(* todo: already proved before *)
assert (sRx : StronglySorted mys ((p1, Datatypes.S ms) :: R0)).
apply (sorting_app (rev S'')).
replace (rev S'' ++ (p1, Datatypes.S ms) :: R0) with ((rev S'' ++ [(p1, Datatypes.S ms)]) ++ R0).
replace (rev S'' ++ [(p1, Datatypes.S ms)]) with (rev ((p1, Datatypes.S ms) :: S'')).
rewrite <- eq2.
rewrite <- inv2.
apply sL.
apply cons_rev_1.
rewrite <- app_assoc.
auto.

assert (lemma2 : mys (p1, Datatypes.S ms) (n0, Datatypes.S m)).
apply (existence_sorting_In _ R0).
apply sRx.
rewrite -> eq.
apply in_eq.

assert (lemma3 : forall p q, In (p, q) S0 -> ll (cd c p) = q).
intros p2 q ins.
assert (indec : {In (p2, ll (cd c p2)) S0}+{~In (p2, ll (cd c p2)) S0}).
apply in_dec.
apply pair_dec.
elim indec.
intros inS.
assert (inL1 : In (p2, q) L0).
rewrite -> inv2.
apply in_or_app.
apply or_introl.
apply in_rev.
rewrite -> rev_involutive.
auto.
assert (inL2 : In (p2, ll (cd c p2)) L0).
rewrite -> inv2.
apply in_or_app.
apply or_introl.
apply in_rev.
rewrite -> rev_involutive.
auto.
assert (l1 : Vnth x p2 = q).
apply Lasc0.
auto.
assert (l2 : Vnth x p2 = ll (cd c p2)).
apply Lasc0.
auto.
rewrite <- l1.
rewrite -> l2.
reflexivity.
intros notin.
assert (quark : In (p2, Vnth x p2) R0).
apply inv1.
auto.
assert (contr : In (p2, q) S0 /\ In (p2, Vnth x p2) R0).
auto.
contradict contr.
apply lemma1.

assert (lemma4 : forall q, lex (cd c q) (cd c p1)).
elim inv3.
intros s_eq_nil.
rewrite -> eq2 in s_eq_nil.
inversion s_eq_nil.
rewrite -> eq2.
unfold car.
unfold fst.
auto.

assert (lemma5 : p1 <> n0).
intros p_eq_n.
assert (in1 : In (n0, Datatypes.S ms) S0).
rewrite <- p_eq_n.
rewrite -> eq2.
apply in_eq.
assert (in2 : In (n0, Datatypes.S m) R0).
rewrite -> eq.
apply in_eq.
apply (lemma1 n0 (Datatypes.S ms) (Datatypes.S m)).
auto.

assert (H0 : {c' | forall q, ((q = n0) -> Vnth c' q = m0 ++ repeat (m - ms)%nat false)
                             /\ ((q <> n0) -> Vnth c' q = cd c q)}).
apply array_set.
destruct H0 as [c' c_x].

assert (m0_x_len : ll (m0 ++ repeat (m - ms)%nat false) = Datatypes.S m).
rewrite -> app_length.
rewrite -> rep_length.
replace (ll m0) with (Datatypes.S ms).
replace ((m - ms)%nat) with ((Datatypes.S m - Datatypes.S ms)%nat).
symmetry.
apply le_plus_minus.
inversion lemma2.
auto.
apply lt_le_weak.
auto.
apply Nat.sub_succ.
replace (ll m0) with (ll (cd c p1)).
symmetry.
apply lemma3.
rewrite -> eq2.
apply in_eq.
apply m0_ex.

assert (prefix_free : forall a b, a <> b -> ((Vnth c' a) = nil) + ~ (prefix (Vnth c' a) (Vnth c' b))).
intros a b neq.
elim (eq_fin_dec a n0).
intros a_eq_n.
elim (eq_fin_dec b n0).
intros b_eq_n.
contradict neq.
rewrite -> a_eq_n.
rewrite -> b_eq_n.
reflexivity.
intros b_neq_n.
apply inr.
replace (Vnth c' a) with (m0 ++ repeat (m - ms) false).
replace (Vnth c' b) with (cd c b).
intros pref.
assert (lx1 : lex m0 (cd c p1)).
apply (lex_trans _ (m0 ++ repeat (m - ms) false)).
apply prefix_lex.
exists (repeat (m - ms) false). reflexivity.
apply (lex_trans _ (cd c b)).
apply prefix_lex.
apply pref.
apply lemma4.
assert (lx2 : lex (cd c p1) m0).
apply m0_ex.
assert (equal : (cd c p1) = m0).
apply lex_antisym.
split. auto. auto.
contradict equal.
apply m0_ex.
symmetry.
apply c_x.
auto.
symmetry.
apply c_x.
auto.
elim (eq_fin_dec b n0).
intros b_eq_n.
intros a_neq_n.
elim (list_eq_dec bool_dec (Vnth c' a) Bnil).
auto.
intros nnil.
apply inr.
intros pref.
assert (ca : Vnth c' a = cd c a).
apply c_x. auto.
assert (cb : Vnth c' b = m0 ++ repeat (m - ms) false).
apply c_x. auto.
rewrite -> ca in pref.
rewrite -> cb in pref.
assert (pref2 : prefix (cd c a) m0).
apply (prefix_app _ _ (repeat (m - ms) false)).
apply pref.
replace (ll m0) with (ll (cd c p1)).
elim (eq_fin_dec a p1).
intros a_eq_p.
rewrite -> a_eq_p.
apply le_refl.
intros a_neq_p.
assert (mys (a, ll (cd c a)) (p1, ll (cd c p1))).
apply (existence_sorting_In _ S'' _ (fun x y => mys y x)).
rewrite -> (lemma3 p1 (Datatypes.S ms)).
rewrite <- eq2.
auto.
rewrite -> eq2.
apply in_eq.
assert (indec : {In (a, ll (cd c a)) S''} + {~ In (a, ll (cd c a)) S''}).
apply in_dec.
apply pair_dec.
elim indec.
auto.
intros nin.
assert (ninS : ~ In (a, ll (cd c a)) S0).
rewrite -> eq2.
contradict nin.
assert (inve : ((p1, Datatypes.S ms)=(a, ll (cd c a))) \/ In (a, ll (cd c a)) S'').
apply in_inv.
apply nin.
elim inve.
intros peq.
inversion peq.
contradict a_neq_p.
auto.
auto.
contradict nnil.
rewrite -> ca.
apply inv1.
auto.
inversion H.
auto.
apply lt_le_weak.
auto.
apply m0_ex.
elim (eq_fin_dec a p1).
intros a_eq_p.
rewrite -> a_eq_p in pref2.
assert (contr_eq : (cd c p1) = m0).
apply prefix_ll_eq.
split.
auto.
apply m0_ex.
contradict contr_eq.
apply m0_ex.
intros a_neq_p.
elim (prefix_dec (cd c a) (cd c p1)).
assert (pref4_or : (((cd c a) = Bnil) + ~ prefix (cd c a) (cd c p1))%type).
apply (prefix_free_set n c).
contradict a_neq_p.
apply a_neq_p.
elim pref4_or.
intros bnil.
contradict nnil.
rewrite -> ca.
apply bnil.
auto.
intros npref.
assert (nlex : lex (cd c p1) (cd c a)).
apply (existence_lex_lemma _ m0).
apply m0_ex.
apply pref2.
apply npref.
assert (nlex2 : lex (cd c a) (cd c p1)).
apply lemma4.
assert (nlex3 : cd c a = cd c p1).
apply lex_antisym.
auto.
contradict a_neq_p.
apply (dc_injective c).
rewrite <- ca.
apply nnil.
apply nlex3.
intros b_neq_n a_neq_n.
replace (Vnth c' a) with (cd c a).
replace (Vnth c' b) with (cd c b).
apply prefix_free_set.
contradict neq.
apply neq.
symmetry.
apply c_x.
apply b_neq_n.
symmetry.
apply c_x.
apply a_neq_n.

assert (length_lex : forall a b, (ll (Vnth c' a) < ll (Vnth c' b))%nat -> lex (Vnth c' a) (Vnth c' b)).
intros a b.
elim (eq_fin_dec a n0).
intros a_eq_n.
rewrite -> a_eq_n.
elim (eq_fin_dec b n0).
intros b_eq_n.
rewrite -> b_eq_n.
intros.
apply lex_refl.
intros b_neq_n.
replace (Vnth c' n0) with (m0 ++ repeat (m - ms) false).
replace (Vnth c' b) with (cd c b).
intros ll_lt.

assert (ll_gt : (ll (m0 ++ repeat (m - ms) false) >= ll (cd c b))%nat).
rewrite -> m0_x_len.
assert (indec : {In (b, ll (cd c b)) S0} + {~ In (b, ll (cd c b)) S0}).
apply in_dec.
apply pair_dec.
elim indec.
intros isinS.
assert (mss : mys (b, ll (cd c b)) (n0, Datatypes.S m)).
elim (eq_fin_dec b p1).
intros b_eq_p.
rewrite -> b_eq_p.
assert (quark : ll (cd c p1) = Datatypes.S ms).
apply lemma3.
rewrite -> eq2.
apply in_eq.
rewrite -> quark.
auto.
intros b_neq_p.
apply (mys_trans _ (p1, Datatypes.S ms)).
apply (existence_sorting_In _ S'' _ (fun x y => mys y x)).
rewrite <- eq2.
auto.
assert (ininv: (p1, Datatypes.S ms) = (b, ll (cd c b)) \/ In (b, ll (cd c b)) S'').
apply in_inv.
rewrite <- eq2.
auto.
elim ininv.
intros contr.
inversion contr.
contradict b_neq_p.
auto.
auto.
auto.
inversion mss.
apply le_refl.
apply lt_le_weak.
auto.
intros nin.
replace (cd c b) with Bnil.
unfold ll.
omega.
symmetry.
apply inv1.
apply nin.
contradict ll_gt.
apply lt_not_le.
apply ll_lt.
symmetry.
apply c_x.
apply b_neq_n.
symmetry.
apply c_x.
reflexivity.
intros a_neq_n.
elim (eq_fin_dec b n0).
intros b_eq_n.
intros ll_lt.
replace (Vnth c' b) with (m0 ++ repeat (m - ms) false).
apply (lex_trans _ m0).
apply (lex_trans _ (Vnth c' p1)).
replace (Vnth c' p1) with (cd c p1).
replace (Vnth c' a) with (cd c a).
apply lemma4.
symmetry.
apply c_x.
apply a_neq_n.
symmetry.
apply c_x.
apply lemma5.
replace (Vnth c' p1) with (cd c p1).
apply m0_ex.
symmetry.
apply c_x.
apply lemma5.
apply prefix_lex.
exists (repeat (m - ms) false).
reflexivity.
symmetry.
apply c_x.
apply b_eq_n.
intros b_neq_n.
replace (Vnth c' a) with (cd c a).
replace (Vnth c' b) with (cd c b).
apply length_lex.
symmetry.
apply c_x.
apply b_neq_n.
symmetry.
apply c_x.
apply a_neq_n.

assert (char_enc : forall a b, ll (Vnth c' a) = ll (Vnth c' b) -> (f_le a b) -> lex (Vnth c' a) (Vnth c' b)).
intros a b.
elim (eq_fin_dec a n0).
intros a_eq_n.
elim (eq_fin_dec b n0).
intros b_eq_n.
rewrite -> a_eq_n.
rewrite -> b_eq_n.
intros.
apply lex_refl.
intros b_neq_n.
intros ll_eq fle.
assert (indec : {In (b, ll (Vnth c' b)) S0} + {~ In (b, ll (Vnth c' b)) S0}).
apply in_dec.
apply pair_dec.
elim indec.
intros isin.
assert (mys' : mys (p1, ll (Vnth c' p1)) (a, ll (Vnth c' a))).
rewrite -> a_eq_n.
replace (ll (Vnth c' p1)) with (Datatypes.S ms).
replace (ll (Vnth c' n0)) with (Datatypes.S m).
apply lemma2.
replace (Vnth c' n0) with (m0 ++ repeat (m - ms) false).
symmetry. auto.
symmetry.
apply c_x. auto.
symmetry.
replace (Vnth c' p1) with (cd c p1).
apply lemma3.
rewrite -> eq2.
apply in_eq.
symmetry.
apply c_x.
apply lemma5.
assert (mys'' : mys (b, ll (Vnth c' b)) (a, ll (Vnth c' a))).
elim (eq_fin_dec b p1).
intros b_eq_p.
rewrite -> b_eq_p.
apply mys'.
intros b_neq_p.
apply (mys_trans _ (p1, Datatypes.S ms)).
apply (existence_sorting_In _ S'' _ (fun x y => mys y x)).
rewrite <- eq2.
auto.
assert (ininv : (p1, Datatypes.S ms) = (b, ll (Vnth c' b)) \/ In (b, ll (Vnth c' b)) S'').
apply in_inv.
rewrite <- eq2.
auto.
elim ininv.
intros contr.
inversion contr.
contradict b_neq_p.
symmetry.
apply H0.
auto.
replace (ll (Vnth c' a)) with (Datatypes.S m).
rewrite -> a_eq_n.
auto.
symmetry.
replace (Vnth c' a) with (m0 ++ repeat (m - ms) false).
auto.
symmetry.
apply c_x.
auto.
inversion mys''.
contradict fle.
apply lt_not_le.
auto.
contradict H0.
rewrite -> ll_eq.
apply lt_irrefl.
intros nin.
assert (isnil : (Vnth c' b) = Bnil).
assert (tmpeq : Vnth c' b = cd c b).
apply c_x.
auto.
rewrite -> tmpeq.
apply inv1.
rewrite <- tmpeq.
auto.
rewrite -> isnil in ll_eq.
assert (tmpeq : Vnth c' a = m0 ++ repeat (m - ms) false).
apply c_x.
auto.
rewrite -> tmpeq in ll_eq.
rewrite -> m0_x_len in ll_eq.
inversion ll_eq.
intros a_neq_n.
elim (eq_fin_dec b n0).
intros b_eq_n.
intros ll_eq f_le.
replace (Vnth c' b) with (m0 ++ repeat (m - ms) false).
apply (lex_trans _ m0).
elim (eq_fin_dec a p1).
intros a_eq_p.
rewrite -> a_eq_p.
replace (Vnth c' p1) with (cd c p1).
apply m0_ex.
symmetry.
apply c_x.
apply lemma5.
intros a_neq_p.
replace (Vnth c' a) with (cd c a).
apply (lex_trans _ (cd c p1)).
apply lemma4.
apply m0_ex.
symmetry.
apply c_x.
apply a_neq_n.
apply prefix_lex.
exists (repeat (m - ms) false).
reflexivity.
symmetry.
apply c_x.
apply b_eq_n.
intros b_neq_n.
replace (Vnth c' a) with (cd c a).
replace (Vnth c' b) with (cd c b).
intros ll_eq fle.
apply char_enc.
apply ll_eq.
trivial.
symmetry.
apply c_x.
auto.
symmetry.
apply c_x.
auto.

assert (dense : forall a c, c <> nil -> lex c (Vnth c' a) -> ll c = ll (Vnth c' a)
                            -> exists b, (~ (Vnth c' b) = nil) /\ (prefix (Vnth c' b) c)).
assert (lltmp1 : ll (Vnth c' p1) = Datatypes.S ms).

replace (Vnth c' p1) with (cd c p1).
apply lemma3.
rewrite -> eq2.
apply in_eq.
symmetry.
apply c_x.
apply lemma5.
intros a c0 nnil lx ll_eq.
elim (eq_fin_dec a n0).
intros a_eq_n.
assert (tk : {l' | prefix l' c0 /\ ll l' = ll (Vnth c' p1)}).
apply take_lemma.
rewrite -> ll_eq.
rewrite -> a_eq_n.
rewrite -> lltmp1.
replace (ll (Vnth c' n0)) with (Datatypes.S m).
inversion lemma2.
auto.
apply lt_le_weak.
auto.
symmetry.
replace (Vnth c' n0) with (m0 ++ repeat (m - ms) false).
auto.
symmetry.
apply c_x.
auto.
elim tk.
intros l' l'_ex.
elim l'_ex.
intros l'1 l'2.
elim (lex_total l' (Vnth c' p1)).
intros lx2.
assert(H1 : exists b', cd c b' <> Bnil /\ prefix (cd c b') l').
apply (dense n _ p1).
apply nnil_ll.
rewrite -> l'2.
rewrite -> lltmp1.
intros Q.
inversion Q.
replace (Vnth (C n c) p1) with (Vnth c' p1).
apply lx2.
apply c_x.
apply lemma5.
replace (Vnth (C n c) p1) with (Vnth c' p1).
apply l'2.
apply c_x.
auto.
elim H1.
intros b b_ex.
elim b_ex.
intros b'1 b'2.
elim (eq_fin_dec b n0).
intros iseq.
assert (nin : ~ In (n0, ll (cd c n0)) S0).
intros Q.
assert (inn : In (n0, Datatypes.S m) R0).
rewrite -> eq.
apply in_eq.
apply (lemma1 n0 (ll (cd c n0)) (Datatypes.S m)).
auto.
contradict b'1.
rewrite -> iseq.
apply inv1.
auto.
intros b_neq_n.
exists b.
assert (eqtmp1 : Vnth c' b = cd c b).
apply c_x.
auto.
rewrite -> eqtmp1.
split.
apply b'1.
apply (prefix_trans _ l').
apply b_ex.
apply l'1.
intros lx2.
elim (list_eq_dec bool_dec (Vnth c' p1) l').
intros iseq.
exists p1.
split.
apply nnil_ll.
rewrite -> lltmp1.
intros Q.
inversion Q.
rewrite -> iseq.
auto.
intros isneq.
assert (gl : l' = m0).
apply lex_antisym.
split.
apply (lex_take _ _ c0 (Vnth c' n0)).
auto.
replace (Vnth c' n0) with (m0 ++ repeat (m - ms) false).
exists (repeat (m - ms) false).
reflexivity.
symmetry.
apply c_x.
reflexivity.
rewrite -> l'2.
replace (Vnth c' p1) with (cd c p1).
apply m0_ex.
symmetry.
apply c_x.
apply lemma5.
rewrite <- a_eq_n.
auto.
apply m0_ex.
replace (cd c p1) with (Vnth c' p1).
apply isneq.
apply c_x.
apply lemma5.
replace (cd c p1) with (Vnth c' p1).
symmetry.
apply l'2.
apply c_x.
apply lemma5.
replace (cd c p1) with (Vnth c' p1).
apply lx2.
apply c_x.
apply lemma5.
elim l'1.
intros x0 H1.
rewrite -> gl in H1.
assert (lx3 : (lex x0 (repeat (m - ms) false))).
apply (lex_apprm m0).
rewrite -> H1.
replace (m0 ++ repeat (m - ms) false) with (Vnth c' n0).
rewrite <- a_eq_n.
auto.
apply c_x.
auto.
assert (x0pref : prefix x0 (repeat (m - ms) false)).
apply lex_0_is_prefix.
apply lx3.
exists n0.
split.
apply nnil_ll.
replace (Vnth c' n0) with (m0 ++ repeat (m - ms) false).
rewrite -> m0_x_len.
intros Q.
inversion Q. 
symmetry.
apply c_x.
reflexivity.
replace (Vnth c' n0) with (m0 ++ repeat (m - ms) false).
rewrite <- H1.
assert (x0eql : x0 = repeat (m - ms) false).
apply prefix_ll_eq.
split.
apply x0pref.
apply (Nat.add_cancel_l _ _ (ll m0)).
rewrite <- app_length.
rewrite <- app_length.
rewrite -> H1.
replace (m0 ++ repeat (m - ms) false) with (Vnth c' a).
auto.
apply c_x.
auto.
rewrite <- x0eql.
exists Bnil.
apply app_nil_r.
symmetry.
apply c_x.
auto.
intros a_neq_n.
assert (exists b', Vnth (C n c) b' <> Bnil /\ prefix (Vnth (C n c) b') c0).
apply (dense n c a).
apply nnil.
replace (Vnth (C n c) a) with (Vnth c' a).
auto.
apply c_x.
auto.
replace (Vnth (C n c) a) with (Vnth c' a).
auto.
apply c_x.
auto.
destruct H as [b' [H3 H4]].
exists b'.
assert (b'_neq_n : b' <> n0).
intros b'_eq_n.
assert (ninS : ~ In (b', ll (cd c b')) S0).
intros otherwise.
assert (ninR : In (b', Datatypes.S m) R0).
rewrite -> b'_eq_n.
rewrite -> eq.
apply in_eq.
apply (lemma1 b' (ll (cd c b')) (Datatypes.S m)).
auto.
contradict H3.
apply inv1.
auto.
assert (equal : cd c b' = Vnth c' b').
symmetry.
apply c_x.
apply b'_neq_n.
split.
rewrite <- equal.
auto.
rewrite <- equal.
auto.

set (C' := mkDeflateCoding
             n c' (prefix_free_set_inv _ prefix_free) length_lex char_enc dense).

assert(inv1':forall q : fin n,
               ~ In (q, ll (cd C' q)) ((n0,Datatypes.S m) :: S0) ->
               cd C' q = Bnil /\ In (q, Vnth x q) R').
intros q.
elim (eq_fin_dec q n0).
intros q_eq_n.
rewrite -> q_eq_n.
intros nin.
contradict nin.
replace (cd C' n0) with (m0 ++ repeat (m - ms) false).
rewrite -> m0_x_len.
apply in_eq.
symmetry.
replace (m0 ++ repeat (m - ms) false) with (Vnth c' n0).
auto.
apply c_x.
reflexivity.
intros q_neq_n.
intros nin.
assert (~ In (q, ll (cd C' q)) S0).
contradict nin.
apply in_cons.
apply nin.
assert (qeq : cd C' q = cd c q).
apply c_x.
apply q_neq_n.
split.
rewrite -> qeq.
apply inv1.
rewrite <- qeq.
apply H.
assert (ininv : (n0, Datatypes.S m) = (q, Vnth x q) \/ In (q, Vnth x q) R').
apply in_inv.
rewrite <- eq.
apply inv1.
rewrite <- qeq.
apply H.
elim ininv.
intros contr.
inversion contr.
contradict q_neq_n.
auto.
auto.

assert (inv2' : L0 = rev ((n0, Datatypes.S m)::S0) ++ R').
rewrite -> cons_rev.
rewrite <- eq.
apply inv2.

assert (sS' : StronglySorted (fun x y => mys y x) ((n0, Datatypes.S m)::S0)).
apply (existence_sorting_S _ (n0,Datatypes.S m) R').
rewrite -> cons_rev.
rewrite <- eq.
rewrite <- inv2.
apply sL.

assert (sR' : StronglySorted mys R').
rewrite -> eq in sR.
inversion sR.
trivial.

assert (inv3' : (((n0, Datatypes.S m) :: S0 = [ ]) +
                 (forall q : fin n,
                    lex (cd C' q)
                        (cd C' (fst (car (q, 0%nat) ((n0, Datatypes.S m) :: S0))))))%type).
apply inr.
intros q.
unfold car.
unfold fst.
elim (eq_fin_dec q n0).
intros q_eq_n.
rewrite -> q_eq_n.
apply lex_refl.
intros q_neq_n.
replace (cd C' q) with (cd c q).
replace (cd C' n0) with (m0 ++ repeat (m - ms) false).
apply (lex_trans _ m0).
apply (lex_trans _ (cd c p1)).
apply lemma4.
apply m0_ex.
apply prefix_lex.
exists (repeat (m - ms) false).
reflexivity.
symmetry.
apply c_x.
reflexivity.
symmetry.
apply c_x.
apply q_neq_n.
apply (complicated R' ((n0, Datatypes.S m)::S0) L0 x xeq Lasc0 sL sR' sS' C' inv1' inv2' inv3').

(* Beginning *)
apply SSorted_nil.
intros q _.
split.
apply allnil.
apply Lasc.
reflexivity.
auto.
apply inl.
reflexivity.
Defined.

Local Open Scope nat_scope.
(* TODO: This function is very inefficient *)
Theorem decodePointWithVec : forall {n} (c : VecLB n) bits,
                               ({char : nat &
                                            { code : LB &
                                                        { rest : LB | code <> Bnil /\
                                                                      bits = code ++ rest /\
                                                                      Vnth_is n char c code}}}) +
                               ({char : nat &
                                            { code : LB &
                                                        { rest : LB | code <> Bnil /\
                                                                      bits = code ++ rest /\
                                                                      Vnth_is n char c code}}} -> False).
Proof.
  dependent induction n.
  intros.
  apply inr.
  intro Q.
  destruct Q as [? [? [? [? [? no]]]]].
  inversion no.

  intros c bits.
  dependent destruction c.
  destruct h as [|h' h''] eqn:heq.
  destruct (IHn c bits) as [[ch [cd [r [a1 [a2 a3]]]]] | j].
  apply inl.
  exists (S ch).
  exists cd.
  exists r.
  firstorder.
  constructor.
  trivial.

  apply inr.
  intro Q.
  contradict j.
  destruct Q as [ch [cd [r [nnil [rst vn]]]]].
  destruct ch.
  contradict vn.
  intros Q.
  inversion Q.
  contradict nnil.
  auto.

  exists ch.
  exists cd.
  exists r.

  inversion vn.
  inversion H3. (* TODO *)
  firstorder.

  destruct (prefix_dec h bits) as [q | nq].
  destruct (prefix_split _ _ q) as [r nr].
  apply inl.
  exists 0.
  exists h.
  exists r.
  firstorder.
  rewrite -> heq.
  intro Q.
  inversion Q.
  rewrite <- heq.
  constructor.

  destruct (IHn c bits) as [[ch [cd [r [a1 [a2 a3]]]]] | j].
  apply inl.
  exists (S ch).
  exists cd.
  exists r.
  split.
  trivial.
  split.
  trivial.
  constructor.
  trivial.

  apply inr.
  intro Q.
  destruct Q as [ch [cd [r [nnil [A B]]]]].
  destruct ch.
  inversion B.
  contradict nq.
  exists r.
  rewrite -> heq.
  rewrite -> H1. (* TODO *)
  auto.

  contradict j.
  exists ch.
  exists cd.
  exists r.
  split.
  trivial.
  split.
  trivial.
  inversion B.
  inversion H3. (* TODO *)
  auto.
Qed.

(* TODO: This is inefficient *)
Theorem dc_StrongDec : forall {m} (dc : deflateCoding m), StrongDec (dc_enc dc).
Proof.
  intros m dc l.
  destruct (decodePointWithVec (C m dc) l) as [[char [code [rest [code_nnil [lapp vni]]]]]|no].
  apply inl.
  exists char.
  exists code.
  exists rest.
  split.
  trivial.
  unfold dc_enc.
  split.
  trivial.
  trivial.

  apply inr.
  split.
  exact ("No character recognized in the current deflate coding"++blstring l)%string.
  intro Q.
  contradict no.
  destruct Q as [a [l' [l'' [lapp [vni nn]]]]].
  exists a.
  exists l'.
  exists l''.
  auto.
Qed.

Theorem vec_StrongUnique : forall {m} (q : vec LB m) a (l1 l2 : LB),
                             Vnth_is m a q l1 -> Vnth_is m a q l2 -> l1 = l2.
Proof.
  intros m q a l1 l2 vna vnb.
  dependent induction q.
  inversion vna.
  dependent destruction vna.
  dependent destruction vnb.
  reflexivity.
  dependent destruction vnb.
  apply (IHq m).
  trivial.
  trivial.
Qed.

Lemma vnth_is_correct : forall {A} {m} (v : vec A m) x n,
                          Vnth_is m n v x ->
                          {e : n < m & Vnth v (Fin.of_nat_lt e) = x}.
Proof.
  intros A m v c n vi.
  dependent induction vi.
  assert (e : 0 < S n).
  omega.
  exists e.
  reflexivity.

  destruct IHvi as [e vnb].
  assert (e' : S m < S n).
  omega.
  exists e'.
  assert (H : (Fin.of_nat_lt e') = FinFS (Fin.of_nat_lt e)).
  compute.
  replace (lt_S_n m n e') with e.
  reflexivity.
  apply proof_irrelevance.
  rewrite -> H.
  auto.
Qed.

Lemma prefix_free' : forall {m} (dc : deflateCoding m) a b l1 l2,
                       a <> b ->
                       dc_enc dc a l1 ->
                       dc_enc dc b l2 ->
                       ~ prefix l1 l2.
Proof.
  intros m dc a b l1 l2 neq dca dcb.
  destruct dca as [va annil].
  destruct dcb as [vb bnnil].
  destruct (vnth_is_correct _ _ _ va) as [xa ea].
  destruct (vnth_is_correct _ _ _ vb) as [xb eb].
  destruct (prefix_free_set m dc (Fin.of_nat_lt xa) (Fin.of_nat_lt xb)).
  intro Q.
  contradict neq.
  apply (of_nat_lt_inj xa xb).
  trivial.
  rewrite -> ea in e.
  contradict annil.
  trivial.
  rewrite <- ea.
  rewrite <- eb.
  trivial.
Qed.

Theorem dc_StrongUnique : forall {m} (dc : deflateCoding m), StrongUnique (dc_enc dc).
Proof.
  intros m dc n b la las lb lbs apps dca dcb.
  (* destruct dca as [vnia nnilla]. *)
  (* destruct dcb as [vnib nnillb]. *)

  destruct (eq_nat_dec n b) as [e | e].
  split.
  trivial.
  apply (vec_StrongUnique (C m dc) n).
  destruct dca.
  trivial.
  rewrite -> e.
  destruct dcb.
  trivial.
  destruct (prefix_common la lb (lb ++ lbs)) as [ab | ba].
  rewrite <- apps.
  exists las.
  reflexivity.
  exists lbs.
  reflexivity.
  contradict ab.
  apply (prefix_free' dc n b).
  trivial.
  trivial.
  trivial.
  contradict ba.
  apply (prefix_free' dc b n).
  auto.
  trivial.
  trivial.
Qed.
