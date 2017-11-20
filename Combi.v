(* a lot of small combinatorical lemmata that might be found elsewhere *)

Require Import Coq.Sorting.Sorted.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.QArith.Qfield.
Require Import Program.
Require Import EqdepFacts.
Require Import Eqdep_dec.

Require Import Shorthand.
Require Import Lex.
Require Import Prefix.
Require Import Repeat.
Require Import Transports.

Module NatDec <: DecidableSet.
  Definition U := nat.
  Lemma eq_dec : forall (x y : U), {x = y} + {x <> y}.
  Proof. decide equality. Qed.
End NatDec.

Module NatEqDep := DecidableEqDepSet(NatDec).

Ltac depelim_fin x :=
  match type of x with
  | fin ?n =>
      let m := fresh "n" in
      let y := fresh x in
      let H := fresh in
      match goal with
      |- ?gl =>
        enough (forall (m : nat) (y : fin m), existT fin m y = existT fin n x ->
          gl) as H by (eapply H; reflexivity);
        destruct y;
        (intros H;
          let H' := fresh H in
          pose proof (eq_sigT_fst H) as H';
          inversion H'; subst; clear H';
          apply NatEqDep.inj_pairT2 in H; subst)
      end
  end.

Fixpoint array_set {A} {n : nat} (a : vec A n) (b : fin n) (d : A) {struct a} :
  {c : vec A n | forall (q : fin n), (q = b -> Vnth c q = d) /\ ((q <> b) -> Vnth c q = Vnth a q)}.
Proof.
  destruct a.
  - abstract (inversion b).
  - depelim_fin b.
    + exists (Vcons d n a).
      intros; split.
      * now intros ->.
      * intros Hq. depelim_fin q.
        -- now elim Hq.
        -- reflexivity.
    + destruct (array_set _ _ a b0 d) as [rec Hrec].
      exists (Vcons h n rec).
      intros; split.
      * intros ->. now apply Hrec.
      * intros. depelim_fin q.
        -- reflexivity.
        -- apply Hrec. contradict H. now f_equal.
Defined.

Local Open Scope nat.

Record halforder (A : Set) : Type :=
  mkHalfOrder { ord : A -> A -> Prop ;
                linear : forall a b, ord a b + ord b a ;
                refl : forall a, ord a a ;
                trans : forall a b c, ord a b -> ord b c -> ord a c
              }.

Lemma lex_inc : forall (l : LB),
                  (l <> repeat (ll l) true) ->
                  {m : LB | l <> m /\ ll l = ll m /\ lex l m
                            /\ forall n, l <> n -> ll l = ll n ->
                                         lex l n -> lex m n}.
Proof.
  intros l lneq.
  induction l as [|a l IHl].
  contradict lneq.
  auto.
  induction a.
  assert(H:{ m : LB | l <> m /\ ll l = ll m /\ lex l m /\
                     forall n, l <> n -> ll l = ll n -> lex l n -> lex m n }).
  apply IHl.
  contradict lneq.
  rewrite -> lneq.
  replace (ll (true :: repeat (ll l) true)) with (S(ll(repeat (ll l) true))).
  rewrite -> rep_length.
  auto.
  auto.
  destruct H as [x p].
  exists (true :: x).
  destruct p as [H0 [H2 [H4 H5]]].
  split.
  contradict H0.
  inversion H0.
  reflexivity.
  split.
  replace (ll (true :: x)) with (S (ll x)).
  replace (ll (true :: l)) with (S (ll l)).
  rewrite -> H2.
  reflexivity.
  auto.
  auto.
  split.
  apply cdr_lex.
  auto.
  intros n tl_neq_n ll_eq lexi.
  induction n as [|a n IHn].
  inversion ll_eq.
  induction a.
  assert (tl_neq_n' : l <> n).
  contradict tl_neq_n.
  rewrite tl_neq_n.
  reflexivity.
  assert (ll_eq' : ll l = ll n).
  inversion ll_eq.
  auto.
  assert (lexi' : lex l n).
  apply lex_cdr with true.
  auto.
  assert (lex' : lex x n).
  apply H5.
  apply tl_neq_n'.
  apply ll_eq'.
  apply lexi'.
  apply cdr_lex.
  apply lex'.
  inversion lexi.
  elim (list_eq_dec bool_dec l (repeat (ll l) true)).
  intros istrue.
  exists (true :: repeat (ll l) false).
  split.
  intros Q. inversion Q.
  split.
  replace (ll (false :: l)) with (S (ll l)).
  replace (ll (true :: repeat (ll l) false)) with (S(ll (repeat (ll l) false))).
  rewrite -> rep_length.
  reflexivity.
  auto.
  auto.
  split.
  apply car_lex.  
  intros n fl_neq_n ll_eq lex_fl_n.
  induction n as [|a n IHn].
  inversion ll_eq.
  induction a.
  apply cdr_lex.
  assert (ll_eq' : ll l = ll n).
  inversion ll_eq.
  auto.
  rewrite -> ll_eq'.
  apply lex_0_x.
  assert (lln : lex l n).
  apply lex_cdr with false.
  auto.
  contradict lex_fl_n.
  rewrite -> istrue.
  assert (ll_eq' : ll l = ll n).
  inversion ll_eq.
  auto.
  assert (n = repeat (ll n) true).
  apply lex_1_is_1.
  rewrite <- ll_eq'.
  rewrite <- istrue.
  apply lln.
  contradict fl_neq_n.
  rewrite -> istrue.
  rewrite -> H.
  rewrite <- ll_eq'.
  reflexivity.

  intros b.
  elim IHl.
  intros x p.
  destruct p as [H [H1 [H3 H4]]].
  exists (false :: x).
  split.
  contradict H.
  inversion H.
  auto.
  split.
  replace (ll (false :: l)) with (S (ll l)).
  replace (ll (false :: x)) with (S (ll x)).
  rewrite <- H1.
  auto.
  auto.
  auto.
  split.
  apply cdr_lex.
  auto.
  intros n flnn ll_eq lx.
  induction n.
  inversion lx.
  induction a.
  apply car_lex.
  apply cdr_lex.
  apply H4.
  contradict flnn.
  rewrite -> flnn.
  auto.
  inversion ll_eq.
  auto.
  apply lex_cdr with  false.
  auto.
  auto.
Defined.

Lemma genmax : forall (o : halforder LB) m (f : fin (S m) -> LB),
                 { n | forall n', ord _ o (f n') (f n) }.
Proof.
  intros o.
  induction m as [|m IHm].

  (* m = 0 *)
  intros f.
  exists (Fin.F1 (n := 0)).
  intros n'.
  assert (H : n' = Fin.F1).
  apply fin_1_is_1.
  rewrite -> H.
  apply (refl _ o).

  (* m = S m *)
  intros f.
  assert (IH : {n : fin (S m) | forall (n' : fin (S m)), ord LB o (f (FinLR 1 n')) (f (FinLR 1 n))}).
  apply IHm.

  destruct IH as [x x0].
  induction (linear _ o (f (FinLR 1 x)) (f (lastfin (S m)))).

  (* ord LB o (f (FinLR 1 x)) (f (lastfin (S m)))) *)
  exists (lastfin (S m)).
  intros n'.
  assert (H : {n' = lastfin (S m)} + {n' <> lastfin (S m)}).
  apply eq_fin_dec.
  induction H as [a0 | b].

  (* n' = lastfin (S m) *)
  rewrite -> a0.
  apply (refl _ o).

  (* n' <> lastfin (S m) *)
  apply (trans _ o _ (f (FinLR 1 x))).
  assert (predf : {q | n' = FinLR 1 q}).
  apply ex_predfin.
  apply b.
  elim predf.
  intros x1 n'eq.
  rewrite -> n'eq.
  apply x0.
  trivial.

  (* b : ord LB o (f (lastfin (S m))) (f (FinLR 1 x)) *)
  exists (FinLR 1 x).
  intros n'.
  assert(H: {n'=lastfin(S m)}+{n'<>lastfin(S m)}).
  apply eq_fin_dec.
  induction H as [a | b0].
  (* n' = lastfin (S m) *)
  rewrite -> a.
  apply b.
  (* n' <> S m *)
  apply (trans _ o _ (f (FinLR 1 x))).
  assert (predf:{q|n'=FinLR 1 q}).
  apply ex_predfin.
  trivial.
  destruct predf as [n'' n''eq].
  rewrite n''eq.
  apply x0.
  apply (refl _ o).
Defined.

Lemma lenmax : forall m (f : fin (S m) -> LB), { n | forall n', ll (f n') <= ll (f n)}.
Proof.
  intros m f.
  assert (trans : forall (a b c : LB), ll a <= ll b -> ll b <= ll c -> ll a <= ll c).
  intros a b c.
  apply le_trans.
  assert (refl : forall (a : LB), ll a <= ll a). auto.
  assert (lin : forall (a b : LB), (ll a <= ll b) + (ll b <= ll a)).
  intros a b.
  assert (lin' : {ll a <= ll b} + {ll b <= ll a}).
  apply le_ge_dec.
  induction lin'.  apply inl. trivial. apply inr. trivial.
  apply (genmax (mkHalfOrder LB (fun x => fun y => (ll x <= ll y)) lin refl trans)).
Defined.

Lemma lexmax : forall m (f : fin (S m) -> LB), { n | forall n', lex (f n') (f n)}.
Proof.
  intros m f.
  apply (genmax (mkHalfOrder LB lex lex_total lex_refl lex_trans)).
Defined.

Lemma lexmin : forall m (f : fin (S m) -> LB), {n | forall n', lex (f n) (f n')}.
Proof.
  set (xel a b := lex b a).
  assert (xel_refl : forall a, xel a a).
  apply lex_refl.
  assert (xel_total : forall a b, xel a b + xel b a).
  intros a b.
  elim (lex_total a b).
  apply inr.
  apply inl.
  assert (xel_trans : forall a b c, xel a b -> xel b c -> xel a c).
  intros a b c xab xbc.
  apply lex_trans with b.
  auto. auto.
  intros.
  apply (genmax (mkHalfOrder LB xel xel_total xel_refl xel_trans)).
Defined.

Function longest_f m f : LB :=
  let lm := (lenmax m f) in (f (` lm)).

Function lenmax_f m f : nat := ll (longest_f m f).

Lemma prefix_lex : forall a b, prefix a b -> lex a b.
Proof.
  refine (fix f a b : prefix a b -> lex a b := _).
  intros.
  inversion H as [x H0].
  assert (H1 : lex (a ++ x) b).
  rewrite H0.
  apply lex_refl.
  induction a as [|a a0 IHa].
  apply nil_lex.
  inversion H0 as [H2].
  apply cdr_lex.
  apply (f a0 (a0 ++ x)).
  exists x.
  auto.
Defined.

Fixpoint fold {n} {A} (null : A) (f : A -> A -> A) (vc : vec A n) : A :=
  match vc with
      | Vnil => null
      | Vcons a _ r => f a (fold null f r)
  end.

Fixpoint foldlist {A B} (null : B) (f : A -> B -> B) (l : list A) : B :=
  match l with
      | [] => null
      | a :: r => f a (foldlist null f r)
  end.

Lemma fold_lemma_1 : forall {A} null f (vc : vec _ 0%nat), fold (A:=A) null f vc = null.
Proof.
  intros A null f vc.
  rewrite (vec_0_nil vc).
  reflexivity.
Defined.

Lemma vec_id_fold : forall {A} {n m : nat} (eq : n = m) (a : A)
                           (b : A -> A -> A) (v : vec A n),
                      fold a b (vec_id eq v) = fold a b v.
Proof.
  intros A n m eq a b v.
  dependent destruction eq.
  rewrite -> (vec_id_destroy v).
  reflexivity.
Qed.

Inductive dflist {A : Set} : list A -> Set := 
  | dflist_nil : dflist nil
  | dflist_cons :
      forall a b, dflist b -> (~ (In a b)) -> dflist (a :: b).

Definition pflist (l : list LB) :=
  forall (a b : LB), In a l -> In b l -> a <> b -> ~ prefix a b.

Fixpoint splitlist (b : bool) (l : list LB) :=
  match l with
    | nil => nil
    | xl :: l' =>
      match xl with
        | nil => splitlist b l'
        | b' :: b'' =>
          match (b, b') with
              | (true, true) => b'' :: (splitlist b l')
              | (false, false) => b'' :: (splitlist b l')
              | _ => splitlist b l'
          end
      end
  end.

Lemma pflist_splittable_3 : forall a b l, In (a :: b) l -> In b (splitlist a l).
Proof.
  intros a b l inabl.
  induction l as [|a0 l IHl].
  inversion inabl.
  inversion inabl as [H|H].
  rewrite -> H.
  destruct a.
  apply in_eq.
  apply in_eq.
  destruct a0.
  apply IHl.
  apply H.
  destruct (bool_dec a b0) as [a_eq_b0 | a_neq_b0].
  assert(sl : splitlist a ((b0 :: a0) :: l) = a0 :: splitlist a l).
  destruct a.
  rewrite <- a_eq_b0.
  reflexivity.
  rewrite <- a_eq_b0.
  reflexivity.
  rewrite -> sl.
  assert (ininv : (b0 :: a0) = (a :: b) \/ In (a :: b) l).
  apply in_inv.
  apply inabl.
  destruct ininv as [iseq | inabl2].
  inversion iseq.
  apply in_eq.
  apply in_cons.
  apply IHl.
  apply inabl2.
  destruct a.
  destruct b0.
  contradict a_neq_b0.
  reflexivity.
  apply IHl.
  apply H.
  destruct b0.
  apply IHl.
  apply H.
  contradict a_neq_b0.
  reflexivity.
Defined.

Lemma pflist_splittable_2 : forall a b l, In b (splitlist a l) -> In (a :: b) l.
Proof.
  intros a b l inbal.
  induction l.
  inversion inbal.
  destruct a0.
  apply in_cons.
  assert (tmp1 : splitlist a (Bnil :: l) = splitlist a l).
  reflexivity.
  rewrite -> tmp1 in inbal.
  apply IHl.
  apply inbal.
  elim (list_eq_dec bool_dec b a0).
  intros b_eq_a0.
  rewrite <- b_eq_a0.
  induction a.
  induction b0.
  apply in_eq.
  apply in_cons.
  apply IHl.
  apply inbal.
  induction b0.
  apply in_cons.
  apply IHl.
  apply inbal.
  apply in_eq.
  intros b_neq_a0.
  apply in_cons.
  apply IHl.
  induction a.
  induction b0.
  assert (ininv:a0=b\/In b (splitlist true l)).
  apply in_inv.
  apply inbal.
  elim ininv.
  intros a0_eq_b.
  contradict b_neq_a0.
  symmetry.
  apply a0_eq_b.
  trivial.
  apply inbal.
  induction b0.
  apply inbal.
  assert (ininv:a0=b\/In b (splitlist false l)).
  apply in_inv.
  apply inbal.
  elim ininv.
  intros a_eq_b.
  contradict b_neq_a0.
  symmetry.
  auto.
  trivial.
Defined.

Lemma pflist_splittable :
  forall (l : list LB) (b : bool), pflist l -> pflist (splitlist b l).
Proof.
  unfold pflist.
  intros l b pf c d inc ind c_neq_d pref.
  assert (inc' : In (b :: c) l).
  apply pflist_splittable_2.
  apply inc.
  assert (ind' : In (b :: d) l).
  apply pflist_splittable_2.
  apply ind.
  assert (H : prefix (b :: c) (b :: d)).
  elim pref.
  intros x p.
  exists x.
  rewrite <- p.
  reflexivity.
  revert H.
  apply pf.
  apply inc'.
  apply ind'.
  contradict c_neq_d.
  inversion c_neq_d.
  reflexivity.
Defined.


Lemma dflist_splittable :
  forall (l : list LB) (b : bool), dflist l -> dflist (splitlist b l).
Proof.
  intros l b dl.
  induction dl.
  apply dflist_nil.
  destruct a.
  apply IHdl.
  elim (bool_dec b b1).
  intros beq.
  rewrite <- beq.
  assert (tmp1:splitlist b ((b :: a) :: b0) = a :: splitlist b b0).
  induction b.
  reflexivity.
  reflexivity.
  rewrite -> tmp1.
  apply dflist_cons.
  apply IHdl.
  contradict n.
  rewrite <- beq.
  apply pflist_splittable_2.
  apply n.
  intros b_neq_b1.
  assert (H:splitlist b ((b1 :: a) :: b0) = splitlist b b0).
  induction b.
  induction b1.
  contradict b_neq_b1.
  reflexivity.
  reflexivity.
  induction b1.
  reflexivity.
  contradict b_neq_b1.
  reflexivity.
  rewrite -> H.
  apply IHdl.
Defined.

Function list_maxlen (l : list LB) :=
  match l with
    | nil => 0%nat
    | x :: y => max (ll x) (list_maxlen y)
  end.

Lemma maxlen_split_1 : forall n1 n2 m1 m2, (n1<n2)%nat->(m1<m2)%nat->(max n1 m1<max n2 m2)%nat.
Proof.
  intros n1 n2 m1 m2 ln lm.
  elim (le_lt_dec n1 m1).
  intros n1_le_m1.
  elim (le_lt_dec n2 m2).
  intros n2_le_m2.
  rewrite -> Max.max_r.
  rewrite -> Max.max_r.
  auto.
  auto.
  auto.
  intros m2_lt_n2.
  rewrite -> Max.max_r.
  rewrite -> Max.max_l.
  apply (lt_trans _ m2).
  auto.
  auto.
  apply lt_le_weak.
  auto.
  auto.
  intros m1_lt_n1.
  rewrite -> Max.max_l.
  elim (le_lt_dec n2 m2).
  intros n2_le_m2.
  rewrite -> Max.max_r.
  apply (lt_le_trans _ n2).
  auto.
  auto.
  auto.
  intros m2_lt_n2.
  rewrite -> Max.max_l.
  auto.
  apply lt_le_weak.
  auto.
  apply lt_le_weak.
  auto.
Defined.

Lemma maxlen_split_3 : forall b l, list_maxlen l = 0%nat -> list_maxlen (splitlist b l) = 0%nat.
Proof.
  intros b l isnull.
  induction l.
  reflexivity.
  destruct a.
  apply IHl.
  apply isnull.


  inversion isnull.
  destruct (list_maxlen l).
  inversion H0.
  inversion H0.
Defined.  

Lemma maxlen_split : forall b l, list_maxlen l <> 0%nat ->
                                 (list_maxlen (splitlist b l) < list_maxlen l)%nat.
Proof.
  intros b l nn0.
  induction l.
  contradict nn0.
  reflexivity.
  assert(tmp1:list_maxlen(a::l) = max (ll a) (list_maxlen l)).
  reflexivity.
  rewrite -> tmp1.
  destruct a.
  assert (tmp2 : splitlist b (Bnil :: l) = splitlist b l).
  reflexivity.
  rewrite -> tmp2.
  assert (tmp3 : max (ll Bnil) (list_maxlen l) = list_maxlen l).
  reflexivity.
  rewrite -> tmp3.
  apply IHl.
  rewrite -> tmp1 in nn0.
  rewrite -> tmp3 in nn0.
  apply nn0.
  elim (bool_dec b b0).
  intros b_eq_b0.
  rewrite <- b_eq_b0.
  assert (tmp4 : splitlist b ((b :: a) :: l) = a :: splitlist b l).
  induction b.
  reflexivity.
  reflexivity.
  rewrite -> tmp4.
  assert (tmp5 : list_maxlen (a :: splitlist b l) = max (ll a) (list_maxlen (splitlist b l))).
  reflexivity.
  rewrite -> tmp5.
  elim (eq_nat_dec (list_maxlen l) 0%nat).
  intros isnull.
  rewrite -> isnull.
  rewrite -> Max.max_0_r.
  assert (isnull2 : list_maxlen (splitlist b l) = 0%nat).
  apply maxlen_split_3.
  auto.
  rewrite -> isnull2.
  rewrite -> Max.max_0_r.
  auto.
  intros nonnull.
  apply maxlen_split_1.
  auto.
  apply IHl.
  auto.
  intros b_neq_b0.
  assert (tmp2 : splitlist b ((b0 :: a) :: l) = splitlist b l).
  induction b.
  induction b0.
  contradict b_neq_b0.
  reflexivity.
  reflexivity.
  induction b0.
  reflexivity.
  contradict b_neq_b0.
  reflexivity.
  rewrite -> tmp2.
  elim (eq_nat_dec (list_maxlen l) 0%nat).
  intros isnull.
  assert (isnull2 : list_maxlen (splitlist b l) = 0%nat).
  apply maxlen_split_3.
  auto.
  rewrite -> isnull.
  rewrite -> isnull2.
  apply lt_0_Sn.
  intros nonnull.
  replace (list_maxlen (splitlist b l)) with (max 0 (list_maxlen (splitlist b l))).
  apply maxlen_split_1.
  apply lt_0_Sn.
  apply IHl.
  auto.
  rewrite -> Max.max_0_l.
  reflexivity.
Defined.

Function car {A} (a : A) (l : list A) : A :=
  match l with
    | nil => a
    | (x :: l) => x
  end.

Fixpoint take {A : Set} (n : nat) (l : list A) : list A :=
  match n with
  | 0 => []
  | S n_ => match l with
            | [] => []
            | x :: l_ => x :: take n_ l_
            end
  end.

Lemma prefix_take : forall {A : Set} (n : nat) (l : list A), prefix (take n l) l.
Proof.
  intro A;
  induction n as [|n IHn];
  [ intro;
    eexists;
    reflexivity
  | intro l;
    destruct l as [|x l IHl];
    [ eexists;
      reflexivity
    | simpl;
      apply prefix_cons;
      apply IHn]].
Qed.  

Lemma take_le_length : forall {A : Set} n (l : list A), (n <= ll l)%nat -> ll (take n l) = n.
Proof.
  intro A;
  induction n as [|n IHn];
  [ reflexivity
  | destruct l as [|x l];
    [ simpl;
      omega
    | simpl;
      intro xle;
      rewrite -> IHn;
      [ reflexivity
      | omega ]]].
Qed.  
  
Lemma take_lemma : forall (n : nat) (l : LB), ((n <= ll l)%nat) -> {l' | prefix l' l /\ ll l' = n}.
Proof.

  intros n l nle.
  exists (take n l).
  split.

  apply prefix_take.
  apply take_le_length.
  exact nle.
Defined.  

Lemma lexcut : forall a b, lex a b -> {x | lex (a ++ x) b /\ ll (a ++ x) = ll b} +
                                      {x | ll x = ll b /\ prefix x a /\ lex x b}.
Proof.
  intros a b lx.
  elim (le_lt_dec (ll a) (ll b)).
  intros alb.
  apply inl.
  exists (repeat (ll b - ll a)%nat false).
  split.

  refine ((fix f x y (llx : lex x y) (lxly : (ll x <= ll y)%nat) : lex (x ++ repeat (ll y - ll x) false) y :=
             match x as k return (k = x -> _) with
               | [] => fun eq => _
               | x' :: x'' => fun eq =>
                                match y as m return (y = m -> _) with
                                  | [] => fun eq0 => _
                                  | y' :: y'' => fun eq0 => _
                                end eq_refl
             end eq_refl) a b lx alb).
  replace ((ll y - ll Bnil)%nat) with (ll y).
  apply lex_0_x.
  apply minus_n_O.
  rewrite -> eq0 in lxly.
  rewrite <- eq in lxly.
  inversion lxly.
  elim (bool_dec x' y').
  intros xyeq.
  (*rewrite -> eq. *)
  rewrite <- xyeq.
  assert (ll_rec : (ll (x' :: y'') - ll (x' :: x'') = ll y'' - ll x'')%nat).
  auto.
  rewrite -> ll_rec.
  apply cdr_lex.
  apply f.
  apply (lex_cdr _ _ x').
  rewrite <- eq in llx.
  rewrite -> eq0 in llx.
  rewrite <- xyeq in llx.
  apply llx.
  rewrite <- eq in lxly.
  rewrite -> eq0 in lxly.
  apply le_S_n.
  auto.

  intros x_neq_y.
  destruct x'.
  destruct y'.
  contradict x_neq_y.
  reflexivity.
  rewrite -> eq0 in llx.
  rewrite <- eq in llx.
  inversion llx.
  destruct y'.
  (*rewrite -> eq.*)
  apply car_lex.
  contradict x_neq_y.
  reflexivity.

  refine ((fix f x y (lxly : (ll x <= ll y)%nat) : ll (x ++ repeat (ll y - ll x) false) = ll y :=
             match x as k return (k = x -> _) with
               | [] => fun eq0 => _
               | x' :: x'' => fun eq0 =>
                                match y as m return (y = m -> _) with
                                  | [] => fun eq => _
                                  | y' :: y'' => fun eq => _
                                end eq_refl
             end eq_refl) a b alb).
  rewrite -> app_nil_l.
  rewrite <- minus_n_O.
  apply rep_length.
  rewrite -> eq in lxly.
  rewrite <- eq0 in lxly.
  inversion lxly.
  assert (tmp1 : (ll (y' :: y'') - ll (x' :: x'') = ll y'' - ll x'')%nat).
  reflexivity.
  (*rewrite -> eq.*)
  rewrite -> tmp1.
  assert (tmp2 : ll ((x' :: x'') ++ repeat (ll y'' - ll x'') false) = S (ll (x'' ++ repeat (ll y'' - ll x'') false))).
  reflexivity.
  rewrite -> tmp2.
  assert (tmp3 : ll (y' :: y'') = S (ll y'')).
  reflexivity.
  rewrite -> tmp3.
  f_equal.
  apply f.
  rewrite -> eq in lxly.
  rewrite <- eq0 in lxly.
  apply le_S_n.
  auto.

  intros lba.
  apply inr.
  assert (H:{x | prefix x a /\ ll x = ll b}).
  apply take_lemma.
  apply lt_le_weak.
  apply lba.
  elim H.
  intros x n.
  elim n.
  intros pref llq.
  exists x.
  split.
  apply llq.
  split.
  apply pref.
  apply (lex_trans _ a).
  apply prefix_lex.
  apply pref.
  apply lx.
Defined.

Lemma vec_identity : forall {m}, {vc : vec _ m | forall q, Vnth vc q = q}.
Proof.
  (* todo: inefficient *)
  intros m.
  induction m.
  eexists Vnil.
  intros q. inversion q.
  elim IHm.
  intros x fq.
  exists (Vcons FinF1 _ (Vmap FinFS x)).
  intros q.
  dependent induction q.
  auto.
  assert (H : Vnth (Vcons FinF1 m (Vmap FinFS x)) (FinFS q) =
          Vnth (Vmap FinFS x) q).
  auto.
  rewrite -> H.
  replace (FinFS q) with (FinFS (Vnth x q)).
  apply nth_map.
  reflexivity.
  rewrite -> fq.
  reflexivity.
Defined.

Lemma toListLemma : forall {A} {n}
                           (f : vec A n) (m : A),
                      (exists o, m = Vnth f o) <-> In m (to_list f).
intros A n f m.
split.
intros ex.
elim ex.
intros o H.
dependent induction f.
inversion o.
dependent destruction o.
rewrite -> H.
apply or_introl.
auto.
apply or_intror.
assert(ex_o : exists o, m = Vnth f o).
exists o.
rewrite -> H.
auto.
apply (IHf m ex_o o).
rewrite -> H.
auto.
intros im.
induction f.
contradict im.
elim im.
intros h_eq_m.
exists (FinF1 (n:=n)).
rewrite <- h_eq_m.
auto.
intros im2.
assert (H : exists o : fin n, m = Vnth f o).
apply IHf.
compute.
trivial.
elim H.
intros x m_eq.
exists (FinFS x).
rewrite -> m_eq.
auto.
Defined.

Lemma assoc_lemma : forall {A} {n} (f : vec A n),
                      { l | forall m o, In (m, o) l <-> Vnth f m = o }.
intros A n f.
set (id := vec_identity (m := n)).
elim id.
intros x fq.
exists (to_list (Vmap (fun n => (n, Vnth f n)) x)).
intros m o.
split.
intros im.
assert (ex : exists q, (m, o) = Vnth (Vmap (fun n => (n, Vnth f n)) x) q).
apply toListLemma.
trivial.
elim ex.
intros x0 mo_eq.
assert (H : Vnth (Vmap (fun n0 : fin n => (n0, Vnth f n0)) x) x0 =
        ((Vnth x x0), Vnth f (Vnth x x0))).
apply (nth_map (fun n0 : fin n => (n0, Vnth f n0)) x).
reflexivity.
assert (H2 : (m, o) = (Vnth x x0, Vnth f (Vnth x x0))).
rewrite <- H. auto.
inversion H2.
reflexivity.

intros vnthfmo.
apply toListLemma.
exists m.
assert (H : Vnth (Vmap (fun n0 : fin n => (n0, Vnth f n0)) x) m =
            (Vnth x m, Vnth f (Vnth x m))).
apply (nth_map (fun n0 : fin n => (n0, Vnth f n0)) x).
reflexivity.
rewrite -> H.
rewrite -> (fq m).
rewrite -> vnthfmo.
reflexivity.
Defined.

Lemma pair_dec : forall (n0 : nat) (x0 y : fin n0 * nat), {x0 = y} + {x0 <> y}.
Proof.
  intros n0 x0 y.
  elim x0.
  elim y.
  intros a b c d.
  elim (eq_fin_dec a c).
  intros a_eq_c.
  elim (eq_nat_dec b d).
  intros b_eq_d.
  apply left.
  rewrite -> a_eq_c.
  rewrite -> b_eq_d.
  reflexivity.
  intros b_neq_d.
  apply right.
  contradict b_neq_d.
  inversion b_neq_d.
  auto.
  intros a_neq_c.
  apply right.
  contradict a_neq_c.
  inversion a_neq_c.
  auto.
Defined.

Fixpoint rmdup {n} (L : list (fin n * nat)) :=
  match L with
    | [] => []
    | x :: L' =>
      match L' with
        | [] => [x]
        | y :: L'' =>
          match (pair_dec _ x y) with
            | left _ => rmdup (L')
            | right _ => x :: rmdup (L')
          end
      end
  end.

Lemma rmdup_lemma_1 : forall {n} (a p : fin n*nat) {q} L,
                          (pair_dec n a p = left q -> rmdup (a :: p :: L) = rmdup (p :: L)).
Proof.
  intros n a p q L pd.
  assert (tmp2 : match (pair_dec _ a p) with
                   | left _ => rmdup (a :: L)
                   | right _ => a :: rmdup (p :: L)
                 end = rmdup (p :: L)).
  rewrite -> pd.
  rewrite <- q.
  reflexivity.
  assert (tmp3 : rmdup (a :: p :: L) =
                 match (pair_dec _ a p) with
                   | left _ => rmdup (p :: L)
                   | right _ => a :: rmdup (p :: L)
                 end).
  auto.
  rewrite <- tmp2.
  rewrite -> tmp3.
  rewrite <- q.
  reflexivity.
Defined.

Lemma rmdup_lemma_2 : forall {n} (a p : fin n*nat) {r} L,
                          pair_dec n a p = right r -> rmdup (a :: p :: L) = a :: rmdup (p :: L).
  intros n a p r L pd.
  assert (tmp2 : rmdup (a :: p :: L) = 
                 match (pair_dec _ a p) with
                   | left _ => rmdup (p :: L)
                   | right _ => a :: rmdup (p :: L)
                 end).
  auto.
  assert (tmp3 : match (pair_dec _ a p) with
                   | left _ => rmdup (p :: L)
                   | right _ => a :: rmdup (p :: L)
                 end = a :: rmdup (p :: L)).
  rewrite -> pd.
  reflexivity.
  rewrite -> tmp2.
  rewrite <- tmp3.
  rewrite -> pd.
  reflexivity.
Defined.

Lemma rmdup_eq : forall n L (x : fin n * nat), In x L <-> In x (rmdup L).
Proof.
  intros n.
  induction L.
  intros x.
  compute.
  auto.
  intros x.
  split.
  intros inxal.
  destruct L.
  compute.
  inversion inxal.
  auto.
  inversion H.
  induction (pair_dec _ a p) eqn:pd.
  assert (tmp1 : rmdup (a :: p :: L) = rmdup (p :: L)).
  apply (rmdup_lemma_1 _ _ _ pd).
  rewrite -> tmp1.
  apply IHL.
  inversion inxal.
  rewrite <- H.
  rewrite <- a0.
  apply in_eq.
  apply H.
  assert (tmp1 : rmdup (a :: p :: L) = a :: rmdup (p :: L)).
  apply (rmdup_lemma_2 _ _ _ pd).
  rewrite -> tmp1.
  inversion inxal.
  rewrite <- H.
  apply in_eq.
  apply in_cons.
  apply IHL.
  apply H.

  intros inrmdup.
  destruct L.
  apply inrmdup.
  induction (pair_dec _ a p) eqn:pd.
  assert (tmp1 : rmdup (a :: p :: L) = rmdup (p :: L)).
  apply (rmdup_lemma_1 _ _ _ pd).
  rewrite -> tmp1 in inrmdup.
  apply in_cons.
  apply IHL.
  apply inrmdup.
  assert (tmp1 : rmdup (a :: p :: L) = a :: rmdup (p :: L)).
  apply (rmdup_lemma_2 _ _ _ pd).
  rewrite -> tmp1 in inrmdup.
  inversion inrmdup.
  rewrite <- H.
  apply in_eq.
  apply in_cons.
  apply IHL.
  apply H.
Defined.

Lemma rmdup_lemma_3 : forall {n} (p : fin n*nat) L, {K | rmdup (p :: L) = p :: K}.
Proof.
  intros n p L.
  induction L.
  exists (nil(A:=fin n*nat)).
  reflexivity.
  induction (pair_dec _ p a) eqn:pa.
  assert (tmp1 : rmdup (p :: a :: L) = rmdup (a :: L)).
  apply (rmdup_lemma_1 _ _ _ pa).
  rewrite -> tmp1.
  rewrite <- a0.
  apply IHL.
  assert (tmp1 : rmdup (p :: a :: L) = p :: rmdup (a :: L)).
  apply (rmdup_lemma_2 _ _ _ pa).
  rewrite -> tmp1.
  exists (rmdup (a :: L)).
  reflexivity.
Defined.

Lemma dec_in_dec : forall {n} {A} (e : vec A n) (Q : A -> Prop) ,
                     (forall a, (Q a + (Q a -> False))) -> {n | Q (Vnth e n)} + ({n | Q (Vnth e n)} -> False).
Proof.
  intros n A e Q dc.
  dependent induction e.
  apply inr.
  intros nex.
  elim nex.
  intros x.
  inversion x.

  elim (dc h).
  intros Qh.
  apply inl.
  exists (FinF1(n:=n)).
  compute. auto.
  intros nQh.
  assert (prev : {n : fin n | Q (Vnth e n)} + ({n : fin n | Q (Vnth e n)} -> False)).
  apply IHe.
  apply dc.
  elim prev.
  intros n0ex.
  elim n0ex.
  intros x qex.
  apply inl.
  exists (FinFS x).
  replace (Vnth (Vcons h n e) (FinFS x)) with (Vnth e x).
  apply qex.
  reflexivity.
  intros nexn0.
  apply inr.
  intros nexn0n.
  elim nexn0n.
  intros x qx.
  dependent induction x.
  contradict nQh.
  apply qx.
  contradict nexn0.
  exists x.
  apply qx.
Defined.

(* todo: can this be unified with dec_in_dec? *)
Lemma dec_in_dec_set : forall {n} {A} (e : vec A n) (Q : A -> Type) ,
                     (forall a, (Q a + (Q a -> False))) -> {n' : fin n & (Q (Vnth e n'))} +
                                                           ({n' : fin n & Q (Vnth e n')} -> False).
Proof.
  intros n A e Q dc.
  dependent induction e.
  apply inr.
  intros nex.
  elim nex.
  intros x.
  inversion x.

  elim (dc h).
  intros Qh.
  apply inl.
  exists (FinF1(n:=n)).
  compute. auto.
  intros nQh.
  assert (prev : {n : fin n & Q (Vnth e n)} + ({n : fin n & Q (Vnth e n)} -> False)).
  apply IHe.
  apply dc.
  elim prev.
  intros n0ex.
  elim n0ex.
  intros x qex.
  apply inl.
  exists (FinFS x).
  replace (Vnth (Vcons h n e) (FinFS x)) with (Vnth e x).
  apply qex.
  reflexivity.
  intros nexn0.
  apply inr.
  intros nexn0n.
  elim nexn0n.
  intros x qx.
  dependent induction x.
  contradict nQh.
  apply qx.
  contradict nexn0.
  exists x.
  apply qx.
Defined.

Lemma dec_in_dec_all : forall {n} {A} (e : vec A n) (Q : A -> Prop) ,
                         (forall a, (Q a + (Q a -> False))) -> (forall n, Q (Vnth e n)) + ((forall n, Q (Vnth e n)) -> False).
Proof.
  intros.
  assert (dc: {n | ~ Q (Vnth e n)} + ({n | ~ Q (Vnth e n)} -> False)).
  apply (dec_in_dec _ (fun n => ~ Q n)).
  intros a.
  elim (X a).
  intros Qa.
  apply inr. auto.
  intros nQa.
  auto.
  elim dc.
  intros ex.
  apply inr.
  intros fa.
  elim ex.
  intros x nQ.
  apply nQ.
  apply fa.
  intros nex.
  apply inl.
  apply forall_notexists.
  intros a.
  apply X.
  apply nex.
Defined.

Lemma dec_ex : forall {n} (Q : fin n -> Prop), (forall a, (Q a + (Q a -> False))%type) -> ({n | Q n} + ({n | Q n} -> False))%type.
Proof.
  induction n.
  intros Q H.
  apply inr.  
  intros ex_n.
  elim ex_n.
  intros x.
  inversion x.
  intros Q Qdec.
  elim (Qdec FinF1).
  intros QFinF1.
  apply inl.
  exists (FinF1 (n:=n)).
  apply QFinF1.
  intros nQFinF1.
  set (Q' m := Q (FinFS m)).
  assert (H : {n : fin n | Q' n} + ({n : fin n | Q' n} -> False)).
  apply IHn.
  intros a.
  apply Qdec.
  elim H.
  intros ex.
  elim ex.
  intros m m_ex.
  apply inl.
  exists (FinFS m).
  apply m_ex.
  intros nex.
  apply inr.
  intros asmnex.
  elim asmnex.
  intros nn nnQ.
  dependent induction nn.
  apply nQFinF1.
  apply nnQ.
  contradict nex.
  exists nn.
  apply nnQ.
Defined.

Lemma min_dec_ex : forall {n} (e : vec LB n) (Q : fin n -> Prop),
                     (forall a, Q a + (Q a -> False)) -> {n | Q n} ->
                     {m | Q m /\ forall n, Q n -> lex (Vnth e m) (Vnth e n)}.
dependent induction e.
intros _q _r Q.
elim Q.
intros QQ.
inversion QQ.
intros Q H H0.
set (Q' m := Q (FinFS m)).

assert (IH : {m | Q' m} -> {m : fin n | Q' m /\ (forall n0 : fin n, Q' n0 -> lex (Vnth e m) (Vnth e n0))}).
intros exm.
apply IHe.
intros a.
apply H.
apply exm.

elim (H FinF1).
intros QFinF1.
assert(Q'exq : {m | Q' m} + ({m | Q' m} -> False)).
apply dec_ex.
intros a.
apply H.
elim Q'exq.
intros exm.
elim (IH exm).
intros m m_ex.
elim m_ex. intros m_ex_1 m_ex_2.
elim (dec_lex h (Vnth e m)).
intros islex.
exists (FinF1(n:=n)).
split.
apply QFinF1.
intros n0.
dependent destruction n0.
intros a. apply lex_refl.
intros QQ.
apply (lex_trans _ (Vnth e m)).
apply islex.
apply m_ex_2.
apply QQ.
intros nlex.
exists (FinFS m).
split.
apply m_ex_1.
intros n0 Qn0.
dependent destruction n0.
apply lex_total_lemma.
apply nlex.
apply m_ex_2.
apply Qn0.
intros nQ'.
exists (FinF1(n:=n)).
split.
apply QFinF1.
intros n0 Qn0.
dependent destruction n0.
apply lex_refl.
contradict nQ'.
exists n2.
apply Qn0.
intros nQFinF1.
elim (dec_ex Q').
intros n0ex.
elim (IH n0ex).
intros m mex.
elim mex. intros Q'm Q'mdec.
exists (FinFS m).
split.
apply Q'm.
intros n0 Qn0.
dependent destruction n0.
contradict nQFinF1.
apply Qn0.
apply Q'mdec.
apply Qn0.
intros nex.
contradict H0.
contradict nex.
elim nex.
intros x x_ex.
dependent destruction x.
contradict nQFinF1.
apply x_ex.
exists x.
apply x_ex.
intros a.
apply H.
Defined.

Lemma cons_inj : forall {A} {a c : A} b d, a :: b = c :: d -> (a = c /\ b = d).
Proof.
  intros A a c b d eq.
  inversion eq.
  auto.
Defined.

Lemma cons_rev_1 : forall {A} (a : A) b, rev (a :: b) = rev b ++ [a].
Proof.
  intros A a b.
  replace (a :: b) with ([a] ++ b).
  apply rev_app_distr.
  auto.
Defined.

Lemma cons_rev : forall {A} {a : A} {b c}, (rev (a :: b) ++ c) = (rev b) ++ (a :: c).
Proof.
  intros A a b c.
  rewrite -> cons_rev_1.
  replace ((rev b ++ [a]) ++ c) with (rev b ++ [a] ++ c).
  auto.
  apply app_assoc.
Defined.

(*Lemma array_set : forall {A} {n : nat} (a : vec A n) (b : fin n) (d : A),
                    {c | forall q, ((q = b) -> Vnth c q = d) /\ ((q <> b) -> Vnth c q = Vnth a q)}.
Proof.
  intros A n a b d.
  dependent induction a.
  inversion b.
  dependent induction b.
  exists (Vcons d n a).
  intros q.
  split.
  intros eq.
  rewrite eq.
  auto.
  intros neq.
  dependent induction q.
  contradict neq.
  auto.
  auto.
  assert (X : {c' : vec A n | forall q : fin n, (q = b -> Vnth c' q = d) /\ (q <> b -> Vnth c' q = Vnth a q)}).
  apply IHa.
  elim X.
  intros c' c'x.
  exists (Vcons h n c').
  intros q.
  split.
  intros eq.
  rewrite -> eq.
  apply c'x.
  auto.
  intros neq.
  dependent induction q.
  reflexivity.
  assert (neq2 : q <> b).
  contradict neq.
  f_equal.
  apply neq.
  apply c'x.
  apply neq2.
Defined. *)

Lemma forall_app : forall {A} (a b : list A) R, Forall R (a ++ b) -> Forall R a /\ Forall R b.
Proof.
  intros A a b R all.
  induction a.
  split.
  apply Forall_nil.
  rewrite <- app_nil_l.
  apply all.
  split.
  apply Forall_cons.
  inversion all.
  apply H1.
  apply IHa.
  inversion all.
  apply H2.
  apply IHa.
  inversion all.
  apply H2.
Defined.

Lemma app_forall : forall {A} (a b : list A) R, Forall R a -> Forall R b -> Forall R (a ++ b).
Proof.
  intros A a b R Ra Rb.
  induction a.
  apply Rb.
  replace ((a :: a0) ++ b) with (a :: a0 ++ b).
  apply Forall_cons.
  inversion Ra.
  apply H1.
  apply IHa.
  inversion Ra.
  apply H2.
  auto.
Defined.

Lemma forall_In : forall {A} (a : list A) (b : A) R, Forall R a -> In b a -> R b.
Proof.
  intros A a b R H H0.
  induction a.
  inversion H0.
  inversion H0.
  rewrite <- H1.
  inversion H.
  auto.
  inversion H.
  apply IHa.
  auto.
  auto.
Defined.

Lemma sorting_app : forall {A} (a b : list A) f, StronglySorted f (a ++ b) -> StronglySorted f a /\ StronglySorted f b.
Proof.
intros A a b f H.
induction a.
split.
apply SSorted_nil.
rewrite <- app_nil_l.
apply H.
split.
assert (H' : StronglySorted f (a :: (a0 ++ b))).
auto.
inversion H'.
apply SSorted_cons.
apply IHa.
apply H2.
apply (forall_app _ b).
auto.
apply IHa.
inversion H.
auto.
Defined.

Lemma sorting_rev_1 : forall {A} (a : A) l f,
                        StronglySorted f l -> Forall (fun x => f x a) l -> StronglySorted f (l ++ [a]).
Proof.
  intros A a l f ssfl all.
  induction l.
  unfold app.
  apply SSorted_cons.
  apply SSorted_nil.
  apply Forall_nil.
  replace ((a0 :: l) ++ [a]) with (a0 :: l ++ [a]).
  apply SSorted_cons.
  apply IHl.
  inversion ssfl.
  apply H1.
  inversion all.
  apply H2.
  inversion ssfl.
  apply app_forall.
  apply H2.
  apply Forall_cons.
  inversion all.
  apply H5.
  apply Forall_nil.
  auto.
Defined.

Lemma forall_rev : forall {A} (a : list A) R, Forall R a -> Forall R (rev a).
Proof.
  intros A a R Ra.
  induction a.
  apply Ra.
  rewrite -> cons_rev_1.
  apply app_forall.
  apply IHa.
  inversion Ra.
  auto.
  apply Forall_cons.
  inversion Ra.
  auto.
  apply Forall_nil.
Defined.

Lemma sorting_rev : forall {A} a f,
                      StronglySorted f a -> StronglySorted (A:=A) (fun x y => f y x) (rev a).
Proof.
  intros A a f.
  induction a.
  intros _.
  apply SSorted_nil.
  intros sk.
  elim sk.
  apply SSorted_nil.
  intros a1 l H H0 H1.
  rewrite -> cons_rev_1.
  apply sorting_rev_1.
  apply H0.
  apply forall_rev.
  apply H1.
Defined.

Lemma in_invert : forall {A} (a b : A) c, (a = b) \/ (In a c) -> In a (b :: c).
Proof.
  intros A a b c.
  intros vel.
  elim vel.
  intros eql.
  rewrite -> eql.
  apply in_eq.
  intros inin.
  apply in_cons.
  auto.
Defined.

Lemma lex_take : forall a b c d, prefix a c -> prefix b d -> ll a = ll b -> lex c d -> lex a b.
Proof.
  refine (fix f a b c d :=
            match (a, b, c, d) as S return ((a, b, c, d) = S -> _) with
                | (nil, _, _, _) => fun e => _
                | (xa :: a', nil, _, _) => fun e => _
                | (xa :: a', xb :: b', nil, _) => fun e => _
                | (xa :: a', xb :: b', xc :: c', nil) => fun e => _
                | (xa :: a', xb :: b', xc :: c', xd :: d') => fun eq => _
            end eq_refl).
inversion e.
intros _ _ _ _.
apply nil_lex.
inversion e.
intros _ _ Q.
inversion Q.
inversion e.
intros Q.
inversion Q.
inversion H.
inversion e.
intros _ Q.
inversion Q.
inversion H.
inversion eq.
intros pac pbd lleq lcd.
induction xa.
induction xb.
apply cdr_lex.
apply (f _ _ c' d').
inversion pac.
inversion H.
exists x.
reflexivity.
inversion pbd.
inversion H.
exists x.
reflexivity.
inversion lleq.
reflexivity.
induction xc.
induction xd.
apply (lex_cdr _ _ true).
apply lcd.
inversion pbd.
inversion H.
induction xd.
inversion pac.
inversion H.
apply (lex_cdr _ _ false).
apply lcd.
inversion pac.
inversion H.
inversion pbd.
inversion H4.
inversion lcd.
rewrite <- H12 in H8.
inversion H8.
rewrite <- H8 in H12.
rewrite <- H5 in H12.
inversion H12.
induction xb.
apply car_lex.
apply cdr_lex.
apply (f _ _ c' d').
inversion pac.
inversion H.
exists x.
reflexivity.
inversion pbd.
inversion H.
exists x.
reflexivity.
inversion lleq.
reflexivity.
induction xc.
inversion pac.
inversion H.
induction xd.
inversion pbd.
inversion H.
apply (lex_cdr _ _ false).
apply lcd.
Defined.

Lemma nullVec : forall (n : nat), {c : VecLB n | forall q, Vnth c q = Bnil}.
Proof.
  induction n.
  eexists Vnil.
  intros q.
  inversion q.
  elim IHn.
  intros x s.
  exists (Vcons Bnil _ x).
  intros q.
  dependent induction q.
  reflexivity.
  apply s.
Defined.

(* TODO: This is provided in newer standard libraries *)
Lemma of_nat_ext {p}{n} (h h' : p < n) : Fin.of_nat_lt h = Fin.of_nat_lt h'.
Proof.
 now rewrite (Peano_dec.le_unique _ _ h h').
Qed.

Lemma to_nat_inj {n} (p q : fin n) :
 proj1_sig (Fin.to_nat p) = proj1_sig (Fin.to_nat q) -> p = q.
Proof.
 intro H.
 rewrite <- (Fin.of_nat_to_nat_inv p), <- (Fin.of_nat_to_nat_inv q).
 destruct (Fin.to_nat p) as (np,hp), (Fin.to_nat q) as (nq,hq); simpl in *.
 revert hp hq. rewrite H. apply of_nat_ext.
Qed.

Lemma app_ll : forall {A} (a b c d : list A), a ++ b = c ++ d -> ll a = ll c -> a = c /\ b = d.
Proof.
  intros ? a b c.
  revert b.
  revert c.
  induction a.
  induction c.
  firstorder.
  intros ? ? ? Q.  
  inversion Q.

  destruct c.
  intros ? ? ? Q.
  inversion Q.
  intros b d appeq lleq.
  split.
  inversion appeq.
  f_equal.
  apply (IHa c b d).
  auto.
  inversion lleq.
  auto.
  apply (IHa c b d).
  inversion appeq.
  auto.
  inversion lleq.
  auto.
Qed.

Lemma app_ll_r : forall {A} (la las lb lbs : list A),
                   la ++ las = lb ++ lbs ->
                   ll las = ll lbs ->
                   la = lb /\ las = lbs.
Proof.
  intros A la las lb lbs apps lens.
  assert (lens' : ll la = ll lb).
  assert (ll la + ll las = ll lb + ll lbs).
  rewrite <- app_length.
  rewrite <- app_length.
  f_equal.
  auto.
  omega.
  apply app_ll.
  trivial.
  trivial.
Qed.

Lemma slice_list : forall {A} n (l : list A),
                     ({l1 : list A & {l2 : list A | l1 ++ l2 = l /\ ll l1 = n}} +
                      ({l1 : list A & {l2 : list A | l1 ++ l2 = l /\ ll l1 = n}} -> False))%type.
Proof.
  intros A n l.
  revert n.
  induction l as [|a l].
  intro n.
  destruct n.
  apply inl.
  exists (nil (A:=A)).
  exists (nil (A:=A)).
  auto.

  apply inr.
  intro Q.
  destruct Q as [l1 [l2 [appeq lleq]]].
  destruct l1.
  inversion lleq.
  inversion appeq.

  intro n.
  destruct n.
  apply inl.
  exists (nil (A:=A)).
  exists (a :: l).
  firstorder.

  destruct (IHl n) as [[l1 [l2 [appeq lleq]]]|no].
  apply inl.
  exists (a :: l1).
  exists l2.
  split.
  compute.
  compute in appeq.
  rewrite -> appeq.
  reflexivity.
  compute.
  compute in lleq.
  rewrite -> lleq.
  reflexivity.

  apply inr.
  intro Q.
  destruct Q as [l1 [l2 [k j]]].
  destruct l1 as [|q l1].
  inversion j.
  contradict no.
  exists l1.
  exists l2.
  split.
  inversion k.
  reflexivity.
  inversion j.
  reflexivity.
Qed.

Lemma slice_list_le : forall {A} n (l : list A),
                        n <= ll l -> {l1 : list A & {l2 : list A | l1 ++ l2 = l /\ ll l1 = n}}.
Proof.
  intros A.
  refine (fix f n l n_le_l {struct n} :=
            match n as N return (n=N->_) with
              | 0 => fun eqN => _
              | (S n') => fun eqN => match l as L return (l=L->_) with
                                       | [] => fun eqL => _
                                       | (x :: l') => fun eqL => _
                                     end eq_refl
            end eq_refl).

  exists (nil (A:=A)).
  exists l.
  auto.

  rewrite -> eqL in n_le_l.
  unfold ll in n_le_l.
  omega.

  destruct (f n' l') as [l1 [l2 [lapp lll]]].
  rewrite -> eqL in n_le_l.
  rewrite -> eqN in n_le_l.
  compute in n_le_l.
  compute.
  omega.
  exists (x :: l1).
  exists l2.
  split.
  rewrite <- lapp.
  reflexivity.
  unfold ll.
  unfold ll in lll.
  omega.
Qed.

Lemma list_tail_destruct : forall {A} (L : list A), (L = nil) + {L' : list A & {m : A | L = L' ++ [m]}}.
Proof.
  intros A.
  induction L.
  auto.
  apply inr.
  destruct IHL.
  rewrite -> e.
  exists L.
  exists a.
  rewrite -> e.
  reflexivity.
  destruct s as [L' [m Lapp]].
  exists (a :: L').
  exists m.
  compute.
  compute in Lapp.
  rewrite <- Lapp.
  reflexivity.
Qed.

Theorem rev_ind_computational : forall {A} (P:list A -> Type),
                                  P [] ->
                                  (forall (x:A) (l:list A), P l -> P (l ++ [x])) -> forall l:list A, P l.
Proof.
  intros A P H' X' l'.
  refine ((fix f n l (n_l : n = ll l) H X := 
             match n as N return (n=N->_) with
               | 0 => fun eq => _
               | (S n') => fun eq => _
             end eq_refl) (ll l') l' eq_refl H' X').
  destruct l.
  trivial.
  rewrite -> eq in n_l.
  inversion n_l.
  destruct (list_tail_destruct l) as [isnil | [l'' [m' mapp]]].
  rewrite -> isnil in n_l.
  rewrite -> eq in n_l.
  inversion n_l.
  rewrite -> mapp.
  apply X.
  apply (f n').
  assert (S n' = ll l'' + 1).
  replace 1 with (ll [m']).
  rewrite <- eq.
  rewrite -> n_l.
  rewrite -> mapp.
  apply app_length.
  reflexivity.
  omega.
  trivial.
  trivial.
Qed.

Theorem StrongInduction : forall P, (forall n, (forall x, x < n -> P x) -> P n) -> forall n, P n.
Proof.
  intros P trans n.
  apply trans.

  induction n.
  intros x x0.
  omega.

  intros x x0.
  destruct (eq_nat_dec x n) as [e|e].
  rewrite -> e.
  apply trans.
  auto.
  assert (x < n).
  omega.
  apply IHn.
  auto.
Qed.


Lemma to_list_inj : forall {A} {m : nat} (t u : vec A m), to_list t = to_list u -> t = u.
Proof.
  intros A m t u eq.
  dependent induction m.
  dependent destruction t.
  dependent destruction u.
  reflexivity.
  dependent destruction t.
  dependent destruction u.
  replace h with h0.
  replace t with u.
  reflexivity.
  assert (H0 : to_list (Vcons h m t) = h :: to_list t).
  reflexivity.
  assert (H1: to_list (Vcons h0 m u) = h0 :: to_list u).
  reflexivity.
  apply IHm.
  rewrite -> H1 in eq.
  rewrite -> H0 in eq.
  inversion eq.
  reflexivity.
  assert (H0 : to_list (Vcons h m t) = h :: to_list t).
  reflexivity.
  assert (H1: to_list (Vcons h0 m u) = h0 :: to_list u).
  reflexivity.
  rewrite -> H1 in eq.
  rewrite -> H0 in eq. 
  inversion eq.
  reflexivity.
Qed.

Theorem ListToByte : forall l, lb l = 8 -> {X : Byte | to_list X = l}.
Proof.
  intros l l8.
  assert (Y : {X : vec bool (lb l) | to_list X = l}).
  exists (of_list l).
  do 9 (destruct l; auto).
  inversion l8.
  rewrite -> l8 in Y.
  apply Y.
Qed.

Lemma to_list_length : forall {A} {n} (v : vec A n), ll (to_list v) = n.
Proof.
  intros A n.
  dependent induction n.
  intro v.
  dependent destruction v.
  auto.
  intro v.
  dependent destruction v.
  compute.
  compute in IHn.
  rewrite -> IHn.
  reflexivity.
Qed.

Lemma ll_cons_s : forall {A} (c : A) (l : list A), ll (c :: l) = S (ll l).
Proof.
  auto.
Qed.

Lemma vec_eq_dec : forall {A} {n : nat} (a b : vec A n), (forall (c d : A), ({c = d} + {c <> d})%type) ->
                                                         ((a = b) + (a = b -> False))%type.
Proof.
  intro A.
  dependent induction n.
  intros a b.
  dependent destruction a.
  dependent destruction b.
  auto.

  intros a b.
  dependent destruction a.
  dependent destruction b.

  intro eqdec.
  destruct (eqdec h h0) as [yes | no].
  destruct (IHn a b eqdec) as [yes2 | no].

  rewrite -> yes.
  rewrite -> yes2.
  auto.

  apply inr.
  intro Q.
  dependent induction Q.
  contradict no.
  reflexivity.

  apply inr.
  intro Q.
  dependent induction Q.
  contradict no.
  reflexivity.
Defined.


Lemma app_cancel_l : forall {A} (a b c : list A),
                    a ++ b = a ++ c -> b = c.
Proof.
  intros A. 
  induction a as [|x a IHa].
  auto.
  intros b c app.
  apply IHa.
  rewrite <- app_comm_cons in app.
  rewrite <- app_comm_cons in app.
  inversion app.
  auto.
Qed.

Lemma nth_error_nil : forall {A} n, nth_error (@nil A) n = error.
Proof.
  destruct n; reflexivity.
Qed.

Lemma nth_extend : forall {A} (b c : list A) n, n < ll b -> nth_error b n = nth_error (b ++ c) n.
Proof.
  induction b.
  simpl; intros; omega.
  intros c n nl.
  rewrite <- app_comm_cons.
  destruct n.
  reflexivity.
  simpl.
  apply IHb.
  simpl in nl.
  omega.
Qed.

Lemma nth_split : forall {A} l n (k : A),
                    nth_error l n = Some k <-> exists l' l'', ll l' = n /\ l = l' ++ [k] ++ l''.
Proof.
  intros A l n k;
  split;
  [ revert l n;
    refine (fix f l n (isk : nth_error l n = Some k) {struct l} :=
              match l as L return (l=L->_) with
                | [] => fun eqL => _
                | (x :: xs) => fun eqL => match n as N return (n=N->_) with
                                            | 0 => fun eqN => _
                                            | S n' => fun eqN => _
                                          end eq_refl
              end eq_refl);
    [ rewrite -> eqL in isk; destruct n; inversion isk
    | exists (@nil A);
      exists xs;
      split;
      [ reflexivity
      | simpl;
        rewrite -> eqL in isk;
        rewrite -> eqN in isk;
        inversion isk;
        reflexivity ]
    | rewrite -> eqL in isk;
      rewrite -> eqN in isk;
      simpl in isk;
      destruct (f _ _ isk) as [l_ [l__ [lll_ xxx_]]];
      exists (x :: l_);
      exists l__;
      split;
      [ simpl; omega
      | rewrite -> xxx_;
        reflexivity]]
  | revert l n;
    refine (fix f l n (x : (exists l' l'' : list A, ll l' = n /\ l = l' ++ [k] ++ l'')) {struct l} :=
              match l as L return (l=L->_) with
                | [] => fun eqL => _
                | (x_ :: xs) => fun eqL => match n as N return (n=N->_) with
                                           | 0 => fun eqN => _
                                           | S n' => fun eqN => _
                                           end eq_refl
              end eq_refl);
  [ destruct x as [l' [l'' [lll' lapp]]];
      rewrite -> eqL in lapp;
      destruct l'; inversion lapp
    | destruct x as [l' [l'' [lll' lapp]]];
      rewrite -> eqL in lapp;
      rewrite -> lapp;
      destruct l';
      [ reflexivity
      | rewrite -> eqN in lll';
        inversion lll' ]
    | destruct x as [l' [l'' [lll' lapp]]];
      destruct l' as [|a l'];
      [ rewrite -> eqN in lll';
        inversion lll'
      | simpl;
        apply f;
        exists l';
        exists l'';
        split;
        [ simpl in lll'; omega
        | rewrite -> eqL in lapp;
          inversion lapp;
          trivial ]]]].
Qed.

Lemma nth_error_lt : forall {A} l n (k : A), nth_error l n = Some k -> n < ll l.
Proof.
  induction l as [|x l IHl].
  destruct n; intros ? Q; inversion Q.
  destruct n.
  intros; simpl; omega.
  intros k nerr.
  simpl in nerr.
  simpl.
  assert (n < ll l).
  eapply IHl.
  eauto.
  omega.
Qed.

Lemma nth_error_nth : forall {A} n l (q k : A), nth_error l n = Some k -> nth n l q = k.
Proof.
  intros A n l q k.
  revert n l.
  refine (fix f n l {struct n} :=
            match l as L return (l=L->_) with
              | [] => fun eqL => _
              | (x :: l') => fun eqL =>
                               match n as N return (n=N->_) with
                                 | 0 => fun eqN => _
                                 | S n' => fun eqN => _
                               end eq_refl
            end eq_refl).
  intro nerr; destruct n; inversion nerr.
  intro Q; inversion Q; reflexivity.
  simpl; apply f.
Qed.

(* NTHLAST1 *)				     
Inductive nthLast {A : Set}
 : forall (n : nat) (L : list A) (a : A), Prop :=
| makeNthLast : forall L M a, nthLast (ll (a :: M)) (L ++ a :: M) a.
(* NTHLAST2 *)


Lemma nthNthLast : forall {A : Set} (l : list A) (a b : A) (n : nat),
                     nth n (rev l) a = b -> n < ll l ->
                     nthLast (S n) l b.
Proof.
  intros A.
  apply (rev_ind (fun l => forall (a b : A) (n : nat),
   nth n (rev l) a = b -> n < ll l -> nthLast (S n) l b)).

  simpl. intros. omega.

  intros x l IHl.
  intros a b n nthn nll.
  rewrite -> rev_app_distr in nthn.
  destruct n as [|n].
  simpl in nthn.
  rewrite <- nthn.
  apply (makeNthLast l [] x).

  assert (Q : nthLast (S n) l b).
  eapply IHl.
  simpl in nthn.
  exact nthn.
  rewrite -> app_length in nll.
  simpl in nll.
  omega.
  inversion Q as [B C D E F G].
  assert (K1 : S (S (ll C)) = S (ll (C ++ [x]))).
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> K1.
  rewrite <- app_assoc.
  rewrite <- app_comm_cons.
  constructor.
Qed.

Lemma nthLastNth : forall {A : Set} (l : list A) (a b : A) (n : nat),
                     nthLast (S n) l b -> nth n (rev l) a = b.
Proof.
  intros A l a b n nlst.
  inversion nlst.
  rewrite -> rev_nth.
  rewrite -> app_length.
  simpl.
  assert (K0 : ll L + S (ll M) - S (ll M) = ll L).
  omega.
  rewrite -> K0.
  assert (K1 : b :: M = [b] ++ M).
  reflexivity.
  rewrite -> K1.
  rewrite -> app_assoc.
  rewrite -> app_nth1.
  assert (K2 : ll L = ll (L ++ [b]) - 1).
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> K2.
  rewrite <- rev_nth.
  rewrite -> rev_app_distr.
  reflexivity.
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> app_length.
  simpl.
  omega.
  rewrite -> app_length.
  simpl.
  omega.
Qed.
