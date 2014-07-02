Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qfield.
Require Import Coq.PArith.BinPos.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import NPeano.

Require Import DeflateNotations.
Require Import Prefix.
Require Import Combi.

Local Open Scope nat.

Fixpoint e2 (x : nat) : positive :=
  match x with
      | 0 => xH
      | S m => xO (e2 m)
  end.

Local Open Scope positive_scope.

Theorem e2_mul : forall (a : nat) (b : nat), (e2 a) * (e2 b) = e2 (a + b).
Proof.
  intros.
  induction a.
  replace (e2 0) with BinNums.xH.
  replace (0 + b)%nat with b.
  apply Pos.mul_1_l.
  auto.
  auto.
  replace (S a + b)%nat with (S (a + b))%nat.
  replace (e2 (S a)) with (BinPos.Pos.mul 2 (e2 (a))).
  replace (e2 (S (a + b))) with (BinPos.Pos.mul 2 (e2 (a + b))).
  apply eq_sym.
  replace (e2 (a + b)) with (BinPos.Pos.mul (e2 a) (e2 b)).
  apply BinPos.Pos.mul_assoc.
  auto.
  auto.
  auto.
Defined.

(* todo: gibts vmtl woanders *)
Definition kraft_f_1 : forall (m n : nat), (m - n = 0 -> m <= n)%nat.
refine (fix k m n : (m - n = 0 -> m <= n)%nat :=
          match m,n with
              (*| 0%nat, 0%nat => _*)
              | 0%nat, n => _
              | (S m), (S n) => _
              | (S m), 0%nat => _
          end
).
intros q. apply le_0_n.
intros q. inversion q.
intros a.
apply le_n_S.
apply k.
assert (H : (S m - S n)%nat = (m - n)%nat).
apply Nat.sub_succ.
rewrite <- H.
trivial.
Defined.

Local Open Scope Q_scope.

Function kraft_list (l : list LB) : Q :=
  foldlist 0 (fun x y => Qplus (1 # (e2 (ll x))) y) l.

Lemma kraft_pflist_split : forall l, pflist l -> (In Bnil l +
  (kraft_list (splitlist true l) + kraft_list (splitlist false l) ==
  (2 # 1) * kraft_list l))%type.
Proof.
  intros l pfl.
  induction l.
  apply inr.
  reflexivity.
  induction a.
  apply inl.
  apply in_eq.
  assert (H:In Bnil l + (kraft_list (splitlist true l) + kraft_list (splitlist false l) ==
                       (2 # 1) * kraft_list l)).
  apply IHl.
  unfold pflist.
  intros x y z t u.
  apply pfl.
  apply in_cons.
  auto.
  apply in_cons.
  auto.
  auto.
  elim H.
  intros innil.
  apply inl.
  apply in_cons.
  auto.
  intros kraftind.
  apply inr.
  induction a.
  assert(tmp1:kraft_list (splitlist true ((true :: a0) :: l)) =
              (1 # (e2 (ll a0))) + kraft_list (splitlist true l)).
  reflexivity.
  rewrite -> tmp1.
  assert(tmp2: splitlist false ((true :: a0) :: l) = splitlist false l).
  reflexivity.
  rewrite -> tmp2.
  assert(tmp3:kraft_list ((true :: a0) :: l)=(1 # (e2 (ll (true :: a0))))+kraft_list l).
  reflexivity.
  rewrite -> tmp3.
  assert(tmp4:(2 # 1) * ((1 # e2 (ll (true :: a0))) + kraft_list l) ==
              (2 # 1) * (1 # e2 (ll (true :: a0))) + (2 # 1) * (kraft_list l)).
  ring.
  rewrite -> tmp4.
  assert (tmp5:(1 # e2 (ll a0)) + kraft_list (splitlist true l) +
               kraft_list (splitlist false l) ==
               (1 # e2 (ll a0)) + (kraft_list (splitlist true l) +
                                   kraft_list (splitlist false l))).
  ring.
  rewrite -> tmp5.
  rewrite -> kraftind.
  assert (tmp1337:(1 # e2 (ll (true :: a0))) = (1#2)*(1#e2(ll(a0)))).
  reflexivity.
  rewrite -> tmp1337.
  ring.
  assert(tmp1:kraft_list (splitlist false ((false :: a0) :: l)) =
              (1 # (e2 (ll a0))) + kraft_list (splitlist false l)).
  reflexivity.
  rewrite -> tmp1.
  assert(tmp2: splitlist true ((false :: a0) :: l) = splitlist true l).
  reflexivity.
  rewrite -> tmp2.
  assert(tmp3:kraft_list ((false :: a0) :: l)=(1 # (e2 (ll (false :: a0))))+kraft_list l).
  reflexivity.
  rewrite -> tmp3.
  assert(tmp4:(2 # 1) * ((1 # e2 (ll (false :: a0))) + kraft_list l) ==
              (2 # 1) * (1 # e2 (ll (false :: a0))) + (2 # 1) * (kraft_list l)).
  ring.
  rewrite -> tmp4.
  assert (tmp5:kraft_list (splitlist true l) + ((1 # e2 (ll a0)) + 
               kraft_list (splitlist false l)) ==
               (1 # e2 (ll a0)) + (kraft_list (splitlist true l) +
                                   kraft_list (splitlist false l))).
  ring.
  rewrite -> tmp5.
  rewrite -> kraftind.
  assert (tmp1337:(1 # e2 (ll (false :: a0))) = (1#2)*(1#e2(ll(a0)))).
  reflexivity.
  rewrite -> tmp1337.
  ring.
Defined.

Lemma kraft_pflist : forall l, dflist l -> pflist l -> kraft_list l <= 1.
Proof.
  intros l df pf.
  refine ((fix f n l df pf (eq : (list_maxlen l <= n)%nat) :=
             match n as m return ((m = n) -> _) with
               | 0%nat => (fun eq => _)
               | (S n') => (fun eq => _)
             end eq_refl) (S (list_maxlen l)) l df pf _).
  rewrite <- eq in eq0.
  inversion eq0.
  induction l.
  compute.
  intros Q.
  inversion Q.
  inversion H0.
  destruct a.
  destruct l.  
  apply Qle_refl.
  destruct l.
  inversion df.
  contradict H4.
  apply in_eq.
  assert (H2:max (ll Bnil) (list_maxlen ((b :: l) :: l1))=(list_maxlen ((b :: l) :: l1))).
  apply Max.max_0_l.
  rewrite -> H2 in H1.
  inversion H1.
  destruct (list_maxlen l1).
  inversion H3.
  inversion H3.
  inversion H1.
  destruct (list_maxlen l).
  inversion H2.
  inversion H2.

  elim (kraft_pflist_split l pf).
  intros innil.
  destruct l.
  inversion innil.
  destruct l.
  destruct l1.
  compute.
  intros Q.
  inversion Q.
  assert (q1 : In l (Bnil :: l :: l1)).
  apply in_cons.
  apply in_eq.
  assert (q2 : Bnil <> l).
  inversion df.
  contradict H2.
  rewrite <- H2.
  apply in_eq.
  assert (ispref : prefix Bnil l).
  exists l.
  apply app_nil_l.
  contradict ispref.
  apply pf.
  apply innil.
  apply q1.
  apply q2.
  assert(q1:In(b :: l)((b :: l) :: l1)).
  apply in_eq.
  assert (ispref : prefix Bnil (b :: l)).
  exists (b :: l).
  apply app_nil_l.
  contradict ispref.
  apply pf.
  apply innil.
  apply q1.
  intros Q.
  inversion Q.
  intros rc.
  assert(tmp1:(1#2)*(kraft_list (splitlist true l)) + (1#2)*kraft_list (splitlist false l) ==
              kraft_list l).
  assert(tmp2:(1#2)*(kraft_list (splitlist true l)) + (1#2)*(kraft_list (splitlist false l)) ==
              (1#2)*(kraft_list (splitlist true l) + kraft_list (splitlist false l))).
  ring.
  rewrite -> tmp2.
  rewrite -> rc.
  ring.
  rewrite <- tmp1.
  assert (tmp2 : 1 == (1 # 2) + (1 # 2)).
  ring.
  rewrite -> tmp2.
  assert (rec : forall b, kraft_list (splitlist b l) <= 1).
  intros b.
  apply (f n').
  apply dflist_splittable.
  auto.
  apply pflist_splittable.
  auto.
  elim (eq_nat_dec (list_maxlen (splitlist b l)) 0).
  intros iseq.
  rewrite -> iseq.
  apply le_0_n.
  intros isneq.
  apply lt_n_Sm_le.
  rewrite -> eq.
  apply (lt_le_trans _ (list_maxlen l)).
  apply maxlen_split.
  contradict isneq.
  apply maxlen_split_3.
  apply isneq.
  auto.
  apply Qplus_le_compat.
  assert (tmp3 : 1 # 2 == (1 # 2) * 1).
  ring.
  rewrite -> tmp3.
  apply Qmult_le_l.
  reflexivity.
  apply rec.
  assert (tmp3 : 1 # 2 == (1 # 2) * 1).
  ring.
  rewrite -> tmp3.
  apply Qmult_le_l.
  reflexivity.
  apply rec.
  auto.
Defined.

Lemma kraft_pflist_sharp_2 : forall l, 0 <= kraft_list l.
Proof.
  induction l.
  compute.
  intros Q.
  inversion Q.
  assert (l' : kraft_list (a :: l) == (1 # (e2 (ll a))) + kraft_list l).
  reflexivity.
  rewrite -> l'.
  assert (l'' : 0 == 0 + 0).
  ring.
  rewrite l''.
  apply Qplus_le_compat.
  compute.
  intros Q.
  inversion Q.
  apply IHl.
Defined.

Lemma kraft_pflist_sharp_1 : forall l, dflist l -> pflist l ->
                                       (forall m, dflist (m :: l) -> pflist (m :: l) -> False)
                                       -> kraft_list l <> 0.
Proof.
  intros l H H0 H1 k0.
  destruct l.
  apply (H1 nil).
  apply dflist_cons.
  auto.
  auto.
  intros a b ina inb anb pf.
  inversion ina.
  inversion inb.
  contradict anb.
  rewrite <- H2.
  apply H3.
  inversion H3.
  inversion H2.
  destruct l.
  destruct l0.
  inversion k0.
  destruct l.
  inversion H.
  contradict H5.
  apply in_eq.
  assert (pref : prefix Bnil (b :: l)).
  exists (b :: l).
  apply app_nil_l.
  contradict pref.
  apply H0.
  apply in_eq.
  apply in_cons.
  apply in_eq.
  intros Q.
  inversion Q.
  assert (k1 : 0 == kraft_list ((b :: l) :: l0)).
  rewrite -> k0.
  reflexivity.
  contradict k1.
  apply Qlt_not_eq.
  assert (kg' : kraft_list ((b :: l) :: l0) == (1 # (e2 (S (ll l)))) + kraft_list l0).
  reflexivity.
  rewrite -> kg'.
  assert (kg'' : 0 == 0 + 0).
  ring.
  rewrite -> kg''.
  apply Qplus_lt_le_compat.
  reflexivity.
  apply kraft_pflist_sharp_2.
Defined.

Lemma kraft_pflist_sharp : forall l, dflist l -> pflist l ->
                                     (forall m, dflist (m :: l) -> pflist (m :: l) -> False)
                                     -> kraft_list l == 1.
Proof.
  intros l df pf fm.
  refine ((fix f n l (le : (list_maxlen l <= n)%nat) df pf fm :=
             match n as m return (n = m -> _) with
               | 0%nat => fun eq => _
               | S n' => fun eq => _
             end eq_refl)
            (list_maxlen l) l (le_refl (list_maxlen l)) df pf fm).
  rewrite -> eq in le.
  induction l.
  assert (Q:False).
  apply (fm nil).
  apply dflist_cons.
  auto.
  auto.
  unfold pflist.
  intros a b ina inb aneqb.
  inversion ina.
  inversion inb.
  contradict aneqb.
  rewrite <- H.
  auto.
  inversion H0.
  inversion H.
  contradict Q.
  inversion le.
  destruct a.  
  destruct l.
  reflexivity.
  destruct l.
  inversion df.
  contradict H3.
  apply in_eq.
  assert (ispf : prefix Bnil (b :: l)).
  exists (b :: l).
  apply app_nil_l.
  contradict ispf.
  apply pf.
  apply in_eq.
  apply in_cons.
  apply in_eq.
  intros Q.
  inversion Q.
  inversion H0.
  destruct (list_maxlen l).
  inversion H1.
  inversion H1.

  assert(indec : {In nil l}+{~ In nil l}).
  apply in_dec.
  apply list_eq_dec.
  apply bool_dec.
  elim indec.
  intros innil.
  destruct l.
  inversion innil.
  destruct l.
  destruct l1.
  reflexivity.
  destruct l.
  inversion df.
  contradict H2.
  apply in_eq.
  assert (pref : prefix Bnil (b :: l)).
  exists (b :: l).
  auto.
  contradict pref.
  apply pf.
  apply in_eq.
  apply in_cons.
  apply in_eq.
  intros Q.
  inversion Q.
  assert (pref : prefix Bnil (b :: l)).
  exists (b :: l).
  auto.
  contradict pref.
  apply pf.
  apply innil.
  apply in_eq.
  intros Q.
  inversion Q.
  intros nin.
  elim (kraft_pflist_split l pf).
  intros isin.
  contradict nin.
  auto.
  intros kl.
  apply (Qmult_inj_l _ _ (2 # 1)).
  compute.
  intros Q.
  inversion Q.
  rewrite <- kl.

  assert (H_bl : forall bl, kraft_list (splitlist bl l) == 1).
  intros bl.
  apply (f n').
  apply le_S_n.
  apply (le_trans _ (list_maxlen l)).
  apply maxlen_split.
  destruct l.
  intros _.
  apply (fm nil).
  apply dflist_cons.
  apply dflist_nil.
  apply nin.
  intros a b ina inb anb.
  inversion ina.
  inversion inb.
  contradict anb.
  rewrite <- H.
  apply H0.
  inversion H0.
  inversion H.

  destruct l.
  contradict nin.
  apply in_eq.
  intros Q.
  inversion Q.
  destruct(list_maxlen l1).
  inversion H0.
  inversion H0.
  rewrite <- eq.
  auto.
  apply dflist_splittable.
  auto.
  apply pflist_splittable.
  auto.
  intros m d p.
  apply (fm (bl :: m)).
  inversion d.
  apply dflist_cons.
  apply df.
  contradict H2.
  apply pflist_splittable_3.
  apply H2.
  intros a b ina inb anb.

  elim (list_eq_dec bool_dec a (bl :: m)).

  intros a_eq.
  rewrite a_eq.
  inversion inb.
  contradict H.
  rewrite <- a_eq.
  apply anb.
  destruct b.
  auto.
  intros ispref.
  inversion ispref.
  inversion H0.
  assert (ispref2 : prefix m b0).
  exists x.
  apply H3.
  contradict ispref2.
  apply p.
  apply in_eq.
  apply in_cons.
  apply pflist_splittable_3.
  rewrite -> H2.
  auto.
  rewrite -> a_eq in anb.
  rewrite <- H2 in anb.
  intros q.
  contradict anb.
  rewrite <- q.
  reflexivity.
  intros a_neq.
  destruct a.
  contradict nin.
  assert (ininv : (bl :: m) = Bnil \/ In Bnil l).
  apply in_inv.
  auto.
  elim ininv.
  intros Q.
  inversion Q.
  trivial.
  elim (list_eq_dec bool_dec b (bl :: m)).
  intros beq.
  rewrite -> beq.
  intros pref.
  inversion pref.
  inversion H.
  assert (pref2 : prefix a m).
  exists x.
  apply H2.
  contradict pref2.
  apply p.
  rewrite -> H1 in ina.
  inversion ina.
  contradict a_neq.
  rewrite -> H1.
  auto.
  apply in_cons.
  apply pflist_splittable_3.
  apply H0.
  apply in_eq.
  rewrite -> H1 in a_neq.
  contradict a_neq.
  rewrite <- a_neq.
  reflexivity.
  intros b_neq.
  assert (ininv : (bl :: m) = (b0 :: a) \/ In (b0 :: a) l).
  apply in_inv.
  auto.
  elim ininv.
  intros iseq.
  contradict a_neq.
  auto.
  intros isinl.
  assert (ininv2 : (bl :: m) = b \/ In b l).
  apply in_inv.
  auto.
  elim ininv2.
  intros iseq.
  contradict b_neq.
  auto.
  intros isinl2.
  apply pf.
  auto.
  auto.
  auto.

  rewrite -> H_bl.
  rewrite -> H_bl.
  reflexivity.
Defined.
