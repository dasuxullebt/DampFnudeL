Require Import List.
Require Import BinNat.
Require Import Shorthand.
Require Import Program.
Require Import Omega.

Open Scope Z_scope.

Inductive Closed : Z -> Z -> list Z -> list Z -> Set :=
| ClosedCons1 : forall min max, Closed min max (min :: nil) (max :: nil)
| ClosedCons2 : forall min a2 a3 max L R,
                  Closed (1 + a2) max ((1 + a2) :: L) (a3 :: R) ->
                  Closed min max (min :: (1 + a2) :: L) (a2 :: a3 :: R).

Lemma Zle_dec : forall n m, {n <= m} + {~ n <= m}.
Proof.  
  intros a b;
  destruct (a ?= b) eqn:ab;
  solve [ apply left;
          apply (proj1 (Z.compare_le_iff a b));
          intro Q;
          rewrite -> ab in Q;
          inversion Q
        | apply right;
          intro Q;
            apply (proj2 (Z.compare_le_iff a b));
            [ exact Q
            | exact ab ]].
Defined.

Lemma ClosedTable : forall n min max L R,
                      Closed min max L R ->
                      min <= n <= max ->
                      {m : nat | (m < ll L)%nat /\
                                 forall d1 d2,                                   
                                   nth m L d1 <= n <= nth m R d2}.
Proof.
  intros n min max L R cl.
  induction cl;
  [ intro q;
    exists 0%nat;
    auto
  | destruct (Zle_dec n a2) as [le | nle];
    [ intro q;
      exists 0%nat;
      split;
      [ simpl;
        omega
      | intros d1 d2;
        simpl;
        omega ]
    | intro q;
      assert (h : 1 + a2 <= n <= max);
      [ omega
      | destruct (IHcl h) as [m mx];
        exists (S m);
        split;
        [ simpl;
          simpl in mx;
          omega
        | intros d1 d2;
          apply mx ]]]].
Defined.

Fixpoint CheckIfClosed min max L R {struct L} :=
  match L with
    | [] => false
    | (a :: L'') =>
      match L'' with
        | [] => match R with
                   | (c :: []) =>
                     match a ?= min with
                       | Eq => match c ?= max with
                                 | Eq => true
                                 | _ => false
                               end
                       | _ => false
                     end
                   | _ => false
                 end
        | (b :: L') =>
          match R with
            | (c :: d :: R') =>
              match a ?= min with
                | Eq => match b ?= 1 + c with
                          | Eq => CheckIfClosed b max L'' (d :: R')
                          | _ => false
                        end
                | _ => false
              end
            | _ => false
          end
      end
  end.

Lemma ClosedDec : forall min max L R,
                    let x := Closed min max L R
                    in x + (x -> False).
Proof.
  intros min max L.
  revert min max.
  induction L as [| a L C]; [ intros min max q; apply inr; intro Q; inversion Q | ].

  intros min max R;
  destruct R as [| c R];
  [ apply inr;
    intro Q;
    inversion Q
  | ].

  destruct L as [| b L];
  [ destruct R as [| d R];
    [ destruct (Z.eq_dec min a) as [eqa | neqa];
      [ destruct (Z.eq_dec max c) as [eqc | neqc];
        [ apply inl;
          rewrite -> eqa;
          rewrite -> eqc;
          constructor
        | apply inr;
          intro Q;
          inversion Q;
          firstorder ]
      | apply inr;
        intro Q;
        inversion Q;
        firstorder ]
    | apply inr;
      intro Q;
      inversion Q]
  | ].

  destruct (Z.eq_dec a min) as [amin | namin];
  [ destruct R as [| d R];
    [ apply inr;
      intro Q;
      inversion Q
    | destruct (Z.eq_dec b (1 + c)) as [cb | ncb];
      [ destruct (C b max (d :: R)) as [yC | nC];
        [ apply inl;
          rewrite -> amin;
          rewrite -> cb;
          constructor;
          rewrite <- cb;
          auto
        | apply inr;
          intro Q;
          inversion Q;
          rewrite -> cb in nC;
          apply nC;
          auto ]
      | apply inr;
        intro Q;
        contradict ncb;
        inversion Q;
        reflexivity ]]
  | apply inr;
    intro Q;
    contradict namin;
    inversion Q;
    reflexivity ].
Defined.

Lemma ClosedDec' : forall min max L R,
                     let x := Closed min max L R
                     in {b : bool & match b with
                                      | true => x
                                      | false => x -> False
                                    end }.
Proof.
  assert (inl : forall x, x -> {b : bool & match b with
                                      | true => x
                                      | false => x -> False
                                    end }).
  intros x X.
  exists true.
  auto.

  assert (inr : forall x, (x -> False) ->
                          {b : bool & match b with
                                      | true => x
                                      | false => x -> False
                                    end }).
  intros x xf.
  exists false.
  auto.

  intros min max L.
  revert min max.
  induction L as [| a L C]; [ intros min max q; apply inr; intro Q; inversion Q | ].

  intros min max R;
  destruct R as [| c R];
  [ apply inr;
    intro Q;
    inversion Q
  | ].

  destruct L as [| b L];
  [ destruct R as [| d R];
    [ destruct (Z.eq_dec min a) as [eqa | neqa];
      [ destruct (Z.eq_dec max c) as [eqc | neqc];
        [ apply inl;
          rewrite -> eqa;
          rewrite -> eqc;
          constructor
        | apply inr;
          intro Q;
          inversion Q;
          firstorder ]
      | apply inr;
        intro Q;
        inversion Q;
        firstorder ]
    | apply inr;
      intro Q;
      inversion Q]
  | ].

  destruct (Z.eq_dec a min) as [amin | namin];
  [ destruct R as [| d R];
    [ apply inr;
      intro Q;
      inversion Q
    | destruct (Z.eq_dec b (1 + c)) as [cb | ncb];
      [ 
      | apply inr;
        intro Q;
        contradict ncb;
        inversion Q;
        reflexivity ]]
  | apply inr;
    intro Q;
    contradict namin;
    inversion Q;
    reflexivity ].

  destruct (C b max (d :: R)) as [x j].
  destruct x.
  apply inl.
  rewrite -> amin.
  rewrite -> cb.
  constructor.
  rewrite <- cb.
  exact j.

  apply inr.
  intro Q.
  inversion Q.
  contradict j.
  rewrite -> cb.
  auto.
Defined.
