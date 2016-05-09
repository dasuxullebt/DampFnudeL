Require Import Coq.Logic.Decidable.
Require Import Coq.Arith.Compare_dec.

Require Import Coq.Numbers.NatInt.NZOrder.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Vectors.Vector.
Require Import Coq.Lists.List.
Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.Div2.

Require Import Coq.NArith.BinNatDef.
Require Import Coq.NArith.BinNat.
Require Import Coq.PArith.BinPos.
Require Import NArith.
Require Import Coq.QArith.QArith_base.
Require Import Coq.Strings.String.
Require Import Ascii.
Require Import Program.

Require Import Shorthand.
Require Import DeflateCoding.
Require Import KraftVec.
Require Import KraftList.
Require Import Combi.
Require Import Transports.
Require Import Prefix.
Require Import LSB.
Require Import Repeat.
Require Import Backreferences.
Require Import StrongDec.
Require Import EncodingRelation.

Local Open Scope nat_scope.

Goal CLCHeaderPermuted 1 [true; false; false] [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0].
Proof.
  set (unperm := [1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]).
  set (perm :=   [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0]).
  assert (forall m, nth_error perm (nth m HCLensNat 19) =
                    nth_error unperm m).
  repeat (destruct m; [reflexivity|(reflexivity||idtac)]).
  apply (makeCLCHeaderPermuted _ _ _ unperm).
  apply (makeCLCHeaderPadded _ _ _ 18 [1]).
  replace [true; false; false] with ([true; false; false] ++ Bnil).
  apply (succCLCHeaderRaw _ _ _ _ _ zeroCLCHeaderRaw).
  reflexivity.
  apply (oneLSBnat [false; false] 0).
  apply (zeroLSBnat [false] 0).
  apply (zeroLSBnat [] 0).
  constructor.
  reflexivity.
  reflexivity.
  reflexivity.
  apply H.
Qed.

(* TODO *)
Function bools (l : list nat) := map (fun x => match x with
                                                 | 0 => false
                                                 | _ => true
                                               end) l.

Lemma simpleslice3 : forall {A} (a b c : A) l, a :: b :: c :: l = [a; b; c] ++ l.
Proof.
  intros.
  reflexivity.
Qed.

Lemma ExampleCLCHeaderPermuted :
  CLCHeaderPermuted 18
     (bools [0;0;0; 1;1;0; 0;1;0; 1;1;0; 0;0;0; 0;0;0; 0;0;0; 0;0;0; 0;0;0;
             0;0;0; 0;0;0; 0;1;0; 0;0;0; 1;1;0; 0;0;0; 0;0;0; 0;0;0; 1;1;0])
     [3; 3; 0; 3; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 2].
Proof.
               (* 0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 16 17 18*)
  set (unperm := [3; 3; 0; 3; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 2]).
               (*  [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15] *)
  set (perm :=     [0;   3;  2; 3; 0; 0; 0; 0;  0; 0;  0; 2;  0; 3;  0; 0;  0; 3;  0]).
  assert (forall m, nth_error unperm (nth m HCLensNat 19) =
                    nth_error perm m).
  repeat (destruct m; [reflexivity|(reflexivity||idtac)]).
  apply (makeCLCHeaderPermuted _ _ _ perm).
  apply (makeCLCHeaderPadded _ _ _ 1 [0; 3; 2; 3; 0; 0; 0; 0; 0; 0; 0; 2; 0; 3; 0; 0; 0; 3]).
  compute.
  assert (lem3 : LSBnat [true; true; false] 3).
  apply (oneLSBnat [true; false] 1).
  apply (oneLSBnat [false] 0).
  apply (zeroLSBnat [] 0).
  constructor.
  assert (lem0 : LSBnat [false; false; false] 0).
  apply (zeroLSBnat [false; false] 0).
  apply (zeroLSBnat [false] 0).
  apply (zeroLSBnat [] 0).
  constructor.
  assert (lem2 : LSBnat [false; true; false] 2).
  apply (zeroLSBnat [true; false] 1).
  apply (oneLSBnat [false] 0).
  apply (zeroLSBnat [] 0).
  constructor.
  repeat (rewrite -> simpleslice3; apply succCLCHeaderRaw; auto).
  constructor.
  reflexivity.
  auto.
  auto.
Qed.

Definition ExampleCLC : deflateCoding 19.
Proof.
  set (inp := [3; 3; 0; 3; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 2]).
  assert (ki : (kraft_nvec (of_list inp) <= 1)%Q).
  compute.
  intro Q.
  inversion Q.
  destruct (existence (ll inp) (of_list inp) ki) as [x e].
  compute in x.
  exact x.
Defined.

Lemma EExplodeStep : forall {n} (Q : fin (S n) -> Prop),
                      (Q FinF1 \/ (exists (m : fin n), Q (FinFS m))) -> (exists (m : fin (S n)), Q m).
  intros n Q H.
  destruct H as [H|[h H]].
  exists (FinF1 (n:=n)).
  trivial.
  exists (FinFS h).
  trivial.
Qed.

Lemma AExplodeStep : forall {n} (Q : fin (S n) -> Prop),
                      (Q FinF1 /\ (forall (m : fin n), Q (FinFS m))) -> (forall (m : fin (S n)), Q m).
  intros n Q H.
  destruct H as [H h].
  intro m.
  dependent destruction m.
  exact H.
  apply h.
Qed.

Fixpoint EExplodeType {n} (Q : fin n -> Prop) :=
  match n as N return (N=n->_) with
    | 0 => fun eq => False
    | (S n') => fun eq => Q (fin_id eq (FinF1 (n:=n'))) \/ EExplodeType (n:=n') (fun k => Q (fin_id eq (FinFS k)))
  end eq_refl.

Fixpoint AExplodeType {n} (Q : fin n -> Prop) :=
  match n as N return (N=n->_) with
    | 0 => fun eq => True
    | (S n') => fun eq => Q (fin_id eq (FinF1 (n:=n'))) /\ AExplodeType (n:=n') (fun k => Q (fin_id eq (FinFS k)))
  end eq_refl.

Lemma EExplode : forall {n} (Q : fin n -> Prop), EExplodeType Q -> (exists (m : fin n), Q m).
Proof.
  intros n Q Ex.
  dependent induction n.
  contradict Ex.
  apply EExplodeStep.
  destruct Ex as [f1|fs].
  apply or_introl.
  rewrite -> fin_id_destroy in f1.
  exact f1.
  apply or_intror.
  destruct (IHn _ fs) as [m x].
  exists m.
  rewrite -> fin_id_destroy in x.
  exact x.
Defined.

Lemma AExplode : forall {n} (Q : fin n -> Prop), AExplodeType Q -> (forall (m : fin n), Q m).
Proof.
  intros n Q All.
  dependent induction n.
  intro m.
  inversion m.
  intro m.
  destruct All as [A1 A2].
  dependent destruction m.
  rewrite -> fin_id_destroy in A1.
  exact A1.
  apply (IHn _ A2 m).
Qed.

Definition ExampleCLC' : deflateCoding 19.
Proof.
  set (x:=of_list [
           [true; false; false]; (* 0 *)
           [true; false; true]; (* 1 *)
           [];                  (* 2 *)
           [true; true; false]; (* 3 *)
           [false; false];      (* 4 *)
           [];[];[];[];[];[];[];[];[];[];[];[]; (* 5 - 16 *)
           [true; true; true];  (* 17 *)
           [false; true]]).     (* 18 *)
  apply (mkDeflateCoding _ x).
  (* we just use brute force *)
  intro a.
  abstract (
  repeat ((try solve [inversion a])
            || (dependent destruction a;
                [(abstract (intro b;
                            repeat ((try solve [ inversion b ])
                                      || (dependent destruction b;
                                          [(compute; intros neq nnil q; destruct q as [c eq];
                                            (solve [(contradict neq; reflexivity) | (contradict nnil; reflexivity) | inversion eq])) |
                                           idtac]))))|idtac]))).
  
  abstract (
  intro a;
  repeat (dependent destruction a;
          [(intro b;
            repeat ((try solve [inversion b]) || (dependent destruction b; [(solve [(compute; abstract omega)|(intro q; constructor)])|idtac])))
           |idtac]);
  inversion a).

  abstract (
  intro a;
  repeat ((try solve [inversion a])
                      || (dependent destruction a;
                          [(intro b;
                             (repeat ((try solve [inversion b])
                                                || (dependent destruction b;
                                                    [(intros lens fle; 
                                                      solve [ apply Lex.lex_refl
                                                            | repeat constructor
                                                            | inversion lens
                                                            | (compute in fle; omega) ])
                                                    |idtac]))))|idtac]))).

  intros a c nnil lexs lbs.
  destruct c as [| b1 c].
  contradict nnil; reflexivity.
  destruct c as [| b2 c].
  compute in a.
  repeat (dependent destruction a;
          [(compute in lbs; omega) | idtac]).
  inversion a.
  destruct c as [| b3 c].
  repeat (dependent destruction a;
          [(compute in lbs; omega) | idtac]).
  dependent destruction a.
  unfold ll.
  exists (FinFS(FinFS(FinFS(FinFS(FinF1 (n:=14)))))).
  split.
  intro Q.
  inversion Q.
  inversion lexs as [| | ? ? ? lexs2].
  inversion lexs2 as [| | ? ? ? lexs3].
  exists Bnil.
  reflexivity.
  repeat (dependent destruction a;
          [(compute in lbs; omega) | idtac]).
  dependent destruction a.
  inversion lexs as [| A B C lexs2 | A B C lexs2].
  inversion lexs2 as [| A2 B2 C2 lexs3 | A2 B2 C2 lexs3].
  exists (FinFS(FinFS(FinFS(FinFS(FinF1 (n:=14)))))).
  split.
  intro Q.
  inversion Q.
  exists Bnil.
  reflexivity.
  exists (FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinF1 (n:=0)))))))))))))))))))).
  split.
  intro Q.
  inversion Q.
  exists Bnil.
  reflexivity.
  inversion a.

  destruct c as [|b4 c].
  dependent destruction a.
  destruct b1.
  destruct b2.
  inversion lexs.
  inversion H0.
  destruct b3.
  inversion lexs.
  inversion H0.
  inversion H4.
  exists (FinF1 (n:=18)).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  destruct b2.
  exists (FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinF1 (n:=0)))))))))))))))))))).
  split.
  intro Q; inversion Q.
  exists [b3].
  reflexivity.
  exists (FinFS(FinFS(FinFS(FinFS(FinF1 (n:=14)))))).
  split.
  intro Q; inversion Q.
  exists [b3]; reflexivity.

  dependent destruction a.
  destruct b1.
  destruct b2.
  inversion lexs.
  inversion H0.
  destruct b3.
  exists (FinFS (FinF1 (n:=17))).
  split.
  intro Q; inversion Q.
  exists Bnil.
  reflexivity.
  exists (FinF1 (n:=18)).
  split.
  intro Q; inversion Q.
  exists Bnil.
  reflexivity.
  destruct b2.
  exists (FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinF1 (n:=0)))))))))))))))))))).
  split.
  intro Q; inversion Q.
  exists [b3].
  reflexivity.
  exists (FinFS(FinFS(FinFS(FinFS(FinF1 (n:=14)))))).
  split.
  intro Q; inversion Q.
  exists [b3]; reflexivity.
  dependent destruction a; [(compute in lbs; omega) | idtac].
  dependent destruction a.

  destruct b1.
  destruct b2.
  destruct b3.
  inversion lexs.
  inversion H0.
  inversion H4.
  exists (FinFS (FinFS (FinFS (FinF1 (n:=15))))).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  destruct b3.
  exists (FinFS (FinF1 (n:=17))).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  exists (FinF1 (n:=18)).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  destruct b2.
  exists (FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinF1 (n:=0)))))))))))))))))))).
  split.
  intro Q; inversion Q.
  exists [b3].
  reflexivity.
  exists (FinFS (FinFS (FinFS (FinFS (FinF1 (n:=14)))))).
  split.
  intro Q; inversion Q.
  exists [b3]; reflexivity.
  repeat (dependent destruction a; [(compute in lbs; omega) | idtac]).
  dependent destruction a.

  destruct b1.
  destruct b2.
  destruct b3.
  exists (FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinF1 (n:=1))))))))))))))))))).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  exists (FinFS(FinFS(FinFS(FinF1(n:=15))))).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  destruct b3.
  exists (FinFS(FinF1(n:=17))).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  exists (FinF1(n:=18)).
  split.
  intro Q; inversion Q.
  exists Bnil; reflexivity.
  destruct b2.
  exists (FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinF1 (n:=0)))))))))))))))))))).
  split.
  intro Q; inversion Q.
  exists [b3].
  reflexivity.
  exists (FinFS (FinFS (FinFS (FinFS (FinF1 (n:=14)))))).
  split.
  intro Q; inversion Q.
  exists [b3]; reflexivity.  

  dependent destruction a.
  destruct b1.
  inversion lexs.
  destruct b2.
  exists (FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinFS(FinF1 (n:=0)))))))))))))))))))).
  split.
  intro Q; inversion Q.
  exists [b3].
  reflexivity.
  exists (FinFS (FinFS (FinFS (FinFS (FinF1 (n:=14)))))).
  split.
  intro Q; inversion Q.
  exists [b3]; reflexivity.
  inversion a.

  repeat (dependent destruction a; [(compute in lbs; omega) | idtac]).
  inversion a.
Defined.

(*  set (checkprefix :=
         fix f (l m : LB) :=
           match l with
             | [] => match m with 
                       | [] => true
                       | _ => false
                     end
             | (true :: l') =>
               match m with
                 | (true :: m') => f l' m'
                 | _ => false
               end
             | (false :: l') =>
               match m with
                 | (false :: m') => f l' m'
                 | _ => false
               end
           end).
                      
  set (findprefix' :=
         fix f l desired : nat :=
           match l with
             | [] => 0
             | (x :: L) =>
               match (checkprefix x desired) with
                 | false => f L desired
                 | true => 18 - ll L
               end
           end).

  set (of_nat_max :=
         fix f n : fin 19 :=
           match nat_compare n 19 as nc return (nat_compare n 19 = nc -> _) with
             | Lt => fun eq => of_nat_lt (nat_compare_Lt_lt _ _ eq)
             | _ => fun eq => FinF1
           end eq_refl).

  set (findprefix l m := of_nat_max (findprefix' l m)).

  destruct c as [| b0 c].
  contradict nnil.
  reflexivity.
  destruct c as [| b1 c].
  inversion lbs.
  destruct c as [| b2 c].
  inversion lbs.
  destruct c as [| b3 c].
  destruct b0.
  destruct b1.
  destruct b2.
  destruct lexdec.
  contradict l.
  contradict n.

    [ ((try solve [ inversion lbs
                  | (destruct lexdec;
                     [ (

])
         || (repeat ((solve [(inversion lx; []

    [ (intros nnil lx lbs;
       destruct c as [| b1 c];
       [ inversion lx

  intros nnil lx lbs.
  destruct c.
  compute in lbs.
  omega.
  destruct c.
  compute in lbs.
  omega.
  destruct c.
  compute in lbs.
  omega.
  destruct c.
  

  destruct c as [|b c].
  intro Q.
  contradict Q.
  reflexivity.

  dependent destruction a.
  destruct b.
  destruct c as [|b c].
  intros.
  compute in H0.
  compute in H1.
  omega.


  dependent destruction a.
  intros ? ? l
  destruct b. 
  
  *)
(***********************)


Lemma ExampleCLCHeader :
  CLCHeader 18
     ExampleCLC'
     (bools [0;0;0; 1;1;0; 0;1;0; 1;1;0; 0;0;0; 0;0;0; 0;0;0; 0;0;0; 0;0;0;
             0;0;0; 0;0;0; 0;1;0; 0;0;0; 1;1;0; 0;0;0; 0;0;0; 0;0;0; 1;1;0]).
Proof.
  set (seq := [3; 3; 0; 3; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 3; 2]).
  apply (makeCLCHeader _ _ _ seq).
  apply ExampleCLCHeaderPermuted.
  apply (makeCodingOfSequence seq ExampleCLC' eq_refl).
  rewrite -> vec_id_destroy.
  reflexivity.
Qed.
