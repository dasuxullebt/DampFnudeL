Require Import Coq.NArith.BinNat.
Require Import Coq.Numbers.Cyclic.Int31.Int31.
Require Import Backreferences.
Require Import String.
Require Import Program.
Require Import List.

Open Scope N.

Inductive BackBuffer (A : Set) : Set :=
| BBNil : BackBuffer A
| BBCons1 : A -> BackBuffer (A * A)%type -> BackBuffer A
| BBCons2 : A -> A -> BackBuffer (A * A)%type -> BackBuffer A.

Arguments BBNil [_].
Arguments BBCons1 [_] _ _.
Arguments BBCons2 [_] _ _ _.

Fixpoint bbcons {A : Set} (a : A) (bb : BackBuffer A) :=
  match bb with
    | BBNil => BBCons1 a BBNil
    | BBCons1 b x => BBCons2 a b x
    | BBCons2 b c x => BBCons1 a (bbcons (b, c) x)
  end.

Fixpoint bbnth {A : Set} (n : N) (bb : BackBuffer A) : option A :=
  match bb with
    | BBNil => None
    | BBCons1 a x => match n with
                       | 0 => Some a
                       | _ => match (bbnth ((n - 1) / 2) x) with
                                | Some (l, r) => match (n mod 2) with
                                                   | 0 => Some r (* n - 1 = 0 => l *)
                                                   | _ => Some l
                                                 end
                                | None => None
                              end
                     end
    | BBCons2 a b x => match n with
                         | 0 => Some a
                         | 1 => Some b
                         | _ => match (bbnth ((n - 2) / 2) x) with
                                  | Some (l, r) => match (n mod 2) with
                                                     | 0 => Some l
                                                     | _ => Some r
                                                   end
                                  | None => None
                                end
                       end
  end.

Definition Nth_error := (fun {A : Set} (n : N) (l : list A) => nth_error l (N.to_nat n)).

Definition reflList {A : Set} (bb : BackBuffer A) (l : list A) :=
  forall (n : N), Nth_error n l = bbnth n bb.

Lemma nth_bbcons : forall {A : Set} (b : A) bb l, reflList bb l -> reflList (bbcons b bb) (b :: l).
Proof.
  intros A b bb l rl n.
  apply (N.peano_ind (fun n => Nth_error n (b :: l) = bbnth n (bbcons b bb))).
  unfold Nth_error.
  unfold N.to_nat.
  unfold nth_error.
  destruct bb.  
  reflexivity.
  reflexivity.
  reflexivity.

  
  
  revert l bb.
  induction l.
  intros bb rlbb.
  destruct bb.
  intro n.
  apply (N.peano_ind (fun n => Nth_error n [b] = bbnth n (bbcons b BBNil))).
  reflexivity.
  
  
  induction bb.
  intros l rlnil.
  destruct l.
  intro n.
  apply (N.peano_ind (fun n => Nth_error n [b] = bbnth n (bbcons b BBNil))).
  reflexivity.
  intros n0 nerr.
  unfold Nth_error.
  rewrite -> Nnat.N2Nat.inj_succ.
  unfold nth_error.
  destruct ((N.to_nat n0)).
  compute.
  destruct n0.
  reflexivity.
  reflexivity.
  compute.
  destruct n0.
  reflexivity.
  reflexivity.

  unfold reflList in rlnil.
  assert (Q : Nth_error 0 (a :: l) = bbnth 0 BBNil).
  apply rlnil.
  inversion Q.

  intros l rl.
  intro n.
  apply (N.peano_ind (fun n => Nth_error n _ = bbnth n _)).
  reflexivity.
  intros n0 nerr0.
  unfold Nth_error.
  rewrite -> Nnat.N2Nat.inj_succ.
  
  destruct l as [|l' l''].
  intro Q.
  assert (R : Nth_error 0 [] = bbnth 0 (BBCons1 a bb)).
  apply Q.
  inversion R.

  intro rl.
  

  intro n.
  destruct n.
  Check N.peano_rec.
  compute.
  apply N.peano_rect.
  
Fixpoint behead {A : Set} (bb : BackBuffer A) : option (A * BackBuffer A) :=
  match bb with
    | BBNil => None
    | BBCons1 a x => match behead x with
                       | None => Some (a, BBNil)
                       | Some ((l, r), y) => Some (a, BBCons2 l r y)
                     end
    | BBCons2 a b x => Some (a, BBCons1 b x)
  end.

(* left: extracted so far. error. right: extracted. *)
Program Fixpoint rbr {A : Set} (q : SequenceWithBackRefs A) (bbl : N) (bb1 bb2 : BackBuffer A) {measure (brlen q)}: option (list A) :=
  match q with
    | [] => Some []
    | (x :: L) => let (bbl', bb1', bb2') := match bbl with
                                                | 0 => ((16384, BBNil), bb1)
                                                | _ => ((bbl - 1, bb1), bb2)
                                              end
                  in None
  end.