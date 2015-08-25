(** We're implementing a simple compression algorithm. *)

Require Import Vector.
Require Import List.
Require Import Bool.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Program.
Require Import Intervals.
Require Import Prefix.

Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.
Require Import HashTable.

Require Import Shorthand.
Require Import Backreferences.
Require Import EncodingRelation.
Require Import LSB.
Require Import Combi.
Require Import DeflateCoding.

(** For finding Backreferences, we use a slightly modified version of
the algorithm specified in RFC 1951. *)

(** A simple forgetful list structure, that only saves a certain
amount of items. We realize it by having two lists, where the second
one is thrown away if the first one is long enough. This is similar to
the forgetful lists suggested in RFC 1951, except that we do forget
multiple references in a bulk, as this is better suited in a purely
functional setting. *)

Open Scope nat_scope.

Function ForgetfulList (A : Set) : Set := (nat * (list A) * (list A))%type.

Function FFLForall {A : Set} (Q : A -> Prop) (ffl : ForgetfulList A) :=
  match ffl with
    | (n, l1, l2) => Forall Q l1 /\ Forall Q l2
  end.

Function FFLNil (A : Set) := (0, @nil A, @nil A).

Lemma FFLForallNil : forall {A : Set} (Q : A -> Prop), FFLForall Q (FFLNil A).
Proof.
  intros A Q.
  simpl; split; constructor.
Qed.

(** notice that m is the maximal number of items the first list + 1. *)

Function FFLCons {A : Set} (m : nat) (a : A) (b : ForgetfulList A) :=
  match b with
    | (n, L1, L2) => match nat_compare n m with
                         (* n > m is handled equally to n = m *)
                       | Lt => (S n, a :: L1, L2)
                       | _ => (1, a :: nil, L1)
                     end
  end.

Lemma FFLForallCons : forall {A : Set} (m : nat) (a : A) (b : ForgetfulList A)
                             (Q : A -> Prop),
                        FFLForall Q b -> Q a -> FFLForall Q (FFLCons m a b).
Proof.
  intros A m a b Q ab Qa.
  unfold FFLCons.
  destruct b as [[b L1] L2].
  destruct (nat_compare b m).
  simpl.
  simpl in ab.
  split.
  constructor.
  exact Qa.
  constructor.
  firstorder.

  simpl.
  simpl in ab.
  split.
  constructor.
  exact Qa.
  firstorder.
  firstorder.

  simpl.
  simpl in ab.
  split.
  constructor.
  exact Qa.
  constructor.
  firstorder.
Qed.

Fixpoint FilterList {A : Set} (find : A -> bool) (L : list A) : list A :=
  match L with
    | nil => nil
    | (x :: L') => match find x with
                     | true => x :: FilterList find L'
                     | false => FilterList find L'
                   end
  end.

Functional Scheme FilterList_ind := Induction for FilterList Sort Prop.

Lemma ForallFilterList : forall {A : Set} find (L : list A) Q,
                           Forall Q L -> Forall Q (FilterList find L).
Proof.
  intros A find L Q QL;
  functional induction (FilterList find L) as [ | ? ? ? ? ? IHl |x l];
  [ trivial
  | constructor;
    inversion QL;
    trivial;
    apply IHl;
    inversion QL;
    trivial
  | apply IHl;
    inversion QL;
    trivial ].
Qed.

Function FFLSearch {A : Set} (find : A -> bool) (L : ForgetfulList A) : list A :=
  match L with
    | (_, L1, L2) => FilterList find L1 ++ FilterList find L2
  end.

Lemma FFLForallSearch : forall {A : Set} (find : A -> bool) (L : ForgetfulList A)
                               (Q : A -> Prop),
                          FFLForall Q L -> Forall Q (FFLSearch find L).
Proof.
  intros A find L Q QL.
  functional induction (FFLSearch find L).
  apply app_forall.
  apply ForallFilterList.
  inversion QL.
  trivial.
  apply ForallFilterList.
  inversion QL.
  trivial.
Qed.

(** An entry consists of three bytes, an index and a list which
contains the uncompressed bytes beginning with that index. *)

Definition Entry := (LByte * nat)%type.

(** The entry checksum is just the sum of the byte values modulo 128 *)
Function EntryChecksum (e : Entry) : option nat :=
  match e with
    | (b1 :: b2 :: b3 :: r, _) =>
      Some ((ByteToNat b1 + ByteToNat b2 + ByteToNat b3) mod 128)
    | _ => None
  end.

Definition HashTable := HashTable.M.t (ForgetfulList Entry).

Function ForallHashTable {A : Set} (Q : A -> Prop):=
  ForallHashTable_ (FFLForall Q).

Lemma ForallHashTableEmpty : forall {A : Set} (Q : A -> Prop),
                               ForallHashTable Q (M.empty (ForgetfulList A)).
Proof.
  intros A Q.
  apply ForallHashTableEmpty_.
Qed.

(** an entry is classified by its first 3 bytes only. entries which do
not have lists of length 3 are ignored and never equal. *)
Function entry_eq (a b : Entry) : bool :=
  match a with
    | (b0 :: b1 :: b2 :: r1, _) =>
      match b with
        | (b3 :: b4 :: b5 :: r2, _) =>
          match vec_eq_dec b0 b3 bool_dec with
            | inl _ => match vec_eq_dec b1 b4 bool_dec with
                         | inl _ => match vec_eq_dec b2 b5 bool_dec with
                                      | inl _ => true
                                      | _ => false
                                    end
                         | inr _ => false
                       end
            | inr _ => false
          end
        | _ => false
      end
    | _ => false
  end.

(** return the indices of occurences and boolean lists of an entry *)
Function search (e : Entry) (t : HashTable) : list Entry :=
  match EntryChecksum e with
    | None => nil
    | Some chk =>
      match M.find chk t with
        | None => nil
        | Some d => FFLSearch (entry_eq e) d
      end
  end.

Lemma ForallHashTableSearch : forall (Q : Entry -> Prop) t e,
                                ForallHashTable Q t ->
                                Forall Q (search e t).
Proof.
  intros Q t e all.
  functional induction (search e t);
  [ constructor
  | constructor
  | apply FFLForallSearch;
    eapply all;
    apply M.find_2;
    eauto ].
Qed.

(** Constant for history *)
Definition hist := 256.

Function insert (e : Entry) (t : HashTable) : HashTable :=
  match EntryChecksum e with
    | Some cse => 
      let xe := match M.find cse t with
                  | None => FFLNil Entry
                  | Some x => x
                end
      in M.add cse (FFLCons hist e xe) t
    | _ => t
  end.

Lemma ForallHashTableInsert : forall (Q : Entry -> Prop) h e,
                                ForallHashTable Q h ->
                                Q e ->
                                ForallHashTable Q (insert e h).
Proof.
  intros Q h e Qh Qe.
  functional induction (insert e h);
  [ apply ForallHashTableAdd_;
    [ apply FFLForallCons;
      [ constructor; [ constructor | constructor ]
      | trivial ]
    | intuition ]
  | apply ForallHashTableAdd_;
    [ apply FFLForallCons;
      [ assert (M.MapsTo cse x h);
        [ apply M.find_2;
          trivial
        | apply (Qh _ _ H) ]
      | trivial ]
    | trivial ]
  | trivial ].
Qed.

Fixpoint max_eq_len (stop : nat) (ref todo : LByte) {struct todo} : nat :=
  match stop with
    | 0 => 0
    | (S n) => match ref with
                 | [] => 0
                 | (r :: ref') =>
                   match todo with
                     | [] => 0
                     | (t :: todo') =>
                       match vec_eq_dec r t bool_dec with
                         | inl _ => S (max_eq_len n ref' todo')
                         | inr _ => 0
                       end
                   end
               end
  end.

Functional Scheme max_eq_len_ind := Induction for max_eq_len Sort Prop.

Lemma max_eq_len_correct_stop : forall s r t,
                                  max_eq_len s r t <= s.
Proof.
  intros s r t.
  functional induction (max_eq_len s r t); omega.
Qed.

Lemma max_eq_len_correct_max_ref : forall s r t,
                                     max_eq_len s r t <= ll r.
Proof.
  intros s r t.
  functional induction (max_eq_len s r t);
    (omega || (simpl; omega)).
Qed.

Lemma max_eq_len_correct_max_todo : forall s r t,
                                     max_eq_len s r t <= ll t.
Proof.
  intros s r t.
  functional induction (max_eq_len s r t);
    (omega || (simpl; omega)).
Qed.

Lemma ForallHashTableImp_ : forall {A} (Q : A -> Prop) (R : A -> Prop) h,
                              (forall a, Q a -> R a) ->
                              ForallHashTable_ Q h -> ForallHashTable_ R h.
Proof.
  intros A Q R h imp Qh.
  intros k v mt.
  apply imp.
  eapply Qh.
  eauto.
Qed.

Lemma FFLForallImp : forall {A : Set} (Q : A -> Prop) (R : A -> Prop) ffl,
                       (forall a, Q a -> R a) ->
                       FFLForall Q ffl -> FFLForall R ffl.
Proof.
  intros A Q R ffl imp Qffl.
  destruct ffl as [[n L1] L2].
  simpl.
  simpl in Qffl.
  split; (eapply Forall_impl; [exact imp | apply Qffl]).
Qed.

Lemma ForallHashTableImp : forall {A : Set} (Q : A -> Prop) (R : A -> Prop) h,
                           (forall a, Q a -> R a) ->
                           ForallHashTable Q h -> ForallHashTable R h.
Proof.
  intros A Q R h imp Qh.
  eapply (ForallHashTableImp_ (fun a => FFLForall Q a)).
  intros a Qa.
  eapply FFLForallImp.
  exact imp.
  exact Qa.
  exact Qh.
Qed.

Inductive EntryCorrect (complete : LByte) : Entry -> Prop :=
| mkEC : forall done list, done ++ list = complete ->
                           EntryCorrect complete (list, ll done).

Definition CommonPrefix (n : nat) (o l m : LByte) :=
  { l' : LByte & { m' : LByte | o ++ l' = l /\ o ++ m' = m /\ ll o = n }}.

Lemma CalculateCommonPrefix :
  forall l m stop,
    { n : nat & { o : LByte & {x : CommonPrefix n o l m | n <= stop }}}.
Proof.
  induction l as [|lx l IHl];
  [ intros m stop;
    exists 0;
    exists (@nil Byte);
    split;
    [ exists (@nil Byte);
      exists m;
      auto
    | omega]
   |].

  intros m stop.
  destruct stop as [|stop];
  [ exists 0;
    exists (@nil Byte);
    split;
    [ exists (lx :: l);
      exists m;
      auto
    | omega]
  |].

  destruct m as [|mx m];
  [ exists 0;
    exists (@nil Byte);
    split;
    [ exists (lx :: l);
      exists (@nil Byte);
      auto
    | omega]
   |].

  destruct (vec_eq_dec lx mx bool_dec) as [e|e];
    [ | ].

  destruct (IHl m stop) as [n' [o' [[l' [m' [oll [omm lon]]]] nst]]].
  exists (S n').
  exists (mx :: o').
  split; [ | omega].
  exists l'.
  exists m'.
  split.
  rewrite -> e.
  rewrite <- app_comm_cons.
  f_equal.
  exact oll.  
  split.
  rewrite <- app_comm_cons.
  f_equal.
  exact omm.
  simpl.
  omega.

  exists 0.
  exists (@nil Byte).
  split.
  exists (lx :: l).
  exists (mx :: m).
  auto.
  omega.
Qed.

Lemma CorrectEntryToBackRef :
  forall done todo entry donelen maxlen,
    donelen = ll done ->
    snd entry < donelen ->
    EntryCorrect (done ++ todo) entry ->
           { len : nat
         & { dist : nat
         & { br : LByte
         & { rest : LByte
         | len <= maxlen /\
           ResolveBackReference len dist done (done ++ br) /\
           done ++ todo = done ++ br ++ rest }}}}.
Proof.
  intros done todo [ref refn] donelen maxlen lldonelen refn_done_len ec.
  destruct (CalculateCommonPrefix ref todo maxlen) as [len [o [[l' [m' [olr [omr lol]]]] nst]]].
  exists len.
  exists (donelen - refn).
  exists o.
  exists m'.
  assert (Null : Byte);
  [ apply (NatToByte 0); [ omega ]
  | ].

  split;
  [ exact nst
  | split;
    [ inversion ec as [ecdone b C [D E]];
      simpl in refn_done_len;
      rewrite -> E;
      rewrite <- lol;
      revert o done todo ref refn donelen maxlen lldonelen refn_done_len ec len l' m' olr omr lol nst ecdone b C D E;
      apply (rev_ind
               (fun o => forall (done todo ref : LByte) (refn donelen maxlen : nat),
                           donelen = ll done ->
                           refn < donelen ->
                           EntryCorrect (done ++ todo) (ref, refn) ->
                           forall (len : nat) (l' m' : LByte),
                             o ++ l' = ref ->
                             o ++ m' = todo ->
                             ll o = len ->
                             len <= maxlen ->
                             forall ecdone b : LByte,
                               ecdone ++ ref = done ++ todo ->
                               b = ref ->
                               ll ecdone = refn ->
                               ResolveBackReference (ll o) (donelen - refn) done (done ++ o)));
      [ intros done todo ref refn donelen maxlen lldonelen refn_done_len ec len l' m' olr omr lol nst ecdone b C D E;
        rewrite -> app_nil_r;
        constructor
      | intros lx l IHl done todo ref refn donelen maxlen lldonelen refn_done_len ec len l' m' olr omr lol nst ecdone b C D E;
        rewrite -> app_assoc;
        rewrite -> app_length;
        replace (ll l + ll [lx]) with (S (ll l));
        [ constructor;
          [ destruct len as [|len];
            [ rewrite -> app_length in lol;
              simpl in lol;
              contradict lol;
              omega
            | assert (k1 : len <= maxlen);
              [ omega
              | assert (k2 : ll l = len);
                [ rewrite -> app_length in lol;
                  simpl in lol;
                  omega
                | assert (k3 : l ++ ([lx] ++ l') = ref);
                  [ rewrite -> app_assoc;
                    exact olr
                  | assert (k4 : l ++ ([lx] ++ m') = todo);
                    [ rewrite -> app_assoc;
                      exact omr
                    | apply (IHl done todo ref refn donelen maxlen lldonelen refn_done_len ec len ([lx] ++ l') ([lx] ++ m') k3 k4 k2 k1 ecdone b C D E)]]]]]
          | destruct (donelen - refn) as [|rn] eqn:diff;
            [ omega
            | apply (nthNthLast _ _ Null);
              [ rewrite <- diff;
                rewrite -> app_length;
                omega
              | rewrite <- diff;
                rewrite -> app_length;
                rewrite -> lldonelen;
                replace (ll done + ll l - (ll done - refn))
                with (ll l + refn);
                [ rewrite <- E;
                  assert (ped : prefix ecdone done);
                  [ destruct (prefix_common ecdone done (done ++ todo));
                    [ rewrite <- C;
                      exists ref; reflexivity
                    | exists todo; reflexivity
                    | auto
                    | assert (ll done <= ll ecdone);
                      [ apply prefix_le;
                        auto
                      | omega ]]
                  | destruct ped as [suff suff_app];
                    rewrite <- suff_app;
                    rewrite <- app_assoc;
                    rewrite -> app_nth2;
                    [ replace (ll l + ll ecdone - ll ecdone) with (ll l);
                      [ assert (pls : prefix l (suff ++ l));
                        [ destruct (prefix_common l (suff ++ l) ref);
                          [ exists ([lx] ++ l');
                              rewrite -> app_assoc;
                              auto
                                 | exists ([lx] ++ m');
                                   apply (app_ll ecdone _ ecdone _);
                                   [ rewrite <- app_assoc;
                                     rewrite <- app_assoc in omr;
                                     rewrite -> omr;
                                     rewrite -> app_assoc;
                                     rewrite -> suff_app;
                                     auto
                                   | reflexivity ]
                                 | auto
                                 | destruct suff as [|t suff];
                                   [ exists (@nil Byte); (* cannot happen, but easier that contradiction *)
                                       rewrite -> app_nil_r;
                                       reflexivity
                                          | assert (Q : ll ((t :: suff) ++ l) <= ll l);
                                            [ apply prefix_le;
                                              auto
                                            | rewrite -> app_length in Q;
                                              simpl in Q;
                                              omega ]]]
                        | destruct pls as [suff' suff'app];
                          rewrite <- suff'app;
                          destruct suff' as [|t' suff'];
                          [ destruct suff as [|t suff];
                            [ assert (ll ecdone = ll done);
                              [ replace ecdone with (ecdone ++ []);
                                [ f_equal; auto | apply app_nil_r ]
                              | omega ]
                            | assert (Q : ll (l ++ []) = ll ((t :: suff) ++ l));
                              [ f_equal; auto
                              | rewrite -> app_length in Q;
                                rewrite -> app_length in Q;
                                simpl in Q;
                                omega ]]
                          | assert (suff'' : ecdone ++ suff ++ todo = done ++ todo);
                            [ rewrite -> app_assoc;
                              f_equal;
                              auto
                            | rewrite <- C in suff'';
                              assert (str : suff ++ todo = ref);
                              [ apply (app_cancel_l ecdone);
                                auto
                              | rewrite <- olr in str;
                                rewrite <- omr in str;
                                rewrite -> app_assoc in str;
                                rewrite -> app_assoc in str;
                                rewrite <- suff'app in str;
                                repeat (rewrite <- app_assoc in str);
                                rewrite -> app_nth2;
                                [ replace (ll l - ll l) with 0;
                                  [ simpl;
                                    assert (R : (t' :: suff') ++ [lx] ++ m' = [lx] ++ l');
                                    [ apply (app_cancel_l l);
                                      auto
                                    | simpl in R;
                                      inversion R;
                                      reflexivity ]
                                  | omega]
                                | omega]]]]]
                       | omega]
                    | omega]]
                | omega]]]]
        | simpl; omega]]
    | rewrite <- omr;
      reflexivity ]].
Qed.

(** this searches for the largest possible backreference out of a list
of possible backreferences. We only proved that it always returns
correct backreferences. *)

(*Lemma makeSingleBackReference :
  forall (stop maxdist donelen : nat) (done todo : LByte) (heuristic : list Entry),
    ll done = donelen ->
    Forall (EntryCorrect (done ++ todo)) heuristic ->
    Forall (fun x => snd x < donelen) heuristic ->
    option { length : nat
         & { dist : nat
         & { todo2 : LByte
         | exists done2, (* we do not want "done2" to be comp. relev. *)
           ResolveBackReference length dist done done2
           /\ done ++ todo = done2 ++ todo2
           /\ length <= stop /\ dist <= maxdist }}}.
Proof.
  intros stop maxdist donelen done todo heuristic donecorrect hcorrect hdonelen;
  revert stop maxdist donelen done todo donecorrect hcorrect hdonelen;
  induction heuristic as [|[reflist a] heuristic IHheuristic];
  [ intros; apply None
  | intros stop maxdist donelen done todo donecorrect ec hdonelen;
    destruct (CorrectEntryToBackRef done todo (reflist, a) donelen stop)
      as [x [distx [brx [restx [stopx [rbrx appx]]]]]];
    [ auto
    | inversion hdonelen;
      auto
    | inversion ec;
      auto
    | destruct (IHheuristic stop maxdist donelen done todo) as [[l wl]|];
      [ auto
      | inversion ec; auto
      | inversion hdonelen; auto
      | destruct (le_dec distx maxdist) as [d|d];
        [ apply Some;
          destruct (le_dec x l) as [e|e];
          [ exists x;
              exists distx;
              exists restx;
              exists (done ++ brx);
              split;
              [ trivial
              | split; [ rewrite <- app_assoc; auto | split; [ trivial | trivial ]]]
                 | exists l;
                   auto ]
        | apply Some; exists l; auto ]
      | destruct (le_dec distx maxdist);
        [ apply Some;
          exists x;
          exists distx;
          exists restx;
          exists (done ++ brx);
          split;
          [ trivial
          | split; [ rewrite <- app_assoc; auto | split; [ trivial | trivial ]]]
        | apply None]]]].
Qed.*)

Lemma makeSingleBackReference :
  forall (stop maxdist donelen : nat) (done todo : LByte) (heuristic : list Entry),
    ll done = donelen ->
    Forall (EntryCorrect (done ++ todo)) heuristic ->
    Forall (fun x => snd x < donelen) heuristic ->
    option { length : nat
         & { dist : nat
         & { todo2 : LByte
         & { brx : LByte
           | ResolveBackReference length dist done (done ++ brx)
           /\ done ++ todo = done ++ brx ++ todo2
           /\ length <= stop /\ dist <= maxdist }}}}.
Proof.
  intros stop maxdist donelen done todo heuristic donecorrect hcorrect hdonelen;
  revert stop maxdist donelen done todo donecorrect hcorrect hdonelen;
  induction heuristic as [|[reflist a] heuristic IHheuristic];
  [ intros; apply None | ].

  intros stop maxdist donelen done todo donecorrect ec hdonelen.
  destruct (CorrectEntryToBackRef done todo (reflist, a) donelen stop)
      as [x [distx [brx [restx [stopx [rbrx appx]]]]]];
    [ auto
    | inversion hdonelen;
      auto
    | inversion ec;
      auto
    | destruct (IHheuristic stop maxdist donelen done todo) as [[l wl]|];
      [ auto | inversion ec; auto | inversion hdonelen; auto | | ]].

  destruct (le_dec distx maxdist) as [d|d]; [ 
  apply Some;
  destruct (le_dec x l) as [e|e];
  [ exists x;
    exists distx;
    exists restx;
    exists brx;
    split; [ trivial | split; [ trivial | split; trivial ]]
  | exists l;
    auto ]
| apply Some; exists l; auto ].

    destruct (le_dec distx maxdist).
    apply Some.
    exists x.
    exists distx.
    exists restx.
    exists brx.
    split;
      [ trivial
      | split; [ auto | split; [ trivial | trivial ]]].

    apply None.
Qed.

(* Lemma makeSingleBackReference :
  forall (stop maxdist donelen : nat) (done todo : LByte) (heuristic : list Entry),
    ll done = donelen ->
    Forall (EntryCorrect (done ++ todo)) heuristic ->
    Forall (fun x => snd x < donelen) heuristic ->
    option { length : nat
         & { dist : nat
         & { todo2 : LByte
         | exists done2, (* we do not want "done2" to be comp. relev. *)
           ResolveBackReference length dist done done2
           /\ done ++ todo = done2 ++ todo2
           /\ length <= stop /\ dist <= maxdist }}}.
Proof.
  intros stop maxdist donelen done todo heuristic donecorrect hcorrect hdonelen;
  revert stop maxdist donelen done todo donecorrect hcorrect hdonelen;
  induction heuristic as [|[reflist a] heuristic IHheuristic];
  [ intros; apply None
  | intros stop maxdist donelen done todo donecorrect ec hdonelen;
    destruct (CorrectEntryToBackRef done todo (reflist, a) donelen stop)
      as [x [distx [brx [restx [stopx [rbrx appx]]]]]];
    [ auto
    | inversion hdonelen;
      auto
    | inversion ec;
      auto
    | destruct (IHheuristic stop maxdist donelen done todo) as [[l wl]|];
      [ auto
      | inversion ec; auto
      | inversion hdonelen; auto
      | destruct (le_dec distx maxdist) as [d|d];
        [ apply Some;
          destruct (le_dec x l) as [e|e];
          [ exists x;
              exists distx;
              exists restx;
              exists (done ++ brx);
              split;
              [ trivial
              | split; [ rewrite <- app_assoc; auto | split; [ trivial | trivial ]]]
                 | exists l;
                   auto ]
        | apply Some; exists l; auto ]
      | destruct (le_dec distx maxdist);
        [ apply Some;
          exists x;
          exists distx;
          exists restx;
          exists (done ++ brx);
          split;
          [ trivial
          | split; [ rewrite <- app_assoc; auto | split; [ trivial | trivial ]]]
        | apply None]]]].
Qed.
*)

Lemma EntryCorrectCons : forall donelen done todo br todo2 h,
                           donelen = ll done ->
                           done ++ [br] ++ todo2 = done ++ todo ->
                           ForallHashTable (EntryCorrect (done ++ todo)) h ->
                           ForallHashTable (EntryCorrect (done ++ [br] ++ todo2))
                                           (insert (br :: todo2, donelen) h).
Proof.
  intros donelen done todo br todo2 h leneq appeq all;
  apply ForallHashTableInsert;
  [ rewrite -> appeq;
    exact all
  | rewrite -> leneq;
    constructor;
    reflexivity ].
Qed.

Lemma EntryLensCons : forall donelen br todo2 h k,
                        ForallHashTable (fun en => snd en < donelen) h ->
                        ForallHashTable (fun en => snd en < S (donelen + k))
                                        (insert (br :: todo2, donelen) h).
Proof.
  intros donelen br todo2 h k all;
  apply ForallHashTableInsert;
  [ apply (ForallHashTableImp (fun en => snd en < donelen));
    [ intros [a1 a2]; simpl; omega
    | exact all ]
  | simpl; omega ].
Qed.

Fixpoint FeedHashTable (n : nat) (b r : LByte) (h : HashTable) :=
  match b with
    | [] => h
    | (b1 :: br) => insert (b ++ r, n) (FeedHashTable (S n) br r h)
  end.

Functional Scheme FeedHashTable_ind := Induction for FeedHashTable Sort Prop.

Lemma EntryLensFeed : forall donelen done todo brs todo2 h,
                        donelen = ll done ->
                        done ++ brs ++ todo2 = done ++ todo ->
                        ForallHashTable (fun en => snd en < donelen) h ->
                        ForallHashTable (fun en => snd en < donelen + ll brs)
                                        (FeedHashTable donelen brs todo2 h).
Proof.
  intros donelen done todo brs. 
  revert brs donelen done todo.

  refine (fix f brs donelen done todo todo2 h leneq appeq all {struct brs} :=
            match brs as Brs return (brs = Brs -> _) with
              | [] => fun eq => _
              | (br :: brs') => fun eq => _
            end eq_refl).
  simpl.
  replace (donelen + 0) with donelen; [exact all | omega].
  assert (K : ForallHashTable (fun en => snd en < S donelen + ll brs')
                          (FeedHashTable (S donelen) brs' todo2 h)).
  apply (f brs' (S donelen) (done ++ [br]) (brs' ++ todo2) todo2 h).
  rewrite -> app_length; simpl; omega.
  reflexivity.
  apply (ForallHashTableImp (fun en => snd en < donelen)).
  intros [a1 a2].
  simpl.
  omega.
  exact all.
  simpl.
  apply ForallHashTableInsert.
  replace (donelen + S (ll brs')) with (S donelen + ll brs').
  exact K.
  omega.
  simpl.
  omega.
Qed.

Lemma EntryCorrectFeed : forall donelen done todo brs todo2 h,
                           donelen = ll done ->
                           done ++ brs ++ todo2 = done ++ todo ->
                           ForallHashTable (EntryCorrect (done ++ todo)) h ->
                           ForallHashTable (EntryCorrect (done ++ brs ++ todo2))
                                           (FeedHashTable donelen brs todo2 h).
Proof.
  intros donelen done todo brs.
  revert brs donelen done todo.
  induction brs as [|br brs IHbrs];
  [ intros donelen done todo todo2 h ldone eq ec1;
    rewrite -> eq;
    auto
  | intros donelen done todo todo2 h leneq appeq ec1;
    rewrite <- app_comm_cons;
    simpl;
    apply (EntryCorrectCons _ _ todo);
    [ auto
    | simpl; auto
    | replace (done ++ todo) with ((done ++ [br]) ++ brs ++ todo2);
      [ apply (IHbrs _ _ (brs ++ todo2));
        [ rewrite -> app_length; simpl; omega
        | reflexivity
        | rewrite <- app_assoc;
          simpl;
          simpl in appeq;
          rewrite -> appeq;
          exact ec1 ]
      | rewrite <- app_assoc;
        simpl;
        simpl in appeq;
        exact appeq ]]].
Qed.

Lemma RBRlenLemma1 : forall {A : Set} length dist (done donerbr : list A),
                       ResolveBackReference length dist done donerbr ->
                       ll done + length = ll donerbr.
Proof.
  intros A.
  induction length.
  intros dist done donerbr rbr.
  dependent destruction rbr.
  omega.

  intros dist done donerbr rbr.
  dependent destruction rbr.
  rewrite -> app_length.
  simpl.

  match goal with
    | X : _ |- ll ?A + S ?B = ll ?C + 1 =>
      assert (K : ll A + B = ll C);
        [ eapply IHlength;
          exact rbr
        | omega ]
  end.
Qed.

Lemma RBRlenLemma : forall {A : Set} length dist (done brx : list A),
                      ResolveBackReference length dist done (done ++ brx) ->
                      ll brx = length.
Proof.
  intros A length dist done brx rbr.
  assert (K : ll done + length = ll (done ++ brx)).
  eapply RBRlenLemma1.
  exact rbr.
  rewrite -> app_length in K.
  omega.
Qed.

Lemma makeBackReferences : forall (minlen maxlen mindist maxdist : nat) (l : LByte), minlen > 0 ->
                             {seq : SequenceWithBackRefs Byte |
                              BackRefsBounded minlen maxlen mindist maxdist seq /\
                              ResolveBackReferences seq l}.
Proof.
  intros minlen maxlen mindist maxdist l_ minlen_gt_0.
  refine ((fix f
               (done todo : LByte)
               (done_len : nat)
               (r_done_seq : SequenceWithBackRefs Byte)
               (done_res : ResolveBackReferences (rev r_done_seq) done)
               (done_brb : BackRefsBounded minlen maxlen mindist maxdist (rev r_done_seq))
               (m : nat) (h : HashTable)
               (hec : ForallHashTable (EntryCorrect (done ++ todo)) h)
               (entrylens : ForallHashTable (fun en => snd en < done_len) h)
               (inv1 : done ++ todo = l_)
               (inv2 : ll todo <= m)
               (inv3 : done_len = ll done)
               {struct m}
           : {seq : SequenceWithBackRefs Byte
             | BackRefsBounded minlen maxlen mindist maxdist seq
               /\ ResolveBackReferences seq (done ++ todo)}
           := _) [] l_ 0 [] _ _ (ll l_) (M.empty _) _ _ _ _ _);
    [ | constructor | constructor | apply ForallHashTableEmpty | apply ForallHashTableEmpty | 
      reflexivity | omega | reflexivity ].

  assert (singlestep : {seq : SequenceWithBackRefs Byte |
                        BackRefsBounded minlen maxlen mindist maxdist seq /\
                        ResolveBackReferences seq (done ++ todo)});
    [ destruct todo as [| t todo];
      [ (* todo = []: we're done *)
        exists (rev r_done_seq);
        rewrite -> app_nil_r;
        auto
      | (* best length is < 3: no backreference *)
        set (h2 := insert (t :: todo, done_len) h);
        set (r_done_seq_2 := inl t :: r_done_seq);
        assert (h2_hec : ForallHashTable (EntryCorrect (done ++ t :: todo)) h2);
        [ apply (EntryCorrectCons _ _ (t :: todo));
          [ auto
          | reflexivity
          | auto ]
        | assert (h2_entrylens : ForallHashTable (fun en : LByte * nat => snd en < (S done_len)) h2);
          [ replace done_len with (done_len + 0);
            [ eapply EntryLensCons;
              auto
            | omega]
          | assert (r_done_seq_2_rbr : ResolveBackReferences (rev r_done_seq_2) (done ++ [t]));
            [ unfold r_done_seq_2;
              rewrite -> cons_rev_1;
              constructor;
              auto
            | assert (r_done_seq_2_brb : BackRefsBounded minlen maxlen mindist maxdist (rev r_done_seq_2));
              [ unfold r_done_seq_2;
                rewrite -> cons_rev_1;
                apply app_forall;
                [ auto | constructor; constructor ]
              | destruct m as [|m];
                [ simpl in inv2;
                  omega
                | assert (k : (done ++ [t]) ++ todo = done ++ t :: todo);
                  [ rewrite <- app_assoc;
                    reflexivity
                  | rewrite <- k in h2_hec;
                    rewrite <- k;
                    apply (f (done ++ [t]) todo (S done_len) r_done_seq_2 r_done_seq_2_rbr r_done_seq_2_brb m h2 h2_hec h2_entrylens);
                    [ rewrite -> k; auto
                    | simpl in inv2; omega
                    | rewrite -> app_length;
                      simpl;
                      omega ]]]]]]]]
    | ].


  destruct (makeSingleBackReference maxlen maxdist done_len done todo (search (todo, done_len) h))
    as [[length [dist [todo2 [brx [rbr [dtd [lml dmd]]]]]]]|];
  [ auto
  | apply ForallHashTableSearch;
    exact hec
  | apply ForallHashTableSearch;
    exact entrylens
  | destruct (le_dec minlen length) as [e | e];
    [ destruct (le_dec mindist dist) as [d | d];
    [ assert (brxlen : ll brx = length);
      [ eapply RBRlenLemma; eauto
      | destruct m;
        [ destruct todo;
          [ assert (dtd' : [] = brx ++ todo2);
            [ eapply app_cancel_l;
              exact dtd
            | destruct brx;
              [ destruct length;
                [ omega
                | simpl in brxlen;
                  omega ]
              | inversion dtd' ]]
          | simpl in inv2;
            omega ]
        | set (h2 := FeedHashTable done_len brx todo2 h);
          rewrite -> dtd;
          rewrite -> app_assoc;
          eapply (f (done ++ brx) todo2 (done_len + length) (inr (length, dist) :: r_done_seq) _ _ m h2);
          [ rewrite <- app_assoc;
            eapply EntryCorrectFeed;
            [ auto
            | symmetry;
              exact dtd
            | auto ]
          | unfold h2;
            rewrite <- brxlen;
            eapply EntryLensFeed;
            [ exact inv3
            | symmetry; exact dtd
            | auto ]
          | rewrite <- app_assoc;
            rewrite <- dtd;
            auto
          | assert (TD : ll todo = ll (brx ++ todo2));
            [ f_equal;
              eapply app_cancel_l;
              exact dtd
            | rewrite -> app_length in TD; omega ]
          | rewrite -> app_length; omega ]]]
    | apply singlestep ]
    | apply singlestep ]
  | apply singlestep ].

Grab Existential Variables.
simpl.
apply app_forall.
auto.
constructor.
constructor.
auto.
auto.
auto.
auto.
constructor.

simpl.
econstructor.
eauto.
auto.
Qed.

(* this is just a tool for the below proof. there is no need for it to
be absolutely correct, as we only use it to automate our proof. *)

Fixpoint find_interval_index
         (bases maxs : list nat) (value default zero : nat) : nat :=
  match bases with
    | [] => default
    | (base :: bases') =>
      match maxs with
        | [] => default
        | (max :: maxs') =>
          match le_dec base value with
            | (left _) =>
              match le_dec value max with
                | (left _) => zero
                | (right _) => find_interval_index bases' maxs' value default (S zero)
              end
            | (right _) => find_interval_index bases' maxs' value default (S zero)
          end
      end
  end.

Lemma EncodeLengthStatic_ :
  forall (len : nat),
    3 <= len ->
    len <= 258 ->
    {n : nat | n < ll repeatCodeBase /\
               nth n repeatCodeBase 259 <= len /\
               len <= nth n repeatCodeMax 2 }.
Proof.
  intros l lmin lmax.
  set (L := l).
  repeat (destruct l as [|l]; [solve [omega] | idtac]).
  do 256 (destruct l as [|l]; [solve [exists (find_interval_index repeatCodeBase repeatCodeMax L 259 0); compute; omega] | idtac]).
  abstract(omega).
Defined.

Lemma EncodeLengthStatic__ :
  forall (l m o n : nat),
    n < ll repeatCodeBase ->
    nth n repeatCodeMax l - nth n repeatCodeBase m < 2 ^ nth n repeatCodeExtraBits o.
Proof.
  intros ? ? ? n.
  do 29 (destruct n as [|n]; [compute;omega|idtac]).
  compute; omega.
Defined.

(* todo: elsewhere *)
Lemma Vnth_is_Vnth : forall (A : Type) (m n : nat) (v : vec A m) (e : n < m),
                       Vnth_is m n v (Vnth v (Fin.of_nat_lt e)).
Proof.
  intro A. 
  induction m.
  intros ? ? e.
  omega.
  intros n v e.
  dependent destruction v.
  destruct n.
  constructor.
  constructor.
  apply IHm.
Qed.

(* todo: elsewhere *)
Lemma static_litlen_full :
  forall n (nlt : n < 288),
    Vnth (C _ fixed_lit_code) (Fin.of_nat_lt nlt) <> [].
Proof.
  intros n nlt.
  assert (R : Vnth vector_for_fixed_lit_code (Fin.of_nat_lt nlt) = ll (Vnth (C 288 fixed_lit_code) (Fin.of_nat_lt nlt)));
  [ unfold fixed_lit_code;
    destruct fixed_lit_code_ex as [a b] eqn:abeq;
    rewrite <- abeq;
    replace (Vnth vector_for_fixed_lit_code (Fin.of_nat_lt nlt))
    with (Vnth (Vmap lb (C 288 a)) (Fin.of_nat_lt nlt));
    [ erewrite nth_map;
      [ rewrite -> abeq;
        simpl;
        reflexivity
      | reflexivity ]
    | rewrite -> b;
      reflexivity ]
  | intro Q;
    rewrite -> Q in R;
    do 288 (destruct n; [ simpl in R; abstract(omega) | idtac ]);
    abstract(omega) ].
Qed.

(* todo: elsewhere *)
Lemma static_dist_full :
  forall n (nlt : n < 32),
    Vnth (C _ fixed_dist_code) (Fin.of_nat_lt nlt) <> [].
Proof.
  intros n nlt.
  assert (R : Vnth vector_for_fixed_dist_code (Fin.of_nat_lt nlt) = ll (Vnth (C _ fixed_dist_code) (Fin.of_nat_lt nlt)));
  [ unfold fixed_dist_code;
    destruct fixed_dist_code_ex as [a b] eqn:abeq;
    rewrite <- abeq;
    replace (Vnth vector_for_fixed_dist_code (Fin.of_nat_lt nlt))
    with (Vnth (Vmap lb (C _ a)) (Fin.of_nat_lt nlt));
    [ erewrite nth_map;
      [ rewrite -> abeq;
        simpl;
        reflexivity
      | reflexivity ]
    | rewrite -> b;
      reflexivity ]
  | intro Q;
    rewrite -> Q in R;
    do 32 (destruct n; [ simpl in R; abstract(omega) | idtac ]);
    abstract(omega) ].
Qed.

Lemma EncodeLengthStatic :
  forall (len : nat),
    3 <= len ->
    len <= 258 ->
    {l : LB | CompressedLength fixed_lit_code len l}.
Proof.
  intros l lmin lmax.
  destruct (EncodeLengthStatic_ l lmin lmax) as [n [nl [nmin nmax]]].
  assert (Q : l - nth n repeatCodeBase 259 < 2 ^ nth n repeatCodeExtraBits 259);
  [ assert (nth n repeatCodeMax 2 - nth n repeatCodeBase 259 < 2 ^ nth n repeatCodeExtraBits 259);
    [ apply (EncodeLengthStatic__ 2 259 259 n nl)
    | omega ] | idtac ].

  destruct (NatToList _ _ Q) as [L lsb_L ll_L].
  assert (char_ok : 257 + n < 288); [ compute in nl; omega | idtac ].
  exists (Vnth (C _ fixed_lit_code) (Fin.of_nat_lt char_ok) ++ L).
  assert (R : l = nth n repeatCodeBase 259 + (l - nth n repeatCodeBase 259));
  [ omega
  | rewrite -> R;
    eapply (complength _ _ _ _ _ _ _ _ (nth n repeatCodeMax 259) (nth n repeatCodeExtraBits 259));
    [ split;
      [ apply Vnth_is_Vnth
      | apply static_litlen_full ]
    | simpl in nl;
      unfold repeatCodeExtraBits;
      abstract
        (do 29 (destruct n as [|n]; [simpl;reflexivity|idtac]);
         omega)
    | simpl in nl;
      unfold repeatCodeBase;
      abstract
        (do 29 (destruct n as [|n]; [simpl;reflexivity|idtac]);
         omega)
    | simpl in nl;
      unfold repeatCodeMax;
      abstract
        (do 29 (destruct n as [|n]; [simpl;reflexivity|idtac]);
         omega)
    | auto
    | auto
    | replace (nth n repeatCodeMax 259) with (nth n repeatCodeMax 2);
      [ abstract(omega)
      | apply nth_indep;
        auto ]]].
Defined.

Require Import String.
Require Import BinNat.

Local Open Scope Z_scope.

(* TODO: This would not be necessary if we changed the definition of
strToNat in Shorthand.v, and we should do so and merge this into the
dissertation text *)

Fixpoint strToNat_' (str : string) (n : nat) : option nat :=
  match str with
    | EmptyString => Some n
    | String "0" str => strToNat_' str ((10 * n) + 0)
    | String "1" str => strToNat_' str ((10 * n) + 1)
    | String "2" str => strToNat_' str ((10 * n) + 2)
    | String "3" str => strToNat_' str ((10 * n) + 3)
    | String "4" str => strToNat_' str ((10 * n) + 4)
    | String "5" str => strToNat_' str ((10 * n) + 5)
    | String "6" str => strToNat_' str ((10 * n) + 6)
    | String "7" str => strToNat_' str ((10 * n) + 7)
    | String "8" str => strToNat_' str ((10 * n) + 8)
    | String "9" str => strToNat_' str ((10 * n) + 9)
    | _ => None
  end.

Function strToNat' (str : string) := strToNat_' str 0.

Lemma strToNat__ : forall str, strToNat' str = strToNat str.
Proof.
  induction str; [reflexivity | compute; reflexivity].
Qed.

(*Require Import Coq.Numbers.Cyclic.Int31.Int31.
Require Import Coq.Numbers.Cyclic.Int31.Cyclic31.

Local Open Scope int31_scope.

Fixpoint strToInt31_ (str : string) (n : int31) : option int31 :=
  match str with
    | EmptyString => Some n
    | String "0" str => strToInt31_ str ((10 * n) + 0)
    | String "1" str => strToInt31_ str ((10 * n) + 1)
    | String "2" str => strToInt31_ str ((10 * n) + 2)
    | String "3" str => strToInt31_ str ((10 * n) + 3)
    | String "4" str => strToInt31_ str ((10 * n) + 4)
    | String "5" str => strToInt31_ str ((10 * n) + 5)
    | String "6" str => strToInt31_ str ((10 * n) + 6)
    | String "7" str => strToInt31_ str ((10 * n) + 7)
    | String "8" str => strToInt31_ str ((10 * n) + 8)
    | String "9" str => strToInt31_ str ((10 * n) + 9)
    | _ => None
  end.
Function strToInt31 (strn : string) : option int31 := strToInt31_ strn 0.

Definition D (s : string) :=
  forceOption int31 parseError (strToInt31 s) ParseError.*)

Require Import BinInt.

Open Scope Z_scope.

Fixpoint strToZ_ (str : string) (n : Z) : option Z :=
   match str with
     | EmptyString => Some n
     | String "0" str => strToZ_ str ((10 * n) + 0)
     | String "1" str => strToZ_ str ((10 * n) + 1)
     | String "2" str => strToZ_ str ((10 * n) + 2)
     | String "3" str => strToZ_ str ((10 * n) + 3)
     | String "4" str => strToZ_ str ((10 * n) + 4)
     | String "5" str => strToZ_ str ((10 * n) + 5)
     | String "6" str => strToZ_ str ((10 * n) + 6)
     | String "7" str => strToZ_ str ((10 * n) + 7)
     | String "8" str => strToZ_ str ((10 * n) + 8)
     | String "9" str => strToZ_ str ((10 * n) + 9)
     | _ => None
   end.

Function strToZ (strn : string) : option Z := strToZ_ strn 0.

Definition D (s : string) :=
  forceOption Z parseError (strToZ s) ParseError.

Require Import Coq.Strings.Ascii.

Local Open Scope char_scope.
(*Lemma strToInt31n':
  forall x n m N M,
       N.of_nat m = M ->
       strToNat_' x m = Some n ->
       strToN_ x M = Some N ->
       N.of_nat n = N.
Proof.
  induction x as [|a x IHx].

  intros n m N M mM n_ N_.

  inversion n_.
  inversion N_.
  replace n with m.
  replace N with M.
  exact mM.

  intros n m N M mM n_ N_.

  assert (asciis : N.of_nat (10 * m + (nat_of_ascii a - nat_of_ascii "0")) =
                   (10 * M + (N_of_ascii a - N_of_ascii "0")));
  [ unfold nat_of_ascii;
    rewrite <- Nnat.N2Nat.inj_sub;
    rewrite -> Nnat.Nat2N.inj_add;
    rewrite -> Nnat.N2Nat.id;
    f_equal;
    rewrite -> Nnat.Nat2N.inj_mul;
    rewrite -> mM;
    reflexivity
  | ].

  refine (match a as X return (a=X->_) with
              | "0" => fun eq => _
              | "1" => fun eq => _
              | "2" => fun eq => _
              | "3" => fun eq => _
              | "4" => fun eq => _
              | "5" => fun eq => _
              | "6" => fun eq => _
              | "7" => fun eq => _
              | "8" => fun eq => _
              | "9" => fun eq => _
              | _ => fun eq => _
            end eq_refl);
    (solve [ rewrite -> eq in n_;
             inversion n_
           | assert (n__ : strToNat_' (String a x) m = strToNat_' x (10 * m + (nat_of_ascii a - nat_of_ascii "0")));
             [ rewrite -> eq;
               reflexivity
             | assert (N__ : strToN_ (String a x) M = strToN_ x (10 * M + (N_of_ascii a - N_of_ascii "0")));
               [ rewrite -> eq;
                 reflexivity
               | rewrite -> n__ in n_;
                 rewrite -> N__ in N_;
                 apply (IHx _ _ _ _ asciis n_ N_) ]]]).
Qed.

Lemma strToNn:
  forall x n N, strToNat x = Some n ->
                strToN x = Some N ->
                N.of_nat n = N.
Proof.
  intros x n N.
  rewrite <- strToNat__.
  unfold strToNat'.
  unfold strToN.
  apply strToNn'.
  reflexivity.
Qed.*)

(* AAAND the same again for distances. however, we need N this time, because coq doesn't do well with large nats. *)

(* Fixpoint find_interval_index_int31
         (bases maxs : list int31) (value : int31) (default zero : nat) : nat :=
  match bases with
    | [] => default
    | (base :: bases') =>
      match maxs with
        | [] => default
        | (max :: maxs') =>
          match base ?= value with
            | Gt => find_interval_index_int31 bases' maxs' value default (S zero)
            | _ =>
              match value ?= max with
                | Gt => find_interval_index_int31 bases' maxs' value default (S zero)
                | _ => zero
              end
          end
      end
  end. *)

Definition distCodeBase' :=
  [ D"1"     ; D"2"     ; D"3"     ; D"4"     ;
    D"5"     ; D"7"     ; D"9"     ; D"13"    ;
    D"17"    ; D"25"    ; D"33"    ; D"49"    ;
    D"65"    ; D"97"    ; D"129"   ; D"193"   ;
    D"257"   ; D"385"   ; D"513"   ; D"769"   ;
    D"1025"  ; D"1537"  ; D"2049"  ; D"3073"  ;
    D"4097"  ; D"6145"  ; D"8193"  ; D"12289" ;
    D"16385" ; D"24577" ].

Definition distCodeMax' :=
  [ D"1"     ; D"2"     ; D"3"     ; D"4"     ;
    D"6"     ; D"8"     ; D"12"    ; D"16"    ;
    D"24"    ; D"32"    ; D"48"    ; D"64"    ;
    D"96"    ; D"128"   ; D"192"   ; D"256"   ;
    D"384"   ; D"512"   ; D"768"   ; D"1024"  ;
    D"1536"  ; D"2048"  ; D"3072"  ; D"4096"  ;
    D"6144"  ; D"8192"  ; D"12288" ; D"16384" ;
    D"24576" ; D"32768" ].

Lemma distCodeBase'correct : map Z.of_nat distCodeBase = distCodeBase'.
Proof.
  unfold distCodeBase.
  unfold map.
  unfold d.
  unfold forceOption.
  unfold strToNat.

  repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul).
  reflexivity.
Qed.

Lemma distCodeMax'correct : map Z.of_nat distCodeMax = distCodeMax'.
Proof.
  unfold distCodeMax.
  unfold map.
  unfold d.
  unfold forceOption.
  unfold strToNat.

  repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul).
  reflexivity.
Qed.

Lemma distClosed : Closed 1 32768 distCodeBase' distCodeMax'.
Proof.
  exact (projT2 (ClosedDec' 1 32768 distCodeBase' distCodeMax')).
Qed.
  
Lemma EncodeDistStatic_ :
  forall (dist : Z),
    1 <= dist ->
    dist <= 32768 ->
    {n : nat | (n < ll distCodeBase')%nat /\
               nth n distCodeBase' 32769 <= dist /\
               dist <= nth n distCodeMax' 0}.
Proof.
  intros e emin emax.
  destruct (ClosedTable e _ _ distCodeBase' distCodeMax' distClosed) as [x a]; [ auto | ].
  exists x.
  split.
  apply a.
  apply a.
Defined.

Lemma EncodeDistStatic__ :
  forall (l m : Z) (n o : nat),
    (n < ll distCodeBase')%nat ->
    nth n distCodeMax' l - nth n distCodeBase' m < 2 ^ Z.of_nat (nth n distCodeExtraBits o).
Proof.
  intros ? ? n ?.
  do 31 (destruct n as [|n]; [compute;auto|idtac]).

  omega.
  compute.
  omega.
Defined.

(* TODO: gibts vmtl woanders *)
Lemma Zpow_inj : forall n m, Z.of_nat (n ^ m) = Z.of_nat n ^ Z.of_nat m.
Proof.
  intro n;
  induction m as [|m IHm].
  reflexivity.
  replace (n ^ S m)%nat with (n * n ^ m)%nat; [ | reflexivity ].

  rewrite -> Znat.Nat2Z.inj_succ.
  rewrite -> Z.pow_succ_r.
  rewrite -> Znat.Nat2Z.inj_mul.
  rewrite -> IHm.
  reflexivity.
  omega.
Defined.

(* TODO: nach Combi.v *)
Lemma nth_error_ll :
  forall {B} n l (m : B),
    nth_error l n = Some (nth n l m) <-> (n < ll l)%nat.
Proof.
  intros B n l m.
  revert n l.
  refine (fix f n l :=
            match n as n' return (n = n' -> _) with
              | 0%nat => fun eqN =>
                           match l as l' return (l = l' -> _) with
                             | nil => fun eqL => _
                             | (x :: L) => fun eqL => _
                           end eq_refl
              | (S N) => fun eqN =>
                           match l as l' return (l = l' -> _) with
                             | nil => fun eqL => _
                             | (x :: L) => fun eqL => _
                           end eq_refl
            end eq_refl);
    [ rewrite -> eqL;
      rewrite -> eqN;
      split;
      intro Q;
      inversion Q
    | rewrite -> eqL;
      rewrite -> eqN;
      simpl;
      split;
      [ intro Q;
        apply Lt.lt_0_Sn
      | reflexivity ]
    | rewrite -> eqL;
      rewrite -> eqN;
      split;
      intro Q;
      inversion Q
    | rewrite -> eqL;
      rewrite -> eqN;
      split;
      [ simpl;
        intro Q;
        apply Lt.lt_n_S;
        apply f;
        exact Q
      | simpl;
        intro Q;
        apply f;
        apply Lt.lt_S_n;
        exact Q ]].
Qed.

Lemma EncodeDistStatic :
  forall (dist : nat),
    (1 <= dist)%nat ->
    (dist <= d"32768")%nat ->
    {l : LB | CompressedDist fixed_dist_code dist l}.
Proof.
  intros e' emin' emax'.
  set (e := Z.of_nat e').
  assert (emin: 1 <= e).
  unfold e.
  omega.

  assert (emax: e <= D"32768").
  unfold e.
  replace (D"32768") with (Z.of_nat (d"32768")).
  omega.
  unfold d.
  unfold strToNat.
  unfold forceOption.
  unfold D.
  unfold strToZ.
  unfold strToZ_.
  unfold forceOption.

  repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul).
  reflexivity.

  destruct (EncodeDistStatic_ e emin emax) as [n [nl [nmin nmax]]].

  assert (Q : e - nth n distCodeBase' 32769 < 2 ^ Z.of_nat (nth n distCodeExtraBits (d"32769")));
  [ assert (nth n distCodeMax' 0 - nth n distCodeBase' 32769 < 2 ^ Z.of_nat (nth n distCodeExtraBits (d"32769")));
    [ apply (EncodeDistStatic__ _ _ _ _ nl)
    | omega ]
  | idtac ].

  assert (N : Z.of_nat (d"32769") = 32769);
  [ unfold d;
    unfold strToNat;
    unfold forceOption;
    repeat (rewrite -> Znat.Nat2Z.inj_add || rewrite -> Znat.Nat2Z.inj_mul);
    reflexivity
  | assert (R : Z.of_nat (nth n distCodeBase (d"32769")) =
                nth n distCodeBase' 32769);
    [ rewrite <- distCodeBase'correct;
      rewrite <- N;
      rewrite -> map_nth;
      reflexivity
    | assert (T : Z.of_nat (nth n distCodeMax 0%nat) =
                  nth n distCodeMax' 0);
      [ rewrite <- distCodeMax'correct;
        replace 0 with (Z.of_nat 0);
        [ rewrite -> map_nth;
          reflexivity
        | reflexivity]
      | ]]].

  assert (Q' : (e' - nth n distCodeBase (d"32769") <
                2 ^ (nth n distCodeExtraBits (d "32769")))%nat);
  [ assert (Q1 : Z.of_nat (e' - nth n distCodeBase (d "32769"))%nat =
                 e - nth n distCodeBase' 32769);
    [ rewrite -> Znat.Nat2Z.inj_sub;
      [ unfold e;
        f_equal;
        apply R
      | apply Znat.Nat2Z.inj_le;
        rewrite -> R;
        exact nmin ]
    | apply Znat.Nat2Z.inj_lt;
      rewrite -> Q1;
      rewrite -> Zpow_inj;
      apply Q ]
   | ].

  destruct (NatToList _ _ Q') as [L lsb_L ll_L].
  assert (char_ok : (n < 32)%nat);
    [ compute in nl; omega | idtac ].
  exists (Vnth (C _ fixed_dist_code) (Fin.of_nat_lt char_ok) ++ L).

  assert (U : (e' = nth n distCodeBase (d "32769") + (e' - nth n distCodeBase (d "32769")))%nat);
  [ apply Znat.Nat2Z.inj;
    rewrite -> Znat.Nat2Z.inj_add;
    rewrite -> Znat.Nat2Z.inj_sub;
    [ omega
    | apply Znat.Nat2Z.inj_le;
      rewrite -> R;
      auto ]
  | ].
  rewrite -> U.
  eapply (complength _ _ _ _ _ _ _ _ (nth n distCodeMax 0%nat) (nth n distCodeExtraBits (d "32769")));
  [ split;
    [ apply Vnth_is_Vnth
    | apply static_dist_full ]
  | apply nth_error_ll;
    exact nl
  | apply nth_error_ll;
    exact nl
  | apply nth_error_ll;
    exact nl
  | exact ll_L
  | exact lsb_L
  | assert (e' <= nth n distCodeMax 0)%nat;
    [ apply Znat.Nat2Z.inj_le;
      rewrite -> T;
      exact nmax
    | omega ]].
Defined.

Open Scope nat_scope.

Lemma EncodeSWBRStatic :
  forall (s : SequenceWithBackRefs Byte),
         BackRefsBounded 3 258 1 (d"32768") s ->
         { l : LB | CompressedSWBR fixed_lit_code fixed_dist_code s l }.
Proof.
  induction s as [|c s];
  [ intro brb;
    eexists (Vnth (C _ fixed_lit_code) (@Fin.of_nat_lt 256 _ _));
    constructor;
    split; [ apply Vnth_is_Vnth | apply static_litlen_full ]
  | intro brb;
    destruct c as [c | [l d]];
    [ destruct IHs as [l' ihs'];
      [ inversion brb;
        auto
      | exists (Vnth (C _ fixed_lit_code) (ByteToFin288 c) ++ l');
        constructor;
        [ split; [ apply Vnth_is_Vnth | apply static_litlen_full ]
        | exact ihs' ]]
    | destruct (EncodeLengthStatic l) as [cl clx];
      [ inversion brb;
        match goal with
          | H : BackRefBounded _ _ _ _ _ |- _ => inversion H; omega
        end
      | inversion brb;
        match goal with
          | H : BackRefBounded _ _ _ _ _ |- _ => inversion H; omega
        end
      | destruct (EncodeDistStatic d) as [cd cdx];
        [ inversion brb;
          match goal with
            | H : BackRefBounded _ _ _ _ _ |- _ => inversion H; omega
          end
        | inversion brb;
          match goal with
            | H : BackRefBounded _ _ _ _ _ |- _ => inversion H; omega
          end
        | destruct IHs as [l' ihs'];
          [ inversion brb;
            auto
          | exists (cl ++ cd ++ l');
            constructor;
            auto ]]]]].    
  Grab Existential Variables.
  omega.
Defined.

Lemma compress : forall (l : LByte),
                   {b : LB | DeflateEncodes l b}.
Proof.
  intro l.
  destruct (makeBackReferences 3 258 1 (d"32768") l) as [x [brb rb]].
  omega.
  destruct (EncodeSWBRStatic x brb) as [b c].
  exists (true :: true :: false :: b).
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  exact c.
  exact rb.
Qed.

Extraction Language Haskell.

Definition compressX := fun l => ` (compress l).

(** Strings *)

Extract Inductive ascii => "Data.Char.Char" ["Extraction.makechar"] "Extraction.charrec".

Extract Inductive string => "[Data.Char.Char]" ["[]" "(:)"] "Extraction.stringrec".

(** Several simple types mapped to Haskell-standard-types *)

Extract Inductive prod => "(,)" ["(,)"] "Extraction.prodrec".
Extract Constant fst => "Prelude.fst".
Extract Constant snd => "Prelude.snd".

Extract Inductive option => "Data.Maybe.Maybe" [ "Data.Maybe.Just" "Data.Maybe.Nothing" ].

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"] "Extraction.sumboolrec".

Extract Inductive sumor => "Data.Maybe.Maybe" [ "Data.Maybe.Just" "Data.Maybe.Nothing" ]
                                              "Extraction.sumorrec".

Extract Inductive comparison => "Extraction.Cmp" ["Extraction.Eq" "Extraction.Lt" "Extraction.Gt"]
                                                 "Extraction.cmprec".

(** Constants for nat *)

Extract Inductive nat => "Prelude.Int" [ "0" "Extraction.natinc" ]
                                       "Extraction.natrec".
(*                               "( let r z s n = case n of {0 -> z 0 ; q -> s (q Prelude.- 1)} in r )".*)


(** Fin is just nat with an index that is not relevant *)
Extract Inductive fin => "Extraction.Fin" [ "Extraction.fin1" "Extraction.fins" ] "Extraction.finrec".

Extract Constant lt_eq_lt_dec => "Extraction.lt_eq_lt_dec".

Extract Constant le_lt_dec => "(Prelude.<=)".

Extract Constant nat_compare => "Extraction.nat_compare".

Extract Constant plus => "(Prelude.+)".

Extract Constant mult => "(Prelude.*)".

Extract Constant minus => "Extraction.natminus".

(*Extract Constant eq_nat_dec => "(Prelude.==)".*)

Extract Constant pow => "(Prelude.^)".

Extract Inductive list => "[]" [ "[]" "(\ a b -> a : b)" ]
                               "(\ n c l -> case l of { [] -> n [] ; (b : bs) -> c b bs })".

Extraction "CompressX.hs" compressX.