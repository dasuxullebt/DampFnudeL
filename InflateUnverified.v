Require Import Omega.
Require Import Recdef.
Require Import Coq.Arith.Euclid.
Require Import Coq.Lists.List.
Require Import DeflateNotations.
Require Import Lex.
Require Import Transports.
Require Import Prefix.
Require Import Repeat.
Require Import Combi.
Require Import KraftList.
Require Import KraftVec.

Inductive BackBufferBase (A : Set) : Set :=
| bbnil : BackBufferBase A
| bbcons1 : A -> BackBufferBase (A * A)%type -> BackBufferBase A
| bbcons2 : A -> A -> BackBufferBase (A * A)%type -> BackBufferBase A.

Record BackBufferWithLength (A : Set) : Set :=
  mkBackBufferWithLength {
      l : nat ;
      buffer : BackBufferBase A
    }.

Fixpoint bbbcons {A : Set} (x : A) (bbb : BackBufferBase A) : BackBufferBase A :=
  match bbb with
    | bbnil _ => bbcons1 A x (bbnil (A * A)%type)
    | bbcons1 _ a bb => bbcons2 A x a bb
    | bbcons2 _ a b bb => bbcons1 A x (bbbcons (a, b) bb)
  end.

Function bbwlcons {A : Set} (x : A) (bbwl : BackBufferWithLength A) : BackBufferWithLength A :=
  mkBackBufferWithLength A (S (l A bbwl)) (bbbcons x (buffer A bbwl)).

Lemma bbbget {A : Set} (nn : nat) (bbbb : BackBufferBase A) : option A.
  refine
    ((fix rec (B : Set) (bbb : BackBufferBase B) (n : nat) : option B :=
       match bbb with
         | bbnil _ => error
         | bbcons1 _ a bb =>
           match n with
             | 0 => value a
             | (S n') =>
               match (eucl_dev 2 _ n') with
                 | divex _ _ q r _ _ =>
                   option_map  (match r with
                                  | 0 => fst
                                  | _ => snd
                                end) (rec (B * B)%type bb q)
               end
           end
         | bbcons2 _ a b bb =>
           match n with
             | 0 => value a
             | 1 => value b
             | (S (S n')) =>
               match (eucl_dev 2 _ n') with
                 | divex _ _ q r _ _ =>
                   option_map  (match r with
                                  | 0 => fst
                                  | _ => snd
                                end) (rec (B * B)%type bb q) 
               end
           end
       end) A bbbb nn).
  omega.
  omega.
Defined.

Function bbwlget {A : Set} (n : nat) (bbwl : BackBufferWithLength A) : option A :=
  match (Compare_dec.lt_dec n (l A bbwl)) with (* this is for efficiency *)
    | left _ => bbbget n (buffer A bbwl)
    | right _ => error
  end.

Record BackBuffer (A : Set) : Set :=
  mkBackBuffer {
      length : nat ;
      topbuf : BackBufferWithLength A ;
      botbuf : BackBufferWithLength A
    }.

Function bbcons {A : Set} (x : A) (bb : BackBuffer A) : BackBuffer A :=
  match Compare_dec.le_dec (l A (topbuf A bb)) (length A bb) with
    | left _ => mkBackBuffer A (length A bb) (bbwlcons x (topbuf A bb)) (botbuf A bb)
    | right _ => mkBackBuffer (* move topbuffer to bottom, drop botbuffer, start new buffer *)
                   A
                   (length A bb)
                   (mkBackBufferWithLength A 1
                                           (bbcons1 A x (bbnil (A * A)%type)))
                   (topbuf A bb)
  end.

Function bbget {A : Set} (n : nat) (bb : BackBuffer A) : option A :=
  match Compare_dec.le_dec n (length A bb) with
    | left _ =>
      match (bbwlget n (topbuf A bb)) with
        | Some a => value a
        | None => bbwlget (n - (l A (topbuf A bb))) (botbuf A bb)
      end
    | right _ => error
  end.

Inductive BitByteList : Set :=
  | BBLNil : BitByteList
  | BBLConsBit : bool -> BitByteList -> BitByteList
  | BBLConsByte : Byte -> BitByteList -> BitByteList -> BitByteList.

Fixpoint bbllength (bbl : BitByteList) : nat :=
  match bbl with
    | BBLNil => 0
    | BBLConsBit _ bb => S (bbllength bb)
    | BBLConsByte _ bb _ => bbllength bb
  end.

(* this function requires laziness *)
Fixpoint LByteToBBL (lb : LByte) :  BitByteList :=
  match lb with
    | nil => BBLNil
    | (x :: L) =>
      let next := (LByteToBBL L) in
      BBLConsByte x
                  ((fix f b c :=
                    match b with
                      | nil => c
                      | (bb :: bbb) => BBLConsBit bb (f bbb c)
                    end) (rev (VectorDef.to_list x)) next) next
  end.

Fixpoint nextBit (BBL : BitByteList) : option (bool * BitByteList) :=
  match BBL with
    | BBLNil => None
    | BBLConsBit bit bb => Some (bit, bb)
    | BBLConsByte _ bb _ => nextBit bb
  end.

Fixpoint nBits (BBL : BitByteList) (n : nat) : option (LB * BitByteList) :=
  match n with
    | 0 => Some (nil, BBL)
    | (S n) => match nextBit BBL with
                 | None => None
                 | Some (bit, rest) =>
                   option_map (fun x => (bit :: fst x, snd x)) (nBits rest n)
               end
  end.

Fixpoint lsbToInt (l : LB) : nat :=
  match l with
    | nil => 0
    | false :: R => 2 * (lsbToInt R)
    | true :: R => S (2 * (lsbToInt R))
  end.

Definition StreamEndedEarly := 1.
Definition WrongBlockHeader := 2.

Inductive CoqCantIntoMutualRecursion : Set :=
| Start : CoqCantIntoMutualRecursion
| BlockParse : bool -> CoqCantIntoMutualRecursion
| UncompressedBlockParse : bool -> CoqCantIntoMutualRecursion
| UncompressedBlockPass : nat -> bool -> CoqCantIntoMutualRecursion
| DynamicallyCompressedBlockParse : bool -> CoqCantIntoMutualRecursion
| StaticallyCompressedBlockParse : bool -> CoqCantIntoMutualRecursion.

(* if there is some error, "onerror" is called with a number *)
Function inflate (status : CoqCantIntoMutualRecursion) (input : BitByteList) (back : BackBuffer Byte)
         (onerror :  CoqCantIntoMutualRecursion -> BitByteList -> nat -> LByte) {measure bbllength input} : LByte :=
  match status with
    | Start => match (nextBit input) with
                 | None => onerror Start input StreamEndedEarly
                 | Some (bit, rest) => inflate (BlockParse bit) rest back onerror
               end
    | BlockParse x =>
      match (nBits input 2) with
        | None => onerror (BlockParse x) input StreamEndedEarly
        | Some (lb, rest) =>
          match lb with
            | false :: false :: nil => inflate (UncompressedBlockParse x) rest back onerror
            | false :: true :: nil => inflate (DynamicallyCompressedBlockParse x) rest back onerror
            | true :: false :: nil => inflate (StaticallyCompressedBlockParse x) rest back onerror
            | _ => onerror (BlockParse x) rest WrongBlockHeader
          end
      end
    | UncompressedBlockParse x => (* first, overjump bits *)
      match input with
        | BBLConsBit bit rest => inflate (UncompressedBlockParse x) rest back onerror
        | BBLConsByte _ bb _ =>
          match nBits bb 16 with
            | None => onerror (UncompressedBlockParse x) bb 0
            | Some (bits1, bbb) =>
              match nBits bbb 16 with
                | None => onerror (UncompressedBlockParse x) bb 1
                | Some (bits2, rest) =>
                  (fix f a b :=
                           match (a, b) with
                             | (true :: L1, true :: L2) => f L1 L2
                             | (false :: L1, false :: L2) => f L1 L2
                             | (nil, nil) => inflate (UncompressedBlockPass (lsbToInt bits1) x) rest back onerror
                             | _ => onerror (UncompressedBlockParse x) rest 2
                           end) bits1 bits2
              end
          end
        | _ => onerror (UncompressedBlockParse x) input 3
      end
    | UncompressedBlockPass n x => (* pass bytes *)
      match n with
        | 0 => match x with
                 | false => inflate Start input back onerror
                 | true => nil (* last block *)
               end
        | (S n) =>
          match input with
            | BBLConsByte byte _ bb => byte :: inflate (UncompressedBlockPass n x) bb (bbcons byte back) onerror
            | _ => onerror (UncompressedBlockPass n x) input 0
          end
      end
    | _ => onerror Start input 9
  end.