(** This file contains the Encoding Relation for the Deflate bit
format. It is the core component of the verified implementation. It is
_axiomatic_, and therefore the single point of failure: It specifies a
compression format, but there is no guarantee that the specified
format is actually what the world understands as "deflate". We refer
to RFC 1951 in this file. *)

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

Local Open Scope nat_scope.

(** See RFC 1951, section 3.2.5. *)
Definition repeatCodeExtraBits : list nat :=
  [ d"0" ; d"0" ; d"0" ; d"0" ; d"0" ; d"0" ; d"0" ; d"0" ;
    d"1" ; d"1" ; d"1" ; d"1" ;
    d"2" ; d"2" ; d"2" ; d"2" ;
    d"3" ; d"3" ; d"3" ; d"3" ;
    d"4" ; d"4" ; d"4" ; d"4" ;
    d"5" ; d"5" ; d"5" ; d"5" ;
    d"0" ].

(** See RFC 1951, section 3.2.5. *)
Definition repeatCodeBase : list nat :=
  [ d"3" ; d"4" ; d"5" ; d"6" ; d"7" ; d"8" ; d"9" ; d"10" ;
    d"11" ; d"13" ; d"15" ; d"17" ;
    d"19" ; d"23" ; d"27" ; d"31" ;
    d"35" ; d"43" ; d"51" ; d"59" ;
    d"67" ; d"83" ; d"99" ; d"115" ;
    d"131" ; d"163" ; d"195" ; d"227" ;
    d"258" ].

(** See RFC 1951, section 3.2.5. *)
Definition repeatCodeMax : list nat :=
  [ d"3"; d"4"; d"5"; d"6"; d"7"; d"8"; d"9"; d"10";
    d"12"; d"14"; d"16"; d"18";
    d"22"; d"26"; d"30"; d"34";
    d"42"; d"50"; d"58"; d"66";
    d"82"; d"98"; d"114"; d"130";
    d"162"; d"194"; d"226"; d"257";
    d"258" ].

(** See RFC 1951, section 3.2.5. *)
Definition distCodeExtraBits :=
  [ d"0"  ;  d"0"  ; d"0"  ; d"0" ;
    d"1"  ;  d"1"  ; d"2"  ; d"2" ;
    d"3"  ;  d"3"  ; d"4"  ; d"4" ;
    d"5"  ;  d"5"  ; d"6"  ; d"6" ;
    d"7"  ;  d"7"  ; d"8"  ; d"8" ;
    d"9"  ;  d"9"  ; d"10" ; d"10" ;
    d"11" ; d"11"  ; d"12" ; d"12" ;
    d"13" ; d"13" ].

(** See RFC 1951, section 3.2.5. Notice that these numbers are large,
and may cause warnings by Coq when actually evaluated.  *)
Definition distCodeBase :=
  [ d"1"     ; d"2"     ; d"3"     ; d"4"     ;
    d"5"     ; d"7"     ; d"9"     ; d"13"    ;
    d"17"    ; d"25"    ; d"33"    ; d"49"    ;
    d"65"    ; d"97"    ; d"129"   ; d"193"   ;
    d"257"   ; d"385"   ; d"513"   ; d"769"   ;
    d"1025"  ; d"1537"  ; d"2049"  ; d"3073"  ;
    d"4097"  ; d"6145"  ; d"8193"  ; d"12289" ;
    d"16385" ; d"24577" ].

(** See RFC 1951, section 3.2.5. Notice that these numbers are large,
and may cause warnings by Coq when actually evaluated.  *)
Definition distCodeMax :=
  [ d"1"     ; d"2"     ; d"3"     ; d"4"     ;
    d"6"     ; d"8"     ; d"12"    ; d"16"    ;
    d"24"    ; d"32"    ; d"48"    ; d"64"    ;
    d"96"    ; d"128"   ; d"192"   ; d"256"   ;
    d"384"   ; d"512"   ; d"768"   ; d"1024"  ;
    d"1536"  ; d"2048"  ; d"3072"  ; d"4096"  ;
    d"6144"  ; d"8192"  ; d"12288" ; d"16384" ;
    d"24576" ; d"32768" ].

(** See RFC 1951, section 3.2.6. *)
Definition vector_for_fixed_lit_code : vec nat 288 :=
  of_list ((repeat 144 8) ++ (repeat (255 - 143) 9) ++ (repeat (279 - 255) 7) ++ (repeat (287 - 279) 8)).

(** See RFC 1951, section 3.2.6. *)
Definition vector_for_fixed_dist_code : vec nat 32 := of_list (repeat 32 5).


(** For the constant codings, we use our already proved uniqueness and existence predicates *)
Definition fixed_lit_code_ex : { D : deflateCoding 288 | vector_for_fixed_lit_code = Vmap lb (C 288 D)}.
Proof.
  apply existence.
  compute.
  intros Q.
  inversion Q.
Defined.

(** For the constant codings, we use our already proved uniqueness and existence predicates *)
Definition fixed_dist_code_ex : { D : deflateCoding 32 | vector_for_fixed_dist_code = Vmap lb (C 32 D)}.
Proof.
  apply existence.
  compute.
  intros Q.
  inversion Q.
Defined.

Definition fixed_lit_code := proj1_sig fixed_lit_code_ex.
Definition fixed_dist_code := proj1_sig fixed_dist_code_ex.

(** See RFC 1951, section 3.2.7. *)
Definition HCLensNat := [16; 17; 18; 0; 8; 7; 9; 6; 10; 5; 11; 4; 12; 3; 13; 2; 14; 1; 15].

(** [nBytesDirect n L S] means that [S] is a sequence of the [n] Bytes
in the bit sequence [L] without back references *)

Inductive nBytesDirect : nat -> LB -> SequenceWithBackRefs Byte -> Prop :=
| nBytesDirect0 : nBytesDirect 0 nil nil
| nBytesDirectS : forall n a b bools thebyte,
                    nBytesDirect n a b -> bools = to_list thebyte ->
                    nBytesDirect (S n) (bools ++ a) ((inl thebyte) :: b).

(** [readBitsLSB length n l] means that the list [l] of given [length]
encodes the number [n] in least-significant-first bit-order. *)

Inductive readBitsLSB (length : nat) : nat -> LB -> Prop :=
| mkRBLSB : forall l n, ll l = length -> LSBnat l n -> readBitsLSB length n l.

(** Uncompressed block, no padding. Padding is done in
[OneBlockWithPadding]. See RFC 1951, section 3.2.4. *)

Definition UncompressedBlockDirect : SequenceWithBackRefs Byte -> LB -> Prop :=
  (readBitsLSB 16) >>=
  fun len  => (readBitsLSB 16) >>=
  fun nlen =>
    (fun swbr lb => len + nlen = 2 ^ 16 - 1 /\ nBytesDirect len lb swbr).

(** header parsing for dynamically compressed blocks *)

(** [CodingOfSequence l dc] means that the list of natural numbers [l]
is the list of lengths of the coding [dc], ordered by the encoded
characters. For further detail, see [DeflateCoding]. *)

Inductive CodingOfSequence {n : nat} (l : list nat) (dc : deflateCoding n) :=
| makeCodingOfSequence : forall (eq : ll l = n), Vmap lb (C _ dc) = vec_id eq (of_list l) -> CodingOfSequence l dc.

(** The code length code. *)

(** Raw code length code - a list of [hclen] bit-triples, which encode code lengths from 0 to 7. *)

Inductive CLCHeaderRaw : forall (hclen : nat) (input : LB) (output : list nat), Prop :=
| zeroCLCHeaderRaw : CLCHeaderRaw 0 nil nil
| succCLCHeaderRaw : forall n i o j m, CLCHeaderRaw n i o -> ll m = 3 -> LSBnat m j -> CLCHeaderRaw (S n) (m ++ i) (j :: o).

(** Pad the raw header with zeroes, so its length is 19. *)

Inductive CLCHeaderPadded (hclen : nat) (input : LB) (output : list nat) : Prop :=
| makeCLCHeaderPadded : forall m output1, CLCHeaderRaw hclen input output1 ->
                                          output = output1 ++ repeat m 0 ->
                                          ll output = 19 ->
                                          CLCHeaderPadded hclen input output.

(** Apply the permutation to the padded header. *)

Inductive CLCHeaderPermuted (hclen : nat) (input : LB) (output : list nat) : Prop :=
| makeCLCHeaderPermuted : forall output1,
                            CLCHeaderPadded hclen input output1 ->
                            (forall m, nth_error output (nth m HCLensNat 19) = nth_error output1 m) ->
                            CLCHeaderPermuted hclen input output.

(** [CLCHeader hclen output input] means that the code length coding [output] is encoded in thee [hclen]*3 bits (see above) from [input]. *)

Inductive CLCHeader (hclen : nat) (output : deflateCoding 19) (input : LB) : Prop :=
| makeCLCHeader : forall cooked,
                    CLCHeaderPermuted hclen input cooked ->
                    CodingOfSequence cooked output ->
                    CLCHeader hclen output input.

(** This definition is rather complicated, but it makes later
definitions easier, and encodes a pattern that occurs in multiple
places: A code from a coding is followed by some suffix bits, and
encodes a value which must be in a given range.

Let [coding] be a given Deflate coding, [mincode] be a natural number
denoting the minimal encoded code which is allowed, [xbitnums] the
numbers of extra bits for a given encoded code, starting from the
extra bits for [mincode], [bases] the corresponding minimal encoded
values, and [maxs] the corresponding maximal values. Then
[CompressedWithExtraBits coding mincode xbitnums bases maxs n l] means
that the bit list [l] encodes the value [n], according to these
rules. *)

Inductive CompressedWithExtraBits {m : nat} (coding : deflateCoding m)
          (mincode : nat) (xbitnums bases maxs : list nat) : nat -> LB -> Prop :=
| complength : forall (base extra code max xbitnum : nat) (bbits xbits : LB),
                 dc_enc coding (mincode + code) bbits -> (* code >= mincode *)
                 nth_error xbitnums code = Some xbitnum -> (* number of additional bits *)
                 nth_error bases code = Some base -> (* base *)
                 nth_error maxs code = Some max -> (* maximum *)
                 ll xbits = xbitnum -> (* additional bits have specified length *)
                 LSBnat xbits extra -> (* binary number made by xbits *)
                 base + extra <= max -> 
                 CompressedWithExtraBits coding mincode xbitnums bases maxs (base + extra) (bbits ++ xbits).

(** A sequence of code lengths, encoded with the given code length
coding. See RFC 1951 section 3.2.7. We encode into a sequence with
backreferences, because some codes encode repetitions. *)

Inductive CommonCodeLengthsSWBR (clc : deflateCoding 19) : nat -> SequenceWithBackRefs nat -> LB -> Prop :=
| cswbr0 : CommonCodeLengthsSWBR clc 0 [] []
| cswbrc :
    forall m n brs lb1 input,
      CommonCodeLengthsSWBR clc n brs lb1 ->
      m < 16 ->
      dc_enc clc m input ->
      CommonCodeLengthsSWBR clc (n + 1) (inl m :: brs) (input ++ lb1)
| cswbr16 :
    forall m n brs lb1 input,
      CommonCodeLengthsSWBR clc n brs lb1 ->
      CompressedWithExtraBits clc 16 [2] [3] [6] m input ->
      CommonCodeLengthsSWBR clc (n + m) (inr (m, 1) :: brs) (input ++ lb1)
| cswbr17 :
    forall m n brs lb1 input,
      CommonCodeLengthsSWBR clc n brs lb1 ->
      CompressedWithExtraBits clc 17 [3] [3 - 1] [10 - 1] m input ->
      CommonCodeLengthsSWBR clc (n + m + 1) (inl 0 :: inr (m, 1) :: brs) (input ++ lb1)
| cswbr18 :
    forall m n brs lb1 input,
      CommonCodeLengthsSWBR clc n brs lb1 ->
      CompressedWithExtraBits clc 18 [7] [11 - 1] [138 - 1] m input ->
      CommonCodeLengthsSWBR clc (n + m + 1) (inl 0 :: inr (m, 1) :: brs) (input ++ lb1).

(** A sequence of code lengths, encoded with the given code length
coding. Backreferences will be resolved, so only code lengths 0
through 15 remain. *)

Inductive CommonCodeLengthsN (clc : deflateCoding 19) (n : nat) (B : list nat) (A : LB) : Prop := 
| ccl : forall C, CommonCodeLengthsSWBR clc n C A -> ResolveBackReferences C B -> CommonCodeLengthsN clc n B A.

(** After the code lengths are read and repeated, they are split and
then parsed into a literal/lengt and a distance code lengths . *)

Inductive SplitCodeLengths (clc : deflateCoding 19) (hlit hdist : nat) (litlen : vec nat 288) (dist : vec nat 32) (input : LB) : Prop :=
| makeSplitCodeLengths :
    forall litlenL distL lm ld,
      ll litlenL = hlit ->
      ll distL = hdist ->
      to_list litlen = litlenL ++ repeat lm 0 ->
      to_list dist = distL ++ repeat ld 0 ->
      CommonCodeLengthsN clc (hlit + hdist) (litlenL ++ distL) input ->
      SplitCodeLengths clc hlit hdist litlen dist input.

(** From the vector of lengths, encode codings *)

Inductive LitLenDist (clc : deflateCoding 19) (hlit hdist : nat) (litlen : deflateCoding 288) (dist : deflateCoding 32) (input : LB) : Prop :=
| makeLitLenDist :
    SplitCodeLengths clc hlit hdist (Vmap lb (C 288 litlen)) (Vmap lb (C 32 dist)) input ->
    LitLenDist clc hlit hdist litlen dist input.

Function CompressedLength (litlen : deflateCoding 288) := CompressedWithExtraBits litlen 257 repeatCodeExtraBits repeatCodeBase repeatCodeMax.
Function CompressedDist (dist : deflateCoding 32) := CompressedWithExtraBits dist 0 distCodeExtraBits distCodeBase distCodeMax.

Inductive CompressedSWBR (litlen : deflateCoding 288) (dist : deflateCoding 32) : SequenceWithBackRefs Byte -> LB -> Prop :=
| cswbr_end : forall l, dc_enc litlen 256 l -> CompressedSWBR litlen dist [] l
| cswbr_direct : forall prev_swbr prev_lb l n,
                   dc_enc litlen (ByteToNat n) l ->
                   CompressedSWBR litlen dist prev_swbr prev_lb ->
                   CompressedSWBR litlen dist ((inl n) :: prev_swbr) (l ++ prev_lb)
| cswbr_backref : forall prev_swbr prev_lb l d lbits dbits,
                    CompressedSWBR litlen dist prev_swbr prev_lb ->
                    CompressedLength litlen l lbits ->
                    CompressedDist dist d dbits ->
                    CompressedSWBR litlen dist ((inr (l, d)) :: prev_swbr) (lbits ++ dbits ++ prev_lb).

Definition DynamicallyCompressedHeader : (deflateCoding 288 * deflateCoding 32) -> LB -> Prop :=
  (readBitsLSB 5)
    >>= fun hlit => (readBitsLSB 5)
    >>= fun hdist => (readBitsLSB 4)
    >>= fun hclen => (CLCHeader (hclen + 4))
    >>= fun clc lld =>
          LitLenDist clc (hlit + 257) (hdist + 1) (fst lld) (snd lld).

Definition DynamicallyCompressedBlock : SequenceWithBackRefs Byte -> LB -> Prop :=
  DynamicallyCompressedHeader >>= (fun lld => CompressedSWBR (fst lld) (snd lld)).

(** A statically compressed block is a block with defined static codings *)

Inductive StaticallyCompressedBlock  (output : SequenceWithBackRefs Byte) : LB -> Prop :=
| makeSCB :
    forall input,
      CompressedSWBR fixed_lit_code fixed_dist_code output input ->
      StaticallyCompressedBlock output input.

(** The natural argument denotes the bits that have already been
read. Padding is assured by making the bit count a multiple of
eight. *)

Inductive OneBlockWithPadding (out : SequenceWithBackRefs Byte) : nat -> LB -> Prop :=
| obwpDCB : forall dcb n, DynamicallyCompressedBlock out dcb -> OneBlockWithPadding out n (false :: true :: dcb)
| obwpSCB : forall scb n, StaticallyCompressedBlock out scb -> OneBlockWithPadding out n (true :: false :: scb)
| obwpUCB : forall ucb n m pad, UncompressedBlockDirect out ucb ->
                                n + ll (false :: false :: pad) = 8 * m ->
                                ll pad < 8 ->
                                OneBlockWithPadding out n (false :: false :: pad ++ ucb).

Inductive ManyBlocks : nat -> SequenceWithBackRefs Byte -> LB -> Prop :=
| lastBlock : forall n inp out, OneBlockWithPadding out (n + 1) inp -> ManyBlocks n out (true :: inp)
| middleBlock : forall n inp1 inp2 out1 out2,
    OneBlockWithPadding out1 (n + 1) inp1 ->
    ManyBlocks (n + 1 + ll inp1) out2 inp2 ->
    ManyBlocks n (out1 ++ out2) (false :: inp1 ++ inp2).

Inductive DeflateEncodes (out : LByte) (inp : LB) : Prop :=
| deflateEncodes : forall swbr,
                     ManyBlocks 0 swbr inp ->
                     ResolveBackReferences swbr out ->
                     DeflateEncodes out inp.