(* =============================================================================
   Formal Verification of User Datagram Protocol (UDP)
   
   Specification: RFC 768 (J. Postel, August 1980)
   Target: UDP over IPv4 (with IPv6 extensions per RFC 8200)
   
   Module: UDP Protocol Formalization and Verification
   Author: Charles C Norton
   Date: August 23rd 2025
   
   "And so at the gates of Eregion, the Gift-lord stood."
   
   =============================================================================
   
   This formalization provides a machine-verified implementation of the UDP
   protocol with the following components:
   
   - Wire format encoding/decoding (§2-3 RFC 768)
   - Internet checksum computation (§4 RFC 1071)
   - Pseudo-header construction for IPv4/IPv6 (§8.1 RFC 8200)
   - Length field validation (0-65535 octets)
   - Port number handling (including source port 0 semantics)
   
   Verification targets:
   - Encode/decode bijection for well-formed datagrams
   - Checksum algorithm correctness
   - Protocol conformance to RFC specifications
   ============================================================================= *)

(* ===== Dependencies ===== *)

From Coq Require Import
  List           (* List operations and notations *)
  NArith.NArith  (* Binary natural numbers (N) *)
  Lia            (* Linear integer arithmetic tactic *)
  Bool           (* Boolean operations and lemmas *)
  Arith.         (* Peano natural numbers (nat) *)
  
Require Import Coq.Init.Prelude.

(* ===== Notation Scopes ===== *)

Import ListNotations.
Open Scope N_scope.  (* Default interpretation of numerals as binary naturals (N) *)

(* =============================================================================
   Section 1: Numeric Types and Basic Operations
   ============================================================================= *)

(* ===== 1.1 Type Definitions ===== *)

Definition byte   := N.  (* 8-bit octet: range [0, 255] *)
Definition word16 := N.  (* 16-bit word: range [0, 65535] *)

(* ===== 1.2 Numeric Constants ===== *)

Definition two8   : N := 256.         (* 2^8: byte modulus *)
Definition two16  : N := 65536.       (* 2^16: word modulus *)
Definition mask16 : N := two16 - 1.   (* 0xFFFF: 16-bit mask *)

(* ===== 1.3 Positivity Lemmas ===== *)

Lemma two8_pos  : 0 < two8.  
Proof. unfold two8; lia. Qed.

Lemma two16_pos : 0 < two16. 
Proof. unfold two16; lia. Qed.

(* ===== 1.4 Canonical Truncation Functions ===== *)

Definition to_byte (x:N) : byte := x mod two8.
Definition to_word16 (x:N) : word16 := x mod two16.

(* ===== 1.5 Truncation Properties ===== *)

Lemma to_word16_lt_two16 : forall x, to_word16 x < two16.
Proof. 
  intro x. unfold to_word16. apply N.mod_lt. unfold two16. lia. 
Qed.

Lemma to_word16_id_if_lt : forall x, x < two16 -> to_word16 x = x.
Proof. 
  intros x Hx. unfold to_word16. apply N.mod_small. exact Hx. 
Qed.

Lemma to_word16_id_if_le_mask : forall x, x <= mask16 -> to_word16 x = x.
Proof.
  intros x Hx. 
  apply to_word16_id_if_lt. 
  unfold mask16 in Hx.
  assert (two16 = 65536) by reflexivity.
  rewrite H. 
  lia.
Qed.

(* ===== 1.6 List Length Operations ===== *)

Definition lenN {A} (xs:list A) : N := N.of_nat (List.length xs).

Lemma lenN_app : forall (A:Type) (xs ys:list A), 
  lenN (xs ++ ys) = lenN xs + lenN ys.
Proof. 
  intros A xs ys. unfold lenN. 
  rewrite List.length_app, Nat2N.inj_add. reflexivity. 
Qed.

Lemma lenN_cons : forall (A:Type) (x:A) xs, 
  lenN (x::xs) = 1 + lenN xs.
Proof. 
  intros A x xs. 
  unfold lenN. 
  simpl.
  induction xs as [|y ys IH].
  - reflexivity.
  - simpl.
    destruct (length ys) as [|n].
    + reflexivity.
    + simpl.
      destruct n as [|n'].
      * reflexivity.
      * f_equal.
        induction n' as [|n'' IH'].
        ** reflexivity.
        ** simpl. f_equal.
           destruct (Pos.of_succ_nat n''); reflexivity.
Qed.

Lemma N_to_nat_lenN : forall (A:Type) (xs:list A), 
  N.to_nat (lenN xs) = List.length xs.
Proof. 
  intros; unfold lenN; apply Nat2N.id. 
Qed.

(* ===== 1.7 List Manipulation Functions ===== *)

Fixpoint take {A} (n:nat) (xs:list A) : list A :=
  match n, xs with
  | O, _ => []
  | S n', [] => []
  | S n', x::xs' => x :: take n' xs'
  end.

Fixpoint drop {A} (n:nat) (xs:list A) : list A :=
  match n, xs with
  | O, _ => xs
  | S n', [] => []
  | S n', _::xs' => drop n' xs'
  end.

Lemma take_length_id : forall (A:Type) (xs:list A), 
  take (List.length xs) xs = xs.
Proof. 
  intros A xs; induction xs; simpl; congruence. 
Qed.

(* ===== 1.8 Byte Range Validation ===== *)

Definition is_byte (b:byte) : bool := b <? two8.

Lemma is_byte_true_of_mod : forall x, 
  is_byte (x mod two8) = true.
Proof.
  intros x. unfold is_byte. apply N.ltb_lt. apply N.mod_lt. 
  apply N.neq_0_lt_0. unfold two8. lia.
Qed.

(* =============================================================================
   Section 2: Big-Endian 16-bit Serialization
   ============================================================================= *)

(* ===== 2.1 Word-to-Bytes Decomposition ===== *)

Definition be16_of_word16 (w:word16) : byte * byte :=
  ( (w / two8) mod two8,    (* High-order octet *)
    w mod two8).            (* Low-order octet *)

(* ===== 2.2 Bytes-to-Word Composition ===== *)

Definition word16_of_be (hi lo: byte) : word16 :=
  hi * two8 + lo.

(* ===== 2.3 Decomposition Bounds ===== *)

Lemma div256_lt256 : forall w, 
  w < two16 -> (w / two8) < two8.
Proof.
  intros w Hw.
  assert (two8 <> 0) by (cbv [two8]; lia).
  apply N.div_lt_upper_bound; [cbv [two8]; lia|].
  cbv [two16 two8] in *. lia.
Qed.

(* ===== 2.4 Serialization Round-Trip Property ===== *)

Lemma word16_of_be_be16 : forall w, 
  w < two16 ->
  let '(hi,lo) := be16_of_word16 w in 
  word16_of_be hi lo = w.
Proof.
  intros w Hw. unfold be16_of_word16, word16_of_be.
  rewrite (N.mod_small (w / two8) two8).
  2:{ apply div256_lt256; exact Hw. }
  assert (two8 <> 0) by (unfold two8; lia).
  rewrite N.mul_comm.
  rewrite <- N.div_mod; [reflexivity | exact H].
Qed.

(* ===== 2.5 Octet Range Preservation ===== *)

Lemma be16_of_word16_bytes_are_bytes_true : forall w, 
  let '(hi,lo) := be16_of_word16 (to_word16 w) in
  is_byte hi = true /\ is_byte lo = true.
Proof.
  intros w. unfold be16_of_word16, is_byte.
  simpl. split; apply N.ltb_lt; apply N.mod_lt; 
  apply N.neq_0_lt_0; unfold two8; lia.
Qed.

(* ===== 2.6 List Serialization Functions ===== *)

Fixpoint bytes_of_words16_be (ws:list word16) : list byte :=
  match ws with
  | [] => []
  | w::tl =>
      let '(hi,lo) := be16_of_word16 (to_word16 w) in
      hi :: lo :: bytes_of_words16_be tl
  end.

Fixpoint words16_of_bytes_be (bs:list byte) : list word16 :=
  match bs with
  | [] => []
  | [b] => [ word16_of_be (to_byte b) 0 ]  (* Pad with 0x00 *)
  | b1::b2::tl =>
      word16_of_be (to_byte b1) (to_byte b2) :: words16_of_bytes_be tl
  end.

(* ===== 2.7 Length Properties ===== *)

Lemma lenN_bytes_of_words16_be_4 : forall a b c d,
  lenN (bytes_of_words16_be [a;b;c;d]) = 8%N.
Proof.
  intros. simpl.
  repeat (destruct (be16_of_word16 (to_word16 _)) as [x y]).
  reflexivity.
Qed.

(* =============================================================================
   Section 3: IPv4 Addresses and Pseudo-Header
   ============================================================================= *)

(* ===== 3.1 IPv4 Address Structure ===== *)

Record IPv4 := { 
  a0: byte;  (* First octet *)
  a1: byte;  (* Second octet *)
  a2: byte;  (* Third octet *)
  a3: byte   (* Fourth octet *)
}.

(* ===== 3.2 IPv4 Address Construction ===== *)

Definition mkIPv4 (x0 x1 x2 x3:byte) : IPv4 :=
  {| a0 := to_byte x0; a1 := to_byte x1; a2 := to_byte x2; a3 := to_byte x3 |}.

Definition normalizeIPv4 (ip:IPv4) : IPv4 :=
  mkIPv4 ip.(a0) ip.(a1) ip.(a2) ip.(a3).

(* ===== 3.3 IPv4 Properties ===== *)

Lemma to_byte_idempotent : forall x, 
  to_byte (to_byte x) = to_byte x.
Proof.
  intro x. unfold to_byte.
  rewrite N.mod_mod.
  - reflexivity.
  - unfold two8. lia.
Qed.

Lemma normalizeIPv4_idempotent : forall ip, 
  normalizeIPv4 (normalizeIPv4 ip) = normalizeIPv4 ip.
Proof. 
  intros [x0 x1 x2 x3].
  unfold normalizeIPv4, mkIPv4. simpl.
  f_equal; apply to_byte_idempotent.
Qed.

(* ===== 3.4 IPv4 Serialization ===== *)

Definition ipv4_words (ip:IPv4) : list word16 :=
  [ word16_of_be ip.(a0) ip.(a1);
    word16_of_be ip.(a2) ip.(a3) ].

(* ===== 3.5 UDP Protocol Number ===== *)

Definition udp_protocol_number : byte := 17%N.

(* ===== 3.6 IPv4 Pseudo-Header (RFC 768) ===== *)

Definition pseudo_header_v4 (src dst:IPv4) (udp_len:word16) : list word16 :=
  ipv4_words src ++
  ipv4_words dst ++
  [ word16_of_be 0 udp_protocol_number;
    udp_len ].

(* ===== 3.7 Multicast Detection ===== *)

Definition is_multicast_ipv4 (ip:IPv4) : bool :=
  (224 <=? ip.(a0)) && (ip.(a0) <=? 239).

(* =============================================================================
   Section 4: One's Complement 16-bit Checksum
   ============================================================================= *)

(* ===== 4.1 One's Complement Addition ===== *)

Definition add16_ones (acc w:word16) : word16 :=
  let s := acc + w in
  if s <? two16 then s else s - mask16.

(* ===== 4.2 Fundamental Properties ===== *)

Lemma add16_ones_bound : forall acc w, 
  acc < two16 -> w < two16 -> add16_ones acc w < two16.
Proof.
  intros acc w Hacc Hw. unfold add16_ones.
  destruct (acc + w <? two16) eqn:E.
  - apply N.ltb_lt in E; exact E.
  - apply N.ltb_ge in E. 
    assert (acc + w < 2*two16) by (unfold two16 in *; lia).
    unfold mask16, two16 in *. lia.
Qed.

(* ===== 4.3 Checksum Accumulator ===== *)

Fixpoint sum16 (ws:list word16) : word16 :=
  match ws with
  | [] => 0
  | w::tl => add16_ones (sum16 tl) (to_word16 w)
  end.

Lemma sum16_lt_two16 : forall ws, 
  sum16 ws < two16.
Proof.
  induction ws as [|w tl IH]; simpl.
  - unfold two16. lia.
  - apply add16_ones_bound; auto. apply to_word16_lt_two16.
Qed.

(* ===== 4.4 One's Complement Checksum ===== *)

Definition complement16 (x:word16) : word16 := mask16 - x.
Definition cksum16 (ws:list word16) : word16 := complement16 (sum16 ws).

(* ===== 4.5 Basic Algebraic Properties ===== *)

Lemma sum16_singleton : forall x,
  sum16 [x] = add16_ones 0 (to_word16 x).
Proof. reflexivity. Qed.

Lemma add16_ones_comm : forall x y,
  add16_ones x y = add16_ones y x.
Proof.
  intros x y. unfold add16_ones. rewrite N.add_comm. reflexivity.
Qed.

(* ===== 4.6 Overflow Behavior Specifications ===== *)

Lemma add16_ones_no_overflow : forall x y,
  x + y < two16 -> add16_ones x y = x + y.
Proof.
  intros x y H. unfold add16_ones.
  apply N.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma add16_ones_overflow : forall x y,
  x + y >= two16 -> add16_ones x y = x + y - mask16.
Proof.
  intros x y H. unfold add16_ones.
  destruct (x + y <? two16) eqn:E.
  - apply N.ltb_lt in E. lia.
  - reflexivity.
Qed.

(* ===== 4.7 Auxiliary Arithmetic Lemmas ===== *)

Lemma sum_bound_double : forall x y,
  x < two16 -> y < two16 -> x + y < 2 * two16.
Proof.
  intros x y Hx Hy. unfold two16 in *. lia.
Qed.

Lemma add_comm_3way : forall a b c : N,
  a - b + c = c + (a - b).
Proof.
  intros. apply N.add_comm.
Qed.

Lemma sub_add_assoc : forall a b c : N,
  b <= a -> c + (a - b) = c + a - b.
Proof.
  intros a b c Hle. rewrite <- N.add_sub_assoc; [reflexivity | exact Hle].
Qed.

Lemma two16_gt_mask16 : two16 > mask16.
Proof.
  unfold two16, mask16. compute. constructor.
Qed.

Lemma ge_two16_sub_mask16_ge_1 : forall x,
  two16 <= x -> 1 <= x - mask16.
Proof.
  intros x H. unfold two16, mask16 in *.
  assert (65536 - 65535 <= x - 65535) by (apply N.sub_le_mono_r; exact H).
  assert (65536 - 65535 = 1) by reflexivity.
  rewrite <- H1. exact H0.
Qed.

Lemma two16_implies_mask16_le : forall y z,
  y + z >= two16 -> mask16 <= y + z.
Proof.
  intros y z H.
  pose proof two16_gt_mask16 as Hgt.
  unfold two16, mask16 in *. lia.
Qed.

Lemma add_rearrange : forall x y z : N,
  x + (y + z) = x + y + z.
Proof. intros. lia. Qed.

Lemma overflow_arithmetic_eq : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  y + z >= two16 ->
  x + (y + z - mask16) = x + y + z - mask16.
Proof.
  intros x y z Hx Hy Hz Hyz.
  pose proof (two16_implies_mask16_le y z Hyz) as Hle.
  rewrite sub_add_assoc by exact Hle.
  rewrite <- add_rearrange.
  reflexivity.
Qed.

Lemma add_assoc_N : forall x y z : N,
  (x + y) + z = x + (y + z).
Proof. intros. lia. Qed.

Lemma add16_ones_assoc_case_yz_overflow : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  x + y < two16 -> y + z >= two16 ->
  x + y + z >= two16 -> x + (y + z - mask16) < two16 ->
  (x + y) + z - mask16 = x + (y + z - mask16).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz Hsum Hxyz_mask.
  transitivity (x + y + z - mask16).
  - lia.
  - symmetry. apply overflow_arithmetic_eq; assumption.
Qed.

Lemma add16_ones_cond_no_overflow : forall a b,
  a + b < two16 ->
  (if a + b <? two16 then a + b else a + b - mask16) = a + b.
Proof.
  intros a b H.
  apply N.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma add16_ones_assoc_yz_overflow_with_cond : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  x + y < two16 -> y + z >= two16 ->
  x + y + z >= two16 -> x + (y + z - mask16) < two16 ->
  (x + y) + z - mask16 = 
  (if x + (y + z - mask16) <? two16 
   then x + (y + z - mask16)
   else x + (y + z - mask16) - mask16).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz Hsum Hxyz_mask.
  rewrite add16_ones_cond_no_overflow by assumption.
  apply add16_ones_assoc_case_yz_overflow; assumption.
Qed.

Lemma add16_ones_assoc_both_overflow : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  x + y >= two16 -> y + z >= two16 ->
  x + y + z >= two16 -> x + (y + z - mask16) >= two16 ->
  (x + y - mask16) + z - mask16 = 
  (x + (y + z - mask16) - mask16).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz Hsum Hxyz_mask.
  assert (H1: (x + y - mask16) + z - mask16 = x + y + z - mask16 - mask16) by lia.
  assert (H2: x + (y + z - mask16) - mask16 = x + y + z - mask16 - mask16).
  { assert (H2a: x + (y + z - mask16) = x + y + z - mask16).
    { apply overflow_arithmetic_eq; assumption. }
    rewrite H2a. reflexivity. }
  rewrite H1. symmetry. exact H2.
Qed.

Lemma double_sub_assoc : forall a b c d : N,
  d <= a + b + c ->
  (a + b) + c - d = a + b + c - d.
Proof.
  intros a b c d H. lia.
Qed.

Lemma add16_ones_overflow_bound : forall x y,
  x < two16 -> y < two16 -> x + y >= two16 -> x + y - mask16 < two16.
Proof.
  intros x y Hx Hy Hsum.
  pose proof (sum_bound_double x y Hx Hy) as Hdouble.
  unfold two16, mask16 in *.
  assert (x + y <= 131071) by lia.
  assert (x + y - 65535 <= 65536) by lia.
  assert (x + y - 65535 >= 1) by lia.
  assert (x + y <= 65535 + 65535) by lia.
  assert (65535 + 65535 = 131070) by reflexivity.
  assert (x + y <= 131070) by lia.
  assert (x + y - 65535 <= 131070 - 65535) by lia.
  assert (131070 - 65535 = 65535) by reflexivity.
  assert (x + y - 65535 <= 65535) by lia.
  assert (65535 < 65536) by reflexivity.
  assert (x + y - 65535 < 65536) by lia.
  exact H9.
Qed.

Lemma tail_le_y : forall y z,
  z < two16 -> y + z - mask16 <= y.
Proof.
  intros y z Hz.
  assert (Hz_le : z <= mask16) by (unfold mask16, two16 in *; lia).
  assert (Hmono : y + z - mask16 <= y + mask16 - mask16).
  { apply N.sub_le_mono_r. apply N.add_le_mono_l. exact Hz_le. }
  replace (y + mask16 - mask16) with y in Hmono by lia.
  exact Hmono.
Qed.

Lemma tail_lt_when_xy_no : forall x y z,
  x < two16 -> y < two16 -> z < two16 -> x + y < two16 ->
  x + (y + z - mask16) < two16.
Proof.
  intros x y z Hx Hy Hz Hxy.
  pose proof (tail_le_y y z Hz) as Htail.
  assert (Hxy_le : x + y <= mask16) by (unfold mask16, two16 in *; lia).
  assert (Hsum_le : x + (y + z - mask16) <= x + y) by (apply N.add_le_mono_l; exact Htail).
  unfold two16, mask16 in *; lia.
Qed.

Lemma sub_add_rewrite_right : forall x y z, 
  mask16 <= y + z ->
  x + (y + z - mask16) = x + y + z - mask16.
Proof.
  intros x y z Hyz.
  rewrite (sub_add_assoc (y + z) mask16 x Hyz). lia.
Qed.

Lemma sub_add_rewrite_left : forall x y z, 
  mask16 <= x + y ->
  z + (x + y - mask16) = x + y + z - mask16.
Proof.
  intros x y z Hxy.
  rewrite (sub_add_assoc (x + y) mask16 z Hxy).
  rewrite (N.add_comm z (x + y)).
  reflexivity.
Qed.

Lemma add16_ones_assoc_case_nn : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  (x + y <? two16) = true ->
  (y + z <? two16) = true ->
  add16_ones (add16_ones x y) z = add16_ones x (add16_ones y z).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz.
  apply N.ltb_lt in Hxy.
  apply N.ltb_lt in Hyz.
  rewrite (add16_ones_no_overflow x y Hxy).
  rewrite (add16_ones_no_overflow y z Hyz).
  unfold add16_ones at 1 2.
  rewrite <- add_assoc_N.
  reflexivity.
Qed.

Lemma add16_ones_assoc_case_ny : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  (x + y <? two16) = true ->
  (y + z <? two16) = false ->
  add16_ones (add16_ones x y) z = add16_ones x (add16_ones y z).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz.
  apply N.ltb_lt in Hxy.
  apply N.ltb_ge in Hyz.
  assert (Hyz_ge : y + z >= two16) by lia.
  rewrite (add16_ones_no_overflow x y Hxy).
  rewrite (add16_ones_overflow y z Hyz_ge).
  assert (Hsum_ge : (x + y) + z >= two16) by lia.
  rewrite (add16_ones_overflow (x + y) z Hsum_ge).
  rewrite (add16_ones_no_overflow x (y + z - mask16)
            (tail_lt_when_xy_no x y z Hx Hy Hz Hxy)).
  rewrite (sub_add_rewrite_right x y z (two16_implies_mask16_le _ _ Hyz_ge)).
  reflexivity.
Qed.

Lemma add16_ones_overflow_le : forall x y, 
  two16 <= x + y -> add16_ones x y = x + y - mask16.
Proof.
  intros x y H.
  apply add16_ones_overflow. lia.
Qed.

Lemma add16_ones_ext_by_sum : forall a b c d,
  a + b = c + d ->
  add16_ones a b = add16_ones c d.
Proof.
  intros a b c d Heq.
  unfold add16_ones.
  now rewrite Heq.
Qed.

Lemma mask16_le_two16 : mask16 <= two16.
Proof. cbv [mask16 two16]; lia. Qed.

Lemma overflow_info : forall x y, 
  (x + y <? two16) = false ->
  two16 <= x + y /\ mask16 <= x + y.
Proof.
  intros x y H.
  apply N.ltb_ge in H.
  split; [ exact H | eapply N.le_trans; [apply mask16_le_two16 | exact H] ].
Qed.

Lemma sums_align_both_overflow : forall x y z,
  (x + y <? two16) = false ->
  (y + z <? two16) = false ->
  (x + y - mask16) + z = x + (y + z - mask16).
Proof.
  intros x y z Hxy Hyz.
  destruct (overflow_info x y Hxy) as [_ Hxy_mle].
  destruct (overflow_info y z Hyz) as [_ Hyz_mle].
  rewrite (N.add_comm (x + y - mask16) z).
  rewrite (sub_add_rewrite_left x y z Hxy_mle).
  rewrite (sub_add_rewrite_right x y z Hyz_mle).
  reflexivity.
Qed.

Lemma add16_ones_overflow_ltb_false : forall x y,
  (x + y <? two16) = false ->
  add16_ones x y = x + y - mask16.
Proof.
  intros x y H.
  apply N.ltb_ge in H.
  apply add16_ones_overflow; lia.
Qed.

Lemma add16_ones_assoc_case_yy : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  (x + y <? two16) = false ->
  (y + z <? two16) = false ->
  add16_ones (add16_ones x y) z = add16_ones x (add16_ones y z).
Proof.
  intros x y z _ _ _ Hxy Hyz.
  rewrite (add16_ones_overflow_ltb_false x y Hxy).
  rewrite (add16_ones_overflow_ltb_false y z Hyz).
  apply add16_ones_ext_by_sum.
  apply (sums_align_both_overflow x y z); assumption.
Qed.

Lemma add16_ones_no_overflow_ltb_true : forall x y,
  (x + y <? two16) = true ->
  add16_ones x y = x + y.
Proof.
  intros x y H.
  apply N.ltb_lt in H.
  apply add16_ones_no_overflow; exact H.
Qed.

Lemma add_minus_mask16_lt_two16 : forall x t, 
  x < two16 -> t <= mask16 -> x + t - mask16 < two16.
Proof.
  intros x t Hx Ht.
  assert (Hle : x + t - mask16 <= x + mask16 - mask16).
  { apply N.sub_le_mono_r. apply N.add_le_mono_l. exact Ht. }
  replace (x + mask16 - mask16) with x in Hle by lia.
  eapply N.le_lt_trans; [exact Hle| exact Hx].
Qed.

Lemma add16_ones_assoc_case_yn : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  (x + y <? two16) = false ->
  (y + z <? two16) = true ->
  add16_ones (add16_ones x y) z = add16_ones x (add16_ones y z).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz.
  rewrite (add16_ones_overflow_ltb_false x y Hxy).
  rewrite (add16_ones_no_overflow_ltb_true y z Hyz).
  destruct (overflow_info x y Hxy) as [Hxy_ge Hxy_mle].
  apply N.ltb_lt in Hyz.
  assert (Hyz_le : y + z <= mask16).
  { unfold mask16, two16. 
    assert (y + z <= 65535).
    { assert (y + z < 65536) by exact Hyz. lia. }
    exact H. }
  assert (Hout_lt : (x + y - mask16) + z < two16).
  { rewrite N.add_comm.
    rewrite (sub_add_rewrite_left x y z Hxy_mle).
    replace (x + y + z - mask16) with (x + (y + z) - mask16) by lia.
    assert (Htail_le_x : x + (y + z) - mask16 <= x).
    { assert (x + (y + z) <= x + mask16).
      { apply N.add_le_mono_l. exact Hyz_le. }
      lia. }
    eapply N.le_lt_trans; [exact Htail_le_x | exact Hx]. }
  rewrite (add16_ones_no_overflow (x + y - mask16) z Hout_lt).
  assert (Hrhs_ge : x + (y + z) >= two16) by lia.
  rewrite (add16_ones_overflow x (y + z) Hrhs_ge).
  rewrite N.add_comm with (n := x + y - mask16) (m := z).
  rewrite (sub_add_rewrite_left x y z Hxy_mle).
  replace (x + y + z - mask16) with (x + (y + z) - mask16) by lia.
  reflexivity.
Qed.

(* ===== 4.8 Main Associativity Theorem ===== *)

Theorem add16_ones_assoc : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  add16_ones (add16_ones x y) z = add16_ones x (add16_ones y z).
Proof.
  intros x y z Hx Hy Hz.
  destruct (x + y <? two16) eqn:Exy.
  - destruct (y + z <? two16) eqn:Eyz.
    + apply add16_ones_assoc_case_nn; auto.
    + apply add16_ones_assoc_case_ny; auto.
  - destruct (y + z <? two16) eqn:Eyz.
    + apply add16_ones_assoc_case_yn; auto.
    + apply add16_ones_assoc_case_yy; auto.
Qed.

(* ===== 4.9 List Operations ===== *)

Lemma sum16_app_single : forall xs y,
  sum16 (xs ++ [y]) = add16_ones (sum16 xs) (to_word16 y).
Proof.
  induction xs as [|x xs IH]; intro y.
  - reflexivity.
  - simpl.
    rewrite IH.
    rewrite <- add16_ones_comm with (x := to_word16 x) (y := add16_ones (sum16 xs) (to_word16 y)).
    rewrite <- add16_ones_assoc.
    + rewrite add16_ones_comm with (x := to_word16 x) (y := sum16 xs).
      reflexivity.
    + apply to_word16_lt_two16.
    + apply sum16_lt_two16.
    + apply to_word16_lt_two16.
Qed.

Lemma sum16_app : forall xs ys,
  sum16 (xs ++ ys) = fold_left add16_ones (map to_word16 ys) (sum16 xs).
Proof.
  intros xs ys. 
  destruct ys as [|y ys'].
  - rewrite app_nil_r. reflexivity.
  - destruct ys' as [|y' ys''].
    + simpl. rewrite sum16_app_single. reflexivity.
    + simpl. 
      assert (sum16 ((xs ++ [y]) ++ y' :: ys'') = 
              fold_left add16_ones (map to_word16 (y' :: ys'')) (sum16 (xs ++ [y]))).
      { clear. 
        generalize (xs ++ [y]) as zs.
        intro zs.
        generalize (y' :: ys'') as ws.
        intro ws.
        clear xs y y' ys''.
        revert zs.
        induction ws as [|w ws' IH]; intro zs; simpl.
        - rewrite app_nil_r. reflexivity.
        - assert (sum16 (zs ++ w :: ws') = sum16 ((zs ++ [w]) ++ ws')).
          { rewrite <- app_assoc. simpl. reflexivity. }
          rewrite H. clear H.
          rewrite IH.
          simpl.
          rewrite sum16_app_single.
          reflexivity.
      }
      rewrite <- app_assoc in H. simpl in H.
      rewrite H.
      rewrite sum16_app_single.
      reflexivity.
Qed.

(* ===== 4.10 Checksum Verification Property ===== *)

Lemma add16_ones_complement : forall s, 
  s < two16 -> add16_ones s (complement16 s) = mask16.
Proof.
  intros s Hs. unfold add16_ones, complement16.
  assert (s + (mask16 - s) = mask16) by (unfold mask16; lia).
  rewrite H.
  assert (mask16 < two16) by (unfold mask16, two16; lia).
  apply N.ltb_lt in H0.
  rewrite H0.
  reflexivity.
Qed.

Theorem sum16_with_cksum_is_allones : forall ws, 
  sum16 (ws ++ [cksum16 ws]) = mask16.
Proof.
  intro ws.
  rewrite sum16_app. simpl.
  set (s := sum16 ws).
  unfold cksum16, complement16.
  simpl.
  assert (mask16 - s <= mask16).
  { assert (s <= mask16).
    { pose proof (sum16_lt_two16 ws).
      unfold mask16, two16 in *. lia. }
    lia. }
  change (add16_ones s (to_word16 (mask16 - s)) = mask16).
  rewrite (to_word16_id_if_le_mask (mask16 - s) H).
  apply add16_ones_complement. apply sum16_lt_two16.
Qed.

(* =============================================================================
   Section 5: UDP Header Structure and Protocol Implementation
   ============================================================================= *)

(* ===== 5.1 UDP Header Structure (RFC 768 §Format) ===== *)

Record UdpHeader := {
  src_port : word16;   (* Source port: 0 indicates no reply expected (RFC 768) *)
  dst_port : word16;   (* Destination port: 0 handling per host policy *)
  length16 : word16;   (* Total length in octets: header (8) + data *)
  checksum : word16    (* Internet checksum: 0 indicates no checksum (IPv4 only) *)
}.

(* ===== 5.2 Header Serialization Functions ===== *)

Definition udp_header_words (h:UdpHeader) : list word16 :=
  [ h.(src_port); h.(dst_port); h.(length16); h.(checksum) ].

Definition udp_header_words_zero_ck (h:UdpHeader) : list word16 :=
  [ h.(src_port); h.(dst_port); h.(length16); 0 ].

Definition udp_header_bytes (h:UdpHeader) : list byte :=
  bytes_of_words16_be (udp_header_words h).

(* ===== 5.3 Protocol Configuration Policies ===== *)

Inductive ChecksumTxMode := WithChecksum | NoChecksum.
Inductive ChecksumRxMode := RequireValidOnly | ValidOrZero.
Inductive ZeroChecksumPolicy := ZeroAlwaysAccept | ZeroForbidOnMultiOrBcast | ZeroForbidAlways.
Inductive LengthRxMode   := StrictEq | AcceptShorterIP.
Inductive DstPortZeroPolicy := Allow | Reject.

Record Config := {
  checksum_tx_mode     : ChecksumTxMode;
  checksum_rx_mode     : ChecksumRxMode;
  zero_checksum_policy : ZeroChecksumPolicy;
  length_rx_mode       : LengthRxMode;
  dst_port0_policy     : DstPortZeroPolicy;
  is_broadcast         : IPv4 -> bool  (* Host-specific broadcast predicate *)
}.

(* ===== 5.4 Standard Configuration Profiles ===== *)

Definition defaults_ipv4 : Config :=
  {| checksum_tx_mode     := WithChecksum;
     checksum_rx_mode     := ValidOrZero;
     zero_checksum_policy := ZeroAlwaysAccept;
     length_rx_mode       := StrictEq;
     dst_port0_policy     := Reject;
     is_broadcast         := fun _ => false |}.

Definition defaults_ipv4_allow0 : Config :=
  {| checksum_tx_mode     := WithChecksum;
     checksum_rx_mode     := ValidOrZero;
     zero_checksum_policy := ZeroAlwaysAccept;
     length_rx_mode       := StrictEq;
     dst_port0_policy     := Allow;
     is_broadcast         := fun _ => false |}.

Definition defaults_ipv4_acceptShorter : Config :=
  {| checksum_tx_mode     := WithChecksum;
     checksum_rx_mode     := ValidOrZero;
     zero_checksum_policy := ZeroAlwaysAccept;
     length_rx_mode       := AcceptShorterIP;
     dst_port0_policy     := Reject;
     is_broadcast         := fun _ => false |}.

Definition defaults_ipv4_allow0_acceptShorter : Config :=
  {| checksum_tx_mode     := WithChecksum;
     checksum_rx_mode     := ValidOrZero;
     zero_checksum_policy := ZeroAlwaysAccept;
     length_rx_mode       := AcceptShorterIP;
     dst_port0_policy     := Allow;
     is_broadcast         := fun _ => false |}.

(* ===== 5.5 Error Types ===== *)

Inductive EncodeError := Oversize.
Inductive DecodeError := BadLength | BadChecksum | DstPortZeroNotAllowed.

(* ===== 5.6 Checksum Computation (RFC 768 §Checksum) ===== *)

Definition checksum_words_ipv4
  (src dst:IPv4) (h:UdpHeader) (data:list byte) : list word16 :=
  pseudo_header_v4 src dst h.(length16)
  ++ udp_header_words_zero_ck h
  ++ words16_of_bytes_be data.

Definition compute_udp_checksum_ipv4
  (src dst:IPv4) (h:UdpHeader) (data:list byte) : word16 :=
  let words := checksum_words_ipv4 src dst h data in
  let x := cksum16 words in
  if N.eqb x 0 then mask16 else x.

Lemma compute_udp_checksum_ipv4_nonzero :
  forall ipS ipD h data, compute_udp_checksum_ipv4 ipS ipD h data <> 0%N.
Proof.
  intros ipS ipD h data.
  unfold compute_udp_checksum_ipv4.
  destruct (N.eqb (cksum16 (checksum_words_ipv4 ipS ipD h data)) 0) eqn:E; simpl.
  - unfold mask16. intro H. discriminate.
  - apply N.eqb_neq in E. intro H. exact (E H).
Qed.

Definition zero_checksum_allowed (cfg:Config) (dst:IPv4) : bool :=
  match cfg.(zero_checksum_policy) with
  | ZeroAlwaysAccept => true
  | ZeroForbidAlways => false
  | ZeroForbidOnMultiOrBcast =>
      negb (is_multicast_ipv4 dst || cfg.(is_broadcast) dst)
  end.

(* ===== 5.7 Encoder Implementation ===== *)

Definition mk_header (sp dp:word16) (data_len_N:N) : option UdpHeader :=
  let L := 8 + data_len_N in
  if (L <=? mask16)%N
  then Some {| src_port := to_word16 sp;
               dst_port := to_word16 dp;
               length16 := to_word16 L;
               checksum := 0 |}
  else None.

Lemma mk_header_ok :
  forall sp dp len h0,
    mk_header sp dp len = Some h0 ->
    8 + len <= mask16
    /\ src_port h0 = to_word16 sp
    /\ dst_port h0 = to_word16 dp
    /\ length16 h0 = to_word16 (8 + len)
    /\ checksum h0 = 0.
Proof.
  intros sp dp len h0 H.
  unfold mk_header in H. destruct (8 + len <=? mask16)%N eqn:E; try discriminate.
  inversion H; subst h0; clear H.
  apply N.leb_le in E. repeat split; auto.
Qed.

Definition result (A E:Type) := sum A E.
Definition Ok {A E} (a:A) : result A E := inl a.
Definition Err {A E} (e:E) : result A E := inr e.

Definition encode_udp_ipv4
  (cfg:Config) (src_ip dst_ip:IPv4)
  (sp dp:word16) (data:list byte)
  : result (list byte) EncodeError :=
  match mk_header sp dp (lenN data) with
  | None => Err Oversize
  | Some h0 =>
      let h1 :=
        match cfg.(checksum_tx_mode) with
        | NoChecksum => {| src_port := src_port h0
                         ; dst_port := dst_port h0
                         ; length16 := length16 h0
                         ; checksum := 0 |}
        | WithChecksum =>
            let c := compute_udp_checksum_ipv4 src_ip dst_ip h0 data in
            {| src_port := src_port h0
             ; dst_port := dst_port h0
             ; length16 := length16 h0
             ; checksum := c |}
        end in
      Ok (udp_header_bytes h1 ++ data)
  end.

(* ===== 5.8 Decoder Implementation ===== *)

Definition parse_header (wire:list byte) : option (UdpHeader * list byte) :=
  match wire with
  | s0::s1::d0::d1::l0::l1::c0::c1::rest =>
      let header8 := [s0;s1;d0;d1;l0;l1;c0;c1] in
      if forallb is_byte header8 then
        let sp := word16_of_be s0 s1 in
        let dp := word16_of_be d0 d1 in
        let L  := word16_of_be l0 l1 in
        let ck := word16_of_be c0 c1 in
        Some ({| src_port := sp; dst_port := dp; length16 := L; checksum := ck |}, rest)
      else None
  | _ => None
  end.

Definition verify_checksum_ipv4
  (src dst:IPv4) (h:UdpHeader) (data_exact:list byte) : bool :=
  let words := checksum_words_ipv4 src dst h data_exact in
  let ws := words ++ [ h.(checksum) ] in
  N.eqb (sum16 ws) mask16.

Definition Decoded := (word16 * word16 * list byte)%type.

Definition decode_udp_ipv4
  (cfg:Config) (src_ip dst_ip:IPv4) (wire:list byte)
  : result Decoded DecodeError :=
  match parse_header wire with
  | None => Err BadLength
  | Some (h, rest) =>
      match cfg.(dst_port0_policy), N.eqb h.(dst_port) 0 with
      | Reject, true => Err DstPortZeroNotAllowed
      | _, _ =>
          let Nbytes := lenN wire in
          let L := h.(length16) in
          if (L <? 8)%N then Err BadLength else
          if (Nbytes <? L)%N then Err BadLength else
          let delivered_len_N := (L - 8)%N in
          let delivered_len := N.to_nat delivered_len_N in
          let delivered := take delivered_len rest in
          match cfg.(length_rx_mode) with
          | StrictEq =>
              if N.eqb Nbytes L
              then
                match N.eqb h.(checksum) 0 with
                | true =>
                    match cfg.(checksum_rx_mode) with
                    | RequireValidOnly => Err BadChecksum
                    | ValidOrZero =>
                        if zero_checksum_allowed cfg dst_ip
                        then Ok (h.(src_port), h.(dst_port), delivered)
                        else Err BadChecksum
                    end
                | false =>
                    if verify_checksum_ipv4 src_ip dst_ip h delivered
                    then Ok (h.(src_port), h.(dst_port), delivered)
                    else Err BadChecksum
                end
              else Err BadLength
          | AcceptShorterIP =>
              match N.eqb h.(checksum) 0 with
              | true =>
                  match cfg.(checksum_rx_mode) with
                  | RequireValidOnly => Err BadChecksum
                  | ValidOrZero =>
                      if zero_checksum_allowed cfg dst_ip
                      then Ok (h.(src_port), h.(dst_port), delivered)
                      else Err BadChecksum
                  end
              | false =>
                  if verify_checksum_ipv4 src_ip dst_ip h delivered
                  then Ok (h.(src_port), h.(dst_port), delivered)
                  else Err BadChecksum
              end
          end
      end
  end.

(* =============================================================================
   Section 6: Receive API Enrichment (RFC 1122 §4.1.3.5)
   
   Extends the decoder to provide source/destination addresses to the
   application layer as required by RFC 1122 for proper socket demultiplexing.
   ============================================================================= *)

(* ===== 6.1 Extended Delivery Record ===== *)

Record UdpDeliver := {
  src_ip_out  : IPv4;        (* Source IP address *)
  dst_ip_out  : IPv4;        (* Specific destination address *)
  src_port_out: word16;       (* Source port *)
  dst_port_out: word16;       (* Destination port *)
  payload_out : list byte     (* Application data *)
}.

(* ===== 6.2 Compatibility Definitions ===== *)

Definition DecodedV1 := Decoded.

(* ===== 6.3 Address-Aware Decoder ===== *)

Definition decode_udp_ipv4_with_addrs
  (cfg:Config) (src_ip dst_ip:IPv4) (wire:list byte)
  : result UdpDeliver DecodeError :=
  match decode_udp_ipv4 cfg src_ip dst_ip wire with
  | inl (sp, dp, data) =>
      Ok {| src_ip_out := src_ip
          ; dst_ip_out := dst_ip
          ; src_port_out := sp
          ; dst_port_out := dp
          ; payload_out  := data |}
  | inr e => Err e
  end.

(* =============================================================================
   Section 7: ICMP Error Handling (RFC 768/1122/1812)
   
   Implements ICMP error generation and processing per RFC 1122 §4.1.3.3
   and RFC 1812 §4.3 for proper UDP error reporting.
   ============================================================================= *)

(* ===== 7.1 ICMP Type and Code Definitions (RFC 792) ===== *)

(* Destination Unreachable codes *)
Definition ICMP_NET_UNREACH    : N := 0.
Definition ICMP_HOST_UNREACH   : N := 1.
Definition ICMP_PROTO_UNREACH  : N := 2.
Definition ICMP_PORT_UNREACH   : N := 3.
Definition ICMP_FRAG_NEEDED    : N := 4.
Definition ICMP_SR_FAILED      : N := 5.

(* Time Exceeded codes *)
Definition ICMP_TTL_EXCEEDED   : N := 0.
Definition ICMP_FRAG_TIME_EXCEEDED : N := 1.

(* Parameter Problem codes *)
Definition ICMP_PARAM_POINTER  : N := 0.

(* ===== 7.2 ICMP Generation Advice ===== *)

Inductive RxAdvice :=
  | SendICMPDestUnreach (code: N)      (* Port/Host/Net unreachable *)
  | SendICMPTimeExceeded (code: N)     (* TTL or reassembly timeout *)
  | SendICMPParamProblem (pointer: N)  (* Header parameter error *)
  | NoAdvice.

(* ===== 7.3 Application Error Notifications ===== *)

Inductive TxError :=
  | ICMPDestUnreach (code: N)
  | ICMPSourceQuench
  | ICMPTimeExceeded (code: N)
  | ICMPParamProblem (pointer: N)
  | NetworkError.

(* ===== 7.4 Port Unreachable Generation ===== *)

Definition udp_rx_icmp_advice
  (has_listener: IPv4 -> word16 -> bool)
  (decode_result: result UdpDeliver DecodeError)
  : RxAdvice :=
  match decode_result with
  | inl d =>
      if has_listener d.(dst_ip_out) d.(dst_port_out)
      then NoAdvice
      else SendICMPDestUnreach ICMP_PORT_UNREACH
  | inr BadLength => NoAdvice
  | inr BadChecksum => NoAdvice
  | inr DstPortZeroNotAllowed => NoAdvice
  end.

(* ===== 7.5 ICMP Suppression for Multicast/Broadcast ===== *)

Definition should_send_icmp (cfg:Config) (dst:IPv4) : bool :=
  negb (is_multicast_ipv4 dst || cfg.(is_broadcast) dst).

Definition udp_complete_icmp_advice
  (cfg:Config)
  (has_listener: IPv4 -> word16 -> bool)
  (src_ip dst_ip:IPv4)
  (decode_result: result UdpDeliver DecodeError)
  : RxAdvice :=
  if should_send_icmp cfg dst_ip
  then udp_rx_icmp_advice has_listener decode_result
  else NoAdvice.

(* ===== 7.6 ICMP Error Context ===== *)

Record ICMPErrorContext := {
  icmp_type     : N;          (* ICMP type field *)
  icmp_code     : N;          (* ICMP code field *)
  orig_src_ip   : IPv4;       (* Original source IP *)
  orig_dst_ip   : IPv4;       (* Original destination IP *)
  orig_src_port : word16;     (* Original source port *)
  orig_dst_port : word16      (* Original destination port *)
}.

(* ===== 7.7 ICMP to Application Error Mapping ===== *)

Definition icmp_to_tx_error (ctx:ICMPErrorContext) : TxError :=
  if N.eqb ctx.(icmp_type) 3 then        (* Destination Unreachable *)
    ICMPDestUnreach ctx.(icmp_code)
  else if N.eqb ctx.(icmp_type) 4 then   (* Source Quench *)
    ICMPSourceQuench
  else if N.eqb ctx.(icmp_type) 11 then  (* Time Exceeded *)
    ICMPTimeExceeded ctx.(icmp_code)
  else if N.eqb ctx.(icmp_type) 12 then  (* Parameter Problem *)
    ICMPParamProblem ctx.(icmp_code)
  else NetworkError.

(* ===== 7.8 Mandatory Application Notification ===== *)

Definition udp_must_notify_app (err:TxError) : bool := true.

(* ===== 7.9 ICMP Rate Limiting Configuration ===== *)

Record ConfigWithICMP := {
  base_config      : Config;
  rate_limit_icmp  : N -> N -> bool  (* (flow_hash, time) -> allow? *)
}.

Definition defaults_ipv4_with_icmp : ConfigWithICMP :=
  {| base_config := defaults_ipv4;
     rate_limit_icmp := fun _ _ => true |}.  (* No rate limiting *)
     
Definition udp_complete_icmp_advice_rl
  (cfg:ConfigWithICMP)
  (has_listener: IPv4 -> word16 -> bool)
  (src_ip dst_ip:IPv4)
  (flow_hash now:N)
  (res: result UdpDeliver DecodeError)
  : RxAdvice :=
  if cfg.(rate_limit_icmp) flow_hash now
  then udp_complete_icmp_advice cfg.(base_config) has_listener src_ip dst_ip res
  else NoAdvice.

(* =============================================================================
   Section 8: Correctness Proofs
   
   Verification of parser/serializer round-trip properties and checksum
   algorithm correctness.
   ============================================================================= *)

(* ===== 8.1 Header Normalization ===== *)

Definition header_norm (h:UdpHeader) : Prop :=
  src_port h < two16
  /\ dst_port h < two16
  /\ length16 h < two16
  /\ checksum h < two16.

Lemma header_norm_encode_h1 :
  forall sp dp len h0 ipS ipD data,
    mk_header sp dp len = Some h0 ->
    header_norm {| src_port := src_port h0;
                   dst_port := dst_port h0;
                   length16 := length16 h0;
                   checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}.
Proof.
  intros sp dp len h0 ipS ipD data Hmk.
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp [Hlen _]]]].
  unfold header_norm; simpl. 
  rewrite Hsp, Hdp, Hlen.
  repeat split; try apply to_word16_lt_two16.
  - unfold compute_udp_checksum_ipv4.
    set (x := cksum16 (checksum_words_ipv4 ipS ipD h0 data)).
    destruct (N.eqb x 0).
    + unfold mask16, two16. reflexivity.
    + unfold cksum16, complement16.
      pose proof (sum16_lt_two16 (checksum_words_ipv4 ipS ipD h0 data)) as Hs.
      unfold x. clear x.
      unfold mask16, two16.
      assert (65535 - sum16 (checksum_words_ipv4 ipS ipD h0 data) < 65536).
      { assert (sum16 (checksum_words_ipv4 ipS ipD h0 data) < 65536) by exact Hs.
        assert (sum16 (checksum_words_ipv4 ipS ipD h0 data) <= 65535) by lia.
        lia. }
      exact H.
Qed.

Lemma is_byte_8_andb_true :
  forall b0 b1 b2 b3 b4 b5 b6 b7,
    is_byte b0 = true -> is_byte b1 = true ->
    is_byte b2 = true -> is_byte b3 = true ->
    is_byte b4 = true -> is_byte b5 = true ->
    is_byte b6 = true -> is_byte b7 = true ->
    is_byte b0 && is_byte b1 && is_byte b2 && is_byte b3 &&
    is_byte b4 && is_byte b5 && is_byte b6 && is_byte b7 && true = true.
Proof.
  intros.
  rewrite H, H0, H1, H2, H3, H4, H5, H6.
  reflexivity.
Qed.

Lemma word16_of_be_reconstruct :
  forall w,
    w < two16 ->
    word16_of_be ((w / two8) mod two8) (w mod two8) = w.
Proof.
  intros w Hw.
  generalize (word16_of_be_be16 w Hw).
  unfold be16_of_word16.
  simpl. intros H. exact H.
Qed.

Lemma parse_header_bytes_of_header_norm :
  forall h rest,
    header_norm h ->
    parse_header (udp_header_bytes h ++ rest) = Some (h, rest).
Proof.
  intros h rest [Hsp [Hdp [HL Hck]]].
  unfold udp_header_bytes, udp_header_words, parse_header.
  simpl.
  repeat rewrite is_byte_true_of_mod.
  simpl.
  repeat rewrite word16_of_be_be16.
  repeat rewrite to_word16_id_if_lt by assumption.
  f_equal. destruct h. simpl. reflexivity.
  all: apply to_word16_lt_two16.
Qed.

(* ===== 8.2 Checksum Verification Helpers ===== *)

Lemma checksum_words_ipv4_ck_invariant :
  forall ipS ipD h data ck,
    checksum_words_ipv4 ipS ipD
      {| src_port := src_port h
       ; dst_port := dst_port h
       ; length16 := length16 h
       ; checksum := ck |} data
    = checksum_words_ipv4 ipS ipD h data.
Proof.
  intros. cbn [checksum_words_ipv4 udp_header_words_zero_ck]. reflexivity.
Qed.

Lemma cksum16_zero_sum_allones :
  forall ws, cksum16 ws = 0 -> sum16 ws = mask16.
Proof.
  intros ws H0.
  unfold cksum16, complement16 in H0.
  assert (Hlt : sum16 ws < two16) by apply sum16_lt_two16.
  assert (Hle : sum16 ws <= mask16) by (unfold mask16, two16 in *; lia).
  lia.
Qed.

Lemma to_word16_mask16_id : to_word16 mask16 = mask16.
Proof. apply to_word16_id_if_le_mask; unfold mask16; lia. Qed.

Lemma sum16_app_mask16_of_allones :
  forall ws, sum16 ws = mask16 -> sum16 (ws ++ [mask16]) = mask16.
Proof.
  intros ws Hs.
  rewrite sum16_app_single, to_word16_mask16_id, Hs.
  rewrite add16_ones_overflow by (unfold mask16, two16; lia).
  reflexivity.
Qed.

Lemma tail_if_cksum_zero :
  forall ws, (cksum16 ws =? 0) = true ->
    ws ++ [if cksum16 ws =? 0 then mask16 else cksum16 ws] = ws ++ [mask16].
Proof. intros ws Ez. now rewrite Ez. Qed.

Lemma sum16_app_if_cksum_zero :
  forall ws, (cksum16 ws =? 0) = true ->
    sum16 (ws ++ [if cksum16 ws =? 0 then mask16 else cksum16 ws]) = mask16.
Proof.
  intros ws Ez.
  rewrite (tail_if_cksum_zero ws Ez).
  apply sum16_app_mask16_of_allones.
  apply cksum16_zero_sum_allones. now apply N.eqb_eq in Ez.
Qed.

Lemma sum16_app_if_cksum_nonzero :
  forall ws, (cksum16 ws =? 0) = false ->
    sum16 (ws ++ [if cksum16 ws =? 0 then mask16 else cksum16 ws]) = mask16.
Proof.
  intros ws Ez. rewrite Ez. simpl.
  change (sum16 (ws ++ [cksum16 ws]) = mask16).
  apply sum16_with_cksum_is_allones.
Qed.

Lemma sum16_app_if_cksum_zero_words :
  forall ws ws', ws' = ws -> (cksum16 ws =? 0) = true ->
    sum16 (ws ++ [if cksum16 ws' =? 0 then mask16 else cksum16 ws']) = mask16.
Proof.
  intros ws ws' Heq Hz. subst ws'. apply sum16_app_if_cksum_zero; assumption.
Qed.

Lemma sum16_app_if_cksum_zero_concrete :
  forall ipS ipD h0 data,
    (cksum16 (checksum_words_ipv4 ipS ipD h0 data) =? 0) = true ->
    sum16 (checksum_words_ipv4 ipS ipD h0 data ++
           [if cksum16 (checksum_words_ipv4 ipS ipD h0 data) =? 0
            then mask16 else cksum16 (checksum_words_ipv4 ipS ipD h0 data)]) = mask16.
Proof.
  intros ipS ipD h0 data Ez.
  set (ws := checksum_words_ipv4 ipS ipD h0 data).
  rewrite (tail_if_cksum_zero ws Ez).
  apply sum16_app_mask16_of_allones.
  apply cksum16_zero_sum_allones. now apply N.eqb_eq in Ez.
Qed.

Lemma tail_if_cksum_nonzero :
  forall ws, (cksum16 ws =? 0) = false ->
    ws ++ [if cksum16 ws =? 0 then mask16 else cksum16 ws] = ws ++ [cksum16 ws].
Proof.
  intros ws Ez. rewrite Ez; reflexivity.
Qed.

Lemma sum16_app_if_cksum_nonzero_concrete :
  forall ipS ipD h0 data,
    (cksum16 (checksum_words_ipv4 ipS ipD h0 data) =? 0) = false ->
    sum16 (checksum_words_ipv4 ipS ipD h0 data ++
           [if cksum16 (checksum_words_ipv4 ipS ipD h0 data) =? 0
            then mask16 else cksum16 (checksum_words_ipv4 ipS ipD h0 data)]) = mask16.
Proof.
  intros ipS ipD h0 data Ez.
  set (ws := checksum_words_ipv4 ipS ipD h0 data).
  rewrite (tail_if_cksum_nonzero ws Ez).
  change (sum16 (ws ++ [cksum16 ws]) = mask16).
  apply sum16_with_cksum_is_allones.
Qed.

Lemma sum16_app_if_cksum_nonzero_words :
  forall ws ws', ws' = ws ->
    (cksum16 ws =? 0) = false ->
    sum16 (ws ++ [if cksum16 ws' =? 0 then mask16 else cksum16 ws']) = mask16.
Proof.
  intros ws ws' Heq Hz. subst ws'. apply sum16_app_if_cksum_nonzero; exact Hz.
Qed.

(* ===== 8.3 Main Checksum Verification Lemma ===== *)

Lemma verify_checksum_ipv4_encode_ok :
  forall ipS ipD sp dp data h0 h1,
    mk_header sp dp (lenN data) = Some h0 ->
    h1 = {| src_port := h0.(src_port)
          ; dst_port := h0.(dst_port)
          ; length16 := h0.(length16)
          ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |} ->
    verify_checksum_ipv4 ipS ipD h1 data = true.
Proof.
  intros ipS ipD sp dp data h0 h1 Hmk ->.
  unfold verify_checksum_ipv4.
  rewrite (checksum_words_ipv4_ck_invariant ipS ipD h0 data
            (compute_udp_checksum_ipv4 ipS ipD h0 data)).
  cbn [checksum].
  set (words := checksum_words_ipv4 ipS ipD h0 data).
  unfold compute_udp_checksum_ipv4.
  destruct (N.eqb (cksum16 words) 0) eqn:Ez.
  apply N.eqb_eq.
  subst words.
  apply sum16_app_if_cksum_zero_concrete.
  exact Ez.
  apply N.eqb_eq.
  eapply sum16_app_if_cksum_nonzero_words.
  - reflexivity.
  - exact Ez.
Qed.

Lemma lenN_udp_header_bytes_8 :
  forall h, lenN (udp_header_bytes h) = 8%N.
Proof.
  intros h. unfold udp_header_bytes, udp_header_words.
  rewrite lenN_bytes_of_words16_be_4. reflexivity.
Qed.

(* ===== 8.4 Encode-Decode Round-trip Helpers ===== *)

Lemma wire_length_eq_field :
  forall h data,
    lenN (udp_header_bytes h ++ data) = length16 h ->
    lenN data = length16 h - 8.
Proof.
  intros h data Heq.
  rewrite lenN_app, lenN_udp_header_bytes_8 in Heq.
  nia.
Qed.

Lemma Ok_inj {A E} (x y : A) : @Ok A E x = Ok y -> x = y.
Proof. now inversion 1. Qed.

Lemma lenN_wire_from_header_bytes :
  forall h data, lenN (udp_header_bytes h ++ data) = 8 + lenN data.
Proof.
  intros h data.
  rewrite lenN_app, lenN_udp_header_bytes_8. lia.
Qed.

Lemma length16_h1_total_len :
  forall ipS ipD sp dp data h0 h1,
    mk_header sp dp (lenN data) = Some h0 ->
    h1 = {| src_port := src_port h0
          ; dst_port := dst_port h0
          ; length16 := length16 h0
          ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |} ->
    length16 h1 = 8 + lenN data.
Proof.
  intros ipS ipD sp dp data h0 h1 Hmk ->.
  simpl.
  destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL _]]]].
  rewrite HL. now apply to_word16_id_if_le_mask.
Qed.

Lemma checksum_h1_eqb_zero_false :
  forall ipS ipD sp dp data h0 h1,
    mk_header sp dp (lenN data) = Some h0 ->
    h1 = {| src_port := src_port h0
          ; dst_port := dst_port h0
          ; length16 := length16 h0
          ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |} ->
    N.eqb (checksum h1) 0 = false.
Proof.
  intros ipS ipD sp dp data h0 h1 Hmk ->. simpl.
  apply N.eqb_neq.
  apply compute_udp_checksum_ipv4_nonzero.
Qed.

Lemma h1_ports_eq :
  forall ipS ipD sp dp data h0 h1,
    mk_header sp dp (lenN data) = Some h0 ->
    h1 = {| src_port := src_port h0
          ; dst_port := dst_port h0
          ; length16 := length16 h0
          ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |} ->
    src_port h1 = to_word16 sp /\ dst_port h1 = to_word16 dp.
Proof.
  intros ipS ipD sp dp data h0 h1 Hmk ->. simpl.
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp _]]].
  now rewrite Hsp, Hdp.
Qed.

Lemma take_lenN_id :
  forall (A:Type) (xs:list A),
    take (N.to_nat (lenN xs)) xs = xs.
Proof.
  intros A xs. rewrite N_to_nat_lenN. apply take_length_id.
Qed.

Lemma encode_udp_defaults_wire_eq_fast :
  forall ipS ipD sp dp data h0 h1 wire,
    mk_header sp dp (lenN data) = Some h0 ->
    h1 = {| src_port := src_port h0
          ; dst_port := dst_port h0
          ; length16 := length16 h0
          ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |} ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    wire = udp_header_bytes h1 ++ data.
Proof.
  intros ipS ipD sp dp data h0 h1 wire Hmk -> Henc.
  unfold encode_udp_ipv4 in Henc. rewrite Hmk in Henc.
  change (checksum_tx_mode defaults_ipv4) with WithChecksum in Henc.
  apply Ok_inj in Henc. symmetry; exact Henc.
Qed.

Lemma N_add_sub_cancel_l : forall a b : N, a + b - a = b.
Proof. intros a b; lia. Qed.

Lemma delivered_eq_data :
  forall (A:Type) (data:list A) L,
    L = 8 + lenN data ->
    take (N.to_nat (L - 8)) data = data.
Proof.
  intros A data L HL.
  rewrite HL.
  rewrite N_add_sub_cancel_l.
  rewrite N_to_nat_lenN.
  apply take_length_id.
Qed.

Lemma dst_port0_test_reject_nonzero_h0 :
  forall sp dp (data:list byte) h0,
    mk_header sp dp (lenN (A:=byte) data) = Some h0 ->
    to_word16 dp <> 0 ->
    N.eqb (dst_port h0) 0 = false.
Proof.
  intros sp dp data h0 Hmk Hnz.
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [Hdp _]]].
  rewrite Hdp. apply N.eqb_neq. exact Hnz.
Qed.

Lemma encode_produces_h1_wire :
  forall ipS ipD sp dp data h0 wire,
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    exists c, c <> 0 /\
    wire = udp_header_bytes 
      {| src_port := src_port h0;
         dst_port := dst_port h0;
         length16 := length16 h0;
         checksum := c |} ++ data.
Proof.
  intros ipS ipD sp dp data h0 wire Hmk Henc.
  exists (compute_udp_checksum_ipv4 ipS ipD h0 data).
  split.
  - apply compute_udp_checksum_ipv4_nonzero.
  - apply (encode_udp_defaults_wire_eq_fast ipS ipD sp dp data h0 _ wire Hmk).
    + reflexivity.
    + exact Henc.
Qed.

Lemma h1_checksum_nonzero :
  forall ipS ipD sp dp data h0,
    mk_header sp dp (lenN data) = Some h0 ->
    let h1 := {| src_port := src_port h0;
                 dst_port := dst_port h0;
                 length16 := length16 h0;
                 checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |} in
    checksum h1 <> 0.
Proof.
  intros. apply compute_udp_checksum_ipv4_nonzero.
Qed.

Lemma verify_with_computed_checksum :
  forall ipS ipD sp dp data h0,
    mk_header sp dp (lenN data) = Some h0 ->
    let c := compute_udp_checksum_ipv4 ipS ipD h0 data in
    let h1 := {| src_port := src_port h0;
                 dst_port := dst_port h0;
                 length16 := length16 h0;
                 checksum := c |} in
    verify_checksum_ipv4 ipS ipD h1 data = true.
Proof.
  intros.
  apply (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0).
  - exact H.
  - reflexivity.
Qed.

(* ===== 8.5 Main Round-trip Theorem ===== *)

Theorem decode_encode_roundtrip_ipv4_defaults_reject_nonzero16 :
  forall ipS ipD sp dp data wire h0,
    to_word16 dp <> 0%N ->
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire
      = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros ipS ipD sp dp data wire h0 Hdp_nz Hmk Henc.
  set (h1 :=
        {| src_port := src_port h0;
           dst_port := dst_port h0;
           length16 := length16 h0;
           checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).

  assert (Hwire : wire = udp_header_bytes h1 ++ data).
  { apply (encode_udp_defaults_wire_eq_fast ipS ipD sp dp data h0 h1);
      [exact Hmk|reflexivity|exact Henc]. }

  rewrite Hwire. unfold decode_udp_ipv4.
  assert (Hnorm : header_norm h1) by (eapply header_norm_encode_h1; eauto).
  rewrite (parse_header_bytes_of_header_norm h1 data Hnorm).

  destruct (dst_port0_policy defaults_ipv4) eqn:Epol.
  - assert (E_dp0 : dst_port0_policy defaults_ipv4 = Reject) by reflexivity.
    rewrite E_dp0 in Epol. discriminate.
  - assert (Hdp_h1_eq : dst_port h1 = to_word16 dp).
    { unfold h1.
      destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [Hdp_h0 _]]]; exact Hdp_h0. }
    assert (Eport : (N.eqb (dst_port h1) 0) = false)
      by (apply N.eqb_neq; rewrite Hdp_h1_eq; exact Hdp_nz).
    rewrite Eport.

    set (Nbytes := lenN (udp_header_bytes h1 ++ data)).
    set (L := length16 h1).

    assert (HL : L = 8 + lenN data).
    { unfold L, h1.
      destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL0 _]]]].
      rewrite HL0. now apply to_word16_id_if_le_mask. }

    assert (HNbytes : Nbytes = 8 + lenN data)
      by (unfold Nbytes; apply lenN_wire_from_header_bytes).

    assert (EL8  : (L <? 8) = false)      by (rewrite HL; apply N.ltb_ge; lia).
    assert (ENbL : (Nbytes <? L) = false) by (rewrite HNbytes, HL; apply N.ltb_ge; lia).
    rewrite EL8, ENbL.

    assert (Emode : length_rx_mode defaults_ipv4 = StrictEq) by reflexivity.
    rewrite Emode.

    assert (EEq : N.eqb Nbytes L = true) by (apply N.eqb_eq; now rewrite HNbytes, HL).
    rewrite EEq.

    assert (Eck : N.eqb (checksum h1) 0 = false).
    { unfold h1. apply N.eqb_neq. apply compute_udp_checksum_ipv4_nonzero. }
    rewrite Eck.

    assert (Hver :
              verify_checksum_ipv4 ipS ipD h1
                (take (N.to_nat (L - 8)) data) = true).
    { rewrite HL, N_add_sub_cancel_l, N_to_nat_lenN, take_length_id.
      eapply (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1);
        [exact Hmk|reflexivity]. }
    rewrite Hver.

    apply f_equal.
    assert (Hsrc : src_port h1 = to_word16 sp).
    { unfold h1.
      destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp _]]. exact Hsp. }
    assert (Hdata :
              take (N.to_nat (L - 8)) data = data).
    { rewrite HL, N_add_sub_cancel_l, N_to_nat_lenN. apply take_length_id. }
    rewrite Hsrc, Hdp_h1_eq, Hdata. reflexivity.
Qed.

(* =============================================================================
   Section 9: Fixed UDP/IPv4 Instance Examples
   ============================================================================= *)

Section UDP_Fixed_Instance.
  Open Scope N_scope.

  (* ===== 9.1 Fixed Test Parameters ===== *)
  
  Definition ex_src := mkIPv4 192 0 2 1.
  Definition ex_dst := mkIPv4 192 0 2 99.
  Definition ex_sp  : word16 := 40000.
  Definition ex_dp  : word16 := 4242.
  Definition ex_payload : list byte := [1;2;3].

  (* ===== 9.2 Wire Generation ===== *)
  
  Definition ex_wire : list byte :=
    match encode_udp_ipv4 defaults_ipv4 ex_src ex_dst ex_sp ex_dp ex_payload with
    | inl w  => w
    | inr _  => []
    end.

  (* ===== 9.3 Encoding Success ===== *)
  
  Example ex_encode_ok :
    exists w,
      encode_udp_ipv4 defaults_ipv4 ex_src ex_dst ex_sp ex_dp ex_payload = Ok w.
  Proof. vm_compute. eexists; reflexivity. Qed.

  (* ===== 9.4 No Listener Function ===== *)
  
  Definition no_listener (_:IPv4) (_:word16) : bool := false.

  (* ===== 9.5 Unicast Verification ===== *)
  
  Lemma ex_unicast : is_multicast_ipv4 ex_dst = false.
  Proof. vm_compute. reflexivity. Qed.

  (* ===== 9.6 ICMP Port Unreachable Generation ===== *)
  
  Example ex_icmp_advice :
    udp_complete_icmp_advice defaults_ipv4 no_listener ex_src ex_dst
       (decode_udp_ipv4_with_addrs defaults_ipv4 ex_src ex_dst ex_wire)
    = SendICMPDestUnreach ICMP_PORT_UNREACH.
  Proof.
    unfold ex_wire.
    destruct ex_encode_ok as [w Hw]. rewrite Hw.
    replace (match Ok w with inl w0 => w0 | inr _ => [] end) with w by reflexivity.

    assert (Hexists : exists h0, mk_header ex_sp ex_dp (lenN ex_payload) = Some h0).
    { unfold encode_udp_ipv4 in Hw.
      destruct (mk_header ex_sp ex_dp (lenN ex_payload)) as [h0|] eqn:Hmk; [now eexists|discriminate]. }
    destruct Hexists as [h0 Hmk].

    assert (Hdp_lt : ex_dp < two16) by (cbv [ex_dp two16]; lia).
    assert (Hdp_nz : to_word16 ex_dp <> 0).
    { intro Heq. rewrite (to_word16_id_if_lt ex_dp Hdp_lt) in Heq; cbv [ex_dp] in Heq; discriminate. }

    pose proof (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16
                  ex_src ex_dst ex_sp ex_dp ex_payload w h0 Hdp_nz Hmk Hw) as Hrt.

    unfold decode_udp_ipv4_with_addrs. cbn. rewrite Hrt. cbn.
    cbn [udp_complete_icmp_advice should_send_icmp udp_rx_icmp_advice defaults_ipv4].
    reflexivity.
  Qed.

  (* ===== 9.7 Wire Length Verification ===== *)
  
  Example ex_total_length_matches :
    lenN ex_wire = 8 + lenN ex_payload.
  Proof.
    unfold ex_wire.
    destruct ex_encode_ok as [w Henc_w]. rewrite Henc_w. cbn.
    assert (Hmk : exists h0, mk_header ex_sp ex_dp (lenN ex_payload) = Some h0).
    { unfold encode_udp_ipv4 in Henc_w.
      destruct (mk_header ex_sp ex_dp (lenN ex_payload)) as [h0|] eqn:E; [eauto|discriminate]. }
    destruct Hmk as [h0 Hmk].
    set (h1 :=
          {| src_port := src_port h0;
             dst_port := dst_port h0;
             length16 := length16 h0;
             checksum := compute_udp_checksum_ipv4 ex_src ex_dst h0 ex_payload |}).
    unfold encode_udp_ipv4 in Henc_w. rewrite Hmk in Henc_w.
    change (checksum_tx_mode defaults_ipv4) with WithChecksum in Henc_w.
    apply Ok_inj in Henc_w. rewrite <- Henc_w.
    apply lenN_wire_from_header_bytes.
  Qed.

End UDP_Fixed_Instance.

(* =============================================================================
   Section 10: Decoder-Encoder Completeness (Round-trip Properties)
   
   Proves that for any wire accepted by the decoder with default configuration,
   re-encoding the decoded result produces either:
   - Exactly the same wire (non-zero checksum case)
   - A canonicalized wire differing only in checksum field (zero-checksum case)
   
   This establishes the decoder-encoder pair forms a proper codec for valid
   UDP datagrams per RFC 768.
   ============================================================================= *)

Section UDP_Decode_Encode_Completeness.
  Open Scope N_scope.

(* ===== 10.1 Header Parsing Well-formedness ===== *)

(* Byte range validation *)
Lemma is_byte_lt_two8 : forall b, 
  is_byte b = true -> b < two8.
Proof.
  intros b Hb.
  unfold is_byte in Hb.
  apply N.ltb_lt in Hb.
  exact Hb.
Qed.

(* Big-endian word construction preserves range *)
Lemma word16_of_be_lt_two16_of_is_byte : forall hi lo,
  is_byte hi = true -> is_byte lo = true ->
  word16_of_be hi lo < two16.
Proof.
  intros hi lo Hhi Hlo.
  apply is_byte_lt_two8 in Hhi.
  apply is_byte_lt_two8 in Hlo.
  unfold word16_of_be, two8, two16 in *.
  lia.
Qed.

(* Parser produces normalized headers *)
Lemma header_norm_of_parse_success : forall w h rest,
  parse_header w = Some (h, rest) -> header_norm h.
Proof.
  intros w h rest H.
  unfold parse_header in H.
  destruct w as [|s0 w]; try discriminate.
  destruct w as [|s1 w]; try discriminate.
  destruct w as [|d0 w]; try discriminate.
  destruct w as [|d1 w]; try discriminate.
  destruct w as [|l0 w]; try discriminate.
  destruct w as [|l1 w]; try discriminate.
  destruct w as [|c0 w]; try discriminate.
  destruct w as [|c1 rest0]; try discriminate.
  cbn in H.
  destruct (forallb is_byte [s0; s1; d0; d1; l0; l1; c0; c1]) eqn:Hall.
  - simpl in Hall.
    rewrite Hall in H. cbn in H. inversion H; subst h rest; clear H.
    revert Hall; simpl; intro Hall.
    apply Bool.andb_true_iff in Hall as [Hs0 Hall].
    apply Bool.andb_true_iff in Hall as [Hs1 Hall].
    apply Bool.andb_true_iff in Hall as [Hd0 Hall].
    apply Bool.andb_true_iff in Hall as [Hd1 Hall].
    apply Bool.andb_true_iff in Hall as [Hl0 Hall].
    apply Bool.andb_true_iff in Hall as [Hl1 Hall].
    apply Bool.andb_true_iff in Hall as [Hc0 Hall].
    apply Bool.andb_true_iff in Hall as [Hc1 _].
    unfold header_norm; simpl.
    repeat split;
      eapply word16_of_be_lt_two16_of_is_byte; eauto.
  - simpl in Hall. rewrite Hall in H. discriminate.
Qed.

(* Performance optimization: prevent unintended unfolding *)
Local Opaque
  add16_ones sum16 to_word16
  checksum_words_ipv4 compute_udp_checksum_ipv4
  cksum16 complement16
  bytes_of_words16_be words16_of_bytes_be be16_of_word16 word16_of_be
  ipv4_words pseudo_header_v4.

(* ===== 10.2 Internet Checksum Algebraic Properties ===== *)

(* Verifier success implies end-around carry equation *)
Lemma verify_add16_mask16 : forall ipS ipD h data,
  header_norm h ->
  verify_checksum_ipv4 ipS ipD h data = true ->
  add16_ones (sum16 (checksum_words_ipv4 ipS ipD h data)) (checksum h) = mask16.
Proof.
  intros ipS ipD h data Hn Hver.
  unfold verify_checksum_ipv4 in Hver.
  apply N.eqb_eq in Hver.
  set (ws := checksum_words_ipv4 ipS ipD h data).
  set (ck := checksum h).
  pose proof (sum16_app_single ws ck) as Happ.
  destruct Hn as [_ [_ [_ Hck_lt]]].
  rewrite (to_word16_id_if_lt ck Hck_lt) in Happ.
  exact (eq_trans (eq_sym Happ) Hver).
Qed.

(* When add16_ones mask16 ck = mask16 with ck ≠ 0, then ck = 0xFFFF *)
Lemma add16_ones_mask16_nonzero_eq_mask16 : forall ck,
  ck < two16 ->
  ck <> 0 ->
  add16_ones mask16 ck = mask16 ->
  ck = mask16.
Proof.
  intros ck _ Hnz H.
  destruct (mask16 + ck <? two16) eqn:E.
  - apply N.ltb_lt in E.
    rewrite (add16_ones_no_overflow mask16 ck E) in H.
    unfold two16, mask16 in *.
    exfalso; lia.
  - apply N.ltb_ge in E.
    rewrite (add16_ones_overflow_le mask16 ck E) in H.
    unfold two16, mask16 in *; lia.
Qed.

(* ===== 10.3 Decomposition of sum = 0xFFFF Constraint ===== *)

(* No-overflow case: equality to mask16 fixes ck = mask16 - s *)
Lemma add16_ones_eq_mask16_no_overflow : forall s ck,
  s + ck < two16 ->
  add16_ones s ck = mask16 ->
  ck = mask16 - s.
Proof.
  intros s ck Hlt H.
  rewrite (add16_ones_no_overflow s ck Hlt) in H.
  unfold two16, mask16 in *; lia.
Qed.

(* Overflow case: equality to mask16 forces s + ck = 2·mask16 *)
Lemma add16_ones_eq_mask16_overflow_sum : forall s ck,
  two16 <= s + ck ->
  add16_ones s ck = mask16 ->
  s + ck = mask16 + mask16.
Proof.
  intros s ck Hge H.
  rewrite (add16_ones_overflow_le s ck Hge) in H.
  unfold two16, mask16 in *; lia.
Qed.

(* Under bounds s,ck < 2^16, sum = 2·mask16 implies both equal mask16 *)
Lemma sum_eq_2mask16_bounds_force_mask16 : forall s ck,
  s < two16 -> ck < two16 ->
  s + ck = mask16 + mask16 ->
  s = mask16 /\ ck = mask16.
Proof.
  intros s ck Hs Hck Hsum.
  cbv [two16 mask16] in *.
  assert (Hs_le  : s  <= 65535) by lia.
  assert (Hck_le : ck <= 65535) by lia.
  assert (Hs_ge  : 65535 <= s)  by lia.
  assert (Hck_ge : 65535 <= ck) by lia.
  split; lia.
Qed.

(* If add16_ones s ck = mask16 with s ≠ mask16, then ck = mask16 - s *)
Lemma add16_ones_eq_mask16_nonallones : forall s ck,
  s < two16 ->
  ck < two16 ->
  s <> mask16 ->
  add16_ones s ck = mask16 ->
  ck = mask16 - s.
Proof.
  intros s ck Hs Hck Hsneq H.
  destruct (s + ck <? two16) eqn:E.
  - apply N.ltb_lt in E.
    eapply add16_ones_eq_mask16_no_overflow; eauto.
  - apply N.ltb_ge in E.
    pose proof (add16_ones_eq_mask16_overflow_sum s ck E H) as Hsum.
    destruct (sum_eq_2mask16_bounds_force_mask16 s ck Hs Hck Hsum) as [Hs_eq _].
    exfalso; apply Hsneq; exact Hs_eq.
Qed.

(* Renamed variant for consistency *)
Lemma add16_ones_eq_mask16_complement : forall s ck,
  s < two16 ->
  ck < two16 ->
  s <> mask16 ->
  add16_ones s ck = mask16 ->
  ck = mask16 - s.
Proof.
  intros s ck Hs Hck Hsneq H.
  destruct (s + ck <? two16) eqn:E.
  - apply N.ltb_lt in E.
    eapply add16_ones_eq_mask16_no_overflow; eauto.
  - apply N.ltb_ge in E.
    pose proof (add16_ones_eq_mask16_overflow_sum s ck E H) as Hsum.
    destruct (sum_eq_2mask16_bounds_force_mask16 s ck Hs Hck Hsum) as [Hs_eq _].
    exfalso; apply Hsneq; exact Hs_eq.
Qed.

(* Helper: if mask16 - s ≠ 0, then s ≠ mask16 *)
Lemma mask16_sub_nonzero_implies_neq : forall s, 
  mask16 - s <> 0 -> s <> mask16.
Proof.
  intros s Hnz Heq. subst s.
  rewrite N.sub_diag in Hnz. contradiction.
Qed.

(* ===== 10.4 Checksum Field Recovery from Verifier ===== *)

(* Branch 1: When computed checksum = 0, transmitted field must be 0xFFFF *)
Lemma verify_ck_eq_mask16_when_cksum_zero : forall ipS ipD h data,
  header_norm h ->
  verify_checksum_ipv4 ipS ipD h data = true ->
  N.eqb (checksum h) 0 = false ->
  N.eqb (cksum16 (checksum_words_ipv4 ipS ipD h data)) 0 = true ->
  checksum h = mask16.
Proof.
  intros ipS ipD h data Hnorm Hver Hck_nz Heq0.
  set (ws := checksum_words_ipv4 ipS ipD h data).
  set (ck := checksum h).
  pose proof (verify_add16_mask16 ipS ipD h data Hnorm Hver) as Hadd.
  fold ws in Hadd. change (checksum h) with ck in Hadd.
  apply N.eqb_eq in Heq0.
  pose proof (cksum16_zero_sum_allones ws Heq0) as Hs_all.
  rewrite Hs_all in Hadd.
  apply N.eqb_neq in Hck_nz. change (checksum h) with ck in Hck_nz.
  destruct Hnorm as [_ [_ [_ Hck_lt]]].
  change (checksum h) with ck.
  apply (add16_ones_mask16_nonzero_eq_mask16 ck Hck_lt Hck_nz Hadd).
Qed.

(* Branch 2: When computed checksum ≠ 0, transmitted field equals computed value *)
Lemma verify_ck_eq_cksum16_when_cksum_nonzero : forall ipS ipD h data,
  header_norm h ->
  verify_checksum_ipv4 ipS ipD h data = true ->
  N.eqb (checksum h) 0 = false ->
  N.eqb (cksum16 (checksum_words_ipv4 ipS ipD h data)) 0 = false ->
  checksum h = cksum16 (checksum_words_ipv4 ipS ipD h data).
Proof.
  intros ipS ipD h data Hnorm Hver Hck_nz HeqNZ.
  set (ws := checksum_words_ipv4 ipS ipD h data).
  set (ck := checksum h).
  set (s  := sum16 ws) in *.
  pose proof (verify_add16_mask16 ipS ipD h data Hnorm Hver) as Hadd.
  fold ws in Hadd. change (checksum h) with ck in Hadd. fold s in Hadd.
  destruct Hnorm as [_ [_ [_ Hck_lt]]].
  apply N.eqb_neq in Hck_nz. change (checksum h) with ck in Hck_nz.
  assert (Hs_lt : s < two16) by (unfold s; apply sum16_lt_two16).
  apply N.eqb_neq in HeqNZ.
  Transparent cksum16 complement16.
  unfold cksum16, complement16 in HeqNZ. fold ws in HeqNZ. fold s in HeqNZ.
  pose proof (mask16_sub_nonzero_implies_neq s HeqNZ) as Hs_neq.
  Opaque cksum16 complement16.
  assert (Hck_eq : ck = mask16 - s)
    by (apply add16_ones_eq_mask16_complement; try assumption).
  change (checksum h) with ck.
  Transparent cksum16 complement16.
  unfold cksum16, complement16. fold ws. fold s. rewrite Hck_eq. reflexivity.
Qed.

(* Unified: verifier implies checksum equals computed value (non-zero case) *)
Lemma verify_implies_checksum_equals_computed_nonzero_split : forall ipS ipD h data,
  header_norm h ->
  verify_checksum_ipv4 ipS ipD h data = true ->
  N.eqb (checksum h) 0 = false ->
  checksum h = compute_udp_checksum_ipv4 ipS ipD h data.
Proof.
  intros ipS ipD h data Hnorm Hver Hnz.
  Transparent compute_udp_checksum_ipv4.
  unfold compute_udp_checksum_ipv4.
  destruct (N.eqb (cksum16 (checksum_words_ipv4 ipS ipD h data)) 0) eqn:Ez.
  - eapply verify_ck_eq_mask16_when_cksum_zero; eauto.
  - eapply verify_ck_eq_cksum16_when_cksum_nonzero; eauto.
  Opaque compute_udp_checksum_ipv4.
Qed.

(* ===== 10.5 Parser-Serializer Determinism ===== *)

(* Parsing serialized headers is deterministic *)
Lemma parse_header_bytes_of_header_norm_inv : forall h rest h' rest',
  header_norm h ->
  parse_header (udp_header_bytes h ++ rest) = Some (h', rest') ->
  h' = h /\ rest' = rest.
Proof.
  intros h rest h' rest' Hnorm Hparse.
  rewrite (parse_header_bytes_of_header_norm h rest Hnorm) in Hparse.
  inversion Hparse; subst; split; reflexivity.
Qed.

(* ===== 10.6 Big-Endian Round-trip at Byte Level ===== *)

Lemma be16_of_word16_word16_of_be_id : forall b0 b1,
  is_byte b0 = true -> is_byte b1 = true ->
  be16_of_word16 (word16_of_be b0 b1) = (b0, b1).
Proof.
  intros b0 b1 Hb0 Hb1.
  pose proof (is_byte_lt_two8 _ Hb0) as Hb0_lt.
  pose proof (is_byte_lt_two8 _ Hb1) as Hb1_lt.
  Transparent be16_of_word16 word16_of_be.
  unfold be16_of_word16, word16_of_be.
  
  assert (two8_ne : two8 <> 0) by (unfold two8; lia).
  
  assert (Hlo : (b0 * two8 + b1) mod two8 = b1).
  { rewrite N.add_mod by exact two8_ne.
    rewrite N.mod_mul by exact two8_ne.
    rewrite N.add_0_l.
    rewrite N.mod_mod by exact two8_ne.
    now rewrite N.mod_small by exact Hb1_lt. }
  
  assert (Hdiv : (b0 * two8 + b1) / two8 = b0).
  { rewrite N.div_add_l by exact two8_ne.
    rewrite N.div_small by exact Hb1_lt.
    rewrite N.add_0_r.
    reflexivity. }
  
  assert (Hhi : ((b0 * two8 + b1) / two8) mod two8 = b0).
  { rewrite Hdiv. 
    now rewrite N.mod_small by exact Hb0_lt. }
  
  rewrite Hhi, Hlo.
  reflexivity.
  Opaque be16_of_word16 word16_of_be.
Qed.

(* ===== 10.7 Parser Reveals Wire Structure ===== *)

Lemma parse_header_shape_bytes : forall w h rest,
  parse_header w = Some (h, rest) ->
  w = udp_header_bytes h ++ rest.
Proof.
  intros w h rest H.
  unfold parse_header in H.
  destruct w as [|s0 w]; try discriminate.
  destruct w as [|s1 w]; try discriminate.
  destruct w as [|d0 w]; try discriminate.
  destruct w as [|d1 w]; try discriminate.
  destruct w as [|l0 w]; try discriminate.
  destruct w as [|l1 w]; try discriminate.
  destruct w as [|c0 w]; try discriminate.
  destruct w as [|c1 rest0]; try discriminate.
  cbn in H.
  set (header8 := [s0; s1; d0; d1; l0; l1; c0; c1]).
  destruct (forallb is_byte header8) eqn:Hall.
  - unfold header8 in Hall.
    simpl in Hall.
    rewrite Hall in H.
    simpl in H.
    inversion H; subst h rest0; clear H.
    cbn in Hall.
    repeat (apply Bool.andb_true_iff in Hall as [? Hall]).
    unfold udp_header_bytes, udp_header_words; cbn.
    Transparent bytes_of_words16_be to_word16.
    simpl.
    assert (Hs: word16_of_be s0 s1 < two16) by (apply word16_of_be_lt_two16_of_is_byte; auto).
    assert (Hd: word16_of_be d0 d1 < two16) by (apply word16_of_be_lt_two16_of_is_byte; auto).
    assert (Hl: word16_of_be l0 l1 < two16) by (apply word16_of_be_lt_two16_of_is_byte; auto).
    assert (Hc: word16_of_be c0 c1 < two16) by (apply word16_of_be_lt_two16_of_is_byte; auto).
    rewrite (to_word16_id_if_lt _ Hs).
    rewrite (to_word16_id_if_lt _ Hd).
    rewrite (to_word16_id_if_lt _ Hl).
    rewrite (to_word16_id_if_lt _ Hc).
    rewrite (be16_of_word16_word16_of_be_id s0 s1); try assumption.
    rewrite (be16_of_word16_word16_of_be_id d0 d1); try assumption.
    rewrite (be16_of_word16_word16_of_be_id l0 l1); try assumption.
    rewrite (be16_of_word16_word16_of_be_id c0 c1); try assumption.
    reflexivity.
  - unfold header8 in Hall.
    simpl in Hall.
    rewrite Hall in H.
    simpl in H.
    discriminate H.
  Opaque bytes_of_words16_be to_word16.
Qed.

(* ===== 10.8 Decoder Analysis for Non-zero Checksum ===== *)

Lemma decode_defaults_nonzero_analysis : forall ipS ipD w sp dp data h rest,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  N.eqb (checksum h) 0 = false ->
  (* Conclusions *)
  header_norm h /\
  N.eqb (dst_port h) 0 = false /\
  lenN w = length16 h /\
  length16 h >= 8 /\
  data = rest /\
  sp = src_port h /\
  dp = dst_port h /\
  verify_checksum_ipv4 ipS ipD h rest = true.
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck_nz.
  
  assert (Hnorm : header_norm h) by (apply header_norm_of_parse_success with (w:=w) (rest:=rest); exact Hparse).
  
  unfold decode_udp_ipv4 in Hdec.
  rewrite Hparse in Hdec.
  
  assert (Epol : dst_port0_policy defaults_ipv4 = Reject) by reflexivity.
  rewrite Epol in Hdec.
  destruct (N.eqb (dst_port h) 0) eqn:Edp0; [discriminate|].
  
  set (Nbytes := lenN w) in *.
  set (L := length16 h) in *.
  
  assert (Emode : length_rx_mode defaults_ipv4 = StrictEq) by reflexivity.
  rewrite Emode in Hdec.
  
  destruct (L <? 8) eqn:EL8; [discriminate|].
  destruct (Nbytes <? L) eqn:ENbL; [discriminate|].
  destruct (N.eqb Nbytes L) eqn:EEq; [|discriminate].
  
  rewrite Hck_nz in Hdec.
  
  remember (take (N.to_nat (L - 8)) rest) as delivered.
  destruct (verify_checksum_ipv4 ipS ipD h delivered) eqn:Hver; [|discriminate].
  inversion Hdec; subst sp dp data; clear Hdec.
  
  assert (Hlen_eq : Nbytes = L) by (apply N.eqb_eq; exact EEq).
  assert (Hrest_eq : delivered = rest).
  { subst delivered Nbytes L.
    replace (length16 h - 8) with (lenN rest).
    2: { pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
         rewrite Hw in Hlen_eq.
         rewrite lenN_app, lenN_udp_header_bytes_8 in Hlen_eq. lia. }
    rewrite N_to_nat_lenN, take_length_id; reflexivity. }
  
  split; [exact Hnorm|].
  split; [reflexivity|].
  split; [exact Hlen_eq|].
  split. { apply N.ltb_ge in EL8. fold L in EL8. lia. }
  split; [exact Hrest_eq|].
  split; [reflexivity|].
  split; [reflexivity|].
  rewrite <- Hrest_eq; exact Hver.
Qed.

(* ===== 10.9 Encoder Setup for Non-zero Checksum ===== *)

Lemma encode_setup_for_defaults_nonzero : forall ipS ipD w h rest,
  parse_header w = Some (h, rest) ->
  header_norm h ->
  lenN w = length16 h ->
  (* Conclusions about encoding setup *)
  (8 + lenN rest <= mask16) /\
  (length16 h = 8 + lenN rest) /\
  (mk_header (src_port h) (dst_port h) (lenN rest) = 
   Some {| src_port := to_word16 (src_port h);
           dst_port := to_word16 (dst_port h);
           length16 := to_word16 (8 + lenN rest);
           checksum := 0 |}) /\
  (encode_udp_ipv4 defaults_ipv4 ipS ipD (src_port h) (dst_port h) rest =
   Ok (udp_header_bytes
        {| src_port := src_port h;
           dst_port := dst_port h;
           length16 := length16 h;
           checksum := compute_udp_checksum_ipv4 ipS ipD
                       {| src_port := src_port h;
                          dst_port := dst_port h;
                          length16 := length16 h;
                          checksum := 0 |} rest |} ++ rest)).
Proof.
  intros ipS ipD w h rest Hparse Hnorm Hlen_eq.
  
  assert (Hmk_ok : 8 + lenN rest <= mask16).
  { destruct Hnorm as [_ [_ [HL_lt _]]].
    assert (HL_eq : length16 h = 8 + lenN rest).
    { pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
      rewrite Hw in Hlen_eq.
      rewrite lenN_app, lenN_udp_header_bytes_8 in Hlen_eq. lia. }
    rewrite <- HL_eq. unfold mask16, two16 in *. lia. }
  
  assert (HL_eq' : length16 h = 8 + lenN rest).
  { pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
    rewrite Hw in Hlen_eq.
    rewrite lenN_app, lenN_udp_header_bytes_8 in Hlen_eq. lia. }
  
  assert (Hmk : mk_header (src_port h) (dst_port h) (lenN rest) = 
                Some {| src_port := to_word16 (src_port h);
                        dst_port := to_word16 (dst_port h);
                        length16 := to_word16 (8 + lenN rest);
                        checksum := 0 |}).
  { unfold mk_header. 
    apply N.leb_le in Hmk_ok. rewrite Hmk_ok. reflexivity. }
  
  split; [exact Hmk_ok|].
  split; [exact HL_eq'|].
  split; [exact Hmk|].
  
  unfold encode_udp_ipv4.
  rewrite Hmk.
  change (checksum_tx_mode defaults_ipv4) with WithChecksum.
  
  set (h0 := {| src_port := to_word16 (src_port h);
                dst_port := to_word16 (dst_port h);
                length16 := to_word16 (8 + lenN rest);
                checksum := 0 |}).
  
  destruct Hnorm as [Hsp_lt [Hdp_lt [HL_lt Hck_lt]]].
  
  assert (Hh0_eq : h0 = {| src_port := src_port h;
                           dst_port := dst_port h;
                           length16 := length16 h;
                           checksum := 0 |}).
  { unfold h0.
    rewrite (to_word16_id_if_lt (src_port h) Hsp_lt).
    rewrite (to_word16_id_if_lt (dst_port h) Hdp_lt).
    rewrite <- HL_eq'.
    rewrite (to_word16_id_if_lt (length16 h) HL_lt).
    reflexivity. }
  
  rewrite Hh0_eq.
  reflexivity.
Qed.

(* ===== 10.10 Checksum Computation Invariance ===== *)

Lemma checksum_invariant_with_zero : forall ipS ipD h rest,
  compute_udp_checksum_ipv4 ipS ipD h rest =
  compute_udp_checksum_ipv4 ipS ipD 
    {| src_port := src_port h;
       dst_port := dst_port h;
       length16 := length16 h;
       checksum := 0 |} rest.
Proof.
  intros ipS ipD h rest.
  Transparent compute_udp_checksum_ipv4.
  unfold compute_udp_checksum_ipv4.
  rewrite (checksum_words_ipv4_ck_invariant ipS ipD h rest 0).
  reflexivity.
  Opaque compute_udp_checksum_ipv4.
Qed.

(* ===== 10.11 Wire Equality for Non-zero Checksum ===== *)

Lemma encode_wire_equality_nonzero : forall ipS ipD w h rest,
  parse_header w = Some (h, rest) ->
  header_norm h ->
  verify_checksum_ipv4 ipS ipD h rest = true ->
  N.eqb (checksum h) 0 = false ->
  udp_header_bytes
    {| src_port := src_port h;
       dst_port := dst_port h;
       length16 := length16 h;
       checksum := compute_udp_checksum_ipv4 ipS ipD
                    {| src_port := src_port h;
                       dst_port := dst_port h;
                       length16 := length16 h;
                       checksum := 0 |} rest |} ++ rest = w.
Proof.
  intros ipS ipD w h rest Hparse Hnorm Hver Hck_nz.
  
  assert (Hck_eq : checksum h = compute_udp_checksum_ipv4 ipS ipD h rest).
  { apply verify_implies_checksum_equals_computed_nonzero_split; assumption. }
  
  rewrite <- (checksum_invariant_with_zero ipS ipD h rest).
  rewrite <- Hck_eq.
  rewrite (parse_header_shape_bytes w h rest Hparse).
  reflexivity.
Qed.

(* ===== 10.12 Main Completeness Theorem (Non-zero Checksum) ===== *)

Theorem decode_encode_completeness_defaults_nonzero_ck : forall ipS ipD w sp dp data h rest,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  N.eqb (checksum h) 0 = false ->
  encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok w.
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck_nz.
  
  pose proof (decode_defaults_nonzero_analysis ipS ipD w sp dp data h rest 
              Hdec Hparse Hck_nz) as 
              [Hnorm [Edp0 [Hlen_eq [HL_ge8 [Hdata_eq [Hsp_eq [Hdp_eq Hver]]]]]]].
  
  subst sp dp data.
  
  pose proof (encode_setup_for_defaults_nonzero ipS ipD w h rest 
              Hparse Hnorm Hlen_eq) as 
              [Hmk_ok [HL_eq' [Hmk Henc_shape]]].
  
  rewrite Henc_shape.
  f_equal.
  apply encode_wire_equality_nonzero; assumption.
Qed.

Corollary decode_encode_exact_match_nonzero : forall ipS ipD w sp dp data h rest,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  N.eqb (checksum h) 0 = false ->
  encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok w.
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck_nz.
  apply decode_encode_completeness_defaults_nonzero_ck with h rest; assumption.
Qed.

(* ===== 10.13 Canonical Wire Definition ===== *)

(* Canonical wire: header with computed checksum + data *)
Definition canonical_wire_defaults (ipS ipD:IPv4) (h:UdpHeader) (rest:list byte)
  : list byte :=
  udp_header_bytes
    {| src_port := src_port h;
       dst_port := dst_port h;
       length16 := length16 h;
       checksum := compute_udp_checksum_ipv4 ipS ipD h rest |}
  ++ rest.

(* ===== 10.14 Decoder Analysis for Zero Checksum ===== *)

Lemma decode_defaults_zero_analysis : forall ipS ipD w sp dp data h rest,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  N.eqb (checksum h) 0 = true ->
  (* Conclusions *)
  header_norm h /\
  N.eqb (dst_port h) 0 = false /\
  lenN w = length16 h /\
  length16 h >= 8 /\
  data = rest /\
  sp = src_port h /\
  dp = dst_port h.
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck0.
  assert (Hnorm : header_norm h)
    by (apply header_norm_of_parse_success with (w:=w) (rest:=rest); exact Hparse).
  unfold decode_udp_ipv4 in Hdec. rewrite Hparse in Hdec.
  assert (Epol : dst_port0_policy defaults_ipv4 = Reject) by reflexivity.
  rewrite Epol in Hdec.
  destruct (N.eqb (dst_port h) 0) eqn:Edp0; [discriminate|].
  set (Nbytes := lenN w) in *.
  set (L := length16 h) in *.
  assert (Emode : length_rx_mode defaults_ipv4 = StrictEq) by reflexivity.
  rewrite Emode in Hdec.
  destruct (L <? 8) eqn:EL8; [discriminate|].
  destruct (Nbytes <? L) eqn:ENbL; [discriminate|].
  destruct (N.eqb Nbytes L) eqn:EEq; [|discriminate].
  rewrite Hck0 in Hdec.
  change (checksum_rx_mode defaults_ipv4) with ValidOrZero in Hdec.
  change (zero_checksum_allowed defaults_ipv4 ipD) with true in Hdec.
  remember (take (N.to_nat (L - 8)) rest) as delivered.
  inversion Hdec; subst sp dp data; clear Hdec.
  assert (Hlen_eq : Nbytes = L) by (apply N.eqb_eq; exact EEq).
  assert (Hrest_eq : delivered = rest).
  { subst delivered Nbytes L.
    replace (length16 h - 8) with (lenN rest).
    2: { pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
         rewrite Hw in Hlen_eq.
         rewrite lenN_app, lenN_udp_header_bytes_8 in Hlen_eq. lia. }
    rewrite N_to_nat_lenN, take_length_id; reflexivity. }
  split; [exact Hnorm|].
  split; [reflexivity|].
  split; [exact Hlen_eq|].
  split. { apply N.ltb_ge in EL8. fold L in EL8. 
           assert (length16 h >= 8) by (unfold L in EL8; lia).
           assumption. }
  split; [exact Hrest_eq|].
  split; [reflexivity|reflexivity].
Qed.

(* ===== 10.15 Completeness for Zero Checksum ===== *)

Theorem decode_encode_completeness_defaults_zero_ck : forall ipS ipD w sp dp data h rest,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  N.eqb (checksum h) 0 = true ->
  encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data
    = Ok (canonical_wire_defaults ipS ipD h rest).
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck0.
  
  pose proof (decode_defaults_zero_analysis ipS ipD w sp dp data h rest
                Hdec Hparse Hck0)
    as [Hnorm [Edp0 [Hlen_eq [_ [Hdata_eq [Hsp_eq Hdp_eq]]]]]].
  subst sp dp data.

  pose proof (encode_setup_for_defaults_nonzero ipS ipD w h rest
                Hparse Hnorm Hlen_eq)
    as [Hmk_ok [_ [Hmk Hshape]]].

  unfold canonical_wire_defaults.
  rewrite Hshape.
  rewrite <- (checksum_invariant_with_zero ipS ipD h rest).
  reflexivity.
Qed.

(* ===== 10.16 Canonical Wire Properties ===== *)

Lemma canonical_wire_equals_original_nonzero : forall ipS ipD w sp dp data h rest,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  N.eqb (checksum h) 0 = false ->
  canonical_wire_defaults ipS ipD h rest = w.
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hcz.
  pose proof (decode_defaults_nonzero_analysis ipS ipD w sp dp data h rest
                Hdec Hparse Hcz)
    as [Hnorm [_ [_ [_ [_ [_ [_ Hver]]]]]]].
  unfold canonical_wire_defaults.
  
  assert (Hck_eq : checksum h = compute_udp_checksum_ipv4 ipS ipD h rest).
  { apply verify_implies_checksum_equals_computed_nonzero_split; assumption. }
  
  rewrite <- Hck_eq.
  symmetry.
  apply (parse_header_shape_bytes w h rest Hparse).
Qed.

(* ===== 10.17 Consolidated Completeness Theorem ===== *)

Theorem decode_encode_completeness_defaults : forall ipS ipD w sp dp data h rest,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data
    = Ok (canonical_wire_defaults ipS ipD h rest)
  /\
  (N.eqb (checksum h) 0 = false ->
     canonical_wire_defaults ipS ipD h rest = w).
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse.
  destruct (N.eqb (checksum h) 0) eqn:Hcz.
  - split.
    + eapply decode_encode_completeness_defaults_zero_ck; eauto.
    + intros Hcontra. discriminate.
  - split.
    + pose proof (decode_encode_completeness_defaults_nonzero_ck
                    ipS ipD w sp dp data h rest Hdec Hparse Hcz) as Henc_eq.
      rewrite Henc_eq.
      f_equal.
      symmetry.
      apply canonical_wire_equals_original_nonzero with sp dp data; assumption.
    + intros _.
      apply canonical_wire_equals_original_nonzero with sp dp data; assumption.
Qed.

(* ===== 10.18 Canonicalization Corollaries ===== *)

Corollary udp_canonicalization : forall ipS ipD w sp dp data,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  exists h rest,
    parse_header w = Some (h, rest) /\
    data = rest /\
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = 
      Ok (canonical_wire_defaults ipS ipD h rest) /\
    (N.eqb (checksum h) 0 = true \/ 
     canonical_wire_defaults ipS ipD h rest = w).
Proof.
  intros ipS ipD w sp dp data Hdec.
  assert (Hdec_copy := Hdec).
  unfold decode_udp_ipv4 in Hdec_copy.
  destruct (parse_header w) as [[h rest]|] eqn:Hparse; [|discriminate Hdec_copy].
  exists h, rest.
  split; [reflexivity|].
  
  pose proof (decode_encode_completeness_defaults ipS ipD w sp dp data h rest 
              Hdec Hparse) as [Henc Heq].
  
  destruct (N.eqb (checksum h) 0) eqn:Hcz.
  - pose proof (decode_defaults_zero_analysis ipS ipD w sp dp data h rest 
                Hdec Hparse Hcz) as [_ [_ [_ [_ [Hdata _]]]]].
    split; [exact Hdata|].
    split; [exact Henc|].
    left; reflexivity.
  - pose proof (decode_defaults_nonzero_analysis ipS ipD w sp dp data h rest 
                Hdec Hparse Hcz) as [_ [_ [_ [_ [Hdata _]]]]].
    split; [exact Hdata|].
    split; [exact Henc|].
    right; apply Heq; reflexivity.
Qed.

Corollary decode_encode_completeness_defaults_no_parse : forall ipS ipD w sp dp data,
  decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
  exists h rest,
    parse_header w = Some (h, rest) /\
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data
      = Ok (canonical_wire_defaults ipS ipD h rest) /\
    (N.eqb (checksum h) 0 = false ->
       canonical_wire_defaults ipS ipD h rest = w).
Proof.
  intros ipS ipD w sp dp data Hdec.
  assert (Hdec_copy := Hdec).
  unfold decode_udp_ipv4 in Hdec_copy.
  destruct (parse_header w) as [(h,rest)|] eqn:Hparse.
  - exists h, rest. 
    split; [reflexivity|].
    exact (decode_encode_completeness_defaults ipS ipD w sp dp data h rest Hdec Hparse).
  - discriminate Hdec_copy.
Qed.

End UDP_Decode_Encode_Completeness.

(* =============================================================================
   Section 11: Conformance Properties and Extended Validation
   
   Establishes additional protocol conformance properties including:
   - Injectivity of header serialization
   - Oversize detection boundaries
   - Checksum verification stability
   - AcceptShorter mode behavior
   - ICMP generation control with IP metadata
   - Source address validation
   ============================================================================= *)

Section UDP_R5_Conformance.
  Open Scope N_scope.

(* ===== 11.1 Injectivity of Header Serialization ===== *)

(* Header bytes uniquely determine the header under normalization *)
Lemma udp_header_bytes_inj : forall h1 h2,
  header_norm h1 -> header_norm h2 ->
  udp_header_bytes h1 = udp_header_bytes h2 ->
  h1 = h2.
Proof.
  intros h1 h2 Hn1 Hn2 Heq.
  pose proof (parse_header_bytes_of_header_norm h1 [] Hn1) as P1.
  pose proof (parse_header_bytes_of_header_norm h2 [] Hn2) as P2.
  rewrite Heq in P1.
  rewrite P1 in P2.
  now inversion P2.
Qed.

(* ===== 11.2 Encoder Size Monotonicity ===== *)

(* Oversize error occurs exactly when total length exceeds 65535 *)
Lemma encode_oversize_iff : forall cfg ipS ipD sp dp data,
  encode_udp_ipv4 cfg ipS ipD sp dp data = Err Oversize <->
  8 + lenN data > mask16.
Proof.
  intros cfg ipS ipD sp dp data; split; intro H.
  - (* -> *)
    unfold encode_udp_ipv4 in H.
    destruct (mk_header sp dp (lenN data)) as [h0|] eqn:Hmk; [discriminate|].
    unfold mk_header in Hmk.
    destruct (8 + lenN data <=? mask16) eqn:Hleb; [discriminate|].
    apply N.leb_gt in Hleb. lia.
  - (* <- *)
    unfold encode_udp_ipv4.
    unfold mk_header.
    destruct (8 + lenN data <=? mask16) eqn:Hleb.
    + apply N.leb_le in Hleb. lia.
    + reflexivity.
Qed.

(* ===== 11.3 Verification Stability Under Prefix ===== *)

Lemma take_len_app : forall (A:Type) (xs ys:list A),
  take (List.length xs) (xs ++ ys) = xs.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros ys; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma take_lenN_app : forall (A:Type) (xs ys:list A),
  take (N.to_nat (lenN xs)) (xs ++ ys) = xs.
Proof.
  intros A xs ys. rewrite N_to_nat_lenN. apply take_len_app.
Qed.

(* Verifier depends only on the L-8 prefix of data *)
Lemma verify_prefix_stability : forall ipS ipD h data tail,
  length16 h = 8 + lenN data ->
  verify_checksum_ipv4 ipS ipD h
    (take (N.to_nat (length16 h - 8)) (data ++ tail))
  = verify_checksum_ipv4 ipS ipD h data.
Proof.
  intros ipS ipD h data tail HL.
  rewrite HL, N_add_sub_cancel_l, N_to_nat_lenN.
  rewrite take_len_app. reflexivity.
Qed.

Corollary verify_prefix_stability_true : forall ipS ipD h data tail,
  length16 h = 8 + lenN data ->
  verify_checksum_ipv4 ipS ipD h data = true ->
  verify_checksum_ipv4 ipS ipD h
    (take (N.to_nat (length16 h - 8)) (data ++ tail)) = true.
Proof.
  intros; rewrite verify_prefix_stability by assumption; assumption.
Qed.

End UDP_R5_Conformance.

(* =============================================================================
   Section 12: AcceptShorter Mode - Surplus Octet Handling
   
   In AcceptShorterIP mode, the decoder accepts datagrams where the IP layer
   provides more data than the UDP length field indicates. The decoder delivers
   exactly the amount specified by the UDP length field, ignoring surplus.
   ============================================================================= *)

Section UDP_R2_AcceptShorter_Surplus.
  Open Scope N_scope.

(* ===== 12.1 Helper Lemmas ===== *)

(* Compute delivered slice under length constraints *)
Lemma delivered_eq_data_from_L : forall h (data tail : list byte),
  length16 h = 8 + lenN data ->
  take (N.to_nat (length16 h - 8)) (data ++ tail) = data.
Proof.
  intros h data tail HL.
  rewrite HL, N_add_sub_cancel_l, N_to_nat_lenN.
  apply take_len_app.
Qed.

(* Length guards for AcceptShorter with surplus *)
Lemma acceptShorter_length_guards : forall w h data tail,
  parse_header w = Some (h, data ++ tail) ->
  length16 h = 8 + lenN data ->
  (length16 h <? 8) = false /\
  (lenN w <? length16 h) = false.
Proof.
  intros w h data tail Hparse HL.
  pose proof (parse_header_shape_bytes _ _ _ Hparse) as Hw.
  split.
  - rewrite HL. apply N.ltb_ge. lia.
  - rewrite Hw, lenN_app, lenN_udp_header_bytes_8, HL, lenN_app.
    apply N.ltb_ge. lia.
Qed.

(* ===== 12.2 Main Acceptance Theorem ===== *)

(* AcceptShorter mode accepts surplus octets with Reject policy *)
Theorem decode_acceptShorter_surplus_defaults_reject_nonzero16 : 
  forall ipS ipD w h data tail,
  parse_header w = Some (h, data ++ tail) ->
  N.eqb (dst_port h) 0 = false ->
  length16 h = 8 + lenN data ->
  ( N.eqb (checksum h) 0 = true \/
    (N.eqb (checksum h) 0 = false /\ verify_checksum_ipv4 ipS ipD h data = true) ) ->
  decode_udp_ipv4 defaults_ipv4_acceptShorter ipS ipD w
    = Ok (src_port h, dst_port h, data).
Proof.
  intros ipS ipD w h data tail Hparse Hdp_nz HL Hck_cases.
  
  destruct (acceptShorter_length_guards w h data tail Hparse HL) as [EL8 ENbL].
  
  unfold decode_udp_ipv4. rewrite Hparse.
  change (dst_port0_policy defaults_ipv4_acceptShorter) with Reject.
  rewrite Hdp_nz, EL8, ENbL.
  change (length_rx_mode defaults_ipv4_acceptShorter) with AcceptShorterIP.
  
  destruct Hck_cases as [Hck0 | [HckNZ Hver_data]].
  - (* checksum = 0 *)
    rewrite Hck0.
    change (checksum_rx_mode defaults_ipv4_acceptShorter) with ValidOrZero.
    change (zero_checksum_allowed defaults_ipv4_acceptShorter ipD) with true.
    rewrite (delivered_eq_data_from_L h data tail HL).
    reflexivity.
  - (* checksum ≠ 0 *)
    rewrite HckNZ.
    rewrite (delivered_eq_data_from_L h data tail HL), Hver_data.
    reflexivity.
Qed.

(* Variant with Allow0 policy *)
Theorem decode_acceptShorter_surplus_defaults_allow0 : 
  forall ipS ipD w h data tail,
  parse_header w = Some (h, data ++ tail) ->
  length16 h = 8 + lenN data ->
  ( N.eqb (checksum h) 0 = true \/
    (N.eqb (checksum h) 0 = false /\ verify_checksum_ipv4 ipS ipD h data = true) ) ->
  decode_udp_ipv4 defaults_ipv4_allow0_acceptShorter ipS ipD w
    = Ok (src_port h, dst_port h, data).
Proof.
  intros ipS ipD w h data tail Hparse HL Hck_cases.
  
  destruct (acceptShorter_length_guards w h data tail Hparse HL) as [EL8 ENbL].
  
  unfold decode_udp_ipv4. rewrite Hparse.
  change (dst_port0_policy defaults_ipv4_allow0_acceptShorter) with Allow.
  rewrite EL8, ENbL.
  change (length_rx_mode defaults_ipv4_allow0_acceptShorter) with AcceptShorterIP.
  
  destruct Hck_cases as [Hck0 | [HckNZ Hver_data]].
  - rewrite Hck0.
    change (checksum_rx_mode defaults_ipv4_allow0_acceptShorter) with ValidOrZero.
    change (zero_checksum_allowed defaults_ipv4_allow0_acceptShorter ipD) with true.
    rewrite (delivered_eq_data_from_L h data tail HL).
    reflexivity.
  - rewrite HckNZ.
    rewrite (delivered_eq_data_from_L h data tail HL), Hver_data.
    reflexivity.
Qed.

End UDP_R2_AcceptShorter_Surplus.

(* =============================================================================
   Section 13: ICMP Error Suppression with IP Metadata
   
   Extends ICMP advisory interface with IP-layer metadata to enforce standard
   suppressions per RFC 1122 §3.2.2 and RFC 1812 §4.3.2.7.
   ============================================================================= *)

Section UDP_R3_ICMP_Suppression.
  Open Scope N_scope.

(* ===== 13.1 IP Metadata Structure ===== *)

Record IPMeta := {
  ll_broadcast     : bool;  (* Link-layer broadcast frame *)
  initial_fragment : bool;  (* True iff packet is initial fragment *)
  src_is_unicast   : bool   (* False for invalid/non-unicast sources *)
}.

(* ===== 13.2 Suppression Wrapper ===== *)

(* Apply standard suppressions before delegating to base advice *)
Definition udp_complete_icmp_advice_meta
  (cfg:Config) (meta:IPMeta)
  (has_listener: IPv4 -> word16 -> bool)
  (src_ip dst_ip:IPv4)
  (res: result UdpDeliver DecodeError) : RxAdvice :=
  if negb meta.(src_is_unicast) then NoAdvice else
  if negb meta.(initial_fragment) then NoAdvice else
  if meta.(ll_broadcast) then NoAdvice else
    udp_complete_icmp_advice cfg has_listener src_ip dst_ip res.

(* ===== 13.3 Elementary Suppression Lemmas ===== *)

Lemma icmp_suppression_src_not_unicast : forall cfg meta has_listener src dst res,
  meta.(src_is_unicast) = false ->
  udp_complete_icmp_advice_meta cfg meta has_listener src dst res = NoAdvice.
Proof.
  intros; unfold udp_complete_icmp_advice_meta.
  now rewrite H.
Qed.

Lemma icmp_suppression_non_initial_fragment : forall cfg meta has_listener src dst res,
  meta.(initial_fragment) = false ->
  udp_complete_icmp_advice_meta cfg meta has_listener src dst res = NoAdvice.
Proof.
  intros; unfold udp_complete_icmp_advice_meta.
  destruct (meta.(src_is_unicast)); [now rewrite H|reflexivity].
Qed.

Lemma icmp_suppression_ll_broadcast : forall cfg meta has_listener src dst res,
  meta.(ll_broadcast) = true ->
  udp_complete_icmp_advice_meta cfg meta has_listener src dst res = NoAdvice.
Proof.
  intros; unfold udp_complete_icmp_advice_meta.
  destruct (meta.(src_is_unicast)); [|reflexivity].
  destruct (meta.(initial_fragment)); [now rewrite H|reflexivity].
Qed.

(* ===== 13.4 Reduction to Base Advice ===== *)

Lemma icmp_meta_reduces_to_base : forall cfg meta has_listener src dst res,
  meta.(src_is_unicast) = true ->
  meta.(initial_fragment) = true ->
  meta.(ll_broadcast) = false ->
  udp_complete_icmp_advice_meta cfg meta has_listener src dst res
    = udp_complete_icmp_advice cfg has_listener src dst res.
Proof.
  intros; unfold udp_complete_icmp_advice_meta.
  now rewrite H, H0, H1.
Qed.

Lemma icmp_meta_reduces_to_rx_when_send : forall cfg meta has_listener src dst res,
  meta.(src_is_unicast) = true ->
  meta.(initial_fragment) = true ->
  meta.(ll_broadcast) = false ->
  should_send_icmp cfg dst = true ->
  udp_complete_icmp_advice_meta cfg meta has_listener src dst res
    = udp_rx_icmp_advice has_listener res.
Proof.
  intros cfg meta has_listener src dst res Hunicast Hinit Hll Hb.
  rewrite (icmp_meta_reduces_to_base cfg meta has_listener src dst res Hunicast Hinit Hll).
  unfold udp_complete_icmp_advice; now rewrite Hb.
Qed.

(* ===== 13.5 Port Unreachable with Metadata ===== *)

Corollary decode_generates_port_unreachable_with_meta : 
  forall ipS ipD sp dp data wire h0 has_listener meta,
  mk_header sp dp (lenN data) = Some h0 ->
  encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
  decode_udp_ipv4 defaults_ipv4 ipS ipD wire
    = Ok (to_word16 sp, to_word16 dp, data) ->
  has_listener ipD (to_word16 dp) = false ->
  should_send_icmp defaults_ipv4 ipD = true ->
  meta.(src_is_unicast) = true ->
  meta.(initial_fragment) = true ->
  meta.(ll_broadcast) = false ->
  udp_complete_icmp_advice_meta defaults_ipv4 meta has_listener ipS ipD
    (decode_udp_ipv4_with_addrs defaults_ipv4 ipS ipD wire)
  = SendICMPDestUnreach ICMP_PORT_UNREACH.
Proof.
  intros ipS ipD sp dp data wire h0 has_listener meta Hmk Henc Hdec Hnol Hsend Hun Hin Hll.
  rewrite (icmp_meta_reduces_to_rx_when_send
             defaults_ipv4 meta has_listener ipS ipD
             (decode_udp_ipv4_with_addrs defaults_ipv4 ipS ipD wire)
             Hun Hin Hll Hsend).
  unfold udp_rx_icmp_advice, decode_udp_ipv4_with_addrs.
  rewrite Hdec. cbn.
  rewrite Hnol. reflexivity.
Qed.

End UDP_R3_ICMP_Suppression.

(* =============================================================================
   Section 14: Source Address Screening
   
   Provides a wrapper that screens non-unicast source addresses per RFC 1122
   §3.2.1.3, dropping such datagrams without generating ICMP errors.
   ============================================================================= *)

Section UDP_R4_Source_Screening.
  Open Scope N_scope.

(* ===== 14.1 Screened Decoder ===== *)

Definition udp_decode_with_addrs_screened
  (cfg:Config) (meta:IPMeta)
  (src_ip dst_ip:IPv4) (wire:list byte) : option UdpDeliver :=
  if meta.(src_is_unicast)
  then match decode_udp_ipv4_with_addrs cfg src_ip dst_ip wire with
       | inl d  => Some d
       | inr _  => None
       end
  else None.

(* ===== 14.2 Screening Properties ===== *)

Lemma screened_preserves_success_with_addrs : forall cfg meta src dst wire d,
  meta.(src_is_unicast) = true ->
  decode_udp_ipv4_with_addrs cfg src dst wire = Ok d ->
  udp_decode_with_addrs_screened cfg meta src dst wire = Some d.
Proof.
  intros cfg meta src dst wire d Hun Hdec.
  unfold udp_decode_with_addrs_screened.
  rewrite Hun, Hdec. reflexivity.
Qed.

Lemma screened_blocks_invalid_with_addrs : forall cfg meta src dst wire,
  meta.(src_is_unicast) = false ->
  udp_decode_with_addrs_screened cfg meta src dst wire = None.
Proof.
  intros cfg meta src dst wire Hnu.
  unfold udp_decode_with_addrs_screened. now rewrite Hnu.
Qed.

Lemma screened_no_icmp_on_invalid_source : forall cfg meta has_listener src dst wire,
  meta.(src_is_unicast) = false ->
  udp_complete_icmp_advice_meta cfg meta has_listener src dst
    (decode_udp_ipv4_with_addrs cfg src dst wire)
  = NoAdvice.
Proof.
  intros cfg meta has_listener src dst wire Hnu.
  eapply icmp_suppression_src_not_unicast; exact Hnu.
Qed.

(* ===== 14.3 Round-trip Preservation ===== *)

Corollary screened_roundtrip_defaults_reject_nonzero16_with_addrs : 
  forall ipS ipD sp dp data wire h0 meta,
  meta.(src_is_unicast) = true ->
  to_word16 dp <> 0%N ->
  mk_header sp dp (lenN data) = Some h0 ->
  encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
  udp_decode_with_addrs_screened defaults_ipv4 meta ipS ipD wire
    = Some {| src_ip_out := ipS
            ; dst_ip_out := ipD
            ; src_port_out := to_word16 sp
            ; dst_port_out := to_word16 dp
            ; payload_out := data |}.
Proof.
  intros ipS ipD sp dp data wire h0 meta Hun HdpNZ Hmk Henc.
  eapply screened_preserves_success_with_addrs; [exact Hun|].
  unfold decode_udp_ipv4_with_addrs.
  rewrite (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16
             ipS ipD sp dp data wire h0 HdpNZ Hmk Henc).
  reflexivity.
Qed.

Corollary screened_roundtrip_defaults_allow0_with_addrs : 
  forall ipS ipD sp dp data wire h0 meta,
  meta.(src_is_unicast) = true ->
  mk_header sp dp (lenN data) = Some h0 ->
  encode_udp_ipv4 defaults_ipv4_allow0 ipS ipD sp dp data = Ok wire ->
  udp_decode_with_addrs_screened defaults_ipv4_allow0 meta ipS ipD wire
    = Some {| src_ip_out := ipS
            ; dst_ip_out := ipD
            ; src_port_out := to_word16 sp
            ; dst_port_out := to_word16 dp
            ; payload_out := data |}.
Proof.
  intros ipS ipD sp dp data wire h0 meta Hun Hmk Henc.
  eapply screened_preserves_success_with_addrs; [exact Hun|].
  unfold decode_udp_ipv4_with_addrs.
  set (h1 :=
        {| src_port := src_port h0
         ; dst_port := dst_port h0
         ; length16 := length16 h0
         ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).
  unfold encode_udp_ipv4 in Henc.
  rewrite Hmk in Henc.
  change (checksum_tx_mode defaults_ipv4_allow0) with WithChecksum in Henc.
  apply Ok_inj in Henc.
  subst wire.
  unfold decode_udp_ipv4.
  assert (Hnorm : header_norm h1)
    by (eapply header_norm_encode_h1; eauto).
  fold h1.
  replace (parse_header (udp_header_bytes h1 ++ data))
    with (Some (h1, data))
    by (symmetry; apply parse_header_bytes_of_header_norm; exact Hnorm).
  change (dst_port0_policy defaults_ipv4_allow0) with Allow.
  destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL0 _]]]].
  assert (HL0id : length16 h0 = 8 + lenN data)
    by (rewrite HL0; now apply to_word16_id_if_le_mask).
  
  assert (HL1 : length16 h1 = 8 + lenN data) by (unfold h1; simpl; exact HL0id).
  rewrite HL1.
  
  assert (EL8 : (8 + lenN data <? 8) = false) by (apply N.ltb_ge; lia).
  rewrite EL8.
  
  assert (ENbL : (lenN (udp_header_bytes h1 ++ data) <? 8 + lenN data) = false).
  { rewrite lenN_wire_from_header_bytes. apply N.ltb_ge. lia. }
  rewrite ENbL.
  
  change (length_rx_mode defaults_ipv4_allow0) with StrictEq.
  
  assert (EEq : (lenN (udp_header_bytes h1 ++ data) =? 8 + lenN data) = true).
  { rewrite lenN_wire_from_header_bytes. apply N.eqb_eq. reflexivity. }
  rewrite EEq.
  
  (* Checksum checks - be very precise, no simpl *)
  assert (Hck1 : checksum h1 = compute_udp_checksum_ipv4 ipS ipD h0 data)
    by reflexivity.
  rewrite Hck1.
  
  assert (Ecz : N.eqb (compute_udp_checksum_ipv4 ipS ipD h0 data) 0 = false)
    by (apply N.eqb_neq; apply compute_udp_checksum_ipv4_nonzero).
  rewrite Ecz.
  
  assert (Hdel : take (N.to_nat (8 + lenN data - 8)) data = data).
  { rewrite N_add_sub_cancel_l, N_to_nat_lenN. apply take_length_id. }
  rewrite Hdel.
  
  rewrite (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1 Hmk eq_refl).
  
  apply f_equal.
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp _]]].
  assert (Hsp1 : src_port h1 = src_port h0) by reflexivity.
  assert (Hdp1 : dst_port h1 = dst_port h0) by reflexivity.
  rewrite Hsp1, Hdp1, Hsp, Hdp.
  reflexivity.
Qed.

End UDP_R4_Source_Screening.

(* =============================================================================
   Section 15: Required Examples
   
   Demonstrates key protocol behaviors:
   E1: Surplus octet handling (accepted/rejected by mode)
   E2: Oversize boundary (rejection at mask16+1, acceptance at mask16)
   E3: ICMP suppression conditions
   ============================================================================= *)

Section UDP_Required_Examples.
  Open Scope N_scope.

(* ===== 15.1 Surplus Octet Behavior ===== *)

Definition tail2 : list byte := [0; 0].

(* AcceptShorter accepts surplus octets *)
Example EX_surplus_acceptShorter :
  exists w,
    let w' := w ++ tail2 in
    decode_udp_ipv4 defaults_ipv4_acceptShorter ex_src ex_dst w'
      = Ok (to_word16 ex_sp, to_word16 ex_dp, ex_payload).
Proof.
  destruct ex_encode_ok as [w Hw]. exists w. cbv zeta.
  assert (Hmk : exists h0, mk_header ex_sp ex_dp (lenN ex_payload) = Some h0).
  { unfold encode_udp_ipv4 in Hw.
    destruct (mk_header ex_sp ex_dp (lenN ex_payload)) as [h0|] eqn:E; [eauto|discriminate]. }
  destruct Hmk as [h0 Hmk].
  set (h1 :=
    {| src_port := src_port h0
     ; dst_port := dst_port h0
     ; length16 := length16 h0
     ; checksum := compute_udp_checksum_ipv4 ex_src ex_dst h0 ex_payload |}).
  unfold encode_udp_ipv4 in Hw. rewrite Hmk in Hw.
  change (checksum_tx_mode defaults_ipv4) with WithChecksum in Hw.
  apply Ok_inj in Hw.
  subst w.
  assert (Hnorm : header_norm h1) by (eapply header_norm_encode_h1; eauto).
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp0 [Hdp0' _]]].
  assert (Hsp1 : src_port h1 = to_word16 ex_sp) by (unfold h1; simpl; exact Hsp0).
  assert (Hdp1 : dst_port h1 = to_word16 ex_dp) by (unfold h1; simpl; exact Hdp0').
  rewrite <- Hsp1, <- Hdp1.
  eapply decode_acceptShorter_surplus_defaults_reject_nonzero16
    with (h := h1) (data := ex_payload) (tail := tail2).
  - rewrite <- app_assoc.
    apply parse_header_bytes_of_header_norm; exact Hnorm.
  - assert (Hdp_lt : ex_dp < two16) by (cbv [ex_dp two16]; lia).
    assert (Hdp_nz : to_word16 ex_dp <> 0).
    { intro Heq. rewrite (to_word16_id_if_lt _ Hdp_lt) in Heq.
      cbv [ex_dp] in Heq; discriminate. }
    apply N.eqb_neq. rewrite Hdp1. exact Hdp_nz.
  - eapply length16_h1_total_len; [exact Hmk|reflexivity].
  - right. split.
    + (* Prove checksum h1 ≠ 0 directly *)
      assert (checksum h1 = compute_udp_checksum_ipv4 ex_src ex_dst h0 ex_payload) by reflexivity.
      rewrite H.
      apply N.eqb_neq, compute_udp_checksum_ipv4_nonzero.
    + pose proof (verify_checksum_ipv4_encode_ok
                    ex_src ex_dst ex_sp ex_dp ex_payload h0 h1 Hmk eq_refl) as Hver.
      exact Hver.
Qed.

(* StrictEq rejects surplus octets *)
Example EX_surplus_rejected_StrictEq :
  exists w,
    decode_udp_ipv4 defaults_ipv4 ex_src ex_dst (w ++ tail2) = Err BadLength.
Proof.
  destruct ex_encode_ok as [w Hw]. exists w.
  assert (Hmk : exists h0, mk_header ex_sp ex_dp (lenN ex_payload) = Some h0).
  { unfold encode_udp_ipv4 in Hw.
    destruct (mk_header ex_sp ex_dp (lenN ex_payload)) as [h0|] eqn:E; [eauto|discriminate]. }
  destruct Hmk as [h0 Hmk].
  set (h1 :=
    {| src_port := src_port h0
     ; dst_port := dst_port h0
     ; length16 := length16 h0
     ; checksum := compute_udp_checksum_ipv4 ex_src ex_dst h0 ex_payload |}).
  unfold encode_udp_ipv4 in Hw. rewrite Hmk in Hw.
  change (checksum_tx_mode defaults_ipv4) with WithChecksum in Hw.
  apply Ok_inj in Hw.  (* <-- Fix 1: Use Ok_inj instead of inversion *)
  subst w.
  unfold decode_udp_ipv4.
  assert (Hnorm : header_norm h1) by (eapply header_norm_encode_h1; eauto).
  fold h1.
  rewrite <- app_assoc.
  rewrite (parse_header_bytes_of_header_norm h1 (ex_payload ++ tail2) Hnorm).
  change (dst_port0_policy defaults_ipv4) with Reject.
  assert (Hdp0 : (dst_port h1 =? 0) = false).
  { destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [Hdp _]]].
    (* Fix 2: Avoid unfold h1; simpl *)
    assert (dst_port h1 = dst_port h0) by reflexivity.
    rewrite H, Hdp.
    change (to_word16 ex_dp =? 0) with ((ex_dp mod two16) =? 0).
    cbv [ex_dp two16]. reflexivity. }
  rewrite Hdp0.
  set (Nbytes := lenN (udp_header_bytes h1 ++ ex_payload ++ tail2)).
  set (L := length16 h1).
  assert (HL : L = 8 + lenN ex_payload)
    by (eapply length16_h1_total_len; [exact Hmk|reflexivity]).
  assert (HNbytes : Nbytes = 8 + lenN ex_payload + lenN tail2).
  { subst Nbytes.
    rewrite lenN_app, lenN_udp_header_bytes_8, lenN_app. lia. }
  assert (EL8  : (L <? 8) = false)     by (rewrite HL; apply N.ltb_ge; lia).
  assert (ENbL : (Nbytes <? L) = false) by (rewrite HL, HNbytes; apply N.ltb_ge; lia).
  rewrite EL8, ENbL.
  change (length_rx_mode defaults_ipv4) with StrictEq.
  assert (EEq : (Nbytes =? L) = false).
  { rewrite HL, HNbytes. apply N.eqb_neq.
    assert (lenN tail2 > 0).
    { cbv [tail2 lenN]. simpl. lia. }
    lia. }
  rewrite EEq. reflexivity.
Qed.

(* ===== 15.2 Oversize Boundary ===== *)

Definition bytes_n (n:N) : list byte := List.repeat 0%N (N.to_nat n).

Lemma lenN_bytes_n : forall n, lenN (bytes_n n) = n.
Proof.
  intro n. unfold bytes_n, lenN.
  rewrite repeat_length.
  rewrite N2Nat.id. reflexivity.
Qed.

Definition n_over  : N := mask16 - 7.  (* 8 + n_over = mask16 + 1 *)
Definition n_limit : N := mask16 - 8.  (* 8 + n_limit = mask16 *)

Example EX_encode_oversize_at_boundary : forall cfg ipS ipD sp dp,
  encode_udp_ipv4 cfg ipS ipD sp dp (bytes_n n_over) = Err Oversize.
Proof.
  intros. rewrite encode_oversize_iff, lenN_bytes_n.
  cbv [n_over]. lia.
Qed.

Example EX_encode_accepts_at_limit : forall cfg ipS ipD sp dp,
  exists w, encode_udp_ipv4 cfg ipS ipD sp dp (bytes_n n_limit) = Ok w.
Proof.
  intros. destruct (encode_udp_ipv4 cfg ipS ipD sp dp (bytes_n n_limit)) eqn:E.
  - eauto.
  - destruct e.
    + rewrite encode_oversize_iff in E. rewrite lenN_bytes_n in E.
      cbv [n_limit] in E.
      exfalso.
      assert (8 + (mask16 - 8) = mask16).
      { unfold mask16. simpl. reflexivity. }
      rewrite H in E.
      unfold N.gt in E.
      rewrite N.compare_refl in E. discriminate.
Qed.

(* ===== 15.3 ICMP Suppression Examples ===== *)

Example EX_icmp_suppress_ll_broadcast_any : forall res,
  udp_complete_icmp_advice_meta defaults_ipv4
    {| ll_broadcast := true; initial_fragment := true; src_is_unicast := true |}
    (fun _ _ => false) ex_src ex_dst res
  = NoAdvice.
Proof. intros res. apply icmp_suppression_ll_broadcast. reflexivity. Qed.

Example EX_icmp_suppress_non_initial_fragment_any : forall res,
  udp_complete_icmp_advice_meta defaults_ipv4
    {| ll_broadcast := false; initial_fragment := false; src_is_unicast := true |}
    (fun _ _ => false) ex_src ex_dst res
  = NoAdvice.
Proof. intros res. apply icmp_suppression_non_initial_fragment. reflexivity. Qed.

Example EX_icmp_suppress_invalid_source_any : forall res,
  udp_complete_icmp_advice_meta defaults_ipv4
    {| ll_broadcast := false; initial_fragment := true; src_is_unicast := false |}
    (fun _ _ => false) ex_src ex_dst res
  = NoAdvice.
Proof. intros res. apply icmp_suppression_src_not_unicast. reflexivity. Qed.

End UDP_Required_Examples.

(* =============================================================================
   Section 16: Port Zero Source Handling
   
   RFC 768 permits source port 0 meaning "no reply expected". This section
   proves this works correctly through encode/decode cycles.
   ============================================================================= *)

Section UDP_Port_Zero_Source.
  Open Scope N_scope.

(* ===== 16.1 Encoding with Source Port Zero ===== *)

Theorem encode_source_port_zero_ok : forall cfg ipS ipD dp data,
  8 + lenN data <= mask16 ->
  exists wire, encode_udp_ipv4 cfg ipS ipD 0 dp data = Ok wire.
Proof.
  intros cfg ipS ipD dp data Hlen.
  unfold encode_udp_ipv4.
  assert (Hmk: mk_header 0 dp (lenN data) = 
          Some {| src_port := 0;
                  dst_port := to_word16 dp;
                  length16 := to_word16 (8 + lenN data);
                  checksum := 0 |}).
  { unfold mk_header.
    apply N.leb_le in Hlen. rewrite Hlen.
    reflexivity. }
  rewrite Hmk.
  destruct (checksum_tx_mode cfg); eexists; reflexivity.
Qed.

(* ===== 16.2 Decoding with Source Port Zero ===== *)

Theorem decode_source_port_zero_ok : forall ipS ipD dp data wire h0,
  to_word16 dp <> 0 ->
  mk_header 0 dp (lenN data) = Some h0 ->
  encode_udp_ipv4 defaults_ipv4 ipS ipD 0 dp data = Ok wire ->
  decode_udp_ipv4 defaults_ipv4 ipS ipD wire = Ok (0, to_word16 dp, data).
Proof.
  intros ipS ipD dp data wire h0 Hdp_nz Hmk Henc.
  apply (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16 
         ipS ipD 0 dp data wire h0 Hdp_nz Hmk Henc).
Qed.

(* ===== 16.3 Round-trip Properties ===== *)

Theorem roundtrip_source_port_zero : forall ipS ipD dp data,
  to_word16 dp <> 0 ->
  8 + lenN data <= mask16 ->
  exists wire,
    encode_udp_ipv4 defaults_ipv4 ipS ipD 0 dp data = Ok wire /\
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire = Ok (0, to_word16 dp, data).
Proof.
  intros ipS ipD dp data Hdp_nz Hlen.
  assert (Hmk: exists h0, mk_header 0 dp (lenN data) = Some h0).
  { unfold mk_header.
    apply N.leb_le in Hlen. rewrite Hlen.
    eexists; reflexivity. }
  destruct Hmk as [h0 Hmk].
  pose proof (encode_source_port_zero_ok defaults_ipv4 ipS ipD dp data Hlen) as [wire Henc].
  exists wire. split.
  - exact Henc.
  - apply (decode_source_port_zero_ok ipS ipD dp data wire h0 Hdp_nz Hmk Henc).
Qed.

(* ===== 16.4 Concrete Example ===== *)

Example ex_source_port_zero :
  let payload := [1; 2; 3]%N in
  exists wire,
    encode_udp_ipv4 defaults_ipv4 ex_src ex_dst 0 4242 payload = Ok wire /\
    decode_udp_ipv4 defaults_ipv4 ex_src ex_dst wire = Ok (0, 4242, payload).
Proof.
  simpl. 
  apply roundtrip_source_port_zero.
  - intro H. vm_compute in H. discriminate.
  - discriminate.
Qed.

End UDP_Port_Zero_Source.

(* =============================================================================
   Section 17: Maximum Length Edge Cases
   
   RFC 768 maximum datagram size handling: proves that the maximum valid
   datagram (65527 bytes of data, total 65535) works correctly and that
   length field overflow is impossible.
   ============================================================================= *)

Section UDP_Maximum_Length.
  Open Scope N_scope.

(* ===== 17.1 Maximum Size Definitions ===== *)

Definition max_udp_data_size : N := mask16 - 8.  (* 65527 bytes of data *)
Definition max_udp_total_size : N := mask16.      (* 65535 bytes total *)

(* ===== 17.2 Maximum Datagram Encoding ===== *)

Theorem encode_maximum_datagram_ok : forall cfg ipS ipD sp dp,
  exists wire,
    encode_udp_ipv4 cfg ipS ipD sp dp (bytes_n max_udp_data_size) = Ok wire /\
    lenN wire = max_udp_total_size.
Proof.
  intros cfg ipS ipD sp dp.
  assert (Hlen: 8 + lenN (bytes_n max_udp_data_size) <= mask16).
  { rewrite lenN_bytes_n. unfold max_udp_data_size.
    assert (8 + (mask16 - 8) = mask16).
    { unfold mask16. simpl. reflexivity. }
    rewrite H. reflexivity. }
  
  unfold encode_udp_ipv4.
  assert (Hmk: exists h0, mk_header sp dp (lenN (bytes_n max_udp_data_size)) = Some h0).
  { unfold mk_header. rewrite lenN_bytes_n.
    unfold max_udp_data_size.
    assert ((8 + (mask16 - 8) <=? mask16) = true).
    { apply N.leb_le. 
      assert (8 + (mask16 - 8) = mask16).
      { unfold mask16. simpl. reflexivity. }
      rewrite H. reflexivity. }
    rewrite H. eexists; reflexivity. }
  destruct Hmk as [h0 Hmk].
  rewrite Hmk.
  
  destruct (checksum_tx_mode cfg) eqn:Etx.
  - (* WithChecksum *)
    exists (udp_header_bytes
             {| src_port := src_port h0;
                dst_port := dst_port h0;
                length16 := length16 h0;
                checksum := compute_udp_checksum_ipv4 ipS ipD h0 (bytes_n max_udp_data_size) |}
           ++ bytes_n max_udp_data_size).
    split.
    + reflexivity.
    + rewrite lenN_app, lenN_udp_header_bytes_8, lenN_bytes_n.
      unfold max_udp_data_size, max_udp_total_size.
      assert (8 + (mask16 - 8) = mask16).
      { unfold mask16. simpl. reflexivity. }
      exact H.
  - (* NoChecksum *)
    exists (udp_header_bytes
             {| src_port := src_port h0;
                dst_port := dst_port h0;
                length16 := length16 h0;
                checksum := 0 |}
           ++ bytes_n max_udp_data_size).
    split.
    + reflexivity.
    + rewrite lenN_app, lenN_udp_header_bytes_8, lenN_bytes_n.
      unfold max_udp_data_size, max_udp_total_size.
      assert (8 + (mask16 - 8) = mask16).
      { unfold mask16. simpl. reflexivity. }
      exact H.
Qed.

(* ===== 17.3 Overflow Prevention ===== *)

Theorem length_field_no_overflow : forall sp dp data_len h,
  mk_header sp dp data_len = Some h ->
  length16 h < two16.
Proof.
  intros sp dp data_len h Hmk.
  destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL _]]]].
  rewrite HL.
  apply to_word16_lt_two16.
Qed.

Theorem length_field_correct : forall sp dp data_len h,
  mk_header sp dp data_len = Some h ->
  length16 h = to_word16 (8 + data_len) /\
  8 + data_len <= mask16.
Proof.
  intros sp dp data_len h Hmk.
  destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL _]]]].
  split.
  - exact HL.
  - exact Hle.
Qed.

(* ===== 17.4 Oversize Detection ===== *)

Theorem encode_oversized_fails : forall cfg ipS ipD sp dp,
  encode_udp_ipv4 cfg ipS ipD sp dp (bytes_n (max_udp_data_size + 1)) = Err Oversize.
Proof.
  intros cfg ipS ipD sp dp.
  rewrite encode_oversize_iff.
  rewrite lenN_bytes_n.
  unfold max_udp_data_size. lia.
Qed.

Theorem max_length_field_value : forall sp dp h,
  mk_header sp dp max_udp_data_size = Some h ->
  length16 h = mask16.
Proof.
  intros sp dp h Hmk.
  destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL _]]]].
  rewrite HL.
  unfold max_udp_data_size.
  assert (8 + (mask16 - 8) = mask16) by lia.
  rewrite H.
  apply to_word16_id_if_le_mask.
  lia.
Qed.

(* ===== 17.5 Maximum Size Round-trip ===== *)

Theorem roundtrip_maximum_size : forall ipS ipD sp dp,
  to_word16 dp <> 0 ->
  exists wire h0,
    mk_header sp dp max_udp_data_size = Some h0 /\
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp (bytes_n max_udp_data_size) = Ok wire /\
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire = 
      Ok (to_word16 sp, to_word16 dp, bytes_n max_udp_data_size).
Proof.
  intros ipS ipD sp dp Hdp_nz.
  assert (Hmk: exists h0, mk_header sp dp (lenN (bytes_n max_udp_data_size)) = Some h0).
  { unfold mk_header. rewrite lenN_bytes_n.
    unfold max_udp_data_size.
    assert ((8 + (mask16 - 8) <=? mask16) = true).
    { apply N.leb_le. 
      assert (8 + (mask16 - 8) = mask16).
      { unfold mask16. simpl. reflexivity. }
      rewrite H. reflexivity. }
    rewrite H. eexists; reflexivity. }
  destruct Hmk as [h0 Hmk].
  
  pose proof (encode_maximum_datagram_ok defaults_ipv4 ipS ipD sp dp) as [wire [Henc _]].
  exists wire, h0.
  split; [|split].
  - rewrite lenN_bytes_n in Hmk. exact Hmk.
  - exact Henc.
  - rewrite lenN_bytes_n in Hmk.
    apply (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16
             ipS ipD sp dp (bytes_n max_udp_data_size) wire h0 Hdp_nz Hmk Henc).
Qed.

(* ===== 17.6 No Valid Length Overflow ===== *)

Theorem no_valid_length_overflow : forall (data : list byte),
  lenN data <= max_udp_data_size ->
  8 + lenN data <= mask16.
Proof.
  intros data Hdata.
  unfold max_udp_data_size in Hdata.
  assert (lenN data <= mask16 - 8) by exact Hdata.
  assert (8 + lenN data <= 8 + (mask16 - 8)).
  { apply N.add_le_mono_l. exact H. }
  assert (8 + (mask16 - 8) = mask16).
  { unfold mask16. simpl. reflexivity. }
  rewrite H1 in H0. exact H0.
Qed.

End UDP_Maximum_Length.

(* =============================================================================
   Section 18: Checksum Zero Edge Cases
   
   Proves correct handling when computed checksum is 0x0000 (transmitted as
   0xFFFF) and zero checksum acceptance policies.
   ============================================================================= *)

Section UDP_Checksum_Zero.
  Open Scope N_scope.

(* ===== 18.1 Zero Checksum Transmission ===== *)

(* When computed checksum is 0x0000, transmitted value is 0xFFFF (mask16) *)
Theorem computed_zero_transmitted_mask16 : forall ipS ipD sp dp data h0,
  mk_header sp dp (lenN data) = Some h0 ->
  cksum16 (checksum_words_ipv4 ipS ipD h0 data) = 0 ->
  compute_udp_checksum_ipv4 ipS ipD h0 data = mask16.
Proof.
  intros ipS ipD sp dp data h0 Hmk Hzero.
  Transparent compute_udp_checksum_ipv4.
  unfold compute_udp_checksum_ipv4.
  apply N.eqb_eq in Hzero.
  rewrite Hzero.
  reflexivity.
Qed.

(* ===== 18.2 Zero Checksum Acceptance ===== *)

Example ex_zero_checksum_accepted :
  let h := {| src_port := 1234;
              dst_port := 5678;
              length16 := 11;
              checksum := 0 |} in
  let data := [1; 2; 3]%N in
  let wire := udp_header_bytes h ++ data in
  decode_udp_ipv4 defaults_ipv4 ex_src ex_dst wire = Ok (1234, 5678, data).
Proof.
  simpl.
  unfold decode_udp_ipv4.
  simpl.
  reflexivity.
Qed.

End UDP_Checksum_Zero.

(* =============================================================================
   Section 19: Property Exhaustiveness
   
   Proves that the decoder result is exhaustive - it always returns one of
   the four possible outcomes, establishing totality of the decoder function.
   ============================================================================= *)

Section UDP_Exhaustiveness.
  Open Scope N_scope.

(* ===== 19.1 Decoder Totality ===== *)

Theorem decode_total : forall cfg src dst wire,
  (exists sp dp data, decode_udp_ipv4 cfg src dst wire = Ok (sp, dp, data)) \/
  (decode_udp_ipv4 cfg src dst wire = Err BadLength) \/
  (decode_udp_ipv4 cfg src dst wire = Err BadChecksum) \/
  (decode_udp_ipv4 cfg src dst wire = Err DstPortZeroNotAllowed).
Proof.
  intros cfg src dst wire.
  unfold decode_udp_ipv4.
  destruct (parse_header wire) as [[h rest]|] eqn:Hparse.
  - (* Parse succeeded *)
    destruct (dst_port0_policy cfg) eqn:Epol.
    + (* Allow *)
      destruct (length16 h <? 8) eqn:EL8.
      * (* Length < 8 *)
        right. left. reflexivity.
      * (* Length >= 8 *)
        destruct (lenN wire <? length16 h) eqn:ENbL.
        -- (* Wire too short *)
           right. left. reflexivity.
        -- (* Wire long enough *)
           destruct (length_rx_mode cfg) eqn:Emode.
           ++ (* StrictEq *)
              destruct (lenN wire =? length16 h) eqn:EEq.
              ** (* Lengths match *)
                 destruct (checksum h =? 0) eqn:Eck.
                 --- (* Zero checksum *)
                     destruct (checksum_rx_mode cfg) eqn:Erx.
                     +++ (* RequireValidOnly *)
                         right. right. left. reflexivity.
                     +++ (* ValidOrZero *)
                         destruct (zero_checksum_allowed cfg dst) eqn:Ezero.
                         ++++ (* Zero allowed *)
                              left. eexists. eexists. eexists. reflexivity.
                         ++++ (* Zero not allowed *)
                              right. right. left. reflexivity.
                 --- (* Non-zero checksum *)
                     destruct (verify_checksum_ipv4 src dst h 
                                (take (N.to_nat (length16 h - 8)) rest)) eqn:Ever.
                     +++ (* Checksum valid *)
                         left. eexists. eexists. eexists. reflexivity.
                     +++ (* Checksum invalid *)
                         right. right. left. reflexivity.
              ** (* Lengths don't match *)
                 right. left. reflexivity.
           ++ (* AcceptShorterIP *)
              destruct (checksum h =? 0) eqn:Eck.
              ** (* Zero checksum *)
                 destruct (checksum_rx_mode cfg) eqn:Erx.
                 --- (* RequireValidOnly *)
                     right. right. left. reflexivity.
                 --- (* ValidOrZero *)
                     destruct (zero_checksum_allowed cfg dst) eqn:Ezero.
                     +++ (* Zero allowed *)
                         left. eexists. eexists. eexists. reflexivity.
                     +++ (* Zero not allowed *)
                         right. right. left. reflexivity.
              ** (* Non-zero checksum *)
                 destruct (verify_checksum_ipv4 src dst h 
                            (take (N.to_nat (length16 h - 8)) rest)) eqn:Ever.
                 --- (* Checksum valid *)
                     left. eexists. eexists. eexists. reflexivity.
                 --- (* Checksum invalid *)
                     right. right. left. reflexivity.
    + (* Reject *)
      destruct (dst_port h =? 0) eqn:Edp0.
      * (* Port 0 rejected *)
        right. right. right. reflexivity.
      * (* Port non-zero *)
        destruct (length16 h <? 8) eqn:EL8.
        -- (* Length < 8 *)
           right. left. reflexivity.
        -- (* Length >= 8 *)
           destruct (lenN wire <? length16 h) eqn:ENbL.
           ++ (* Wire too short *)
              right. left. reflexivity.
           ++ (* Wire long enough *)
              destruct (length_rx_mode cfg) eqn:Emode.
              ** (* StrictEq *)
                 destruct (lenN wire =? length16 h) eqn:EEq.
                 --- (* Lengths match *)
                     destruct (checksum h =? 0) eqn:Eck.
                     +++ (* Zero checksum *)
                         destruct (checksum_rx_mode cfg) eqn:Erx.
                         ++++ (* RequireValidOnly *)
                              right. right. left. reflexivity.
                         ++++ (* ValidOrZero *)
                              destruct (zero_checksum_allowed cfg dst) eqn:Ezero.
                              +++++ (* Zero allowed *)
                                    left. eexists. eexists. eexists. reflexivity.
                              +++++ (* Zero not allowed *)
                                    right. right. left. reflexivity.
                     +++ (* Non-zero checksum *)
                         destruct (verify_checksum_ipv4 src dst h 
                                    (take (N.to_nat (length16 h - 8)) rest)) eqn:Ever.
                         ++++ (* Checksum valid *)
                              left. eexists. eexists. eexists. reflexivity.
                         ++++ (* Checksum invalid *)
                              right. right. left. reflexivity.
                 --- (* Lengths don't match *)
                     right. left. reflexivity.
              ** (* AcceptShorterIP *)
                 destruct (checksum h =? 0) eqn:Eck.
                 --- (* Zero checksum *)
                     destruct (checksum_rx_mode cfg) eqn:Erx.
                     +++ (* RequireValidOnly *)
                         right. right. left. reflexivity.
                     +++ (* ValidOrZero *)
                         destruct (zero_checksum_allowed cfg dst) eqn:Ezero.
                         ++++ (* Zero allowed *)
                              left. eexists. eexists. eexists. reflexivity.
                         ++++ (* Zero not allowed *)
                              right. right. left. reflexivity.
                 --- (* Non-zero checksum *)
                     destruct (verify_checksum_ipv4 src dst h 
                                (take (N.to_nat (length16 h - 8)) rest)) eqn:Ever.
                     +++ (* Checksum valid *)
                         left. eexists. eexists. eexists. reflexivity.
                     +++ (* Checksum invalid *)
                         right. right. left. reflexivity.
  - (* Parse failed *)
    right. left. reflexivity.
Qed.

(* ===== 19.2 Decoder Never Gets Stuck ===== *)

Corollary decode_never_stuck : forall cfg src dst wire,
  exists r, decode_udp_ipv4 cfg src dst wire = r.
Proof.
  intros. eexists. reflexivity.
Qed.

End UDP_Exhaustiveness.

(* =============================================================================
   Section 20: Grand Unified Example
   
   Comprehensive test demonstrating all major protocol features:
   - Source port 0 handling
   - Oversize detection
   - Empty payload support
   - Decoder exhaustiveness
   - ICMP generation
   ============================================================================= *)

Section UDP_Grand_Proven_Example.
  Open Scope N_scope.
  
  Definition test_payload := [1; 2; 3]%N : list byte.
  Definition test_sp : word16 := 0.
  Definition test_dp : word16 := 53.
  
Theorem UDP_complete_test :
    (* Part 1: Source port 0 round-trip *)
    (exists wire,
      encode_udp_ipv4 defaults_ipv4 ex_src ex_dst test_sp test_dp test_payload = Ok wire /\
      decode_udp_ipv4 defaults_ipv4 ex_src ex_dst wire = Ok (0, test_dp, test_payload)) /\
    
    (* Part 2: Oversize boundary *)
    encode_udp_ipv4 defaults_ipv4 ex_src ex_dst test_sp test_dp (bytes_n (mask16 - 7)) = Err Oversize /\
    
    (* Part 3: Empty payload works *)
    (exists wire,
      encode_udp_ipv4 defaults_ipv4 ex_src ex_dst test_sp test_dp [] = Ok wire /\
      lenN wire = 8) /\
    
    (* Part 4: Decoder exhaustiveness *)
    (forall wire, exists r, decode_udp_ipv4 defaults_ipv4 ex_src ex_dst wire = r) /\
    
    (* Part 5: ICMP generated for unicast with no listener *)
    (exists wire,
      encode_udp_ipv4 defaults_ipv4 ex_src ex_dst test_sp test_dp test_payload = Ok wire /\
      udp_complete_icmp_advice defaults_ipv4 no_listener ex_src ex_dst
        (decode_udp_ipv4_with_addrs defaults_ipv4 ex_src ex_dst wire) = 
        SendICMPDestUnreach ICMP_PORT_UNREACH).
  Proof.
    split.
    
    (* Part 1: Source port 0 round-trip *)
    - apply roundtrip_source_port_zero.
      + intro H. vm_compute in H. discriminate.
      + simpl. vm_compute. discriminate.
    
    - split.
    
    (* Part 2: Oversize detection *)
    + rewrite encode_oversize_iff.
      rewrite lenN_bytes_n.
      unfold mask16. simpl. reflexivity.
    
    + split.
    
    (* Part 3: Empty payload *)
    * unfold encode_udp_ipv4.
      assert (HlenN: lenN (@nil byte) = 0) by reflexivity.
      rewrite HlenN.
      assert (Hmk: mk_header test_sp test_dp 0 = 
                   Some {| src_port := 0;
                           dst_port := test_dp;
                           length16 := 8;
                           checksum := 0 |}).
      { unfold mk_header. simpl.
        vm_compute. reflexivity. }
      rewrite Hmk.
      change (checksum_tx_mode defaults_ipv4) with WithChecksum.
      eexists. split.
      -- reflexivity.
      -- rewrite lenN_app, lenN_udp_header_bytes_8, HlenN.
         reflexivity.
    
    * split.
    
    (* Part 4: Exhaustiveness *)
    -- intro wire. eexists. reflexivity.
    
    (* Part 5: ICMP generation *)
    -- assert (Hdp_nz: to_word16 test_dp <> 0) by (intro H; vm_compute in H; discriminate).
       assert (Hlen: 8 + lenN test_payload <= mask16) by (simpl; vm_compute; discriminate).
       destruct (roundtrip_source_port_zero ex_src ex_dst test_dp test_payload Hdp_nz Hlen) 
         as [wire [Henc Hdec]].
       exists wire. split.
       ++ exact Henc.
       ++ unfold udp_complete_icmp_advice, should_send_icmp, udp_rx_icmp_advice.
          unfold decode_udp_ipv4_with_addrs.
          rewrite Hdec. simpl.
          unfold no_listener. reflexivity.
  Qed.

End UDP_Grand_Proven_Example.

(* =============================================================================
   Section 21: IPv6 Support for UDP
   
   RFC 8200 (IPv6) and RFC 2460 require non-zero checksums for UDP over IPv6.
   The pseudo-header includes 128-bit addresses and different fields.
   ============================================================================= *)

Section UDP_IPv6.
  Open Scope N_scope.

(* ===== 21.1 IPv6 Address Representation ===== *)

(* IPv6 address: 128 bits as 8 words of 16 bits each *)
Record IPv6 := {
  v6_0 : word16; v6_1 : word16; v6_2 : word16; v6_3 : word16;
  v6_4 : word16; v6_5 : word16; v6_6 : word16; v6_7 : word16
}.

(* Constructor with normalization *)
Definition mkIPv6 (w0 w1 w2 w3 w4 w5 w6 w7 : word16) : IPv6 :=
  {| v6_0 := to_word16 w0; v6_1 := to_word16 w1;
     v6_2 := to_word16 w2; v6_3 := to_word16 w3;
     v6_4 := to_word16 w4; v6_5 := to_word16 w5;
     v6_6 := to_word16 w6; v6_7 := to_word16 w7 |}.

(* IPv6 address as list of 16-bit words for checksum *)
Definition ipv6_words (ip : IPv6) : list word16 :=
  [ip.(v6_0); ip.(v6_1); ip.(v6_2); ip.(v6_3);
   ip.(v6_4); ip.(v6_5); ip.(v6_6); ip.(v6_7)].

(* ===== 21.2 IPv6 Pseudo-header ===== *)

(* IPv6 pseudo-header for UDP checksum (RFC 8200 Section 8.1) *)
Definition pseudo_header_v6 (src dst : IPv6) (udp_len : word16) : list word16 :=
  ipv6_words src ++
  ipv6_words dst ++
  [0; udp_len] ++              (* Upper-layer packet length *)
  [0; udp_protocol_number].    (* Next Header = 17 for UDP *)

(* ===== 21.3 IPv6 Checksum Computation ===== *)

(* Checksum material for UDP over IPv6 *)
Definition checksum_words_ipv6
  (src dst : IPv6) (h : UdpHeader) (data : list byte) : list word16 :=
  pseudo_header_v6 src dst h.(length16) ++
  udp_header_words_zero_ck h ++
  words16_of_bytes_be data.

(* Compute UDP checksum for IPv6 - NEVER returns 0 *)
Definition compute_udp_checksum_ipv6
  (src dst : IPv6) (h : UdpHeader) (data : list byte) : word16 :=
  let words := checksum_words_ipv6 src dst h data in
  let x := cksum16 words in
  if N.eqb x 0 then mask16 else x.

(* Verify checksum for IPv6 *)
Definition verify_checksum_ipv6
  (src dst : IPv6) (h : UdpHeader) (data : list byte) : bool :=
  let words := checksum_words_ipv6 src dst h data in
  let ws := words ++ [h.(checksum)] in
  N.eqb (sum16 ws) mask16.

(* ===== 21.4 IPv6 Configuration ===== *)

(* IPv6 configuration: checksum is MANDATORY *)
Definition defaults_ipv6 : Config :=
  {| checksum_tx_mode := WithChecksum;       (* Always compute checksum *)
     checksum_rx_mode := RequireValidOnly;   (* Zero checksum forbidden *)
     zero_checksum_policy := ZeroForbidAlways; (* Never accept zero *)
     length_rx_mode := StrictEq;
     dst_port0_policy := Reject;
     is_broadcast := fun _ => false          (* No broadcast in IPv6 *)
  |}.

(* ===== 21.5 IPv6 Encoder/Decoder ===== *)

(* IPv6 encoder - always includes checksum *)
Definition encode_udp_ipv6
  (src_ip dst_ip : IPv6) (sp dp : word16) (data : list byte)
  : result (list byte) EncodeError :=
  match mk_header sp dp (lenN data) with
  | None => Err Oversize
  | Some h0 =>
      let c := compute_udp_checksum_ipv6 src_ip dst_ip h0 data in
      let h1 := {| src_port := src_port h0;
                   dst_port := dst_port h0;
                   length16 := length16 h0;
                   checksum := c |} in
      Ok (udp_header_bytes h1 ++ data)
  end.

(* IPv6 decoder - rejects zero checksum *)
Definition decode_udp_ipv6
  (src_ip dst_ip : IPv6) (wire : list byte)
  : result Decoded DecodeError :=
  match parse_header wire with
  | None => Err BadLength
  | Some (h, rest) =>
      (* Check destination port policy *)
      match N.eqb h.(dst_port) 0 with
      | true => Err DstPortZeroNotAllowed
      | false =>
          let Nbytes := lenN wire in
          let L := h.(length16) in
          if (L <? 8)%N then Err BadLength else
          if (Nbytes <? L)%N then Err BadLength else
          if negb (N.eqb Nbytes L) then Err BadLength else
          (* IPv6: Zero checksum is ALWAYS invalid *)
          match N.eqb h.(checksum) 0 with
          | true => Err BadChecksum  (* RFC 8200: MUST NOT be zero *)
          | false =>
              let delivered := take (N.to_nat (L - 8)) rest in
              if verify_checksum_ipv6 src_ip dst_ip h delivered
              then Ok (h.(src_port), h.(dst_port), delivered)
              else Err BadChecksum
          end
      end
  end.

(* ===== 21.6 IPv6 Address Properties ===== *)

(* Multicast detection for IPv6: FF00::/8 *)
Definition is_multicast_ipv6 (ip : IPv6) : bool :=
  (ip.(v6_0) / 256) =? 255.  (* First byte is 0xFF *)

(* Example: IPv6 loopback address *)
Definition ipv6_loopback : IPv6 := mkIPv6 0 0 0 0 0 0 0 1.

(* Example: IPv6 link-local multicast *)
Definition ipv6_multicast : IPv6 := mkIPv6 0xFF02 0 0 0 0 0 0 1.

Example ipv6_multicast_detected :
  is_multicast_ipv6 ipv6_multicast = true.
Proof. reflexivity. Qed.

(* ===== 21.7 Zero Checksum Rejection in IPv6 ===== *)

Theorem ipv6_zero_checksum_rejected : forall src dst w h rest,
  parse_header w = Some (h, rest) ->
  checksum h = 0 ->
  N.eqb (dst_port h) 0 = false ->
  length16 h >= 8 ->
  lenN w = length16 h ->
  decode_udp_ipv6 src dst w = Err BadChecksum.
Proof.
  intros src dst w h rest Hparse Hck0 Hdp HL8 Hlen.
  unfold decode_udp_ipv6.
  rewrite Hparse.
  rewrite Hdp.
  assert (EL8: (length16 h <? 8) = false) by (apply N.ltb_ge; lia).
  rewrite EL8.
  assert (ENbL: (lenN w <? length16 h) = false) by (apply N.ltb_ge; lia).
  rewrite ENbL.
  assert (EEq: (lenN w =? length16 h) = true) by (apply N.eqb_eq; exact Hlen).
  rewrite EEq.
  assert (N.eqb (checksum h) 0 = true) by (apply N.eqb_eq; exact Hck0).
  rewrite H. reflexivity.
Qed.

(* ===== 21.8 Helper Lemmas for IPv6 ===== *)

(* IPv6 always produces non-zero checksum *)
Lemma compute_udp_checksum_ipv6_nonzero : forall src dst h data,
  compute_udp_checksum_ipv6 src dst h data <> 0.
Proof.
  intros src dst h data.
  unfold compute_udp_checksum_ipv6.
  destruct (cksum16 (checksum_words_ipv6 src dst h data) =? 0) eqn:E.
  - intro H. unfold mask16 in H. discriminate.
  - apply N.eqb_neq in E. exact E.
Qed.

(* cksum16 is always less than two16 *)
Lemma cksum16_lt_two16 : forall ws, 
  cksum16 ws < two16.
Proof.
  intro ws.
  Transparent cksum16 complement16.
  unfold cksum16, complement16.
  Opaque cksum16 complement16.
  assert (sum16 ws < two16) by apply sum16_lt_two16.
  unfold mask16, two16 in *.
  lia.
Qed.

(* Length equality for IPv6 *)
Lemma ipv6_length_equality : forall h0 data,
  length16 h0 = 8 + lenN data ->
  lenN (udp_header_bytes h0 ++ data) = length16 h0.
Proof.
  intros h0 data HL.
  rewrite lenN_app, lenN_udp_header_bytes_8.
  rewrite HL. reflexivity.
Qed.

(* Checksum words equality *)
Lemma checksum_words_ipv6_eq : forall src dst h data,
  checksum_words_ipv6 src dst h data =
  pseudo_header_v6 src dst (length16 h) ++
  udp_header_words_zero_ck h ++
  words16_of_bytes_be data.
Proof.
  intros. reflexivity.
Qed.

(* Sum16 with computed checksum *)
Lemma sum16_with_computed_ipv6 : forall src dst h0 data,
  sum16 (checksum_words_ipv6 src dst h0 data ++ 
         [compute_udp_checksum_ipv6 src dst h0 data]) = mask16.
Proof.
  intros.
  unfold compute_udp_checksum_ipv6.
  destruct (cksum16 (checksum_words_ipv6 src dst h0 data) =? 0) eqn:Ez.
  - apply sum16_app_mask16_of_allones.
    apply cksum16_zero_sum_allones.
    apply N.eqb_eq. exact Ez.
  - apply sum16_with_cksum_is_allones.
Qed.

(* Conditional checksum simplification when zero *)
Lemma compute_checksum_ipv6_zero_case : forall ws,
  cksum16 ws = 0 ->
  (if cksum16 ws =? 0 then mask16 else cksum16 ws) = mask16.
Proof.
  intros ws H.
  rewrite <- N.eqb_eq in H.
  rewrite H. reflexivity.
Qed.

(* Conditional checksum simplification when non-zero *)
Lemma compute_checksum_ipv6_nonzero_case : forall ws,
  cksum16 ws <> 0 ->
  (if cksum16 ws =? 0 then mask16 else cksum16 ws) = cksum16 ws.
Proof.
  intros ws H.
  rewrite <- N.eqb_neq in H.
  rewrite H. reflexivity.
Qed.

(* Sum with cksum when checksum is non-zero *)
Lemma sum16_ipv6_checksum_nonzero : forall ws n,
  cksum16 ws = N.pos n ->
  sum16 (ws ++ [if N.pos n =? 0 then mask16 else N.pos n]) = mask16.
Proof.
  intros ws n H.
  assert (N.pos n =? 0 = false) by (apply N.eqb_neq; lia).
  rewrite H0. simpl.
  rewrite <- H.
  apply sum16_with_cksum_is_allones.
Qed.

(* Sum with mask16 when checksum is 0 *)
Lemma sum16_ipv6_checksum_zero : forall ws,
  cksum16 ws = 0 ->
  sum16 (ws ++ [if 0 =? 0 then mask16 else 0]) = mask16.
Proof.
  intros ws H.
  assert (0 =? 0 = true) by reflexivity.
  rewrite H0.
  apply sum16_app_mask16_of_allones.
  apply cksum16_zero_sum_allones.
  exact H.
Qed.

(* Header norm for IPv6 encoded headers *)
Lemma header_norm_encode_ipv6 : forall sp dp len h0 src dst data,
  mk_header sp dp len = Some h0 ->
  header_norm {| src_port := src_port h0;
                 dst_port := dst_port h0;
                 length16 := length16 h0;
                 checksum := compute_udp_checksum_ipv6 src dst h0 data |}.
Proof.
  intros sp dp len h0 src dst data Hmk.
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp [Hlen _]]]].
  unfold header_norm; simpl.
  rewrite Hsp, Hdp, Hlen.
  repeat split; try apply to_word16_lt_two16.
  (* The checksum field *)
  unfold compute_udp_checksum_ipv6.
  destruct (cksum16 (checksum_words_ipv6 src dst h0 data) =? 0).
  - (* Zero case: returns mask16 *)
    unfold mask16, two16. compute. constructor.
  - (* Non-zero case: returns cksum16 value *)
    apply cksum16_lt_two16.
Qed.

(* ===== 21.9 IPv6 Never Generates Zero Checksum ===== *)

Theorem ipv6_checksum_never_zero : forall src dst sp dp data wire,
  encode_udp_ipv6 src dst sp dp data = Ok wire ->
  exists h rest,
    parse_header wire = Some (h, rest) /\
    checksum h <> 0.
Proof.
  intros src dst sp dp data wire Henc.
  unfold encode_udp_ipv6 in Henc.
  destruct (mk_header sp dp (lenN data)) as [h0|] eqn:Hmk; [|discriminate].
  apply Ok_inj in Henc.
  subst wire.
  
  set (c := compute_udp_checksum_ipv6 src dst h0 data).
  set (h1 := {| src_port := src_port h0;
                dst_port := dst_port h0;
                length16 := length16 h0;
                checksum := c |}).
  
  exists h1, data.
  split.
  - assert (Hnorm: header_norm h1).
    { unfold h1. apply header_norm_encode_ipv6 with (sp := sp) (dp := dp) (len := lenN data). exact Hmk. }
    apply parse_header_bytes_of_header_norm. exact Hnorm.
  - unfold h1, c; simpl.
    apply compute_udp_checksum_ipv6_nonzero.
Qed.

(* ===== 21.10 Verifier Correctness for IPv6 ===== *)

Lemma verify_checksum_ipv6_encode_ok : forall src dst sp dp data h0 h1,
  mk_header sp dp (lenN data) = Some h0 ->
  h1 = {| src_port := src_port h0;
          dst_port := dst_port h0;
          length16 := length16 h0;
          checksum := compute_udp_checksum_ipv6 src dst h0 data |} ->
  verify_checksum_ipv6 src dst h1 data = true.
Proof.
  intros src dst sp dp data h0 h1 Hmk ->.
  unfold verify_checksum_ipv6.
  
  assert (Heq: checksum_words_ipv6 src dst 
         {| src_port := src_port h0;
            dst_port := dst_port h0;
            length16 := length16 h0;
            checksum := compute_udp_checksum_ipv6 src dst h0 data |} data =
         checksum_words_ipv6 src dst h0 data).
  { unfold checksum_words_ipv6, udp_header_words_zero_ck. simpl. reflexivity. }
  
  rewrite Heq.
  (* Don't use simpl - just note that the checksum field is compute_udp_checksum_ipv6 *)
  assert (Hck_eq: checksum {| src_port := src_port h0;
                              dst_port := dst_port h0;
                              length16 := length16 h0;
                              checksum := compute_udp_checksum_ipv6 src dst h0 data |} = 
                  compute_udp_checksum_ipv6 src dst h0 data) by reflexivity.
  rewrite Hck_eq.
  
  apply N.eqb_eq.
  apply sum16_with_computed_ipv6.
Qed.

(* ===== 21.11 Decoder Analysis Lemmas ===== *)

Lemma decode_ipv6_structure : forall src dst sp dp data h0,
  to_word16 dp <> 0 ->
  mk_header sp dp (lenN data) = Some h0 ->
  let h1 := {| src_port := src_port h0;
               dst_port := dst_port h0;
               length16 := length16 h0;
               checksum := compute_udp_checksum_ipv6 src dst h0 data |} in
  let wire := udp_header_bytes h1 ++ data in
  decode_udp_ipv6 src dst wire = 
    if verify_checksum_ipv6 src dst h1 (take (N.to_nat (length16 h1 - 8)) data)
    then Ok (src_port h1, dst_port h1, take (N.to_nat (length16 h1 - 8)) data)
    else Err BadChecksum.
Proof.
  intros src dst sp dp data h0 Hdp_nz Hmk.
  
  set (h1 := {| src_port := src_port h0;
                dst_port := dst_port h0;
                length16 := length16 h0;
                checksum := compute_udp_checksum_ipv6 src dst h0 data |}).
  
  unfold decode_udp_ipv6.
  
  assert (Hnorm: header_norm h1) by (unfold h1; eapply header_norm_encode_ipv6; exact Hmk).
  rewrite (parse_header_bytes_of_header_norm h1 data Hnorm).
  
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [Hdp _]]].
  assert (Hdp_eq: dst_port h1 = to_word16 dp) by (unfold h1; simpl; exact Hdp).
  rewrite Hdp_eq.
  rewrite <- N.eqb_neq in Hdp_nz.
  rewrite Hdp_nz.
  
  destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [Hsp [_ [HL _]]]].
  assert (HL_eq: length16 h1 = to_word16 (8 + lenN data)) by (unfold h1; simpl; exact HL).
  rewrite HL_eq.
  rewrite to_word16_id_if_le_mask by exact Hle.
  
  assert (EL8: (8 + lenN data <? 8) = false) by (apply N.ltb_ge; lia).
  rewrite EL8.
  
  assert (HNbytes: lenN (udp_header_bytes h1 ++ data) = 8 + lenN data)
    by (rewrite lenN_app, lenN_udp_header_bytes_8; reflexivity).
  rewrite HNbytes.
  
  assert (ENbL: (8 + lenN data <? 8 + lenN data) = false) by (apply N.ltb_ge; lia).
  rewrite ENbL.
  
  assert (EEq: (8 + lenN data =? 8 + lenN data) = true) by (apply N.eqb_eq; reflexivity).
  rewrite EEq.
  assert (Hnegb: negb true = false) by reflexivity.
  rewrite Hnegb.
  
  (* Show checksum h1 ≠ 0 *)
  assert (Hck_eq: checksum h1 = compute_udp_checksum_ipv6 src dst h0 data) 
    by (unfold h1; simpl; reflexivity).
  rewrite Hck_eq.
  assert (Hck_nz: compute_udp_checksum_ipv6 src dst h0 data <> 0) 
    by apply compute_udp_checksum_ipv6_nonzero.
  rewrite <- N.eqb_neq in Hck_nz.
  rewrite Hck_nz.
  
  reflexivity.
Qed.

(* ===== 21.12 Round-trip Theorems for IPv6 ===== *)

Lemma decode_ipv6_returns_values : forall src dst sp dp data h0,
  to_word16 dp <> 0 ->
  mk_header sp dp (lenN data) = Some h0 ->
  let h1 := {| src_port := src_port h0;
               dst_port := dst_port h0;
               length16 := length16 h0;
               checksum := compute_udp_checksum_ipv6 src dst h0 data |} in
  let wire := udp_header_bytes h1 ++ data in
  decode_udp_ipv6 src dst wire = Ok (src_port h0, dst_port h0, data).
Proof.
  intros src dst sp dp data h0 Hdp_nz Hmk.
  
  set (h1 := {| src_port := src_port h0;
                dst_port := dst_port h0;
                length16 := length16 h0;
                checksum := compute_udp_checksum_ipv6 src dst h0 data |}).
  
  unfold h1.
  rewrite (decode_ipv6_structure src dst sp dp data h0 Hdp_nz Hmk).
  fold h1.
  
  destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [Hsp [Hdp' [HL _]]]].
  assert (Htake: take (N.to_nat (length16 h1 - 8)) data = data).
  { unfold h1; simpl.
    rewrite HL.
    rewrite to_word16_id_if_le_mask by exact Hle.
    rewrite N_add_sub_cancel_l, N_to_nat_lenN.
    apply take_length_id. }
  rewrite Htake.
  
  rewrite (verify_checksum_ipv6_encode_ok src dst sp dp data h0 h1 Hmk eq_refl).
  
  reflexivity.
Qed.

Theorem decode_encode_roundtrip_ipv6 : forall src dst sp dp data wire h0,
  to_word16 dp <> 0 ->
  mk_header sp dp (lenN data) = Some h0 ->
  encode_udp_ipv6 src dst sp dp data = Ok wire ->
  decode_udp_ipv6 src dst wire = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros src dst sp dp data wire h0 Hdp_nz Hmk Henc.
  
  unfold encode_udp_ipv6 in Henc.
  rewrite Hmk in Henc.
  apply Ok_inj in Henc.
  subst wire.
  
  rewrite (decode_ipv6_returns_values src dst sp dp data h0 Hdp_nz Hmk).
  
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp _]]].
  rewrite Hsp, Hdp.
  reflexivity.
Qed.

(* ===== 21.13 Additional Helper Lemmas ===== *)

(* If sum is all-ones, then cksum16 is zero *)
Lemma cksum16_zero_of_sum_allones : forall ws, 
  sum16 ws = mask16 -> cksum16 ws = 0.
Proof.
  intros ws H.
  Transparent cksum16 complement16.
  unfold cksum16, complement16.
  Opaque cksum16 complement16.
  rewrite H.
  unfold mask16. lia.
Qed.

Lemma sum16_app_single_inv : forall ws ck,
  ck < two16 ->
  sum16 (ws ++ [ck]) = mask16 ->
  add16_ones (sum16 ws) ck = mask16.
Proof.
  intros ws ck Hlt Hsum.
  rewrite sum16_app_single in Hsum.
  rewrite to_word16_id_if_lt in Hsum by assumption.
  exact Hsum.
Qed.

(* Opaque lemma for the checksum words equality *)
Lemma checksum_words_ipv6_zero_ck_eq : forall src dst h data,
  checksum_words_ipv6 src dst h data =
  checksum_words_ipv6 src dst
    {| src_port := src_port h;
       dst_port := dst_port h;
       length16 := length16 h;
       checksum := 0 |} data.
Proof.
  intros. unfold checksum_words_ipv6, udp_header_words_zero_ck. simpl. reflexivity.
Qed.
Opaque checksum_words_ipv6_zero_ck_eq.

(* Establishing the add16_ones equation from verifier success *)
Lemma verify_ipv6_implies_add16_ones_mask16 : forall src dst h data,
  header_norm h ->
  verify_checksum_ipv6 src dst h data = true ->
  add16_ones (sum16 (checksum_words_ipv6 src dst
              {| src_port := src_port h;
                 dst_port := dst_port h;
                 length16 := length16 h;
                 checksum := 0 |} data)) (checksum h) = mask16.
Proof.
  intros src dst h data Hnorm Hver.
  destruct Hnorm as [_ [_ [_ Hck_lt]]].
  
  (* Establish the key equation abstractly *)
  assert (E: verify_checksum_ipv6 src dst h data = 
             N.eqb (sum16 (checksum_words_ipv6 src dst h data ++ [checksum h])) mask16)
    by reflexivity.
  
  rewrite E in Hver. clear E.
  rewrite checksum_words_ipv6_zero_ck_eq in Hver.
  apply N.eqb_eq in Hver.
  
  exact (sum16_app_single_inv _ _ Hck_lt Hver).
Defined.

(* When cksum16 is non-zero and add16_ones gives mask16, checksum equals cksum16 *)
Lemma checksum_equals_cksum16_when_nonzero : forall ws ck,
  ck < two16 ->
  ck <> 0 ->
  cksum16 ws <> 0 ->
  add16_ones (sum16 ws) ck = mask16 ->
  ck = cksum16 ws.
Proof.
  intros ws ck Hck_lt Hck_nz Hws_nz Hadd.
  assert (Hs_lt: sum16 ws < two16) by apply sum16_lt_two16.
  
  assert (Hs_neq: sum16 ws <> mask16).
  { intro Heq.
    assert (cksum16 ws = 0) by (apply cksum16_zero_of_sum_allones; exact Heq).
    contradiction. }
  
  apply add16_ones_eq_mask16_complement in Hadd; [|exact Hs_lt|exact Hck_lt|exact Hs_neq].
  Transparent cksum16 complement16.
  unfold cksum16, complement16 in *.
  Opaque cksum16 complement16.
  exact Hadd.
Qed.

(* ===== 21.14 Completeness Theorem for IPv6 ===== *)

(* Various helper lemmas for completeness proof *)

Lemma decode_ipv6_parse_success : forall src dst w sp dp data,
  decode_udp_ipv6 src dst w = Ok (sp, dp, data) ->
  exists h rest, parse_header w = Some (h, rest).
Proof.
  intros src dst w sp dp data Hdec.
  unfold decode_udp_ipv6 in Hdec.
  destruct (parse_header w) as [[h rest]|] eqn:Hparse.
  - eauto.
  - discriminate.
Qed.

Lemma decode_ipv6_checksum_nonzero : forall src dst w sp dp data h rest,
  decode_udp_ipv6 src dst w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  checksum h <> 0.
Proof.
  intros src dst w sp dp data h rest Hdec Hparse.
  unfold decode_udp_ipv6 in Hdec.
  rewrite Hparse in Hdec.
  destruct (dst_port h =? 0); [discriminate|].
  destruct (length16 h <? 8); [discriminate|].
  destruct (lenN w <? length16 h); [discriminate|].
  destruct (negb (lenN w =? length16 h)); [discriminate|].
  destruct (checksum h =? 0) eqn:E; [discriminate|].
  apply N.eqb_neq. exact E.
Qed.

Lemma decode_ipv6_length_eq : forall src dst w sp dp data h rest,
  decode_udp_ipv6 src dst w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  lenN w = length16 h /\ length16 h = 8 + lenN rest.
Proof.
  intros src dst w sp dp data h rest Hdec Hparse.
  unfold decode_udp_ipv6 in Hdec.
  rewrite Hparse in Hdec.
  destruct (dst_port h =? 0); [discriminate|].
  destruct (length16 h <? 8); [discriminate|].
  destruct (lenN w <? length16 h); [discriminate|].
  destruct (negb (lenN w =? length16 h)) eqn:E; [discriminate|].
  simpl in E. apply negb_false_iff, N.eqb_eq in E.
  split. 
  - exact E.
  - pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
    rewrite Hw, lenN_app, lenN_udp_header_bytes_8 in E. lia.
Qed.

Lemma decode_ipv6_data_eq_rest : forall src dst w sp dp data h rest,
  decode_udp_ipv6 src dst w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  data = rest /\ sp = src_port h /\ dp = dst_port h.
Proof.
  intros src dst w sp dp data h rest Hdec Hparse.
  unfold decode_udp_ipv6 in Hdec.
  rewrite Hparse in Hdec.
  destruct (dst_port h =? 0); [discriminate|].
  destruct (length16 h <? 8) eqn:EL8; [discriminate|].
  destruct (lenN w <? length16 h); [discriminate|].
  destruct (negb (lenN w =? length16 h)) eqn:EEq; [discriminate|].
  destruct (checksum h =? 0); [discriminate|].
  simpl in EEq. apply negb_false_iff, N.eqb_eq in EEq.
  destruct (verify_checksum_ipv6 src dst h (take (N.to_nat (length16 h - 8)) rest)); [|discriminate].
  apply Ok_inj in Hdec. injection Hdec as <- <- <-.
  apply N.ltb_ge in EL8.
  pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
  rewrite Hw, lenN_app, lenN_udp_header_bytes_8 in EEq.
  assert (length16 h = 8 + lenN rest) by lia.
  rewrite H, N_add_sub_cancel_l, N_to_nat_lenN.
  rewrite take_length_id.
  auto.
Qed.

Lemma verify_implies_checksum_equals_computed_ipv6 : forall src dst h data,
  header_norm h ->
  verify_checksum_ipv6 src dst h data = true ->
  checksum h <> 0 ->
  checksum h = compute_udp_checksum_ipv6 src dst 
    {| src_port := src_port h;
       dst_port := dst_port h;
       length16 := length16 h;
       checksum := 0 |} data.
Proof.
  intros src dst h data Hnorm Hver Hnz.
  
  pose proof (verify_ipv6_implies_add16_ones_mask16 src dst h data Hnorm Hver) as Hadd.
  
  set (ws := checksum_words_ipv6 src dst
               {| src_port := src_port h;
                  dst_port := dst_port h;
                  length16 := length16 h;
                  checksum := 0 |} data) in *.
  
  unfold compute_udp_checksum_ipv6.
  fold ws.
  destruct (cksum16 ws =? 0) eqn:Ez.
  - apply N.eqb_eq in Ez.
    apply cksum16_zero_sum_allones in Ez.
    rewrite Ez in Hadd.
    destruct Hnorm as [_ [_ [_ Hck_lt]]].
    apply add16_ones_mask16_nonzero_eq_mask16 in Hadd; [|exact Hck_lt|exact Hnz].
    exact Hadd.
    
  - apply N.eqb_neq in Ez.
    destruct Hnorm as [_ [_ [_ Hck_lt]]].
    apply checksum_equals_cksum16_when_nonzero with (ws := ws); assumption.
Qed.

Lemma decode_ipv6_checksum_eq_computed : forall src dst w sp dp data h rest,
  decode_udp_ipv6 src dst w = Ok (sp, dp, data) ->
  parse_header w = Some (h, rest) ->
  verify_checksum_ipv6 src dst h rest = true /\
  checksum h = compute_udp_checksum_ipv6 src dst 
    {| src_port := src_port h;
       dst_port := dst_port h;
       length16 := length16 h;
       checksum := 0 |} rest.
Proof.
  intros src dst w sp dp data h rest Hdec Hparse.
  unfold decode_udp_ipv6 in Hdec.
  rewrite Hparse in Hdec.
  destruct (dst_port h =? 0); [discriminate|].
  destruct (length16 h <? 8) eqn:EL8; [discriminate|].
  destruct (lenN w <? length16 h); [discriminate|].
  destruct (negb (lenN w =? length16 h)) eqn:EEq; [discriminate|].
  destruct (checksum h =? 0) eqn:Eck0; [discriminate|].
  simpl in EEq. apply negb_false_iff, N.eqb_eq in EEq.
  apply N.ltb_ge in EL8.
  pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
  rewrite Hw, lenN_app, lenN_udp_header_bytes_8 in EEq.
  assert (HL: length16 h = 8 + lenN rest) by lia.
  rewrite HL, N_add_sub_cancel_l, N_to_nat_lenN in Hdec.
  rewrite take_length_id in Hdec.
  destruct (verify_checksum_ipv6 src dst h rest) eqn:Ever; [|discriminate].
  split.
  - reflexivity.
  - apply N.eqb_neq in Eck0.
    pose proof (header_norm_of_parse_success _ _ _ Hparse) as Hnorm.
    apply (verify_implies_checksum_equals_computed_ipv6 _ _ _ _ Hnorm Ever Eck0).
Qed.

Lemma encode_ipv6_header_eq : forall src dst src_port0 dst_port0 length17 checksum0 rest,
  src_port0 < two16 ->
  dst_port0 < two16 ->
  length17 < two16 ->
  checksum0 < two16 ->
  length17 = 8 + lenN rest ->
  checksum0 = compute_udp_checksum_ipv6 src dst 
    {| src_port := src_port0; dst_port := dst_port0; length16 := length17; checksum := 0 |} rest ->
  {| src_port := to_word16 src_port0;
     dst_port := to_word16 dst_port0;
     length16 := to_word16 (8 + lenN rest);
     checksum := compute_udp_checksum_ipv6 src dst
                  {| src_port := to_word16 src_port0;
                     dst_port := to_word16 dst_port0;
                     length16 := to_word16 (8 + lenN rest);
                     checksum := 0 |} rest |}
  = {| src_port := src_port0;
       dst_port := dst_port0;
       length16 := length17;
       checksum := checksum0 |}.
Proof.
  intros src dst src_port0 dst_port0 length17 checksum0 rest 
         Hsp_lt Hdp_lt HL_lt Hck_lt HL Hck.
  assert (HLen_lt: 8 + lenN rest < two16) by (rewrite <- HL; assumption).
  f_equal.
  - rewrite to_word16_id_if_lt by assumption. reflexivity.
  - rewrite to_word16_id_if_lt by assumption. reflexivity.
  - rewrite to_word16_id_if_lt by assumption. symmetry. exact HL.
  - rewrite Hck. f_equal.
    unfold checksum_words_ipv6, udp_header_words_zero_ck. simpl.
    do 3 (rewrite to_word16_id_if_lt by assumption).
    rewrite HL. reflexivity.
Qed.

(** Completeness: successful decode implies encode produces the same wire *)
Theorem decode_encode_completeness_ipv6 :
  forall src dst w sp dp data,
    decode_udp_ipv6 src dst w = Ok (sp, dp, data) ->
    exists h rest,
      parse_header w = Some (h, rest) /\
      data = rest /\
      encode_udp_ipv6 src dst sp dp data = Ok w.
Proof.
  intros src dst w sp dp data Hdec.
  (* 1) Expose the parsed header from the successful decode *)
  destruct (decode_ipv6_parse_success src dst w sp dp data Hdec)
    as [h [rest Hparse]].
  exists h, rest. split; [assumption|].
  (* 2) From the decode path, recover data/rest and ports equality *)
  pose proof (decode_ipv6_data_eq_rest src dst w sp dp data h rest Hdec Hparse)
    as [Hdata [Hsp_eq Hdp_eq]].
  split; [assumption|].
  (* 3) Facts we will need: header norm, length equality, checksum equality *)
  pose proof (header_norm_of_parse_success w h rest Hparse) as Hnorm.
  pose proof (decode_ipv6_length_eq src dst w sp dp data h rest Hdec Hparse)
    as [Hlen_eq Hlen_form].
  pose proof (decode_ipv6_checksum_eq_computed src dst w sp dp data h rest Hdec Hparse)
    as [Hver Hckeq].
  (* 4) mk_header guard: 8 + |rest| ≤ 65535 *)
  destruct Hnorm as [Hsp_lt [Hdp_lt [HL_lt Hck_lt]]].
  assert (Hle : 8 + lenN rest <= mask16).
  { unfold mask16, two16 in *.
    assert (length16 h <= 65535) by lia.
    now rewrite Hlen_form in H. }
  (* 5) Evaluate the encoder and show it yields exactly w *)
  unfold encode_udp_ipv6.
  rewrite Hsp_eq, Hdp_eq, Hdata.
  unfold mk_header.
  assert (Hleb : (8 + lenN rest <=? mask16) = true) by (apply N.leb_le; exact Hle).
  rewrite Hleb.
  f_equal.
  (* 6) The encoder's header equals the parsed header *)
  destruct h as [sp0 dp0 len0 ck0]; simpl in *.
  assert (H_eq: {| src_port := to_word16 sp0;
                   dst_port := to_word16 dp0;
                   length16 := to_word16 (8 + lenN rest);
                   checksum := compute_udp_checksum_ipv6 src dst
                                {| src_port := to_word16 sp0;
                                   dst_port := to_word16 dp0;
                                   length16 := to_word16 (8 + lenN rest);
                                   checksum := 0 |} rest |}
                = {| src_port := sp0;
                     dst_port := dp0;
                     length16 := len0;
                     checksum := ck0 |}).
  { eapply encode_ipv6_header_eq; eauto. }
  change (udp_header_bytes
           {| src_port := to_word16 sp0;
              dst_port := to_word16 dp0;
              length16 := to_word16 (8 + lenN rest);
              checksum := compute_udp_checksum_ipv6 src dst
                           {| src_port := to_word16 sp0;
                              dst_port := to_word16 dp0;
                              length16 := to_word16 (8 + lenN rest);
                              checksum := 0 |} rest |} ++ rest = w).
  rewrite H_eq.
  symmetry. apply (parse_header_shape_bytes w _ rest Hparse).
Qed.

End UDP_IPv6.

(* =============================================================================
   Section 22: Permutation Invariance of Internet Checksum
   
   The Internet checksum algorithm's result is independent of the order in 
   which 16-bit words are summed. This section provides a formal proof of
   this critical property using Coq's Permutation library.
   ============================================================================= *)

From Coq Require Import Sorting.Permutation.

Section UDP_Permutation_Invariance.
  Open Scope N_scope.

(* ===== 22.1 Canonical Fold Form ===== *)

(* Canonical fold_left form for sum16, specialized from sum16_app *)
Lemma sum16_fold_left : forall ws,
  sum16 ws = fold_left add16_ones (map to_word16 ws) 0.
Proof.
  intro ws.
  replace (sum16 ws) with (sum16 ([] ++ ws)) by reflexivity.
  rewrite sum16_app. simpl. reflexivity.
Qed.

(* ===== 22.2 Accumulator Swap Properties ===== *)

(* Swapping two successive additions under the invariant s,x,y < 2^16 *)
Lemma add16_ones_swap_acc : forall s x y,
  s < two16 -> x < two16 -> y < two16 ->
  add16_ones (add16_ones s x) y =
  add16_ones (add16_ones s y) x.
Proof.
  intros s x y Hs Hx Hy.
  rewrite (add16_ones_assoc s x y Hs Hx Hy).
  rewrite (add16_ones_comm x y).
  rewrite <- (add16_ones_assoc s y x); auto.
Qed.

(* ===== 22.3 Forall Transport Along Permutations ===== *)

(* Transport Forall along permutations (helper for the accumulator invariant) *)
Lemma Forall_perm : forall (A:Type) (P:A->Prop) (l l':list A),
  Forall P l -> Permutation l l' -> Forall P l'.
Proof.
  intros A P l l' Hf Hperm.
  induction Hperm.
  - (* perm_nil *) exact Hf.
  - (* perm_skip *)
    inversion Hf as [| x0 l0 Hx0 Hf0]; subst.
    constructor; [assumption| now apply IHHperm].
  - (* perm_swap *)
    (* l = y :: x :: l0, l' = x :: y :: l0 *)
    inversion Hf as [| y0 l0 Hy Hf0]; subst.
    inversion Hf0 as [| x0 l1 Hx Hf1]; subst.
    constructor; [ exact Hx | constructor; [ exact Hy | exact Hf1 ] ].
  - (* perm_trans *)
    eapply IHHperm2. eapply IHHperm1. exact Hf.
Qed.

(* ===== 22.4 Fold Left Permutation Invariance ===== *)

(* fold_left invariance under permutation, given the < 2^16 invariant *)
Lemma fold_left_add16_perm_acc : forall l1 l2 s,
  s < two16 ->
  Forall (fun z => z < two16) l1 ->
  Permutation l1 l2 ->
  fold_left add16_ones l1 s = fold_left add16_ones l2 s.
Proof.
  intros l1 l2 s Hs Hfor Hperm.
  (* Make the accumulator and bound available to all IHs *)
  revert s Hs Hfor.
  induction Hperm
    as [ (* perm_nil *) 
       | a l1 l2 Hperm IH
       | a b l
       | l1 l2 l3 H12 IH12 H23 IH23
       ]; intros s Hs Hfor.
  - (* [] ~ [] *)
    reflexivity.
  - (* skip: a :: l1 ~ a :: l2 *)
    inversion Hfor as [| a' l' Ha Hfor']; subst.
    simpl.
    apply IH.
    + eapply add16_ones_bound; eauto.
    + exact Hfor'.
  - (* swap: a :: b :: l ~ b :: a :: l *)
    inversion Hfor as [| a' l0 Ha Hfor0]; subst.
    inversion Hfor0 as [| b' l1 Hb Hfor1]; subst.
    (* Reduce both sides to folding over the same tail [l] with different bases *)
    simpl. simpl.
    (* Now rewrite the base using the swap lemma on the accumulator *)
    rewrite (add16_ones_swap_acc s a b); try assumption.
    reflexivity.
  - (* transitivity *)
    transitivity (fold_left add16_ones l2 s).
    + apply IH12; assumption.
    + apply IH23; [assumption|].
      eapply Forall_perm; eauto.
Qed.

(* ===== 22.5 Word Bounds Helper ===== *)

(* All mapped words are strictly below 2^16 *)
Lemma Forall_lt_two16_map_to_word16 : forall ws, 
  Forall (fun x => x < two16) (map to_word16 ws).
Proof.
  intro ws. induction ws as [|w ws IH]; simpl; constructor; auto.
  apply to_word16_lt_two16.
Qed.

(* ===== 22.6 Main Permutation Invariance Theorem ===== *)

(* Main result: permutation invariance of the end-around sum *)
Theorem sum16_perm : forall ws ws',
  Permutation ws ws' ->
  sum16 ws = sum16 ws'.
Proof.
  intros ws ws' Hperm.
  rewrite !sum16_fold_left.
  eapply fold_left_add16_perm_acc
    with (l1 := map to_word16 ws) (l2 := map to_word16 ws') (s := 0).
  - apply two16_pos.
  - apply Forall_lt_two16_map_to_word16.
  - apply Permutation_map. exact Hperm.
Qed.

(* ===== 22.7 Checksum Permutation Invariance ===== *)

(* Immediate corollary for the one's-complement checksum *)
Corollary cksum16_perm : forall ws ws',
  Permutation ws ws' ->
  cksum16 ws = cksum16 ws'.
Proof.
  intros ws ws' Hperm.
  (* Temporarily expose the definition of cksum16 *)
  Transparent cksum16 complement16.
  change (mask16 - sum16 ws = mask16 - sum16 ws').
  now rewrite (sum16_perm ws ws' Hperm).
  Opaque cksum16 complement16.
Qed.

End UDP_Permutation_Invariance.

(* =============================================================================
   Section 23: Equivalence with Mod-and-Carry Checksum
   
   This section proves that the end-around carry addition used in Internet
   checksums is equivalent to the standard implementation approach of adding
   the carry bit back to the modulo-65536 result.
   ============================================================================= *)

Section UDP_ModCarry_Equivalence.
  Open Scope N_scope.

(* ===== 23.1 Arithmetic Helper ===== *)

(* Small arithmetic helper: (a - b) + b = a when b <= a *)
Lemma add_sub_cancel_N : forall a b, 
  b <= a -> (a - b) + b = a.
Proof. 
  intros; lia. 
Qed.

(* ===== 23.2 Main Mod-and-Carry Equivalence Theorem ===== *)

(** End-around addition equals (mod 2^16) + (carry), for inputs < 2^16.
    
    This theorem shows that our abstract add16_ones operation is equivalent
    to the standard implementation technique of:
    1. Computing the sum modulo 65536
    2. Adding the carry bit (sum / 65536)
    
    This equivalence is crucial for relating our formal specification to
    actual implementations in C or assembly language. *)
    
Lemma add16_ones_modcarry : forall x y,
  x < two16 -> y < two16 ->
  add16_ones x y = ((x + y) mod two16) + ((x + y) / two16).
Proof.
  intros x y Hx Hy.
  set (s := x + y).
  destruct (N.lt_ge_cases s two16) as [Hlt|Hge].
  - (* Case 1: No overflow (s < 2^16) *)
    rewrite (add16_ones_no_overflow x y Hlt).
    rewrite N.mod_small by exact Hlt.
    rewrite N.div_small by exact Hlt.
    rewrite N.add_0_r.
    unfold s; reflexivity.
    
  - (* Case 2: Overflow (2^16 <= s < 2*2^16) *)
    assert (Hge' : x + y >= two16) by (unfold s in Hge; lia).
    rewrite (add16_ones_overflow x y Hge').  (* LHS = s - mask16 *)
    set (r := s - two16).
    assert (Hr_lt : r < two16) by (unfold r; lia).
    assert (two16_ne : two16 <> 0) by (cbv [two16]; lia).
    assert (Hs_eq : s = two16 + r) by (unfold r; lia).
    
    (* Mod part: (s mod 2^16) = r *)
    replace (s mod two16) with ((r + 1 * two16) mod two16)
      by (rewrite Hs_eq, N.add_comm, N.mul_1_l; reflexivity).
    rewrite (N.mod_add r 1 two16) by exact two16_ne.
    rewrite N.mod_small by exact Hr_lt.
    
    (* Div part: (s / 2^16) = 1 *)
    replace (s / two16) with ((r + 1 * two16) / two16)
      by (rewrite Hs_eq, N.add_comm, N.mul_1_l; reflexivity).
    replace ((r + 1 * two16) / two16) with ((1 * two16 + r) / two16)
      by (f_equal; apply N.add_comm).
    rewrite N.div_add_l by exact two16_ne.
    rewrite N.div_small by exact Hr_lt.
    rewrite N.add_0_r.  (* 1 + 0 -> 1 *)
    
    (* Finalize: s = 2^16 + r, mask16 = 2^16 - 1 *)
    unfold s.
    assert (x + y = two16 + r) by (unfold s in Hs_eq; exact Hs_eq).
    rewrite H.
    cbv [mask16 two16]; lia.
Qed.

End UDP_ModCarry_Equivalence.

(* =============================================================================
   Section 24: Serialization Round-Trip Extras
   
   Helper lemmas for serialization that are robust to Opaque declarations
   on be16_of_word16. These lemmas establish key properties about byte/word
   conversions and their length relationships.
   ============================================================================= *)

Section UDP_Serialization_Extras.
  Import ListNotations.

(* ===== 24.1 Byte Canonicalization ===== *)

(* Canonicalization for bytes: if < 256, mod 256 is identity *)
Lemma to_byte_id_if_lt : forall x, 
  x < two8 -> to_byte x = x.
Proof. 
  intros x Hx; unfold to_byte; now apply N.mod_small. 
Qed.

(* ===== 24.2 Length of Words from Bytes ===== *)

(* Length relationship: converting bytes to 16-bit words halves the count (rounded up) *)
Lemma lenN_words16_of_bytes_be : forall bs, 
  lenN (words16_of_bytes_be bs) = (lenN bs + 1) / 2.
Proof.
  fix IH 1.
  intro bs.
  destruct bs as [|b1 bs'].
  - (* Empty *)
    cbn. cbv [lenN]. reflexivity.
  - destruct bs' as [|b2 tl].
    + (* Single [b1] *)
      cbn. cbv [lenN]. simpl. reflexivity. 
    + (* b1::b2::tl *)
      cbn [words16_of_bytes_be].
      rewrite lenN_cons.
      rewrite IH.
      rewrite !lenN_cons.
      (* Goal: 1 + (lenN tl + 1) / 2 = (1 + (1 + lenN tl) + 1) / 2 *)
      replace (1 + (1 + lenN tl) + 1) with (lenN tl + 3) by lia.
      replace (lenN tl + 3) with ((lenN tl + 1) + 1 * 2) by lia.
      rewrite N.div_add by (cbv; discriminate).
      lia.
Qed.

(* ===== 24.3 Length of Bytes from Words ===== *)

(* The general "bytes length is 2× words length" helper *)
Lemma lenN_bytes_of_words16_be : forall ws, 
  lenN (bytes_of_words16_be ws) = 2 * lenN ws.
Proof.
  induction ws as [|w tl IH].
  - simpl. reflexivity.
  - change (lenN (bytes_of_words16_be (w :: tl)) = 2 * lenN (w :: tl)).
    simpl bytes_of_words16_be.
    destruct (be16_of_word16 (to_word16 w)) as [hi lo].
    change (lenN (hi :: lo :: bytes_of_words16_be tl) = 2 * lenN (w :: tl)).
    rewrite !lenN_cons.
    rewrite IH.
    lia.
Qed.

End UDP_Serialization_Extras.

(* =============================================================================
   Section 25: Full Pipeline Implementation - ARPANET Example
   
   This section provides a complete worked example of UDP packet construction
   and verification using the historic ARPANET "LO" message - the first 
   message ever sent over the Internet's predecessor on October 29, 1969.
   
   The implementation demonstrates:
   - Step-by-step packet construction
   - Checksum computation with all intermediate values
   - Complete verification that our formal specification matches reality
   ============================================================================= *)

Section UDP_Full_Pipeline_Implementation.
  Open Scope N_scope.

(* ===== 25.1 Historic ARPANET Configuration ===== *)

(* Historic ARPANET message "LO" *)
Definition msg_L : byte := 76.  (* ASCII 'L' *)
Definition msg_O : byte := 79.  (* ASCII 'O' *)
Definition arpanet_payload := [msg_L; msg_O].

(* UCLA (10.0.0.1) to SRI (10.0.0.2) *)
Definition ucla_ip := mkIPv4 10 0 0 1.
Definition sri_ip := mkIPv4 10 0 0 2.

(* Year of ARPANET: 1969 *)
Definition arpanet_sp : word16 := 1969.

(* Telnet port: 23 *)
Definition telnet_dp : word16 := 23.

(* ===== 25.2 Step-by-Step Packet Construction ===== *)

(* Step 1: Build the header with zero checksum *)
Definition header_zero_ck := {|
  src_port := arpanet_sp;
  dst_port := telnet_dp;
  length16 := 10;  (* 8 header + 2 payload *)
  checksum := 0
|}.

(* Step 2: Build the pseudo-header for checksum computation *)
Definition pseudo := pseudo_header_v4 ucla_ip sri_ip 10.

(* Step 3: Checksum material = pseudo + header + data as 16-bit words *)
Definition checksum_material := 
  pseudo ++ udp_header_words_zero_ck header_zero_ck ++ words16_of_bytes_be arpanet_payload.

(* Step 4: Actually compute the checksum *)
Definition computed_checksum := cksum16 checksum_material.

(* Step 5: Apply the 0x0000 -> 0xFFFF rule *)
Definition final_checksum := 
  if N.eqb computed_checksum 0 then mask16 else computed_checksum.

(* Step 6: Build the final header with checksum *)
Definition final_header := {|
  src_port := arpanet_sp;
  dst_port := telnet_dp;
  length16 := 10;
  checksum := final_checksum
|}.

(* Step 7: Serialize to bytes *)
Definition packet_bytes := udp_header_bytes final_header ++ arpanet_payload.

(* ===== 25.3 Complete Pipeline Correctness Theorem ===== *)

(* Now prove this entire pipeline is correct *)
Theorem Full_Pipeline_Correctness :
  (* Our manually constructed packet *)
  let manual_packet := packet_bytes in
  
  (* The encoder's packet *)
  exists encoder_packet,
    (* 1. The encoder produces the same packet *)
    encode_udp_ipv4 defaults_ipv4 ucla_ip sri_ip arpanet_sp telnet_dp arpanet_payload = Ok encoder_packet /\
    encoder_packet = manual_packet /\
    
    (* 2. The packet has exactly 10 bytes *)
    lenN manual_packet = 10 /\
    
    (* 3. The checksum is non-zero *)
    final_checksum <> 0 /\
    
    (* 4. The packet decodes correctly *)
    decode_udp_ipv4 defaults_ipv4 ucla_ip sri_ip manual_packet = 
      Ok (arpanet_sp, telnet_dp, arpanet_payload) /\
    
    (* 5. The exact byte layout is: *)
    (* [0x07, 0xB1,  -- source port 1969 (0x07B1) big-endian
        0x00, 0x17,  -- dest port 23 (0x0017) big-endian  
        0x00, 0x0A,  -- length 10 (0x000A) big-endian
        ck_hi, ck_lo, -- checksum big-endian
        0x4C, 0x4F]  -- 'L', 'O' *) 
    (exists ck_hi ck_lo,
      manual_packet = [
        7; 177;      (* 1969 = 0x07B1 *)
        0; 23;       (* 23 = 0x0017 *)
        0; 10;       (* 10 = 0x000A *)
        ck_hi; ck_lo;
        76; 79       (* 'L', 'O' *)
      ] /\
      word16_of_be ck_hi ck_lo = final_checksum) /\
    
    (* 6. Verify checksum computation step by step *)
    checksum_material = [
      (* Pseudo-header *)
      10 * 256 + 0;    (* src IP high *)
      0 * 256 + 1;     (* src IP low *)
      10 * 256 + 0;    (* dst IP high *)
      0 * 256 + 2;     (* dst IP low *)
      17;              (* word16_of_be 0 17 = 0*256 + 17 = 17 *)
      10;              (* length *)
      (* UDP header with zero checksum *)
      1969;            (* src port *)
      23;              (* dst port *)
      10;              (* length again *)
      0;               (* zero checksum *)
      (* Payload as 16-bit words *)
      76 * 256 + 79    (* 'LO' *)
    ] /\
    
    (* 7. The actual checksum value can be computed *)
    final_checksum = compute_udp_checksum_ipv4 ucla_ip sri_ip header_zero_ck arpanet_payload.

Proof.
  simpl.
  
  (* First establish the encoder produces a packet *)
  assert (Hmk: mk_header arpanet_sp telnet_dp (lenN arpanet_payload) = Some header_zero_ck).
  { unfold mk_header, arpanet_sp, telnet_dp, arpanet_payload. simpl. reflexivity. }
  
  assert (Henc_exists: exists w, encode_udp_ipv4 defaults_ipv4 ucla_ip sri_ip arpanet_sp telnet_dp arpanet_payload = Ok w).
  { unfold encode_udp_ipv4. rewrite Hmk. simpl. eexists. reflexivity. }
  destruct Henc_exists as [encoder_packet Henc].
  
  exists encoder_packet.
  
  split.
  - (* Encoder produces packet *) exact Henc.
  - (* Rest of the goals *)
    split.
    + (* Packets are equal *)
      unfold encode_udp_ipv4 in Henc.
      rewrite Hmk in Henc.
      simpl in Henc.
      inversion Henc; subst encoder_packet; clear Henc.
      reflexivity.
    
    + split.
      * (* Length is 10 *)
        unfold packet_bytes.
        rewrite lenN_app, lenN_udp_header_bytes_8.
        unfold arpanet_payload. simpl. reflexivity.
      
      * split.
        -- (* Checksum non-zero *)
           unfold final_checksum.
           destruct (computed_checksum =? 0) eqn:E.
           ++ unfold mask16. discriminate.
           ++ apply N.eqb_neq in E. exact E.
        
        -- split.
           ++ (* Decodes correctly *)
              assert (Hdec_eq: decode_udp_ipv4 defaults_ipv4 ucla_ip sri_ip packet_bytes = 
                               Ok (to_word16 arpanet_sp, to_word16 telnet_dp, arpanet_payload)).
              { apply decode_encode_roundtrip_ipv4_defaults_reject_nonzero16 with header_zero_ck.
                - unfold telnet_dp. intro H. vm_compute in H. discriminate.
                - exact Hmk.
                - unfold encode_udp_ipv4. rewrite Hmk. simpl. reflexivity. }
              assert (arpanet_sp < two16) by (unfold arpanet_sp; vm_compute; constructor).
              assert (telnet_dp < two16) by (unfold telnet_dp; vm_compute; constructor).
              rewrite to_word16_id_if_lt in Hdec_eq by assumption.
              rewrite to_word16_id_if_lt in Hdec_eq by assumption.
              exact Hdec_eq.
           
           ++ split.
              ** (* Exact byte layout *)
                 unfold packet_bytes, final_header, udp_header_bytes.
                 simpl.
                 destruct (be16_of_word16 (to_word16 arpanet_sp)) as [sp_hi sp_lo] eqn:Esp.
                 destruct (be16_of_word16 (to_word16 telnet_dp)) as [dp_hi dp_lo] eqn:Edp.
                 destruct (be16_of_word16 (to_word16 10)) as [l_hi l_lo] eqn:El.
                 destruct (be16_of_word16 (to_word16 final_checksum)) as [ck_hi ck_lo] eqn:Eck.
                 
                 (* Compute byte values for source port *)
                 assert (Esp_calc: sp_hi = 7 /\ sp_lo = 177).
                 { assert (H3: to_word16 arpanet_sp = arpanet_sp).
                   { apply to_word16_id_if_lt. unfold arpanet_sp. vm_compute. constructor. }
                   rewrite H3 in Esp.
                   unfold arpanet_sp in Esp.
                   assert (H1: be16_of_word16 1969 = (7, 177)) by (vm_compute; reflexivity).
                   rewrite H1 in Esp.
                   injection Esp as -> ->. split; reflexivity. }
                 
                 (* Compute byte values for dest port *)
                 assert (Edp_calc: dp_hi = 0 /\ dp_lo = 23).
                 { assert (H2: to_word16 telnet_dp = telnet_dp).
                   { apply to_word16_id_if_lt. unfold telnet_dp. vm_compute. constructor. }
                   rewrite H2 in Edp.
                   unfold telnet_dp in Edp.
                   assert (H3: be16_of_word16 23 = (0, 23)) by (vm_compute; reflexivity).
                   rewrite H3 in Edp.
                   injection Edp as -> ->. split; reflexivity. }
                 
                 (* Compute byte values for length *)
                 assert (El_calc: l_hi = 0 /\ l_lo = 10).
                 { assert (H2: to_word16 10 = 10) by (vm_compute; reflexivity).
                   rewrite H2 in El.
                   assert (H1: be16_of_word16 10 = (0, 10)) by (vm_compute; reflexivity).
                   rewrite H1 in El.
                   injection El as -> ->. split; reflexivity. }
                 
                 (* Destruct the calc results *)
                 destruct Esp_calc as [Hsp_hi Hsp_lo].
                 destruct Edp_calc as [Hdp_hi Hdp_lo].
                 destruct El_calc as [Hl_hi Hl_lo].
                 
                 exists ck_hi, ck_lo.
                 split.
--- (* Show the exact byte layout *)
                     unfold udp_header_bytes, udp_header_words.
                     
                     (* Temporarily make bytes_of_words16_be transparent *)
                     Transparent bytes_of_words16_be.
                     simpl bytes_of_words16_be.
                     
                     (* Now the computation should expose the be16_of_word16 calls *)
                     simpl.
                     
                     (* Directly compute all the byte values *)
                     assert (H1: (to_word16 arpanet_sp / two8) mod two8 = 7).
                     { unfold arpanet_sp, to_word16, two8. vm_compute. reflexivity. }
                     assert (H2: to_word16 arpanet_sp mod two8 = 177).
                     { unfold arpanet_sp, to_word16, two8. vm_compute. reflexivity. }
                     assert (H3: (to_word16 telnet_dp / two8) mod two8 = 0).
                     { unfold telnet_dp, to_word16, two8. vm_compute. reflexivity. }
                     assert (H4: to_word16 telnet_dp mod two8 = 23).
                     { unfold telnet_dp, to_word16, two8. vm_compute. reflexivity. }
                     assert (H5: (to_word16 10 / two8) mod two8 = 0).
                     { unfold to_word16, two8. vm_compute. reflexivity. }
                     assert (H6: to_word16 10 mod two8 = 10).
                     { unfold to_word16, two8. vm_compute. reflexivity. }
                     
                     rewrite H1, H2, H3, H4, H5, H6.
                     
                     (* For the checksum bytes, use the fact that be16_of_word16 splits them *)
                     assert (Hck_hi: ck_hi = (to_word16 final_checksum / two8) mod two8).
                     { unfold be16_of_word16 in Eck. 
                       injection Eck as <- _. reflexivity. }
                     assert (Hck_lo: ck_lo = to_word16 final_checksum mod two8).
                     { unfold be16_of_word16 in Eck. 
                       injection Eck as _ <-. reflexivity. }
                     
                     rewrite <- Hck_hi, <- Hck_lo.
                     
                     unfold arpanet_payload, msg_L, msg_O.
                     reflexivity.
                     
                     (* Make it opaque again if needed *)
                     Opaque bytes_of_words16_be.
                 
                 --- (* Checksum bytes match *)
                     assert (Hfinal_lt: final_checksum < two16).
                     { unfold final_checksum.
                       destruct (computed_checksum =? 0).
                       - unfold mask16, two16. compute. constructor.
                       - apply cksum16_lt_two16. }
                     
                     pose proof (word16_of_be_be16 (to_word16 final_checksum) (to_word16_lt_two16 final_checksum)) as H.
                     rewrite Eck in H.
                     simpl in H.
                     rewrite H.
                     
                     rewrite to_word16_id_if_lt by exact Hfinal_lt.
                     reflexivity.
              
              ** split.
                 --- (* Checksum material breakdown *)
                     unfold checksum_material, pseudo.
                     Transparent pseudo_header_v4 ipv4_words words16_of_bytes_be word16_of_be.
                     unfold pseudo_header_v4.
                     unfold udp_header_words_zero_ck, header_zero_ck.
                     unfold ipv4_words.
                     unfold ucla_ip, sri_ip, arpanet_sp, telnet_dp.
                     simpl.
                     unfold words16_of_bytes_be, arpanet_payload, msg_L, msg_O.
                     simpl.
                     unfold word16_of_be, udp_protocol_number.
                     compute.
                     reflexivity.
                     Opaque pseudo_header_v4 ipv4_words words16_of_bytes_be word16_of_be.
                 
                 --- (* Final checksum equals compute function *)
                     reflexivity.
Qed.

(* ===== 25.4 Compute Final Checksum Value ===== *)

(* Compute the actual checksum value for the ARPANET example *)
Compute final_checksum.
(* Result: 38848 = 0x97C0 *)

End UDP_Full_Pipeline_Implementation.

(* =============================================================================
   Section 26: Hardened Security Implementations
   
   This section provides security-hardened decoder variants that address
   common attack vectors and implementation vulnerabilities:
   - Payload byte normalization to prevent out-of-range values
   - Stricter zero-checksum policies for broadcast/multicast
   - Strict length validation to reject malformed packets
   - Configurable broadcast detection
   ============================================================================= *)

(* ===== 26.1 Payload Normalization ===== *)

(* Normalize a list of bytes by truncating each element modulo 256 *)
Definition normalize_bytes (xs : list byte) : list byte :=
  List.map to_byte xs.

(* Convenience lemma: normalized bytes are always in range *)
Lemma normalize_bytes_are_bytes : forall xs, 
  Forall (fun b => is_byte b = true) (normalize_bytes xs).
Proof.
  intros xs; induction xs as [|a xs IH]; simpl; constructor.
  - unfold to_byte. apply is_byte_true_of_mod.
  - exact IH.
Qed.

(* ===== 26.2 Hardened IPv4 Configurations ===== *)

(* A hardened IPv4 configuration with stricter receive-side policies *)
Definition ipv4_hardened_default : Config :=
  {| checksum_tx_mode     := WithChecksum;
     checksum_rx_mode     := ValidOrZero;
     zero_checksum_policy := ZeroForbidOnMultiOrBcast;  (* forbid on multicast/broadcast *)
     length_rx_mode       := StrictEq;                  (* enforce Nbytes = L *)
     dst_port0_policy     := Reject;                    (* reject dp = 0 *)
     is_broadcast         := fun _ => false |}.         (* supply your own if available *)

(* Variant allowing a host-specific broadcast predicate *)
Definition ipv4_hardened_with (is_bcast : IPv4 -> bool) : Config :=
  {| checksum_tx_mode     := WithChecksum;
     checksum_rx_mode     := ValidOrZero;
     zero_checksum_policy := ZeroForbidOnMultiOrBcast;
     length_rx_mode       := StrictEq;
     dst_port0_policy     := Reject;
     is_broadcast         := is_bcast |}.

(* ===== 26.3 Hardened Decoder Wrappers ===== *)

(* IPv4: hardened decoder that also normalizes the delivered payload bytes *)
Definition decode_udp_ipv4_hardened
  (src_ip dst_ip : IPv4) (wire : list byte)
  : result Decoded DecodeError :=
  match decode_udp_ipv4 ipv4_hardened_default src_ip dst_ip wire with
  | inl (sp, dp, data) => Ok (sp, dp, normalize_bytes data)
  | inr e => Err e
  end.

(* IPv4: address-carrying hardened decoder with normalized payload *)
Definition decode_udp_ipv4_with_addrs_hardened
  (src_ip dst_ip : IPv4) (wire : list byte)
  : result UdpDeliver DecodeError :=
  match decode_udp_ipv4 ipv4_hardened_default src_ip dst_ip wire with
  | inl (sp, dp, data) =>
      Ok {| src_ip_out   := src_ip
          ; dst_ip_out   := dst_ip
          ; src_port_out := sp
          ; dst_port_out := dp
          ; payload_out  := normalize_bytes data |}
  | inr e => Err e
  end.

(* IPv6: decoder wrapper that normalizes the delivered payload bytes *)
Definition decode_udp_ipv6_hardened
  (src_ip dst_ip : IPv6) (wire : list byte)
  : result Decoded DecodeError :=
  match decode_udp_ipv6 src_ip dst_ip wire with
  | inl (sp, dp, data) => Ok (sp, dp, normalize_bytes data)
  | inr e => Err e
  end.

(* ===== 26.4 Security Hardening Examples ===== *)

Section UDP_Hardened_Examples.
  Open Scope N_scope.

  (* A tiny payload "HI" *)
  Definition msg_H : byte := 72.  (* 'H' *)
  Definition msg_I : byte := 73.  (* 'I' *)
  Definition payload_HI := [msg_H; msg_I].

  (* Hosts *)
  Definition srcA := mkIPv4 10 0 0 100.
  Definition dstB := mkIPv4 10 0 0 200.

  (* Ports *)
  Definition p_src : word16 := 1969.
  Definition p_dst : word16 := 23.

  (* ================================================================
     Example 1: Zero-checksum to broadcast is rejected
     ================================================================ *)

  (* Treat 10.0.0.255 as a broadcast address *)
  Definition dstB_broadcast := mkIPv4 10 0 0 255.

  Definition is_bcast_10_0_0_255 (ip : IPv4) : bool :=
    match ip with
    | Build_IPv4 a b c d =>
        N.eqb a 10 && N.eqb b 0 && N.eqb c 0 && N.eqb d 255
    end.

  Definition cfg_hardened_bcast := ipv4_hardened_with is_bcast_10_0_0_255.

  (* Build a UDP header that claims length 10 and has a zero checksum *)
  Definition hdr_zero_ck_bcast : UdpHeader :=
    {| src_port := p_src; dst_port := p_dst; length16 := 10; checksum := 0 |}.

  (* Wire = header (with checksum=0) ++ payload (2 bytes) *)
  Definition wire_zero_ck_bcast : list byte :=
    udp_header_bytes hdr_zero_ck_bcast ++ payload_HI.

  (* Under hardened policy with broadcast detection, this must be an error *)
  Example Hardened_rejects_zero_ck_on_broadcast :
    exists e, decode_udp_ipv4 cfg_hardened_bcast srcA dstB_broadcast wire_zero_ck_bcast = Err e.
  Proof. eexists; vm_compute; reflexivity. Qed.

  (* For comparison: with the default "no broadcast knowledge" hardened config,
     the same zero checksum would be allowed (because zero is allowed
     for unicast and is_broadcast = (fun _ => false)) *)
  Example Hardened_default_allows_zero_ck_for_unicast :
    decode_udp_ipv4 ipv4_hardened_default srcA dstB wire_zero_ck_bcast
    = Ok (to_word16 p_src, to_word16 p_dst, payload_HI).
  Proof. vm_compute; reflexivity. Qed.

  (* ================================================================
     Example 2: Payload bytes are normalized (mod 256)
     ================================================================ *)

  (* Compute a correct non-zero checksum for payload_HI *)
  Definition hdr_zero_ck_norm : UdpHeader :=
    {| src_port := p_src; dst_port := p_dst; length16 := 10; checksum := 0 |}.

  Definition pseudo_norm := pseudo_header_v4 srcA dstB 10.
  Definition checksum_material_norm :=
    pseudo_norm ++ udp_header_words_zero_ck hdr_zero_ck_norm ++ words16_of_bytes_be payload_HI.
  Definition computed_checksum_norm := cksum16 checksum_material_norm.
  Definition final_checksum_norm :=
    if N.eqb computed_checksum_norm 0 then mask16 else computed_checksum_norm.

  Definition hdr_final_norm : UdpHeader :=
    {| src_port := p_src; dst_port := p_dst; length16 := 10; checksum := final_checksum_norm |}.

  (* "Good" wire produced for payload_HI *)
  Definition wire_good_norm : list byte :=
    udp_header_bytes hdr_final_norm ++ payload_HI.

  (* Attack variant: same header, but payload bytes outside [0,255].
     Because UDP checksum math uses modulo-256 bytes internally, the
     checksum still validates on decode — but a hardened wrapper
     will normalize the delivered payload back into [0,255] *)
  Definition payload_out_of_range := [msg_H + 256; msg_I + 256].  (* 328, 329 *)
  Definition wire_bad_norm : list byte :=
    udp_header_bytes hdr_final_norm ++ payload_out_of_range.

  (* Baseline decoder (no normalization): returns out-of-range bytes as-is *)
  Example Baseline_decoder_leaks_out_of_range_bytes :
    decode_udp_ipv4 ipv4_hardened_default srcA dstB wire_bad_norm
    = Ok (to_word16 p_src, to_word16 p_dst, payload_out_of_range).
  Proof. vm_compute; reflexivity. Qed.

  (* Hardened wrapper: normalizes payload bytes (mod 256) *)
  Example Hardened_decoder_normalizes_payload_bytes :
    decode_udp_ipv4_hardened srcA dstB wire_bad_norm
    = Ok (to_word16 p_src, to_word16 p_dst, [msg_H; msg_I]).
  Proof. vm_compute; reflexivity. Qed.

  (* ================================================================
     Example 3: Strict length equality rejects overlong IP data
     ================================================================ *)

  (* Overlong IP payload: header says length=10, but 11 bytes provided *)
  Definition wire_overlong : list byte := wire_good_norm ++ [0].

  (* Hardened (StrictEq) must reject *)
  Example Hardened_rejects_overlong_payload :
    exists e, decode_udp_ipv4 ipv4_hardened_default srcA dstB wire_overlong = Err e.
  Proof. eexists; vm_compute; reflexivity. Qed.

  (* If you keep or expose a permissive config with AcceptShorter semantics,
     the same overlong wire should succeed and deliver only the first (L-8)
     bytes of payload. If your file defines [defaults_ipv4_acceptShorter],
     you can uncomment the following to see the contrast:

     Example Permissive_accepts_overlong_and_truncates :
       decode_udp_ipv4 defaults_ipv4_acceptShorter srcA dstB wire_overlong
       = Ok (to_word16 p_src, to_word16 p_dst, payload_HI).
     Proof. vm_compute; reflexivity. Qed.
   *)

End UDP_Hardened_Examples.

(** ****************************************************************************
    
    RFC 768 UDP/IPv4/IPv6 Formal Verification in Coq
    =================================================
    
    This formalization provides a comprehensive, machine-checked 
    verification of the User Datagram Protocol (UDP) as specified in RFC 768,
    with full IPv6 support (RFC 8200) and extensions from RFC 1122/1812 for 
    ICMP error handling.
    
    ## Future Work
    
    ### 1. Extraction and Testing
    - OCaml extraction for executable verified code
    - QuickChick property-based testing framework
    - Performance benchmarks against standard implementations
    
    ### 2. Extended Protocols
    - UDP-Lite (RFC 3828) with partial checksums
    - DTLS integration for secure UDP
    - Path MTU discovery integration
    - Jumbogram support for IPv6 payloads > 65535 bytes
    
    ### 3. Formal Network Stack
    - Integration with verified IP layer
    - Composition with verified Ethernet
    - Full verified socket API
    - ICMPv6 error handling
    
    ## Usage
    
    The implementation provides both encoding and decoding functions that can
    be extracted to OCaml for use in real systems:
    
    - encode_udp_ipv4: Produces RFC-compliant UDP/IPv4 datagrams
    - decode_udp_ipv4: Parses and validates incoming IPv4 datagrams
    - encode_udp_ipv6: Produces RFC-compliant UDP/IPv6 datagrams  
    - decode_udp_ipv6: Parses and validates incoming IPv6 datagrams
    - Configurable policies via the Config record
    
    **************************************************************************** *)

