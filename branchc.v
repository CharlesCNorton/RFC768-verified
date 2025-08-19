(*
  =============================================================================
  RFC 768 — User Datagram Protocol (UDP, 1980)
  UDP over IPv4 – Formalization
  =============================================================================
*)

From Coq Require Import
  List
  NArith.NArith
  Lia
  Bool
  Arith.
  
Require Import Coq.Init.Prelude.

Import ListNotations.
Open Scope N_scope.

(* ----------------------------------------------------------------------------
   0) Basic numeric types, constants, and helpers
   --------------------------------------------------------------------------*)

Definition byte   := N.  (* 0..255; normalized where constructed/used *)
Definition word16 := N.  (* 0..65535 *)

Definition two8   : N := 256.
Definition two16  : N := 65536.
Definition mask16 : N := two16 - 1.  (* 65535 *)

Lemma two8_pos  : 0 < two8.  Proof. unfold two8; lia. Qed.
Lemma two16_pos : 0 < two16. Proof. unfold two16; lia. Qed.

(* Canonical truncations *)
Definition to_byte   (x:N) : byte   := x mod two8.
Definition to_word16 (x:N) : word16 := x mod two16.

Lemma to_word16_lt_two16 : forall x, to_word16 x < two16.
Proof. intro x. unfold to_word16. apply N.mod_lt. unfold two16. lia. Qed.

Lemma to_word16_id_if_lt : forall x, x < two16 -> to_word16 x = x.
Proof. intros x Hx. unfold to_word16. apply N.mod_small. exact Hx. Qed.

Lemma to_word16_id_if_le_mask :
  forall x, x <= mask16 -> to_word16 x = x.
Proof.
  intros x Hx. 
  apply to_word16_id_if_lt. 
  unfold mask16 in Hx.
  assert (two16 = 65536) by reflexivity.
  rewrite H. 
  lia.
Qed.

(* List length in N *)
Definition lenN {A} (xs:list A) : N := N.of_nat (List.length xs).
Lemma lenN_app : forall (A:Type) (xs ys:list A), lenN (xs ++ ys) = lenN xs + lenN ys.
Proof. intros A xs ys. unfold lenN. rewrite List.length_app, Nat2N.inj_add. reflexivity. Qed.
Lemma lenN_cons : forall (A:Type) (x:A) xs, lenN (x::xs) = 1 + lenN xs.
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

Lemma N_to_nat_lenN : forall (A:Type) (xs:list A), N.to_nat (lenN xs) = List.length xs.
Proof. intros; unfold lenN; apply Nat2N.id. Qed.

(* take/drop (on nat) *)
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

Lemma take_length_id : forall (A:Type) (xs:list A), take (List.length xs) xs = xs.
Proof. intros A xs; induction xs; simpl; congruence. Qed.

(* ----------------------------------------------------------------------------
   0') Byte-range predicate (for well-formed wire input)
   --------------------------------------------------------------------------*)

(* Predicate/boolean for "well-formed byte" (0..255). *)
Definition is_byte (b:byte) : bool := b <? two8.

Lemma is_byte_true_of_mod : forall x, is_byte (x mod two8) = true.
Proof.
  intros x. unfold is_byte. apply N.ltb_lt. apply N.mod_lt. 
  apply N.neq_0_lt_0. unfold two8. lia.
Qed.

(* ----------------------------------------------------------------------------
   1) Big-endian 16-bit serialization (arithmetic-only)
   --------------------------------------------------------------------------*)

(* Split a 16-bit word into two bytes (hi, lo) in big-endian order. *)
Definition be16_of_word16 (w:word16) : byte * byte :=
  ( (w / two8) mod two8
  ,  w mod two8).

(* Recompose two bytes (hi, lo) into a 16-bit word. *)
Definition word16_of_be (hi lo: byte) : word16 :=
  hi * two8 + lo.

Lemma div256_lt256 :
  forall w, w < two16 -> (w / two8) < two8.
Proof.
  intros w Hw. 
  unfold two8, two16 in *.
  assert (w <= 65535) by lia.
  assert (w / 256 <= 65535 / 256) by (apply N.div_le_mono; lia).
  assert (65535 / 256 = 255) by reflexivity.
  rewrite H1 in H0.
  lia.
Qed.

Lemma word16_of_be_be16 :
  forall w, w < two16 ->
    let '(hi,lo) := be16_of_word16 w in word16_of_be hi lo = w.
Proof.
  intros w Hw. unfold be16_of_word16, word16_of_be.
  rewrite (N.mod_small (w / two8) two8).
  2:{ apply div256_lt256; exact Hw. }
  assert (two8 <> 0) by (unfold two8; lia).
  rewrite N.mul_comm.
  rewrite <- N.div_mod; [reflexivity | exact H].
Qed.

(* Each byte produced by be16_of_word16 (after to_word16) is in range. *)
Lemma be16_of_word16_bytes_are_bytes_true :
  forall w, let '(hi,lo) := be16_of_word16 (to_word16 w) in
            is_byte hi = true /\ is_byte lo = true.
Proof.
  intros w. unfold be16_of_word16, is_byte.
  simpl. split; apply N.ltb_lt; apply N.mod_lt; 
  apply N.neq_0_lt_0; unfold two8; lia.
Qed.

(* Flatten list of 16-bit words into bytes *)
Fixpoint bytes_of_words16_be (ws:list word16) : list byte :=
  match ws with
  | [] => []
  | w::tl =>
      let '(hi,lo) := be16_of_word16 (to_word16 w) in
      hi :: lo :: bytes_of_words16_be tl
  end.

(* Pair bytes into 16-bit words, padding a trailing odd byte with 0x00
   for checksum computations (UDP/IPv4 odd-length rule). *)
Fixpoint words16_of_bytes_be (bs:list byte) : list word16 :=
  match bs with
  | [] => []
  | [b] => [ word16_of_be b 0 ]  (* odd length: pad one zero byte *)
  | b1::b2::tl => word16_of_be b1 b2 :: words16_of_bytes_be tl
  end.

Lemma lenN_bytes_of_words16_be_4 :
  forall a b c d,
    lenN (bytes_of_words16_be [a;b;c;d]) = 8%N.
Proof.
  intros. simpl.
  repeat (destruct (be16_of_word16 (to_word16 _)) as [x y]).
  reflexivity.
Qed.

(* ----------------------------------------------------------------------------
   2) IPv4 addresses and pseudo-header for UDP checksum
   --------------------------------------------------------------------------*)

Record IPv4 := { a0: byte; a1: byte; a2: byte; a3: byte }.

(* Normalize each octet via to_byte. *)
Definition mkIPv4 (x0 x1 x2 x3:byte) : IPv4 :=
  {| a0 := to_byte x0; a1 := to_byte x1; a2 := to_byte x2; a3 := to_byte x3 |}.

Definition normalizeIPv4 (ip:IPv4) : IPv4 :=
  mkIPv4 ip.(a0) ip.(a1) ip.(a2) ip.(a3).

Lemma to_byte_idempotent : forall x, to_byte (to_byte x) = to_byte x.
Proof.
  intro x. unfold to_byte.
  rewrite N.mod_mod.
  - reflexivity.
  - unfold two8. lia.
Qed.

Lemma normalizeIPv4_idempotent :
  forall ip, normalizeIPv4 (normalizeIPv4 ip) = normalizeIPv4 ip.
Proof. 
  intros [x0 x1 x2 x3].
  unfold normalizeIPv4, mkIPv4. simpl.
  f_equal; apply to_byte_idempotent.
Qed.

(* Two 16-bit words for a 32-bit IPv4 address, big-endian *)
Definition ipv4_words (ip:IPv4) : list word16 :=
  [ word16_of_be ip.(a0) ip.(a1)
  ; word16_of_be ip.(a2) ip.(a3) ].

Definition udp_protocol_number : byte := 17%N.

(* IPv4 pseudo-header fields for UDP checksum *)
Definition pseudo_header_v4 (src dst:IPv4) (udp_len:word16) : list word16 :=
  ipv4_words src ++
  ipv4_words dst ++
  [ word16_of_be 0 udp_protocol_number
  ; udp_len ].

(* Basic multicast predicate for IPv4: 224.0.0.0/4 *)
Definition is_multicast_ipv4 (ip:IPv4) : bool :=
  (224 <=? ip.(a0)) && (ip.(a0) <=? 239).

(* ----------------------------------------------------------------------------
   3) One's-complement 16-bit checksum (end-around carry)
   --------------------------------------------------------------------------*)

(* One step of end-around addition on two 16-bit words. Invariant: acc,w < 2^16. *)
Definition add16_ones (acc w:word16) : word16 :=
  let s := acc + w in
  if s <? two16 then s else s - mask16.

Lemma add16_ones_bound :
  forall acc w, acc < two16 -> w < two16 -> add16_ones acc w < two16.
Proof.
  intros acc w Hacc Hw. unfold add16_ones.
  destruct (acc + w <? two16) eqn:E.
  - apply N.ltb_lt in E; exact E.
  - apply N.ltb_ge in E. 
    assert (acc + w < 2*two16).
    { unfold two16 in *. lia. }
    unfold mask16, two16 in *. lia.
Qed.

(* Fold over a list of 16-bit words with one's-complement addition. *)
Fixpoint sum16 (ws:list word16) : word16 :=
  match ws with
  | [] => 0
  | w::tl => add16_ones (sum16 tl) (to_word16 w)
  end.

Lemma sum16_lt_two16 : forall ws, sum16 ws < two16.
Proof.
  induction ws as [|w tl IH]; simpl.
  - unfold two16. lia.
  - apply add16_ones_bound; auto.
    apply to_word16_lt_two16.
Qed.

(* One's-complement (bitwise not) within 16 bits. *)
Definition complement16 (x:word16) : word16 := mask16 - x.
Definition cksum16 (ws:list word16) : word16 := complement16 (sum16 ws).

Lemma sum16_singleton : forall x,
  sum16 [x] = add16_ones 0 (to_word16 x).
Proof. reflexivity. Qed.

Lemma add16_ones_comm : forall x y,
  add16_ones x y = add16_ones y x.
Proof.
  intros x y.
  unfold add16_ones.
  rewrite N.add_comm.
  reflexivity.
Qed.

(* Micro lemma 1: When no overflow, add16_ones is just addition *)
Lemma add16_ones_no_overflow : forall x y,
  x + y < two16 -> add16_ones x y = x + y.
Proof.
  intros x y H.
  unfold add16_ones.
  apply N.ltb_lt in H.
  rewrite H.
  reflexivity.
Qed.

(* Micro lemma 2: When overflow, add16_ones subtracts mask16 *)
Lemma add16_ones_overflow : forall x y,
  x + y >= two16 -> add16_ones x y = x + y - mask16.
Proof.
  intros x y H.
  unfold add16_ones.
  destruct (x + y <? two16) eqn:E.
  - apply N.ltb_lt in E. lia.
  - reflexivity.
Qed.

(* Micro lemma 3: Sum of two values less than two16 is less than 2*two16 *)
Lemma sum_bound_double : forall x y,
  x < two16 -> y < two16 -> x + y < 2 * two16.
Proof.
  intros x y Hx Hy.
  unfold two16 in *.
  lia.
Qed.

(* Micro lemma 4a: Commutativity for addition *)
Lemma add_comm_3way : forall a b c : N,
  a - b + c = c + (a - b).
Proof.
  intros. apply N.add_comm.
Qed.

(* Micro lemma 4a': When b <= a, c + (a - b) = (c + a) - b *)
Lemma sub_add_assoc : forall a b c : N,
  b <= a -> c + (a - b) = c + a - b.
Proof.
  intros a b c Hle.
  (* c + (a - b) = c + a - b when b <= a *)
  (* This follows from the fact that subtraction associates with addition from the right *)
  rewrite <- N.add_sub_assoc.
  - reflexivity.
  - exact Hle.
Qed.


(* Micro lemma 4b1: 65536 > 65535 *)
Lemma two16_gt_mask16 : two16 > mask16.
Proof.
  unfold two16, mask16.
  compute. constructor.
Qed.

(* Micro lemma 4b2: if x >= two16 then x - mask16 >= 1 *)
Lemma ge_two16_sub_mask16_ge_1 : forall x,
  two16 <= x -> 1 <= x - mask16.
Proof.
  intros x H.
  unfold two16, mask16 in *.
  (* x >= 65536 and mask16 = 65535, so x - 65535 >= 65536 - 65535 = 1 *)
  assert (65536 - 65535 <= x - 65535).
  { apply N.sub_le_mono_r. exact H. }
  assert (65536 - 65535 = 1) by reflexivity.
  rewrite <- H1.
  exact H0.
Qed.

(* Micro lemma 4b: y + z >= two16 implies mask16 <= y + z *)
Lemma two16_implies_mask16_le : forall y z,
  y + z >= two16 -> mask16 <= y + z.
Proof.
  intros y z H.
  pose proof two16_gt_mask16 as Hgt.
  unfold two16, mask16 in *.
  (* If y + z >= 65536 and 65536 > 65535, then y + z > 65535, so 65535 <= y + z *)
  clear - H Hgt.
  lia.
Qed.

(* Micro lemma 4c: Rearranging addition *)
Lemma add_rearrange : forall x y z : N,
  x + (y + z) = x + y + z.
Proof. intros. lia. Qed.

(* Micro lemma 4: Arithmetic equality for overflow case *)
Lemma overflow_arithmetic_eq : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  y + z >= two16 ->
  x + (y + z - mask16) = x + y + z - mask16.
Proof.
  intros x y z Hx Hy Hz Hyz.
  pose proof (two16_implies_mask16_le y z Hyz) as Hle.
  (* We want to show: x + (y + z - mask16) = x + y + z - mask16 *)
  (* Using sub_add_assoc with a := y+z, b := mask16, c := x *)
  (* We get: x + ((y+z) - mask16) = x + (y+z) - mask16 *)
  rewrite sub_add_assoc by exact Hle.
  (* Now we have: x + (y + z) - mask16 *)
  (* We need: x + y + z - mask16 *)
  rewrite <- add_rearrange.
  reflexivity.
Qed.

(* Micro lemma 5: Associativity with parentheses *)
Lemma add_assoc_N : forall x y z : N,
  (x + y) + z = x + (y + z).
Proof. intros. lia. Qed.

(* Micro lemma 6: Case when y+z overflows but x+y doesn't *)
Lemma add16_ones_assoc_case_yz_overflow : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  x + y < two16 -> y + z >= two16 ->
  x + y + z >= two16 -> x + (y + z - mask16) < two16 ->
  (x + y) + z - mask16 = x + (y + z - mask16).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz Hsum Hxyz_mask.
  (* Both sides equal x + y + z - mask16 *)
  transitivity (x + y + z - mask16).
  - (* (x + y) + z - mask16 = x + y + z - mask16 *)
    lia.
  - (* x + y + z - mask16 = x + (y + z - mask16) *)
    symmetry. apply overflow_arithmetic_eq; assumption.
Qed.

(* Micro lemma 7: Conditional simplification when no overflow *)
Lemma add16_ones_cond_no_overflow : forall a b,
  a + b < two16 ->
  (if a + b <? two16 then a + b else a + b - mask16) = a + b.
Proof.
  intros a b H.
  apply N.ltb_lt in H. rewrite H. reflexivity.
Qed.

(* Micro lemma 8: Handle the specific conditional in case yz overflow *)
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
  (* Since x + (y + z - mask16) < two16, the conditional chooses 'then' *)
  rewrite add16_ones_cond_no_overflow by assumption.
  (* Now apply the previous lemma *)
  apply add16_ones_assoc_case_yz_overflow; assumption.
Qed.

(* Micro lemma 9: Both sides overflow case *)
Lemma add16_ones_assoc_both_overflow : forall x y z,
  x < two16 -> y < two16 -> z < two16 ->
  x + y >= two16 -> y + z >= two16 ->
  x + y + z >= two16 -> x + (y + z - mask16) >= two16 ->
  (x + y - mask16) + z - mask16 = 
  (x + (y + z - mask16) - mask16).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz Hsum Hxyz_mask.
  (* Both sides have two subtractions *)
  assert (H1: (x + y - mask16) + z - mask16 = x + y + z - mask16 - mask16) by lia.
  assert (H2: x + (y + z - mask16) - mask16 = x + y + z - mask16 - mask16).
  { (* Apply overflow_arithmetic_eq and then subtract mask16 again *)
    assert (H2a: x + (y + z - mask16) = x + y + z - mask16).
    { apply overflow_arithmetic_eq; assumption. }
    rewrite H2a. reflexivity. }
  rewrite H1. symmetry. exact H2.
Qed.

(* Micro lemma 10: Simple arithmetic for double subtraction *)
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
  (* Since x + y >= 65536, we have x + y - 65535 >= 1 *)
  assert (x + y - 65535 >= 1) by lia.
  assert (x + y <= 65535 + 65535) by lia.
  assert (65535 + 65535 = 131070) by reflexivity.
  assert (x + y <= 131070) by lia.
  assert (x + y - 65535 <= 131070 - 65535) by lia.
  assert (131070 - 65535 = 65535) by reflexivity.
  assert (x + y - 65535 <= 65535) by lia.
  (* Since x + y - 65535 <= 65535 < 65536, we have the result *)
  assert (65535 < 65536) by reflexivity.
  assert (x + y - 65535 < 65536) by lia.
  exact H9.
Qed.


(* --- Small helpers with the right side conditions --- *)

(* For any y,z with z < 2^16, the tail (y+z - mask16) is <= y. *)
Lemma tail_le_y : forall y z,
  z < two16 -> y + z - mask16 <= y.
Proof.
  intros y z Hz.
  assert (Hz_le : z <= mask16) by (unfold mask16, two16 in *; lia).
  (* Monotonicity of subtraction on the right: *)
  assert (Hmono : y + z - mask16 <= y + mask16 - mask16).
  { apply N.sub_le_mono_r. apply N.add_le_mono_l. exact Hz_le. }
  (* Reduce RHS to y and conclude *)
  replace (y + mask16 - mask16) with y in Hmono by lia.
  exact Hmono.
Qed.


(* 2) If x+y doesn't overflow, then x + (y+z - mask16) is also below 2^16. *)
Lemma tail_lt_when_xy_no :
  forall x y z,
    x < two16 -> y < two16 -> z < two16 -> x + y < two16 ->
    x + (y + z - mask16) < two16.
Proof.
  intros x y z Hx Hy Hz Hxy.
  pose proof (tail_le_y y z Hz) as Htail.
  assert (Hxy_le : x + y <= mask16) by (unfold mask16, two16 in *; lia).
  assert (Hsum_le : x + (y + z - mask16) <= x + y) by (apply N.add_le_mono_l; exact Htail).
  unfold two16, mask16 in *; lia.
Qed.

(* 3) Rewrite x + (y+z - mask16) to x + y + z - mask16 when mask16 <= y+z. *)
Lemma sub_add_rewrite_right :
  forall x y z, mask16 <= y + z ->
  x + (y + z - mask16) = x + y + z - mask16.
Proof.
  intros x y z Hyz.
  (* Use your earlier lemma: sub_add_assoc : b <= a -> c + (a - b) = c + a - b *)
  rewrite (sub_add_assoc (y + z) mask16 x Hyz). lia.
Qed.

(* 4) Symmetric rewrite on the left when mask16 <= x+y. *)
Lemma sub_add_rewrite_left :
  forall x y z, mask16 <= x + y ->
  z + (x + y - mask16) = x + y + z - mask16.
Proof.
  intros x y z Hxy.
  (* Use your lemma: c + (a - b) = c + a - b when b <= a *)
  rewrite (sub_add_assoc (x + y) mask16 z Hxy).     (* z + (x+y) - mask16 *)
  (* Commute ONLY the inner sum on the LHS; keep RHS unchanged *)
  rewrite (N.add_comm z (x + y)).                   (* (x+y) + z - mask16 *)
  reflexivity.                                      (* same as x+y+z - mask16 *)
Qed.


Lemma add16_ones_assoc_case_nn :
  forall x y z,
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
  rewrite <- add_assoc_N.  (* x + (y + z)  ->  (x + y) + z *)
  reflexivity.
Qed.

Lemma add16_ones_assoc_case_ny :
  forall x y z,
    x < two16 -> y < two16 -> z < two16 ->
    (x + y <? two16) = true ->
    (y + z <? two16) = false ->
    add16_ones (add16_ones x y) z = add16_ones x (add16_ones y z).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz.
  apply N.ltb_lt in Hxy.
  apply N.ltb_ge in Hyz.
  (* Reorient the inequality with [lia] to match lemmas that expect [>=] *)
  assert (Hyz_ge : y + z >= two16) by lia.

  rewrite (add16_ones_no_overflow x y Hxy).
  rewrite (add16_ones_overflow y z Hyz_ge).

  (* (x+y)+z >= y+z >= 2^16 *)
  assert (Hsum_ge : (x + y) + z >= two16) by lia.
  rewrite (add16_ones_overflow (x + y) z Hsum_ge).

  (* tail ≤ y and x+y < 2^16 ⇒ no overflow *)
  rewrite (add16_ones_no_overflow x (y + z - mask16)
            (tail_lt_when_xy_no x y z Hx Hy Hz Hxy)).

  (* (x+y)+z - mask16 = x + (y+z - mask16) since y+z >= 2^16 *)
  rewrite (sub_add_rewrite_right x y z (two16_implies_mask16_le _ _ Hyz_ge)).
  reflexivity.
Qed.

(* Convenience orientation: accepts "two16 <= x+y" form *)
Lemma add16_ones_overflow_le :
  forall x y, two16 <= x + y -> add16_ones x y = x + y - mask16.
Proof.
  intros x y H.
  apply add16_ones_overflow. lia.
Qed.

Lemma add16_ones_ext_by_sum :
  forall a b c d,
    a + b = c + d ->
    add16_ones a b = add16_ones c d.
Proof.
  intros a b c d Heq.
  unfold add16_ones.
  now rewrite Heq.
Qed.

Lemma mask16_le_two16 : mask16 <= two16.
Proof. cbv [mask16 two16]; lia. Qed.

Lemma overflow_info :
  forall x y, (x + y <? two16) = false ->
  two16 <= x + y /\ mask16 <= x + y.
Proof.
  intros x y H.
  apply N.ltb_ge in H. (* two16 <= x + y *)
  split; [ exact H | eapply N.le_trans; [apply mask16_le_two16 | exact H] ].
Qed.

(* Align the outer sums when both inner pairs overflow (ltb=false premises). *)
Lemma sums_align_both_overflow :
  forall x y z,
    (x + y <? two16) = false ->
    (y + z <? two16) = false ->
    (x + y - mask16) + z = x + (y + z - mask16).
Proof.
  intros x y z Hxy Hyz.
  destruct (overflow_info x y Hxy) as [_ Hxy_mle].  (* mask16 <= x+y *)
  destruct (overflow_info y z Hyz) as [_ Hyz_mle].  (* mask16 <= y+z *)
  rewrite (N.add_comm (x + y - mask16) z).
  rewrite (sub_add_rewrite_left  x y z Hxy_mle).
  rewrite (sub_add_rewrite_right x y z Hyz_mle).
  reflexivity.
Qed.

Lemma add16_ones_overflow_ltb_false :
  forall x y,
    (x + y <? two16) = false ->
    add16_ones x y = x + y - mask16.
Proof.
  intros x y H.
  apply N.ltb_ge in H.                (* two16 <= x + y *)
  apply add16_ones_overflow; lia.     (* x + y >= two16 *)
Qed.

Lemma add16_ones_assoc_case_yy :
  forall x y z,
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

Lemma add16_ones_no_overflow_ltb_true :
  forall x y,
    (x + y <? two16) = true ->
    add16_ones x y = x + y.
Proof.
  intros x y H.
  apply N.ltb_lt in H.
  apply add16_ones_no_overflow; exact H.
Qed.


(* If t ≤ mask16, then x + t - mask16 is strictly below 2^16 whenever x is. *)
Lemma add_minus_mask16_lt_two16 :
  forall x t, x < two16 -> t <= mask16 -> x + t - mask16 < two16.
Proof.
  intros x t Hx Ht.
  assert (Hle : x + t - mask16 <= x + mask16 - mask16).
  { apply N.sub_le_mono_r. apply N.add_le_mono_l. exact Ht. }
  replace (x + mask16 - mask16) with x in Hle by lia.
  eapply N.le_lt_trans; [exact Hle| exact Hx].
Qed.


Lemma add16_ones_assoc_case_yn :
  forall x y z,
    x < two16 -> y < two16 -> z < two16 ->
    (x + y <? two16) = false ->
    (y + z <? two16) = true ->
    add16_ones (add16_ones x y) z = add16_ones x (add16_ones y z).
Proof.
  intros x y z Hx Hy Hz Hxy Hyz.
  (* Reduce the two inner sums by their tests *)
  rewrite (add16_ones_overflow_ltb_false x y Hxy).
  rewrite (add16_ones_no_overflow_ltb_true y z Hyz).

  (* From overflow on x+y, get mask16 <= x+y *)
  destruct (overflow_info x y Hxy) as [Hxy_ge Hxy_mle].

  (* From no-overflow on y+z, get y+z <= mask16 *)
  apply N.ltb_lt in Hyz.
  assert (Hyz_le : y + z <= mask16).
  { unfold mask16, two16. 
    assert (y + z <= 65535).
    { assert (y + z < 65536) by exact Hyz. lia. }
    exact H. }

  (* LHS outer is no-overflow: ((x+y)-mask16)+z < 2^16 *)
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

  (* RHS outer overflows: x + (y+z) >= x + y >= 2^16 *)
  assert (Hrhs_ge : x + (y + z) >= two16) by lia.
  rewrite (add16_ones_overflow x (y + z) Hrhs_ge).

  (* Align arithmetic on both sides *)
  rewrite N.add_comm with (n := x + y - mask16) (m := z).
  rewrite (sub_add_rewrite_left x y z Hxy_mle).
  replace (x + y + z - mask16) with (x + (y + z) - mask16) by lia.
  reflexivity.
Qed.

Lemma add16_ones_assoc : forall x y z,
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

Lemma add16_ones_complement :
  forall s, s < two16 -> add16_ones s (complement16 s) = mask16.
Proof.
  intros s Hs. unfold add16_ones, complement16.
  assert (s + (mask16 - s) = mask16).
  { unfold mask16. lia. }
  rewrite H.
  assert (mask16 < two16).
  { unfold mask16, two16. lia. }
  apply N.ltb_lt in H0.
  rewrite H0.
  reflexivity.
Qed.

Lemma sum16_with_cksum_is_allones :
  forall ws, sum16 (ws ++ [cksum16 ws]) = mask16.
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

(* ----------------------------------------------------------------------------
   4) UDP header, wire format, policies, and checksum material
   --------------------------------------------------------------------------*)

Record UdpHeader := {
  (* RFC 768: Source port is OPTIONAL; 0 means "unspecified" (no reply expected).
     Our model permits src_port = 0 everywhere and never rejects it. *)
  src_port : word16;
  dst_port : word16;   (* Destination port 0 is a host policy decision *)
  length16 : word16;   (* Header (8) + data; MUST be >= 8 *)
  checksum : word16    (* 0 => no checksum (IPv4); else Internet checksum *)
}.

Definition udp_header_words (h:UdpHeader) : list word16 :=
  [ h.(src_port); h.(dst_port); h.(length16); h.(checksum) ].

Definition udp_header_words_zero_ck (h:UdpHeader) : list word16 :=
  [ h.(src_port); h.(dst_port); h.(length16); 0 ].

Definition udp_header_bytes (h:UdpHeader) : list byte :=
  bytes_of_words16_be (udp_header_words h).

(* Receiver/sender policies *)
Inductive ChecksumTxMode := WithChecksum | NoChecksum.
Inductive ChecksumRxMode := RequireValidOnly | ValidOrZero.
Inductive ZeroChecksumPolicy := ZeroAlwaysAccept | ZeroForbidOnMultiOrBcast | ZeroForbidAlways.
Inductive LengthRxMode   := StrictEq | AcceptShorterIP.
Inductive DstPortZeroPolicy := Allow | Reject.

Record Config := {
  checksum_tx_mode     : ChecksumTxMode;
  checksum_rx_mode     : ChecksumRxMode;
  zero_checksum_policy : ZeroChecksumPolicy;     (* governs acceptance of ck=0 *)
  length_rx_mode       : LengthRxMode;
  dst_port0_policy     : DstPortZeroPolicy;
  is_broadcast         : IPv4 -> bool           (* host-specific broadcast test *)
}.

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

Inductive EncodeError := Oversize.
Inductive DecodeError := BadLength | BadChecksum | DstPortZeroNotAllowed.

(* Material over which the UDP checksum is computed for IPv4 *)
Definition checksum_words_ipv4
  (src dst:IPv4) (h:UdpHeader) (data:list byte) : list word16 :=
  pseudo_header_v4 src dst h.(length16)
  ++ udp_header_words_zero_ck h
  ++ words16_of_bytes_be data.

(* RFC 768 rule: if the computed checksum is 0x0000, transmit 0xFFFF *)
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

(* Helper: zero-checksum acceptance per cfg and destination address *)
Definition zero_checksum_allowed (cfg:Config) (dst:IPv4) : bool :=
  match cfg.(zero_checksum_policy) with
  | ZeroAlwaysAccept => true
  | ZeroForbidAlways => false
  | ZeroForbidOnMultiOrBcast =>
      negb (is_multicast_ipv4 dst || cfg.(is_broadcast) dst)
  end.

(* ----------------------------------------------------------------------------
   5) TOTAL encoder
   --------------------------------------------------------------------------*)

Definition mk_header (sp dp:word16) (data_len_N:N) : option UdpHeader :=
  let L := 8 + data_len_N in
  if (L <=? mask16)%N
  then Some {| src_port := to_word16 sp;
               dst_port := to_word16 dp;
               length16 := to_word16 L;
               checksum := 0 |}
  else None.

(* Precise "Some" inversion for mk_header *)
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

(* ----------------------------------------------------------------------------
   6) TOTAL decoder
   --------------------------------------------------------------------------*)

(* Parse first 8 bytes into UdpHeader (big-endian).
   NEW: reject headers containing any out-of-range "bytes" (>= 256). *)
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

(* Verify checksum: sum over pseudo + header-with-zero + data + transmitted ck. *)
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
      (* Host policy on destination port 0. *)
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

(* ----------------------------------------------------------------------------
   6') Receive API enrichment (RFC 768/1122) without modifying V1 proofs
   --------------------------------------------------------------------------*)

(* Receive record that carries addresses per RFC 1122. *)
Record UdpDeliver := {
  src_ip_out  : IPv4;
  dst_ip_out  : IPv4;        (* specific destination address *)
  src_port_out: word16;
  dst_port_out: word16;
  payload_out : list byte
}.

(* Backward-compatibility alias. *)
Definition DecodedV1 := Decoded.

(* Wrapper that augments V1 decode with addresses. *)
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

(* ----------------------------------------------------------------------------
   6'') ICMP error handling (RFC 768/1122/1812 alignment)
   --------------------------------------------------------------------------*)

(* ICMP Destination Unreachable codes (RFC 792) *)
Definition ICMP_NET_UNREACH    : N := 0.
Definition ICMP_HOST_UNREACH   : N := 1.
Definition ICMP_PROTO_UNREACH  : N := 2.
Definition ICMP_PORT_UNREACH   : N := 3.
Definition ICMP_FRAG_NEEDED    : N := 4.
Definition ICMP_SR_FAILED      : N := 5.

(* ICMP Time Exceeded codes *)
Definition ICMP_TTL_EXCEEDED   : N := 0.
Definition ICMP_FRAG_TIME_EXCEEDED : N := 1.

(* ICMP Parameter Problem codes *)
Definition ICMP_PARAM_POINTER  : N := 0.

(* Receive-side advice for generating ICMP based on UDP result. *)
Inductive RxAdvice :=
  | SendICMPDestUnreach (code: N)   (* Port/Host/Net unreachable, etc. *)
  | SendICMPTimeExceeded (code: N)  (* TTL or fragment reassembly timeout *)
  | SendICMPParamProblem (pointer: N) (* IP header parameter problem *)
  | NoAdvice.

(* Transmit-side error notification mapped from received ICMP. *)
Inductive TxError :=
  | ICMPDestUnreach (code: N)
  | ICMPSourceQuench
  | ICMPTimeExceeded (code: N)
  | ICMPParamProblem (pointer: N)
  | NetworkError.

(* Enhanced port unreachable advice with listener check. *)
Definition udp_rx_icmp_advice
  (has_listener: IPv4 -> word16 -> bool)
  (decode_result: result UdpDeliver DecodeError)
  : RxAdvice :=
  match decode_result with
  | inl d =>
      if has_listener d.(dst_ip_out) d.(dst_port_out)
      then NoAdvice
      else SendICMPDestUnreach ICMP_PORT_UNREACH
  | inr BadLength => NoAdvice            (* UDP length errors: drop; no ICMP *)
  | inr BadChecksum => NoAdvice          (* Checksum errors: drop; no ICMP *)
  | inr DstPortZeroNotAllowed => NoAdvice
  end.

(* Determine if ICMP should be sent based on destination type. *)
Definition should_send_icmp (cfg:Config) (dst:IPv4) : bool :=
  negb (is_multicast_ipv4 dst || cfg.(is_broadcast) dst).

(* Complete ICMP advice considering destination type. *)
Definition udp_complete_icmp_advice
  (cfg:Config)
  (has_listener: IPv4 -> word16 -> bool)
  (src_ip dst_ip:IPv4)
  (decode_result: result UdpDeliver DecodeError)
  : RxAdvice :=
  if should_send_icmp cfg dst_ip
  then udp_rx_icmp_advice has_listener decode_result
  else NoAdvice.

(* Context extracted from an ICMP error quoted packet. *)
Record ICMPErrorContext := {
  icmp_type     : N;          (* ICMP type field *)
  icmp_code     : N;          (* ICMP code field *)
  orig_src_ip   : IPv4;       (* Original source IP *)
  orig_dst_ip   : IPv4;       (* Original destination IP *)
  orig_src_port : word16;     (* Original source port *)
  orig_dst_port : word16      (* Original destination port *)
}.

(* Map ICMP error to TxError for application notification. *)
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

(* UDP MUST pass all received ICMP errors up to the application. *)
Definition udp_must_notify_app (err:TxError) : bool := true.

(* Extended configuration with optional ICMP rate limiting for transmission. *)
Record ConfigWithICMP := {
  base_config      : Config;
  rate_limit_icmp  : N -> N -> bool  (* (hash_of_srcdst, current_time) -> allow? *)
}.

(* Default configuration with ICMP support. *)
Definition defaults_ipv4_with_icmp : ConfigWithICMP :=
  {| base_config := defaults_ipv4;
     rate_limit_icmp := fun _ _ => true |}.  (* no rate limiting by default *)

(* ----------------------------------------------------------------------------
   7) Parser/serializer round-trip and checksum correctness proofs
   --------------------------------------------------------------------------*)

(* Normalization predicate: all fields < 2^16 *)
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

(* === Helper 1: checksum material ignores the checksum field ================= *)

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

(* === Helper 2: cksum16 ws = 0  ⇒  sum16 ws = 0xFFFF ======================== *)

Lemma cksum16_zero_sum_allones :
  forall ws, cksum16 ws = 0 -> sum16 ws = mask16.
Proof.
  intros ws H0.
  unfold cksum16, complement16 in H0.
  assert (Hlt : sum16 ws < two16) by apply sum16_lt_two16.
  assert (Hle : sum16 ws <= mask16) by (unfold mask16, two16 in *; lia).
  lia.
Qed.

(* === Helper 3: canonicalization for 0xFFFF ================================= *)

Lemma to_word16_mask16_id : to_word16 mask16 = mask16.
Proof. apply to_word16_id_if_le_mask; unfold mask16; lia. Qed.

(* === Helper 4: if sum16 ws = 0xFFFF then appending 0xFFFF keeps it all-ones == *)

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


(* === Main lemma (short, uses the helpers) ================================== *)

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
  (* Only unfold the verifier; keep compute_udp folded so the invariant matches. *)
  unfold verify_checksum_ipv4.

  (* Replace the checksum material built from [h1] by the one from [h0]. *)
  rewrite (checksum_words_ipv4_ck_invariant ipS ipD h0 data
            (compute_udp_checksum_ipv4 ipS ipD h0 data)).

  (* The appended singleton is just the header's checksum field. *)
  cbn [checksum].

  (* Freeze the words; only now unfold compute_udp. *)
  set (words := checksum_words_ipv4 ipS ipD h0 data).
  unfold compute_udp_checksum_ipv4.

(* Split on whether the computed checksum would be zero. *)
destruct (N.eqb (cksum16 words) 0) eqn:Ez.  (* NOTE: no [simpl] here *)

(* zero branch *)
apply N.eqb_eq.
subst words.
apply sum16_app_if_cksum_zero_concrete.
exact Ez.

(* nonzero branch *)
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

(* ----------------------------------------------------------------------------
   8) Encode→Decode round-trips (StrictEq)
   --------------------------------------------------------------------------*)

(* Helper: length equality holds on wires produced by the encoder (StrictEq) *)
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


Theorem decode_encode_roundtrip_ipv4_defaults_reject_nonzero16 :
  forall ipS ipD sp dp data wire h0,
    to_word16 dp <> 0%N ->
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire
      = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros ipS ipD sp dp data wire h0 HdpNZ Hmk Henc.

  (* Header used by encoder (checksum filled in) *)
  set (h1 :=
    {| src_port := src_port h0
     ; dst_port := dst_port h0
     ; length16 := length16 h0
     ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).

  (* Concrete wire from encoder (no heavy simpl) *)
  pose proof (encode_udp_defaults_wire_eq_fast ipS ipD sp dp data h0 h1 wire Hmk eq_refl Henc) as Hw.

  (* Decode that exact wire *)
  unfold decode_udp_ipv4. rewrite Hw. clear Hw.

  (* parse_header succeeds on encoder bytes *)
  assert (Hnorm : header_norm h1)
    by (apply (header_norm_encode_h1 sp dp (lenN data) h0 ipS ipD data Hmk)).
  rewrite (parse_header_bytes_of_header_norm h1 data Hnorm). cbn.

  (* Port-0 policy under Reject with nonzero destination port *)
  cbn [defaults_ipv4].
  rewrite (dst_port0_test_reject_nonzero_h0 sp dp data h0 Hmk HdpNZ). cbn.

  (* Length checks under StrictEq *)
  cbn [defaults_ipv4].
  (* Name and normalize totals *)
  set (Nbytes := lenN (udp_header_bytes h1 ++ data)).
  set (L := length16 h1).
  replace Nbytes with (8 + lenN data)
    by (subst Nbytes; apply lenN_wire_from_header_bytes).
  replace L with (8 + lenN data)
    by (apply (length16_h1_total_len ipS ipD sp dp data h0 h1); [exact Hmk|reflexivity]).
  rewrite N.ltb_ge by lia.    (* L >= 8 *)
  rewrite N.ltb_ge by lia.    (* Nbytes >= L (actually =) *)
  rewrite (N.eqb_eq (8 + lenN data) (8 + lenN data)) by lia.

  (* Checksum is nonzero on IPv4 transmit *)
  rewrite (checksum_h1_eqb_zero_false ipS ipD sp dp data h0 h1 Hmk eq_refl).

  (* Delivered slice equals original payload *)
  set (delivered_len_N := (8 + lenN data) - 8).
  set (delivered_len := N.to_nat delivered_len_N).
  set (delivered := take delivered_len data).
  assert (Hdel : delivered = data).
  { subst delivered delivered_len delivered_len_N.
    eapply delivered_eq_data. reflexivity. }
  rewrite Hdel.

  (* Verifier succeeds on encoder-produced checksum *)
  rewrite (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1 Hmk eq_refl).

  (* Return tuple *)
  destruct (h1_ports_eq ipS ipD sp dp data h0 h1 Hmk eq_refl) as [Hsp Hdp].
  f_equal; [exact Hsp | exact Hdp | reflexivity].
Qed.



Theorem decode_encode_roundtrip_ipv4_defaults_reject_nonzero16 :
  forall ipS ipD sp dp data wire h0,
    to_word16 dp <> 0%N ->
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire
      = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros ipS ipD sp dp data wire h0 Hdp16NZ Hmk Henc.

  (* Define the header used by the encoder's WithChecksum branch. *)
  set (h1 :=
    {| src_port := src_port h0
     ; dst_port := dst_port h0
     ; length16 := length16 h0
     ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).

  (* From the encoder equality, get the concrete wire bytes. *)
  unfold encode_udp_ipv4 in Henc. rewrite Hmk in Henc.
  assert (Etx : checksum_tx_mode defaults_ipv4 = WithChecksum) by reflexivity.
  rewrite Etx in Henc. apply Ok_inj in Henc. symmetry in Henc.
  set (Hw := Henc). clear Henc.

  (* Decode that exact wire *)
  unfold decode_udp_ipv4. rewrite Hw.

  (* parse_header succeeds on bytes we produced *)
  assert (Hnorm : header_norm h1)
    by (apply (header_norm_encode_h1 sp dp (lenN data) h0 ipS ipD data Hmk)).
  rewrite (parse_header_bytes_of_header_norm h1 data Hnorm). cbn.

  (* Port-0 policy: Reject + nonzero destination port => proceed *)
  cbn [defaults_ipv4].
  destruct (h1_ports_eq ipS ipD sp dp data h0 h1 Hmk eq_refl) as [Hsp1 Hdp1].
  assert (Hdp0 : N.eqb (dst_port h1) 0 = false)
    by (rewrite Hdp1; apply N.eqb_neq; exact Hdp16NZ).
  rewrite Hdp0. cbn.

  (* Length bookkeeping *)
  set (Nbytes := lenN (udp_header_bytes h1 ++ data)).
  set (L := length16 h1).
  assert (HNbytes : Nbytes = 8 + lenN data)
    by (subst Nbytes; apply lenN_wire_from_header_bytes).
  assert (HLtot : L = 8 + lenN data)
    by (apply (length16_h1_total_len ipS ipD sp dp data h0 h1); [exact Hmk|reflexivity]).
  rewrite HNbytes, HLtot.
  rewrite N.ltb_ge by lia.  (* L >= 8 *)
  rewrite N.ltb_ge by lia.  (* Nbytes >= L, in fact = *)

  (* StrictEq path; Nbytes = L *)
  cbn [defaults_ipv4].
  assert (Hbeq : N.eqb (8 + lenN data) (8 + lenN data) = true)
    by (apply N.eqb_eq; lia).
  rewrite Hbeq.

  (* Checksum is nonzero on TX for IPv4 *)
  rewrite (checksum_h1_eqb_zero_false ipS ipD sp dp data h0 h1 Hmk eq_refl).

  (* Name the delivered slice and show it's exactly [data] *)
  set (delivered_len_N := (8 + lenN data) - 8).
  set (delivered_len := N.to_nat delivered_len_N).
  set (delivered := take delivered_len data).
  assert (HdN   : delivered_len_N = lenN data) by (subst delivered_len_N; lia).
  assert (Hdlen : delivered_len = List.length data)
    by (subst delivered_len; rewrite HdN, N_to_nat_lenN; reflexivity).
  assert (Hdel  : delivered = data)
    by (subst delivered; rewrite Hdlen, take_length_id; reflexivity).

  (* Verifier succeeds on encoder-produced checksum *)
  rewrite Hdel.
  rewrite (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1 Hmk eq_refl).

  (* Return tuple components *)
  f_equal; [rewrite Hsp1|rewrite Hdp1|reflexivity].
Qed.


(* MAIN Theorem B (StrictEq):
   Alternate defaults (Allow destination-port 0). No premise required. *)
Theorem decode_encode_roundtrip_ipv4_defaults_allow0 :
  forall ipS ipD sp dp data wire h0,
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4_allow0 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4_allow0 ipS ipD wire
      = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros ipS ipD sp dp data wire h0 Hmk Henc.
  unfold encode_udp_ipv4 in Henc.
  rewrite Hmk in Henc.
  destruct (checksum_tx_mode defaults_ipv4_allow0) eqn:Etx; [|discriminate].
  inversion Henc; subst wire; clear Henc.
  set (h1 := {| src_port := src_port h0 ;
                dst_port := dst_port h0 ;
                length16 := length16 h0 ;
                checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).
  unfold decode_udp_ipv4.
  assert (Hnorm: header_norm h1) by (apply (header_norm_encode_h1 sp dp (lenN data) h0 ipS ipD data Hmk)).
  rewrite (parse_header_bytes_of_header_norm h1 data Hnorm). cbn.
  set (Nbytes := lenN (udp_header_bytes h1 ++ data)).
  set (L := length16 h1).
  assert (HNbytes: Nbytes = 8 + lenN data).
  { unfold Nbytes. rewrite lenN_app, lenN_udp_header_bytes_8. lia. }
  assert (HL: L = to_word16 (8 + lenN data)).
  { unfold L, h1. simpl.
    destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [_ [HL0 _]]]]; exact HL0. }
  assert (Hle: 8 + lenN data <= mask16) by (destruct (mk_header_ok _ _ _ _ Hmk) as [Hle' _]; exact Hle').
  assert (HLid: to_word16 (8 + lenN data) = 8 + lenN data) by (apply to_word16_id_if_le_mask; exact Hle).
  rewrite HNbytes, HL, HLid.
  rewrite N.ltb_ge; [|lia].
  rewrite N.ltb_ge; [|lia].
  rewrite N.eqb_eq; [|lia].
  destruct (N.eqb (checksum h1) 0) eqn:Eck.
  - exfalso.
    unfold h1 in Eck; simpl in Eck.
    apply N.eqb_eq in Eck.
    pose proof (compute_udp_checksum_ipv4_nonzero ipS ipD h0 data) as Hnz.
    congruence.
  - rewrite (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1 Hmk eq_refl).
    f_equal. f_equal. f_equal.
    all: try (unfold h1; simpl;
              destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp _]]];
              now rewrite Hsp || rewrite Hdp).
Qed.

(* ----------------------------------------------------------------------------
   8') Encode→Decode round-trips (AcceptShorterIP)
   --------------------------------------------------------------------------*)

Theorem decode_encode_roundtrip_ipv4_defaults_reject_nonzero16_acceptShorter :
  forall ipS ipD sp dp data wire h0,
    to_word16 dp <> 0%N ->
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4_acceptShorter ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4_acceptShorter ipS ipD wire
      = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros ipS ipD sp dp data wire h0 Hdp16NZ Hmk Henc.
  unfold encode_udp_ipv4 in Henc.
  rewrite Hmk in Henc.
  destruct (checksum_tx_mode defaults_ipv4_acceptShorter) eqn:Etx; [|discriminate].
  inversion Henc; subst wire; clear Henc.
  set (h1 := {| src_port := src_port h0 ;
                dst_port := dst_port h0 ;
                length16 := length16 h0 ;
                checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).
  unfold decode_udp_ipv4.
  assert (Hnorm: header_norm h1) by (apply (header_norm_encode_h1 sp dp (lenN data) h0 ipS ipD data Hmk)).
  rewrite (parse_header_bytes_of_header_norm h1 data Hnorm). cbn.
  rewrite N.eqb_neq.
  2:{ unfold h1. simpl.
      destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [Hdp _]]].
      rewrite Hdp. exact Hdp16NZ. }
  set (Nbytes := lenN (udp_header_bytes h1 ++ data)).
  set (L := length16 h1).
  assert (HNbytes: Nbytes = 8 + lenN data).
  { unfold Nbytes. rewrite lenN_app, lenN_udp_header_bytes_8. lia. }
  assert (HL: L = to_word16 (8 + lenN data)).
  { unfold L, h1. simpl.
    destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL0 _]]]]. exact HL0. }
  assert (Hle: 8 + lenN data <= mask16) by (destruct (mk_header_ok _ _ _ _ Hmk) as [Hle' _]; exact Hle').
  assert (HLid: to_word16 (8 + lenN data) = 8 + lenN data) by (apply to_word16_id_if_le_mask; exact Hle).
  rewrite HNbytes, HL, HLid.
  rewrite N.ltb_ge; [|lia].
  rewrite N.ltb_ge; [|lia].
  destruct (N.eqb (checksum h1) 0) eqn:Eck.
  - exfalso. unfold h1 in Eck; simpl in Eck.
    apply N.eqb_eq in Eck.
    pose proof (compute_udp_checksum_ipv4_nonzero ipS ipD h0 data) as Hnz.
    congruence.
  - rewrite (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1 Hmk eq_refl).
    f_equal. f_equal. f_equal.
    all: try (unfold h1; simpl;
              destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp _]]];
              now rewrite Hsp || rewrite Hdp).
Qed.

Theorem decode_encode_roundtrip_ipv4_defaults_allow0_acceptShorter :
  forall ipS ipD sp dp data wire h0,
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4_allow0_acceptShorter ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4_allow0_acceptShorter ipS ipD wire
      = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros ipS ipD sp dp data wire h0 Hmk Henc.
  unfold encode_udp_ipv4 in Henc.
  rewrite Hmk in Henc.
  destruct (checksum_tx_mode defaults_ipv4_allow0_acceptShorter) eqn:Etx; [|discriminate].
  inversion Henc; subst wire; clear Henc.
  set (h1 := {| src_port := src_port h0 ;
                dst_port := dst_port h0 ;
                length16 := length16 h0 ;
                checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).
  unfold decode_udp_ipv4.
  assert (Hnorm: header_norm h1) by (apply (header_norm_encode_h1 sp dp (lenN data) h0 ipS ipD data Hmk)).
  rewrite (parse_header_bytes_of_header_norm h1 data Hnorm). cbn.
  set (Nbytes := lenN (udp_header_bytes h1 ++ data)).
  set (L := length16 h1).
  assert (HNbytes: Nbytes = 8 + lenN data).
  { unfold Nbytes. rewrite lenN_app, lenN_udp_header_bytes_8. lia. }
  assert (HL: L = to_word16 (8 + lenN data)).
  { unfold L, h1. simpl.
    destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [_ [HL0 _]]]]; exact HL0. }
  assert (Hle: 8 + lenN data <= mask16) by (destruct (mk_header_ok _ _ _ _ Hmk) as [Hle' _]; exact Hle').
  assert (HLid: to_word16 (8 + lenN data) = 8 + lenN data) by (apply to_word16_id_if_le_mask; exact Hle).
  rewrite HNbytes, HL, HLid.
  rewrite N.ltb_ge; [|lia].
  rewrite N.ltb_ge; [|lia].
  destruct (N.eqb (checksum h1) 0) eqn:Eck.
  - exfalso. unfold h1 in Eck; simpl in Eck.
    apply N.eqb_eq in Eck.
    pose proof (compute_udp_checksum_ipv4_nonzero ipS ipD h0 data) as Hnz.
    congruence.
  - rewrite (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1 Hmk eq_refl).
    f_equal. f_equal. f_equal.
    all: try (unfold h1; simpl;
              destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp _]]];
              now rewrite Hsp || rewrite Hdp).
Qed.

(* ----------------------------------------------------------------------------
   8'') Address-carrying round-trips (corollaries)
   --------------------------------------------------------------------------*)

Theorem decode_encode_roundtrip_ipv4_defaults_reject_nonzero16_with_addrs :
  forall ipS ipD sp dp data wire h0,
    to_word16 dp <> 0%N ->
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4_with_addrs defaults_ipv4 ipS ipD wire
      = Ok {| src_ip_out := ipS
            ; dst_ip_out := ipD
            ; src_port_out := to_word16 sp
            ; dst_port_out := to_word16 dp
            ; payload_out := data |}.
Proof.
  intros. unfold decode_udp_ipv4_with_addrs.
  rewrite (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16
             ipS ipD sp dp data wire h0); auto. reflexivity.
Qed.

Theorem decode_encode_roundtrip_ipv4_defaults_allow0_with_addrs :
  forall ipS ipD sp dp data wire h0,
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4_allow0 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4_with_addrs defaults_ipv4 ipS ipD wire
      = Ok {| src_ip_out := ipS
            ; dst_ip_out := ipD
            ; src_port_out := to_word16 sp
            ; dst_port_out := to_word16 dp
            ; payload_out := data |}.
Proof.
  intros. unfold decode_udp_ipv4_with_addrs.
  rewrite (decode_encode_roundtrip_ipv4_defaults_allow0
             ipS ipD sp dp data wire h0); auto. reflexivity.
Qed.

Theorem decode_encode_roundtrip_ipv4_defaults_reject_nonzero16_with_addrs_acceptShorter :
  forall ipS ipD sp dp data wire h0,
    to_word16 dp <> 0%N ->
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4_acceptShorter ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4_with_addrs defaults_ipv4_acceptShorter ipS ipD wire
      = Ok {| src_ip_out := ipS
            ; dst_ip_out := ipD
            ; src_port_out := to_word16 sp
            ; dst_port_out := to_word16 dp
            ; payload_out := data |}.
Proof.
  intros. unfold decode_udp_ipv4_with_addrs.
  rewrite (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16_acceptShorter
             ipS ipD sp dp data wire h0); auto. reflexivity.
Qed.

Theorem decode_encode_roundtrip_ipv4_defaults_allow0_with_addrs_acceptShorter :
  forall ipS ipD sp dp data wire h0,
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4_allow0_acceptShorter ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4_with_addrs defaults_ipv4_allow0_acceptShorter ipS ipD wire
      = Ok {| src_ip_out := ipS
            ; dst_ip_out := ipD
            ; src_port_out := to_word16 sp
            ; dst_port_out := to_word16 dp
            ; payload_out := data |}.
Proof.
  intros. unfold decode_udp_ipv4_with_addrs.
  rewrite (decode_encode_roundtrip_ipv4_defaults_allow0_acceptShorter
             ipS ipD sp dp data wire h0); auto. reflexivity.
Qed.

(* ----------------------------------------------------------------------------
   8''') ICMP-aware round-trips with advice
   --------------------------------------------------------------------------*)

(* Encoder never produces packets that trigger ICMP on decode when a listener exists. *)
Theorem encode_decode_no_icmp_on_success :
  forall ipS ipD sp dp data wire h0 has_listener,
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire = Ok (to_word16 sp, to_word16 dp, data) ->
    has_listener ipD (to_word16 dp) = true ->
    udp_rx_icmp_advice has_listener
      (decode_udp_ipv4_with_addrs defaults_ipv4 ipS ipD wire) = NoAdvice.
Proof.
  intros ipS ipD sp dp data wire h0 has_listener Hmk Henc Hdec Hlistener.
  unfold udp_rx_icmp_advice.
  unfold decode_udp_ipv4_with_addrs.
  rewrite Hdec. simpl.
  rewrite Hlistener. reflexivity.
Qed.

(* Port unreachable is generated when no listener exists. *)
Theorem decode_generates_port_unreachable :
  forall ipS ipD sp dp data wire h0 has_listener,
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire = Ok (to_word16 sp, to_word16 dp, data) ->
    has_listener ipD (to_word16 dp) = false ->
    udp_rx_icmp_advice has_listener
      (decode_udp_ipv4_with_addrs defaults_ipv4 ipS ipD wire) =
      SendICMPDestUnreach ICMP_PORT_UNREACH.
Proof.
  intros ipS ipD sp dp data wire h0 has_listener Hmk Henc Hdec Hno_listener.
  unfold udp_rx_icmp_advice.
  unfold decode_udp_ipv4_with_addrs.
  rewrite Hdec. simpl.
  rewrite Hno_listener. reflexivity.
Qed.

(* ----------------------------------------------------------------------------
   9) Small executable examples (sanity checks)
   --------------------------------------------------------------------------*)

Definition EX_src := mkIPv4 192 0 2 1.
Definition EX_dst := mkIPv4 198 51 100 2.
Definition EX_data : list byte := [ 104; 105 ].
Definition EX_data_odd : list byte := [ 42 ].

Example EX_encode_ok :
  exists wire h0, mk_header 5353 9999 (lenN EX_data) = Some h0
              /\ encode_udp_ipv4 defaults_ipv4 EX_src EX_dst 5353 9999 EX_data = Ok wire.
Proof.
  unfold encode_udp_ipv4, mk_header, lenN, EX_data.
  simpl. rewrite N.leb_le by lia. eexists. eexists. split; [reflexivity|].
  simpl. reflexivity.
Qed.

(* Under Reject policy, require the exact modular premise to_word16 dp ≠ 0. *)
Example EX_roundtrip_reject_nonzero16 :
  forall wire h0,
    mk_header 5353 9999 (lenN EX_data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 EX_src EX_dst 5353 9999 EX_data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 EX_src EX_dst wire
      = Ok (to_word16 5353, to_word16 9999, EX_data).
Proof.
  intros wire h0 Hmk Henc.
  apply (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16
           EX_src EX_dst 5353 9999 EX_data wire h0).
  - change (9999 mod 65536 <> 0). cbv; discriminate.
  - exact Hmk.
  - exact Henc.
Qed.

(* Under Allow policy, no premise needed. *)
Example EX_roundtrip_allow0 :
  forall wire h0,
    mk_header 5353 0 (lenN EX_data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4_allow0 EX_src EX_dst 5353 0 EX_data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4_allow0 EX_src EX_dst wire
      = Ok (to_word16 5353, to_word16 0, EX_data).
Proof.
  intros wire h0 Hmk Henc.
  eapply decode_encode_roundtrip_ipv4_defaults_allow0; eauto.
Qed.

(* Address-carrying example *)
Example EX_roundtrip_with_addrs :
  forall wire h0,
    mk_header 5353 9999 (lenN EX_data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 EX_src EX_dst 5353 9999 EX_data = Ok wire ->
    decode_udp_ipv4_with_addrs defaults_ipv4 EX_src EX_dst wire
      = Ok {| src_ip_out := EX_src
            ; dst_ip_out := EX_dst
            ; src_port_out := to_word16 5353
            ; dst_port_out := to_word16 9999
            ; payload_out := EX_data |}.
Proof.
  intros; eapply decode_encode_roundtrip_ipv4_defaults_reject_nonzero16_with_addrs; eauto.
Qed.

(* Odd-length payload example (pads one zero byte for checksum computation). *)
Example EX_roundtrip_oddlen :
  forall wire h0,
    mk_header 5353 9999 (lenN EX_data_odd) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 EX_src EX_dst 5353 9999 EX_data_odd = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 EX_src EX_dst wire
      = Ok (to_word16 5353, to_word16 9999, EX_data_odd).
Proof.
  intros wire h0 Hmk Henc.
  eapply decode_encode_roundtrip_ipv4_defaults_reject_nonzero16; eauto.
  change (9999 mod 65536 <> 0). cbv; discriminate.
Qed.

(* Multicast destination suppresses ICMP. *)
Definition EX_multicast_dst := mkIPv4 224 0 0 1.

Example EX_no_icmp_for_multicast :
  forall has_listener,
    should_send_icmp defaults_ipv4 EX_multicast_dst = false.
Proof.
  intro has_listener.
  unfold should_send_icmp, is_multicast_ipv4, EX_multicast_dst.
  simpl. reflexivity.
Qed.

(* Example documenting RFC 768 "source port optional (0 permitted)". *)
Example EX_roundtrip_src_port_zero :
  forall wire h0,
    mk_header 0 9999 (lenN EX_data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 EX_src EX_dst 0 9999 EX_data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 EX_src EX_DST wire
      = Ok (to_word16 0, to_word16 9999, EX_data).
Proof.
  intros wire h0 Hmk Henc.
  apply (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16
           EX_src EX_DST 0 9999 EX_data wire h0).
  - change (9999 mod 65536 <> 0). cbv; discriminate.
  - exact Hmk.
  - exact Henc.
Qed.
