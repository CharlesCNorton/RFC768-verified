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

(* Helper lemmas to avoid computing checksums *)

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

(*
===============================================================================
Fixed UDP/IPv4 instance: round‑trip and ancillary properties
===============================================================================
*)

Section UDP_Fixed_Instance.
  Open Scope N_scope.

  (* Fixed parameters. *)
  Definition ex_src := mkIPv4 192 0 2 1.
  Definition ex_dst := mkIPv4 192 0 2 99.
  Definition ex_sp  : word16 := 40000.
  Definition ex_dp  : word16 := 4242.
  Definition ex_payload : list byte := [1;2;3].

  (* Wire obtained from the encoder (defaults). *)
  Definition ex_wire : list byte :=
    match encode_udp_ipv4 defaults_ipv4 ex_src ex_dst ex_sp ex_dp ex_payload with
    | inl w  => w
    | inr _  => []
    end.

  Example ex_encode_ok :
    exists w,
      encode_udp_ipv4 defaults_ipv4 ex_src ex_dst ex_sp ex_dp ex_payload = Ok w.
  Proof. vm_compute. eexists; reflexivity. Qed.

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

  Definition no_listener (_:IPv4) (_:word16) : bool := false.

  Lemma ex_unicast : is_multicast_ipv4 ex_dst = false.
  Proof. vm_compute. reflexivity. Qed.

Example ex_icmp_advice :
  udp_complete_icmp_advice defaults_ipv4 no_listener ex_src ex_dst
     (decode_udp_ipv4_with_addrs defaults_ipv4 ex_src ex_dst ex_wire)
  = SendICMPDestUnreach ICMP_PORT_UNREACH.
Proof.
  unfold ex_wire.
  destruct ex_encode_ok as [w Hw]. rewrite Hw.
  replace (match Ok w with inl w0 => w0 | inr _ => [] end) with w by reflexivity.

  (* Existence of a header from the successful encode. *)
  assert (Hexists : exists h0, mk_header ex_sp ex_dp (lenN ex_payload) = Some h0).
  { unfold encode_udp_ipv4 in Hw.
    destruct (mk_header ex_sp ex_dp (lenN ex_payload)) as [h0|] eqn:Hmk; [now eexists|discriminate]. }
  destruct Hexists as [h0 Hmk].

  (* Destination port is nonzero in 16 bits. *)
  assert (Hdp_lt : ex_dp < two16) by (cbv [ex_dp two16]; lia).
  assert (Hdp_nz : to_word16 ex_dp <> 0).
  { intro Heq. rewrite (to_word16_id_if_lt ex_dp Hdp_lt) in Heq; cbv [ex_dp] in Heq; discriminate. }

  (* Collapse decode via the round‑trip theorem. *)
  pose proof (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16
                ex_src ex_dst ex_sp ex_dp ex_payload w h0 Hdp_nz Hmk Hw) as Hrt.

  (* Conclude the advice decision. *)
  unfold decode_udp_ipv4_with_addrs. cbn. rewrite Hrt. cbn.
  cbn [udp_complete_icmp_advice should_send_icmp udp_rx_icmp_advice defaults_ipv4].
  reflexivity.
Qed.

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

(** ****************************************************************************
    Decoder → Encoder completeness (defaults, StrictEq), modulo checksum
    canonicalization.  If the default decoder accepts a wire [w] as
    [(sp,dp,data)], then re‑encoding [(sp,dp,data)] under the same defaults
    yields either exactly [w] (non‑zero checksum case) or the canonicalized
    wire that differs only in the checksum field (zero‑checksum case).
    **************************************************************************** *)

Section UDP_Decode_Encode_Completeness.
  Open Scope N_scope.

(** * §1. Header parsing and numeric well-formedness *)

(** Well-formedness of the 8-bit predicate. *)
Lemma is_byte_lt_two8 :
  forall b, is_byte b = true -> b < two8.
Proof.
  intros b Hb.
  unfold is_byte in Hb.
  apply N.ltb_lt in Hb.
  exact Hb.
Qed.

(** If both octets are within [0,256), the big-endian 16-bit value is < 2^16. *)
Lemma word16_of_be_lt_two16_of_is_byte :
  forall hi lo,
    is_byte hi = true -> is_byte lo = true ->
    word16_of_be hi lo < two16.
Proof.
  intros hi lo Hhi Hlo.
  apply is_byte_lt_two8 in Hhi.
  apply is_byte_lt_two8 in Hlo.
  unfold word16_of_be, two8, two16 in *.
  lia.
Qed.

(** Any header produced by [parse_header] satisfies [header_norm]. *)
Lemma header_norm_of_parse_success :
  forall w h rest,
    parse_header w = Some (h, rest) -> header_norm h.
Proof.
  intros w h rest H.
  unfold parse_header in H.
  (* Decompose the 8 header octets *)
  destruct w as [|s0 w]; try discriminate.
  destruct w as [|s1 w]; try discriminate.
  destruct w as [|d0 w]; try discriminate.
  destruct w as [|d1 w]; try discriminate.
  destruct w as [|l0 w]; try discriminate.
  destruct w as [|l1 w]; try discriminate.
  destruct w as [|c0 w]; try discriminate.
  destruct w as [|c1 rest0]; try discriminate.
  cbn in H.

  (* Split on the [forallb] range guard *)
  destruct (forallb is_byte [s0; s1; d0; d1; l0; l1; c0; c1]) eqn:Hall.
  - (* Guard true: reduce and invert *)
    simpl in Hall.
    rewrite Hall in H. cbn in H. inversion H; subst h rest; clear H.

    (* Extract per-octet range facts from the and-chained guard *)
    revert Hall; simpl; intro Hall.
    apply Bool.andb_true_iff in Hall as [Hs0 Hall].
    apply Bool.andb_true_iff in Hall as [Hs1 Hall].
    apply Bool.andb_true_iff in Hall as [Hd0 Hall].
    apply Bool.andb_true_iff in Hall as [Hd1 Hall].
    apply Bool.andb_true_iff in Hall as [Hl0 Hall].
    apply Bool.andb_true_iff in Hall as [Hl1 Hall].
    apply Bool.andb_true_iff in Hall as [Hc0 Hall].
    apply Bool.andb_true_iff in Hall as [Hc1 _].

    (* Each 16-bit field is < 2^16 *)
    unfold header_norm; simpl.
    repeat split;
      eapply word16_of_be_lt_two16_of_is_byte; eauto.
  - (* Guard false: cannot produce [Some] *)
    simpl in Hall. rewrite Hall in H. discriminate.
Qed.

(** Performance note: prevent Coq from unfolding large definitions incidentally. *)
Local Opaque
  add16_ones sum16 to_word16
  checksum_words_ipv4 compute_udp_checksum_ipv4
  cksum16 complement16
  bytes_of_words16_be words16_of_bytes_be be16_of_word16 word16_of_be
  ipv4_words pseudo_header_v4.

(** * §2. Algebraic facts for the Internet checksum (one’s-complement) *)

(** Verifier truth reduces to a single end-around carry equation. *)
Lemma verify_add16_mask16 :
  forall ipS ipD h data,
    header_norm h ->
    verify_checksum_ipv4 ipS ipD h data = true ->
    add16_ones (sum16 (checksum_words_ipv4 ipS ipD h data)) (checksum h) = mask16.
Proof.
  intros ipS ipD h data Hn Hver.
  unfold verify_checksum_ipv4 in Hver.
  apply N.eqb_eq in Hver.                      (* sum16 (ws ++ [ck]) = mask16 *)
  set (ws := checksum_words_ipv4 ipS ipD h data).
  set (ck := checksum h).
  pose proof (sum16_app_single ws ck) as Happ. (* sum16 (ws ++ [ck]) = add16_ones (sum16 ws) (to_word16 ck) *)
  destruct Hn as [_ [_ [_ Hck_lt]]].           (* ck < 2^16 *)
  rewrite (to_word16_id_if_lt ck Hck_lt) in Happ.
  exact (eq_trans (eq_sym Happ) Hver).
Qed.

(** If [add16_ones mask16 ck = mask16] and [ck ≠ 0], then [ck = 0xFFFF]. *)
Lemma add16_ones_mask16_nonzero_eq_mask16 :
  forall ck,
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

(** Decomposition of the “sum = 0xFFFF” constraint for [add16_ones]. *)

(** (i) No-overflow case: equality to [mask16] fixes [ck = mask16 − s]. *)
Lemma add16_ones_eq_mask16_no_overflow :
  forall s ck,
    s + ck < two16 ->
    add16_ones s ck = mask16 ->
    ck = mask16 - s.
Proof.
  intros s ck Hlt H.
  rewrite (add16_ones_no_overflow s ck Hlt) in H.
  unfold two16, mask16 in *; lia.
Qed.

(** (ii) Overflow case: equality to [mask16] forces [s + ck = 2·mask16]. *)
Lemma add16_ones_eq_mask16_overflow_sum :
  forall s ck,
    two16 <= s + ck ->
    add16_ones s ck = mask16 ->
    s + ck = mask16 + mask16.
Proof.
  intros s ck Hge H.
  rewrite (add16_ones_overflow_le s ck Hge) in H.
  unfold two16, mask16 in *; lia.
Qed.

(** (iii) Under [s,ck < 2^16], [s + ck = 2·mask16] implies [s = ck = mask16]. *)
Lemma sum_eq_2mask16_bounds_force_mask16 :
  forall s ck,
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

(** (iv) If [add16_ones s ck = mask16] with [s ≠ mask16], then [ck = mask16 − s]. *)
Lemma add16_ones_eq_mask16_nonallones :
  forall s ck,
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

(** (iv′) Renamed variant used in subsequent proofs. *)
Lemma add16_ones_eq_mask16_complement :
  forall s ck,
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

(** Auxiliary: if [mask16 − s ≠ 0], then [s ≠ mask16]. *)
Lemma mask16_sub_nonzero_implies_neq :
  forall s, mask16 - s <> 0 -> s <> mask16.
Proof.
  intros s Hnz Heq. subst s.
  rewrite N.sub_diag in Hnz. contradiction.
Qed.

(** * §3. Verifier → canonical checksum equality (split by the computed branch) *)

(** Branch “computed checksum == 0”: TX field must be [0xFFFF]. *)
Lemma verify_ck_eq_mask16_when_cksum_zero :
  forall ipS ipD h data,
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

(** Branch “computed checksum != 0”: TX field equals that value. *)
Lemma verify_ck_eq_cksum16_when_cksum_nonzero :
  forall ipS ipD h data,
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
  Opaque cksum16 complement16.
Qed.

(** Single-point corollary that dispatches on the computed checksum branch. *)
Lemma verify_implies_checksum_equals_computed_nonzero_split :
  forall ipS ipD h data,
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

(** * §4. Parser/serializer determinism on serializer output *)

(** On bytes produced by [udp_header_bytes], a successful parse is unique. *)
Lemma parse_header_bytes_of_header_norm_inv :
  forall h rest h' rest',
    header_norm h ->
    parse_header (udp_header_bytes h ++ rest) = Some (h', rest') ->
    h' = h /\ rest' = rest.
Proof.
  intros h rest h' rest' Hnorm Hparse.
  rewrite (parse_header_bytes_of_header_norm h rest Hnorm) in Hparse.
  inversion Hparse; subst; split; reflexivity.
Qed.

Section UDP_Decode_Encode_Completeness.
  Open Scope N_scope.

  (** Auxiliary: round‑trip on bytes for BE16 at the byte level. *)
Lemma be16_of_word16_word16_of_be_id :
 forall b0 b1,
   is_byte b0 = true -> is_byte b1 = true ->
   be16_of_word16 (word16_of_be b0 b1) = (b0, b1).
Proof.
 intros b0 b1 Hb0 Hb1.
 pose proof (is_byte_lt_two8 _ Hb0) as Hb0_lt.
 pose proof (is_byte_lt_two8 _ Hb1) as Hb1_lt.
 Transparent be16_of_word16 word16_of_be.
 unfold be16_of_word16, word16_of_be.
 
 assert (two8_ne : two8 <> 0) by (unfold two8; lia).
 
 (* Low octet *)
 assert (Hlo : (b0 * two8 + b1) mod two8 = b1).
 { rewrite N.add_mod by exact two8_ne.
   rewrite N.mod_mul by exact two8_ne.
   rewrite N.add_0_l.
   rewrite N.mod_mod by exact two8_ne.
   now rewrite N.mod_small by exact Hb1_lt. }
 
 (* High octet *)
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

  (** Any successful parse reveals that the wire is exactly header‑bytes ++ rest. *)
Lemma parse_header_shape_bytes :
  forall w h rest,
    parse_header w = Some (h, rest) ->
    w = udp_header_bytes h ++ rest.
Proof.
  intros w h rest H.
  unfold parse_header in H.
  (* Decompose the first eight bytes of [w]. *)
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
  - (* Case: Hall = true *)
    unfold header8 in Hall.
    simpl in Hall.
    rewrite Hall in H.
    simpl in H.
    inversion H; subst h rest0; clear H.
    (* Extract byte‑range facts from [Hall]. *)
    cbn in Hall.
    repeat (apply Bool.andb_true_iff in Hall as [? Hall]).
    (* Equality of the first 8 bytes with [udp_header_bytes h]. *)
    unfold udp_header_bytes, udp_header_words; cbn.
    Transparent bytes_of_words16_be to_word16.
    simpl.
    (* Need to show to_word16 doesn't change values already < two16 *)
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
  - (* Case: Hall = false *)
    unfold header8 in Hall.
    simpl in Hall.
    rewrite Hall in H.
    simpl in H.
    discriminate H.
  Opaque bytes_of_words16_be to_word16.
Qed.

Lemma decode_defaults_nonzero_analysis :
 forall ipS ipD w sp dp data h rest,
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
 
 (* Invariants extracted from the decoding path (defaults = StrictEq). *)
 assert (Hnorm : header_norm h) by (apply header_norm_of_parse_success with (w:=w) (rest:=rest); exact Hparse).
 
 (* The decode path under defaults with non‑zero checksum must go through verification
    and StrictEq length equality; from this we get L = 8 + |data| and rest = data. *)
 unfold decode_udp_ipv4 in Hdec.
 rewrite Hparse in Hdec.
 
 (* Destination‑port‑0 is rejected by defaults, so dst_port h must be nonzero *)
 assert (Epol : dst_port0_policy defaults_ipv4 = Reject) by reflexivity.
 rewrite Epol in Hdec.
 destruct (N.eqb (dst_port h) 0) eqn:Edp0; [discriminate|].
 
 (* Name length quantities. *)
 set (Nbytes := lenN w) in *.
 set (L := length16 h) in *.
 
 (* Under StrictEq we must have Nbytes = L; produce that equality. *)
 assert (Emode : length_rx_mode defaults_ipv4 = StrictEq) by reflexivity.
 rewrite Emode in Hdec.
 
 (* Discharge the length guards: L ≥ 8 and Nbytes ≥ L, and finally Nbytes = L. *)
 destruct (L <? 8) eqn:EL8; [discriminate|].
 destruct (Nbytes <? L) eqn:ENbL; [discriminate|].
 destruct (N.eqb Nbytes L) eqn:EEq; [|discriminate].
 
 (* We know checksum h ≠ 0, so we're in the verify branch *)
 rewrite Hck_nz in Hdec.
 
 (* From the successful branch we learn that the verifier succeeded *)
 remember (take (N.to_nat (L - 8)) rest) as delivered.
 destruct (verify_checksum_ipv4 ipS ipD h delivered) eqn:Hver; [|discriminate].
 inversion Hdec; subst sp dp data; clear Hdec.
 
 (* Under StrictEq and [Nbytes = L], the delivered slice is the whole [rest]. *)
 assert (Hlen_eq : Nbytes = L) by (apply N.eqb_eq; exact EEq).
 assert (Hrest_eq : delivered = rest).
 { subst delivered Nbytes L.
   replace (length16 h - 8) with (lenN rest).
   2: { pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
        rewrite Hw in Hlen_eq.
        rewrite lenN_app, lenN_udp_header_bytes_8 in Hlen_eq. lia. }
   rewrite N_to_nat_lenN, take_length_id; reflexivity. }
 
 (* Collect all the facts *)
 split; [exact Hnorm|].
 split; [reflexivity|].
 split; [exact Hlen_eq|].
 split. { apply N.ltb_ge in EL8. fold L in EL8. lia. }
 split; [exact Hrest_eq|].
 split; [reflexivity|].
 split; [reflexivity|].
 rewrite <- Hrest_eq; exact Hver.
Qed.

Lemma encode_setup_for_defaults_nonzero :
  forall ipS ipD w h rest,
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
  
  (* Build the encoder's header and show it coincides with [h]. *)
  assert (Hmk_ok : 8 + lenN rest <= mask16).
  { destruct Hnorm as [_ [_ [HL_lt _]]].
    assert (HL_eq : length16 h = 8 + lenN rest).
    { pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
      rewrite Hw in Hlen_eq.
      rewrite lenN_app, lenN_udp_header_bytes_8 in Hlen_eq. lia. }
    rewrite <- HL_eq. unfold mask16, two16 in *. lia. }
  
  (* Replace [to_word16 (8 + lenN rest)] by [length16 h] *)
  assert (HL_eq' : length16 h = 8 + lenN rest).
  { pose proof (parse_header_shape_bytes w h rest Hparse) as Hw.
    rewrite Hw in Hlen_eq.
    rewrite lenN_app, lenN_udp_header_bytes_8 in Hlen_eq. lia. }
  
  (* mk_header succeeds on (src_port h, dst_port h, |rest|) *)
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
  
  (* Show encode produces the expected wire *)
  unfold encode_udp_ipv4.
  rewrite Hmk.
  change (checksum_tx_mode defaults_ipv4) with WithChecksum.
  
  (* Build the header with computed checksum *)
  set (h0 := {| src_port := to_word16 (src_port h);
                dst_port := to_word16 (dst_port h);
                length16 := to_word16 (8 + lenN rest);
                checksum := 0 |}).
  
  (* Simplify using [to_word16_id_if_lt] from [header_norm] *)
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

Lemma checksum_invariant_with_zero :
 forall ipS ipD h rest,
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

Lemma encode_wire_equality_nonzero :
 forall ipS ipD w h rest,
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
 
 (* Show the computed checksum equals h's checksum *)
 assert (Hck_eq : checksum h = compute_udp_checksum_ipv4 ipS ipD h rest).
 { apply verify_implies_checksum_equals_computed_nonzero_split; assumption. }
 
 rewrite <- (checksum_invariant_with_zero ipS ipD h rest).
 rewrite <- Hck_eq.
 rewrite (parse_header_shape_bytes w h rest Hparse).
 reflexivity.
Qed.

Theorem decode_encode_completeness_defaults_nonzero_ck :
  forall ipS ipD w sp dp data h rest,
    decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
    parse_header w = Some (h, rest) ->
    N.eqb (checksum h) 0 = false ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok w.
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck_nz.
  
  (* Apply the analysis lemma *)
  pose proof (decode_defaults_nonzero_analysis ipS ipD w sp dp data h rest 
              Hdec Hparse Hck_nz) as 
              [Hnorm [Edp0 [Hlen_eq [HL_ge8 [Hdata_eq [Hsp_eq [Hdp_eq Hver]]]]]]].
  
  subst sp dp data.
  
  (* Apply the encoding setup lemma *)
  pose proof (encode_setup_for_defaults_nonzero ipS ipD w h rest 
              Hparse Hnorm Hlen_eq) as 
              [Hmk_ok [HL_eq' [Hmk Henc_shape]]].
  
  rewrite Henc_shape.
  f_equal.
  apply encode_wire_equality_nonzero; assumption.
Qed.

Corollary decode_encode_exact_match_nonzero :
  forall ipS ipD w sp dp data h rest,
    decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
    parse_header w = Some (h, rest) ->
    N.eqb (checksum h) 0 = false ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok w.
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck_nz.
  apply decode_encode_completeness_defaults_nonzero_ck with h rest; assumption.
Qed.

(** Canonicalized wire for defaults: same header fields, checksum replaced by the
    computed (non-zero) UDP checksum over the pseudo-header, header-with-zero,
    and data. *)
Definition canonical_wire_defaults (ipS ipD:IPv4) (h:UdpHeader) (rest:list byte)
  : list byte :=
  udp_header_bytes
    {| src_port := src_port h;
       dst_port := dst_port h;
       length16 := length16 h;
       checksum := compute_udp_checksum_ipv4 ipS ipD h rest |}
  ++ rest.

(** Decoder-path analysis for the defaults when the transmitted checksum is zero.
    This mirrors [decode_defaults_nonzero_analysis] but does not produce a
    verifier fact (the defaults accept checksum=0 without verification). *)
Lemma decode_defaults_zero_analysis :
 forall ipS ipD w sp dp data h rest,
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
 rewrite Hck0 in Hdec.                       (* zero-checksum branch *)
 (* defaults: ValidOrZero + ZeroAlwaysAccept *)
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

(** Completeness for the zero-checksum case: re-encoding yields the canonicalized
    wire that differs from the original only in the checksum field. *)
Theorem decode_encode_completeness_defaults_zero_ck :
  forall ipS ipD w sp dp data h rest,
    decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
    parse_header w = Some (h, rest) ->
    N.eqb (checksum h) 0 = true ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data
      = Ok (canonical_wire_defaults ipS ipD h rest).
Proof.
  intros ipS ipD w sp dp data h rest Hdec Hparse Hck0.
  
  (* Analyze the decode path and substitute [sp,dp,data]. *)
  pose proof (decode_defaults_zero_analysis ipS ipD w sp dp data h rest
                Hdec Hparse Hck0)
    as [Hnorm [Edp0 [Hlen_eq [_ [Hdata_eq [Hsp_eq Hdp_eq]]]]]].
  subst sp dp data.

  (* Set up the encoder shape (mk_header success and WithChecksum branch). *)
  pose proof (encode_setup_for_defaults_nonzero ipS ipD w h rest
                Hparse Hnorm Hlen_eq)
    as [Hmk_ok [_ [Hmk Hshape]]].

  (* The encoder produces the canonical wire *)
  unfold canonical_wire_defaults.
  rewrite Hshape.
  (* Both checksums are equal by the invariant lemma *)
  rewrite <- (checksum_invariant_with_zero ipS ipD h rest).
  reflexivity.
Qed.

Lemma canonical_wire_equals_original_nonzero :
  forall ipS ipD w sp dp data h rest,
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
  
  (* The canonical wire has computed checksum, original has checksum h *)
  assert (Hck_eq : checksum h = compute_udp_checksum_ipv4 ipS ipD h rest).
  { apply verify_implies_checksum_equals_computed_nonzero_split; assumption. }
  
  (* Build the equality step by step *)
  rewrite <- Hck_eq.
  symmetry.
  apply (parse_header_shape_bytes w h rest Hparse).
Qed.

(** Consolidated completeness (defaults, StrictEq).
    Always returns the canonicalized wire; in the non-zero case, it is equal to
    the original wire. *)
Theorem decode_encode_completeness_defaults :
  forall ipS ipD w sp dp data h rest,
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
  - (* checksum = 0: produce canonicalized wire; equality to [w] not claimed *)
    split.
    + eapply decode_encode_completeness_defaults_zero_ck; eauto.
    + intros Hcontra. discriminate.
  - (* checksum ≠ 0: exact equality and canonicalization coincide *)
    split.
    + (* show encode returns Ok (canonical wire), via exact-equality to [w] *)
      pose proof (decode_encode_completeness_defaults_nonzero_ck
                    ipS ipD w sp dp data h rest Hdec Hparse Hcz) as Henc_eq.
      rewrite Henc_eq.
      f_equal.
      symmetry.
      apply canonical_wire_equals_original_nonzero with sp dp data; assumption.
    + (* the promised equality canonical_wire = w *)
      intros _.
      apply canonical_wire_equals_original_nonzero with sp dp data; assumption.
Qed.

(** Corollary: The encoder always produces canonical wires, and these are
    exactly the wires accepted by the decoder. *)
Corollary udp_canonicalization :
  forall ipS ipD w sp dp data,
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
  (* Get the header from the successful decode *)
  assert (Hdec_copy := Hdec).
  unfold decode_udp_ipv4 in Hdec_copy.
  destruct (parse_header w) as [[h rest]|] eqn:Hparse; [|discriminate Hdec_copy].
  exists h, rest.
  split; [reflexivity|].
  
  (* Apply the completeness theorem *)
  pose proof (decode_encode_completeness_defaults ipS ipD w sp dp data h rest 
              Hdec Hparse) as [Henc Heq].
  
  (* Get data = rest from the decoder analysis *)
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

Corollary decode_encode_completeness_defaults_no_parse :
  forall ipS ipD w sp dp data,
    decode_udp_ipv4 defaults_ipv4 ipS ipD w = Ok (sp, dp, data) ->
    exists h rest,
      parse_header w = Some (h, rest) /\
      encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data
        = Ok (canonical_wire_defaults ipS ipD h rest) /\
      (N.eqb (checksum h) 0 = false ->
         canonical_wire_defaults ipS ipD h rest = w).
Proof.
  intros ipS ipD w sp dp data Hdec.
  (* The decoder starts by parsing; expose that match *)
  assert (Hdec_copy := Hdec).
  unfold decode_udp_ipv4 in Hdec_copy.
  destruct (parse_header w) as [(h,rest)|] eqn:Hparse.
  - (* Successful parse *)
    exists h, rest. 
    split; [reflexivity|].
    exact (decode_encode_completeness_defaults ipS ipD w sp dp data h rest Hdec Hparse).
  - (* Failed parse - contradicts successful decode *)
    discriminate Hdec_copy.
Qed.

(** ****************************************************************************
    Conformance lemmas): injectivity, oversize monotonicity, and
    verification stability under AcceptShorter
    **************************************************************************** *)

Section UDP_R5_Conformance.
  Open Scope N_scope.

  (** * R5a. Injectivity of [udp_header_bytes] under [header_norm] *)

  Lemma udp_header_bytes_inj :
    forall h1 h2,
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

  (** * R5b. Encoder monotonicity for size: oversize iff [8 + lenN data > mask16] *)

Lemma encode_oversize_iff :
  forall cfg ipS ipD sp dp data,
    encode_udp_ipv4 cfg ipS ipD sp dp data = Err Oversize <->
    8 + lenN data > mask16.
Proof.
  intros cfg ipS ipD sp dp data; split; intro H.
  - (* -> *)
    unfold encode_udp_ipv4 in H.
    destruct (mk_header sp dp (lenN data)) as [h0|] eqn:Hmk; [discriminate|].
    unfold mk_header in Hmk.
    destruct (8 + lenN data <=? mask16) eqn:Hleb; [discriminate|].
    (* From [leb=false], deduce strict inequality *)
    apply N.leb_gt in Hleb. lia.
  - (* <- *)
    unfold encode_udp_ipv4.
    unfold mk_header.
    destruct (8 + lenN data <=? mask16) eqn:Hleb.
    + apply N.leb_le in Hleb. lia.
    + reflexivity.
Qed.

  (** * R5c. Verification stability under AcceptShorter:
          the verifier depends only on the [L−8]-bounded prefix *)

Lemma take_len_app :
  forall (A:Type) (xs ys:list A),
    take (List.length xs) (xs ++ ys) = xs.
Proof.
  intros A xs; induction xs as [|x xs IH]; intros ys; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma take_lenN_app :
  forall (A:Type) (xs ys:list A),
    take (N.to_nat (lenN xs)) (xs ++ ys) = xs.
Proof.
  intros A xs ys. rewrite N_to_nat_lenN. apply take_len_app.
Qed.

Lemma verify_prefix_stability :
  forall ipS ipD h data tail,
    length16 h = 8 + lenN data ->
    verify_checksum_ipv4 ipS ipD h
      (take (N.to_nat (length16 h - 8)) (data ++ tail))
    = verify_checksum_ipv4 ipS ipD h data.
Proof.
  intros ipS ipD h data tail HL.
  rewrite HL, N_add_sub_cancel_l, N_to_nat_lenN.
  rewrite take_len_app. reflexivity.
Qed.

  Corollary verify_prefix_stability_true :
    forall ipS ipD h data tail,
      length16 h = 8 + lenN data ->
      verify_checksum_ipv4 ipS ipD h data = true ->
      verify_checksum_ipv4 ipS ipD h
        (take (N.to_nat (length16 h - 8)) (data ++ tail)) = true.
  Proof.
    intros; rewrite verify_prefix_stability by assumption; assumption.
  Qed.

End UDP_R5_Conformance.

(** ****************************************************************************
    AcceptShorter surplus‑octet case
    ----------------------------------------------------------------------------
    In AcceptShorterIP mode, if IP presents a UDP datagram whose payload is
    [data ++ tail] but the UDP Length field equals [8 + |data|], then the
    decoder accepts the datagram and delivers exactly [data], ignoring [tail].
    Acceptance holds:
      • unconditionally when the transmitted checksum is 0 (defaults accept 0),
      • or when the verifier succeeds on [data] (non‑zero checksum).
    **************************************************************************** *)

Section UDP_R2_AcceptShorter_Surplus.
  Open Scope N_scope.

(** A small helper: compute the delivered slice under the hypothesis
    [length16 h = 8 + lenN data] and [rest = data ++ tail]. *)
Lemma delivered_eq_data_from_L :
  forall h (data tail : list byte),
    length16 h = 8 + lenN data ->
    take (N.to_nat (length16 h - 8)) (data ++ tail) = data.
Proof.
  intros h data tail HL.
  rewrite HL, N_add_sub_cancel_l, N_to_nat_lenN.
  apply take_len_app.
Qed.

(** Helper: Length guards for AcceptShorter with surplus *)
Lemma acceptShorter_length_guards :
 forall w h data tail,
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

(** Main acceptance lemma for defaults with AcceptShorterIP and dp≠0. *)
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
  
  (* Get length guards *)
  destruct (acceptShorter_length_guards w h data tail Hparse HL) as [EL8 ENbL].
  
  (* Evaluate decoder *)
  unfold decode_udp_ipv4. rewrite Hparse.
  change (dst_port0_policy defaults_ipv4_acceptShorter) with Reject.
  rewrite Hdp_nz, EL8, ENbL.
  change (length_rx_mode defaults_ipv4_acceptShorter) with AcceptShorterIP.
  
  destruct Hck_cases as [Hck0 | [HckNZ Hver_data]].
  - (* checksum==0 *)
    rewrite Hck0.
    change (checksum_rx_mode defaults_ipv4_acceptShorter) with ValidOrZero.
    change (zero_checksum_allowed defaults_ipv4_acceptShorter ipD) with true.
    rewrite (delivered_eq_data_from_L h data tail HL).
    reflexivity.
  - (* checksum!=0 *)
    rewrite HckNZ.
    rewrite (delivered_eq_data_from_L h data tail HL), Hver_data.
    reflexivity.
Qed.

(** Variant with Allow0 policy: no premise on [dst_port h]. *)
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
  
  (* Get length guards *)
  destruct (acceptShorter_length_guards w h data tail Hparse HL) as [EL8 ENbL].
  
  (* Evaluate decoder *)
  unfold decode_udp_ipv4. rewrite Hparse.
  change (dst_port0_policy defaults_ipv4_allow0_acceptShorter) with Allow.
  rewrite EL8, ENbL.
  change (length_rx_mode defaults_ipv4_allow0_acceptShorter) with AcceptShorterIP.
  
  destruct Hck_cases as [Hck0 | [HckNZ Hver_data]].
  - (* checksum==0 *)
    rewrite Hck0.
    change (checksum_rx_mode defaults_ipv4_allow0_acceptShorter) with ValidOrZero.
    change (zero_checksum_allowed defaults_ipv4_allow0_acceptShorter ipD) with true.
    rewrite (delivered_eq_data_from_L h data tail HL).
    reflexivity.
  - (* checksum!=0 *)
    rewrite HckNZ.
    rewrite (delivered_eq_data_from_L h data tail HL), Hver_data.
    reflexivity.
Qed.

End UDP_R2_AcceptShorter_Surplus.

(** ****************************************************************************
    R3: Minimal ICMP suppression matrix via IP metadata (additive interface)
    ----------------------------------------------------------------------------
    We extend the advisory interface with a small record of IP-derived flags
    and define a wrapper that enforces the standard suppressions before
    delegating to [udp_complete_icmp_advice].
    **************************************************************************** *)

Section UDP_R3_ICMP_Suppression.
  Open Scope N_scope.

  (** Minimal metadata required from IP / link. *)
  Record IPMeta := {
    ll_broadcast     : bool;  (* link-layer broadcast frame *)
    initial_fragment : bool;  (* true iff packet is an initial fragment *)
    src_is_unicast   : bool   (* false for invalid/non-unicast sources *)
  }.

  (** Suppression wrapper: any suppressing condition forces [NoAdvice];
      otherwise defer to the existing [udp_complete_icmp_advice]. *)
  Definition udp_complete_icmp_advice_meta
    (cfg:Config) (meta:IPMeta)
    (has_listener: IPv4 -> word16 -> bool)
    (src_ip dst_ip:IPv4)
    (res: result UdpDeliver DecodeError) : RxAdvice :=
    if negb meta.(src_is_unicast) then NoAdvice else
    if negb meta.(initial_fragment) then NoAdvice else
    if        meta.(ll_broadcast)   then NoAdvice else
      udp_complete_icmp_advice cfg has_listener src_ip dst_ip res.

  (** Elementary suppressions. *)
  Lemma icmp_suppression_src_not_unicast :
    forall cfg meta has_listener src dst res,
      meta.(src_is_unicast) = false ->
      udp_complete_icmp_advice_meta cfg meta has_listener src dst res = NoAdvice.
  Proof.
    intros; unfold udp_complete_icmp_advice_meta.
    now rewrite H.
  Qed.

  Lemma icmp_suppression_non_initial_fragment :
    forall cfg meta has_listener src dst res,
      meta.(initial_fragment) = false ->
      udp_complete_icmp_advice_meta cfg meta has_listener src dst res = NoAdvice.
  Proof.
    intros; unfold udp_complete_icmp_advice_meta.
    destruct (meta.(src_is_unicast)); [now rewrite H|reflexivity].
  Qed.

  Lemma icmp_suppression_ll_broadcast :
    forall cfg meta has_listener src dst res,
      meta.(ll_broadcast) = true ->
      udp_complete_icmp_advice_meta cfg meta has_listener src dst res = NoAdvice.
  Proof.
    intros; unfold udp_complete_icmp_advice_meta.
    destruct (meta.(src_is_unicast)); [|reflexivity].
    destruct (meta.(initial_fragment)); [now rewrite H|reflexivity].
  Qed.

  (** When meta says “OK to notify”, the wrapper reduces to the base advice. *)
  Lemma icmp_meta_reduces_to_base :
    forall cfg meta has_listener src dst res,
      meta.(src_is_unicast) = true ->
      meta.(initial_fragment) = true ->
      meta.(ll_broadcast) = false ->
      udp_complete_icmp_advice_meta cfg meta has_listener src dst res
        = udp_complete_icmp_advice cfg has_listener src dst res.
  Proof.
    intros; unfold udp_complete_icmp_advice_meta.
    now rewrite H, H0, H1.
  Qed.

  (** …and if host policy says “send ICMP”, it further reduces to [udp_rx_icmp_advice]. *)
  Lemma icmp_meta_reduces_to_rx_when_send :
    forall cfg meta has_listener src dst res,
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

(** Example corollary: port-unreachable with metadata, proved directly. *)
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
  (* Reduce meta-wrapper to base advice under “OK to notify” conditions. *)
  rewrite (icmp_meta_reduces_to_rx_when_send
             defaults_ipv4 meta has_listener ipS ipD
             (decode_udp_ipv4_with_addrs defaults_ipv4 ipS ipD wire)
             Hun Hin Hll Hsend).
  (* Inline the base advice on the successful decode result. *)
  unfold udp_rx_icmp_advice, decode_udp_ipv4_with_addrs.
  rewrite Hdec. cbn.
  rewrite Hnol. reflexivity.
Qed.

End UDP_R3_ICMP_Suppression.

(** ****************************************************************************
    R4: Source-address screening (additive wrapper)
    ----------------------------------------------------------------------------
    UDP does not itself validate IP source addresses; per RFC 1122 invalid or
    non‑unicast sources should be dropped without eliciting ICMP.  We provide a
    thin wrapper that (i) screens by a meta flag and (ii) leaves existing proofs
    intact.  When screening succeeds, the wrapper preserves successful decodes;
    when it fails, the result is [None] and—via the R3 wrapper—ICMP is suppressed.
    **************************************************************************** *)

Section UDP_R4_Source_Screening.
  Open Scope N_scope.

  (** Screened decode: [Some d] iff [src_is_unicast] and the base decode succeeds. *)
  Definition udp_decode_with_addrs_screened
    (cfg:Config) (meta:IPMeta)
    (src_ip dst_ip:IPv4) (wire:list byte) : option UdpDeliver :=
    if meta.(src_is_unicast)
    then match decode_udp_ipv4_with_addrs cfg src_ip dst_ip wire with
         | inl d  => Some d
         | inr _  => None
         end
    else None.

  (** Screening preserves success when the source is declared unicast. *)
  Lemma screened_preserves_success_with_addrs :
    forall cfg meta src dst wire d,
      meta.(src_is_unicast) = true ->
      decode_udp_ipv4_with_addrs cfg src dst wire = Ok d ->
      udp_decode_with_addrs_screened cfg meta src dst wire = Some d.
  Proof.
    intros cfg meta src dst wire d Hun Hdec.
    unfold udp_decode_with_addrs_screened.
    rewrite Hun, Hdec. reflexivity.
  Qed.

  (** Screening blocks delivery for non‑unicast sources. *)
  Lemma screened_blocks_invalid_with_addrs :
    forall cfg meta src dst wire,
      meta.(src_is_unicast) = false ->
      udp_decode_with_addrs_screened cfg meta src dst wire = None.
  Proof.
    intros cfg meta src dst wire Hnu.
    unfold udp_decode_with_addrs_screened. now rewrite Hnu.
  Qed.

  (** ICMP suppression follows immediately from the R3 meta wrapper. *)
  Lemma screened_no_icmp_on_invalid_source :
    forall cfg meta has_listener src dst wire,
      meta.(src_is_unicast) = false ->
      udp_complete_icmp_advice_meta cfg meta has_listener src dst
        (decode_udp_ipv4_with_addrs cfg src dst wire)
      = NoAdvice.
  Proof.
    intros cfg meta has_listener src dst wire Hnu.
    eapply icmp_suppression_src_not_unicast; exact Hnu.
  Qed.

  (** Illustration: preservation for a proven round‑trip (defaults, Reject). *)
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

  (** Illustration: preservation for a proven round‑trip (defaults, Allow0). *)
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

    (* Header actually used by the encoder (WithChecksum branch). *)
    set (h1 :=
          {| src_port := src_port h0
           ; dst_port := dst_port h0
           ; length16 := length16 h0
           ; checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).

    (* Encoder equality -> canonical wire shape. *)
    unfold encode_udp_ipv4 in Henc.
    rewrite Hmk in Henc.
    change (checksum_tx_mode defaults_ipv4_allow0) with WithChecksum in Henc.
    inversion Henc; subst wire; clear Henc.

    (* Decode that known wire. *)
    unfold decode_udp_ipv4.

    (* Parsing step on header bytes from the serializer. *)
    assert (Hnorm : header_norm h1)
      by (eapply header_norm_encode_h1; eauto).
    fold h1.
    replace (parse_header (udp_header_bytes h1 ++ data))
      with (Some (h1, data))
      by (symmetry; apply parse_header_bytes_of_header_norm; exact Hnorm).
    cbn.

    (* Policy and mode.*)
    change (dst_port0_policy defaults_ipv4_allow0) with Allow.
    cbn.

    (* Length bookkeeping: note the branch uses [length16 h0]. *)
    destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL0 _]]]]. (* HL0: length16 h0 = to_word16 (8 + |data|) *)
    assert (HL0id : length16 h0 = 8 + lenN data)
      by (rewrite HL0; now apply to_word16_id_if_le_mask).
    assert (HNbytes : lenN (udp_header_bytes h1 ++ data) = 8 + lenN data)
      by (apply lenN_wire_from_header_bytes).

    (* Manufacture boolean guard equalities explicitly. *)
    assert (EL8  : (8 + lenN data <? 8) = false) by (apply N.ltb_ge; lia).
    assert (ENbL : (lenN (udp_header_bytes h1 ++ data) <? 8 + lenN data) = false).
    { rewrite HNbytes. apply N.ltb_ge. lia. }
    assert (EEq  : (lenN (udp_header_bytes h1 ++ data) =? 8 + lenN data) = true).
    { rewrite HNbytes. apply N.eqb_eq. reflexivity. }

    (* Discharge the guards and StrictEq equality. *)
    rewrite HL0id.            (* turns L into 8 + |data| *)
    rewrite EL8.
    rewrite ENbL.
    change (length_rx_mode defaults_ipv4_allow0) with StrictEq.
    rewrite EEq.

    (* Non‑zero checksum on TX for IPv4. *)
    assert (Ecz : N.eqb (compute_udp_checksum_ipv4 ipS ipD h0 data) 0 = false)
      by (apply N.eqb_neq; apply compute_udp_checksum_ipv4_nonzero).
    rewrite Ecz.

    (* Verifier succeeds; delivered slice = data. *)
    assert (Hdel : take (N.to_nat (8 + lenN data - 8)) data = data).
    { rewrite N_add_sub_cancel_l, N_to_nat_lenN. apply take_length_id. }
    rewrite Hdel.
    rewrite (verify_checksum_ipv4_encode_ok ipS ipD sp dp data h0 h1 Hmk eq_refl).

    (* Wrap into UdpDeliver and reconcile fields. *)
    apply f_equal.
    destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp [Hdp _]]].
    now rewrite Hsp, Hdp.
  Qed.

End UDP_R4_Source_Screening.

(* ----------------------------------------------------------------------------
   Required examples (E1–E3): surplus handling, oversize boundary, ICMP suppression
   --------------------------------------------------------------------------*)

Section UDP_Required_Examples.
  Open Scope N_scope.

  (** E1. Surplus-octet behavior: accepted under AcceptShorter, rejected under StrictEq. *)

  Definition tail2 : list byte := [0; 0].

(* Positive case (AcceptShorter): appending surplus octets is accepted and the
   delivered payload equals the first L−8 octets (here, the original payload). *)
Example EX_surplus_acceptShorter :
  exists w,
    let w' := w ++ tail2 in
    decode_udp_ipv4 defaults_ipv4_acceptShorter ex_src ex_dst w'
      = Ok (to_word16 ex_sp, to_word16 ex_dp, ex_payload).
Proof.
  destruct ex_encode_ok as [w Hw]. exists w. cbv zeta.

  (* Extract mk_header success and define the header used by the encoder. *)
  assert (Hmk : exists h0, mk_header ex_sp ex_dp (lenN ex_payload) = Some h0).
  { unfold encode_udp_ipv4 in Hw.
    destruct (mk_header ex_sp ex_dp (lenN ex_payload)) as [h0|] eqn:E; [eauto|discriminate]. }
  destruct Hmk as [h0 Hmk].

  set (h1 :=
    {| src_port := src_port h0
     ; dst_port := dst_port h0
     ; length16 := length16 h0
     ; checksum := compute_udp_checksum_ipv4 ex_src ex_dst h0 ex_payload |}).

  (* Encoder wire shape. *)
  unfold encode_udp_ipv4 in Hw. rewrite Hmk in Hw.
  change (checksum_tx_mode defaults_ipv4) with WithChecksum in Hw.
  inversion Hw; subst w; clear Hw.

  (* Parsed headers produced by the serializer are normalized. *)
  assert (Hnorm : header_norm h1) by (eapply header_norm_encode_h1; eauto).

  (* Align the goal's RHS to the lemma's (src_port h1, dst_port h1, …). *)
  destruct (mk_header_ok _ _ _ _ Hmk) as [_ [Hsp0 [Hdp0' _]]].
  assert (Hsp1 : src_port h1 = to_word16 ex_sp) by (unfold h1; simpl; exact Hsp0).
  assert (Hdp1 : dst_port h1 = to_word16 ex_dp) by (unfold h1; simpl; exact Hdp0').
  rewrite <- Hsp1, <- Hdp1.

  (* Apply the AcceptShorter surplus lemma with the concrete surplus wire. *)
  eapply decode_acceptShorter_surplus_defaults_reject_nonzero16
    with (h := h1) (data := ex_payload) (tail := tail2).
  - (* parse_header w = Some (h1, ex_payload ++ tail2) *)
    (* w here is ((udp_header_bytes h1 ++ ex_payload) ++ tail2); reassociate. *)
    rewrite <- app_assoc.
    apply parse_header_bytes_of_header_norm; exact Hnorm.
  - (* (dst_port h1 =? 0) = false *)
    assert (Hdp_lt : ex_dp < two16) by (cbv [ex_dp two16]; lia).
    assert (Hdp_nz : to_word16 ex_dp <> 0).
    { intro Heq. rewrite (to_word16_id_if_lt _ Hdp_lt) in Heq.
      cbv [ex_dp] in Heq; discriminate. }
    apply N.eqb_neq. rewrite Hdp1. exact Hdp_nz.
  - (* length16 h1 = 8 + |ex_payload| *)
    eapply length16_h1_total_len; [exact Hmk|reflexivity].
  - (* checksum case: non-zero on TX and verifier holds on the prefix *)
    right. split.
    + unfold h1; simpl. apply N.eqb_neq, compute_udp_checksum_ipv4_nonzero.
    + pose proof (verify_checksum_ipv4_encode_ok
                    ex_src ex_dst ex_sp ex_dp ex_payload h0 h1 Hmk eq_refl) as Hver.
      exact Hver.
Qed.

(* Negative case (StrictEq): a surplus tail is rejected with BadLength. *)
Example EX_surplus_rejected_StrictEq :
  exists w,
    decode_udp_ipv4 defaults_ipv4 ex_src ex_dst (w ++ tail2) = Err BadLength.
Proof.
  destruct ex_encode_ok as [w Hw]. exists w.
  (* Recover mk_header success and the header used by the encoder. *)
  assert (Hmk : exists h0, mk_header ex_sp ex_dp (lenN ex_payload) = Some h0).
  { unfold encode_udp_ipv4 in Hw.
    destruct (mk_header ex_sp ex_dp (lenN ex_payload)) as [h0|] eqn:E; [eauto|discriminate]. }
  destruct Hmk as [h0 Hmk].
  set (h1 :=
    {| src_port := src_port h0
     ; dst_port := dst_port h0
     ; length16 := length16 h0
     ; checksum := compute_udp_checksum_ipv4 ex_src ex_dst h0 ex_payload |}).
  (* Encoder wire shape *)
  unfold encode_udp_ipv4 in Hw. rewrite Hmk in Hw.
  change (checksum_tx_mode defaults_ipv4) with WithChecksum in Hw.
  inversion Hw; subst w; clear Hw.
  (* Decode defaults (StrictEq) on surplus wire *)
  unfold decode_udp_ipv4.
  (* Parse step on serializer output with surplus tail *)
  assert (Hnorm : header_norm h1) by (eapply header_norm_encode_h1; eauto).
  fold h1.
  rewrite <- app_assoc.
  rewrite (parse_header_bytes_of_header_norm h1 (ex_payload ++ tail2) Hnorm).
  (* Port-zero policy = Reject, and destination port is non-zero *)
  change (dst_port0_policy defaults_ipv4) with Reject.
  assert (Hdp0 : (dst_port h1 =? 0) = false).
  { destruct (mk_header_ok _ _ _ _ Hmk) as [_ [_ [Hdp _]]].
    unfold h1; simpl. rewrite Hdp.
    change (to_word16 ex_dp =? 0) with ((ex_dp mod two16) =? 0).
    cbv [ex_dp two16]. reflexivity. }
  rewrite Hdp0.
  (* Length bookkeeping *)
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
  (* StrictEq mode and inequality Nbytes ≠ L *)
  change (length_rx_mode defaults_ipv4) with StrictEq.
assert (EEq : (Nbytes =? L) = false).
{ rewrite HL, HNbytes. apply N.eqb_neq.
  assert (lenN tail2 > 0).
  { cbv [tail2 lenN]. simpl. lia. }
  lia. }
  rewrite EEq. reflexivity.
  Qed.

  (** E2. Oversize boundary: rejection just above the limit; acceptance at the limit. *)

  Definition bytes_n (n:N) : list byte := List.repeat 0%N (N.to_nat n).

Lemma lenN_bytes_n : forall n, lenN (bytes_n n) = n.
Proof.
  intro n. unfold bytes_n, lenN.
  rewrite repeat_length.
  rewrite N2Nat.id. reflexivity.
Qed.

  Definition n_over  : N := mask16 - 7.  (* 8 + n_over = mask16 + 1 *)
  Definition n_limit : N := mask16 - 8.  (* 8 + n_limit = mask16 *)

  Example EX_encode_oversize_at_boundary :
    forall cfg ipS ipD sp dp,
      encode_udp_ipv4 cfg ipS ipD sp dp (bytes_n n_over) = Err Oversize.
  Proof.
    intros. rewrite encode_oversize_iff, lenN_bytes_n.
    cbv [n_over]. lia.
  Qed.

Example EX_encode_accepts_at_limit :
  forall cfg ipS ipD sp dp,
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

  (** E3. ICMP suppression via metadata: LL broadcast, non-initial fragment, invalid source. *)

  Example EX_icmp_suppress_ll_broadcast_any :
    forall res,
      udp_complete_icmp_advice_meta defaults_ipv4
        {| ll_broadcast := true; initial_fragment := true; src_is_unicast := true |}
        (fun _ _ => false) ex_src ex_dst res
      = NoAdvice.
  Proof. intros res. apply icmp_suppression_ll_broadcast. reflexivity. Qed.

  Example EX_icmp_suppress_non_initial_fragment_any :
    forall res,
      udp_complete_icmp_advice_meta defaults_ipv4
        {| ll_broadcast := false; initial_fragment := false; src_is_unicast := true |}
        (fun _ _ => false) ex_src ex_dst res
      = NoAdvice.
  Proof. intros res. apply icmp_suppression_non_initial_fragment. reflexivity. Qed.

  Example EX_icmp_suppress_invalid_source_any :
    forall res,
      udp_complete_icmp_advice_meta defaults_ipv4
        {| ll_broadcast := false; initial_fragment := true; src_is_unicast := false |}
        (fun _ _ => false) ex_src ex_dst res
      = NoAdvice.
  Proof. intros res. apply icmp_suppression_src_not_unicast. reflexivity. Qed.

End UDP_Required_Examples.

(** ****************************************************************************
    Port Zero Source Handling
    ----------------------------------------------------------------------------
    RFC 768 permits source port 0 meaning "no reply expected". We prove this
    works correctly through encode/decode cycles.
    **************************************************************************** *)

Section UDP_Port_Zero_Source.
  Open Scope N_scope.

  (** Encoding with source port 0 succeeds *)
  Theorem encode_source_port_zero_ok :
    forall cfg ipS ipD dp data,
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

  (** Decoding with source port 0 succeeds (with non-zero dst port) *)
  Theorem decode_source_port_zero_ok :
    forall ipS ipD dp data wire h0,
      to_word16 dp <> 0 ->
      mk_header 0 dp (lenN data) = Some h0 ->
      encode_udp_ipv4 defaults_ipv4 ipS ipD 0 dp data = Ok wire ->
      decode_udp_ipv4 defaults_ipv4 ipS ipD wire = Ok (0, to_word16 dp, data).
  Proof.
    intros ipS ipD dp data wire h0 Hdp_nz Hmk Henc.
    apply (decode_encode_roundtrip_ipv4_defaults_reject_nonzero16 
           ipS ipD 0 dp data wire h0 Hdp_nz Hmk Henc).
  Qed.

  (** Round-trip with source port 0 preserves data *)
  Theorem roundtrip_source_port_zero :
    forall ipS ipD dp data,
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

(** Example: concrete test with source port 0 *)
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

(** ****************************************************************************
    Maximum Length Edge Cases
    ----------------------------------------------------------------------------
    RFC 768 maximum datagram size handling: proves that the maximum valid
    datagram (65527 bytes of data, total 65535) works correctly and that
    length field overflow is impossible.
    **************************************************************************** *)

Section UDP_Maximum_Length.
  Open Scope N_scope.

  (** Maximum data size that fits in UDP (65535 total - 8 header) *)
  Definition max_udp_data_size : N := mask16 - 8.
  
  (** Maximum total UDP datagram size *)
  Definition max_udp_total_size : N := mask16.

(** Proof that maximum valid datagram encodes successfully *)
  Theorem encode_maximum_datagram_ok :
    forall cfg ipS ipD sp dp,
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

  (** Proof that length field overflow is impossible *)
  Theorem length_field_no_overflow :
    forall sp dp data_len h,
      mk_header sp dp data_len = Some h ->
      length16 h < two16.
  Proof.
    intros sp dp data_len h Hmk.
    destruct (mk_header_ok _ _ _ _ Hmk) as [Hle [_ [_ [HL _]]]].
    rewrite HL.
    apply to_word16_lt_two16.
  Qed.

  (** The length field correctly represents 8 + data_len when valid *)
  Theorem length_field_correct :
    forall sp dp data_len h,
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

  (** Attempting to encode data larger than max fails with Oversize *)
  Theorem encode_oversized_fails :
    forall cfg ipS ipD sp dp,
      encode_udp_ipv4 cfg ipS ipD sp dp (bytes_n (max_udp_data_size + 1)) = Err Oversize.
  Proof.
    intros cfg ipS ipD sp dp.
    rewrite encode_oversize_iff.
    rewrite lenN_bytes_n.
    unfold max_udp_data_size. lia.
  Qed.

  (** The maximum valid length field value is exactly mask16 *)
  Theorem max_length_field_value :
    forall sp dp h,
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

(** Round-trip at maximum size preserves data *)
  Theorem roundtrip_maximum_size :
    forall ipS ipD sp dp,
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

(** No valid data size can cause length overflow *)
  Theorem no_valid_length_overflow :
    forall (data : list byte),
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
