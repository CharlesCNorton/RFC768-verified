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
  Bool.

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
Proof. intro x. unfold to_word16. apply N.mod_lt. exact two16_pos. Qed.

Lemma to_word16_id_if_lt : forall x, x < two16 -> to_word16 x = x.
Proof. intros x Hx. unfold to_word16. apply N.mod_small. exact Hx. Qed.

Lemma to_word16_id_if_le_mask :
  forall x, x <= mask16 -> to_word16 x = x.
Proof.
  intros x Hx. apply to_word16_id_if_lt. unfold mask16 in Hx. lia.
Qed.

(* List length in N *)
Definition lenN {A} (xs:list A) : N := N.of_nat (List.length xs).
Lemma lenN_app : forall (A:Type) (xs ys:list A), lenN (xs ++ ys) = lenN xs + lenN ys.
Proof. intros A xs ys. unfold lenN. rewrite List.app_length, Nat2N.inj_add. reflexivity. Qed.
Lemma lenN_cons : forall (A:Type) (x:A) xs, lenN (x::xs) = 1 + lenN xs.
Proof. intros; unfold lenN; simpl; rewrite Nat2N.inj_succ; lia. Qed.

Lemma N_to_nat_lenN : forall (A:Type) (xs:list A), N.to_nat (lenN xs) = List.length xs.
Proof. intros; unfold lenN; now rewrite N2Nat.id. Qed.

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
  intros x. unfold is_byte. apply N.ltb_lt. apply N.mod_lt. exact two8_pos.
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
  intros w Hw. apply N.div_lt_upper_bound; try exact two8_pos.
  unfold two8, two16 in *. lia.
Qed.

Lemma word16_of_be_be16 :
  forall w, w < two16 ->
    let '(hi,lo) := be16_of_word16 w in word16_of_be hi lo = w.
Proof.
  intros w Hw. unfold be16_of_word16, word16_of_be.
  rewrite (N.mod_small (w / two8) two8).
  2:{ apply div256_lt256; exact Hw. }
  rewrite <- (N.div_mod w two8) by (apply N.neq_0_lt_0; exact two8_pos).
  lia.
Qed.

(* Each byte produced by be16_of_word16 (after to_word16) is in range. *)
Lemma be16_of_word16_bytes_are_bytes_true :
  forall w, let '(hi,lo) := be16_of_word16 (to_word16 w) in
            is_byte hi = true /\ is_byte lo = true.
Proof.
  intros w. unfold be16_of_word16, is_byte.
  simpl. split; apply N.ltb_lt; apply N.mod_lt; exact two8_pos.
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

Lemma normalizeIPv4_idempotent :
  forall ip, normalizeIPv4 (normalizeIPv4 ip) = normalizeIPv4 ip.
Proof. intros [x0 x1 x2 x3]; reflexivity. Qed.

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
  - apply N.ltb_ge in E. assert (acc + w < 2*two16) by nia. lia.
Qed.

(* Fold over a list of 16-bit words with one's-complement addition. *)
Fixpoint sum16 (ws:list word16) : word16 :=
  match ws with
  | [] => 0
  | w::tl => add16_ones (sum16 tl) (to_word16 w)
  end.

Lemma sum16_lt_two16 : forall ws, sum16 ws < two16.
Proof.
  induction ws as [|w tl IH]; simpl; try lia.
  apply add16_ones_bound; auto.
  apply to_word16_lt_two16.
Qed.

(* One's-complement (bitwise not) within 16 bits. *)
Definition complement16 (x:word16) : word16 := mask16 - x.
Definition cksum16 (ws:list word16) : word16 := complement16 (sum16 ws).

Lemma sum16_app : forall xs ys,
  sum16 (xs ++ ys) = fold_left add16_ones (map to_word16 ys) (sum16 xs).
Proof.
  induction xs as [|x xs IH]; intros ys; simpl; auto.
  now rewrite IH.
Qed.

Lemma add16_ones_complement :
  forall s, s < two16 -> add16_ones s (complement16 s) = mask16.
Proof.
  intros s Hs. unfold add16_ones, complement16.
  replace (s + (mask16 - s)) with mask16 by lia.
  rewrite N.ltb_lt; [reflexivity|].
  unfold mask16, two16 in *; lia.
Qed.

Lemma sum16_with_cksum_is_allones :
  forall ws, sum16 (ws ++ [cksum16 ws]) = mask16.
Proof.
  intro ws.
  rewrite sum16_app. simpl.
  set (s := sum16 ws).
  unfold cksum16, complement16.
  simpl.
  rewrite (to_word16_id_if_le_mask (mask16 - s)).
  - apply add16_ones_complement. apply sum16_lt_two16.
  - unfold mask16, two16. lia.
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
  destruct (N.eqb (cksum16 (checksum_words_ipv4 ipS ipD h data)) 0) eqn:E; cbn; lia.
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
  (src_port dst_port:word16) (data:list byte)
  : result (list byte) EncodeError :=
  match mk_header src_port dst_port (lenN data) with
  | None => Err Oversize
  | Some h0 =>
      let h1 :=
        match cfg.(checksum_tx_mode) with
        | NoChecksum => {| src_port := h0.(src_port)
                         ; dst_port := h0.(dst_port)
                         ; length16 := h0.(length16)
                         ; checksum := 0 |}
        | WithChecksum =>
            let c := compute_udp_checksum_ipv4 src_ip dst_ip h0 data in
            {| src_port := h0.(src_port)
             ; dst_port := h0.(dst_port)
             ; length16 := h0.(length16)
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
  | Ok d =>
      if has_listener d.(dst_ip_out) d.(dst_port_out)
      then NoAdvice
      else SendICMPDestUnreach ICMP_PORT_UNREACH
  | Err BadLength => NoAdvice            (* UDP length errors: drop; no ICMP *)
  | Err BadChecksum => NoAdvice          (* Checksum errors: drop; no ICMP *)
  | Err DstPortZeroNotAllowed => NoAdvice
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
  forall h0 ipS ipD data,
    header_norm {| src_port := src_port h0;
                   dst_port := dst_port h0;
                   length16 := length16 h0;
                   checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}.
Proof.
  intros h0 ipS ipD data. unfold header_norm; repeat split.
  all: try apply to_word16_lt_two16.
  - apply to_word16_lt_two16.
  - unfold compute_udp_checksum_ipv4.
    set (x := cksum16 (checksum_words_ipv4 ipS ipD h0 data)).
    destruct (N.eqb x 0).
    + unfold mask16, two16; lia.
    + unfold cksum16, complement16.
      pose proof (sum16_lt_two16 (checksum_words_ipv4 ipS ipD h0 data)) as Hs.
      unfold mask16, two16 in *. lia.
Qed.

Lemma parse_header_bytes_of_header_norm :
  forall h rest,
    header_norm h ->
    parse_header (udp_header_bytes h ++ rest) = Some (h, rest).
Proof.
  intros h rest Hn.
  unfold udp_header_bytes, udp_header_words. simpl.
  remember (be16_of_word16 (to_word16 (src_port h))) as p0 eqn:Hp0.
  destruct p0 as [s0 s1].
  remember (be16_of_word16 (to_word16 (dst_port h))) as p1 eqn:Hp1.
  destruct p1 as [d0 d1].
  remember (be16_of_word16 (to_word16 (length16 h))) as p2 eqn:Hp2.
  destruct p2 as [l0 l1].
  remember (be16_of_word16 (to_word16 (checksum h))) as p3 eqn:Hp3.
  destruct p3 as [c0 c1].
  cbn.
  unfold parse_header; cbn.
  (* Header byte-range check succeeds *)
  pose proof (be16_of_word16_bytes_are_bytes_true (src_port h)) as [Hsp0 Hsp1].
  rewrite Hp0 in Hsp0, Hsp1; cbn in Hsp0, Hsp1.
  pose proof (be16_of_word16_bytes_are_bytes_true (dst_port h)) as [Hdp0 Hdp1].
  rewrite Hp1 in Hdp0, Hdp1; cbn in Hdp0, Hdp1.
  pose proof (be16_of_word16_bytes_are_bytes_true (length16 h)) as [Hl0 Hl1].
  rewrite Hp2 in Hl0, Hl1; cbn in Hl0, Hl1.
  pose proof (be16_of_word16_bytes_are_bytes_true (checksum h)) as [Hc0 Hc1].
  rewrite Hp3 in Hc0, Hc1; cbn in Hc0, Hc1.
  simpl.
  rewrite Hsp0; simpl. rewrite Hsp1; simpl.
  rewrite Hdp0; simpl. rewrite Hdp1; simpl.
  rewrite Hl0;  simpl. rewrite Hl1;  simpl.
  rewrite Hc0;  simpl. rewrite Hc1;  simpl.
  (* Now the parse succeeds; show fields reconstruct h *)
  f_equal.
  - apply f_equal2; [|].
    + apply f_equal2.
      * destruct Hn as [Hsp [Hdp [HL Hck]]].
        rewrite (to_word16_id_if_lt (src_port h) Hsp).
        rewrite <- Hp0.
        rewrite (word16_of_be_be16 (to_word16 (src_port h))).
        { rewrite to_word16_id_if_lt by apply to_word16_lt_two16. reflexivity. }
        apply to_word16_lt_two16.
      * destruct Hn as [_ [Hdp [HL Hck]]].
        rewrite (to_word16_id_if_lt (dst_port h) Hdp).
        rewrite <- Hp1.
        rewrite (word16_of_be_be16 (to_word16 (dst_port h))).
        { rewrite to_word16_id_if_lt by apply to_word16_lt_two16. reflexivity. }
        apply to_word16_lt_two16.
    + apply f_equal2.
      * destruct Hn as [_ [_ [HL Hck]]].
        rewrite (to_word16_id_if_lt (length16 h) HL).
        rewrite <- Hp2.
        rewrite (word16_of_be_be16 (to_word16 (length16 h))).
        { rewrite to_word16_id_if_lt by apply to_word16_lt_two16. reflexivity. }
        apply to_word16_lt_two16.
      * destruct Hn as [_ [_ [_ Hck]]].
        rewrite (to_word16_id_if_lt (checksum h) Hck).
        rewrite <- Hp3.
        rewrite (word16_of_be_be16 (to_word16 (checksum h))).
        { rewrite to_word16_id_if_lt by apply to_word16_lt_two16. reflexivity. }
        apply to_word16_lt_two16.
  - reflexivity.
Qed.

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
  unfold verify_checksum_ipv4, compute_udp_checksum_ipv4.
  set (words := checksum_words_ipv4 ipS ipD h0 data).
  remember (cksum16 words) as c.
  destruct (N.eqb c 0) eqn:Ez.
  - apply N.eqb_eq. simpl.
    assert (Hs: sum16 words = mask16).
    { apply N.eqb_eq in Ez. subst c.
      unfold cksum16 in Heqc. subst.
      unfold complement16.
      assert (Hlt: sum16 words < two16) by apply sum16_lt_two16.
      assert (Hle: sum16 words <= mask16) by (unfold mask16, two16 in *; lia).
      lia. }
    rewrite <- Hs. rewrite sum16_app. simpl.
    unfold add16_ones. rewrite N.ltb_ge; [|lia]. lia.
  - apply N.eqb_eq. simpl. rewrite <- Heqc.
    apply sum16_with_cksum_is_allones.
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

(* MAIN Theorem A (StrictEq):
   Defaults (Reject destination-port 0). Premise: to_word16 dp ≠ 0. *)
Theorem decode_encode_roundtrip_ipv4_defaults_reject_nonzero16 :
  forall ipS ipD sp dp data wire h0,
    to_word16 dp <> 0%N ->
    mk_header sp dp (lenN data) = Some h0 ->
    encode_udp_ipv4 defaults_ipv4 ipS ipD sp dp data = Ok wire ->
    decode_udp_ipv4 defaults_ipv4 ipS ipD wire
      = Ok (to_word16 sp, to_word16 dp, data).
Proof.
  intros ipS ipD sp dp data wire h0 Hdp16NZ Hmk Henc.
  unfold encode_udp_ipv4 in Henc.
  rewrite Hmk in Henc.
  destruct (checksum_tx_mode defaults_ipv4) eqn:Etx; [|discriminate].
  inversion Henc; subst wire; clear Henc.
  set (h1 := {| src_port := src_port h0 ;
                dst_port := dst_port h0 ;
                length16 := length16 h0 ;
                checksum := compute_udp_checksum_ipv4 ipS ipD h0 data |}).
  unfold decode_udp_ipv4.
  assert (Hnorm: header_norm h1) by apply header_norm_encode_h1.
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
  assert (Hnorm: header_norm h1) by apply header_norm_encode_h1.
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
  assert (Hnorm: header_norm h1) by apply header_norm_encode_h1.
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
  assert (Hnorm: header_norm h1) by apply header_norm_encode_h1.
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

(* NEW: example documenting RFC 768 "source port optional (0 permitted)". *)
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
