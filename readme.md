# UDP over IPv4/IPv6 — mechanized specification and proof in Coq

This repository contains a complete, machine‑checked development of the User Datagram Protocol as it appears on the wire for IPv4 and IPv6. The model captures the RFC 768 header format, the Internet one’s‑complement checksum (including the pseudo‑header contributions for IPv4 and IPv6), and realistic receive‑side policies used by production stacks. On top of the specification, it provides a verified encoder/decoder pair and proves that they form a proper codec for all well‑formed datagrams, with precise behavior on corner cases such as zero checksums, destination‑port zero, and IP‑layer surplus octets.

## Scope and structure

The development starts from a small numeric core: bytes and 16‑bit words are modeled over Coq’s binary naturals, with big‑endian decomposition and composition, length‑aware list operations, and total truncation to the 8‑ and 16‑bit ranges. The Internet checksum is defined using end‑around‑carry addition. The algebra behind that operation—associativity and commutativity under the relevant bounds—is proved in the small, as is permutation invariance of the final checksum over any reordering of 16‑bit words. An explicit equivalence with the common “mod‑and‑carry” implementation technique connects the proof to how checksums are typically computed in systems code.

UDP is then given as a normalized header record with big‑endian serialization. The encoder builds the appropriate pseudo‑header, inserts a zero checksum for the calculation, computes the final value (mapping the all‑zero result to 0xFFFF as required on the wire), and emits header plus payload. The decoder parses the octet stream and enforces: a minimum total length of eight octets; total‑length consistency; and checksum validity against the same pseudo‑header. Two policies are provided for how strictly to compare the IP‑supplied byte count with the UDP length: a strict equality mode and a mode that accepts IP‑layer surplus and delivers exactly the prefix indicated by the UDP length. For IPv4, acceptance of a zero checksum is configurable (always accept, forbid for multicast/broadcast, or forbid always); for IPv6, zero checksums are rejected, per RFC 8200.

Configurations are first‑class. A single record controls transmit‑time checksums, receive‑time checksum policy, zero‑checksum handling, how to treat surplus IP bytes, whether to allow destination‑port zero, and how to detect broadcast addresses. This parameterization lets one fix a “standards‑strict” profile, an interoperability profile, or a hardened profile for deployment, with the proofs written against the abstract configuration.

## Main results

Codec soundness and completeness are proved precisely. Round‑trip theorems state that, for any configuration with destination‑port zero forbidden, encoding followed by decoding returns the original source port, destination port, and payload; a companion result covers the special canonicalization that arises when the computed checksum is all‑zeros and must be transmitted as 0xFFFF. The converse completeness result shows that any wire accepted by the decoder is reproduced by the encoder (modulo that same canonicalization). Parser/serializer injectivity is established for normalized headers, so a byte‑accurate wire uniquely determines the header that produced it.

Checksum correctness is developed in several layers useful to implementers. The end‑around adder is associative and commutative under 16‑bit bounds, so the fold of 16‑bit words is well‑defined independent of chunking decisions. The checksum is invariant under permutation of words, justifying common transporter transformations that re‑order chunks. Finally, the add‑mod‑carry equivalence is proved, matching the textbook implementation pattern: sum modulo 2^16, add the carry, and complement.

Robustness properties important for implementers come with crisp characterizations. Oversize rejection is equivalent to the total requested length exceeding 65 535; the maximum legal datagram (65 527 data octets, 65 535 total) is constructible, encodable, and round‑trips. The minimum eight‑byte packet behaves as expected. Source port zero—“no reply expected”—is supported end‑to‑end. The decoder is total (never stuck) and always returns either a well‑typed result or one of three explicit errors: BadLength, BadChecksum, or DstPortZeroNotAllowed. When surplus from the IP layer is accepted, prefix‑stability results show that checksum verification depends only on the prefix dictated by the UDP length, and delivery is exactly that prefix; in strict mode the same surplus is rejected.

## IPv6 status

The IPv6 model mirrors the IPv4 one with the differences mandated by RFC 8200. Addresses are represented as eight normalized 16‑bit words; the pseudo‑header consists of source and destination addresses, the upper‑layer packet length, and the Next Header value for UDP (17). The encoder and decoder enforce the mandatory checksum (zero is rejected), and round‑trip plus completeness theorems hold as in IPv4. A simple multicast predicate for ff00::/8 is included. Jumbograms (upper‑layer lengths beyond 65 535) are intentionally out of scope in this formalization.

## ICMP advice and receive‑side enrichment

To support realistic application integration, the decoder can return source and destination IP addresses alongside ports and payload, enabling precise socket demultiplexing. An ICMP advisory layer determines when to generate Destination Unreachable (Port) and related errors, with the correct suppressions for multicast and broadcast traffic and with the ability to incorporate link‑layer metadata (whether the packet arrived as a link‑layer broadcast, whether it was the initial fragment, and whether the source address is a plausible unicast). The advice path also includes a simple rate‑limiting hook and a small mapping to application‑visible transmission errors.

## Hardened variants

A hardened wrapper is provided for defense‑in‑depth: delivered bytes are normalized into octets (modulo 256), zero checksums are refused for multicast and broadcast even when unicast zero is permitted, and strict total‑length equality is enforced. These wrappers compose with the address‑aware decoder and the ICMP advisory path without disturbing the core proofs.

## Using the library

The surface API is a set of total, pure functions intended for extraction to OCaml. For IPv4, the encoder takes a configuration, source and destination IPv4 addresses, source and destination ports, and a list of bytes; it returns either an octet stream or an Oversize error. The decoder takes a configuration, the corresponding addresses, and a candidate octet stream; it returns either a triple of source port, destination port, and payload, or one of the explicit errors mentioned above. The IPv6 encoder/decoder pair is analogous but enforces mandatory non‑zero checksums by construction. Address‑aware decoders return the IP endpoints together with the transport fields. Because configuration is explicit, applications can opt into strict equality, surplus acceptance, and port‑zero rules appropriate to their environment.

## Building

The development targets Coq 8.13 or newer and depends only on the Coq standard library. A conventional build flow is provided via \_CoqProject: generate a Makefile with coq\_makefile and build with make. The included proofs use only standard automation (lia for arithmetic, list combinators, and boolean rewrites); concrete examples discharge computations using vm\_compute so the repository remains self‑contained.

## Included, worked examples

To make the artifact tangible, the repository contains executable proofs that synthesize and check specific packets. A historically themed pipeline builds the canonical “LO” message as a UDP/IPv4 datagram from UCLA (10.0.0.1) to SRI (10.0.0.2), computes the checksum through the IPv4 pseudo‑header and zero‑then‑final checksum flow, proves the transmitted checksum is non‑zero, and shows the handcrafted bytes decode to the expected ports and payload. Additional examples show that adding surplus octets at the IP layer is accepted and truncated precisely in the surplus‑tolerant mode but rejected under strict equality; that oversize encoding fails exactly at 65 535+1; that the maximum legal datagram is encodable; and that the ICMP advisory logic produces Port Unreachable with the required suppressions.

## What is not modeled (yet)

The proof covers UDP over IPv4 and IPv6 as they appear in the base RFCs. It does not model IPv6 jumbograms, UDP‑Lite partial coverage, DTLS, or ICMPv6 message families; these are natural extensions on top of the existing codec and checksum algebra. The current ICMP layer focuses on classic IPv4 error signaling and its standard suppressions; an ICMPv6 counterpart would follow the same pattern but is outside the present development.

## Why this matters

UDP is a small protocol with outsized surface area: subtle errors in length and checksum handling, policy around zero checksums, and edge cases at the maximum length have all been sources of interoperability and security issues. By deriving an executable encoder/decoder from a single mechanized specification and proving the algebra it rests on, the development gives implementers a reference that is at once executable, interoperable, and justified end‑to‑end. The proofs around permutation invariance and the mod‑and‑carry equivalence in particular make it straightforward to connect the model to efficient, conventional implementations.

## Roadmap

The code is structured to accommodate growth. Immediate next steps include adding ICMPv6 advice alongside the IPv6 codec, modeling IPv6 jumbograms, and offering UDP‑Lite for partial checksums. On the engineering side, extraction to OCaml is straightforward, and property‑based testing can be layered on top of the proven invariants to stress the extracted code. None of these extensions require changes to the established checksum algebra or the core codec proofs; they build on the same foundations.
