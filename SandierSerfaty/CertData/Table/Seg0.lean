/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.S000
public import SandierSerfaty.CertData.Table.S001
public import SandierSerfaty.CertData.Table.S002
public import SandierSerfaty.CertData.Table.S003
public import SandierSerfaty.CertData.Table.S004
public import SandierSerfaty.Certificate.Assemble.Lists

/-!
# The chunks of segment 0, joined

The shard theorems of segment `0` joined into one statement over all its chunks (`Assemble.forall_lt_succ_of`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The check of the chunk `c` of segment `0`. -/
abbrev SegP0 (c : Nat) : Prop :=
  innerB (chunkLenAt 0) dLit.pi nodeAt ctAt ntAt (knotCell 0 + chunkLenAt 0 * c) = true

/-- **All chunks of segment `0`** (98 chunks of 8 cells). -/
theorem seg0_chunks : ∀ c, c < chunkCnt 0 → SegP0 c := by
  have h0 : ∀ c, c < 0 → SegP0 c := forall_lt_zero'
  have h1 : ∀ c, c < 1 → SegP0 c := forall_lt_succ_of h0 chunk_0
  have h2 : ∀ c, c < 2 → SegP0 c := forall_lt_succ_of h1 chunk_8
  have h3 : ∀ c, c < 3 → SegP0 c := forall_lt_succ_of h2 chunk_16
  have h4 : ∀ c, c < 4 → SegP0 c := forall_lt_succ_of h3 chunk_24
  have h5 : ∀ c, c < 5 → SegP0 c := forall_lt_succ_of h4 chunk_32
  have h6 : ∀ c, c < 6 → SegP0 c := forall_lt_succ_of h5 chunk_40
  have h7 : ∀ c, c < 7 → SegP0 c := forall_lt_succ_of h6 chunk_48
  have h8 : ∀ c, c < 8 → SegP0 c := forall_lt_succ_of h7 chunk_56
  have h9 : ∀ c, c < 9 → SegP0 c := forall_lt_succ_of h8 chunk_64
  have h10 : ∀ c, c < 10 → SegP0 c := forall_lt_succ_of h9 chunk_72
  have h11 : ∀ c, c < 11 → SegP0 c := forall_lt_succ_of h10 chunk_80
  have h12 : ∀ c, c < 12 → SegP0 c := forall_lt_succ_of h11 chunk_88
  have h13 : ∀ c, c < 13 → SegP0 c := forall_lt_succ_of h12 chunk_96
  have h14 : ∀ c, c < 14 → SegP0 c := forall_lt_succ_of h13 chunk_104
  have h15 : ∀ c, c < 15 → SegP0 c := forall_lt_succ_of h14 chunk_112
  have h16 : ∀ c, c < 16 → SegP0 c := forall_lt_succ_of h15 chunk_120
  have h17 : ∀ c, c < 17 → SegP0 c := forall_lt_succ_of h16 chunk_128
  have h18 : ∀ c, c < 18 → SegP0 c := forall_lt_succ_of h17 chunk_136
  have h19 : ∀ c, c < 19 → SegP0 c := forall_lt_succ_of h18 chunk_144
  have h20 : ∀ c, c < 20 → SegP0 c := forall_lt_succ_of h19 chunk_152
  have h21 : ∀ c, c < 21 → SegP0 c := forall_lt_succ_of h20 chunk_160
  have h22 : ∀ c, c < 22 → SegP0 c := forall_lt_succ_of h21 chunk_168
  have h23 : ∀ c, c < 23 → SegP0 c := forall_lt_succ_of h22 chunk_176
  have h24 : ∀ c, c < 24 → SegP0 c := forall_lt_succ_of h23 chunk_184
  have h25 : ∀ c, c < 25 → SegP0 c := forall_lt_succ_of h24 chunk_192
  have h26 : ∀ c, c < 26 → SegP0 c := forall_lt_succ_of h25 chunk_200
  have h27 : ∀ c, c < 27 → SegP0 c := forall_lt_succ_of h26 chunk_208
  have h28 : ∀ c, c < 28 → SegP0 c := forall_lt_succ_of h27 chunk_216
  have h29 : ∀ c, c < 29 → SegP0 c := forall_lt_succ_of h28 chunk_224
  have h30 : ∀ c, c < 30 → SegP0 c := forall_lt_succ_of h29 chunk_232
  have h31 : ∀ c, c < 31 → SegP0 c := forall_lt_succ_of h30 chunk_240
  have h32 : ∀ c, c < 32 → SegP0 c := forall_lt_succ_of h31 chunk_248
  have h33 : ∀ c, c < 33 → SegP0 c := forall_lt_succ_of h32 chunk_256
  have h34 : ∀ c, c < 34 → SegP0 c := forall_lt_succ_of h33 chunk_264
  have h35 : ∀ c, c < 35 → SegP0 c := forall_lt_succ_of h34 chunk_272
  have h36 : ∀ c, c < 36 → SegP0 c := forall_lt_succ_of h35 chunk_280
  have h37 : ∀ c, c < 37 → SegP0 c := forall_lt_succ_of h36 chunk_288
  have h38 : ∀ c, c < 38 → SegP0 c := forall_lt_succ_of h37 chunk_296
  have h39 : ∀ c, c < 39 → SegP0 c := forall_lt_succ_of h38 chunk_304
  have h40 : ∀ c, c < 40 → SegP0 c := forall_lt_succ_of h39 chunk_312
  have h41 : ∀ c, c < 41 → SegP0 c := forall_lt_succ_of h40 chunk_320
  have h42 : ∀ c, c < 42 → SegP0 c := forall_lt_succ_of h41 chunk_328
  have h43 : ∀ c, c < 43 → SegP0 c := forall_lt_succ_of h42 chunk_336
  have h44 : ∀ c, c < 44 → SegP0 c := forall_lt_succ_of h43 chunk_344
  have h45 : ∀ c, c < 45 → SegP0 c := forall_lt_succ_of h44 chunk_352
  have h46 : ∀ c, c < 46 → SegP0 c := forall_lt_succ_of h45 chunk_360
  have h47 : ∀ c, c < 47 → SegP0 c := forall_lt_succ_of h46 chunk_368
  have h48 : ∀ c, c < 48 → SegP0 c := forall_lt_succ_of h47 chunk_376
  have h49 : ∀ c, c < 49 → SegP0 c := forall_lt_succ_of h48 chunk_384
  have h50 : ∀ c, c < 50 → SegP0 c := forall_lt_succ_of h49 chunk_392
  have h51 : ∀ c, c < 51 → SegP0 c := forall_lt_succ_of h50 chunk_400
  have h52 : ∀ c, c < 52 → SegP0 c := forall_lt_succ_of h51 chunk_408
  have h53 : ∀ c, c < 53 → SegP0 c := forall_lt_succ_of h52 chunk_416
  have h54 : ∀ c, c < 54 → SegP0 c := forall_lt_succ_of h53 chunk_424
  have h55 : ∀ c, c < 55 → SegP0 c := forall_lt_succ_of h54 chunk_432
  have h56 : ∀ c, c < 56 → SegP0 c := forall_lt_succ_of h55 chunk_440
  have h57 : ∀ c, c < 57 → SegP0 c := forall_lt_succ_of h56 chunk_448
  have h58 : ∀ c, c < 58 → SegP0 c := forall_lt_succ_of h57 chunk_456
  have h59 : ∀ c, c < 59 → SegP0 c := forall_lt_succ_of h58 chunk_464
  have h60 : ∀ c, c < 60 → SegP0 c := forall_lt_succ_of h59 chunk_472
  have h61 : ∀ c, c < 61 → SegP0 c := forall_lt_succ_of h60 chunk_480
  have h62 : ∀ c, c < 62 → SegP0 c := forall_lt_succ_of h61 chunk_488
  have h63 : ∀ c, c < 63 → SegP0 c := forall_lt_succ_of h62 chunk_496
  have h64 : ∀ c, c < 64 → SegP0 c := forall_lt_succ_of h63 chunk_504
  have h65 : ∀ c, c < 65 → SegP0 c := forall_lt_succ_of h64 chunk_512
  have h66 : ∀ c, c < 66 → SegP0 c := forall_lt_succ_of h65 chunk_520
  have h67 : ∀ c, c < 67 → SegP0 c := forall_lt_succ_of h66 chunk_528
  have h68 : ∀ c, c < 68 → SegP0 c := forall_lt_succ_of h67 chunk_536
  have h69 : ∀ c, c < 69 → SegP0 c := forall_lt_succ_of h68 chunk_544
  have h70 : ∀ c, c < 70 → SegP0 c := forall_lt_succ_of h69 chunk_552
  have h71 : ∀ c, c < 71 → SegP0 c := forall_lt_succ_of h70 chunk_560
  have h72 : ∀ c, c < 72 → SegP0 c := forall_lt_succ_of h71 chunk_568
  have h73 : ∀ c, c < 73 → SegP0 c := forall_lt_succ_of h72 chunk_576
  have h74 : ∀ c, c < 74 → SegP0 c := forall_lt_succ_of h73 chunk_584
  have h75 : ∀ c, c < 75 → SegP0 c := forall_lt_succ_of h74 chunk_592
  have h76 : ∀ c, c < 76 → SegP0 c := forall_lt_succ_of h75 chunk_600
  have h77 : ∀ c, c < 77 → SegP0 c := forall_lt_succ_of h76 chunk_608
  have h78 : ∀ c, c < 78 → SegP0 c := forall_lt_succ_of h77 chunk_616
  have h79 : ∀ c, c < 79 → SegP0 c := forall_lt_succ_of h78 chunk_624
  have h80 : ∀ c, c < 80 → SegP0 c := forall_lt_succ_of h79 chunk_632
  have h81 : ∀ c, c < 81 → SegP0 c := forall_lt_succ_of h80 chunk_640
  have h82 : ∀ c, c < 82 → SegP0 c := forall_lt_succ_of h81 chunk_648
  have h83 : ∀ c, c < 83 → SegP0 c := forall_lt_succ_of h82 chunk_656
  have h84 : ∀ c, c < 84 → SegP0 c := forall_lt_succ_of h83 chunk_664
  have h85 : ∀ c, c < 85 → SegP0 c := forall_lt_succ_of h84 chunk_672
  have h86 : ∀ c, c < 86 → SegP0 c := forall_lt_succ_of h85 chunk_680
  have h87 : ∀ c, c < 87 → SegP0 c := forall_lt_succ_of h86 chunk_688
  have h88 : ∀ c, c < 88 → SegP0 c := forall_lt_succ_of h87 chunk_696
  have h89 : ∀ c, c < 89 → SegP0 c := forall_lt_succ_of h88 chunk_704
  have h90 : ∀ c, c < 90 → SegP0 c := forall_lt_succ_of h89 chunk_712
  have h91 : ∀ c, c < 91 → SegP0 c := forall_lt_succ_of h90 chunk_720
  have h92 : ∀ c, c < 92 → SegP0 c := forall_lt_succ_of h91 chunk_728
  have h93 : ∀ c, c < 93 → SegP0 c := forall_lt_succ_of h92 chunk_736
  have h94 : ∀ c, c < 94 → SegP0 c := forall_lt_succ_of h93 chunk_744
  have h95 : ∀ c, c < 95 → SegP0 c := forall_lt_succ_of h94 chunk_752
  have h96 : ∀ c, c < 96 → SegP0 c := forall_lt_succ_of h95 chunk_760
  have h97 : ∀ c, c < 97 → SegP0 c := forall_lt_succ_of h96 chunk_768
  have h98 : ∀ c, c < 98 → SegP0 c := forall_lt_succ_of h97 chunk_776
  exact h98

end SandierSerfaty.CertData
