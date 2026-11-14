/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.S130
public import SandierSerfaty.Certificate.Assemble.Lists

/-!
# The chunks of segment 5, joined

The shard theorems of segment `5` joined into one statement over all its chunks (`Assemble.forall_lt_succ_of`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The check of the chunk `c` of segment `5`. -/
abbrev SegP5 (c : Nat) : Prop :=
  chunkB (chunkLenAt 5) dLit nodeAt ctAt ntAt ckAt 5 (knotCell 5 + chunkLenAt 5 * c) = true

/-- **All chunks of segment `5`** (12 chunks of 2 cells). -/
theorem seg5_chunks : ∀ c, c < chunkCnt 5 → SegP5 c := by
  have h0 : ∀ c, c < 0 → SegP5 c := forall_lt_zero'
  have h1 : ∀ c, c < 1 → SegP5 c := forall_lt_succ_of h0 chunk_3824
  have h2 : ∀ c, c < 2 → SegP5 c := forall_lt_succ_of h1 chunk_3826
  have h3 : ∀ c, c < 3 → SegP5 c := forall_lt_succ_of h2 chunk_3828
  have h4 : ∀ c, c < 4 → SegP5 c := forall_lt_succ_of h3 chunk_3830
  have h5 : ∀ c, c < 5 → SegP5 c := forall_lt_succ_of h4 chunk_3832
  have h6 : ∀ c, c < 6 → SegP5 c := forall_lt_succ_of h5 chunk_3834
  have h7 : ∀ c, c < 7 → SegP5 c := forall_lt_succ_of h6 chunk_3836
  have h8 : ∀ c, c < 8 → SegP5 c := forall_lt_succ_of h7 chunk_3838
  have h9 : ∀ c, c < 9 → SegP5 c := forall_lt_succ_of h8 chunk_3840
  have h10 : ∀ c, c < 10 → SegP5 c := forall_lt_succ_of h9 chunk_3842
  have h11 : ∀ c, c < 11 → SegP5 c := forall_lt_succ_of h10 chunk_3844
  have h12 : ∀ c, c < 12 → SegP5 c := forall_lt_succ_of h11 chunk_3846
  exact h12

end SandierSerfaty.CertData
