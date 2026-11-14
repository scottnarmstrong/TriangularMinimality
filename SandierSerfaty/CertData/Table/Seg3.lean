/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.S069
public import SandierSerfaty.Certificate.Assemble.Lists

/-!
# The chunks of segment 3, joined

The shard theorems of segment `3` joined into one statement over all its chunks (`Assemble.forall_lt_succ_of`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The check of the chunk `c` of segment `3`. -/
abbrev SegP3 (c : Nat) : Prop :=
  chunkB (chunkLenAt 3) dLit nodeAt ctAt ntAt ckAt 3 (knotCell 3 + chunkLenAt 3 * c) = true

/-- **All chunks of segment `3`** (12 chunks of 2 cells). -/
theorem seg3_chunks : ∀ c, c < chunkCnt 3 → SegP3 c := by
  have h0 : ∀ c, c < 0 → SegP3 c := forall_lt_zero'
  have h1 : ∀ c, c < 1 → SegP3 c := forall_lt_succ_of h0 chunk_2016
  have h2 : ∀ c, c < 2 → SegP3 c := forall_lt_succ_of h1 chunk_2018
  have h3 : ∀ c, c < 3 → SegP3 c := forall_lt_succ_of h2 chunk_2020
  have h4 : ∀ c, c < 4 → SegP3 c := forall_lt_succ_of h3 chunk_2022
  have h5 : ∀ c, c < 5 → SegP3 c := forall_lt_succ_of h4 chunk_2024
  have h6 : ∀ c, c < 6 → SegP3 c := forall_lt_succ_of h5 chunk_2026
  have h7 : ∀ c, c < 7 → SegP3 c := forall_lt_succ_of h6 chunk_2028
  have h8 : ∀ c, c < 8 → SegP3 c := forall_lt_succ_of h7 chunk_2030
  have h9 : ∀ c, c < 9 → SegP3 c := forall_lt_succ_of h8 chunk_2032
  have h10 : ∀ c, c < 10 → SegP3 c := forall_lt_succ_of h9 chunk_2034
  have h11 : ∀ c, c < 11 → SegP3 c := forall_lt_succ_of h10 chunk_2036
  have h12 : ∀ c, c < 12 → SegP3 c := forall_lt_succ_of h11 chunk_2038
  exact h12

end SandierSerfaty.CertData
