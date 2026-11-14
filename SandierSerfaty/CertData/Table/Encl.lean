/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Seg0
public import SandierSerfaty.CertData.Table.Seg1
public import SandierSerfaty.CertData.Table.Seg2
public import SandierSerfaty.CertData.Table.Seg3
public import SandierSerfaty.CertData.Table.Seg4
public import SandierSerfaty.CertData.Table.Seg5
public import SandierSerfaty.CertData.Table.Nodes
public import SandierSerfaty.CertData.Core.Valid
public import SandierSerfaty.Certificate.Assemble.Realize

/-!
# Assertion A3: the whole radial table encloses the truncated calibration

`tbl_encl`: the real nodes `aTbl = realNode nodeAt knotCell` realize the generated table `iTbl`
(`Query.ITable.Encl`: on every cell `[aTbl i, aTbl (i + 1)]`, `i < 3848`, the cell tuple encloses `Trunc.f₀`,
`Trunc.f₀'`, `Trunc.e`, `Trunc.e'`), and every node tuple of the segments `1, …, 5` encloses `Trunc.f₀`, `Trunc.e`
at its node. From the shards: the nodes (`nodes_ok`), the chunks of the six segments (`seg0_chunks`, …,
`seg5_chunks`), the initial checkpoint (`init_ok`), the finite core (`finiteCore`) and the basis constants
(`dLit_valid`), through `Assemble.tableEncl_of_checks`.

`tbl_model`: from the same shards, the realization `Lambda.TableModel ⟨iTbl, ntAt⟩ aTbl` of the table by the segment
models (`Assemble.tableModel_of_checks`), consumed by the box layer and the fine `λ` (`Lambda.certificateGoal_of_checks''`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The real nodes of the table. -/
noncomputable abbrev aTbl : ℕ → ℝ := realNode nodeAt knotCell

theorem knotsUp : KnotsUp knotCell := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [knotCell]

/-- **Assertion A3** (the whole table) and the node tuples. -/
theorem tbl_encl : ITable.Encl iTbl aTbl ∧
    ∀ j, 1 ≤ j → j ≤ 5 → ∀ i, knotCell j ≤ i → i < knotCell (j + 1) →
      IV.Mem (SandierSerfaty.Calibration.Trunc.f₀ (aTbl (i + 1))) (ntAt i).f0 ∧
        IV.Mem (SandierSerfaty.Calibration.Trunc.e (aTbl (i + 1))) (ntAt i).e0 := by
  have h := tableEncl_of_checks finiteCore dLit_valid (node := nodeAt) (ct := ctAt) (nt := ntAt) (ck := ckAt)
    (K := knotCell) (Ls := chunkLenAt) (Ns := chunkCnt) rfl
    (fun j hj => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      all_goals rfl)
    (fun j hj => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      all_goals simp [chunkLenAt])
    (fun j hj => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      all_goals simp [chunkCnt])
    nodes_ok seg0_chunks init_ok
    (fun j h1 h5 => by
      obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      exacts [seg1_chunks, seg2_chunks, seg3_chunks, seg4_chunks, seg5_chunks])
  exact h

/-- **The table model**: every cell and its right node tuple enclose the model of their segment. -/
theorem tbl_model : SandierSerfaty.Certificate.Lambda.TableModel ⟨iTbl, ntAt⟩ aTbl :=
  tableModel_of_checks dLit_valid (node := nodeAt) (ct := ctAt) (nt := ntAt) (ck := ckAt)
    (K := knotCell) (Ls := chunkLenAt) (Ns := chunkCnt) rfl
    (fun j hj => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      all_goals rfl)
    (fun j hj => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      all_goals simp [chunkLenAt])
    (fun j hj => by
      obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      all_goals simp [chunkCnt])
    nodes_ok seg0_chunks init_ok
    (fun j h1 h5 => by
      obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      exacts [seg1_chunks, seg2_chunks, seg3_chunks, seg4_chunks, seg5_chunks])

end SandierSerfaty.CertData
