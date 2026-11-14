/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.CtxSound

/-!
# The second-order table realization `Box.Encl2` from the table chunks

`Table.TableEncloses` (the output of `Table.chunks_sound_trunc`) encloses the *model* functions `F0m j`, `Em j` of a
segment `j` and their first and second derivative witnesses on every stored cell `[τ_i, τ_{i+1}]`. This file turns that
into the realization predicates consumed by the box layer:

* `CellModel j x y ct`: one stored cell `ct` of segment `j` on the nondegenerate interval `[x, y] ⊆ seg j` (`x < y`)
  carries `TupEncl (Icc x y) (F0m j ·) (Em j) ct`;
* `CellModel.f2`: `HasDerivAt (deriv f̃₀) F t` with `F ∈ ct.f2` for every `t ∈ [x, y]` (two-sided; the witness `F₂` of
  the model is identified with the second derivative `G₂` of `exists_jet_Trunc_f₀` by uniqueness of derivatives on the
  nondegenerate cell);
* `CellModel.e2`: a right derivative of `ẽ'` at `t ∈ [x, y)` in `ct.e2` (the model's `E₂`: `deriv ẽ = E₁` on the cell);
* `TableRealized T a`: the real nodes `a` lie in the node intervals, run from `b` to `l`, and every cell is a
  `CellModel` of some segment `j ≤ 6`;
* `TableRealized.encl`, `TableRealized.encl2`: `ITable.Encl T a` and `Box.Encl2 T a`.
-/

open Set Filter Topology

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The real content of one stored cell: the interval `[x, y]` (`x < y`) lies in the segment `j ≤ 6` and the stored
tuple encloses the model `(F0m j, Em j)` with its derivative witnesses on it. -/
structure CellModel (j : ℕ) (x y : ℝ) (ct : Tup) : Prop where
  /-- The segment index. -/
  hj : j ≤ 6
  /-- The cell is nondegenerate. -/
  lt : x < y
  /-- The cell lies in the closed segment. -/
  sub : Icc x y ⊆ seg j
  /-- The stored tuple encloses the model. -/
  encl : TupEncl (Icc x y) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) ct

/-- **Two-sided `f̃₀''` on a cell** from the table soundness. -/
theorem CellModel.f2 (hc : FiniteCore) {j : ℕ} {x y : ℝ} {ct : Tup} (h : CellModel j x y ct) :
    ∀ t ∈ Icc x y, ∃ F, HasDerivAt (deriv Trunc.f₀) F t ∧ IV.Mem F ct.f2 := by
  intro t ht
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := h.encl
  obtain ⟨G₁, G₂, jt⟩ := exists_jet_Trunc_f₀ hc
  have ht0 : t ∈ Ioi (0 : ℝ) := seg_subset_Ioi (h.sub ht)
  have hG : HasDerivAt (deriv Trunc.f₀) (G₂ t) t := by
    refine (jt.d1 t ht0).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht0] with u hu
    exact (jt.d0 u hu).deriv
  have hF : HasDerivWithinAt (deriv Trunc.f₀) (F₂ t) (Icc x y) t :=
    (hd t ht).2.1.hasDerivWithinAt.congr (fun u hu => deriv_trunc_f₀_eq hc h.hj (h.sub hu) (hd u hu).1)
      (deriv_trunc_f₀_eq hc h.hj (h.sub ht) (hd t ht).1)
  have hu := (uniqueDiffOn_Icc h.lt t ht).eq_deriv _ hG.hasDerivWithinAt hF
  exact ⟨F₂ t, hu ▸ hG, (hm t ht).2.2.1⟩

/-- **A right derivative of `ẽ'` on a cell** from the table soundness: for `t ∈ [x, y)` the model's `E₂` is a right
derivative of `ẽ'` at `t`. -/
theorem CellModel.e2 {j : ℕ} {x y : ℝ} {ct : Tup} (h : CellModel j x y ct) :
    ∀ t ∈ Ico x y, ∃ E, HasDerivWithinAt (deriv Trunc.e) E (Ici t) t ∧ IV.Mem E ct.e2 := by
  intro t ht
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := h.encl
  have htI : t ∈ Icc x y := ⟨ht.1, ht.2.le⟩
  have hE : HasDerivWithinAt (deriv Trunc.e) (E₂ t) (Icc x y) t :=
    (hd t htI).2.2.2.hasDerivWithinAt.congr (fun u hu => deriv_trunc_e_eq h.hj (h.sub hu) (hd u hu).2.2.1)
      (deriv_trunc_e_eq h.hj (h.sub htI) (hd t htI).2.2.1)
  have hnb : Icc x y ∈ 𝓝[Ici t] t :=
    mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  exact ⟨E₂ t, hE.mono_of_mem_nhdsWithin hnb, (hm t htI).2.2.2.2.2⟩

/-- **The real nodes realize the stored table**: the nodes lie in the node intervals, run from `b` to `l`, and every
stored cell is the model of a segment `j ≤ 6` on its (nondegenerate) real interval. -/
structure TableRealized (T : ITable) (a : ℕ → ℝ) : Prop where
  /-- `a i ∈ node i`. -/
  node : ∀ i, i ≤ T.n → IV.Mem (a i) (T.node i)
  /-- The first node is `b`. -/
  first : a 0 = Calibration.b
  /-- The last node is `l`. -/
  last : a T.n = Calibration.l
  /-- Every cell is a model cell of some segment. -/
  cell : ∀ i, i < T.n → ∃ j, CellModel j (a i) (a (i + 1)) (T.cell i)

/-- **The first-order realization** `ITable.Encl` from the table chunks. -/
theorem TableRealized.encl (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (h : TableRealized T a) : T.Encl a where
  node := h.node
  mono i hi := by obtain ⟨j, hj⟩ := h.cell i hi; exact hj.lt.le
  first := h.first
  last := h.last
  f0 i hi t ht := by
    obtain ⟨j, hj⟩ := h.cell i hi
    exact (cell_enclosures hc hj.hj hj.sub hj.encl t ht).1
  f1 i hi t ht := by
    obtain ⟨j, hj⟩ := h.cell i hi
    exact (cell_enclosures hc hj.hj hj.sub hj.encl t ht).2.1
  e0 i hi t ht := by
    obtain ⟨j, hj⟩ := h.cell i hi
    exact (cell_enclosures hc hj.hj hj.sub hj.encl t ht).2.2.1
  e1 i hi t ht := by
    obtain ⟨j, hj⟩ := h.cell i hi
    exact (cell_enclosures hc hj.hj hj.sub hj.encl t ht).2.2.2

/-- **`Box.Encl2` from the table chunks**: the second-order table realization consumed by `A7Env`, `HessEnv` and
`derivBounds_of_a7`. -/
theorem TableRealized.encl2 (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (h : TableRealized T a) : Encl2 T a where
  base := h.encl hc
  f2 i hi t ht := by
    obtain ⟨j, hj⟩ := h.cell i hi
    exact hj.f2 hc t ht
  e2 i hi t ht := by
    obtain ⟨j, hj⟩ := h.cell i hi
    exact hj.e2 t ht

/-! ### The cells of a chunk -/

end SandierSerfaty.Certificate.Box
