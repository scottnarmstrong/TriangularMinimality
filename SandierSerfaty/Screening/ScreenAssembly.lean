/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.SoftCutBounds
public import SandierSerfaty.Screening.KeepDrop
public import SandierSerfaty.Screening.ColumnFlux
public import SandierSerfaty.Screening.ColumnFiller
public import SandierSerfaty.Screening.CarryField
public import SandierSerfaty.Screening.AeAtMostOne

/-!
# The screened configuration (screening note, Definition 4.23)

The screening note, Definition 4.23 (`def:assembly`). The column cut
(Lemma 4.18, applied through `Hyp.cutHyp`) and the filler partitions of all columns (Lemma 4.21 as
in Definition 4.23) are bundled in `Scr.Asm`, with their properties in `Scr.Asm.Good`
(`Asm.exists_good`). For `A : Asm`:

* `cols`: the columns `(j, k)`, `k < K_j`; `pcs`: the filler pieces `(j, k, p)`, `p ∈ I_{jk}`;
* `Z`: the piece centres, `Y = K ∪ Z`, `rho`: `α` on `K`, `r₀` on `Z`;
* `Vflux = ∑ V_k`, `Vcarry = ∑ V^c_j`, `Vpiece = ∑ Ψ_P`, and the screened field
  `E' = ψX + Vflux + Vcarry + Vpiece`.

Geometry (`Asm.Good.…`): columns lie in `R_j` and have null pairwise intersections; they cover the
frame; flux cells and filler parts lie in their columns, pieces in their filler parts.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

/-- **Partitions cover**: every `s ∈ [0, L]` lies in some step `[u_k, u_{k+1}]`, `k < K`. -/
theorem IsPartition.exists_mem {ℓ L : ℝ} {K : ℕ} {u : ℕ → ℝ} (hP : IsPartition ℓ 0 L K u)
    {s : ℝ} (hs : s ∈ Icc 0 L) : ∃ k < K, s ∈ Icc (u k) (u (k + 1)) := by
  classical
  have hK := hP.one_le
  have hex : ∃ k, s ≤ u (k + 1) := ⟨K - 1, by rw [show K - 1 + 1 = K by omega, hP.last]; exact hs.2⟩
  set k := Nat.find hex
  have hk : s ≤ u (k + 1) := Nat.find_spec hex
  have hkK : k ≤ K - 1 := Nat.find_min' hex (by rw [show K - 1 + 1 = K by omega, hP.last]; exact hs.2)
  refine ⟨k, by omega, ?_, hk⟩
  rcases Nat.eq_zero_or_eq_succ_pred k with h0 | hsucc
  · rw [h0, hP.zero]; exact hs.1
  · have := Nat.find_min hex (show k.pred < k by omega)
    rw [not_le, show k.pred + 1 = k by omega] at this
    exact this.le

/-- Distinct steps of a partition overlap in a null set. -/
theorem IsPartition.volume_inter {ℓ L : ℝ} {K : ℕ} {u : ℕ → ℝ} (hP : IsPartition ℓ 0 L K u)
    (hℓ : 0 ≤ ℓ) {k k' : ℕ} (hk : k < K) (hk' : k' < K) (hne : k ≠ k') :
    volume (Icc (u k) (u (k + 1)) ∩ Icc (u k') (u (k' + 1))) = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hle : u (k + 1) ≤ u k' := hP.mono hℓ (by omega) hk'.le
    refine measure_mono_null (t := Icc (u k') (u (k + 1))) (fun x hx => ⟨hx.2.1, hx.1.2⟩) ?_
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
  · have hle : u (k' + 1) ≤ u k := hP.mono hℓ (by omega) hk.le
    refine measure_mono_null (t := Icc (u k) (u (k' + 1))) (fun x hx => ⟨hx.1.1, hx.2.2⟩) ?_
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith

namespace Scr

open Pinwheel

/-- The column cut and the filler partitions of the screening construction. -/
structure Asm where
  /-- the column cut (screening note, Lemma 4.18) -/
  cut : ColumnCut
  /-- the integer column masses -/
  n : Fin 4 → ℕ → ℕ
  /-- the indices of the filler pieces of each column -/
  I : Fin 4 → ℕ → Finset (ℕ × ℕ)
  /-- the filler pieces of each column -/
  piece : Fin 4 → ℕ → ℕ × ℕ → Rect

namespace Asm

variable (D : Data) (A : Asm)

/-- The properties of the column cut and the filler partitions. -/
structure Good : Prop where
  isCut : A.cut.IsCut D.c D.t D.d D.ℓ D.g ((D.N : ℤ) - D.K.card)
  mass : ∀ j k, k < A.cut.K j →
    1 ≤ A.n j k ∧ ∫ z in A.cut.col D.c D.t D.d j k, A.cut.src D.c D.t D.d D.g z = 2 * π * A.n j k
  filler : ∀ j k, k < A.cut.K j →
    IsFillerPartition (A.cut.fillRect D.c D.t D.d j k) (A.cut.fillDensity D.c D.t D.d D.m D.ℓ D.g j k)
      D.m (A.n j k) (A.I j k) (A.piece j k)

/-- **Existence of the column cut and the filler partitions** (screening note, Lemmas 4.18, 4.21). -/
theorem exists_good {D : Data} (h : D.Hyp) : ∃ A : Asm, A.Good D := by
  classical
  obtain ⟨C, hC⟩ := h.cutHyp.exists_columnCut
  have hn : ∀ j k, ∃ n : ℕ, k < C.K j →
      1 ≤ n ∧ ∫ z in C.col D.c D.t D.d j k, C.src D.c D.t D.d D.g z = 2 * π * n := by
    intro j k
    by_cases hk : k < C.K j
    · obtain ⟨n, hn1, hn⟩ := hC.mass j k hk
      exact ⟨n, fun _ => ⟨hn1, hn⟩⟩
    · exact ⟨0, fun hk' => absurd hk' hk⟩
  choose n hn using hn
  have hF : ∀ j k, ∃ (I : Finset (ℕ × ℕ)) (piece : ℕ × ℕ → Rect), k < C.K j →
      IsFillerPartition (C.fillRect D.c D.t D.d j k) (C.fillDensity D.c D.t D.d D.m D.ℓ D.g j k)
        D.m (n j k) I piece := by
    intro j k
    by_cases hk : k < C.K j
    · obtain ⟨I, piece, hIP⟩ := h.cutHyp.exists_fillerPartition_col hC hk (hn j k hk).2
      exact ⟨I, piece, fun _ => hIP⟩
    · exact ⟨∅, fun _ => rect D.c D.t D.d 0, fun hk' => absurd hk' hk⟩
  choose I piece hIP using hF
  exact ⟨⟨C, n, I, piece⟩, ⟨hC, hn, hIP⟩⟩

/-! ### Index sets -/

/-- The columns `(j, k)`, `k < K_j`. -/
@[expose] noncomputable def cols : Finset (Fin 4 × ℕ) :=
  Finset.univ.biUnion fun j => (Finset.range (A.cut.K j)).image fun k => (j, k)

/-- The filler pieces `(j, k, p)`, `k < K_j`, `p ∈ I_{jk}`. -/
@[expose] noncomputable def pcs : Finset (Fin 4 × ℕ × (ℕ × ℕ)) :=
  A.cols.biUnion fun jk => (A.I jk.1 jk.2).image fun p => (jk.1, jk.2, p)

variable {A}

theorem mem_cols {jk : Fin 4 × ℕ} : jk ∈ A.cols ↔ jk.2 < A.cut.K jk.1 := by
  simp only [cols, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, Finset.mem_range,
    true_and]
  constructor
  · rintro ⟨j, k, hk, rfl⟩; exact hk
  · intro hk; exact ⟨jk.1, jk.2, hk, rfl⟩

theorem mem_pcs {i : Fin 4 × ℕ × (ℕ × ℕ)} :
    i ∈ A.pcs ↔ i.2.1 < A.cut.K i.1 ∧ i.2.2 ∈ A.I i.1 i.2.1 := by
  simp only [pcs, Finset.mem_biUnion, Finset.mem_image, mem_cols]
  constructor
  · rintro ⟨jk, hjk, p, hp, rfl⟩; exact ⟨hjk, hp⟩
  · rintro ⟨h1, h2⟩; exact ⟨(i.1, i.2.1), h1, i.2.2, h2, rfl⟩

variable (A)

/-- The column `Col_{jk}`. -/
@[expose] def col (jk : Fin 4 × ℕ) : Set ℂ := A.cut.col D.c D.t D.d jk.1 jk.2

/-- The flux cell `H_{jk}` (as a rectangle). -/
@[expose] noncomputable def fluxRect (jk : Fin 4 × ℕ) : Rect :=
  A.cut.fluxRect D.c D.t D.d D.ℓ jk.1 jk.2

/-- The filler part `P_{jk}` (as a rectangle). -/
@[expose] noncomputable def fillRect (jk : Fin 4 × ℕ) : Rect := A.cut.fillRect D.c D.t D.d jk.1 jk.2

/-- The piece `P_i`. -/
@[expose] def pc (i : Fin 4 × ℕ × (ℕ × ℕ)) : Rect := A.piece i.1 i.2.1 i.2.2

/-- The filler density of the column of the piece `i`. -/
@[expose] noncomputable def μ (i : Fin 4 × ℕ × (ℕ × ℕ)) : ℂ → ℝ :=
  A.cut.fillDensity D.c D.t D.d D.m D.ℓ D.g i.1 i.2.1

/-- The new charges: the piece centres. -/
@[expose] noncomputable def Z : Finset ℂ := A.pcs.image fun i => (A.pc i).centre

/-- The screened charges `Y = K ∪ Z`. -/
@[expose] noncomputable def Y : Finset ℂ := D.K ∪ A.Z

open scoped Classical in
/-- The radii `ρ`: `α` on `K`, `r₀` elsewhere. -/
@[expose] noncomputable def rho (x : ℂ) : ℝ := if x ∈ D.K then D.α x else D.r₀

/-- The flux-cell field `∑ V_k`. -/
@[expose] noncomputable def Vflux (x : ℂ) : ℂ :=
  ∑ jk ∈ A.cols, A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2 x

/-- The carry field `∑ V^c_j`. -/
@[expose] noncomputable def Vcarry (x : ℂ) : ℂ :=
  ∑ j : Fin 4, carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x

/-- The piece fields `Ψ_P`. -/
@[expose] noncomputable def Pfield (i : Fin 4 × ℕ × (ℕ × ℕ)) (x : ℂ) : ℂ :=
  (A.pc i).pieceField D.r₀ (A.μ D i) x

/-- The filler field `∑_P Ψ_P`. -/
@[expose] noncomputable def Vpiece (x : ℂ) : ℂ := ∑ i ∈ A.pcs, A.Pfield D i x

/-- **The screened field** `E' = ψX + ∑ V_k + ∑ V^c_j + ∑_P Ψ_P` (screening note, Definition 4.23). -/
@[expose] noncomputable def E' (x : ℂ) : ℂ := D.psiX x + A.Vflux D x + A.Vcarry D x + A.Vpiece D x

/-! ### Geometry of the columns -/

variable {D A}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

omit h in
theorem part (j : Fin 4) : IsPartition D.ℓ 0 (side D.t D.d) (A.cut.K j) (A.cut.u j) :=
  hA.isCut.partition j

theorem u_mem {jk : Fin 4 × ℕ} (hjk : jk ∈ A.cols) :
    A.cut.u jk.1 jk.2 ∈ Icc 0 (side D.t D.d) ∧ A.cut.u jk.1 (jk.2 + 1) ∈ Icc 0 (side D.t D.d) :=
  ⟨(hA.part jk.1).mem_Icc h.ℓ_pos.le (mem_cols.1 hjk).le,
    (hA.part jk.1).mem_Icc h.ℓ_pos.le (Nat.succ_le_of_lt (mem_cols.1 hjk))⟩

theorem col_subset_rect {jk : Fin 4 × ℕ} (hjk : jk ∈ A.cols) :
    A.col D jk ⊆ (rect D.c D.t D.d jk.1).carrier :=
  Rect.box_mono (Icc_subset_Icc (hA.u_mem h hjk).1.1 (hA.u_mem h hjk).2.2)
    (Icc_subset_Icc le_rfl (by simp))

/-- Distinct columns overlap in a null set. -/
theorem volume_col_inter {jk jk' : Fin 4 × ℕ} (hjk : jk ∈ A.cols) (hjk' : jk' ∈ A.cols)
    (hne : jk ≠ jk') : volume (A.col D jk ∩ A.col D jk') = 0 := by
  by_cases hj : jk.1 = jk'.1
  · have hk : jk.2 ≠ jk'.2 := fun hk => hne (Prod.ext hj hk)
    rw [col, col, ColumnCut.col, ColumnCut.col, ← hj, Rect.box_inter, Rect.volume_box]
    have hk' : jk'.2 < A.cut.K jk.1 := by rw [hj]; exact mem_cols.1 hjk'
    rw [(hA.part jk.1).volume_inter h.ℓ_pos.le (mem_cols.1 hjk) hk' hk, zero_mul]
  · refine measure_mono_null ?_ (volume_junctionLines D.c (offset D.t D.d))
    exact (inter_subset_inter (hA.col_subset_rect h hjk) (hA.col_subset_rect h hjk')).trans
      (rect_inter_subset h.offset_pos hj)

/-- **The columns cover the frame.** -/
theorem exists_mem_col {x : ℂ} (hx : x ∈ frameSet D.c D.t D.d) :
    ∃ jk ∈ A.cols, x ∈ A.col D jk := by
  rw [← iUnion_rect h.offset_pos.le, mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  rw [Rect.carrier_eq_box, Rect.mem_box, rect_width, rect_height] at hj
  obtain ⟨k, hk, hks⟩ := (hA.part j).exists_mem hj.1
  exact ⟨(j, k), mem_cols.2 hk, hks, hj.2⟩

theorem col_subset_frame {jk : Fin 4 × ℕ} (hjk : jk ∈ A.cols) :
    A.col D jk ⊆ frameSet D.c D.t D.d := by
  refine (hA.col_subset_rect h hjk).trans ?_
  rw [← iUnion_rect h.offset_pos.le]
  exact subset_iUnion (fun j => (rect D.c D.t D.d j).carrier) jk.1

omit hA in
theorem fluxRect_subset_col {jk : Fin 4 × ℕ} :
    (A.fluxRect D jk).carrier ⊆ A.col D jk := by
  rw [fluxRect, ColumnCut.carrier_fluxRect]
  exact Rect.box_mono subset_rfl (Icc_subset_Icc (by linarith [h.d_ge_ℓ, h.K4]) le_rfl)

omit h hA in
theorem fillRect_subset_col {jk : Fin 4 × ℕ} :
    (A.fillRect D jk).carrier ⊆ A.col D jk := by
  rw [fillRect, ColumnCut.carrier_fillRect]
  exact Rect.box_mono subset_rfl (Icc_subset_Icc le_rfl (by linarith))

omit h in
theorem pc_subset_fillRect {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) :
    (A.pc i).carrier ⊆ (A.fillRect D (i.1, i.2.1)).carrier := by
  show (A.pc i).carrier ⊆ (A.cut.fillRect D.c D.t D.d i.1 i.2.1).carrier
  rw [← (hA.filler i.1 i.2.1 (mem_pcs.1 hi).1).cover]
  exact subset_biUnion_of_mem (u := fun p => (A.piece i.1 i.2.1 p).carrier) (mem_pcs.1 hi).2

omit h in
theorem pc_subset_col {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) :
    (A.pc i).carrier ⊆ A.col D (i.1, i.2.1) :=
  (hA.pc_subset_fillRect hi).trans (Good.fillRect_subset_col)

omit h hA in
theorem col_mem_cols {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) : (i.1, i.2.1) ∈ A.cols :=
  mem_cols.2 (mem_pcs.1 hi).1

/-- Distinct pieces overlap in a null set. -/
theorem volume_pc_inter {i i' : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) (hi' : i' ∈ A.pcs)
    (hne : i ≠ i') : volume ((A.pc i).carrier ∩ (A.pc i').carrier) = 0 := by
  by_cases hc : (i.1, i.2.1) = (i'.1, i'.2.1)
  · have h1 : i.1 = i'.1 := (Prod.ext_iff.1 hc).1
    have h2 : i.2.1 = i'.2.1 := (Prod.ext_iff.1 hc).2
    have hp : i.2.2 ≠ i'.2.2 := fun hp => hne (Prod.ext h1 (Prod.ext h2 hp))
    have hmem' := (mem_pcs.1 hi').2
    rw [← h1, ← h2] at hmem'
    have := (hA.filler i.1 i.2.1 (mem_pcs.1 hi).1).null_inter i.2.2 (mem_pcs.1 hi).2 i'.2.2 hmem' hp
    simpa [pc, h1, h2] using this
  · exact measure_mono_null (inter_subset_inter (hA.pc_subset_col hi) (hA.pc_subset_col hi'))
      (hA.volume_col_inter h (Good.col_mem_cols hi) (Good.col_mem_cols hi') hc)

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
