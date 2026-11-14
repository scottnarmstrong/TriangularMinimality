/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.Lattice

/-!
# Periods of a planar lattice

`SandierSerfaty.Torus.exists_period_ratio`: every `ℤ`-lattice `Γ ⊆ ℂ` has the form `p (ℤ + ℤ τ)` with
`p ≠ 0` and `Im τ > 0`, and its covolume is `‖p‖² Im τ`. This reduces constructions on the torus
`ℂ / Γ` to the normalized torus `ℂ / (ℤ + ℤ τ)`.
-/

open MeasureTheory Module

public section

namespace SandierSerfaty

namespace Torus

theorem det_basisOneI (B : Basis (Fin 2) ℝ ℂ) :
    Complex.basisOneI.det B = (B 0).re * (B 1).im - (B 0).im * (B 1).re := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply]
  ring

/-- Every `ℤ`-lattice of `ℂ` is `p (ℤ + ℤ τ)` with `Im τ > 0`; its covolume is `‖p‖² Im τ`. -/
theorem exists_period_ratio (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    ∃ p τ : ℂ, p ≠ 0 ∧ 0 < τ.im ∧ (∀ z, z ∈ Γ ↔ ∃ m n : ℤ, z = p * (m + n * τ)) ∧
      ZLattice.covolume Γ = ‖p‖ ^ 2 * τ.im := by
  have := ZLattice.module_free ℝ Γ
  have := ZLattice.module_finite ℝ Γ
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Γ) = 2 := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ Γ, Complex.finrank_real_complex]
  set b : Basis (Fin 2) ℤ Γ :=
    (Module.Free.chooseBasis ℤ Γ).reindex (Fintype.equivFinOfCardEq hcard) with hb
  set B : Basis (Fin 2) ℝ ℂ := b.ofZLatticeBasis ℝ Γ with hB
  have hspan : Γ = Submodule.span ℤ (Set.range B) := (b.ofZLatticeBasis_span ℝ).symm
  have hcov := covolume_of_eq B hspan
  have hdet : (B 0).re * (B 1).im - (B 0).im * (B 1).re ≠ 0 := by
    rw [← det_basisOneI]
    exact (Complex.basisOneI.isUnit_det B).ne_zero
  have hcov' : ZLattice.covolume Γ = |(B 0).re * (B 1).im - (B 0).im * (B 1).re| := by
    rw [hcov, det_basisOneI]
  set u := B 0 with hu
  set v := B 1 with hv
  have hu0 : u ≠ 0 := by
    intro h; apply hdet; simp [h]
  have hmem : ∀ z, z ∈ Γ ↔ ∃ m n : ℤ, z = m * u + n * v := by
    intro z
    have hr : Set.range B = {u, v} := by
      ext x; simp [Set.mem_range, Fin.exists_fin_two, hu, hv, eq_comm]
    rw [hspan, hr, Submodule.mem_span_pair]
    constructor
    · rintro ⟨m, n, h⟩
      exact ⟨m, n, by rw [← h]; simp⟩
    · rintro ⟨m, n, h⟩
      exact ⟨m, n, by rw [h]; simp⟩
  have himv : (v / u).im = (u.re * v.im - u.im * v.re) / ‖u‖ ^ 2 := by
    rw [Complex.div_im, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hn : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · -- orientation reversed: use `-v`
    refine ⟨u, -(v / u), hu0, ?_, ?_, ?_⟩
    · rw [Complex.neg_im, himv]
      exact neg_pos.2 (div_neg_of_neg_of_pos hneg hn)
    · intro z
      rw [hmem]
      constructor
      · rintro ⟨m, n, h⟩
        exact ⟨m, -n, by rw [h]; push_cast; field_simp⟩
      · rintro ⟨m, n, h⟩
        exact ⟨m, -n, by rw [h]; push_cast; field_simp⟩
    · rw [hcov', Complex.neg_im, himv, abs_of_neg hneg]
      field_simp
  · refine ⟨u, v / u, hu0, ?_, ?_, ?_⟩
    · rw [himv]; exact div_pos hpos hn
    · intro z
      rw [hmem]
      constructor
      · rintro ⟨m, n, h⟩
        exact ⟨m, n, by rw [h]; field_simp⟩
      · rintro ⟨m, n, h⟩
        exact ⟨m, n, by rw [h]; field_simp⟩
    · rw [hcov', himv, abs_of_pos hpos]
      field_simp

end Torus

end SandierSerfaty

end
