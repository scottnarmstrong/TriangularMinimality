/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.LatticeCount
public import SandierSerfaty.Torus.Lattice
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Averages of periodic functions over large squares

Let `Γ ⊆ ℂ` be a lattice of covolume `1`, `F` a bounded measurable fundamental domain, and
`G : ℂ → ℝ≥0∞` a `Γ`-periodic function with `∫⁻_F G < ∞`. Then
`ℓ⁻² ∫⁻_{□_ℓ} G → ∫⁻_F G` as `ℓ → ∞` (`SandierSerfaty.Torus.tendsto_lintegral_cube_div`). The proof
tiles by translates of `F`: the translates of `F` by the lattice points of `□_{ℓ - 2d}` lie inside `□_ℓ`,
which lies inside the union of the translates by the lattice points of `□_{ℓ + 2d}`; here `F ⊆ B(0, d)`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal Pointwise

public section

namespace SandierSerfaty

namespace Torus

section FundamentalDomain

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- A bounded measurable fundamental domain of `Γ` such that every point has a translate in it. -/
theorem exists_fundamentalDomain :
    ∃ F : Set ℂ, IsAddFundamentalDomain Γ F volume ∧ MeasurableSet F ∧ Bornology.IsBounded F ∧
      ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F := by
  let b := Module.Free.chooseBasis ℤ Γ
  have hspan := b.ofZLatticeBasis_span ℝ
  refine ⟨ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ), ZLattice.isAddFundamentalDomain b volume,
    ZSpan.fundamentalDomain_measurableSet _, ZSpan.fundamentalDomain_isBounded _, fun x => ?_⟩
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain (b.ofZLatticeBasis ℝ) x
  have hvΓ : (v : ℂ) ∈ Γ := (SetLike.ext_iff.1 hspan _).1 v.2
  refine ⟨-(v : ℂ), Γ.neg_mem hvΓ, ?_⟩
  have hv' : (v : ℂ) + x ∈ ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) := hv
  rwa [sub_neg_eq_add, add_comm]

end FundamentalDomain

section Tiling

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- The translate `γ + F`. -/
@[expose] def translate (F : Set ℂ) (γ : ℂ) : Set ℂ := (fun x => x - γ) ⁻¹' F

theorem measurableSet_translate {F : Set ℂ} (hF : MeasurableSet F) (γ : ℂ) :
    MeasurableSet (translate F γ) :=
  hF.preimage (measurable_id.sub_const γ)

theorem mem_translate {F : Set ℂ} {γ x : ℂ} : x ∈ translate F γ ↔ x - γ ∈ F := Iff.rfl

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem lintegral_translate {F : Set ℂ} (hF : MeasurableSet F) {G : ℂ → ℝ≥0∞}
    (hG : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x) {γ : ℂ} (hγ : γ ∈ Γ) :
    ∫⁻ x in translate F γ, G x = ∫⁻ x in F, G x := by
  rw [← lintegral_indicator (measurableSet_translate hF γ), ← lintegral_indicator hF]
  rw [← lintegral_add_right_eq_self (μ := volume) (fun x => (translate F γ).indicator G x) γ]
  congr 1
  funext x
  by_cases h : x ∈ F
  · have : x + γ ∈ translate F γ := by simpa [mem_translate] using h
    rw [indicator_of_mem h, indicator_of_mem this]
    exact hG γ hγ x
  · have : x + γ ∉ translate F γ := by simpa [mem_translate] using h
    rw [indicator_of_notMem h, indicator_of_notMem this]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem translate_eq_vadd {F : Set ℂ} {γ : ℂ} (hγ : γ ∈ Γ) :
    translate F γ = (⟨γ, hγ⟩ : Γ) +ᵥ F := by
  ext x
  rw [mem_translate, Set.mem_vadd_set_iff_neg_vadd_mem]
  show x - γ ∈ F ↔ -γ + x ∈ F
  rw [neg_add_eq_sub]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem aedisjoint_translate {F : Set ℂ} (hF : IsAddFundamentalDomain Γ F volume) {γ γ' : ℂ}
    (hγ : γ ∈ Γ) (hγ' : γ' ∈ Γ) (hne : γ ≠ γ') :
    AEDisjoint volume (translate F γ) (translate F γ') := by
  rw [translate_eq_vadd hγ, translate_eq_vadd hγ']
  exact hF.aedisjoint (show (⟨γ, hγ⟩ : Γ) ≠ ⟨γ', hγ'⟩ from fun h => hne (Subtype.mk.inj h))

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem lintegral_biUnion_translate {F : Set ℂ} (hF : IsAddFundamentalDomain Γ F volume)
    (hFm : MeasurableSet F) {G : ℂ → ℝ≥0∞} (hG : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x) (S : Finset ℂ)
    (hS : ∀ γ ∈ S, γ ∈ Γ) :
    ∫⁻ x in ⋃ γ ∈ S, translate F γ, G x = S.card * ∫⁻ x in F, G x := by
  rw [lintegral_biUnion_finset₀]
  · rw [Finset.sum_congr rfl fun γ hγ => lintegral_translate hFm hG (hS γ hγ), Finset.sum_const,
      nsmul_eq_mul]
  · intro γ hγ γ' hγ' hne
    exact aedisjoint_translate hF (hS γ hγ) (hS γ' hγ') hne
  · intro γ _
    exact (measurableSet_translate hFm γ).nullMeasurableSet

theorem abs_re_le_of_mem_closedBall {z : ℂ} {d : ℝ} (hz : z ∈ closedBall (0 : ℂ) d) : |z.re| ≤ d :=
  (Complex.abs_re_le_norm z).trans (by simpa using hz)

theorem abs_im_le_of_mem_closedBall {z : ℂ} {d : ℝ} (hz : z ∈ closedBall (0 : ℂ) d) : |z.im| ≤ d :=
  (Complex.abs_im_le_norm z).trans (by simpa using hz)

omit [IsZLattice ℝ Γ] in
/-- **Tiling bounds.** The integral of a periodic function over `□_ℓ` is squeezed between the integrals
over the unions of translates of `F` lying inside `□_ℓ` and covering `□_ℓ`. -/
theorem lintegral_cube_bounds {F : Set ℂ} (hF : IsAddFundamentalDomain Γ F volume)
    (hFm : MeasurableSet F) {d : ℝ} (hd : F ⊆ closedBall 0 d)
    (hcov : ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F) {G : ℂ → ℝ≥0∞} (hG : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x)
    (ℓ : ℝ) :
    (((Γ : Set ℂ) ∩ cube (ℓ - 2 * d)).ncard : ℝ≥0∞) * ∫⁻ x in F, G x ≤ ∫⁻ x in cube ℓ, G x ∧
      ∫⁻ x in cube ℓ, G x ≤ (((Γ : Set ℂ) ∩ cube (ℓ + 2 * d)).ncard : ℝ≥0∞) * ∫⁻ x in F, G x := by
  have hfin1 := finite_lattice_inter (Γ := Γ) (isBounded_cube (ℓ - 2 * d))
  have hfin2 := finite_lattice_inter (Γ := Γ) (isBounded_cube (ℓ + 2 * d))
  constructor
  · have := lintegral_biUnion_translate hF hFm hG hfin1.toFinset
      (fun γ hγ => (hfin1.mem_toFinset.1 hγ).1)
    rw [← Set.ncard_eq_toFinset_card _ hfin1] at this
    rw [← this]
    refine lintegral_mono_set ?_
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨γ, hγS, hx⟩ := hx
    have hγ := (hfin1.mem_toFinset.1 hγS).2
    have hxF : x - γ ∈ F := hx
    have hb := hd hxF
    rw [mem_cube_iff] at hγ ⊢
    have h1 := abs_re_le_of_mem_closedBall hb
    have h2 := abs_im_le_of_mem_closedBall hb
    have e1 : x.re = γ.re + (x - γ).re := by simp
    have e2 : x.im = γ.im + (x - γ).im := by simp
    constructor
    · calc |x.re| = |γ.re + (x - γ).re| := by rw [← e1]
        _ ≤ |γ.re| + |(x - γ).re| := abs_add_le _ _
        _ ≤ ℓ / 2 := by linarith [hγ.1]
    · calc |x.im| = |γ.im + (x - γ).im| := by rw [← e2]
        _ ≤ |γ.im| + |(x - γ).im| := abs_add_le _ _
        _ ≤ ℓ / 2 := by linarith [hγ.2]
  · have := lintegral_biUnion_translate hF hFm hG hfin2.toFinset
      (fun γ hγ => (hfin2.mem_toFinset.1 hγ).1)
    rw [← Set.ncard_eq_toFinset_card _ hfin2] at this
    rw [← this]
    refine lintegral_mono_set ?_
    intro x hx
    obtain ⟨γ, hγ, hxF⟩ := hcov x
    simp only [mem_iUnion]
    refine ⟨γ, hfin2.mem_toFinset.2 ⟨hγ, ?_⟩, hxF⟩
    have hb := hd hxF
    rw [mem_cube_iff] at hx ⊢
    have h1 := abs_re_le_of_mem_closedBall hb
    have h2 := abs_im_le_of_mem_closedBall hb
    have e1 : γ.re = x.re - (x - γ).re := by simp
    have e2 : γ.im = x.im - (x - γ).im := by simp
    constructor
    · calc |γ.re| = |x.re - (x - γ).re| := by rw [← e1]
        _ ≤ |x.re| + |(x - γ).re| := abs_sub _ _
        _ ≤ (ℓ + 2 * d) / 2 := by linarith [hx.1]
    · calc |γ.im| = |x.im - (x - γ).im| := by rw [← e2]
        _ ≤ |x.im| + |(x - γ).im| := abs_sub _ _
        _ ≤ (ℓ + 2 * d) / 2 := by linarith [hx.2]

omit [IsZLattice ℝ Γ] in
/-- The integral of a periodic function with finite cell integral over a square is finite. -/
theorem lintegral_cube_ne_top {F : Set ℂ} (hF : IsAddFundamentalDomain Γ F volume)
    (hFm : MeasurableSet F) {d : ℝ} (hd : F ⊆ closedBall 0 d)
    (hcov : ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F) {G : ℂ → ℝ≥0∞} (hG : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x)
    (hJ : ∫⁻ x in F, G x ≠ ∞) (ℓ : ℝ) : ∫⁻ x in cube ℓ, G x ≠ ∞ := by
  have := (lintegral_cube_bounds hF hFm hd hcov hG ℓ).2
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hJ) this

/-- **Averages of periodic functions over large squares.** -/
theorem tendsto_lintegral_cube_div (hΓ : ZLattice.covolume Γ = 1) {F : Set ℂ}
    (hF : IsAddFundamentalDomain Γ F volume) (hFm : MeasurableSet F) {d : ℝ}
    (hd : F ⊆ closedBall 0 d) (hcov : ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F) {G : ℂ → ℝ≥0∞}
    (hG : ∀ γ ∈ Γ, ∀ x, G (x + γ) = G x) :
    Tendsto (fun ℓ : ℝ => ENNReal.ofReal ((ℓ ^ 2)⁻¹) * ∫⁻ x in cube ℓ, G x) atTop
      (𝓝 (∫⁻ x in F, G x)) := by
  set J := ∫⁻ x in F, G x with hJdef
  have hlo : Tendsto (fun ℓ : ℝ => ENNReal.ofReal
      ((((Γ : Set ℂ) ∩ cube (ℓ - 2 * d)).ncard : ℝ) / ℓ ^ 2) * J) atTop (𝓝 J) := by
    have h := tendsto_ncard_inter_cube_add_div Γ hΓ (-(2 * d))
    simp only [← sub_eq_add_neg] at h
    have h2 := ENNReal.tendsto_ofReal h
    rw [ENNReal.ofReal_one] at h2
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inl one_ne_zero)
  have hup : Tendsto (fun ℓ : ℝ => ENNReal.ofReal
      ((((Γ : Set ℂ) ∩ cube (ℓ + 2 * d)).ncard : ℝ) / ℓ ^ 2) * J) atTop (𝓝 J) := by
    have h := tendsto_ncard_inter_cube_add_div Γ hΓ (2 * d)
    have h2 := ENNReal.tendsto_ofReal h
    rw [ENNReal.ofReal_one] at h2
    simpa using ENNReal.Tendsto.mul_const h2 (Or.inl one_ne_zero)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    have h := (lintegral_cube_bounds hF hFm hd hcov hG ℓ).1
    have e : ENNReal.ofReal ((((Γ : Set ℂ) ∩ cube (ℓ - 2 * d)).ncard : ℝ) / ℓ ^ 2) * J =
        ENNReal.ofReal ((ℓ ^ 2)⁻¹) * ((((Γ : Set ℂ) ∩ cube (ℓ - 2 * d)).ncard : ℝ≥0∞) * J) := by
      rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 3
      ring
    rw [e]
    exact mul_le_mul_right h _
  · filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    have h := (lintegral_cube_bounds hF hFm hd hcov hG ℓ).2
    have e : ENNReal.ofReal ((((Γ : Set ℂ) ∩ cube (ℓ + 2 * d)).ncard : ℝ) / ℓ ^ 2) * J =
        ENNReal.ofReal ((ℓ ^ 2)⁻¹) * ((((Γ : Set ℂ) ∩ cube (ℓ + 2 * d)).ncard : ℝ≥0∞) * J) := by
      rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 3
      ring
    rw [e]
    exact mul_le_mul_right h _

end Tiling

end Torus

end SandierSerfaty

end
