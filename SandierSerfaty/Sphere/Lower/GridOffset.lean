/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.WallDist
public import SandierSerfaty.Sphere.Lower.Pigeonhole

/-!
# Random grid offset (sphere note, Lemma 6.12, the Fubini choice of the grid, abstract form)

For `θ ∈ ℝ²` and `R > 0`, `gridDist R θ z` is the distance from `z ∈ ℂ` to the walls of the grid
`θ + R ℤ²` (that is, to the boundary of the half-open grid square `K ∋ z`), and
`gridBand R θ a b = {z | a ≤ gridDist R θ z ≤ b}`.
`Lower.exists_offset_two_bands`: for every measurable `g : ℂ → ℝ≥0∞` with finite integral there is `θ ∈ [0,R]²`
with `(∫_{band i} g) R² ≤ 3 · 4 (bᵢ - aᵢ) R ∫ g` for two bands simultaneously (`i = 1, 2`). With
`strip⁺(K) = {z ∈ K | ℓ̃/2 ≤ dist(z, ∂K) ≤ 2ℓ̃ + 1}` and `lay(K) = {z ∈ K | dist(z, ∂K) ≤ 2}`, `Σ_K ∫_{strip⁺(K)} g`
is at most the integral of `g` over the first band, since the half-open squares `K` are pairwise disjoint.
-/

open MeasureTheory Set
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- Distance from `z` to the walls of the grid `θ + R ℤ²`. -/
@[expose] noncomputable def gridDist (R : ℝ) (θ : ℝ × ℝ) (z : ℂ) : ℝ :=
  min (wallDist R (z.re - θ.1)) (wallDist R (z.im - θ.2))

/-- The set of points at distance in `[a,b]` from the walls of the grid `θ + R ℤ²`. -/
@[expose] def gridBand (R : ℝ) (θ : ℝ × ℝ) (a b : ℝ) : Set ℂ :=
  {z | a ≤ gridDist R θ z ∧ gridDist R θ z ≤ b}

theorem measurable_gridDist (R : ℝ) : Measurable fun p : (ℝ × ℝ) × ℂ => gridDist R p.1 p.2 := by
  unfold gridDist
  exact ((measurable_wallDist R).comp (by fun_prop)).min ((measurable_wallDist R).comp (by fun_prop))

theorem measurableSet_gridBandProd (R a b : ℝ) :
    MeasurableSet {p : (ℝ × ℝ) × ℂ | a ≤ gridDist R p.1 p.2 ∧ gridDist R p.1 p.2 ≤ b} :=
  (measurableSet_le measurable_const (measurable_gridDist R)).inter
    (measurableSet_le (measurable_gridDist R) measurable_const)

/-- For fixed `z`, the offsets in `[0,R]²` placing `z` in the band `[a,b]` have measure `≤ 4 (b - a) R`. -/
theorem volume_offsets_le {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b) (z : ℂ) :
    volume {θ ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R | z ∈ gridBand R θ a b} ≤
      ENNReal.ofReal (4 * (b - a) * R) := by
  set S₁ : Set ℝ := {θ ∈ Icc (0 : ℝ) R | z.re - θ ∈ wallBand R a b} with hS₁
  set S₂ : Set ℝ := {θ ∈ Icc (0 : ℝ) R | z.im - θ ∈ wallBand R a b} with hS₂
  have hsub : {θ ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R | z ∈ gridBand R θ a b} ⊆
      S₁ ×ˢ Icc (0 : ℝ) R ∪ Icc (0 : ℝ) R ×ˢ S₂ := by
    rintro ⟨θ₁, θ₂⟩ ⟨⟨h1, h2⟩, hz⟩
    simp only [gridBand, gridDist, Set.mem_ofPred_eq] at hz
    rcases le_total (wallDist R (z.re - θ₁)) (wallDist R (z.im - θ₂)) with h | h
    · rw [min_eq_left h] at hz
      exact Or.inl ⟨⟨h1, hz⟩, h2⟩
    · rw [min_eq_right h] at hz
      exact Or.inr ⟨h1, ⟨h2, hz⟩⟩
  have e1 : volume S₁ ≤ ENNReal.ofReal (2 * (b - a)) := volume_wallBand_shift_le hR hab _
  have e2 : volume S₂ ≤ ENNReal.ofReal (2 * (b - a)) := volume_wallBand_shift_le hR hab _
  calc _ ≤ volume (S₁ ×ˢ Icc (0 : ℝ) R ∪ Icc (0 : ℝ) R ×ˢ S₂) := measure_mono hsub
    _ ≤ volume (S₁ ×ˢ Icc (0 : ℝ) R) + volume (Icc (0 : ℝ) R ×ˢ S₂) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * (b - a)) * ENNReal.ofReal R +
        ENNReal.ofReal R * ENNReal.ofReal (2 * (b - a)) := by
        rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.prod_prod,
          Real.volume_Icc, sub_zero]
        gcongr
    _ = ENNReal.ofReal (4 * (b - a) * R) := by
        rw [mul_comm (ENNReal.ofReal R), ← two_mul, ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring


/-- The joint integrand `(θ, z) ↦ 1_{band θ}(z) g(z)`. -/
@[expose] noncomputable def bandIntegrand (R a b : ℝ) (g : ℂ → ℝ≥0∞) : (ℝ × ℝ) × ℂ → ℝ≥0∞ :=
  {p : (ℝ × ℝ) × ℂ | a ≤ gridDist R p.1 p.2 ∧ gridDist R p.1 p.2 ≤ b}.indicator (fun p => g p.2)

theorem measurable_bandIntegrand (R a b : ℝ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable (bandIntegrand R a b g) :=
  (hg.comp measurable_snd).indicator (measurableSet_gridBandProd R a b)

theorem lintegral_bandIntegrand {R a b : ℝ} (θ : ℝ × ℝ) (g : ℂ → ℝ≥0∞) :
    ∫⁻ z, bandIntegrand R a b g (θ, z) = ∫⁻ z in gridBand R θ a b, g z := by
  have hm : MeasurableSet (gridBand R θ a b) :=
    (measurableSet_gridBandProd R a b).preimage (measurable_prodMk_left (x := θ))
  rw [← lintegral_indicator hm]
  rfl

theorem lintegral_offsets_le {R a b : ℝ} (hR : 0 < R) (hab : a ≤ b) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ θ in Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R, (∫⁻ z in gridBand R θ a b, g z) ≤
      ENNReal.ofReal (4 * (b - a) * R) * ∫⁻ z, g z := by
  set s : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R with hs
  have hΦ := measurable_bandIntegrand R a b hg
  have h1 : ∀ θ : ℝ × ℝ, ∫⁻ z in gridBand R θ a b, g z = ∫⁻ z, bandIntegrand R a b g (θ, z) :=
    fun θ => (lintegral_bandIntegrand θ g).symm
  simp_rw [h1]
  rw [lintegral_lintegral_swap (μ := volume.restrict s) (ν := (volume : Measure ℂ))
    (f := fun θ z => bandIntegrand R a b g (θ, z)) hΦ.aemeasurable]
  calc ∫⁻ z, ∫⁻ θ in s, bandIntegrand R a b g (θ, z)
      ≤ ∫⁻ z, g z * ENNReal.ofReal (4 * (b - a) * R) := by
        refine lintegral_mono fun z => ?_
        have hmeas : MeasurableSet {θ : ℝ × ℝ | z ∈ gridBand R θ a b} :=
          (measurableSet_gridBandProd R a b).preimage (measurable_prodMk_right (y := z))
        have : (fun θ : ℝ × ℝ => bandIntegrand R a b g (θ, z)) =
            {θ : ℝ × ℝ | z ∈ gridBand R θ a b}.indicator (fun _ => g z) := by
          ext θ
          by_cases h : a ≤ gridDist R θ z ∧ gridDist R θ z ≤ b <;>
            simp [bandIntegrand, Set.indicator, gridBand, h]
        rw [this, lintegral_indicator_const hmeas, Measure.restrict_apply hmeas]
        gcongr
        refine le_trans (measure_mono ?_) (volume_offsets_le hR hab z)
        intro θ hθ
        exact ⟨hθ.2, hθ.1⟩
    _ = ENNReal.ofReal (4 * (b - a) * R) * ∫⁻ z, g z := by
        rw [lintegral_mul_const _ hg, mul_comm]


theorem measurable_bandLintegral (R a b : ℝ) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun θ : ℝ × ℝ => ∫⁻ z in gridBand R θ a b, g z := by
  have := (measurable_bandIntegrand R a b hg).lintegral_prod_right'
    (ν := (volume : Measure ℂ))
  simpa [lintegral_bandIntegrand] using this

/-- **Lemma 6.12 (Fubini choice of the grid), abstract form.** For every measurable `g ≥ 0` with finite integral
there is an offset `θ ∈ [0,R]²` such that, for two bands `[a₁,b₁]`, `[a₂,b₂]` of distances to the grid walls, the
`g`-mass of the band is at most `3 · 4 (bᵢ - aᵢ) / R` times the total mass:
`(∫_{band i} g) R² ≤ 3 · 4 (bᵢ - aᵢ) R · ∫ g`. -/
theorem exists_offset_two_bands {R a₁ b₁ a₂ b₂ : ℝ} (hR : 0 < R) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) (hG : ∫⁻ z, g z ≠ ⊤) :
    ∃ θ ∈ Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R,
      (∫⁻ z in gridBand R θ a₁ b₁, g z) * ENNReal.ofReal (R * R) ≤
        3 * (ENNReal.ofReal (4 * (b₁ - a₁) * R) * ∫⁻ z, g z) ∧
      (∫⁻ z in gridBand R θ a₂ b₂, g z) * ENNReal.ofReal (R * R) ≤
        3 * (ENNReal.ofReal (4 * (b₂ - a₂) * R) * ∫⁻ z, g z) := by
  set s : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (0 : ℝ) R with hs
  have hsm : MeasurableSet s := measurableSet_Icc.prod measurableSet_Icc
  have hνs : (volume : Measure (ℝ × ℝ)) s = ENNReal.ofReal (R * R) := by
    rw [hs, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul hR.le]
  have hRR : 0 < R * R := mul_pos hR hR
  have hE : ∀ a b : ℝ, a ≤ b → ∫⁻ θ in s, (∫⁻ z in gridBand R θ a b, g z) ≠ ⊤ := by
    intro a b hab
    refine ne_top_of_le_ne_top ?_ (lintegral_offsets_le hR hab hg)
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG
  obtain ⟨θ, hθ, e1, e2⟩ := exists_two_le_three_avg (volume : Measure (ℝ × ℝ)) s hsm
    (by rw [hνs]; simp [hRR]) (by rw [hνs]; exact ENNReal.ofReal_ne_top)
    (measurable_bandLintegral R a₁ b₁ hg) (measurable_bandLintegral R a₂ b₂ hg)
    (hE a₁ b₁ h₁) (hE a₂ b₂ h₂)
  refine ⟨θ, hθ, ?_, ?_⟩
  · rw [hνs] at e1
    exact e1.trans (by gcongr; exact lintegral_offsets_le hR h₁ hg)
  · rw [hνs] at e2
    exact e2.trans (by gcongr; exact lintegral_offsets_le hR h₂ hg)


end Lower

end Sphere

end SandierSerfaty

end
