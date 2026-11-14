/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.PunctureCauchy
public import SandierSerfaty.Whole.Comparison
public import SandierSerfaty.Whole.TorusCurl
public import SandierSerfaty.Jellium.TriangularEnergyLimit
public import SandierSerfaty.Jellium.TriangularRadii
public import SandierSerfaty.Geometry.LatticeAverage
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy

/-!
# The periodic average of the triangular field: `W(E_△) = W_tri`

**Theorem** (`wholeEnergy_paperTriangularField`). For every cutoff family `χ`,
`W(E_△) = W_tri` (comparison note, Lemmas `lem:periodic`, `lem:tri`; paper Lemma `red:periodic-average`).

## Proof

Write `Λ = Λ_△`, `E = E_△ = -∇h_△` and `P_η(χ_R)` for the real puncture expression
(`punctureReal`). The nonzero lattice points have norm `≥ 1`, `E` is `Λ`-periodic, `|E - κ(· - p)| ≤ M` on
`B(p, ¼) ∖ {p}` (local form of `h_△`) and `E` is bounded off `⋃ B(p, ε)`. So:

* *Uniformity in `R`* (`abs_punctureReal_sub_le`, then `η' ↓ 0`):
  `|W(E, χ_R) - P_η(χ_R)| ≤ #(Λ ∩ □_{2R+1}) c(η)` for `0 < η ≤ ¼`, with `c(η) = O(η)`.
* *Periodic average at fixed `η`*: `χ_R` lies between `1_{□_{2R-2}}` and `1_{□_{2R}}`, so
  `(2R)⁻² P_η(χ_R) → T(η) = ½ ∫_F 1_{far η} |∇h_△|² + π log η` (`tendsto_lintegral_cube_div`,
  lattice counting), `F` a bounded fundamental domain.
* *The torus limit*: `T(η) → W_tri` as `η ↓ 0` (`Torus.tendsto_puncture`, the definition of `torusEnergy`).

Hence `(2R)⁻² W(E, χ_R)` is eventually within `2 c(η) + |T(η) - W_tri| + o(1)` of `W_tri`, for every
small `η`: it tends to `W_tri`, and so does its `limsup`.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Whole

open Screening

/-! ### Local data of `E_△` -/

theorem triangular_hmin : ∀ γ ∈ triangularLattice, γ ≠ 0 → 1 ≤ ‖γ‖ :=
  fun _ hγ h0 => triangularLattice_norm_ge_one hγ h0

theorem triangular_sep : ∀ p ∈ (triangularLattice : Set ℂ), ∀ q ∈ (triangularLattice : Set ℂ),
    p ≠ q → 1 ≤ ‖p - q‖ := fun _ hp _ hq hpq =>
  triangularLattice_norm_ge_one (triangularLattice.sub_mem hp hq) (sub_ne_zero.2 hpq)

theorem paperTriangularField_add {γ : ℂ} (hγ : γ ∈ triangularLattice) (x : ℂ) :
    paperTriangularField (x + γ) = paperTriangularField x := by
  simp only [paperTriangularField]
  rw [Torus.gradient_add_periodic isTorusPotential_triangular.1 hγ x]

/-- `|E_△ - κ(· - p)| ≤ M` on `B(p, ¼) ∖ {p}`, uniformly in `p ∈ Λ_△`. -/
theorem exists_near_bound_paperTriangularField : ∃ M : ℝ, 0 ≤ M ∧
    ∀ p ∈ (triangularLattice : Set ℂ), ∀ x : ℂ, 0 < ‖x - p‖ → ‖x - p‖ < 1 / 4 →
      ‖paperTriangularField x - kernel (x - p)‖ ≤ M := by
  obtain ⟨v, hv, -, hloc⟩ := Torus.exists_local_form_ball triangular_hmin isTorusPotential_triangular
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 4)).exists_bound_of_continuousOn
    ((Torus.continuousOn_gradient hv).mono Torus.closedBall_quarter_subset)
  refine ⟨max M 0, le_max_right _ _, fun p hp x hx0 hx => ?_⟩
  have hy1 : x - p ∈ ball (0 : ℂ) 1 := by rw [mem_ball_zero_iff]; linarith
  have hy0 : x - p ≠ 0 := norm_pos_iff.1 hx0
  have e : paperTriangularField x = paperTriangularField (x - p) := by
    have := paperTriangularField_add hp (x - p); rwa [sub_add_cancel] at this
  have hg := Torus.gradient_eq_of_local hv hloc hy1 hy0
  have e2 : paperTriangularField x - kernel (x - p) = -gradient v (x - p) := by
    rw [e]; simp only [paperTriangularField]; rw [hg, kernel]; abel
  rw [e2, norm_neg]
  exact (hM _ (mem_closedBall_zero_iff.2 hx.le)).trans (le_max_left _ _)

theorem punctured_triangular_eq (ε : ℝ) :
    punctured (triangularLattice : Set ℂ) ε = Torus.farSet triangularLattice ε := by
  ext x; rw [mem_punctured]; exact Iff.rfl

/-- `E_△` is bounded off `⋃_{p ∈ Λ_△} B(p, ε)`. -/
theorem exists_far_bound_paperTriangularField {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ x ∈ punctured (triangularLattice : Set ℂ) ε, ‖paperTriangularField x‖ ≤ C := by
  obtain ⟨F, -, -, hFb, hcov⟩ := Torus.exists_fundamentalDomain triangularLattice
  obtain ⟨C, hC⟩ := Torus.exists_bound_gradient_far isTorusPotential_triangular hFb hcov hε
  refine ⟨C, fun x hx => ?_⟩
  rw [punctured_triangular_eq] at hx
  simpa [paperTriangularField] using hC x hx

theorem IsCutoffFamily.eq_zero_of_notMem {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) {R : ℝ}
    (hR : 1 < R) : ∀ x ∉ cube (2 * R), χ R x = 0 := fun _ hx =>
  image_eq_zero_of_notMem_tsupport fun h => hx (IsCutoffFamily.tsupport_subset_cube hχ hR h)

/-! ### Uniformity in `R` -/

/-- `|W(E_△, χ_R) - P_η(χ_R)| ≤ #(Λ_△ ∩ □_{2R+1}) c(η)` for `0 < η ≤ ¼`. -/
theorem abs_localEnergy_toReal_sub_le {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) {L : ℝ}
    (hL : ∀ R : ℝ, 1 < R → ∀ x : ℂ, ‖gradient (χ R) x‖ ≤ L) {M : ℝ} (hM : 0 ≤ M)
    (hnear : ∀ p ∈ (triangularLattice : Set ℂ), ∀ x : ℂ, 0 < ‖x - p‖ → ‖x - p‖ < 1 / 4 →
      ‖paperTriangularField x - kernel (x - p)‖ ≤ M)
    {R : ℝ} (hR : 1 < R) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 4) :
    |(localEnergy (triangularLattice : Set ℂ) paperTriangularField (χ R)).toReal -
        punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η| ≤
      (((triangularLattice : Set ℂ) ∩ cube (2 * R + 1)).ncard : ℝ) *
        (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2) := by
  have hE := isAdmissibleField_paperTriangularField
  obtain ⟨hsm, hcs, h01, -, -⟩ := hχ.1 R hR
  obtain ⟨w, hw⟩ := exists_tendsto_punctureFunctional hE hsm hcs
  have hloc : (localEnergy (triangularLattice : Set ℂ) paperTriangularField (χ R)).toReal = w := by
    unfold localEnergy; rw [hw.limsup_eq, EReal.toReal_coe]
  rw [hloc]
  have hkey : ∀ η' ∈ Ioo 0 η,
      punctureFunctional (triangularLattice : Set ℂ) paperTriangularField (χ R) η' =
        punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η' ∧
      |punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η' -
          punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η| ≤
        (((triangularLattice : Set ℂ) ∩ cube (2 * R + 1)).ncard : ℝ) *
          (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2) := fun η' hη' => by
    have h := abs_punctureReal_sub_le hE.1 triangular_sep hE.2.1.aestronglyMeasurable hM hnear
      (fun ε hε => exists_far_bound_paperTriangularField hε) hsm.continuous (fun x => (h01 x).1)
      (fun x => (h01 x).2) (lipschitz_of_gradient_le hsm (hL R hR)) (IsCutoffFamily.eq_zero_of_notMem hχ hR)
      hη'.1 hη'.2 hη
    exact ⟨h.1, h.2.2⟩
  have hlim : Tendsto (fun η' => punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η')
      (𝓝[>] 0) (𝓝 w) := by
    have h1 : Tendsto
        (fun η' => (punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η' : EReal))
        (𝓝[>] 0) (𝓝 (w : EReal)) := by
      refine hw.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hη0] with η' hη' using (hkey η' hη').1
    exact EReal.tendsto_coe.1 h1
  have hev : ∀ᶠ η' in 𝓝[>] 0,
      |punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η' -
          punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η| ≤
        (((triangularLattice : Set ℂ) ∩ cube (2 * R + 1)).ncard : ℝ) *
          (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2) := by
    filter_upwards [Ioo_mem_nhdsGT hη0] with η' hη' using (hkey η' hη').2
  exact le_of_tendsto ((hlim.sub_const _).abs) hev

/-! ### The periodic average at fixed `η` -/

/-- The periodic density `1_{far η} |∇h_△|²` of the triangular cell energy. -/
@[expose] noncomputable def triCellDensity (η : ℝ) : ℂ → ℝ≥0∞ :=
  (Torus.farSet triangularLattice η).indicator
    (Torus.cellGradSq (torusPotential triangularLattice fun _ : Fin 1 => (0 : ℂ)))

theorem triCellDensity_add {η : ℝ} {γ : ℂ} (hγ : γ ∈ triangularLattice) (x : ℂ) :
    triCellDensity η (x + γ) = triCellDensity η x := by
  unfold triCellDensity
  by_cases hx : x ∈ Torus.farSet triangularLattice η
  · rw [indicator_of_mem hx, indicator_of_mem ((Torus.farSet_add_periodic hγ).2 hx),
      Torus.cellGradSq_add_periodic isTorusPotential_triangular.1 hγ]
  · rw [indicator_of_notMem hx,
      indicator_of_notMem fun h => hx ((Torus.farSet_add_periodic hγ).1 h)]

theorem integral_punctured_eq_lintegral (η : ℝ) {ξ : ℂ → ℝ} (hξc : Continuous ξ)
    (hξ0 : ∀ x, 0 ≤ ξ x) :
    ∫ x in punctured (triangularLattice : Set ℂ) η, ξ x * ‖paperTriangularField x‖ ^ 2 =
      (∫⁻ x, ENNReal.ofReal (ξ x) * triCellDensity η x).toReal := by
  have hs := measurableSet_punctured (triangularLattice : Set ℂ) η
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => mul_nonneg (hξ0 x) (sq_nonneg _))
    (hξc.aestronglyMeasurable.mul
      (isAdmissibleField_paperTriangularField.2.1.aestronglyMeasurable.norm.pow 2)).restrict]
  congr 1
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun x => ?_
  unfold triCellDensity
  by_cases hx : x ∈ Torus.farSet triangularLattice η
  · have hx' : x ∈ punctured (triangularLattice : Set ℂ) η := by
      rw [punctured_triangular_eq]; exact hx
    rw [indicator_of_mem hx', indicator_of_mem hx, Torus.cellGradSq, ENNReal.ofReal_mul (hξ0 x)]
    simp [paperTriangularField]
  · have hx' : x ∉ punctured (triangularLattice : Set ℂ) η := by
      rw [punctured_triangular_eq]; exact hx
    rw [indicator_of_notMem hx', indicator_of_notMem hx, mul_zero]

/-- `(ℓ - 2)` in place of `ℓ` does not change a quadratic average. -/
theorem tendsto_sq_inv_mul_sub_two {u : ℝ → ℝ} {A : ℝ}
    (h : Tendsto (fun ℓ => (ℓ ^ 2)⁻¹ * u ℓ) atTop (𝓝 A)) :
    Tendsto (fun ℓ => (ℓ ^ 2)⁻¹ * u (ℓ - 2)) atTop (𝓝 A) := by
  have h1 := h.comp (tendsto_atTop_add_const_right atTop (-2) tendsto_id)
  have h2 : Tendsto (fun ℓ : ℝ => (1 - 2 / ℓ) ^ 2) atTop (𝓝 ((1 - 0) ^ 2)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop tendsto_id)).pow 2
  have h3 := h2.mul h1
  rw [show ((1 : ℝ) - 0) ^ 2 * A = A by ring] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 2] with ℓ hℓ
  simp only [Function.comp, id, ← sub_eq_add_neg]
  have h0 : ℓ ≠ 0 := by linarith
  have h2' : ℓ - 2 ≠ 0 := by linarith
  field_simp

theorem tendsto_two_mul_atTop : Tendsto (fun R : ℝ => 2 * R) atTop atTop :=
  tendsto_id.const_mul_atTop' (by norm_num)

/-- `(2R)⁻² ∫_{Ω_η} χ_R |E_△|² → ∫_F 1_{far η} |∇h_△|²`. -/
theorem tendsto_integral_punctured_div {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) {η : ℝ}
    (hη : 0 < η) {F : Set ℂ} (hF : IsAddFundamentalDomain triangularLattice F volume)
    (hFm : MeasurableSet F) {d : ℝ} (hd : F ⊆ closedBall 0 d)
    (hcov : ∀ x : ℂ, ∃ γ ∈ triangularLattice, x - γ ∈ F) :
    Tendsto (fun R : ℝ => ((2 * R) ^ 2)⁻¹ *
        ∫ x in punctured (triangularLattice : Set ℂ) η, χ R x * ‖paperTriangularField x‖ ^ 2)
      atTop (𝓝 (∫⁻ x in F, triCellDensity η x).toReal) := by
  have hGper : ∀ γ ∈ triangularLattice, ∀ x, triCellDensity η (x + γ) = triCellDensity η x :=
    fun γ hγ x => triCellDensity_add hγ x
  have hJ : ∫⁻ x in F, triCellDensity η x ≠ ⊤ :=
    Torus.lintegral_far_ne_top isTorusPotential_triangular (isBounded_closedBall.subset hd) hcov hη
  have hfin : ∀ ℓ, ∫⁻ x in cube ℓ, triCellDensity η x ≠ ⊤ :=
    Torus.lintegral_cube_ne_top hF hFm hd hcov hGper hJ
  have hcube : Tendsto (fun ℓ : ℝ => (ℓ ^ 2)⁻¹ * (∫⁻ x in cube ℓ, triCellDensity η x).toReal) atTop
      (𝓝 (∫⁻ x in F, triCellDensity η x).toReal) := by
    have := (ENNReal.tendsto_toReal hJ).comp
      (Torus.tendsto_lintegral_cube_div Torus.covolume_triangularLattice hF hFm hd hcov hGper)
    refine this.congr fun ℓ => ?_
    simp only [Function.comp, ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.2 (sq_nonneg ℓ))]
  have hup := hcube.comp tendsto_two_mul_atTop
  have hlo := (tendsto_sq_inv_mul_sub_two hcube).comp tendsto_two_mul_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with R hR
    obtain ⟨hsm, -, h01, -, -⟩ := hχ.1 R hR
    simp only [Function.comp]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [integral_punctured_eq_lintegral η hsm.continuous fun x => (h01 x).1]
    have hle : ∫⁻ x in cube (2 * R - 2), triCellDensity η x ≤
        ∫⁻ x, ENNReal.ofReal (χ R x) * triCellDensity η x := by
      rw [← lintegral_indicator (isCompact_cube _).measurableSet]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ cube (2 * R - 2)
      · rw [indicator_of_mem hx, IsCutoffFamily.eq_one hχ hR x (by rwa [show 2 * (R - 1) = 2 * R - 2 by ring]),
          ENNReal.ofReal_one, one_mul]
      · rw [indicator_of_notMem hx]; exact zero_le
    have hle2 : ∫⁻ x, ENNReal.ofReal (χ R x) * triCellDensity η x ≤
        ∫⁻ x in cube (2 * R), triCellDensity η x := by
      rw [← lintegral_indicator (isCompact_cube _).measurableSet]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ cube (2 * R)
      · rw [indicator_of_mem hx]
        exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 (h01 x).2)
      · rw [IsCutoffFamily.eq_zero_of_notMem hχ hR x hx, ENNReal.ofReal_zero, zero_mul]; exact zero_le
    exact ENNReal.toReal_mono (ne_top_of_le_ne_top (hfin _) hle2) hle
  · filter_upwards [eventually_gt_atTop 1] with R hR
    obtain ⟨hsm, -, h01, -, -⟩ := hχ.1 R hR
    simp only [Function.comp]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [integral_punctured_eq_lintegral η hsm.continuous fun x => (h01 x).1]
    have hle2 : ∫⁻ x, ENNReal.ofReal (χ R x) * triCellDensity η x ≤
        ∫⁻ x in cube (2 * R), triCellDensity η x := by
      rw [← lintegral_indicator (isCompact_cube _).measurableSet]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ cube (2 * R)
      · rw [indicator_of_mem hx]
        exact mul_le_of_le_one_left zero_le (ENNReal.ofReal_le_one.2 (h01 x).2)
      · rw [IsCutoffFamily.eq_zero_of_notMem hχ hR x hx, ENNReal.ofReal_zero, zero_mul]; exact zero_le
    exact ENNReal.toReal_mono (hfin _) hle2

/-- `#(Λ_△ ∩ □_{2R-2}) ≤ ∑_{p ∈ Λ_△} χ_R(p) ≤ #(Λ_△ ∩ □_{2R})`. -/
theorem finsum_cutoff_bounds {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) {R : ℝ} (hR : 1 < R) :
    ((((triangularLattice : Set ℂ) ∩ cube (2 * R - 2)).ncard : ℝ) ≤
        ∑ᶠ p ∈ (triangularLattice : Set ℂ), χ R p) ∧
      ∑ᶠ p ∈ (triangularLattice : Set ℂ), χ R p ≤
        (((triangularLattice : Set ℂ) ∩ cube (2 * R)).ncard : ℝ) := by
  have hfin2 := Torus.finite_lattice_inter (Γ := triangularLattice) (Torus.isBounded_cube (2 * R))
  have hfin1 :=
    Torus.finite_lattice_inter (Γ := triangularLattice) (Torus.isBounded_cube (2 * R - 2))
  have h01 := (hχ.1 R hR).2.2.1
  have hsum : ∑ᶠ p ∈ (triangularLattice : Set ℂ), χ R p = ∑ p ∈ hfin2.toFinset, χ R p :=
    finsum_mem_eq_finsetSum (fun p hp => (hfin2.mem_toFinset.1 hp).1) fun p hpΛ hp =>
      IsCutoffFamily.eq_zero_of_notMem hχ hR p fun h => hp (hfin2.mem_toFinset.2 ⟨hpΛ, h⟩)
  rw [hsum, Set.ncard_eq_toFinset_card _ hfin1, Set.ncard_eq_toFinset_card _ hfin2]
  constructor
  · have hsub : hfin1.toFinset ⊆ hfin2.toFinset := fun p hp =>
      hfin2.mem_toFinset.2 ⟨(hfin1.mem_toFinset.1 hp).1,
        Torus.cube_mono (by linarith) (hfin1.mem_toFinset.1 hp).2⟩
    calc (hfin1.toFinset.card : ℝ) = ∑ p ∈ hfin1.toFinset, χ R p := by
          rw [Finset.sum_congr rfl fun p hp => IsCutoffFamily.eq_one hχ hR p
            (by rw [show 2 * (R - 1) = 2 * R - 2 by ring]; exact (hfin1.mem_toFinset.1 hp).2),
            Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ p ∈ hfin2.toFinset, χ R p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => (h01 p).1
  · calc ∑ p ∈ hfin2.toFinset, χ R p ≤ ∑ _p ∈ hfin2.toFinset, (1 : ℝ) :=
          Finset.sum_le_sum fun p _ => (h01 p).2
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `(2R)⁻² ∑_{p ∈ Λ_△} χ_R(p) → 1`. -/
theorem tendsto_finsum_cutoff_div {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) :
    Tendsto (fun R : ℝ => ((2 * R) ^ 2)⁻¹ * ∑ᶠ p ∈ (triangularLattice : Set ℂ), χ R p) atTop
      (𝓝 1) := by
  have hup := (Torus.tendsto_ncard_inter_cube_div triangularLattice
    Torus.covolume_triangularLattice).comp tendsto_two_mul_atTop
  have hlo := (Torus.tendsto_ncard_inter_cube_add_div triangularLattice
    Torus.covolume_triangularLattice (-2)).comp tendsto_two_mul_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with R hR
    simp only [Function.comp, ← sub_eq_add_neg]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (finsum_cutoff_bounds hχ hR).1 (by positivity)
  · filter_upwards [eventually_gt_atTop 1] with R hR
    simp only [Function.comp]
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (finsum_cutoff_bounds hχ hR).2 (by positivity)

/-! ### The torus limit -/

/-- `½ ∫_F 1_{far η} |∇h_△|² + π log η → W_tri` as `η ↓ 0`. -/
theorem tendsto_cellEnergy_triangular {F : Set ℂ}
    (hF : IsAddFundamentalDomain triangularLattice F volume) (hFb : Bornology.IsBounded F)
    (hcov : ∀ x : ℂ, ∃ γ ∈ triangularLattice, x - γ ∈ F) :
    Tendsto (fun η : ℝ => (1 / 2 : ℝ) * (∫⁻ x in F, triCellDensity η x).toReal +
      Real.pi * Real.log η) (𝓝[>] 0) (𝓝 triangularEnergy) := by
  obtain ⟨v, hv⟩ := Torus.exists_local_form_ball triangular_hmin isTorusPotential_triangular
  have h := Torus.tendsto_puncture triangular_hmin isTorusPotential_triangular hv hF hFb hcov
  have h' : Tendsto (fun ε : ℝ => (1 / 2 : ℝ) * (∫ x in torusDomain triangularLattice \
        ⋃ i : Fin 1, ⋃ γ ∈ triangularLattice, ball (Torus.zeroCharge i + γ) ε,
        ‖gradient (torusPotential triangularLattice fun _ : Fin 1 => (0 : ℂ)) x‖ ^ 2) +
        Real.pi * ((1 : ℕ) : ℝ) * Real.log ε) (𝓝[>] 0) (𝓝 triangularEnergy) := by
    have e : triangularEnergy = limUnder (𝓝[>] 0) (fun ε : ℝ => (1 / 2 : ℝ) *
        (∫ x in torusDomain triangularLattice \
          ⋃ i : Fin 1, ⋃ γ ∈ triangularLattice, ball (Torus.zeroCharge i + γ) ε,
          ‖gradient (torusPotential triangularLattice fun _ : Fin 1 => (0 : ℂ)) x‖ ^ 2) +
        Real.pi * ((1 : ℕ) : ℝ) * Real.log ε) := rfl
    rw [e, h.limUnder_eq]
    exact h
  refine h'.congr fun ε => ?_
  rw [Torus.integral_torusDomain_far isTorusPotential_triangular.1 hF ε, Nat.cast_one, mul_one]
  rfl

/-! ### The main theorem -/

/-- **`W(E_△) = W_tri`** for every cutoff family (comparison note, Lemmas `lem:periodic`, `lem:tri`). -/
theorem wholeEnergy_paperTriangularField {χ : ℝ → ℂ → ℝ} (hχ : IsCutoffFamily χ) :
    wholeEnergy χ (triangularLattice : Set ℂ) paperTriangularField = (triangularEnergy : EReal) := by
  obtain ⟨F, hF, hFm, hFb, hcov⟩ := Torus.exists_fundamentalDomain triangularLattice
  obtain ⟨d, hd⟩ := hFb.subset_closedBall (0 : ℂ)
  obtain ⟨L, hL⟩ := hχ.2
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 2 (by norm_num) 0)
  obtain ⟨M, hM0, hnear⟩ := exists_near_bound_paperTriangularField
  have hT := tendsto_cellEnergy_triangular hF hFb hcov
  have hc : Tendsto (fun η : ℝ => 2 * (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun η : ℝ => 2 * (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2))
        (𝓝 0) (𝓝 (2 * (Real.pi * (L + 2 * M) * 0 + Real.pi / 2 * M ^ 2 * 0 ^ 2))) :=
      (Continuous.tendsto (by fun_prop) 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun R : ℝ => ((2 * R) ^ 2)⁻¹ *
      (localEnergy (triangularLattice : Set ℂ) paperTriangularField (χ R)).toReal) atTop
      (𝓝 triangularEnergy) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have ev1 := Metric.tendsto_nhds.1 hT (ε / 4) (by linarith)
    have ev2 := hc.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ε / 4))
    have ev3 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Ioo 0 (1 / 4) := Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨η, hη1, hη2, hη3⟩ := (ev1.and (ev2.and ev3)).exists
    rw [Real.dist_eq] at hη1
    have hP : Tendsto (fun R : ℝ => ((2 * R) ^ 2)⁻¹ *
        punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η) atTop
        (𝓝 ((1 / 2 : ℝ) * (∫⁻ x in F, triCellDensity η x).toReal + Real.pi * Real.log η)) := by
      have h1 := tendsto_integral_punctured_div hχ hη3.1 hF hFm hd hcov
      have h2 := tendsto_finsum_cutoff_div hχ
      have h3 := (h1.const_mul (1 / 2)).add (h2.const_mul (Real.pi * Real.log η))
      rw [mul_one] at h3
      refine h3.congr fun R => ?_
      simp only [punctureReal]; ring
    have hn := (Torus.tendsto_ncard_inter_cube_add_div triangularLattice
      Torus.covolume_triangularLattice 1).comp tendsto_two_mul_atTop
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (Metric.tendsto_nhds.1 hP (ε / 4) (by linarith))
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
      (hn.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)))
    refine ⟨max (max N₁ N₂) 2, fun R hR => ?_⟩
    have hR1 : 1 < R := by linarith [le_max_right (max N₁ N₂) 2]
    have hb := abs_localEnergy_toReal_sub_le hχ hL hM0 hnear hR1 hη3.1 hη3.2.le
    have hnR : (((triangularLattice : Set ℂ) ∩ cube (2 * R + 1)).ncard : ℝ) / (2 * R) ^ 2 ≤ 2 :=
      hN₂ R ((le_max_right _ _).trans ((le_max_left _ _).trans hR))
    have hPR := hN₁ R ((le_max_left _ _).trans ((le_max_left _ _).trans hR))
    rw [Real.dist_eq] at hPR ⊢
    have hpos : 0 < ((2 * R) ^ 2)⁻¹ := by positivity
    have hc0 : 0 ≤ Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2 :=
      add_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) hη3.1.le) (by positivity)
    have hA : |((2 * R) ^ 2)⁻¹ *
          (localEnergy (triangularLattice : Set ℂ) paperTriangularField (χ R)).toReal -
        ((2 * R) ^ 2)⁻¹ * punctureReal (triangularLattice : Set ℂ) paperTriangularField (χ R) η| ≤
        2 * (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2) := by
      rw [← mul_sub, abs_mul, abs_of_pos hpos]
      calc _ ≤ ((2 * R) ^ 2)⁻¹ * ((((triangularLattice : Set ℂ) ∩ cube (2 * R + 1)).ncard : ℝ) *
            (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2)) :=
            mul_le_mul_of_nonneg_left hb hpos.le
        _ = ((((triangularLattice : Set ℂ) ∩ cube (2 * R + 1)).ncard : ℝ) / (2 * R) ^ 2) *
            (Real.pi * (L + 2 * M) * η + Real.pi / 2 * M ^ 2 * η ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hnR hc0
    have e1 := abs_sub_lt_iff.1 hPR
    have e2 := abs_sub_lt_iff.1 hη1
    have e3 := abs_le.1 hA
    rw [abs_sub_lt_iff]
    constructor <;> linarith
  have hev : (fun R : ℝ => ((((2 * R) ^ 2)⁻¹ : ℝ) : EReal) *
      localEnergy (triangularLattice : Set ℂ) paperTriangularField (χ R)) =ᶠ[atTop]
      fun R => ((((2 * R) ^ 2)⁻¹ *
        (localEnergy (triangularLattice : Set ℂ) paperTriangularField (χ R)).toReal : ℝ) : EReal) := by
    filter_upwards [eventually_gt_atTop 1] with R hR
    rw [EReal.coe_mul, ← localEnergy_eq_coe_toReal isAdmissibleField_paperTriangularField
      (hχ.1 R hR).1 (hχ.1 R hR).2.1]
  unfold wholeEnergy
  rw [limsup_congr hev, (EReal.tendsto_coe.2 hmain).limsup_eq]

end Whole

end SandierSerfaty

end
