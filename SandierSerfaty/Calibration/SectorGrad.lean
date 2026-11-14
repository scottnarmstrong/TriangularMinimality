/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.RadialAdmissible
public import SandierSerfaty.Calibration.KernelSeries
public import SandierSerfaty.Calibration.SectorPolar
public import SandierSerfaty.Dual.SectorDeriv
public import SandierSerfaty.Dual.ModelSector

/-!
# The gradient of the trial potential on the model sector

Paper `cal:trial-potential`. On the model sector `S(d, α, β)` the trial potential is
`modelH radialData d w = B(‖w‖) + ∑ᵢ g^{kᵢ} Dᵢ(‖w‖/g)`, `g = Re w / d`. Termwise differentiation of the series on
the open convex sector (`hasFDerivAt_modelH`) gives, with `r = ‖w‖`, `t = r/g`, `ΣA = ∑ g^{k-1} Dᵢ'(t)`,
`ΣB = ∑ (kᵢ g^{k-1} Dᵢ(t) - g^{k-1} t Dᵢ'(t)) = -∑ g^{k-1} Qᵢ(t)`:

`|∇H|² = (B'(r) + ΣA + ΣB · x/(r d))² + (ΣB · y/(r d))²`   (`gradSq_modelH`)

(the radial and angular components `H_r` and `H_φ / r` of the paper). In polar form
`gradSq_modelH_polar`: `H_r = B'(r) + (1/r) ∑ kᵢ (r/t)^{kᵢ} Dᵢ(t)` and `H_φ/r = (tan φ / r) ∑ (r/t)^{kᵢ} Qᵢ(t)`
with `t = d sec φ`.
-/

open Set Filter Topology MeasureTheory Real

public section

namespace SandierSerfaty

namespace Calibration

open SandierSerfaty.Dual

/-- The sector variables `Ψ(w) = (‖w‖, Re w / d)` of `modelH`. -/
@[expose] noncomputable def PsiM (d : ℝ) (w : ℂ) : ℝ × ℝ := (‖w‖, w.re / d)

theorem modelH_eq (d : ℝ) (w : ℂ) :
    modelH radialData d w = B ‖w‖ + serF radialData (PsiM d w) := rfl

/-- The upper radius `T₀ = d / cos (max |α| |β|)` of the sector. -/
@[expose] noncomputable def secRadius (d α β : ℝ) : ℝ := d / Real.cos (max |α| |β|)

theorem cos_max_pos {α β : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) : 0 < Real.cos (max |α| |β|) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, show 0 ≤ max |α| |β| from le_max_of_le_left (abs_nonneg α)],
    max_lt hα hβ⟩

theorem secRadius_pos {d α β : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    0 < secRadius d α β := div_pos hd (cos_max_pos hα hβ)

theorem d_le_secRadius {d α β : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    d ≤ secRadius d α β := by
  unfold secRadius
  rw [le_div_iff₀ (cos_max_pos hα hβ)]
  nlinarith [Real.cos_le_one (max |α| |β|)]

theorem ne_zero_of_mem_modelSector {d α β : ℝ} {w : ℂ} (hw : w ∈ modelSector d α β) : w ≠ 0 := fun h => by
  have := hw.1; rw [h] at this; simp at this

/-- On the sector, `cos (max |α| |β|) ≤ Re w / ‖w‖`. -/
theorem cos_max_le_re_div {d α β : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) {w : ℂ}
    (hw : w ∈ modelSector d α β) : Real.cos (max |α| |β|) ≤ w.re / ‖w‖ := by
  obtain ⟨h1, h2⟩ := arg_mem_of_mem_modelSector hα hβ hw
  rw [← Complex.cos_arg (ne_zero_of_mem_modelSector hw), ← Real.cos_abs (Complex.arg w)]
  have hφ : |Complex.arg w| ≤ max |α| |β| := by
    rw [abs_le]
    constructor
    · have := le_abs_self α; have := le_max_left |α| |β|; linarith
    · have := le_abs_self β; have := le_max_right |α| |β|; linarith
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    (by linarith [pi_pos, max_lt hα hβ]) hφ

theorem PsiM_mem_cone {d α β : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) {w : ℂ}
    (hw : w ∈ modelSector d α β) : PsiM d w ∈ cone d (secRadius d α β) := by
  have hcos := cos_max_le_re_div hα hβ hw
  have hc0 := cos_max_pos hα hβ
  have hw0 := ne_zero_of_mem_modelSector hw
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  obtain ⟨hre, hlt, -, -⟩ := hw
  unfold PsiM cone secRadius
  refine ⟨div_pos hre hd, ?_, ?_, ?_⟩
  · simp only; rw [div_le_one hd]; exact hlt.le
  · simp only; rw [mul_div_cancel₀ _ hd.ne']; exact Complex.re_le_norm w
  · simp only
    rw [le_div_iff₀ hn] at hcos
    have e : d / Real.cos (max |α| |β|) * (w.re / d) = w.re / Real.cos (max |α| |β|) := by
      field_simp
    rw [e, le_div_iff₀ hc0]
    linarith

theorem cone_mono {d T T' : ℝ} (h : T ≤ T') : cone d T ⊆ cone d T' := by
  rintro x ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, h4.trans (mul_le_mul_of_nonneg_right h h1.le)⟩

/-- The derivative of the sector variables `PsiM`. -/
@[expose] noncomputable def PsiM' (d : ℝ) (w : ℂ) : ℂ →L[ℝ] ℝ × ℝ :=
  ((‖w‖)⁻¹ • innerSL ℝ w).prod (d⁻¹ • Complex.reCLM)

theorem hasFDerivAt_norm' {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => ‖z‖) ((‖w‖)⁻¹ • innerSL ℝ w) w := by
  simpa using hasFDerivAt_norm_sub (c := 0) (y := w) (by simpa using hw)

theorem hasFDerivAt_PsiM {d : ℝ} {w : ℂ} (hw : w ≠ 0) : HasFDerivAt (PsiM d) (PsiM' d w) w := by
  have h1 := hasFDerivAt_norm' hw
  have h2 : HasFDerivAt (fun z : ℂ => z.re / d) (d⁻¹ • Complex.reCLM) w := by
    have := (Complex.reCLM.hasFDerivAt (x := w)).const_smul d⁻¹
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp [div_eq_inv_mul]
  exact h1.prodMk h2

/-- The derivative of the `i`-th term of the series along the sector variables. -/
@[expose] noncomputable def modelTermDeriv (d : ℝ) (i : ℕ) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  (termDeriv radialData i (PsiM d w)).comp (PsiM' d w)

theorem hasFDerivAt_modelTerm {d α β : ℝ} {w : ℂ} (hw : w ∈ modelSector d α β) (hd : 0 < d) (i : ℕ) :
    HasFDerivAt (fun y => termFn radialData i (PsiM d y)) (modelTermDeriv d i w) w := by
  have hw0 := ne_zero_of_mem_modelSector hw
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hg : 0 < (PsiM d w).2 := div_pos hw.1 hd
  have h1 : HasFDerivAt (termFn radialData i) (termDeriv radialData i (PsiM d w)) (PsiM d w) :=
    hasFDerivAt_termFn' radialData (fun i => (contDiffOn_D i).of_le (by norm_num)) hg hpos
  exact h1.comp w (hasFDerivAt_PsiM hw0)

theorem norm_PsiM'_le {d : ℝ} (hd : 0 < d) {w : ℂ} (hw : w ≠ 0) : ‖PsiM' d w‖ ≤ 1 + 1 / d := by
  unfold PsiM'
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  refine max_le ?_ ?_
  · rw [norm_inv_smul_innerSL hw]; linarith [show (0 : ℝ) ≤ 1 / d by positivity]
  · have : ‖d⁻¹ • Complex.reCLM‖ ≤ d⁻¹ := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hd]
      have : ‖Complex.reCLM‖ ≤ 1 :=
        ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
          simpa using Complex.abs_re_le_norm z
      calc d⁻¹ * ‖Complex.reCLM‖ ≤ d⁻¹ * 1 := mul_le_mul_of_nonneg_left this (by positivity)
        _ = d⁻¹ := mul_one _
    calc _ ≤ d⁻¹ := this
      _ ≤ 1 + 1 / d := by rw [one_div]; linarith

theorem norm_modelTermDeriv_le {d α β T : ℝ} {M : ℕ → ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hM : Bnd radialData d T M) (hT : secRadius d α β ≤ T) {w : ℂ} (hw : w ∈ modelSector d α β) (i : ℕ) :
    ‖modelTermDeriv d i w‖ ≤ (2 + 1 / d) * M i * (1 + 1 / d) := by
  have hR := radialData_isAdmissible hd
  have hc := cone_mono hT (PsiM_mem_cone hd hα hβ hw)
  have hMn : 0 ≤ M i := hM.nonneg hd ((d_le_secRadius hd hα hβ).trans hT) i
  have h1 := norm_termDeriv_le hR hM hd i hc
  have h2 := norm_PsiM'_le hd (ne_zero_of_mem_modelSector hw)
  have hp : (PsiM d w).2 ^ (radialData.k i - 1) ≤ 1 := pow_le_one₀ hc.1.le hc.2.1
  have hc2 : 0 ≤ (2 + 1 / d) * M i := mul_nonneg (by positivity) hMn
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_mul ?_ h2 (norm_nonneg _) (mul_nonneg hc2 hMn |>.trans' (le_refl _) |> fun _ => by positivity)
  refine h1.trans ?_
  nlinarith [mul_nonneg hc2 (sub_nonneg.2 hp)]

theorem hasFDerivAt_serF_model {d α β T : ℝ} {M : ℕ → ℝ} (hd : 0 < d) (hα : |α| < π / 2)
    (hβ : |β| < π / 2) (hM : Bnd radialData d T M) (hT : secRadius d α β ≤ T) {w : ℂ}
    (hw : w ∈ modelSector d α β) :
    HasFDerivAt (fun y => serF radialData (PsiM d y)) (∑' i, modelTermDeriv d i w) w := by
  have hR := radialData_isAdmissible hd
  have hu : Summable fun i => (2 + 1 / d) * M i * (1 + 1 / d) :=
    (hM.summable.mul_left (2 + 1 / d)).mul_right (1 + 1 / d)
  have := hasFDerivAt_tsum_of_isPreconnected (f := fun i y => termFn radialData i (PsiM d y))
    (f' := fun i y => modelTermDeriv d i y) hu (isOpen_modelSector d α β)
    (convex_modelSector d α β).isPreconnected (fun i y hy => hasFDerivAt_modelTerm hy hd i)
    (fun i y hy => norm_modelTermDeriv_le hd hα hβ hM hT hy i) hw
    (summable_termFn hM hR hd (cone_mono hT (PsiM_mem_cone hd hα hβ hw))) hw
  simpa [serF] using this

theorem summable_modelTermDeriv {d α β T : ℝ} {M : ℕ → ℝ} (hd : 0 < d) (hα : |α| < π / 2)
    (hβ : |β| < π / 2) (hM : Bnd radialData d T M) (hT : secRadius d α β ≤ T) {w : ℂ}
    (hw : w ∈ modelSector d α β) : Summable fun i => modelTermDeriv d i w :=
  Summable.of_norm_bounded ((hM.summable.mul_left (2 + 1 / d)).mul_right (1 + 1 / d))
    fun i => norm_modelTermDeriv_le hd hα hβ hM hT hw i

/-- **The derivative of the trial potential on the model sector.** -/
theorem hasFDerivAt_modelH {d α β T : ℝ} {M : ℕ → ℝ} (hd : 0 < d) (hα : |α| < π / 2)
    (hβ : |β| < π / 2) (hM : Bnd radialData d T M) (hT : secRadius d α β ≤ T) {w : ℂ}
    (hw : w ∈ modelSector d α β) :
    HasFDerivAt (modelH radialData d)
      (deriv B ‖w‖ • ((‖w‖)⁻¹ • innerSL ℝ w) + ∑' i, modelTermDeriv d i w) w := by
  have hw0 := ne_zero_of_mem_modelSector hw
  have hB : HasDerivAt B (deriv B ‖w‖) ‖w‖ :=
    (((contDiffOn_B.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffAt
      (isOpen_Ioi.mem_nhds (norm_pos_iff.2 hw0))).differentiableAt one_ne_zero).hasDerivAt
  have h1' : HasFDerivAt (fun y : ℂ => B ‖y‖) (deriv B ‖w‖ • ((‖w‖)⁻¹ • innerSL ℝ w)) w :=
    hB.comp_hasFDerivAt w (hasFDerivAt_norm' hw0)
  exact h1'.add (hasFDerivAt_serF_model hd hα hβ hM hT hw)

/-! ### The coefficient sequences -/

/-- `∂_r` of the `i`-th term `g^{k} D_i(r/g)` at `(r, g)`, as a function of `(g, t = r/g)`. -/
@[expose] noncomputable def cA (g t : ℝ) (i : ℕ) : ℝ := g ^ (k i - 1) * deriv (D i) t

/-- `∂_g` of the `i`-th term, as a function of `(g, t)`: `-g^{k-1} Q_i(t)`. -/
@[expose] noncomputable def cB (g t : ℝ) (i : ℕ) : ℝ := -(g ^ (k i - 1) * Q i t)

theorem termDeriv_fst_coeff {g r : ℝ} (hg : 0 < g) (i : ℕ) :
    g ^ k i * (deriv (D i) (r / g) / g) = cA g (r / g) i := by
  unfold cA
  have : g ^ k i = g ^ (k i - 1) * g := by rw [← pow_succ]; congr 1; have := k_ge_one i; omega
  rw [this]; field_simp

theorem termDeriv_snd_coeff {g r : ℝ} (hg : 0 < g) (i : ℕ) :
    (k i : ℝ) * g ^ (k i - 1) * D i (r / g) - g ^ k i * deriv (D i) (r / g) * r / g ^ 2 =
      cB g (r / g) i := by
  unfold cB Q
  have : g ^ k i = g ^ (k i - 1) * g := by rw [← pow_succ]; congr 1; have := k_ge_one i; omega
  rw [this]; field_simp; ring

section Coeff

variable {d T g t : ℝ} {M : ℕ → ℝ}

theorem abs_cA_le (hM : Bnd radialData d T M) (hd : 0 < d) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (ht : t ∈ Icc d T) (i : ℕ) : |cA g t i| ≤ M i / d := by
  unfold cA
  rw [abs_mul, abs_of_pos (pow_pos hg0 _)]
  have h1 := hM.abs_deriv_le hd i ht
  have hMn : 0 ≤ M i / d := (abs_nonneg _).trans h1
  calc g ^ (k i - 1) * |deriv (D i) t| ≤ 1 * (M i / d) :=
        mul_le_mul (pow_le_one₀ hg0.le hg1) h1 (abs_nonneg _) zero_le_one
    _ = M i / d := one_mul _

theorem abs_cB_le (hM : Bnd radialData d T M) (hd : 0 < d) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (ht : t ∈ Icc d T) (i : ℕ) : |cB g t i| ≤ 2 * M i := by
  unfold cB
  rw [abs_neg, abs_mul, abs_of_pos (pow_pos hg0 _)]
  have h1 := hM.t_mul_abs_deriv_le i ht
  have h2 := hM.k_mul_abs_D_le hd i ht
  have hQ : |Q i t| ≤ 2 * M i := by
    unfold Q
    calc |t * deriv (D i) t - (k i : ℝ) * D i t| ≤ |t * deriv (D i) t| + |(k i : ℝ) * D i t| := abs_sub _ _
      _ ≤ M i + M i := by
          refine add_le_add ?_ ?_
          · rw [abs_mul, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]; exact h1
          · rw [abs_mul, Nat.abs_cast]; exact h2
      _ = 2 * M i := by ring
  have hMn : 0 ≤ 2 * M i := (abs_nonneg _).trans hQ
  calc g ^ (k i - 1) * |Q i t| ≤ 1 * (2 * M i) :=
        mul_le_mul (pow_le_one₀ hg0.le hg1) hQ (abs_nonneg _) zero_le_one
    _ = 2 * M i := one_mul _

theorem summable_cA (hM : Bnd radialData d T M) (hd : 0 < d) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (ht : t ∈ Icc d T) : Summable (cA g t) :=
  Summable.of_norm_bounded (hM.summable.div_const d) fun i => by
    rw [Real.norm_eq_abs]; exact abs_cA_le hM hd hg0 hg1 ht i

theorem summable_cB (hM : Bnd radialData d T M) (hd : 0 < d) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (ht : t ∈ Icc d T) : Summable (cB g t) :=
  Summable.of_norm_bounded (hM.summable.mul_left 2) fun i => by
    rw [Real.norm_eq_abs]; exact abs_cB_le hM hd hg0 hg1 ht i

end Coeff

/-! ### Polar form of the gradient -/

theorem polarCoord_symm_re (r φ : ℝ) : (Complex.polarCoord.symm (r, φ) : ℂ).re = r * Real.cos φ := by
  rw [Complex.polarCoord_symm_apply]
  simp [Complex.mul_re, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem polarCoord_symm_im (r φ : ℝ) : (Complex.polarCoord.symm (r, φ) : ℂ).im = r * Real.sin φ := by
  rw [Complex.polarCoord_symm_apply]
  simp [Complex.mul_im, -Complex.ofReal_cos, -Complex.ofReal_sin]

theorem polar_mem_modelSector {d α β r φ : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) (hr : 0 < r)
    (hφ : φ ∈ Ioo (-α) β) (hrt : r * Real.cos φ < d) :
    (Complex.polarCoord.symm (r, φ) : ℂ) ∈ modelSector d α β := by
  have hx : (r, φ) ∈ polarCoord.target := by
    rw [polarCoord_target]
    obtain ⟨a1, a2⟩ := abs_lt.1 hα
    obtain ⟨b1, b2⟩ := abs_lt.1 hβ
    exact ⟨hr, by linarith [hφ.1], by linarith [hφ.2]⟩
  exact ((polarCoord_symm_mem_iff (η := 0) hα hβ hx).2 ⟨hφ, hr, hrt⟩).1

theorem modelTermDeriv_apply {d α β : ℝ} (hd : 0 < d) {w : ℂ} (hw : w ∈ modelSector d α β) (i : ℕ) (v : ℂ) :
    modelTermDeriv d i w v =
      cA (w.re / d) (‖w‖ / (w.re / d)) i * ((‖w‖)⁻¹ * inner ℝ w v) +
        cB (w.re / d) (‖w‖ / (w.re / d)) i * (d⁻¹ * v.re) := by
  have hg : 0 < w.re / d := div_pos hw.1 hd
  simp only [modelTermDeriv, termDeriv, PsiM', PsiM, ContinuousLinearMap.comp_apply,
    add_apply, smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.prod_apply, innerSL_apply_apply, smul_eq_mul,
    Complex.reCLM_apply]
  have e1 := termDeriv_fst_coeff (r := ‖w‖) hg i
  have e2 := termDeriv_snd_coeff (r := ‖w‖) hg i
  simp only [radialData]
  rw [e1, e2]

theorem exists_bnd_model {d α β : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    ∃ M : ℕ → ℝ, Bnd radialData d (secRadius d α β + 1) M := by
  obtain ⟨M, hMs, hMb⟩ := (radialData_isAdmissible hd).summable (secRadius d α β + 1)
    (by linarith [d_le_secRadius hd hα hβ])
  exact ⟨M, hMs, hMb⟩

/-- **The gradient energy density of the trial potential in polar form** (paper, verification of `cal:angle-density`):
`|∇H|² = H_r² + (H_φ / r)²` with `H_r = B'(r) + (1/r) ∑ kᵢ (r/t)^{kᵢ} Dᵢ(t)` and
`H_φ / r = (tan φ / r) ∑ (r/t)^{kᵢ} Qᵢ(t)`, `t = d sec φ`. -/
theorem gradSq_modelH_polar {d α β r φ : ℝ} (hd : 0 < d) (hα : |α| < π / 2) (hβ : |β| < π / 2)
    (hr : 0 < r) (hφ : φ ∈ Ioo (-α) β) (hrt : r * Real.cos φ < d) :
    Analysis.gradSq (modelH radialData d) (Complex.polarCoord.symm (r, φ)) =
      (deriv B r + 1 / r * ∑' i, (k i : ℝ) * (r * Real.cos φ / d) ^ k i * D i (d / Real.cos φ)) ^ 2 +
        (Real.tan φ / r * ∑' i, (r * Real.cos φ / d) ^ k i * Q i (d / Real.cos φ)) ^ 2 := by
  set w : ℂ := Complex.polarCoord.symm (r, φ) with hwdef
  have hw : w ∈ modelSector d α β := polar_mem_modelSector hα hβ hr hφ hrt
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(abs_lt.1 hα).2, hφ.1, pi_pos, (abs_lt.1 hα).1], by linarith [(abs_lt.1 hβ).2, hφ.2]⟩
  have hre : w.re = r * Real.cos φ := polarCoord_symm_re r φ
  have him : w.im = r * Real.sin φ := polarCoord_symm_im r φ
  have hn : ‖w‖ = r := polarCoord_symm_norm (x := (r, φ)) hr
  obtain ⟨M, hM⟩ := exists_bnd_model hd hα hβ
  have hT : secRadius d α β ≤ secRadius d α β + 1 := by linarith
  have hD := hasFDerivAt_modelH hd hα hβ hM hT hw
  set g : ℝ := r * Real.cos φ / d with hgdef
  have hg0 : 0 < g := by positivity
  have hg1 : g ≤ 1 := by rw [hgdef, div_le_one hd]; exact hrt.le
  set t : ℝ := d / Real.cos φ with htdef
  have hwg : w.re / d = g := by rw [hre]
  have hrg : r / g = t := by rw [hgdef, htdef]; field_simp
  have hcone := cone_mono hT (PsiM_mem_cone hd hα hβ hw)
  have hts : t ∈ Icc d (secRadius d α β + 1) := by
    have := div_mem_Icc_of_mem_cone hcone
    simp only [PsiM, hn, hwg, hrg] at this
    exact this
  have hsA := summable_cA hM hd hg0 hg1 hts
  have hsB := summable_cB hM hd hg0 hg1 hts
  have hcoef : ∀ v : ℂ, (deriv B ‖w‖ • ((‖w‖)⁻¹ • innerSL ℝ w) + ∑' i, modelTermDeriv d i w) v =
      deriv B r * (r⁻¹ * inner ℝ w v) + ((∑' i, cA g t i) * (r⁻¹ * inner ℝ w v) +
        (∑' i, cB g t i) * (d⁻¹ * v.re)) := by
    intro v
    have h1 : (∑' i, modelTermDeriv d i w) v = ∑' i, modelTermDeriv d i w v := by
      have := (ContinuousLinearMap.apply ℝ ℝ v).map_tsum
        (summable_modelTermDeriv hd hα hβ hM hT hw)
      simpa using this
    simp only [add_apply, smul_apply, smul_eq_mul,
      innerSL_apply_apply, h1, hn]
    simp_rw [modelTermDeriv_apply hd hw, hn, hwg, hrg]
    rw [Summable.tsum_add (hsA.mul_right _) (hsB.mul_right _), tsum_mul_right, tsum_mul_right]
  have hL1 := hcoef 1
  have hLI := hcoef Complex.I
  have e1 : inner ℝ w (1 : ℂ) = r * Real.cos φ := by simp [Complex.inner, hre]
  have eI : inner ℝ w Complex.I = r * Real.sin φ := by simp [Complex.inner, him]
  -- the two series identities
  have hrt' : r = g * t := by rw [← hrg]; field_simp
  have hA : ∑' i, (k i : ℝ) * g ^ k i * D i t = r * ∑' i, cA g t i + g * ∑' i, cB g t i := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add (hsA.mul_left r) (hsB.mul_left g)]
    refine tsum_congr fun i => ?_
    unfold cA cB Q
    have : g ^ k i = g ^ (k i - 1) * g := by rw [← pow_succ]; congr 1; have := k_ge_one i; omega
    rw [this, hrt']
    ring
  have hB : ∑' i, g ^ k i * Q i t = -g * ∑' i, cB g t i := by
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    unfold cB
    have : g ^ k i = g ^ (k i - 1) * g := by rw [← pow_succ]; congr 1; have := k_ge_one i; omega
    rw [this]
    ring
  have hgr : g / r = Real.cos φ / d := by rw [hgdef]; field_simp
  have htan : Real.tan φ * g / r = Real.sin φ / d := by
    rw [mul_div_assoc, hgr, Real.tan_eq_sin_div_cos]; field_simp
  unfold Analysis.gradSq Analysis.pd₁ Analysis.pd₂
  rw [hD.fderiv, hL1, hLI, e1, eI]
  simp only [Complex.one_re, Complex.I_re, mul_zero, add_zero]
  rw [show r⁻¹ * (r * Real.cos φ) = Real.cos φ by field_simp,
    show r⁻¹ * (r * Real.sin φ) = Real.sin φ by field_simp]
  rw [hA, hB]
  have hSA : ∑' i, cA g t i = ∑' i, cA g t i := rfl
  set SA := ∑' i, cA g t i
  set SB := ∑' i, cB g t i
  have e3 : 1 / r * (r * SA + g * SB) = SA + SB * (Real.cos φ / d) := by
    rw [← hgr]; field_simp
  have e4 : Real.tan φ / r * (-g * SB) = -(SB * (Real.sin φ / d)) := by
    rw [← htan]; field_simp
  rw [e3, e4]
  have hs := Real.sin_sq_add_cos_sq φ
  linear_combination ((deriv B r + SA) ^ 2 - (SB / d) ^ 2) * hs

end Calibration

end SandierSerfaty

end
