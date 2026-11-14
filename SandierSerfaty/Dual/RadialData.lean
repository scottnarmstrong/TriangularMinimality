/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Radial data of the glued trial potential

Paper `(dual:radial-origin)`–`(dual:radial-sum)`.
The trial potential on a sector is `H(r, φ) = B(r) + ∑ᵢ (r / t(φ))^{kᵢ} Dᵢ(t(φ))` with `t(φ) = d sec φ`.
Writing `g = r / t`, this is `Fpair (r, g) = B r + serF (r, g)`, `serF (r, g) = ∑ᵢ g^{kᵢ} Dᵢ(r / g)`.

* `RadialData ι`: the data `(B, kᵢ, Dᵢ)`; `RadialData.IsAdmissible R d₀`: the hypotheses of the paper
  (`kᵢ ≥ 6`, `B, Dᵢ ∈ C¹((0,∞))`, the expansion of `B` at `0`, and the summability `(dual:radial-sum)`).
* `Bnd R d₀ T₀ M`: a summable bound `M` for `(1 + kᵢ)|Dᵢ| + t |Dᵢ'|` on `[d₀, T₀]`.
* `cone d₀ T₀`: the convex set `{(r, g) | 0 < g ≤ 1, d₀ g ≤ r ≤ T₀ g}`, on which `t = r/g ∈ [d₀, T₀]`.
* `hasFDerivAt_termFn`, `norm_termDeriv_le`: the derivative of one term, and its bound `g^{k-1}(2 + 1/d₀) Mᵢ`.
* `abs_serF_le`: `|serF (r, g)| ≤ g^6 ∑ Mᵢ`.
* `lipschitzOnWith_serF`: `serF` is Lipschitz on `cone d₀ T₀`, and (`abs_serF_le`) tends to `0` at the apex.
-/

open Set Filter Topology

public section

namespace SandierSerfaty

namespace Dual

/-- The radial data `(B, kᵢ, Dᵢ)` of the paper. -/
structure RadialData (ι : Type*) where
  /-- The singular part `B`. -/
  B : ℝ → ℝ
  /-- The exponents `kᵢ`. -/
  k : ι → ℕ
  /-- The correction profiles `Dᵢ`. -/
  D : ι → ℝ → ℝ

variable {ι : Type*}

/-- The hypotheses `(dual:radial-origin)`–`(dual:radial-sum)` of the paper on radial data, for the
lower edge distance `d₀`. -/
structure RadialData.IsAdmissible (R : RadialData ι) (d₀ : ℝ) : Prop where
  /-- `kᵢ ≥ 6`. -/
  six_le : ∀ i, 6 ≤ R.k i
  /-- `B ∈ C¹((0,∞))`. -/
  contDiffOn_B : ContDiffOn ℝ 1 R.B (Ioi 0)
  /-- `Dᵢ ∈ C¹((0,∞))`. -/
  contDiffOn_D : ∀ i, ContDiffOn ℝ 1 (R.D i) (Ioi 0)
  /-- `B(r) = -log r + O(r²)`, `B'(r) = -1/r + O(r)` as `r ↓ 0`. -/
  origin : ∃ C ρ : ℝ, 0 < ρ ∧ ∀ r ∈ Ioo 0 ρ,
    |R.B r + Real.log r| ≤ C * r ^ 2 ∧ |deriv R.B r + 1 / r| ≤ C * r
  /-- `(dual:radial-sum)`: for every `T₀ > d₀` the sums of `sup_{[d₀,T₀]} ((1+kᵢ)|Dᵢ| + t|Dᵢ'|)` are
  finite (stated through a summable majorant). -/
  summable : ∀ T₀ > d₀, ∃ M : ι → ℝ, Summable M ∧ ∀ i, ∀ t ∈ Icc d₀ T₀,
    (1 + (R.k i : ℝ)) * |R.D i t| + t * |deriv (R.D i) t| ≤ M i

/-- A summable majorant `M` of `(1 + kᵢ)|Dᵢ| + t|Dᵢ'|` on `[d₀, T₀]`. -/
structure Bnd (R : RadialData ι) (d₀ T₀ : ℝ) (M : ι → ℝ) : Prop where
  /-- `M` is summable. -/
  summable : Summable M
  /-- The pointwise bound. -/
  bound : ∀ i, ∀ t ∈ Icc d₀ T₀,
    (1 + (R.k i : ℝ)) * |R.D i t| + t * |deriv (R.D i) t| ≤ M i

/-- The `i`-th term `g^{kᵢ} Dᵢ(r / g)` of the correction series, as a function of `(r, g)`. -/
@[expose] noncomputable def termFn (R : RadialData ι) (i : ι) (x : ℝ × ℝ) : ℝ :=
  x.2 ^ R.k i * R.D i (x.1 / x.2)

/-- The correction series `∑ᵢ g^{kᵢ} Dᵢ(r / g)`. -/
@[expose] noncomputable def serF (R : RadialData ι) (x : ℝ × ℝ) : ℝ := ∑' i, termFn R i x

/-- The trial function in the variables `(r, g)`, `g = r / t`. -/
@[expose] noncomputable def Fpair (R : RadialData ι) (x : ℝ × ℝ) : ℝ := R.B x.1 + serF R x

/-- The convex set `{(r, g) | 0 < g ≤ 1, d₀ g ≤ r ≤ T₀ g}`, on which `t = r / g ∈ [d₀, T₀]`. -/
@[expose] def cone (d₀ T₀ : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 < x.2 ∧ x.2 ≤ 1 ∧ d₀ * x.2 ≤ x.1 ∧ x.1 ≤ T₀ * x.2}

theorem convex_cone (d₀ T₀ : ℝ) : Convex ℝ (cone d₀ T₀) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  simp only [cone, mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases ha.eq_or_lt with rfl | ha'
    · have : b = 1 := by linarith
      subst this; simpa using hy1
    · have := mul_pos ha' hx1
      nlinarith
  · nlinarith
  · nlinarith
  · nlinarith

theorem div_mem_Icc_of_mem_cone {d₀ T₀ : ℝ} {x : ℝ × ℝ} (hx : x ∈ cone d₀ T₀) :
    x.1 / x.2 ∈ Icc d₀ T₀ := by
  obtain ⟨h1, -, h3, h4⟩ := hx
  exact ⟨by rw [le_div_iff₀ h1]; exact h3, by rw [div_le_iff₀ h1]; exact h4⟩

section Bounds

variable {R : RadialData ι} {d₀ T₀ : ℝ} {M : ι → ℝ}

theorem Bnd.abs_D_le (hM : Bnd R d₀ T₀ M) (hd : 0 < d₀) (i : ι) {t : ℝ} (ht : t ∈ Icc d₀ T₀) :
    |R.D i t| ≤ M i := by
  have h := hM.bound i t ht
  have h1 : 0 ≤ t * |deriv (R.D i) t| := mul_nonneg (by linarith [ht.1]) (abs_nonneg _)
  have h2 : (1 : ℝ) ≤ 1 + (R.k i : ℝ) := by simp
  nlinarith [abs_nonneg (R.D i t)]

theorem Bnd.k_mul_abs_D_le (hM : Bnd R d₀ T₀ M) (hd : 0 < d₀) (i : ι) {t : ℝ} (ht : t ∈ Icc d₀ T₀) :
    (R.k i : ℝ) * |R.D i t| ≤ M i := by
  have h := hM.bound i t ht
  have h1 : 0 ≤ t * |deriv (R.D i) t| := mul_nonneg (by linarith [ht.1]) (abs_nonneg _)
  nlinarith [abs_nonneg (R.D i t)]

theorem Bnd.t_mul_abs_deriv_le (hM : Bnd R d₀ T₀ M) (i : ι) {t : ℝ} (ht : t ∈ Icc d₀ T₀) :
    t * |deriv (R.D i) t| ≤ M i := by
  have h := hM.bound i t ht
  have h1 : 0 ≤ (1 + (R.k i : ℝ)) * |R.D i t| := by positivity
  linarith

theorem Bnd.nonneg (hM : Bnd R d₀ T₀ M) (hd : 0 < d₀) (hT : d₀ ≤ T₀) (i : ι) : 0 ≤ M i :=
  (abs_nonneg _).trans (hM.abs_D_le hd i ⟨le_rfl, hT⟩)

theorem Bnd.abs_deriv_le (hM : Bnd R d₀ T₀ M) (hd : 0 < d₀) (i : ι) {t : ℝ} (ht : t ∈ Icc d₀ T₀) :
    |deriv (R.D i) t| ≤ M i / d₀ := by
  have h := hM.t_mul_abs_deriv_le i ht
  rw [le_div_iff₀ hd]
  have : d₀ * |deriv (R.D i) t| ≤ t * |deriv (R.D i) t| :=
    mul_le_mul_of_nonneg_right ht.1 (abs_nonneg _)
  linarith

end Bounds

/-- The derivative of one term of the series. -/
theorem hasFDerivAt_termFn (k : ℕ) {D : ℝ → ℝ} {x : ℝ × ℝ} (hg : 0 < x.2)
    (hD : HasDerivAt D (deriv D (x.1 / x.2)) (x.1 / x.2)) :
    HasFDerivAt (fun y : ℝ × ℝ => y.2 ^ k * D (y.1 / y.2))
      ((x.2 ^ k * (deriv D (x.1 / x.2) / x.2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (k * x.2 ^ (k - 1) * D (x.1 / x.2) - x.2 ^ k * deriv D (x.1 / x.2) * x.1 / x.2 ^ 2) •
          ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
  have hinv : HasFDerivAt (fun y : ℝ × ℝ => (y.2)⁻¹)
      ((-(x.2 ^ 2)⁻¹) • ContinuousLinearMap.snd ℝ ℝ ℝ) x := by
    have := (hasDerivAt_inv hg.ne').hasFDerivAt.comp x
      (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x))
    refine this.congr_fderiv ?_
    refine ContinuousLinearMap.ext fun z => ?_
    simp [mul_comm]
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x)).mul hinv
  have h2 := hD.hasFDerivAt.comp x h1
  have h3 := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := x)).pow k
  have h4 := h3.mul h2
  refine (h4.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · refine ContinuousLinearMap.ext fun z => ?_
    simp [div_eq_mul_inv]
    field_simp
    ring
  · exact Eventually.of_forall fun y => by simp [div_eq_mul_inv]

theorem norm_smul_fst_add_smul_snd_le (a b : ℝ) :
    ‖a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |a| + |b| := by
  have h1 : ‖a • ContinuousLinearMap.fst ℝ ℝ ℝ‖ ≤ |a| := by
    rw [norm_smul, Real.norm_eq_abs]
    have := ContinuousLinearMap.norm_fst_le (𝕜 := ℝ) (E := ℝ) (F := ℝ)
    nlinarith [abs_nonneg a]
  have h2 : ‖b • ContinuousLinearMap.snd ℝ ℝ ℝ‖ ≤ |b| := by
    rw [norm_smul, Real.norm_eq_abs]
    have := ContinuousLinearMap.norm_snd_le (𝕜 := ℝ) (E := ℝ) (F := ℝ)
    nlinarith [abs_nonneg b]
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

/-- The derivative functional of the `i`-th term. -/
@[expose] noncomputable def termDeriv (R : RadialData ι) (i : ι) (x : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ :=
  (x.2 ^ R.k i * (deriv (R.D i) (x.1 / x.2) / x.2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    ((R.k i : ℝ) * x.2 ^ (R.k i - 1) * R.D i (x.1 / x.2) -
      x.2 ^ R.k i * deriv (R.D i) (x.1 / x.2) * x.1 / x.2 ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ

theorem hasFDerivAt_termFn' (R : RadialData ι) (hR : ∀ i, ContDiffOn ℝ 1 (R.D i) (Ioi 0))
    {i : ι} {x : ℝ × ℝ} (hg : 0 < x.2) (hr : 0 < x.1) :
    HasFDerivAt (termFn R i) (termDeriv R i x) x := by
  have hpos : (0 : ℝ) < x.1 / x.2 := div_pos hr hg
  have hD : HasDerivAt (R.D i) (deriv (R.D i) (x.1 / x.2)) (x.1 / x.2) :=
    (((hR i).contDiffAt (isOpen_Ioi.mem_nhds hpos)).differentiableAt one_ne_zero).hasDerivAt
  exact hasFDerivAt_termFn (R.k i) hg hD

section Estimates

variable {R : RadialData ι} {d₀ T₀ : ℝ} {M : ι → ℝ}

theorem norm_termDeriv_le (hR : R.IsAdmissible d₀) (hM : Bnd R d₀ T₀ M) (hd : 0 < d₀) (i : ι)
    {x : ℝ × ℝ} (hx : x ∈ cone d₀ T₀) :
    ‖termDeriv R i x‖ ≤ x.2 ^ (R.k i - 1) * (2 + 1 / d₀) * M i := by
  have hg := hx.1
  have ht := div_mem_Icc_of_mem_cone hx
  have hk := hR.six_le i
  set k := R.k i with hkdef
  set t := x.1 / x.2 with htdef
  have hx1 : x.1 = t * x.2 := by rw [htdef]; field_simp
  have h1 := hM.abs_deriv_le hd i ht
  have h2 := hM.k_mul_abs_D_le hd i ht
  have h3 := hM.t_mul_abs_deriv_le i ht
  have hpow : x.2 ^ k = x.2 ^ (k - 1) * x.2 := by
    rw [← pow_succ]; congr 1; omega
  set a := x.2 ^ k * (deriv (R.D i) t / x.2) with ha
  set b := (k : ℝ) * x.2 ^ (k - 1) * R.D i t - x.2 ^ k * deriv (R.D i) t * x.1 / x.2 ^ 2 with hb
  have ha' : a = x.2 ^ (k - 1) * deriv (R.D i) t := by
    rw [ha, hpow]; field_simp
  have hb' : b = x.2 ^ (k - 1) * ((k : ℝ) * R.D i t - t * deriv (R.D i) t) := by
    rw [hb, hpow, hx1]; field_simp
  have hp : 0 ≤ x.2 ^ (k - 1) := by positivity
  have hnorm : ‖termDeriv R i x‖ ≤ |a| + |b| := norm_smul_fst_add_smul_snd_le a b
  refine hnorm.trans ?_
  have hMi : 0 ≤ M i := hM.nonneg hd (hx.1.trans_le (le_refl _) |> fun _ => by
    have := ht.2; have := ht.1; linarith) i
  have e1 : |a| ≤ x.2 ^ (k - 1) * (M i / d₀) := by
    rw [ha', abs_mul, abs_of_nonneg hp]
    exact mul_le_mul_of_nonneg_left h1 hp
  have e2 : |b| ≤ x.2 ^ (k - 1) * (2 * M i) := by
    rw [hb', abs_mul, abs_of_nonneg hp]
    refine mul_le_mul_of_nonneg_left ?_ hp
    calc |(k : ℝ) * R.D i t - t * deriv (R.D i) t|
        ≤ |(k : ℝ) * R.D i t| + |t * deriv (R.D i) t| := abs_sub _ _
      _ ≤ M i + M i := by
          refine add_le_add ?_ ?_
          · rw [abs_mul, Nat.abs_cast]; exact h2
          · rw [abs_mul, abs_of_nonneg (by linarith [ht.1] : 0 ≤ t)]; exact h3
      _ = 2 * M i := by ring
  calc |a| + |b| ≤ x.2 ^ (k - 1) * (M i / d₀) + x.2 ^ (k - 1) * (2 * M i) := add_le_add e1 e2
    _ = x.2 ^ (k - 1) * (2 + 1 / d₀) * M i := by field_simp; ring

theorem abs_termFn_le (hM : Bnd R d₀ T₀ M) (hR : R.IsAdmissible d₀) (hd : 0 < d₀) (i : ι)
    {x : ℝ × ℝ} (hx : x ∈ cone d₀ T₀) : |termFn R i x| ≤ x.2 ^ 6 * M i := by
  have hg := hx.1
  have ht := div_mem_Icc_of_mem_cone hx
  unfold termFn
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ x.2 ^ R.k i)]
  calc x.2 ^ R.k i * |R.D i (x.1 / x.2)| ≤ x.2 ^ 6 * M i := by
        refine mul_le_mul ?_ (hM.abs_D_le hd i ht) (abs_nonneg _) (by positivity)
        exact pow_le_pow_of_le_one hg.le hx.2.1 (hR.six_le i)

theorem summable_termFn (hM : Bnd R d₀ T₀ M) (hR : R.IsAdmissible d₀) (hd : 0 < d₀)
    {x : ℝ × ℝ} (hx : x ∈ cone d₀ T₀) : Summable fun i => termFn R i x :=
  Summable.of_norm_bounded ((hM.summable).mul_left (x.2 ^ 6)) fun i => by
    rw [Real.norm_eq_abs]; exact abs_termFn_le hM hR hd i hx

theorem abs_serF_le (hM : Bnd R d₀ T₀ M) (hR : R.IsAdmissible d₀) (hd : 0 < d₀)
    {x : ℝ × ℝ} (hx : x ∈ cone d₀ T₀) : |serF R x| ≤ x.2 ^ 6 * ∑' i, M i := by
  have := tsum_of_norm_bounded ((hM.summable).mul_left (x.2 ^ 6)).hasSum
    (fun i => by rw [Real.norm_eq_abs]; exact abs_termFn_le hM hR hd i hx)
  rw [tsum_mul_left] at this
  simpa [serF, Real.norm_eq_abs] using this

/-- Lipschitz estimate for the series on the cone. -/
theorem lipschitzOnWith_serF (hR : R.IsAdmissible d₀) (hM : Bnd R d₀ T₀ M) (hd : 0 < d₀) :
    LipschitzOnWith (Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i)) (serF R) (cone d₀ T₀) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hMn : ∀ i, 0 ≤ M i := fun i => hM.nonneg hd (by
    have := (div_mem_Icc_of_mem_cone hx); linarith [this.1, this.2]) i
  have hterm : ∀ i, ‖termFn R i x - termFn R i y‖ ≤ ((2 + 1 / d₀) * M i) * ‖x - y‖ := by
    intro i
    have := (convex_cone d₀ T₀).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := termFn R i) (f' := termDeriv R i) (C := (2 + 1 / d₀) * M i)
      (fun z hz => (hasFDerivAt_termFn' R hR.contDiffOn_D hz.1
        (by obtain ⟨h1, -, h3, -⟩ := hz; nlinarith)).hasFDerivWithinAt)
      (fun z hz => (norm_termDeriv_le hR hM hd i hz).trans (by
        have hp : z.2 ^ (R.k i - 1) ≤ 1 := pow_le_one₀ hz.1.le hz.2.1
        have : 0 ≤ (2 + 1 / d₀) * M i := mul_nonneg (by positivity) (hMn i)
        nlinarith))
      hy hx
    exact this
  have hsx := summable_termFn hM hR hd hx
  have hsy := summable_termFn hM hR hd hy
  have hS : Summable fun i => ((2 + 1 / d₀) * M i) * ‖x - y‖ :=
    ((hM.summable.mul_left (2 + 1 / d₀)).mul_right _)
  have := tsum_of_norm_bounded hS.hasSum (f := fun i => termFn R i x - termFn R i y) hterm
  rw [Real.dist_eq]
  calc |serF R x - serF R y| = ‖∑' i, (termFn R i x - termFn R i y)‖ := by
        rw [Real.norm_eq_abs, hsx.tsum_sub hsy]; rfl
    _ ≤ ∑' i, ((2 + 1 / d₀) * M i) * ‖x - y‖ := this
    _ = (Real.toNNReal ((2 + 1 / d₀) * ∑' i, M i) : ℝ) * dist x y := by
        rw [tsum_mul_right, tsum_mul_left, Real.coe_toNNReal _ (by
          have : 0 ≤ ∑' i, M i := tsum_nonneg hMn
          positivity), dist_eq_norm]

end Estimates

end Dual

end SandierSerfaty

end
