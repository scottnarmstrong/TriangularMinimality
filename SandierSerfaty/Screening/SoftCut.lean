/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenData
public import SandierSerfaty.Screening.FieldGluing
public import SandierSerfaty.Screening.ChartBox
public import SandierSerfaty.Screening.PieceField

/-!
# The soft cut (screening note, Lemma 4.11(b),(d))

The screening note, Lemma 4.11 (`lem:soft`), parts (b) and (d), for the data
`Scr.Data` under `Scr.Data.Hyp`:

* `Hyp.integral_inner_X_gradient`: for every Lipschitz `χ` with compact support in `{δ > d - 1}`,
  `∫ X · ∇χ = 2π(∑_{K} χ(p) + ∫ (∑_{D*} u_q) χ - m ∫ χ)` (I1 for `Φ`, Lemma 4.5 for the radial pieces;
  the charges of `C \ (K ∪ D*)` do not see `χ`);
* `Hyp.isFieldPiece_psiX`: **Lemma 4.11(b)**: `ψX` is a field piece with charges `K` and source
  `ρ₀ = 2πmψ - 2πψ ∑_{D*} u_q + X · ∇ψ` (`= 2πm - g` on `Q`, `0` off `Q`), i.e.
  `∫ ψX · ∇φ = 2π ∑_K φ(p) - ∫ ρ₀ φ` for smooth compactly supported `φ`;
* `Hyp.setIntegral_g`: **Lemma 4.11(d)**: `∫_Q g = 2π(N - #K)`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real ContDiff

public section

namespace SandierSerfaty.Screening.Scr

namespace Data

variable (D : Data)

/-- The truncated field `ψX`. -/
@[expose] noncomputable def psiX (x : ℂ) : ℂ := D.psi x • D.X x

/-- The source of `ψX`: `ρ₀ = 2πmψ - 2πψ ∑_{D*} u_q + X · ∇ψ`. -/
@[expose] noncomputable def rho0 (x : ℂ) : ℝ :=
  2 * π * D.m * D.psi x - 2 * π * D.psi x * D.uSum x + inner ℝ (D.X x) (gradient D.psi x)

variable {D}

theorem rho0_eq (x : ℂ) : D.rho0 x = 2 * π * D.m - D.g x := by
  rw [rho0, g]; ring

theorem isClosed_setOf_le_dep (a : ℝ) : IsClosed {x | a ≤ D.dep x} :=
  isClosed_le continuous_const continuous_dep

theorem psi_eq_zero_of_notMem {x : ℂ} (hx : x ∉ {x | D.d - 1 ≤ D.dep x}) : D.psi x = 0 :=
  psi_eq_zero (le_of_lt (not_le.1 hx))

theorem volume_Q : volume D.Q = ENNReal.ofReal D.t ^ 2 := by
  rw [Q, sq, volume_reProdIm, Real.volume_Icc, Real.volume_Icc, pow_two]
  congr 1 <;> ring_nf

theorem setOf_le_dep_subset_U {a : ℝ} (ha : 1 / 2 < a) : {x | a ≤ D.dep x} ⊆ D.U := fun x hx => by
  rw [mem_U_iff]; exact lt_of_lt_of_le ha hx

theorem measurable_uSum : Measurable D.uSum :=
  Finset.measurable_sum _ fun q _ => (measurable_radialU _).comp (measurable_id.sub_const q)

theorem uSum_le (x : ℂ) : D.uSum x ≤ 16 / π * D.Ds.card := by
  rw [uSum_eq, nD]
  gcongr
  exact Finset.filter_subset _ _

/-- `ρ₀` vanishes off `{δ ≥ d - 1}`. -/
theorem rho0_eq_zero_of_notMem {x : ℂ} (hx : x ∉ {x | D.d - 1 ≤ D.dep x}) : D.rho0 x = 0 := by
  have hx' : D.dep x < D.d - 1 := not_le.1 hx
  rw [rho0, psi_eq_zero hx'.le, gradient_psi_of_lt' hx', inner_zero_right]
  ring

namespace Hyp

variable (h : D.Hyp)
include h

/-- `X` is integrable on every compact subset of `U`. -/
theorem integrableOn_X {S : Set ℂ} (hS : IsCompact S) (hSU : S ⊆ D.U) : IntegrableOn D.X S := by
  have h1 := h.integrableOn_Φ hS hSU
  have h2 : Integrable fun x => ∑ p ∈ D.K, gradient (truncLog (1 / 4)) (x - p) :=
    integrable_finsetSum _ fun p _ => integrable_gradient_truncLog (by norm_num) p
  have h3 : Integrable fun x => ∑ q ∈ D.Ds, radialW (1 / 4) (x - q) :=
    integrable_finsetSum _ fun q _ =>
      (integrable_radialW (by norm_num)).comp_sub_right q
  exact (h1.add h2.integrableOn).sub h3.integrableOn

theorem integrableOn_X_Abar : IntegrableOn D.X D.Abar :=
  h.integrableOn_X ((isCompact_dep_ge (D := D) (D.d - 1)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_dep).inter
        (isClosed_le continuous_dep continuous_const)) fun _ hx => hx.1)
    (fun _ hx => (setOf_le_dep_subset_U (by linarith [h.d_pos])) hx.1)

/-- `ψX` is integrable. -/
theorem integrable_psiX : Integrable D.psiX := by
  set S := {x | D.d - 1 ≤ D.dep x}
  have hS : IsCompact S := isCompact_dep_ge _
  have hX := h.integrableOn_X hS (setOf_le_dep_subset_U (by linarith [h.d_pos]))
  have heq : D.psiX = S.indicator D.psiX := by
    ext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, psiX, psi_eq_zero_of_notMem hx, zero_smul]
  rw [heq, integrable_indicator_iff hS.measurableSet]
  refine Integrable.mono' hX.norm
    ((continuous_psi.aestronglyMeasurable.restrict).smul hX.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [psiX, norm_smul, Real.norm_eq_abs, abs_of_nonneg (psi_nonneg x)]
  exact mul_le_of_le_one_left (norm_nonneg _) (psi_le_one x)

/-- `ρ₀` is integrable. -/
theorem integrable_rho0 : Integrable D.rho0 := by
  set S := {x | D.d - 1 ≤ D.dep x}
  have hS : IsCompact S := isCompact_dep_ge _
  have hfin : volume S ≠ ⊤ := hS.measure_lt_top.ne
  have heq : D.rho0 = S.indicator D.rho0 := by
    ext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, rho0_eq_zero_of_notMem hx]
  rw [heq, integrable_indicator_iff hS.measurableSet]
  have hb1 : IntegrableOn (fun x => 2 * π * D.m * D.psi x - 2 * π * D.psi x * D.uSum x) S := by
    refine Measure.integrableOn_of_bounded (M := 2 * π * |D.m| + 2 * π * (16 / π * D.Ds.card)) hfin
      ((continuous_psi.aestronglyMeasurable.const_mul _).sub
        ((continuous_psi.aestronglyMeasurable.const_mul _).mul
          measurable_uSum.aestronglyMeasurable)) (Eventually.of_forall fun x => ?_)
    have h0 := psi_nonneg (D := D) x
    have h1 := psi_le_one (D := D) x
    have h2 := uSum_nonneg (D := D) x
    have h3 := uSum_le (D := D) x
    have hpi := Real.pi_pos
    have ha : |2 * π * D.m * D.psi x| ≤ 2 * π * |D.m| := by
      rw [show 2 * π * D.m * D.psi x = (2 * π) * (D.m * D.psi x) by ring, abs_mul,
        abs_of_pos Real.two_pi_pos, abs_mul, abs_of_nonneg h0]
      gcongr
      exact mul_le_of_le_one_right (abs_nonneg _) h1
    have hb : |2 * π * D.psi x * D.uSum x| ≤ 2 * π * (16 / π * D.Ds.card) := by
      rw [abs_of_nonneg (by positivity)]
      have : D.psi x * D.uSum x ≤ 16 / π * D.Ds.card := by nlinarith
      nlinarith
    rw [Real.norm_eq_abs]
    calc |2 * π * D.m * D.psi x - 2 * π * D.psi x * D.uSum x|
        ≤ |2 * π * D.m * D.psi x| + |2 * π * D.psi x * D.uSum x| := abs_sub _ _
      _ ≤ 2 * π * |D.m| + 2 * π * (16 / π * D.Ds.card) := add_le_add ha hb
  have hb2 : IntegrableOn (fun x => inner ℝ (D.X x) (gradient D.psi x)) S := by
    have hA := h.integrableOn_X_Abar
    have heq2 : (fun x => inner ℝ (D.X x) (gradient D.psi x)) =
        D.Abar.indicator fun x => inner ℝ (D.X x) (gradient D.psi x) := by
      ext x
      by_cases hx : x ∈ D.Abar
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, gradient_psi_of_notMem hx, inner_zero_right]
    rw [heq2]
    refine ((integrable_indicator_iff measurableSet_Abar).2 ?_).integrableOn
    refine Integrable.mono' hA.norm
      (hA.aestronglyMeasurable.inner (aestronglyMeasurable_gradient _))
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    calc |inner ℝ (D.X x) (gradient D.psi x)| ≤ ‖D.X x‖ * ‖gradient D.psi x‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖D.X x‖ * 1 := by gcongr; exact norm_gradient_psi_le x
      _ = ‖D.X x‖ := mul_one _
  exact hb1.add hb2

/-- The pairing of `X` with Lipschitz functions supported in `{δ > d - 1}`. -/
theorem integral_inner_X_gradient {χ : ℂ → ℝ} {Kχ : ℝ≥0} (hχ : LipschitzWith Kχ χ)
    (hχc : HasCompactSupport χ) (hχ0 : ∀ x, D.dep x ≤ D.d - 1 → χ x = 0) :
    ∫ x, inner ℝ (D.X x) (gradient χ x) =
      2 * π * ((∑ p ∈ D.K, χ p) + (∫ x, D.uSum x * χ x) - D.m * ∫ x, χ x) := by
  have hq : (0 : ℝ) < 1 / 4 := by norm_num
  have hU := setOf_le_dep_subset_U (D := D) (a := D.d - 1) (by linarith [h.d_pos])
  have hχs : tsupport χ ⊆ {x | D.d - 1 ≤ D.dep x} := by
    refine closure_minimal (fun x hx => ?_) (isClosed_setOf_le_dep _)
    by_contra hc
    exact hx (hχ0 x (le_of_lt (not_le.1 hc)))
  -- I1 for `Φ`
  have hI1 := integral_inner_truncField_lipschitz isOpen_U h.hC h.hE
    (α := fun _ => 1 / 4) (fun _ _ => hq) ⟨1 / 4, fun _ _ => le_rfl⟩ hχ hχc (hχs.trans hU)
  -- the charges far from the cut do not see `χ`
  have hfar : ∀ p ∈ D.C, p ∉ D.K ∪ D.Ds → Real.circleAverage χ p (1 / 4) = 0 := by
    intro p hp hpKD
    rw [Finset.mem_union, not_or] at hpKD
    have hdep := h.dep_le_of_notMem hp hpKD.1 hpKD.2
    refine Real.circleAverage_const_on_circle fun z hz => ?_
    rw [mem_sphere, abs_of_pos hq] at hz
    refine hχ0 z ?_
    have h2 := dep_le_add (D := D) z p
    rw [dist_eq_norm] at hz
    linarith
  have hKDC : ((D.K ∪ D.Ds : Finset ℂ) : Set ℂ) ⊆ D.C := by
    rw [Finset.coe_union]; exact union_subset h.K_subset_C h.Ds_subset_C
  rw [finsum_mem_eq_finsetSum hKDC hfar, Finset.sum_union h.disjoint_K_Ds] at hI1
  change ∫ x, inner ℝ (D.Φ x) (gradient χ x) = _ at hI1
  -- the radial pieces
  have hK1 : ∀ p ∈ D.K, ∫ x, inner ℝ (gradient (truncLog (1 / 4)) (x - p)) (gradient χ x) =
      2 * π * (χ p - Real.circleAverage χ p (1 / 4)) := fun p _ =>
    integral_inner_gradient_truncLog_lipschitz hq p hχ
  have hD1 : ∀ q ∈ D.Ds, ∫ x, inner ℝ (radialW (1 / 4) (x - q)) (gradient χ x) =
      2 * π * (Real.circleAverage χ q (1 / 4) - ∫ x, radialU (1 / 4) (x - q) * χ x) := fun q _ =>
    integral_inner_radialW hq q hχ
  -- integrability
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖gradient χ x‖ ≤ B := ⟨Kχ, fun x => norm_gradient_le_of_lipschitz hχ x⟩
  have hgm : AEStronglyMeasurable (gradient χ) volume := aestronglyMeasurable_gradient χ
  have hintΦ : Integrable fun x => inner ℝ (D.Φ x) (gradient χ x) := by
    have hS : IsCompact (tsupport χ) := hχc
    have hΦS := h.integrableOn_Φ hS (hχs.trans hU)
    have heq : (fun x => inner ℝ (D.Φ x) (gradient χ x)) =
        (tsupport χ).indicator fun x => inner ℝ (D.Φ x) (gradient χ x) := by
      ext x
      by_cases hx : x ∈ tsupport χ
      · rw [indicator_of_mem hx]
      · rw [indicator_of_notMem hx, gradient_eq_zero_of_notMem_tsupport hx, inner_zero_right]
    rw [heq, integrable_indicator_iff (isClosed_tsupport _).measurableSet]
    exact Integrable.mono' (hΦS.norm.const_mul B) (hΦS.aestronglyMeasurable.inner hgm.restrict)
      (Eventually.of_forall fun x => (abs_real_inner_le_norm _ _).trans (by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)))
  have hbdd : ∀ {V : ℂ → ℂ}, Integrable V → Integrable fun x => inner ℝ (V x) (gradient χ x) :=
    fun {V} hV => Integrable.mono' (hV.norm.const_mul B) (hV.aestronglyMeasurable.inner hgm)
      (Eventually.of_forall fun x => (abs_real_inner_le_norm _ _).trans (by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)))
  have hintK : ∀ p ∈ D.K, Integrable fun x =>
      inner ℝ (gradient (truncLog (1 / 4)) (x - p)) (gradient χ x) :=
    fun p _ => hbdd (integrable_gradient_truncLog hq p)
  have hintD : ∀ q ∈ D.Ds, Integrable fun x => inner ℝ (radialW (1 / 4) (x - q)) (gradient χ x) :=
    fun q _ => hbdd ((integrable_radialW hq).comp_sub_right q)
  -- assemble
  have hX : (fun x => inner ℝ (D.X x) (gradient χ x)) = fun x =>
      inner ℝ (D.Φ x) (gradient χ x) +
        ∑ p ∈ D.K, inner ℝ (gradient (truncLog (1 / 4)) (x - p)) (gradient χ x) -
          ∑ q ∈ D.Ds, inner ℝ (radialW (1 / 4) (x - q)) (gradient χ x) := by
    ext x
    rw [X, inner_sub_left, inner_add_left, sum_inner, sum_inner]
  have h12 : Integrable fun x => inner ℝ (D.Φ x) (gradient χ x) +
      ∑ p ∈ D.K, inner ℝ (gradient (truncLog (1 / 4)) (x - p)) (gradient χ x) :=
    hintΦ.add (integrable_finsetSum _ hintK)
  rw [hX, integral_sub h12 (integrable_finsetSum _ hintD),
    integral_add hintΦ (integrable_finsetSum _ hintK), integral_finsetSum _ hintK,
    integral_finsetSum _ hintD, hI1, Finset.sum_congr rfl hK1, Finset.sum_congr rfl hD1]
  have hu : ∫ x, D.uSum x * χ x = ∑ q ∈ D.Ds, ∫ x, radialU (1 / 4) (x - q) * χ x := by
    have hint : ∀ q ∈ D.Ds, Integrable fun x => radialU (1 / 4) (x - q) * χ x := by
      intro q _
      obtain ⟨M, hM⟩ := hχc.exists_bound_of_continuous hχ.continuous
      exact Integrable.mono' (((integrable_radialU _).comp_sub_right q).const_mul M)
        (((measurable_radialU _).comp (measurable_id.sub_const q)).aestronglyMeasurable.mul
          hχ.continuous.aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [norm_mul, Real.norm_of_nonneg (radialU_nonneg _ _), mul_comm]
          exact mul_le_mul_of_nonneg_right (hM x) (radialU_nonneg _ _))
    rw [← integral_finsetSum _ hint]
    congr 1; ext x
    rw [uSum, Finset.sum_mul]
  rw [hu]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **Lemma 4.11(b)**: `ψX` is a field piece with charges `K` and source `ρ₀`. -/
theorem isFieldPiece_psiX : IsFieldPiece D.psiX D.K D.rho0 := by
  refine ⟨h.integrable_psiX, h.integrable_rho0, fun φ hφ hφc => ?_⟩
  obtain ⟨Kφ, hKφ⟩ := exists_lipschitzWith_of_contDiff hφ hφc
  obtain ⟨Bφ, hBφ⟩ := hφc.exists_bound_of_continuous hφ.continuous
  set χ : ℂ → ℝ := fun x => D.psi x * φ x
  have hχL : LipschitzWith (Kφ + Bφ.toNNReal) χ := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, NNReal.coe_add, Real.coe_toNNReal']
    have h1 : |D.psi a - D.psi b| ≤ dist a b := by
      rw [← Real.dist_eq]; simpa using lipschitzWith_psi.dist_le_mul a b
    have h2 : |φ a - φ b| ≤ Kφ * dist a b := by rw [← Real.dist_eq]; exact hKφ.dist_le_mul a b
    have hb : |φ b| ≤ Bφ := by simpa [Real.norm_eq_abs] using hBφ b
    have hpa := psi_nonneg (D := D) a
    have hpa1 := psi_le_one (D := D) a
    calc |D.psi a * φ a - D.psi b * φ b| = |D.psi a * (φ a - φ b) + φ b * (D.psi a - D.psi b)| := by
          ring_nf
      _ ≤ |D.psi a| * |φ a - φ b| + |φ b| * |D.psi a - D.psi b| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ 1 * (Kφ * dist a b) + max Bφ 0 * dist a b := by
          rw [abs_of_nonneg hpa]
          gcongr
          exact hb.trans (le_max_left _ _)
      _ = (Kφ + max Bφ 0) * dist a b := by ring
  have hχc : HasCompactSupport χ := hφc.mul_left
  have hχ0 : ∀ x, D.dep x ≤ D.d - 1 → χ x = 0 := fun x hx => by
    simp only [χ]; rw [psi_eq_zero hx, zero_mul]
  have hmain := h.integral_inner_X_gradient hχL hχc hχ0
  -- the product rule, a.e.
  have hdiff : ∀ᵐ x, DifferentiableAt ℝ D.psi x := lipschitzWith_psi.ae_differentiableAt
  have hprod : ∀ᵐ x, inner ℝ (D.X x) (gradient χ x) =
      inner ℝ (D.psiX x) (gradient φ x) + φ x * inner ℝ (D.X x) (gradient D.psi x) := by
    filter_upwards [hdiff] with x hx
    have hφd : DifferentiableAt ℝ φ x := (hφ.differentiable (by simp)).differentiableAt
    have hg : gradient χ x = D.psi x • gradient φ x + φ x • gradient D.psi x := by
      simp only [χ, gradient, fderiv_fun_mul hx hφd, map_add, map_smul]
    rw [hg, inner_add_right, inner_smul_right, inner_smul_right, psiX, real_inner_smul_left]
  -- integrability of the two pieces
  have hgφ : ∀ x, ‖gradient φ x‖ ≤ Kφ := fun x => norm_gradient_le_of_lipschitz hKφ x
  have hint1 : Integrable fun x => inner ℝ (D.psiX x) (gradient φ x) :=
    Integrable.mono' (h.integrable_psiX.norm.const_mul Kφ)
      (h.integrable_psiX.aestronglyMeasurable.inner (aestronglyMeasurable_gradient φ))
      (Eventually.of_forall fun x => (abs_real_inner_le_norm _ _).trans (by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hgφ x) (norm_nonneg _)))
  have hρφ : Integrable fun x => D.rho0 x * φ x :=
    Integrable.mono' (h.integrable_rho0.norm.const_mul Bφ)
      (h.integrable_rho0.aestronglyMeasurable.mul hφ.continuous.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul, mul_comm]; exact mul_le_mul_of_nonneg_right (hBφ x) (norm_nonneg _))
  -- `φ ⟪X, ∇ψ⟫ = φ (ρ₀ - 2πmψ + 2πψ ∑u)`
  have hsplit : ∀ x, φ x * inner ℝ (D.X x) (gradient D.psi x) =
      D.rho0 x * φ x - 2 * π * D.m * χ x + 2 * π * (D.uSum x * χ x) := by
    intro x; simp only [χ, rho0]; ring
  have hχi : Integrable χ := hχL.continuous.integrable_of_hasCompactSupport hχc
  have huχ : Integrable fun x => D.uSum x * χ x := by
    obtain ⟨M, hM⟩ := hχc.exists_bound_of_continuous hχL.continuous
    have hu : ∀ x, ‖D.uSum x‖ ≤ 16 / π * D.Ds.card := fun x => by
      rw [Real.norm_of_nonneg (uSum_nonneg x)]; exact uSum_le x
    exact Integrable.mono' (hχi.norm.const_mul (16 / π * D.Ds.card))
      (measurable_uSum.aestronglyMeasurable.mul hχi.aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _))
  have hint2 : Integrable fun x => φ x * inner ℝ (D.X x) (gradient D.psi x) := by
    simp_rw [hsplit]
    have hA : Integrable fun x => D.rho0 x * φ x - 2 * π * D.m * χ x := hρφ.sub (hχi.const_mul _)
    exact hA.add (huχ.const_mul _)
  have hlhs : ∫ x, inner ℝ (D.X x) (gradient χ x) =
      (∫ x, inner ℝ (D.psiX x) (gradient φ x)) +
        ∫ x, φ x * inner ℝ (D.X x) (gradient D.psi x) := by
    rw [← integral_add hint1 hint2]; exact integral_congr_ae hprod
  have hKχ : ∑ p ∈ D.K, χ p = ∑ p ∈ D.K, φ p := Finset.sum_congr rfl fun p hp => by
    simp only [χ]; rw [psi_eq_one (by linarith [(h.mem_K.1 hp).2]), one_mul]
  have hsplitI : ∫ x, φ x * inner ℝ (D.X x) (gradient D.psi x) =
      (∫ x, D.rho0 x * φ x) - 2 * π * D.m * (∫ x, χ x) + 2 * π * ∫ x, D.uSum x * χ x := by
    simp_rw [hsplit]
    have hA : Integrable fun x => D.rho0 x * φ x - 2 * π * D.m * χ x := hρφ.sub (hχi.const_mul _)
    have hB : Integrable fun x => 2 * π * (D.uSum x * χ x) := huχ.const_mul _
    have hC : Integrable fun x => 2 * π * D.m * χ x := hχi.const_mul _
    rw [integral_add hA hB, integral_sub hρφ hC, integral_const_mul, integral_const_mul]
  rw [hlhs, hsplitI, hKχ] at hmain
  linarith

theorem t_pos : 0 < D.t := by linarith [h.t_ge, h.ℓt_ge]

omit h in
theorem Q_subset_closedBall : D.Q ⊆ closedBall D.c D.t := fun x hx => by
  rw [Q, mem_sq_iff] at hx
  rw [mem_closedBall, dist_eq_norm]
  have h1 : |(x - D.c).re| ≤ D.t / 2 := by
    rw [Complex.sub_re, abs_le]; constructor <;> linarith [hx.1.1, hx.1.2]
  have h2 : |(x - D.c).im| ≤ D.t / 2 := by
    rw [Complex.sub_im, abs_le]; constructor <;> linarith [hx.2.1, hx.2.2]
  linarith [Complex.norm_le_abs_re_add_abs_im (x - D.c)]

theorem volume_real_Q : volume.real D.Q = D.t ^ 2 := by
  rw [measureReal_def, volume_Q, ENNReal.toReal_pow, ENNReal.toReal_ofReal h.t_pos.le]

/-- `g = 2πm - ρ₀` is integrable on `Q`. -/
theorem integrableOn_g_Q : IntegrableOn D.g D.Q := by
  have hfin : volume D.Q ≠ ⊤ := by rw [volume_Q]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have : D.g = fun x => 2 * π * D.m - D.rho0 x := by ext x; rw [rho0_eq]; ring
  rw [this]
  exact (integrableOn_const hfin).sub h.integrable_rho0.integrableOn

/-- `ρ₀` vanishes off `Q`. -/
theorem rho0_eq_zero_of_notMem_Q {x : ℂ} (hx : x ∉ D.Q) : D.rho0 x = 0 := by
  refine rho0_eq_zero_of_notMem fun hx' => hx ?_
  rw [mem_Q_iff]; simp only [mem_ofPred_eq] at hx'; linarith [h.d_pos]

/-- **Lemma 4.11(d)**: `∫_Q g = 2π(N - #K)`. -/
theorem setIntegral_g : ∫ x in D.Q, D.g x = 2 * π * ((D.N : ℝ) - D.K.card) := by
  have ht := h.t_pos
  -- a smooth function equal to `1` near `Q`
  let b : ContDiffBump D.c := ⟨2 * D.t, 2 * D.t + 1, by linarith, by linarith⟩
  have hb1 : ∀ x ∈ closedBall D.c (2 * D.t), b x = 1 := fun x hx => b.one_of_mem_closedBall hx
  have hgrad : ∀ x ∈ ball D.c (2 * D.t), gradient (⇑b) x = 0 := by
    intro x hx
    have hev : (⇑b) =ᶠ[nhds x] fun _ => 1 := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hb1 y (ball_subset_closedBall hy)
    simp only [gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]
  have hQb : ∀ x ∈ D.Q, x ∈ ball D.c (2 * D.t) := fun x hx => by
    have := Q_subset_closedBall hx
    rw [mem_closedBall] at this; rw [mem_ball]; linarith
  have hid := (h.isFieldPiece_psiX).2.2 b (b.contDiff (n := ⊤)) b.hasCompactSupport
  have hlhs : ∫ x, inner ℝ (D.psiX x) (gradient (⇑b) x) = 0 := by
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ D.Q
    · simp only [Pi.zero_apply]; rw [hgrad x (hQb x hx), inner_zero_right]
    · have : D.psiX x = 0 := by
        rw [psiX, psi_eq_zero, zero_smul]
        rw [mem_Q_iff, not_le] at hx; linarith [h.d_pos]
      simp only [Pi.zero_apply]; rw [this, inner_zero_left]
  have hK : ∑ y ∈ D.K, b y = D.K.card := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine Finset.sum_congr rfl fun p hp => hb1 p (ball_subset_closedBall (hQb p ?_))
    rw [mem_Q_iff]; linarith [(h.mem_K.1 hp).2, h.d_pos]
  have hρ : ∫ x, D.rho0 x * b x = ∫ x in D.Q, D.rho0 x := by
    rw [← integral_indicator D.measurableSet_Q]
    congr 1; ext x
    by_cases hx : x ∈ D.Q
    · rw [indicator_of_mem hx, hb1 x (ball_subset_closedBall (hQb x hx)), mul_one]
    · rw [indicator_of_notMem hx, h.rho0_eq_zero_of_notMem_Q hx, zero_mul]
  have hρQ : ∫ x in D.Q, D.rho0 x = 2 * π * D.m * D.t ^ 2 - ∫ x in D.Q, D.g x := by
    have : (fun x => D.rho0 x) = fun x => 2 * π * D.m - D.g x := by ext x; exact rho0_eq x
    rw [this, integral_sub (integrableOn_const (by
      rw [volume_Q]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) h.integrableOn_g_Q,
      setIntegral_const, smul_eq_mul, h.volume_real_Q]
    ring
  rw [hlhs, hK, hρ, hρQ] at hid
  have hN := h.N_eq
  linear_combination (-1 : ℝ) * hid + 2 * π * hN

end Hyp

end Data

end SandierSerfaty.Screening.Scr

end
