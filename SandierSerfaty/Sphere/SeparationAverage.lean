/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.SeparationChart
public import SandierSerfaty.Sphere.RadialGreen
public import SandierSerfaty.Sphere.ChartLaplacian
public import SandierSerfaty.Sphere.Density

/-!
# Separation of minimizers (sphere note, Theorem 4.2): isotropic averaging

* `Sphere.integral_gKer_circle`: `⨍_{∂B(c,ρ)} g(· - z) = -log max(ρ, |z - c|)`;
* `Sphere.circleAverage_potV_le`: `⨍_{∂B(c,ρ)} V - V(c) ≤ ρ²` (radial Green identity and
  `ΔV = 4π µ ≤ 4`);
* `Sphere.chart_separation`: for a minimizer `T ∘ X`, `|x_i - x_j| ≥ √(log 2 / (2(n-1)))`.
-/

open MeasureTheory Filter Topology Set Finset Laplacian
open scoped ENNReal ContDiff

public section

namespace SandierSerfaty

namespace Sphere

theorem integral_gKer_circle (c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ θ in Ioo (-Real.pi) Real.pi, gKer (c + circleMap 0 ρ θ - z) =
      -(2 * Real.pi * Real.log (max ρ ‖z - c‖)) := by
  have h := integral_log_norm_sub_circle (z - c) hρ
  have e : ∀ θ : ℝ, gKer (c + circleMap 0 ρ θ - z) = -Real.log ‖z - c - circleMap 0 ρ θ‖ := by
    intro θ
    unfold gKer
    rw [← norm_neg (c + circleMap 0 ρ θ - z)]
    congr 3; ring
  simp only [e]
  rw [integral_neg, h]

theorem circleAverage_potV_le (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Real.circleAverage potV c ρ - potV c ≤ ρ ^ 2 := by
  have hpi := Real.pi_pos
  have hcd : ∀ x : ℂ, ContDiffAt ℝ 2 potV x := fun x =>
    (contDiff_potV.of_le (by norm_cast)).contDiffAt
  have key := circleAverage_sub_eq_integral (u := potV) (ϱ := fun x => 2 * dens x) (p := c)
    hρ ((contDiff_potV.of_le (by norm_cast)).contDiffAt)
    (fun x _ _ => hcd x) (continuous_dens.const_mul 2 |>.continuousOn)
    (fun x _ _ => by rw [laplacian_potV]; ring)
  rw [key]
  have hint : Integrable (fun x : ℂ => truncLog ρ (x - c)) :=
    (Screening.integrable_truncLog hρ).comp_sub_right c
  have hnn : ∀ x : ℂ, 0 ≤ truncLog ρ (x - c) := fun x => Screening.truncLog_nonneg ρ (x - c)
  have hdens : ∀ x : ℂ, 0 ≤ dens x := fun x => by rw [dens_eq]; positivity
  calc ∫ x in Metric.ball c ρ, truncLog ρ (x - c) * (2 * dens x)
      ≤ ∫ x in Metric.ball c ρ, (2 / Real.pi) * truncLog ρ (x - c) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => ?_)
          (hint.const_mul (2 / Real.pi)).integrableOn
          (ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun x _ => ?_)
        · exact mul_nonneg (hnn x) (mul_nonneg two_pos.le (hdens x))
        · have := dens_le x
          have h2 : 2 * dens x ≤ 2 / Real.pi := by
            calc 2 * dens x ≤ 2 * (1 / Real.pi) := by linarith
              _ = 2 / Real.pi := by ring
          calc truncLog ρ (x - c) * (2 * dens x) ≤ truncLog ρ (x - c) * (2 / Real.pi) :=
                mul_le_mul_of_nonneg_left h2 (hnn x)
            _ = 2 / Real.pi * truncLog ρ (x - c) := mul_comm _ _
    _ ≤ ∫ x, (2 / Real.pi) * truncLog ρ (x - c) :=
        setIntegral_le_integral (hint.const_mul (2 / Real.pi))
          (Eventually.of_forall fun x => mul_nonneg (by positivity) (hnn x))
    _ = ρ ^ 2 := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun y => truncLog ρ y) c,
          Screening.integral_truncLog_eq hρ]
        field_simp

/-- **Chart separation.** In any chart in which `W = T ∘ X` is a minimizer,
`|x_i - x_j| ≥ √(log 2 / (2 (n - 1)))` for `j ≠ i`. -/
theorem chart_separation {n : ℕ} (hn : 2 ≤ n) {W : Fin n → R3} (hW : IsSphereMinimizer W)
    {X : Fin n → ℂ} (hX : ∀ k, stereo (X k) = W k) {i j : Fin n} (hji : j ≠ i) :
    Real.sqrt (Real.log 2 / (2 * ((n : ℝ) - 1))) ≤ ‖X i - X j‖ := by
  classical
  have hpi := Real.pi_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hN : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hNc : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  set N : ℝ := (n : ℝ) - 1 with hNdef
  set r₀ : ℝ := 2 * Real.sqrt (Real.log 2 / (2 * N)) with hr₀
  have hr₀sq : r₀ ^ 2 = 2 * Real.log 2 / N := by
    rw [hr₀, mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  have hr₀pos : 0 < r₀ := by rw [hr₀]; positivity
  have hXinj : ∀ b, b ≠ i → X i ≠ X b := fun b hb h => hb (hW.injective (by rw [← hX, ← hX, h]))
  by_contra hlt
  rw [not_le] at hlt
  set d : ℝ := ‖X i - X j‖ with hd
  have hdpos : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 (hXinj j hji))
  have hd2 : 2 * d < r₀ := by rw [hr₀]; linarith
  -- choice of the radius
  obtain ⟨ρ, hρmem, hρne⟩ := (Set.Ioc_infinite hd2).exists_notMem_finset
    (Finset.univ.image fun b => ‖X i - X b‖)
  have hρ2 : 2 * d < ρ := hρmem.1
  have hρr : ρ ≤ r₀ := hρmem.2
  have hρ0 : 0 < ρ := by linarith
  have hρb : ∀ b, b ≠ i → ‖X i - X b‖ ≠ ρ := fun b hb h =>
    hρne (Finset.mem_image.2 ⟨b, Finset.mem_univ b, h⟩)
  set c : ℂ := X i with hc
  -- the circle avoids the other chart points
  have hcirc : ∀ θ : ℝ, ∀ b, b ≠ i → c + circleMap 0 ρ θ ≠ X b := by
    intro θ b hb h
    apply hρb b hb
    have : ‖circleMap 0 ρ θ‖ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ0]
    rw [← this, norm_sub_rev, hc]
    congr 1
    rw [← h]; ring
  have hmin := fun θ => chart_minimality hW hX i (x := c + circleMap 0 ρ θ)
    (fun b hb => hcirc θ b hb)
  set φ : ℂ → ℝ := fun x => ∑ b ∈ Finset.univ.erase i, gKer (x - X b) + (N / 2) * potV x with hφ
  have hmin' : ∀ θ : ℝ, φ c ≤ φ (c + circleMap 0 ρ θ) := fun θ => by
    have := hmin θ
    rw [hNc] at this
    exact this
  -- continuity along the circle
  have hcg : ∀ b, b ≠ i → Continuous fun θ : ℝ => gKer (c + circleMap 0 ρ θ - X b) := by
    intro b hb
    unfold gKer
    exact (Continuous.log (by have := continuous_circleMap 0 ρ; fun_prop)
      fun θ => norm_ne_zero_iff.2 (sub_ne_zero.2 (hcirc θ b hb))).neg
  have hcp : Continuous fun θ : ℝ => potV (c + circleMap 0 ρ θ) :=
    contDiff_potV.continuous.comp (continuous_const.add (continuous_circleMap 0 ρ))
  have iG : ∀ b ∈ Finset.univ.erase i, IntegrableOn (fun θ : ℝ => gKer (c + circleMap 0 ρ θ - X b))
      (Ioo (-Real.pi) Real.pi) := fun b hb =>
    ((hcg b (Finset.ne_of_mem_erase hb)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have iP : IntegrableOn (fun θ : ℝ => potV (c + circleMap 0 ρ θ)) (Ioo (-Real.pi) Real.pi) :=
    hcp.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have iS : IntegrableOn (fun θ : ℝ => ∑ b ∈ Finset.univ.erase i, gKer (c + circleMap 0 ρ θ - X b))
      (Ioo (-Real.pi) Real.pi) := integrable_finsetSum _ iG
  -- integrate the pointwise inequality
  have hineq : ∫ _θ in Ioo (-Real.pi) Real.pi, φ c ≤
      ∫ θ in Ioo (-Real.pi) Real.pi, φ (c + circleMap 0 ρ θ) :=
    setIntegral_mono_on (integrableOn_const (by simp)) (iS.add (iP.const_mul (N / 2))) measurableSet_Ioo
      fun θ _ => hmin' θ
  have hconst : ∫ _θ in Ioo (-Real.pi) Real.pi, φ c = 2 * Real.pi * φ c := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]; ring
  have hsplit : ∫ θ in Ioo (-Real.pi) Real.pi, φ (c + circleMap 0 ρ θ) =
      ∑ b ∈ Finset.univ.erase i, (-(2 * Real.pi * Real.log (max ρ ‖X b - c‖))) +
        N / 2 * (2 * Real.pi * Real.circleAverage potV c ρ) := by
    simp only [hφ]
    rw [integral_add iS (iP.const_mul (N / 2)), integral_finsetSum _ iG, integral_const_mul]
    congr 1
    · exact Finset.sum_congr rfl fun b hb => integral_gKer_circle c (X b) hρ0
    · congr 1
      have := integral_Ioo_eq_circleAverage (fun z : ℂ => potV (z + c)) ρ
      simp only [add_comm c] at this ⊢
      rw [this, Real.circleAverage_map_add_const]
  have hφc : φ c = ∑ b ∈ Finset.univ.erase i, -Real.log ‖X i - X b‖ + N / 2 * potV c := by
    simp only [hφ, gKer]
    rfl
  have havg := circleAverage_potV_le c hρ0
  have hsplit' : ∫ θ in Ioo (-Real.pi) Real.pi, φ (c + circleMap 0 ρ θ) =
      2 * Real.pi * (∑ b ∈ Finset.univ.erase i, -Real.log (max ρ ‖X b - c‖) +
        N / 2 * Real.circleAverage potV c ρ) := by
    rw [hsplit, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun b _ => by ring
    · ring
  have h1 := hineq
  rw [hconst, hsplit', hφc] at h1
  have h2 := le_of_mul_le_mul_left h1 (by positivity)
  -- reduce to the comparison of logarithms
  have hdb : ∀ b ∈ Finset.univ.erase i, 0 < ‖X i - X b‖ := fun b hb =>
    norm_pos_iff.2 (sub_ne_zero.2 (hXinj b (Finset.ne_of_mem_erase hb)))
  have hnorm : ∀ b, ‖X b - c‖ = ‖X i - X b‖ := fun b => by rw [norm_sub_rev, hc]
  simp only [hnorm] at h2
  set T : Fin n → ℝ := fun b => Real.log ‖X i - X b‖ - Real.log (max ρ ‖X i - X b‖) with hT
  have hTle : ∀ b ∈ Finset.univ.erase i, T b ≤ 0 := fun b hb => by
    have := Real.log_le_log (hdb b hb) (le_max_right ρ ‖X i - X b‖)
    simp only [hT]; linarith
  have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩
  have hSle : ∑ b ∈ Finset.univ.erase i, T b ≤ T j := by
    rw [← Finset.add_sum_erase _ _ hjmem]
    have : ∑ b ∈ (Finset.univ.erase i).erase j, T b ≤ 0 :=
      Finset.sum_nonpos fun b hb => hTle b (Finset.mem_of_mem_erase hb)
    linarith
  have hTj : T j < -Real.log 2 := by
    have hdρ : d < ρ := by linarith
    have : max ρ ‖X i - X j‖ = ρ := max_eq_left hdρ.le
    simp only [hT, this]
    have h3 : Real.log (2 * d) < Real.log ρ := Real.log_lt_log (by positivity) hρ2
    rw [Real.log_mul (by norm_num) hdpos.ne'] at h3
    rw [← hd]
    linarith
  have hsum : ∑ b ∈ Finset.univ.erase i, T b =
      ∑ b ∈ Finset.univ.erase i, Real.log ‖X i - X b‖ -
        ∑ b ∈ Finset.univ.erase i, Real.log (max ρ ‖X i - X b‖) := by
    simp only [hT, Finset.sum_sub_distrib]
  have hρN : N / 2 * ρ ^ 2 ≤ Real.log 2 := by
    have : ρ ^ 2 ≤ r₀ ^ 2 := pow_le_pow_left₀ hρ0.le hρr 2
    calc N / 2 * ρ ^ 2 ≤ N / 2 * r₀ ^ 2 := by gcongr
      _ = Real.log 2 := by rw [hr₀sq]; field_simp
  have hav : N / 2 * (Real.circleAverage potV c ρ - potV c) ≤ N / 2 * ρ ^ 2 := by gcongr
  simp only [Finset.sum_neg_distrib] at h2
  linarith [h2, hsum, hSle, hTj, hρN, hav]

end Sphere

end SandierSerfaty

end
