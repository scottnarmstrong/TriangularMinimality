/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.SeparationAverage
public import SandierSerfaty.Sphere.Scaling

/-!
# Separation of minimizers (sphere note, Theorem 4.2)

A minimizer `Y` of the logarithmic energy on `(S²)ⁿ`, `n ≥ 2`, satisfies
`‖yᵢ - yⱼ‖ ≥ c_sep / √n` for `i ≠ j`, `c_sep = √(log 2 / 10)` (`Sphere.separation`). The proof is the
isotropic averaging of the sphere note, in a chart whose pole is chosen so that `|xᵢ| ≤ 1`
(`Sphere.exists_chart`, `Sphere.chart_separation`). Corollaries: the chordal-to-chart comparison
`|xᵢ - xⱼ| ≥ c_sep / (2√n)` in any chart (`Sphere.separation_chart`) and the unit separation
`|zᵢ - zⱼ| ≥ 1` in blown-up coordinates `z = s_n x` (`Sphere.separation_blowup`).
-/

open Filter Topology Set Finset

public section

namespace SandierSerfaty

namespace Sphere

/-- The north pole `(0, 0, 1)`. -/
@[expose] noncomputable def northPole : R3 := EuclideanSpace.single 2 1

theorem norm_northPole : ‖northPole‖ = 1 := by simp [northPole]

theorem eq_northPole {w : R3} (hw : ‖w‖ = 1) (h2 : w 2 = 1) : w = northPole := by
  have hsq : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
    have := hw
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three] at this
    simpa [Real.norm_eq_abs, sq_abs] using this
  have h0 : w 0 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  have h1 : w 1 = 0 := by nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]
  ext i
  fin_cases i <;> simp [northPole, h0, h1, h2]

theorem lam_le_two (x : ℂ) : lam x ≤ 2 := by
  unfold lam
  rw [div_le_iff₀ (one_add_norm_sq_pos x)]
  linarith [sq_nonneg ‖x‖]

theorem one_le_lam {x : ℂ} (hx : ‖x‖ ≤ 1) : 1 ≤ lam x := by
  unfold lam
  rw [le_div_iff₀ (one_add_norm_sq_pos x)]
  nlinarith [norm_nonneg x]

theorem one_fifth_le_lam {x : ℂ} (hx : ‖x‖ ≤ 3) : 1 / 5 ≤ lam x := by
  unfold lam
  rw [div_le_div_iff₀ (by norm_num) (one_add_norm_sq_pos x)]
  nlinarith [norm_nonneg x]

theorem stereo_apply_two_le_zero {x : ℂ} (hx : ‖x‖ ≤ 1) : stereo x 2 ≤ 0 := by
  rw [stereo_apply_two]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [norm_nonneg x]) (one_add_norm_sq_pos x).le

theorem norm_le_one_of_stereo_apply_two_le_zero {x : ℂ} (h : stereo x 2 ≤ 0) : ‖x‖ ≤ 1 := by
  rw [stereo_apply_two, div_nonpos_iff] at h
  rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
  · linarith [one_add_norm_sq_pos x]
  · nlinarith [norm_nonneg x]

theorem three_lt_stereo_apply_two {x : ℂ} (hx : 3 < ‖x‖) : 4 / 5 < stereo x 2 := by
  rw [stereo_apply_two, lt_div_iff₀ (one_add_norm_sq_pos x)]
  nlinarith [norm_nonneg x]

/-- **Choice of chart.** For a minimizer `Y` and an index `i` there are an orthogonal map `R` and
chart points `X` with `T (X k) = R (Y k)` for all `k`, `R Y` a minimizer, `|X i| ≤ 1` and
`(R Y i)₃ ≤ 0`. -/
theorem exists_chart {n : ℕ} {Y : Fin n → R3} (hY : IsSphereMinimizer Y) (i : Fin n) :
    ∃ (R : R3 ≃ₗᵢ[ℝ] R3) (X : Fin n → ℂ), IsSphereMinimizer (fun k => R (Y k)) ∧
      (∀ k, stereo (X k) = R (Y k)) ∧ ‖X i‖ ≤ 1 := by
  classical
  have hinf : (Metric.sphere (0 : R3) 1).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := stereo) stereo_injective fun x => ?_
    simpa using norm_stereo x
  obtain ⟨v, hv, hvF⟩ := hinf.exists_notMem_finset
    (Finset.univ.image Y ∪ Finset.univ.image fun k => -Y k)
  have hvn : ‖v‖ = 1 := by simpa using hv
  have hvY : ∀ k, Y k ≠ v := fun k h => hvF (Finset.mem_union_left _
    (Finset.mem_image.2 ⟨k, Finset.mem_univ k, h⟩))
  have hvY' : ∀ k, Y k ≠ -v := fun k h => hvF (Finset.mem_union_right _
    (Finset.mem_image.2 ⟨k, Finset.mem_univ k, by rw [h, neg_neg]⟩))
  -- the pole `p = ± v`, in the closed hemisphere opposite to `Y i`
  obtain ⟨p, hpn, hpi, hpY⟩ : ∃ p : R3, ‖p‖ = 1 ∧ inner ℝ p (Y i) ≤ 0 ∧ ∀ k, Y k ≠ p := by
    by_cases h : inner ℝ v (Y i) ≤ 0
    · exact ⟨v, hvn, h, hvY⟩
    · refine ⟨-v, by rw [norm_neg, hvn], ?_, hvY'⟩
      rw [inner_neg_left]; linarith [not_le.1 h]
  obtain ⟨R, hR⟩ := exists_isometry_apply_eq (a := p) (b := northPole) (by rw [hpn, norm_northPole])
  have hW := hY.comp_isometry R
  have hne : ∀ k, (R (Y k)) 2 ≠ 1 := fun k h => by
    have := eq_northPole (hW.norm_eq k) h
    exact hpY k (R.injective (by rw [hR]; exact this))
  choose X hX using fun k => exists_stereo_eq (hW.norm_eq k) (hne k)
  refine ⟨R, X, hW, hX, ?_⟩
  refine norm_le_one_of_stereo_apply_two_le_zero ?_
  rw [hX i]
  have h1 : (R (Y i)) 2 = inner ℝ northPole (R (Y i)) := by
    simp [northPole, EuclideanSpace.inner_single_left]
  rw [h1, ← hR, LinearIsometryEquiv.inner_map_map]
  exact hpi

theorem sqrt_div_le_of_chart {n : ℕ} (hn : 2 ≤ n) :
    cSep / Real.sqrt n = Real.sqrt (Real.log 2 / (10 * n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  unfold cSep
  rw [← Real.sqrt_div (by positivity)]
  congr 1
  field_simp

/-- **Theorem 4.2 (separation).** A minimizer of `E` on `(S²)ⁿ`, `n ≥ 2`, satisfies
`‖yᵢ - yⱼ‖ ≥ c_sep / √n` for `i ≠ j`. -/
theorem separation {n : ℕ} (hn : 2 ≤ n) {Y : Fin n → R3} (hY : IsSphereMinimizer Y) {i j : Fin n}
    (hij : i ≠ j) : cSep / Real.sqrt n ≤ ‖Y i - Y j‖ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (x := 2) (by norm_num) (by norm_num)
    linarith
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨R, X, hW, hX, hXi⟩ := exists_chart hY i
  have hnorm : ‖Y i - Y j‖ = ‖stereo (X i) - stereo (X j)‖ := by
    rw [hX, hX, ← map_sub, LinearIsometryEquiv.norm_map]
  rw [hnorm, sqrt_div_le_of_chart hn, norm_stereo_sub]
  have hsep := chart_separation hn hW hX (i := i) (j := j) hij.symm
  by_cases hj : ‖X j‖ ≤ 3
  · -- both points in a bounded region of the chart
    have hl : 1 / 5 ≤ lam (X i) * lam (X j) := by
      have := one_le_lam hXi
      have := one_fifth_le_lam hj
      nlinarith [lam_pos (X i), lam_pos (X j)]
    have h1 : Real.sqrt (1 / 5) ≤ Real.sqrt (lam (X i) * lam (X j)) := Real.sqrt_le_sqrt hl
    calc Real.sqrt (Real.log 2 / (10 * n)) ≤ Real.sqrt (1 / 5) *
          Real.sqrt (Real.log 2 / (2 * ((n : ℝ) - 1))) := by
          rw [← Real.sqrt_mul (by norm_num)]
          refine Real.sqrt_le_sqrt ?_
          rw [show 1 / 5 * (Real.log 2 / (2 * ((n : ℝ) - 1))) = Real.log 2 / (10 * ((n : ℝ) - 1))
            by field_simp; ring]
          exact div_le_div_of_nonneg_left hlog2.le (by linarith) (by linarith)
      _ ≤ Real.sqrt (lam (X i) * lam (X j)) * ‖X i - X j‖ :=
          mul_le_mul h1 hsep (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · -- `x_j` is far: the third coordinates already separate the points
    rw [not_le] at hj
    have h3 := three_lt_stereo_apply_two hj
    have h4 : stereo (X i) 2 ≤ 0 := stereo_apply_two_le_zero hXi
    have h5 : |(stereo (X i) - stereo (X j)) 2| ≤ ‖stereo (X i) - stereo (X j)‖ := by
      have := PiLp.norm_apply_le (stereo (X i) - stereo (X j)) 2
      simpa using this
    have h6 : 4 / 5 ≤ ‖stereo (X i) - stereo (X j)‖ := by
      refine le_trans ?_ h5
      rw [PiLp.sub_apply, abs_sub_comm]
      rw [abs_of_pos (by linarith)]
      linarith
    rw [← norm_stereo_sub] at *
    calc Real.sqrt (Real.log 2 / (10 * n)) ≤ 4 / 5 := by
          rw [Real.sqrt_le_left (by norm_num)]
          rw [div_le_iff₀ (by positivity)]
          linarith
      _ ≤ _ := h6

/-- **Theorem 4.2 (consequence in any chart).** If `T (x_k) = R y_k` for an orthogonal map `R`, then
`|x_i - x_j| ≥ c_sep / (2 √n)`. -/
theorem separation_chart {n : ℕ} (hn : 2 ≤ n) {Y : Fin n → R3} (hY : IsSphereMinimizer Y)
    (R : R3 ≃ₗᵢ[ℝ] R3) {X : Fin n → ℂ} (hX : ∀ k, stereo (X k) = R (Y k)) {i j : Fin n}
    (hij : i ≠ j) : cSep / (2 * Real.sqrt n) ≤ ‖X i - X j‖ := by
  have hsep := separation hn hY hij
  have hnorm : ‖Y i - Y j‖ = ‖stereo (X i) - stereo (X j)‖ := by
    rw [hX, hX, ← map_sub, LinearIsometryEquiv.norm_map]
  rw [hnorm, norm_stereo_sub] at hsep
  have hl : Real.sqrt (lam (X i) * lam (X j)) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := lam_le_two (X i)
    have := lam_le_two (X j)
    nlinarith [lam_pos (X i), lam_pos (X j)]
  have h2 : Real.sqrt (lam (X i) * lam (X j)) * ‖X i - X j‖ ≤ 2 * ‖X i - X j‖ :=
    mul_le_mul_of_nonneg_right hl (norm_nonneg _)
  have hn0 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  rw [div_le_iff₀ (by positivity)]
  calc cSep = cSep / Real.sqrt n * Real.sqrt n := by field_simp
    _ ≤ 2 * ‖X i - X j‖ * Real.sqrt n := by gcongr; exact hsep.trans h2
    _ = ‖X i - X j‖ * (2 * Real.sqrt n) := by ring

/-- **Theorem 4.2 (blown-up coordinates).** With `z_k = s_n x_k`, `s_n = κ √n`, `|z_i - z_j| ≥ 1`. -/
theorem separation_blowup {n : ℕ} (hn : 2 ≤ n) {Y : Fin n → R3} (hY : IsSphereMinimizer Y)
    (R : R3 ≃ₗᵢ[ℝ] R3) {X : Fin n → ℂ} (hX : ∀ k, stereo (X k) = R (Y k)) {i j : Fin n}
    (hij : i ≠ j) : 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖ := by
  have h := separation_chart hn hY R hX hij
  have hn0 : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < n))
  have hs : 0 < blowupScale n := blowupScale_pos (by omega)
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hs.le]
  have hc : 0 < cSep := cSep_pos
  calc (1 : ℝ) = blowupScale n * (cSep / (2 * Real.sqrt n)) := by
        unfold blowupScale blowupKappa; field_simp
    _ ≤ _ := by gcongr

end Sphere

end SandierSerfaty

end
