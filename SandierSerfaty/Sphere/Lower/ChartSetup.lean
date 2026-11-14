/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Apriori
public import SandierSerfaty.Sphere.Separation
public import SandierSerfaty.Sphere.SeparationChart

/-!
# Setup for a minimizer (sphere note, Definition 6.7, "Setup for a minimizer")

For a minimizer `Y` (`n ≥ 2`), `Lower.exists_chart_setup` produces chart coordinates `X : Fin n → ℂ` (the stereographic
preimage of a rotation of `Y` avoiding both poles) with `X` injective, `xᵢ ≠ 0`, `𝔎(T X) = 𝔎(Y)`, and the blown-up points
`1`-separated in both charts `X` and `ι X` (the second uses `‖T ιx - T ιy‖ = ‖T x - T y‖`).
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The chordal distance is invariant under the inversion `ι`. -/
theorem norm_stereo_invC_sub {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖stereo (invC x) - stereo (invC y)‖ = ‖stereo x - stereo y‖ := by
  rw [norm_stereo_sub, norm_stereo_sub, norm_invC_sub hx hy, lam_invC hx, lam_invC hy]
  have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h : Real.sqrt (‖x‖ ^ 2 * lam x * (‖y‖ ^ 2 * lam y)) =
      ‖x‖ * ‖y‖ * Real.sqrt (lam x * lam y) := by
    rw [show ‖x‖ ^ 2 * lam x * (‖y‖ ^ 2 * lam y) = (‖x‖ * ‖y‖) ^ 2 * (lam x * lam y) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  rw [h]
  field_simp

theorem exists_chart_setup {n : ℕ} (hn : 2 ≤ n) {Y : Fin n → R3} (hY : IsSphereMinimizer Y) :
    ∃ X : Fin n → ℂ, Function.Injective X ∧ (∀ i, X i ≠ 0) ∧
      normalizedEnergy (fun i => stereo (X i)) = normalizedEnergy Y ∧
      (∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) ∧
      (∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • invC (X i) - blowupScale n • invC (X j)‖) := by
  classical
  have hn0 : 0 < n := by omega
  have hs := blowupScale_pos hn0
  obtain ⟨R, hR⟩ := exists_isometry_avoiding Y norm_northPole
  have hex : ∀ i, ∃ x : ℂ, stereo x = R (Y i) := fun i => by
    refine exists_stereo_eq (by rw [LinearIsometryEquiv.norm_map, hY.norm_eq]) ?_
    intro h
    exact (hR i).1 (eq_northPole (by rw [LinearIsometryEquiv.norm_map, hY.norm_eq]) h)
  choose X hX using hex
  have hXY : ∀ i j, ‖X i - X j‖ ≠ 0 → True := fun _ _ _ => trivial
  have hXi : Function.Injective X := fun a b h => by
    have : R (Y a) = R (Y b) := by rw [← hX, ← hX, h]
    exact hY.injective (R.injective this)
  have hX0 : ∀ i, X i ≠ 0 := by
    intro i h
    apply (hR i).2
    rw [← hX, h]
    ext k
    fin_cases k <;> simp [stereo, northPole]
  refine ⟨X, hXi, hX0, ?_, ?_, ?_⟩
  · unfold normalizedEnergy
    have : sphereEnergy (fun i => stereo (X i)) = sphereEnergy Y := by
      simp only [hX]; exact sphereEnergy_comp_isometry Y R
    rw [this]
  · intro i j hij
    exact separation_blowup hn hY R hX hij
  · intro i j hij
    have hsep := separation hn hY hij
    have hnorm : ‖stereo (invC (X i)) - stereo (invC (X j))‖ = ‖Y i - Y j‖ := by
      rw [norm_stereo_invC_sub (hX0 i) (hX0 j), hX, hX, ← map_sub, LinearIsometryEquiv.norm_map]
    rw [← hnorm, norm_stereo_sub] at hsep
    have hl : Real.sqrt (lam (invC (X i)) * lam (invC (X j))) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have := lam_le_two (invC (X i))
      have := lam_le_two (invC (X j))
      nlinarith [lam_pos (invC (X i)), lam_pos (invC (X j))]
    have h2 : Real.sqrt (lam (invC (X i)) * lam (invC (X j))) * ‖invC (X i) - invC (X j)‖ ≤
        2 * ‖invC (X i) - invC (X j)‖ := mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn0)
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg hs.le]
    have hc : 0 < cSep := cSep_pos
    have hsep' := hsep.trans h2
    rw [sqrt_div_le_of_chart hn] at hsep
    calc (1 : ℝ) = blowupScale n * (cSep / (2 * Real.sqrt n)) := by
          unfold blowupScale blowupKappa; field_simp
      _ ≤ _ := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          have h3 : cSep / Real.sqrt n ≤ 2 * ‖invC (X i) - invC (X j)‖ := by
            have := hsep.trans h2
            rwa [sqrt_div_le_of_chart hn]
          calc cSep = cSep / Real.sqrt n * Real.sqrt n := by field_simp
            _ ≤ 2 * ‖invC (X i) - invC (X j)‖ * Real.sqrt n := by gcongr
            _ = ‖invC (X i) - invC (X j)‖ * (2 * Real.sqrt n) := by ring

end Lower

end Sphere

end SandierSerfaty

end
