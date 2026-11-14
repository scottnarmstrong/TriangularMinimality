/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.PerRow

/-!
# The ring configuration is a configuration of distinct points of `S²`; the crude bound

* `Sphere.norm_ringConfig`: every point of `Y_n` lies on `S²`;
* `Sphere.ringConfig_injective`: for `n ≥ 102` the points of `Y_n` are pairwise distinct (distinct
  rows have distinct heights by (G4), and the points of one row are rotations by distinct `N_k`-th roots
  of unity);
* `Sphere.normalizedEnergy_ringConfig`: `𝔎(Y_n) = (n/2) log 2 + ∑_k B_k` (Proposition 5.5);
* `Sphere.normalizedEnergy_ringConfig_le`: the crude form of Theorem 5.13, `𝔎(Y_n) ≤ C n` for
  `n ≥ 102` (Proposition 5.12 (i) summed over the rows).
-/

open Complex Finset

public section

namespace SandierSerfaty

namespace Sphere

theorem norm_mercator (s t : ℝ) : ‖mercator s t‖ = 1 := by
  rw [mercator_eq_stereo]; exact norm_stereo _

/-- Equal Mercator points have `e^{ζ' - ζ} = 1`. -/
theorem exp_sub_eq_one_of_mercator_eq {s t s' t' : ℝ} (h : mercator s t = mercator s' t') :
    Complex.exp (((t' : ℂ) + (s' : ℂ) * I) - ((t : ℂ) + (s : ℂ) * I)) = 1 := by
  have h0 := norm_mercator_sub_eq s t s' t'
  rw [h, sub_self, norm_zero] at h0
  have hc : 0 < Real.sqrt (Real.cosh t * Real.cosh t') :=
    Real.sqrt_pos.2 (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))
  rw [eq_div_iff hc.ne', zero_mul] at h0
  rcases mul_eq_zero.1 h0.symm with h1 | h1
  · exact absurd h1 (Real.exp_pos _).ne'
  · exact (sub_eq_zero.1 (norm_eq_zero.1 h1)).symm

/-- Equal Mercator points have equal heights. -/
theorem height_eq_of_mercator_eq {s t s' t' : ℝ} (h : mercator s t = mercator s' t') : t = t' := by
  have h1 := congrArg norm (exp_sub_eq_one_of_mercator_eq h)
  rw [Complex.norm_exp, norm_one] at h1
  have h2 : (((t' : ℂ) + (s' : ℂ) * I) - ((t : ℂ) + (s : ℂ) * I)).re = t' - t := by simp
  rw [h2, Real.exp_eq_one_iff] at h1
  linarith

theorem ringConfig_apply (n : ℕ) (i : Fin n) :
    ∃ p : (Σ k : Fin (ringRows n).K, Fin ((ringRows n).N k)), ringConfig n i = (ringRows n).points p :=
  ⟨_, rfl⟩

/-- **`Y_n ⊂ S²`.** -/
theorem norm_ringConfig (n : ℕ) (i : Fin n) : ‖ringConfig n i‖ = 1 := by
  obtain ⟨p, hp⟩ := ringConfig_apply n i
  rw [hp]
  exact norm_mercator _ _

/-- Distinct rows of `Y_n` have distinct heights. -/
theorem ringHeight_inj {n k l : ℕ} (hn : 102 ≤ n) (hk : k < ringK n) (hl : l < ringK n)
    (h : ringHeight n k = ringHeight n l) : k = l := by
  have h0 : ∀ m < ringK n, (0 : ℝ) < 3 / (112 * (ringN n m : ℝ)) := fun m hm => by
    have : (3 : ℝ) ≤ ringN n m := by exact_mod_cast three_le_ringN (by omega) m hm
    positivity
  have := h0 k hk
  have := h0 l hl
  by_contra hkl
  rcases lt_or_gt_of_ne hkl with h' | h'
  · have := ringHeight_sep hn h' hl; linarith
  · have := ringHeight_sep hn h' hk; linarith

/-- The points of `Y_n` (indexed by rows) are pairwise distinct. -/
theorem ringRows_points_injective {n : ℕ} (hn : 102 ≤ n) : Function.Injective (ringRows n).points := by
  rintro ⟨k, a⟩ ⟨l, b⟩ h
  have h' : mercator ((ringRows n).angle k a) (ringHeight n k) =
      mercator ((ringRows n).angle l b) (ringHeight n l) := h
  have hkl : k = l := Fin.ext (ringHeight_inj hn k.2 l.2 (height_eq_of_mercator_eq h'))
  subst hkl
  have hN : 0 < (ringRows n).N k := ringRows_N_pos k.2
  have h1 := exp_sub_eq_one_of_mercator_eq h'
  have e : Complex.exp ((ringRows n).zeta k b - (ringRows n).zeta k a) = 1 := h1
  rw [(ringRows n).exp_zeta_sub_self k a b hN] at e
  have hω := Complex.isPrimitiveRoot_exp ((ringRows n).N k) hN.ne'
  have hne : Complex.exp (2 * Real.pi * I / (ringRows n).N k) ^ (a : ℕ) ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  have hab : (b : ℕ) = a := hω.pow_inj b.2 a.2 (by rw [mul_inv_eq_one₀ hne] at e; exact e)
  rw [show b = a from Fin.ext hab]

/-- **`Y_n` consists of `n` distinct points** (`n ≥ 102`). -/
theorem ringConfig_injective {n : ℕ} (hn : 102 ≤ n) : Function.Injective (ringConfig n) :=
  (ringRows_points_injective hn).comp
    (finSigmaFinEquiv.symm.injective.comp (Fin.cast_injective _))

/-- `∑_k N_k = n`. -/
theorem sum_ringN (n : ℕ) : ∑ k ∈ range (ringK n), (ringN n k : ℝ) = n := by
  have h := ringRows_card n
  rw [RowConfig.card] at h
  exact_mod_cast h

/-- **Proposition 5.5 for `Y_n`**, normalized: `𝔎(Y_n) = (n/2) log 2 + ∑_k B_k`. -/
theorem normalizedEnergy_ringConfig (n : ℕ) :
    normalizedEnergy (ringConfig n) =
      (n : ℝ) / 2 * Real.log 2 + ∑ k ∈ range (ringK n), (ringRows n).rowB k := by
  rw [normalizedEnergy, sphereEnergy_ringConfig]
  ring

/-- **Theorem 5.13, crude form**: `𝔎(Y_n) ≤ C n` for `n ≥ 102` (Proposition 5.12 (i)). -/
theorem normalizedEnergy_ringConfig_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 102 ≤ n →
    normalizedEnergy (ringConfig n) ≤ C * n := by
  obtain ⟨C, hC, hB⟩ := ringRows_rowB_le
  refine ⟨Real.log 2 / 2 + C, by positivity, fun n hn => ?_⟩
  rw [normalizedEnergy_ringConfig]
  have h := sum_le_sum fun k hk => hB n hn k (mem_range.1 hk)
  rw [← mul_sum, sum_ringN] at h
  linarith

end Sphere

end SandierSerfaty

end
