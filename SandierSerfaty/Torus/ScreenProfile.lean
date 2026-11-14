/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The screening profile of the separation lemma

Paper proof of Lemma `geo:separation`: with `r_* = 1/√π`,

```
φ(x) = -log(|x| / r_*) + (π/2) (|x|² - r_*²)   for 0 < |x| < r_*,       φ(x) = 0   for |x| ≥ r_*.
```

Here `screenProfile t` is the radial profile (`t = |x|`). It is nonnegative, strictly positive for
`0 < t < r_*`, vanishes for `t ≥ r_*`, and is continuous on `t > 0` (value and radial derivative
vanish at `r_*`; the radial derivative is not needed).
-/

open Filter Topology Set

public section

namespace SandierSerfaty

namespace Torus

/-- The separation radius `r_* = 1/√π`. -/
@[expose] noncomputable def rStar : ℝ := (√Real.pi)⁻¹

theorem rStar_pos : 0 < rStar := inv_pos.2 (Real.sqrt_pos.2 Real.pi_pos)

/-- `π r_*² = 1`: the disk of radius `r_*` has area one. -/
theorem pi_mul_rStar_sq : Real.pi * rStar ^ 2 = 1 := by
  unfold rStar
  rw [inv_pow, Real.sq_sqrt Real.pi_pos.le]
  exact mul_inv_cancel₀ Real.pi_pos.ne'

/-- For `n ≥ 2`, `r_* < √n / 2` (half the shortest lattice vector). -/
theorem rStar_lt_sqrt_div_two {n : ℕ} (hn : 2 ≤ n) : rStar < √(n : ℝ) / 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi := Real.pi_gt_three
  have h1 : 2 < √((n : ℝ) * Real.pi) :=
    (Real.lt_sqrt (by norm_num)).2 (by nlinarith)
  rw [Real.sqrt_mul (Nat.cast_nonneg n)] at h1
  have hp : 0 < √Real.pi := Real.sqrt_pos.2 Real.pi_pos
  unfold rStar
  rw [inv_eq_one_div, div_lt_div_iff₀ hp two_pos]
  linarith

/-- The formula `-log(t / r_*) + (π/2)(t² - r_*²)` of the profile inside the disk. -/
@[expose] noncomputable def screenFormula (t : ℝ) : ℝ :=
  -Real.log (t / rStar) + Real.pi / 2 * (t ^ 2 - rStar ^ 2)

/-- The radial profile of the screening potential `φ`. -/
@[expose] noncomputable def screenProfile (t : ℝ) : ℝ :=
  if t < rStar then screenFormula t else 0

theorem screenFormula_rStar : screenFormula rStar = 0 := by
  unfold screenFormula
  rw [div_self rStar_pos.ne']
  simp

theorem screenProfile_of_lt {t : ℝ} (h : t < rStar) : screenProfile t = screenFormula t := by
  simp [screenProfile, h]

theorem screenProfile_of_le {t : ℝ} (h : rStar ≤ t) : screenProfile t = 0 := by
  simp [screenProfile, not_lt.2 h]

theorem screenFormula_pos {t : ℝ} (ht : 0 < t) (h : t ≠ rStar) : 0 < screenFormula t := by
  unfold screenFormula
  set s := t / rStar with hs
  have hr := rStar_pos
  have hs0 : 0 < s := div_pos ht hr
  have hs1 : s ≠ 1 := by
    intro h1
    apply h
    have : t = s * rStar := by rw [hs]; field_simp
    rw [this, h1, one_mul]
  have hts : t = s * rStar := by rw [hs]; field_simp
  have h2 : Real.pi / 2 * (t ^ 2 - rStar ^ 2) = (s ^ 2 - 1) / 2 := by
    rw [hts]
    have := pi_mul_rStar_sq
    nlinarith [this]
  rw [h2]
  have hlog : Real.log (s ^ 2) < s ^ 2 - 1 :=
    Real.log_lt_sub_one_of_pos (by positivity) (by
      intro h1
      apply hs1
      nlinarith [sq_nonneg (s - 1), sq_nonneg (s + 1)])
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

theorem screenFormula_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ screenFormula t := by
  by_cases h : t = rStar
  · rw [h, screenFormula_rStar]
  · exact (screenFormula_pos ht h).le

theorem screenProfile_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ screenProfile t := by
  unfold screenProfile
  split_ifs with h
  · exact screenFormula_nonneg ht
  · exact le_rfl

theorem screenProfile_pos {t : ℝ} (ht : 0 < t) (h : t < rStar) : 0 < screenProfile t := by
  rw [screenProfile_of_lt h]
  exact screenFormula_pos ht h.ne

theorem continuousAt_screenFormula {t : ℝ} (ht : 0 < t) : ContinuousAt screenFormula t := by
  unfold screenFormula
  have hr := rStar_pos
  have : ContinuousAt (fun t : ℝ => t / rStar) t := by fun_prop
  refine ContinuousAt.add ?_ (by fun_prop)
  exact (this.log (div_pos ht hr).ne').neg

/-- The profile is continuous away from `0`. -/
theorem continuousAt_screenProfile {t : ℝ} (ht : 0 < t) : ContinuousAt screenProfile t := by
  have hr := rStar_pos
  rcases lt_trichotomy t rStar with h | h | h
  · refine (continuousAt_screenFormula ht).congr ?_
    filter_upwards [Iio_mem_nhds h] with s hs
    exact (screenProfile_of_lt hs).symm
  · subst h
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · refine (continuousAt_screenFormula ht).continuousWithinAt.congr (fun s hs => ?_) ?_
      · rcases (mem_Iic.1 hs).lt_or_eq with h1 | h1
        · exact screenProfile_of_lt h1
        · rw [h1, screenFormula_rStar, screenProfile_of_le le_rfl]
      · rw [screenProfile_of_le le_rfl, screenFormula_rStar]
    · refine (continuousWithinAt_const (b := (0 : ℝ))).congr (fun s hs => ?_) ?_
      · exact screenProfile_of_le (mem_Ici.1 hs)
      · exact screenProfile_of_le le_rfl
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Ioi_mem_nhds h] with s hs
    exact (screenProfile_of_le hs.le).symm

end Torus

end SandierSerfaty

end
