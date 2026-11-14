/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.GreenExpansion
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Convergence of the Green expansion on `|z| < a`, with all derivatives

Paper `cal:green-expansion`: the series `∑_{m ≥ 1} c_m Re (z^{6 m})` and all its
derivatives converge locally uniformly on the open disc `|z| < a`
(not "away from `|z| = a`": the series diverges for `|z| > a`).

Write `greenTerm m z = c_{m+1} z^{6(m+1)}` (complex) and `greenPartial N` for the partial sums.

* `Cal.hasSum_greenTerm`: the complex series converges on `|z| < a` (`greenSeries`), and
  `h_△ z = - log ‖z‖ + C_△ + π ‖z‖² / 2 + Re (greenSeries z)` there (`hTri_eq_re_greenSeries`);
* `Cal.summable_norm_greenTerm`: absolute convergence `∑ |c_m| r^{6m} < ∞` for `r < a`;
* `Cal.tendstoLocallyUniformlyOn_greenPartial_iteratedDeriv`: for every `k`, `∂^k` of the partial sums
  converges locally uniformly on `|z| < a` to `∂^k greenSeries` (Weierstrass' theorem for holomorphic
  limits, `TendstoLocallyUniformlyOn.deriv`);
* `Cal.tendstoLocallyUniformlyOn_greenPartial_re_iteratedFDeriv`: the same for the real series
  `∑ c_m Re (z^{6m})`, in terms of the real Fréchet derivatives `iteratedFDeriv ℝ k`.
-/

open Filter Topology Metric Complex
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm Torus

/-- The `m`-th term `c_{m+1} z^{6 (m+1)}` of the complex Green series. -/
@[expose] noncomputable def greenTerm (m : ℕ) (z : ℂ) : ℂ := (coeff (m + 1) : ℂ) * z ^ (6 * (m + 1))

/-- The sum of the complex Green series. -/
@[expose] noncomputable def greenSeries (z : ℂ) : ℂ := ∑' m : ℕ, greenTerm m z

theorem greenTerm_eq (m : ℕ) (z : ℂ) :
    hexPair.G (6 * (m + 1)) / ((6 * (m + 1) : ℕ) : ℂ) * (z / (a : ℂ)) ^ (6 * (m + 1)) =
      greenTerm m z := by
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  have h := triPair_G_six_mul (m + 1) (Nat.succ_pos m)
  rw [triPair_G] at h
  have hpn : ((a : ℂ) ^ (6 * (m + 1))) ≠ 0 := pow_ne_zero _ ha
  have hn0 : (((6 * (m + 1) : ℕ)) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 6 * (m + 1) ≠ 0)
  have h2 : hexPair.G (6 * (m + 1)) =
      (a : ℂ) ^ (6 * (m + 1)) * ((((6 * (m + 1) : ℕ) : ℝ) * coeff (m + 1) : ℝ) : ℂ) := by
    have := congrArg (fun t => (a : ℂ) ^ (6 * (m + 1)) * t) h
    beta_reduce at this
    rw [← mul_assoc, mul_inv_cancel₀ hpn, one_mul] at this
    exact this
  unfold greenTerm
  rw [h2, div_pow]
  push_cast
  field_simp

theorem exists_hasSum_greenTerm :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ ball (0 : ℂ) a, HasSum (fun m : ℕ => greenTerm m z) (Φ z) := by
  obtain ⟨C, Φ, -, -, hΦs, -⟩ := exists_green_series
  refine ⟨fun z => Φ (z / (a : ℂ)), fun z hz => ?_⟩
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  have hw : z / (a : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg a_pos.le,
      div_lt_one a_pos]
    simpa using hz
  have := hΦs _ hw
  convert this using 1
  funext m
  exact (greenTerm_eq m z).symm

theorem summable_greenTerm {z : ℂ} (hz : z ∈ ball (0 : ℂ) a) :
    Summable (fun m : ℕ => greenTerm m z) := by
  obtain ⟨Φ, hΦ⟩ := exists_hasSum_greenTerm
  exact (hΦ z hz).summable

/-- The complex Green series converges on `|z| < a`. -/
theorem hasSum_greenTerm {z : ℂ} (hz : z ∈ ball (0 : ℂ) a) :
    HasSum (fun m : ℕ => greenTerm m z) (greenSeries z) :=
  (summable_greenTerm hz).hasSum

/-- The real series of `cal:green-expansion` is the real part of the complex Green series. -/
theorem hTri_eq_re_greenSeries {z : ℂ} (hz : z ∈ ball (0 : ℂ) a) (hz0 : z ≠ 0) :
    hTri z = -Real.log ‖z‖ + CTri + Real.pi * ‖z‖ ^ 2 / 2 + (greenSeries z).re := by
  have hza : ‖z‖ < a := by simpa using hz
  have h1 := green_expansion_hasSum hz0 hza
  have h2 : HasSum (fun m : ℕ => (greenTerm m z).re) (greenSeries z).re :=
    Complex.reCLM.hasSum (hasSum_greenTerm hz)
  have h3 : (fun m : ℕ => (greenTerm m z).re) =
      fun m : ℕ => coeff (m + 1) * (z ^ (6 * (m + 1))).re := by
    funext m
    simp [greenTerm]
  rw [h3] at h2
  have := h1.unique h2
  linarith

end Calibration

end SandierSerfaty

end
