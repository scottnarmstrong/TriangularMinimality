/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Radial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The sector functions, `f₀`, `e`, the calibration constants, and the primitive `g`

Exactly the objects of paper `cal:radial-integrals`, `cal:f0-e`, `cal:positive-kernel`, as real functions of the radial data of
`Radial.lean`; all sums include the index `0` and are `tsum`s over `ℕ` (`ℕ × ℕ` for the double sums;
they are absolutely convergent, which is proved in other modules). Nothing here asserts convergence.

* `S₁ t = ∫₀ᵗ B r r dr`, `S₂ t = ∫₀ᵗ (-2 B₁ + r B₁²) dr`, `H k t = t^{-k} ∫₀ᵗ B₁ r^k dr`
  (indexed by the *exponent* `k`, so both modes with exponent six use `H 6`),
  `Q i t = t D_i'(t) - k_i D_i(t)` (`cal:radial-integrals`);
* `f₀ t`, `e t` (`cal:f0-e`);
* `lam`, `mu`, `K` (`cal:constants`; the first integrand `(f₀(√(p²+s²)) - f₀ p)/s²` is used as written, its
  value `0` at `s = 0` is irrelevant for the interval integral);
* `f t = f₀ t - lam t²/2 - mu`, `G d s = d f(t)/t² - s² e(t)/(d t²)` with `t = √(d²+s²)`,
  `g d x = ∫₀ˣ G d s ds` (`cal:primitive`).

The truncations `Trunc.*` (modes `0, …, 38` only; the tilde objects of §6–§7) are in `Trunc.lean`.
-/

open MeasureTheory

public section

namespace SandierSerfaty

namespace Calibration

/-- `S₁(t) = ∫₀ᵗ B(r) r dr` (paper `cal:radial-integrals`). -/
@[expose] noncomputable def S₁ (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, B r * r

/-- `S₂(t) = ∫₀ᵗ (-2 B₁(r) + r B₁(r)²) dr` (paper `cal:radial-integrals`). -/
@[expose] noncomputable def S₂ (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, (-2 * B₁ r + r * B₁ r ^ 2)

/-- `H_k(t) = t^{-k} ∫₀ᵗ B₁(r) r^k dr`, indexed by the exponent `k` (paper `cal:radial-integrals`, §5.4). -/
@[expose] noncomputable def H (k : ℕ) (t : ℝ) : ℝ := (t ^ k)⁻¹ * ∫ r in (0 : ℝ)..t, B₁ r * r ^ k

/-- `Q_i(t) = t D_i'(t) - k_i D_i(t)` (paper `cal:radial-integrals`). -/
@[expose] noncomputable def Q (i : ℕ) (t : ℝ) : ℝ := t * deriv (D i) t - (k i : ℝ) * D i t

/-- The radial source and energy function `f₀` (paper `cal:f0-e`). -/
@[expose] noncomputable def f₀ (t : ℝ) : ℝ :=
  -2 * Real.pi * (S₁ t + t ^ 2 * ∑' i, D i t / ((k i : ℝ) + 2))
    - 1 / 2 * (Real.log t + S₂ t
      + ∑' i, (-2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t)
      + ∑' ij : ℕ × ℕ, (k ij.1 : ℝ) * (k ij.2 : ℝ) / ((k ij.1 : ℝ) + (k ij.2 : ℝ))
          * D ij.1 t * D ij.2 t)

/-- The angular coefficient `e(t) = ½ ∑_{i,j} Q_i Q_j / (k_i + k_j)` (paper `cal:f0-e`). -/
@[expose] noncomputable def e (t : ℝ) : ℝ :=
  1 / 2 * ∑' ij : ℕ × ℕ, Q ij.1 t * Q ij.2 t / ((k ij.1 : ℝ) + (k ij.2 : ℝ))

/-- The calibration constant `λ` (paper `cal:constants`). The first integral is parenthesized:
without the parentheses the integrand of `∫ s in 0..x₀, …` would swallow the rest of the sum, so that the
last term would read `x₀ ∫ e` instead of `(1/p) ∫ e`. -/
@[expose] noncomputable def lam : ℝ :=
  1 / (p * x₀) *
    (p / x₀ * (f₀ R₀ - f₀ p) - x₀ / p * e R₀
      + p * (∫ s in (0 : ℝ)..x₀, (f₀ (√(p ^ 2 + s ^ 2)) - f₀ p) / s ^ 2)
      + 1 / p * ∫ s in (0 : ℝ)..x₀, e (√(p ^ 2 + s ^ 2)))

/-- The calibration constant `μ = f₀(R₀) - e(R₀)/3 - λ R₀²/2` (paper `cal:constants`). -/
@[expose] noncomputable def mu : ℝ := f₀ R₀ - e R₀ / 3 - lam * R₀ ^ 2 / 2

/-- The adjusted radial function `f(t) = f₀(t) - λ t²/2 - μ` (paper `cal:primitive`). -/
@[expose] noncomputable def f (t : ℝ) : ℝ := f₀ t - lam * t ^ 2 / 2 - mu

/-- The radius `t = √(d² + s²)` of the point at signed height `s` over the edge at distance `d`. -/
@[expose] noncomputable def tt (d s : ℝ) : ℝ := √(d ^ 2 + s ^ 2)

/-- The integrand `G(d, s) = d f(t)/t² - s² e(t)/(d t²)`, `t = √(d²+s²)` (paper `cal:primitive`). -/
@[expose] noncomputable def G (d s : ℝ) : ℝ :=
  d / tt d s ^ 2 * f (tt d s) - s ^ 2 / (d * tt d s ^ 2) * e (tt d s)

/-- The primitive `g_d(x) = ∫₀ˣ G(d, s) ds` (paper `cal:primitive`). -/
@[expose] noncomputable def g (d x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, G d s

/-- The constant `K = 2 g_p(x₀)` (paper `cal:constants`). -/
@[expose] noncomputable def K : ℝ := 2 * g p x₀

theorem tt_sq {d s : ℝ} (hd : 0 < d) : tt d s ^ 2 = d ^ 2 + s ^ 2 := by
  unfold tt; exact Real.sq_sqrt (by positivity)

theorem tt_pos {d s : ℝ} (hd : 0 < d) : 0 < tt d s := by
  unfold tt; exact Real.sqrt_pos.2 (by positivity)

theorem tt_p_x₀ : tt p x₀ = R₀ := sqrt_p_sq_add_x₀_sq

/-- `G` is even in `s` (paper §5.5), so that `g_d` is odd. -/
theorem G_neg (d s : ℝ) : G d (-s) = G d s := by
  simp [G, tt]

/-- `g_d` is odd (paper §5.5). -/
theorem g_neg (d x : ℝ) : g d (-x) = -g d x := by
  unfold g
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x) (fun s => G d s)
  simp only [G_neg, neg_zero] at h
  have h2 := intervalIntegral.integral_symm (μ := volume) (f := fun s => G d s) (-x) 0
  linarith

theorem G_at_p_x₀ : G p x₀ = p / R₀ ^ 2 * f R₀ - x₀ ^ 2 / (p * R₀ ^ 2) * e R₀ := by
  simp [G, tt_p_x₀]

end Calibration

end SandierSerfaty
