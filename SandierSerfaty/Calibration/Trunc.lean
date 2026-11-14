/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Sector

/-!
# The truncated objects (modes `0, …, 38`)

paper §6: "Tildes will always mean that the modes `m ≥ 39` have been omitted; the
index-zero term is retained." The truncated radial data are the full `u_i`, `D_i` for `i ≤ 38` (the tilde
objects of §6–§7 use the same `D_i`; only the sums stop at `38`):

* `Trunc.B t = ∑_{i=0}^{38} u_i(t)` and `Trunc.B₁ = B̃' + 1/t`;
* `Trunc.S₁, S₂, H` are defined from `B̃`, `B̃₁`; `Trunc.Q i = Q i` (same `D_i`);
* `Trunc.f₀, Trunc.e` are `cal:f0-e` with all sums over `i, j ∈ {0, …, 38}`.

The finite sums are `Finset.sum` over `Finset.range 39`; `Trunc.modes = 38` (the largest retained index).
-/

open MeasureTheory Finset

public section

namespace SandierSerfaty

namespace Calibration

namespace Trunc

/-- The largest retained mode, `38`. -/
@[expose] def modes : ℕ := 38

/-- `B̃(t) = ∑_{i=0}^{38} u_i(t)`. -/
@[expose] noncomputable def B (t : ℝ) : ℝ := ∑ i ∈ range (modes + 1), u i t

/-- `B̃₁(t) = B̃'(t) + 1/t`. -/
@[expose] noncomputable def B₁ (t : ℝ) : ℝ := deriv B t + 1 / t

/-- `S̃₁(t) = ∫₀ᵗ B̃(r) r dr`. -/
@[expose] noncomputable def S₁ (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, B r * r

/-- `S̃₂(t) = ∫₀ᵗ (-2 B̃₁ + r B̃₁²) dr`. -/
@[expose] noncomputable def S₂ (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, (-2 * B₁ r + r * B₁ r ^ 2)

/-- `H̃_k(t) = t^{-k} ∫₀ᵗ B̃₁(r) r^k dr`. -/
@[expose] noncomputable def H (k : ℕ) (t : ℝ) : ℝ := (t ^ k)⁻¹ * ∫ r in (0 : ℝ)..t, B₁ r * r ^ k

/-- `f̃₀`: `f₀` with the modes `m ≥ 39` omitted and `B̃, H̃` in place of `B, H`. -/
@[expose] noncomputable def f₀ (t : ℝ) : ℝ :=
  -2 * Real.pi * (S₁ t + t ^ 2 * ∑ i ∈ range (modes + 1), D i t / ((k i : ℝ) + 2))
    - 1 / 2 * (Real.log t + S₂ t
      + ∑ i ∈ range (modes + 1), (-2 * D i t + 2 * (k i : ℝ) * D i t * H (k i) t)
      + ∑ i ∈ range (modes + 1), ∑ j ∈ range (modes + 1),
          (k i : ℝ) * (k j : ℝ) / ((k i : ℝ) + (k j : ℝ)) * D i t * D j t)

/-- `ẽ(t) = ½ ∑_{i,j ≤ 38} Q_i Q_j / (k_i + k_j)`. -/
@[expose] noncomputable def e (t : ℝ) : ℝ :=
  1 / 2 * ∑ i ∈ range (modes + 1), ∑ j ∈ range (modes + 1),
    Q i t * Q j t / ((k i : ℝ) + (k j : ℝ))

end Trunc

end Calibration

end SandierSerfaty
