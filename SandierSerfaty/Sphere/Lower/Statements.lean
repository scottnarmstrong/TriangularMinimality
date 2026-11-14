/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.Neumann
public import SandierSerfaty.Sphere.Minimizer
public import SandierSerfaty.Assembly.Statements
public import SandierSerfaty.Statements.Jellium.Defs.TruncLog
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The statements assumed by the sphere lower bound (sphere note, §6)

Three `Prop`s, written out. Each is proved elsewhere (see below):

* `Assembly.TorusBoundStatement`: the square-torus bound `mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2),
  proved through the certificate (`CertData.CertificateGoal`).
* `Lower.Input63Statement`: **Input 6.3** of the sphere note (screening at constant density, with the repairs
  `ℓ ≥ ℓ₀(m₋, m₊)` and (X1)–(X3′)); proved from the screening theorem I4 (itself proved) as
  `Sphere.Bridge.input63Statement` (`Sphere/Bridge/Input63.lean`).
  `Lower.HasWeakGradientOn Ω u g` says `u ∈ H¹(Ω°)` with weak gradient `g` (as a complex number
  `∂ₓ u + i ∂ᵧ u`).
* `Lower.RingBoundStatement`: the conclusion of the ring upper bound (sphere note, Theorem 5.13):
  `min 𝔎 ≤ C_U n` for all `n ≥ 2`; proved as `Lower.ringBoundStatement` (`Sphere/Ring/RingBound.lean`).
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- `u ∈ H¹(Ω°)` with weak gradient `g`: `u` and `g` are square integrable on `Ω`, and
`∫_Ω u ∂φ = -∫_Ω g_φ φ` for every smooth `φ` with compact support in the interior of `Ω`
(`g = g.re + i g.im` represents `(∂ₓ u, ∂ᵧ u)`). -/
@[expose] def HasWeakGradientOn (Ω : Set ℂ) (u : ℂ → ℝ) (g : ℂ → ℂ) : Prop :=
  MemLp u 2 (volume.restrict Ω) ∧ MemLp g 2 (volume.restrict Ω) ∧
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ interior Ω →
      (∫ x in Ω, u x * fderiv ℝ φ x 1 = -∫ x in Ω, (g x).re * φ x) ∧
      (∫ x in Ω, u x * fderiv ℝ φ x Complex.I = -∫ x in Ω, (g x).im * φ x)

/-- **Input 6.3** (sphere note, screening at constant density; book Prop. 7.18 with Remark 7.19,
specialized; interface (X1)–(X3′) of Remark 6.4 and the repair `ℓ ≥ ℓ₀(m₋, m₊)`).

For `0 < m₋ ≤ m₊ ≤ 1/150` there are `C_S, C_scr, ℓ₀ ≥ 1`, depending only on `(m₋, m₊)`, such that: for a square
`Q = a₀ + [0,t]²`, `m̄ ∈ [m₋, m₊]` with `n̄ = m̄ t² ∈ ℕ`, `max(4 m₊/m₋, ℓ₀) ≤ ℓ ≤ ℓ̃ ≤ t/8`, points `X ⊆ Q` that
are `1`-separated, and `w` with `w^♮ = w - ∑ f_{1/4}(· - x) ∈ H¹(Q)` (weak gradient `g`) and
`-Δw = 2π(∑_{x ∈ X ∩ Q^{1/2}} δ_x - m̄)` in `𝒟'((Q^{1/2})°)`: if
`S := ∫_{Q^{ℓ̃/2} ∖ Q^{2ℓ̃}} |g|² ≤ ℓ³ ℓ̃ / C_scr`, then there are `n̄` pairwise distinct points `Y ⊂ Q°` with
`W^Neu_Q(Y; m̄) ≤ ½ ∫_Q |g|² + π p log ¼ - 2π m̄ ∑_{x ∈ X} ∫_Q f_{1/4}(· - x) + C_S (ℓ S/ℓ̃ + t ℓ̃ + |n̄ - p|)`,
`p = #X`. -/
@[expose] def Input63Statement : Prop :=
  ∀ {mLo mHi : ℝ}, 0 < mLo → mLo ≤ mHi → mHi ≤ 1 / 150 →
    ∃ CS Cscr ℓ₀ : ℝ, 1 ≤ CS ∧ 1 ≤ Cscr ∧ 1 ≤ ℓ₀ ∧
      ∀ (a₀ : ℂ) (t m ℓ ℓt : ℝ) (nb : ℕ) (X : Finset ℂ) (w : ℂ → ℝ) (g : ℂ → ℂ),
        mLo ≤ m → m ≤ mHi → (nb : ℝ) = m * t ^ 2 →
        max (4 * mHi / mLo) ℓ₀ ≤ ℓ → ℓ ≤ ℓt → ℓt ≤ t / 8 →
        (↑X : Set ℂ) ⊆ sqAt a₀ t → (∀ p ∈ X, ∀ q ∈ X, p ≠ q → 1 ≤ ‖p - q‖) →
        HasWeakGradientOn (sqAt a₀ t) (fun x => w x - ∑ p ∈ X, truncLog (1 / 4) (x - p)) g →
        (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ interior (sqShrink a₀ t (1 / 2)) →
          -(∫ x, w x * Δ φ x) =
            2 * Real.pi * ((∑ p ∈ X.filter (· ∈ sqShrink a₀ t (1 / 2)), φ p) - m * ∫ x, φ x)) →
        (∫ x in sqShrink a₀ t (ℓt / 2) \ sqShrink a₀ t (2 * ℓt), ‖g x‖ ^ 2) ≤ ℓ ^ 3 * ℓt / Cscr →
        ∃ Y : Fin nb → ℂ, Function.Injective Y ∧ (∀ i, Y i ∈ interior (sqAt a₀ t)) ∧
          neumannEnergy a₀ t m Y ≤
            (1 / 2 : ℝ) * (∫ x in sqAt a₀ t, ‖g x‖ ^ 2) + Real.pi * X.card * Real.log (1 / 4) -
              2 * Real.pi * m * ∑ p ∈ X, (∫ x in sqAt a₀ t, truncLog (1 / 4) (x - p)) +
              CS * (ℓ * (∫ x in sqShrink a₀ t (ℓt / 2) \ sqShrink a₀ t (2 * ℓt), ‖g x‖ ^ 2) / ℓt +
                t * ℓt + |(nb : ℝ) - X.card|)

/-- The conclusion of the ring upper bound (sphere note, Theorem 5.13): `min 𝔎 ≤ C_U n` for all `n ≥ 2`,
stated for every minimizer. -/
@[expose] def RingBoundStatement : Prop :=
  ∃ CU : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ Y : Fin n → R3, IsSphereMinimizer Y → normalizedEnergy Y ≤ CU * n

/-- The constant `C_tri = ½ log (4π) + W_tri / π` (sphere note, Definition 2.5). -/
@[expose] noncomputable def cTri : ℝ :=
  Real.log (4 * Real.pi) / 2 + triangularEnergy / Real.pi

end Lower

end Sphere

end SandierSerfaty

end
