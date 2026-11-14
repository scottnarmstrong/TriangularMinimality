/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Torus potentials

`IsTorusPotential Γ a h` says that `h` is the mean-zero `Γ`-periodic solution of `-Δh = 2π(∑ᵢ δ_{a i} - 1)` on
`ℂ/Γ`, the potential of OpenAI, *Triangular minimality for planar Coulomb renormalized energy*, Theorem 1.2
and `dual:torus-potential`, written in classical form: periodic, smooth off the charges with `Δh = 2π` there,
`h + log|· - a i|` convergent at each charge, and mean zero over a fundamental domain. This is equivalent to
the distributional form of the paper. Existence and uniqueness are `existsUnique_isTorusPotential`.
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

/-- `h` is the mean-zero `Γ`-periodic solution of `-Δh = 2π(∑ᵢ δ_{a i} - 1)` on `ℂ/Γ`
(paper, Theorem 1.2 and `dual:torus-potential`), in classical form:
periodic; smooth off the charges `a i + Γ` with `Δh = 2π` there; `h + log|· - a i|` has a finite
limit at each charge; integral zero over a fundamental domain; and (a convention)
`h = 0` at the charges, where the equation does not determine it. -/
@[expose] def IsTorusPotential (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (h : ℂ → ℝ) : Prop :=
  (∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) ∧
  ContDiffOn ℝ ∞ h {x | ∀ i, x - a i ∉ Γ} ∧
  (∀ x, (∀ i, x - a i ∉ Γ) → Δ h x = 2 * Real.pi) ∧
  (∀ i, ∃ c : ℝ, Tendsto (fun x ↦ h x + Real.log ‖x - a i‖) (𝓝[≠] (a i)) (𝓝 c)) ∧
  (∫ x in torusDomain Γ, h x) = 0 ∧
  (∀ x, (∃ i, x - a i ∈ Γ) → h x = 0)

end SandierSerfaty

end
