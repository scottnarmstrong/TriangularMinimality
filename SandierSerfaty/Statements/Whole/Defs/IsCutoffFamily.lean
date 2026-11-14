/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Cutoff families

`IsCutoffFamily χ` says that `χ` is a family of cutoffs `χ R`, `R > 1`, as in OpenAI, *Triangular minimality
for planar Coulomb renormalized energy*, `eq:cutoffs`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- A cutoff family in the sense of the paper's `eq:cutoffs`: for every
real `R > 1`, `χ R ∈ C_c^∞(ℂ)`, `0 ≤ χ R ≤ 1`, `supp (χ R) ⊆ K_R = [-R, R]²`,
`χ R = 1` on `K_{R-1} = [-(R-1), R-1]²`, and `sup_{R>1} ‖∇(χ R)‖_∞ < ∞` (Euclidean norm of the gradient on `ℂ`). -/
@[expose] def IsCutoffFamily (χ : ℝ → ℂ → ℝ) : Prop :=
  (∀ R : ℝ, 1 < R →
    ContDiff ℝ ∞ (χ R) ∧ HasCompactSupport (χ R) ∧
    (∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
    tsupport (χ R) ⊆ Set.Icc (-R) R ×ℂ Set.Icc (-R) R ∧
    (∀ x ∈ Set.Icc (-(R - 1)) (R - 1) ×ℂ Set.Icc (-(R - 1)) (R - 1), χ R x = 1)) ∧
  ∃ L : ℝ, ∀ R : ℝ, 1 < R → ∀ x : ℂ, ‖gradient (χ R) x‖ ≤ L

end SandierSerfaty

end
