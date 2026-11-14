/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.Cube
public import SandierSerfaty.Statements.Jellium.Defs.CubeRadius
public import SandierSerfaty.Statements.Jellium.Defs.TruncField
public import SandierSerfaty.Statements.Jellium.Defs.TruncLog
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The energy of a field in a square

`cubeEnergy C E ℓ` is the energy `F^{□_ℓ}(E, 1)` of a field `E` with charges at the points of `C`, in the
square `□_ℓ` (S. Serfaty, *Lectures on Coulomb and Riesz gases*, (11.2.6), in dimension two with `s = 0` and
background `m = 1`).
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

/-- `F^{□_ℓ}(E, 1) = (1/4π) ∫_{□_ℓ} |E_r̃|² - ½ ∑_{p ∈ C ∩ □_ℓ} g(r̃_p) - ∑_{p ∈ C ∩ □_ℓ} ∫ f_{r̃_p}(x - p) dx`
(*Lectures*, (11.2.6), `c_{2,0} = 2π`, `m = 1`; points on `∂□_ℓ` counted). The field
integral is a lower Lebesgue integral, so `F = +∞` when `E_r̃ ∉ L²(□_ℓ)`. The `+∞` branch of the *Lectures*
("some `r_p = 0`") cannot occur for a locally finite set. -/
@[expose] noncomputable def cubeEnergy (C : Set ℂ) (E : ℂ → ℂ) (ℓ : ℝ) : EReal :=
  ((1 / (4 * Real.pi) : ℝ) : EReal) *
      (((∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (cubeRadius C ℓ) E x‖ ^ 2)) : ℝ≥0∞) : EReal) +
    (((-(1 / 2 : ℝ)) * (∑ᶠ p ∈ C ∩ cube ℓ, -Real.log (cubeRadius C ℓ p)) -
      (∑ᶠ p ∈ C ∩ cube ℓ, (∫ x, truncLog (cubeRadius C ℓ p) (x - p))) : ℝ) : EReal)

end SandierSerfaty

end
