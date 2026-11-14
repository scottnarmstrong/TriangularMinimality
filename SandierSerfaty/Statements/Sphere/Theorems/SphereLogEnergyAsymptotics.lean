/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
-- PREFIX_BEGIN
module

public import SandierSerfaty.Statements.Sphere.Defs.BhsConstant
public import SandierSerfaty.Statements.Sphere.Defs.SphereLogEnergy
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
import SandierSerfaty.Proofs.Sphere.SphereLogEnergyAsymptotics

/-!
# The logarithmic energy on the sphere

`sphereLogEnergy_asymptotics` is OpenAI, *Triangular minimality for planar Coulomb renormalized energy*,
Corollary 1.3 (`cor:bhs`): `E_log(n) = (½ - log 2) n² - (n/2) log n + C_BHS n + o(n)` as `n → ∞`. It is the
case `d = 2` of the logarithmic-energy conjecture of Brauchart, Hardin and Saff. The statement gives a
remainder `r = o(n)` with an exact identity for every `n ≥ 2`, so in particular the energies are finite.

The proof is `SandierSerfaty.Proofs.sphereLogEnergy_asymptotics`, in the module
`SandierSerfaty.Proofs.Sphere.SphereLogEnergyAsymptotics`.
-/

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

@[expose] public section

namespace SandierSerfaty

/-- **Paper Corollary 1.3** (`cor:bhs`):
`E_log(n) = (½ - log 2) n² - (n/2) log n + C_BHS n + o(n)` as `n → ∞`; the energies are finite
(real) for `n ≥ 2`, and the remainder `r` is `o(n)`. -/
theorem sphereLogEnergy_asymptotics :
    ∃ r : ℕ → ℝ, (r =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 2 ≤ n →
      sphereLogEnergy n =
        ((((1 / 2 : ℝ) - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + bhsConstant * n + r n : ℝ) :
          EReal) :=
  -- PROOF_BEGIN
  by exact SandierSerfaty.Proofs.sphereLogEnergy_asymptotics
  -- PROOF_END
-- SUFFIX_BEGIN

end SandierSerfaty

end
-- SUFFIX_END
