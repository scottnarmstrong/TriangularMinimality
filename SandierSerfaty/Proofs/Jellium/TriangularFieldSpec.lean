/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TriangularEnergy
public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
public import SandierSerfaty.Statements.Jellium.Defs.TriangularField
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice

/-!
# Proof of `SandierSerfaty.triangularField_spec`

`SandierSerfaty.Proofs.triangularField_spec` proves the statement `SandierSerfaty.triangularField_spec` of the
module `SandierSerfaty.Statements.Jellium.Theorems.TriangularFieldSpec`.

The first conjunct is `SandierSerfaty.triangularField_mem_elec`. The second is
`SandierSerfaty.neutralEnergy_triangularField`: with all radii equal to `¼`, the cube energy of the truncated
field `E_{¼}` is `(1/4π) ∫_{□_ℓ} ‖E_{¼}‖² + #(Λ ∩ □_ℓ) (½ log ¼ - π/32)`, and the average of the periodic
function `‖E_{¼}‖²` over large squares converges to its cell integral `J`; the puncture limit defining `W_tri`
(`SandierSerfaty.Torus.tendsto_puncture`) then gives `(1/4π) J + ½ log ¼ - π/32 = W_tri / (2π)`.
-/

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty.Proofs

/-- Proof of `SandierSerfaty.triangularField_spec`. -/
theorem triangularField_spec :
    triangularField ∈ elec (triangularLattice : Set ℂ) ∧
      neutralEnergy (triangularLattice : Set ℂ) triangularField =
        ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) :=
  ⟨triangularField_mem_elec, neutralEnergy_triangularField⟩

end SandierSerfaty.Proofs

end
