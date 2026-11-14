/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.ClosedForm.RobinTri
public import SandierSerfaty.ClosedForm.Discriminant
public import SandierSerfaty.Torus.PairEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy

/-!
# The closed form of `W_tri`

`SandierSerfaty.ClosedForm.triangularEnergy_eq`:

`W_tri = π log (2 √2 π / (√3 Γ(1/3)³)) = -4.1504128076789…`

(closed-form note, target theorem and assembly §6). The chain is

* `torusEnergy_one`: the puncture energy of one charge on a lattice of covolume `1` is `π R_Γ`
  (`SandierSerfaty/Torus/PairEnergy.lean`);
* `torusRobin_triangularLattice`: `R_△ = -log (2π) + log a - (1/12) log ‖Δ(ρ)‖` (`RobinTri.lean`);
* `norm_discriminant_rhoH`: `‖Δ(ρ)‖ = 3³ Γ(1/3)³⁶ / (2²⁴ π²⁴)` (`Discriminant.lean`, the closed-form note's Theorem C).

The last step is real-logarithm algebra, `a = √(2/√3)`.
-/

open Real

public section

namespace SandierSerfaty

namespace ClosedForm

/-- The Robin constant of the triangular lattice in closed form:
`R_△ = log (2 √2 π / (√3 Γ(1/3)³))`. -/
theorem torusRobin_triangularLattice_eq :
    torusRobin triangularLattice =
      Real.log (2 * √2 * Real.pi / (√3 * Real.Gamma (1 / 3) ^ 3)) := by
  rw [torusRobin_triangularLattice, norm_discriminant_rhoH]
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hs2 : 0 < √2 := Real.sqrt_pos.2 h2
  have hs3 : 0 < √3 := Real.sqrt_pos.2 h3
  have hl2 : Real.log √2 = Real.log 2 / 2 := by
    rw [Real.log_sqrt h2.le]
  have hl3 : Real.log √3 = Real.log 3 / 2 := by
    rw [Real.log_sqrt h3.le]
  have hla : Real.log Calibration.a = (Real.log 2 - Real.log 3 / 2) / 2 := by
    unfold Calibration.a
    rw [Real.log_sqrt (by positivity), Real.log_div h2.ne' hs3.ne', hl3]
  have h27 : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hnum : Real.log ((3 : ℝ) ^ 3 * Real.Gamma (1 / 3) ^ 36 / (2 ^ 24 * Real.pi ^ 24)) =
      3 * Real.log 3 + 36 * Real.log (Real.Gamma (1 / 3)) - 24 * Real.log 2 -
        24 * Real.log Real.pi := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hrhs : Real.log (2 * √2 * Real.pi / (√3 * Real.Gamma (1 / 3) ^ 3)) =
      Real.log 2 + Real.log 2 / 2 + Real.log Real.pi - Real.log 3 / 2 -
        3 * Real.log (Real.Gamma (1 / 3)) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, hl2, hl3]
    push_cast
    ring
  rw [hnum, hrhs, hla, Real.log_mul (by norm_num) hpi.ne']
  ring

/-- **The closed form of `W_tri`.** -/
theorem triangularEnergy_eq :
    triangularEnergy =
      Real.pi * Real.log (2 * √2 * Real.pi / (√3 * Real.Gamma (1 / 3) ^ 3)) := by
  unfold triangularEnergy
  rw [torusEnergy_one Torus.covolume_triangularLattice, torusRobin_triangularLattice_eq]

end ClosedForm

end SandierSerfaty

end
