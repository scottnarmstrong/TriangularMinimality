/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Encl
public import SandierSerfaty.CertData.Exterior.Checks
public import SandierSerfaty.Certificate.Query.ExteriorSigns
public import SandierSerfaty.Assembly.TorusBoundOfCertificate

/-!
# The exterior sign fields of `CertificateGoal`, proved

Paper `comp:tail-signs`: `f(l) > 0` and `-π B(l) - λ/2 > 0`, i.e. the fields
`f_l_pos` and `slope_pos` of `Assembly.CertificateGoal`, proved outright from the generated data and the kernel
shards through `Query.f_l_pos_slope_pos_of_certificate`:

* the finite core `finiteCore` (A2), the basis constants `dLit_valid`, `p2_pos` (A1 and the constants);
* the table realization `tbl_encl` (A3);
* the `λ` enclosure `lam_ok : lamEnc iTbl dLit 64 lamRad = some lamLit` (A5, coarse);
* the node tuples at `R₀` (node `2016`, the end of segment `2`) and at `l` (node `3848`) and the basis at `l`,
  A4 (`B_l_mem`, `f0_l_mem`, `f0_e_R_mem`);
* the test `a6_ok` (A6).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem lamRad_ge : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ (lamRad : ℝ) := by
  rw [div_le_iff₀ (by positivity)]
  norm_num [lamRad]

theorem l_pos_ok : IV.posB (knotIV dLit 6) = true := by
  decide +kernel

theorem nR_mem : IV.Mem (SandierSerfaty.Calibration.Trunc.f₀ SandierSerfaty.Calibration.R₀) (ntAt 2015).f0 ∧
    IV.Mem (SandierSerfaty.Calibration.Trunc.e SandierSerfaty.Calibration.R₀) (ntAt 2015).e0 := by
  have h := tbl_encl.2 2 (by norm_num) (by norm_num) 2015 (by simp [knotCell]) (by simp [knotCell])
  have e : aTbl (2015 + 1) = SandierSerfaty.Calibration.R₀ := realNode_K knotsUp (j := 3) (by norm_num)
  rwa [e] at h

theorem nL_mem : IV.Mem (SandierSerfaty.Calibration.Trunc.f₀ SandierSerfaty.Calibration.l) (ntAt 3847).f0 := by
  have h := tbl_encl.2 5 (by norm_num) (by norm_num) 3847 (by simp [knotCell]) (by simp [knotCell])
  have e : aTbl (3847 + 1) = SandierSerfaty.Calibration.l := realNode_K knotsUp (j := 6) (by norm_num)
  rw [e] at h
  exact h.1

/-- **A4**: `B(l)` lies in the basis enclosure on segment `5` at `l`, widened by `lamRad`. -/
theorem B_l_mem : IV.Mem (SandierSerfaty.Calibration.B SandierSerfaty.Calibration.l)
    (IV.addRad (basis dLit 5 (knotIV dLit 6)).bsum.c0 lamRad) :=
  mem_B_l dLit_valid l_pos_ok (mem_knotIV dLit_valid (j := 6) le_rfl) lamRad_ge

/-- **A4**: the exact `f₀(l)` lies in the node tuple at `l`, widened by `lamRad` (`tail:uniform-error`). -/
theorem f0_l_mem : IV.Mem (SandierSerfaty.Calibration.f₀ SandierSerfaty.Calibration.l)
    (IV.addRad (ntAt 3847).f0 lamRad) :=
  mem_f0_exact finiteCore l_mem_Icc nL_mem lamRad_ge

/-- The exact `f₀(R₀)` and `e(R₀)` in the node tuple at `R₀`, widened by `lamRad`. -/
theorem f0_e_R_mem : IV.Mem (SandierSerfaty.Calibration.f₀ SandierSerfaty.Calibration.R₀)
      (IV.addRad (ntAt 2015).f0 lamRad) ∧
    IV.Mem (SandierSerfaty.Calibration.e SandierSerfaty.Calibration.R₀) (IV.addRad (ntAt 2015).e0 lamRad) :=
  ⟨mem_f0_exact finiteCore R₀_mem_Icc nR_mem.1 lamRad_ge, mem_e_exact finiteCore R₀_mem_Icc nR_mem.2 lamRad_ge⟩

end SandierSerfaty.CertData
