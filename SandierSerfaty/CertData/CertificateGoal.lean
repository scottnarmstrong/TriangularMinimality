/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.ExteriorSigns
public import SandierSerfaty.CertData.Lam.Final
public import SandierSerfaty.CertData.Box.Final
public import SandierSerfaty.CertData.Box.Checks
public import SandierSerfaty.Certificate.Lambda.GoalIdx

/-!
# The certificate for the square-torus bound: `Assembly.CertificateGoal`, proved

**`certificateGoal : Assembly.CertificateGoal`**, the five fields of the certificate (paper §7: the
exterior signs `f(l) > 0`, `-π B(l) - λ/2 > 0`, the outer and inner assertions `K ≤ 2g` on `𝒟`, and the
negative-part assertion), from `Lambda.certificateGoal_of_checks''` with:

* the finite core `finiteCore` (A2) and the basis constants `dLit_valid`, `p2_pos` (A1);
* the table model `tbl_model` (A3: the table shards, `Assemble.tableModel_of_checks`);
* the enclosures of the constants (A4: `ExteriorSigns`), tied to the box literals by the `ivEq` checks of `Box.Checks`;
* the coarse `λ` and the exterior test A6 (`lam_ok`, `a6_ok`);
* the fine `λ` of the box layer (`lamFine_ok`, the `λ` shards `Lam.*`);
* the Boolean checks of the box layer (`Box.Final`, `Box.Checks`: the query cells, the evaluator test, the A7
  rectangles and Hessian rows with the checked index, the outer, negative-part and `K` rows, the scalar
  inequalities).

Every check is a `decide +kernel` shard; no `native_decide`, no `Lean.ofReduceBool`.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble SandierSerfaty.Certificate.Box
open SandierSerfaty.Certificate.Lambda SandierSerfaty.CertData.Box

theorem l_mem_knot : IV.Mem SandierSerfaty.Calibration.l (knotIV dLit 6) :=
  mem_knotIV dLit_valid (j := 6) le_rfl

theorem f0l_mem : IV.Mem (SandierSerfaty.Calibration.f₀ SandierSerfaty.Calibration.l) f0lLit := by
  rw [eq_of_ivEq f0l_ok]; exact f0_l_mem

theorem f0R_mem : IV.Mem (SandierSerfaty.Calibration.f₀ SandierSerfaty.Calibration.R₀) f0RLit := by
  rw [eq_of_ivEq f0R_ok]; exact f0_e_R_mem.1

theorem eR_mem : IV.Mem (SandierSerfaty.Calibration.e SandierSerfaty.Calibration.R₀) eRLit := by
  rw [eq_of_ivEq eR_ok]; exact f0_e_R_mem.2

theorem bl_mem : IV.Mem (SandierSerfaty.Calibration.B SandierSerfaty.Calibration.l) blLit := by
  rw [eq_of_ivEq bl_ok]; exact B_l_mem

theorem lsq_mem : IV.Mem (SandierSerfaty.Calibration.l ^ 2) lsqLit := by
  rw [eq_of_ivEq lsq_ok]; exact IV.mem_sq l_mem_knot

theorem l_mem : IV.Mem SandierSerfaty.Calibration.l lLit := by
  rw [eq_of_ivEq l_ok]; exact l_mem_knot

theorem qn_ok : Nat.ble qTbl.n tblN = true := by
  decide +kernel

/-- **The certificate for the square-torus bound**: the five fields of `Assembly.CertificateGoal`, proved. -/
theorem certificateGoal : SandierSerfaty.Assembly.CertificateGoal :=
  certificateGoal_of_checks'' (E := evalE) (rf := qRf) (re := qRe) (lamA := lamLit) (lamI := lamFLit)
    (piI := dLit.pi) (r0I := dLit.r0) (f0lI := f0lLit) (f0RI := f0RLit) (eRI := eRLit) (blI := blLit)
    (lsqI := lsqLit) (lI := lLit) finiteCore (FL := flTbl) tbl_model dLit_valid.mpi dLit_valid.mr0 f0l_mem f0R_mem
    eR_mem bl_mem lsq_mem l_mem dLit_valid p2_pos (N := 64) (rad := lamRad) (by norm_num) lamRad_ge
    (optEqB_sound lam_ok) l_pos_ok l_mem_knot nR_mem nL_mem a6_ok (PL := lamPar) lamRad_ge lamFine_ok
    (A := a7Dat) rfl rfl (eq_of_ivEq k0_ok) rfl rfl rfl (eq_of_ivEq mu_ok) lamRad_ge
    (H := hessDat) rfl rfl (eq_of_ivEq k0_ok) rfl rfl rfl (eq_of_ivEq mu_ok) lamRad_ge
    oGrid nGrid kGrid parLit deltaLit kcLit aIx hIx qn_ok qcells_ok eval_ok a7B_ok outer_ok neg_ok k_ok hess_ok
    kc_ok thr_ok nthr_ok delta_ok

end SandierSerfaty.CertData
