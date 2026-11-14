/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split
public import SandierSerfaty.Certificate.Box.NumScalar
public import SandierSerfaty.CertData.Exterior.Data

/-!
# The non-row conjuncts and the scalar checks of the box (kernel)

The enclosure literals against their definitions (`ivEq`), the conjuncts of `outerGridB`, `negGridB`, `kRowB`,
`a7B`, `hessB` other than the rows (`outerPre`, …), the evaluator test and the scalar checks.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem f0l_ok : ivEq f0lLit (IV.addRad (ntAt 3847).f0 lamRad) = true := by
  decide +kernel

theorem f0R_ok : ivEq f0RLit (IV.addRad (ntAt 2015).f0 lamRad) = true := by
  decide +kernel

theorem eR_ok : ivEq eRLit (IV.addRad (ntAt 2015).e0 lamRad) = true := by
  decide +kernel

theorem bl_ok : ivEq blLit (IV.addRad (basis dLit 5 (knotIV dLit 6)).bsum.c0 lamRad) = true := by
  decide +kernel

theorem lsq_ok : ivEq lsqLit (IV.sq (knotIV dLit 6)) = true := by
  decide +kernel

theorem l_ok : ivEq lLit (knotIV dLit 6) = true := by
  decide +kernel

theorem k0_ok : ivEq k0Lit (IV.neg (IV.mul dLit.pi blLit)) = true := by
  decide +kernel

theorem mu_ok : ivEq muLit (muEnc dLit.r0 f0RLit eRLit lamBox) = true := by
  decide +kernel

theorem outer_pre : outerPre a7Dat oGrid parLit = true := by
  decide +kernel

theorem neg_pre : negPre a7Dat nGrid parLit = true := by
  decide +kernel

theorem k_pre : kPre kGrid parLit = true := by
  decide +kernel

theorem a7_pre : a7Pre a7Dat = true := by
  decide +kernel

theorem hess_pre : hessPre hessDat = true := by
  decide +kernel

theorem eval_ok : evalCheckOf evalE lamBox dLit.pi dLit.r0 f0lLit f0RLit eRLit blLit lsqLit qRf qRe = true := by
  decide +kernel

theorem kc_ok : kcB a7Dat.L1 a7Dat.L2 a7Dat.L3 a7Dat.L4 kGrid.thr.toInt (kGrid.sm kGrid.nx) parLit.kSh parLit.kRd parLit.kRx deltaLit kcLit = true := by
  decide +kernel

theorem thr_ok : outThrB a7Dat.L1 a7Dat.L2 a7Dat.L3 a7Dat.L4 oGrid.thr.toInt (oGrid.sm oGrid.nx) parLit.oSh parLit.oDh parLit.oRho deltaLit kcLit = true := by
  decide +kernel

theorem nthr_ok : negThrB a7Dat.L1 a7Dat.L2 nGrid.thr.toInt (nGrid.sm nGrid.nx) parLit.nSh parLit.nDh deltaLit kcLit = true := by
  decide +kernel

theorem delta_ok : deltaB qRf qRe lamBox dLit.pi dLit.r0 f0lLit f0RLit eRLit blLit lsqLit deltaLit = true := by
  decide +kernel

end SandierSerfaty.CertData.Box
