/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Coeff.Encl
public import SandierSerfaty.Certificate.Basis.DataSound
public import SandierSerfaty.Certificate.Arith.Pi

/-!
# Assertion A1 assembled, and the validity of the literal basis constants

* `cosAll_encl`: the five coefficient blocks (`SandierSerfaty.CertData.Coeff.Encl`) concatenated enclose
  `coeff 1, …, coeff 38`;
* `abs_coeff_one_lt`: `|coeff 1| < 1` (`Basis.absLtOneB_sound`);
* `dLit_valid`: the literal basis constants `dLit` are valid (`Basis.BasisData.Valid`): `dataOK` checks the side
  conditions of `mkData piIV pI rI cosAll`, which is valid by `Basis.mkData_valid`, and `dataSubB` checks that
  its constants lie in those of `dLit` (`BasisData.Valid.of_subB`);
* `p2_pos`: the enclosure of `p²` is positive.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Assemble

/-- **Assertion A1**: `cosAll` encloses `c_1, …, c_38`. -/
theorem cosAll_encl : EnclFrom SandierSerfaty.Calibration.coeff 1 cosAll := by
  have h12 := enclFrom_append cosB1_encl (by rw [show 1 + cosB1.length = 2 from rfl]; exact cosB2_encl)
  have h3 := enclFrom_append h12 (by rw [show 1 + (cosB1 ++ cosB2).length = 11 from rfl]; exact cosB3_encl)
  have h4 := enclFrom_append h3 (by rw [show 1 + (cosB1 ++ cosB2 ++ cosB3).length = 20 from rfl]; exact cosB4_encl)
  exact enclFrom_append h4
    (by rw [show 1 + (cosB1 ++ cosB2 ++ cosB3 ++ cosB4).length = 29 from rfl]; exact cosB5_encl)

theorem c1_ok : absLtOneB (cosB1.headD default) = true := by
  decide +kernel

/-- `|c_1| < 1` (paper §6.3). -/
theorem abs_coeff_one_lt : |SandierSerfaty.Calibration.coeff 1| < 1 := by
  have h : EnclFrom SandierSerfaty.Calibration.coeff 1 cosB1 := cosB1_encl
  unfold cosB1 at h
  exact absLtOneB_sound c1_ok h.1

theorem dataOK_ok : dataOK pI rI cosAll = true := by
  decide +kernel

theorem dataSub_ok : dataSubB (mkData piIV pI rI cosAll) dLit = true := by
  decide +kernel

/-- The enclosure of `p²` in `dLit` is positive. -/
theorem p2_pos : IV.posB dLit.p2 = true := by
  decide +kernel

/-- **The literal basis constants are valid.** -/
theorem dLit_valid : dLit.Valid :=
  BasisData.Valid.of_subB (mkData_valid mem_piIV cosAll_encl dataOK_ok) dataSub_ok

end SandierSerfaty.CertData
