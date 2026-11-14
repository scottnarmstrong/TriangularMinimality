/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Coeff.B1
public import SandierSerfaty.CertData.Coeff.B2
public import SandierSerfaty.CertData.Coeff.B3
public import SandierSerfaty.CertData.Coeff.B4
public import SandierSerfaty.CertData.Coeff.B5
public import SandierSerfaty.Certificate.Assemble.Coeff

/-!
# Assertion A1: the coefficient enclosures

The row shards of each block joined (`Assemble.rows_extend`) and passed to `Assemble.coeffs_of_rows`.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- Assertion A1, block 1: `cosB1` encloses `c_1, …, c_1`. -/
theorem cosB1_encl : EnclFrom SandierSerfaty.Calibration.coeff 1 cosB1 :=
  coeffs_of_rows (cnt := 1) (by norm_num) (by norm_num)
    (fun c hc => (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rowsB_sound rows_b1_0) rows_b1_8) rows_b1_16) rows_b1_24) rows_b1_32) rows_b1_40) rows_b1_48) rows_b1_56) rows_b1_64) rows_b1_72) rows_b1_80) rows_b1_88) rows_b1_96) rows_b1_104) rows_b1_112) rows_b1_120) rows_b1_128) rows_b1_136) rows_b1_144) rows_b1_152) rows_b1_160) rows_b1_168) rows_b1_176) rows_b1_184) rows_b1_192) rows_b1_200) rows_b1_208) rows_b1_216) rows_b1_224) rows_b1_232) rows_b1_240) rows_b1_248) rows_b1_256) rows_b1_264) rows_b1_272) rows_b1_280) rows_b1_288) rows_b1_296) rows_b1_304) rows_b1_312) rows_b1_320) rows_b1_328) rows_b1_336) rows_b1_344) rows_b1_352) rows_b1_360) rows_b1_368) rows_b1_376) rows_b1_384) rows_b1_392) rows_b1_400) rows_b1_408) rows_b1_416) rows_b1_424) rows_b1_432) rows_b1_440) rows_b1_448) rows_b1_456) rows_b1_464) rows_b1_472) rows_b1_480) rows_b1_488) rows_b1_496) rows_b1_504) rows_b1_512) c (Nat.zero_le c) (by omega)) fin_b1

/-- Assertion A1, block 2: `cosB2` encloses `c_2, …, c_10`. -/
theorem cosB2_encl : EnclFrom SandierSerfaty.Calibration.coeff 2 cosB2 :=
  coeffs_of_rows (cnt := 9) (by norm_num) (by norm_num)
    (fun c hc => (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rowsB_sound rows_b2_0) rows_b2_13) rows_b2_26) rows_b2_39) rows_b2_52) rows_b2_65) rows_b2_78) rows_b2_91) c (Nat.zero_le c) (by omega)) fin_b2

/-- Assertion A1, block 3: `cosB3` encloses `c_11, …, c_19`. -/
theorem cosB3_encl : EnclFrom SandierSerfaty.Calibration.coeff 11 cosB3 :=
  coeffs_of_rows (cnt := 9) (by norm_num) (by norm_num)
    (fun c hc => (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rowsB_sound rows_b3_0) rows_b3_13) rows_b3_26) rows_b3_39) rows_b3_52) rows_b3_65) rows_b3_78) rows_b3_91) c (Nat.zero_le c) (by omega)) fin_b3

/-- Assertion A1, block 4: `cosB4` encloses `c_20, …, c_28`. -/
theorem cosB4_encl : EnclFrom SandierSerfaty.Calibration.coeff 20 cosB4 :=
  coeffs_of_rows (cnt := 9) (by norm_num) (by norm_num)
    (fun c hc => (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rowsB_sound rows_b4_0) rows_b4_13) rows_b4_26) rows_b4_39) rows_b4_52) rows_b4_65) rows_b4_78) rows_b4_91) c (Nat.zero_le c) (by omega)) fin_b4

/-- Assertion A1, block 5: `cosB5` encloses `c_29, …, c_38`. -/
theorem cosB5_encl : EnclFrom SandierSerfaty.Calibration.coeff 29 cosB5 :=
  coeffs_of_rows (cnt := 10) (by norm_num) (by norm_num)
    (fun c hc => (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rows_extend (rowsB_sound rows_b5_0) rows_b5_13) rows_b5_26) rows_b5_39) rows_b5_52) rows_b5_65) rows_b5_78) rows_b5_91) c (Nat.zero_le c) (by omega)) fin_b5

end SandierSerfaty.CertData
