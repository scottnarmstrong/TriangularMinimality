/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Coeff.Rows

/-!
# Assertion A1, block 3 (kernel shards)

`decide +kernel` shards: the rows of the box `|n|, |q| ≤ 48` for the modes from `11` (13 rows per declaration), and the final enclosure test.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem rows_b3_0 : rowsB 11 48 9 rowCk3 0 13 = true := by
  decide +kernel

theorem rows_b3_13 : rowsB 11 48 9 rowCk3 13 13 = true := by
  decide +kernel

theorem rows_b3_26 : rowsB 11 48 9 rowCk3 26 13 = true := by
  decide +kernel

theorem rows_b3_39 : rowsB 11 48 9 rowCk3 39 13 = true := by
  decide +kernel

theorem rows_b3_52 : rowsB 11 48 9 rowCk3 52 13 = true := by
  decide +kernel

theorem rows_b3_65 : rowsB 11 48 9 rowCk3 65 13 = true := by
  decide +kernel

theorem rows_b3_78 : rowsB 11 48 9 rowCk3 78 13 = true := by
  decide +kernel

theorem rows_b3_91 : rowsB 11 48 9 rowCk3 91 6 = true := by
  decide +kernel

theorem fin_b3 : coeffFinB s3lo s3hi 11 48 rowCk3 cosB3 = true := by
  decide +kernel

end SandierSerfaty.CertData
