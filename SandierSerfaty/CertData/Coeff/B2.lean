/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Coeff.Rows

/-!
# Assertion A1, block 2 (kernel shards)

`decide +kernel` shards: the rows of the box `|n|, |q| ≤ 48` for the modes from `2` (13 rows per declaration), and the final enclosure test.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem rows_b2_0 : rowsB 2 48 9 rowCk2 0 13 = true := by
  decide +kernel

theorem rows_b2_13 : rowsB 2 48 9 rowCk2 13 13 = true := by
  decide +kernel

theorem rows_b2_26 : rowsB 2 48 9 rowCk2 26 13 = true := by
  decide +kernel

theorem rows_b2_39 : rowsB 2 48 9 rowCk2 39 13 = true := by
  decide +kernel

theorem rows_b2_52 : rowsB 2 48 9 rowCk2 52 13 = true := by
  decide +kernel

theorem rows_b2_65 : rowsB 2 48 9 rowCk2 65 13 = true := by
  decide +kernel

theorem rows_b2_78 : rowsB 2 48 9 rowCk2 78 13 = true := by
  decide +kernel

theorem rows_b2_91 : rowsB 2 48 9 rowCk2 91 6 = true := by
  decide +kernel

theorem fin_b2 : coeffFinB s3lo s3hi 2 48 rowCk2 cosB2 = true := by
  decide +kernel

end SandierSerfaty.CertData
