/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Coeff.Rows

/-!
# Assertion A1, block 5 (kernel shards)

`decide +kernel` shards: the rows of the box `|n|, |q| ≤ 48` for the modes from `29` (13 rows per declaration), and the final enclosure test.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem rows_b5_0 : rowsB 29 48 10 rowCk5 0 13 = true := by
  decide +kernel

theorem rows_b5_13 : rowsB 29 48 10 rowCk5 13 13 = true := by
  decide +kernel

theorem rows_b5_26 : rowsB 29 48 10 rowCk5 26 13 = true := by
  decide +kernel

theorem rows_b5_39 : rowsB 29 48 10 rowCk5 39 13 = true := by
  decide +kernel

theorem rows_b5_52 : rowsB 29 48 10 rowCk5 52 13 = true := by
  decide +kernel

theorem rows_b5_65 : rowsB 29 48 10 rowCk5 65 13 = true := by
  decide +kernel

theorem rows_b5_78 : rowsB 29 48 10 rowCk5 78 13 = true := by
  decide +kernel

theorem rows_b5_91 : rowsB 29 48 10 rowCk5 91 6 = true := by
  decide +kernel

theorem fin_b5 : coeffFinB s3lo s3hi 29 48 rowCk5 cosB5 = true := by
  decide +kernel

end SandierSerfaty.CertData
