/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Coeff.Rows

/-!
# Assertion A1, block 4 (kernel shards)

`decide +kernel` shards: the rows of the box `|n|, |q| ≤ 48` for the modes from `20` (13 rows per declaration), and the final enclosure test.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem rows_b4_0 : rowsB 20 48 9 rowCk4 0 13 = true := by
  decide +kernel

theorem rows_b4_13 : rowsB 20 48 9 rowCk4 13 13 = true := by
  decide +kernel

theorem rows_b4_26 : rowsB 20 48 9 rowCk4 26 13 = true := by
  decide +kernel

theorem rows_b4_39 : rowsB 20 48 9 rowCk4 39 13 = true := by
  decide +kernel

theorem rows_b4_52 : rowsB 20 48 9 rowCk4 52 13 = true := by
  decide +kernel

theorem rows_b4_65 : rowsB 20 48 9 rowCk4 65 13 = true := by
  decide +kernel

theorem rows_b4_78 : rowsB 20 48 9 rowCk4 78 13 = true := by
  decide +kernel

theorem rows_b4_91 : rowsB 20 48 9 rowCk4 91 6 = true := by
  decide +kernel

theorem fin_b4 : coeffFinB s3lo s3hi 20 48 rowCk4 cosB4 = true := by
  decide +kernel

end SandierSerfaty.CertData
