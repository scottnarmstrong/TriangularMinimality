/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 29 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `1504, …, 1511` (2 cells per declaration; estimated 48 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1504 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1504 = true := by
  decide +kernel

theorem chunk_1506 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1506 = true := by
  decide +kernel

theorem chunk_1508 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1508 = true := by
  decide +kernel

theorem chunk_1510 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 1510 = true := by
  decide +kernel

end SandierSerfaty.CertData
