/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 39 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1629, …, 1641` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1629 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1629 = true := by
  decide +kernel

theorem chunk_1630 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1630 = true := by
  decide +kernel

theorem chunk_1631 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1631 = true := by
  decide +kernel

theorem chunk_1632 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1632 = true := by
  decide +kernel

theorem chunk_1633 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1633 = true := by
  decide +kernel

theorem chunk_1634 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1634 = true := by
  decide +kernel

theorem chunk_1635 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1635 = true := by
  decide +kernel

theorem chunk_1636 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1636 = true := by
  decide +kernel

theorem chunk_1637 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1637 = true := by
  decide +kernel

theorem chunk_1638 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1638 = true := by
  decide +kernel

theorem chunk_1639 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1639 = true := by
  decide +kernel

theorem chunk_1640 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1640 = true := by
  decide +kernel

theorem chunk_1641 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1641 = true := by
  decide +kernel

end SandierSerfaty.CertData
