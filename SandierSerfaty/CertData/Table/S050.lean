/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 50 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1772, …, 1784` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1772 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1772 = true := by
  decide +kernel

theorem chunk_1773 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1773 = true := by
  decide +kernel

theorem chunk_1774 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1774 = true := by
  decide +kernel

theorem chunk_1775 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1775 = true := by
  decide +kernel

theorem chunk_1776 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1776 = true := by
  decide +kernel

theorem chunk_1777 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1777 = true := by
  decide +kernel

theorem chunk_1778 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1778 = true := by
  decide +kernel

theorem chunk_1779 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1779 = true := by
  decide +kernel

theorem chunk_1780 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1780 = true := by
  decide +kernel

theorem chunk_1781 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1781 = true := by
  decide +kernel

theorem chunk_1782 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1782 = true := by
  decide +kernel

theorem chunk_1783 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1783 = true := by
  decide +kernel

theorem chunk_1784 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1784 = true := by
  decide +kernel

end SandierSerfaty.CertData
