/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 49 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1759, …, 1771` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1759 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1759 = true := by
  decide +kernel

theorem chunk_1760 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1760 = true := by
  decide +kernel

theorem chunk_1761 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1761 = true := by
  decide +kernel

theorem chunk_1762 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1762 = true := by
  decide +kernel

theorem chunk_1763 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1763 = true := by
  decide +kernel

theorem chunk_1764 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1764 = true := by
  decide +kernel

theorem chunk_1765 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1765 = true := by
  decide +kernel

theorem chunk_1766 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1766 = true := by
  decide +kernel

theorem chunk_1767 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1767 = true := by
  decide +kernel

theorem chunk_1768 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1768 = true := by
  decide +kernel

theorem chunk_1769 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1769 = true := by
  decide +kernel

theorem chunk_1770 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1770 = true := by
  decide +kernel

theorem chunk_1771 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1771 = true := by
  decide +kernel

end SandierSerfaty.CertData
