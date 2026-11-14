/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 51 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1785, …, 1797` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1785 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1785 = true := by
  decide +kernel

theorem chunk_1786 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1786 = true := by
  decide +kernel

theorem chunk_1787 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1787 = true := by
  decide +kernel

theorem chunk_1788 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1788 = true := by
  decide +kernel

theorem chunk_1789 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1789 = true := by
  decide +kernel

theorem chunk_1790 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1790 = true := by
  decide +kernel

theorem chunk_1791 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1791 = true := by
  decide +kernel

theorem chunk_1792 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1792 = true := by
  decide +kernel

theorem chunk_1793 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1793 = true := by
  decide +kernel

theorem chunk_1794 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1794 = true := by
  decide +kernel

theorem chunk_1795 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1795 = true := by
  decide +kernel

theorem chunk_1796 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1796 = true := by
  decide +kernel

theorem chunk_1797 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1797 = true := by
  decide +kernel

end SandierSerfaty.CertData
