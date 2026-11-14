/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 53 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1811, …, 1823` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1811 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1811 = true := by
  decide +kernel

theorem chunk_1812 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1812 = true := by
  decide +kernel

theorem chunk_1813 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1813 = true := by
  decide +kernel

theorem chunk_1814 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1814 = true := by
  decide +kernel

theorem chunk_1815 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1815 = true := by
  decide +kernel

theorem chunk_1816 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1816 = true := by
  decide +kernel

theorem chunk_1817 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1817 = true := by
  decide +kernel

theorem chunk_1818 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1818 = true := by
  decide +kernel

theorem chunk_1819 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1819 = true := by
  decide +kernel

theorem chunk_1820 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1820 = true := by
  decide +kernel

theorem chunk_1821 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1821 = true := by
  decide +kernel

theorem chunk_1822 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1822 = true := by
  decide +kernel

theorem chunk_1823 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1823 = true := by
  decide +kernel

end SandierSerfaty.CertData
