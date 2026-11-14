/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 54 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1824, …, 1836` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1824 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1824 = true := by
  decide +kernel

theorem chunk_1825 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1825 = true := by
  decide +kernel

theorem chunk_1826 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1826 = true := by
  decide +kernel

theorem chunk_1827 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1827 = true := by
  decide +kernel

theorem chunk_1828 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1828 = true := by
  decide +kernel

theorem chunk_1829 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1829 = true := by
  decide +kernel

theorem chunk_1830 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1830 = true := by
  decide +kernel

theorem chunk_1831 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1831 = true := by
  decide +kernel

theorem chunk_1832 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1832 = true := by
  decide +kernel

theorem chunk_1833 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1833 = true := by
  decide +kernel

theorem chunk_1834 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1834 = true := by
  decide +kernel

theorem chunk_1835 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1835 = true := by
  decide +kernel

theorem chunk_1836 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1836 = true := by
  decide +kernel

end SandierSerfaty.CertData
