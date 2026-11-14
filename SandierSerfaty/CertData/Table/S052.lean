/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 52 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1798, …, 1810` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1798 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1798 = true := by
  decide +kernel

theorem chunk_1799 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1799 = true := by
  decide +kernel

theorem chunk_1800 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1800 = true := by
  decide +kernel

theorem chunk_1801 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1801 = true := by
  decide +kernel

theorem chunk_1802 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1802 = true := by
  decide +kernel

theorem chunk_1803 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1803 = true := by
  decide +kernel

theorem chunk_1804 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1804 = true := by
  decide +kernel

theorem chunk_1805 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1805 = true := by
  decide +kernel

theorem chunk_1806 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1806 = true := by
  decide +kernel

theorem chunk_1807 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1807 = true := by
  decide +kernel

theorem chunk_1808 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1808 = true := by
  decide +kernel

theorem chunk_1809 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1809 = true := by
  decide +kernel

theorem chunk_1810 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1810 = true := by
  decide +kernel

end SandierSerfaty.CertData
