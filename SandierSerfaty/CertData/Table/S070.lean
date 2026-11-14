/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 70 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2040, …, 2069` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2040 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2040 = true := by
  decide +kernel

theorem chunk_2042 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2042 = true := by
  decide +kernel

theorem chunk_2044 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2044 = true := by
  decide +kernel

theorem chunk_2046 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2046 = true := by
  decide +kernel

theorem chunk_2048 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2048 = true := by
  decide +kernel

theorem chunk_2050 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2050 = true := by
  decide +kernel

theorem chunk_2052 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2052 = true := by
  decide +kernel

theorem chunk_2054 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2054 = true := by
  decide +kernel

theorem chunk_2056 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2056 = true := by
  decide +kernel

theorem chunk_2058 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2058 = true := by
  decide +kernel

theorem chunk_2060 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2060 = true := by
  decide +kernel

theorem chunk_2062 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2062 = true := by
  decide +kernel

theorem chunk_2064 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2064 = true := by
  decide +kernel

theorem chunk_2066 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2066 = true := by
  decide +kernel

theorem chunk_2068 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2068 = true := by
  decide +kernel

end SandierSerfaty.CertData
