/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 75 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2190, …, 2219` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2190 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2190 = true := by
  decide +kernel

theorem chunk_2192 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2192 = true := by
  decide +kernel

theorem chunk_2194 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2194 = true := by
  decide +kernel

theorem chunk_2196 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2196 = true := by
  decide +kernel

theorem chunk_2198 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2198 = true := by
  decide +kernel

theorem chunk_2200 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2200 = true := by
  decide +kernel

theorem chunk_2202 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2202 = true := by
  decide +kernel

theorem chunk_2204 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2204 = true := by
  decide +kernel

theorem chunk_2206 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2206 = true := by
  decide +kernel

theorem chunk_2208 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2208 = true := by
  decide +kernel

theorem chunk_2210 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2210 = true := by
  decide +kernel

theorem chunk_2212 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2212 = true := by
  decide +kernel

theorem chunk_2214 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2214 = true := by
  decide +kernel

theorem chunk_2216 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2216 = true := by
  decide +kernel

theorem chunk_2218 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2218 = true := by
  decide +kernel

end SandierSerfaty.CertData
