/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 73 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2130, …, 2159` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2130 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2130 = true := by
  decide +kernel

theorem chunk_2132 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2132 = true := by
  decide +kernel

theorem chunk_2134 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2134 = true := by
  decide +kernel

theorem chunk_2136 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2136 = true := by
  decide +kernel

theorem chunk_2138 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2138 = true := by
  decide +kernel

theorem chunk_2140 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2140 = true := by
  decide +kernel

theorem chunk_2142 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2142 = true := by
  decide +kernel

theorem chunk_2144 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2144 = true := by
  decide +kernel

theorem chunk_2146 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2146 = true := by
  decide +kernel

theorem chunk_2148 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2148 = true := by
  decide +kernel

theorem chunk_2150 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2150 = true := by
  decide +kernel

theorem chunk_2152 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2152 = true := by
  decide +kernel

theorem chunk_2154 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2154 = true := by
  decide +kernel

theorem chunk_2156 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2156 = true := by
  decide +kernel

theorem chunk_2158 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2158 = true := by
  decide +kernel

end SandierSerfaty.CertData
