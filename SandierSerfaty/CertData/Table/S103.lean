/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 103 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3030, …, 3059` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3030 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3030 = true := by
  decide +kernel

theorem chunk_3032 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3032 = true := by
  decide +kernel

theorem chunk_3034 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3034 = true := by
  decide +kernel

theorem chunk_3036 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3036 = true := by
  decide +kernel

theorem chunk_3038 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3038 = true := by
  decide +kernel

theorem chunk_3040 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3040 = true := by
  decide +kernel

theorem chunk_3042 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3042 = true := by
  decide +kernel

theorem chunk_3044 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3044 = true := by
  decide +kernel

theorem chunk_3046 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3046 = true := by
  decide +kernel

theorem chunk_3048 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3048 = true := by
  decide +kernel

theorem chunk_3050 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3050 = true := by
  decide +kernel

theorem chunk_3052 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3052 = true := by
  decide +kernel

theorem chunk_3054 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3054 = true := by
  decide +kernel

theorem chunk_3056 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3056 = true := by
  decide +kernel

theorem chunk_3058 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3058 = true := by
  decide +kernel

end SandierSerfaty.CertData
