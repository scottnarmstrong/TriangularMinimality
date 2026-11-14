/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 102 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3000, …, 3029` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3000 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3000 = true := by
  decide +kernel

theorem chunk_3002 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3002 = true := by
  decide +kernel

theorem chunk_3004 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3004 = true := by
  decide +kernel

theorem chunk_3006 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3006 = true := by
  decide +kernel

theorem chunk_3008 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3008 = true := by
  decide +kernel

theorem chunk_3010 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3010 = true := by
  decide +kernel

theorem chunk_3012 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3012 = true := by
  decide +kernel

theorem chunk_3014 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3014 = true := by
  decide +kernel

theorem chunk_3016 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3016 = true := by
  decide +kernel

theorem chunk_3018 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3018 = true := by
  decide +kernel

theorem chunk_3020 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3020 = true := by
  decide +kernel

theorem chunk_3022 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3022 = true := by
  decide +kernel

theorem chunk_3024 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3024 = true := by
  decide +kernel

theorem chunk_3026 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3026 = true := by
  decide +kernel

theorem chunk_3028 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3028 = true := by
  decide +kernel

end SandierSerfaty.CertData
