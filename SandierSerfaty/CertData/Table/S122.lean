/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 122 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3600, …, 3629` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3600 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3600 = true := by
  decide +kernel

theorem chunk_3602 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3602 = true := by
  decide +kernel

theorem chunk_3604 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3604 = true := by
  decide +kernel

theorem chunk_3606 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3606 = true := by
  decide +kernel

theorem chunk_3608 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3608 = true := by
  decide +kernel

theorem chunk_3610 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3610 = true := by
  decide +kernel

theorem chunk_3612 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3612 = true := by
  decide +kernel

theorem chunk_3614 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3614 = true := by
  decide +kernel

theorem chunk_3616 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3616 = true := by
  decide +kernel

theorem chunk_3618 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3618 = true := by
  decide +kernel

theorem chunk_3620 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3620 = true := by
  decide +kernel

theorem chunk_3622 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3622 = true := by
  decide +kernel

theorem chunk_3624 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3624 = true := by
  decide +kernel

theorem chunk_3626 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3626 = true := by
  decide +kernel

theorem chunk_3628 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3628 = true := by
  decide +kernel

end SandierSerfaty.CertData
