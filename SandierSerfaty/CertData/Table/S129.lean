/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 129 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3810, …, 3823` (2 cells per declaration; estimated 84 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3810 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3810 = true := by
  decide +kernel

theorem chunk_3812 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3812 = true := by
  decide +kernel

theorem chunk_3814 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3814 = true := by
  decide +kernel

theorem chunk_3816 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3816 = true := by
  decide +kernel

theorem chunk_3818 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3818 = true := by
  decide +kernel

theorem chunk_3820 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3820 = true := by
  decide +kernel

theorem chunk_3822 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3822 = true := by
  decide +kernel

end SandierSerfaty.CertData
