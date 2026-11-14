/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 121 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3570, …, 3599` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3570 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3570 = true := by
  decide +kernel

theorem chunk_3572 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3572 = true := by
  decide +kernel

theorem chunk_3574 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3574 = true := by
  decide +kernel

theorem chunk_3576 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3576 = true := by
  decide +kernel

theorem chunk_3578 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3578 = true := by
  decide +kernel

theorem chunk_3580 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3580 = true := by
  decide +kernel

theorem chunk_3582 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3582 = true := by
  decide +kernel

theorem chunk_3584 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3584 = true := by
  decide +kernel

theorem chunk_3586 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3586 = true := by
  decide +kernel

theorem chunk_3588 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3588 = true := by
  decide +kernel

theorem chunk_3590 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3590 = true := by
  decide +kernel

theorem chunk_3592 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3592 = true := by
  decide +kernel

theorem chunk_3594 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3594 = true := by
  decide +kernel

theorem chunk_3596 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3596 = true := by
  decide +kernel

theorem chunk_3598 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3598 = true := by
  decide +kernel

end SandierSerfaty.CertData
