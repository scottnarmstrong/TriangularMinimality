/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 123 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3630, …, 3659` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3630 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3630 = true := by
  decide +kernel

theorem chunk_3632 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3632 = true := by
  decide +kernel

theorem chunk_3634 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3634 = true := by
  decide +kernel

theorem chunk_3636 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3636 = true := by
  decide +kernel

theorem chunk_3638 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3638 = true := by
  decide +kernel

theorem chunk_3640 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3640 = true := by
  decide +kernel

theorem chunk_3642 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3642 = true := by
  decide +kernel

theorem chunk_3644 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3644 = true := by
  decide +kernel

theorem chunk_3646 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3646 = true := by
  decide +kernel

theorem chunk_3648 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3648 = true := by
  decide +kernel

theorem chunk_3650 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3650 = true := by
  decide +kernel

theorem chunk_3652 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3652 = true := by
  decide +kernel

theorem chunk_3654 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3654 = true := by
  decide +kernel

theorem chunk_3656 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3656 = true := by
  decide +kernel

theorem chunk_3658 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3658 = true := by
  decide +kernel

end SandierSerfaty.CertData
