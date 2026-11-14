/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 126 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3720, …, 3749` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3720 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3720 = true := by
  decide +kernel

theorem chunk_3722 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3722 = true := by
  decide +kernel

theorem chunk_3724 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3724 = true := by
  decide +kernel

theorem chunk_3726 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3726 = true := by
  decide +kernel

theorem chunk_3728 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3728 = true := by
  decide +kernel

theorem chunk_3730 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3730 = true := by
  decide +kernel

theorem chunk_3732 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3732 = true := by
  decide +kernel

theorem chunk_3734 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3734 = true := by
  decide +kernel

theorem chunk_3736 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3736 = true := by
  decide +kernel

theorem chunk_3738 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3738 = true := by
  decide +kernel

theorem chunk_3740 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3740 = true := by
  decide +kernel

theorem chunk_3742 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3742 = true := by
  decide +kernel

theorem chunk_3744 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3744 = true := by
  decide +kernel

theorem chunk_3746 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3746 = true := by
  decide +kernel

theorem chunk_3748 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3748 = true := by
  decide +kernel

end SandierSerfaty.CertData
