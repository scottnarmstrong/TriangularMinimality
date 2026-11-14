/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 128 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3780, …, 3809` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3780 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3780 = true := by
  decide +kernel

theorem chunk_3782 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3782 = true := by
  decide +kernel

theorem chunk_3784 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3784 = true := by
  decide +kernel

theorem chunk_3786 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3786 = true := by
  decide +kernel

theorem chunk_3788 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3788 = true := by
  decide +kernel

theorem chunk_3790 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3790 = true := by
  decide +kernel

theorem chunk_3792 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3792 = true := by
  decide +kernel

theorem chunk_3794 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3794 = true := by
  decide +kernel

theorem chunk_3796 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3796 = true := by
  decide +kernel

theorem chunk_3798 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3798 = true := by
  decide +kernel

theorem chunk_3800 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3800 = true := by
  decide +kernel

theorem chunk_3802 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3802 = true := by
  decide +kernel

theorem chunk_3804 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3804 = true := by
  decide +kernel

theorem chunk_3806 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3806 = true := by
  decide +kernel

theorem chunk_3808 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3808 = true := by
  decide +kernel

end SandierSerfaty.CertData
