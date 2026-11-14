/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 5 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `784, …, 813` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_784 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 784 = true := by
  decide +kernel

theorem chunk_786 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 786 = true := by
  decide +kernel

theorem chunk_788 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 788 = true := by
  decide +kernel

theorem chunk_790 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 790 = true := by
  decide +kernel

theorem chunk_792 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 792 = true := by
  decide +kernel

theorem chunk_794 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 794 = true := by
  decide +kernel

theorem chunk_796 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 796 = true := by
  decide +kernel

theorem chunk_798 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 798 = true := by
  decide +kernel

theorem chunk_800 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 800 = true := by
  decide +kernel

theorem chunk_802 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 802 = true := by
  decide +kernel

theorem chunk_804 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 804 = true := by
  decide +kernel

theorem chunk_806 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 806 = true := by
  decide +kernel

theorem chunk_808 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 808 = true := by
  decide +kernel

theorem chunk_810 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 810 = true := by
  decide +kernel

theorem chunk_812 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 812 = true := by
  decide +kernel

end SandierSerfaty.CertData
