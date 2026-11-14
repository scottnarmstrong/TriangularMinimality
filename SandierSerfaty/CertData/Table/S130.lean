/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 130 (kernel)

`decide +kernel` shards of segment `5`: the chunks of the cells `3824, …, 3847` (2 cells per declaration; estimated 144 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3824 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3824 = true := by
  decide +kernel

theorem chunk_3826 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3826 = true := by
  decide +kernel

theorem chunk_3828 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3828 = true := by
  decide +kernel

theorem chunk_3830 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3830 = true := by
  decide +kernel

theorem chunk_3832 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3832 = true := by
  decide +kernel

theorem chunk_3834 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3834 = true := by
  decide +kernel

theorem chunk_3836 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3836 = true := by
  decide +kernel

theorem chunk_3838 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3838 = true := by
  decide +kernel

theorem chunk_3840 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3840 = true := by
  decide +kernel

theorem chunk_3842 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3842 = true := by
  decide +kernel

theorem chunk_3844 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3844 = true := by
  decide +kernel

theorem chunk_3846 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 5 3846 = true := by
  decide +kernel

end SandierSerfaty.CertData
