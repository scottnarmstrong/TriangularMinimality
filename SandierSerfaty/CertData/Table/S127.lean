/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 127 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3750, …, 3779` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3750 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3750 = true := by
  decide +kernel

theorem chunk_3752 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3752 = true := by
  decide +kernel

theorem chunk_3754 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3754 = true := by
  decide +kernel

theorem chunk_3756 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3756 = true := by
  decide +kernel

theorem chunk_3758 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3758 = true := by
  decide +kernel

theorem chunk_3760 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3760 = true := by
  decide +kernel

theorem chunk_3762 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3762 = true := by
  decide +kernel

theorem chunk_3764 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3764 = true := by
  decide +kernel

theorem chunk_3766 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3766 = true := by
  decide +kernel

theorem chunk_3768 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3768 = true := by
  decide +kernel

theorem chunk_3770 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3770 = true := by
  decide +kernel

theorem chunk_3772 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3772 = true := by
  decide +kernel

theorem chunk_3774 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3774 = true := by
  decide +kernel

theorem chunk_3776 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3776 = true := by
  decide +kernel

theorem chunk_3778 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3778 = true := by
  decide +kernel

end SandierSerfaty.CertData
