/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 124 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3660, …, 3689` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3660 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3660 = true := by
  decide +kernel

theorem chunk_3662 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3662 = true := by
  decide +kernel

theorem chunk_3664 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3664 = true := by
  decide +kernel

theorem chunk_3666 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3666 = true := by
  decide +kernel

theorem chunk_3668 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3668 = true := by
  decide +kernel

theorem chunk_3670 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3670 = true := by
  decide +kernel

theorem chunk_3672 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3672 = true := by
  decide +kernel

theorem chunk_3674 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3674 = true := by
  decide +kernel

theorem chunk_3676 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3676 = true := by
  decide +kernel

theorem chunk_3678 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3678 = true := by
  decide +kernel

theorem chunk_3680 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3680 = true := by
  decide +kernel

theorem chunk_3682 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3682 = true := by
  decide +kernel

theorem chunk_3684 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3684 = true := by
  decide +kernel

theorem chunk_3686 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3686 = true := by
  decide +kernel

theorem chunk_3688 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3688 = true := by
  decide +kernel

end SandierSerfaty.CertData
