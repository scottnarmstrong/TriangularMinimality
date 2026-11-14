/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 125 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `3690, …, 3719` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_3690 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3690 = true := by
  decide +kernel

theorem chunk_3692 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3692 = true := by
  decide +kernel

theorem chunk_3694 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3694 = true := by
  decide +kernel

theorem chunk_3696 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3696 = true := by
  decide +kernel

theorem chunk_3698 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3698 = true := by
  decide +kernel

theorem chunk_3700 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3700 = true := by
  decide +kernel

theorem chunk_3702 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3702 = true := by
  decide +kernel

theorem chunk_3704 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3704 = true := by
  decide +kernel

theorem chunk_3706 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3706 = true := by
  decide +kernel

theorem chunk_3708 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3708 = true := by
  decide +kernel

theorem chunk_3710 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3710 = true := by
  decide +kernel

theorem chunk_3712 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3712 = true := by
  decide +kernel

theorem chunk_3714 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3714 = true := by
  decide +kernel

theorem chunk_3716 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3716 = true := by
  decide +kernel

theorem chunk_3718 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 3718 = true := by
  decide +kernel

end SandierSerfaty.CertData
