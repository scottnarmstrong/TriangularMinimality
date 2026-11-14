/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 89 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2610, …, 2639` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2610 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2610 = true := by
  decide +kernel

theorem chunk_2612 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2612 = true := by
  decide +kernel

theorem chunk_2614 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2614 = true := by
  decide +kernel

theorem chunk_2616 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2616 = true := by
  decide +kernel

theorem chunk_2618 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2618 = true := by
  decide +kernel

theorem chunk_2620 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2620 = true := by
  decide +kernel

theorem chunk_2622 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2622 = true := by
  decide +kernel

theorem chunk_2624 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2624 = true := by
  decide +kernel

theorem chunk_2626 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2626 = true := by
  decide +kernel

theorem chunk_2628 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2628 = true := by
  decide +kernel

theorem chunk_2630 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2630 = true := by
  decide +kernel

theorem chunk_2632 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2632 = true := by
  decide +kernel

theorem chunk_2634 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2634 = true := by
  decide +kernel

theorem chunk_2636 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2636 = true := by
  decide +kernel

theorem chunk_2638 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2638 = true := by
  decide +kernel

end SandierSerfaty.CertData
