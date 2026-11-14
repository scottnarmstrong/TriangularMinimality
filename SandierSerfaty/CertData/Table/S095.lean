/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 95 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2790, …, 2819` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2790 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2790 = true := by
  decide +kernel

theorem chunk_2792 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2792 = true := by
  decide +kernel

theorem chunk_2794 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2794 = true := by
  decide +kernel

theorem chunk_2796 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2796 = true := by
  decide +kernel

theorem chunk_2798 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2798 = true := by
  decide +kernel

theorem chunk_2800 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2800 = true := by
  decide +kernel

theorem chunk_2802 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2802 = true := by
  decide +kernel

theorem chunk_2804 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2804 = true := by
  decide +kernel

theorem chunk_2806 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2806 = true := by
  decide +kernel

theorem chunk_2808 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2808 = true := by
  decide +kernel

theorem chunk_2810 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2810 = true := by
  decide +kernel

theorem chunk_2812 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2812 = true := by
  decide +kernel

theorem chunk_2814 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2814 = true := by
  decide +kernel

theorem chunk_2816 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2816 = true := by
  decide +kernel

theorem chunk_2818 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2818 = true := by
  decide +kernel

end SandierSerfaty.CertData
