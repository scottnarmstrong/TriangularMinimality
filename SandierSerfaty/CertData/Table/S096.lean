/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 96 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2820, …, 2849` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2820 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2820 = true := by
  decide +kernel

theorem chunk_2822 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2822 = true := by
  decide +kernel

theorem chunk_2824 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2824 = true := by
  decide +kernel

theorem chunk_2826 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2826 = true := by
  decide +kernel

theorem chunk_2828 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2828 = true := by
  decide +kernel

theorem chunk_2830 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2830 = true := by
  decide +kernel

theorem chunk_2832 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2832 = true := by
  decide +kernel

theorem chunk_2834 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2834 = true := by
  decide +kernel

theorem chunk_2836 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2836 = true := by
  decide +kernel

theorem chunk_2838 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2838 = true := by
  decide +kernel

theorem chunk_2840 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2840 = true := by
  decide +kernel

theorem chunk_2842 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2842 = true := by
  decide +kernel

theorem chunk_2844 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2844 = true := by
  decide +kernel

theorem chunk_2846 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2846 = true := by
  decide +kernel

theorem chunk_2848 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2848 = true := by
  decide +kernel

end SandierSerfaty.CertData
