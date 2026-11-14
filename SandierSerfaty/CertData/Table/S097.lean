/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 97 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2850, …, 2879` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2850 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2850 = true := by
  decide +kernel

theorem chunk_2852 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2852 = true := by
  decide +kernel

theorem chunk_2854 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2854 = true := by
  decide +kernel

theorem chunk_2856 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2856 = true := by
  decide +kernel

theorem chunk_2858 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2858 = true := by
  decide +kernel

theorem chunk_2860 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2860 = true := by
  decide +kernel

theorem chunk_2862 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2862 = true := by
  decide +kernel

theorem chunk_2864 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2864 = true := by
  decide +kernel

theorem chunk_2866 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2866 = true := by
  decide +kernel

theorem chunk_2868 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2868 = true := by
  decide +kernel

theorem chunk_2870 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2870 = true := by
  decide +kernel

theorem chunk_2872 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2872 = true := by
  decide +kernel

theorem chunk_2874 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2874 = true := by
  decide +kernel

theorem chunk_2876 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2876 = true := by
  decide +kernel

theorem chunk_2878 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2878 = true := by
  decide +kernel

end SandierSerfaty.CertData
