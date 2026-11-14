/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 99 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2910, …, 2939` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2910 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2910 = true := by
  decide +kernel

theorem chunk_2912 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2912 = true := by
  decide +kernel

theorem chunk_2914 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2914 = true := by
  decide +kernel

theorem chunk_2916 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2916 = true := by
  decide +kernel

theorem chunk_2918 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2918 = true := by
  decide +kernel

theorem chunk_2920 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2920 = true := by
  decide +kernel

theorem chunk_2922 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2922 = true := by
  decide +kernel

theorem chunk_2924 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2924 = true := by
  decide +kernel

theorem chunk_2926 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2926 = true := by
  decide +kernel

theorem chunk_2928 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2928 = true := by
  decide +kernel

theorem chunk_2930 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2930 = true := by
  decide +kernel

theorem chunk_2932 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2932 = true := by
  decide +kernel

theorem chunk_2934 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2934 = true := by
  decide +kernel

theorem chunk_2936 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2936 = true := by
  decide +kernel

theorem chunk_2938 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2938 = true := by
  decide +kernel

end SandierSerfaty.CertData
