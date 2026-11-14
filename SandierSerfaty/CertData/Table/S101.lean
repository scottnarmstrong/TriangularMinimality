/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 101 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2970, …, 2999` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2970 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2970 = true := by
  decide +kernel

theorem chunk_2972 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2972 = true := by
  decide +kernel

theorem chunk_2974 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2974 = true := by
  decide +kernel

theorem chunk_2976 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2976 = true := by
  decide +kernel

theorem chunk_2978 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2978 = true := by
  decide +kernel

theorem chunk_2980 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2980 = true := by
  decide +kernel

theorem chunk_2982 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2982 = true := by
  decide +kernel

theorem chunk_2984 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2984 = true := by
  decide +kernel

theorem chunk_2986 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2986 = true := by
  decide +kernel

theorem chunk_2988 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2988 = true := by
  decide +kernel

theorem chunk_2990 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2990 = true := by
  decide +kernel

theorem chunk_2992 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2992 = true := by
  decide +kernel

theorem chunk_2994 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2994 = true := by
  decide +kernel

theorem chunk_2996 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2996 = true := by
  decide +kernel

theorem chunk_2998 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2998 = true := by
  decide +kernel

end SandierSerfaty.CertData
