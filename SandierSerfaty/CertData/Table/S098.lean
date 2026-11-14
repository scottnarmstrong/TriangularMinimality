/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 98 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2880, …, 2909` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2880 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2880 = true := by
  decide +kernel

theorem chunk_2882 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2882 = true := by
  decide +kernel

theorem chunk_2884 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2884 = true := by
  decide +kernel

theorem chunk_2886 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2886 = true := by
  decide +kernel

theorem chunk_2888 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2888 = true := by
  decide +kernel

theorem chunk_2890 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2890 = true := by
  decide +kernel

theorem chunk_2892 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2892 = true := by
  decide +kernel

theorem chunk_2894 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2894 = true := by
  decide +kernel

theorem chunk_2896 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2896 = true := by
  decide +kernel

theorem chunk_2898 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2898 = true := by
  decide +kernel

theorem chunk_2900 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2900 = true := by
  decide +kernel

theorem chunk_2902 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2902 = true := by
  decide +kernel

theorem chunk_2904 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2904 = true := by
  decide +kernel

theorem chunk_2906 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2906 = true := by
  decide +kernel

theorem chunk_2908 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2908 = true := by
  decide +kernel

end SandierSerfaty.CertData
