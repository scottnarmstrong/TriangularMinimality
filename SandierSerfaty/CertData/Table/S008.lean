/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 8 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `874, …, 903` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_874 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 874 = true := by
  decide +kernel

theorem chunk_876 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 876 = true := by
  decide +kernel

theorem chunk_878 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 878 = true := by
  decide +kernel

theorem chunk_880 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 880 = true := by
  decide +kernel

theorem chunk_882 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 882 = true := by
  decide +kernel

theorem chunk_884 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 884 = true := by
  decide +kernel

theorem chunk_886 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 886 = true := by
  decide +kernel

theorem chunk_888 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 888 = true := by
  decide +kernel

theorem chunk_890 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 890 = true := by
  decide +kernel

theorem chunk_892 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 892 = true := by
  decide +kernel

theorem chunk_894 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 894 = true := by
  decide +kernel

theorem chunk_896 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 896 = true := by
  decide +kernel

theorem chunk_898 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 898 = true := by
  decide +kernel

theorem chunk_900 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 900 = true := by
  decide +kernel

theorem chunk_902 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 902 = true := by
  decide +kernel

end SandierSerfaty.CertData
