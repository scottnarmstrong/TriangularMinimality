/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 11 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `964, …, 993` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_964 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 964 = true := by
  decide +kernel

theorem chunk_966 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 966 = true := by
  decide +kernel

theorem chunk_968 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 968 = true := by
  decide +kernel

theorem chunk_970 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 970 = true := by
  decide +kernel

theorem chunk_972 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 972 = true := by
  decide +kernel

theorem chunk_974 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 974 = true := by
  decide +kernel

theorem chunk_976 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 976 = true := by
  decide +kernel

theorem chunk_978 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 978 = true := by
  decide +kernel

theorem chunk_980 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 980 = true := by
  decide +kernel

theorem chunk_982 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 982 = true := by
  decide +kernel

theorem chunk_984 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 984 = true := by
  decide +kernel

theorem chunk_986 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 986 = true := by
  decide +kernel

theorem chunk_988 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 988 = true := by
  decide +kernel

theorem chunk_990 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 990 = true := by
  decide +kernel

theorem chunk_992 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 992 = true := by
  decide +kernel

end SandierSerfaty.CertData
