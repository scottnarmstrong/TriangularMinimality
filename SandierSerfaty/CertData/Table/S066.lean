/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 66 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1980, …, 1992` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1980 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1980 = true := by
  decide +kernel

theorem chunk_1981 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1981 = true := by
  decide +kernel

theorem chunk_1982 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1982 = true := by
  decide +kernel

theorem chunk_1983 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1983 = true := by
  decide +kernel

theorem chunk_1984 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1984 = true := by
  decide +kernel

theorem chunk_1985 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1985 = true := by
  decide +kernel

theorem chunk_1986 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1986 = true := by
  decide +kernel

theorem chunk_1987 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1987 = true := by
  decide +kernel

theorem chunk_1988 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1988 = true := by
  decide +kernel

theorem chunk_1989 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1989 = true := by
  decide +kernel

theorem chunk_1990 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1990 = true := by
  decide +kernel

theorem chunk_1991 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1991 = true := by
  decide +kernel

theorem chunk_1992 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1992 = true := by
  decide +kernel

end SandierSerfaty.CertData
