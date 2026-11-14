/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 65 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1967, …, 1979` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1967 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1967 = true := by
  decide +kernel

theorem chunk_1968 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1968 = true := by
  decide +kernel

theorem chunk_1969 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1969 = true := by
  decide +kernel

theorem chunk_1970 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1970 = true := by
  decide +kernel

theorem chunk_1971 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1971 = true := by
  decide +kernel

theorem chunk_1972 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1972 = true := by
  decide +kernel

theorem chunk_1973 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1973 = true := by
  decide +kernel

theorem chunk_1974 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1974 = true := by
  decide +kernel

theorem chunk_1975 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1975 = true := by
  decide +kernel

theorem chunk_1976 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1976 = true := by
  decide +kernel

theorem chunk_1977 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1977 = true := by
  decide +kernel

theorem chunk_1978 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1978 = true := by
  decide +kernel

theorem chunk_1979 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1979 = true := by
  decide +kernel

end SandierSerfaty.CertData
