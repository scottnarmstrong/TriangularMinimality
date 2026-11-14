/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 64 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1954, …, 1966` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1954 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1954 = true := by
  decide +kernel

theorem chunk_1955 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1955 = true := by
  decide +kernel

theorem chunk_1956 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1956 = true := by
  decide +kernel

theorem chunk_1957 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1957 = true := by
  decide +kernel

theorem chunk_1958 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1958 = true := by
  decide +kernel

theorem chunk_1959 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1959 = true := by
  decide +kernel

theorem chunk_1960 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1960 = true := by
  decide +kernel

theorem chunk_1961 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1961 = true := by
  decide +kernel

theorem chunk_1962 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1962 = true := by
  decide +kernel

theorem chunk_1963 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1963 = true := by
  decide +kernel

theorem chunk_1964 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1964 = true := by
  decide +kernel

theorem chunk_1965 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1965 = true := by
  decide +kernel

theorem chunk_1966 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1966 = true := by
  decide +kernel

end SandierSerfaty.CertData
