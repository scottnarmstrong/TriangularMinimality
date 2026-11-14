/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 69 (kernel)

`decide +kernel` shards of segment `3`: the chunks of the cells `2016, …, 2039` (2 cells per declaration; estimated 144 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2016 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2016 = true := by
  decide +kernel

theorem chunk_2018 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2018 = true := by
  decide +kernel

theorem chunk_2020 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2020 = true := by
  decide +kernel

theorem chunk_2022 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2022 = true := by
  decide +kernel

theorem chunk_2024 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2024 = true := by
  decide +kernel

theorem chunk_2026 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2026 = true := by
  decide +kernel

theorem chunk_2028 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2028 = true := by
  decide +kernel

theorem chunk_2030 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2030 = true := by
  decide +kernel

theorem chunk_2032 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2032 = true := by
  decide +kernel

theorem chunk_2034 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2034 = true := by
  decide +kernel

theorem chunk_2036 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2036 = true := by
  decide +kernel

theorem chunk_2038 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 3 2038 = true := by
  decide +kernel

end SandierSerfaty.CertData
