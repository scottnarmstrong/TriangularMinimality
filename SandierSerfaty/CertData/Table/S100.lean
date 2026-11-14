/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 100 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2940, …, 2969` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2940 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2940 = true := by
  decide +kernel

theorem chunk_2942 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2942 = true := by
  decide +kernel

theorem chunk_2944 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2944 = true := by
  decide +kernel

theorem chunk_2946 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2946 = true := by
  decide +kernel

theorem chunk_2948 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2948 = true := by
  decide +kernel

theorem chunk_2950 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2950 = true := by
  decide +kernel

theorem chunk_2952 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2952 = true := by
  decide +kernel

theorem chunk_2954 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2954 = true := by
  decide +kernel

theorem chunk_2956 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2956 = true := by
  decide +kernel

theorem chunk_2958 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2958 = true := by
  decide +kernel

theorem chunk_2960 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2960 = true := by
  decide +kernel

theorem chunk_2962 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2962 = true := by
  decide +kernel

theorem chunk_2964 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2964 = true := by
  decide +kernel

theorem chunk_2966 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2966 = true := by
  decide +kernel

theorem chunk_2968 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2968 = true := by
  decide +kernel

end SandierSerfaty.CertData
