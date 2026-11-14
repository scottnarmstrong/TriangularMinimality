/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 10 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `934, …, 963` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_934 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 934 = true := by
  decide +kernel

theorem chunk_936 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 936 = true := by
  decide +kernel

theorem chunk_938 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 938 = true := by
  decide +kernel

theorem chunk_940 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 940 = true := by
  decide +kernel

theorem chunk_942 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 942 = true := by
  decide +kernel

theorem chunk_944 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 944 = true := by
  decide +kernel

theorem chunk_946 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 946 = true := by
  decide +kernel

theorem chunk_948 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 948 = true := by
  decide +kernel

theorem chunk_950 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 950 = true := by
  decide +kernel

theorem chunk_952 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 952 = true := by
  decide +kernel

theorem chunk_954 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 954 = true := by
  decide +kernel

theorem chunk_956 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 956 = true := by
  decide +kernel

theorem chunk_958 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 958 = true := by
  decide +kernel

theorem chunk_960 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 960 = true := by
  decide +kernel

theorem chunk_962 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 962 = true := by
  decide +kernel

end SandierSerfaty.CertData
