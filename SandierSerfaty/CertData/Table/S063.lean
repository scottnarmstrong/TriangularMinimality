/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 63 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1941, …, 1953` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1941 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1941 = true := by
  decide +kernel

theorem chunk_1942 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1942 = true := by
  decide +kernel

theorem chunk_1943 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1943 = true := by
  decide +kernel

theorem chunk_1944 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1944 = true := by
  decide +kernel

theorem chunk_1945 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1945 = true := by
  decide +kernel

theorem chunk_1946 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1946 = true := by
  decide +kernel

theorem chunk_1947 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1947 = true := by
  decide +kernel

theorem chunk_1948 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1948 = true := by
  decide +kernel

theorem chunk_1949 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1949 = true := by
  decide +kernel

theorem chunk_1950 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1950 = true := by
  decide +kernel

theorem chunk_1951 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1951 = true := by
  decide +kernel

theorem chunk_1952 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1952 = true := by
  decide +kernel

theorem chunk_1953 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1953 = true := by
  decide +kernel

end SandierSerfaty.CertData
