/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 62 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1928, …, 1940` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1928 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1928 = true := by
  decide +kernel

theorem chunk_1929 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1929 = true := by
  decide +kernel

theorem chunk_1930 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1930 = true := by
  decide +kernel

theorem chunk_1931 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1931 = true := by
  decide +kernel

theorem chunk_1932 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1932 = true := by
  decide +kernel

theorem chunk_1933 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1933 = true := by
  decide +kernel

theorem chunk_1934 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1934 = true := by
  decide +kernel

theorem chunk_1935 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1935 = true := by
  decide +kernel

theorem chunk_1936 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1936 = true := by
  decide +kernel

theorem chunk_1937 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1937 = true := by
  decide +kernel

theorem chunk_1938 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1938 = true := by
  decide +kernel

theorem chunk_1939 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1939 = true := by
  decide +kernel

theorem chunk_1940 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1940 = true := by
  decide +kernel

end SandierSerfaty.CertData
