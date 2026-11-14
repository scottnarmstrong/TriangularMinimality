/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 61 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1915, …, 1927` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1915 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1915 = true := by
  decide +kernel

theorem chunk_1916 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1916 = true := by
  decide +kernel

theorem chunk_1917 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1917 = true := by
  decide +kernel

theorem chunk_1918 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1918 = true := by
  decide +kernel

theorem chunk_1919 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1919 = true := by
  decide +kernel

theorem chunk_1920 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1920 = true := by
  decide +kernel

theorem chunk_1921 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1921 = true := by
  decide +kernel

theorem chunk_1922 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1922 = true := by
  decide +kernel

theorem chunk_1923 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1923 = true := by
  decide +kernel

theorem chunk_1924 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1924 = true := by
  decide +kernel

theorem chunk_1925 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1925 = true := by
  decide +kernel

theorem chunk_1926 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1926 = true := by
  decide +kernel

theorem chunk_1927 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1927 = true := by
  decide +kernel

end SandierSerfaty.CertData
