/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 60 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1902, …, 1914` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1902 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1902 = true := by
  decide +kernel

theorem chunk_1903 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1903 = true := by
  decide +kernel

theorem chunk_1904 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1904 = true := by
  decide +kernel

theorem chunk_1905 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1905 = true := by
  decide +kernel

theorem chunk_1906 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1906 = true := by
  decide +kernel

theorem chunk_1907 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1907 = true := by
  decide +kernel

theorem chunk_1908 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1908 = true := by
  decide +kernel

theorem chunk_1909 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1909 = true := by
  decide +kernel

theorem chunk_1910 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1910 = true := by
  decide +kernel

theorem chunk_1911 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1911 = true := by
  decide +kernel

theorem chunk_1912 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1912 = true := by
  decide +kernel

theorem chunk_1913 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1913 = true := by
  decide +kernel

theorem chunk_1914 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1914 = true := by
  decide +kernel

end SandierSerfaty.CertData
