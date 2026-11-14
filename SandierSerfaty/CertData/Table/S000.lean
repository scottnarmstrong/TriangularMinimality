/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 0 (kernel)

`decide +kernel` shards of segment `0`: the chunks of the cells `0, …, 175` (8 cells per declaration; estimated 176 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_0 : innerB 8 dLit.pi nodeAt ctAt ntAt 0 = true := by
  decide +kernel

theorem chunk_8 : innerB 8 dLit.pi nodeAt ctAt ntAt 8 = true := by
  decide +kernel

theorem chunk_16 : innerB 8 dLit.pi nodeAt ctAt ntAt 16 = true := by
  decide +kernel

theorem chunk_24 : innerB 8 dLit.pi nodeAt ctAt ntAt 24 = true := by
  decide +kernel

theorem chunk_32 : innerB 8 dLit.pi nodeAt ctAt ntAt 32 = true := by
  decide +kernel

theorem chunk_40 : innerB 8 dLit.pi nodeAt ctAt ntAt 40 = true := by
  decide +kernel

theorem chunk_48 : innerB 8 dLit.pi nodeAt ctAt ntAt 48 = true := by
  decide +kernel

theorem chunk_56 : innerB 8 dLit.pi nodeAt ctAt ntAt 56 = true := by
  decide +kernel

theorem chunk_64 : innerB 8 dLit.pi nodeAt ctAt ntAt 64 = true := by
  decide +kernel

theorem chunk_72 : innerB 8 dLit.pi nodeAt ctAt ntAt 72 = true := by
  decide +kernel

theorem chunk_80 : innerB 8 dLit.pi nodeAt ctAt ntAt 80 = true := by
  decide +kernel

theorem chunk_88 : innerB 8 dLit.pi nodeAt ctAt ntAt 88 = true := by
  decide +kernel

theorem chunk_96 : innerB 8 dLit.pi nodeAt ctAt ntAt 96 = true := by
  decide +kernel

theorem chunk_104 : innerB 8 dLit.pi nodeAt ctAt ntAt 104 = true := by
  decide +kernel

theorem chunk_112 : innerB 8 dLit.pi nodeAt ctAt ntAt 112 = true := by
  decide +kernel

theorem chunk_120 : innerB 8 dLit.pi nodeAt ctAt ntAt 120 = true := by
  decide +kernel

theorem chunk_128 : innerB 8 dLit.pi nodeAt ctAt ntAt 128 = true := by
  decide +kernel

theorem chunk_136 : innerB 8 dLit.pi nodeAt ctAt ntAt 136 = true := by
  decide +kernel

theorem chunk_144 : innerB 8 dLit.pi nodeAt ctAt ntAt 144 = true := by
  decide +kernel

theorem chunk_152 : innerB 8 dLit.pi nodeAt ctAt ntAt 152 = true := by
  decide +kernel

theorem chunk_160 : innerB 8 dLit.pi nodeAt ctAt ntAt 160 = true := by
  decide +kernel

theorem chunk_168 : innerB 8 dLit.pi nodeAt ctAt ntAt 168 = true := by
  decide +kernel

end SandierSerfaty.CertData
