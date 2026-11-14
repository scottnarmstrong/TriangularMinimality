/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 1 (kernel)

`decide +kernel` shards of segment `0`: the chunks of the cells `176, …, 351` (8 cells per declaration; estimated 176 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_176 : innerB 8 dLit.pi nodeAt ctAt ntAt 176 = true := by
  decide +kernel

theorem chunk_184 : innerB 8 dLit.pi nodeAt ctAt ntAt 184 = true := by
  decide +kernel

theorem chunk_192 : innerB 8 dLit.pi nodeAt ctAt ntAt 192 = true := by
  decide +kernel

theorem chunk_200 : innerB 8 dLit.pi nodeAt ctAt ntAt 200 = true := by
  decide +kernel

theorem chunk_208 : innerB 8 dLit.pi nodeAt ctAt ntAt 208 = true := by
  decide +kernel

theorem chunk_216 : innerB 8 dLit.pi nodeAt ctAt ntAt 216 = true := by
  decide +kernel

theorem chunk_224 : innerB 8 dLit.pi nodeAt ctAt ntAt 224 = true := by
  decide +kernel

theorem chunk_232 : innerB 8 dLit.pi nodeAt ctAt ntAt 232 = true := by
  decide +kernel

theorem chunk_240 : innerB 8 dLit.pi nodeAt ctAt ntAt 240 = true := by
  decide +kernel

theorem chunk_248 : innerB 8 dLit.pi nodeAt ctAt ntAt 248 = true := by
  decide +kernel

theorem chunk_256 : innerB 8 dLit.pi nodeAt ctAt ntAt 256 = true := by
  decide +kernel

theorem chunk_264 : innerB 8 dLit.pi nodeAt ctAt ntAt 264 = true := by
  decide +kernel

theorem chunk_272 : innerB 8 dLit.pi nodeAt ctAt ntAt 272 = true := by
  decide +kernel

theorem chunk_280 : innerB 8 dLit.pi nodeAt ctAt ntAt 280 = true := by
  decide +kernel

theorem chunk_288 : innerB 8 dLit.pi nodeAt ctAt ntAt 288 = true := by
  decide +kernel

theorem chunk_296 : innerB 8 dLit.pi nodeAt ctAt ntAt 296 = true := by
  decide +kernel

theorem chunk_304 : innerB 8 dLit.pi nodeAt ctAt ntAt 304 = true := by
  decide +kernel

theorem chunk_312 : innerB 8 dLit.pi nodeAt ctAt ntAt 312 = true := by
  decide +kernel

theorem chunk_320 : innerB 8 dLit.pi nodeAt ctAt ntAt 320 = true := by
  decide +kernel

theorem chunk_328 : innerB 8 dLit.pi nodeAt ctAt ntAt 328 = true := by
  decide +kernel

theorem chunk_336 : innerB 8 dLit.pi nodeAt ctAt ntAt 336 = true := by
  decide +kernel

theorem chunk_344 : innerB 8 dLit.pi nodeAt ctAt ntAt 344 = true := by
  decide +kernel

end SandierSerfaty.CertData
