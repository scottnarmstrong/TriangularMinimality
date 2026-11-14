/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 2 (kernel)

`decide +kernel` shards of segment `0`: the chunks of the cells `352, …, 527` (8 cells per declaration; estimated 176 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_352 : innerB 8 dLit.pi nodeAt ctAt ntAt 352 = true := by
  decide +kernel

theorem chunk_360 : innerB 8 dLit.pi nodeAt ctAt ntAt 360 = true := by
  decide +kernel

theorem chunk_368 : innerB 8 dLit.pi nodeAt ctAt ntAt 368 = true := by
  decide +kernel

theorem chunk_376 : innerB 8 dLit.pi nodeAt ctAt ntAt 376 = true := by
  decide +kernel

theorem chunk_384 : innerB 8 dLit.pi nodeAt ctAt ntAt 384 = true := by
  decide +kernel

theorem chunk_392 : innerB 8 dLit.pi nodeAt ctAt ntAt 392 = true := by
  decide +kernel

theorem chunk_400 : innerB 8 dLit.pi nodeAt ctAt ntAt 400 = true := by
  decide +kernel

theorem chunk_408 : innerB 8 dLit.pi nodeAt ctAt ntAt 408 = true := by
  decide +kernel

theorem chunk_416 : innerB 8 dLit.pi nodeAt ctAt ntAt 416 = true := by
  decide +kernel

theorem chunk_424 : innerB 8 dLit.pi nodeAt ctAt ntAt 424 = true := by
  decide +kernel

theorem chunk_432 : innerB 8 dLit.pi nodeAt ctAt ntAt 432 = true := by
  decide +kernel

theorem chunk_440 : innerB 8 dLit.pi nodeAt ctAt ntAt 440 = true := by
  decide +kernel

theorem chunk_448 : innerB 8 dLit.pi nodeAt ctAt ntAt 448 = true := by
  decide +kernel

theorem chunk_456 : innerB 8 dLit.pi nodeAt ctAt ntAt 456 = true := by
  decide +kernel

theorem chunk_464 : innerB 8 dLit.pi nodeAt ctAt ntAt 464 = true := by
  decide +kernel

theorem chunk_472 : innerB 8 dLit.pi nodeAt ctAt ntAt 472 = true := by
  decide +kernel

theorem chunk_480 : innerB 8 dLit.pi nodeAt ctAt ntAt 480 = true := by
  decide +kernel

theorem chunk_488 : innerB 8 dLit.pi nodeAt ctAt ntAt 488 = true := by
  decide +kernel

theorem chunk_496 : innerB 8 dLit.pi nodeAt ctAt ntAt 496 = true := by
  decide +kernel

theorem chunk_504 : innerB 8 dLit.pi nodeAt ctAt ntAt 504 = true := by
  decide +kernel

theorem chunk_512 : innerB 8 dLit.pi nodeAt ctAt ntAt 512 = true := by
  decide +kernel

theorem chunk_520 : innerB 8 dLit.pi nodeAt ctAt ntAt 520 = true := by
  decide +kernel

end SandierSerfaty.CertData
