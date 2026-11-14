/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 3 (kernel)

`decide +kernel` shards of segment `0`: the chunks of the cells `528, …, 703` (8 cells per declaration; estimated 176 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_528 : innerB 8 dLit.pi nodeAt ctAt ntAt 528 = true := by
  decide +kernel

theorem chunk_536 : innerB 8 dLit.pi nodeAt ctAt ntAt 536 = true := by
  decide +kernel

theorem chunk_544 : innerB 8 dLit.pi nodeAt ctAt ntAt 544 = true := by
  decide +kernel

theorem chunk_552 : innerB 8 dLit.pi nodeAt ctAt ntAt 552 = true := by
  decide +kernel

theorem chunk_560 : innerB 8 dLit.pi nodeAt ctAt ntAt 560 = true := by
  decide +kernel

theorem chunk_568 : innerB 8 dLit.pi nodeAt ctAt ntAt 568 = true := by
  decide +kernel

theorem chunk_576 : innerB 8 dLit.pi nodeAt ctAt ntAt 576 = true := by
  decide +kernel

theorem chunk_584 : innerB 8 dLit.pi nodeAt ctAt ntAt 584 = true := by
  decide +kernel

theorem chunk_592 : innerB 8 dLit.pi nodeAt ctAt ntAt 592 = true := by
  decide +kernel

theorem chunk_600 : innerB 8 dLit.pi nodeAt ctAt ntAt 600 = true := by
  decide +kernel

theorem chunk_608 : innerB 8 dLit.pi nodeAt ctAt ntAt 608 = true := by
  decide +kernel

theorem chunk_616 : innerB 8 dLit.pi nodeAt ctAt ntAt 616 = true := by
  decide +kernel

theorem chunk_624 : innerB 8 dLit.pi nodeAt ctAt ntAt 624 = true := by
  decide +kernel

theorem chunk_632 : innerB 8 dLit.pi nodeAt ctAt ntAt 632 = true := by
  decide +kernel

theorem chunk_640 : innerB 8 dLit.pi nodeAt ctAt ntAt 640 = true := by
  decide +kernel

theorem chunk_648 : innerB 8 dLit.pi nodeAt ctAt ntAt 648 = true := by
  decide +kernel

theorem chunk_656 : innerB 8 dLit.pi nodeAt ctAt ntAt 656 = true := by
  decide +kernel

theorem chunk_664 : innerB 8 dLit.pi nodeAt ctAt ntAt 664 = true := by
  decide +kernel

theorem chunk_672 : innerB 8 dLit.pi nodeAt ctAt ntAt 672 = true := by
  decide +kernel

theorem chunk_680 : innerB 8 dLit.pi nodeAt ctAt ntAt 680 = true := by
  decide +kernel

theorem chunk_688 : innerB 8 dLit.pi nodeAt ctAt ntAt 688 = true := by
  decide +kernel

theorem chunk_696 : innerB 8 dLit.pi nodeAt ctAt ntAt 696 = true := by
  decide +kernel

end SandierSerfaty.CertData
