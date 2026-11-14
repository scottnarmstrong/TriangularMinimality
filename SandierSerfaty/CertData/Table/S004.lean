/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 4 (kernel)

`decide +kernel` shards of segment `0`: the chunks of the cells `704, …, 783` (8 cells per declaration; estimated 80 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_704 : innerB 8 dLit.pi nodeAt ctAt ntAt 704 = true := by
  decide +kernel

theorem chunk_712 : innerB 8 dLit.pi nodeAt ctAt ntAt 712 = true := by
  decide +kernel

theorem chunk_720 : innerB 8 dLit.pi nodeAt ctAt ntAt 720 = true := by
  decide +kernel

theorem chunk_728 : innerB 8 dLit.pi nodeAt ctAt ntAt 728 = true := by
  decide +kernel

theorem chunk_736 : innerB 8 dLit.pi nodeAt ctAt ntAt 736 = true := by
  decide +kernel

theorem chunk_744 : innerB 8 dLit.pi nodeAt ctAt ntAt 744 = true := by
  decide +kernel

theorem chunk_752 : innerB 8 dLit.pi nodeAt ctAt ntAt 752 = true := by
  decide +kernel

theorem chunk_760 : innerB 8 dLit.pi nodeAt ctAt ntAt 760 = true := by
  decide +kernel

theorem chunk_768 : innerB 8 dLit.pi nodeAt ctAt ntAt 768 = true := by
  decide +kernel

theorem chunk_776 : innerB 8 dLit.pi nodeAt ctAt ntAt 776 = true := by
  decide +kernel

end SandierSerfaty.CertData
