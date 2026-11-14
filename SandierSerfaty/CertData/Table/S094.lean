/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 94 (kernel)

`decide +kernel` shards of segment `4`: the chunks of the cells `2760, …, 2789` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2760 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2760 = true := by
  decide +kernel

theorem chunk_2762 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2762 = true := by
  decide +kernel

theorem chunk_2764 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2764 = true := by
  decide +kernel

theorem chunk_2766 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2766 = true := by
  decide +kernel

theorem chunk_2768 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2768 = true := by
  decide +kernel

theorem chunk_2770 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2770 = true := by
  decide +kernel

theorem chunk_2772 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2772 = true := by
  decide +kernel

theorem chunk_2774 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2774 = true := by
  decide +kernel

theorem chunk_2776 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2776 = true := by
  decide +kernel

theorem chunk_2778 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2778 = true := by
  decide +kernel

theorem chunk_2780 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2780 = true := by
  decide +kernel

theorem chunk_2782 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2782 = true := by
  decide +kernel

theorem chunk_2784 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2784 = true := by
  decide +kernel

theorem chunk_2786 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2786 = true := by
  decide +kernel

theorem chunk_2788 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 4 2788 = true := by
  decide +kernel

end SandierSerfaty.CertData
