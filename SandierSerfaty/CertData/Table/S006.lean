/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 6 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `814, …, 843` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_814 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 814 = true := by
  decide +kernel

theorem chunk_816 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 816 = true := by
  decide +kernel

theorem chunk_818 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 818 = true := by
  decide +kernel

theorem chunk_820 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 820 = true := by
  decide +kernel

theorem chunk_822 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 822 = true := by
  decide +kernel

theorem chunk_824 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 824 = true := by
  decide +kernel

theorem chunk_826 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 826 = true := by
  decide +kernel

theorem chunk_828 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 828 = true := by
  decide +kernel

theorem chunk_830 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 830 = true := by
  decide +kernel

theorem chunk_832 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 832 = true := by
  decide +kernel

theorem chunk_834 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 834 = true := by
  decide +kernel

theorem chunk_836 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 836 = true := by
  decide +kernel

theorem chunk_838 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 838 = true := by
  decide +kernel

theorem chunk_840 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 840 = true := by
  decide +kernel

theorem chunk_842 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 842 = true := by
  decide +kernel

end SandierSerfaty.CertData
