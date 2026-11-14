/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 9 (kernel)

`decide +kernel` shards of segment `1`: the chunks of the cells `904, …, 933` (2 cells per declaration; estimated 180 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_904 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 904 = true := by
  decide +kernel

theorem chunk_906 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 906 = true := by
  decide +kernel

theorem chunk_908 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 908 = true := by
  decide +kernel

theorem chunk_910 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 910 = true := by
  decide +kernel

theorem chunk_912 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 912 = true := by
  decide +kernel

theorem chunk_914 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 914 = true := by
  decide +kernel

theorem chunk_916 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 916 = true := by
  decide +kernel

theorem chunk_918 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 918 = true := by
  decide +kernel

theorem chunk_920 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 920 = true := by
  decide +kernel

theorem chunk_922 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 922 = true := by
  decide +kernel

theorem chunk_924 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 924 = true := by
  decide +kernel

theorem chunk_926 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 926 = true := by
  decide +kernel

theorem chunk_928 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 928 = true := by
  decide +kernel

theorem chunk_930 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 930 = true := by
  decide +kernel

theorem chunk_932 : chunkB 2 dLit nodeAt ctAt ntAt ckAt 1 932 = true := by
  decide +kernel

end SandierSerfaty.CertData
