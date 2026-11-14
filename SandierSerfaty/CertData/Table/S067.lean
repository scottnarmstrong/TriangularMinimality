/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 67 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `1993, …, 2005` (1 cells per declaration; estimated 169 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_1993 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1993 = true := by
  decide +kernel

theorem chunk_1994 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1994 = true := by
  decide +kernel

theorem chunk_1995 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1995 = true := by
  decide +kernel

theorem chunk_1996 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1996 = true := by
  decide +kernel

theorem chunk_1997 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1997 = true := by
  decide +kernel

theorem chunk_1998 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1998 = true := by
  decide +kernel

theorem chunk_1999 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 1999 = true := by
  decide +kernel

theorem chunk_2000 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2000 = true := by
  decide +kernel

theorem chunk_2001 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2001 = true := by
  decide +kernel

theorem chunk_2002 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2002 = true := by
  decide +kernel

theorem chunk_2003 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2003 = true := by
  decide +kernel

theorem chunk_2004 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2004 = true := by
  decide +kernel

theorem chunk_2005 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2005 = true := by
  decide +kernel

end SandierSerfaty.CertData
