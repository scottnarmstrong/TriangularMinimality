/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The radial table, shard 68 (kernel)

`decide +kernel` shards of segment `2`: the chunks of the cells `2006, …, 2015` (1 cells per declaration; estimated 130 s of kernel time).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

theorem chunk_2006 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2006 = true := by
  decide +kernel

theorem chunk_2007 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2007 = true := by
  decide +kernel

theorem chunk_2008 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2008 = true := by
  decide +kernel

theorem chunk_2009 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2009 = true := by
  decide +kernel

theorem chunk_2010 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2010 = true := by
  decide +kernel

theorem chunk_2011 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2011 = true := by
  decide +kernel

theorem chunk_2012 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2012 = true := by
  decide +kernel

theorem chunk_2013 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2013 = true := by
  decide +kernel

theorem chunk_2014 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2014 = true := by
  decide +kernel

theorem chunk_2015 : chunkB 1 dLit nodeAt ctAt ntAt ckAt 2 2015 = true := by
  decide +kernel

end SandierSerfaty.CertData
