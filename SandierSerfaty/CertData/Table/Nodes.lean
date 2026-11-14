/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Data

/-!
# The nodes and the initial checkpoint (kernel shard)

`decide +kernel` shards: `nodesB` and the initial checkpoint.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- Node separation, nondegeneracy and the knots. -/
theorem nodes_ok : nodesB dLit nodeAt knotCell tblN = true := by
  decide +kernel

/-- The initial checkpoint at `p - c`. -/
theorem init_ok : initCheck dLit (nodeAt 784) (ckAt 784) = true := by
  decide +kernel

end SandierSerfaty.CertData
