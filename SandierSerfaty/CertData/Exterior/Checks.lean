/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Exterior.Data
public import SandierSerfaty.Certificate.Query.Const

/-!
# The λ enclosure and the exterior test A6 (kernel shard)

`decide +kernel` shards: `lamEnc` on the whole table, and `a6Check`.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The `λ` quadrature returns the literal enclosure. -/
theorem lam_ok : optEqB (lamEnc iTbl dLit 64 lamRad) lamLit = true := by
  decide +kernel

/-- The exterior test A6 on the node tuples at `l` (node `3848`) and `R₀` (node `2016`). -/
theorem a6_ok : a6Check dLit.pi dLit.r0 (IV.addRad (ntAt 3847).f0 lamRad) (IV.addRad (ntAt 2015).f0 lamRad)
    (IV.addRad (ntAt 2015).e0 lamRad) (IV.addRad (basis dLit 5 (knotIV dLit 6)).bsum.c0 lamRad) lamLit = true := by
  decide +kernel

end SandierSerfaty.CertData
