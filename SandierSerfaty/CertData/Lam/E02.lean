/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum E, shard 2 (kernel)

`decide +kernel` segments of 1000 steps of the second midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem e_18 : runSeg (eTerm flTbl cELit) lamL (lamL * 18) (eCk 18).1 (eCk 18).2
    (eCk (18 + 1)).1 (eCk (18 + 1)).2 = true := by
  decide +kernel

theorem e_19 : runSeg (eTerm flTbl cELit) lamL (lamL * 19) (eCk 19).1 (eCk 19).2
    (eCk (19 + 1)).1 (eCk (19 + 1)).2 = true := by
  decide +kernel

theorem e_20 : runSeg (eTerm flTbl cELit) lamL (lamL * 20) (eCk 20).1 (eCk 20).2
    (eCk (20 + 1)).1 (eCk (20 + 1)).2 = true := by
  decide +kernel

theorem e_21 : runSeg (eTerm flTbl cELit) lamL (lamL * 21) (eCk 21).1 (eCk 21).2
    (eCk (21 + 1)).1 (eCk (21 + 1)).2 = true := by
  decide +kernel

theorem e_22 : runSeg (eTerm flTbl cELit) lamL (lamL * 22) (eCk 22).1 (eCk 22).2
    (eCk (22 + 1)).1 (eCk (22 + 1)).2 = true := by
  decide +kernel

theorem e_23 : runSeg (eTerm flTbl cELit) lamL (lamL * 23) (eCk 23).1 (eCk 23).2
    (eCk (23 + 1)).1 (eCk (23 + 1)).2 = true := by
  decide +kernel

theorem e_24 : runSeg (eTerm flTbl cELit) lamL (lamL * 24) (eCk 24).1 (eCk 24).2
    (eCk (24 + 1)).1 (eCk (24 + 1)).2 = true := by
  decide +kernel

theorem e_25 : runSeg (eTerm flTbl cELit) lamL (lamL * 25) (eCk 25).1 (eCk 25).2
    (eCk (25 + 1)).1 (eCk (25 + 1)).2 = true := by
  decide +kernel

theorem e_26 : runSeg (eTerm flTbl cELit) lamL (lamL * 26) (eCk 26).1 (eCk 26).2
    (eCk (26 + 1)).1 (eCk (26 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
