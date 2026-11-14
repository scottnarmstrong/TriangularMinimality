/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum E, shard 0 (kernel)

`decide +kernel` segments of 1000 steps of the second midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem e_0 : runSeg (eTerm flTbl cELit) lamL (lamL * 0) (eCk 0).1 (eCk 0).2
    (eCk (0 + 1)).1 (eCk (0 + 1)).2 = true := by
  decide +kernel

theorem e_1 : runSeg (eTerm flTbl cELit) lamL (lamL * 1) (eCk 1).1 (eCk 1).2
    (eCk (1 + 1)).1 (eCk (1 + 1)).2 = true := by
  decide +kernel

theorem e_2 : runSeg (eTerm flTbl cELit) lamL (lamL * 2) (eCk 2).1 (eCk 2).2
    (eCk (2 + 1)).1 (eCk (2 + 1)).2 = true := by
  decide +kernel

theorem e_3 : runSeg (eTerm flTbl cELit) lamL (lamL * 3) (eCk 3).1 (eCk 3).2
    (eCk (3 + 1)).1 (eCk (3 + 1)).2 = true := by
  decide +kernel

theorem e_4 : runSeg (eTerm flTbl cELit) lamL (lamL * 4) (eCk 4).1 (eCk 4).2
    (eCk (4 + 1)).1 (eCk (4 + 1)).2 = true := by
  decide +kernel

theorem e_5 : runSeg (eTerm flTbl cELit) lamL (lamL * 5) (eCk 5).1 (eCk 5).2
    (eCk (5 + 1)).1 (eCk (5 + 1)).2 = true := by
  decide +kernel

theorem e_6 : runSeg (eTerm flTbl cELit) lamL (lamL * 6) (eCk 6).1 (eCk 6).2
    (eCk (6 + 1)).1 (eCk (6 + 1)).2 = true := by
  decide +kernel

theorem e_7 : runSeg (eTerm flTbl cELit) lamL (lamL * 7) (eCk 7).1 (eCk 7).2
    (eCk (7 + 1)).1 (eCk (7 + 1)).2 = true := by
  decide +kernel

theorem e_8 : runSeg (eTerm flTbl cELit) lamL (lamL * 8) (eCk 8).1 (eCk 8).2
    (eCk (8 + 1)).1 (eCk (8 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
