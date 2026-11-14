/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum E, shard 1 (kernel)

`decide +kernel` segments of 1000 steps of the second midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem e_9 : runSeg (eTerm flTbl cELit) lamL (lamL * 9) (eCk 9).1 (eCk 9).2
    (eCk (9 + 1)).1 (eCk (9 + 1)).2 = true := by
  decide +kernel

theorem e_10 : runSeg (eTerm flTbl cELit) lamL (lamL * 10) (eCk 10).1 (eCk 10).2
    (eCk (10 + 1)).1 (eCk (10 + 1)).2 = true := by
  decide +kernel

theorem e_11 : runSeg (eTerm flTbl cELit) lamL (lamL * 11) (eCk 11).1 (eCk 11).2
    (eCk (11 + 1)).1 (eCk (11 + 1)).2 = true := by
  decide +kernel

theorem e_12 : runSeg (eTerm flTbl cELit) lamL (lamL * 12) (eCk 12).1 (eCk 12).2
    (eCk (12 + 1)).1 (eCk (12 + 1)).2 = true := by
  decide +kernel

theorem e_13 : runSeg (eTerm flTbl cELit) lamL (lamL * 13) (eCk 13).1 (eCk 13).2
    (eCk (13 + 1)).1 (eCk (13 + 1)).2 = true := by
  decide +kernel

theorem e_14 : runSeg (eTerm flTbl cELit) lamL (lamL * 14) (eCk 14).1 (eCk 14).2
    (eCk (14 + 1)).1 (eCk (14 + 1)).2 = true := by
  decide +kernel

theorem e_15 : runSeg (eTerm flTbl cELit) lamL (lamL * 15) (eCk 15).1 (eCk 15).2
    (eCk (15 + 1)).1 (eCk (15 + 1)).2 = true := by
  decide +kernel

theorem e_16 : runSeg (eTerm flTbl cELit) lamL (lamL * 16) (eCk 16).1 (eCk 16).2
    (eCk (16 + 1)).1 (eCk (16 + 1)).2 = true := by
  decide +kernel

theorem e_17 : runSeg (eTerm flTbl cELit) lamL (lamL * 17) (eCk 17).1 (eCk 17).2
    (eCk (17 + 1)).1 (eCk (17 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
