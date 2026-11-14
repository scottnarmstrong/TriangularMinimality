/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum E, shard 3 (kernel)

`decide +kernel` segments of 1000 steps of the second midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem e_27 : runSeg (eTerm flTbl cELit) lamL (lamL * 27) (eCk 27).1 (eCk 27).2
    (eCk (27 + 1)).1 (eCk (27 + 1)).2 = true := by
  decide +kernel

theorem e_28 : runSeg (eTerm flTbl cELit) lamL (lamL * 28) (eCk 28).1 (eCk 28).2
    (eCk (28 + 1)).1 (eCk (28 + 1)).2 = true := by
  decide +kernel

theorem e_29 : runSeg (eTerm flTbl cELit) lamL (lamL * 29) (eCk 29).1 (eCk 29).2
    (eCk (29 + 1)).1 (eCk (29 + 1)).2 = true := by
  decide +kernel

theorem e_30 : runSeg (eTerm flTbl cELit) lamL (lamL * 30) (eCk 30).1 (eCk 30).2
    (eCk (30 + 1)).1 (eCk (30 + 1)).2 = true := by
  decide +kernel

theorem e_31 : runSeg (eTerm flTbl cELit) lamL (lamL * 31) (eCk 31).1 (eCk 31).2
    (eCk (31 + 1)).1 (eCk (31 + 1)).2 = true := by
  decide +kernel

theorem e_32 : runSeg (eTerm flTbl cELit) lamL (lamL * 32) (eCk 32).1 (eCk 32).2
    (eCk (32 + 1)).1 (eCk (32 + 1)).2 = true := by
  decide +kernel

theorem e_33 : runSeg (eTerm flTbl cELit) lamL (lamL * 33) (eCk 33).1 (eCk 33).2
    (eCk (33 + 1)).1 (eCk (33 + 1)).2 = true := by
  decide +kernel

theorem e_34 : runSeg (eTerm flTbl cELit) lamL (lamL * 34) (eCk 34).1 (eCk 34).2
    (eCk (34 + 1)).1 (eCk (34 + 1)).2 = true := by
  decide +kernel

theorem e_35 : runSeg (eTerm flTbl cELit) lamL (lamL * 35) (eCk 35).1 (eCk 35).2
    (eCk (35 + 1)).1 (eCk (35 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
