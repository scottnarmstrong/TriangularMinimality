/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum E, shard 4 (kernel)

`decide +kernel` segments of 1000 steps of the second midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem e_36 : runSeg (eTerm flTbl cELit) lamL (lamL * 36) (eCk 36).1 (eCk 36).2
    (eCk (36 + 1)).1 (eCk (36 + 1)).2 = true := by
  decide +kernel

theorem e_37 : runSeg (eTerm flTbl cELit) lamL (lamL * 37) (eCk 37).1 (eCk 37).2
    (eCk (37 + 1)).1 (eCk (37 + 1)).2 = true := by
  decide +kernel

theorem e_38 : runSeg (eTerm flTbl cELit) lamL (lamL * 38) (eCk 38).1 (eCk 38).2
    (eCk (38 + 1)).1 (eCk (38 + 1)).2 = true := by
  decide +kernel

theorem e_39 : runSeg (eTerm flTbl cELit) lamL (lamL * 39) (eCk 39).1 (eCk 39).2
    (eCk (39 + 1)).1 (eCk (39 + 1)).2 = true := by
  decide +kernel

theorem e_40 : runSeg (eTerm flTbl cELit) lamL (lamL * 40) (eCk 40).1 (eCk 40).2
    (eCk (40 + 1)).1 (eCk (40 + 1)).2 = true := by
  decide +kernel

theorem e_41 : runSeg (eTerm flTbl cELit) lamL (lamL * 41) (eCk 41).1 (eCk 41).2
    (eCk (41 + 1)).1 (eCk (41 + 1)).2 = true := by
  decide +kernel

theorem e_42 : runSeg (eTerm flTbl cELit) lamL (lamL * 42) (eCk 42).1 (eCk 42).2
    (eCk (42 + 1)).1 (eCk (42 + 1)).2 = true := by
  decide +kernel

theorem e_43 : runSeg (eTerm flTbl cELit) lamL (lamL * 43) (eCk 43).1 (eCk 43).2
    (eCk (43 + 1)).1 (eCk (43 + 1)).2 = true := by
  decide +kernel

theorem e_44 : runSeg (eTerm flTbl cELit) lamL (lamL * 44) (eCk 44).1 (eCk 44).2
    (eCk (44 + 1)).1 (eCk (44 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
