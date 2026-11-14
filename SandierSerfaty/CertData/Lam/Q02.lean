/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum Q, shard 2 (kernel)

`decide +kernel` segments of 1000 steps of the first midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem q_18 : runSeg (qTerm flTbl cQLit) lamL (lamL * 18) (qCk 18).1 (qCk 18).2
    (qCk (18 + 1)).1 (qCk (18 + 1)).2 = true := by
  decide +kernel

theorem q_19 : runSeg (qTerm flTbl cQLit) lamL (lamL * 19) (qCk 19).1 (qCk 19).2
    (qCk (19 + 1)).1 (qCk (19 + 1)).2 = true := by
  decide +kernel

theorem q_20 : runSeg (qTerm flTbl cQLit) lamL (lamL * 20) (qCk 20).1 (qCk 20).2
    (qCk (20 + 1)).1 (qCk (20 + 1)).2 = true := by
  decide +kernel

theorem q_21 : runSeg (qTerm flTbl cQLit) lamL (lamL * 21) (qCk 21).1 (qCk 21).2
    (qCk (21 + 1)).1 (qCk (21 + 1)).2 = true := by
  decide +kernel

theorem q_22 : runSeg (qTerm flTbl cQLit) lamL (lamL * 22) (qCk 22).1 (qCk 22).2
    (qCk (22 + 1)).1 (qCk (22 + 1)).2 = true := by
  decide +kernel

theorem q_23 : runSeg (qTerm flTbl cQLit) lamL (lamL * 23) (qCk 23).1 (qCk 23).2
    (qCk (23 + 1)).1 (qCk (23 + 1)).2 = true := by
  decide +kernel

theorem q_24 : runSeg (qTerm flTbl cQLit) lamL (lamL * 24) (qCk 24).1 (qCk 24).2
    (qCk (24 + 1)).1 (qCk (24 + 1)).2 = true := by
  decide +kernel

theorem q_25 : runSeg (qTerm flTbl cQLit) lamL (lamL * 25) (qCk 25).1 (qCk 25).2
    (qCk (25 + 1)).1 (qCk (25 + 1)).2 = true := by
  decide +kernel

theorem q_26 : runSeg (qTerm flTbl cQLit) lamL (lamL * 26) (qCk 26).1 (qCk 26).2
    (qCk (26 + 1)).1 (qCk (26 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
