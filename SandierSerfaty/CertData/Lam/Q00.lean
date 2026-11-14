/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum Q, shard 0 (kernel)

`decide +kernel` segments of 1000 steps of the first midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem q_0 : runSeg (qTerm flTbl cQLit) lamL (lamL * 0) (qCk 0).1 (qCk 0).2
    (qCk (0 + 1)).1 (qCk (0 + 1)).2 = true := by
  decide +kernel

theorem q_1 : runSeg (qTerm flTbl cQLit) lamL (lamL * 1) (qCk 1).1 (qCk 1).2
    (qCk (1 + 1)).1 (qCk (1 + 1)).2 = true := by
  decide +kernel

theorem q_2 : runSeg (qTerm flTbl cQLit) lamL (lamL * 2) (qCk 2).1 (qCk 2).2
    (qCk (2 + 1)).1 (qCk (2 + 1)).2 = true := by
  decide +kernel

theorem q_3 : runSeg (qTerm flTbl cQLit) lamL (lamL * 3) (qCk 3).1 (qCk 3).2
    (qCk (3 + 1)).1 (qCk (3 + 1)).2 = true := by
  decide +kernel

theorem q_4 : runSeg (qTerm flTbl cQLit) lamL (lamL * 4) (qCk 4).1 (qCk 4).2
    (qCk (4 + 1)).1 (qCk (4 + 1)).2 = true := by
  decide +kernel

theorem q_5 : runSeg (qTerm flTbl cQLit) lamL (lamL * 5) (qCk 5).1 (qCk 5).2
    (qCk (5 + 1)).1 (qCk (5 + 1)).2 = true := by
  decide +kernel

theorem q_6 : runSeg (qTerm flTbl cQLit) lamL (lamL * 6) (qCk 6).1 (qCk 6).2
    (qCk (6 + 1)).1 (qCk (6 + 1)).2 = true := by
  decide +kernel

theorem q_7 : runSeg (qTerm flTbl cQLit) lamL (lamL * 7) (qCk 7).1 (qCk 7).2
    (qCk (7 + 1)).1 (qCk (7 + 1)).2 = true := by
  decide +kernel

theorem q_8 : runSeg (qTerm flTbl cQLit) lamL (lamL * 8) (qCk 8).1 (qCk 8).2
    (qCk (8 + 1)).1 (qCk (8 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
