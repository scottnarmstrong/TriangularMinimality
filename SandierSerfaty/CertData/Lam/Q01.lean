/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum Q, shard 1 (kernel)

`decide +kernel` segments of 1000 steps of the first midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem q_9 : runSeg (qTerm flTbl cQLit) lamL (lamL * 9) (qCk 9).1 (qCk 9).2
    (qCk (9 + 1)).1 (qCk (9 + 1)).2 = true := by
  decide +kernel

theorem q_10 : runSeg (qTerm flTbl cQLit) lamL (lamL * 10) (qCk 10).1 (qCk 10).2
    (qCk (10 + 1)).1 (qCk (10 + 1)).2 = true := by
  decide +kernel

theorem q_11 : runSeg (qTerm flTbl cQLit) lamL (lamL * 11) (qCk 11).1 (qCk 11).2
    (qCk (11 + 1)).1 (qCk (11 + 1)).2 = true := by
  decide +kernel

theorem q_12 : runSeg (qTerm flTbl cQLit) lamL (lamL * 12) (qCk 12).1 (qCk 12).2
    (qCk (12 + 1)).1 (qCk (12 + 1)).2 = true := by
  decide +kernel

theorem q_13 : runSeg (qTerm flTbl cQLit) lamL (lamL * 13) (qCk 13).1 (qCk 13).2
    (qCk (13 + 1)).1 (qCk (13 + 1)).2 = true := by
  decide +kernel

theorem q_14 : runSeg (qTerm flTbl cQLit) lamL (lamL * 14) (qCk 14).1 (qCk 14).2
    (qCk (14 + 1)).1 (qCk (14 + 1)).2 = true := by
  decide +kernel

theorem q_15 : runSeg (qTerm flTbl cQLit) lamL (lamL * 15) (qCk 15).1 (qCk 15).2
    (qCk (15 + 1)).1 (qCk (15 + 1)).2 = true := by
  decide +kernel

theorem q_16 : runSeg (qTerm flTbl cQLit) lamL (lamL * 16) (qCk 16).1 (qCk 16).2
    (qCk (16 + 1)).1 (qCk (16 + 1)).2 = true := by
  decide +kernel

theorem q_17 : runSeg (qTerm flTbl cQLit) lamL (lamL * 17) (qCk 17).1 (qCk 17).2
    (qCk (17 + 1)).1 (qCk (17 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
