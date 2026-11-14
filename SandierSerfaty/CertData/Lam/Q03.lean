/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum Q, shard 3 (kernel)

`decide +kernel` segments of 1000 steps of the first midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem q_27 : runSeg (qTerm flTbl cQLit) lamL (lamL * 27) (qCk 27).1 (qCk 27).2
    (qCk (27 + 1)).1 (qCk (27 + 1)).2 = true := by
  decide +kernel

theorem q_28 : runSeg (qTerm flTbl cQLit) lamL (lamL * 28) (qCk 28).1 (qCk 28).2
    (qCk (28 + 1)).1 (qCk (28 + 1)).2 = true := by
  decide +kernel

theorem q_29 : runSeg (qTerm flTbl cQLit) lamL (lamL * 29) (qCk 29).1 (qCk 29).2
    (qCk (29 + 1)).1 (qCk (29 + 1)).2 = true := by
  decide +kernel

theorem q_30 : runSeg (qTerm flTbl cQLit) lamL (lamL * 30) (qCk 30).1 (qCk 30).2
    (qCk (30 + 1)).1 (qCk (30 + 1)).2 = true := by
  decide +kernel

theorem q_31 : runSeg (qTerm flTbl cQLit) lamL (lamL * 31) (qCk 31).1 (qCk 31).2
    (qCk (31 + 1)).1 (qCk (31 + 1)).2 = true := by
  decide +kernel

theorem q_32 : runSeg (qTerm flTbl cQLit) lamL (lamL * 32) (qCk 32).1 (qCk 32).2
    (qCk (32 + 1)).1 (qCk (32 + 1)).2 = true := by
  decide +kernel

theorem q_33 : runSeg (qTerm flTbl cQLit) lamL (lamL * 33) (qCk 33).1 (qCk 33).2
    (qCk (33 + 1)).1 (qCk (33 + 1)).2 = true := by
  decide +kernel

theorem q_34 : runSeg (qTerm flTbl cQLit) lamL (lamL * 34) (qCk 34).1 (qCk 34).2
    (qCk (34 + 1)).1 (qCk (34 + 1)).2 = true := by
  decide +kernel

theorem q_35 : runSeg (qTerm flTbl cQLit) lamL (lamL * 35) (qCk 35).1 (qCk 35).2
    (qCk (35 + 1)).1 (qCk (35 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
