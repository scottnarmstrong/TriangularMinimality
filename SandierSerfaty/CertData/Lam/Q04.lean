/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The fine λ, sum Q, shard 4 (kernel)

`decide +kernel` segments of 1000 steps of the first midpoint sum, from literal checkpoints (`Lambda.runSeg`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem q_36 : runSeg (qTerm flTbl cQLit) lamL (lamL * 36) (qCk 36).1 (qCk 36).2
    (qCk (36 + 1)).1 (qCk (36 + 1)).2 = true := by
  decide +kernel

theorem q_37 : runSeg (qTerm flTbl cQLit) lamL (lamL * 37) (qCk 37).1 (qCk 37).2
    (qCk (37 + 1)).1 (qCk (37 + 1)).2 = true := by
  decide +kernel

theorem q_38 : runSeg (qTerm flTbl cQLit) lamL (lamL * 38) (qCk 38).1 (qCk 38).2
    (qCk (38 + 1)).1 (qCk (38 + 1)).2 = true := by
  decide +kernel

theorem q_39 : runSeg (qTerm flTbl cQLit) lamL (lamL * 39) (qCk 39).1 (qCk 39).2
    (qCk (39 + 1)).1 (qCk (39 + 1)).2 = true := by
  decide +kernel

theorem q_40 : runSeg (qTerm flTbl cQLit) lamL (lamL * 40) (qCk 40).1 (qCk 40).2
    (qCk (40 + 1)).1 (qCk (40 + 1)).2 = true := by
  decide +kernel

theorem q_41 : runSeg (qTerm flTbl cQLit) lamL (lamL * 41) (qCk 41).1 (qCk 41).2
    (qCk (41 + 1)).1 (qCk (41 + 1)).2 = true := by
  decide +kernel

theorem q_42 : runSeg (qTerm flTbl cQLit) lamL (lamL * 42) (qCk 42).1 (qCk 42).2
    (qCk (42 + 1)).1 (qCk (42 + 1)).2 = true := by
  decide +kernel

theorem q_43 : runSeg (qTerm flTbl cQLit) lamL (lamL * 43) (qCk 43).1 (qCk 43).2
    (qCk (43 + 1)).1 (qCk (43 + 1)).2 = true := by
  decide +kernel

theorem q_44 : runSeg (qTerm flTbl cQLit) lamL (lamL * 44) (qCk 44).1 (qCk 44).2
    (qCk (44 + 1)).1 (qCk (44 + 1)).2 = true := by
  decide +kernel

end SandierSerfaty.CertData
