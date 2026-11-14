/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Data

/-!
# The prelude of the fine λ (kernel shard)

`decide +kernel` checks of the literal prelude of `lamFine`: the root `t₀`, the two lookups, the four point values, the two contexts, the initial checkpoints and the last stage.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

theorem lh_ok : and (Nat.beq (IV.sqrtProposal (IV.add dLit.p2 (IV.sq (s0Of lamPar)))).1 lhLit.1) (Nat.beq (IV.sqrtProposal (IV.add dLit.p2 (IV.sq (s0Of lamPar)))).2 lhLit.2) = true := by
  decide +kernel

theorem sq_ok : IV.sqrtCheck (IV.add dLit.p2 (IV.sq (s0Of lamPar))) lhLit.1 lhLit.2 = true := by
  decide +kernel

theorem cB_ok : optTupEqB (lookup flTbl.T (IV.hull dLit.p dLit.r0)) cBLit = true := by
  decide +kernel

theorem cY_ok : optTupEqB (lookup flTbl.T (IV.hull dLit.p (IV.ofNatPair lhLit.1 lhLit.2))) cYLit = true := by
  decide +kernel

theorem fp_ok : optEqB (fPt flTbl lamPar.rad dLit.p) fpLit = true := by
  decide +kernel

theorem fp1_ok : optEqB (f1Pt flTbl lamPar.rad dLit.p) fp1Lit = true := by
  decide +kernel

theorem fr_ok : optEqB (fPt flTbl lamPar.rad dLit.r0) frLit = true := by
  decide +kernel

theorem er_ok : optEqB (ePt flTbl lamPar.rad dLit.r0) erLit = true := by
  decide +kernel

theorem cQ_ok : qctxEqB (qCtxOf dLit lamPar.Nq lamPar.rad (s0Of lamPar) cBLit fpLit) cQLit = true := by
  decide +kernel

theorem cE_ok : qctxEqB (eCtxOf dLit lamPar.Ne lamPar.rad cBLit) cELit = true := by
  decide +kernel

theorem q0_ok : and (Nat.beq (qCk 0).1 0) (ivEqB (qCk 0).2 (IV.ofNat 0)) = true := by
  decide +kernel

theorem e0_ok : and (Nat.beq (eCk 0).1 0) (ivEqB (eCk 0).2 (IV.ofNat 0)) = true := by
  decide +kernel

theorem fin_ok : optEqB (lamFineS dLit lamPar (s0Of lamPar) (IV.ofNatPair lhLit.1 lhLit.2) cYLit fpLit fp1Lit frLit erLit (some (qCk 45).2) (some (eCk 45).2)) lamFLit = true := by
  decide +kernel

end SandierSerfaty.CertData
