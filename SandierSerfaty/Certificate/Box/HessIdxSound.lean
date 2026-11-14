/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.HessIdx
public import SandierSerfaty.Certificate.Box.HessSound
public import SandierSerfaty.Certificate.Box.CtxIdxSound

/-!
# Soundness of the Hessian check with the checked-index lookup

`hess_localHessI`: the statement of `hess_localHess` (`LocalHess S` from the rows) with the rows `HessData.rowsI H ix`
(the table read through the proposed index range `ix a i` of each rectangle, verified by the kernel). The conclusion
and every other hypothesis (including `HessEnv`) are unchanged; `ix` is untrusted data.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

variable {H : HessData} {a : ℕ → ℝ}

theorem ctxI_pt_of (E : HessEnv H a) (ix : ℕ → ℕ → ℕ × ℕ) {ad i : ℕ} {c : DCtx2}
    (hm : H.ctxI ix ad i = some c) : CtxPt H ad i c := by
  intro d s hbd hd hs
  unfold HessData.ctxI at hm
  cases hix : ix ad i with
  | mk i0 i1 =>
    rw [hix] at hm
    exact mkDCtx2I_sound E.fc E.encl E.rad E.hl E.hf0l E.hk0 E.hlsq E.hlam E.hmu hm hbd (mem_ofNatPair hd.1 hd.2)
      (mem_ofNatPair hs.1 hs.2)

/-- **`LocalHess` from the Hessian rows with the checked index** (A10). -/
theorem hess_localHessI (E : HessEnv H a) (ix : ℕ → ℕ → ℕ × ℕ) {S : Set (ℝ × ℝ)} (hnd : 0 < H.nd)
    (hnx : H.jmin < H.nx) (hdp0 : Calibration.b ≤ dpt H 0) (hsp0 : H.sp 0 = 0)
    (hrows : H.rowsI ix H.nd = true)
    (hS : ∀ q ∈ S, q.1 ∈ Icc (dpt H 0) (dpt H H.nd) ∧ q.2 ∈ Icc (sgm H H.jmin) (sgm H H.nx)) :
    LocalHess S :=
  hess_localHessG (H.ctxI ix) (fun _ _ _ hm => ctxI_pt_of E ix hm) hnd hnx hdp0 hsp0 hrows hS

end SandierSerfaty.Certificate.Box
