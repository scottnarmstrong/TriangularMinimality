/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Inner
public import SandierSerfaty.Certificate.Box.A7Idx
public import SandierSerfaty.Certificate.Box.HessIdxSound

/-!
# The inner assertion from the checked-index rows

`derivBounds_of_envI`, `inner_of_certificateI`: `Box.derivBounds_of_env` and `Box.inner_of_certificate` with the A7
rectangle rows `A7Data.rowI D ix` and the Hessian rows `HessData.rowsI H hix` (checked index ranges `ix`, `hix`,
untrusted data) in place of the scanning rows. Every other hypothesis and the conclusions are unchanged.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- **The derivative bounds of A7** with the checked index (`derivBounds_of_env`). -/
theorem derivBounds_of_envI {D : A7Data} (ix : Nat → Nat → Nat × Nat) {a : ℕ → ℝ} (E : A7Env D a)
    {dHi xHi : ℝ} (hnj : 0 < D.nj) (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : dHi ≤ (D.dp D.nj : ℝ) / 2 ^ 128) (hsp0 : D.sp 0 = 0) (hspn : xHi ≤ (D.sp D.nk : ℝ) / 2 ^ 128)
    (hrows : ∀ j < D.nj, D.rowI ix j D.nk = true) :
    DerivBounds Calibration.b dHi xHi ((D.L1 : ℝ) / 2 ^ 128) ((D.L2 : ℝ) / 2 ^ 128)
      ((D.L3 : ℝ) / 2 ^ 128) ((D.L4 : ℝ) / 2 ^ 128) :=
  derivBounds_of_a7I E.fc D ix E.encl E.rad E.hl E.hf0l E.hk0 E.hlsq E.hlam E.hmu hnj hnk hdp0 hdpn hsp0 hspn hrows

/-- **The inner assertion** (A10, T4) from the checked-index A7 rows and Hessian rows. -/
theorem inner_of_certificateI {D : A7Data} (ix : Nat → Nat → Nat × Nat) {a : ℕ → ℝ} (DE : A7Env D a)
    {H : HessData} (hix : Nat → Nat → Nat × Nat) {a' : ℕ → ℝ} (HE : HessEnv H a')
    -- the derivative partition covers `𝒟`
    (hnj : 0 < D.nj) (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : (697 : ℝ) / 1000 ≤ (D.dp D.nj : ℝ) / 2 ^ 128) (hsp0 : D.sp 0 = 0)
    (hspn : (65 : ℝ) / 100 ≤ (D.sp D.nk : ℝ) / 2 ^ 128) (hrows : ∀ j < D.nj, D.rowI ix j D.nk = true)
    -- the Hessian partitions cover `𝒟₀`
    (hnd : 0 < H.nd) (hjn : H.jmin < H.nx) (hhdp0 : Calibration.b ≤ dpt H 0) (hhsp0 : H.sp 0 = 0)
    (hhrows : H.rowsI hix H.nd = true) (hd_lo : dpt H 0 ≤ 52528 / 100000)
    (hd_hi : (54930 : ℝ) / 100000 ≤ dpt H H.nd) (hx_lo : sgm H H.jmin ≤ 29420 / 100000)
    (hx_hi : (32621 : ℝ) / 100000 ≤ sgm H H.nx) :
    ∀ q ∈ boxD₀, K ≤ 2 * g q.1 q.2 := by
  intro q hq
  have hB := derivBounds_of_envI ix DE hnj hnk hdp0 hdpn hsp0 hspn hrows
  have hloc : LocalHess boxD₀ := hess_localHessI HE hix hnd hjn hhdp0 hhsp0 hhrows (fun q hq =>
    ⟨⟨hd_lo.trans hq.1.1, hq.1.2.trans hd_hi⟩, ⟨hx_lo.trans hq.2.1, hq.2.2.trans hx_hi⟩⟩)
  have hconv : Convex ℝ boxD₀ := (convex_Icc _ _).prod (convex_Icc _ _)
  have hp : (p, x₀) ∈ boxD₀ := interior_subset pt_mem_interior_boxD₀
  have hgd : gd p x₀ = 0 := integral_Gd_eq_zero
  have hG : G p x₀ = 0 := G_p_x₀_eq_zero
  have := inner_of_localHess hB (S := boxD₀) boxD₀_subset_boxD hconv hloc hp hq hgd hG
  unfold K
  linarith

end SandierSerfaty.Certificate.Box
