/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.HessSound
public import SandierSerfaty.Calibration.Stationarity

/-!
# The inner assertion `K ≤ 2g` on `𝒟₀` from the certificate data (A10, theorem T4)

`inner_of_certificate` is the field `inner` of `Assembly.CertificateGoal`:

  `∀ q ∈ boxD₀, K ≤ 2 * g q.1 q.2`

from the finite data of the certificate: the derivative rectangles of A7 (`A7Data`, rows passing `A7Data.row`,
partition covering `𝒟 = [b, .697] × [0, .65]`) and the Hessian rows of A10 (`HessData`, `H.rows H.nd = true`, partitions
covering `𝒟₀ = [.52528, .5493] × [.2942, .32621]`), with the table realization and the enclosures of the constants
(`A7Env`, `HessEnv`). The proof is a one-dimensional Taylor argument along segments (the paper, `comp:hessian`, argues by
mollification instead): `A7` gives the derivative bounds
(`DerivBounds`), A10 gives `LocalHess 𝒟₀`, and `inner_of_localHess` with the stationarity of `(p, x₀)`
(`Calibration.integral_Gd_eq_zero`, `Calibration.G_p_x₀_eq_zero`) gives `g_p(x₀) ≤ g_d(x)`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The premises tying the interval data of the derivative assertion A7 to the exact calibration objects. -/
structure A7Env (D : A7Data) (a : ℕ → ℝ) : Prop where
  /-- The finite-core premise of §6. -/
  fc : FiniteCore
  /-- The table is realized by the real nodes `a`. -/
  encl : Encl2 D.T a
  /-- The table widening. -/
  rad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ D.rad
  /-- `l`. -/
  hl : IV.Mem Calibration.l D.lI
  /-- `f₀(l)`. -/
  hf0l : IV.Mem (f₀ Calibration.l) D.f0lI
  /-- `-π B(l)`. -/
  hk0 : IV.Mem (-(Real.pi * B Calibration.l)) D.k0I
  /-- `l²`. -/
  hlsq : IV.Mem (Calibration.l ^ 2) D.lsqI
  /-- `λ`. -/
  hlam : IV.Mem lam D.lamI
  /-- `μ`. -/
  hmu : IV.Mem mu D.muI

/-- **The derivative bounds of A7** on `[b, dHi] × [0, xHi]`, for any box inside the covered one. -/
theorem derivBounds_of_env {D : A7Data} {a : ℕ → ℝ} (E : A7Env D a) {dHi xHi : ℝ} (hnj : 0 < D.nj)
    (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b) (hdpn : dHi ≤ (D.dp D.nj : ℝ) / 2 ^ 128)
    (hsp0 : D.sp 0 = 0) (hspn : xHi ≤ (D.sp D.nk : ℝ) / 2 ^ 128) (hrows : ∀ j < D.nj, D.row j D.nk = true) :
    DerivBounds Calibration.b dHi xHi ((D.L1 : ℝ) / 2 ^ 128) ((D.L2 : ℝ) / 2 ^ 128)
      ((D.L3 : ℝ) / 2 ^ 128) ((D.L4 : ℝ) / 2 ^ 128) :=
  derivBounds_of_a7 E.fc D E.encl E.rad E.hl E.hf0l E.hk0 E.hlsq E.hlam E.hmu hnj hnk hdp0 hdpn hsp0 hspn hrows

/-- The derivative bounds restrict to a smaller box. -/
theorem DerivBounds.mono {dLo dHi xHi dHi' xHi' L1 L2 L3 L4 : ℝ} (h : DerivBounds dLo dHi xHi L1 L2 L3 L4)
    (h1 : dHi' ≤ dHi) (h2 : xHi' ≤ xHi) : DerivBounds dLo dHi' xHi' L1 L2 L3 L4 :=
  ⟨h.pos, h.nonneg, fun d hd s hs => h.gd_le d ⟨hd.1, hd.2.trans h1⟩ s ⟨hs.1, hs.2.trans h2⟩,
    fun d hd s hs => h.gs_le d ⟨hd.1, hd.2.trans h1⟩ s ⟨hs.1, hs.2.trans h2⟩,
    fun s hs d hd d' hd' => h.gd_lip s ⟨hs.1, hs.2.trans h2⟩ d ⟨hd.1, hd.2.trans h1⟩ d' ⟨hd'.1, hd'.2.trans h1⟩,
    fun d hd s hs s' hs' => h.gs_lip d ⟨hd.1, hd.2.trans h1⟩ s ⟨hs.1, hs.2.trans h2⟩ s' ⟨hs'.1, hs'.2.trans h2⟩⟩

/-- **The inner assertion** (A10, T4), from the A7 rectangle rows and the Hessian rows. -/
theorem inner_of_certificate {D : A7Data} {a : ℕ → ℝ} (DE : A7Env D a) {H : HessData} {a' : ℕ → ℝ}
    (HE : HessEnv H a')
    -- the derivative partition covers `𝒟`
    (hnj : 0 < D.nj) (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : (697 : ℝ) / 1000 ≤ (D.dp D.nj : ℝ) / 2 ^ 128) (hsp0 : D.sp 0 = 0)
    (hspn : (65 : ℝ) / 100 ≤ (D.sp D.nk : ℝ) / 2 ^ 128) (hrows : ∀ j < D.nj, D.row j D.nk = true)
    -- the Hessian partitions cover `𝒟₀`
    (hnd : 0 < H.nd) (hjn : H.jmin < H.nx) (hhdp0 : Calibration.b ≤ dpt H 0) (hhsp0 : H.sp 0 = 0)
    (hhrows : H.rows H.nd = true) (hd_lo : dpt H 0 ≤ 52528 / 100000) (hd_hi : (54930 : ℝ) / 100000 ≤ dpt H H.nd)
    (hx_lo : sgm H H.jmin ≤ 29420 / 100000) (hx_hi : (32621 : ℝ) / 100000 ≤ sgm H H.nx) :
    ∀ q ∈ boxD₀, K ≤ 2 * g q.1 q.2 := by
  intro q hq
  have hB := derivBounds_of_env DE hnj hnk hdp0 hdpn hsp0 hspn hrows
  have hloc : LocalHess boxD₀ := hess_localHess HE hnd hjn hhdp0 hhsp0 hhrows (fun q hq =>
    ⟨⟨hd_lo.trans hq.1.1, hq.1.2.trans hd_hi⟩, ⟨hx_lo.trans hq.2.1, hq.2.2.trans hx_hi⟩⟩)
  have hconv : Convex ℝ boxD₀ := (convex_Icc _ _).prod (convex_Icc _ _)
  have hp : (p, x₀) ∈ boxD₀ := interior_subset pt_mem_interior_boxD₀
  have hgd : gd p x₀ = 0 := integral_Gd_eq_zero
  have hG : G p x₀ = 0 := G_p_x₀_eq_zero
  have := inner_of_localHess hB (S := boxD₀) boxD₀_subset_boxD hconv hloc hp hq hgd hG
  unfold K
  linarith

end SandierSerfaty.Certificate.Box
