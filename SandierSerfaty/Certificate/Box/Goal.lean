/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Cert
public import SandierSerfaty.Certificate.Query.ExteriorSigns
public import SandierSerfaty.Assembly.TorusBoundOfCertificate

/-!
# `CertificateGoal` from the certificate data (all five fields)

`certificateGoal_of_data` assembles the five fields of `Assembly.CertificateGoal`

* `f_l_pos`, `slope_pos` (`Query.f_l_pos_slope_pos_of_certificate`, A4–A6),
* `outer` (`Box.outer_of_certificate`, A7–A8, T2),
* `inner` (`Box.inner_of_certificate`, A7, A10, T4),
* `negative` (`Box.negative_of_certificate`, A7, A9, T3)

from the finite data of the certificate: the radial table (nodes, cells, query cells) with its realization, the A7
rectangles, the outer / negative / `K` / Hessian rows, and the finite numerical facts about the literal grids and
thresholds. The hypotheses are exactly those of the five theorems; none states a field of the goal. The purely finite facts
(Boolean row and grid checks, rational inequalities) are discharged by the literal data and `decide +kernel`.
The enclosures of exact objects (`IV.Mem lam lamI`, `IV.Mem (f₀ l) f0lI`, `IV.Mem π piI`, …) are not decidable
on literals: they need the proved soundness lemmas (`lamEnc_sound`, `mem_f0_exact`, `mem_e_exact`, `mem_B_l`,
`BasisData.Valid`), and `Tails.FiniteCore` needs the A2 checks. `Calibration.K`, `lam`, `g` and `G` appear only in
conclusions.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Certificate.Basis SandierSerfaty.Calibration SandierSerfaty.Tails

/-- **The five fields of the certificate goal from the finite data.** -/
theorem certificateGoal_of_data {E : EvalData} {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI) (fc : FiniteCore)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    -- the exterior signs (A4–A6)
    {d : BasisData} (hd : d.Valid) (hp2 : IV.posB d.p2 = true) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {N rad : ℕ}
    (hN : 0 < N) (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) (hlam : lamEnc T d N rad = some lamI) {X : IV 128}
    (hX : IV.posB X = true) (hlX : IV.Mem Calibration.l X) {nR nL : Tup}
    (hnR : IV.Mem (Trunc.f₀ R₀) nR.f0 ∧ IV.Mem (Trunc.e R₀) nR.e0) (hnL : IV.Mem (Trunc.f₀ Calibration.l) nL.f0)
    (hchk6 : a6Check d.pi d.r0 (IV.addRad nL.f0 rad) (IV.addRad nR.f0 rad) (IV.addRad nR.e0 rad)
      (IV.addRad (basis d 5 X).bsum.c0 rad) lamI = true)
    -- the derivative rectangles A7
    {A : A7Data} {a7 : ℕ → ℝ} (DE : A7Env A a7) (hnj : 0 < A.nj) (hnk : 0 < A.nk)
    (hdp0 : (A.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b) (hsp0 : A.sp 0 = 0) (hrows7 : ∀ j < A.nj, A.row j A.nk = true)
    -- the `K` row
    (KG : KGrid) {ShK ρd ρx δ Kc : ℝ}
    (hKrow : KG.row E = true) (hdK : (KG.dm : ℝ) / 2 ^ 128 ∈ Icc Calibration.b (697 / 1000 : ℝ))
    (hKs0 : KG.sm 0 = 0) (hKtop : sg KG.sm KG.nx ≤ 65 / 100)
    (hKstep : ∀ k < KG.nx, sg KG.sm (k + 1) - sg KG.sm k ≤ ShK)
    (hρd0 : 0 ≤ ρd) (hρd1 : 0 ≤ (KG.dm : ℝ) / 2 ^ 128 - ρd) (hρd2 : ((KG.dm : ℝ) / 2 ^ 128 - ρd) ^ 4 ≤ 1 / 12)
    (hρd3 : (1 : ℝ) / 12 ≤ ((KG.dm : ℝ) / 2 ^ 128 + ρd) ^ 4)
    (hρx1 : 0 ≤ sg KG.sm KG.nx - ρx) (hρx2 : (sg KG.sm KG.nx - ρx) ^ 4 ≤ 1 / 108)
    (hρx3 : (1 : ℝ) / 108 ≤ sg KG.sm KG.nx ^ 4)
    (hKc : 2 * ((KG.thr.toInt : ℝ) / 2 ^ 256 + δ * sg KG.sm KG.nx + A.c4 * ShK ^ 2 * sg KG.sm KG.nx / 24 +
      (A.c2 * ρx ^ 2 / 2 + A.c1 * ρd * ρx + 65 / 100 * A.c3 * ρd ^ 2 / 2)) ≤ Kc)
    (hδ0 : 0 ≤ δ) (hδ : deltaData rf re lamI piI r0I f0lI f0RI eRI blI lsqI ≤ δ)
    -- the outer grid
    (G : OuterGrid) {Sh Dh ρ : ℝ}
    (hOdpn : sg G.dm G.nd ≤ (A.dp A.nj : ℝ) / 2 ^ 128) (hOspn : sg G.sm G.nx ≤ (A.sp A.nk : ℝ) / 2 ^ 128)
    (hOdm : ∀ j < G.nd, G.dm j ≤ G.dm (j + 1)) (hOdlo : Calibration.b ≤ sg G.dm 0)
    (hOdρ : sg G.dm 0 - Calibration.b ≤ ρ) (hOdstep : ∀ j < G.nd, sg G.dm (j + 1) - sg G.dm j ≤ Dh)
    (hOdtop : (697 : ℝ) / 1000 ≤ sg G.dm G.nd) (hOd1 : sg G.dm G.nd ≤ 1)
    (hOs0 : G.sm 0 = 0) (hOsm : ∀ k < G.nx, G.sm k ≤ G.sm (k + 1))
    (hOxstep : ∀ k < G.nx, sg G.sm (k + 1) - sg G.sm k ≤ Sh) (hOxtop : (65 : ℝ) / 100 ≤ sg G.sm G.nx)
    (hjl : 0 < G.jl) (hjlr : G.jl ≤ G.nd) (hjr : G.jr < G.nd) (hkl : 0 < G.kl) (hklr : G.kl ≤ G.nx)
    (hkr : G.kr < G.nx) (hD1 : (52528 : ℝ) / 100000 ≤ sg G.dm G.jl) (hD2 : sg G.dm G.jr ≤ 54930 / 100000)
    (hX1 : (29420 : ℝ) / 100000 ≤ sg G.sm G.kl) (hX2 : sg G.sm G.kr ≤ 32621 / 100000)
    (hOrows : ∀ j ≤ G.nd, G.row E j = true)
    (hOthr : Kc + 2 * A.c2 * Sh ^ 2 / 8 + 2 * sg G.sm G.nx * A.c3 * Dh ^ 2 / 8 + 2 * sg G.sm G.nx * A.c1 * ρ +
      (A.c4 * Sh ^ 2 / 12 + 2 * δ) * sg G.sm G.nx ≤ (G.thr.toInt : ℝ) / 2 ^ 256)
    -- the negative-part grid
    (Gr : NegGrid) {Sh' Dh' : ℝ}
    (hNdpn : sg Gr.dm Gr.nd ≤ (A.dp A.nj : ℝ) / 2 ^ 128) (hNspn : sg Gr.sm Gr.nx ≤ (A.sp A.nk : ℝ) / 2 ^ 128)
    (hNdm : ∀ j < Gr.nd, Gr.dm j ≤ Gr.dm (j + 1)) (hNdlo : Calibration.b ≤ sg Gr.dm 0)
    (hNdnear : sg Gr.dm 0 ≤ Calibration.b + Dh' / 2)
    (hNdstep : ∀ j < Gr.nd, sg Gr.dm (j + 1) - sg Gr.dm j ≤ Dh')
    (hNdtop : (697 : ℝ) / 1000 ≤ sg Gr.dm Gr.nd) (hNd1 : sg Gr.dm Gr.nd ≤ 1)
    (hNs0 : Gr.sm 0 = 0) (hNsm : ∀ k < Gr.nx, Gr.sm k ≤ Gr.sm (k + 1))
    (hNxstep : ∀ k < Gr.nx, sg Gr.sm (k + 1) - sg Gr.sm k ≤ Sh') (hNxtop : (65 : ℝ) / 100 ≤ sg Gr.sm Gr.nx)
    (hNrows : ∀ j ≤ Gr.nd, Gr.row E j = true)
    (hNthr : (Gr.thr.toInt : ℝ) / 2 ^ 256 + (δ + A.c2 * Sh' / 4) * sg Gr.sm Gr.nx +
      sg Gr.sm Gr.nx * A.c1 * Dh' / 2 + Kc ≤ 0)
    -- the Hessian rows A10
    {H : HessData} {a' : ℕ → ℝ} (HE : HessEnv H a') (hdpn7 : (697 : ℝ) / 1000 ≤ (A.dp A.nj : ℝ) / 2 ^ 128)
    (hspn7 : (65 : ℝ) / 100 ≤ (A.sp A.nk : ℝ) / 2 ^ 128)
    (hnd : 0 < H.nd) (hjn : H.jmin < H.nx) (hhdp0 : Calibration.b ≤ dpt H 0) (hhsp0 : H.sp 0 = 0)
    (hhrows : H.rows H.nd = true) (hd_lo : dpt H 0 ≤ 52528 / 100000) (hd_hi : (54930 : ℝ) / 100000 ≤ dpt H H.nd)
    (hx_lo : sgm H H.jmin ≤ 29420 / 100000) (hx_hi : (32621 : ℝ) / 100000 ≤ sgm H H.nx) :
    Assembly.CertificateGoal := by
  obtain ⟨hfl, hsl⟩ := f_l_pos_slope_pos_of_certificate fc hd hp2 hT hN hrad hlam hX hlX hnR hnL hchk6
  exact ⟨hfl, hsl,
    outer_of_certificate P fc hchk DE G KG hnj hnk hdp0 hOdpn hsp0 hOspn hrows7 hOdm hOdlo hOdρ hOdstep hOdtop hOd1
      hOs0 hOsm hOxstep hOxtop hjl hjlr hjr hkl hklr hkr hD1 hD2 hX1 hX2 hOrows hKrow hdK hKs0 hKtop hKstep hρd0
      hρd1 hρd2 hρd3 hρx1 hρx2 hρx3 hKc hδ0 hδ hOthr,
    inner_of_certificate DE HE hnj hnk hdp0 hdpn7 hsp0 hspn7 hrows7 hnd hjn hhdp0 hhsp0 hhrows hd_lo hd_hi hx_lo hx_hi,
    negative_of_certificate P fc hchk DE Gr KG hnj hnk hdp0 hNdpn hsp0 hNspn hrows7 hNdm hNdlo hNdnear hNdstep hNdtop
      hNd1 hNs0 hNsm hNxstep hNxtop hNrows hKrow hdK hKs0 hKtop hKstep hρd0 hρd1 hρd2 hρd3 hρx1 hρx2 hρx3 hKc hδ
      hNthr⟩

end SandierSerfaty.Certificate.Box
