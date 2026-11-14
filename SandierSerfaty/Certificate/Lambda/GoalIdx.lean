/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumGoal
public import SandierSerfaty.Certificate.Lambda.Sound
public import SandierSerfaty.Certificate.Lambda.Model
public import SandierSerfaty.Certificate.Box.CertIdx
public import SandierSerfaty.Certificate.Box.NumCheckIdx

/-!
# The certificate goal from Boolean checks and the table model

The final assembly of the certificate: the fine `λ` in the box layer (`Lambda.lamFine`) and
the checked-index lookup in the A7 and Hessian checks.

* `certificateGoal_of_dataI`: `Box.certificateGoal_of_data` with separate enclosures of `λ` for A6 and for the box
  layer, the A7 rows `A7Data.rowI A ix` and the Hessian rows
  `HessData.rowsI H hix` (`Box.outer_of_certificateI`, `Box.negative_of_certificateI`,
  `Box.inner_of_certificateI`);
* `certificateGoal_of_checks''`: **`Assembly.CertificateGoal` from the Boolean checks and the realization of the
  table by the segment models** (`Lambda.TableModel`, produced from the table shards by
  `Assemble.tableModel_of_checks`). The premises are: the finite-core premise, the table model, the enclosures of
  the primitive constants (`π`, `R₀`, `l`, `l²`, `f₀(l)`, `f₀(R₀)`, `e(R₀)`, `B(l)`, and the node tuples at `R₀`, `l`),
  the validity of the basis constants, the identification of the literal data (the A7 and Hessian data read the
  table of the model and the enclosures of the constants), and Boolean checks. Every realization the layers consume
  is derived inside: `Box.TableRealized`, `Box.Encl2` (`A7Env`, `HessEnv`), `ITable.Encl` (the exterior signs),
  `Lambda.FRealized` (the fine `λ`) and `Box.QRealizes` (the query cells, from `cellCheck` on every cell).

The earlier variant `Box.certificateGoal_of_checks` is kept (the primed `Lambda.certificateGoal_of_data'`,
`Lambda.certificateGoal_of_checks'` were removed by the dead-code sweep DEAD-1).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Box SandierSerfaty.Calibration SandierSerfaty.Tails

/-- **The five fields of the certificate goal from the finite data**, with separate enclosures of `λ` and the checked-index A7 rows `A7Data.rowI A ix` and Hessian rows `HessData.rowsI H hix`. -/
theorem certificateGoal_of_dataI {E : EvalData} {rf re : ℕ} {lamA lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI) (fc : FiniteCore)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    -- the exterior signs (A4–A6)
    {d : BasisData} (hd : d.Valid) (hp2 : IV.posB d.p2 = true) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {N rad : ℕ}
    (hN : 0 < N) (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) (hlam : lamEnc T d N rad = some lamA) {X : IV 128}
    (hX : IV.posB X = true) (hlX : IV.Mem Calibration.l X) {nR nL : Tup}
    (hnR : IV.Mem (Trunc.f₀ R₀) nR.f0 ∧ IV.Mem (Trunc.e R₀) nR.e0) (hnL : IV.Mem (Trunc.f₀ Calibration.l) nL.f0)
    (hchk6 : a6Check d.pi d.r0 (IV.addRad nL.f0 rad) (IV.addRad nR.f0 rad) (IV.addRad nR.e0 rad)
      (IV.addRad (basis d 5 X).bsum.c0 rad) lamA = true)
    -- the derivative rectangles A7
    {A : A7Data} (ix : Nat → Nat → Nat × Nat) {a7 : ℕ → ℝ} (DE : A7Env A a7) (hnj : 0 < A.nj) (hnk : 0 < A.nk)
    (hdp0 : (A.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b) (hsp0 : A.sp 0 = 0) (hrows7 : ∀ j < A.nj, A.rowI ix j A.nk = true)
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
    {H : HessData} (hix : Nat → Nat → Nat × Nat) {a' : ℕ → ℝ} (HE : HessEnv H a') (hdpn7 : (697 : ℝ) / 1000 ≤ (A.dp A.nj : ℝ) / 2 ^ 128)
    (hspn7 : (65 : ℝ) / 100 ≤ (A.sp A.nk : ℝ) / 2 ^ 128)
    (hnd : 0 < H.nd) (hjn : H.jmin < H.nx) (hhdp0 : Calibration.b ≤ dpt H 0) (hhsp0 : H.sp 0 = 0)
    (hhrows : H.rowsI hix H.nd = true) (hd_lo : dpt H 0 ≤ 52528 / 100000) (hd_hi : (54930 : ℝ) / 100000 ≤ dpt H H.nd)
    (hx_lo : sgm H H.jmin ≤ 29420 / 100000) (hx_hi : (32621 : ℝ) / 100000 ≤ sgm H H.nx) :
    Assembly.CertificateGoal := by
  obtain ⟨hfl, hsl⟩ := f_l_pos_slope_pos_of_certificate fc hd hp2 hT hN hrad hlam hX hlX hnR hnL hchk6
  exact ⟨hfl, hsl,
    outer_of_certificateI P fc hchk ix DE G KG hnj hnk hdp0 hOdpn hsp0 hOspn hrows7 hOdm hOdlo hOdρ hOdstep hOdtop hOd1
      hOs0 hOsm hOxstep hOxtop hjl hjlr hjr hkl hklr hkr hD1 hD2 hX1 hX2 hOrows hKrow hdK hKs0 hKtop hKstep hρd0
      hρd1 hρd2 hρd3 hρx1 hρx2 hρx3 hKc hδ0 hδ hOthr,
    inner_of_certificateI ix DE hix HE hnj hnk hdp0 hdpn7 hsp0 hspn7 hrows7 hnd hjn hhdp0 hhsp0 hhrows hd_lo hd_hi hx_lo hx_hi,
    negative_of_certificateI P fc hchk ix DE Gr KG hnj hnk hdp0 hNdpn hsp0 hNspn hrows7 hNdm hNdlo hNdnear hNdstep hNdtop
      hNd1 hNs0 hNsm hNxstep hNxtop hNrows hKrow hdK hKs0 hKtop hKstep hρd0 hρd1 hρd2 hρd3 hρx1 hρx2 hρx3 hKc hδ
      hNthr⟩

/-- **The certificate goal from the Boolean checks and the table model.** The premises are the finite-core
premise, the realization `TableModel FL aL` of the table by the segment models, the enclosures of the primitive
constants and of the node values at `R₀`, `l`, the validity of the basis constants, the identification of the literal
data (`A`, `H` read the table `FL.T` and the constant enclosures; their widening `rad ≥ 10⁻¹¹ 2^128`), and Boolean
checks: the query cells against the table (`cellCheck`), the evaluator test, the coarse `λ` and the exterior test
A6, the fine `λ` (`lamFine`), the A7 rectangles and Hessian rows with the checked index (`a7BI`, `hessBI`), the outer,
negative-part and `K` rows, and the scalar inequalities. -/
theorem certificateGoal_of_checks'' {E : EvalData} {rf re : ℕ}
    {lamA lamI piI r0I f0lI f0RI eRI blI lsqI lI : IV 128} (fc : FiniteCore)
    -- the table, realized by the segment models
    {FL : FTable} {aL : ℕ → ℝ} (hTM : TableModel FL aL)
    -- the enclosures of the primitive constants
    (hpi : IV.Mem Real.pi piI) (hr0 : IV.Mem R₀ r0I) (hf0l : IV.Mem (f₀ Calibration.l) f0lI)
    (hf0R : IV.Mem (f₀ R₀) f0RI) (heR : IV.Mem (e R₀) eRI) (hbl : IV.Mem (B Calibration.l) blI)
    (hlsq : IV.Mem (Calibration.l ^ 2) lsqI) (hl : IV.Mem Calibration.l lI)
    -- the basis constants
    {d : BasisData} (hd : d.Valid) (hp2 : IV.posB d.p2 = true)
    -- the exterior signs (A4–A6) on the table of the model, with the coarse `λ`
    {N rad : ℕ} (hN : 0 < N) (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) (hlam : lamEnc FL.T d N rad = some lamA)
    {X : IV 128} (hX : IV.posB X = true) (hlX : IV.Mem Calibration.l X) {nR nL : Tup}
    (hnR : IV.Mem (Trunc.f₀ R₀) nR.f0 ∧ IV.Mem (Trunc.e R₀) nR.e0) (hnL : IV.Mem (Trunc.f₀ Calibration.l) nL.f0)
    (hchk6 : a6Check d.pi d.r0 (IV.addRad nL.f0 rad) (IV.addRad nR.f0 rad) (IV.addRad nR.e0 rad)
      (IV.addRad (basis d 5 X).bsum.c0 rad) lamA = true)
    -- the fine `λ` of the box layer on the table of the model
    {PL : LamPar} (hradL : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ PL.rad) (hfine : lamFine FL d PL = some lamI)
    -- the A7 and Hessian data read the table of the model and the constant enclosures
    {A : A7Data} (hAT : A.T = FL.T) (hAf : A.f0lI = f0lI) (hAk : A.k0I = IV.neg (IV.mul piI blI))
    (hAs : A.lsqI = lsqI) (hAl : A.lI = lI) (hAlam : A.lamI = lamI) (hAmu : A.muI = muEnc r0I f0RI eRI lamI)
    (hArad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ A.rad)
    {H : HessData} (hHT : H.T = FL.T) (hHf : H.f0lI = f0lI) (hHk : H.k0I = IV.neg (IV.mul piI blI))
    (hHs : H.lsqI = lsqI) (hHl : H.lI = lI) (hHlam : H.lamI = lamI) (hHmu : H.muI = muEnc r0I f0RI eRI lamI)
    (hHrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ H.rad)
    -- the literal grids, parameters and index ranges
    (G : OuterGrid) (Gr : NegGrid) (KG : KGrid) (par : NumFree) (δ Kc : ℚ) (ix hix : Nat → Nat → Nat × Nat)
    -- the Boolean checks
    (hqn : Nat.ble E.T.n FL.T.n = true)
    (hqc : allLt (fun i => cellCheck (FL.T.node i) (FL.T.node (Nat.succ i)) (FL.T.cell i) (FL.nt i) (E.T.cell i)
      rf re) E.T.n = true)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    (hA : a7BI A ix = true) (hO : outerGridB A G E par = true) (hNg : negGridB A Gr E par = true)
    (hK : kRowB KG E par = true) (hH : hessBI H hix = true)
    (hkc : kcB A.L1 A.L2 A.L3 A.L4 KG.thr.toInt (KG.sm KG.nx) par.kSh par.kRd par.kRx δ Kc = true)
    (hthr : outThrB A.L1 A.L2 A.L3 A.L4 G.thr.toInt (G.sm G.nx) par.oSh par.oDh par.oRho δ Kc = true)
    (hnthr : negThrB A.L1 A.L2 Gr.thr.toInt (Gr.sm Gr.nx) par.nSh par.nDh δ Kc = true)
    (hdel : deltaB rf re lamI piI r0I f0lI f0RI eRI blI lsqI δ = true) :
    Assembly.CertificateGoal := by
  have hE2 : Encl2 FL.T aL := hTM.tableRealized.encl2 fc
  have hT : FL.T.Encl aL := hTM.tableRealized.encl fc
  have hQ : QRealizes E.T rf re :=
    hTM.qRealizes (Nat.le_of_ble_eq_true hqn) fun i hi => (allLt_iff.1 hqc) i hi
  have hlamI : IV.Mem lam lamI := lamFine_sound fc hTM.fRealized hd hradL hfine
  have hmu : IV.Mem mu (muEnc r0I f0RI eRI lamI) := muEnc_mem hr0 hf0R heR hlamI
  have hk0 : IV.Mem (-(Real.pi * B Calibration.l)) (IV.neg (IV.mul piI blI)) := IV.mem_neg (IV.mem_mul hpi hbl)
  have DE : A7Env A aL := ⟨fc, by rw [hAT]; exact hE2, hArad, by rw [hAl]; exact hl, by rw [hAf]; exact hf0l,
    by rw [hAk]; exact hk0, by rw [hAs]; exact hlsq, by rw [hAlam]; exact hlamI, by rw [hAmu]; exact hmu⟩
  have HE : HessEnv H aL := ⟨fc, by rw [hHT]; exact hE2, hHrad, by rw [hHl]; exact hl, by rw [hHf]; exact hf0l,
    by rw [hHk]; exact hk0, by rw [hHs]; exact hlsq, by rw [hHlam]; exact hlamI, by rw [hHmu]; exact hmu⟩
  have P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI :=
    ⟨hQ, hlamI, hpi, hr0, hf0l, hf0R, heR, hbl, hlsq⟩
  simp only [a7BI, andL, Bool.and_true, Bool.and_eq_true] at hA
  obtain ⟨hnj, hnk, hdp0, hsp0, hrows7, hdpn7, hspn7⟩ := hA
  simp only [outerGridB, andL, Bool.and_true, Bool.and_eq_true] at hO
  obtain ⟨hOdpn, hOspn, hOdm, hOdlo, hOdρ, hOdstep, hOdtop, hOd1, hOs0, hOsm, hOxstep, hOxtop, hjl, hjlr, hjr, hkl,
    hklr, hkr, hD1, hD2, hX1, hX2, hOrows⟩ := hO
  simp only [negGridB, andL, Bool.and_true, Bool.and_eq_true] at hNg
  obtain ⟨hNdpn, hNspn, hNdm, hNdlo, hNdnear, hNdstep, hNdtop, hNd1, hNs0, hNsm, hNxstep, hNxtop, hNrows⟩ := hNg
  simp only [kRowB, andL, Bool.and_true, Bool.and_eq_true] at hK
  obtain ⟨hKrow, hKd1, hKd2, hKs0, hKtop, hKstep, hKlo, hKhi, hKxlo, hKxhi⟩ := hK
  simp only [hessBI, andL, Bool.and_true, Bool.and_eq_true] at hH
  obtain ⟨hnd, hjn, hhdp0, hhsp0, hhrows, hd_lo, hd_hi, hx_lo, hx_hi⟩ := hH
  obtain ⟨hδ0, hδ⟩ := deltaB_sound hdel
  obtain ⟨hρd1, hρd2, hρd3⟩ := close_p hKlo hKhi
  obtain ⟨hρx1, hρx2, hρx3⟩ := close_x hKxlo hKxhi
  refine certificateGoal_of_dataI (ShK := (par.kSh : ℝ) / 2 ^ 128) (ρd := (par.kRd : ℝ) / 2 ^ 128)
    (ρx := (par.kRx : ℝ) / 2 ^ 128) (δ := (δ : ℝ)) (Kc := (Kc : ℝ)) (Sh := (par.oSh : ℝ) / 2 ^ 128)
    (Dh := (par.oDh : ℝ) / 2 ^ 128) (ρ := (par.oRho : ℝ) / 2 ^ 128) (Sh' := (par.nSh : ℝ) / 2 ^ 128)
    (Dh' := (par.nDh : ℝ) / 2 ^ 128) P fc hchk hd hp2 hT hN hrad hlam hX hlX hnR hnL hchk6 ix DE
    (lt_of_blt hnj) (lt_of_blt hnk) (le_b hdp0) (Nat.eq_of_beq_eq_true hsp0)
    (fun j hj => (allLt_iff.1 hrows7) j hj) KG hKrow ⟨b_le hKd1, leLit' (by norm_num) hKd2 (by norm_num)⟩
    (Nat.eq_of_beq_eq_true hKs0) (leLit' (by norm_num) hKtop (by norm_num)) (stepB_sound hKstep)
    (by positivity) hρd1 hρd2 hρd3 hρx1 hρx2 hρx3 (kcB_sound A KG hkc) hδ0 hδ G (natle_div hOdpn) (natle_div hOspn)
    (monoB_sound hOdm) (b_le hOdlo) (sub_b_le hOdρ) (stepB_sound hOdstep)
    (geLit' (by norm_num) hOdtop (by norm_num)) (natle_one hOd1) (Nat.eq_of_beq_eq_true hOs0) (monoB_sound hOsm)
    (stepB_sound hOxstep) (geLit' (by norm_num) hOxtop (by norm_num)) (lt_of_blt hjl)
    (Nat.le_of_ble_eq_true hjlr) (lt_of_blt hjr) (lt_of_blt hkl)
    (Nat.le_of_ble_eq_true hklr) (lt_of_blt hkr) (geLit' (by norm_num) hD1 (by norm_num))
    (leLit' (by norm_num) hD2 (by norm_num)) (geLit' (by norm_num) hX1 (by norm_num))
    (leLit' (by norm_num) hX2 (by norm_num)) (fun j hj => (allLt_iff.1 hOrows) j (Nat.lt_succ_of_le hj))
    (outThrB_sound A G hthr) Gr (natle_div hNdpn) (natle_div hNspn) (monoB_sound hNdm) (b_le hNdlo) (near_b hNdnear)
    (stepB_sound hNdstep) (geLit' (by norm_num) hNdtop (by norm_num)) (natle_one hNd1)
    (Nat.eq_of_beq_eq_true hNs0) (monoB_sound hNsm) (stepB_sound hNxstep)
    (geLit' (by norm_num) hNxtop (by norm_num)) (fun j hj => (allLt_iff.1 hNrows) j (Nat.lt_succ_of_le hj))
    (negThrB_sound A Gr hnthr) hix HE (geLit' (by norm_num) hdpn7 (by norm_num))
    (geLit' (by norm_num) hspn7 (by norm_num)) (lt_of_blt hnd) (lt_of_blt hjn) (b_le hhdp0)
    (Nat.eq_of_beq_eq_true hhsp0) hhrows (leLit' (by norm_num) hd_lo (by norm_num))
    (geLit' (by norm_num) hd_hi (by norm_num)) (leLit' (by norm_num) hx_lo (by norm_num))
    (geLit' (by norm_num) hx_hi (by norm_num))

end SandierSerfaty.Certificate.Lambda
