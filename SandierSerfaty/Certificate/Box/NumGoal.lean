/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Goal
public import SandierSerfaty.Certificate.Box.NumCheck
public import SandierSerfaty.Certificate.Box.NumScalar

/-!
# `CertificateGoal` from Boolean checks only

`certificateGoal_of_checks` is `Box.certificateGoal_of_data` with every numeric side condition (grid steps,
monotonicity, comparisons with rational literals, the fourth-power closeness facts, the thresholds `hKc`, `hthr`,
`hNthr` and `deltaData ≤ δ`) replaced by a `Bool` that `decide +kernel` evaluates on the literal data (`a7B`, `outerGridB`,
`negGridB`, `kRowB`, `hessB`, `kcB`, `outThrB`, `negThrB`, `deltaB`). The free real parameters of the assertions are the
rational literals of `NumFree` (steps `sh/2^128`, …) and `δ, Kc : ℚ`; no `norm_num` on casts of literals remains.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Certificate.Basis SandierSerfaty.Calibration SandierSerfaty.Tails

theorem lt_of_blt {a b : ℕ} (h : Nat.blt a b = true) : a < b := Nat.le_of_ble_eq_true h

theorem natle_div{a b : ℕ} (h : Nat.ble a b = true) : (a : ℝ) / 2 ^ 128 ≤ (b : ℝ) / 2 ^ 128 :=
  div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_of_ble_eq_true h) (by positivity)

theorem natle_one {a : ℕ} (h : Nat.ble a bigP = true) : (a : ℝ) / 2 ^ 128 ≤ 1 := by
  have := natle_div h
  rw [cast_bigP] at this
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  rwa [div_self hN.ne'] at this

theorem leLit' {m num den : ℕ} (hd : 0 < den) (h : leLitB m num den = true) {x : ℝ}
    (hx : x = (num : ℝ) / den) : (m : ℝ) / 2 ^ 128 ≤ x := hx ▸ leLitB_sound hd h

theorem geLit' {m num den : ℕ} (hd : 0 < den) (h : geLitB m num den = true) {x : ℝ}
    (hx : x = (num : ℝ) / den) : x ≤ (m : ℝ) / 2 ^ 128 := hx ▸ geLitB_sound hd h

theorem le_b {m : ℕ} (h : leLitB m 28209 100000 = true) : (m : ℝ) / 2 ^ 128 ≤ Calibration.b :=
  leLit' (by norm_num) h (by unfold Calibration.b; norm_num)

theorem b_le {m : ℕ} (h : geLitB m 28209 100000 = true) : Calibration.b ≤ (m : ℝ) / 2 ^ 128 :=
  geLit' (by norm_num) h (by unfold Calibration.b; norm_num)

theorem sub_b_le {m r : ℕ} (h : subLeB m 28209 100000 r = true) :
    (m : ℝ) / 2 ^ 128 - Calibration.b ≤ (r : ℝ) / 2 ^ 128 := by
  have := subLeB_sound (by norm_num) h
  have hb : Calibration.b = ((28209 : ℕ) : ℝ) / ((100000 : ℕ) : ℝ) := by unfold Calibration.b; norm_num
  rwa [hb]

theorem near_b {m r : ℕ} (h : nearB m 28209 100000 r = true) :
    (m : ℝ) / 2 ^ 128 ≤ Calibration.b + ((r : ℝ) / 2 ^ 128) / 2 := by
  have := nearB_sound (by norm_num) h
  have hb : Calibration.b = ((28209 : ℕ) : ℝ) / ((100000 : ℕ) : ℝ) := by unfold Calibration.b; norm_num
  rwa [hb]

theorem close_p {m r : ℕ} (h : closeLoB m r 12 = true) (h' : closeHiB m r 12 = true) :
    0 ≤ (m : ℝ) / 2 ^ 128 - (r : ℝ) / 2 ^ 128 ∧ ((m : ℝ) / 2 ^ 128 - (r : ℝ) / 2 ^ 128) ^ 4 ≤ 1 / 12 ∧
      (1 : ℝ) / 12 ≤ ((m : ℝ) / 2 ^ 128 + (r : ℝ) / 2 ^ 128) ^ 4 := by
  obtain ⟨a, b⟩ := closeLoB_sound (by norm_num) h
  have c := closeHiB_sound (by norm_num) h'
  exact ⟨a, by simpa using b, by simpa using c⟩

theorem close_x {m r : ℕ} (h : closeLoB m r 108 = true) (h' : closeHiB m 0 108 = true) :
    0 ≤ (m : ℝ) / 2 ^ 128 - (r : ℝ) / 2 ^ 128 ∧ ((m : ℝ) / 2 ^ 128 - (r : ℝ) / 2 ^ 128) ^ 4 ≤ 1 / 108 ∧
      (1 : ℝ) / 108 ≤ ((m : ℝ) / 2 ^ 128) ^ 4 := by
  obtain ⟨a, b⟩ := closeLoB_sound (by norm_num) h
  have c := closeHiB_sound (by norm_num) h'
  exact ⟨a, by simpa using b, by simpa using c⟩

/-- **The five fields of the certificate goal from Boolean checks.** -/
theorem certificateGoal_of_checks {E : EvalData} {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI) (fc : FiniteCore)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    -- the exterior signs (A4–A6)
    {d : BasisData} (hd : d.Valid) (hp2 : IV.posB d.p2 = true) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {N rad : ℕ}
    (hN : 0 < N) (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) (hlam : lamEnc T d N rad = some lamI) {X : IV 128}
    (hX : IV.posB X = true) (hlX : IV.Mem Calibration.l X) {nR nL : Tup}
    (hnR : IV.Mem (Trunc.f₀ R₀) nR.f0 ∧ IV.Mem (Trunc.e R₀) nR.e0) (hnL : IV.Mem (Trunc.f₀ Calibration.l) nL.f0)
    (hchk6 : a6Check d.pi d.r0 (IV.addRad nL.f0 rad) (IV.addRad nR.f0 rad) (IV.addRad nR.e0 rad)
      (IV.addRad (basis d 5 X).bsum.c0 rad) lamI = true)
    -- the table realizations
    {A : A7Data} {a7 : ℕ → ℝ} (DE : A7Env A a7) {H : HessData} {a' : ℕ → ℝ} (HE : HessEnv H a')
    -- the literal grids and parameters
    (G : OuterGrid) (Gr : NegGrid) (KG : KGrid) (par : NumFree) (δ Kc : ℚ)
    -- the Boolean checks
    (hA : a7B A = true) (hO : outerGridB A G E par = true) (hNg : negGridB A Gr E par = true) (hK : kRowB KG E par = true)
    (hH : hessB H = true)
    (hkc : kcB A.L1 A.L2 A.L3 A.L4 KG.thr.toInt (KG.sm KG.nx) par.kSh par.kRd par.kRx δ Kc = true)
    (hthr : outThrB A.L1 A.L2 A.L3 A.L4 G.thr.toInt (G.sm G.nx) par.oSh par.oDh par.oRho δ Kc = true)
    (hnthr : negThrB A.L1 A.L2 Gr.thr.toInt (Gr.sm Gr.nx) par.nSh par.nDh δ Kc = true)
    (hdel : deltaB rf re lamI piI r0I f0lI f0RI eRI blI lsqI δ = true) :
    Assembly.CertificateGoal := by
  simp only [a7B, andL, Bool.and_true, Bool.and_eq_true] at hA
  obtain ⟨hnj, hnk, hdp0, hsp0, hrows7, hdpn7, hspn7⟩ := hA
  simp only [outerGridB, andL, Bool.and_true, Bool.and_eq_true] at hO
  obtain ⟨hOdpn, hOspn, hOdm, hOdlo, hOdρ, hOdstep, hOdtop, hOd1, hOs0, hOsm, hOxstep, hOxtop, hjl, hjlr, hjr, hkl,
    hklr, hkr, hD1, hD2, hX1, hX2, hOrows⟩ := hO
  simp only [negGridB, andL, Bool.and_true, Bool.and_eq_true] at hNg
  obtain ⟨hNdpn, hNspn, hNdm, hNdlo, hNdnear, hNdstep, hNdtop, hNd1, hNs0, hNsm, hNxstep, hNxtop, hNrows⟩ := hNg
  simp only [kRowB, andL, Bool.and_true, Bool.and_eq_true] at hK
  obtain ⟨hKrow, hKd1, hKd2, hKs0, hKtop, hKstep, hKlo, hKhi, hKxlo, hKxhi⟩ := hK
  simp only [hessB, andL, Bool.and_true, Bool.and_eq_true] at hH
  obtain ⟨hnd, hjn, hhdp0, hhsp0, hhrows, hd_lo, hd_hi, hx_lo, hx_hi⟩ := hH
  obtain ⟨hδ0, hδ⟩ := deltaB_sound hdel
  obtain ⟨hρd1, hρd2, hρd3⟩ := close_p hKlo hKhi
  obtain ⟨hρx1, hρx2, hρx3⟩ := close_x hKxlo hKxhi
  refine certificateGoal_of_data (ShK := (par.kSh : ℝ) / 2 ^ 128) (ρd := (par.kRd : ℝ) / 2 ^ 128)
    (ρx := (par.kRx : ℝ) / 2 ^ 128) (δ := (δ : ℝ)) (Kc := (Kc : ℝ)) (Sh := (par.oSh : ℝ) / 2 ^ 128)
    (Dh := (par.oDh : ℝ) / 2 ^ 128) (ρ := (par.oRho : ℝ) / 2 ^ 128) (Sh' := (par.nSh : ℝ) / 2 ^ 128)
    (Dh' := (par.nDh : ℝ) / 2 ^ 128) P fc hchk hd hp2 hT hN hrad hlam hX hlX hnR hnL hchk6 DE
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
    (negThrB_sound A Gr hnthr) HE (geLit' (by norm_num) hdpn7 (by norm_num))
    (geLit' (by norm_num) hspn7 (by norm_num)) (lt_of_blt hnd) (lt_of_blt hjn) (b_le hhdp0)
    (Nat.eq_of_beq_eq_true hhsp0) hhrows (leLit' (by norm_num) hd_lo (by norm_num))
    (geLit' (by norm_num) hd_hi (by norm_num)) (leLit' (by norm_num) hx_lo (by norm_num))
    (geLit' (by norm_num) hx_hi (by norm_num))

end SandierSerfaty.Certificate.Box
