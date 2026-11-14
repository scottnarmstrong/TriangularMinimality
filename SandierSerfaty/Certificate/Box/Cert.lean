/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.EvalData
public import SandierSerfaty.Certificate.Box.KBound
public import SandierSerfaty.Certificate.Box.Negative
public import SandierSerfaty.Certificate.Box.Inner

/-!
# The outer and negative-part assertions from the certificate data (A8, A9; theorems T2, T3)

`CertPrem` collects the premises tying the exact calibration objects to the literal enclosures of the query layer
(`FiniteCore`, the realization of the query table by the table chunks, `λ`, `π`, `R₀`, `f₀(l)`, `f₀(R₀)`, `e(R₀)`,
`B(l)`, `l²`); from it and one Boolean test (`evalCheckOf`) the hypotheses of the box evaluator follow
(`CertPrem.evalHyp`). The remaining hypotheses are finite facts about the literal data (grids, thresholds): decidable
inequalities between rationals and the row checks.

* `outer_of_certificate`: `∀ q ∈ boxD ∖ int boxD₀, K ≤ 2 g q.1 q.2` (`comp:outer-assertion`). The derivative bounds
  come from the A7 rows (`Box.derivBounds_of_env`), `K ≤ Kc` from the `K` row (`Box.K_le_of_row`).
* `negative_of_certificate`: `∀ d ∈ [b, .697], ∫₀^{.65} max 0 (-G d s) ds ≤ -K` (`comp:negative-assertion`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The enclosure of `c = f(l) - κ l²`. -/
@[expose] def cEnc (r0 f0l f0R eR lamI pi bl lsq : IV 128) : IV 128 :=
  IV.sub (fLEnc r0 f0l f0R eR lamI) (IV.mul (slopeEnc pi bl lamI) lsq)

/-- **The Boolean test of the evaluator data** on the enclosures built from the primitives. -/
@[expose] def evalCheckOf (E : EvalData) (lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128) (rf re : Nat) : Bool :=
  evalHypCheck E lamI (muEnc r0I f0RI eRI lamI) (slopeEnc piI blI lamI) (cEnc r0I f0lI f0RI eRI lamI piI blI lsqI)
    lsqI rf re

/-- The error budget `deltaMax` of the evaluator on the data. -/
@[expose] noncomputable def deltaData (rf re : ℕ) (lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128) : ℝ :=
  deltaMax rf re (widthR lamI) (widthR (muEnc r0I f0RI eRI lamI)) (widthR (slopeEnc piI blI lamI))
    (widthR (cEnc r0I f0lI f0RI eRI lamI piI blI lsqI))

/-- **The premises of the evaluator**: the exact calibration objects against the literal enclosures. -/
structure CertPrem (E : EvalData) (rf re : ℕ) (lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128) : Prop where
  /-- The query table is realized by the table chunks. -/
  hQ : QRealizes E.T rf re
  /-- `λ`. -/
  hlam : IV.Mem Calibration.lam lamI
  /-- `π`. -/
  hpi : IV.Mem Real.pi piI
  /-- `R₀`. -/
  hr0 : IV.Mem R₀ r0I
  /-- `f₀(l)`. -/
  hf0l : IV.Mem (f₀ Calibration.l) f0lI
  /-- `f₀(R₀)`. -/
  hf0R : IV.Mem (f₀ R₀) f0RI
  /-- `e(R₀)`. -/
  heR : IV.Mem (e R₀) eRI
  /-- `B(l)`. -/
  hbl : IV.Mem (B Calibration.l) blI
  /-- `l²`. -/
  hlsq : IV.Mem (Calibration.l ^ 2) lsqI

/-- **`EvalHyp` from the premises and the Boolean test.** -/
theorem CertPrem.evalHyp {E : EvalData} {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true) :
    EvalHyp E rf re (widthR lamI) (widthR (muEnc r0I f0RI eRI lamI)) (widthR (slopeEnc piI blI lamI))
      (widthR (cEnc r0I f0lI f0RI eRI lamI piI blI lsqI)) := by
  have hκ : IV.Mem extSlope (slopeEnc piI blI lamI) := slopeEnc_mem P.hpi P.hbl P.hlam
  have hc : IV.Mem extConst (cEnc r0I f0lI f0RI eRI lamI piI blI lsqI) := by
    have := IV.mem_sub (fLEnc_mem P.hr0 P.hf0l P.hf0R P.heR P.hlam) (IV.mem_mul hκ P.hlsq)
    exact this
  exact evalHyp_of_data P.hQ P.hlam (muEnc_mem P.hr0 P.hf0R P.heR P.hlam) hκ hc P.hlsq hchk

/-- The literal derivative bounds `L₁, …, L₄` of an A7 data set, as reals. -/
@[expose] noncomputable def A7Data.c1 (A : A7Data) : ℝ := (A.L1 : ℝ) / 2 ^ 128
/-- `L₂`. -/
@[expose] noncomputable def A7Data.c2 (A : A7Data) : ℝ := (A.L2 : ℝ) / 2 ^ 128
/-- `L₃`. -/
@[expose] noncomputable def A7Data.c3 (A : A7Data) : ℝ := (A.L3 : ℝ) / 2 ^ 128
/-- `L₄`. -/
@[expose] noncomputable def A7Data.c4 (A : A7Data) : ℝ := (A.L4 : ℝ) / 2 ^ 128

/-- **The outer assertion** (A7, A8, T2): `K ≤ 2 g` on `𝒟 ∖ int 𝒟₀`, from the finite data of the certificate. The
hypotheses are the premises `P` and the test `hchk` of the evaluator, the A7 rows (`DE`, `hrows7`), the outer rows
(`hrows`), the `K` row (`hKrow`) and the finite numerical facts about the literal grids and thresholds. -/
theorem outer_of_certificate {E : EvalData} {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI) (fc : FiniteCore)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    {A : A7Data} {a : ℕ → ℝ} (DE : A7Env A a) (G : OuterGrid) (KG : KGrid)
    {Sh Dh δ Kc ρ ShK ρd ρx : ℝ}
    -- the derivative rectangles cover the grid box
    (hnj : 0 < A.nj) (hnk : 0 < A.nk) (hdp0 : (A.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : sg G.dm G.nd ≤ (A.dp A.nj : ℝ) / 2 ^ 128) (hsp0 : A.sp 0 = 0)
    (hspn : sg G.sm G.nx ≤ (A.sp A.nk : ℝ) / 2 ^ 128) (hrows7 : ∀ j < A.nj, A.row j A.nk = true)
    -- the `d` grid
    (hdm : ∀ j < G.nd, G.dm j ≤ G.dm (j + 1)) (hdlo : Calibration.b ≤ sg G.dm 0)
    (hdρ : sg G.dm 0 - Calibration.b ≤ ρ) (hdstep : ∀ j < G.nd, sg G.dm (j + 1) - sg G.dm j ≤ Dh)
    (hdtop : (697 : ℝ) / 1000 ≤ sg G.dm G.nd) (hd1 : sg G.dm G.nd ≤ 1)
    -- the `s` grid
    (hs0 : G.sm 0 = 0) (hsm : ∀ k < G.nx, G.sm k ≤ G.sm (k + 1))
    (hxstep : ∀ k < G.nx, sg G.sm (k + 1) - sg G.sm k ≤ Sh) (hxtop : (65 : ℝ) / 100 ≤ sg G.sm G.nx)
    -- the hole, inside `𝒟₀`
    (hjl : 0 < G.jl) (hjlr : G.jl ≤ G.nd) (hjr : G.jr < G.nd) (hkl : 0 < G.kl) (hklr : G.kl ≤ G.nx)
    (hkr : G.kr < G.nx) (hD1 : (52528 : ℝ) / 100000 ≤ sg G.dm G.jl) (hD2 : sg G.dm G.jr ≤ 54930 / 100000)
    (hX1 : (29420 : ℝ) / 100000 ≤ sg G.sm G.kl) (hX2 : sg G.sm G.kr ≤ 32621 / 100000)
    -- the rows
    (hrows : ∀ j ≤ G.nd, G.row E j = true)
    -- the `K` row: `K ≤ Kc`
    (hKrow : KG.row E = true) (hdK : (KG.dm : ℝ) / 2 ^ 128 ∈ Icc Calibration.b (697 / 1000 : ℝ))
    (hKs0 : KG.sm 0 = 0) (hKtop : sg KG.sm KG.nx ≤ 65 / 100)
    (hKstep : ∀ k < KG.nx, sg KG.sm (k + 1) - sg KG.sm k ≤ ShK)
    (hρd0 : 0 ≤ ρd) (hρd1 : 0 ≤ (KG.dm : ℝ) / 2 ^ 128 - ρd) (hρd2 : ((KG.dm : ℝ) / 2 ^ 128 - ρd) ^ 4 ≤ 1 / 12)
    (hρd3 : (1 : ℝ) / 12 ≤ ((KG.dm : ℝ) / 2 ^ 128 + ρd) ^ 4)
    (hρx1 : 0 ≤ sg KG.sm KG.nx - ρx) (hρx2 : (sg KG.sm KG.nx - ρx) ^ 4 ≤ 1 / 108)
    (hρx3 : (1 : ℝ) / 108 ≤ sg KG.sm KG.nx ^ 4)
    (hKc : 2 * ((KG.thr.toInt : ℝ) / 2 ^ 256 + δ * sg KG.sm KG.nx + A.c4 * ShK ^ 2 * sg KG.sm KG.nx / 24 +
      (A.c2 * ρx ^ 2 / 2 + A.c1 * ρd * ρx + 65 / 100 * A.c3 * ρd ^ 2 / 2)) ≤ Kc)
    -- the error budget and the threshold
    (hδ0 : 0 ≤ δ) (hδ : deltaData rf re lamI piI r0I f0lI f0RI eRI blI lsqI ≤ δ)
    (hthr : Kc + 2 * A.c2 * Sh ^ 2 / 8 + 2 * sg G.sm G.nx * A.c3 * Dh ^ 2 / 8 + 2 * sg G.sm G.nx * A.c1 * ρ +
      (A.c4 * Sh ^ 2 / 12 + 2 * δ) * sg G.sm G.nx ≤ (G.thr.toInt : ℝ) / 2 ^ 256) :
    ∀ q ∈ boxD \ interior boxD₀, Calibration.K ≤ 2 * g q.1 q.2 := by
  have H := P.evalHyp hchk
  have hB : DerivBounds Calibration.b (sg G.dm G.nd) (sg G.sm G.nx) A.c1 A.c2 A.c3 A.c4 :=
    derivBounds_of_env DE hnj hnk hdp0 hdpn hsp0 hspn hrows7
  have hB' : DerivBounds Calibration.b (697 / 1000) (65 / 100) A.c1 A.c2 A.c3 A.c4 := hB.mono hdtop hxtop
  have hX0 : 0 ≤ sg KG.sm KG.nx := by unfold sg; positivity
  have hρ := abs_sub_p_le hρd0 hρd1 hρd2 hρd3
  have hx0 := x₀_le_of hX0 hρx3
  have hρ' := sub_x₀_le hρx1 hρx2
  have hK := K_le_of_row fc H KG hB' hKrow hdK hKs0 hKtop hKstep hδ hρ hx0 (ρ' := ρx) (by linarith)
  exact outer_of_rows fc H G hB hdm hdlo hdρ hdstep hdtop hd1 hs0 hsm hxstep hxtop hjl hjlr hjr hkl hklr hkr hD1 hD2
    hX1 hX2 hrows (hK.trans hKc) hδ0 hδ hthr

/-- **The negative-part assertion** (A7, A9, T3): `∫₀^{.65} max 0 (-G(d, ·)) ≤ -K` for `d ∈ [b, .697]`, from the finite
data of the certificate (the same premises and `K` row as `outer_of_certificate`). -/
theorem negative_of_certificate {E : EvalData} {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI) (fc : FiniteCore)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    {A : A7Data} {a : ℕ → ℝ} (DE : A7Env A a) (Gr : NegGrid) (KG : KGrid)
    {Sh Dh δ Kc ShK ρd ρx : ℝ}
    -- the derivative rectangles cover the grid box
    (hnj : 0 < A.nj) (hnk : 0 < A.nk) (hdp0 : (A.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : sg Gr.dm Gr.nd ≤ (A.dp A.nj : ℝ) / 2 ^ 128) (hsp0 : A.sp 0 = 0)
    (hspn : sg Gr.sm Gr.nx ≤ (A.sp A.nk : ℝ) / 2 ^ 128) (hrows7 : ∀ j < A.nj, A.row j A.nk = true)
    -- the `d` grid
    (hdm : ∀ j < Gr.nd, Gr.dm j ≤ Gr.dm (j + 1)) (hdlo : Calibration.b ≤ sg Gr.dm 0)
    (hdnear : sg Gr.dm 0 ≤ Calibration.b + Dh / 2) (hdstep : ∀ j < Gr.nd, sg Gr.dm (j + 1) - sg Gr.dm j ≤ Dh)
    (hdtop : (697 : ℝ) / 1000 ≤ sg Gr.dm Gr.nd) (hd1 : sg Gr.dm Gr.nd ≤ 1)
    -- the `s` grid
    (hs0 : Gr.sm 0 = 0) (hsm : ∀ k < Gr.nx, Gr.sm k ≤ Gr.sm (k + 1))
    (hxstep : ∀ k < Gr.nx, sg Gr.sm (k + 1) - sg Gr.sm k ≤ Sh) (hxtop : (65 : ℝ) / 100 ≤ sg Gr.sm Gr.nx)
    -- the rows
    (hrows : ∀ j ≤ Gr.nd, Gr.row E j = true)
    -- the `K` row: `K ≤ Kc`
    (hKrow : KG.row E = true) (hdK : (KG.dm : ℝ) / 2 ^ 128 ∈ Icc Calibration.b (697 / 1000 : ℝ))
    (hKs0 : KG.sm 0 = 0) (hKtop : sg KG.sm KG.nx ≤ 65 / 100)
    (hKstep : ∀ k < KG.nx, sg KG.sm (k + 1) - sg KG.sm k ≤ ShK)
    (hρd0 : 0 ≤ ρd) (hρd1 : 0 ≤ (KG.dm : ℝ) / 2 ^ 128 - ρd) (hρd2 : ((KG.dm : ℝ) / 2 ^ 128 - ρd) ^ 4 ≤ 1 / 12)
    (hρd3 : (1 : ℝ) / 12 ≤ ((KG.dm : ℝ) / 2 ^ 128 + ρd) ^ 4)
    (hρx1 : 0 ≤ sg KG.sm KG.nx - ρx) (hρx2 : (sg KG.sm KG.nx - ρx) ^ 4 ≤ 1 / 108)
    (hρx3 : (1 : ℝ) / 108 ≤ sg KG.sm KG.nx ^ 4)
    (hKc : 2 * ((KG.thr.toInt : ℝ) / 2 ^ 256 + δ * sg KG.sm KG.nx + A.c4 * ShK ^ 2 * sg KG.sm KG.nx / 24 +
      (A.c2 * ρx ^ 2 / 2 + A.c1 * ρd * ρx + 65 / 100 * A.c3 * ρd ^ 2 / 2)) ≤ Kc)
    -- the error budget and the threshold
    (hδ : deltaData rf re lamI piI r0I f0lI f0RI eRI blI lsqI ≤ δ)
    (hthr : (Gr.thr.toInt : ℝ) / 2 ^ 256 + (δ + A.c2 * Sh / 4) * sg Gr.sm Gr.nx + sg Gr.sm Gr.nx * A.c1 * Dh / 2 +
      Kc ≤ 0) :
    ∀ d ∈ Icc Calibration.b (697 / 1000 : ℝ), ∫ s in (0 : ℝ)..(65 / 100 : ℝ), max 0 (-G d s) ≤ -Calibration.K := by
  have H := P.evalHyp hchk
  have hB : DerivBounds Calibration.b (sg Gr.dm Gr.nd) (sg Gr.sm Gr.nx) A.c1 A.c2 A.c3 A.c4 :=
    derivBounds_of_env DE hnj hnk hdp0 hdpn hsp0 hspn hrows7
  have hB' : DerivBounds Calibration.b (697 / 1000) (65 / 100) A.c1 A.c2 A.c3 A.c4 := hB.mono hdtop hxtop
  have hX0 : 0 ≤ sg KG.sm KG.nx := by unfold sg; positivity
  have hρ := abs_sub_p_le hρd0 hρd1 hρd2 hρd3
  have hx0 := x₀_le_of hX0 hρx3
  have hρ' := sub_x₀_le hρx1 hρx2
  have hK := K_le_of_row fc H KG hB' hKrow hdK hKs0 hKtop hKstep hδ hρ hx0 (ρ' := ρx) (by linarith)
  exact negative_of_rows fc H Gr hB hdm hdlo hdnear hdstep hdtop hd1 hs0 hsm hxstep hxtop hrows (hK.trans hKc) hδ hthr

end SandierSerfaty.Certificate.Box
