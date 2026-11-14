/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Cert
public import SandierSerfaty.Certificate.Box.InnerIdx

/-!
# The outer and negative-part assertions with the checked-index A7 rows

`outer_of_certificateI`, `negative_of_certificateI`: `Box.outer_of_certificate` and `Box.negative_of_certificate`
with the derivative bounds from the A7 rows `A7Data.rowI A ix` (`Box.derivBounds_of_envI`; the index ranges `ix` are
untrusted data checked by the kernel) in place of the scanning rows. Every other hypothesis and the conclusions
are unchanged; the proofs are those of the scanning versions.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- **The outer assertion** (A7, A8, T2) with the checked-index A7 rows `A7Data.rowI A ix` (`outer_of_certificate`). -/
theorem outer_of_certificateI {E : EvalData} {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI) (fc : FiniteCore)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    {A : A7Data} (ix : Nat → Nat → Nat × Nat) {a : ℕ → ℝ} (DE : A7Env A a) (G : OuterGrid) (KG : KGrid)
    {Sh Dh δ Kc ρ ShK ρd ρx : ℝ}
    -- the derivative rectangles cover the grid box
    (hnj : 0 < A.nj) (hnk : 0 < A.nk) (hdp0 : (A.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : sg G.dm G.nd ≤ (A.dp A.nj : ℝ) / 2 ^ 128) (hsp0 : A.sp 0 = 0)
    (hspn : sg G.sm G.nx ≤ (A.sp A.nk : ℝ) / 2 ^ 128) (hrows7 : ∀ j < A.nj, A.rowI ix j A.nk = true)
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
    derivBounds_of_envI ix DE hnj hnk hdp0 hdpn hsp0 hspn hrows7
  have hB' : DerivBounds Calibration.b (697 / 1000) (65 / 100) A.c1 A.c2 A.c3 A.c4 := hB.mono hdtop hxtop
  have hX0 : 0 ≤ sg KG.sm KG.nx := by unfold sg; positivity
  have hρ := abs_sub_p_le hρd0 hρd1 hρd2 hρd3
  have hx0 := x₀_le_of hX0 hρx3
  have hρ' := sub_x₀_le hρx1 hρx2
  have hK := K_le_of_row fc H KG hB' hKrow hdK hKs0 hKtop hKstep hδ hρ hx0 (ρ' := ρx) (by linarith)
  exact outer_of_rows fc H G hB hdm hdlo hdρ hdstep hdtop hd1 hs0 hsm hxstep hxtop hjl hjlr hjr hkl hklr hkr hD1 hD2
    hX1 hX2 hrows (hK.trans hKc) hδ0 hδ hthr

/-- **The negative-part assertion** (A7, A9, T3) with the checked-index A7 rows (`negative_of_certificate`). -/
theorem negative_of_certificateI {E : EvalData} {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128}
    (P : CertPrem E rf re lamI piI r0I f0lI f0RI eRI blI lsqI) (fc : FiniteCore)
    (hchk : evalCheckOf E lamI piI r0I f0lI f0RI eRI blI lsqI rf re = true)
    {A : A7Data} (ix : Nat → Nat → Nat × Nat) {a : ℕ → ℝ} (DE : A7Env A a) (Gr : NegGrid) (KG : KGrid)
    {Sh Dh δ Kc ShK ρd ρx : ℝ}
    -- the derivative rectangles cover the grid box
    (hnj : 0 < A.nj) (hnk : 0 < A.nk) (hdp0 : (A.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : sg Gr.dm Gr.nd ≤ (A.dp A.nj : ℝ) / 2 ^ 128) (hsp0 : A.sp 0 = 0)
    (hspn : sg Gr.sm Gr.nx ≤ (A.sp A.nk : ℝ) / 2 ^ 128) (hrows7 : ∀ j < A.nj, A.rowI ix j A.nk = true)
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
    derivBounds_of_envI ix DE hnj hnk hdp0 hdpn hsp0 hspn hrows7
  have hB' : DerivBounds Calibration.b (697 / 1000) (65 / 100) A.c1 A.c2 A.c3 A.c4 := hB.mono hdtop hxtop
  have hX0 : 0 ≤ sg KG.sm KG.nx := by unfold sg; positivity
  have hρ := abs_sub_p_le hρd0 hρd1 hρd2 hρd3
  have hx0 := x₀_le_of hX0 hρx3
  have hρ' := sub_x₀_le hρx1 hρx2
  have hK := K_le_of_row fc H KG hB' hKrow hdK hKs0 hKtop hKstep hδ hρ hx0 (ρ' := ρx) (by linarith)
  exact negative_of_rows fc H Gr hB hdm hdlo hdnear hdstep hdtop hd1 hs0 hsm hxstep hxtop hrows (hK.trans hKc) hδ hthr

end SandierSerfaty.Certificate.Box
