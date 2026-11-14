/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumSound
public import SandierSerfaty.Certificate.Box.Cert

/-!
# Rational checks of the scalar threshold inequalities

The few polynomial inequalities of `Box.certificateGoal_of_data` (the thresholds `hKc`, `hthr`, `hNthr` and the error
budget `deltaData ≤ δ`) are decided in `ℚ` (a handful of operations; no grid is looped over). The free real parameters
of the assertions are rational literals: `Sh = sh/2^128` etc. (`sh : ℕ`) and `δ, Kc : ℚ`.

* `kcB`, `kcB_sound`: `K ≤ Kc` threshold (`hKc`);
* `outThrB`, `outThrB_sound`: the outer threshold (`hthr`);
* `negThrB`, `negThrB_sound`: the negative-part threshold (`hNthr`);
* `deltaB`, `deltaB_sound`: `0 ≤ δ` and `deltaData ≤ δ`.
-/

open Set

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query SandierSerfaty.Calibration SandierSerfaty.Tails

/-- A dyadic quantity `n / 2^128` as a rational. -/
def qd (n : ℕ) : ℚ := (n : ℚ) / 2 ^ 128

/-- **The threshold of the `K` row** (`hKc`): `2 (thr/2^256 + δ x + L₄ Sh² x/24 + (L₂ ρx²/2 + L₁ ρd ρx +
.65 L₃ ρd²/2)) ≤ Kc`, `x` the top `s` node. -/
def kcB (L1 L2 L3 L4 : ℕ) (thr : ℤ) (x shK rd rx : ℕ) (δ Kc : ℚ) : Bool :=
  decide (2 * ((thr : ℚ) / 2 ^ 256 + δ * qd x + qd L4 * qd shK ^ 2 * qd x / 24 +
    (qd L2 * qd rx ^ 2 / 2 + qd L1 * qd rd * qd rx + 65 / 100 * qd L3 * qd rd ^ 2 / 2)) ≤ Kc)

theorem kcB_sound (A : A7Data) (KG : KGrid) {shK rd rx : ℕ} {δ Kc : ℚ}
    (h : kcB A.L1 A.L2 A.L3 A.L4 KG.thr.toInt (KG.sm KG.nx) shK rd rx δ Kc = true) :
    2 * ((KG.thr.toInt : ℝ) / 2 ^ 256 + (δ : ℝ) * sg KG.sm KG.nx +
      A.c4 * ((shK : ℝ) / 2 ^ 128) ^ 2 * sg KG.sm KG.nx / 24 +
      (A.c2 * ((rx : ℝ) / 2 ^ 128) ^ 2 / 2 + A.c1 * ((rd : ℝ) / 2 ^ 128) * ((rx : ℝ) / 2 ^ 128) +
        65 / 100 * A.c3 * ((rd : ℝ) / 2 ^ 128) ^ 2 / 2)) ≤ (Kc : ℝ) := by
  have h1 := of_decide_eq_true h
  have h2 : ((2 * ((KG.thr.toInt : ℚ) / 2 ^ 256 + δ * qd (KG.sm KG.nx) + qd A.L4 * qd shK ^ 2 * qd (KG.sm KG.nx) / 24 +
    (qd A.L2 * qd rx ^ 2 / 2 + qd A.L1 * qd rd * qd rx + 65 / 100 * qd A.L3 * qd rd ^ 2 / 2)) : ℚ) : ℝ) ≤
      (Kc : ℝ) := by exact_mod_cast h1
  push_cast [qd] at h2
  simpa [A7Data.c1, A7Data.c2, A7Data.c3, A7Data.c4, sg] using h2

/-- **The outer threshold** (`hthr`): `Kc + L₂ Sh²/4 + L₃ x Dh²/4 + 2 x L₁ ρ + (L₄ Sh²/12 + 2 δ) x ≤ thr/2^256`. -/
def outThrB (L1 L2 L3 L4 : ℕ) (thr : ℤ) (x sh dh rho : ℕ) (δ Kc : ℚ) : Bool :=
  decide (Kc + 2 * qd L2 * qd sh ^ 2 / 8 + 2 * qd x * qd L3 * qd dh ^ 2 / 8 + 2 * qd x * qd L1 * qd rho +
    (qd L4 * qd sh ^ 2 / 12 + 2 * δ) * qd x ≤ (thr : ℚ) / 2 ^ 256)

theorem outThrB_sound (A : A7Data) (G : OuterGrid) {sh dh rho : ℕ} {δ Kc : ℚ}
    (h : outThrB A.L1 A.L2 A.L3 A.L4 G.thr.toInt (G.sm G.nx) sh dh rho δ Kc = true) :
    (Kc : ℝ) + 2 * A.c2 * ((sh : ℝ) / 2 ^ 128) ^ 2 / 8 + 2 * sg G.sm G.nx * A.c3 * ((dh : ℝ) / 2 ^ 128) ^ 2 / 8 +
      2 * sg G.sm G.nx * A.c1 * ((rho : ℝ) / 2 ^ 128) +
      (A.c4 * ((sh : ℝ) / 2 ^ 128) ^ 2 / 12 + 2 * (δ : ℝ)) * sg G.sm G.nx ≤ (G.thr.toInt : ℝ) / 2 ^ 256 := by
  have h1 := of_decide_eq_true h
  have h2 : ((Kc + 2 * qd A.L2 * qd sh ^ 2 / 8 + 2 * qd (G.sm G.nx) * qd A.L3 * qd dh ^ 2 / 8 +
      2 * qd (G.sm G.nx) * qd A.L1 * qd rho + (qd A.L4 * qd sh ^ 2 / 12 + 2 * δ) * qd (G.sm G.nx) : ℚ) : ℝ) ≤
      (((G.thr.toInt : ℚ) / 2 ^ 256 : ℚ) : ℝ) := by exact_mod_cast h1
  push_cast [qd] at h2
  simpa [A7Data.c1, A7Data.c2, A7Data.c3, A7Data.c4, sg] using h2

/-- **The negative-part threshold** (`hNthr`): `thr/2^256 + (δ + L₂ Sh/4) x + x L₁ Dh/2 + Kc ≤ 0`. -/
def negThrB (L1 L2 : ℕ) (thr : ℤ) (x sh dh : ℕ) (δ Kc : ℚ) : Bool :=
  decide ((thr : ℚ) / 2 ^ 256 + (δ + qd L2 * qd sh / 4) * qd x + qd x * qd L1 * qd dh / 2 + Kc ≤ 0)

theorem negThrB_sound (A : A7Data) (Gr : NegGrid) {sh dh : ℕ} {δ Kc : ℚ}
    (h : negThrB A.L1 A.L2 Gr.thr.toInt (Gr.sm Gr.nx) sh dh δ Kc = true) :
    (Gr.thr.toInt : ℝ) / 2 ^ 256 + ((δ : ℝ) + A.c2 * ((sh : ℝ) / 2 ^ 128) / 4) * sg Gr.sm Gr.nx +
      sg Gr.sm Gr.nx * A.c1 * ((dh : ℝ) / 2 ^ 128) / 2 + (Kc : ℝ) ≤ 0 := by
  have h1 := of_decide_eq_true h
  have h2 : (((Gr.thr.toInt : ℚ) / 2 ^ 256 + (δ + qd A.L2 * qd sh / 4) * qd (Gr.sm Gr.nx) +
      qd (Gr.sm Gr.nx) * qd A.L1 * qd dh / 2 + Kc : ℚ) : ℝ) ≤ ((0 : ℚ) : ℝ) := by exact_mod_cast h1
  push_cast [qd] at h2
  simpa [A7Data.c1, A7Data.c2, sg] using h2

/-- The width of an enclosure as a rational. -/
def wq (I : IV 128) : ℚ := ((SInt.sub I.hi I.lo).mag : ℚ) / 2 ^ 128

/-- **The error budget** (`0 ≤ δ` and `deltaData ≤ δ`) from the widths of the enclosures. -/
def deltaB (rf re : ℕ) (lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128) (δ : ℚ) : Bool :=
  and (decide (0 ≤ δ))
    (and (decide ((qd rf + qd re + 2 * (1 / 10 ^ 11) + wq (muEnc r0I f0RI eRI lamI) + wq lamI / 4) /
        (28209 / 100000) + 1 / 2 ^ 60 ≤ δ))
      (decide (wq (slopeEnc piI blI lamI) + 4 * wq (cEnc r0I f0lI f0RI eRI lamI piI blI lsqI) + 1 / 2 ^ 100 ≤ δ)))

theorem widthR_eq (I : IV 128) : widthR I = ((wq I : ℚ) : ℝ) := by
  simp [widthR, wq]

theorem deltaB_sound {rf re : ℕ} {lamI piI r0I f0lI f0RI eRI blI lsqI : IV 128} {δ : ℚ}
    (h : deltaB rf re lamI piI r0I f0lI f0RI eRI blI lsqI δ = true) :
    0 ≤ (δ : ℝ) ∧ deltaData rf re lamI piI r0I f0lI f0RI eRI blI lsqI ≤ (δ : ℝ) := by
  simp only [deltaB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  refine ⟨by exact_mod_cast h0, ?_⟩
  unfold deltaData deltaMax deltaG deltaExt
  rw [widthR_eq, widthR_eq, widthR_eq, widthR_eq]
  have e1 : ((qd rf + qd re + 2 * (1 / 10 ^ 11) + wq (muEnc r0I f0RI eRI lamI) + wq lamI / 4) /
        (28209 / 100000) + 1 / 2 ^ 60 : ℚ) ≤ δ := h1
  have a1 : ((((qd rf + qd re + 2 * (1 / 10 ^ 11) + wq (muEnc r0I f0RI eRI lamI) + wq lamI / 4) /
        (28209 / 100000) + 1 / 2 ^ 60 : ℚ)) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast e1
  have a2 : (((wq (slopeEnc piI blI lamI) + 4 * wq (cEnc r0I f0lI f0RI eRI lamI piI blI lsqI) + 1 / 2 ^ 100 : ℚ)) : ℝ)
      ≤ (δ : ℝ) := by exact_mod_cast h2
  push_cast [qd] at a1 a2
  refine max_le ?_ ?_
  · have hb : Calibration.b = 28209 / 100000 := by unfold Calibration.b; norm_num
    have he : epsTail = 1 / 10 ^ 11 := rfl
    rw [hb, he]
    exact a1
  · exact a2

end SandierSerfaty.Certificate.Box
