/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Jet.Encl

/-!
# Classical derivatives from a jet enclosure on a cell

`JetEncl T F J` encloses `F` and derivative witnesses `F₁, F₂, F₃` (two-sided `HasDerivAt` at the points of
`T` only). On a nondegenerate cell `T = [a, b]` (`a < b`) and for `F` of class `C³` on an open set `U ⊇ T`, the
witnesses are the iterated derivatives at every point of `T`, endpoints included
(`iteratedDeriv_eq_of_jet3`): derivatives within `[a, b]` are unique, and the iterated derivatives of `F`
are differentiable on `U`. Hence (`jetEncl_iteratedDeriv`)

  `F t ∈ J.c0`, `iteratedDeriv 1 F t ∈ J.c1`, `iteratedDeriv 2 F t / 2 ∈ J.c2`, `iteratedDeriv 3 F t / 6 ∈ J.c3`

for every `t` in the cell `{t | t ∈ X}` of an interval `X` with `X.lo < X.hi`. This is the form in which the
finite-core premise (`Tails.FiniteCore`, one-sided derivatives of the pieces at the knots) and the constants
`V_i'(R₀)`, `V_i''(R₀)`, `γ'(R₀)`, `γ''(R₀)` are read off the jets.
-/

open Set Filter

public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Tails

variable {P : ℕ}

/-- The cell of an interval is a closed interval. -/
theorem setOf_mem_eq_Icc (X : IV P) :
    {t | IV.Mem t X} = Icc (((X.lo.toInt : ℤ) : ℝ) / 2 ^ P) (((X.hi.toInt : ℤ) : ℝ) / 2 ^ P) := by
  have hp := IV.two_pow_pos' P
  ext t
  simp only [mem_ofPred_eq, IV.Mem, mem_Icc]
  rw [div_le_iff₀ hp, le_div_iff₀ hp]

theorem cell_lt {X : IV P} (h : SInt.blt X.lo X.hi = true) :
    ((X.lo.toInt : ℤ) : ℝ) / 2 ^ P < ((X.hi.toInt : ℤ) : ℝ) / 2 ^ P := by
  have hp := IV.two_pow_pos' P
  rw [SInt.blt_iff] at h
  exact div_lt_div_of_pos_right (by exact_mod_cast h) hp

theorem differentiableAt_iteratedDeriv {F : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 3 F U)
    {m : ℕ} (hm : m < 3) {x : ℝ} (hx : x ∈ U) : DifferentiableAt ℝ (iteratedDeriv m F) x := by
  have h1 := (hF.differentiableOn_iteratedDerivWithin (m := m) (by exact_mod_cast hm) hU.uniqueDiffOn) x hx
  have h2 := h1.differentiableAt (hU.mem_nhds hx)
  exact h2.congr_of_eventuallyEq ((iteratedDerivWithin_of_isOpen hU).eventuallyEq_of_mem (hU.mem_nhds hx)).symm

/-- On a nondegenerate closed interval inside an open set where `F` is `C³`, jet witnesses are the iterated
derivatives. -/
theorem iteratedDeriv_eq_of_jet3 {F F₁ F₂ F₃ : ℝ → ℝ} {a b : ℝ} (hab : a < b) {U : Set ℝ} (hU : IsOpen U)
    (hsub : Icc a b ⊆ U) (hF : ContDiffOn ℝ 3 F U) (hj : Jet3 (Icc a b) F F₁ F₂ F₃) {x : ℝ}
    (hx : x ∈ Icc a b) :
    iteratedDeriv 1 F x = F₁ x ∧ iteratedDeriv 2 F x = F₂ x ∧ iteratedDeriv 3 F x = F₃ x := by
  have hu : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have s1 : ∀ y ∈ Icc a b, iteratedDeriv 1 F y = F₁ y := fun y hy => by
    rw [iteratedDeriv_one]; exact (hj.d0 y hy).deriv
  have step : ∀ (m : ℕ) (G₁ G₂ : ℝ → ℝ), m < 3 → (∀ y ∈ Icc a b, iteratedDeriv m F y = G₁ y) →
      (∀ y ∈ Icc a b, HasDerivAt G₁ (G₂ y) y) → ∀ y ∈ Icc a b, iteratedDeriv (m + 1) F y = G₂ y := by
    intro m G₁ G₂ hm hG hG' y hy
    rw [iteratedDeriv_succ]
    have hd := (differentiableAt_iteratedDeriv hU hF hm (hsub hy)).hasDerivAt.hasDerivWithinAt (s := Icc a b)
    have h2 : HasDerivWithinAt (iteratedDeriv m F) (G₂ y) (Icc a b) y :=
      (hG' y hy).hasDerivWithinAt.congr hG (hG y hy)
    exact (hu y hy).eq_deriv _ hd h2
  have s2 := step 1 F₁ F₂ (by norm_num) s1 hj.d1
  have s3 := step 2 F₂ F₃ (by norm_num) s2 hj.d2
  exact ⟨s1 x hx, s2 x hx, s3 x hx⟩

/-- **Derivatives from a jet enclosure.** On the cell of `X` (`X.lo < X.hi`) inside an open set where `F` is
`C³`, the jet encloses `F, F', F''/2, F'''/6` with the classical iterated derivatives. -/
theorem jetEncl_iteratedDeriv {X : IV P} (hlt : SInt.blt X.lo X.hi = true) {U : Set ℝ} (hU : IsOpen U)
    (hsub : ∀ t, IV.Mem t X → t ∈ U) {F : ℝ → ℝ} (hF : ContDiffOn ℝ 3 F U) {J : IJet P}
    (h : JetEncl {t | IV.Mem t X} F J) {t : ℝ} (ht : IV.Mem t X) :
    IV.Mem (F t) J.c0 ∧ IV.Mem (iteratedDeriv 1 F t) J.c1 ∧ IV.Mem (iteratedDeriv 2 F t / 2) J.c2 ∧
      IV.Mem (iteratedDeriv 3 F t / 6) J.c3 := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := h
  rw [setOf_mem_eq_Icc] at hj
  have hsub' : Icc (((X.lo.toInt : ℤ) : ℝ) / 2 ^ P) (((X.hi.toInt : ℤ) : ℝ) / 2 ^ P) ⊆ U := by
    rw [← setOf_mem_eq_Icc]; exact fun s hs => hsub s hs
  have ht' : t ∈ Icc (((X.lo.toInt : ℤ) : ℝ) / 2 ^ P) (((X.hi.toInt : ℤ) : ℝ) / 2 ^ P) := by
    rw [← setOf_mem_eq_Icc]; exact ht
  obtain ⟨e1, e2, e3⟩ := iteratedDeriv_eq_of_jet3 (cell_lt hlt) hU hsub' hF hj ht'
  obtain ⟨b0, b1, b2, b3⟩ := hb t ht
  exact ⟨b0, e1 ▸ b1, e2 ▸ b2, e3 ▸ b3⟩

/-- The order-two analogue: from an order-three enclosure of `F`, the classical first and second
derivatives. -/
theorem jetEncl_deriv {X : IV P} (hlt : SInt.blt X.lo X.hi = true) {U : Set ℝ} (hU : IsOpen U)
    (hsub : ∀ t, IV.Mem t X → t ∈ U) {F : ℝ → ℝ} (hF : ContDiffOn ℝ 3 F U) {J : IJet P}
    (h : JetEncl {t | IV.Mem t X} F J) {t : ℝ} (ht : IV.Mem t X) :
    IV.Mem (F t) J.c0 ∧ IV.Mem (deriv F t) J.c1 ∧ IV.Mem (deriv (deriv F) t / 2) J.c2 := by
  obtain ⟨h0, h1, h2, -⟩ := jetEncl_iteratedDeriv hlt hU hsub hF h ht
  rw [iteratedDeriv_one] at h1
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h2
  exact ⟨h0, h1, h2⟩

end SandierSerfaty.Certificate.Basis
