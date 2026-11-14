/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenPointwise

/-!
# The energy of the screened field (screening note, Proposition 4.27)

The screening note, Proposition 4.27 (`prop:energy`). Integrating the a.e.
bound `½|E'_ρ|² ≤ B - c` of `ScreenPointwise` (with `∫ c ≥ 0`, Lemma 4.26) and inserting
`½∫_Q |E_β|² + ∑_K τ_m(α_p) ≤ G_Q(α) + c_m n_∂` (Lemma 4.9(c)) and
`∑_Y τ_m(ρ_y) = ∑_K τ_m(α_p) + #Z τ_m(r₀) ≤ ∑_K τ_m(α_p)`:

`G_Q(ρ)[E'; Y] ≤ G_Q(α)[E; C] + c_m n_∂ + excess`, `excess = 2S_d + 1008 ℓc Gb + 32 N2b +
64π²/ℓc + 2 #Z e_P` (`Good.locEnergy_le`), with `e_P = 2(π/2 + 1056π² + 256π/(r₀√m))` the energy
bound of one piece (Lemma 4.22) and `Gb`, `N2b` the bounds of `ScreenFluxEnergy`. The constants differ
from the screening note's (`½S_d + 32N₂ + X_A + 2V_flux + 12π²/ℓc + 3#Z(π/2 + e_T)`) only in the numerical
factors; they are absorbed in `C_S`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

/-- A nonnegative function with `∫⁻ ofReal f ≤ ofReal b` is integrable with `∫ f ≤ b`. -/
theorem integrable_and_integral_le {μ : Measure ℂ} {f : ℂ → ℝ} (hm : AEStronglyMeasurable f μ)
    (h0 : ∀ x, 0 ≤ f x) {b : ℝ} (hb0 : 0 ≤ b) (hb : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal b) :
    Integrable f μ ∧ ∫ x, f x ∂μ ≤ b := by
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).2
    (hb.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall h0) hm]
  exact ENNReal.toReal_le_of_le_ofReal hb0 hb

theorem ofReal_indicator_apply (s : Set ℂ) (f : ℂ → ℝ) (x : ℂ) :
    ENNReal.ofReal (s.indicator f x) = s.indicator (fun y => ENNReal.ofReal (f y)) x := by
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, ENNReal.ofReal_zero]

theorem integral_add6 {f₁ f₂ f₃ f₄ f₅ f₆ : ℂ → ℝ} (i₁ : Integrable f₁) (i₂ : Integrable f₂)
    (i₃ : Integrable f₃) (i₄ : Integrable f₄) (i₅ : Integrable f₅) (i₆ : Integrable f₆) :
    ∫ x, (f₁ x + f₂ x + f₃ x + f₄ x + f₅ x + f₆ x) =
      (∫ x, f₁ x) + (∫ x, f₂ x) + (∫ x, f₃ x) + (∫ x, f₄ x) + (∫ x, f₅ x) + ∫ x, f₆ x := by
  have h₂ : Integrable (fun x => f₁ x + f₂ x) := i₁.add i₂
  have h₃ : Integrable (fun x => f₁ x + f₂ x + f₃ x) := h₂.add i₃
  have h₄ : Integrable (fun x => f₁ x + f₂ x + f₃ x + f₄ x) := h₃.add i₄
  have h₅ : Integrable (fun x => f₁ x + f₂ x + f₃ x + f₄ x + f₅ x) := h₄.add i₅
  rw [integral_add h₅ i₆, integral_add h₄ i₅, integral_add h₃ i₄, integral_add h₂ i₃,
    integral_add i₁ i₂]

namespace Scr

open Pinwheel

/-- The energy bound `e_P = 2(π/2 + 1056π² + 256π/(r₀√m))` of one filler piece (Lemma 4.22). -/
@[expose] noncomputable def ePiece (m r : ℝ) : ℝ := 2 * (π / 2 + (1056 * π ^ 2 + 256 * π / (r * √m)))

/-- The excess of Proposition 4.27 over `G_Q(α) + c_m n_∂`. -/
@[expose] noncomputable def excess (m t ℓ Sd r : ℝ) (nZ : ℕ) : ℝ :=
  2 * Sd + 1008 * ℓ * Gb m t ℓ Sd + 32 * N2b m t Sd + 64 * π ^ 2 / ℓ + 2 * nZ * ePiece m r

namespace Asm

variable {D : Data} {A : Asm}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

/-! ### The six terms of the majorant -/

omit h hA in
theorem measurableSet_Ωp : MeasurableSet (Ωp D) :=
  (isOpen_lt continuous_const Data.continuous_dep).measurableSet

omit hA in
theorem term_Eβ :
    Integrable ((Ωp D).indicator fun y => ‖D.Eβ y‖ ^ 2) ∧
      ∫ x, (Ωp D).indicator (fun y => ‖D.Eβ y‖ ^ 2) x ≤
        (∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2)).toReal := by
  have hS : IsCompact {x | D.d ≤ D.dep x} := Data.isCompact_dep_ge _
  have hSU : {x | D.d ≤ D.dep x} ⊆ D.U := Data.setOf_le_dep_subset_U (by linarith [h.d_pos])
  have hint : IntegrableOn D.Eβ {x | D.d ≤ D.dep x} :=
    integrableOn_truncField h.hC h.hE.1 (fun p hp => h.beta_pos hp) ⟨1 / 4, fun _ _ => h.beta_le⟩
      hS hSU
  have hΩS : Ωp D ⊆ {x | D.d ≤ D.dep x} := fun x hx => by
    simp only [mem_ofPred_eq]; exact le_of_lt hx
  have hm : AEStronglyMeasurable ((Ωp D).indicator fun y => ‖D.Eβ y‖ ^ 2) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ωp).2
      ((hint.mono_set hΩS).aestronglyMeasurable.norm.pow 2)
  have hQ : Ωp D ⊆ D.Q := fun x hx => Data.mem_Q_iff.2 (by
    change D.d < D.dep x at hx; linarith [h.d_pos])
  refine integrable_and_integral_le hm (fun x => indicator_nonneg (fun _ _ => sq_nonneg _) x)
    ENNReal.toReal_nonneg ?_
  simp_rw [ofReal_indicator_apply]
  rw [lintegral_indicator measurableSet_Ωp, ENNReal.ofReal_toReal h.lintegral_Eβ_ne_top]
  exact lintegral_mono_set hQ

omit hA in
theorem term_Φ :
    Integrable (D.R.indicator fun y => ‖D.Φ y‖ ^ 2) ∧
      ∫ x, D.R.indicator (fun y => ‖D.Φ y‖ ^ 2) x ≤ D.Sd := by
  have hm : AEStronglyMeasurable (D.R.indicator fun y => ‖D.Φ y‖ ^ 2) volume :=
    (aestronglyMeasurable_indicator_iff Data.measurableSet_R).2
      (h.integrableOn_Φ_R.aestronglyMeasurable.norm.pow 2)
  refine integrable_and_integral_le hm (fun x => indicator_nonneg (fun _ _ => sq_nonneg _) x)
    h.Sd_nonneg ?_
  simp_rw [ofReal_indicator_apply]
  rw [lintegral_indicator Data.measurableSet_R]
  exact h.hSd

omit hA in
theorem Gb_nonneg : 0 ≤ Gb D.m D.t D.ℓ D.Sd := by
  have := h.t_pos; have := h.ℓ_pos; have := h.Sd_nonneg; have := h.m_pos
  unfold Gb N2b; positivity

omit hA in
theorem N2b_nonneg : 0 ≤ N2b D.m D.t D.Sd := by
  have := h.t_pos; have := h.Sd_nonneg
  unfold N2b; positivity

theorem term_Vflux :
    Integrable (fun x => ‖A.Vflux D x‖ ^ 2) ∧
      ∫ x, ‖A.Vflux D x‖ ^ 2 ≤ 504 * D.ℓ * Gb D.m D.t D.ℓ D.Sd :=
  integrable_and_integral_le ((hA.integrable_Vflux h).aestronglyMeasurable.norm.pow 2)
    (fun _ => sq_nonneg _) (mul_nonneg (by linarith [h.ℓ_pos]) (Gb_nonneg h))
    (hA.lintegral_Vflux_le h)

omit hA in
theorem term_nD : Integrable (fun x => D.nD x ^ 2) ∧ ∫ x, D.nD x ^ 2 ≤ N2b D.m D.t D.Sd :=
  integrable_and_integral_le ((Data.measurable_nD.pow_const 2).aestronglyMeasurable)
    (fun _ => sq_nonneg _) (N2b_nonneg h) h.lintegral_nD_sq_le_N2b

theorem term_carry (j : Fin 4) :
    Integrable (fun x => ‖carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x‖ ^ 2) ∧
      ∫ x, ‖carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x‖ ^ 2 ≤ 8 * π ^ 2 / (3 * D.ℓ) := by
  have hw := hA.lastWidth_mem j
  have hw0 : 0 < A.cut.lastWidth j := h.ℓ_pos.trans_le hw.1
  refine integrable_and_integral_le
    ((isFieldPiece_carryField (c := D.c) (t := D.t) (d := D.d) (j := j) (θ := A.cut.θ j) hw0).1
      |>.aestronglyMeasurable.norm.pow 2) (fun _ => sq_nonneg _)
    (by have := h.ℓ_pos; positivity) ?_
  exact lintegral_norm_sq_carryField_le' h.ℓ_pos hw.1 (hA.isCut.θ_mem j)

theorem term_Pdiff {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) :
    Integrable (fun x => ‖A.Pdiff D i x‖ ^ 2) ∧ ∫ x, ‖A.Pdiff D i x‖ ^ 2 ≤ ePiece D.m D.r₀ := by
  have hP := hA.isFillerPiece h hi
  have hm : AEStronglyMeasurable (A.Pdiff D i) volume :=
    (hP.isFieldPiece_pieceField h.r₀_pos h.r₀_le').1.aestronglyMeasurable.sub
      ((measurable_gradient _).comp (measurable_id.sub_const _)).aestronglyMeasurable
  have hm0 : 0 ≤ ePiece D.m D.r₀ := by
    have := h.r₀_pos; have := h.m_pos; unfold ePiece; positivity
  exact integrable_and_integral_le (hm.norm.pow 2) (fun _ => sq_nonneg _) hm0
    (hP.lintegral_norm_sq_pieceField_sub_le h.r₀_pos h.r₀_le')

/-! ### Integration -/

theorem integrable_bound_and_le :
    Integrable (A.bound D) ∧
      ∫ x, A.bound D x ≤ 1 / 2 * (∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2)).toReal +
        excess D.m D.t D.ℓ D.Sd D.r₀ A.pcs.card := by
  obtain ⟨i1, b1⟩ := term_Eβ h
  obtain ⟨i2, b2⟩ := term_Φ h
  obtain ⟨i3, b3⟩ := hA.term_Vflux h
  obtain ⟨i4, b4⟩ := term_nD h
  have i5 := integrable_finsetSum Finset.univ fun j _ => (hA.term_carry h j).1
  have b5 : ∑ j : Fin 4, ∫ x, ‖carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x‖ ^ 2 ≤
      4 * (8 * π ^ 2 / (3 * D.ℓ)) := by
    refine (Finset.sum_le_sum fun j _ => (hA.term_carry h j).2).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  have i6 := integrable_finsetSum A.pcs fun i hi => (hA.term_Pdiff h hi).1
  have b6 : ∑ i ∈ A.pcs, ∫ x, ‖A.Pdiff D i x‖ ^ 2 ≤ A.pcs.card * ePiece D.m D.r₀ := by
    refine (Finset.sum_le_sum fun i hi => (hA.term_Pdiff h hi).2).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
  have j1 := i1.const_mul (1 / 2)
  have j2 := i2.const_mul 2
  have j3 := i3.const_mul 2
  have j4 := i4.const_mul 32
  have j5 := i5.const_mul 6
  have j6 := i6.const_mul 2
  have hsum := integral_add6 j1 j2 j3 j4 j5 j6
  have hfun : A.bound D = fun x =>
      1 / 2 * (Ωp D).indicator (fun y => ‖D.Eβ y‖ ^ 2) x + 2 * D.R.indicator (fun y => ‖D.Φ y‖ ^ 2) x +
        2 * ‖A.Vflux D x‖ ^ 2 + 32 * D.nD x ^ 2 +
        6 * ∑ j : Fin 4, ‖carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x‖ ^ 2 +
        2 * ∑ i ∈ A.pcs, ‖A.Pdiff D i x‖ ^ 2 := rfl
  rw [hfun]
  refine ⟨((((j1.add j2).add j3).add j4).add j5).add j6, ?_⟩
  rw [hsum, integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ fun j _ => (hA.term_carry h j).1,
    integral_finsetSum _ fun i hi => (hA.term_Pdiff h hi).1]
  have hℓ := h.ℓ_pos
  have e : excess D.m D.t D.ℓ D.Sd D.r₀ A.pcs.card = 2 * D.Sd + 2 * (504 * D.ℓ * Gb D.m D.t D.ℓ D.Sd) +
      32 * N2b D.m D.t D.Sd + 6 * (4 * (8 * π ^ 2 / (3 * D.ℓ))) +
        2 * (A.pcs.card * ePiece D.m D.r₀) := by
    unfold excess; field_simp; ring
  rw [e]
  linarith

theorem integrable_cross_and_nonneg : Integrable (A.cross D) ∧ 0 ≤ ∫ x, A.cross D x := by
  have hint : ∀ p ∈ D.K, Integrable fun x => inner ℝ (A.YF D x) (gradient (Fp D p) x) := by
    intro p hp
    have hα := h.hα p (h.K_subset_C hp)
    exact integrable_inner_gradient_of_lipschitz (hA.integrable_YF h)
      (lipschitzWith_truncDiff_sub hα.1 hα.2 p)
  have hfun : A.cross D = fun x => ∑ p ∈ D.K, inner ℝ (A.YF D x) (gradient (Fp D p) x) := rfl
  refine ⟨hfun ▸ integrable_finsetSum _ hint, ?_⟩
  rw [hfun, integral_finsetSum _ hint]
  exact Finset.sum_nonneg fun p hp => hA.integral_inner_YF_Fp_nonneg h hp

theorem aestronglyMeasurable_Erho : AEStronglyMeasurable (A.Erho D) volume := by
  have hfun : A.Erho D = fun x => D.psiX x - kSum D x + A.Vflux D x + A.Vcarry D x +
      ∑ i ∈ A.pcs, A.Pdiff D i x := funext fun x => hA.Erho_eq h x
  have hK : AEStronglyMeasurable (kSum D) volume := by
    have : kSum D = ∑ p ∈ D.K, fun x => gradient (truncLog (D.α p)) (x - p) := by
      funext x; simp [kSum, Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun p _ =>
      ((measurable_gradient _).comp (measurable_id.sub_const _)).aestronglyMeasurable
  have hP : AEStronglyMeasurable (fun x => ∑ i ∈ A.pcs, A.Pdiff D i x) volume := by
    have : (fun x => ∑ i ∈ A.pcs, A.Pdiff D i x) = ∑ i ∈ A.pcs, A.Pdiff D i := by
      funext x; simp [Finset.sum_apply]
    rw [this]
    exact Finset.aestronglyMeasurable_sum _ fun i hi =>
      ((hA.isFillerPiece h hi).isFieldPiece_pieceField h.r₀_pos h.r₀_le').1.aestronglyMeasurable.sub
        ((measurable_gradient _).comp (measurable_id.sub_const _)).aestronglyMeasurable
  rw [hfun]
  exact (((h.integrable_psiX.aestronglyMeasurable.sub hK).add
    (hA.integrable_Vflux h).aestronglyMeasurable).add
      (hA.isFieldPiece_Vcarry h).1.aestronglyMeasurable).add hP

/-- `½ ∫_Q |E'_ρ|² ≤ ½ ∫_Q |E_β|² + excess`, with `E'_ρ ∈ L²(Q)`. -/
theorem integrableOn_and_half_integral_le :
    IntegrableOn (fun x => ‖A.Erho D x‖ ^ 2) D.Q ∧
      1 / 2 * ∫ x in D.Q, ‖A.Erho D x‖ ^ 2 ≤
        1 / 2 * (∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2)).toReal +
          excess D.m D.t D.ℓ D.Sd D.r₀ A.pcs.card := by
  obtain ⟨iB, bB⟩ := hA.integrable_bound_and_le h
  obtain ⟨iC, bC⟩ := hA.integrable_cross_and_nonneg h
  have hint : Integrable fun x => ‖A.Erho D x‖ ^ 2 := by
    refine Integrable.mono' ((iB.sub iC).const_mul 2) ((hA.aestronglyMeasurable_Erho h).norm.pow 2) ?_
    filter_upwards [hA.ae_half_norm_sq_Erho_le h] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.sub_apply]
    linarith
  refine ⟨hint.integrableOn, ?_⟩
  have h1 : ∫ x in D.Q, ‖A.Erho D x‖ ^ 2 ≤ ∫ x, ‖A.Erho D x‖ ^ 2 :=
    setIntegral_le_integral hint (Eventually.of_forall fun _ => sq_nonneg _)
  have h2 : ∫ x, 1 / 2 * ‖A.Erho D x‖ ^ 2 ≤ ∫ x, (A.bound D x - A.cross D x) :=
    integral_mono_ae (hint.const_mul _) (iB.sub iC) (hA.ae_half_norm_sq_Erho_le h)
  rw [integral_const_mul, integral_sub iB iC] at h2
  nlinarith

/-! ### The point terms -/

omit hA in
theorem tauM_r₀_nonpos : tauM D.m D.r₀ ≤ 0 := by
  have h1 : Real.log D.r₀ ≤ 0 := Real.log_nonpos h.r₀_pos.le (by linarith [h.r₀_le])
  have h2 : 0 ≤ π ^ 2 * D.m * D.r₀ ^ 2 := by have := h.m_pos; positivity
  unfold tauM
  nlinarith [Real.pi_pos]

theorem finsum_tau_rho_le :
    ∑ᶠ p ∈ (A.Y D : Set ℂ) ∩ D.Q, tauM D.m (Asm.rho D p) ≤ ∑ p ∈ D.K, tauM D.m (D.α p) := by
  classical
  have hYQ : (A.Y D : Set ℂ) ∩ D.Q = (A.Y D : Set ℂ) :=
    inter_eq_left.2 fun y hy => interior_subset (hA.mem_interior_Q h hy)
  rw [hYQ, finsum_mem_coe_finset, Y, Finset.sum_union (hA.disjoint_K_Z h)]
  have hK : ∑ p ∈ D.K, tauM D.m (Asm.rho D p) = ∑ p ∈ D.K, tauM D.m (D.α p) :=
    Finset.sum_congr rfl fun p hp => by rw [rho_of_mem_K hp]
  have hZ : ∑ z ∈ A.Z, tauM D.m (Asm.rho D z) ≤ 0 :=
    Finset.sum_nonpos fun z hz => by
      rw [rho_of_notMem_K (hA.notMem_K_of_mem_Z h hz)]
      exact tauM_r₀_nonpos h
  rw [hK]
  linarith

/-- **Proposition 4.27**: `G_Q(ρ)[E'; Y] ≤ G_Q(α)[E; C] + c_m n_∂ + excess`. -/
theorem locEnergy_le :
    locEnergy D.m (A.Y D : Set ℂ) (Asm.rho D) (A.E' D) D.Q ≤
      locEnergy D.m D.C D.α D.E D.Q +
        ((cQuarter D.m * D.nBd + excess D.m D.t D.ℓ D.Sd D.r₀ A.pcs.card : ℝ) : EReal) := by
  obtain ⟨hint, hle⟩ := hA.integrableOn_and_half_integral_le h
  have hlin : ∫⁻ x in D.Q, ENNReal.ofReal (‖truncField (A.Y D : Set ℂ) (Asm.rho D) (A.E' D) x‖ ^ 2) =
      ENNReal.ofReal (∫ x in D.Q, ‖A.Erho D x‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => sq_nonneg _)).symm
  have hne : ∫⁻ x in D.Q, ENNReal.ofReal (‖truncField (A.Y D : Set ℂ) (Asm.rho D) (A.E' D) x‖ ^ 2) ≠ ⊤ := by
    rw [hlin]; exact ENNReal.ofReal_ne_top
  rw [Data.locEnergy_eq_coe hne, hlin,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hτ := hA.finsum_tau_rho_le h
  have hK := h.half_add_tau_le
  set a := (∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2)).toReal
  set τK := ∑ p ∈ D.K, tauM D.m (D.α p)
  set ex := excess D.m D.t D.ℓ D.Sd D.r₀ A.pcs.card
  have hreal : 1 / 2 * (∫ x in D.Q, ‖A.Erho D x‖ ^ 2) +
      ∑ᶠ p ∈ (A.Y D : Set ℂ) ∩ D.Q, tauM D.m (Asm.rho D p) ≤ (1 / 2 * a + τK) + ex := by
    change 1 / 2 * (∫ x in D.Q, ‖A.Erho D x‖ ^ 2) ≤ 1 / 2 * a + ex at hle
    linarith
  calc (((1 / 2) * (∫ x in D.Q, ‖A.Erho D x‖ ^ 2) +
        ∑ᶠ p ∈ (A.Y D : Set ℂ) ∩ D.Q, tauM D.m (Asm.rho D p) : ℝ) : EReal)
      ≤ (((1 / 2 * a + τK) + ex : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hreal
    _ = ((1 / 2 * a + τK : ℝ) : EReal) + ((ex : ℝ) : EReal) := EReal.coe_add _ _
    _ ≤ (locEnergy D.m D.C D.α D.E D.Q + ((cQuarter D.m * D.nBd : ℝ) : EReal)) + ((ex : ℝ) : EReal) :=
        add_le_add hK le_rfl
    _ = _ := by rw [add_assoc, ← EReal.coe_add]

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
