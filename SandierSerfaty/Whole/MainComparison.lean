/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.Layered
public import SandierSerfaty.Whole.TruncCompare
public import SandierSerfaty.Screening.NeutralBridge
public import SandierSerfaty.Statements.Whole.Defs.LocalEnergy
public import SandierSerfaty.Statements.Whole.Defs.IsCutoffFamily

/-!
# The main comparison MC (comparison note, Theorem `thm:MC`)

**Theorem** (`twoPi_mul_cubeEnergy_le_localEnergy`). Let `E ∈ 𝒜₁`, `χ = χ_R` a cutoff of the family
(smooth, `0 ≤ χ ≤ 1`, `supp χ ⊆ K_R`, `χ = 1` on `K_{R-1}`, `|∇χ| ≤ L`, `L ≥ 1`), `ℓ/2 + 4 ≤ R`. Then
```
2π F^{□_ℓ}(-E, 1) ≤ W(E, χ_R) + C(L) #(Λ ∩ K_R ∖ □_ℓ),     C(L) = c₀ + π (1 + log L).
```

## Proof

For small `η`, the layered inequality (`twoPi_mul_cubeEnergy_le_locEnergy_layer`) and puncture versus
truncation (`lintegral_truncField_neg_le`) give, for every `t ∈ (0, 1)`,
`2π F - ∑_{p} φ_p(t) ≤ ½ a(t) + ½ ε(η) + π log η · #(Λ ∩ A_t)`, with `a(t) = ∫_{A_t ∩ Ω_η} |E|²`,
`φ_p(t) = 1_{t < χ(p)} (c₀ + π log (L / (χ(p) - t)))` and `ε(η) = M² |S| π η²`. Integrating over
`t ∈ (0, 1)` (layer cake, `∫_0^1 φ_p ≤ C(L)`) gives `2π F ≤ P_η(χ) + ½ ε(η) + C(L) #(Λ ∩ K_R ∖ □_ℓ)`, and
`η ↓ 0` gives MC.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Whole

open Screening

/-- The constant `C(L) = c₀ + π (1 + log L)` of MC. -/
@[expose] noncomputable def mcConst (L : ℝ) : ℝ := cQuarter 1 + Real.pi * (1 + Real.log L)

theorem cQuarter_one_pos : 0 < cQuarter 1 := by
  rw [cQuarter_eq]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  positivity

theorem cQuarter_le_mcConst {L : ℝ} (hL : 1 ≤ L) : cQuarter 1 ≤ mcConst L := by
  unfold mcConst
  have := Real.log_nonneg hL
  have := Real.pi_pos
  nlinarith

/-- `-E ∈ Elec(Λ, 1)` for `E ∈ 𝒜₁` (the sign convention of the comparison note). -/
theorem neg_mem_elec {Λ : Set ℂ} {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E) :
    (fun x => -E x) ∈ elec Λ := by
  refine ⟨hE.1, hE.2.1.neg, fun φ hφ hc => ?_⟩
  simp_rw [inner_neg_left]
  rw [integral_neg, hE.2.2.1 φ hφ hc, neg_neg]

theorem cube_two_mul (R : ℝ) : cube (2 * R) = Icc (-R) R ×ℂ Icc (-R) R := by
  unfold cube
  rw [show 2 * R / 2 = R by ring]

theorem ereal_mul_ne_bot {c : ℝ} (hc : 0 < c) {x : EReal} (hx : x ≠ ⊥) : (c : EReal) * x ≠ ⊥ := by
  induction x using EReal.rec with
  | bot => exact absurd rfl hx
  | top => rw [EReal.coe_mul_top_of_pos hc]; exact top_ne_bot
  | coe y => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

/-- A family cutoff is `L`-Lipschitz. -/
theorem lipschitz_of_gradient_le {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) {L : ℝ}
    (hL : ∀ x, ‖gradient χ x‖ ≤ L) (x y : ℂ) : |χ x - χ y| ≤ L * ‖x - y‖ := by
  have := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := χ) (C := L)
    (fun z _ => hχ.differentiable (by simp) z)
    (fun z _ => by rw [← Torus.norm_gradient_eq]; exact hL z) (mem_univ y) (mem_univ x)
  rwa [Real.norm_eq_abs] at this

/-- **The main comparison MC** (comparison note, Theorem `thm:MC`). -/
theorem twoPi_mul_cubeEnergy_le_localEnergy {Λ : Set ℂ} {E : ℂ → ℂ} (hE : IsAdmissibleField Λ E)
    {χ : ℂ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1) {R : ℝ} (hχs : tsupport χ ⊆ cube (2 * R))
    (hχone : ∀ x ∈ cube (2 * (R - 1)), χ x = 1) {L : ℝ} (hL : 1 ≤ L)
    (hχL : ∀ x, ‖gradient χ x‖ ≤ L) {ℓ : ℝ} (hR : ℓ / 2 + 4 ≤ R) :
    ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ (fun x => -E x) ℓ ≤
      localEnergy Λ E χ + ((mcConst L * (Λ ∩ (cube (2 * R) \ cube ℓ)).ncard : ℝ) : EReal) := by
  set Et : ℂ → ℂ := fun x => -E x with hEtdef
  have hEt : Et ∈ elec Λ := neg_mem_elec hE
  have hC := hE.1
  have hχcont : Continuous χ := hχ.continuous
  have hχzero : ∀ x ∉ cube (2 * R), χ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hχs h)
  have hLip := lipschitz_of_gradient_le hχ hχL
  -- the puncture limit
  obtain ⟨w, hw⟩ := exists_tendsto_punctureFunctional hE hχ hχc
  have hloc : localEnergy Λ E χ = (w : EReal) := hw.limsup_eq
  -- local data on `B̄(0, 2R) ⊇ K_R`
  obtain ⟨S, ρ, M, hρ, hρ2, hM, hS, hdisj, hlocal⟩ := IsAdmissibleField.exists_localData hE (2 * R)
  have hKball : cube (2 * R) ⊆ closedBall 0 (2 * R) := by
    intro x hx
    rw [mem_cube_iff_cubeNorm, cubeNorm] at hx
    rw [mem_closedBall_zero_iff]
    calc ‖x‖ ≤ |x.re| + |x.im| := Complex.norm_le_abs_re_add_abs_im x
      _ ≤ 2 * R := by linarith [le_max_left |x.re| |x.im|, le_max_right |x.re| |x.im|]
  have hAK : ∀ t : ℝ, 0 ≤ t → {x | t < χ x} ⊆ cube (2 * R) := fun t ht x hx => by
    by_contra h
    have h1 : t < χ x := hx
    rw [hχzero x h] at h1
    linarith
  have hAm : ∀ t : ℝ, MeasurableSet {x | t < χ x} := fun t =>
    (isOpen_lt continuous_const hχcont).measurableSet
  -- finite sets of charges
  have hfinK : (Λ ∩ cube (2 * R)).Finite := finite_inter_cube hC (2 * R)
  set SK := hfinK.toFinset with hSK
  have hfin' : (Λ ∩ (cube (2 * R) \ cube ℓ)).Finite :=
    hfinK.subset (inter_subset_inter_right _ sdiff_subset)
  set S' := hfin'.toFinset with hS'def
  have hS' : ∀ p, p ∈ S' ↔ p ∈ Λ ∧ p ∈ cube (2 * R) ∧ p ∉ cube ℓ := fun p => by
    rw [hS'def, Set.Finite.mem_toFinset, mem_inter_iff, Set.mem_sdiff]
  have hncard : ((Λ ∩ (cube (2 * R) \ cube ℓ)).ncard : ℝ) = S'.card := by
    rw [Set.ncard_eq_toFinset_card _ hfin']
  set T := (finite_inter_cube hC (ℓ + 1)).toFinset with hT
  -- the sum of `χ` over the charges
  have hsumχ : ∑ᶠ p ∈ Λ, χ p = ∑ p ∈ SK, χ p := by
    refine Screening.finsum_mem_eq_finsetSum (fun p hp => ((Set.Finite.mem_toFinset _).1 hp).1)
      fun p hpΛ hp => hχzero p fun h => hp ((Set.Finite.mem_toFinset _).2 ⟨hpΛ, h⟩)
  -- the key inequality for a fixed small `η`
  have hkey : ∀ η : ℝ, 0 < η → η < ρ → η ≤ 1 / 4 → (∀ p ∈ T, η ≤ cubeRadius Λ ℓ p) →
      punctureFunctional Λ E χ η = ((punctureFunctional Λ E χ η).toReal : EReal) ∧
      ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ ≤
        (((punctureFunctional Λ E χ η).toReal + M ^ 2 * S.card * (Real.pi * η ^ 2) / 2 +
          mcConst L * S'.card : ℝ) : EReal) := by
    intro η hη hηρ hη4 hηT
    have hηr : ∀ p ∈ Λ, p ∈ cube (ℓ + 1) → η ≤ cubeRadius Λ ℓ p := fun p hp hpc =>
      hηT p ((Set.Finite.mem_toFinset _).2 ⟨hp, hpc⟩)
    set Ω := punctured Λ η with hΩ
    set ε : ℝ := M ^ 2 * S.card * (Real.pi * η ^ 2) with hε
    have hε0 : 0 ≤ ε := by positivity
    set a : ℝ → ℝ := fun t => (∫⁻ x in {x | t < χ x} ∩ Ω, ENNReal.ofReal (‖E x‖ ^ 2)).toReal
      with ha
    set b : ℝ → ℝ := fun t => ∑ p ∈ SK, (Iio (χ p)).indicator (fun _ => (1 : ℝ)) t with hb
    set φ : ℝ → ℝ := fun t => ∑ p ∈ S', logLayer (cQuarter 1) L (χ p) t with hφ
    have hcmp : ∀ t : ℝ, 0 ≤ t →
        (∫⁻ x in {x | t < χ x}, ENNReal.ofReal (‖truncField Λ (fun _ => η) Et x‖ ^ 2)) ≤
          (∫⁻ x in {x | t < χ x} ∩ Ω, ENNReal.ofReal (‖E x‖ ^ 2)) + ENNReal.ofReal ε ∧
        (∫⁻ x in {x | t < χ x} ∩ Ω, ENNReal.ofReal (‖E x‖ ^ 2)) ≠ ⊤ := fun t ht =>
      lintegral_truncField_neg_le hρ2 hS hdisj hlocal hη hηρ (hAm t) ((hAK t ht).trans hKball)
    -- the count of the charges in a layer
    have htau : ∀ t : ℝ, 0 ≤ t →
        ∑ᶠ p ∈ Λ ∩ {x | t < χ x}, tauM 1 ((fun _ => η) p) = tauM 1 η * b t := by
      intro t ht
      have h1 : ∑ᶠ p ∈ Λ ∩ {x | t < χ x}, tauM 1 ((fun _ => η) p) =
          ∑ᶠ p ∈ Λ ∩ {x | t < χ x}, (Iio (χ p)).indicator (fun _ => tauM 1 η) t :=
        finsum_mem_congr rfl fun p hp => by rw [indicator_of_mem (mem_Iio.2 hp.2)]
      have h2 : ∑ᶠ p ∈ Λ ∩ {x | t < χ x}, (Iio (χ p)).indicator (fun _ => tauM 1 η) t =
          ∑ᶠ p ∈ (SK : Set ℂ), (Iio (χ p)).indicator (fun _ => tauM 1 η) t := by
        apply finsum_mem_inter_support_eq
        ext p
        simp only [mem_inter_iff, Finset.mem_coe, hSK, Set.Finite.mem_toFinset, Function.mem_support]
        constructor
        · rintro ⟨⟨hpΛ, hpt⟩, hp0⟩
          exact ⟨⟨hpΛ, hAK t ht hpt⟩, hp0⟩
        · rintro ⟨⟨hpΛ, _⟩, hp0⟩
          refine ⟨⟨hpΛ, ?_⟩, hp0⟩
          by_contra h
          exact hp0 (indicator_of_notMem (fun h' => h (mem_Iio.1 h')) _)
      rw [h1, h2, finsum_mem_coe_finset, hb, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hpt : t < χ p
      · rw [indicator_of_mem (mem_Iio.2 hpt), indicator_of_mem (mem_Iio.2 hpt), mul_one]
      · rw [indicator_of_notMem (fun h => hpt (mem_Iio.1 h)),
          indicator_of_notMem (fun h => hpt (mem_Iio.1 h)), mul_zero]
    have hb0 : ∀ t, 0 ≤ b t := fun t =>
      Finset.sum_nonneg fun p _ => indicator_nonneg (fun _ _ => zero_le_one) _
    have htauη : tauM 1 η ≤ Real.pi * Real.log η := by
      unfold tauM; nlinarith [sq_nonneg η, Real.pi_pos]
    -- the inequality at each level `t`
    have hper : ∀ t ∈ Ioo (0 : ℝ) 1, ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ +
        ((-φ t : ℝ) : EReal) ≤ ((a t / 2 + ε / 2 + Real.pi * Real.log η * b t : ℝ) : EReal) := by
      intro t ht
      have hlay := twoPi_mul_cubeEnergy_le_locEnergy_layer hEt hχcont hχ1 hL hLip hR hχone hχzero
        ht.1 ht.2 hη hη4 hηr hS'
      refine hlay.trans ?_
      unfold locEnergy
      rw [htau t ht.1.le]
      obtain ⟨h1, h2⟩ := hcmp t ht.1.le
      have hX : (((∫⁻ x in {x | t < χ x},
          ENNReal.ofReal (‖truncField Λ (fun _ => η) Et x‖ ^ 2)) : ℝ≥0∞) : EReal) ≤
          ((a t + ε : ℝ) : EReal) := by
        rw [← Screening.coe_ennreal_ofReal_of_nonneg (by positivity : (0 : ℝ) ≤ a t + ε)]
        refine EReal.coe_ennreal_le_coe_ennreal_iff.2 (h1.trans (le_of_eq ?_))
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hε0, ENNReal.ofReal_toReal h2]
      have hτ : tauM 1 η * b t ≤ Real.pi * Real.log η * b t :=
        mul_le_mul_of_nonneg_right htauη (hb0 t)
      calc ((1 / 2 : ℝ) : EReal) * (((∫⁻ x in {x | t < χ x},
              ENNReal.ofReal (‖truncField Λ (fun _ => η) Et x‖ ^ 2)) : ℝ≥0∞) : EReal) +
            ((tauM 1 η * b t : ℝ) : EReal)
          ≤ ((1 / 2 : ℝ) : EReal) * ((a t + ε : ℝ) : EReal) +
            ((Real.pi * Real.log η * b t : ℝ) : EReal) := by
            gcongr
        _ = ((a t / 2 + ε / 2 + Real.pi * Real.log η * b t : ℝ) : EReal) := by
            rw [← EReal.coe_mul, ← EReal.coe_add]; congr 1; ring
    -- `2π F` is a real number
    have hF_top : ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ ≠ ⊤ := by
      intro h
      have := hper (1 / 2) ⟨by norm_num, by norm_num⟩
      rw [h, EReal.top_add_coe] at this
      exact absurd this (not_le.2 (EReal.coe_lt_top _))
    have hF_bot : ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ ≠ ⊥ :=
      ereal_mul_ne_bot (by positivity) (cubeEnergy_ne_bot Λ Et ℓ)
    set Fr := (((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ).toReal with hFr
    have hFeq : ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ = (Fr : EReal) :=
      (EReal.coe_toReal hF_top hF_bot).symm
    have hper' : ∀ t ∈ Ioo (0 : ℝ) 1, Fr - φ t ≤ a t / 2 + ε / 2 + Real.pi * Real.log η * b t := by
      intro t ht
      have := hper t ht
      rw [hFeq, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
      linarith
    -- integrability in `t`
    have hφint : IntegrableOn φ (Ioo (0 : ℝ) 1) :=
      integrable_finsetSum S' fun p _ =>
        (integral_logLayer_le cQuarter_one_pos.le hL (hχ0 p) (hχ1 p)).1
    have hbint : IntegrableOn b (Ioo (0 : ℝ) 1) :=
      integrable_finsetSum SK fun p _ => integrableOn_Ioo_indicator_Iio_one (χ p)
    have haint : IntegrableOn a (Ioo (0 : ℝ) 1) := by
      refine (AntitoneOn.integrableOn_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1)) ?_).mono_set
        Ioo_subset_Icc_self
      intro t ht s _ hts
      exact ENNReal.toReal_mono (hcmp t ht.1).2
        (lintegral_mono_set (inter_subset_inter_left _ fun x hx => lt_of_le_of_lt hts hx))
    have hvol : volume (Ioo (0 : ℝ) 1) = 1 := by simp
    have hconst : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Ioo (0 : ℝ) 1) := fun c =>
      integrableOn_const (by simp)
    have hint1 : ∫ t in Ioo (0 : ℝ) 1, (Fr - φ t) = Fr - ∫ t in Ioo (0 : ℝ) 1, φ t := by
      rw [integral_sub (hconst Fr) hφint, setIntegral_const, Measure.real, hvol]
      simp
    have hint2 : ∫ t in Ioo (0 : ℝ) 1, (a t / 2 + ε / 2 + Real.pi * Real.log η * b t) =
        (∫ t in Ioo (0 : ℝ) 1, a t) / 2 + ε / 2 + Real.pi * Real.log η * ∑ p ∈ SK, χ p := by
      have hb' : ∫ t in Ioo (0 : ℝ) 1, b t = ∑ p ∈ SK, χ p := by
        rw [hb, integral_finsetSum SK fun p _ => integrableOn_Ioo_indicator_Iio_one (χ p)]
        exact Finset.sum_congr rfl fun p _ => integral_Ioo_indicator_Iio_one (hχ0 p) (hχ1 p)
      have i1 : IntegrableOn (fun t => a t / 2) (Ioo (0 : ℝ) 1) := haint.div_const 2
      have i2 : IntegrableOn (fun t => a t / 2 + ε / 2) (Ioo (0 : ℝ) 1) := i1.add (hconst _)
      have i3 : IntegrableOn (fun t => Real.pi * Real.log η * b t) (Ioo (0 : ℝ) 1) :=
        hbint.const_mul _
      rw [integral_add i2 i3, integral_add i1 (hconst _), integral_div, setIntegral_const,
        Measure.real, hvol, integral_const_mul, hb']
      simp
    have hφle : ∫ t in Ioo (0 : ℝ) 1, φ t ≤ mcConst L * S'.card := by
      rw [hφ, integral_finsetSum S' fun p _ =>
        (integral_logLayer_le cQuarter_one_pos.le hL (hχ0 p) (hχ1 p)).1]
      calc ∑ p ∈ S', ∫ t in Ioo (0 : ℝ) 1, logLayer (cQuarter 1) L (χ p) t
          ≤ ∑ _p ∈ S', mcConst L := Finset.sum_le_sum fun p _ =>
            (integral_logLayer_le cQuarter_one_pos.le hL (hχ0 p) (hχ1 p)).2
        _ = mcConst L * S'.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hmono : ∫ t in Ioo (0 : ℝ) 1, (Fr - φ t) ≤
        ∫ t in Ioo (0 : ℝ) 1, (a t / 2 + ε / 2 + Real.pi * Real.log η * b t) :=
      setIntegral_mono_on ((hconst Fr).sub hφint)
        (((haint.div_const 2).add (hconst _)).add (hbint.const_mul _)) measurableSet_Ioo hper'
    rw [hint1, hint2] at hmono
    -- the puncture functional is `½ ∫ a + π log η ∑ χ(p)`
    have hP : punctureFunctional Λ E χ η =
        (((∫ t in Ioo (0 : ℝ) 1, a t) / 2 + Real.pi * Real.log η * ∑ p ∈ SK, χ p : ℝ) : EReal) := by
      have hneg0 : ∀ x, ENNReal.ofReal (-(χ x * ‖E x‖ ^ 2)) = 0 := fun x =>
        ENNReal.ofReal_of_nonpos (neg_nonpos.2 (mul_nonneg (hχ0 x) (sq_nonneg _)))
      have hEm : AEMeasurable (fun x => ENNReal.ofReal (‖E x‖ ^ 2)) volume :=
        (hE.2.1.aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
      have hpos : (∫⁻ x in Ω, ENNReal.ofReal (χ x * ‖E x‖ ^ 2)) =
          ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, a t) := by
        calc (∫⁻ x in Ω, ENNReal.ofReal (χ x * ‖E x‖ ^ 2))
            = ∫⁻ x in Ω, ENNReal.ofReal (χ x) * ENNReal.ofReal (‖E x‖ ^ 2) :=
              lintegral_congr fun x => ENNReal.ofReal_mul (hχ0 x)
          _ = ∫⁻ t in Ioo (0 : ℝ) 1, ∫⁻ x in {x | t < χ x} ∩ Ω, ENNReal.ofReal (‖E x‖ ^ 2) :=
              lintegral_ofReal_mul_eq_lintegral_layers hχcont hχ1 hEm (measurableSet_punctured Λ η)
          _ = ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (a t) :=
              setLIntegral_congr_fun measurableSet_Ioo fun t ht =>
                (ENNReal.ofReal_toReal (hcmp t ht.1.le).2).symm
          _ = ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, a t) :=
              (ofReal_integral_eq_lintegral_ofReal haint
                (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
      unfold punctureFunctional
      have hΩ' : (⋃ p ∈ Λ, ball p η)ᶜ = Ω := rfl
      simp only [hneg0, lintegral_zero]
      rw [hΩ', hpos, hsumχ, Screening.coe_ennreal_ofReal_of_nonneg
        (setIntegral_nonneg measurableSet_Ioo fun _ _ => ENNReal.toReal_nonneg),
        EReal.coe_ennreal_zero, sub_zero, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      ring
    refine ⟨by rw [hP, EReal.toReal_coe], ?_⟩
    rw [hFeq, hP, EReal.toReal_coe, EReal.coe_le_coe_iff]
    linarith
  -- small radii
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ η < ρ ∧ η ≤ 1 / 4 ∧ ∀ p ∈ T, η ≤ cubeRadius Λ ℓ p := by
    refine (eventually_mem_nhdsWithin.mono fun η (h : η ∈ Ioi (0 : ℝ)) => (h : 0 < η)).and ?_
    refine (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hρ)).and ?_
    refine (eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (by norm_num))).and ?_
    exact (Filter.eventually_all_finset T).2 fun p _ =>
      eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (cubeRadius_pos hC ℓ p))
  -- the limit `η ↓ 0`
  have hreal : Tendsto (fun η => (punctureFunctional Λ E χ η).toReal) (𝓝[>] 0) (𝓝 w) := by
    have h1 : Tendsto (fun η => (((punctureFunctional Λ E χ η).toReal : ℝ) : EReal)) (𝓝[>] 0)
        (𝓝 (w : EReal)) :=
      hw.congr' (hev.mono fun η hη => (hkey η hη.1 hη.2.1 hη.2.2.1 hη.2.2.2).1)
    exact EReal.tendsto_coe.1 h1
  have hε : Tendsto (fun η : ℝ => M ^ 2 * S.card * (Real.pi * η ^ 2) / 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun η : ℝ => M ^ 2 * S.card * (Real.pi * η ^ 2) / 2) (𝓝 0)
        (𝓝 (M ^ 2 * S.card * (Real.pi * 0 ^ 2) / 2)) :=
      ((continuous_const.mul (continuous_const.mul (continuous_id.pow 2))).div_const 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun η => ((((punctureFunctional Λ E χ η).toReal +
      M ^ 2 * S.card * (Real.pi * η ^ 2) / 2 + mcConst L * S'.card : ℝ)) : EReal)) (𝓝[>] 0)
      (𝓝 (((w + 0 + mcConst L * S'.card : ℝ)) : EReal)) :=
    continuous_coe_real_ereal.continuousAt.tendsto.comp ((hreal.add hε).add_const _)
  have hle := ge_of_tendsto hlim (hev.mono fun η hη => (hkey η hη.1 hη.2.1 hη.2.2.1 hη.2.2.2).2)
  rw [hloc, hncard, ← EReal.coe_add]
  simpa using hle

end Whole

end SandierSerfaty

end
