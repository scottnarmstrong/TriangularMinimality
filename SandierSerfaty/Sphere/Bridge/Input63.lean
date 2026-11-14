/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Bridge.Input63Field
public import SandierSerfaty.Sphere.Bridge.NeumannProjection
public import SandierSerfaty.Sphere.Lower.Counting
public import SandierSerfaty.Sphere.Lower.Quantize
public import SandierSerfaty.Screening.ScreenTheorem

/-!
# The sphere note's Input 6.3 from the screening theorem I4 (screening note, Proposition 7.2)

**The pinned statement is mis-parenthesized.** In `Lower.Input63Statement`
(`SandierSerfaty/Sphere/Lower/Statements.lean`) the right side is written
`… - 2 * Real.pi * m * ∑ p ∈ X, ∫ x in sqAt a₀ t, truncLog (1 / 4) (x - p) + CS * (…)`. The
integral `∫` extends as far right as possible (the body of `∑` stops before `+`, but here the body of the `∑` is the
integral, which swallows the error term), so Lean reads the error term *inside* the integral, hence inside the sum:
`… - 2π m ∑_{p ∈ X} ∫_Q (f_{1/4}(x - p) + C_S (ℓ S/ℓ̃ + t ℓ̃ + |n̄ - p|)) dx`. Then the error term enters
with the factor `-2π m p t² < 0` and not `+1`. This is not the sphere note's Input 6.3, and it is in general
false. `Bridge.Input63StatementRepaired` is the statement with the intended parentheses (all hypotheses
unchanged), and `Bridge.input63StatementRepaired` proves it.

**Proof** (screening note, §7, Proposition 7.2). Apply I4 (`Screening.exists_screened_neumannChargeField`) with
`C = X`, `E = g + ∑ ∇f_{1/4}(· - p)` (`Bridge.input63Field`, a charge field on `(Q^{1/2})°` by
`Bridge.isChargeField_input63Field`), `α ≡ 1/4`, `ℓc = ℓ`, `ℓt = ℓ̃`. The output `(Y, ρ, E')` satisfies
`W^Neu_Q(Y; m) ≤ G_Q(ρ)[E']` (Lemma 7.1, `Bridge.neumannEnergy_le_locEnergy`). Then
`G_Q(1/4)[E] = ½ ∫_Q |g|² + p (π log ¼ - π² m/16) ≤ ½ ∫_Q |g|² + π p log ¼ - 2π m ∑ ∫_Q f_{1/4}(· - p)`, since
`∫_Q f_{1/4}(· - p) ≤ π/32`. Finally the boundary count `n_∂ ≤ (48/π) t ℓ̃` (`Bridge.ncard_boundary_le`,
from Lemma 6.5) gives the constant `C_S' = (1 + 48/π) C_S + 1`. The condition `ℓ ≥ 4 m₊/m₋` is not used.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal Real ContDiff Laplacian Pointwise

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

open Lower Screening

open scoped Classical in
/-- **Input 6.3, repaired parentheses.** `Lower.Input63Statement` with the error term
`C_S (ℓ S/ℓ̃ + t ℓ̃ + |n̄ - p|)` outside the sum and the integral, as in the sphere note Input 6.3. All
hypotheses are those of `Lower.Input63Statement`. -/
@[expose] def Input63StatementRepaired : Prop :=
  ∀ {mLo mHi : ℝ}, 0 < mLo → mLo ≤ mHi → mHi ≤ 1 / 150 →
    ∃ CS Cscr ℓ₀ : ℝ, 1 ≤ CS ∧ 1 ≤ Cscr ∧ 1 ≤ ℓ₀ ∧
      ∀ (a₀ : ℂ) (t m ℓ ℓt : ℝ) (nb : ℕ) (X : Finset ℂ) (w : ℂ → ℝ) (g : ℂ → ℂ),
        mLo ≤ m → m ≤ mHi → (nb : ℝ) = m * t ^ 2 →
        max (4 * mHi / mLo) ℓ₀ ≤ ℓ → ℓ ≤ ℓt → ℓt ≤ t / 8 →
        (↑X : Set ℂ) ⊆ sqAt a₀ t → (∀ p ∈ X, ∀ q ∈ X, p ≠ q → 1 ≤ ‖p - q‖) →
        HasWeakGradientOn (sqAt a₀ t) (fun x => w x - ∑ p ∈ X, truncLog (1 / 4) (x - p)) g →
        (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ interior (sqShrink a₀ t (1 / 2)) →
          -(∫ x, w x * Δ φ x) =
            2 * Real.pi * ((∑ p ∈ X.filter (· ∈ sqShrink a₀ t (1 / 2)), φ p) - m * ∫ x, φ x)) →
        (∫ x in sqShrink a₀ t (ℓt / 2) \ sqShrink a₀ t (2 * ℓt), ‖g x‖ ^ 2) ≤ ℓ ^ 3 * ℓt / Cscr →
        ∃ Y : Fin nb → ℂ, Function.Injective Y ∧ (∀ i, Y i ∈ interior (sqAt a₀ t)) ∧
          neumannEnergy a₀ t m Y ≤
            (1 / 2 : ℝ) * (∫ x in sqAt a₀ t, ‖g x‖ ^ 2) + Real.pi * X.card * Real.log (1 / 4) -
              2 * Real.pi * m * (∑ p ∈ X, ∫ x in sqAt a₀ t, truncLog (1 / 4) (x - p)) +
              CS * (ℓ * (∫ x in sqShrink a₀ t (ℓt / 2) \ sqShrink a₀ t (2 * ℓt), ‖g x‖ ^ 2) / ℓt +
                t * ℓt + |(nb : ℝ) - X.card|)

/-! ### The boundary count -/

theorem volume_sq (c : ℂ) (s : ℝ) : volume (sq c s) = ENNReal.ofReal s * ENNReal.ofReal s := by
  have : sq c s = sqAt (c - ⟨s / 2, s / 2⟩) s := by
    rw [sqAt_eq_sq]; congr 1; apply Complex.ext <;> simp
  rw [this, volume_sqAt]

theorem add_ball_subset {c : ℂ} {t ℓt : ℝ} :
    (sq c t \ sq c (t - 4 * ℓt)) + ball (0 : ℂ) (1 / 2) ⊆ sq c (t + 1) \ sq c (t - 4 * ℓt - 1) := by
  rintro x ⟨a, ha, b, hb, rfl⟩
  show a + b ∈ _
  have hA := sq_diff_sq_eq c t 0 (2 * ℓt)
  rw [mul_zero, sub_zero, show t - 2 * (2 * ℓt) = t - 4 * ℓt by ring] at hA
  rw [hA] at ha
  have hb' : ‖b‖ < 1 / 2 := by simpa using hb
  have hd := abs_sqDepth_sub_le c t (a + b) a
  rw [add_sub_cancel_left] at hd
  have hd' := abs_le.1 (hd.trans hb'.le)
  refine ⟨?_, ?_⟩
  · rw [show t + 1 = t - 2 * (-(1 / 2)) by ring, mem_sq_iff_le_sqDepth]
    linarith [ha.1]
  · rw [show t - 4 * ℓt - 1 = t - 2 * (2 * ℓt + 1 / 2) by ring, mem_sq_iff_le_sqDepth, not_le]
    have := abs_sqDepth_sub_le c t (a + b) a
    rw [add_sub_cancel_left] at this
    have h2 := (abs_le.1 this).2
    linarith [ha.2]

theorem ncard_inter_mul_le_volume {S : Finset ℂ} (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖)
    (A : Set ℂ) :
    (((↑S : Set ℂ) ∩ A).ncard : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 4) ≤
      volume (A + ball (0 : ℂ) (1 / 2)) := by
  have h := card_filter_mul_le_volume hS A
  convert h using 3
  rw [← ncard_coe_finset, Finset.coe_filter]
  rfl

/-- **The boundary count**: `n_∂ = #(X ∩ (Q ∖ sq c (t - 4ℓ̃))) ≤ (48/π) t ℓ̃` for `1`-separated `X`. -/
theorem ncard_boundary_le {X : Finset ℂ} (hX : ∀ p ∈ X, ∀ q ∈ X, p ≠ q → 1 ≤ ‖p - q‖) {c : ℂ}
    {t ℓt : ℝ} (hℓt : 1 ≤ ℓt) (ht : 8 * ℓt ≤ t) :
    (((↑X : Set ℂ) ∩ (sq c t \ sq c (t - 4 * ℓt))).ncard : ℝ) ≤ 48 / π * (t * ℓt) := by
  have h := ncard_inter_mul_le_volume hX (sq c t \ sq c (t - 4 * ℓt))
  have hsub := measure_mono (μ := volume) (add_ball_subset (c := c) (t := t) (ℓt := ℓt))
  have hsmall : sq c (t - 4 * ℓt - 1) ⊆ sq c (t + 1) := by
    intro x hx
    rw [mem_sq_iff, mem_Icc, mem_Icc] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hb : 0 ≤ t - 4 * ℓt - 1 := by linarith
  rw [measure_sdiff hsmall (measurableSet_sq _ _).nullMeasurableSet
    (by rw [volume_sq]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    volume_sq, volume_sq, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_sub _ (by positivity)] at hsub
  have h2 := h.trans hsub
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by nlinarith)] at h2
  have hπ := Real.pi_pos
  have h3 : (t + 1) * (t + 1) - (t - 4 * ℓt - 1) * (t - 4 * ℓt - 1) ≤ 12 * (t * ℓt) := by nlinarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hπ]
  linarith

/-! ### The energy of the data -/

theorem setIntegral_truncLog_le (S : Set ℂ) (p : ℂ) :
    ∫ x in S, truncLog (1 / 4) (x - p) ≤ π / 32 := by
  have hi : Integrable (fun x => truncLog (1 / 4 : ℝ) (x - p)) :=
    (integrable_truncLog (by norm_num)).comp_sub_right p
  refine (setIntegral_le_integral hi (Eventually.of_forall fun x => truncLog_nonneg _ _)).trans_eq ?_
  rw [integral_sub_right_eq_self (fun x => truncLog (1 / 4 : ℝ) x) p,
    Torus.integral_truncLog (by norm_num)]
  ring

theorem card_mul_tauM_le (X : Finset ℂ) (S : Set ℂ) {m : ℝ} (hm : 0 ≤ m) :
    (X.card : ℝ) * tauM m (1 / 4) ≤
      π * X.card * Real.log (1 / 4) - 2 * π * m * ∑ p ∈ X, ∫ x in S, truncLog (1 / 4) (x - p) := by
  have h : ∑ p ∈ X, ∫ x in S, truncLog (1 / 4) (x - p) ≤ X.card * (π / 32) := by
    have := Finset.sum_le_card_nsmul X (fun p => ∫ x in S, truncLog (1 / 4) (x - p)) (π / 32)
      fun p _ => setIntegral_truncLog_le S p
    rwa [nsmul_eq_mul] at this
  have hπ := Real.pi_pos
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * π * m)
  unfold tauM
  linarith

/-! ### The mismatch with the pinned statement -/

/-! ### Input 6.3 -/

/-- **The sphere note's Input 6.3 (with repaired parentheses) from the screening theorem I4.** -/
theorem input63StatementRepaired : Input63StatementRepaired := by
  intro mLo mHi hmLo hm _hm150
  obtain ⟨ℓ₀, Cscr, CS, hℓ₀, hCscr, hCS, hI4⟩ := exists_screened_neumannChargeField hmLo hm
  refine ⟨(1 + 48 / π) * CS + 1, max Cscr 1, max ℓ₀ 1, ?_, le_max_right _ _, le_max_right _ _, ?_⟩
  · have := Real.pi_pos
    have : 0 ≤ (1 + 48 / π) * CS := by positivity
    linarith
  intro a₀ t m ℓ ℓt nb X w g hm1 hm2 hnb hℓ hℓℓt hℓt hXQ hXsep hw hΔ hS
  have hπ := Real.pi_pos
  have hℓ1 : max ℓ₀ 1 ≤ ℓ := (le_max_right _ _).trans hℓ
  have hℓ₀ℓ : ℓ₀ ≤ ℓ := (le_max_left _ _).trans hℓ1
  have hℓpos : 1 ≤ ℓ := (le_max_right _ _).trans hℓ1
  have hℓt1 : 1 ≤ ℓt := hℓpos.trans hℓℓt
  have ht8 : 8 * ℓt ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hm0 : 0 < m := hmLo.trans_le hm1
  have hnb1 : 1 ≤ nb := by
    have : (0 : ℝ) < nb := by rw [hnb]; positivity
    exact_mod_cast this
  set c : ℂ := a₀ + ⟨t / 2, t / 2⟩ with hc
  have hQ : sqAt a₀ t = sq c t := sqAt_eq_sq a₀ t
  have hU : sqShrink a₀ t (1 / 2) = sq c (t - 1) := by
    show sqShrink a₀ t (1 / 2) = sq (a₀ + ⟨t / 2, t / 2⟩) (t - 1)
    rw [sqShrink_eq_sq]; norm_num
  have hstrip : sqShrink a₀ t (ℓt / 2) \ sqShrink a₀ t (2 * ℓt) =
      sq c (t - ℓt) \ sq c (t - 4 * ℓt) := by
    rw [sqShrink_eq_sq, sqShrink_eq_sq]; congr 2 <;> ring
  set E := input63Field X g with hEdef
  have htrunc : ∀ x, truncField (↑X) (fun _ => 1 / 4) E x = g x := truncField_input63Field X g
  have hE : IsChargeField (interior (sq c (t - 1))) m (↑X) E := by
    rw [← hU]; exact isChargeField_input63Field hw hΔ
  have hgsq : IntegrableOn (fun x => ‖g x‖ ^ 2) (sqAt a₀ t) := hw.2.1.norm.integrable_sq
  have hL2 : ∫⁻ x in sq c t, ENNReal.ofReal (‖truncField (↑X) (fun _ => 1 / 4) E x‖ ^ 2) ≠ ⊤ := by
    simp only [htrunc]; rw [← hQ]; exact hgsq.lintegral_lt_top.ne
  have hstripQ : sq c (t - ℓt) \ sq c (t - 4 * ℓt) ⊆ sq c t := by
    intro x hx
    have := hx.1
    rw [mem_sq_iff, mem_Icc, mem_Icc] at this ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := this
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hSfin : ∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
      ENNReal.ofReal (‖truncField (↑X) (fun _ ↦ 1 / 4) E x‖ ^ 2) ≠ ⊤ :=
    ne_top_of_le_ne_top hL2 (lintegral_mono_set hstripQ)
  set Sv := ∫ x in sqShrink a₀ t (ℓt / 2) \ sqShrink a₀ t (2 * ℓt), ‖g x‖ ^ 2 with hSv
  have hSeq : (∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
      ENNReal.ofReal (‖truncField (↑X) (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal = Sv := by
    simp only [htrunc]
    rw [hSv, hstrip, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
      ((hgsq.mono_set (hQ ▸ hstripQ)).aestronglyMeasurable)]
  have hSb : (∫⁻ x in sq c (t - ℓt) \ sq c (t - 4 * ℓt),
      ENNReal.ofReal (‖truncField (↑X) (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal ≤ ℓ ^ 3 * ℓt / Cscr := by
    rw [hSeq]
    exact hS.trans (div_le_div_of_nonneg_left (by positivity) hCscr (le_max_left _ _))
  have hXfin : ∀ R : ℝ, ((↑X : Set ℂ) ∩ closedBall 0 R).Finite := fun R =>
    X.finite_toSet.inter_of_left _
  obtain ⟨Y, ρ, E', hcard, hYQ, hρ, hdisj, hE', hloc⟩ := hI4 c t m ℓ ℓt nb (↑X) (fun _ => 1 / 4) E
    hm1 hm2 hnb.symm hℓ₀ℓ hℓℓt ht8 hXfin hE (fun _ _ => by norm_num) (fun _ _ _ => rfl)
    (fun p hp q hq hpq => by
      have := hXsep p hp.1 q hq.1 hpq
      linarith) hL2 hSfin hSb
  rw [hSeq] at hloc
  -- the points as a function
  set Yf : Fin nb → ℂ := fun i => ((Y.equivFin.symm (Fin.cast hcard.symm i) : Y) : ℂ) with hYf
  have hYfi : Function.Injective Yf := fun i j h =>
    Fin.cast_injective _ (Y.equivFin.symm.injective (Subtype.ext h))
  have hYfmem : ∀ i, Yf i ∈ Y := fun i => (Y.equivFin.symm (Fin.cast hcard.symm i)).2
  have hYfsurj : ∀ y ∈ Y, ∃ i, Yf i = y := fun y hy =>
    ⟨Fin.cast hcard (Y.equivFin ⟨y, hy⟩), by simp [hYf]⟩
  have himage : Finset.univ.image Yf = Y := by
    ext y; simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ => hi ▸ hYfmem i, hYfsurj y⟩
  have hrange : range Yf = ↑Y := by
    rw [← coe_image_univ, himage]
  have hW := neumannEnergy_le_locEnergy (a₀ := a₀) (ρ := ρ) hnb1 hm0 ht0 hnb hYfi
    (fun i => hQ ▸ hYQ _ (hYfmem i)) (fun i => (hρ _ (hYfmem i)).1)
    (fun i => hQ ▸ (hρ _ (hYfmem i)).2.2)
    (fun i j hij => hdisj _ (hYfmem i) _ (hYfmem j) (fun h => hij (hYfi h)))
    (E := E') (by rw [himage, hQ]; exact hE')
  rw [hrange, hQ] at hW
  have hW2 := hW.trans hloc
  -- the energy of the data
  have hXQ' : (↑X : Set ℂ) ∩ sq c t = ↑X := inter_eq_left.2 (hQ ▸ hXQ)
  rw [locEnergy_eq_coe hL2, hXQ', finsum_mem_coe_finset, Finset.sum_const, nsmul_eq_mul,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hW2
  simp only [htrunc] at hW2
  have hG : (∫⁻ x in sq c t, ENNReal.ofReal (‖g x‖ ^ 2)).toReal = ∫ x in sqAt a₀ t, ‖g x‖ ^ 2 := by
    rw [← hQ, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
      hgsq.aestronglyMeasurable]
  rw [hG] at hW2
  have hτ := card_mul_tauM_le X (sqAt a₀ t) hm0.le
  have hcount := ncard_boundary_le hXsep (c := c) hℓt1 ht8
  -- the constant chase
  set a1 := ℓ * Sv / ℓt with ha1
  set b1 := t * ℓt with hb1
  set d1 := |(nb : ℝ) - X.card| with hd1
  set n1 := (((↑X : Set ℂ) ∩ (sq c t \ sq c (t - 4 * ℓt))).ncard : ℝ) with hn1
  have hSv0 : 0 ≤ Sv := setIntegral_nonneg_of_ae (Eventually.of_forall fun x => by positivity)
  have ha0 : 0 ≤ a1 := by positivity
  have hb0 : 0 ≤ b1 := by positivity
  have hd0 : 0 ≤ d1 := abs_nonneg _
  have hK : 0 ≤ 48 / π := by positivity
  have hc1 : CS * n1 ≤ CS * (48 / π * b1) := mul_le_mul_of_nonneg_left hcount hCS.le
  have hc2 : CS * (a1 + b1 + n1) ≤ ((1 + 48 / π) * CS + 1) * (a1 + b1 + d1) := by
    have e : ((1 + 48 / π) * CS + 1) * (a1 + b1 + d1) =
        CS * (a1 + b1) + CS * (48 / π * b1) +
          (CS * d1 + 48 / π * CS * (a1 + d1) + (a1 + b1 + d1)) := by ring
    have : 0 ≤ CS * d1 + 48 / π * CS * (a1 + d1) + (a1 + b1 + d1) := by positivity
    rw [e, mul_add CS (a1 + b1) n1]
    linarith
  refine ⟨Yf, hYfi, fun i => hQ ▸ hYQ _ (hYfmem i), ?_⟩
  linarith

/-- **Input 6.3** in the form the sphere lower bound consumes (`Lower.Input63Statement`, whose error term is
parenthesized as in `Input63StatementRepaired` and the sphere note Input 6.3). -/
theorem input63Statement : Lower.Input63Statement := input63StatementRepaired

end Bridge

end Sphere

end SandierSerfaty

end
