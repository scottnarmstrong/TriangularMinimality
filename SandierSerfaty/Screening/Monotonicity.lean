/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Pairing
public import SandierSerfaty.Screening.TruncDiff
public import SandierSerfaty.Screening.EnergyExpansion

/-!
# Lemma 4.13 in field form, exact (I2)

**I2** (`locEnergy_eq_add_truncInteraction`; [Serfaty, *Lectures on Coulomb and Riesz gases*, Lemma 4.13]; the comparison note's
Proposition `prop:mono`): for a charge field `E` of density `m` in an open set `U`, radii
`0 < α ≤ β` on `C` and a bounded measurable set `D` such that every changed ball `B̄(p, β_p)`
(`α_p < β_p`) lies in `U ∩ D`, and `E_α ∈ L²(D)`,
`G_D(β) = G_D(α) + π ∑_{i : α_i < β_i} ∑_{q ≠ i} ⟨f_{α_i,β_i}(· - i), δ_q^{(α_q)} + δ_q^{(β_q)}⟩`.
The interaction is `≤ 0` (`truncInteraction_nonpos`) and vanishes when the changed balls are
disjoint from all others (`truncInteraction_eq_zero`).

Proof (comparison note, §3): `E_β = E_α + ∑_{i ∈ I} ∇F_i` a.e., `F_i = f_{α_i,β_i}(· - i)` Lipschitz with
support in `B̄(i, β_i)`; expand the square on the changed balls (`lintegral_norm_sq_perturb`), pair
`E_α` with `∇F_i` by I1 and `∇F_i` with `∇F_j` by `integral_inner_gradient_truncLog_sub_lipschitz`,
then collect the terms (`interaction_algebra`).
-/

open MeasureTheory Metric Filter Topology Set InnerProductSpace
open scoped ENNReal NNReal ContDiff Real

public section

namespace SandierSerfaty

namespace Screening

/-! ### The functions `F_i = f_{α_i,β_i}(· - i)` -/

theorem gradient_truncDiff_sub_eq_zero {a b : ℝ} {i x : ℂ} (hx : x ∉ closedBall i b) :
    gradient (fun y => truncDiff a b (y - i)) x = 0 :=
  gradient_eq_zero_of_notMem_tsupport fun h => hx (tsupport_truncDiff_subset a b i h)

theorem norm_gradient_truncDiff_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (i x : ℂ) :
    ‖gradient (fun y => truncDiff a b (y - i)) x‖ ≤ a⁻¹ := by
  have h := norm_gradient_le_of_lipschitz (lipschitzWith_truncDiff_sub ha hab i) x
  rwa [Real.coe_toNNReal _ (inv_nonneg.2 ha.le)] at h

theorem integrable_gradient_truncDiff_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (i : ℂ) :
    Integrable (gradient fun y => truncDiff a b (y - i)) volume :=
  ((integrable_gradient_truncLog ha i).sub (integrable_gradient_truncLog (ha.trans_le hab) i)).congr
    (Filter.EventuallyEq.symm (ae_gradient_truncDiff_sub ha hab i))

theorem truncDiff_sub_eq_zero_of_far {a b : ℝ} {i x : ℂ} (hx : x ∉ closedBall i b) :
    truncDiff a b (x - i) = 0 :=
  truncDiff_eq_zero (by rw [mem_closedBall, dist_eq_norm, not_le] at hx; exact hx.le)

/-- `⨍_{∂B(q, r)} f_{α_i,β_i}(· - i)`. -/
@[expose] noncomputable def avgF (α β : ℂ → ℝ) (i q : ℂ) (r : ℝ) : ℝ :=
  Real.circleAverage (fun y => truncDiff (α i) (β i) (y - i)) q r

/-! ### The truncated field changes only on the changed balls -/

/-- `E_β = E_α + ∑_{i ∈ I} (∇f_{α_i}(· - i) - ∇f_{β_i}(· - i))` everywhere. -/
theorem truncField_eq_add {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) {α β : ℂ → ℝ}
    (hα : ∀ p ∈ C, 0 < α p) (hαβ : ∀ p ∈ C, α p ≤ β p) {M : ℝ} (hβM : ∀ p ∈ C, β p ≤ M)
    (E : ℂ → ℂ) {IF : Finset ℂ} (hIF : ∀ p, p ∈ IF ↔ p ∈ C ∧ α p < β p) (x : ℂ) :
    truncField C β E x = truncField C α E x +
      ∑ i ∈ IF, (gradient (truncLog (α i)) (x - i) - gradient (truncLog (β i)) (x - i)) := by
  have hβ : ∀ p ∈ C, 0 < β p := fun p hp => (hα p hp).trans_le (hαβ p hp)
  have hαM : ∀ p ∈ C, α p ≤ M := fun p hp => (hαβ p hp).trans (hβM p hp)
  rw [truncField_eq_sum hC hβ hβM E (le_refl ‖x‖), truncField_eq_sum hC hα hαM E (le_refl ‖x‖)]
  set T := (hC (‖x‖ + M)).toFinset
  set h : ℂ → ℂ := fun p => gradient (truncLog (α p)) (x - p) - gradient (truncLog (β p)) (x - p)
  have h1 : ∑ᶠ p ∈ C, h p = ∑ p ∈ T, h p :=
    finsum_mem_eq_finsetSum (fun p hp => mem_of_mem_toFinset _ hp) fun p hpC hp => by
      have hfar := lt_norm_of_notMem_toFinset _ hpC hp
      simp only [h, gradient_truncLog_far (hα p hpC) (hαM p hpC) (le_refl ‖x‖) hfar,
        gradient_truncLog_far (hβ p hpC) (hβM p hpC) (le_refl ‖x‖) hfar, sub_zero]
  have h2 : ∑ᶠ p ∈ C, h p = ∑ p ∈ IF, h p :=
    finsum_mem_eq_finsetSum (fun p hp => ((hIF p).1 hp).1) fun p hpC hp => by
      have : α p = β p := le_antisymm (hαβ p hpC) (not_lt.1 fun h' => hp ((hIF p).2 ⟨hpC, h'⟩))
      simp only [h, this, sub_self]
  have h3 : ∑ p ∈ T, h p = (∑ p ∈ T, gradient (truncLog (α p)) (x - p)) -
      ∑ p ∈ T, gradient (truncLog (β p)) (x - p) := Finset.sum_sub_distrib _ _
  rw [← h2, h1, h3]
  abel

/-! ### The two pairings -/

/-- `∫ ⟪E_α, ∑_i ∇F_i⟫ = ∑_i 2π (∑_{q ∈ C} ⨍_{∂B(q, α_q)} F_i - m ∫ F_i)` (I1). -/
theorem integral_inner_truncField_sum_gradient {U : Set ℂ} (hU : IsOpen U) {m : ℝ} {C : Set ℂ}
    (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) {E : ℂ → ℂ} (hE : IsChargeField U m C E)
    {α β : ℂ → ℝ} (hα : ∀ p ∈ C, 0 < α p) (hαβ : ∀ p ∈ C, α p ≤ β p) {M : ℝ}
    (hβM : ∀ p ∈ C, β p ≤ M) {IF : Finset ℂ} (hIC : ∀ i ∈ IF, i ∈ C)
    (hIU : ∀ i ∈ IF, closedBall i (β i) ⊆ U) :
    (∫ x, inner ℝ (truncField C α E x)
      (∑ i ∈ IF, gradient (fun y => truncDiff (α i) (β i) (y - i)) x)) =
      ∑ i ∈ IF, 2 * π * ((∑ᶠ q ∈ C, avgF α β i q (α q)) - m * (π * (α i ^ 2 - β i ^ 2) / 2)) := by
  have hαb : ∃ M, ∀ p ∈ C, α p ≤ M := ⟨M, fun p hp => (hαβ p hp).trans (hβM p hp)⟩
  have hint : ∀ i ∈ IF, Integrable (fun x => inner ℝ (truncField C α E x)
      (gradient (fun y => truncDiff (α i) (β i) (y - i)) x)) volume := fun i hi =>
    integrable_inner_of_integrableOn (isCompact_closedBall i (β i)).measurableSet
      (integrableOn_truncField hC hE.1 hα hαb (isCompact_closedBall _ _) (hIU i hi))
      (aestronglyMeasurable_gradient _)
      (norm_gradient_truncDiff_sub_le (hα i (hIC i hi)) (hαβ i (hIC i hi)) i)
      (fun x hx => gradient_truncDiff_sub_eq_zero hx)
  simp_rw [inner_sum]
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [integral_inner_truncField_lipschitz hU hC hE hα hαb
    (lipschitzWith_truncDiff_sub (hα i (hIC i hi)) (hαβ i (hIC i hi)) i)
    (hasCompactSupport_truncDiff _ _ i) ((tsupport_truncDiff_subset _ _ i).trans (hIU i hi)),
    integral_truncDiff_sub (hα i (hIC i hi)) (hαβ i (hIC i hi))]
  rfl

/-- `∫ |∑_i ∇F_i|² = ∑_j ∑_i 2π (⨍_{∂B(i, β_i)} F_j - ⨍_{∂B(i, α_i)} F_j)`. -/
theorem integral_norm_sq_sum_gradient {α β : ℂ → ℝ} {IF : Finset ℂ} (hα : ∀ i ∈ IF, 0 < α i)
    (hαβ : ∀ i ∈ IF, α i ≤ β i) :
    (∫ x, ‖∑ i ∈ IF, gradient (fun y => truncDiff (α i) (β i) (y - i)) x‖ ^ 2) =
      ∑ j ∈ IF, ∑ i ∈ IF, 2 * π * (avgF α β j i (β i) - avgF α β j i (α i)) := by
  have hpair : ∀ i ∈ IF, ∀ j ∈ IF, Integrable (fun x =>
      inner ℝ (gradient (fun y => truncDiff (α i) (β i) (y - i)) x)
        (gradient (fun y => truncDiff (α j) (β j) (y - j)) x)) volume := fun i hi j hj =>
    integrable_inner_of_integrableOn MeasurableSet.univ
      (integrable_gradient_truncDiff_sub (hα i hi) (hαβ i hi) i).integrableOn
      (aestronglyMeasurable_gradient _) (norm_gradient_truncDiff_sub_le (hα j hj) (hαβ j hj) j)
      (fun x hx => absurd (mem_univ x) hx)
  simp only [← real_inner_self_eq_norm_sq]
  simp only [inner_sum]
  simp only [sum_inner]
  rw [integral_finsetSum _ fun j hj => integrable_finsetSum _ fun i hi => hpair i hi j hj]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_finsetSum _ fun i hi => hpair i hi j hj]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hae : (fun x => inner ℝ (gradient (fun y => truncDiff (α i) (β i) (y - i)) x)
      (gradient (fun y => truncDiff (α j) (β j) (y - j)) x)) =ᵐ[volume]
      fun x => inner ℝ (gradient (truncLog (α i)) (x - i) - gradient (truncLog (β i)) (x - i))
        (gradient (fun y => truncDiff (α j) (β j) (y - j)) x) := by
    filter_upwards [ae_gradient_truncDiff_sub (hα i hi) (hαβ i hi) i] with x hx
    rw [hx]
  rw [integral_congr_ae hae, integral_inner_gradient_truncLog_sub_lipschitz (hα i hi)
    ((hα i hi).trans_le (hαβ i hi)) i (lipschitzWith_truncDiff_sub (hα j hj) (hαβ j hj) j)
    (hasCompactSupport_truncDiff _ _ j)]
  rfl

/-! ### Collecting the terms -/

theorem sum_split_aux (s : Finset ℂ) (x y t : ℂ → ℝ) :
    (1 / 2 : ℝ) * (2 * ∑ i ∈ s, x i + ∑ i ∈ s, y i) + ∑ i ∈ s, t i =
      ∑ i ∈ s, ((1 / 2 : ℝ) * (2 * x i + y i) + t i) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- The algebra of the comparison note's §3 ("Collecting"). -/
theorem interaction_algebra {IF Q : Finset ℂ} (hIQ : IF ⊆ Q) (α β : ℂ → ℝ) (m : ℝ)
    (a b : ℂ → ℂ → ℝ) (hab : ∀ i ∈ IF, ∀ q ∈ Q, q ∉ IF → a i q = b i q)
    (haii : ∀ i ∈ IF, a i i = Real.log (α i) - Real.log (β i)) (hbii : ∀ i ∈ IF, b i i = 0) :
    (1 / 2 : ℝ) * (2 * (∑ i ∈ IF, 2 * π * ((∑ q ∈ Q, a i q) - m * (π * (α i ^ 2 - β i ^ 2) / 2))) +
      ∑ j ∈ IF, ∑ i ∈ IF, 2 * π * (b j i - a j i)) +
      ∑ i ∈ IF, (tauM m (β i) - tauM m (α i)) =
      π * ∑ i ∈ IF, ∑ q ∈ Q.erase i, (a i q + b i q) := by
  rw [sum_split_aux, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have h1 : ∑ q ∈ IF, 2 * π * (b i q - a i q) = 2 * π * ∑ q ∈ Q, (b i q - a i q) := by
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_subset hIQ fun q hq hqI => by rw [hab i hi q hq hqI, sub_self]
  have h2 : ∑ q ∈ Q, (a i q + b i q) = (a i i + b i i) + ∑ q ∈ Q.erase i, (a i q + b i q) :=
    (Finset.add_sum_erase Q _ (hIQ hi)).symm
  rw [Finset.sum_add_distrib, haii i hi, hbii i hi] at h2
  rw [h1, Finset.sum_sub_distrib]
  unfold tauM
  have h3 : ∑ q ∈ Q.erase i, (a i q + b i q) =
      (∑ q ∈ Q, a i q) + (∑ q ∈ Q, b i q) - (Real.log (α i) - Real.log (β i)) := by
    linarith
  rw [h3]
  ring

/-! ### I2 -/

theorem circleAverage_nonpos_of_nonpos {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (hf : ∀ x, f x ≤ 0) :
    Real.circleAverage f c r ≤ 0 := by
  by_cases hi : CircleIntegrable f c r
  · exact Real.circleAverage_mono_on_of_le_circle hi fun x _ => hf x
  · rw [Real.circleAverage.integral_undef hi]

theorem finsum_mem_nonpos' {s : Set ℂ} {f : ℂ → ℝ} (h : ∀ i ∈ s, f i ≤ 0) :
    ∑ᶠ i ∈ s, f i ≤ 0 := by
  have : 0 ≤ ∑ᶠ i ∈ s, -f i :=
    finsum_nonneg fun i => finsum_nonneg fun hi => neg_nonneg.2 (h i hi)
  simp only [finsum_neg_distrib] at this
  linarith

end Screening

open Screening in
/-- **The interaction is nonpositive** (comparison note Prop. `prop:mono`): `G_D(β) ≤ G_D(α)`. -/
theorem truncInteraction_nonpos (C : Set ℂ) (α β : ℂ → ℝ) (hα : ∀ p ∈ C, 0 < α p)
    (hαβ : ∀ p ∈ C, α p ≤ β p) : truncInteraction C α β ≤ 0 := by
  unfold truncInteraction
  refine mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le (finsum_mem_nonpos' fun i hi => ?_)
  refine finsum_mem_nonpos' fun q _ => add_nonpos ?_ ?_ <;>
    exact circleAverage_nonpos_of_nonpos fun x =>
      truncLog_sub_truncLog_nonpos (hα i hi.1) (hαβ i hi.1) (x - i)

open Screening in
/-- **The interaction vanishes for disjoint changed balls.** Positivity and monotonicity of the
radii (`hα`, `hαβ`) are needed: without them the interaction need not vanish. -/
theorem truncInteraction_eq_zero (C : Set ℂ) (α β : ℂ → ℝ) (hα : ∀ p ∈ C, 0 < α p)
    (hαβ : ∀ p ∈ C, α p ≤ β p)
    (hdisj : ∀ i ∈ C, ∀ q ∈ C, i ≠ q → α i < β i → β i + β q ≤ ‖i - q‖) :
    truncInteraction C α β = 0 := by
  unfold truncInteraction
  rw [finsum_mem_eq_zero_of_forall_eq_zero (fun i hi => ?_), mul_zero]
  refine finsum_mem_eq_zero_of_forall_eq_zero fun q hq => ?_
  have hiq : i ≠ q := fun h => hq.2 (h ▸ rfl)
  have hd := hdisj i hi.1 q hq.1 hiq hi.2
  have hβi : 0 < β i := (hα i hi.1).trans hi.2
  have hzero : ∀ r : ℝ, 0 < r → r ≤ β q →
      Real.circleAverage (fun x => truncLog (α i) (x - i) - truncLog (β i) (x - i)) q r = 0 := by
    intro r hr hrq
    refine Real.circleAverage_const_on_circle fun x hx => ?_
    rw [mem_sphere, dist_eq_norm, abs_of_pos hr] at hx
    have h1 : β i ≤ ‖x - i‖ := by
      have := norm_sub_norm_le (i - q) (x - q)
      rw [show i - q - (x - q) = -(x - i) by abel, norm_neg, hx] at this
      linarith
    rw [truncLog_eq_zero (hα i hi.1) (hi.2.le.trans h1), truncLog_eq_zero hβi h1, sub_zero]
  rw [hzero _ (hα q hq.1) (hαβ q hq.1), hzero _ ((hα q hq.1).trans_le (hαβ q hq.1)) le_rfl,
    add_zero]

end SandierSerfaty

end
