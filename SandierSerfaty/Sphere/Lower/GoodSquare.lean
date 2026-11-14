/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.GoodSquareAux
public import SandierSerfaty.Sphere.Lower.Reflection
public import SandierSerfaty.Sphere.Lower.Statements
public import SandierSerfaty.Sphere.Lower.GoodSquareAlg

/-!
# Good squares (sphere note, Proposition 6.13)

`Lower.good_square`: under `TorusBoundStatement` and `Input63Statement`, for a square `Q = a + [0,t]²` with integer mass
`n̄ = m̄ t²` on which the density `m` is `δ`-close to `m̄`, for a correction `v` with `Δ v = 2π (m - m̄)`, and if the
strip energy `S = ∫_{Q^{ℓ̃/2} ∖ Q^{2ℓ̃}} |∇(H_{1/4} - v)|²` is at most `ℓ³ ℓ̃ / C_scr`, then for every `ε ∈ (0,1]`

`p c_* ≤ 𝔉(Q) + π ∑_{z_i ∈ Q} log λ(x_i) + C (ℓ S / ℓ̃ + t ℓ̃ + |n̄ - p| + p δ + t) + (ε/2) ∫_Q |∇H_{1/4}|² + (C/ε) ∫_Q |∇v|²`,

`p = #(Z ∩ Q)`, `𝔉(Q) = ½ ∫_Q |∇H_{1/4}|² + ∑_{z_i ∈ Q} [π log ¼ - 2π ∫ f_{1/4}(· - z_i) m]`.  (The additive `t` absorbs the
`O(R)` points within `1/4` of `∂Q`; the sphere note's `C R`.)
-/

open MeasureTheory Set Filter Topology Laplacian
open scoped ContDiff Classical

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- `c_* = W_tri + (π/2) log (4 π κ²)`. -/
@[expose] noncomputable def cStar : ℝ :=
  triangularEnergy + Real.pi / 2 * Real.log (4 * Real.pi * blowupKappa ^ 2)

/-- `𝔉(Q)` of the sphere note. -/
@[expose] noncomputable def fnQ {n : ℕ} (X : Fin n → ℂ) (a : ℂ) (t : ℝ) : ℝ :=
  1 / 2 * (∫ x in sqAt a t, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) +
    ∑ q ∈ ptsIn X a t, (Real.pi * Real.log (1 / 4) -
      2 * Real.pi * ∫ x, truncLog (1 / 4) (x - q) * blowupDens n x)

/-- `π ∑_{z_i ∈ Q} log λ(x_i)`. -/
@[expose] noncomputable def chartSum {n : ℕ} (X : Fin n → ℂ) (a : ℂ) (t : ℝ) : ℝ :=
  Real.pi * ∑ i ∈ Finset.univ.filter (fun i => blowupScale n • X i ∈ sqAt a t), Real.log (lam (X i))

/-- The strip energy `∫_{Q^{ℓ̃/2} ∖ Q^{2ℓ̃}} |∇ u|²`. -/
@[expose] noncomputable def stripEnergy (u : ℂ → ℝ) (a : ℂ) (t ℓt : ℝ) : ℝ :=
  ∫ x in sqShrink a t (ℓt / 2) \ sqShrink a t (2 * ℓt), ‖gradC u x‖ ^ 2

theorem separated_ptsIn {n : ℕ} (X : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) (a : ℂ) (t : ℝ) :
    ∀ p ∈ ptsIn X a t, ∀ q ∈ ptsIn X a t, p ≠ q → 1 ≤ ‖p - q‖ := by
  intro p hp q hq hpq
  have hp' := (Finset.mem_filter.1 hp).1
  have hq' := (Finset.mem_filter.1 hq).1
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp'
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq'
  exact hsep i j fun h => hpq (by rw [h])

theorem injective_of_sep {n : ℕ} (X : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) :
    Function.Injective fun i => blowupScale n • X i := by
  intro i j hij
  by_contra hne
  have := hsep i j hne
  simp only at hij
  rw [hij, sub_self, norm_zero] at this
  linarith

theorem sum_density_sub_le {n : ℕ} (X : Fin n → ℂ)
    (hsep : ∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) {a : ℂ} {t : ℝ}
    (ht : 2 ≤ t) {mb δ : ℝ} (hmb : 0 ≤ mb) (hδ0 : 0 ≤ δ)
    (hδ : ∀ x ∈ sqAt a t, |blowupDens n x - mb| ≤ δ) :
    (∑ q ∈ ptsIn X a t, ((∫ x, truncLog (1 / 4) (x - q) * blowupDens n x) -
        mb * ∫ x in sqAt a t, truncLog (1 / 4) (x - q))) ≤
      (ptsIn X a t).card * (Real.pi / 32 * δ) + Real.pi / 32 * mPlus * (7 * t) := by
  set S := ptsIn X a t with hS
  have hSQ : ∀ q ∈ S, q ∈ sqAt a t := fun q hq => (Finset.mem_filter.1 hq).2
  have h1 : ∀ q ∈ S, ((∫ x, truncLog (1 / 4) (x - q) * blowupDens n x) -
        mb * ∫ x in sqAt a t, truncLog (1 / 4) (x - q)) ≤
      Real.pi / 32 * δ + (if q ∈ sqShrink a t (1 / 4) then 0 else Real.pi / 32 * mPlus) :=
    fun q _ => integral_truncLog_density_sub_le hmb hδ0 hδ
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ q ∈ S, (if q ∈ sqShrink a t (1 / 4) then (0 : ℝ) else Real.pi / 32 * mPlus) =
      (S.filter (· ∈ sqAt a t \ sqShrink a t (1 / 4))).card * (Real.pi / 32 * mPlus) := by
    have hset : S.filter (fun q => ¬ q ∈ sqShrink a t (1 / 4)) =
        S.filter (· ∈ sqAt a t \ sqShrink a t (1 / 4)) := by
      refine Finset.filter_congr fun q hq => ?_
      simp only [Set.mem_sdiff]
      exact ⟨fun h => ⟨hSQ q hq, h⟩, fun h => h.2⟩
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, hset]
  rw [h2]
  have h3 := card_filter_not_shrink_le (separated_ptsIn X hsep a t) a ht
  have hm := mPlus_pos
  have hp := Real.pi_pos
  have : ((S.filter (· ∈ sqAt a t \ sqShrink a t (1 / 4))).card : ℝ) * (Real.pi / 32 * mPlus) ≤
      7 * t * (Real.pi / 32 * mPlus) := mul_le_mul_of_nonneg_right h3 (by positivity)
  linarith

theorem chartSum_ge {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ)
    (hinj : Function.Injective fun i => blowupScale n • X i) {a : ℂ} {t : ℝ} {mb δ : ℝ}
    (hmb : mMinus ≤ mb) (hQ : ∀ x ∈ sqAt a t, ‖x‖ ≤ 2 * blowupScale n)
    (hδ : ∀ x ∈ sqAt a t, |blowupDens n x - mb| ≤ δ) :
    ((ptsIn X a t).card : ℝ) * (Real.pi / 2 * (Real.log mb + Real.log (4 * Real.pi * blowupKappa ^ 2)) -
        Real.pi / 2 * (δ / mMinus)) ≤ chartSum X a t := by
  unfold chartSum
  rw [card_ptsIn X hinj, Finset.mul_sum, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun i hi => ?_
  have hz := (Finset.mem_filter.1 hi).2
  exact pi_log_lam_ge hn (X i) hmb (by simpa using hQ _ hz) (hδ _ hz)

theorem fnQ_eq {n : ℕ} (X : Fin n → ℂ) (a : ℂ) (t : ℝ) :
    fnQ X a t = 1 / 2 * (∫ x in sqAt a t, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) +
      (Real.pi * Real.log (1 / 4) * ((ptsIn X a t).card : ℝ) -
        2 * Real.pi * ∑ q ∈ ptsIn X a t, ∫ x, truncLog (1 / 4) (x - q) * blowupDens n x) := by
  unfold fnQ
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem abs_log_le_of_mem {mb : ℝ} (hmbL : mMinus ≤ mb) (hmbH : mb ≤ mPlus) :
    |Real.log mb| ≤ |Real.log mMinus| + |Real.log mPlus| := by
  have hmb0 : 0 < mb := lt_of_lt_of_le mMinus_pos hmbL
  have h1 : Real.log mMinus ≤ Real.log mb := Real.log_le_log mMinus_pos hmbL
  have h2 : Real.log mb ≤ Real.log mPlus := Real.log_le_log hmb0 hmbH
  rw [abs_le]
  have := le_abs_self (Real.log mPlus)
  have := neg_abs_le (Real.log mMinus)
  have := abs_nonneg (Real.log mMinus)
  have := abs_nonneg (Real.log mPlus)
  constructor <;> linarith

theorem abs_sub_mul_ge {W lm : ℝ} {nb p mb : ℝ} (hlm : |Real.log mb| ≤ lm) :
    (nb - p) * (W - Real.pi / 2 * Real.log mb) ≥ -(|nb - p| * (|W| + Real.pi / 2 * lm)) := by
  have h1 : |W - Real.pi / 2 * Real.log mb| ≤ |W| + Real.pi / 2 * lm := by
    calc |W - Real.pi / 2 * Real.log mb| ≤ |W| + |Real.pi / 2 * Real.log mb| := abs_sub _ _
      _ = |W| + Real.pi / 2 * |Real.log mb| := by
        rw [abs_mul, abs_of_pos (by positivity : 0 < Real.pi / 2)]
      _ ≤ |W| + Real.pi / 2 * lm := by gcongr
  have h3 : |(nb - p) * (W - Real.pi / 2 * Real.log mb)| ≤ |nb - p| * (|W| + Real.pi / 2 * lm) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have := neg_abs_le ((nb - p) * (W - Real.pi / 2 * Real.log mb))
  linarith

/-- **Proposition 6.13 (good squares).** -/
theorem good_square (hR1 : Assembly.TorusBoundStatement) (hI : Input63Statement) :
    ∃ Cscr ℓ₀ C : ℝ, 1 ≤ Cscr ∧ 1 ≤ ℓ₀ ∧ 1 ≤ C ∧
      ∀ {n : ℕ} (_ : 0 < n) (X : Fin n → ℂ),
        (∀ i j, i ≠ j → 1 ≤ ‖blowupScale n • X i - blowupScale n • X j‖) →
        ∀ (a : ℂ) (t ℓ ℓt mb δ : ℝ) (nb : ℕ) (v : ℂ → ℝ),
          (∀ x ∈ sqAt a t, ‖x‖ ≤ 2 * blowupScale n) → (nb : ℝ) = mb * t ^ 2 → 1 ≤ nb →
          mMinus ≤ mb → mb ≤ mPlus → 0 ≤ δ → (∀ x ∈ sqAt a t, |blowupDens n x - mb| ≤ δ) →
          max 100 ℓ₀ ≤ ℓ → ℓ ≤ ℓt → ℓt ≤ t / 8 →
          ContDiff ℝ ∞ v → (∀ x, Δ v x = 2 * Real.pi * (blowupDens n x - mb)) →
          stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t ℓt ≤ ℓ ^ 3 * ℓt / Cscr →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            (ptsIn X a t).card * cStar ≤ fnQ X a t + chartSum X a t +
              C * (ℓ * stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t ℓt / ℓt + t * ℓt +
                |(nb : ℝ) - (ptsIn X a t).card| + (ptsIn X a t).card * δ + t) +
              ε / 2 * (∫ x in sqAt a t, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) +
              C / ε * ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 := by
  obtain ⟨CS, Cscr, ℓ₀, hCS, hCscr, hℓ₀, key⟩ :=
    hI mMinus_pos mMinus_le_mPlus mPlus_lt.le
  have hη : (0 : ℝ) < 1 / 4 := by norm_num
  have hC₂0 : 0 ≤ |triangularEnergy| + Real.pi / 2 * (|Real.log mMinus| + |Real.log mPlus|) := by positivity
  have hCdef : 0 ≤ Real.pi / (2 * mMinus) := by have := mMinus_pos; positivity
  refine ⟨Cscr, ℓ₀, 1 + CS + (|triangularEnergy| + Real.pi / 2 * (|Real.log mMinus| + |Real.log mPlus|)) +
      Real.pi ^ 2 / 16 * (1 + 7 * mPlus) + Real.pi / (2 * mMinus), hCscr, hℓ₀, ?_, ?_⟩
  · have : 0 ≤ Real.pi ^ 2 / 16 * (1 + 7 * mPlus) := by have := mPlus_pos; positivity
    linarith
  intro n hn X hsep a t ℓ ℓt mb δ nb v hQ hnb hnb1 hmbL hmbH hδ0 hδ hℓ hℓℓt hℓtt hv hΔv hS ε hε hε1
  have hmb0 : 0 < mb := lt_of_lt_of_le mMinus_pos hmbL
  have hℓ100 : 100 ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓ0ℓ : ℓ₀ ≤ ℓ := (le_max_right _ _).trans hℓ
  have ht2 : 2 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hℓt0 : 0 < ℓt := by linarith
  have hinj := injective_of_sep X hsep
  have hv1 : LocallyLipschitz v := (hv.of_le (by norm_cast)).locallyLipschitz
  have hlip : LocallyLipschitz fun y => truncPot X (1 / 4) y - v y :=
    (locallyLipschitz_truncPot X hη).sub hv1
  have hweak : HasWeakGradientOn (sqAt a t)
      (fun x => wFun X (ptsIn X a t) v x - ∑ q ∈ ptsIn X a t, truncLog (1 / 4) (x - q))
      (gradC fun y => truncPot X (1 / 4) y - v y) := by
    rw [wFun_natural]
    exact hasWeakGradientOn_of_locallyLipschitz hlip (isCompact_sqAt a t)
  have h4 : max (4 * mPlus / mMinus) ℓ₀ ≤ ℓ := by
    rw [four_mul_mPlus_div_mMinus]; exact max_le hℓ100 hℓ0ℓ
  obtain ⟨Y, hYinj, hYint, hYle⟩ := key a t mb ℓ ℓt nb (ptsIn X a t) (wFun X (ptsIn X a t) v)
    (gradC fun y => truncPot X (1 / 4) y - v y) hmbL hmbH hnb h4 hℓℓt hℓtt
    (fun q hq => (Finset.mem_filter.1 hq).2) (separated_ptsIn X hsep a t) hweak
    (fun φ hφ hc hsupp => weak_eq_wFun hn X hinj hv hΔv hφ hc hsupp) hS
  have hR1' := neumannEnergy_ge hR1 hnb1 hmb0 ht0 hnb hYinj hYint
  have hgrad := integral_norm_gradC_sub_le (a := a) (t := t) (locallyLipschitz_truncPot X hη) hv hε
  have hdens := sum_density_sub_le X hsep ht2 hmb0.le hδ0 hδ
  have hchart := chartSum_ge hn X hinj hmbL hQ hδ
  have hdens' : (∑ q ∈ ptsIn X a t, ∫ x, truncLog (1 / 4) (x - q) * blowupDens n x) -
      mb * ∑ q ∈ ptsIn X a t, ∫ x in sqAt a t, truncLog (1 / 4) (x - q) ≤
      ((ptsIn X a t).card : ℝ) * (Real.pi / 32 * δ) + Real.pi / 32 * mPlus * (7 * t) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; exact hdens
  have hV0 : 0 ≤ ∫ x in sqAt a t, ‖gradC v x‖ ^ 2 :=
    setIntegral_nonneg (measurableSet_sqAt a t) fun x _ => by positivity
  have hSl0 : 0 ≤ stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t ℓt :=
    setIntegral_nonneg ((measurableSet_sqShrink _ _ _).diff (measurableSet_sqShrink _ _ _))
      fun x _ => by positivity
  have hE1 : 0 ≤ ℓ * stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t ℓt / ℓt := by
    have : 0 < ℓ := by linarith
    positivity
  exact good_square_algebra triangularEnergy (Real.log (4 * Real.pi * blowupKappa ^ 2)) (Real.log mb)
    mPlus mMinus ((ptsIn X a t).card : ℝ) (nb : ℝ) δ t
    (ℓ * stripEnergy (fun y => truncPot X (1 / 4) y - v y) a t ℓt / ℓt) (t * ℓt)
    |(nb : ℝ) - (ptsIn X a t).card|
    (∫ x in sqAt a t, ‖gradC (truncPot X (1 / 4)) x‖ ^ 2) (∫ x in sqAt a t, ‖gradC v x‖ ^ 2)
    (∫ x in sqAt a t, ‖gradC (fun y => truncPot X (1 / 4) y - v y) x‖ ^ 2)
    (∑ q ∈ ptsIn X a t, ∫ x, truncLog (1 / 4) (x - q) * blowupDens n x)
    (∑ q ∈ ptsIn X a t, ∫ x in sqAt a t, truncLog (1 / 4) (x - q))
    (neumannEnergy a t mb Y) (fnQ X a t) (chartSum X a t) CS _
    (|triangularEnergy| + Real.pi / 2 * (|Real.log mMinus| + |Real.log mPlus|)) ε mb hε hε1 hV0
    (Nat.cast_nonneg _) hδ0 ht0.le hE1 (by positivity) (abs_nonneg _) mPlus_pos mMinus_pos
    (by linarith) hC₂0 rfl hR1' hYle hgrad hdens' (fnQ_eq X a t) hchart
    (abs_sub_mul_ge (abs_log_le_of_mem hmbL hmbH))

end Lower

end Sphere

end SandierSerfaty

end
