/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Minimizer

/-!
# Separation of minimizers (sphere note, Theorem 4.2): minimality in a chart

* `Sphere.sum_update_sub`: moving one point `i` of a configuration changes a symmetric ordered-pair
  sum by `2 (∑_{b ≠ i} f(y', y_b) - ∑_{b ≠ i} f(y_i, y_b))`;
* `Sphere.exists_stereo_eq`: every point of `S²` other than the north pole is `T x`;
* `Sphere.chart_minimality`: if `W = T ∘ X` is a minimizer then
  `φ(x_i) ≤ φ(x)` for every `x` not among the other `x_j`, where
  `φ(x) = ∑_{j ≠ i} g(x - x_j) + ((n-1)/2) V(x)` (`g = -log |·|`, `V = log (1 + |·|²)`).
-/

open Filter Topology Set Finset

public section

namespace SandierSerfaty

namespace Sphere

theorem sum_update_sub {n : ℕ} {M : Type*} [DecidableEq (Fin n)] (f : M → M → ℝ)
    (hf : ∀ a b, f a b = f b a) (Y : Fin n → M) (i : Fin n) (y' : M) :
    (∑ a, ∑ b ∈ Finset.univ.erase a, f (Function.update Y i y' a) (Function.update Y i y' b)) -
      (∑ a, ∑ b ∈ Finset.univ.erase a, f (Y a) (Y b)) =
    2 * ((∑ b ∈ Finset.univ.erase i, f y' (Y b)) - ∑ b ∈ Finset.univ.erase i, f (Y i) (Y b)) := by
  set Z := Function.update Y i y' with hZ
  have hZi : Z i = y' := Function.update_self i y' Y
  have hZne : ∀ a, a ≠ i → Z a = Y a := fun a ha => Function.update_of_ne ha y' Y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∑ b ∈ Finset.univ.erase i, f (Z i) (Z b) = ∑ b ∈ Finset.univ.erase i, f y' (Y b) :=
    Finset.sum_congr rfl fun b hb => by rw [hZi, hZne b (Finset.ne_of_mem_erase hb)]
  have h2 : ∀ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase a, f (Z a) (Z b) -
      ∑ b ∈ Finset.univ.erase a, f (Y a) (Y b) = f (Y a) y' - f (Y a) (Y i) := by
    intro a ha
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    have hi : i ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hai.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase _ _ hi, ← Finset.add_sum_erase _ _ hi, hZi, hZne a hai]
    have : ∑ b ∈ (Finset.univ.erase a).erase i, f (Y a) (Z b) =
        ∑ b ∈ (Finset.univ.erase a).erase i, f (Y a) (Y b) :=
      Finset.sum_congr rfl fun b hb => by
        rw [hZne b (Finset.ne_of_mem_erase hb)]
    rw [this]; ring
  have h3 : ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase a, f (Z a) (Z b) -
      ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase a, f (Y a) (Y b) =
      ∑ a ∈ Finset.univ.erase i, (f y' (Y a) - f (Y i) (Y a)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [h2 a ha, hf (Y a) y', hf (Y a) (Y i)]
  rw [h1] at *
  have h4 : ∑ b ∈ Finset.univ.erase i, f (Y i) (Y b) =
      ∑ b ∈ Finset.univ.erase i, f (Y i) (Y b) := rfl
  rw [Finset.sum_sub_distrib] at h3
  linarith

theorem exists_stereo_eq {y : R3} (hy : ‖y‖ = 1) (h2 : y 2 ≠ 1) : ∃ x : ℂ, stereo x = y := by
  have hsq : y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1 := by
    have := hy
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one, Fin.sum_univ_three] at this
    simpa [Real.norm_eq_abs, sq_abs] using this
  have hle : y 2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  have hlt : y 2 < 1 := lt_of_le_of_ne (by nlinarith) h2
  have hd : 0 < 1 - y 2 := by linarith
  set x : ℂ := ⟨y 0 / (1 - y 2), y 1 / (1 - y 2)⟩ with hx
  have hn : ‖x‖ ^ 2 = (1 + y 2) / (1 - y 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [hx]
    field_simp
    nlinarith
  have h1 : 1 + ‖x‖ ^ 2 = 2 / (1 - y 2) := by
    rw [hn]; field_simp; ring
  have hre : x.re = y 0 / (1 - y 2) := rfl
  have him : x.im = y 1 / (1 - y 2) := rfl
  refine ⟨x, ?_⟩
  ext i
  fin_cases i
  · simp only [Fin.zero_eta]
    rw [stereo_apply_zero, h1, hre]
    field_simp
  · simp only [Fin.mk_one]
    rw [stereo_apply_one, h1, him]
    field_simp
  · simp only [Fin.reduceFinMk]
    have h3 : ‖x‖ ^ 2 - 1 = 2 * y 2 / (1 - y 2) := by
      rw [hn]; field_simp; ring
    rw [stereo_apply_two, h3, h1]
    field_simp

/-- **Minimality in a chart.** If `W = T ∘ X` is a minimizer, then moving the `i`-th point to any `x`
not among the other chart points does not decrease
`φ(x) = ∑_{j ≠ i} g(x - x_j) + ((n-1)/2) V(x)`. -/
theorem chart_minimality {n : ℕ} {W : Fin n → R3} (hW : IsSphereMinimizer W) {X : Fin n → ℂ}
    (hX : ∀ k, stereo (X k) = W k) (i : Fin n) {x : ℂ} (hx : ∀ j, j ≠ i → x ≠ X j) :
    ∑ b ∈ Finset.univ.erase i, gKer (X i - X b) + (((n - 1 : ℕ) : ℝ) / 2) * potV (X i) ≤
      ∑ b ∈ Finset.univ.erase i, gKer (x - X b) + (((n - 1 : ℕ) : ℝ) / 2) * potV x := by
  classical
  set Z : Fin n → R3 := Function.update W i (stereo x) with hZ
  have hZn : ∀ a, ‖Z a‖ = 1 := by
    intro a
    by_cases ha : a = i
    · subst ha; rw [hZ, Function.update_self]; exact norm_stereo x
    · rw [hZ, Function.update_of_ne ha]; exact hW.norm_eq a
  have hZi : Function.Injective Z := by
    intro a b hab
    by_cases ha : a = i <;> by_cases hb : b = i
    · rw [ha, hb]
    · exfalso
      rw [hZ, ha, Function.update_self, Function.update_of_ne hb, ← hX b] at hab
      exact hx b hb (stereo_injective hab)
    · exfalso
      rw [hZ, hb, Function.update_self, Function.update_of_ne ha, ← hX a] at hab
      exact hx a ha (stereo_injective hab.symm)
    · rw [hZ, Function.update_of_ne ha, Function.update_of_ne hb] at hab
      exact hW.injective hab
  have hle := hW.le Z hZn hZi
  have hupd := sum_update_sub (fun a b : R3 => -Real.log ‖a - b‖)
    (fun a b => by simp only [norm_sub_rev a b]) W i (stereo x)
  change sphereEnergy Z - sphereEnergy W = _ at hupd
  have h0 : 0 ≤ ∑ b ∈ Finset.univ.erase i, -Real.log ‖stereo x - W b‖ -
      ∑ b ∈ Finset.univ.erase i, -Real.log ‖W i - W b‖ := by linarith
  have hXi : ∀ b ∈ Finset.univ.erase i, X i ≠ X b := fun b hb h =>
    (Finset.ne_of_mem_erase hb) (hW.injective (by rw [← hX, ← hX, h])).symm
  have e1 : ∑ b ∈ Finset.univ.erase i, -Real.log ‖stereo x - W b‖ =
      ∑ b ∈ Finset.univ.erase i, (gKer (x - X b) - Real.log (lam x) / 2 - Real.log (lam (X b)) / 2) :=
    Finset.sum_congr rfl fun b hb => by
      rw [← hX b]; exact neg_log_norm_stereo_sub (hx b (Finset.ne_of_mem_erase hb))
  have e2 : ∑ b ∈ Finset.univ.erase i, -Real.log ‖W i - W b‖ =
      ∑ b ∈ Finset.univ.erase i,
        (gKer (X i - X b) - Real.log (lam (X i)) / 2 - Real.log (lam (X b)) / 2) :=
    Finset.sum_congr rfl fun b hb => by
      rw [← hX b, ← hX i]; exact neg_log_norm_stereo_sub (hXi b hb)
  rw [e1, e2] at h0
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, log_lam] at h0
  nlinarith [h0]

end Sphere

end SandierSerfaty

end
