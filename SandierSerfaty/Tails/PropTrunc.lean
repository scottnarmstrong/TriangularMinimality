/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.PropH
public import SandierSerfaty.Tails.JetBound

/-!
# Jets of the truncated objects `f̃₀`, `ẽ` (finite sums)

`exists_jet_Trunc_f₀`: `f̃₀` (modes `0, …, 38`, `B̃`, `B̃₁`, `H̃_k`) has a second-order jet on `(0, ∞)` (finite
sums and products of the jets of `S̃₁, S̃₂, log, H̃_k, D_i`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

theorem jet_Trunc_S₁ : Jet2 (Ioi 0) (Ioi 0) Trunc.S₁
    (fun r => Trunc.B r * r) (fun x => (∑ i ∈ Finset.range 39, deriv (u i) x) * x + Trunc.B x) :=
  jet_integral nearZero_trunc_B_mul fun x hx =>
    ((jet_trunc_B.d0 x hx).mul (hasDerivAt_id' x)).congr_deriv (by ring)

/-- The integrand of `S̃₂` and its derivative. -/
@[expose] noncomputable def trφ (r : ℝ) : ℝ := -2 * Trunc.B₁ r + r * Trunc.B₁ r ^ 2

@[expose] noncomputable def trφ₁ (r : ℝ) : ℝ :=
  -2 * Bt1d r + (Trunc.B₁ r ^ 2 + r * (2 * Trunc.B₁ r * Bt1d r))

theorem hasDerivAt_trφ {x : ℝ} (hx : 0 < x) : HasDerivAt trφ (trφ₁ x) x := by
  have hB := jet_Bt1.d0 x hx
  have h1 := (hB.const_mul (-2 : ℝ))
  have h2 := (hasDerivAt_id' x).mul (hB.pow 2)
  refine (h1.add h2).congr_deriv ?_
  unfold trφ₁
  simp

theorem nearZero_trφ (hc : FiniteCore) : NearZero trφ :=
  (((nearZero_Trunc_B₁ hc).const_mul (-2)).add
    (NearZero.id_mul ((nearZero_Trunc_B₁ hc).mul (nearZero_Trunc_B₁ hc)))).congr_pos fun r _ => by
    unfold trφ; ring

theorem jet_Trunc_S₂ (hc : FiniteCore) : Jet2 (Ioi 0) (Ioi 0) Trunc.S₂ trφ trφ₁ :=
  jet_integral (nearZero_trφ hc) fun _ hx => hasDerivAt_trφ hx

theorem jet_log : Jet2 (Ioi 0) (Ioi 0) Real.log (fun x => x⁻¹) (fun x => -(x ^ 2)⁻¹) := by
  refine ⟨fun x hx => Real.hasDerivAt_log (ne_of_gt hx), fun x hx => ?_, subset_rfl⟩
  exact hasDerivAt_inv (ne_of_gt hx)

/-- **`f̃₀` has a jet on `(0, ∞)`** (finite sums of jets). -/
theorem exists_jet_Trunc_f₀ (hc : FiniteCore) : ∃ F₁ F₂ : ℝ → ℝ, Jet2 (Ioi 0) (Ioi 0) Trunc.f₀ F₁ F₂ := by
  have jt : Jet2 (Ioi 0) (Ioi 0) (fun x : ℝ => x) _ _ := Jet2.id subset_rfl
  have jt2 := jt.mul jt
  have jDi : ∀ i, Jet2 (Ioi 0) (Ioi 0) (D i) (deriv (D i)) (deriv (deriv (D i))) := jet_D
  -- the sums over `i ≤ 38`
  have sA := Jet2.finset_sum (U := Ioi (0 : ℝ)) (V := Ioi 0) (Finset.range 39) subset_rfl
    (fun i _ => (jDi i).const_mul (1 / ((k i : ℝ) + 2)))
  have sB := Jet2.finset_sum (U := Ioi (0 : ℝ)) (V := Ioi 0) (Finset.range 39) subset_rfl
    (fun i _ => ((jDi i).const_mul (-2)).add (((jDi i).const_mul (2 * (k i : ℝ))).mul (jet_Hk_trunc hc (k i))))
  have sE := Jet2.finset_sum (U := Ioi (0 : ℝ)) (V := Ioi 0) (Finset.range 39) subset_rfl
    (fun i _ => Jet2.finset_sum (U := Ioi (0 : ℝ)) (V := Ioi 0) (Finset.range 39) subset_rfl
      (fun j _ => ((jDi i).const_mul ((k i : ℝ) * (k j : ℝ) / ((k i : ℝ) + (k j : ℝ)))).mul (jDi j)))
  have big := (((jet_Trunc_S₁.add (jt2.mul sA)).const_mul (-2 * Real.pi)).sub'
    ((((jet_log.add (jet_Trunc_S₂ hc)).add sB).add sE).const_mul (1 / 2)))
  refine ⟨_, _, big.congr isOpen_Ioi (fun x _ => ?_) (fun _ _ => rfl) (fun _ _ => rfl)⟩
  unfold Trunc.f₀
  simp only [Trunc.modes_succ]
  have e1 : ∑ i ∈ Finset.range 39, 1 / ((k i : ℝ) + 2) * D i x = ∑ i ∈ Finset.range 39, D i x / ((k i : ℝ) + 2) :=
    Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∀ i, Hk Trunc.B₁ (k i) x = Trunc.H (k i) x := fun i => rfl
  simp only [e1, e2]
  ring

end Tails

end SandierSerfaty

end
