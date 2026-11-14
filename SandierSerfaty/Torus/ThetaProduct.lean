/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The entire function `y ↦ ∏ₙ (1 - Qⁿ⁺¹ y)`

For `‖Q‖ < 1`, `SandierSerfaty.Torus.thetaR Q y = ∏' n, (1 - Q ^ (n + 1) * y)` is an entire function of `y`,
vanishing exactly when `Q ^ (n + 1) * y = 1` for some `n`, and satisfying the functional equation
`thetaR Q y = (1 - Q * y) * thetaR Q (Q * y)`. It is the building block of the theta product of
`SandierSerfaty.Torus.ThetaFunction`, the explicit single-charge Green function of a lattice torus.
-/

open Filter Topology Metric

public section

namespace SandierSerfaty

namespace Torus

/-- The entire function `y ↦ ∏ₙ (1 - Q ^ (n + 1) * y)` (for `‖Q‖ < 1`). -/
@[expose] noncomputable def thetaR (Q y : ℂ) : ℂ := ∏' n : ℕ, (1 - Q ^ (n + 1) * y)

theorem summable_norm_thetaR {Q : ℂ} (hQ : ‖Q‖ < 1) (y : ℂ) :
    Summable fun n : ℕ => ‖-(Q ^ (n + 1) * y)‖ := by
  have h := ((summable_geometric_of_lt_one (norm_nonneg Q) hQ).mul_left (‖Q‖ * ‖y‖))
  refine h.congr fun n => ?_
  simp [pow_succ]; ring

theorem multipliable_thetaR {Q : ℂ} (hQ : ‖Q‖ < 1) (y : ℂ) :
    Multipliable fun n : ℕ => 1 - Q ^ (n + 1) * y := by
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable (summable_norm_thetaR hQ y)

/-- `thetaR Q y` vanishes iff one of its factors does. -/
theorem thetaR_ne_zero_iff {Q : ℂ} (hQ : ‖Q‖ < 1) (y : ℂ) :
    thetaR Q y ≠ 0 ↔ ∀ n : ℕ, 1 - Q ^ (n + 1) * y ≠ 0 := by
  constructor
  · intro h n hn
    exact h (tprod_of_exists_eq_zero ⟨n, hn⟩)
  · intro h
    have := tprod_one_add_ne_zero_of_summable (f := fun n : ℕ => -(Q ^ (n + 1) * y))
      (by simpa [sub_eq_add_neg] using h) (summable_norm_thetaR hQ y)
    simpa [thetaR, sub_eq_add_neg] using this

theorem differentiable_thetaR {Q : ℂ} (hQ : ‖Q‖ < 1) : Differentiable ℂ (thetaR Q) := by
  intro y
  set r : ℝ := ‖y‖ + 1 with hr
  have hu : Summable fun n : ℕ => r * ‖Q‖ ^ (n + 1) :=
    ((summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (norm_nonneg Q) hQ)).mul_left r
  have hprod : HasProdLocallyUniformlyOn (fun (n : ℕ) (x : ℂ) => 1 + -(Q ^ (n + 1) * x))
      (fun x => ∏' n : ℕ, (1 + -(Q ^ (n + 1) * x))) (ball (0 : ℂ) r) := by
    refine Summable.hasProdLocallyUniformlyOn_nat_one_add (isOpen_ball) hu (Eventually.of_forall ?_)
      (fun n => by fun_prop)
    intro n x hx
    have hx' : ‖x‖ < r := by simpa using hx
    simp only [norm_neg, norm_mul, norm_pow]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hx'.le (pow_nonneg (norm_nonneg Q) _)
  have hd : DifferentiableOn ℂ (fun x => ∏' n : ℕ, (1 + -(Q ^ (n + 1) * x))) (ball (0 : ℂ) r) :=
    hprod.differentiableOn
      (Eventually.of_forall fun s => by
        simpa [Finset.prod_fn] using
          DifferentiableOn.finsetProd (fun i _ => by fun_prop)) isOpen_ball
  have hmem : ball (0 : ℂ) r ∈ 𝓝 y := isOpen_ball.mem_nhds (by simp [hr])
  have e : thetaR Q = fun x => ∏' n : ℕ, (1 + -(Q ^ (n + 1) * x)) := by
    funext x; simp [thetaR, sub_eq_add_neg]
  rw [e]
  exact hd.differentiableAt hmem

/-- The functional equation `thetaR Q y = (1 - Q y) · thetaR Q (Q y)`. -/
theorem thetaR_eq {Q : ℂ} (hQ : ‖Q‖ < 1) (y : ℂ) :
    thetaR Q y = (1 - Q * y) * thetaR Q (Q * y) := by
  have hm : Multipliable (fun n : ℕ => (fun m : ℕ => 1 - Q ^ (m + 1) * y) (n + 1)) := by
    have := multipliable_thetaR hQ (Q * y)
    refine this.congr fun n => ?_
    simp only [pow_succ Q (n + 1)]
    ring
  have h := tprod_eq_zero_mul' (f := fun m : ℕ => 1 - Q ^ (m + 1) * y) hm
  have e : thetaR Q y = ∏' n : ℕ, (1 - Q ^ (n + 1) * y) := rfl
  rw [e, h]
  have e1 : (1 - Q ^ (0 + 1) * y) = 1 - Q * y := by simp
  rw [e1]
  congr 1
  refine tprod_congr fun n => ?_
  simp only [pow_succ Q (n + 1)]
  ring

end Torus

end SandierSerfaty

end
