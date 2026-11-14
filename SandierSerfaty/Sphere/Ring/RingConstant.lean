/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The ring function `e(x)` and the ring constant (sphere note, Definition 2.5)

For `x > 0`,
`e(x) = -½ log x + x/12 - 2 ∑_{m ≥ 1} log |1 - (-1)^m e^{-m x}|` (`Sphere.ringAspectEnergy`) and
`C_ring = e(√3 π) + ½ log 2` (`Sphere.ringConstant`).

* `Sphere.abs_ringLogTerm_le`: `|log |1 - (-1)^m e^{-m x}|| ≤ e^{-m x}/(1 - e^{-x})` (`m ≥ 1`);
* `Sphere.summable_ringLogTerm`, `Sphere.abs_tsum_ringLogTerm_tail_le` (the tail beyond `d` terms is at
  most `e^{-(d+1) x}/(1 - e^{-x})²`);
* `Sphere.abs_ringAspectEnergy_sub_le`: `e` is Lipschitz on `[a, ∞)` for every `a > 0`.
-/

public section

namespace SandierSerfaty

namespace Sphere

/-- The summand `log |1 - (-1)^m e^{-m x}|` of `e(x)`. -/
@[expose] noncomputable def ringLogTerm (x : ℝ) (m : ℕ) : ℝ :=
  Real.log (1 - (-1) ^ m * Real.exp (-(m * x)))

/-- **The ring function** (Definition 2.5):
`e(x) = -½ log x + x/12 - 2 ∑_{m ≥ 1} log |1 - (-1)^m e^{-m x}|`. -/
@[expose] noncomputable def ringAspectEnergy (x : ℝ) : ℝ :=
  -(Real.log x / 2) + x / 12 - 2 * ∑' m : ℕ, ringLogTerm x (m + 1)

/-- **The ring constant** (Definition 2.5): `C_ring = e(√3 π) + ½ log 2`. -/
@[expose] noncomputable def ringConstant : ℝ :=
  ringAspectEnergy (Real.sqrt 3 * Real.pi) + Real.log 2 / 2

theorem abs_log_one_sub_le {w u : ℝ} (hw : |w| ≤ u) (hu : u < 1) :
    |Real.log (1 - w)| ≤ u / (1 - u) := by
  obtain ⟨hw1, hw2⟩ := abs_le.1 hw
  have h1u : 0 < 1 - u := by linarith
  have h1w : 0 < 1 - w := by linarith
  have hu0 : 0 ≤ u := (abs_nonneg w).trans hw
  rw [abs_le]
  constructor
  · -- `log (1 - w) ≥ 1 - 1/(1 - w) = -w/(1 - w) ≥ -u/(1 - u)`
    have h := Real.one_sub_inv_le_log_of_pos h1w
    have e : 1 - (1 - w)⁻¹ = -(w / (1 - w)) := by field_simp; ring
    rw [e] at h
    have : w / (1 - w) ≤ u / (1 - u) := by
      rw [div_le_div_iff₀ h1w h1u]; nlinarith
    linarith
  · have h := Real.log_le_sub_one_of_pos h1w
    have : u ≤ u / (1 - u) := by
      rw [le_div_iff₀ h1u]; nlinarith
    linarith

theorem abs_log_one_sub_sub_le {w w' u : ℝ} (hw : |w| ≤ u) (hw' : |w'| ≤ u) (hu : u < 1) :
    |Real.log (1 - w) - Real.log (1 - w')| ≤ |w - w'| / (1 - u) := by
  obtain ⟨hw1, hw2⟩ := abs_le.1 hw
  obtain ⟨hw1', hw2'⟩ := abs_le.1 hw'
  have h1u : 0 < 1 - u := by linarith
  have h1w : 0 < 1 - w := by linarith
  have h1w' : 0 < 1 - w' := by linarith
  -- `log a - log b ≤ (a - b)/b`
  have key : ∀ a b : ℝ, 0 < a → 1 - u ≤ b → Real.log a - Real.log b ≤ |a - b| / (1 - u) := by
    intro a b ha hb
    have hb0 : 0 < b := lt_of_lt_of_le h1u hb
    have h := Real.log_le_sub_one_of_pos (div_pos ha hb0)
    rw [Real.log_div ha.ne' hb0.ne'] at h
    have : a / b - 1 ≤ |a - b| / (1 - u) := by
      rw [div_sub_one hb0.ne']
      calc (a - b) / b ≤ |a - b| / b := by gcongr; exact le_abs_self _
        _ ≤ |a - b| / (1 - u) := div_le_div_of_nonneg_left (abs_nonneg _) h1u hb
    linarith
  rw [abs_le]
  constructor
  · have := key (1 - w') (1 - w) h1w' (by linarith)
    rw [show (1 - w') - (1 - w) = w - w' by ring] at this
    linarith
  · have := key (1 - w) (1 - w') h1w (by linarith)
    rwa [show (1 - w) - (1 - w') = -(w - w') by ring, abs_neg] at this

theorem abs_neg_one_pow_mul (m : ℕ) (a : ℝ) : |(-1) ^ m * a| = |a| := by
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

theorem exp_neg_mul_le {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (-(m * x)) ≤ Real.exp (-x) :=
  Real.exp_le_exp.2 (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith)

/-- `|log |1 - (-1)^m e^{-m x}|| ≤ e^{-m x}/(1 - e^{-x})` for `x > 0`, `m ≥ 1`. -/
theorem abs_ringLogTerm_le {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : 1 ≤ m) :
    |ringLogTerm x m| ≤ Real.exp (-(m * x)) / (1 - Real.exp (-x)) := by
  have he1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hle := exp_neg_mul_le hx.le hm
  have h := abs_log_one_sub_le (w := (-1) ^ m * Real.exp (-(m * x))) (u := Real.exp (-(m * x)))
    (by rw [abs_neg_one_pow_mul, abs_of_pos (Real.exp_pos _)]) (hle.trans_lt he1)
  refine h.trans ?_
  apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by linarith)
  linarith

theorem exp_neg_succ_mul (x : ℝ) (m : ℕ) :
    Real.exp (-(((m + 1 : ℕ) : ℝ) * x)) = Real.exp (-x) * Real.exp (-x) ^ m := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf

theorem summable_exp_neg_succ {x : ℝ} (hx : 0 < x) :
    Summable fun m : ℕ => Real.exp (-(((m + 1 : ℕ) : ℝ) * x)) := by
  have he1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  simp only [exp_neg_succ_mul]
  exact (summable_geometric_of_lt_one (Real.exp_pos _).le he1).mul_left _

theorem summable_ringLogTerm {x : ℝ} (hx : 0 < x) : Summable fun m : ℕ => ringLogTerm x (m + 1) := by
  have he1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  refine Summable.of_norm_bounded ((summable_exp_neg_succ hx).div_const (1 - Real.exp (-x)))
    fun m => ?_
  rw [Real.norm_eq_abs]
  exact abs_ringLogTerm_le hx (by omega)

/-- The tail: `|∑_{m ≥ d+1} log |1 - (-1)^m e^{-m x}|| ≤ e^{-(d+1) x}/(1 - e^{-x})²`. -/
theorem abs_tsum_ringLogTerm_tail_le {x : ℝ} (hx : 0 < x) (d : ℕ) :
    |∑' m : ℕ, ringLogTerm x (m + d + 1)| ≤ Real.exp (-((d + 1 : ℕ) * x)) / (1 - Real.exp (-x)) ^ 2 := by
  have he1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h1 : 0 < 1 - Real.exp (-x) := by linarith
  set r := Real.exp (-x)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  -- the bound `e^{-(m+d+1) x}/(1 - r) = r^{d+1} r^m/(1 - r)`
  have hb : ∀ m : ℕ, |ringLogTerm x (m + d + 1)| ≤ r ^ (d + 1) * r ^ m / (1 - r) := fun m => by
    have h := abs_ringLogTerm_le hx (m := m + d + 1) (by omega)
    have e : Real.exp (-(((m + d + 1 : ℕ) : ℝ) * x)) = r ^ (d + 1) * r ^ m := by
      simp only [r]; rw [← pow_add, ← Real.exp_nat_mul]; push_cast; ring_nf
    rwa [e] at h
  have hsg : Summable fun m : ℕ => r ^ (d + 1) * r ^ m / (1 - r) :=
    ((summable_geometric_of_lt_one hr0 he1).mul_left _).div_const _
  have hs : Summable fun m : ℕ => ‖ringLogTerm x (m + d + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => by rw [Real.norm_eq_abs]; exact hb m) hsg
  have h2 := norm_tsum_le_tsum_norm hs
  rw [Real.norm_eq_abs] at h2
  refine h2.trans ?_
  have h3 : ∑' m : ℕ, ‖ringLogTerm x (m + d + 1)‖ ≤ ∑' m : ℕ, r ^ (d + 1) * r ^ m / (1 - r) :=
    hs.tsum_le_tsum (fun m => by rw [Real.norm_eq_abs]; exact hb m) hsg
  refine h3.trans (le_of_eq ?_)
  rw [tsum_div_const, tsum_mul_left, tsum_geometric_of_lt_one hr0 he1]
  have e : Real.exp (-(((d + 1 : ℕ) : ℝ) * x)) = r ^ (d + 1) := by
    simp only [r]; rw [← Real.exp_nat_mul]; push_cast; ring_nf
  rw [e]
  field_simp

/-- `|e^{-p} - e^{-q}| ≤ e^{-a} |p - q|` for `p, q ≥ a`. -/
theorem abs_exp_neg_sub_le {p q a : ℝ} (hp : a ≤ p) (hq : a ≤ q) :
    |Real.exp (-p) - Real.exp (-q)| ≤ Real.exp (-a) * |p - q| := by
  have key : ∀ p q : ℝ, a ≤ p → p ≤ q → |Real.exp (-p) - Real.exp (-q)| ≤ Real.exp (-a) * |p - q| := by
    intro p q hp hpq
    have h1 : Real.exp (-q) ≤ Real.exp (-p) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    have h2 : Real.exp (-p) - Real.exp (-q) = Real.exp (-p) * (1 - Real.exp (-(q - p))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
    have h3 : 1 - Real.exp (-(q - p)) ≤ q - p := by linarith [Real.add_one_le_exp (-(q - p))]
    have h4 : Real.exp (-p) ≤ Real.exp (-a) := Real.exp_le_exp.2 (by linarith)
    have h5 : 0 ≤ 1 - Real.exp (-(q - p)) := by
      have : Real.exp (-(q - p)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      linarith
    rw [h2]
    calc Real.exp (-p) * (1 - Real.exp (-(q - p))) ≤ Real.exp (-a) * (1 - Real.exp (-(q - p))) :=
          mul_le_mul_of_nonneg_right h4 h5
      _ ≤ Real.exp (-a) * (q - p) := mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
  rcases le_total p q with h | h
  · exact key p q hp h
  · rw [abs_sub_comm, abs_sub_comm p]; exact key q p hq h

/-- The Lipschitz constant of `e` on `[a, ∞)`. -/
@[expose] noncomputable def ringLip (a : ℝ) : ℝ :=
  1 / (2 * a) + 1 / 12 +
    2 * (∑' m : ℕ, ((m : ℝ) + 1) * Real.exp (-(((m + 1 : ℕ) : ℝ) * a))) / (1 - Real.exp (-a))

theorem summable_succ_mul_exp {a : ℝ} (ha : 0 < a) :
    Summable fun m : ℕ => ((m : ℝ) + 1) * Real.exp (-(((m + 1 : ℕ) : ℝ) * a)) := by
  have he1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := Real.exp (-a))
    (by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact he1)
  have h' := (summable_nat_add_iff 1).2 h
  refine h'.congr fun m => ?_
  simp only [pow_one]
  rw [← Real.exp_nat_mul]; push_cast; ring_nf

/-- **`e` is Lipschitz on `[a, ∞)`**: `|e(x) - e(y)| ≤ ringLip a · |x - y|` for `x, y ≥ a > 0`. -/
theorem abs_ringAspectEnergy_sub_le {a x y : ℝ} (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) :
    |ringAspectEnergy x - ringAspectEnergy y| ≤ ringLip a * |x - y| := by
  have hx0 : 0 < x := ha.trans_le hx
  have hy0 : 0 < y := ha.trans_le hy
  have he1 : Real.exp (-a) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h1a : 0 < 1 - Real.exp (-a) := by linarith
  -- the logarithm
  have hlog : |Real.log x - Real.log y| ≤ |x - y| / a := by
    have key : ∀ p q : ℝ, a ≤ p → a ≤ q → Real.log p - Real.log q ≤ |p - q| / a := by
      intro p q hp hq
      have hp0 : 0 < p := ha.trans_le hp
      have hq0 : 0 < q := ha.trans_le hq
      have h := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
      rw [Real.log_div hp0.ne' hq0.ne', div_sub_one hq0.ne'] at h
      calc Real.log p - Real.log q ≤ (p - q) / q := h
        _ ≤ |p - q| / q := by gcongr; exact le_abs_self _
        _ ≤ |p - q| / a := div_le_div_of_nonneg_left (abs_nonneg _) ha hq
    rw [abs_le]
    constructor
    · have := key y x hy hx; rw [abs_sub_comm] at this; linarith
    · exact key x y hx hy
  -- the series
  set g := fun m : ℕ => ((m : ℝ) + 1) * Real.exp (-(((m + 1 : ℕ) : ℝ) * a))
  have hterm : ∀ m : ℕ, |ringLogTerm x (m + 1) - ringLogTerm y (m + 1)| ≤
      g m * |x - y| / (1 - Real.exp (-a)) := fun m => by
    have hu : ∀ z, a ≤ z → |(-1) ^ (m + 1) * Real.exp (-(((m + 1 : ℕ) : ℝ) * z))| ≤ Real.exp (-a) :=
      fun z hz => by
        rw [abs_neg_one_pow_mul, abs_of_pos (Real.exp_pos _)]
        exact exp_neg_mul_le (ha.le.trans hz) (by omega) |>.trans (Real.exp_le_exp.2 (by linarith))
    have h := abs_log_one_sub_sub_le (hu x hx) (hu y hy) he1
    unfold ringLogTerm
    refine h.trans ?_
    apply div_le_div_of_nonneg_right _ h1a.le
    rw [← mul_sub, abs_neg_one_pow_mul]
    have hm1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
    have h2 := abs_exp_neg_sub_le (p := ((m + 1 : ℕ) : ℝ) * x) (q := ((m + 1 : ℕ) : ℝ) * y)
      (a := ((m + 1 : ℕ) : ℝ) * a) (by nlinarith) (by nlinarith)
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((m + 1 : ℕ) : ℝ))] at h2
    calc |Real.exp (-(((m + 1 : ℕ) : ℝ) * x)) - Real.exp (-(((m + 1 : ℕ) : ℝ) * y))| ≤
        Real.exp (-(((m + 1 : ℕ) : ℝ) * a)) * (((m + 1 : ℕ) : ℝ) * |x - y|) := h2
      _ = g m * |x - y| := by simp only [g]; push_cast; ring
  have hsx := summable_ringLogTerm hx0
  have hsy := summable_ringLogTerm hy0
  have hsg := summable_succ_mul_exp ha
  have hsd : Summable fun m : ℕ => ‖ringLogTerm x (m + 1) - ringLogTerm y (m + 1)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun m => by rw [Real.norm_eq_abs]; exact hterm m)
      ((hsg.mul_right |x - y|).div_const _)
  have hser : |∑' m : ℕ, ringLogTerm x (m + 1) - ∑' m : ℕ, ringLogTerm y (m + 1)| ≤
      (∑' m : ℕ, g m) * |x - y| / (1 - Real.exp (-a)) := by
    rw [← hsx.tsum_sub hsy]
    have h := norm_tsum_le_tsum_norm hsd
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have h3 := hsd.tsum_le_tsum (fun m => by rw [Real.norm_eq_abs]; exact hterm m)
      ((hsg.mul_right |x - y|).div_const _)
    refine h3.trans (le_of_eq ?_)
    rw [tsum_div_const, tsum_mul_right]
  unfold ringAspectEnergy ringLip
  have e : -(Real.log x / 2) + x / 12 - 2 * ∑' m : ℕ, ringLogTerm x (m + 1) -
      (-(Real.log y / 2) + y / 12 - 2 * ∑' m : ℕ, ringLogTerm y (m + 1)) =
      -((Real.log x - Real.log y) / 2) + (x - y) / 12 -
        2 * (∑' m : ℕ, ringLogTerm x (m + 1) - ∑' m : ℕ, ringLogTerm y (m + 1)) := by ring
  rw [e]
  have hxy := abs_nonneg (x - y)
  calc |-((Real.log x - Real.log y) / 2) + (x - y) / 12 -
        2 * (∑' m : ℕ, ringLogTerm x (m + 1) - ∑' m : ℕ, ringLogTerm y (m + 1))|
      ≤ |Real.log x - Real.log y| / 2 + |x - y| / 12 +
        2 * |∑' m : ℕ, ringLogTerm x (m + 1) - ∑' m : ℕ, ringLogTerm y (m + 1)| := by
        have t1 := abs_sub (-((Real.log x - Real.log y) / 2) + (x - y) / 12)
          (2 * (∑' m : ℕ, ringLogTerm x (m + 1) - ∑' m : ℕ, ringLogTerm y (m + 1)))
        have t2 := abs_add_le (-((Real.log x - Real.log y) / 2)) ((x - y) / 12)
        rw [abs_neg, abs_div, abs_two] at t2
        rw [abs_div, show |(12 : ℝ)| = 12 by norm_num] at t2
        rw [abs_mul, abs_two] at t1
        linarith
    _ ≤ |x - y| / a / 2 + |x - y| / 12 + 2 * ((∑' m : ℕ, g m) * |x - y| / (1 - Real.exp (-a))) := by
        linarith
    _ = (1 / (2 * a) + 1 / 12 + 2 * (∑' m : ℕ, g m) / (1 - Real.exp (-a))) * |x - y| := by
        field_simp

end Sphere

end SandierSerfaty

end
