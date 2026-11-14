/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Bridge.LogEnergy
public import SandierSerfaty.Sphere.Ring.RingConstant
public import SandierSerfaty.ClosedForm.Discriminant
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The ring constant equals the triangular constant (sphere note, Lemma 2.6)

`C_ring = e(√3 π) + ½ log 2` (`Sphere.ringConstant`) is an `η`-product constant: with `ρ = e^{iπ/3}`,
`q = e^{2πiρ} = -e^{-√3π}` and Mathlib's `η(ρ) = q^{1/24} ∏_{n ≥ 1} (1 - q^n)` (`ModularForm.eta`),
```
C_ring = -½ log (√3 π) + ½ log 2 - 2 log |η(ρ)|          (`Bridge.ringConstant_eq_log_norm_eta`).
```
With the Chowla–Selberg value `|η(ρ)| = 3^{1/8} Γ(1/3)^{3/2} / (2π)` (`ClosedForm.norm_eta_rho`, CS2) this is
`C_BHS` (`Bridge.ringConstant_eq_bhsConstant`), hence also `C_tri` (`Bridge.ringConstant_eq_cTri`): the lower
constant `C_tri` and the ring upper constant `C_ring` agree, as the sphere note's Lemma 2.6 needs.
-/

open Complex Filter Topology

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

open ClosedForm

/-- `ρ = 1/2 + i √3/2`. -/
theorem rho_eq : rho = (⟨1 / 2, √3 / 2⟩ : ℂ) := Complex.ext rho_re rho_im

/-- `q = e^{2πiρ} = -e^{-√3π}`. -/
theorem cexp_two_pi_I_rho :
    Complex.exp (2 * ↑Real.pi * I * rho) = ((-Real.exp (-(√3 * Real.pi)) : ℝ) : ℂ) := by
  have e : 2 * ↑Real.pi * I * rho = ↑Real.pi * I + ((-(√3 * Real.pi) : ℝ) : ℂ) := by
    rw [rho_eq]
    apply Complex.ext <;> simp <;> ring
  rw [e, Complex.exp_add, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
  push_cast
  ring

theorem norm_qParam_rho : ‖Function.Periodic.qParam 24 rho‖ = Real.exp (-(√3 * Real.pi) / 24) := by
  rw [Function.Periodic.qParam, Complex.norm_exp]
  congr 1
  rw [rho_eq]
  simp
  ring

theorem norm_one_sub_q_pow (n : ℕ) :
    ‖1 - ModularForm.eta_q n rho‖ = 1 - (-1) ^ (n + 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * (√3 * Real.pi))) := by
  have hx : 0 < √3 * Real.pi := by positivity
  rw [ModularForm.eta_q_eq_pow, cexp_two_pi_I_rho, ← Complex.ofReal_pow, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hpow : (-Real.exp (-(√3 * Real.pi))) ^ (n + 1) =
      (-1) ^ (n + 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * (√3 * Real.pi))) := by
    rw [neg_pow, ← Real.exp_nat_mul]
    ring_nf
  rw [hpow]
  refine abs_of_nonneg ?_
  have hle : (-1 : ℝ) ^ (n + 1) * Real.exp (-(((n + 1 : ℕ) : ℝ) * (√3 * Real.pi))) ≤
      Real.exp (-(((n + 1 : ℕ) : ℝ) * (√3 * Real.pi))) := by
    rcases neg_one_pow_eq_or ℝ (n + 1) with h | h <;> rw [h] <;> nlinarith [Real.exp_pos
      (-(((n + 1 : ℕ) : ℝ) * (√3 * Real.pi)))]
  have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlt : Real.exp (-(((n + 1 : ℕ) : ℝ) * (√3 * Real.pi))) < 1 :=
    Real.exp_lt_one_iff.2 (by nlinarith)
  linarith

theorem ringLogTerm_eq (n : ℕ) :
    ringLogTerm (√3 * Real.pi) (n + 1) = Real.log ‖1 - ModularForm.eta_q n rho‖ := by
  rw [norm_one_sub_q_pow, ringLogTerm]

/-- `log |∏_{n ≥ 1} (1 - q^n)| = ∑_{n ≥ 1} log |1 - (-1)^n e^{-n√3π}|`. -/
theorem log_norm_tprod :
    Real.log ‖∏' n, (1 - ModularForm.eta_q n rho)‖ = ∑' n : ℕ, ringLogTerm (√3 * Real.pi) (n + 1) := by
  have hx : 0 < √3 * Real.pi := by positivity
  have hq : ‖Complex.exp (2 * ↑Real.pi * I * rho)‖ < 1 := by
    rw [cexp_two_pi_I_rho, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have hmult : Multipliable fun n => 1 - ModularForm.eta_q n rho := by
    simp_rw [ModularForm.eta_q_eq_pow]
    exact ModularForm.multipliable_one_sub_pow hq
  have hpos : ∀ n : ℕ, 0 < ‖1 - ModularForm.eta_q n rho‖ := fun n =>
    norm_pos_iff.2 (ModularForm.one_sub_eta_q_ne_zero n rho_im_pos)
  have hnorm : ‖∏' n, (1 - ModularForm.eta_q n rho)‖ = ∏' n, ‖1 - ModularForm.eta_q n rho‖ :=
    hmult.map_tprod (normHom : ℂ →*₀ ℝ) continuous_norm
  have hsum : Summable fun n : ℕ => Real.log ‖1 - ModularForm.eta_q n rho‖ := by
    simp_rw [← ringLogTerm_eq]; exact summable_ringLogTerm hx
  rw [hnorm, ← Real.rexp_tsum_eq_tprod hpos hsum, Real.log_exp]
  exact tsum_congr fun n => (ringLogTerm_eq n).symm

/-- `C_ring = -½ log (√3 π) + ½ log 2 - 2 log |η(ρ)|`. -/
theorem ringConstant_eq_log_norm_eta :
    ringConstant = -(Real.log (√3 * Real.pi) / 2) + Real.log 2 / 2 -
      2 * Real.log ‖ModularForm.eta rho‖ := by
  have hη : ‖ModularForm.eta rho‖ = Real.exp (-(√3 * Real.pi) / 24) *
      ‖∏' n, (1 - ModularForm.eta_q n rho)‖ := by
    rw [ModularForm.eta, norm_mul, norm_qParam_rho]
  have hprod : ‖∏' n, (1 - ModularForm.eta_q n rho)‖ ≠ 0 :=
    norm_ne_zero_iff.2 (ModularForm.eta_tprod_ne_zero rho_im_pos)
  rw [hη, Real.log_mul (Real.exp_pos _).ne' hprod, Real.log_exp, log_norm_tprod, ringConstant,
    ringAspectEnergy]
  ring

/-- **`C_ring = C_BHS`**, from the Chowla–Selberg value of `|η(ρ)|` (CS2). -/
theorem ringConstant_eq_bhsConstant : ringConstant = bhsConstant := by
  have hπ := Real.pi_pos
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  have hsπ : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 hπ
  have hη : Real.log ‖ModularForm.eta rho‖ =
      Real.log 3 / 8 + 3 / 2 * Real.log (Real.Gamma (1 / 3)) - Real.log 2 - Real.log Real.pi := by
    rw [norm_eta_rho, Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hπ.ne',
      Real.log_rpow (by norm_num), Real.log_rpow hG]
    ring
  rw [ringConstant_eq_log_norm_eta, hη, Real.log_mul h3.ne' hπ.ne', Real.log_sqrt (by norm_num)]
  unfold bhsConstant
  rw [Real.log_div hsπ.ne' hG.ne', Real.log_div (by norm_num) (by norm_num), Real.log_sqrt hπ.le]
  ring

/-- **`C_ring = C_tri`** (sphere note, Lemma 2.6): the ring upper constant equals the triangular lower
constant. -/
theorem ringConstant_eq_cTri : ringConstant = Lower.cTri := by
  rw [ringConstant_eq_bhsConstant, bhsConstant_eq_cTri]

end Bridge

end Sphere

end SandierSerfaty

end
