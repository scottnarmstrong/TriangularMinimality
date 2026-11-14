/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.ModeDerivative
public import SandierSerfaty.Tails.WeightedSum
public import SandierSerfaty.Tails.Jet2
public import SandierSerfaty.Calibration.Trunc

/-!
# Jets of the omitted modes and of the truncated sums (paper `tail:radial-derivatives`, `tail:w-definition`, `tail:mode-derivative-bound`, §6.4)

* `u_bound_tail`, `D_bound_tail`: `|u_{j+39}^{(q)}(r)|, |D_{j+39}^{(q)}(r)| ≤ w_{k_j}` for `q ≤ 2` and **every**
  `r > 0` (`tail:mode-derivative-bound` on `(0, l]`; beyond `l` the data are constant, `D = 0`);
* `jet2_of_contDiffOn`: a `C²` function on an open set has the jet `(F, F', F'')`;
* `dU0, dU1, dU2` = `∑_{j} u_{j+39}`, `∑_j u_{j+39}'`, `∑_j u_{j+39}''` (`ΔB`, `ΔB'`, `ΔB''`): their jet
  (`jet_dU`, termwise differentiation) and the bound `|ΔB^{(q)}| ≤ ∑_j w_{k_j}` (paper §6.4);
* the splitting `B = B̃ + ΔB`, `B₁ = B̃₁ + ΔB'` on `(0, ∞)` (`B_eq_trunc_add`, `B₁_eq_trunc_add`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

open Calibration

theorem jet2_of_contDiffOn {U : Set ℝ} (hU : IsOpen U) {F : ℝ → ℝ} (h : ContDiffOn ℝ 2 F U) :
    Jet2 U U F (deriv F) (deriv (deriv F)) := by
  have h1 : ContDiffOn ℝ 1 (deriv F) U := h.deriv_of_isOpen hU (by norm_num)
  refine ⟨fun x hx => ?_, fun x hx => ?_, subset_rfl⟩
  · exact ((h.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
  · exact ((h1.differentiableOn (by norm_num) x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt

theorem jet_u (i : ℕ) : Jet2 (Ioi 0) (Ioi 0) (u i) (deriv (u i)) (deriv (deriv (u i))) :=
  jet2_of_contDiffOn isOpen_Ioi (contDiffOn_u i)

theorem jet_D (i : ℕ) : Jet2 (Ioi 0) (Ioi 0) (D i) (deriv (D i)) (deriv (deriv (D i))) :=
  jet2_of_contDiffOn isOpen_Ioi (contDiffOn_D i)

/-! ### The bounds on all of `(0, ∞)` -/

theorem eventuallyEq_u_of_gt (i : ℕ) {r : ℝ} (hr : l < r) : u i =ᶠ[nhds r] fun _ => u i l :=
  Filter.eventually_of_mem (Ioi_mem_nhds hr) fun _x hx => u_eq_of_ge (le_of_lt hx)

theorem eventuallyEq_D_of_gt (i : ℕ) {r : ℝ} (hr : l < r) : D i =ᶠ[nhds r] fun _ => 0 :=
  Filter.eventually_of_mem (Ioi_mem_nhds hr) fun _x hx => D_of_ge (le_of_lt hx)

theorem deriv_deriv_zero_of {F : ℝ → ℝ} {c r : ℝ} (h : F =ᶠ[nhds r] fun _ => c) :
    deriv F r = 0 ∧ deriv (deriv F) r = 0 := by
  have h1 : deriv F =ᶠ[nhds r] deriv (fun _ : ℝ => c) := h.deriv
  refine ⟨by simpa using h1.eq_of_nhds, ?_⟩
  have h2 : deriv F =ᶠ[nhds r] fun _ => (0 : ℝ) := by simpa using h1
  simpa using h2.deriv_eq

theorem k_tail (j : ℕ) : k (j + 39) = kk j := by
  rw [k_of_pos (by omega)]; rfl

/-- `|u_{j+39}|, |u_{j+39}'|, |u_{j+39}''| ≤ w_{k_j}` at every `r > 0`. -/
theorem u_bound_tail (j : ℕ) {r : ℝ} (hr : 0 < r) :
    |u (j + 39) r| ≤ wk (kk j) ∧ |deriv (u (j + 39)) r| ≤ wk (kk j) ∧
      |deriv (deriv (u (j + 39))) r| ≤ wk (kk j) := by
  have hk : k (j + 39) = kk j := k_tail j
  have hm : 39 ≤ j + 39 := by omega
  rcases le_or_gt r l with h | h
  · have := (mode_derivative_bound_le_two hm ⟨hr, h⟩).1
    rwa [hk] at this
  · have hl : (0 : ℝ) < l := by have := l_gt; linarith
    have := (mode_derivative_bound_le_two hm ⟨hl, le_rfl⟩).1
    rw [hk] at this
    obtain ⟨d1, d2⟩ := deriv_deriv_zero_of (eventuallyEq_u_of_gt (j + 39) h)
    have hw := wk_nonneg (kk j)
    rw [u_eq_of_ge h.le, d1, d2]
    exact ⟨this.1, by simpa using hw, by simpa using hw⟩

theorem D_bound_tail (j : ℕ) {r : ℝ} (hr : 0 < r) :
    |D (j + 39) r| ≤ wk (kk j) ∧ |deriv (D (j + 39)) r| ≤ wk (kk j) ∧
      |deriv (deriv (D (j + 39))) r| ≤ wk (kk j) := by
  have hk : k (j + 39) = kk j := k_tail j
  have hm : 39 ≤ j + 39 := by omega
  rcases le_or_gt r l with h | h
  · have := (mode_derivative_bound_le_two hm ⟨hr, h⟩).2
    rwa [hk] at this
  · obtain ⟨d1, d2⟩ := deriv_deriv_zero_of (eventuallyEq_D_of_gt (j + 39) h)
    have hw := wk_nonneg (kk j)
    rw [D_of_ge h.le, d1, d2]
    exact ⟨by simpa using hw, by simpa using hw, by simpa using hw⟩

/-! ### `ΔB = ∑_{m ≥ 39} u_m` and its derivatives -/

/-- `ΔB = ∑_{m ≥ 39} u_m`. -/
@[expose] noncomputable def dU0 (r : ℝ) : ℝ := ∑' j, u (j + 39) r

/-- `ΔB' = ∑_{m ≥ 39} u_m'`. -/
@[expose] noncomputable def dU1 (r : ℝ) : ℝ := ∑' j, deriv (u (j + 39)) r

/-- `ΔB'' = ∑_{m ≥ 39} u_m''`. -/
@[expose] noncomputable def dU2 (r : ℝ) : ℝ := ∑' j, deriv (deriv (u (j + 39))) r

theorem jet_dU : Jet2 (Ioi 0) (Ioi 0) dU0 dU1 dU2 :=
  Jet2.tsum isOpen_Ioi isPreconnected_Ioi isOpen_Ioi isPreconnected_Ioi subset_rfl
    (fun j => jet_u (j + 39)) summable_wk summable_wk summable_wk
    (fun j _ hx => (u_bound_tail j hx).1) (fun j _ hx => (u_bound_tail j hx).2.1)
    (fun j _ hx => (u_bound_tail j hx).2.2)

theorem abs_tsum_le_ww {F : ℕ → ℝ} (hF : ∀ j, |F j| ≤ wk (kk j)) : |∑' j, F j| ≤ ww := by
  have hs : Summable F := Summable.of_norm_bounded summable_wk fun j => by simpa using hF j
  calc |∑' j, F j| = ‖∑' j, F j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' j, ‖F j‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ww := Summable.tsum_le_tsum (fun j => by simpa using hF j) hs.norm summable_wk

/-- `|ΔB^{(q)}(r)| ≤ ∑_j w_{k_j}` for `q = 0, 1, 2` and every `r > 0` (paper §6.5: `W_*/4`). -/
theorem dU_bound {r : ℝ} (hr : 0 < r) : |dU0 r| ≤ ww ∧ |dU1 r| ≤ ww ∧ |dU2 r| ≤ ww :=
  ⟨abs_tsum_le_ww fun j => (u_bound_tail j hr).1, abs_tsum_le_ww fun j => (u_bound_tail j hr).2.1,
    abs_tsum_le_ww fun j => (u_bound_tail j hr).2.2⟩

theorem ww_le_Wstar : ww ≤ Wstar := by unfold Wstar; linarith [ww_nonneg]

/-! ### The splitting `B = B̃ + ΔB` -/

theorem Trunc.modes_succ : Trunc.modes + 1 = 39 := rfl

theorem summable_u {r : ℝ} (hr : 0 < r) : Summable fun i => u i r := by
  rw [← summable_nat_add_iff 39]
  exact Summable.of_norm_bounded summable_wk fun j => by simpa using (u_bound_tail j hr).1

theorem B_eq_trunc_add {r : ℝ} (hr : 0 < r) : B r = Trunc.B r + dU0 r := by
  unfold B Trunc.B dU0
  rw [Trunc.modes_succ]
  exact ((summable_u hr).sum_add_tsum_nat_add 39).symm

theorem jet_trunc_B : Jet2 (Ioi 0) (Ioi 0) Trunc.B (fun r => ∑ i ∈ Finset.range 39, deriv (u i) r)
    (fun r => ∑ i ∈ Finset.range 39, deriv (deriv (u i)) r) := by
  have := Jet2.finset_sum (U := Ioi (0 : ℝ)) (V := Ioi 0) (Finset.range 39) subset_rfl
    (fun i _ => jet_u i)
  unfold Trunc.B
  rw [Trunc.modes_succ]
  exact this

theorem jet_B : Jet2 (Ioi 0) (Ioi 0) B (fun r => (∑ i ∈ Finset.range 39, deriv (u i) r) + dU1 r)
    (fun r => (∑ i ∈ Finset.range 39, deriv (deriv (u i)) r) + dU2 r) :=
  (jet_trunc_B.add jet_dU).congr isOpen_Ioi (fun _ hx => (B_eq_trunc_add hx).symm)
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem deriv_trunc_B {r : ℝ} (hr : 0 < r) : deriv Trunc.B r = ∑ i ∈ Finset.range 39, deriv (u i) r :=
  (jet_trunc_B.d0 r hr).deriv

theorem deriv_B {r : ℝ} (hr : 0 < r) : deriv B r = deriv Trunc.B r + dU1 r := by
  rw [(jet_B.d0 r hr).deriv, deriv_trunc_B hr]

theorem B₁_eq_trunc_add {r : ℝ} (hr : 0 < r) : B₁ r = Trunc.B₁ r + dU1 r := by
  unfold B₁ Trunc.B₁
  rw [deriv_B hr]; ring

end Tails

end SandierSerfaty

end
