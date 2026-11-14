/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Pieces

/-!
# Smoothness of the pieces, and derivatives of the splines on a segment

* `contDiffOn_Piece_*`: every piece is smooth on `(0, ∞)` (indeed `C^ω`: polynomials and `log`);
* `deriv_eq_piece_u`, …: for `x` in the closed segment `seg j`, the first and second derivatives of the
  spline at `x` are those of the piece `j` (the splines being `C²` on `(0, ∞)`, `Radial.lean`).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Calibration

/-! ### Smoothness of the pieces -/

theorem contDiffOn_Piece_tau (j : ℕ) : ContDiffOn ℝ ⊤ (Piece.tau j) (Ioi 0) := by
  have hS := contDiff_Squintic.comp (f := fun r : ℝ => (r - R₀ - 1 / 1000) / hs) (by fun_prop)
  have hc0 : ∀ a : ℝ, ContDiffOn ℝ ⊤ (fun _ : ℝ => a) (Ioi 0) := fun a => contDiffOn_const
  match j with
  | 0 => exact (hc0 0).congr (fun r _ => by simp [Piece.tau])
  | 1 => exact (hc0 0).congr (fun r _ => by simp [Piece.tau])
  | 2 => exact (hc0 0).congr (fun r _ => by simp [Piece.tau])
  | 3 => exact (hc0 0).congr (fun r _ => by simp [Piece.tau])
  | 4 => exact hS.contDiffOn.congr (fun r _ => by simp [Piece.tau])
  | 5 => exact hS.contDiffOn.congr (fun r _ => by simp [Piece.tau])
  | n + 6 => exact (hc0 1).congr (fun r _ => by simp [Piece.tau])

theorem contDiffOn_Piece_b (i j : ℕ) : ContDiffOn ℝ ⊤ (Piece.b i j) (Ioi 0) := by
  have hg := contDiffOn_gamma
  have hcg : ContDiffOn ℝ ⊤ (contPoly gamma) (Ioi 0) := (contDiff_contPoly gamma).contDiffOn
  have hcv : ContDiffOn ℝ ⊤ (contPoly (V i)) (Ioi 0) := (contDiff_contPoly (V i)).contDiffOn
  have hV : ContDiffOn ℝ ⊤ (V i) (Ioi 0) := (contDiff_V i).contDiffOn
  have hP : ContDiffOn ℝ ⊤ (bPoly i) (Ioi 0) := (contDiff_bPoly i).contDiffOn
  have hc0 : ∀ a : ℝ, ContDiffOn ℝ ⊤ (fun _ : ℝ => a) (Ioi 0) := fun a => contDiffOn_const
  by_cases hi : i = 0
  · subst hi
    match j with
    | 0 => exact hg.congr (fun r _ => by simp [Piece.b])
    | 1 => exact hg.congr (fun r _ => by simp [Piece.b])
    | 2 => exact hg.congr (fun r _ => by simp [Piece.b])
    | 3 => exact hcg.congr (fun r _ => by simp [Piece.b])
    | 4 => exact hcg.congr (fun r _ => by simp [Piece.b])
    | 5 => exact (hc0 (gamma R₀)).congr (fun r _ => by simp [Piece.b])
    | n + 6 => exact (hc0 (gamma R₀)).congr (fun r _ => by simp [Piece.b])
  · match j with
    | 0 => exact (hc0 0).congr (fun r _ => by simp [Piece.b, hi])
    | 1 => exact hP.congr (fun r _ => by simp [Piece.b, hi])
    | 2 => exact hV.congr (fun r _ => by simp [Piece.b, hi])
    | 3 => exact hcv.congr (fun r _ => by simp [Piece.b, hi])
    | 4 => exact hcv.congr (fun r _ => by simp [Piece.b, hi])
    | 5 => exact (hc0 (V i R₀)).congr (fun r _ => by simp [Piece.b, hi])
    | n + 6 => exact (hc0 (V i R₀)).congr (fun r _ => by simp [Piece.b, hi])

theorem contDiffOn_Piece_w (i j : ℕ) : ContDiffOn ℝ ⊤ (Piece.w i j) (Ioi 0) := by
  by_cases hi : i = 0
  · subst hi; exact contDiffOn_gamma.congr (fun r _ => by simp [Piece.w])
  · have hS := contDiff_Squintic.comp (f := fun r : ℝ => (r - R₀) / (1 / 10)) (by fun_prop)
    have hpoly : ContDiff ℝ ⊤ fun r : ℝ => (-1 : ℝ) ^ i * coeff i * r ^ k i := by fun_prop
    have h1 : ContDiffOn ℝ ⊤ (fun r : ℝ => (-1 : ℝ) ^ i * coeff i * r ^ k i * 1) (Ioi 0) :=
      (hpoly.mul contDiff_const).contDiffOn
    have h2 : ContDiffOn ℝ ⊤ (fun r : ℝ => (-1 : ℝ) ^ i * coeff i * r ^ k i *
        (1 - Squintic ((r - R₀) / (1 / 10)))) (Ioi 0) :=
      (hpoly.mul (contDiff_const.sub hS)).contDiffOn
    match j with
    | 0 => exact h1.congr (fun r _ => by simp [Piece.w, hi])
    | 1 => exact h1.congr (fun r _ => by simp [Piece.w, hi])
    | 2 => exact h1.congr (fun r _ => by simp [Piece.w, hi])
    | 3 => exact h2.congr (fun r _ => by simp [Piece.w, hi])
    | 4 => exact h2.congr (fun r _ => by simp [Piece.w, hi])
    | 5 => exact h2.congr (fun r _ => by simp [Piece.w, hi])
    | n + 6 => exact h2.congr (fun r _ => by simp [Piece.w, hi])

theorem contDiffOn_Piece_u (i j : ℕ) : ContDiffOn ℝ ⊤ (Piece.u i j) (Ioi 0) :=
  ((contDiffOn_const.sub (contDiffOn_Piece_tau j)).mul (contDiffOn_Piece_w i j)).add
    ((contDiffOn_Piece_tau j).mul (contDiffOn_Piece_b i j))

theorem contDiffOn_Piece_D (i j : ℕ) : ContDiffOn ℝ ⊤ (Piece.D i j) (Ioi 0) :=
  (contDiffOn_Piece_b i j).sub (contDiffOn_Piece_u i j)

/-! ### Derivatives of the splines on a segment -/

theorem uniqueDiffOn_seg {j : ℕ} (hj : j ≤ 6) : UniqueDiffOn ℝ (seg j) := by
  have := R₀_pos; have := hs_pos; have := p_lt_R₀; have := c_pos
  have h1 := R₀_add_hs_lt_l; have h2 := R₀_add_thousandth_lt_R₀_add_hs
  have h3 := p_gt
  interval_cases j
  · exact uniqueDiffOn_Ioc _ _
  · exact uniqueDiffOn_Icc (by linarith)
  · exact uniqueDiffOn_Icc (by linarith)
  · exact uniqueDiffOn_Icc (by linarith)
  · exact uniqueDiffOn_Icc (by linarith)
  · exact uniqueDiffOn_Icc (by linarith)
  · exact uniqueDiffOn_Ici _

theorem deriv_eq_of_eqOn {f g : ℝ → ℝ} {s : Set ℝ} {x : ℝ} (hs : UniqueDiffWithinAt ℝ s x)
    (hx : x ∈ s) (h : EqOn f g s) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv f x = deriv g x := by
  rw [← hf.derivWithin hs, ← hg.derivWithin hs]
  exact derivWithin_congr h (h hx)

/-- If two functions that are `C²` on an open set `U ⊇ s` agree on `s` (a set of unique
differentiability), their first and second derivatives agree on `s`. -/
theorem deriv_deriv_eq_of_eqOn {f g : ℝ → ℝ} {s U : Set ℝ} (hs : UniqueDiffOn ℝ s) (hU : IsOpen U)
    (hsU : s ⊆ U) (h : EqOn f g s) (hf : ContDiffOn ℝ 2 f U) (hg : ContDiffOn ℝ 2 g U) :
    EqOn (deriv f) (deriv g) s ∧ EqOn (deriv (deriv f)) (deriv (deriv g)) s := by
  have hf1 : ContDiffOn ℝ 1 (deriv f) U := hf.deriv_of_isOpen hU (by norm_num)
  have hg1 : ContDiffOn ℝ 1 (deriv g) U := hg.deriv_of_isOpen hU (by norm_num)
  have hd : EqOn (deriv f) (deriv g) s := fun x hx =>
    deriv_eq_of_eqOn (hs x hx) hx h
      ((hf.differentiableOn (by norm_num) x (hsU hx)).differentiableAt (hU.mem_nhds (hsU hx)))
      ((hg.differentiableOn (by norm_num) x (hsU hx)).differentiableAt (hU.mem_nhds (hsU hx)))
  refine ⟨hd, fun x hx => deriv_eq_of_eqOn (hs x hx) hx hd ?_ ?_⟩
  · exact (hf1.differentiableOn (by norm_num) x (hsU hx)).differentiableAt (hU.mem_nhds (hsU hx))
  · exact (hg1.differentiableOn (by norm_num) x (hsU hx)).differentiableAt (hU.mem_nhds (hsU hx))

/-- On the closed segment `seg j`, the first and second derivatives of the spline `u i` are those of the
piece `Piece.u i j`. -/
theorem deriv_u_eq_piece (i : ℕ) {j : ℕ} (hj : j ≤ 6) :
    EqOn (deriv (u i)) (deriv (Piece.u i j)) (seg j) ∧
      EqOn (deriv (deriv (u i))) (deriv (deriv (Piece.u i j))) (seg j) :=
  deriv_deriv_eq_of_eqOn (uniqueDiffOn_seg hj) isOpen_Ioi seg_subset_Ioi (eqOn_u i hj)
    (contDiffOn_u i) ((contDiffOn_Piece_u i j).of_le (by simp))

theorem deriv_D_eq_piece (i : ℕ) {j : ℕ} (hj : j ≤ 6) :
    EqOn (deriv (D i)) (deriv (Piece.D i j)) (seg j) ∧
      EqOn (deriv (deriv (D i))) (deriv (deriv (Piece.D i j))) (seg j) :=
  deriv_deriv_eq_of_eqOn (uniqueDiffOn_seg hj) isOpen_Ioi seg_subset_Ioi (eqOn_D i hj)
    (contDiffOn_D i) ((contDiffOn_Piece_D i j).of_le (by simp))

end Calibration

end SandierSerfaty
