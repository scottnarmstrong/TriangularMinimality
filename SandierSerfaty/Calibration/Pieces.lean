/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Radial

/-!
# The splines as cascades of globally smooth pieces

The knots are
`κ = (b, p - c, p, R₀, R₀ + .001, R₀ + h_s, l)` (`knot 0, …, knot 6`). The segments are

| `j` | `seg j` | meaning |
|-----|---------|---------|
| 0 | `(0, p - c]` | below the first knot (contains `[b, p - c]`, the first certificate segment) |
| 1 | `[p - c, p]` | inner continuation `bPoly` |
| 2 | `[p, R₀]` | edge polynomial `V_m`, `γ` |
| 3 | `[R₀, R₀ + .001]` | `𝓗`-polynomial, `τ = 0`, `U_m` on its ramp |
| 4 | `[R₀ + .001, R₀ + h_s]` | `𝓗`-polynomial, `τ` ramp |
| 5 | `[R₀ + h_s, l]` | constant continuation, `τ` ramp |
| 6 | `[l, ∞)` | `τ = 1`: `u_i = b_i`, `D_i = 0` |

`Piece.tau, Piece.b, Piece.w, Piece.u, Piece.D` are functions `ℕ → ℕ → ℝ → ℝ` (mode `i`, segment `j`),
defined by explicit global formulas and smooth on `(0, ∞)` (`contDiffOn_Piece_*`); `Piece.w` is the baseline
`γ` (`i = 0`) or `U_i` (`i ≥ 1`) used in `u_i = (1 - τ) w_i + τ b_i`. The `EqOn` lemmas
`eqOn_tau`, `eqOn_bRad`, `eqOn_u`, `eqOn_D` say that the splines `tau, bRad i, u i, D i` coincide with the
pieces on the closed segments; `Piece.u i 6 = bRad i` there since `τ = 1`. The spline is the `if`-cascade
of the pieces, hence its classical first and second derivatives on a closed segment
are those of the piece (`deriv_u_eq_piece`, ...).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Calibration

/-- The knots `κ = (b, p - c, p, R₀, R₀ + .001, R₀ + h_s, l)` of the splines (see the module docstring). -/
@[expose] noncomputable def knot : ℕ → ℝ
  | 0 => b
  | 1 => p - c
  | 2 => p
  | 3 => R₀
  | 4 => R₀ + 1 / 1000
  | 5 => R₀ + hs
  | _ => l

/-- The closed segments `seg j` on which the splines coincide with the pieces `j` (see the module
docstring); `seg 0` reaches down to `0` and `seg 6` up to `∞`. -/
@[expose] noncomputable def seg : ℕ → Set ℝ
  | 0 => Ioc 0 (p - c)
  | 1 => Icc (p - c) p
  | 2 => Icc p R₀
  | 3 => Icc R₀ (R₀ + 1 / 1000)
  | 4 => Icc (R₀ + 1 / 1000) (R₀ + hs)
  | 5 => Icc (R₀ + hs) l
  | _ => Ici l

theorem seg_subset_Ioi {j : ℕ} : seg j ⊆ Ioi 0 := by
  have := R₀_pos; have := hs_pos; have := c_pos; have := b_lt_p_sub_c; have := p_lt_R₀
  have := b_pos; have := R₀_lt_l; have := p_pos
  intro r hr
  match j, hr with
  | 0, hr => exact hr.1
  | 1, hr => have := hr.1; simp only [mem_Ioi]; linarith
  | 2, hr => have := hr.1; simp only [mem_Ioi]; linarith
  | 3, hr => have := hr.1; simp only [mem_Ioi]; linarith
  | 4, hr => have := hr.1; simp only [mem_Ioi]; linarith
  | 5, hr => have := hr.1; simp only [mem_Ioi]; linarith
  | n + 6, hr => have := hr; simp only [seg, mem_Ici, mem_Ioi] at this ⊢; linarith

/-! ### The pieces -/

namespace Piece

/-- The piece of `τ`: `0` up to `R₀ + .001`, the quintic ramp on segments 4, 5, and `1` from `l`. -/
@[expose] noncomputable def tau (j : ℕ) (r : ℝ) : ℝ :=
  match j with
  | 0 | 1 | 2 | 3 => 0
  | 4 | 5 => Squintic ((r - R₀ - 1 / 1000) / hs)
  | _ => 1

/-- The piece of `b_i`. -/
@[expose] noncomputable def b (i j : ℕ) (r : ℝ) : ℝ :=
  if i = 0 then
    (match j with
      | 0 | 1 | 2 => gamma r
      | 3 | 4 => contPoly gamma r
      | _ => gamma R₀)
  else
    (match j with
      | 0 => 0
      | 1 => bPoly i r
      | 2 => V i r
      | 3 | 4 => contPoly (V i) r
      | _ => V i R₀)

/-- The piece of the baseline `w_i`: `γ` for `i = 0`, and for `i ≥ 1` the piece of
`U_i = (-1)^i c_i r^{k_i} (1 - S((r - R₀)/(1/10)))`: `S = 0` up to `R₀`, the quintic afterwards. -/
@[expose] noncomputable def w (i j : ℕ) (r : ℝ) : ℝ :=
  if i = 0 then gamma r
  else
    (-1 : ℝ) ^ i * coeff i * r ^ k i *
      (match j with
        | 0 | 1 | 2 => 1
        | _ => 1 - Squintic ((r - R₀) / (1 / 10)))

/-- The piece of `u_i = (1 - τ) w_i + τ b_i`. -/
@[expose] noncomputable def u (i j : ℕ) (r : ℝ) : ℝ :=
  (1 - tau j r) * w i j r + tau j r * b i j r

/-- The piece of `D_i = b_i - u_i`. -/
@[expose] noncomputable def D (i j : ℕ) (r : ℝ) : ℝ := b i j r - u i j r

end Piece

/-! ### `EqOn` lemmas -/

theorem eqOn_tau {j : ℕ} (hj : j ≤ 6) : EqOn tau (Piece.tau j) (seg j) := by
  have := R₀_pos; have := hs_pos; have := p_lt_R₀; have := c_pos
  have h1 := R₀_add_hs_lt_l; have h2 := R₀_add_thousandth_lt_R₀_add_hs
  have h3 := p_gt; have h4 := p_lt; have h5 := R₀_gt
  intro r hr
  interval_cases j
  · exact tau_of_le (by have := hr.2; linarith)
  · exact tau_of_le (by have := hr.2; linarith)
  · exact tau_of_le (by have := hr.2; linarith)
  · exact tau_of_le hr.2
  · exact tau_of_mem_Icc hr.1 (by have := hr.2; linarith)
  · exact tau_of_mem_Icc (by have := hr.1; linarith) hr.2
  · exact tau_of_ge hr

theorem eqOn_bRad (i : ℕ) {j : ℕ} (hj : j ≤ 6) : EqOn (bRad i) (Piece.b i j) (seg j) := by
  have := R₀_pos; have := hs_pos; have := p_lt_R₀; have := c_pos
  have h1 := R₀_add_hs_lt_l; have h2 := R₀_add_thousandth_lt_R₀_add_hs
  have h3 := p_gt; have h4 := p_lt; have h5 := R₀_gt
  intro r hr
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · interval_cases j
    · simp only [Piece.b, ite_true]
      exact bRad_zero_of_le_R₀ (by have := hr.2; linarith)
    · simp only [Piece.b, ite_true]
      exact bRad_zero_of_le_R₀ (by have := hr.2; linarith)
    · simp only [Piece.b, ite_true]
      exact bRad_zero_of_le_R₀ hr.2
    · simp only [Piece.b, ite_true]
      rcases hr.1.eq_or_lt with rfl | hlt
      · rw [bRad_zero_of_le_R₀ le_rfl]
        simp [contPoly, contPolyC]
      · rw [bRad_zero_of_gt hlt, cont_of_le _ (by have := hr.2; linarith)]
    · simp only [Piece.b, ite_true]
      rw [bRad_zero_of_gt (by have := hr.1; linarith), cont_of_le _ hr.2]
    · simp only [Piece.b, ite_true]
      rw [bRad_of_ge (i := 0) hr.1]; simp
    · simp only [Piece.b, ite_true]
      rw [bRad_of_ge (i := 0) (by have hl : l ≤ r := hr; linarith)]; simp
  · have hi0 : i ≠ 0 := hi.ne'
    interval_cases j
    · simp only [Piece.b, hi0, ite_false]
      exact bRad_of_le_inner hi hr.2
    · simp only [Piece.b, hi0, ite_false]
      rcases hr.2.eq_or_lt with rfl | hlt
      · rw [bRad_of_mem_edge hi le_rfl p_lt_R₀.le, V_p, (bPoly_jet_edge i).1]
      · rcases hr.1.eq_or_lt with rfl | hlt'
        · rw [bRad_of_le_inner hi le_rfl, (bPoly_jet_inner i).1]
        · rw [bRad_of_mem_inner hi hlt' hlt, bInner_eq_bPoly hr.1 hr.2]
    · simp only [Piece.b, hi0, ite_false]
      exact bRad_of_mem_edge hi hr.1 hr.2
    · simp only [Piece.b, hi0, ite_false]
      rcases hr.1.eq_or_lt with rfl | hlt
      · rw [bRad_of_mem_edge hi p_lt_R₀.le le_rfl]
        simp [contPoly, contPolyC]
      · rw [bRad_of_gt hi hlt, cont_of_le _ (by have := hr.2; linarith)]
    · simp only [Piece.b, hi0, ite_false]
      rw [bRad_of_gt hi (by have := hr.1; linarith), cont_of_le _ hr.2]
    · simp only [Piece.b, hi0, ite_false]
      rw [bRad_of_ge (i := i) hr.1]; simp [hi0]
    · simp only [Piece.b, hi0, ite_false]
      rw [bRad_of_ge (i := i) (by have hl : l ≤ r := hr; linarith)]; simp [hi0]

/-- On `[R₀, R₀ + .1]` (`≥ [R₀, l]`) the cutoff of `U_m` is the quintic. -/
theorem S_U_of_mem {r : ℝ} (h0 : R₀ ≤ r) (h1 : r ≤ l) :
    S ((r - R₀) / (1 / 10)) = Squintic ((r - R₀) / (1 / 10)) := by
  apply S_of_mem_Icc
  · exact div_nonneg (by linarith) (by norm_num)
  · rw [div_le_one (by norm_num)]
    unfold l at h1; linarith

theorem eqOn_u (i : ℕ) {j : ℕ} (hj : j ≤ 6) : EqOn (u i) (Piece.u i j) (seg j) := by
  have := R₀_pos; have := hs_pos; have := p_lt_R₀; have := c_pos
  have h1 := R₀_add_hs_lt_l; have h2 := R₀_add_thousandth_lt_R₀_add_hs
  have h3 := p_gt; have h4 := p_lt; have h5 := R₀_gt
  intro r hr
  have ht := eqOn_tau hj hr
  have hb := eqOn_bRad i hj hr
  by_cases hj6 : j = 6
  · subst hj6
    have hge : l ≤ r := hr
    rw [u_of_ge hge, hb]
    simp [Piece.u, Piece.tau]
  · have hj5 : j ≤ 5 := by omega
    have hw : (if i = 0 then gamma r else U i r) = Piece.w i j r := by
      by_cases hi : i = 0
      · simp [Piece.w, hi]
      · simp only [hi, ite_false, Piece.w, U]
        interval_cases j
        · rw [S_U_of_le (by have := hr.2; linarith)]; simp
        · rw [S_U_of_le (by have := hr.2; linarith)]; simp
        · rw [S_U_of_le hr.2]; simp
        · rw [S_U_of_mem hr.1 (by have := hr.2; linarith)]; rfl
        · rw [S_U_of_mem (by have := hr.1; linarith) (by have := hr.2; linarith)]; rfl
        · rw [S_U_of_mem (by have := hr.1; linarith) hr.2]; rfl
    unfold u Piece.u
    by_cases hi : i = 0
    · subst hi
      simp only [ite_true] at hw ⊢
      rw [ht, hb, ← hw]
    · simp only [hi, ite_false] at hw ⊢
      rw [ht, hb, ← hw]

theorem eqOn_D (i : ℕ) {j : ℕ} (hj : j ≤ 6) : EqOn (D i) (Piece.D i j) (seg j) := by
  intro r hr
  simp only [D, Piece.D]
  rw [eqOn_bRad i hj hr, eqOn_u i hj hr]

end Calibration

end SandierSerfaty
