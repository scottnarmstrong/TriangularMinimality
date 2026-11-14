/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The constants of the calibration (paper §5)

Namespace `SandierSerfaty.Calibration` (written `Cal.` below).
The geometry `a, p, R₀, x₀` of paper `cal:geometry`, the spline parameters
`b, hs = h_s, c`, `l = R₀ + 19/250` (paper `cal:radial-data`, `cal:scalar-bounds`), the exponents `k` (paper `cal:coefficients`), and the two
boxes `𝒟 = [b, .697] × [0, .65]` (paper `comp:domain`) and `𝒟₀ = [.52528, .54930] × [.29420, .32621]` (paper `comp:inner-domain`).

The exact side facts of the certificate (`l < .697`, `√(b² + .65²) > l`, `p > 1/2 > b`, `x₀ > .01`,
`t(x₀) = R₀ < l`, `(p, x₀) ∈ int 𝒟₀`; the paper uses them without stating them) are proved here from
`a⁴ = 4/3`, `p⁴ = 1/12`, `R₀⁴ = 4/27` by `norm_num`; none is computed in the certificate.

## Naming choices of the whole `Calibration/` library

* `Cal.b` is the constant `28209/100000`, so the spline `b_i` of paper `cal:inner-continuation` is `Cal.bRad i`; its
  pieces are `Cal.Piece.b i j`. The clipped polynomial is `Cal.S`, its quintic `Cal.Squintic`; the
  polynomials `P, Q` are `Cal.Ppoly, Cal.Qpoly` (`Cal.Q i t` is the radial function of paper `cal:radial-integrals`); the
  continuation `𝓗` is `Cal.cont` (`Cal.H k t` is the sector function `H_k`); the boxes `𝒟, 𝒟₀` are
  `Cal.boxD, Cal.boxD₀` (`Cal.D i` is the radial data).
* Segments are indexed `j = 0, …, 6`: `knot = (b, p - c, p, R₀, R₀ + .001, R₀ + h_s, l)` and
  `seg j = [knot j, knot (j+1)]`, except that `seg 0 = (0, p - c]` reaches down to `0` and `seg 6 = [l, ∞)`.
* `C²` of the splines on `(0, ∞)` is proved structurally (`Glue.lean`, `Radial.lean`).
* `Cal.G d s` is written with `Cal.tt d s = √(d² + s²)`.
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

/-- `a = √(2/√3)`, the lattice scale of the covolume-one triangular lattice (paper `cal:geometry`). -/
@[expose] noncomputable def a : ℝ := √(2 / √3)

/-- `p = a/2`, the inradius of the triangular Voronoi hexagon (paper `cal:geometry`). -/
@[expose] noncomputable def p : ℝ := a / 2

/-- `R₀ = 2p/√3`, the circumradius of the hexagon (paper `cal:geometry`). -/
@[expose] noncomputable def R₀ : ℝ := 2 * p / √3

/-- `x₀ = R₀/2 = p tan(π/6)` (paper `cal:geometry`). -/
@[expose] noncomputable def x₀ : ℝ := R₀ / 2

/-- `l = R₀ + 19/250`, the radius beyond which `D_i = 0` and `B` is constant (paper `cal:radial-data`). -/
@[expose] noncomputable def l : ℝ := R₀ + 19 / 250

/-- `b = 28209/100000`, the lower bound on edge distances (paper `cal:scalar-bounds`). -/
@[expose] noncomputable def b : ℝ := 28209 / 100000

/-- `h_s = 3/40`, the length of the continuation `𝓗` (paper §5.3). -/
@[expose] noncomputable def hs : ℝ := 3 / 40

/-- `c = 3/50`, the length of the inner continuation (paper §5.3). -/
@[expose] noncomputable def c : ℝ := 3 / 50

/-- The exponents `k_0 = 6`, `k_m = 6m` (paper `cal:coefficients`); index `0` is the auxiliary mode. -/
@[expose] def k (m : ℕ) : ℕ := if m = 0 then 6 else 6 * m

@[simp] theorem k_zero : k 0 = 6 := rfl

theorem k_of_pos {m : ℕ} (hm : 0 < m) : k m = 6 * m := by
  simp [k, hm.ne']

theorem k_pos (m : ℕ) : 0 < k m := by
  unfold k; split_ifs with h
  · norm_num
  · omega

theorem six_le_k (m : ℕ) : 6 ≤ k m := by
  unfold k; split_ifs with h
  · exact le_rfl
  · omega

theorem k_even (m : ℕ) : Even (k m) := by
  unfold k; split_ifs with h
  · exact ⟨3, rfl⟩
  · exact ⟨3 * m, by ring⟩

/-- The box `𝒟 = [b, .697] × [0, .65]` of the certificate (paper `comp:domain`), as a subset of the
`(d, s)`-plane. -/
@[expose] noncomputable def boxD : Set (ℝ × ℝ) := Icc b (697 / 1000) ×ˢ Icc 0 (65 / 100)

/-- The inner box `𝒟₀ = [.52528, .54930] × [.29420, .32621]` (paper `comp:inner-domain`). -/
@[expose] noncomputable def boxD₀ : Set (ℝ × ℝ) :=
  Icc (52528 / 100000) (54930 / 100000) ×ˢ Icc (29420 / 100000) (32621 / 100000)

/-! ### Algebraic facts: `a² = 2/√3`, `a⁴ = 4/3`, `p⁴ = 1/12`, `R₀⁴ = 4/27` -/

theorem sqrt_three_sq : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

theorem sqrt_three_pos : 0 < √3 := Real.sqrt_pos.2 (by norm_num)

theorem a_pos : 0 < a := Real.sqrt_pos.2 (by have := sqrt_three_pos; positivity)

theorem a_sq : a ^ 2 = 2 / √3 :=
  Real.sq_sqrt (by have := sqrt_three_pos; positivity)

theorem a_pow_four : a ^ 4 = 4 / 3 := by
  have h : a ^ 4 = (a ^ 2) ^ 2 := by ring
  rw [h, a_sq]
  have := sqrt_three_pos
  field_simp
  rw [sqrt_three_sq]; norm_num

theorem p_pos : 0 < p := by unfold p; have := a_pos; positivity

theorem p_pow_four : p ^ 4 = 1 / 12 := by
  unfold p
  have : (a / 2) ^ 4 = a ^ 4 / 16 := by ring
  rw [this, a_pow_four]; norm_num

theorem R₀_pos : 0 < R₀ := by
  unfold R₀; have := p_pos; have := sqrt_three_pos; positivity

theorem R₀_sq : R₀ ^ 2 = 4 * p ^ 2 / 3 := by
  unfold R₀
  have := sqrt_three_pos
  rw [div_pow, mul_pow, sqrt_three_sq]; norm_num

theorem R₀_pow_four : R₀ ^ 4 = 4 / 27 := by
  have h : R₀ ^ 4 = (R₀ ^ 2) ^ 2 := by ring
  rw [h, R₀_sq]
  have : (4 * p ^ 2 / 3) ^ 2 = 16 * p ^ 4 / 9 := by ring
  rw [this, p_pow_four]; norm_num

theorem x₀_pos : 0 < x₀ := by unfold x₀; have := R₀_pos; positivity

/-- `x₀² = p²/3`, i.e. `x₀ = p tan(π/6)`. -/
theorem x₀_sq : x₀ ^ 2 = p ^ 2 / 3 := by
  unfold x₀; rw [div_pow, R₀_sq]; ring

/-- `p² + x₀² = R₀²`: the point at height `x₀` over the edge midpoint lies on the circumcircle. -/
theorem p_sq_add_x₀_sq : p ^ 2 + x₀ ^ 2 = R₀ ^ 2 := by
  rw [x₀_sq, R₀_sq]; ring

/-- `t(x₀) = √(p² + x₀²) = R₀`. -/
theorem sqrt_p_sq_add_x₀_sq : √(p ^ 2 + x₀ ^ 2) = R₀ := by
  rw [p_sq_add_x₀_sq]; exact Real.sqrt_sq R₀_pos.le

/-- Bounds from a fourth power: if `x ≥ 0`, `x⁴ = r` and `q⁴ < r` then `q < x`. -/
theorem lt_of_pow_four {x q r : ℝ} (hx : 0 ≤ x) (h : x ^ 4 = r) (hq : q ^ 4 < r) : q < x := by
  by_contra hcon
  push Not at hcon
  have := pow_le_pow_left₀ hx hcon 4
  linarith

theorem lt_of_pow_four' {x q r : ℝ} (hq0 : 0 ≤ q) (h : x ^ 4 = r) (hq : r < q ^ 4) : x < q := by
  by_contra hcon
  push Not at hcon
  have := pow_le_pow_left₀ hq0 hcon 4
  linarith

theorem p_gt : 537 / 1000 < p := lt_of_pow_four p_pos.le p_pow_four (by norm_num)

theorem p_lt : p < 538 / 1000 := lt_of_pow_four' (by norm_num) p_pow_four (by norm_num)

theorem R₀_gt : 620 / 1000 < R₀ := lt_of_pow_four R₀_pos.le R₀_pow_four (by norm_num)

theorem R₀_lt : R₀ < 621 / 1000 := lt_of_pow_four' (by norm_num) R₀_pow_four (by norm_num)

theorem x₀_gt : 31 / 100 < x₀ := by unfold x₀; linarith [R₀_gt]

theorem x₀_lt : x₀ < 3105 / 10000 := by unfold x₀; linarith [R₀_lt]

theorem l_gt : 696 / 1000 < l := by unfold l; linarith [R₀_gt]

/-- `l < .697`. -/
theorem l_lt : l < 697 / 1000 := by unfold l; linarith [R₀_lt]

/-- `√(b² + .65²) > l`. -/
theorem l_lt_sqrt : l < √(b ^ 2 + (65 / 100) ^ 2) := by
  have h1 : (697 / 1000 : ℝ) ≤ √(b ^ 2 + (65 / 100) ^ 2) :=
    Real.le_sqrt_of_sq_le (by unfold b; norm_num)
  exact l_lt.trans_le h1

/-- `p > 1/2`. -/
theorem half_lt_p : 1 / 2 < p := by linarith [p_gt]

/-- `b < 1/2`. -/
theorem b_lt_half : b < 1 / 2 := by unfold b; norm_num

theorem b_pos : 0 < b := by unfold b; norm_num

theorem hs_pos : 0 < hs := by unfold hs; norm_num

theorem c_pos : 0 < c := by unfold c; norm_num

theorem b_lt_p : b < p := b_lt_half.trans half_lt_p

theorem R₀_lt_l : R₀ < l := by unfold l; linarith

theorem p_lt_R₀ : p < R₀ := by
  have h1 := p_lt; have h2 := R₀_gt; linarith

theorem l_eq : l = R₀ + 1 / 1000 + hs := by unfold l hs; ring

/-- `p - c > b`: the knots `b < p - c < p` are ordered. -/
theorem b_lt_p_sub_c : b < p - c := by
  have := p_gt; unfold b c; linarith

theorem p_sub_c_lt_p : p - c < p := by unfold c; linarith

theorem R₀_add_hs_lt_l : R₀ + hs < l := by rw [l_eq]; unfold hs; linarith

theorem R₀_add_thousandth_lt_R₀_add_hs : R₀ + 1 / 1000 < R₀ + hs := by unfold hs; linarith

/-- `(p, x₀)` lies in the interior of `𝒟₀`. -/
theorem pt_mem_interior_boxD₀ : (p, x₀) ∈ interior boxD₀ := by
  unfold boxD₀
  rw [interior_prod_eq, interior_Icc, interior_Icc]
  have h1 := p_gt; have h2 := p_lt; have h3 := x₀_gt; have h4 := x₀_lt
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [] <;> linarith

theorem boxD₀_subset_boxD : boxD₀ ⊆ boxD := by
  unfold boxD₀ boxD b
  exact prod_mono (Icc_subset_Icc (by norm_num) (by norm_num))
    (Icc_subset_Icc (by norm_num) (by norm_num))

end Calibration

end SandierSerfaty
