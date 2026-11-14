/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Hessian
public import SandierSerfaty.Certificate.Arith.IVLemmas

/-!
# The Hessian assertion on one cell, and local nonnegativity of `theta` (paper `comp:hessian`)

`CellHess Ds Ss A B C` is the real content of a passing Hessian cell `Ds × Ss` with the enclosures `A ∋ ∂_d(gd)`,
`B ∋ ∂_x(gd) = G_d = ∂_d G`, `C ∋ G_s`, in the *difference quotient* form that survives the spline knots (where
`G_dd`, `G_ss` jump): every difference quotient of `gd` in `d` (resp. `x`), of `G` in `d`, in `x`, taken inside the
cell, lies in `A` (resp. `B`, `B`, `C`), and the interval tests `inf A > 0`, `inf C > 0`, `inf (AC - B²) > 0` hold.

* `slope_mem`, `integral_avg_mem`: a difference quotient / an average of a function with enclosed right derivative /
  enclosed values is enclosed.
* `CellHess.step`: for two points of the cell with `q' = q + δ(u, v)`, `δ > 0`: `theta u v q ≤ theta u v q'`
  (`Θ(q') - Θ(q) = δ(u²a + uv(b₁ + b₂) + v²c)` with `a ∈ A`, `b₁, b₂ ∈ B`, `c ∈ C`, a nonnegative quadratic form).
* `exists_cell_dir`: a point and a direction, with the forward ray inside `[a_J, a_n]`, have a cell of a node
  sequence containing the point and the ray for a short time.
* `localHess_of_cells`: `LocalHess S` from `CellHess` on the cells of a product partition covering `S`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Calibration

theorem pow128_pos : (0 : ℝ) < 2 ^ 128 := by positivity

theorem mem_of_bounds {x : ℝ} {I : IV 128} (h1 : ((I.lo.toInt : ℤ) : ℝ) / 2 ^ 128 ≤ x)
    (h2 : x ≤ ((I.hi.toInt : ℤ) : ℝ) / 2 ^ 128) : IV.Mem x I :=
  ⟨by rwa [div_le_iff₀ pow128_pos] at h1, by rwa [le_div_iff₀ pow128_pos] at h2⟩

theorem bounds_of_mem {x : ℝ} {I : IV 128} (h : IV.Mem x I) :
    ((I.lo.toInt : ℤ) : ℝ) / 2 ^ 128 ≤ x ∧ x ≤ ((I.hi.toInt : ℤ) : ℝ) / 2 ^ 128 :=
  ⟨by rw [div_le_iff₀ pow128_pos]; exact h.1, by rw [le_div_iff₀ pow128_pos]; exact h.2⟩

/-- **A difference quotient with an enclosed right derivative is enclosed.** -/
theorem slope_mem {f f' : ℝ → ℝ} {d d' : ℝ} {I : IV 128} (hdd : d < d') (hc : ContinuousOn f (Icc d d'))
    (hd : ∀ x ∈ Ico d d', HasDerivWithinAt f (f' x) (Ici x) x) (hm : ∀ x ∈ Ico d d', IV.Mem (f' x) I) :
    IV.Mem ((f d' - f d) / (d' - d)) I := by
  have h1 := le_sub_of_right_deriv (lo := ((I.lo.toInt : ℤ) : ℝ) / 2 ^ 128) hdd.le hc hd
    (fun x hx => (bounds_of_mem (hm x hx)).1)
  have h2 := sub_le_of_right_deriv (hi := ((I.hi.toInt : ℤ) : ℝ) / 2 ^ 128) hdd.le hc hd
    (fun x hx => (bounds_of_mem (hm x hx)).2)
  have hp : 0 < d' - d := sub_pos.2 hdd
  exact mem_of_bounds (by rw [le_div_iff₀ hp]; exact h1) (by rw [div_le_iff₀ hp]; linarith)

/-- **The average of a continuous function with enclosed values is enclosed.** -/
theorem integral_avg_mem {f : ℝ → ℝ} {y y' : ℝ} {I : IV 128} (hyy : y ≤ y') (hc : ContinuousOn f (Icc y y'))
    (hm : ∀ s ∈ Icc y y', IV.Mem (f s) I) : ∃ q, IV.Mem q I ∧ ∫ s in y..y', f s = (y' - y) * q := by
  rcases hyy.eq_or_lt with h | h
  · subst h
    exact ⟨f y, hm y ⟨le_rfl, le_rfl⟩, by simp⟩
  · have hint : IntervalIntegrable f MeasureTheory.volume y y' := hc.intervalIntegrable_of_Icc hyy
    have hp : 0 < y' - y := sub_pos.2 h
    refine ⟨(∫ s in y..y', f s) / (y' - y), ?_, by field_simp⟩
    have lo := intervalIntegral.integral_mono_on hyy (intervalIntegrable_const (c := ((I.lo.toInt : ℤ) : ℝ) / 2 ^ 128))
      hint (fun s hs => (bounds_of_mem (hm s hs)).1)
    have hi := intervalIntegral.integral_mono_on hyy hint
      (intervalIntegrable_const (c := ((I.hi.toInt : ℤ) : ℝ) / 2 ^ 128)) (fun s hs => (bounds_of_mem (hm s hs)).2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at lo hi
    exact mem_of_bounds (by rw [le_div_iff₀ hp]; linarith) (by rw [div_le_iff₀ hp]; linarith)

/-- From the quotient form on `S` to the equation form for any two distinct points of `S`. -/
theorem quot_any {f : ℝ → ℝ} {S : Set ℝ} {I : IV 128}
    (h : ∀ s ∈ S, ∀ s' ∈ S, s < s' → IV.Mem ((f s' - f s) / (s' - s)) I) :
    ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ∃ a, IV.Mem a I ∧ f s' - f s = (s' - s) * a := by
  intro s hs s' hs' hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨_, h s hs s' hs' hlt, by field_simp [sub_ne_zero.2 hne.symm]⟩
  · refine ⟨_, h s' hs' s hs hgt, ?_⟩
    have : s' - s ≠ 0 := sub_ne_zero.2 hne.symm
    have : s - s' ≠ 0 := sub_ne_zero.2 hne
    field_simp
    ring

/-- **A passing Hessian cell** (difference-quotient form). -/
structure CellHess (Ds Ss : Set ℝ) (Aj Bj Cj : IV 128) : Prop where
  /-- Difference quotients of `gd` in `d` lie in `A`. -/
  A : ∀ y ∈ Ss, ∀ d ∈ Ds, ∀ d' ∈ Ds, d < d' → IV.Mem ((gd d' y - gd d y) / (d' - d)) Aj
  /-- Difference quotients of `gd` in `x` lie in `B`. -/
  B1 : ∀ d ∈ Ds, ∀ y ∈ Ss, ∀ y' ∈ Ss, y < y' → IV.Mem ((gd d y' - gd d y) / (y' - y)) Bj
  /-- Difference quotients of `G` in `d` lie in `B`. -/
  B2 : ∀ y ∈ Ss, ∀ d ∈ Ds, ∀ d' ∈ Ds, d < d' → IV.Mem ((G d' y - G d y) / (d' - d)) Bj
  /-- Difference quotients of `G` in `x` lie in `C`. -/
  C : ∀ d ∈ Ds, ∀ y ∈ Ss, ∀ y' ∈ Ss, y < y' → IV.Mem ((G d y' - G d y) / (y' - y)) Cj
  /-- `inf A > 0`. -/
  posA : IV.posB Aj = true
  /-- `inf C > 0`. -/
  posC : IV.posB Cj = true
  /-- `inf (A C - B²) > 0`. -/
  posD : IV.posB (IV.sub (IV.mul Aj Cj) (IV.sq Bj)) = true

/-- The nonnegativity of the quadratic form `u²a + uv(b₁ + b₂) + v²c`. -/
theorem quad_nonneg {a c b₁ b₂ u v : ℝ} (ha : 0 < a) (hc : 0 < c) (h1 : b₁ ^ 2 < a * c) (h2 : b₂ ^ 2 < a * c) :
    0 ≤ u ^ 2 * a + u * v * (b₁ + b₂) + v ^ 2 * c := by
  have key : ∀ b : ℝ, b ^ 2 < a * c → |u * v * b| ≤ (u ^ 2 * a + v ^ 2 * c) / 2 := by
    intro b hb
    refine abs_le_of_sq_le_sq ?_ (by positivity)
    have : (u * v * b) ^ 2 ≤ (u ^ 2 * a) * (v ^ 2 * c) := by
      have : (u * v * b) ^ 2 = u ^ 2 * v ^ 2 * b ^ 2 := by ring
      rw [this]
      have : 0 ≤ u ^ 2 * v ^ 2 := by positivity
      nlinarith
    nlinarith [sq_nonneg (u ^ 2 * a - v ^ 2 * c)]
  have k1 := (abs_le.1 (key b₁ h1)).1
  have k2 := (abs_le.1 (key b₂ h2)).1
  nlinarith

theorem CellHess.pos {Ds Ss : Set ℝ} {Aj Bj Cj : IV 128} (h : CellHess Ds Ss Aj Bj Cj) {a b c : ℝ}
    (ha : IV.Mem a Aj) (hb : IV.Mem b Bj) (hc : IV.Mem c Cj) : 0 < a ∧ 0 < c ∧ b ^ 2 < a * c := by
  refine ⟨IV.posB_sound h.posA ha, IV.posB_sound h.posC hc, ?_⟩
  have := IV.posB_sound h.posD (IV.mem_sub (IV.mem_mul ha hc) (IV.mem_sq hb))
  linarith

/-- **One step inside a cell**: `theta` does not decrease from `q` to `q + δ(u, v)`, both in the cell. -/
theorem CellHess.step {Ds Ss : Set ℝ} {Aj Bj Cj : IV 128} (h : CellHess Ds Ss Aj Bj Cj) {d x d' x' δ u v : ℝ}
    (hd : d ∈ Ds) (hd' : d' ∈ Ds) (hx : x ∈ Ss) (hx' : x' ∈ Ss) (hδ : 0 < δ) (hdu : d' = d + δ * u)
    (hxv : x' = x + δ * v) : theta u v d x ≤ theta u v d' x' := by
  have qA := fun y hy => quot_any (f := fun d => gd d y) (S := Ds) (I := Aj) (h.A y hy)
  have qB1 := fun d hd => quot_any (f := fun y => gd d y) (S := Ss) (I := Bj) (h.B1 d hd)
  have qB2 := fun y hy => quot_any (f := fun d => G d y) (S := Ds) (I := Bj) (h.B2 y hy)
  have qC := fun d hd => quot_any (f := fun y => G d y) (S := Ss) (I := Cj) (h.C d hd)
  have hdiff : theta u v d' x' - theta u v d x =
      u * ((gd d' x' - gd d x') + (gd d x' - gd d x)) + v * ((G d' x' - G d x') + (G d x' - G d x)) := by
    simp only [theta]; ring
  have hd'd : d' - d = δ * u := by rw [hdu]; ring
  have hx'x : x' - x = δ * v := by rw [hxv]; ring
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · simp [theta, hdu, hxv, hu, hv]
    · -- `d' = d`, only the `C` term
      have hdd : d' = d := by rw [hdu, hu]; ring
      have hne : x ≠ x' := fun e => by rw [← e] at hx'x; simp [hδ.ne', hv] at hx'x
      obtain ⟨c, hc, hce⟩ := qC d hd x hx x' hx' hne
      have hcpos := IV.posB_sound h.posC hc
      have : theta u v d' x' - theta u v d x = δ * v ^ 2 * c := by
        rw [hdiff, hdd, hu]
        have : G d x' - G d x = (x' - x) * c := hce
        rw [this, hx'x]; ring
      have : 0 ≤ δ * v ^ 2 * c := by positivity
      linarith
  · by_cases hv : v = 0
    · have hxx : x' = x := by rw [hxv, hv]; ring
      have hne : d ≠ d' := fun e => by rw [← e] at hd'd; simp [hδ.ne', hu] at hd'd
      obtain ⟨a, ha, hae⟩ := qA x hx d hd d' hd' hne
      have hapos := IV.posB_sound h.posA ha
      have : theta u v d' x' - theta u v d x = δ * u ^ 2 * a := by
        rw [hdiff, hxx, hv]
        have : gd d' x - gd d x = (d' - d) * a := hae
        rw [this, hd'd]; ring
      have : 0 ≤ δ * u ^ 2 * a := by positivity
      linarith
    · have hned : d ≠ d' := fun e => by rw [← e] at hd'd; simp [hδ.ne', hu] at hd'd
      have hnex : x ≠ x' := fun e => by rw [← e] at hx'x; simp [hδ.ne', hv] at hx'x
      obtain ⟨a, ha, hae⟩ := qA x' hx' d hd d' hd' hned
      obtain ⟨b1, hb1, hb1e⟩ := qB1 d hd x hx x' hx' hnex
      obtain ⟨b2, hb2, hb2e⟩ := qB2 x' hx' d hd d' hd' hned
      obtain ⟨c, hc, hce⟩ := qC d hd x hx x' hx' hnex
      obtain ⟨hapos, hcpos, hb1p⟩ := h.pos ha hb1 hc
      obtain ⟨-, -, hb2p⟩ := h.pos ha hb2 hc
      have hq := quad_nonneg (u := u) (v := v) hapos hcpos hb1p hb2p
      have : theta u v d' x' - theta u v d x =
          δ * (u ^ 2 * a + u * v * (b1 + b2) + v ^ 2 * c) := by
        rw [hdiff]
        have e1 : gd d' x' - gd d x' = (d' - d) * a := hae
        have e2 : gd d x' - gd d x = (x' - x) * b1 := hb1e
        have e3 : G d' x' - G d x' = (d' - d) * b2 := hb2e
        have e4 : G d x' - G d x = (x' - x) * c := hce
        rw [e1, e2, e3, e4, hd'd, hx'x]; ring
      have : 0 ≤ δ * (u ^ 2 * a + u * v * (b1 + b2) + v ^ 2 * c) := mul_nonneg hδ.le hq
      linarith

end SandierSerfaty.Certificate.Box
