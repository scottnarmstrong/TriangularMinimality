/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Gluing two smooth functions at a point

`Cal.glue a g h x = if x ≤ a then g x else h x`. If `g` and `h` are `C^n` on an open set `U ∋ a` and
their iterated derivatives of order `≤ n` agree at `a`, then `glue a g h` is `C^n` on `U`
(`contDiffOn_glue`). This is the one generic gluing lemma behind the `C²` statements about the splines
of the calibration (paper §5): the splines are `if`-cascades
of globally smooth pieces, so `C²` of a spline reduces to this lemma at each knot, together with the
equality of the pieces' 2-jets there.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Calibration

/-- `glue a g h` equals `g` on `(-∞, a]` and `h` on `(a, ∞)`. -/
@[expose] noncomputable def glue (a : ℝ) (g h : ℝ → ℝ) : ℝ → ℝ := fun x => if x ≤ a then g x else h x

theorem glue_of_le {a : ℝ} {g h : ℝ → ℝ} {x : ℝ} (hx : x ≤ a) : glue a g h x = g x := by
  simp [glue, hx]

theorem glue_of_gt {a : ℝ} {g h : ℝ → ℝ} {x : ℝ} (hx : a < x) : glue a g h x = h x := by
  simp [glue, not_le.2 hx]

theorem glue_eq_right_of_ge {a : ℝ} {g h : ℝ → ℝ} (hga : g a = h a) {x : ℝ} (hx : a ≤ x) :
    glue a g h x = h x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [glue_of_le le_rfl, hga]
  · exact glue_of_gt hx

theorem continuousAt_glue {a : ℝ} {g h : ℝ → ℝ} (hg : ContinuousAt g a) (hh : ContinuousAt h a)
    (hga : g a = h a) : ContinuousAt (glue a g h) a := by
  have h1 : ContinuousWithinAt (glue a g h) (Iic a) a :=
    hg.continuousWithinAt.congr (fun x hx => glue_of_le hx) (glue_of_le le_rfl)
  have h2 : ContinuousWithinAt (glue a g h) (Ici a) a :=
    hh.continuousWithinAt.congr (fun x hx => glue_eq_right_of_ge hga hx)
      (glue_eq_right_of_ge hga le_rfl)
  have := h1.union h2
  rwa [Iic_union_Ici, continuousWithinAt_univ] at this

theorem hasDerivAt_glue {a : ℝ} {g h : ℝ → ℝ} {g' h' : ℝ} (hg : HasDerivAt g g' a)
    (hh : HasDerivAt h h' a) (hga : g a = h a) (hd : g' = h') :
    HasDerivAt (glue a g h) g' a := by
  have h1 : HasDerivWithinAt (glue a g h) g' (Iic a) a :=
    hg.hasDerivWithinAt.congr (fun x hx => glue_of_le hx) (glue_of_le le_rfl)
  have h2 : HasDerivWithinAt (glue a g h) g' (Ici a) a := by
    rw [hd]
    exact hh.hasDerivWithinAt.congr (fun x hx => glue_eq_right_of_ge hga hx)
      (glue_eq_right_of_ge hga le_rfl)
  have := h1.union h2
  rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this

theorem contDiffOn_glue {U : Set ℝ} (hU : IsOpen U) {a : ℝ} (ha : a ∈ U) :
    ∀ (n : ℕ) (g h : ℝ → ℝ), ContDiffOn ℝ n g U → ContDiffOn ℝ n h U →
      (∀ j ≤ n, iteratedDeriv j g a = iteratedDeriv j h a) →
      ContDiffOn ℝ n (glue a g h) U := by
  intro n
  induction n with
  | zero =>
    intro g h hg hh hj
    have hga : g a = h a := by simpa using hj 0 le_rfl
    rw [Nat.cast_zero, contDiffOn_zero] at hg hh ⊢
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    have hgx : ContinuousAt g x := hg.continuousAt (hU.mem_nhds hx)
    have hhx : ContinuousAt h x := hh.continuousAt (hU.mem_nhds hx)
    rcases lt_trichotomy x a with hxa | rfl | hxa
    · exact hgx.congr (eventually_of_mem (Iio_mem_nhds hxa) fun y hy => (glue_of_le hy.le).symm)
    · exact continuousAt_glue hgx hhx hga
    · exact hhx.congr (eventually_of_mem (Ioi_mem_nhds hxa) fun y hy => (glue_of_gt hy).symm)
  | succ n ih =>
    intro g h hg hh hj
    have hn : (n : WithTop ℕ∞) + 1 = ((n + 1 : ℕ) : WithTop ℕ∞) := by push_cast; rfl
    have hg1 := (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : WithTop ℕ∞)) hU).1 (hn ▸ hg)
    have hh1 := (contDiffOn_succ_iff_deriv_of_isOpen (n := (n : WithTop ℕ∞)) hU).1 (hn ▸ hh)
    have hjd : ∀ j ≤ n, iteratedDeriv j (deriv g) a = iteratedDeriv j (deriv h) a := by
      intro j hjn
      rw [← iteratedDeriv_succ', ← iteratedDeriv_succ']
      exact hj (j + 1) (by omega)
    have key : ∀ x ∈ U, HasDerivAt (glue a g h) (glue a (deriv g) (deriv h) x) x := by
      intro x hx
      have hgx : HasDerivAt g (deriv g x) x :=
        ((hg1.1 x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
      have hhx : HasDerivAt h (deriv h x) x :=
        ((hh1.1 x hx).differentiableAt (hU.mem_nhds hx)).hasDerivAt
      rcases lt_trichotomy x a with hxa | rfl | hxa
      · have e1 : glue x (deriv g) (deriv h) x = deriv g x := glue_of_le le_rfl
        rw [glue_of_le hxa.le]
        exact hgx.congr_of_eventuallyEq
          (eventually_of_mem (Iio_mem_nhds hxa) fun y hy => glue_of_le hy.le)
      · have h0 : g x = h x := by simpa using hj 0 (Nat.zero_le _)
        have h1 : deriv g x = deriv h x := by simpa using hj 1 (by omega)
        rw [glue_of_le le_rfl]
        exact hasDerivAt_glue hgx hhx h0 h1
      · rw [glue_of_gt hxa]
        exact hhx.congr_of_eventuallyEq
          (eventually_of_mem (Ioi_mem_nhds hxa) fun y hy => glue_of_gt hy)
    have hder : ∀ x ∈ U, deriv (glue a g h) x = glue a (deriv g) (deriv h) x :=
      fun x hx => (key x hx).deriv
    rw [← hn, contDiffOn_succ_iff_deriv_of_isOpen hU]
    refine ⟨fun x hx => (key x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro h; exact absurd h (by simp)
    · exact (ih (deriv g) (deriv h) hg1.2.2 hh1.2.2 hjd).congr hder

theorem eventuallyEq_glue_left {a x : ℝ} (g h : ℝ → ℝ) (hx : x < a) :
    glue a g h =ᶠ[nhds x] g :=
  eventually_of_mem (Iio_mem_nhds hx) fun _ hy => glue_of_le hy.le

/-- The `C²` gluing lemma in terms of the 2-jets (`f a`, `f' a`, `f'' a`). -/
theorem contDiffOn_glue_two {U : Set ℝ} (hU : IsOpen U) {a : ℝ} (ha : a ∈ U) {g h : ℝ → ℝ}
    (hg : ContDiffOn ℝ 2 g U) (hh : ContDiffOn ℝ 2 h U) (h0 : g a = h a)
    (h1 : deriv g a = deriv h a) (h2 : deriv (deriv g) a = deriv (deriv h) a) :
    ContDiffOn ℝ 2 (glue a g h) U := by
  have hj : ∀ j ≤ 2, iteratedDeriv j g a = iteratedDeriv j h a := by
    intro j hj
    obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    · simpa using h0
    · simpa [iteratedDeriv_one] using h1
    · simpa [iteratedDeriv_succ, iteratedDeriv_one] using h2
  have := contDiffOn_glue hU ha 2 g h (by exact_mod_cast hg) (by exact_mod_cast hh) hj
  exact_mod_cast this

end Calibration

end SandierSerfaty
