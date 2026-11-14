/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Second-order jets with pointwise norms (paper `tail:norms`)

The norms `|F|_{2,t} = |F(t)| + |F'(t)| + |F''(t)|/2` of the paper (`tail:norms`) are evaluated on explicit
derivative functions:

* `Jet2 U V f f₁ f₂`: `f' = f₁` at every point of `U` and `f₁' = f₂` at every point of `V ⊆ U`
  (so `V = ∅` is a jet of order one; the splines of §5 are `C²` but only piecewise `C³`);
* the calculus: constants, the identity, sums, products (with the explicit Leibniz expressions `mul₁`,
  `mul₂`), finite and infinite sums (`Jet2.tsum`, termwise differentiation on a preconnected open set);
* `jn f f₁ f₂ t = |f t| + |f₁ t| + |f₂ t|/2` (the norm of the paper) and `jn₁ f f₁ t = |f t| + |f₁ t|`;
  `jn_mul_le`, `jn₁_mul_le`: the norms are submultiplicative (paper §6.3).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

/-- `f' = f₁` on `U` and `f₁' = f₂` on `V ⊆ U`. -/
structure Jet2 (U V : Set ℝ) (f f₁ f₂ : ℝ → ℝ) : Prop where
  d0 : ∀ x ∈ U, HasDerivAt f (f₁ x) x
  d1 : ∀ x ∈ V, HasDerivAt f₁ (f₂ x) x
  sub : V ⊆ U

/-- The paper's norm `|F|_{2,t}` of a second-order jet at `t`. -/
@[expose] noncomputable def jn (f f₁ f₂ : ℝ → ℝ) (t : ℝ) : ℝ := |f t| + |f₁ t| + |f₂ t| / 2

/-- The first-order norm `|F|_{1,t}`. -/
@[expose] noncomputable def jn₁ (f f₁ : ℝ → ℝ) (t : ℝ) : ℝ := |f t| + |f₁ t|

/-- The first derivative of a product of jets. -/
@[expose] def mul₁ (f f₁ g g₁ : ℝ → ℝ) : ℝ → ℝ := fun x => f₁ x * g x + f x * g₁ x

/-- The second derivative of a product of jets. -/
@[expose] def mul₂ (f f₁ f₂ g g₁ g₂ : ℝ → ℝ) : ℝ → ℝ := fun x =>
  (f₂ x * g x + f₁ x * g₁ x) + (f₁ x * g₁ x + f x * g₂ x)

namespace Jet2

variable {U V : Set ℝ} {f f₁ f₂ g g₁ g₂ : ℝ → ℝ}

theorem const (c : ℝ) (hVU : V ⊆ U) : Jet2 U V (fun _ => c) (fun _ => 0) (fun _ => 0) :=
  ⟨fun x _ => hasDerivAt_const x c, fun x _ => hasDerivAt_const x _, hVU⟩

theorem id (hVU : V ⊆ U) : Jet2 U V (fun x => x) (fun _ => 1) (fun _ => 0) :=
  ⟨fun x _ => hasDerivAt_id' x, fun x _ => hasDerivAt_const x _, hVU⟩

theorem mono {U' V' : Set ℝ} (h : Jet2 U V f f₁ f₂) (hU : U' ⊆ U) (hV : V' ⊆ V) (hVU : V' ⊆ U') :
    Jet2 U' V' f f₁ f₂ :=
  ⟨fun x hx => h.d0 x (hU hx), fun x hx => h.d1 x (hV hx), hVU⟩

theorem add (hf : Jet2 U V f f₁ f₂) (hg : Jet2 U V g g₁ g₂) :
    Jet2 U V (fun x => f x + g x) (fun x => f₁ x + g₁ x) (fun x => f₂ x + g₂ x) :=
  ⟨fun x hx => (hf.d0 x hx).add (hg.d0 x hx), fun x hx => (hf.d1 x hx).add (hg.d1 x hx), hf.sub⟩

theorem sub' (hf : Jet2 U V f f₁ f₂) (hg : Jet2 U V g g₁ g₂) :
    Jet2 U V (fun x => f x - g x) (fun x => f₁ x - g₁ x) (fun x => f₂ x - g₂ x) :=
  ⟨fun x hx => (hf.d0 x hx).sub (hg.d0 x hx), fun x hx => (hf.d1 x hx).sub (hg.d1 x hx), hf.sub⟩

theorem const_mul (c : ℝ) (hf : Jet2 U V f f₁ f₂) :
    Jet2 U V (fun x => c * f x) (fun x => c * f₁ x) (fun x => c * f₂ x) :=
  ⟨fun x hx => (hf.d0 x hx).const_mul c, fun x hx => (hf.d1 x hx).const_mul c, hf.sub⟩

theorem mul (hf : Jet2 U V f f₁ f₂) (hg : Jet2 U V g g₁ g₂) :
    Jet2 U V (fun x => f x * g x) (mul₁ f f₁ g g₁) (mul₂ f f₁ f₂ g g₁ g₂) := by
  refine ⟨fun x hx => (hf.d0 x hx).mul (hg.d0 x hx), fun x hx => ?_, hf.sub⟩
  have h1 := ((hf.d1 x hx).mul (hg.d0 x (hf.sub hx))).add ((hf.d0 x (hf.sub hx)).mul (hg.d1 x hx))
  exact h1

theorem congr {f' f₁' f₂' : ℝ → ℝ} (hU : IsOpen U) (h : Jet2 U V f f₁ f₂)
    (e0 : EqOn f f' U) (e1 : EqOn f₁ f₁' U) (e2 : EqOn f₂ f₂' V) : Jet2 U V f' f₁' f₂' := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, h.sub⟩
  · rw [← e1 hx]
    exact (h.d0 x hx).congr_of_eventuallyEq ((e0.eventuallyEq_of_mem (hU.mem_nhds hx)).symm)
  · rw [← e2 hx]
    exact (h.d1 x hx).congr_of_eventuallyEq ((e1.eventuallyEq_of_mem (hU.mem_nhds (h.sub hx))).symm)

theorem finset_sum {ι : Type*} (s : Finset ι) {F F₁ F₂ : ι → ℝ → ℝ} (hVU : V ⊆ U)
    (h : ∀ i ∈ s, Jet2 U V (F i) (F₁ i) (F₂ i)) :
    Jet2 U V (fun x => ∑ i ∈ s, F i x) (fun x => ∑ i ∈ s, F₁ i x) (fun x => ∑ i ∈ s, F₂ i x) :=
  ⟨fun x hx => HasDerivAt.fun_sum fun i hi => (h i hi).d0 x hx,
    fun x hx => HasDerivAt.fun_sum fun i hi => (h i hi).d1 x hx, hVU⟩

theorem deriv_eq (hU : IsOpen U) (h : Jet2 U U f f₁ f₂) {t : ℝ} (ht : t ∈ U) :
    deriv f t = f₁ t ∧ deriv (deriv f) t = f₂ t := by
  refine ⟨(h.d0 t ht).deriv, ?_⟩
  have e : deriv f =ᶠ[nhds t] f₁ :=
    Filter.eventually_of_mem (hU.mem_nhds ht) fun x hx => (h.d0 x hx).deriv
  rw [e.deriv_eq]
  exact (h.d1 t ht).deriv

/-- **Termwise differentiation** of a family of jets with summable bounds (`hasDerivAt_tsum_of_isPreconnected`
twice): `U`, `V` are preconnected open sets, `|f i| ≤ u₀ i`, `|f₁ i| ≤ u₁ i` on `U` and `|f₂ i| ≤ u₂ i` on `V`. -/
theorem tsum {ι : Type*} {F F₁ F₂ : ι → ℝ → ℝ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hV : IsOpen V) (hVc : IsPreconnected V) (hVU : V ⊆ U)
    (h : ∀ i, Jet2 U V (F i) (F₁ i) (F₂ i)) {u₀ u₁ u₂ : ι → ℝ}
    (hu₀ : Summable u₀) (hu₁ : Summable u₁) (hu₂ : Summable u₂)
    (h₀ : ∀ i, ∀ x ∈ U, |F i x| ≤ u₀ i) (h₁ : ∀ i, ∀ x ∈ U, |F₁ i x| ≤ u₁ i)
    (h₂ : ∀ i, ∀ x ∈ V, |F₂ i x| ≤ u₂ i) :
    Jet2 U V (fun x => ∑' i, F i x) (fun x => ∑' i, F₁ i x) (fun x => ∑' i, F₂ i x) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, hVU⟩
  · exact hasDerivAt_tsum_of_isPreconnected hu₁ hU hUc (fun i y hy => (h i).d0 y hy)
      (fun i y hy => by simpa using h₁ i y hy) hx
      (Summable.of_norm_bounded hu₀ fun i => by simpa using h₀ i x hx) hx
  · refine hasDerivAt_tsum_of_isPreconnected hu₂ hV hVc (fun i y hy => (h i).d1 y hy)
      (fun i y hy => by simpa using h₂ i y hy) hx
      (Summable.of_norm_bounded hu₁ fun i => by simpa using h₁ i x (hVU hx)) hx

end Jet2

/-! ### Submultiplicativity of the norms (paper §6.3) -/

theorem jn_mul_le (a0 a1 a2 b0 b1 b2 : ℝ) :
    |a0 * b0| + |a1 * b0 + a0 * b1| + |(a2 * b0 + a1 * b1) + (a1 * b1 + a0 * b2)| / 2 ≤
      (|a0| + |a1| + |a2| / 2) * (|b0| + |b1| + |b2| / 2) := by
  have h1 : |a1 * b0 + a0 * b1| ≤ |a1| * |b0| + |a0| * |b1| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
  have h2 : |(a2 * b0 + a1 * b1) + (a1 * b1 + a0 * b2)| ≤
      |a2| * |b0| + 2 * (|a1| * |b1|) + |a0| * |b2| := by
    have e1 := abs_add_le (a2 * b0 + a1 * b1) (a1 * b1 + a0 * b2)
    have e2 := abs_add_le (a2 * b0) (a1 * b1)
    have e3 := abs_add_le (a1 * b1) (a0 * b2)
    simp only [abs_mul] at e1 e2 e3
    linarith
  rw [abs_mul]
  nlinarith [abs_nonneg a0, abs_nonneg a1, abs_nonneg a2, abs_nonneg b0, abs_nonneg b1, abs_nonneg b2,
    mul_nonneg (abs_nonneg a2) (abs_nonneg b2), mul_nonneg (abs_nonneg a1) (abs_nonneg b2),
    mul_nonneg (abs_nonneg a2) (abs_nonneg b1)]

theorem jn₁_mul_le (a0 a1 b0 b1 : ℝ) :
    |a0 * b0| + |a1 * b0 + a0 * b1| ≤ (|a0| + |a1|) * (|b0| + |b1|) := by
  have h1 : |a1 * b0 + a0 * b1| ≤ |a1| * |b0| + |a0| * |b1| := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
  rw [abs_mul]
  nlinarith [abs_nonneg a0, abs_nonneg a1, abs_nonneg b0, abs_nonneg b1]

theorem jn_mul (f f₁ f₂ g g₁ g₂ : ℝ → ℝ) (t : ℝ) :
    jn (fun x => f x * g x) (mul₁ f f₁ g g₁) (mul₂ f f₁ f₂ g g₁ g₂) t ≤
      jn f f₁ f₂ t * jn g g₁ g₂ t :=
  jn_mul_le (f t) (f₁ t) (f₂ t) (g t) (g₁ t) (g₂ t)

theorem jn₁_mul (f f₁ g g₁ : ℝ → ℝ) (t : ℝ) :
    jn₁ (fun x => f x * g x) (mul₁ f f₁ g g₁) t ≤ jn₁ f f₁ t * jn₁ g g₁ t :=
  jn₁_mul_le (f t) (f₁ t) (g t) (g₁ t)

theorem jn_nonneg (f f₁ f₂ : ℝ → ℝ) (t : ℝ) : 0 ≤ jn f f₁ f₂ t := by
  unfold jn; positivity

theorem jn₁_nonneg (f f₁ : ℝ → ℝ) (t : ℝ) : 0 ≤ jn₁ f f₁ t := by
  unfold jn₁; positivity

theorem jn_add_le (f f₁ f₂ g g₁ g₂ : ℝ → ℝ) (t : ℝ) :
    jn (fun x => f x + g x) (fun x => f₁ x + g₁ x) (fun x => f₂ x + g₂ x) t ≤
      jn f f₁ f₂ t + jn g g₁ g₂ t := by
  unfold jn
  have := abs_add_le (f t) (g t)
  have := abs_add_le (f₁ t) (g₁ t)
  have := abs_add_le (f₂ t) (g₂ t)
  linarith

theorem jn_sub_le (f f₁ f₂ g g₁ g₂ : ℝ → ℝ) (t : ℝ) :
    jn (fun x => f x - g x) (fun x => f₁ x - g₁ x) (fun x => f₂ x - g₂ x) t ≤
      jn f f₁ f₂ t + jn g g₁ g₂ t := by
  unfold jn
  have := abs_sub (f t) (g t)
  have := abs_sub (f₁ t) (g₁ t)
  have := abs_sub (f₂ t) (g₂ t)
  linarith

theorem jn_const_mul (c : ℝ) (f f₁ f₂ : ℝ → ℝ) (t : ℝ) :
    jn (fun x => c * f x) (fun x => c * f₁ x) (fun x => c * f₂ x) t = |c| * jn f f₁ f₂ t := by
  unfold jn
  simp only [abs_mul]
  ring

/-- The norm of a termwise sum is at most the sum of the norms. -/
theorem jn_tsum_le {ι : Type*} (F F₁ F₂ : ι → ℝ → ℝ) (t : ℝ) {c : ι → ℝ} (hc : Summable c)
    (h : ∀ i, jn (F i) (F₁ i) (F₂ i) t ≤ c i) :
    jn (fun x => ∑' i, F i x) (fun x => ∑' i, F₁ i x) (fun x => ∑' i, F₂ i x) t ≤ ∑' i, c i := by
  have b0 : ∀ i, |F i t| ≤ c i := fun i => by
    have := h i; unfold jn at this; have := abs_nonneg (F₁ i t); have := abs_nonneg (F₂ i t); linarith
  have b1 : ∀ i, |F₁ i t| ≤ c i := fun i => by
    have := h i; unfold jn at this; have := abs_nonneg (F i t); have := abs_nonneg (F₂ i t); linarith
  have b2 : ∀ i, |F₂ i t| / 2 ≤ c i := fun i => by
    have := h i; unfold jn at this; have := abs_nonneg (F₁ i t); have := abs_nonneg (F i t); linarith
  have s0 : Summable fun i => |F i t| :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) b0 hc
  have s1 : Summable fun i => |F₁ i t| :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) b1 hc
  have s2 : Summable fun i => |F₂ i t| / 2 :=
    Summable.of_nonneg_of_le (fun i => by positivity) b2 hc
  have e0 : |∑' i, F i t| ≤ ∑' i, |F i t| := by
    simpa using norm_tsum_le_tsum_norm (f := fun i => F i t) (by simpa using s0)
  have e1 : |∑' i, F₁ i t| ≤ ∑' i, |F₁ i t| := by
    simpa using norm_tsum_le_tsum_norm (f := fun i => F₁ i t) (by simpa using s1)
  have e2 : |∑' i, F₂ i t| / 2 ≤ ∑' i, |F₂ i t| / 2 := by
    have : |∑' i, F₂ i t| ≤ ∑' i, |F₂ i t| := by
      simpa using norm_tsum_le_tsum_norm (f := fun i => F₂ i t) (by
        simpa using (s2.mul_left 2).congr fun i => by ring)
    rw [tsum_div_const]; linarith
  have : ∑' i, (|F i t| + |F₁ i t| + |F₂ i t| / 2) ≤ ∑' i, c i := by
    refine Summable.tsum_le_tsum (fun i => ?_) ((s0.add s1).add s2) hc
    exact h i
  rw [Summable.tsum_add ((s0.add s1)) s2, Summable.tsum_add s0 s1] at this
  unfold jn
  linarith

/-- First-order version of `jn_tsum_le`. -/
theorem jn₁_tsum_le {ι : Type*} (F F₁ : ι → ℝ → ℝ) (t : ℝ) {c : ι → ℝ} (hc : Summable c)
    (h : ∀ i, jn₁ (F i) (F₁ i) t ≤ c i) :
    jn₁ (fun x => ∑' i, F i x) (fun x => ∑' i, F₁ i x) t ≤ ∑' i, c i := by
  have b0 : ∀ i, |F i t| ≤ c i := fun i => by
    have := h i; unfold jn₁ at this; have := abs_nonneg (F₁ i t); linarith
  have b1 : ∀ i, |F₁ i t| ≤ c i := fun i => by
    have := h i; unfold jn₁ at this; have := abs_nonneg (F i t); linarith
  have s0 : Summable fun i => |F i t| :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) b0 hc
  have s1 : Summable fun i => |F₁ i t| :=
    Summable.of_nonneg_of_le (fun i => abs_nonneg _) b1 hc
  have e0 : |∑' i, F i t| ≤ ∑' i, |F i t| := by
    simpa using norm_tsum_le_tsum_norm (f := fun i => F i t) (by simpa using s0)
  have e1 : |∑' i, F₁ i t| ≤ ∑' i, |F₁ i t| := by
    simpa using norm_tsum_le_tsum_norm (f := fun i => F₁ i t) (by simpa using s1)
  have : ∑' i, (|F i t| + |F₁ i t|) ≤ ∑' i, c i := by
    refine Summable.tsum_le_tsum (fun i => ?_) (s0.add s1) hc
    exact h i
  rw [Summable.tsum_add s0 s1] at this
  unfold jn₁
  linarith

end Tails

end SandierSerfaty

end
