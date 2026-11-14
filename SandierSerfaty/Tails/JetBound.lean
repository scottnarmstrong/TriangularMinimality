/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Jet2
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Jets with pointwise norm bounds

`JB U F B`: `F` has a second-order jet `(F, F₁, F₂)` on the open set `U`, and `|F|_{2,t} ≤ B t` at every `t ∈ U`
(`jn`, the norm of paper §6.3). The calculus (sums, products, finite and infinite sums) propagates both the
jet and the bound; the bound of an infinite sum is the sum of the bounds, and the jet exists as soon as the
bounds are uniformly summable on `U` (`JB.tsum`).

`JB1 U F B` is the same for first-order jets and the norm `jn₁`.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

/-- `F` has a 2-jet on `U` with `|F|_{2,t} ≤ B t` for `t ∈ U`. -/
@[expose] def JB (U : Set ℝ) (F B : ℝ → ℝ) : Prop :=
  ∃ F₁ F₂ : ℝ → ℝ, Jet2 U U F F₁ F₂ ∧ ∀ t ∈ U, jn F F₁ F₂ t ≤ B t

namespace JB

variable {U : Set ℝ} {F G B C : ℝ → ℝ}

theorem of_jet {F₁ F₂ : ℝ → ℝ} (h : Jet2 U U F F₁ F₂) (hb : ∀ t ∈ U, jn F F₁ F₂ t ≤ B t) : JB U F B :=
  ⟨F₁, F₂, h, hb⟩

theorem mono_bound (h : JB U F B) (hBC : ∀ t ∈ U, B t ≤ C t) : JB U F C := by
  obtain ⟨F₁, F₂, hj, hb⟩ := h
  exact ⟨F₁, F₂, hj, fun t ht => (hb t ht).trans (hBC t ht)⟩

theorem mono_set {U' : Set ℝ} (h : JB U F B) (hU : U' ⊆ U) : JB U' F B := by
  obtain ⟨F₁, F₂, hj, hb⟩ := h
  exact ⟨F₁, F₂, hj.mono hU hU subset_rfl, fun t ht => hb t (hU ht)⟩

theorem const (c : ℝ) : JB U (fun _ => c) (fun _ => |c|) :=
  ⟨fun _ => 0, fun _ => 0, Jet2.const c subset_rfl, fun t _ => by simp [jn]⟩

theorem abs_le (h : JB U F B) {t : ℝ} (ht : t ∈ U) : |F t| ≤ B t := by
  obtain ⟨F₁, F₂, -, hb⟩ := h
  have := hb t ht
  unfold jn at this
  linarith [abs_nonneg (F₁ t), abs_nonneg (F₂ t)]

theorem add (hF : JB U F B) (hG : JB U G C) : JB U (fun x => F x + G x) (fun t => B t + C t) := by
  obtain ⟨F₁, F₂, hj, hb⟩ := hF
  obtain ⟨G₁, G₂, hk, hc⟩ := hG
  refine ⟨_, _, hj.add hk, fun t ht => ?_⟩
  exact (jn_add_le F F₁ F₂ G G₁ G₂ t).trans (add_le_add (hb t ht) (hc t ht))

theorem sub (hF : JB U F B) (hG : JB U G C) : JB U (fun x => F x - G x) (fun t => B t + C t) := by
  obtain ⟨F₁, F₂, hj, hb⟩ := hF
  obtain ⟨G₁, G₂, hk, hc⟩ := hG
  refine ⟨_, _, hj.sub' hk, fun t ht => ?_⟩
  exact (jn_sub_le F F₁ F₂ G G₁ G₂ t).trans (add_le_add (hb t ht) (hc t ht))

theorem const_mul (c : ℝ) (hF : JB U F B) : JB U (fun x => c * F x) (fun t => |c| * B t) := by
  obtain ⟨F₁, F₂, hj, hb⟩ := hF
  refine ⟨_, _, hj.const_mul c, fun t ht => ?_⟩
  rw [jn_const_mul]
  exact mul_le_mul_of_nonneg_left (hb t ht) (abs_nonneg c)

theorem mul (hF : JB U F B) (hG : JB U G C) : JB U (fun x => F x * G x) (fun t => B t * C t) := by
  obtain ⟨F₁, F₂, hj, hb⟩ := hF
  obtain ⟨G₁, G₂, hk, hc⟩ := hG
  refine ⟨_, _, hj.mul hk, fun t ht => ?_⟩
  refine (jn_mul F F₁ F₂ G G₁ G₂ t).trans ?_
  exact mul_le_mul (hb t ht) (hc t ht) (jn_nonneg _ _ _ _) ((jn_nonneg _ _ _ _).trans (hb t ht))

theorem id : JB U (fun x => x) (fun t => |t| + 1) :=
  ⟨fun _ => 1, fun _ => 0, Jet2.id subset_rfl, fun t _ => by simp [jn]⟩

theorem finset_sum {ι : Type*} (s : Finset ι) {F B : ι → ℝ → ℝ} (h : ∀ i ∈ s, JB U (F i) (B i)) :
    JB U (fun x => ∑ i ∈ s, F i x) (fun t => ∑ i ∈ s, B i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (U := U) 0).mono_bound fun t _ => by simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Termwise differentiation**: if the bounds are uniformly dominated by a summable `u` on the open
preconnected set `U`, the sum has a jet and its norm is at most the sum of the bounds. -/
theorem tsum {ι : Type*} (hU : IsOpen U) (hUc : IsPreconnected U) {F B : ι → ℝ → ℝ}
    (h : ∀ i, JB U (F i) (B i)) {u : ι → ℝ} (hu : Summable u) (hB : ∀ i, ∀ t ∈ U, B i t ≤ u i) :
    JB U (fun x => ∑' i, F i x) (fun t => ∑' i, B i t) := by
  choose F₁ F₂ hj hb using h
  have hnn : ∀ i, ∀ t ∈ U, 0 ≤ B i t := fun i t ht =>
    (jn_nonneg (F i) (F₁ i) (F₂ i) t).trans (hb i t ht)
  have h0 : ∀ i, ∀ t ∈ U, |F i t| ≤ u i := fun i t ht => by
    have := hb i t ht; have := hB i t ht; unfold jn at *
    linarith [abs_nonneg (F₁ i t), abs_nonneg (F₂ i t)]
  have h1 : ∀ i, ∀ t ∈ U, |F₁ i t| ≤ u i := fun i t ht => by
    have := hb i t ht; have := hB i t ht; unfold jn at *
    linarith [abs_nonneg (F i t), abs_nonneg (F₂ i t)]
  have h2 : ∀ i, ∀ t ∈ U, |F₂ i t| ≤ 2 * u i := fun i t ht => by
    have := hb i t ht; have := hB i t ht; unfold jn at *
    linarith [abs_nonneg (F₁ i t), abs_nonneg (F i t)]
  refine ⟨_, _, Jet2.tsum hU hUc hU hUc subset_rfl hj hu hu (hu.mul_left 2) h0 h1 h2, fun t ht => ?_⟩
  exact jn_tsum_le F F₁ F₂ t (Summable.of_nonneg_of_le (fun i => hnn i t ht) (fun i => hB i t ht) hu)
    (fun i => hb i t ht)

/-- The terms of a family with uniformly summable bounds are summable at each point. -/
theorem summable_family {ι : Type*} {F B : ι → ℝ → ℝ} (h : ∀ i, JB U (F i) (B i)) {u : ι → ℝ}
    (hu : Summable u) (hB : ∀ i, ∀ t ∈ U, B i t ≤ u i) {t : ℝ} (ht : t ∈ U) : Summable fun i => F i t :=
  Summable.of_norm_bounded hu fun i => by
    rw [Real.norm_eq_abs]; exact ((h i).abs_le ht).trans (hB i t ht)

end JB

/-- First-order jets: `F` is differentiable on `U` with derivative `F₁` and `|F|_{1,t} ≤ B t` on `U`. -/
@[expose] def JB1 (U : Set ℝ) (F B : ℝ → ℝ) : Prop :=
  ∃ F₁ : ℝ → ℝ, (∀ x ∈ U, HasDerivAt F (F₁ x) x) ∧ ∀ t ∈ U, jn₁ F F₁ t ≤ B t

namespace JB1

variable {U : Set ℝ} {F G B C : ℝ → ℝ}

theorem mono_bound (h : JB1 U F B) (hBC : ∀ t ∈ U, B t ≤ C t) : JB1 U F C := by
  obtain ⟨F₁, hj, hb⟩ := h
  exact ⟨F₁, hj, fun t ht => (hb t ht).trans (hBC t ht)⟩

theorem mono_set {U' : Set ℝ} (h : JB1 U F B) (hU : U' ⊆ U) : JB1 U' F B := by
  obtain ⟨F₁, hj, hb⟩ := h
  exact ⟨F₁, fun x hx => hj x (hU hx), fun t ht => hb t (hU ht)⟩

theorem const (c : ℝ) : JB1 U (fun _ => c) (fun _ => |c|) :=
  ⟨fun _ => 0, fun x _ => hasDerivAt_const x c, fun t _ => by simp [jn₁]⟩

theorem abs_le (h : JB1 U F B) {t : ℝ} (ht : t ∈ U) : |F t| ≤ B t := by
  obtain ⟨F₁, -, hb⟩ := h
  have := hb t ht
  unfold jn₁ at this
  linarith [abs_nonneg (F₁ t)]

theorem add (hF : JB1 U F B) (hG : JB1 U G C) : JB1 U (fun x => F x + G x) (fun t => B t + C t) := by
  obtain ⟨F₁, hj, hb⟩ := hF
  obtain ⟨G₁, hk, hc⟩ := hG
  refine ⟨fun x => F₁ x + G₁ x, fun x hx => (hj x hx).add (hk x hx), fun t ht => ?_⟩
  have h := add_le_add (hb t ht) (hc t ht)
  unfold jn₁ at *
  have := abs_add_le (F t) (G t)
  have := abs_add_le (F₁ t) (G₁ t)
  linarith

theorem sub (hF : JB1 U F B) (hG : JB1 U G C) : JB1 U (fun x => F x - G x) (fun t => B t + C t) := by
  obtain ⟨F₁, hj, hb⟩ := hF
  obtain ⟨G₁, hk, hc⟩ := hG
  refine ⟨fun x => F₁ x - G₁ x, fun x hx => (hj x hx).sub (hk x hx), fun t ht => ?_⟩
  have h := add_le_add (hb t ht) (hc t ht)
  unfold jn₁ at *
  have := abs_sub (F t) (G t)
  have := abs_sub (F₁ t) (G₁ t)
  linarith

theorem const_mul (c : ℝ) (hF : JB1 U F B) : JB1 U (fun x => c * F x) (fun t => |c| * B t) := by
  obtain ⟨F₁, hj, hb⟩ := hF
  refine ⟨fun x => c * F₁ x, fun x hx => (hj x hx).const_mul c, fun t ht => ?_⟩
  have h := mul_le_mul_of_nonneg_left (hb t ht) (abs_nonneg c)
  unfold jn₁ at *
  simp only [abs_mul]
  linarith

theorem mul (hF : JB1 U F B) (hG : JB1 U G C) : JB1 U (fun x => F x * G x) (fun t => B t * C t) := by
  obtain ⟨F₁, hj, hb⟩ := hF
  obtain ⟨G₁, hk, hc⟩ := hG
  refine ⟨mul₁ F F₁ G G₁, fun x hx => (hj x hx).mul (hk x hx), fun t ht => ?_⟩
  refine (jn₁_mul F F₁ G G₁ t).trans ?_
  exact mul_le_mul (hb t ht) (hc t ht) (jn₁_nonneg _ _ _) ((jn₁_nonneg _ _ _).trans (hb t ht))

theorem finset_sum {ι : Type*} (s : Finset ι) {F B : ι → ℝ → ℝ} (h : ∀ i ∈ s, JB1 U (F i) (B i)) :
    JB1 U (fun x => ∑ i ∈ s, F i x) (fun t => ∑ i ∈ s, B i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (U := U) 0).mono_bound fun t _ => by simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tsum {ι : Type*} (hU : IsOpen U) (hUc : IsPreconnected U) {F B : ι → ℝ → ℝ}
    (h : ∀ i, JB1 U (F i) (B i)) {u : ι → ℝ} (hu : Summable u) (hB : ∀ i, ∀ t ∈ U, B i t ≤ u i) :
    JB1 U (fun x => ∑' i, F i x) (fun t => ∑' i, B i t) := by
  choose F₁ hj hb using h
  have hnn : ∀ i, ∀ t ∈ U, 0 ≤ B i t := fun i t ht => (jn₁_nonneg (F i) (F₁ i) t).trans (hb i t ht)
  have h0 : ∀ i, ∀ t ∈ U, |F i t| ≤ u i := fun i t ht => by
    have := hb i t ht; have := hB i t ht; unfold jn₁ at *
    linarith [abs_nonneg (F₁ i t)]
  have h1 : ∀ i, ∀ t ∈ U, |F₁ i t| ≤ u i := fun i t ht => by
    have := hb i t ht; have := hB i t ht; unfold jn₁ at *
    linarith [abs_nonneg (F i t)]
  refine ⟨fun x => ∑' i, F₁ i x, fun x hx => ?_, fun t ht => ?_⟩
  · exact hasDerivAt_tsum_of_isPreconnected hu hU hUc (fun i y hy => hj i y hy)
      (fun i y hy => by simpa using h1 i y hy) hx
      (Summable.of_norm_bounded hu fun i => by simpa using h0 i x hx) hx
  · exact jn₁_tsum_le F F₁ t (Summable.of_nonneg_of_le (fun i => hnn i t ht) (fun i => hB i t ht) hu)
      (fun i => hb i t ht)

theorem summable_family {ι : Type*} {F B : ι → ℝ → ℝ} (h : ∀ i, JB1 U (F i) (B i)) {u : ι → ℝ}
    (hu : Summable u) (hB : ∀ i, ∀ t ∈ U, B i t ≤ u i) {t : ℝ} (ht : t ∈ U) : Summable fun i => F i t :=
  Summable.of_norm_bounded hu fun i => by
    rw [Real.norm_eq_abs]; exact ((h i).abs_le ht).trans (hB i t ht)

end JB1

end Tails

end SandierSerfaty

end
