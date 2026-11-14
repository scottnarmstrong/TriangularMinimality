/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Jet2

/-!
# Explicit jets with bounds on a larger set

`JE U S F F₁ F₂ B`: `(F, F₁, F₂)` is a second-order jet on the open set `U` (`Jet2 U U`), and the paper's norm
`|F|_{2,t} = jn F F₁ F₂ t` is at most `B t` at every point `t` of `S` (typically `S ⊇ U` is a closed spline
segment and `U` its interior: the pieces are smooth, the bounds of `tail:mode-derivative-bound` hold on the closed
segment). Unlike `JB` the jet is explicit, so that the resulting formulas can be compared with other expressions
of the same derivatives; the calculus mirrors `JB` (sums, products, constant multiples, finite and infinite sums).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

/-- A jet on the open set `U` with `|F|_{2,t} ≤ B t` for `t ∈ S`. -/
structure JE (U S : Set ℝ) (F F₁ F₂ B : ℝ → ℝ) : Prop where
  jet : Jet2 U U F F₁ F₂
  bd : ∀ t ∈ S, jn F F₁ F₂ t ≤ B t

namespace JE

variable {U S : Set ℝ} {F F₁ F₂ G G₁ G₂ B C : ℝ → ℝ}

theorem mono_bound (h : JE U S F F₁ F₂ B) (hBC : ∀ t ∈ S, B t ≤ C t) : JE U S F F₁ F₂ C :=
  ⟨h.jet, fun t ht => (h.bd t ht).trans (hBC t ht)⟩

theorem mono_set {U' S' : Set ℝ} (h : JE U S F F₁ F₂ B) (hU : U' ⊆ U) (hS : S' ⊆ S) :
    JE U' S' F F₁ F₂ B :=
  ⟨h.jet.mono hU hU subset_rfl, fun t ht => h.bd t (hS ht)⟩

theorem const (c : ℝ) : JE U S (fun _ => c) (fun _ => 0) (fun _ => 0) (fun _ => |c|) :=
  ⟨Jet2.const c subset_rfl, fun t _ => by simp [jn]⟩

theorem add (hF : JE U S F F₁ F₂ B) (hG : JE U S G G₁ G₂ C) :
    JE U S (fun x => F x + G x) (fun x => F₁ x + G₁ x) (fun x => F₂ x + G₂ x) (fun t => B t + C t) :=
  ⟨hF.jet.add hG.jet, fun t ht =>
    (jn_add_le F F₁ F₂ G G₁ G₂ t).trans (add_le_add (hF.bd t ht) (hG.bd t ht))⟩

theorem const_mul (c : ℝ) (hF : JE U S F F₁ F₂ B) :
    JE U S (fun x => c * F x) (fun x => c * F₁ x) (fun x => c * F₂ x) (fun t => |c| * B t) :=
  ⟨hF.jet.const_mul c, fun t ht => by
    rw [jn_const_mul]; exact mul_le_mul_of_nonneg_left (hF.bd t ht) (abs_nonneg c)⟩

theorem mul (hF : JE U S F F₁ F₂ B) (hG : JE U S G G₁ G₂ C) :
    JE U S (fun x => F x * G x) (mul₁ F F₁ G G₁) (mul₂ F F₁ F₂ G G₁ G₂) (fun t => B t * C t) :=
  ⟨hF.jet.mul hG.jet, fun t ht =>
    (jn_mul F F₁ F₂ G G₁ G₂ t).trans
      (mul_le_mul (hF.bd t ht) (hG.bd t ht) (jn_nonneg _ _ _ _) ((jn_nonneg _ _ _ _).trans (hF.bd t ht)))⟩

/-- **Termwise differentiation**: `U` open preconnected, `U ⊆ S`, the bounds uniformly dominated by a summable
`u` on `S`; the sum has the termwise-sum jet and its norm is at most the sum of the bounds on `S`. -/
theorem tsum {ι : Type*} (hU : IsOpen U) (hUc : IsPreconnected U) (hUS : U ⊆ S)
    {F F₁ F₂ B : ι → ℝ → ℝ} (h : ∀ i, JE U S (F i) (F₁ i) (F₂ i) (B i)) {u : ι → ℝ} (hu : Summable u)
    (hB : ∀ i, ∀ t ∈ S, B i t ≤ u i) :
    JE U S (fun x => ∑' i, F i x) (fun x => ∑' i, F₁ i x) (fun x => ∑' i, F₂ i x)
      (fun t => ∑' i, B i t) := by
  have hnn : ∀ i, ∀ t ∈ S, 0 ≤ B i t := fun i t ht =>
    (jn_nonneg (F i) (F₁ i) (F₂ i) t).trans ((h i).bd t ht)
  have h0 : ∀ i, ∀ t ∈ U, |F i t| ≤ u i := fun i t ht => by
    have := (h i).bd t (hUS ht); have := hB i t (hUS ht); unfold jn at *
    linarith [abs_nonneg (F₁ i t), abs_nonneg (F₂ i t)]
  have h1 : ∀ i, ∀ t ∈ U, |F₁ i t| ≤ u i := fun i t ht => by
    have := (h i).bd t (hUS ht); have := hB i t (hUS ht); unfold jn at *
    linarith [abs_nonneg (F i t), abs_nonneg (F₂ i t)]
  have h2 : ∀ i, ∀ t ∈ U, |F₂ i t| ≤ 2 * u i := fun i t ht => by
    have := (h i).bd t (hUS ht); have := hB i t (hUS ht); unfold jn at *
    linarith [abs_nonneg (F₁ i t), abs_nonneg (F i t)]
  refine ⟨Jet2.tsum hU hUc hU hUc subset_rfl (fun i => (h i).jet) hu hu (hu.mul_left 2) h0 h1 h2,
    fun t ht => ?_⟩
  exact jn_tsum_le F F₁ F₂ t (Summable.of_nonneg_of_le (fun i => hnn i t ht) (fun i => hB i t ht) hu)
    (fun i => (h i).bd t ht)

end JE

end Tails

end SandierSerfaty

end
