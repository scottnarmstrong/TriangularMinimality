/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Tails.Jet
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Complex.RealDeriv

/-!
# Composition, real parts and complex coercions of bounded jets

Complements `Tails/Jet.lean`:

* `Jet3.comp`, `BJ.comp`: the chain rule for real functions of a real variable with explicit Faà di Bruno
  terms `g₁(w) w₁`, `g₂(w) w₁² + g₁(w) w₂`, `g₃(w) w₁³ + 3 g₂(w) w₁ w₂ + g₁(w) w₃`;
* `BJ.id`, `BJ.one_sub`: the identity and `1 - f`;
* `BJ.ofReal`, `BJ.re`: `ℝ → ℂ` coercion and the real part (`V_m = c_m Re z^{k_m}`, paper §6.2).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

section Real

variable {U : Set ℝ} {g g₁ g₂ g₃ w w₁ w₂ w₃ : ℝ → ℝ}

/-- The chain rule for jets (outer function with a jet on all of `ℝ`). -/
theorem Jet3.comp (hg : Jet3 Set.univ g g₁ g₂ g₃) (hw : Jet3 U w w₁ w₂ w₃) :
    Jet3 U (fun x => g (w x)) (fun x => g₁ (w x) * w₁ x)
      (fun x => (g₂ (w x) * w₁ x) * w₁ x + g₁ (w x) * w₂ x)
      (fun x => (((g₃ (w x) * w₁ x) * w₁ x + g₂ (w x) * w₂ x) * w₁ x + (g₂ (w x) * w₁ x) * w₂ x) +
        ((g₂ (w x) * w₁ x) * w₂ x + g₁ (w x) * w₃ x)) := by
  refine ⟨fun x hx => (hg.d0 (w x) (mem_univ _)).comp x (hw.d0 x hx), fun x hx => ?_,
    fun x hx => ?_⟩
  · exact ((hg.d1 (w x) (mem_univ _)).comp x (hw.d0 x hx)).mul (hw.d1 x hx)
  · have a1 : HasDerivAt (fun x => g₂ (w x) * w₁ x)
        ((g₃ (w x) * w₁ x) * w₁ x + g₂ (w x) * w₂ x) x :=
      ((hg.d2 (w x) (mem_univ _)).comp x (hw.d0 x hx)).mul (hw.d1 x hx)
    exact (a1.mul (hw.d1 x hx)).add
      (((hg.d1 (w x) (mem_univ _)).comp x (hw.d0 x hx)).mul (hw.d2 x hx))

/-- The jet of the identity. -/
theorem Jet3.id (U : Set ℝ) : Jet3 U (fun x : ℝ => x) (fun _ => 1) (fun _ => 0) (fun _ => 0) :=
  ⟨fun x _ => hasDerivAt_id x, fun x _ => hasDerivAt_const x _, fun x _ => hasDerivAt_const x _⟩

variable {s : Set ℝ}

/-- The chain rule for bounded jets: `g` is bounded on `t ∋ w x` and `w` on `s`. -/
theorem BJ.comp {t : Set ℝ} {G₀ G₁ G₂ G₃ W₀ W₁ W₂ W₃ : ℝ}
    (hg : BJ Set.univ t g G₀ G₁ G₂ G₃) (hw : BJ U s w W₀ W₁ W₂ W₃) (hmaps : ∀ x ∈ s, w x ∈ t)
    (hG₁ : 0 ≤ G₁) (hG₂ : 0 ≤ G₂) (hG₃ : 0 ≤ G₃) (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂) :
    BJ U s (fun x => g (w x)) G₀ (G₁ * W₁) ((G₂ * W₁) * W₁ + G₁ * W₂)
      ((((G₃ * W₁) * W₁ + G₂ * W₂) * W₁ + (G₂ * W₁) * W₂) + ((G₂ * W₁) * W₂ + G₁ * W₃)) := by
  obtain ⟨g₁, g₂, g₃, hj, hb⟩ := hg
  obtain ⟨w₁, w₂, w₃, hk, hc⟩ := hw
  refine ⟨_, _, _, hj.comp hk, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb (w x) (hmaps x hx)
  obtain ⟨b0, b1, b2, b3⟩ := hc x hx
  have hGW₁ : 0 ≤ G₁ * W₁ := mul_nonneg hG₁ hW₁
  have hGW₂ : 0 ≤ G₂ * W₁ := mul_nonneg hG₂ hW₁
  have hGW₃ : 0 ≤ (G₂ * W₁) * W₁ := mul_nonneg hGW₂ hW₁
  refine ⟨a0, BJ.nb_mul a1 b1 hG₁, BJ.nb_add (BJ.nb_mul (BJ.nb_mul a2 b1 hG₂) b1 hGW₂)
    (BJ.nb_mul a1 b2 hG₁), BJ.nb_add (BJ.nb_add (BJ.nb_mul (BJ.nb_add (BJ.nb_mul (BJ.nb_mul a3 b1 hG₃) b1
      (mul_nonneg hG₃ hW₁)) (BJ.nb_mul a2 b2 hG₂)) b1 (add_nonneg (mul_nonneg (mul_nonneg hG₃ hW₁) hW₁)
        (mul_nonneg hG₂ hW₂))) (BJ.nb_mul (BJ.nb_mul a2 b1 hG₂) b2 hGW₂))
    (BJ.nb_add (BJ.nb_mul (BJ.nb_mul a2 b1 hG₂) b2 hGW₂) (BJ.nb_mul a1 b3 hG₁))⟩

/-- The identity is bounded on `[-R, R]`. -/
theorem BJ.id (U s : Set ℝ) {R : ℝ} (hs : ∀ x ∈ s, |x| ≤ R) :
    BJ U s (fun x : ℝ => x) R 1 0 0 :=
  ⟨_, _, _, Jet3.id U, fun x hx => ⟨by simpa using hs x hx, by simp, by simp, by simp⟩⟩

/-- `1 - f`, with a separate bound for the value. -/
theorem BJ.one_sub {f : ℝ → ℝ} {M₀ M₁ M₂ M₃ : ℝ} (N₀ : ℝ) (hf : BJ U s f M₀ M₁ M₂ M₃)
    (h : ∀ x ∈ s, |1 - f x| ≤ N₀) : BJ U s (fun x => 1 - f x) N₀ M₁ M₂ M₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  refine ⟨_, _, _, (Jet3.const (1 : ℝ) U).sub hj, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  refine ⟨by simpa using h x hx, ?_, ?_, ?_⟩ <;> simpa using ‹_›

end Real

section Complex

variable {U s : Set ℝ}

/-- The coercion `ℝ → ℂ` of a real jet. -/
theorem Jet3.ofReal {f f₁ f₂ f₃ : ℝ → ℝ} (hf : Jet3 U f f₁ f₂ f₃) :
    Jet3 U (fun x => ((f x : ℝ) : ℂ)) (fun x => ((f₁ x : ℝ) : ℂ)) (fun x => ((f₂ x : ℝ) : ℂ))
      (fun x => ((f₃ x : ℝ) : ℂ)) :=
  ⟨fun x hx => (hf.d0 x hx).ofReal_comp, fun x hx => (hf.d1 x hx).ofReal_comp,
    fun x hx => (hf.d2 x hx).ofReal_comp⟩

theorem BJ.ofReal {f : ℝ → ℝ} {M₀ M₁ M₂ M₃ : ℝ} (hf : BJ U s f M₀ M₁ M₂ M₃) :
    BJ U s (fun x => ((f x : ℝ) : ℂ)) M₀ M₁ M₂ M₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  exact ⟨_, _, _, hj.ofReal, fun x hx => by simpa using hb x hx⟩

/-- The real part of a complex jet. -/
theorem Jet3.re {f f₁ f₂ f₃ : ℝ → ℂ} (hf : Jet3 U f f₁ f₂ f₃) :
    Jet3 U (fun x => (f x).re) (fun x => (f₁ x).re) (fun x => (f₂ x).re) (fun x => (f₃ x).re) := by
  have key : ∀ {a : ℝ → ℂ} {a' : ℂ} {x : ℝ}, HasDerivAt a a' x →
      HasDerivAt (fun y => (a y).re) a'.re x := fun h => Complex.reCLM.hasFDerivAt.comp_hasDerivAt _ h
  exact ⟨fun x hx => key (hf.d0 x hx), fun x hx => key (hf.d1 x hx), fun x hx => key (hf.d2 x hx)⟩

theorem BJ.re {f : ℝ → ℂ} {M₀ M₁ M₂ M₃ : ℝ} (hf : BJ U s f M₀ M₁ M₂ M₃) :
    BJ U s (fun x => (f x).re) M₀ M₁ M₂ M₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  refine ⟨_, _, _, hj.re, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  have h : ∀ z : ℂ, ‖z.re‖ ≤ ‖z‖ := fun z => by
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  exact ⟨(h _).trans a0, (h _).trans a1, (h _).trans a2, (h _).trans a3⟩

end Complex

end Tails

end SandierSerfaty

end
