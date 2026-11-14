/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Algebra.Basic

/-!
# Third-order jets with norm bounds

A small calculus for the derivative bounds of paper `tail:radial-derivatives`:

* `Jet3 U f f₁ f₂ f₃`: `f' = f₁`, `f₁' = f₂`, `f₂' = f₃` at every point of `U` (the derivative functions are
  explicit, so the product rule produces explicit Leibniz expressions; Mathlib v4.35 has no `iteratedDeriv_mul`);
* `BJ U s f M₀ M₁ M₂ M₃`: `f` has a `Jet3` on `U` whose four functions are bounded in norm by `M₀, …, M₃` on `s`.

`BJ` is closed under sums, products (the Leibniz constants `1, 1+1, 1+2+1, 1+3+3+1`), constant multiples,
powers `f^{e+3}` (chain rule) and changes of the function on the open set `U`. For a `BJ` the iterated
derivatives of orders `1, 2, 3` at points of an open `U` are the jet functions (`BJ.iteratedDeriv_le`).

The scalar type `𝔸` is `ℝ` or `ℂ` (a commutative normed algebra over `ℝ`): `ℂ` is used for the binomial
form `V_m = c_m Re (p + i √(r² - p²))^{k_m}` of paper §6.2.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Tails

variable {𝔸 : Type*} [NormedCommRing 𝔸] [NormedAlgebra ℝ 𝔸]

/-- `f' = f₁`, `f₁' = f₂`, `f₂' = f₃` at every point of `U`. -/
structure Jet3 (U : Set ℝ) (f f₁ f₂ f₃ : ℝ → 𝔸) : Prop where
  d0 : ∀ x ∈ U, HasDerivAt f (f₁ x) x
  d1 : ∀ x ∈ U, HasDerivAt f₁ (f₂ x) x
  d2 : ∀ x ∈ U, HasDerivAt f₂ (f₃ x) x

/-- `f` has a jet on `U` bounded in norm by `M₀, M₁, M₂, M₃` on `s`. -/
@[expose] def BJ (U s : Set ℝ) (f : ℝ → 𝔸) (M₀ M₁ M₂ M₃ : ℝ) : Prop :=
  ∃ f₁ f₂ f₃ : ℝ → 𝔸, Jet3 U f f₁ f₂ f₃ ∧
    ∀ x ∈ s, ‖f x‖ ≤ M₀ ∧ ‖f₁ x‖ ≤ M₁ ∧ ‖f₂ x‖ ≤ M₂ ∧ ‖f₃ x‖ ≤ M₃

namespace Jet3

variable {U : Set ℝ} {f f₁ f₂ f₃ g g₁ g₂ g₃ : ℝ → 𝔸}

theorem const (c : 𝔸) (U : Set ℝ) : Jet3 U (fun _ => c) (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  ⟨fun x _ => hasDerivAt_const x c, fun x _ => hasDerivAt_const x _, fun x _ => hasDerivAt_const x _⟩

theorem add (hf : Jet3 U f f₁ f₂ f₃) (hg : Jet3 U g g₁ g₂ g₃) :
    Jet3 U (fun x => f x + g x) (fun x => f₁ x + g₁ x) (fun x => f₂ x + g₂ x)
      (fun x => f₃ x + g₃ x) :=
  ⟨fun x hx => (hf.d0 x hx).add (hg.d0 x hx), fun x hx => (hf.d1 x hx).add (hg.d1 x hx),
    fun x hx => (hf.d2 x hx).add (hg.d2 x hx)⟩

theorem sub (hf : Jet3 U f f₁ f₂ f₃) (hg : Jet3 U g g₁ g₂ g₃) :
    Jet3 U (fun x => f x - g x) (fun x => f₁ x - g₁ x) (fun x => f₂ x - g₂ x)
      (fun x => f₃ x - g₃ x) :=
  ⟨fun x hx => (hf.d0 x hx).sub (hg.d0 x hx), fun x hx => (hf.d1 x hx).sub (hg.d1 x hx),
    fun x hx => (hf.d2 x hx).sub (hg.d2 x hx)⟩

theorem const_mul (c : 𝔸) (hf : Jet3 U f f₁ f₂ f₃) :
    Jet3 U (fun x => c * f x) (fun x => c * f₁ x) (fun x => c * f₂ x) (fun x => c * f₃ x) :=
  ⟨fun x hx => (hf.d0 x hx).const_mul c, fun x hx => (hf.d1 x hx).const_mul c,
    fun x hx => (hf.d2 x hx).const_mul c⟩

theorem mul (hf : Jet3 U f f₁ f₂ f₃) (hg : Jet3 U g g₁ g₂ g₃) :
    Jet3 U (fun x => f x * g x) (fun x => f₁ x * g x + f x * g₁ x)
      (fun x => (f₂ x * g x + f₁ x * g₁ x) + (f₁ x * g₁ x + f x * g₂ x))
      (fun x => ((f₃ x * g x + f₂ x * g₁ x) + (f₂ x * g₁ x + f₁ x * g₂ x)) +
        ((f₂ x * g₁ x + f₁ x * g₂ x) + (f₁ x * g₂ x + f x * g₃ x))) := by
  refine ⟨fun x hx => (hf.d0 x hx).mul (hg.d0 x hx), fun x hx => ?_, fun x hx => ?_⟩
  · exact ((hf.d1 x hx).mul (hg.d0 x hx)).add ((hf.d0 x hx).mul (hg.d1 x hx))
  · exact (((hf.d2 x hx).mul (hg.d0 x hx)).add ((hf.d1 x hx).mul (hg.d1 x hx))).add
      (((hf.d1 x hx).mul (hg.d1 x hx)).add ((hf.d0 x hx).mul (hg.d2 x hx)))

/-- Changing the function on an open set `U` does not change the jet functions on `U`. -/
theorem congr (hU : IsOpen U) (hf : Jet3 U f f₁ f₂ f₃) (h : EqOn f g U) : Jet3 U g f₁ f₂ f₃ :=
  ⟨fun x hx => (hf.d0 x hx).congr_of_eventuallyEq
      ((h.eventuallyEq_of_mem (hU.mem_nhds hx)).symm), hf.d1, hf.d2⟩

theorem mono {V : Set ℝ} (hf : Jet3 U f f₁ f₂ f₃) (h : V ⊆ U) : Jet3 V f f₁ f₂ f₃ :=
  ⟨fun x hx => hf.d0 x (h hx), fun x hx => hf.d1 x (h hx), fun x hx => hf.d2 x (h hx)⟩

/-- On an open set the iterated derivatives of orders `1, 2, 3` are the jet functions. -/
theorem iteratedDeriv_eq (hU : IsOpen U) (hf : Jet3 U f f₁ f₂ f₃) {x : ℝ} (hx : x ∈ U) :
    iteratedDeriv 1 f x = f₁ x ∧ iteratedDeriv 2 f x = f₂ x ∧ iteratedDeriv 3 f x = f₃ x := by
  have e1 : deriv f =ᶠ[nhds x] f₁ := by
    filter_upwards [hU.mem_nhds hx] with y hy using (hf.d0 y hy).deriv
  have e2 : deriv f₁ =ᶠ[nhds x] f₂ := by
    filter_upwards [hU.mem_nhds hx] with y hy using (hf.d1 y hy).deriv
  have h2 : deriv (deriv f) =ᶠ[nhds x] f₂ := by
    filter_upwards [hU.mem_nhds hx, e1.eventuallyEq_nhds] with y hy hy1
    rw [hy1.deriv_eq]; exact (hf.d1 y hy).deriv
  refine ⟨?_, ?_, ?_⟩
  · rw [iteratedDeriv_one]; exact e1.eq_of_nhds
  · rw [iteratedDeriv_succ, iteratedDeriv_one]; exact h2.eq_of_nhds
  · rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one,
      h2.deriv_eq]
    exact (hf.d2 x hx).deriv

theorem hasDerivAt_pow_succ' {c : ℝ → 𝔸} {c' : 𝔸} {x : ℝ} (h : HasDerivAt c c' x) (n : ℕ) :
    HasDerivAt (fun y => c y ^ (n + 1)) (((n + 1 : ℕ) : 𝔸) * c x ^ n * c') x := by
  simpa using h.fun_pow (n + 1)

/-- The jet of `f^{e+3}` (chain rule; the exponent is written `e + 3` to avoid natural subtraction). -/
theorem pow3 (e : ℕ) (hf : Jet3 U f f₁ f₂ f₃) :
    Jet3 U (fun x => f x ^ (e + 3))
      (fun x => ((e + 3 : ℕ) : 𝔸) * f x ^ (e + 2) * f₁ x)
      (fun x => ((e + 3 : ℕ) : 𝔸) *
        (((e + 2 : ℕ) : 𝔸) * f x ^ (e + 1) * f₁ x * f₁ x + f x ^ (e + 2) * f₂ x))
      (fun x => ((e + 3 : ℕ) : 𝔸) *
        (((e + 2 : ℕ) : 𝔸) * ((e + 1 : ℕ) : 𝔸) * f x ^ e * f₁ x * f₁ x * f₁ x +
          3 * ((e + 2 : ℕ) : 𝔸) * f x ^ (e + 1) * f₁ x * f₂ x + f x ^ (e + 2) * f₃ x)) := by
  refine ⟨fun x hx => hasDerivAt_pow_succ' (hf.d0 x hx) (e + 2), fun x hx => ?_, fun x hx => ?_⟩
  · have h1 := (hasDerivAt_pow_succ' (hf.d0 x hx) (e + 1)).mul (hf.d1 x hx)
    have h2 := h1.const_mul ((e + 3 : ℕ) : 𝔸)
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · push_cast; ring
    · simp only [Pi.mul_apply]; ring
  · have h1 := (hasDerivAt_pow_succ' (hf.d0 x hx) e).mul (hf.d1 x hx)
    have h1' := (h1.const_mul ((e + 2 : ℕ) : 𝔸)).mul (hf.d1 x hx)
    have h2 := (hasDerivAt_pow_succ' (hf.d0 x hx) (e + 1)).mul (hf.d2 x hx)
    have h3 := ((h1'.add h2).const_mul ((e + 3 : ℕ) : 𝔸))
    refine (h3.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · simp only [Pi.mul_apply]; push_cast; ring
    · simp only [Pi.mul_apply, Pi.add_apply]; ring

end Jet3

namespace BJ

variable {U s : Set ℝ} {f g : ℝ → 𝔸} {M₀ M₁ M₂ M₃ N₀ N₁ N₂ N₃ : ℝ}

theorem mono (hf : BJ U s f M₀ M₁ M₂ M₃) (h0 : M₀ ≤ N₀) (h1 : M₁ ≤ N₁) (h2 : M₂ ≤ N₂) (h3 : M₃ ≤ N₃) :
    BJ U s f N₀ N₁ N₂ N₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  exact ⟨f₁, f₂, f₃, hj, fun x hx => by
    obtain ⟨a, b, c, d⟩ := hb x hx
    exact ⟨a.trans h0, b.trans h1, c.trans h2, d.trans h3⟩⟩

theorem mono_set {s' : Set ℝ} (hf : BJ U s f M₀ M₁ M₂ M₃) (h : s' ⊆ s) : BJ U s' f M₀ M₁ M₂ M₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  exact ⟨f₁, f₂, f₃, hj, fun x hx => hb x (h hx)⟩

/-- Restricting the open domain of the jet. -/
theorem restrict {U' : Set ℝ} (h : U' ⊆ U) (hf : BJ U s f M₀ M₁ M₂ M₃) : BJ U' s f M₀ M₁ M₂ M₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  exact ⟨f₁, f₂, f₃, hj.mono h, hb⟩

theorem congr (hU : IsOpen U) (hsU : s ⊆ U) (hf : BJ U s f M₀ M₁ M₂ M₃) (h : EqOn f g U) :
    BJ U s g M₀ M₁ M₂ M₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  refine ⟨f₁, f₂, f₃, hj.congr hU h, fun x hx => ?_⟩
  rw [← h (hsU hx)]; exact hb x hx

theorem const (c : 𝔸) (U s : Set ℝ) : BJ U s (fun _ => c) ‖c‖ 0 0 0 :=
  ⟨_, _, _, Jet3.const c U, fun _ _ => ⟨le_rfl, by simp, by simp, by simp⟩⟩

theorem add (hf : BJ U s f M₀ M₁ M₂ M₃) (hg : BJ U s g N₀ N₁ N₂ N₃) :
    BJ U s (fun x => f x + g x) (M₀ + N₀) (M₁ + N₁) (M₂ + N₂) (M₃ + N₃) := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  obtain ⟨g₁, g₂, g₃, hk, hc⟩ := hg
  refine ⟨_, _, _, hj.add hk, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  obtain ⟨b0, b1, b2, b3⟩ := hc x hx
  exact ⟨(norm_add_le _ _).trans (add_le_add a0 b0), (norm_add_le _ _).trans (add_le_add a1 b1),
    (norm_add_le _ _).trans (add_le_add a2 b2), (norm_add_le _ _).trans (add_le_add a3 b3)⟩

theorem sub (hf : BJ U s f M₀ M₁ M₂ M₃) (hg : BJ U s g N₀ N₁ N₂ N₃) :
    BJ U s (fun x => f x - g x) (M₀ + N₀) (M₁ + N₁) (M₂ + N₂) (M₃ + N₃) := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  obtain ⟨g₁, g₂, g₃, hk, hc⟩ := hg
  refine ⟨_, _, _, hj.sub hk, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  obtain ⟨b0, b1, b2, b3⟩ := hc x hx
  exact ⟨(norm_sub_le _ _).trans (add_le_add a0 b0), (norm_sub_le _ _).trans (add_le_add a1 b1),
    (norm_sub_le _ _).trans (add_le_add a2 b2), (norm_sub_le _ _).trans (add_le_add a3 b3)⟩

theorem const_mul (c : 𝔸) (hf : BJ U s f M₀ M₁ M₂ M₃) :
    BJ U s (fun x => c * f x) (‖c‖ * M₀) (‖c‖ * M₁) (‖c‖ * M₂) (‖c‖ * M₃) := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  refine ⟨_, _, _, hj.const_mul c, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  have hc := norm_nonneg c
  exact ⟨(norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left a0 hc),
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left a1 hc),
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left a2 hc),
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left a3 hc)⟩

omit [NormedAlgebra ℝ 𝔸] in
theorem nb_mul {a b : 𝔸} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hA : 0 ≤ A) : ‖a * b‖ ≤ A * B :=
  (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) hA)

omit [NormedAlgebra ℝ 𝔸] in
theorem nb_add {a b : 𝔸} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a + b‖ ≤ A + B :=
  (norm_add_le _ _).trans (add_le_add ha hb)

/-- The Leibniz rule for the bounds (`1, 1+1, 1+2+1, 1+3+3+1`). -/
theorem mul {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : ℝ} (hf : BJ U s f A₀ A₁ A₂ A₃) (hg : BJ U s g B₀ B₁ B₂ B₃)
    (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hA₃ : 0 ≤ A₃) :
    BJ U s (fun x => f x * g x) (A₀ * B₀) (A₁ * B₀ + A₀ * B₁)
      ((A₂ * B₀ + A₁ * B₁) + (A₁ * B₁ + A₀ * B₂))
      (((A₃ * B₀ + A₂ * B₁) + (A₂ * B₁ + A₁ * B₂)) + ((A₂ * B₁ + A₁ * B₂) + (A₁ * B₂ + A₀ * B₃))) := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  obtain ⟨g₁, g₂, g₃, hk, hc⟩ := hg
  refine ⟨_, _, _, hj.mul hk, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  obtain ⟨b0, b1, b2, b3⟩ := hc x hx
  refine ⟨nb_mul a0 b0 hA₀, nb_add (nb_mul a1 b0 hA₁) (nb_mul a0 b1 hA₀),
    nb_add (nb_add (nb_mul a2 b0 hA₂) (nb_mul a1 b1 hA₁)) (nb_add (nb_mul a1 b1 hA₁) (nb_mul a0 b2 hA₀)),
    nb_add (nb_add (nb_add (nb_mul a3 b0 hA₃) (nb_mul a2 b1 hA₂)) (nb_add (nb_mul a2 b1 hA₂) (nb_mul a1 b2 hA₁)))
      (nb_add (nb_add (nb_mul a2 b1 hA₂) (nb_mul a1 b2 hA₁)) (nb_add (nb_mul a1 b2 hA₁) (nb_mul a0 b3 hA₀)))⟩

omit [NormedAlgebra ℝ 𝔸] in
theorem nb_pow [NormOneClass 𝔸] {a : 𝔸} {R : ℝ} (ha : ‖a‖ ≤ R) (n : ℕ) : ‖a ^ n‖ ≤ R ^ n :=
  (norm_pow_le a n).trans (pow_le_pow_left₀ (norm_nonneg _) ha n)

omit [NormedAlgebra ℝ 𝔸] in
theorem norm_natCast_le' [NormOneClass 𝔸] [NormSMulClass ℤ 𝔸] (n : ℕ) : ‖(n : 𝔸)‖ ≤ n :=
  (_root_.norm_natCast n).le

/-- The chain rule bounds for `f^{e+3}` (`‖f‖ ≤ R`). -/
theorem pow3 [NormOneClass 𝔸] [NormSMulClass ℤ 𝔸] (e : ℕ) {R A₁ A₂ A₃ : ℝ} (hf : BJ U s f R A₁ A₂ A₃) (hR : 0 ≤ R)
    (hA₁ : 0 ≤ A₁) :
    BJ U s (fun x => f x ^ (e + 3)) (R ^ (e + 3)) (((e + 3 : ℕ) : ℝ) * R ^ (e + 2) * A₁)
      (((e + 3 : ℕ) : ℝ) * (((e + 2 : ℕ) : ℝ) * R ^ (e + 1) * A₁ * A₁ + R ^ (e + 2) * A₂))
      (((e + 3 : ℕ) : ℝ) * (((e + 2 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ) * R ^ e * A₁ * A₁ * A₁ +
        3 * ((e + 2 : ℕ) : ℝ) * R ^ (e + 1) * A₁ * A₂ + R ^ (e + 2) * A₃)) := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  refine ⟨_, _, _, hj.pow3 e, fun x hx => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  have hRp : ∀ n : ℕ, 0 ≤ R ^ n := fun n => pow_nonneg hR n
  have c3 := norm_natCast_le' (𝔸 := 𝔸) (e + 3)
  have c2 := norm_natCast_le' (𝔸 := 𝔸) (e + 2)
  have c1 := norm_natCast_le' (𝔸 := 𝔸) (e + 1)
  have c3' : ‖(3 : 𝔸)‖ ≤ 3 := by simpa using norm_natCast_le' (𝔸 := 𝔸) 3
  have n3 : (0 : ℝ) ≤ ((e + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have n2 : (0 : ℝ) ≤ ((e + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have n1 : (0 : ℝ) ≤ ((e + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have p0 := nb_pow a0 (e + 3)
  have p1 := nb_pow a0 (e + 2)
  have p2 := nb_pow a0 (e + 1)
  have p3 := nb_pow a0 e
  have m3 : (0 : ℝ) ≤ ((e + 3 : ℕ) : ℝ) * R ^ (e + 2) := mul_nonneg n3 (hRp _)
  have m2 : (0 : ℝ) ≤ ((e + 2 : ℕ) : ℝ) * R ^ (e + 1) := mul_nonneg n2 (hRp _)
  have m21 : (0 : ℝ) ≤ ((e + 2 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ) := mul_nonneg n2 n1
  have m21' : (0 : ℝ) ≤ ((e + 2 : ℕ) : ℝ) * ((e + 1 : ℕ) : ℝ) * R ^ e := mul_nonneg m21 (hRp _)
  have m3' : (0 : ℝ) ≤ 3 * ((e + 2 : ℕ) : ℝ) := by positivity
  refine ⟨p0, nb_mul (nb_mul c3 p1 n3) a1 m3, ?_, ?_⟩
  · refine nb_mul c3 (nb_add ?_ (nb_mul p1 a2 (hRp _))) n3
    exact nb_mul (nb_mul (nb_mul c2 p2 n2) a1 m2) a1 (mul_nonneg m2 hA₁)
  · refine nb_mul c3 (nb_add (nb_add ?_ ?_) (nb_mul p1 a3 (hRp _))) n3
    · exact nb_mul (nb_mul (nb_mul (nb_mul (nb_mul c2 c1 n2) p3 m21) a1 m21') a1 (mul_nonneg m21' hA₁)) a1
        (mul_nonneg (mul_nonneg m21' hA₁) hA₁)
    · exact nb_mul (nb_mul (nb_mul (nb_mul c3' c2 (by norm_num)) p2 m3') a1 (mul_nonneg m3' (hRp _))) a2
        (mul_nonneg (mul_nonneg m3' (hRp _)) hA₁)

/-- On an open set the iterated derivatives of orders `0, …, 3` of a `BJ` function are bounded. -/
theorem iteratedDeriv_le {f : ℝ → ℝ} (hU : IsOpen U) (hsU : s ⊆ U) (hf : BJ U s f M₀ M₁ M₂ M₃)
    {x : ℝ} (hx : x ∈ s) :
    |f x| ≤ M₀ ∧ |iteratedDeriv 1 f x| ≤ M₁ ∧ |iteratedDeriv 2 f x| ≤ M₂ ∧
      |iteratedDeriv 3 f x| ≤ M₃ := by
  obtain ⟨f₁, f₂, f₃, hj, hb⟩ := hf
  obtain ⟨e1, e2, e3⟩ := hj.iteratedDeriv_eq hU (hsU hx)
  obtain ⟨a0, a1, a2, a3⟩ := hb x hx
  simp only [Real.norm_eq_abs] at a0 a1 a2 a3
  rw [e1, e2, e3]
  exact ⟨a0, a1, a2, a3⟩

end BJ

end Tails

end SandierSerfaty

end
