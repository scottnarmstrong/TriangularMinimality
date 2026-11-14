/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A small calculus of bounded `C²` / `C¹` functions on an open set

`Bd2 U f c₀ c₁ c₂`: `f` is `C²` on `U` with `|f| ≤ c₀`, `|f'| ≤ c₁`, `|f''| ≤ c₂` on `U`; `Bd1 U f c₀ c₁` the
same for `C¹`. Closed under sums, products and scalar multiples with the evident constants; used to produce the
summable majorants of the series for `f₀` (`C²`) and `e` (`C¹`) in `SectorSeries.lean`.
-/

open Set

public section

namespace SandierSerfaty

namespace Calibration

/-- `f` is `C²` on `U` with the stated bounds on `f, f', f''`. -/
@[expose] def Bd2 (U : Set ℝ) (f : ℝ → ℝ) (c₀ c₁ c₂ : ℝ) : Prop :=
  ContDiffOn ℝ 2 f U ∧ ∀ x ∈ U, |f x| ≤ c₀ ∧ |deriv f x| ≤ c₁ ∧ |deriv (deriv f) x| ≤ c₂

/-- `f` is `C¹` on `U` with the stated bounds on `f, f'`. -/
@[expose] def Bd1 (U : Set ℝ) (f : ℝ → ℝ) (c₀ c₁ : ℝ) : Prop :=
  ContDiffOn ℝ 1 f U ∧ ∀ x ∈ U, |f x| ≤ c₀ ∧ |deriv f x| ≤ c₁

variable {U : Set ℝ} {f g : ℝ → ℝ}

theorem diffAt_of_contDiffOn {n : WithTop ℕ∞} (hU : IsOpen U)
    (h : ContDiffOn ℝ n f U) (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ U) : DifferentiableAt ℝ f x :=
  ((h.differentiableOn (by rintro rfl; simp at hn)) x hx).differentiableAt (hU.mem_nhds hx)

theorem Bd2.mono {c₀ c₁ c₂ d₀ d₁ d₂ : ℝ} (h : Bd2 U f c₀ c₁ c₂) (h₀ : c₀ ≤ d₀) (h₁ : c₁ ≤ d₁)
    (h₂ : c₂ ≤ d₂) : Bd2 U f d₀ d₁ d₂ :=
  ⟨h.1, fun x hx => ⟨(h.2 x hx).1.trans h₀, (h.2 x hx).2.1.trans h₁, (h.2 x hx).2.2.trans h₂⟩⟩

theorem Bd1.mono {c₀ c₁ d₀ d₁ : ℝ} (h : Bd1 U f c₀ c₁) (h₀ : c₀ ≤ d₀) (h₁ : c₁ ≤ d₁) :
    Bd1 U f d₀ d₁ :=
  ⟨h.1, fun x hx => ⟨(h.2 x hx).1.trans h₀, (h.2 x hx).2.trans h₁⟩⟩

theorem Bd2.to_Bd1 {c₀ c₁ c₂ : ℝ} (h : Bd2 U f c₀ c₁ c₂) : Bd1 U f c₀ c₁ :=
  ⟨h.1.of_le (by norm_num), fun x hx => ⟨(h.2 x hx).1, (h.2 x hx).2.1⟩⟩

/-- The derivative of a `Bd2` function is `Bd1`. -/
theorem Bd2.derivBd (hU : IsOpen U) {c₀ c₁ c₂ : ℝ} (h : Bd2 U f c₀ c₁ c₂) : Bd1 U (deriv f) c₁ c₂ :=
  ⟨ContDiffOn.deriv_of_isOpen h.1 hU (m := 1) (by norm_num), fun x hx => ⟨(h.2 x hx).2.1, (h.2 x hx).2.2⟩⟩

theorem Bd2.congr (hU : IsOpen U) {c₀ c₁ c₂ : ℝ} (h : Bd2 U f c₀ c₁ c₂) (e : EqOn f g U) :
    Bd2 U g c₀ c₁ c₂ := by
  refine ⟨h.1.congr fun x hx => (e hx).symm, fun x hx => ?_⟩
  have ev : f =ᶠ[nhds x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) e
  have ev1 : deriv f =ᶠ[nhds x] deriv g := ev.deriv
  have ev2 : deriv (deriv f) =ᶠ[nhds x] deriv (deriv g) := ev1.deriv
  rw [← e hx, ← ev.deriv_eq, ← ev1.deriv_eq]
  exact h.2 x hx

theorem Bd1.congr (hU : IsOpen U) {c₀ c₁ : ℝ} (h : Bd1 U f c₀ c₁) (e : EqOn f g U) :
    Bd1 U g c₀ c₁ := by
  refine ⟨h.1.congr fun x hx => (e hx).symm, fun x hx => ?_⟩
  have ev : f =ᶠ[nhds x] g := Filter.eventuallyEq_of_mem (hU.mem_nhds hx) e
  rw [← e hx, ← ev.deriv_eq]
  exact h.2 x hx

/-- The identity function, on a set where `|x| ≤ T`. -/
theorem Bd2.id {T : ℝ} (hT : ∀ x ∈ U, |x| ≤ T) : Bd2 U (fun x => x) T 1 0 :=
  ⟨contDiffOn_id, fun x hx => ⟨hT x hx, by simp, by simp⟩⟩

theorem Bd1.id {T : ℝ} (hT : ∀ x ∈ U, |x| ≤ T) : Bd1 U (fun x => x) T 1 :=
  ⟨contDiffOn_id, fun x hx => ⟨hT x hx, by simp⟩⟩

theorem Bd2.const_mul (c : ℝ) {c₀ c₁ c₂ : ℝ} (h : Bd2 U f c₀ c₁ c₂) :
    Bd2 U (fun x => c * f x) (|c| * c₀) (|c| * c₁) (|c| * c₂) := by
  refine ⟨ContDiffOn.mul contDiffOn_const h.1, fun x hx => ?_⟩
  obtain ⟨b0, b1, b2⟩ := h.2 x hx
  have e1 : deriv (fun x => c * f x) = fun x => c * deriv f x := deriv_const_mul_field' c
  have e2 : deriv (fun x => c * deriv f x) = fun x => c * deriv (deriv f) x :=
    deriv_const_mul_field' c
  rw [e1, e2]
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b0 (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b1 (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b2 (abs_nonneg _)

theorem Bd1.const_mul (c : ℝ) {c₀ c₁ : ℝ} (h : Bd1 U f c₀ c₁) :
    Bd1 U (fun x => c * f x) (|c| * c₀) (|c| * c₁) := by
  refine ⟨ContDiffOn.mul contDiffOn_const h.1, fun x hx => ?_⟩
  obtain ⟨b0, b1⟩ := h.2 x hx
  have e1 : deriv (fun x => c * f x) = fun x => c * deriv f x := deriv_const_mul_field' c
  rw [e1]
  refine ⟨?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b0 (abs_nonneg _)
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_left b1 (abs_nonneg _)

theorem Bd2.add (hU : IsOpen U) {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (hf : Bd2 U f a₀ a₁ a₂)
    (hg : Bd2 U g b₀ b₁ b₂) :
    Bd2 U (fun x => f x + g x) (a₀ + b₀) (a₁ + b₁) (a₂ + b₂) := by
  refine ⟨ContDiffOn.add hf.1 hg.1, fun x hx => ?_⟩
  have df := diffAt_of_contDiffOn hU hf.1 (by norm_num) hx
  have dg := diffAt_of_contDiffOn hU hg.1 (by norm_num) hx
  have df' := diffAt_of_contDiffOn hU (hf.derivBd hU).1 le_rfl hx
  have dg' := diffAt_of_contDiffOn hU (hg.derivBd hU).1 le_rfl hx
  have e1 : deriv (fun x => f x + g x) =ᶠ[nhds x] fun x => deriv f x + deriv g x := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact deriv_fun_add (diffAt_of_contDiffOn hU hf.1 (by norm_num) hy)
      (diffAt_of_contDiffOn hU hg.1 (by norm_num) hy)
  obtain ⟨a0, a1, a2⟩ := hf.2 x hx
  obtain ⟨b0, b1, b2⟩ := hg.2 x hx
  refine ⟨(abs_add_le _ _).trans (add_le_add a0 b0), ?_, ?_⟩
  · rw [deriv_fun_add df dg]; exact (abs_add_le _ _).trans (add_le_add a1 b1)
  · rw [e1.deriv_eq, deriv_fun_add df' dg']; exact (abs_add_le _ _).trans (add_le_add a2 b2)

theorem Bd1.add (hU : IsOpen U) {a₀ a₁ b₀ b₁ : ℝ} (hf : Bd1 U f a₀ a₁) (hg : Bd1 U g b₀ b₁) :
    Bd1 U (fun x => f x + g x) (a₀ + b₀) (a₁ + b₁) := by
  refine ⟨ContDiffOn.add hf.1 hg.1, fun x hx => ?_⟩
  have df := diffAt_of_contDiffOn hU hf.1 le_rfl hx
  have dg := diffAt_of_contDiffOn hU hg.1 le_rfl hx
  obtain ⟨a0, a1⟩ := hf.2 x hx
  obtain ⟨b0, b1⟩ := hg.2 x hx
  refine ⟨(abs_add_le _ _).trans (add_le_add a0 b0), ?_⟩
  rw [deriv_fun_add df dg]; exact (abs_add_le _ _).trans (add_le_add a1 b1)

theorem Bd1.mul (hU : IsOpen U) {a₀ a₁ b₀ b₁ : ℝ} (hf : Bd1 U f a₀ a₁) (hg : Bd1 U g b₀ b₁) :
    Bd1 U (fun x => f x * g x) (a₀ * b₀) (a₁ * b₀ + a₀ * b₁) := by
  refine ⟨ContDiffOn.mul hf.1 hg.1, fun x hx => ?_⟩
  have df := diffAt_of_contDiffOn hU hf.1 le_rfl hx
  have dg := diffAt_of_contDiffOn hU hg.1 le_rfl hx
  obtain ⟨a0, a1⟩ := hf.2 x hx
  obtain ⟨b0, b1⟩ := hg.2 x hx
  have z0 := (abs_nonneg (f x)).trans a0
  have z1 := (abs_nonneg (g x)).trans b0
  refine ⟨?_, ?_⟩
  · rw [abs_mul]; exact mul_le_mul a0 b0 (abs_nonneg _) z0
  · rw [deriv_fun_mul df dg]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul a1 b0 (abs_nonneg _) ((abs_nonneg _).trans a1)
    · rw [abs_mul]; exact mul_le_mul a0 b1 (abs_nonneg _) z0

theorem Bd2.mul (hU : IsOpen U) {a₀ a₁ a₂ b₀ b₁ b₂ : ℝ} (hf : Bd2 U f a₀ a₁ a₂)
    (hg : Bd2 U g b₀ b₁ b₂) :
    Bd2 U (fun x => f x * g x) (a₀ * b₀) (a₁ * b₀ + a₀ * b₁) (a₂ * b₀ + 2 * (a₁ * b₁) + a₀ * b₂) := by
  refine ⟨ContDiffOn.mul hf.1 hg.1, fun x hx => ?_⟩
  have d1 := (hf.to_Bd1.mul hU hg.to_Bd1).2 x hx
  have hf' := hf.derivBd hU
  have hg' := hg.derivBd hU
  have df := diffAt_of_contDiffOn hU hf.1 (by norm_num) hx
  have dg := diffAt_of_contDiffOn hU hg.1 (by norm_num) hx
  have df' := diffAt_of_contDiffOn hU hf'.1 le_rfl hx
  have dg' := diffAt_of_contDiffOn hU hg'.1 le_rfl hx
  have e1 : deriv (fun x => f x * g x) =ᶠ[nhds x] fun x => deriv f x * g x + f x * deriv g x := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact deriv_fun_mul (diffAt_of_contDiffOn hU hf.1 (by norm_num) hy)
      (diffAt_of_contDiffOn hU hg.1 (by norm_num) hy)
  obtain ⟨a0, a1, a2⟩ := hf.2 x hx
  obtain ⟨b0, b1, b2⟩ := hg.2 x hx
  have z0 := (abs_nonneg (f x)).trans a0
  have z1 := (abs_nonneg (g x)).trans b0
  have z2 := (abs_nonneg (deriv f x)).trans a1
  have z3 := (abs_nonneg (deriv g x)).trans b1
  refine ⟨d1.1, d1.2, ?_⟩
  rw [e1.deriv_eq, deriv_fun_add (df'.fun_mul dg) (df.fun_mul dg'), deriv_fun_mul df' dg, deriv_fun_mul df dg']
  have t1 : |deriv (deriv f) x * g x| ≤ a₂ * b₀ := by
    rw [abs_mul]; exact mul_le_mul a2 b0 (abs_nonneg _) ((abs_nonneg _).trans a2)
  have t2 : |deriv f x * deriv g x| ≤ a₁ * b₁ := by
    rw [abs_mul]; exact mul_le_mul a1 b1 (abs_nonneg _) z2
  have t3 : |f x * deriv (deriv g) x| ≤ a₀ * b₂ := by
    rw [abs_mul]; exact mul_le_mul a0 b2 (abs_nonneg _) z0
  calc |deriv (deriv f) x * g x + deriv f x * deriv g x + (deriv f x * deriv g x +
        f x * deriv (deriv g) x)|
      ≤ |deriv (deriv f) x * g x| + |deriv f x * deriv g x| + (|deriv f x * deriv g x| +
        |f x * deriv (deriv g) x|) := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ a₂ * b₀ + a₁ * b₁ + (a₁ * b₁ + a₀ * b₂) := by gcongr
    _ = a₂ * b₀ + 2 * (a₁ * b₁) + a₀ * b₂ := by ring

end Calibration

end SandierSerfaty

end
