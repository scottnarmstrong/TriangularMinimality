/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectPotential
public import SandierSerfaty.Sphere.Lower.ReflectDomain
public import SandierSerfaty.Torus.PotentialLocal

/-!
# Reflection invariance of the reflected configuration (sphere note, Lemma 6.2(i), (iii) setup)

For the reflected configuration `reflectPts b Z` on `squareLattice (4 n̄)`:

* `Lower.reflXSymm`, `Lower.reflYSymm`: the reflections `reflX b.re`, `reflY b.im` as `ReflSymm`s;
* `Lower.torusPotential_reflX`, `Lower.torusPotential_reflY` (Lemma 6.2(i)): the torus potential is
  invariant under them;
* the gradient norm is invariant too (`Lower.norm_gradient_refl`), and so is the union of the
  periodic `η`-balls around the charges (`Lower.ballUnion`);
* the periodic integrand `1_{(⋃ balls)ᶜ} |∇h|²` (`Lower.energyDensity`) is `Γ`-periodic, measurable,
  nonnegative and invariant under both reflections.
-/

open MeasureTheory Filter Topology

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

open Torus

section Symm

variable {nb : ℕ} (b : ℂ) (Z : Fin nb → ℂ)

/-- The reflection `reflX b.re` as a symmetry of the reflected configuration. -/
@[expose] noncomputable def reflXSymm : ReflSymm (squareLattice (4 * nb)) (reflectPts b Z) where
  R := reflX b.re
  L := flipRe
  c := ⟨2 * b.re, 0⟩
  R_eq := reflX_eq b.re
  invol := reflX_reflX b.re
  lat := fun _ h => flipRe_mem_squareLattice h
  charge := exists_reflX_reflectPts b Z

/-- The reflection `reflY b.im` as a symmetry of the reflected configuration. -/
@[expose] noncomputable def reflYSymm : ReflSymm (squareLattice (4 * nb)) (reflectPts b Z) where
  R := reflY b.im
  L := flipIm
  c := ⟨0, 2 * b.im⟩
  R_eq := reflY_eq b.im
  invol := reflY_reflY b.im
  lat := fun _ h => flipIm_mem_squareLattice h
  charge := exists_reflY_reflectPts b Z

end Symm

section Invariance

variable {nb : ℕ} (hnb : 1 ≤ nb) (b : ℂ) (Z : Fin nb → ℂ) (hZi : Function.Injective Z)
  (hZ : ∀ i, 0 < (Z i - b).re ∧ (Z i - b).re < √nb ∧ 0 < (Z i - b).im ∧ (Z i - b).im < √nb)

include hnb hZi hZ

theorem torusPotential_reflX (x : ℂ) :
    torusPotential (squareLattice (4 * nb)) (reflectPts b Z) (reflX b.re x) =
      torusPotential (squareLattice (4 * nb)) (reflectPts b Z) x := by
  have : NeZero (4 * nb) := ⟨by omega⟩
  exact congrFun ((reflXSymm b Z).torusPotential_comp (covolume_squareLattice (4 * nb))
    (reflectPts_distinct hnb b Z hZi hZ)) x

theorem torusPotential_reflY (x : ℂ) :
    torusPotential (squareLattice (4 * nb)) (reflectPts b Z) (reflY b.im x) =
      torusPotential (squareLattice (4 * nb)) (reflectPts b Z) x := by
  have : NeZero (4 * nb) := ⟨by omega⟩
  exact congrFun ((reflYSymm b Z).torusPotential_comp (covolume_squareLattice (4 * nb))
    (reflectPts_distinct hnb b Z hZi hZ)) x

end Invariance

section Gradient

theorem norm_fderiv_comp_isom (f : ℂ → ℝ) (L : ℂ ≃ₗᵢ[ℝ] ℂ) (c x : ℂ) :
    ‖fderiv ℝ (fun y => f (L y + c)) x‖ = ‖fderiv ℝ f (L x + c)‖ := by
  have h1 := L.norm_iteratedFDeriv_comp_right (fun z => f (z + c)) x 1
  rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h1
  have e : fderiv ℝ (fun z => f (z + c)) (L x) = fderiv ℝ f (L x + c) := fderiv_comp_add_right c
  rw [e] at h1
  exact h1

/-- The gradient norm of a reflection-invariant function is reflection invariant. -/
theorem norm_gradient_refl {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} (S : ReflSymm Γ a)
    {h : ℂ → ℝ} (hh : ∀ x, h (S.R x) = h x) (x : ℂ) :
    ‖gradient h (S.R x)‖ = ‖gradient h x‖ := by
  rw [norm_gradient_eq, norm_gradient_eq]
  have e : h = fun y => h (S.L y + S.c) := by
    funext y; rw [← S.R_eq, hh]
  conv_rhs => rw [e]
  rw [norm_fderiv_comp_isom h S.L S.c x, ← S.R_eq]

end Gradient

section Balls

/-- The union of the open `η`-balls around the lattice translates of the charges. -/
@[expose] def ballUnion (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (η : ℝ) : Set ℂ :=
  ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η

theorem isOpen_ballUnion (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (η : ℝ) :
    IsOpen (ballUnion Γ a η) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => Metric.isOpen_ball

theorem mem_ballUnion {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} {η : ℝ} {x : ℂ} :
    x ∈ ballUnion Γ a η ↔ ∃ i, ∃ γ ∈ Γ, ‖x - (a i + γ)‖ < η := by
  simp [ballUnion, Metric.mem_ball, dist_eq_norm]

theorem add_mem_ballUnion_iff {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} {η : ℝ} {x γ₀ : ℂ}
    (hγ₀ : γ₀ ∈ Γ) : x + γ₀ ∈ ballUnion Γ a η ↔ x ∈ ballUnion Γ a η := by
  rw [mem_ballUnion, mem_ballUnion]
  constructor
  · rintro ⟨i, γ, hγ, h⟩
    refine ⟨i, γ - γ₀, Γ.sub_mem hγ hγ₀, ?_⟩
    convert h using 2; ring
  · rintro ⟨i, γ, hγ, h⟩
    refine ⟨i, γ + γ₀, Γ.add_mem hγ hγ₀, ?_⟩
    convert h using 2; ring

theorem ReflSymm.mem_ballUnion_of_mem {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} (S : ReflSymm Γ a)
    {η : ℝ} {x : ℂ} (hx : x ∈ ballUnion Γ a η) : S.R x ∈ ballUnion Γ a η := by
  rw [mem_ballUnion] at hx ⊢
  obtain ⟨i, γ, hγ, h⟩ := hx
  obtain ⟨k', hk'⟩ := S.charge i
  refine ⟨k', S.L γ, S.lat γ hγ, ?_⟩
  have : S.R x - (a k' + S.L γ) = S.R x - S.R (a i + γ) := by
    rw [S.R_add, hk']
  rw [this, S.norm_R_sub]
  exact h

theorem ReflSymm.mem_ballUnion_iff {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} (S : ReflSymm Γ a)
    {η : ℝ} {x : ℂ} : S.R x ∈ ballUnion Γ a η ↔ x ∈ ballUnion Γ a η := by
  refine ⟨fun h => ?_, S.mem_ballUnion_of_mem⟩
  simpa [S.invol] using S.mem_ballUnion_of_mem h

/-- The periodic integrand `1_{(⋃ balls)ᶜ} · |∇h|²`. -/
@[expose] noncomputable def energyDensity (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (h : ℂ → ℝ)
    (η : ℝ) (x : ℂ) : ℝ :=
  (ballUnion Γ a η)ᶜ.indicator (fun y => ‖gradient h y‖ ^ 2) x

theorem energyDensity_nonneg (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (h : ℂ → ℝ) (η : ℝ)
    (x : ℂ) : 0 ≤ energyDensity Γ a h η x :=
  Set.indicator_nonneg (fun _ _ => by positivity) x

theorem measurable_energyDensity (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (h : ℂ → ℝ) (η : ℝ) :
    Measurable (energyDensity Γ a h η) := by
  have hm : Measurable fun y : ℂ => ‖gradient h y‖ ^ 2 := by
    simp only [norm_gradient_eq]
    exact (measurable_fderiv ℝ h).norm.pow_const 2
  exact hm.indicator (isOpen_ballUnion Γ a η).measurableSet.compl

theorem energyDensity_add_period {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} {h : ℂ → ℝ}
    (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) (η : ℝ) {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    energyDensity Γ a h η (x + γ) = energyDensity Γ a h η x := by
  unfold energyDensity
  by_cases hx : x ∈ ballUnion Γ a η
  · have hx' : x + γ ∈ ballUnion Γ a η := (add_mem_ballUnion_iff hγ).2 hx
    simp [Set.indicator_of_notMem, hx, hx']
  · have hx' : x + γ ∉ ballUnion Γ a η := fun h' => hx ((add_mem_ballUnion_iff hγ).1 h')
    rw [Set.indicator_of_mem (by simpa using hx'), Set.indicator_of_mem (by simpa using hx)]
    simp only [norm_gradient_eq, fderiv_periodic Γ hper hγ x]

theorem energyDensity_refl {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} (S : ReflSymm Γ a)
    {h : ℂ → ℝ} (hh : ∀ x, h (S.R x) = h x) (η : ℝ) (x : ℂ) :
    energyDensity Γ a h η (S.R x) = energyDensity Γ a h η x := by
  unfold energyDensity
  by_cases hx : x ∈ ballUnion Γ a η
  · have hx' : S.R x ∈ ballUnion Γ a η := S.mem_ballUnion_of_mem hx
    simp [Set.indicator_of_notMem, hx, hx']
  · have hx' : S.R x ∉ ballUnion Γ a η := fun h' => hx (S.mem_ballUnion_iff.1 h')
    rw [Set.indicator_of_mem (by simpa using hx'), Set.indicator_of_mem (by simpa using hx)]
    simp only [norm_gradient_refl S hh x]

end Balls

end Lower

end Sphere

end SandierSerfaty

end
