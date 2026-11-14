/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.SquareLattice
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Lattice facts for the torus

`squareLattice n` (`n ≠ 0`) and `triangularLattice` are `ℤ`-lattices of `ℂ` (discrete and spanning),
with covolumes `n` and `1`; and `VAddInvariantMeasure ↥Γ ℂ volume` for every `Γ`.
-/

open MeasureTheory Module

public section

namespace SandierSerfaty

/-- Translation by elements of a `ℤ`-submodule of `ℂ` preserves Lebesgue measure. -/
instance instVAddInvariantMeasureSubmodule (Γ : Submodule ℤ ℂ) :
    VAddInvariantMeasure Γ ℂ (volume : Measure ℂ) :=
  ⟨fun c s _ => measure_preimage_add volume (c : ℂ) s⟩

namespace Torus

/-- The real basis `![u, v]` of `ℂ`, when `u, v` are `ℝ`-independent. -/
noncomputable def latticeBasis (u v : ℂ) (h : u.re * v.im - u.im * v.re ≠ 0) :
    Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank
    (b := ![u, v])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg Complex.re hst
      have h2 := congrArg Complex.im hst
      simp at h1 h2
      constructor
      · apply (mul_left_inj' h).1
        linear_combination v.im * h1 - v.re * h2
      · apply (mul_left_inj' h).1
        linear_combination u.re * h2 - u.im * h1)
    (by simp [Complex.finrank_real_complex])

@[simp] theorem latticeBasis_apply (u v : ℂ) (h : u.re * v.im - u.im * v.re ≠ 0) (i : Fin 2) :
    latticeBasis u v h i = ![u, v] i := by
  simp [latticeBasis]

theorem det_latticeBasis (u v : ℂ) (h : u.re * v.im - u.im * v.re ≠ 0) :
    Complex.basisOneI.det (latticeBasis u v h) = u.re * v.im - u.im * v.re := by
  rw [Basis.det_apply, Matrix.det_fin_two]
  simp [Basis.toMatrix_apply]
  ring

theorem discreteTopology_of_eq {L : Submodule ℤ ℂ} (b : Basis (Fin 2) ℝ ℂ)
    (hL : L = Submodule.span ℤ (Set.range b)) : DiscreteTopology L := by
  subst hL; infer_instance

theorem isZLattice_of_eq {L : Submodule ℤ ℂ} (b : Basis (Fin 2) ℝ ℂ)
    (hL : L = Submodule.span ℤ (Set.range b)) :
    @IsZLattice ℝ _ ℂ _ _ L (discreteTopology_of_eq b hL) := by
  subst hL; infer_instance

theorem covolume_of_eq {L : Submodule ℤ ℂ} (b : Basis (Fin 2) ℝ ℂ)
    (hL : L = Submodule.span ℤ (Set.range b)) :
    haveI := discreteTopology_of_eq b hL
    haveI := isZLattice_of_eq b hL
    ZLattice.covolume L = |Complex.basisOneI.det b| := by
  subst hL
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume Complex.basisOneI]
  have : volume.real (ZSpan.fundamentalDomain (Complex.basisOneI)) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume)]
    have := Complex.orthonormalBasisOneI.volume_parallelepiped
    simp only [measureReal_def]
    rw [show (Complex.basisOneI : Basis (Fin 2) ℝ ℂ) = Complex.orthonormalBasisOneI.toBasis by
      simp]
    rw [Complex.orthonormalBasisOneI.coe_toBasis, this]; simp
  rw [this, mul_one]

theorem range_latticeBasis (u v : ℂ) (h : u.re * v.im - u.im * v.re ≠ 0) :
    Set.range (latticeBasis u v h) = {u, v} := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, latticeBasis_apply]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem squareLattice_det (n : ℕ) [NeZero n] :
    (⟨√n, 0⟩ : ℂ).re * (⟨0, √n⟩ : ℂ).im - (⟨√n, 0⟩ : ℂ).im * (⟨0, √n⟩ : ℂ).re ≠ 0 := by
  have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have := Real.sqrt_pos.2 this
  have := mul_pos this this
  simp only [ne_eq]
  simpa using this.ne'

theorem squareLattice_eq (n : ℕ) [NeZero n] :
    squareLattice n =
      Submodule.span ℤ (Set.range (latticeBasis ⟨√n, 0⟩ ⟨0, √n⟩ (squareLattice_det n))) := by
  rw [range_latticeBasis]; rfl

theorem triangular_det :
    ((√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ)).re * ((√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)).im -
      ((√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ)).im * ((√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)).re = 1 := by
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  have h2 : √(2 / √3) ^ 2 = 2 / √3 := Real.sq_sqrt (by positivity)
  simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
  field_simp
  have h4 : √(2 / √3) ^ 2 * √3 = 2 := by rw [h2]; field_simp
  nlinarith [h4]

theorem triangularLattice_eq :
    triangularLattice =
      Submodule.span ℤ (Set.range (latticeBasis
        ((√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ)) ((√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ))
        (by rw [triangular_det]; exact one_ne_zero))) := by
  rw [range_latticeBasis]; rfl

instance (n : ℕ) [NeZero n] : DiscreteTopology (squareLattice n) :=
  discreteTopology_of_eq _ (squareLattice_eq n)

instance (n : ℕ) [NeZero n] : IsZLattice ℝ (squareLattice n) :=
  isZLattice_of_eq _ (squareLattice_eq n)

instance : DiscreteTopology triangularLattice :=
  discreteTopology_of_eq _ triangularLattice_eq

instance : IsZLattice ℝ triangularLattice :=
  isZLattice_of_eq _ triangularLattice_eq

theorem covolume_squareLattice (n : ℕ) [NeZero n] : ZLattice.covolume (squareLattice n) = n := by
  have := covolume_of_eq _ (squareLattice_eq n)
  convert this using 1
  rw [det_latticeBasis]
  have h : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp [Real.mul_self_sqrt h, abs_of_nonneg h]

theorem covolume_triangularLattice : ZLattice.covolume triangularLattice = 1 := by
  have := covolume_of_eq _ triangularLattice_eq
  convert this using 1
  rw [det_latticeBasis, triangular_det]; simp

end Torus

end SandierSerfaty

end
