/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.SquareCell
public import SandierSerfaty.Screening.NeumannPairing
public import SandierSerfaty.Jellium.TorusElec
public import SandierSerfaty.Dual.Pairing
public import SandierSerfaty.Dual.DualIdentity
public import SandierSerfaty.Torus.GreenRepr
public import SandierSerfaty.Statements.Torus.Theorems.TorusPotentialSpec

/-!
# The torus potential on the fundamental square

Setting of the screening note's §5: `Γ = squareLattice n = √n ℤ[i]`, `Q = sq c √n`, `n` charges `a i` in the open
square `int Q`, pairwise distinct, and `H = torusPotential Γ a`.

* `sub_mem_squareLattice_imp_eq`: the classes of the `a i` modulo `Γ` are distinct;
* `exists_eq_of_mem_chargeSet_of_mem_sq`: the only charges in `Q` are the `a i`;
* `torusPotential_eventuallyEq_greenSum`: off the charges, `H` is the Green sum;
* `setIntegral_inner_gradient_torusPotential_lipschitz`: for a Lipschitz test function with
  compact support in `int Q`, `∫_Q ⟪∇H, ∇φ⟫ = 2π (∑ᵢ φ(aᵢ) - ∫_Q φ)`;
* `setIntegral_inner_gradient_torusPotential_periodic`: the same identity for every Lipschitz
  `Γ`-periodic `ψ` (the periodic pairing identity `Dual.pairing_identity`, transported from
  `torusDomain Γ` to the fundamental square `Q`);
* `isChargeField_gradient_torusPotential`: `∇H` is a charge field in `int Q` with charges `{aᵢ}`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

open Torus

variable {n : ℕ} {c : ℂ} {a : Fin n → ℂ}

/-- Distinct points of the open square have distinct classes modulo `√n ℤ[i]`. -/
theorem sub_mem_squareLattice_imp_eq (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) :
    ∀ i j, a i - a j ∈ squareLattice n → i = j := fun i j h =>
  ha (eq_of_sub_mem_squareLattice (haQ i) (haQ j) h)

/-- The only charges in the closed square are the `a i`. -/
theorem exists_eq_of_mem_chargeSet_of_mem_sq (haQ : ∀ i, a i ∈ interior (sq c √n)) {x : ℂ}
    (hx : x ∈ chargeSet (squareLattice n) a) (hxQ : x ∈ sq c √n) : ∃ i, x = a i := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  by_contra hne
  exact add_notMem_sq_of_mem_interior (haQ i) hi (sub_ne_zero.2 hne) (by rwa [add_sub_cancel])

/-- A finite sum over the charges of a function supported in `Q` is the sum over the `a i`. -/
theorem finsum_chargeSet_eq (haQ : ∀ i, a i ∈ interior (sq c √n))
    {g : ℂ → ℝ} (hg : ∀ x, g x ≠ 0 → x ∈ sq c √n) :
    ∑ᶠ p ∈ chargeSet (squareLattice n) a, g p = ∑ y ∈ Finset.univ.image a, g y := by
  classical
  refine finsum_mem_eq_finsetSum (fun y hy => ?_) fun p hp hpS => ?_
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨i, by simp⟩
  · by_contra h
    obtain ⟨i, rfl⟩ := exists_eq_of_mem_chargeSet_of_mem_sq haQ hp (hg p h)
    exact hpS (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)

theorem finsum_range_eq {β : Type*} [AddCommMonoid β] (g : ℂ → β) :
    ∑ᶠ p ∈ range a, g p = ∑ y ∈ Finset.univ.image a, g y := by
  classical
  refine finsum_mem_eq_finsetSum (fun y hy => ?_) fun p hp hpS => ?_
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
    exact mem_range_self i
  · obtain ⟨i, rfl⟩ := hp
    exact absurd (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩) hpS

theorem sum_image_eq {β : Type*} [AddCommMonoid β] (ha : Function.Injective a) (g : ℂ → β) :
    ∑ y ∈ Finset.univ.image a, g y = ∑ i, g (a i) := by
  classical
  rw [Finset.sum_image fun i _ j _ h => ha h]

variable [NeZero n]

/-- `H` is a torus potential. -/
theorem isTorusPotential_torusPotential_sq (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) :
    IsTorusPotential (squareLattice n) a (torusPotential (squareLattice n) a) :=
  (torusPotential_spec _ (covolume_squareLattice n) a (sub_mem_squareLattice_imp_eq ha haQ)).1

/-- Off the charges, `H` agrees near every point with the Green sum. -/
theorem torusPotential_eventuallyEq_greenSum (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) {x : ℂ} (hx : x ∉ chargeSet (squareLattice n) a) :
    torusPotential (squareLattice n) a =ᶠ[𝓝 x] greenSum (squareLattice n) a := by
  have hdist := sub_mem_squareLattice_imp_eq ha haQ
  have h := (torusPotential_spec _ (covolume_squareLattice n) a hdist).2 _
    (isTorusPotential_greenSum (covolume_squareLattice n) hdist)
  filter_upwards [(isClosed_chargeSet _ a).isOpen_compl.mem_nhds hx] with y hy
  rw [← h]
  simp [show y ∉ chargeSet (squareLattice n) a from hy]

theorem gradient_torusPotential_eq_greenSum (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) {x : ℂ} (hx : x ∉ chargeSet (squareLattice n) a) :
    gradient (torusPotential (squareLattice n) a) x = gradient (greenSum (squareLattice n) a) x :=
  gradient_congr_nhds (torusPotential_eventuallyEq_greenSum ha haQ hx)

theorem integrableOn_gradient_torusPotential (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) (S : Set ℂ) (hS : IsCompact S) :
    IntegrableOn (gradient (torusPotential (squareLattice n) a)) S :=
  ((isTorusPotential_torusPotential_sq ha haQ).locallyIntegrable_gradient).integrableOn_isCompact hS

/-- `∇H ∈ elec(a + Γ)`. -/
theorem gradient_torusPotential_mem_elec_sq (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) :
    gradient (torusPotential (squareLattice n) a) ∈ elec (chargeSet (squareLattice n) a) := by
  have := gradient_torusPotential_mem_elec _ (covolume_squareLattice n) a
    (sub_mem_squareLattice_imp_eq ha haQ)
  rwa [show periodicSites (squareLattice n) a = chargeSet (squareLattice n) a from
    Set.ext fun _ => mem_periodicSites_iff _ a] at this

/-- The smooth identity for `∇H` on `Q`, test functions supported in `int Q`. -/
theorem setIntegral_inner_gradient_torusPotential_of_contDiff (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφQ : tsupport φ ⊆ interior (sq c √n)) :
    ∫ x in sq c √n, inner ℝ (gradient (torusPotential (squareLattice n) a) x) (gradient φ x) =
      2 * π * (∑ y ∈ Finset.univ.image a, φ y - 1 * ∫ x in sq c √n, φ x) := by
  have hE := gradient_torusPotential_mem_elec_sq ha haQ
  have h := hE.2.2 φ hφ hφc
  have hQ : ∀ x, x ∉ sq c √n → x ∉ tsupport φ := fun x hx h => hx (interior_subset (hφQ h))
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [gradient_eq_zero_of_notMem_tsupport (hQ x hx), inner_zero_right],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
      image_eq_zero_of_notMem_tsupport (hQ x hx), h, one_mul,
    finsum_chargeSet_eq haQ fun x hx => by
      by_contra h'; exact hx (image_eq_zero_of_notMem_tsupport (hQ x h'))]

/-- **The Lipschitz identity for `∇H` on `Q`**, test functions with compact support in `int Q`. -/
theorem setIntegral_inner_gradient_torusPotential_lipschitz (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) {φ : ℂ → ℝ} {K : ℝ≥0} (hφ : LipschitzWith K φ)
    (hφc : HasCompactSupport φ) (hφQ : tsupport φ ⊆ interior (sq c √n)) :
    ∫ x in sq c √n, inner ℝ (gradient (torusPotential (squareLattice n) a) x) (gradient φ x) =
      2 * π * (∑ y ∈ Finset.univ.image a, φ y - 1 * ∫ x in sq c √n, φ x) :=
  setIntegral_inner_gradient_lipschitz (measurableSet_sq c _) isOpen_interior
    (integrableOn_gradient_torusPotential ha haQ _ (isCompact_sq c _))
    (fun _ hψ hψc hψQ => setIntegral_inner_gradient_torusPotential_of_contDiff ha haQ hψ hψc hψQ)
    hφ hφc hφQ

theorem inner_gradient_eq_gradDot (u φ : ℂ → ℝ) (x : ℂ) :
    inner ℝ (gradient u x) (gradient φ x) = Analysis.gradDot φ u x := by
  rw [inner_gradient_gradient]
  simp only [Analysis.gradDot, Analysis.pd₁, Analysis.pd₂, Weyl.pd]
  ring

/-- **The periodic identity for `∇H` on `Q`**: every Lipschitz `Γ`-periodic `ψ`. -/
theorem setIntegral_inner_gradient_torusPotential_periodic (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) {ψ : ℂ → ℝ} {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (hper : ∀ γ ∈ squareLattice n, ∀ x, ψ (x + γ) = ψ x) :
    ∫ x in sq c √n, inner ℝ (gradient (torusPotential (squareLattice n) a) x) (gradient ψ x) =
      2 * π * (∑ y ∈ Finset.univ.image a, ψ y - 1 * ∫ x in sq c √n, ψ x) := by
  set Γ := squareLattice n with hΓ
  have hdist := sub_mem_squareLattice_imp_eq ha haQ
  obtain ⟨-, hpair⟩ := Dual.pairing_identity (covolume_squareLattice n) hdist hψ hper
  have hF := isAddFundamentalDomain_sq (n := n) c
  have hgper := Dual.gradDot_periodic (Γ := Γ) hper fun γ hγ x => greenSum_add_period (Γ := Γ) (a := a) hγ x
  rw [(torusDomain_spec Γ).2 _ hF _ hgper, (torusDomain_spec Γ).2 _ hF _ hper] at hpair
  have hnull : ∀ᵐ x ∂volume, x ∉ chargeSet Γ a := (countable_chargeSet Γ a).ae_notMem volume
  rw [setIntegral_congr_ae (measurableSet_sq c _) (hnull.mono fun x hx _ => by
    rw [gradient_torusPotential_eq_greenSum ha haQ hx, inner_gradient_eq_gradDot]), hpair,
    sum_image_eq ha]
  ring

/-- `∇H` is a charge field in `int Q` with charges `{a i}` (I0 on the square). -/
theorem isChargeField_gradient_torusPotential (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √n)) :
    IsChargeField (interior (sq c √n)) 1 (range a) (gradient (torusPotential (squareLattice n) a)) := by
  have hE := gradient_torusPotential_mem_elec_sq ha haQ
  refine ⟨hE.2.1.locallyIntegrableOn _, fun φ hφ hφc hφQ => ?_⟩
  have hQ : ∀ x, x ∉ sq c √n → x ∉ tsupport φ := fun x hx h => hx (interior_subset (hφQ h))
  rw [hE.2.2 φ hφ hφc, one_mul, finsum_range_eq,
    finsum_chargeSet_eq haQ fun x hx => by
      by_contra h'; exact hx (image_eq_zero_of_notMem_tsupport (hQ x h'))]

end Screening

end SandierSerfaty

end
