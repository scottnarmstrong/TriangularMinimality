/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectBasic
public import SandierSerfaty.Torus.PotentialUnique
public import SandierSerfaty.Torus.Lattice
public import SandierSerfaty.Statements.Torus.Theorems.TorusPotentialSpec
public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec

/-!
# Invariance of the torus potential under reflections (sphere note, Lemma 6.2(i))

`Lower.ReflSymm Γ a` packages an involutive affine isometry `R` of `ℂ` whose linear part preserves the lattice
`Γ` and which permutes the charges `a` exactly. For such an `R`, `h ∘ R` satisfies every clause of
`IsTorusPotential Γ a` whenever `h` does; by uniqueness `torusPotential Γ a ∘ R = torusPotential Γ a`
(`torusPotential_comp_refl`). The two reflections of the reflected configuration are
`Lower.reflXSymm`, `Lower.reflYSymm`.
-/

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- A reflection symmetry of the charges `a` modulo `Γ`. -/
structure ReflSymm (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) where
  /-- the reflection -/
  R : ℂ → ℂ
  /-- its linear part -/
  L : ℂ ≃ₗᵢ[ℝ] ℂ
  /-- its translation part -/
  c : ℂ
  R_eq : ∀ x, R x = L x + c
  invol : ∀ x, R (R x) = x
  lat : ∀ γ ∈ Γ, L γ ∈ Γ
  charge : ∀ k, ∃ k', R (a k) = a k'

namespace ReflSymm

variable {Γ : Submodule ℤ ℂ} {N : ℕ} {a : Fin N → ℂ} (S : ReflSymm Γ a)

theorem R_sub (x y : ℂ) : S.R x - S.R y = S.L (x - y) := by
  rw [S.R_eq, S.R_eq, map_sub]; ring

theorem R_add (x γ : ℂ) : S.R (x + γ) = S.R x + S.L γ := by
  rw [S.R_eq, S.R_eq, map_add]; ring

theorem norm_R_sub (x y : ℂ) : ‖S.R x - S.R y‖ = ‖x - y‖ := by
  rw [S.R_sub, LinearIsometryEquiv.norm_map]

theorem L_L (x : ℂ) : S.L (S.L x) = x := by
  have h0 := S.invol 0
  have h1 := S.invol x
  rw [S.R_eq, S.R_eq, map_add] at h0 h1
  have : S.L (S.L x) + S.L S.c + S.c = x := by
    simpa [map_add, add_assoc] using h1
  have h2 : S.L S.c + S.c = 0 := by simpa using h0
  calc S.L (S.L x) = S.L (S.L x) + (S.L S.c + S.c) := by rw [h2, add_zero]
    _ = x := by rw [← add_assoc]; exact this

theorem contDiff_R : ContDiff ℝ ∞ S.R := by
  have : S.R = fun x => S.L x + S.c := funext S.R_eq
  rw [this]
  exact (S.L.toContinuousLinearEquiv.contDiff).add contDiff_const

theorem continuous_R : Continuous S.R := (S.contDiff_R).continuous

theorem sub_mem_imp (x : ℂ) (k : Fin N) (h : x - a k ∈ Γ) : ∃ k', S.R x - a k' ∈ Γ := by
  obtain ⟨k', hk'⟩ := S.charge k
  refine ⟨k', ?_⟩
  rw [← hk', S.R_sub]
  exact S.lat _ h

/-- The charge set is invariant under the reflection. -/
theorem R_mem_chargeSet_iff (x : ℂ) :
    (∃ k, S.R x - a k ∈ Γ) ↔ ∃ k, x - a k ∈ Γ := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨k', hk'⟩ := S.sub_mem_imp _ k hk
    exact ⟨k', by rwa [S.invol] at hk'⟩
  · rintro ⟨k, hk⟩
    exact S.sub_mem_imp x k hk

/-- `R` is measure preserving. -/
theorem measurePreserving_R : MeasurePreserving S.R volume volume := by
  have : S.R = (fun x => x + S.c) ∘ S.L := funext fun x => S.R_eq x
  rw [this]
  exact (measurePreserving_add_right volume S.c).comp S.L.measurePreserving

theorem measurableEmbedding_R : MeasurableEmbedding S.R := by
  have : S.R = ((S.L.toHomeomorph).trans (Homeomorph.addRight S.c) : ℂ → ℂ) := by
    funext x; simp [S.R_eq]
  rw [this]
  exact (S.L.toHomeomorph.trans (Homeomorph.addRight S.c)).measurableEmbedding

/-- `h ∘ R` is a torus potential of the same charges. -/
theorem isTorusPotential_comp [DiscreteTopology Γ] [IsZLattice ℝ Γ] {h : ℂ → ℝ}
    (hh : IsTorusPotential Γ a h) : IsTorusPotential Γ a (h ∘ S.R) := by
  obtain ⟨hper, hsm, hlap, hlog, hint, hzero⟩ := hh
  have hRfun : S.R = fun x => S.L x + S.c := funext S.R_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ x
    simp only [Function.comp_apply, S.R_add]
    exact hper _ (S.lat γ hγ) _
  · refine hsm.comp S.contDiff_R.contDiffOn ?_
    intro x hx i hi
    obtain ⟨k, hk⟩ : ∃ k, S.R x - a k ∈ Γ := ⟨i, hi⟩
    exact (hx (((S.R_mem_chargeSet_iff x).1 ⟨k, hk⟩).choose))
      (((S.R_mem_chargeSet_iff x).1 ⟨k, hk⟩).choose_spec)
  · intro x hx
    have hRx : ∀ i, S.R x - a i ∉ Γ := fun i hi =>
      hx (((S.R_mem_chargeSet_iff x).1 ⟨i, hi⟩).choose)
        (((S.R_mem_chargeSet_iff x).1 ⟨i, hi⟩).choose_spec)
    have e : (h ∘ S.R) = fun y => h (S.L y + S.c) := by rw [hRfun]; rfl
    rw [e, laplacian_comp_isom h S.L S.c x, ← S.R_eq]
    exact hlap _ hRx
  · intro i
    obtain ⟨k', hk'⟩ := S.charge i
    obtain ⟨C, hC⟩ := hlog k'
    refine ⟨C, ?_⟩
    have h1 : Tendsto S.R (𝓝[≠] (a i)) (𝓝[≠] (a k')) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · rw [← hk']; exact (S.continuous_R.tendsto _).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        intro hxe
        apply hx
        have := congrArg S.R hxe
        rwa [S.invol, ← hk', S.invol] at this
    refine (hC.comp h1).congr fun x => ?_
    simp only [Function.comp_apply]
    rw [← hk', S.norm_R_sub]
  · have hfd := (torusDomain_spec Γ).1
    have hfd' : IsAddFundamentalDomain Γ (S.R ⁻¹' torusDomain Γ) volume := by
      refine hfd.preimage_of_equiv (f := S.R) S.measurePreserving_R.quasiMeasurePreserving
        (e := fun γ : Γ => (⟨S.L γ, S.lat γ γ.2⟩ : Γ)) ?_ ?_
      · constructor
        · intro γ₁ γ₂ h12
          have := congrArg Subtype.val h12
          exact Subtype.ext (S.L.injective this)
        · intro γ'
          refine ⟨⟨S.L γ', S.lat γ' γ'.2⟩, ?_⟩
          exact Subtype.ext (S.L_L γ')
      · intro γ x
        change S.R (S.L γ + x) = (γ : ℂ) + S.R x
        rw [add_comm, S.R_add, S.L_L, add_comm]
    have hper' : ∀ γ ∈ Γ, ∀ x, (h ∘ S.R) (x + γ) = (h ∘ S.R) x := by
      intro γ hγ x
      simp only [Function.comp_apply, S.R_add]
      exact hper _ (S.lat γ hγ) _
    rw [(torusDomain_spec Γ).2 _ hfd' _ hper']
    have := S.measurePreserving_R.setIntegral_preimage_emb S.measurableEmbedding_R h (torusDomain Γ)
    exact this.trans hint
  · intro x hx
    simp only [Function.comp_apply]
    exact hzero _ ((S.R_mem_chargeSet_iff x).2 hx)

/-- **Lemma 6.2(i).** The torus potential is invariant under the reflection. -/
theorem torusPotential_comp [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    torusPotential Γ a ∘ S.R = torusPotential Γ a := by
  obtain ⟨hP, hU⟩ := torusPotential_spec Γ hΓ a ha
  exact (hU _ (S.isTorusPotential_comp hP))

end ReflSymm

end Lower

end Sphere

end SandierSerfaty

end
