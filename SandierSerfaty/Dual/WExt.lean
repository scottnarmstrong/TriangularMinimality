/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.Periodic
public import SandierSerfaty.Dual.Pairing
public import SandierSerfaty.Torus.GreenRepr

/-!
# The difference `h - H` as a global Lipschitz function

`wExt R Γ a z = greenSum Γ a z - gluedH R P z` off the charges, and `cval i = R_Γ + ∑_{j ≠ i} G(aᵢ - aⱼ)` at
the charge `aᵢ + Γ`. It is `Γ`-periodic (`wExt_add_period`) and globally Lipschitz (`exists_lipschitzWith_wExt`):

near a charge, `h = s - log r` (local form of the Green potential) and `H = H₁ - log r` with the
Lipschitz function `H₁` of `SandierSerfaty.Dual.exists_lipschitzOnWith_H1` vanishing at the charge, so
that `h - H = s - H₁` has no singularity; this is the vanishing of the constant term of `H`
(paper `dual:gluing` and proof of `dual:identity`). Away from the charges both `h` and `H` are locally Lipschitz.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Torus

variable {ι : Type*} {R : RadialData ι} {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]
  {N : ℕ} {a : Fin N → ℂ} {d₀ : ℝ}

/-- The value of `h - H` at the charge `a i`: `R_Γ + ∑_{j ≠ i} G (a i - a j)`. -/
@[expose] noncomputable def cval (Γ : Submodule ℤ ℂ) (a : Fin N → ℂ) (i : Fin N) : ℝ :=
  torusRobin Γ + ∑ j ∈ Finset.univ.erase i, torusGreen Γ (a i - a j)

open Classical in
/-- `h - H`, extended continuously to the charges. -/
@[expose] noncomputable def wExt (R : RadialData ι) (Γ : Submodule ℤ ℂ) (a : Fin N → ℂ) (z : ℂ) : ℝ :=
  if h : z ∈ chargeSet Γ a then cval Γ a (Classical.choose h)
  else greenSum Γ a z - gluedH R (periodicSites Γ a) z

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem periodicSites_eq_chargeSet : periodicSites Γ a = chargeSet Γ a := by
  ext x; exact mem_periodicSites_iff Γ a

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem wExt_of_mem (ha : ∀ i j, a i - a j ∈ Γ → i = j) {z : ℂ} {i : Fin N} (hz : z - a i ∈ Γ) :
    wExt R Γ a z = cval Γ a i := by
  have h : z ∈ chargeSet Γ a := ⟨i, hz⟩
  unfold wExt
  rw [dite_eq_left h]
  have hj := Classical.choose_spec h
  have : Classical.choose h = i := by
    refine ha _ _ ?_
    have : a (Classical.choose h) - a i = (z - a i) - (z - a (Classical.choose h)) := by ring
    rw [this]; exact Γ.sub_mem hz hj
  rw [this]

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem wExt_of_notMem {z : ℂ} (hz : z ∉ chargeSet Γ a) :
    wExt R Γ a z = greenSum Γ a z - gluedH R (periodicSites Γ a) z := by
  unfold wExt; rw [dite_eq_right hz]

theorem wExt_add_period (ha : ∀ i j, a i - a j ∈ Γ → i = j) (hS : SepSites (periodicSites Γ a) d₀)
    {γ : ℂ} (hγ : γ ∈ Γ) (z : ℂ) : wExt R Γ a (z + γ) = wExt R Γ a z := by
  by_cases hz : z ∈ chargeSet Γ a
  · obtain ⟨i, hi⟩ := hz
    rw [wExt_of_mem ha hi, wExt_of_mem ha (i := i) (by
      have : z + γ - a i = (z - a i) + γ := by ring
      rw [this]; exact Γ.add_mem hi hγ)]
  · have hz' : z + γ ∉ chargeSet Γ a := fun h => by
      obtain ⟨i, hi⟩ := h
      apply hz
      refine ⟨i, ?_⟩
      have : z - a i = (z + γ - a i) - γ := by ring
      rw [this]; exact Γ.sub_mem hi hγ
    rw [wExt_of_notMem hz', wExt_of_notMem hz, greenSum_add_period hγ,
      gluedH_add hS (fun q => add_mem_periodicSites_iff Γ a hγ)]

theorem locallyLipschitz_wExt_at_base (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    (hR : R.IsAdmissible d₀) (hS : SepSites (periodicSites Γ a) d₀) (i : Fin N) :
    ∃ K : NNReal, ∃ t ∈ 𝓝 (a i), LipschitzOnWith K (wExt R Γ a) t := by
  obtain ⟨K₁, ρ₁, hρ₁, hρ₁d, hH1⟩ := exists_lipschitzOnWith_H1 hR hS
  obtain ⟨s, hs, hs0, hev⟩ := greenSum_localForm ha i
  obtain ⟨K₂, t₂, ht₂, hlip₂⟩ := (hs.of_le (by norm_cast : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
  have hpi : a i ∈ periodicSites Γ a := mem_periodicSites Γ a i
  have hH1i := hH1 (a i) hpi
  have hnot : ∀ᶠ y in 𝓝[≠] (a i), y ∉ chargeSet Γ a := eventually_notMem_chargeSet Γ a (a i)
  have heq : ∀ᶠ y in 𝓝 (a i), wExt R Γ a y = s y - H1 R (periodicSites Γ a) (a i) y := by
    rw [← nhdsNE_sup_pure, eventually_sup]
    refine ⟨?_, ?_⟩
    · filter_upwards [hnot, hev, nhdsWithin_le_nhds (ball_mem_nhds (a i) hρ₁), self_mem_nhdsWithin]
        with y hy1 hy2 hy3 hy4
      have hy4' : y ≠ a i := hy4
      rw [wExt_of_notMem hy1, hy2, gluedH_eq_cellH hS hpi
        (ball_subset_voronoiCell hS hpi (ball_subset_ball hρ₁d hy3)), H1_eq_cellH_add_log hy4']
      ring
    · rw [eventually_pure, wExt_of_mem ha (i := i) (by simp), H1_self hR hS hpi, hs0]
      simp [cval]
  refine ⟨K₂ + K₁, t₂ ∩ ball (a i) ρ₁ ∩ {y | wExt R Γ a y = s y - H1 R (periodicSites Γ a) (a i) y},
    inter_mem (inter_mem ht₂ (ball_mem_nhds _ hρ₁)) heq, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [hx.2, hy.2]
  have h1 := hlip₂.dist_le_mul x hx.1.1 y hy.1.1
  have h2 := hH1i.dist_le_mul x hx.1.2 y hy.1.2
  rw [Real.dist_eq] at h1 h2 ⊢
  push_cast
  calc |s x - H1 R (periodicSites Γ a) (a i) x - (s y - H1 R (periodicSites Γ a) (a i) y)|
      = |(s x - s y) - (H1 R (periodicSites Γ a) (a i) x - H1 R (periodicSites Γ a) (a i) y)| := by
        ring_nf
    _ ≤ |s x - s y| + |H1 R (periodicSites Γ a) (a i) x - H1 R (periodicSites Γ a) (a i) y| := abs_sub _ _
    _ ≤ _ := by nlinarith

theorem locallyLipschitz_wExt (ha : ∀ i j, a i - a j ∈ Γ → i = j) (hR : R.IsAdmissible d₀)
    (hS : SepSites (periodicSites Γ a) d₀) : LocallyLipschitz (wExt R Γ a) := by
  intro x
  by_cases hx : x ∈ chargeSet Γ a
  · obtain ⟨i, hi⟩ := hx
    obtain ⟨K, t, ht, hK⟩ := locallyLipschitz_wExt_at_base ha hR hS i
    refine ⟨K, (fun y => y - (x - a i)) ⁻¹' t, ?_, ?_⟩
    · apply (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      have : x - (x - a i) = a i := by ring
      simpa [this] using ht
    · refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
      have e : ∀ z : ℂ, wExt R Γ a z = wExt R Γ a (z - (x - a i)) := fun z => by
        have := wExt_add_period (R := R) ha hS hi (z - (x - a i))
        rw [sub_add_cancel] at this
        exact this
      rw [e y, e y']
      have := hK.dist_le_mul _ hy _ hy'
      refine this.trans (le_of_eq ?_)
      simp [dist_eq_norm]
  · obtain ⟨K₁, δ, hδ, hH⟩ := exists_lipschitzOnWith_ball hR hS (x := x)
      (by rw [periodicSites_eq_chargeSet]; exact hx)
    obtain ⟨K₂, t₂, ht₂, hlip₂⟩ :=
      ((contDiffAt_greenSum hx).of_le (by norm_cast : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
    have hopen : (chargeSet Γ a)ᶜ ∈ 𝓝 x := (isClosed_chargeSet Γ a).isOpen_compl.mem_nhds hx
    refine ⟨K₂ + K₁, t₂ ∩ ball x δ ∩ (chargeSet Γ a)ᶜ,
      inter_mem (inter_mem ht₂ (ball_mem_nhds _ hδ)) hopen, ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun y hy y' hy' => ?_
    rw [wExt_of_notMem hy.2, wExt_of_notMem hy'.2]
    have h1 := hlip₂.dist_le_mul y hy.1.1 y' hy'.1.1
    have h2 := hH.dist_le_mul y hy.1.2 y' hy'.1.2
    rw [Real.dist_eq] at h1 h2 ⊢
    push_cast
    calc |greenSum Γ a y - gluedH R (periodicSites Γ a) y -
          (greenSum Γ a y' - gluedH R (periodicSites Γ a) y')|
        = |(greenSum Γ a y - greenSum Γ a y') -
            (gluedH R (periodicSites Γ a) y - gluedH R (periodicSites Γ a) y')| := by ring_nf
      _ ≤ _ := (abs_sub _ _).trans (by nlinarith)

theorem exists_lipschitzWith_wExt (ha : ∀ i j, a i - a j ∈ Γ → i = j) (hR : R.IsAdmissible d₀)
    (hS : SepSites (periodicSites Γ a) d₀) : ∃ K, LipschitzWith K (wExt R Γ a) :=
  lipschitzWith_of_locallyLipschitz_periodic (Γ := Γ) (locallyLipschitz_wExt ha hR hS)
    fun _ hγ z => wExt_add_period ha hS hγ z

end Dual

end SandierSerfaty

end
