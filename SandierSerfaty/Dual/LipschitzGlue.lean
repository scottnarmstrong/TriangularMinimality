/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Analysis.Convex.Between

/-!
# Gluing Lipschitz estimates across a finite closed cover

A function which is `K`-Lipschitz on each member of a finite cover of an interval by closed
intervals is `K`-Lipschitz (`lipschitzOnWith_Icc_of_cover`). Consequently a
function on a convex set which is `K`-Lipschitz on each of finitely many closed convex
sets covering it is `K`-Lipschitz (`lipschitzOnWith_of_convex_cover`). This is the form of
the fact (continuous piecewise-`C¹` gives `W^{1,∞}`) used for the glued trial potential.
-/

open Set Filter Topology

public section

namespace SandierSerfaty

namespace Dual

/-- Two Lipschitz estimates on `[a, c]` and `[c, b]` give one on `[a, b]`. -/
theorem lipschitzOnWith_Icc_union {f : ℝ → ℝ} {K : NNReal} {a c b : ℝ}
    (h1 : LipschitzOnWith K f (Icc a c)) (h2 : LipschitzOnWith K f (Icc c b)) (hac : a ≤ c)
    (hcb : c ≤ b) : LipschitzOnWith K f (Icc a b) := by
  have key : ∀ x y, x ∈ Icc a b → y ∈ Icc a b → x ≤ y → |f x - f y| ≤ K * |x - y| := by
    intro x y hx hy hxy
    have hfa : ∀ u v, u ∈ Icc a c → v ∈ Icc a c → |f u - f v| ≤ K * |u - v| := by
      intro u v hu hv
      have := h1.dist_le_mul u hu v hv
      simpa [Real.dist_eq] using this
    have hfb : ∀ u v, u ∈ Icc c b → v ∈ Icc c b → |f u - f v| ≤ K * |u - v| := by
      intro u v hu hv
      have := h2.dist_le_mul u hu v hv
      simpa [Real.dist_eq] using this
    by_cases hxc : y ≤ c
    · exact hfa x y ⟨hx.1, hxy.trans hxc⟩ ⟨hy.1, hxc⟩
    by_cases hyc : c ≤ x
    · exact hfb x y ⟨hyc, hx.2⟩ ⟨hyc.trans hxy, hy.2⟩
    rw [not_le] at hxc hyc
    have e1 := hfa x c ⟨hx.1, hyc.le⟩ ⟨hac, le_rfl⟩
    have e2 := hfb c y ⟨le_rfl, hcb⟩ ⟨hxc.le, hy.2⟩
    calc |f x - f y| ≤ |f x - f c| + |f c - f y| := abs_sub_le _ _ _
      _ ≤ K * |x - c| + K * |c - y| := add_le_add e1 e2
      _ = K * |x - y| := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          ring
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x y with h | h
  · exact key x y hx hy h
  · rw [abs_sub_comm, abs_sub_comm x y]; exact key y x hy hx h

/-- **Gluing on an interval.** -/
theorem lipschitzOnWith_Icc_of_cover {ι : Type*} (F : Finset ι) (s : ι → Set ℝ) {f : ℝ → ℝ}
    {K : NNReal} (hs : ∀ i, IsClosed (s i)) (hoc : ∀ i, (s i).OrdConnected) :
    ∀ {a b : ℝ}, a ≤ b → Icc a b ⊆ ⋃ i ∈ F, s i →
      (∀ i ∈ F, LipschitzOnWith K f (s i ∩ Icc a b)) → LipschitzOnWith K f (Icc a b) := by
  classical
  induction F using Finset.strongInduction with
  | _ F ih =>
  intro a b hab hcov hK
  obtain ⟨j, hjF, haj⟩ : ∃ j ∈ F, a ∈ s j := by
    have := hcov ⟨le_rfl, hab⟩
    simpa using this
  set T : Set ℝ := s j ∩ Icc a b with hT
  have hTc : IsCompact T := isCompact_Icc.inter_left (hs j)
  have hTne : T.Nonempty := ⟨a, haj, le_rfl, hab⟩
  set c := sSup T with hc
  have hcT : c ∈ T := hTc.sSup_mem hTne
  have hac : a ≤ c := le_csSup hTc.bddAbove ⟨haj, le_rfl, hab⟩
  have hcb : c ≤ b := hcT.2.2
  have hacs : Icc a c ⊆ s j := (hoc j).out haj hcT.1
  have hLac : LipschitzOnWith K f (Icc a c) :=
    (hK j hjF).mono (fun x hx => ⟨hacs hx, hx.1, hx.2.trans hcb⟩)
  rcases hcb.eq_or_lt with hcb' | hcb'
  · rw [← hcb'] at hab ⊢
    exact hLac
  · have hcover : Icc c b ⊆ ⋃ i ∈ F.erase j, s i := by
      have hIoc : Ioc c b ⊆ ⋃ i ∈ F.erase j, s i := by
        intro x hx
        have hxab : x ∈ Icc a b := ⟨hac.trans hx.1.le, hx.2⟩
        have := hcov hxab
        simp only [mem_iUnion] at this ⊢
        obtain ⟨i, hiF, hxi⟩ := this
        refine ⟨i, Finset.mem_erase.2 ⟨?_, hiF⟩, hxi⟩
        rintro rfl
        have : x ≤ c := le_csSup hTc.bddAbove ⟨hxi, hxab⟩
        exact absurd hx.1 (not_lt.2 this)
      have hcl : IsClosed (⋃ i ∈ F.erase j, s i) := isClosed_biUnion_finset fun i _ => hs i
      have := closure_minimal hIoc hcl
      rw [closure_Ioc hcb'.ne] at this
      exact this
    have hLcb : LipschitzOnWith K f (Icc c b) :=
      ih (F.erase j) (Finset.erase_ssubset hjF) hcb'.le hcover
        (fun i hi => (hK i (Finset.mem_of_mem_erase hi)).mono
          (inter_subset_inter_right _ (Icc_subset_Icc hac le_rfl)))
    exact lipschitzOnWith_Icc_union hLac hLcb hac hcb'.le

/-- **Gluing on a convex set.** A function on a convex set `U`, `K`-Lipschitz on each of
finitely many closed convex sets covering `U`, is `K`-Lipschitz on `U`. -/
theorem lipschitzOnWith_of_convex_cover {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (F : Finset ι) (T : ι → Set E) {U : Set E} {f : E → ℝ} {K : NNReal}
    (hU : Convex ℝ U) (hT : ∀ i, IsClosed (T i)) (hTc : ∀ i, Convex ℝ (T i))
    (hcov : U ⊆ ⋃ i ∈ F, T i)
    (hK : ∀ i ∈ F, LipschitzOnWith K f (T i ∩ U)) : LipschitzOnWith K f U := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  set φ : ℝ → ℝ := fun s => f (x + s • (y - x)) with hφ
  have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • (y - x) ∈ U := by
    intro s hs
    have := hU hx hy (sub_nonneg.2 hs.2) hs.1 (by ring)
    convert this using 1
    simp only [smul_sub]; module
  set S : ι → Set ℝ := fun i => {s | x + s • (y - x) ∈ T i} with hS
  have hl : Continuous fun s : ℝ => x + s • (y - x) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hSc : ∀ i, IsClosed (S i) := fun i => (hT i).preimage hl
  have hSo : ∀ i, (S i).OrdConnected := by
    intro i
    have : S i = (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E) ⁻¹' T i := by
      ext s
      simp only [hS, mem_ofPred_eq, mem_preimage, AffineMap.lineMap_apply, vsub_eq_sub,
        vadd_eq_add]
      rw [add_comm]
    rw [this]
    exact convex_iff_ordConnected.1 ((hTc i).affine_preimage _)
  have hcov' : Icc (0 : ℝ) 1 ⊆ ⋃ i ∈ F, S i := by
    intro s hs
    have := hcov (hseg s hs)
    simpa [hS] using this
  have hlip : ∀ i ∈ F, LipschitzOnWith (K * ‖y - x‖₊) φ (S i ∩ Icc 0 1) := by
    intro i hi
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
    have := (hK i hi).dist_le_mul _ ⟨hs.1, hseg s hs.2⟩ _ ⟨ht.1, hseg t ht.2⟩
    have e : dist (x + s • (y - x)) (x + t • (y - x)) = dist s t * ‖y - x‖ := by
      rw [dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
        Real.norm_eq_abs]
    rw [e] at this
    simpa [hφ, mul_assoc, mul_comm, mul_left_comm] using this
  have hmain := lipschitzOnWith_Icc_of_cover F S hSc hSo zero_le_one hcov' hlip
  have := hmain.dist_le_mul 1 ⟨zero_le_one, le_rfl⟩ 0 ⟨le_rfl, zero_le_one⟩
  simp only [hφ, one_smul, zero_smul, add_zero, add_sub_cancel, Real.dist_eq, sub_zero,
    abs_one, mul_one, NNReal.coe_mul, coe_nnnorm] at this
  rw [Real.dist_eq, dist_eq_norm, norm_sub_rev]
  rw [abs_sub_comm]
  exact this

end Dual

end SandierSerfaty

end
