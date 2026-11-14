/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Rectangles as fundamental domains of lattices `p (ℤ + ℤ τ)`

* `SandierSerfaty.ClosedForm.isAddFundamentalDomain_rect`: for `p > 0` and `Im τ > 0`, the rectangle
  `[0, p) × [0, p Im τ)` is a fundamental domain (for Lebesgue measure on `ℂ`) of the lattice
  `Γ = {p (m + n τ)}`, for any `Γ : Submodule ℤ ℂ` with that description.
* `SandierSerfaty.ClosedForm.setIntegral_re_im`: Fubini for a product of two real sets in the
  coordinates `(Re z, Im z)`, integrating first in `Re z`.
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace ClosedForm

/-- Fubini on `{z | Re z ∈ S ∧ Im z ∈ T}`, integrating first in the real part. -/
theorem setIntegral_re_im {f : ℂ → ℝ} {S T : Set ℝ}
    (hf : IntegrableOn f {z : ℂ | z.re ∈ S ∧ z.im ∈ T}) :
    ∫ z in {z : ℂ | z.re ∈ S ∧ z.im ∈ T}, f z =
      ∫ y in T, ∫ x in S, f (⟨x, y⟩ : ℂ) := by
  have hmp := Complex.volume_preserving_equiv_real_prod
  have hemb := Complex.measurableEquivRealProd.measurableEmbedding
  have hpre : {z : ℂ | z.re ∈ S ∧ z.im ∈ T} = Complex.measurableEquivRealProd ⁻¹'
      ((S ×ˢ T : Set (ℝ × ℝ))) := by
    ext z; simp [Complex.measurableEquivRealProd]
  set g : ℝ × ℝ → ℝ := fun q => f (Complex.measurableEquivRealProd.symm q) with hg
  have hfg : ∀ z, f z = g (Complex.measurableEquivRealProd z) := by
    intro z; simp [hg]
  have h1 : ∫ z in {z : ℂ | z.re ∈ S ∧ z.im ∈ T}, f z = ∫ q in S ×ˢ T, g q := by
    rw [hpre]
    simp_rw [hfg]
    exact hmp.setIntegral_preimage_emb hemb g _
  have h2 : IntegrableOn g (S ×ˢ T) := by
    rw [hpre] at hf
    have := (hmp.integrableOn_comp_preimage hemb (f := g) (s := S ×ˢ T)).1
    apply this
    convert hf using 1
    funext z; simp [hg]
  have h2' : Integrable g ((volume.restrict S).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]; exact h2
  rw [h1, Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm g h2']
  rfl

/-- The rectangle `[0, p) × [0, p Im τ)` is a fundamental domain of `{p (m + n τ)}`. -/
theorem isAddFundamentalDomain_rect (Γ : Submodule ℤ ℂ) {p : ℝ} (hp : 0 < p) {τ : ℂ}
    (hτ : 0 < τ.im) (hmem : ∀ z, z ∈ Γ ↔ ∃ m n : ℤ, z = p * (m + n * τ)) :
    IsAddFundamentalDomain Γ {z : ℂ | z.re ∈ Ico 0 p ∧ z.im ∈ Ico 0 (p * τ.im)} volume := by
  have hmeas : MeasurableSet {z : ℂ | z.re ∈ Ico 0 p ∧ z.im ∈ Ico 0 (p * τ.im)} :=
    (measurableSet_Ico.preimage Complex.measurable_re).inter
      (measurableSet_Ico.preimage Complex.measurable_im)
  refine IsAddFundamentalDomain.mk' hmeas.nullMeasurableSet fun x => ?_
  have hpb : 0 < p * τ.im := mul_pos hp hτ
  have hre : ∀ m n : ℤ, ((p : ℂ) * (m + n * τ) + x).re = p * (m + n * τ.re) + x.re := by
    intro m n; simp
  have him : ∀ m n : ℤ, ((p : ℂ) * (m + n * τ) + x).im = p * (n * τ.im) + x.im := by
    intro m n; simp
  have hvadd : ∀ g : Γ, g +ᵥ x = (g : ℂ) + x := fun g => rfl
  -- existence
  set n : ℤ := -⌊x.im / (p * τ.im)⌋ with hn
  set m : ℤ := -⌊(x.re + p * (n * τ.re)) / p⌋ with hm
  have hγ : ((p : ℂ) * (m + n * τ)) ∈ Γ := (hmem _).2 ⟨m, n, rfl⟩
  refine ⟨⟨_, hγ⟩, ?_, ?_⟩
  · beta_reduce
    rw [hvadd]
    simp only [mem_ofPred_eq]
    rw [hre, him]
    have h1 := Int.floor_le (x.im / (p * τ.im))
    have h2 := Int.lt_floor_add_one (x.im / (p * τ.im))
    have h3 := Int.floor_le ((x.re + p * (n * τ.re)) / p)
    have h4 := Int.lt_floor_add_one ((x.re + p * (n * τ.re)) / p)
    have e1 : x.im = (x.im / (p * τ.im)) * (p * τ.im) := by field_simp
    have e2 : x.re + p * (n * τ.re) = ((x.re + p * (n * τ.re)) / p) * p := by field_simp
    have hn' : (n : ℝ) = -(⌊x.im / (p * τ.im)⌋ : ℝ) := by rw [hn]; push_cast; ring
    have hm' : (m : ℝ) = -(⌊(x.re + p * (n * τ.re)) / p⌋ : ℝ) := by rw [hm]; push_cast; ring
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hm']
      linarith [mul_nonneg hp.le (sub_nonneg.2 h3)]
    · rw [hm']
      linarith [mul_lt_mul_of_pos_left (sub_lt_iff_lt_add.2 h4) hp]
    · rw [hn']
      linarith [mul_nonneg hpb.le (sub_nonneg.2 h1)]
    · rw [hn']
      linarith [mul_lt_mul_of_pos_left (sub_lt_iff_lt_add.2 h2) hpb]
  · intro g' hg'
    obtain ⟨m', n', hgg⟩ := (hmem g').1 g'.2
    rw [hvadd, hgg] at hg'
    simp only [mem_ofPred_eq] at hg'
    rw [hre, him] at hg'
    obtain ⟨⟨hr0, hr1⟩, hi0, hi1⟩ := hg'
    have e1 : x.im = (x.im / (p * τ.im)) * (p * τ.im) := by field_simp
    have hnn : n' = n := by
      have a1 : 0 ≤ (n' : ℝ) + x.im / (p * τ.im) := by
        by_contra hc
        replace hc := not_le.1 hc
        linarith [mul_neg_of_neg_of_pos hc hpb]
      have a2 : (n' : ℝ) + x.im / (p * τ.im) < 1 := by
        by_contra hc
        replace hc := not_lt.1 hc
        linarith [mul_le_mul_of_nonneg_right hc hpb.le]
      have hfl : ⌊x.im / (p * τ.im)⌋ = -n' :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [hn, hfl]; ring
    subst hnn
    have e2 : x.re + p * (n * τ.re) = ((x.re + p * (n * τ.re)) / p) * p := by field_simp
    have hmm : m' = m := by
      have a1 : 0 ≤ (m' : ℝ) + (x.re + p * (n * τ.re)) / p := by
        by_contra hc
        replace hc := not_le.1 hc
        linarith [mul_neg_of_neg_of_pos hc hp]
      have a2 : (m' : ℝ) + (x.re + p * (n * τ.re)) / p < 1 := by
        by_contra hc
        replace hc := not_lt.1 hc
        linarith [mul_le_mul_of_nonneg_right hc hp.le]
      have hfl : ⌊(x.re + p * (n * τ.re)) / p⌋ = -m' :=
        Int.floor_eq_iff.2 ⟨by push_cast; linarith, by push_cast; linarith⟩
      rw [hm, hfl]; ring
    subst hmm
    exact Subtype.ext hgg

end ClosedForm

end SandierSerfaty

end
