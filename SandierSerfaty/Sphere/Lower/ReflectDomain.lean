/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Lower.ReflectBasic
public import SandierSerfaty.Torus.Lattice
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# A box fundamental domain and the four-quadrant decomposition (sphere note, Lemma 6.2(iii), geometry)

* `Lower.isAddFundamentalDomain_box`: `[c.re, c.re + √n) × [c.im, c.im + √n)` is a fundamental domain of
  `squareLattice n` for Lebesgue measure;
* `Lower.openSq b s`: the open quadrant `b + (0, s)²`;
* `Lower.lintegral_box_eq_four`: for `G` invariant under the reflections `reflX b.re` and `reflY b.im`,
  the integral over the box `b + [-s, s)²` is four times the integral over `openSq b s`
  (the box is, up to null lines, the disjoint union of `openSq` and its three reflections).
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

open Torus

section Box

/-- The box `[c.re, c.re + w) × [c.im, c.im + w)`. -/
@[expose] def boxAt (c : ℂ) (w : ℝ) : Set ℂ :=
  {x | c.re ≤ x.re ∧ x.re < c.re + w ∧ c.im ≤ x.im ∧ x.im < c.im + w}

theorem measurableSet_boxAt (c : ℂ) (w : ℝ) : MeasurableSet (boxAt c w) := by
  have : boxAt c w = (Complex.re ⁻¹' Ico c.re (c.re + w)) ∩ (Complex.im ⁻¹' Ico c.im (c.im + w)) := by
    ext x; simp [boxAt, and_assoc]
  rw [this]
  exact (measurableSet_Ico.preimage Complex.measurable_re).inter
    (measurableSet_Ico.preimage Complex.measurable_im)

theorem isAddFundamentalDomain_box {n : ℕ} (hn : 1 ≤ n) (c : ℂ) :
    IsAddFundamentalDomain (squareLattice n) (boxAt c (√n)) volume := by
  have hw : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  set w := √(n : ℝ) with hwdef
  refine IsAddFundamentalDomain.mk' (measurableSet_boxAt c w).nullMeasurableSet ?_
  intro x
  have key : ∀ (p q : ℤ), ((⟨p * w, q * w⟩ : ℂ) + x ∈ boxAt c w ↔
      p = -⌊(x.re - c.re) / w⌋ ∧ q = -⌊(x.im - c.im) / w⌋) := by
    intro p q
    simp only [boxAt, mem_ofPred_eq, Complex.add_re, Complex.add_im]
    have e1 : p = -⌊(x.re - c.re) / w⌋ ↔ (c.re ≤ p * w + x.re ∧ p * w + x.re < c.re + w) := by
      rw [show ∀ (p z : ℤ), p = -z ↔ z = -p from fun p z => by omega, Int.floor_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        push_cast at h1 h2
        rw [le_div_iff₀ hw] at h1
        rw [div_lt_iff₀ hw] at h2
        constructor <;> nlinarith
      · rintro ⟨h1, h2⟩
        push_cast
        rw [le_div_iff₀ hw, div_lt_iff₀ hw]
        constructor <;> nlinarith
    have e2 : q = -⌊(x.im - c.im) / w⌋ ↔ (c.im ≤ q * w + x.im ∧ q * w + x.im < c.im + w) := by
      rw [show ∀ (p z : ℤ), p = -z ↔ z = -p from fun p z => by omega, Int.floor_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩
        push_cast at h1 h2
        rw [le_div_iff₀ hw] at h1
        rw [div_lt_iff₀ hw] at h2
        constructor <;> nlinarith
      · rintro ⟨h1, h2⟩
        push_cast
        rw [le_div_iff₀ hw, div_lt_iff₀ hw]
        constructor <;> nlinarith
    rw [e1, e2]
    tauto
  refine ⟨⟨⟨(-⌊(x.re - c.re) / w⌋ : ℤ) * w, (-⌊(x.im - c.im) / w⌋ : ℤ) * w⟩,
    mk_mem_squareLattice _ _⟩, ?_, ?_⟩
  · exact (key _ _).2 ⟨rfl, rfl⟩
  · rintro ⟨g, hg⟩ hgx
    obtain ⟨p, q, rfl⟩ := mem_squareLattice_iff.1 hg
    have := (key p q).1 hgx
    obtain ⟨rfl, rfl⟩ := this
    rfl

end Box

section Quadrants

/-- The open quadrant `b + (0, s)²`. -/
@[expose] def openSq (b : ℂ) (s : ℝ) : Set ℂ :=
  {x | b.re < x.re ∧ x.re < b.re + s ∧ b.im < x.im ∧ x.im < b.im + s}

theorem measurableSet_openSq (b : ℂ) (s : ℝ) : MeasurableSet (openSq b s) := by
  have : openSq b s = (Complex.re ⁻¹' Ioo b.re (b.re + s)) ∩ (Complex.im ⁻¹' Ioo b.im (b.im + s)) := by
    ext x; simp [openSq, and_assoc]
  rw [this]
  exact (measurableSet_Ioo.preimage Complex.measurable_re).inter
    (measurableSet_Ioo.preimage Complex.measurable_im)

variable (b : ℂ) (s : ℝ)

/-- The four quadrants of the box `b + [-s, s)²`. -/
def quadX : Set ℂ := reflX b.re ⁻¹' openSq b s
def quadY : Set ℂ := reflY b.im ⁻¹' openSq b s
def quadXY : Set ℂ := reflY b.im ⁻¹' quadX b s

theorem mem_quadX {x : ℂ} : x ∈ quadX b s ↔
    b.re - s < x.re ∧ x.re < b.re ∧ b.im < x.im ∧ x.im < b.im + s := by
  simp only [quadX, openSq, mem_preimage, mem_ofPred_eq, reflX_re, reflX_im]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, h3, h4⟩ <;> linarith

theorem mem_quadY {x : ℂ} : x ∈ quadY b s ↔
    b.re < x.re ∧ x.re < b.re + s ∧ b.im - s < x.im ∧ x.im < b.im := by
  simp only [quadY, openSq, mem_preimage, mem_ofPred_eq, reflY_re, reflY_im]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨h1, h2, ?_, ?_⟩ <;> linarith

theorem mem_quadXY {x : ℂ} : x ∈ quadXY b s ↔
    b.re - s < x.re ∧ x.re < b.re ∧ b.im - s < x.im ∧ x.im < b.im := by
  simp only [quadXY, mem_preimage, mem_quadX, reflY_re, reflY_im]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨h1, h2, ?_, ?_⟩ <;> linarith

theorem measurableSet_quadX : MeasurableSet (quadX b s) :=
  (measurableEmbedding_reflX b.re).measurable (measurableSet_openSq b s)

theorem measurableSet_quadY : MeasurableSet (quadY b s) :=
  (measurableEmbedding_reflY b.im).measurable (measurableSet_openSq b s)

theorem measurableSet_quadXY : MeasurableSet (quadXY b s) :=
  (measurableEmbedding_reflY b.im).measurable (measurableSet_quadX b s)

/-- The box `b + [-s, s)²` is the union of the four quadrants up to null lines. -/
theorem boxAt_ae_eq (_hs : 0 < s) :
    boxAt (b - ⟨s, s⟩) (2 * s) =ᵐ[volume] (openSq b s ∪ quadX b s ∪ quadY b s ∪ quadXY b s) := by
  rw [ae_eq_set]
  constructor
  · have hsub : boxAt (b - ⟨s, s⟩) (2 * s) \ (openSq b s ∪ quadX b s ∪ quadY b s ∪ quadXY b s) ⊆
        ({x : ℂ | x.re = b.re} ∪ {x : ℂ | x.im = b.im}) ∪
          ({x : ℂ | x.re = b.re - s} ∪ {x : ℂ | x.im = b.im - s}) := by
      intro x ⟨hx, hn⟩
      simp only [boxAt, mem_ofPred_eq, Complex.sub_re, Complex.sub_im] at hx
      by_contra hc
      simp only [mem_union, mem_ofPred_eq, not_or] at hc
      obtain ⟨⟨hre, him⟩, hre', him'⟩ := hc
      have hre'' : b.re - s < x.re := lt_of_le_of_ne hx.1 (Ne.symm hre')
      have him'' : b.im - s < x.im := lt_of_le_of_ne hx.2.2.1 (Ne.symm him')
      apply hn
      simp only [mem_union, openSq, mem_quadX, mem_quadY, mem_quadXY, mem_ofPred_eq]
      rcases lt_or_gt_of_ne hre with h1 | h1 <;> rcases lt_or_gt_of_ne him with h2 | h2
      · exact Or.inr ⟨hre'', h1, him'', h2⟩
      · exact Or.inl (Or.inl (Or.inr ⟨hre'', h1, h2, by linarith [hx.2.2.2]⟩))
      · exact Or.inl (Or.inr ⟨h1, by linarith [hx.2.1], him'', h2⟩)
      · exact Or.inl (Or.inl (Or.inl ⟨h1, by linarith [hx.2.1], h2, by linarith [hx.2.2.2]⟩))
    exact measure_mono_null hsub (measure_union_null
      (measure_union_null (volume_re_eq _) (volume_im_eq _))
      (measure_union_null (volume_re_eq _) (volume_im_eq _)))
  · have : (openSq b s ∪ quadX b s ∪ quadY b s ∪ quadXY b s) \ boxAt (b - ⟨s, s⟩) (2 * s) = ∅ := by
      ext x
      simp only [mem_sdiff, mem_union, openSq, mem_quadX, mem_quadY, mem_quadXY, boxAt, mem_ofPred_eq,
        Complex.sub_re, Complex.sub_im, mem_empty_iff_false, iff_false]
      rintro ⟨(((h | h) | h) | h), hn⟩ <;> apply hn <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]
    rw [this]; exact measure_empty

theorem lintegral_box_eq_four (hs : 0 < s) {G : ℂ → ENNReal}
    (hX : ∀ x, G (reflX b.re x) = G x) (hY : ∀ x, G (reflY b.im x) = G x) :
    ∫⁻ x in boxAt (b - ⟨s, s⟩) (2 * s), G x = 4 * ∫⁻ x in openSq b s, G x := by
  rw [setLIntegral_congr (boxAt_ae_eq b s hs)]
  have dX : Disjoint (openSq b s) (quadX b s) := by
    rw [Set.disjoint_left]; intro x h1 h2
    rw [mem_quadX] at h2; simp only [openSq, mem_ofPred_eq] at h1; linarith [h1.1, h2.2.1]
  have dY : Disjoint (openSq b s ∪ quadX b s) (quadY b s) := by
    rw [Set.disjoint_left]; intro x h1 h2
    rw [mem_quadY] at h2
    rcases h1 with h1 | h1
    · simp only [openSq, mem_ofPred_eq] at h1; linarith [h1.2.2.1, h2.2.2.2]
    · rw [mem_quadX] at h1; linarith [h1.2.2.1, h2.2.2.2]
  have dXY : Disjoint (openSq b s ∪ quadX b s ∪ quadY b s) (quadXY b s) := by
    rw [Set.disjoint_left]; intro x h1 h2
    rw [mem_quadXY] at h2
    rcases h1 with (h1 | h1) | h1
    · simp only [openSq, mem_ofPred_eq] at h1; linarith [h1.2.2.1, h2.2.2.2]
    · rw [mem_quadX] at h1; linarith [h1.2.2.1, h2.2.2.2]
    · rw [mem_quadY] at h1; linarith [h1.1, h2.2.1]
  rw [lintegral_union (measurableSet_quadXY b s) dXY, lintegral_union (measurableSet_quadY b s) dY,
    lintegral_union (measurableSet_quadX b s) dX]
  have hQX : ∫⁻ x in quadX b s, G x = ∫⁻ x in openSq b s, G x := by
    have := (measurePreserving_reflX b.re).setLIntegral_comp_preimage_emb
      (measurableEmbedding_reflX b.re) G (openSq b s)
    simpa only [quadX, hX] using this
  have hQY : ∫⁻ x in quadY b s, G x = ∫⁻ x in openSq b s, G x := by
    have := (measurePreserving_reflY b.im).setLIntegral_comp_preimage_emb
      (measurableEmbedding_reflY b.im) G (openSq b s)
    simpa only [quadY, hY] using this
  have hQXY : ∫⁻ x in quadXY b s, G x = ∫⁻ x in openSq b s, G x := by
    have := (measurePreserving_reflY b.im).setLIntegral_comp_preimage_emb
      (measurableEmbedding_reflY b.im) G (quadX b s)
    simpa only [quadXY, hY] using this.trans hQX
  rw [hQX, hQY, hQXY]
  ring

end Quadrants

end Lower

end Sphere

end SandierSerfaty

end
