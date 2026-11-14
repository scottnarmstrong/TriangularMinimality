/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The one-dimensional mass profile and the slab integrals (sphere note, Definition 5.3, Lemma 5.4)

In the Mercator height `t`, the uniform measure of total mass `n` on `S²` projects to
`ν(dt) = ϱ(t) dt` with `ϱ(t) = (n/2) sech² t` and distribution function `Φ(t) = (n/2)(1 + tanh t)`
(Definition 5.3).

* `Sphere.ringMass` (`Φ`), `Sphere.ringDensity` (`ϱ`), `Sphere.ringQuantile` (`τ`, the inverse of `Φ`);
* `Sphere.cellPrimitive n α`: `P(α, u) = α² u + n α log cosh u + (n²/4)(u - tanh u)`, a primitive of
  `(α + (n/2) tanh u)²`; with `α = n/2 - c` this is `(Φ - c)²` (`Sphere.hasDerivAt_cellPrimitive`);
* `Sphere.cellBoundary n c`: the value of `P(n/2 - c, ·)` at the point `τ(c)` of mass `c` (the limits at
  `∓∞` for `c = 0, n`);
* `Sphere.integral_slab`: for `0 ≤ c < d ≤ n` and `c ≤ Φ(s) ≤ d`, the integral over the mass slab
  `{c ≤ Φ ≤ d}` of `((d - c) 1_{t ≥ s} - (Φ(t) - c))²` is
  `P(n/2 - c, s) - P(n/2 - d, s) + cellBoundary n d - cellBoundary n c`.

These explicit primitives replace the measure-theoretic Lemma 5.4 in the proof of Proposition 5.5.
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty

namespace Sphere

/-- `Φ(t) = (n/2)(1 + tanh t)`, the `ν`-mass of `(-∞, t]` (Definition 5.3). -/
@[expose] noncomputable def ringMass (n t : ℝ) : ℝ := n / 2 * (1 + Real.tanh t)

/-- `ϱ(t) = (n/2) sech² t`, the density of `ν` (Definition 5.3). -/
@[expose] noncomputable def ringDensity (n t : ℝ) : ℝ := n / 2 / Real.cosh t ^ 2

/-- `τ(a) = ½ log(a / (n - a))`, the inverse of `Φ` on `(0, n)` (Definition 5.3). -/
@[expose] noncomputable def ringQuantile (n a : ℝ) : ℝ := Real.log (a / (n - a)) / 2

/-- `P(α, u) = α² u + n α log cosh u + (n²/4)(u - tanh u)`. -/
@[expose] noncomputable def cellPrimitive (n α u : ℝ) : ℝ :=
  α ^ 2 * u + n * α * Real.log (Real.cosh u) + n ^ 2 / 4 * (u - Real.tanh u)

/-- The boundary value of `P(n/2 - c, ·)` at mass `c`: `P(n/2 - c, τ(c))` for `0 < c < n`, and the
limits `n²/4 - (n²/2) log 2` at `-∞` (`c = 0`) and `(n²/2) log 2 - n²/4` at `+∞` (`c = n`). -/
@[expose] noncomputable def cellBoundary (n c : ℝ) : ℝ :=
  if c = 0 then n ^ 2 / 4 - n ^ 2 / 2 * Real.log 2
  else if c = n then n ^ 2 / 2 * Real.log 2 - n ^ 2 / 4
  else cellPrimitive n (n / 2 - c) (ringQuantile n c)

theorem one_add_tanh (t : ℝ) : 1 + Real.tanh t = 2 / (1 + Real.exp (-(2 * t))) := by
  have hE := Real.exp_pos t
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, show -(2 * t) = -t + -t by ring,
    Real.exp_add, Real.exp_neg]
  field_simp
  ring

theorem ringMass_eq (n t : ℝ) : ringMass n t = n / (1 + Real.exp (-(2 * t))) := by
  rw [ringMass, one_add_tanh]
  ring

theorem continuous_ringMass (n : ℝ) : Continuous (ringMass n) := by
  have : ringMass n = fun t => n / (1 + Real.exp (-(2 * t))) := funext (ringMass_eq n)
  rw [this]
  exact continuous_const.div (by fun_prop) fun t => (by positivity)

theorem ringMass_strictMono {n : ℝ} (hn : 0 < n) : StrictMono (ringMass n) := by
  intro t t' h
  rw [ringMass_eq, ringMass_eq]
  apply div_lt_div_of_pos_left hn (by positivity)
  have : Real.exp (-(2 * t')) < Real.exp (-(2 * t)) := Real.exp_lt_exp.2 (by linarith)
  linarith

theorem ringMass_pos {n : ℝ} (hn : 0 < n) (t : ℝ) : 0 < ringMass n t := by
  rw [ringMass_eq]; positivity

theorem ringMass_lt {n : ℝ} (hn : 0 < n) (t : ℝ) : ringMass n t < n := by
  rw [ringMass_eq, div_lt_iff₀ (by positivity)]
  have := Real.exp_pos (-(2 * t))
  nlinarith

theorem ringMass_quantile {n a : ℝ} (ha : 0 < a) (han : a < n) : ringMass n (ringQuantile n a) = a := by
  rw [ringMass_eq, ringQuantile, show -(2 * (Real.log (a / (n - a)) / 2)) = -Real.log (a / (n - a)) by
    ring, Real.exp_neg, Real.exp_log (div_pos ha (by linarith))]
  have : n - a ≠ 0 := by linarith
  field_simp
  ring

theorem le_ringMass_iff {n a : ℝ} (ha : 0 < a) (han : a < n) (t : ℝ) :
    a ≤ ringMass n t ↔ ringQuantile n a ≤ t := by
  conv_lhs => rw [← ringMass_quantile ha han]
  exact (ringMass_strictMono (by linarith)).le_iff_le

theorem ringMass_le_iff {n a : ℝ} (ha : 0 < a) (han : a < n) (t : ℝ) :
    ringMass n t ≤ a ↔ t ≤ ringQuantile n a := by
  conv_lhs => rw [← ringMass_quantile ha han]
  exact (ringMass_strictMono (by linarith)).le_iff_le

/-! ### The primitive -/

theorem hasDerivAt_cellPrimitive (n c u : ℝ) :
    HasDerivAt (cellPrimitive n (n / 2 - c)) ((ringMass n u - c) ^ 2) u := by
  have hc := Real.cosh_pos u
  have hP : cellPrimitive n (n / 2 - c) = fun u => (n / 2 - c) ^ 2 * u +
      n * (n / 2 - c) * Real.log (Real.cosh u) + n ^ 2 / 4 * (u - Real.sinh u / Real.cosh u) := by
    funext u; rw [cellPrimitive, Real.tanh_eq_sinh_div_cosh]
  rw [hP]
  have h1 := (Real.hasDerivAt_cosh u).log hc.ne'
  have h2 := (Real.hasDerivAt_sinh u).div (Real.hasDerivAt_cosh u) hc.ne'
  have h := (((hasDerivAt_id u).const_mul ((n / 2 - c) ^ 2)).add (h1.const_mul (n * (n / 2 - c)))).add
    (((hasDerivAt_id u).sub h2).const_mul (n ^ 2 / 4))
  refine h.congr_deriv ?_
  have hcs := Real.cosh_sq u
  have e1 : Real.cosh u * Real.cosh u - Real.sinh u * Real.sinh u = 1 := by nlinarith
  have e2 : 1 - 1 / Real.cosh u ^ 2 = (Real.sinh u / Real.cosh u) ^ 2 := by
    field_simp; linarith
  rw [e1, e2, ringMass, Real.tanh_eq_sinh_div_cosh]
  ring

theorem cellPrimitive_neg (n α u : ℝ) : cellPrimitive n α (-u) = -cellPrimitive n (-α) u := by
  simp only [cellPrimitive, Real.cosh_neg, Real.tanh_neg]
  ring

theorem tendsto_cellPrimitive_atTop (n : ℝ) :
    Tendsto (cellPrimitive n (-(n / 2))) atTop (𝓝 (n ^ 2 / 2 * Real.log 2 - n ^ 2 / 4)) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop two_pos))
  have hform : ∀ u : ℝ, cellPrimitive n (-(n / 2)) u =
      n ^ 2 / 2 * -Real.log ((1 + Real.exp (-(2 * u))) / 2) -
        n ^ 2 / 4 * ((1 - Real.exp (-(2 * u))) / (1 + Real.exp (-(2 * u)))) := by
    intro u
    have hE := Real.exp_pos u
    have hcosh : Real.cosh u = Real.exp u * ((1 + Real.exp (-(2 * u))) / 2) := by
      rw [Real.cosh_eq, Real.exp_neg, Real.exp_neg, show 2 * u = u + u by ring, Real.exp_add]
      field_simp
    have htanh : Real.tanh u = (1 - Real.exp (-(2 * u))) / (1 + Real.exp (-(2 * u))) := by
      have := one_add_tanh u
      have hpos : 0 < 1 + Real.exp (-(2 * u)) := by positivity
      field_simp at this ⊢
      linarith
    rw [cellPrimitive, htanh, hcosh, Real.log_mul hE.ne' (by positivity), Real.log_exp]
    ring
  rw [show cellPrimitive n (-(n / 2)) = fun u => n ^ 2 / 2 * -Real.log ((1 + Real.exp (-(2 * u))) / 2) -
      n ^ 2 / 4 * ((1 - Real.exp (-(2 * u))) / (1 + Real.exp (-(2 * u)))) from funext hform]
  have hlim : n ^ 2 / 2 * Real.log 2 - n ^ 2 / 4 =
      n ^ 2 / 2 * -Real.log ((1 + 0) / 2) - n ^ 2 / 4 * ((1 - 0) / (1 + 0)) := by
    rw [add_zero, sub_zero, div_one, one_div, Real.log_inv]
    ring
  rw [hlim]
  refine Tendsto.sub (Tendsto.const_mul _ (Tendsto.neg ?_)) (Tendsto.const_mul _ ?_)
  · exact ((he.const_add 1).div_const 2).log (by norm_num)
  · exact (tendsto_const_nhds.sub he).div (he.const_add 1) (by norm_num)

theorem tendsto_cellPrimitive_atBot (n : ℝ) :
    Tendsto (cellPrimitive n (n / 2)) atBot (𝓝 (n ^ 2 / 4 - n ^ 2 / 2 * Real.log 2)) := by
  have h := ((tendsto_cellPrimitive_atTop n).comp tendsto_neg_atBot_atTop).neg
  have hv : -(n ^ 2 / 2 * Real.log 2 - n ^ 2 / 4) = n ^ 2 / 4 - n ^ 2 / 2 * Real.log 2 := by ring
  rw [hv] at h
  refine h.congr fun u => ?_
  show -(cellPrimitive n (-(n / 2)) (-u)) = _
  rw [cellPrimitive_neg, neg_neg, neg_neg]

/-! ### Improper integrals of nonnegative derivatives on `(-∞, a]` -/

theorem integrableOn_Iic_of_hasDerivAt_of_nonneg {g g' : ℝ → ℝ} {l : ℝ} (a : ℝ)
    (hderiv : ∀ x, HasDerivAt g (g' x) x) (hpos : ∀ x, 0 ≤ g' x) (hg : Tendsto g atBot (𝓝 l)) :
    IntegrableOn g' (Iic a) := by
  have h1 : IntegrableOn (fun x => g' (-x)) (Ioi (-a)) := by
    refine integrableOn_Ioi_deriv_of_nonneg' (g := fun x => -g (-x)) (l := -l)
      (fun x _ => ?_) (fun x _ => hpos _) ?_
    · have h2 := ((hderiv (-x)).comp x (hasDerivAt_neg x)).neg
      convert h2 using 1
      · funext y; simp
      · ring
    · exact (hg.comp tendsto_neg_atTop_atBot).neg
  have e := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (Homeomorph.neg ℝ).measurableEmbedding (f := g') (s := Iic a)
  rw [← e]
  have hpre : (Neg.neg ⁻¹' Iic a : Set ℝ) = Ici (-a) := by
    ext x; simp
  rw [hpre, integrableOn_Ici_iff_integrableOn_Ioi]
  exact h1

/-! ### The half-slab integrals -/

theorem continuous_cellIntegrand (n c : ℝ) : Continuous fun t => (ringMass n t - c) ^ 2 :=
  ((continuous_ringMass n).sub continuous_const).pow 2

/-- The left half-slab: for `0 ≤ c < n` and `c ≤ Φ(s)`,
`∫_{{c ≤ Φ} ∩ (-∞, s)} (Φ - c)² = P(n/2 - c, s) - cellBoundary n c`. -/
theorem integral_left {n c s : ℝ} (hn : 0 < n) (hc0 : 0 ≤ c) (hcn : c < n)
    (hs : c ≤ ringMass n s) :
    IntegrableOn (fun t => (ringMass n t - c) ^ 2) ({t | c ≤ ringMass n t} ∩ Iio s) ∧
      ∫ t in {t | c ≤ ringMass n t} ∩ Iio s, (ringMass n t - c) ^ 2 =
        cellPrimitive n (n / 2 - c) s - cellBoundary n c := by
  rcases hc0.eq_or_lt with rfl | hc0
  · have hset : {t | (0 : ℝ) ≤ ringMass n t} ∩ Iio s = Iio s := by
      ext t; simp [(ringMass_pos hn t).le]
    rw [hset, cellBoundary, ite_eq_left rfl, sub_zero]
    have hint : IntegrableOn (fun t => (ringMass n t - 0) ^ 2) (Iic s) :=
      integrableOn_Iic_of_hasDerivAt_of_nonneg s (fun x => hasDerivAt_cellPrimitive n 0 x)
        (fun x => sq_nonneg _) (by simpa using tendsto_cellPrimitive_atBot n)
    refine ⟨hint.mono_set Iio_subset_Iic_self, ?_⟩
    rw [← integral_Iic_eq_integral_Iio,
      integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hasDerivAt_cellPrimitive n 0 x) hint
        (by simpa using tendsto_cellPrimitive_atBot n)]
    simp
  · have hτ : ringQuantile n c ≤ s := (le_ringMass_iff hc0 hcn s).1 hs
    have hset : {t | c ≤ ringMass n t} ∩ Iio s = Ico (ringQuantile n c) s := by
      ext t; simp [le_ringMass_iff hc0 hcn t, and_comm]
    rw [hset, cellBoundary, ite_eq_right hc0.ne', ite_eq_right hcn.ne]
    refine ⟨(continuous_cellIntegrand n c).integrableOn_Icc.mono_set Ico_subset_Icc_self, ?_⟩
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_cellPrimitive n c x)
        ((continuous_cellIntegrand n c).intervalIntegrable _ _)]

/-- The right half-slab: for `0 < d ≤ n` and `Φ(s) ≤ d`,
`∫_{{Φ ≤ d} ∩ [s, ∞)} (Φ - d)² = cellBoundary n d - P(n/2 - d, s)`. -/
theorem integral_right {n d s : ℝ} (hn : 0 < n) (hd0 : 0 < d) (hdn : d ≤ n)
    (hs : ringMass n s ≤ d) :
    IntegrableOn (fun t => (ringMass n t - d) ^ 2) ({t | ringMass n t ≤ d} ∩ Ici s) ∧
      ∫ t in {t | ringMass n t ≤ d} ∩ Ici s, (ringMass n t - d) ^ 2 =
        cellBoundary n d - cellPrimitive n (n / 2 - d) s := by
  rcases hdn.eq_or_lt with rfl | hdn
  · have hset : {t | ringMass d t ≤ d} ∩ Ici s = Ici s := by
      ext t; simp [(ringMass_lt hn t).le]
    rw [hset, cellBoundary, ite_eq_right hd0.ne', ite_eq_left rfl]
    have hlim : Tendsto (cellPrimitive d (d / 2 - d)) atTop
        (𝓝 (d ^ 2 / 2 * Real.log 2 - d ^ 2 / 4)) := by
      rw [show d / 2 - d = -(d / 2) by ring]; exact tendsto_cellPrimitive_atTop d
    have hint : IntegrableOn (fun t => (ringMass d t - d) ^ 2) (Ioi s) :=
      integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_cellPrimitive d d x)
        (fun x _ => sq_nonneg _) hlim
    refine ⟨by rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hint, ?_⟩
    rw [integral_Ici_eq_integral_Ioi,
      integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hasDerivAt_cellPrimitive d d x)
        (fun x _ => sq_nonneg _) hlim]
  · have hτ : s ≤ ringQuantile n d := (ringMass_le_iff hd0 hdn s).1 hs
    have hset : {t | ringMass n t ≤ d} ∩ Ici s = Icc s (ringQuantile n d) := by
      ext t; simp [ringMass_le_iff hd0 hdn t, and_comm]
    rw [hset, cellBoundary, ite_eq_right hd0.ne', ite_eq_right hdn.ne]
    refine ⟨(continuous_cellIntegrand n d).integrableOn_Icc, ?_⟩
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_cellPrimitive n d x)
        ((continuous_cellIntegrand n d).intervalIntegrable _ _)]

/-- **The slab integral.** For `0 ≤ c < d ≤ n` and `c ≤ Φ(s) ≤ d`, the integral over the mass slab
`{c ≤ Φ ≤ d}` of `((d - c) 1_{t ≥ s} - (Φ(t) - c))²` equals
`P(n/2 - c, s) - P(n/2 - d, s) + cellBoundary n d - cellBoundary n c`. -/
theorem integral_slab {n c d s : ℝ} (hn : 0 < n) (hc0 : 0 ≤ c) (hcd : c < d) (hdn : d ≤ n)
    (hs1 : c ≤ ringMass n s) (hs2 : ringMass n s ≤ d) :
    ∫ t in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d},
        ((if s ≤ t then d - c else 0) - (ringMass n t - c)) ^ 2 =
      cellPrimitive n (n / 2 - c) s - cellPrimitive n (n / 2 - d) s + cellBoundary n d -
        cellBoundary n c := by
  have hmono := ringMass_strictMono hn
  set S1 := {t | c ≤ ringMass n t} ∩ Iio s
  set S2 := {t | ringMass n t ≤ d} ∩ Ici s
  have hS1 : MeasurableSet S1 :=
    (measurableSet_le measurable_const (continuous_ringMass n).measurable).inter measurableSet_Iio
  have hS2 : MeasurableSet S2 :=
    (measurableSet_le (continuous_ringMass n).measurable measurable_const).inter measurableSet_Ici
  have hunion : {t | c ≤ ringMass n t ∧ ringMass n t ≤ d} = S1 ∪ S2 := by
    ext t
    simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_Iio, mem_Ici, S1, S2]
    rcases lt_or_ge t s with h | h
    · have : ringMass n t ≤ d := (hmono h).le.trans hs2
      constructor
      · intro h'; exact Or.inl ⟨h'.1, h⟩
      · rintro (h' | h')
        · exact ⟨h'.1, this⟩
        · exact absurd h'.2 (not_le.2 h)
    · have : c ≤ ringMass n t := hs1.trans (hmono.monotone h)
      constructor
      · intro h'; exact Or.inr ⟨h'.2, h⟩
      · rintro (h' | h')
        · exact absurd h'.2 (not_lt.2 h)
        · exact ⟨this, h'.1⟩
  have hdisj : Disjoint S1 S2 := by
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2.2 (not_le.2 h1.2)
  have heq1 : EqOn (fun t => ((if s ≤ t then d - c else 0) - (ringMass n t - c)) ^ 2)
      (fun t => (ringMass n t - c) ^ 2) S1 := by
    intro t ht
    simp only [ite_eq_right (not_le.2 ht.2)]
    ring
  have heq2 : EqOn (fun t => ((if s ≤ t then d - c else 0) - (ringMass n t - c)) ^ 2)
      (fun t => (ringMass n t - d) ^ 2) S2 := by
    intro t ht
    simp only [ite_eq_left (show s ≤ t from ht.2)]
    ring
  obtain ⟨hi1, he1⟩ := integral_left hn hc0 (hcd.trans_le hdn) hs1
  obtain ⟨hi2, he2⟩ := integral_right hn (hc0.trans_lt hcd) hdn hs2
  rw [hunion, setIntegral_union hdisj hS2 (hi1.congr_fun heq1.symm hS1)
    (hi2.congr_fun heq2.symm hS2), setIntegral_congr_fun hS1 heq1,
    setIntegral_congr_fun hS2 heq2, he1, he2]
  ring

end Sphere

end SandierSerfaty

end
