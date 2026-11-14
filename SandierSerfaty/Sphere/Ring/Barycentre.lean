/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Identity
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Slab barycentres lie in the slab interiors; Proposition 5.5 for slab-barycentric configurations

* `Sphere.hasDerivAt_ringMass`: `Φ' = ϱ`; `Sphere.integral_density_slab`: `ν({c ≤ Φ ≤ d}) = d - c`;
* `Sphere.integrable_mul_ringDensity`: `∫ |t| dν < ∞`;
* `Sphere.barycentre_mem_interior`: for `0 ≤ c < d ≤ n`, the `ν`-barycentre `b` of the slab
  `{c ≤ Φ ≤ d}` satisfies `c < Φ(b) < d`;
* `Sphere.RowConfig.configEnergy_eq_ring_of_isSlabBarycentric`: **Proposition 5.5** for every
  slab-barycentric row configuration (any phases).
-/

open MeasureTheory Set Filter Topology

public section

namespace SandierSerfaty

namespace Sphere

theorem continuous_ringDensity (n : ℝ) : Continuous (ringDensity n) :=
  continuous_const.div (Real.continuous_cosh.pow 2) fun t => by have := Real.cosh_pos t; positivity

theorem ringDensity_pos {n : ℝ} (hn : 0 < n) (t : ℝ) : 0 < ringDensity n t := by
  have := Real.cosh_pos t
  unfold ringDensity; positivity

theorem hasDerivAt_ringMass (n t : ℝ) : HasDerivAt (ringMass n) (ringDensity n t) t := by
  have hc := Real.cosh_pos t
  have h2 := (Real.hasDerivAt_sinh t).div (Real.hasDerivAt_cosh t) hc.ne'
  have hfun : ringMass n = fun t => n / 2 * (1 + Real.sinh t / Real.cosh t) := by
    funext t; rw [ringMass, Real.tanh_eq_sinh_div_cosh]
  rw [hfun]
  refine ((h2.const_add 1).const_mul (n / 2)).congr_deriv ?_
  have e1 : Real.cosh t * Real.cosh t - Real.sinh t * Real.sinh t = 1 := by
    nlinarith [Real.cosh_sq t]
  rw [e1, ringDensity]
  ring

theorem tendsto_ringMass_atTop (n : ℝ) : Tendsto (ringMass n) atTop (𝓝 n) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop two_pos))
  rw [show ringMass n = fun t => n / (1 + Real.exp (-(2 * t))) from funext (ringMass_eq n)]
  have h2 : Tendsto (fun t => n / (1 + Real.exp (-(2 * t)))) atTop (𝓝 (n / (1 + 0))) :=
    tendsto_const_nhds.div (he.const_add 1) (by norm_num)
  simpa using h2

theorem tendsto_ringMass_atBot (n : ℝ) : Tendsto (ringMass n) atBot (𝓝 0) := by
  have he : Tendsto (fun u : ℝ => Real.exp (-(2 * u))) atBot atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_neg_atBot_atTop.comp
      (tendsto_id.const_mul_atBot two_pos))
  rw [show ringMass n = fun t => n / (1 + Real.exp (-(2 * t))) from funext (ringMass_eq n)]
  exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 he)

/-! ### Generic half-slab integrals -/

/-- Left half-slab, for a nonnegative continuous derivative `f = F'` with `F → L` at `-∞`. -/
theorem integral_left_of_hasDerivAt {n c s L : ℝ} {F f : ℝ → ℝ} (hn : 0 < n) (hc0 : 0 ≤ c)
    (hcn : c < n) (hs : c ≤ ringMass n s) (hF : ∀ x, HasDerivAt F (f x) x) (hf : Continuous f)
    (hpos : ∀ x, 0 ≤ f x) (hlim : Tendsto F atBot (𝓝 L)) :
    IntegrableOn f ({t | c ≤ ringMass n t} ∩ Iio s) ∧
      ∫ t in {t | c ≤ ringMass n t} ∩ Iio s, f t =
        F s - (if c = 0 then L else F (ringQuantile n c)) := by
  rcases hc0.eq_or_lt with rfl | hc0
  · have hset : {t | (0 : ℝ) ≤ ringMass n t} ∩ Iio s = Iio s := by
      ext t; simp [(ringMass_pos hn t).le]
    rw [hset, ite_eq_left rfl]
    have hint : IntegrableOn f (Iic s) :=
      integrableOn_Iic_of_hasDerivAt_of_nonneg s hF hpos hlim
    exact ⟨hint.mono_set Iio_subset_Iic_self, by
      rw [← integral_Iic_eq_integral_Iio,
        integral_Iic_of_hasDerivAt_of_tendsto' (fun x _ => hF x) hint hlim]⟩
  · have hτ : ringQuantile n c ≤ s := (le_ringMass_iff hc0 hcn s).1 hs
    have hset : {t | c ≤ ringMass n t} ∩ Iio s = Ico (ringQuantile n c) s := by
      ext t; simp [le_ringMass_iff hc0 hcn t, and_comm]
    rw [hset, ite_eq_right hc0.ne']
    refine ⟨hf.integrableOn_Icc.mono_set Ico_subset_Icc_self, ?_⟩
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hf.intervalIntegrable _ _)]

/-- Right half-slab, for a nonnegative continuous derivative `f = F'` with `F → L` at `+∞`. -/
theorem integral_right_of_hasDerivAt {n d s L : ℝ} {F f : ℝ → ℝ} (hn : 0 < n) (hd0 : 0 < d)
    (hdn : d ≤ n) (hs : ringMass n s ≤ d) (hF : ∀ x, HasDerivAt F (f x) x) (hf : Continuous f)
    (hpos : ∀ x, 0 ≤ f x) (hlim : Tendsto F atTop (𝓝 L)) :
    IntegrableOn f ({t | ringMass n t ≤ d} ∩ Ici s) ∧
      ∫ t in {t | ringMass n t ≤ d} ∩ Ici s, f t =
        (if d = n then L else F (ringQuantile n d)) - F s := by
  rcases hdn.eq_or_lt with rfl | hdn
  · have hset : {t | ringMass d t ≤ d} ∩ Ici s = Ici s := by
      ext t; simp [(ringMass_lt hn t).le]
    rw [hset, ite_eq_left rfl]
    have hint : IntegrableOn f (Ioi s) :=
      integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hF x) (fun x _ => hpos x) hlim
    refine ⟨by rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hint, ?_⟩
    rw [integral_Ici_eq_integral_Ioi,
      integral_Ioi_of_hasDerivAt_of_nonneg' (fun x _ => hF x) (fun x _ => hpos x) hlim]
  · have hτ : s ≤ ringQuantile n d := (ringMass_le_iff hd0 hdn s).1 hs
    have hset : {t | ringMass n t ≤ d} ∩ Ici s = Icc s (ringQuantile n d) := by
      ext t; simp [ringMass_le_iff hd0 hdn t, and_comm]
    rw [hset, ite_eq_right hdn.ne]
    refine ⟨hf.integrableOn_Icc, ?_⟩
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hτ,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hf.intervalIntegrable _ _)]

/-- The mass slab `{c ≤ Φ ≤ d}` splits at any of its points `s`. -/
theorem slab_eq_union {n c d s : ℝ} (hn : 0 < n) (hs1 : c ≤ ringMass n s) (hs2 : ringMass n s ≤ d) :
    {t | c ≤ ringMass n t ∧ ringMass n t ≤ d} =
      ({t | c ≤ ringMass n t} ∩ Iio s) ∪ ({t | ringMass n t ≤ d} ∩ Ici s) := by
  have hmono := ringMass_strictMono hn
  ext t
  simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_Iio, mem_Ici]
  rcases lt_or_ge t s with h | h
  · have : ringMass n t ≤ d := (hmono h).le.trans hs2
    exact ⟨fun h' => Or.inl ⟨h'.1, h⟩, fun h' => h'.elim (fun h' => ⟨h'.1, this⟩)
      (fun h' => absurd h'.2 (not_le.2 h))⟩
  · have : c ≤ ringMass n t := hs1.trans (hmono.monotone h)
    exact ⟨fun h' => Or.inr ⟨h'.2, h⟩, fun h' => h'.elim (fun h' => absurd h'.2 (not_lt.2 h))
      (fun h' => ⟨this, h'.1⟩)⟩

theorem measurableSet_slab (n c d : ℝ) :
    MeasurableSet {t | c ≤ ringMass n t ∧ ringMass n t ≤ d} :=
  (measurableSet_le measurable_const (continuous_ringMass n).measurable).inter
    (measurableSet_le (continuous_ringMass n).measurable measurable_const)

/-- `ν({c ≤ Φ ≤ d}) = d - c`. -/
theorem integral_density_slab {n c d : ℝ} (hn : 0 < n) (hc0 : 0 ≤ c) (hcd : c < d) (hdn : d ≤ n) :
    IntegrableOn (ringDensity n) {t | c ≤ ringMass n t ∧ ringMass n t ≤ d} ∧
      ∫ t in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d}, ringDensity n t = d - c := by
  set m := (c + d) / 2
  have hm0 : 0 < m := by simp only [m]; linarith
  have hmn : m < n := by simp only [m]; linarith
  set s := ringQuantile n m
  have hs : ringMass n s = m := ringMass_quantile hm0 hmn
  obtain ⟨hi1, he1⟩ := integral_left_of_hasDerivAt hn hc0 (by linarith) (by rw [hs]; simp only [m]; linarith)
    (hasDerivAt_ringMass n) (continuous_ringDensity n) (fun x => (ringDensity_pos hn x).le)
    (tendsto_ringMass_atBot n)
  obtain ⟨hi2, he2⟩ := integral_right_of_hasDerivAt hn (by linarith) hdn
    (by rw [hs]; simp only [m]; linarith) (hasDerivAt_ringMass n) (continuous_ringDensity n)
    (fun x => (ringDensity_pos hn x).le) (tendsto_ringMass_atTop n)
  have hdisj : Disjoint ({t | c ≤ ringMass n t} ∩ Iio s) ({t | ringMass n t ≤ d} ∩ Ici s) := by
    rw [Set.disjoint_left]
    intro t h1 h2
    exact absurd h2.2 (not_le.2 h1.2)
  have hS2 : MeasurableSet ({t | ringMass n t ≤ d} ∩ Ici s) :=
    (measurableSet_le (continuous_ringMass n).measurable measurable_const).inter measurableSet_Ici
  rw [slab_eq_union hn (by rw [hs]; simp only [m]; linarith) (by rw [hs]; simp only [m]; linarith)]
  refine ⟨hi1.union hi2, ?_⟩
  rw [setIntegral_union hdisj hS2 hi1 hi2, he1, he2, hs]
  have hq1 : (if c = 0 then (0 : ℝ) else ringMass n (ringQuantile n c)) = c := by
    split_ifs with h
    · exact h.symm
    · exact ringMass_quantile (lt_of_le_of_ne hc0 (Ne.symm h)) (by linarith)
  have hq2 : (if d = n then n else ringMass n (ringQuantile n d)) = d := by
    split_ifs with h
    · exact h.symm
    · exact ringMass_quantile (by linarith) (lt_of_le_of_ne hdn h)
  rw [hq1, hq2]
  ring

/-! ### Integrability of the first moment -/

theorem integrable_exp_neg_abs : Integrable fun s : ℝ => Real.exp (-|s|) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · refine (integrableOn_exp_Iic 0).congr_fun (fun s hs => ?_) measurableSet_Iic
    simp [abs_of_nonpos (mem_Iic.1 hs)]
  · refine (exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp [abs_of_pos (mem_Ioi.1 hs)]

theorem integrable_mul_ringDensity (n : ℝ) : Integrable fun s => s * ringDensity n s := by
  refine (integrable_exp_neg_abs.const_mul (2 * |n|)).mono'
    (continuous_id.mul (continuous_ringDensity n)).aestronglyMeasurable (ae_of_all _ fun s => ?_)
  set E := Real.exp |s|
  have hE : 0 < E := Real.exp_pos _
  have hcosh : E / 2 ≤ Real.cosh s := by
    rw [← Real.cosh_abs, Real.cosh_eq]; linarith [Real.exp_pos (-|s|)]
  have habs : |s| ≤ E := by linarith [Real.add_one_le_exp |s|]
  have hc := Real.cosh_pos s
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, ringDensity, abs_div, abs_div, abs_of_pos
    (pow_pos hc 2), abs_two]
  calc |s| * (|n| / 2 / Real.cosh s ^ 2) = |s| * (|n| / 2) / Real.cosh s ^ 2 := by ring
    _ ≤ E * (|n| / 2) / (E / 2) ^ 2 := by
        apply div_le_div₀ (by positivity) (by gcongr) (by positivity)
        exact pow_le_pow_left₀ (by positivity) hcosh 2
    _ = 2 * |n| * Real.exp (-|s|) := by
        rw [Real.exp_neg]
        field_simp
        ring

/-! ### The barycentre lies in the interior of its slab -/

/-- For `0 ≤ c < d ≤ n`, the `ν`-barycentre `b = (d - c)⁻¹ ∫_{c ≤ Φ ≤ d} t dν` of the mass slab
satisfies `c < Φ(b) < d`. -/
theorem barycentre_mem_interior {n c d : ℝ} (hn : 0 < n) (hc0 : 0 ≤ c) (hcd : c < d) (hdn : d ≤ n) :
    c < ringMass n ((d - c)⁻¹ * ∫ s in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d},
        s * ringDensity n s) ∧
      ringMass n ((d - c)⁻¹ * ∫ s in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d},
        s * ringDensity n s) < d := by
  set S := {t | c ≤ ringMass n t ∧ ringMass n t ≤ d}
  have hS : MeasurableSet S := measurableSet_slab n c d
  have hmono := ringMass_strictMono hn
  obtain ⟨hρi, hρ⟩ := integral_density_slab hn hc0 hcd hdn
  have hmi : IntegrableOn (fun s => s * ringDensity n s) S := (integrable_mul_ringDensity n).integrableOn
  set I := ∫ s in S, s * ringDensity n s
  have hdc : 0 < d - c := by linarith
  set m := (c + d) / 2
  have hm0 : 0 < m := by simp only [m]; linarith
  have hmn : m < n := by simp only [m]; linarith
  set s0 := ringQuantile n m
  have hs0 : ringMass n s0 = m := ringMass_quantile hm0 hmn
  -- `∫_S (s - a) ϱ = I - a (d - c)`
  have hshift : ∀ a : ℝ, ∫ s in S, (s - a) * ringDensity n s = I - a * (d - c) := by
    intro a
    have : (fun s => (s - a) * ringDensity n s) = fun s => s * ringDensity n s - a * ringDensity n s := by
      funext s; ring
    rw [this, integral_sub hmi (hρi.const_mul a), integral_const_mul, hρ]
  constructor
  · rcases hc0.eq_or_lt with h0 | h0
    · rw [← h0]; exact ringMass_pos hn _
    · set a := ringQuantile n c
      have ha : ringMass n a = c := ringMass_quantile h0 (by linarith)
      have has0 : a < s0 := hmono.lt_iff_lt.1 (by rw [ha, hs0]; simp only [m]; linarith)
      have hpos : 0 < ∫ s in S, (s - a) * ringDensity n s := by
        have hnn : ∀ s ∈ S, 0 ≤ (s - a) * ringDensity n s := fun s hs =>
          mul_nonneg (sub_nonneg.2 ((le_ringMass_iff h0 (by linarith) s).1 hs.1))
            (ringDensity_pos hn s).le
        rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem hS hnn)
          ((hmi.sub (hρi.const_mul a)).congr_fun (fun s _ => by simp only [Pi.sub_apply]; ring) hS)]
        refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo a s0) fun s hs => ⟨?_, ?_, ?_⟩)
        · rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.2 (by linarith)
        · exact (mul_pos (sub_pos.2 hs.1) (ringDensity_pos hn s)).ne'
        · exact (ha ▸ (hmono hs.1).le)
        · exact ((hmono hs.2).trans_eq hs0).le.trans (by simp only [m]; linarith)
      rw [hshift] at hpos
      have key : a < (d - c)⁻¹ * I := by rw [lt_inv_mul_iff₀ hdc]; linarith
      calc c = ringMass n a := ha.symm
        _ < _ := hmono key
  · rcases hdn.eq_or_lt with h0 | h0
    · rw [h0]; exact ringMass_lt hn _
    · set a := ringQuantile n d
      have ha : ringMass n a = d := ringMass_quantile (by linarith) h0
      have has0 : s0 < a := hmono.lt_iff_lt.1 (by rw [ha, hs0]; simp only [m]; linarith)
      have hpos : 0 < ∫ s in S, -((s - a) * ringDensity n s) := by
        have hnn : ∀ s ∈ S, 0 ≤ -((s - a) * ringDensity n s) := fun s hs => by
          have : s ≤ a := (ringMass_le_iff (by linarith) h0 s).1 hs.2
          have := ringDensity_pos hn s
          nlinarith
        rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem hS hnn)
          ((hmi.sub (hρi.const_mul a)).neg.congr_fun
          (fun s _ => by simp only [Pi.neg_apply, Pi.sub_apply]; ring) hS)]
        refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo s0 a) fun s hs => ⟨?_, ?_, ?_⟩)
        · rw [Real.volume_Ioo]; exact ENNReal.ofReal_pos.2 (by linarith)
        · exact neg_ne_zero.2 (mul_neg_of_neg_of_pos (sub_neg.2 hs.2) (ringDensity_pos hn s)).ne
        · exact le_trans (by simp only [m]; linarith) (hs0 ▸ (hmono hs.1).le)
        · exact (ha ▸ (hmono hs.2).le)
      rw [integral_neg, hshift] at hpos
      have key : (d - c)⁻¹ * I < a := by rw [inv_mul_lt_iff₀ hdc]; linarith
      calc _ < ringMass n a := hmono key
        _ = d := ha

namespace RowConfig

variable (R : RowConfig)

theorem mem_interior_of_isSlabBarycentric (hR : R.IsSlabBarycentric) (k : ℕ) (hk : k < R.K) :
    (R.mass k : ℝ) < ringMass R.card (R.t k) ∧ ringMass R.card (R.t k) < R.mass (k + 1) := by
  have hN := hR.1 k hk
  have hNk : (R.N k : ℝ) = (R.mass (k + 1) : ℝ) - R.mass k := by
    rw [mass_succ]; push_cast; ring
  have hn : (0 : ℝ) < R.card := by
    have : R.mass (k + 1) ≤ R.card := R.mass_mono (by omega)
    rw [mass_succ] at this
    exact_mod_cast (show 0 < R.card by omega)
  rw [hR.2 k hk, hNk]
  exact barycentre_mem_interior hn (Nat.cast_nonneg _)
    (by rw [mass_succ]; push_cast; exact_mod_cast (by omega : R.mass k < R.mass k + R.N k))
    (by exact_mod_cast R.mass_mono (by omega : k + 1 ≤ R.K))

/-- **Proposition 5.5 (exact ring identity).** For every slab-barycentric row configuration (any
phases), `E = (½ - log 2) n² - (n/2) log n + (n/2) log 2 + ∑_k B_k`. -/
theorem configEnergy_eq_ring_of_isSlabBarycentric (hR : R.IsSlabBarycentric) :
    configEnergy R.points =
      (1 / 2 - Real.log 2) * (R.card : ℝ) ^ 2 - (R.card : ℝ) / 2 * Real.log R.card +
        (R.card : ℝ) / 2 * Real.log 2 + ∑ k ∈ Finset.range R.K, R.rowB k :=
  R.configEnergy_eq_ring hR.1 (R.mem_interior_of_isSlabBarycentric hR)

end RowConfig

end Sphere

end SandierSerfaty

end
