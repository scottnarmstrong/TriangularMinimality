/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Splitting
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Existence of minimizers of the sphere energy (sphere note, Lemma 4.1)

The energy `E` of Definition 2.1 is `+∞` on a configuration with a coincident pair, while
`Sphere.sphereEnergy` is real valued (the junk value `0` of `Real.log 0`). A *minimizer*
(`Sphere.IsSphereMinimizer`) is therefore a configuration of pairwise distinct points of `S²` whose
`sphereEnergy` is `≤` that of every other such configuration; this is the same as minimizing the
paper's extended-valued `E` over `(S²)ⁿ`.

* `Sphere.logTermE`, `Sphere.sphereEnergyE`: the shifted, extended-valued energy
  `E(Y) + n(n-1) log 2 ∈ [0, ∞]` with values in `ℝ≥0∞` (the shift makes every pair term non-negative
  on the sphere), and `Sphere.lowerSemicontinuous_sphereEnergyE` (lower semicontinuity);
* `Sphere.exists_isSphereMinimizer`: minimizers exist, and consist of distinct points;
* `Sphere.IsSphereMinimizer.comp_isometry`: `O(3)`-invariance;
* `Sphere.IsSphereMinimizer.exists_isometry_avoiding`: a minimizer can be moved by an orthogonal map so
  that no point lies at either of two prescribed antipodal poles.
-/

open Filter Topology Set Finset
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Sphere

/-- A *minimizer* of the logarithmic energy on `(S²)ⁿ`: pairwise distinct points of the unit sphere
with `sphereEnergy` at most that of any other configuration of distinct points of the sphere. -/
structure IsSphereMinimizer {n : ℕ} (Y : Fin n → R3) : Prop where
  norm_eq : ∀ i, ‖Y i‖ = 1
  injective : Function.Injective Y
  le : ∀ Z : Fin n → R3, (∀ i, ‖Z i‖ = 1) → Function.Injective Z → sphereEnergy Y ≤ sphereEnergy Z

/-- The extended-valued pair term `t ↦ -log t + log 2` (in `ℝ≥0∞`), `+∞` for `t ≤ 0`. -/
@[expose] noncomputable def logTermE (t : ℝ) : ℝ≥0∞ :=
  if t ≤ 0 then ⊤ else ENNReal.ofReal (-Real.log t + Real.log 2)

/-- The extended-valued shifted energy `E(Y) + n(n-1) log 2` (`+∞` on coincident configurations). -/
@[expose] noncomputable def sphereEnergyE {n : ℕ} (Y : Fin n → R3) : ℝ≥0∞ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, logTermE ‖Y i - Y j‖

theorem lowerSemicontinuous_logTermE : LowerSemicontinuous logTermE := by
  intro x y hy
  by_cases hx : 0 < x
  · have hc : ContinuousAt (fun t : ℝ => ENNReal.ofReal (-Real.log t + Real.log 2)) x :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (((Real.continuousAt_log hx.ne').neg).add continuousAt_const)
    have hev : logTermE =ᶠ[𝓝 x] fun t : ℝ => ENNReal.ofReal (-Real.log t + Real.log 2) := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      simp [logTermE, not_le.2 ht]
    have hy2 : y < ENNReal.ofReal (-Real.log x + Real.log 2) := by
      rwa [hev.self_of_nhds] at hy
    have := hc.lowerSemicontinuousAt y hy2
    filter_upwards [this, hev] with t h1 h2
    show y < logTermE t
    rw [h2]; exact h1
  · have hx0 : x ≤ 0 := not_lt.1 hx
    have hxt : logTermE x = ⊤ := by simp [logTermE, hx0]
    rw [hxt] at hy
    have hy' : y ≠ ⊤ := hy.ne
    set s : ℝ := y.toReal with hs
    set δ : ℝ := 2 * Real.exp (-s) with hδ
    have hδ0 : 0 < δ := by positivity
    filter_upwards [Iio_mem_nhds (hx0.trans_lt hδ0)] with t ht
    by_cases ht0 : t ≤ 0
    · simp [logTermE, ht0, hy]
    · rw [not_le] at ht0
      have hlt : s < -Real.log t + Real.log 2 := by
        have h1 : Real.log t < Real.log δ := Real.log_lt_log ht0 ht
        have h2 : Real.log δ = Real.log 2 - s := by
          rw [hδ, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]; ring
        linarith
      have hpos : 0 < -Real.log t + Real.log 2 := by
        have : 0 ≤ s := ENNReal.toReal_nonneg
        linarith
      simp only [logTermE, not_le.2 ht0, ite_false]
      calc y = ENNReal.ofReal s := (ENNReal.ofReal_toReal hy').symm
        _ < _ := (ENNReal.ofReal_lt_ofReal_iff hpos).2 hlt

theorem lowerSemicontinuous_sphereEnergyE {n : ℕ} :
    LowerSemicontinuous (sphereEnergyE : (Fin n → R3) → ℝ≥0∞) := by
  unfold sphereEnergyE
  refine lowerSemicontinuous_sum fun i _ => lowerSemicontinuous_sum fun j _ => ?_
  exact lowerSemicontinuous_logTermE.comp ((continuous_apply i).sub (continuous_apply j)).norm

theorem logTermE_of_pos {t : ℝ} (ht : 0 < t) :
    logTermE t = ENNReal.ofReal (-Real.log t + Real.log 2) := by
  simp [logTermE, not_le.2 ht]

theorem logTermE_of_nonpos {t : ℝ} (ht : t ≤ 0) : logTermE t = ⊤ := by simp [logTermE, ht]

theorem stereo_injective : Function.Injective stereo := by
  intro x x' h
  have h1 := norm_stereo_sub x x'
  rw [h, sub_self, norm_zero] at h1
  have h2 : 0 < Real.sqrt (lam x * lam x') := Real.sqrt_pos.2 (mul_pos (lam_pos x) (lam_pos x'))
  have : ‖x - x'‖ = 0 := by
    rcases mul_eq_zero.1 h1.symm with h3 | h3
    · exact absurd h3 h2.ne'
    · exact h3
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

theorem exists_injective_sphere (n : ℕ) :
    ∃ Z : Fin n → R3, (∀ i, ‖Z i‖ = 1) ∧ Function.Injective Z := by
  refine ⟨fun i => stereo ((i : ℕ) : ℂ), fun i => norm_stereo _, ?_⟩
  intro i j h
  have := stereo_injective h
  exact Fin.ext (by exact_mod_cast this)

theorem norm_sub_le_two {a b : R3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : ‖a - b‖ ≤ 2 := by
  have := norm_sub_le a b
  linarith

theorem pair_term_nonneg {a b : R3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    0 ≤ -Real.log ‖a - b‖ + Real.log 2 := by
  have h0 : 0 < ‖a - b‖ := norm_pos_iff.2 (sub_ne_zero.2 hab)
  have := Real.log_le_log h0 (norm_sub_le_two ha hb)
  linarith

/-- On injective configurations of the sphere, `sphereEnergyE` is the shifted energy. -/
theorem sphereEnergyE_eq {n : ℕ} {Y : Fin n → R3} (hY : ∀ i, ‖Y i‖ = 1) (hinj : Function.Injective Y) :
    sphereEnergyE Y =
      ENNReal.ofReal (sphereEnergy Y + ((n * (n - 1) : ℕ) : ℝ) * Real.log 2) := by
  have hpos : ∀ i, ∀ j ∈ Finset.univ.erase i, 0 < ‖Y i - Y j‖ := fun i j hj =>
    norm_pos_iff.2 (sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hj) (hinj h).symm)
  have hnn : ∀ i, ∀ j ∈ Finset.univ.erase i, 0 ≤ -Real.log ‖Y i - Y j‖ + Real.log 2 :=
    fun i j hj => pair_term_nonneg (hY i) (hY j)
      (fun h => (Finset.ne_of_mem_erase hj) (hinj h).symm)
  have e : sphereEnergy Y + ((n * (n - 1) : ℕ) : ℝ) * Real.log 2 =
      ∑ i, ∑ j ∈ Finset.univ.erase i, (-Real.log ‖Y i - Y j‖ + Real.log 2) := by
    simp only [sphereEnergy, Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem,
      Finset.mem_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_mul]; ring
  rw [e, ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg (hnn i)]
  unfold sphereEnergyE
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (hnn i)]
  exact Finset.sum_congr rfl fun j hj => logTermE_of_pos (hpos i j hj)

/-- **Lemma 4.1 (existence).** Minimizers of the logarithmic energy on `(S²)ⁿ` exist; they consist of
pairwise distinct points. -/
theorem exists_isSphereMinimizer (n : ℕ) : ∃ Y : Fin n → R3, IsSphereMinimizer Y := by
  classical
  set K : Set (Fin n → R3) := Set.univ.pi fun _ => Metric.sphere (0 : R3) 1 with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_sphere 0 1
  obtain ⟨Z₀, hZ₀n, hZ₀i⟩ := exists_injective_sphere n
  have hZ₀K : Z₀ ∈ K := fun i _ => by simpa using hZ₀n i
  obtain ⟨Y₀, hY₀K, hmin⟩ :=
    (lowerSemicontinuous_sphereEnergyE.lowerSemicontinuousOn K).exists_isMinOn ⟨Z₀, hZ₀K⟩ hKc
  have hY₀n : ∀ i, ‖Y₀ i‖ = 1 := fun i => by simpa using hY₀K i (Set.mem_univ i)
  have hfin : sphereEnergyE Z₀ < ⊤ := by
    rw [sphereEnergyE_eq hZ₀n hZ₀i]; exact ENNReal.ofReal_lt_top
  have hY₀fin : sphereEnergyE Y₀ < ⊤ :=
    (show sphereEnergyE Y₀ ≤ sphereEnergyE Z₀ from hmin hZ₀K).trans_lt hfin
  have hY₀inj : Function.Injective Y₀ := by
    intro i j hij
    by_contra hne
    have hterm : logTermE ‖Y₀ i - Y₀ j‖ = ⊤ := by
      rw [hij, sub_self, norm_zero]; exact logTermE_of_nonpos le_rfl
    have : sphereEnergyE Y₀ = ⊤ := by
      unfold sphereEnergyE
      refine ENNReal.sum_eq_top.2 ⟨i, Finset.mem_univ i, ENNReal.sum_eq_top.2 ⟨j, ?_, hterm⟩⟩
      exact Finset.mem_erase.2 ⟨fun h => hne h.symm, Finset.mem_univ j⟩
    exact absurd hY₀fin (by rw [this]; exact lt_irrefl _)
  refine ⟨Y₀, hY₀n, hY₀inj, fun Z hZn hZi => ?_⟩
  have hZK : Z ∈ K := fun i _ => by simpa using hZn i
  have h : sphereEnergyE Y₀ ≤ sphereEnergyE Z := hmin hZK
  rw [sphereEnergyE_eq hY₀n hY₀inj, sphereEnergyE_eq hZn hZi] at h
  have hnn : 0 ≤ sphereEnergy Z + ((n * (n - 1) : ℕ) : ℝ) * Real.log 2 := by
    have hh := sphereEnergyE_eq hZn hZi
    have e : sphereEnergy Z + ((n * (n - 1) : ℕ) : ℝ) * Real.log 2 =
        ∑ i, ∑ j ∈ Finset.univ.erase i, (-Real.log ‖Z i - Z j‖ + Real.log 2) := by
      simp only [sphereEnergy, Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem,
        Finset.mem_univ, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_mul]; ring
    rw [e]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j hj =>
      pair_term_nonneg (hZn i) (hZn j) (fun h => (Finset.ne_of_mem_erase hj) (hZi h).symm)
  have := (ENNReal.ofReal_le_ofReal_iff hnn).1 h
  linarith

/-- The sphere energy is invariant under linear isometries of `ℝ³`. -/
theorem sphereEnergy_comp_isometry {n : ℕ} (Y : Fin n → R3) (R : R3 ≃ₗᵢ[ℝ] R3) :
    sphereEnergy (fun i => R (Y i)) = sphereEnergy Y := by
  simp [sphereEnergy, ← map_sub]

/-- **Lemma 4.1 (`O(3)`-invariance).** -/
theorem IsSphereMinimizer.comp_isometry {n : ℕ} {Y : Fin n → R3} (hY : IsSphereMinimizer Y)
    (R : R3 ≃ₗᵢ[ℝ] R3) : IsSphereMinimizer (fun i => R (Y i)) := by
  refine ⟨fun i => by rw [LinearIsometryEquiv.norm_map, hY.norm_eq],
    fun i j h => hY.injective (R.injective h), fun Z hZn hZi => ?_⟩
  rw [sphereEnergy_comp_isometry]
  exact hY.le Z hZn hZi

/-- `O(3)` acts transitively on spheres: a linear isometry (a reflection) of `ℝ³` moving `a` to `b`. -/
theorem exists_isometry_apply_eq {a b : R3} (h : ‖a‖ = ‖b‖) :
    ∃ R : R3 ≃ₗᵢ[ℝ] R3, R a = b :=
  ⟨(Submodule.span ℝ {a - b})ᗮ.reflection, Submodule.reflection_sub h⟩

/-- A finite configuration can be moved by an orthogonal map so that no point lies at either of the
two antipodal poles `±e`. -/
theorem exists_isometry_avoiding {n : ℕ} (Y : Fin n → R3) {e : R3} (he : ‖e‖ = 1) :
    ∃ R : R3 ≃ₗᵢ[ℝ] R3, ∀ i, R (Y i) ≠ e ∧ R (Y i) ≠ -e := by
  classical
  have hinf : (Metric.sphere (0 : R3) 1).Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := stereo) stereo_injective fun x => ?_
    simpa using norm_stereo x
  obtain ⟨v, hv, hvF⟩ := hinf.exists_notMem_finset
    (Finset.univ.image Y ∪ Finset.univ.image fun i => -Y i)
  have hvn : ‖v‖ = ‖e‖ := by rw [he]; simpa using hv
  obtain ⟨R, hR⟩ := exists_isometry_apply_eq hvn
  refine ⟨R, fun i => ⟨fun h => hvF ?_, fun h => hvF ?_⟩⟩
  · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, ?_⟩)
    exact R.injective (by rw [hR, h])
  · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_univ i, ?_⟩)
    have : R (-Y i) = e := by rw [map_neg, h, neg_neg]
    exact R.injective (by rw [hR, this])

/-- **Lemma 4.1 (poles).** A minimizer can be moved by an orthogonal map to a minimizer none of whose
points lies at either of the two antipodal poles `±e`. -/
theorem IsSphereMinimizer.exists_isometry_avoiding {n : ℕ} {Y : Fin n → R3} (hY : IsSphereMinimizer Y)
    {e : R3} (he : ‖e‖ = 1) :
    ∃ R : R3 ≃ₗᵢ[ℝ] R3, IsSphereMinimizer (fun i => R (Y i)) ∧ ∀ i, R (Y i) ≠ e ∧ R (Y i) ≠ -e := by
  obtain ⟨R, hR⟩ := Sphere.exists_isometry_avoiding Y he
  exact ⟨R, hY.comp_isometry R, hR⟩

end Sphere

end SandierSerfaty

end
