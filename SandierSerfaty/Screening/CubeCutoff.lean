/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.CubeEnergyBound
public import SandierSerfaty.Geometry.LatticeCount

/-!
# Lipschitz cutoffs of squares

The test functions of the density argument (the comparison note's §5 `lem:flux`, in the book's sign):

* `cubeNorm z = max |re z| |im z|`, so that `□_ℓ = {cubeNorm ≤ ℓ/2}` (`mem_cube_iff_cubeNorm`);
* `cubeCutoff a w`, the `w⁻¹`-Lipschitz function equal to `1` on `□_{2a}` and to `0` off
  `□_{2(a+w)}`;
* its circle averages of radius `¼` against the points of a locally finite set:
  `#(C ∩ □_{2(a-¼)}) ≤ ∑_{p∈C} ⨍_{∂B(p,¼)} φ ≤ #(C ∩ □_{2(a+w+¼)})`;
* `(2a)² ≤ ∫ φ ≤ (2(a+w))²`;
* the flux bound `|∫ ⟪Φ, ∇φ⟫| ≤ ε L + (2(a+w))²/(ε w²)` when `∫_{□_{2(a+w)}} |Φ|² ≤ L`
  (pointwise `y/w ≤ ε y² + 1/(ε w²)`, no Cauchy–Schwarz).
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty

namespace Screening

/-- The sup norm `max |re z| |im z|`, whose closed balls centred at `0` are the squares `□_ℓ`. -/
@[expose] noncomputable def cubeNorm (z : ℂ) : ℝ := max |z.re| |z.im|

theorem mem_cube_iff_cubeNorm {ℓ : ℝ} {z : ℂ} : z ∈ cube ℓ ↔ cubeNorm z ≤ ℓ / 2 := by
  rw [Torus.mem_cube_iff, cubeNorm, max_le_iff]

theorem abs_cubeNorm_sub_le (x y : ℂ) : |cubeNorm x - cubeNorm y| ≤ ‖x - y‖ := by
  unfold cubeNorm
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  · refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
    rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _

theorem isCompact_cube (ℓ : ℝ) : IsCompact (cube ℓ) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    (Torus.isBounded_cube ℓ)

/-- The cutoff `φ_{a,w}`: equal to `1` on `□_{2a}`, to `0` off `□_{2(a+w)}`, `w⁻¹`-Lipschitz. -/
@[expose] noncomputable def cubeCutoff (a w : ℝ) (z : ℂ) : ℝ :=
  min 1 (max 0 ((a + w - cubeNorm z) / w))

variable {a w : ℝ}

theorem cubeCutoff_nonneg (z : ℂ) : 0 ≤ cubeCutoff a w z := le_min zero_le_one (le_max_left _ _)

theorem cubeCutoff_le_one (z : ℂ) : cubeCutoff a w z ≤ 1 := min_le_left _ _

theorem cubeCutoff_eq_one (hw : 0 < w) {z : ℂ} (hz : cubeNorm z ≤ a) : cubeCutoff a w z = 1 := by
  unfold cubeCutoff
  rw [min_eq_left]
  rw [le_max_iff]; right; rw [le_div_iff₀ hw]; linarith

theorem cubeCutoff_eq_zero (hw : 0 < w) {z : ℂ} (hz : a + w ≤ cubeNorm z) :
    cubeCutoff a w z = 0 := by
  unfold cubeCutoff
  rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le), min_eq_right zero_le_one]

theorem cubeCutoff_eq_zero_of_notMem (hw : 0 < w) {z : ℂ} (hz : z ∉ cube (2 * (a + w))) :
    cubeCutoff a w z = 0 :=
  cubeCutoff_eq_zero hw (by rw [mem_cube_iff_cubeNorm] at hz; linarith [not_le.1 hz])

theorem lipschitzWith_cubeCutoff (hw : 0 < w) :
    LipschitzWith (Real.toNNReal w⁻¹) (cubeCutoff a w) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hw.le), dist_eq_norm]
  unfold cubeCutoff
  calc |min 1 (max 0 ((a + w - cubeNorm x) / w)) - min 1 (max 0 ((a + w - cubeNorm y) / w))|
      ≤ |max 0 ((a + w - cubeNorm x) / w) - max 0 ((a + w - cubeNorm y) / w)| :=
        (abs_min_sub_min_le_max _ _ _ _).trans (by simp)
    _ ≤ |(a + w - cubeNorm x) / w - (a + w - cubeNorm y) / w| :=
        (abs_max_sub_max_le_max _ _ _ _).trans (by simp)
    _ = |cubeNorm y - cubeNorm x| / w := by
        rw [div_sub_div_same, abs_div, abs_of_pos hw]; congr 2; ring
    _ ≤ w⁻¹ * ‖x - y‖ := by
        rw [div_eq_inv_mul, norm_sub_rev]; gcongr; exact abs_cubeNorm_sub_le y x

theorem continuous_cubeCutoff (hw : 0 < w) : Continuous (cubeCutoff a w) :=
  (lipschitzWith_cubeCutoff hw).continuous

theorem tsupport_cubeCutoff_subset (hw : 0 < w) : tsupport (cubeCutoff a w) ⊆ cube (2 * (a + w)) :=
  closure_minimal (fun _ hz => by_contra fun h => hz (cubeCutoff_eq_zero_of_notMem hw h))
    (isClosed_Icc.reProdIm isClosed_Icc)

theorem hasCompactSupport_cubeCutoff (hw : 0 < w) : HasCompactSupport (cubeCutoff a w) :=
  HasCompactSupport.intro (isCompact_cube _) fun _ hz => cubeCutoff_eq_zero_of_notMem hw hz

/-! ### Circle averages of the cutoff -/

theorem norm_sub_eq_of_mem_sphere {x p : ℂ} (hx : x ∈ sphere p |(1 / 4 : ℝ)|) :
    ‖x - p‖ = 1 / 4 := by
  rw [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hx; exact hx

theorem circleAverage_cubeCutoff_eq_one (hw : 0 < w) {p : ℂ} (hp : cubeNorm p ≤ a - 1 / 4) :
    Real.circleAverage (cubeCutoff a w) p (1 / 4) = 1 :=
  Real.circleAverage_const_on_circle fun x hx => cubeCutoff_eq_one hw (by
    have h1 := abs_cubeNorm_sub_le x p
    rw [norm_sub_eq_of_mem_sphere hx] at h1
    linarith [(abs_le.1 h1).2])

theorem circleAverage_cubeCutoff_eq_zero (hw : 0 < w) {p : ℂ} (hp : a + w + 1 / 4 ≤ cubeNorm p) :
    Real.circleAverage (cubeCutoff a w) p (1 / 4) = 0 :=
  Real.circleAverage_const_on_circle fun x hx => cubeCutoff_eq_zero hw (by
    have h1 := abs_cubeNorm_sub_le x p
    rw [norm_sub_eq_of_mem_sphere hx] at h1
    linarith [(abs_le.1 h1).1])

theorem circleAverage_cubeCutoff_nonneg (p : ℂ) :
    0 ≤ Real.circleAverage (cubeCutoff a w) p (1 / 4) :=
  Real.circleAverage_nonneg_of_nonneg fun x _ => cubeCutoff_nonneg x

theorem circleAverage_cubeCutoff_le_one (hw : 0 < w) (p : ℂ) :
    Real.circleAverage (cubeCutoff a w) p (1 / 4) ≤ 1 :=
  Real.circleAverage_mono_on_of_le_circle (continuous_cubeCutoff hw).continuousOn.circleIntegrable'
    fun x _ => cubeCutoff_le_one x

/-! ### Counting against the circle averages -/

theorem finsum_circleAverage_cubeCutoff_le {C : Set ℂ} (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite)
    (hw : 0 < w) :
    ∑ᶠ p ∈ C, Real.circleAverage (cubeCutoff a w) p (1 / 4) ≤
      ((C ∩ cube (2 * (a + w + 1 / 4))).ncard : ℝ) := by
  have hfin := finite_inter_cube hC (2 * (a + w + 1 / 4))
  rw [finsum_mem_eq_finsetSum (S := hfin.toFinset)
    (fun p hp => ((Set.Finite.mem_toFinset hfin).1 hp).1) fun p hpC hp =>
      circleAverage_cubeCutoff_eq_zero hw (by
        have : p ∉ cube (2 * (a + w + 1 / 4)) := fun h =>
          hp ((Set.Finite.mem_toFinset hfin).2 ⟨hpC, h⟩)
        rw [mem_cube_iff_cubeNorm] at this
        linarith [not_le.1 this]),
    Set.ncard_eq_toFinset_card _ hfin]
  calc ∑ p ∈ hfin.toFinset, Real.circleAverage (cubeCutoff a w) p (1 / 4)
      ≤ ∑ p ∈ hfin.toFinset, (1 : ℝ) :=
        Finset.sum_le_sum fun p _ => circleAverage_cubeCutoff_le_one hw p
    _ = hfin.toFinset.card := by simp

theorem ncard_le_finsum_circleAverage_cubeCutoff {C : Set ℂ}
    (hC : ∀ R : ℝ, (C ∩ closedBall 0 R).Finite) (hw : 0 < w) :
    ((C ∩ cube (2 * (a - 1 / 4))).ncard : ℝ) ≤
      ∑ᶠ p ∈ C, Real.circleAverage (cubeCutoff a w) p (1 / 4) := by
  have hfin := finite_inter_cube hC (2 * (a + w + 1 / 4))
  have hfin' := finite_inter_cube hC (2 * (a - 1 / 4))
  rw [finsum_mem_eq_finsetSum (S := hfin.toFinset)
    (fun p hp => ((Set.Finite.mem_toFinset hfin).1 hp).1) fun p hpC hp =>
      circleAverage_cubeCutoff_eq_zero hw (by
        have : p ∉ cube (2 * (a + w + 1 / 4)) := fun h =>
          hp ((Set.Finite.mem_toFinset hfin).2 ⟨hpC, h⟩)
        rw [mem_cube_iff_cubeNorm] at this
        linarith [not_le.1 this]),
    Set.ncard_eq_toFinset_card _ hfin']
  have hsub : hfin'.toFinset ⊆ hfin.toFinset := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp ⊢
    exact ⟨hp.1, Torus.cube_mono (by linarith) hp.2⟩
  calc (hfin'.toFinset.card : ℝ) = ∑ p ∈ hfin'.toFinset, (1 : ℝ) := by simp
    _ = ∑ p ∈ hfin'.toFinset, Real.circleAverage (cubeCutoff a w) p (1 / 4) := by
        refine Finset.sum_congr rfl fun p hp => (circleAverage_cubeCutoff_eq_one hw ?_).symm
        have := ((Set.Finite.mem_toFinset hfin').1 hp).2
        rw [mem_cube_iff_cubeNorm] at this
        linarith
    _ ≤ ∑ p ∈ hfin.toFinset, Real.circleAverage (cubeCutoff a w) p (1 / 4) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => circleAverage_cubeCutoff_nonneg p

/-! ### The integral of the cutoff -/

theorem integrable_cubeCutoff (hw : 0 < w) : Integrable (cubeCutoff a w) :=
  (continuous_cubeCutoff hw).integrable_of_hasCompactSupport (hasCompactSupport_cubeCutoff hw)

theorem integral_indicator_cube (ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ∫ x, (cube ℓ).indicator (1 : ℂ → ℝ) x = ℓ ^ 2 := by
  rw [integral_indicator_one (Torus.measurableSet_cube ℓ), measureReal_def, Torus.volume_cube,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hℓ]

theorem integrable_indicator_cube (ℓ : ℝ) : Integrable ((cube ℓ).indicator (1 : ℂ → ℝ)) :=
  (continuous_const.continuousOn.integrableOn_compact (isCompact_cube ℓ)).integrable_indicator
    (Torus.measurableSet_cube ℓ)

theorem integral_cubeCutoff_le (ha : 0 ≤ a + w) (hw : 0 < w) :
    ∫ x, cubeCutoff a w x ≤ (2 * (a + w)) ^ 2 := by
  rw [← integral_indicator_cube _ (by linarith)]
  refine integral_mono (integrable_cubeCutoff hw) (integrable_indicator_cube _) fun x => ?_
  by_cases hx : x ∈ cube (2 * (a + w))
  · rw [indicator_of_mem hx]; exact cubeCutoff_le_one x
  · rw [indicator_of_notMem hx, cubeCutoff_eq_zero_of_notMem hw hx]

theorem le_integral_cubeCutoff (ha : 0 ≤ a) (hw : 0 < w) :
    (2 * a) ^ 2 ≤ ∫ x, cubeCutoff a w x := by
  rw [← integral_indicator_cube _ (by linarith)]
  refine integral_mono (integrable_indicator_cube _) (integrable_cubeCutoff hw) fun x => ?_
  by_cases hx : x ∈ cube (2 * a)
  · rw [indicator_of_mem hx, Pi.one_apply, cubeCutoff_eq_one hw]
    rw [mem_cube_iff_cubeNorm] at hx; linarith
  · rw [indicator_of_notMem hx]; exact cubeCutoff_nonneg x

/-! ### The flux bound -/

theorem mul_inv_le_mul_sq_add {y w ε : ℝ} (hy : 0 ≤ y) (hw : 0 < w) (hε : 0 < ε) :
    y * w⁻¹ ≤ ε * y ^ 2 + 1 / (ε * w ^ 2) := by
  set v := (ε * w)⁻¹ with hvdef
  have hv : 0 ≤ v := by positivity
  have h1 : w⁻¹ = ε * v := by rw [hvdef]; field_simp
  have h2 : 1 / (ε * w ^ 2) = ε * v ^ 2 := by rw [hvdef]; field_simp
  rw [h1, h2]
  nlinarith [mul_nonneg hε.le (sq_nonneg (y - v)), mul_nonneg hε.le (mul_nonneg hy hv)]

theorem abs_integral_inner_gradient_cubeCutoff_le {Φ : ℂ → ℂ} {ε L : ℝ} (ha : 0 ≤ a + w)
    (hw : 0 < w) (hε : 0 < ε) (hL : 0 ≤ L)
    (hΦ : ∫⁻ x in cube (2 * (a + w)), ENNReal.ofReal (‖Φ x‖ ^ 2) ≤ ENNReal.ofReal L) :
    |∫ x, inner ℝ (Φ x) (gradient (cubeCutoff a w) x)| ≤
      ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2) := by
  set K := cube (2 * (a + w))
  have hpt : ∀ x, ENNReal.ofReal ‖inner ℝ (Φ x) (gradient (cubeCutoff a w) x)‖ ≤
      K.indicator (fun x => ENNReal.ofReal ε * ENNReal.ofReal (‖Φ x‖ ^ 2) +
        ENNReal.ofReal (1 / (ε * w ^ 2))) x := by
    intro x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx, ← ENNReal.ofReal_mul hε.le,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hg := norm_gradient_le_of_lipschitz (lipschitzWith_cubeCutoff (a := a) hw) x
      rw [Real.coe_toNNReal _ (inv_nonneg.2 hw.le)] at hg
      calc ‖inner ℝ (Φ x) (gradient (cubeCutoff a w) x)‖
          ≤ ‖Φ x‖ * ‖gradient (cubeCutoff a w) x‖ := norm_inner_le_norm _ _
        _ ≤ ‖Φ x‖ * w⁻¹ := by gcongr
        _ ≤ ε * ‖Φ x‖ ^ 2 + 1 / (ε * w ^ 2) := mul_inv_le_mul_sq_add (norm_nonneg _) hw hε
    · rw [indicator_of_notMem hx, gradient_eq_zero_of_notMem_tsupport
        (fun h => hx (tsupport_cubeCutoff_subset hw h)), inner_zero_right, norm_zero,
        ENNReal.ofReal_zero]
  have hint : ∫⁻ x, ENNReal.ofReal ‖inner ℝ (Φ x) (gradient (cubeCutoff a w) x)‖ ≤
      ENNReal.ofReal (ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2)) := by
    calc ∫⁻ x, ENNReal.ofReal ‖inner ℝ (Φ x) (gradient (cubeCutoff a w) x)‖
        ≤ ∫⁻ x, K.indicator (fun x => ENNReal.ofReal ε * ENNReal.ofReal (‖Φ x‖ ^ 2) +
          ENNReal.ofReal (1 / (ε * w ^ 2))) x := lintegral_mono hpt
      _ = ∫⁻ x in K, (ENNReal.ofReal ε * ENNReal.ofReal (‖Φ x‖ ^ 2) +
          ENNReal.ofReal (1 / (ε * w ^ 2))) := lintegral_indicator (Torus.measurableSet_cube _) _
      _ = ENNReal.ofReal ε * (∫⁻ x in K, ENNReal.ofReal (‖Φ x‖ ^ 2)) +
          ENNReal.ofReal (1 / (ε * w ^ 2)) * volume K := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]
      _ ≤ ENNReal.ofReal ε * ENNReal.ofReal L +
          ENNReal.ofReal (1 / (ε * w ^ 2)) * ENNReal.ofReal ((2 * (a + w)) ^ 2) := by
          rw [Torus.volume_cube, ← ENNReal.ofReal_pow (by linarith)]
          gcongr
      _ = ENNReal.ofReal (ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2)) := by
          rw [← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  calc |∫ x, inner ℝ (Φ x) (gradient (cubeCutoff a w) x)|
      = ‖∫ x, inner ℝ (Φ x) (gradient (cubeCutoff a w) x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ (∫⁻ x, ENNReal.ofReal ‖inner ℝ (Φ x) (gradient (cubeCutoff a w) x)‖).toReal :=
        norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal (ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hint
    _ = ε * L + (2 * (a + w)) ^ 2 / (ε * w ^ 2) := ENNReal.toReal_ofReal (by positivity)

end Screening

end SandierSerfaty

end
