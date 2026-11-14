/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Bridge.Quadrants
public import SandierSerfaty.Screening.FieldGluing
public import SandierSerfaty.Screening.NeumannPairing

/-!
# The reflected, rescaled field (screening note, Lemma 7.1, the gluing step)

Let `Q = a₀ + [0, t]²`, `σ > 0`, `b = σ a₀`, `s = σ t`, and `E'` a Neumann charge field on `Q` with density `σ²`
and `n̄` charges `Y ⊂ Q°` with truncation radii `ρ` (`B̄(y, ρ_y) ⊂ Q°`). The four similarity images
`quadField σ a₀ e E'` are glued along the quadrant sides into `gluedField σ a₀ t E'` on `Q̂ = sq b (2 s)`:

* `Bridge.isNeumannChargeField_gluedField`: `Ê` is a Neumann charge field on `Q̂` with density `1` and the
  `4 n̄` reflected charges `reflectPts b (σ Y)`;
* `Bridge.lintegral_truncField_gluedField`: `∫_{Q̂} |Ê_ρ̂|² = 4 ∫_Q |E'_ρ|²`, with the radii
  `ρ̂ = σ ρ ∘ fold` (`Bridge.gluedRadius`).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Real

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

open Lower Screening

/-- A Neumann charge field on a set of finite measure is a field piece. -/
theorem isFieldPiece_indicator {Q : Set ℂ} (hQ : MeasurableSet Q) (hQf : volume Q ≠ ⊤) {m : ℝ}
    {Y : Finset ℂ} {E : ℂ → ℂ} (h : IsNeumannChargeField Q m Y E) :
    IsFieldPiece (Q.indicator E) Y (Q.indicator fun _ => 2 * π * m) := by
  refine ⟨(integrable_indicator_iff hQ).2 h.1, (integrable_indicator_iff hQ).2
    (integrableOn_const hQf), fun φ hφ hc => ?_⟩
  rw [← setIntegral_inner_eq_integral_indicator hQ, h.2 φ hφ hc]
  have : (fun x => Q.indicator (fun _ => 2 * π * m) x * φ x) =
      Q.indicator fun x => 2 * π * m * φ x := by
    ext x; by_cases hx : x ∈ Q <;> simp [hx]
  rw [this, integral_indicator hQ, integral_const_mul]
  ring

variable (σ : ℝ) (a₀ : ℂ) (t : ℝ)

/-- The glued field on `sq (σ a₀) (2 σ t)`. -/
@[expose] noncomputable def gluedField (E : ℂ → ℂ) : ℂ → ℂ :=
  ∑ e : Fin 4, (quadClosed (σ • a₀) (σ * t) e).indicator (quadField σ a₀ e E)

/-- The folding map back to `Q`. -/
@[expose] noncomputable def foldPt (x : ℂ) : ℂ :=
  a₀ + ⟨|(x - σ • a₀).re| / σ, |(x - σ • a₀).im| / σ⟩

/-- The glued truncation radii `σ ρ ∘ fold`. -/
@[expose] noncomputable def gluedRadius (ρ : ℂ → ℝ) (x : ℂ) : ℝ := σ * ρ (foldPt σ a₀ x)

variable {σ a₀ t}

theorem abs_sgn_mul {v u : ℝ} (hv : v = 1 ∨ v = -1) : |v * u| = |u| := by
  rcases hv with rfl | rfl <;> simp

theorem foldPt_quadMap (hσ : 0 < σ) (e : Fin 4) {y : ℂ} (hy : y ∈ sqAt a₀ t) :
    foldPt σ a₀ (quadMap σ a₀ e y) = y := by
  obtain ⟨h1, -, h3, -⟩ := hy
  apply Complex.ext
  · have h := quadMap_re (σ := σ) (a₀ := a₀) e y
    show a₀.re + |(quadMap σ a₀ e y - σ • a₀).re| / σ = y.re
    rw [h, abs_sgn_mul (sgnRe_eq e),
      abs_of_nonneg (mul_nonneg hσ.le (by rw [Complex.sub_re]; linarith)), Complex.sub_re]
    field_simp; ring
  · have h := quadMap_im (σ := σ) (a₀ := a₀) e y
    show a₀.im + |(quadMap σ a₀ e y - σ • a₀).im| / σ = y.im
    rw [h, abs_sgn_mul (sgnIm_eq e),
      abs_of_nonneg (mul_nonneg hσ.le (by rw [Complex.sub_im]; linarith)), Complex.sub_im]
    field_simp; ring

theorem gluedRadius_quadMap (hσ : 0 < σ) (ρ : ℂ → ℝ) (e : Fin 4) {y : ℂ} (hy : y ∈ sqAt a₀ t) :
    gluedRadius σ a₀ ρ (quadMap σ a₀ e y) = σ * ρ y := by
  rw [gluedRadius, foldPt_quadMap hσ e hy]

theorem simInv_quadMap (hσ : 0 < σ) (e : Fin 4) (y : ℂ) :
    simInv σ (quadL e) (quadC σ a₀ e) (quadMap σ a₀ e y) = y :=
  simInv_simMap hσ.ne' y

theorem gluedField_eq (e : Fin 4) {x : ℂ} (hx : x ∈ quadOpen (σ • a₀) (σ * t) e) (E : ℂ → ℂ) :
    gluedField σ a₀ t E x = quadField σ a₀ e E x := by
  rw [gluedField, Finset.sum_apply, Finset.sum_eq_single e]
  · exact indicator_of_mem (quadOpen_subset_quadClosed _ _ _ hx) _
  · intro e' _ he'
    exact indicator_of_notMem (Set.disjoint_left.1
      (disjoint_quadOpen_quadClosed _ _ (Ne.symm he')) hx) _
  · simp

/-! ### The charges -/

variable {nb : ℕ} {Y : Fin nb → ℂ}

/-- The charges of the `e`-th copy. -/
@[expose] noncomputable def quadPts (σ : ℝ) (a₀ : ℂ) (Y : Fin nb → ℂ) (e : Fin 4) : Finset ℂ :=
  (Finset.univ.image Y).image (quadMap σ a₀ e)

theorem quadPts_subset (hσ : 0 < σ) (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) (e : Fin 4) :
    (quadPts σ a₀ Y e : Set ℂ) ⊆ quadOpen (σ • a₀) (σ * t) e := by
  intro x hx
  simp only [quadPts, Finset.coe_image, Finset.coe_univ, image_univ, mem_image, mem_range] at hx
  obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hx
  exact (quadMap_mem_quadOpen_iff hσ e _).2 (hY i)

theorem pairwiseDisjoint_quadPts (hσ : 0 < σ) (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) :
    ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint (quadPts σ a₀ Y) := by
  intro e _ e' _ he
  rw [Function.onFun, ← Finset.disjoint_coe]
  exact ((pairwise_disjoint_quadOpen _ _ he).mono (quadPts_subset hσ hY e)
    (quadPts_subset hσ hY e'))

theorem biUnion_quadPts :
    Finset.univ.biUnion (quadPts σ a₀ Y) =
      Finset.univ.image (reflectPts (σ • a₀) (fun i => σ • Y i)) := by
  classical
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, quadPts, Finset.mem_image]
  constructor
  · rintro ⟨e, _, ⟨i, rfl⟩, rfl⟩
    exact ⟨finProdFinEquiv (e, i), reflectPts_eq_quadMap Y e i⟩
  · rintro ⟨k, rfl⟩
    refine ⟨(finProdFinEquiv.symm k).1, Y (finProdFinEquiv.symm k).2, ⟨_, rfl⟩, ?_⟩
    rw [← reflectPts_eq_quadMap Y, Prod.mk.eta, Equiv.apply_symm_apply]

/-! ### The Neumann identity -/

theorem volume_quadClosed_ne_top (b : ℂ) (s : ℝ) (e : Fin 4) : volume (quadClosed b s e) ≠ ⊤ :=
  ((isCompact_sq b (2 * s)).measure_lt_top.trans_le' (measure_mono (quadClosed_subset_sq b s e))).ne

/-- **The glued field is a Neumann charge field** on `sq (σ a₀) (2 σ t)` with density `1` and the
`4 n̄` reflected charges. -/
theorem isNeumannChargeField_gluedField (hσ : 0 < σ) (hY : ∀ i, Y i ∈ interior (sqAt a₀ t))
    {E : ℂ → ℂ} (hE : IsNeumannChargeField (sqAt a₀ t) (σ ^ 2) (Finset.univ.image Y) E) :
    IsNeumannChargeField (sq (σ • a₀) (2 * (σ * t))) 1
      (Finset.univ.image (reflectPts (σ • a₀) (fun i => σ • Y i))) (gluedField σ a₀ t E) := by
  classical
  rw [← biUnion_quadPts]
  have hE1 : IsNeumannChargeField (sqAt a₀ t) (σ ^ 2 * 1) (Finset.univ.image Y) E := by
    rwa [mul_one]
  refine isNeumannChargeField_finsetSum Finset.univ
    (ρ := fun e => (quadClosed (σ • a₀) (σ * t) e).indicator fun _ => 2 * π * 1)
    (fun e _ => ?_) (pairwiseDisjoint_quadPts hσ hY) (measurableSet_sq _ _)
    (fun e _ => Eventually.of_forall fun x hx => indicator_of_notMem
      (fun h => hx (quadClosed_subset_sq _ _ e h)) _) ?_
  · have h := isNeumannChargeField_simField (L := quadL e) (c := quadC σ a₀ e) hσ
      (by rw [sqAt_eq_sq]; exact measurableSet_sq _ _) hE1
    rw [← quadMap, image_quadMap_sqAt hσ] at h
    exact isFieldPiece_indicator (measurableSet_quadClosed _ _ e) (volume_quadClosed_ne_top _ _ e) h
  · filter_upwards [ae_exists_mem_quadOpen (σ • a₀) (σ * t)] with x hx
    rw [Finset.sum_apply]
    by_cases hxQ : x ∈ sq (σ • a₀) (2 * (σ * t))
    · obtain ⟨e, he⟩ := hx hxQ
      rw [indicator_of_mem hxQ, Finset.sum_eq_single e]
      · exact indicator_of_mem (quadOpen_subset_quadClosed _ _ _ he) _
      · intro e' _ he'
        exact indicator_of_notMem (Set.disjoint_left.1
          (disjoint_quadOpen_quadClosed _ _ (Ne.symm he')) he) _
      · simp
    · rw [indicator_of_notMem hxQ]
      exact Finset.sum_eq_zero fun e _ => indicator_of_notMem
        (fun h => hxQ (quadClosed_subset_sq _ _ e h)) _

/-! ### The energy identity -/

theorem coe_image_univ (Y : Fin nb → ℂ) : ((Finset.univ.image Y : Finset ℂ) : Set ℂ) = range Y := by
  simp

variable {ρ : ℂ → ℝ}

/-- The cross terms vanish: a charge of another copy does not see an open quadrant. -/
theorem gradient_truncLog_cross (hσ : 0 < σ) (hρ : ∀ i, 0 < ρ (Y i))
    (hball : ∀ i, closedBall (Y i) (ρ (Y i)) ⊆ interior (sqAt a₀ t)) {e e' : Fin 4} (he : e ≠ e')
    {x : ℂ} (hx : x ∈ quadOpen (σ • a₀) (σ * t) e) (i : Fin nb) :
    gradient (truncLog (σ * ρ (Y i))) (x - quadMap σ a₀ e' (Y i)) = 0 := by
  refine gradient_truncLog_of_gt (mul_pos hσ (hρ i)) (lt_of_not_ge fun hle => ?_)
  obtain ⟨z, rfl⟩ := quadMap_surjective (a₀ := a₀) hσ e' x
  rw [norm_quadMap_sub hσ, mul_le_mul_iff_right₀ hσ] at hle
  have hz : z ∈ interior (sqAt a₀ t) := hball i (mem_closedBall.2 (by rwa [dist_eq_norm]))
  rw [← quadMap_mem_quadOpen_iff hσ e'] at hz
  exact Set.disjoint_left.1 (disjoint_quadOpen_quadClosed _ _ he) hx
    (quadOpen_subset_quadClosed _ _ _ hz)

theorem truncField_gluedField_eq (hσ : 0 < σ) (_hYi : Function.Injective Y)
    (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) (hρ : ∀ i, 0 < ρ (Y i))
    (hball : ∀ i, closedBall (Y i) (ρ (Y i)) ⊆ interior (sqAt a₀ t)) (e : Fin 4) (E : ℂ → ℂ)
    {x : ℂ} (hx : x ∈ quadOpen (σ • a₀) (σ * t) e) :
    truncField (range (reflectPts (σ • a₀) (fun i => σ • Y i))) (gluedRadius σ a₀ ρ)
        (gluedField σ a₀ t E) x =
      truncField (↑(quadPts σ a₀ Y e))
        (fun x => σ * ρ (simInv σ (quadL e) (quadC σ a₀ e) x)) (quadField σ a₀ e E) x := by
  classical
  have hrange : range (reflectPts (σ • a₀) (fun i => σ • Y i)) =
      ↑(Finset.univ.biUnion (quadPts σ a₀ Y)) := by
    rw [biUnion_quadPts, coe_image_univ]
  unfold truncField
  rw [gluedField_eq e hx, hrange, finsum_mem_coe_finset, finsum_mem_coe_finset,
    Finset.sum_biUnion (pairwiseDisjoint_quadPts hσ hY), Finset.sum_eq_single e]
  · congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [quadPts, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hp
    beta_reduce
    rw [gluedRadius_quadMap hσ ρ e (interior_subset (hY i)), simInv_quadMap hσ]
  · intro e' _ he'
    refine Finset.sum_eq_zero fun p hp => ?_
    simp only [quadPts, Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨_, ⟨i, rfl⟩, rfl⟩ := hp
    rw [gluedRadius_quadMap hσ ρ e' (interior_subset (hY i))]
    exact gradient_truncLog_cross hσ hρ hball (Ne.symm he') hx i
  · simp

theorem norm_truncField_gluedField (hσ : 0 < σ) (hYi : Function.Injective Y)
    (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) (hρ : ∀ i, 0 < ρ (Y i))
    (hball : ∀ i, closedBall (Y i) (ρ (Y i)) ⊆ interior (sqAt a₀ t)) (e : Fin 4) (E : ℂ → ℂ)
    {y : ℂ} (hy : y ∈ interior (sqAt a₀ t)) (hyY : y ∉ range Y) :
    ‖truncField (range (reflectPts (σ • a₀) (fun i => σ • Y i))) (gluedRadius σ a₀ ρ)
        (gluedField σ a₀ t E) (quadMap σ a₀ e y)‖ ^ 2 =
      (σ ^ 2)⁻¹ * ‖truncField (range Y) ρ E y‖ ^ 2 := by
  rw [truncField_gluedField_eq hσ hYi hY hρ hball e E ((quadMap_mem_quadOpen_iff hσ e y).2 hy),
    ← coe_image_univ]
  refine norm_truncField_simField hσ (Finset.univ.image Y) (fun p hp => ?_) E ?_
  · simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    exact hρ i
  · rwa [← Finset.mem_coe, coe_image_univ]

/-- **The energy identity**: `∫_{Q̂} |Ê_ρ̂|² = 4 ∫_Q |E_ρ|²`. -/
theorem lintegral_truncField_gluedField (hσ : 0 < σ) (hYi : Function.Injective Y)
    (hY : ∀ i, Y i ∈ interior (sqAt a₀ t)) (hρ : ∀ i, 0 < ρ (Y i))
    (hball : ∀ i, closedBall (Y i) (ρ (Y i)) ⊆ interior (sqAt a₀ t)) (E : ℂ → ℂ) :
    ∫⁻ x in sq (σ • a₀) (2 * (σ * t)),
        ENNReal.ofReal (‖truncField (range (reflectPts (σ • a₀) (fun i => σ • Y i)))
          (gluedRadius σ a₀ ρ) (gluedField σ a₀ t E) x‖ ^ 2) =
      4 * ∫⁻ y in sqAt a₀ t, ENNReal.ofReal (‖truncField (range Y) ρ E y‖ ^ 2) := by
  set G : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖truncField
    (range (reflectPts (σ • a₀) (fun i => σ • Y i))) (gluedRadius σ a₀ ρ) (gluedField σ a₀ t E) x‖ ^ 2)
    with hG
  have hnull : ∀ᵐ y ∂volume, y ∉ range Y :=
    measure_eq_zero_iff_ae_notMem.1 ((Set.finite_range Y).measure_zero volume)
  have hpiece : ∀ e, ∫⁻ x in quadOpen (σ • a₀) (σ * t) e, G x =
      ∫⁻ y in sqAt a₀ t, ENNReal.ofReal (‖truncField (range Y) ρ E y‖ ^ 2) := by
    intro e
    rw [← image_quadMap_interior hσ e, quadMap, setLIntegral_image_simMap hσ isOpen_interior.measurableSet,
      ← setLIntegral_congr (interior_sqAt_ae_eq a₀ t)]
    have hcongr : ∫⁻ y in interior (sqAt a₀ t), G (simMap σ (quadL e) (quadC σ a₀ e) y) =
        ∫⁻ y in interior (sqAt a₀ t), ENNReal.ofReal (σ ^ 2)⁻¹ *
          ENNReal.ofReal (‖truncField (range Y) ρ E y‖ ^ 2) := by
      refine setLIntegral_congr_fun_ae isOpen_interior.measurableSet ?_
      filter_upwards [hnull] with y hyY hy
      rw [hG]
      beta_reduce
      rw [← quadMap, norm_truncField_gluedField hσ hYi hY hρ hball e E hy hyY,
        ENNReal.ofReal_mul (by positivity)]
    rw [hcongr, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
      one_mul]
  rw [setLIntegral_congr (sq_ae_eq_iUnion_quadOpen _ _),
    lintegral_iUnion (measurableSet_quadOpen _ _) (pairwise_disjoint_quadOpen _ _), tsum_fintype]
  rw [Finset.sum_congr rfl fun e _ => hpiece e, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

end Bridge

end Sphere

end SandierSerfaty

end
