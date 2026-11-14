/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiSectorCover
public import SandierSerfaty.Geometry.VoronoiIncidence

/-!
# Sector totals: area `n` and angle `2πn`

* `modelSector_eq_polar`: the Cartesian sector `modelSector d α β` is the paper's polar sector
  `{(r, φ) : -α < φ < β, 0 < r < d sec φ}` (paper `geo:sector`);
* `volume_modelSector`: its area is `d² (tan α + tan β) / 2`;
* `volume_voronoiCell_eq_sum_voronoiSector`, `sum_sectorAngle_eq_two_pi`: the sectors of one cell
  have total area the area of the cell, and total angle `2π`;
* `sum_volume_real_voronoiSector`, `sum_sectorAngle_voronoiIncidences`: over the incidences of a
  periodic configuration of `n` points distinct modulo `Γ`, the sectors have total area
  `covolume Γ` (that is `n` on the torus `ℂ / √n ℤ[i]`) and total angle `2πn`.

Source: paper §4, Lemma `geo:voronoi`, last assertions.

Deviation from the paper: `volume_modelSector` assumes `0 ≤ d`. Stated without
hypotheses, it would be false for `d < 0` (the set is empty while `d² (tan α + tan β) / 2` can be
positive). For `tan α + tan β < 0` the set is empty and both sides vanish, so no hypothesis on the
angles is needed.
-/

open MeasureTheory Metric Set Real

public section

namespace SandierSerfaty

variable {P : Set ℂ} {p q : ℂ}

/-! ### The model sector -/

theorem isOpen_modelSector (d α β : ℝ) : IsOpen (modelSector d α β) := by
  have : modelSector d α β = {z : ℂ | 0 < z.re} ∩ {z | z.re < d} ∩
      {z | -Real.tan α * z.re < z.im} ∩ {z | z.im < Real.tan β * z.re} := by
    ext z; simp [modelSector, and_assoc]
  rw [this]
  refine (((isOpen_lt ?_ ?_).inter (isOpen_lt ?_ ?_)).inter (isOpen_lt ?_ ?_)).inter
    (isOpen_lt ?_ ?_) <;> fun_prop

theorem measurableSet_modelSector (d α β : ℝ) : MeasurableSet (modelSector d α β) :=
  (isOpen_modelSector d α β).measurableSet

/-- The polar angle of a point of the model sector lies in `(-α, β)`. -/
theorem arg_mem_of_mem_modelSector {d α β : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) {z : ℂ}
    (hz : z ∈ modelSector d α β) : -α < Complex.arg z ∧ Complex.arg z < β := by
  obtain ⟨hre, -, hlo, hhi⟩ := hz
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  obtain ⟨ha1, ha2⟩ := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre))
  have htan := Complex.tan_arg z
  have hmem : Complex.arg z ∈ Ioo (-(π / 2)) (π / 2) := ⟨ha1, ha2⟩
  constructor
  · have : Real.tan (-α) < Real.tan (Complex.arg z) := by
      rw [htan, Real.tan_neg, lt_div_iff₀ hre]; linarith
    exact (Real.strictMonoOn_tan.lt_iff_lt ⟨by linarith, by linarith⟩ hmem).1 this
  · have : Real.tan (Complex.arg z) < Real.tan β := by
      rw [htan, div_lt_iff₀ hre]; linarith
    exact (Real.strictMonoOn_tan.lt_iff_lt hmem ⟨hβ1, hβ2⟩).1 this

/-- **Polar form of the sector** (paper `geo:sector`). -/
theorem modelSector_eq_polar {d α β : ℝ} (hα : |α| < π / 2) (hβ : |β| < π / 2) :
    modelSector d α β = {z | z ≠ 0 ∧ -α < Complex.arg z ∧ Complex.arg z < β ∧
      ‖z‖ * Real.cos (Complex.arg z) < d} := by
  obtain ⟨hα1, hα2⟩ := abs_lt.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_lt.1 hβ
  ext z
  constructor
  · intro hz
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; exact lt_irrefl _ hz.1
    obtain ⟨h1, h2⟩ := arg_mem_of_mem_modelSector hα hβ hz
    refine ⟨hz0, h1, h2, ?_⟩
    rw [Complex.cos_arg hz0, mul_div_cancel₀ _ (norm_ne_zero_iff.2 hz0)]
    exact hz.2.1
  · rintro ⟨hz0, h1, h2, h3⟩
    have hmem : Complex.arg z ∈ Ioo (-(π / 2)) (π / 2) := ⟨by linarith, by linarith⟩
    have hcos : 0 < Real.cos (Complex.arg z) := Real.cos_pos_of_mem_Ioo hmem
    rw [Complex.cos_arg hz0] at h3 hcos
    rw [mul_div_cancel₀ _ (norm_ne_zero_iff.2 hz0)] at h3
    have hre : 0 < z.re := by
      have := norm_pos_iff.2 hz0
      exact (div_pos_iff_of_pos_right this).1 hcos
    have htan := Complex.tan_arg z
    refine ⟨hre, h3, ?_, ?_⟩
    · have := (Real.strictMonoOn_tan.lt_iff_lt ⟨by linarith, by linarith⟩ hmem).2 h1
      rw [htan, Real.tan_neg, lt_div_iff₀ hre] at this; linarith
    · have := (Real.strictMonoOn_tan.lt_iff_lt hmem ⟨hβ1, hβ2⟩).2 h2
      rw [htan, div_lt_iff₀ hre] at this; linarith

/-- **Area of the sector** (paper proof of `geo:voronoi`): `d² (tan α + tan β) / 2`. -/
theorem volume_modelSector {d : ℝ} (hd : 0 ≤ d) (α β : ℝ) :
    volume (modelSector d α β) = ENNReal.ofReal (d ^ 2 * (Real.tan α + Real.tan β) / 2) := by
  rcases lt_or_ge (Real.tan α + Real.tan β) 0 with hneg | hnn
  · have hempty : modelSector d α β = ∅ := by
      ext z
      simp only [mem_empty_iff_false, iff_false]
      rintro ⟨h0, -, h1, h2⟩
      nlinarith
    rw [hempty, measure_empty, ENNReal.ofReal_of_nonpos]
    have : d ^ 2 * (Real.tan α + Real.tan β) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg d) hneg.le
    linarith
  set f : ℝ → ℝ := fun x => -Real.tan α * x
  set g : ℝ → ℝ := fun x => Real.tan β * x
  have hpre : modelSector d α β =
      Complex.measurableEquivRealProd ⁻¹' regionBetween f g (Ioo 0 d) := by
    ext z
    simp only [modelSector, mem_ofPred_eq, regionBetween, mem_preimage, f, g, mem_Ioo]
    exact and_assoc.symm
  rw [hpre, Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv,
    Measure.volume_eq_prod, volume_regionBetween_eq_integral
      ((by fun_prop : Continuous f).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      ((by fun_prop : Continuous g).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
      measurableSet_Ioo (fun x hx => by
        simp only [f, g]; nlinarith [hx.1])]
  congr 1
  have : (g - f) = fun x => (Real.tan α + Real.tan β) * x := by
    funext x; simp only [Pi.sub_apply, f, g]; ring
  rw [this, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hd,
    intervalIntegral.integral_const_mul, integral_id]
  ring

/-! ### One cell -/

theorem measurableSet_voronoiSector (h : IsVoronoiNeighbor P p q) :
    MeasurableSet (voronoiSector P p q) :=
  measurableSet_image_mul_add (pairAxis_ne_zero h.ne) p (measurableSet_modelSector _ _ _)

theorem voronoiSector_subset_voronoiCell (hP : IsVoronoiSiteSet P) (h : IsVoronoiNeighbor P p q) :
    voronoiSector P p q ⊆ voronoiCell P p := by
  intro z hz q' hq'
  by_cases hq'p : q' = p
  · rw [hq'p]
  · exact (norm_sub_lt_of_mem_voronoiSector hP h hz hq' hq'p).le

/-- A site has finitely many Voronoi neighbours. -/
theorem finite_isVoronoiNeighbor (hP : IsVoronoiSiteSet P) (hp : p ∈ P) :
    {q | IsVoronoiNeighbor P p q}.Finite := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_closedBall p).1 (hP.isBounded_cell p hp)
  refine (hP.locallyFinite p (2 * R)).subset fun q h => ⟨h.2.1, ?_⟩
  obtain ⟨s, hs, -⟩ := h.2.2.2
  have hy := hR hs
  rw [mem_closedBall, dist_eq_norm] at hy
  have heq := norm_bisectorPoint_sub_eq h.ne s
  have := norm_sub_le_norm_sub_add_norm_sub q (bisectorPoint p q s) p
  rw [norm_sub_rev q (bisectorPoint p q s)] at this
  rw [mem_closedBall, dist_eq_norm]
  linarith

/-- **Area of a cell.** The sectors of a cell have total area the area of the cell. -/
theorem volume_voronoiCell_eq_sum_voronoiSector (hP : IsVoronoiSiteSet P) (hp : p ∈ P) :
    volume (voronoiCell P p) =
      ∑ q ∈ (finite_isVoronoiNeighbor hP hp).toFinset, volume (voronoiSector P p q) := by
  set Q := (finite_isVoronoiNeighbor hP hp).toFinset
  have hQ : ∀ q, q ∈ Q ↔ IsVoronoiNeighbor P p q := fun q => Set.Finite.mem_toFinset _
  have hU : (⋃ q ∈ Q, voronoiSector P p q) =
      ⋃ q ∈ {q | IsVoronoiNeighbor P p q}, voronoiSector P p q := by
    ext z; simp only [mem_iUnion, hQ, mem_ofPred_eq]
  rw [← measure_biUnion_finset (fun q hq q' hq' hqq' =>
      disjoint_voronoiSector hP ((hQ q).1 hq) ((hQ q').1 hq') (by simpa using hqq'))
      (fun q hq => measurableSet_voronoiSector ((hQ q).1 hq))]
  refine (measure_eq_measure_of_null_sdiff ?_ ?_).symm
  · exact iUnion₂_subset fun q hq => voronoiSector_subset_voronoiCell hP ((hQ q).1 hq)
  · rw [hU]; exact volume_voronoiCell_diff_iUnion_voronoiSector hP hp

/-- Near its site, a sector is the polar sector of angle `(-α, β)`. -/
theorem voronoiSector_inter_ball_subset (h : IsVoronoiNeighbor P p q) (ε : ℝ) :
    voronoiSector P p q ∩ ball p ε ⊆ (fun z => p + pairAxis p q * z) ''
      polarSector (-sectorAlpha P p q) (sectorBeta P p q) ε := by
  rintro _ ⟨⟨w, hw, rfl⟩, hb⟩
  refine mem_image_of_mem _ (mem_polarSector_iff.2 ⟨‖w‖, Complex.arg w, ?_, ?_, ?_⟩)
  · exact norm_pos_iff.2 fun h0 => by rw [h0] at hw; exact lt_irrefl _ hw.1
  · rwa [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, norm_pairAxis h.ne,
      one_mul] at hb
  · obtain ⟨h1, h2⟩ := arg_mem_of_mem_modelSector (abs_sectorAlpha_lt P p q)
      (abs_sectorBeta_lt P p q) hw
    refine ⟨h1, h2, ?_⟩
    conv_lhs => rw [← Complex.norm_mul_cos_add_sin_mul_I w]
    rw [Complex.ofReal_cos, Complex.ofReal_sin]

/-- **Angle of a cell.** The sector angles of a cell add up to `2π`. -/
theorem sum_sectorAngle_eq_two_pi (hP : IsVoronoiSiteSet P) (hp : p ∈ P) :
    ∑ q ∈ (finite_isVoronoiNeighbor hP hp).toFinset, (sectorAlpha P p q + sectorBeta P p q) =
      2 * π := by
  set Q := (finite_isVoronoiNeighbor hP hp).toFinset
  have hQ : ∀ q, q ∈ Q ↔ IsVoronoiNeighbor P p q := fun q => Set.Finite.mem_toFinset _
  refine le_antisymm (sum_sectorAngle_le hP p Q fun q hq => (hQ q).1 hq) ?_
  -- a small ball about `p` lies in the cell
  obtain ⟨δ, hδ0, hδ⟩ := exists_local_cone hP.locallyFinite p
  have hpN : p ∈ nearestSites P p := ⟨hp, mem_voronoiCell_self P p⟩
  have hNp : ∀ q ∈ nearestSites P p, q = p := fun q hq => by
    have := norm_sub_eq_of_mem_nearestSites hpN hq
    rw [sub_self, norm_zero, eq_comm, norm_eq_zero, sub_eq_zero] at this
    exact this.symm
  have hball : ∀ ε ≤ δ, ball p ε ⊆ voronoiCell P p := fun ε hε y hy => by
    rw [mem_ball, dist_eq_norm] at hy
    rw [hδ y (by linarith) p hpN]
    intro q hq; rw [hNp q hq]
  -- a common radius
  obtain ⟨ε, hε0, hεδ, hεQ⟩ : ∃ ε > 0, ε ≤ δ ∧ ∀ q ∈ Q, ε ≤ pairHalfDist p q := by
    rcases Q.eq_empty_or_nonempty with he | hne
    · exact ⟨δ, hδ0, le_rfl, fun q hq => by simp [he] at hq⟩
    · refine ⟨min δ (Q.inf' hne fun q => pairHalfDist p q),
        lt_min hδ0 ((Finset.lt_inf'_iff hne).2 fun q hq => pairHalfDist_pos ((hQ q).1 hq).ne),
        min_le_left _ _, fun q hq => (min_le_right _ _).trans (Finset.inf'_le _ hq)⟩
  -- compare areas in `ball p ε`
  have hnull := volume_voronoiCell_diff_iUnion_voronoiSector hP hp
  have hcover : ball p ε ⊆ (⋃ q ∈ Q, (voronoiSector P p q ∩ ball p ε)) ∪
      (voronoiCell P p \ ⋃ q ∈ {q | IsVoronoiNeighbor P p q}, voronoiSector P p q) := by
    intro y hy
    by_cases hyT : y ∈ ⋃ q ∈ {q | IsVoronoiNeighbor P p q}, voronoiSector P p q
    · obtain ⟨q, hq, hyq⟩ := mem_iUnion₂.1 hyT
      exact Or.inl (mem_iUnion₂.2 ⟨q, (hQ q).2 hq, hyq, hy⟩)
    · exact Or.inr ⟨hball ε hεδ hy, hyT⟩
  have hle : volume (ball p ε) ≤ ∑ q ∈ Q, volume ((fun z => p + pairAxis p q * z) ''
      polarSector (-sectorAlpha P p q) (sectorBeta P p q) ε) := by
    calc volume (ball p ε)
        ≤ volume (⋃ q ∈ Q, (voronoiSector P p q ∩ ball p ε)) + 0 := by
          rw [← hnull]; exact (measure_mono hcover).trans (measure_union_le _ _)
      _ ≤ ∑ q ∈ Q, volume (voronoiSector P p q ∩ ball p ε) := by
          rw [add_zero]; exact measure_biUnion_finset_le _ _
      _ ≤ _ := Finset.sum_le_sum fun q hq =>
          measure_mono (voronoiSector_inter_ball_subset ((hQ q).1 hq) ε)
  have hvol : ∀ q ∈ Q, volume ((fun z => p + pairAxis p q * z) ''
      polarSector (-sectorAlpha P p q) (sectorBeta P p q) ε) =
        ENNReal.ofReal ((sectorAlpha P p q + sectorBeta P p q) * ε ^ 2 / 2) := by
    intro q hq
    have hN := (hQ q).1 hq
    have ha := abs_lt.1 (abs_sectorAlpha_lt P p q)
    have hb := abs_lt.1 (abs_sectorBeta_lt P p q)
    have hab := sectorAlpha_add_sectorBeta_pos hP hN
    rw [volume_image_mul_add (norm_pairAxis hN.ne) p
      (measurableSet_polarSector (by linarith) (by linarith)),
      volume_polarSector (by linarith) (by linarith) hε0.le (by linarith), sub_neg_eq_add,
      add_comm (sectorBeta P p q)]
  rw [Finset.sum_congr rfl hvol, ← ENNReal.ofReal_sum_of_nonneg (fun q hq => by
      have := sectorAlpha_add_sectorBeta_pos hP ((hQ q).1 hq); positivity),
    Complex.volume_ball, ← ENNReal.ofReal_pow hε0.le, ← ENNReal.ofReal_coe_nnreal,
    NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun q hq => by
      have := sectorAlpha_add_sectorBeta_pos hP ((hQ q).1 hq); positivity),
    ← Finset.sum_div, ← Finset.sum_mul] at hle
  have hε2 : 0 < ε ^ 2 := by positivity
  by_contra hcon
  rw [not_le] at hcon
  have : (∑ q ∈ Q, (sectorAlpha P p q + sectorBeta P p q)) * ε ^ 2 < 2 * π * ε ^ 2 :=
    mul_lt_mul_of_pos_right hcon hε2
  linarith

/-! ### Translations -/

/-! ### Periodic totals -/

section Periodic

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {n : ℕ} (a : Fin n → ℂ)

/-- Sums over the incidences, grouped by site. -/
theorem sum_voronoiIncidences_eq {M : Type*} [AddCommMonoid M] (f : ℂ → ℂ → M) :
    ∑ e ∈ voronoiIncidences Γ a, f (a e.1) e.2 =
      ∑ i, ∑ q ∈ (finite_isVoronoiNeighbor (isVoronoiSiteSet_periodicSites Γ a)
        (mem_periodicSites Γ a i)).toFinset, f (a i) q := by
  classical
  set I := voronoiIncidences Γ a
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hinj : Set.InjOn Prod.snd (I.filter fun e => e.1 = i : Set (Fin n × ℂ)) := by
    rintro ⟨i₁, q₁⟩ h₁ ⟨i₂, q₂⟩ h₂ hq
    simp only [Finset.coe_filter, mem_ofPred_eq] at h₁ h₂
    simp only at hq
    rw [h₁.2, h₂.2, hq]
  have himg : (I.filter fun e => e.1 = i).image Prod.snd =
      (finite_isVoronoiNeighbor (isVoronoiSiteSet_periodicSites Γ a)
        (mem_periodicSites Γ a i)).toFinset := by
    ext q
    simp only [Finset.mem_image, Finset.mem_filter, Set.Finite.mem_toFinset, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨j, q'⟩, ⟨he, rfl⟩, rfl⟩
      exact (mem_voronoiIncidences Γ a).1 he
    · intro hq
      exact ⟨(i, q), ⟨(mem_voronoiIncidences Γ a).2 hq, rfl⟩, rfl⟩
  calc ∑ e ∈ I.filter (fun e => e.1 = i), f (a e.1) e.2
      = ∑ e ∈ I.filter (fun e => e.1 = i), f (a i) e.2 :=
        Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2]
    _ = ∑ q ∈ (I.filter fun e => e.1 = i).image Prod.snd, f (a i) q :=
        (Finset.sum_image (f := fun q => f (a i) q) hinj).symm
    _ = _ := by rw [himg]

/-- **Total angle `2πn`.** -/
theorem sum_sectorAngle_voronoiIncidences :
    ∑ e ∈ voronoiIncidences Γ a, (sectorAlpha (periodicSites Γ a) (a e.1) e.2 +
      sectorBeta (periodicSites Γ a) (a e.1) e.2) = 2 * π * n := by
  rw [sum_voronoiIncidences_eq Γ a (fun p q => sectorAlpha (periodicSites Γ a) p q +
    sectorBeta (periodicSites Γ a) p q)]
  rw [Finset.sum_congr rfl fun i _ => sum_sectorAngle_eq_two_pi
    (isVoronoiSiteSet_periodicSites Γ a) (mem_periodicSites Γ a i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Total area.** The sectors of the incidences have total area the covolume of `Γ`. -/
theorem sum_volume_real_voronoiSector [NeZero n] (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    ∑ e ∈ voronoiIncidences Γ a, volume.real (voronoiSector (periodicSites Γ a) (a e.1) e.2) =
      ZLattice.covolume Γ := by
  have hP := isVoronoiSiteSet_periodicSites Γ a
  rw [sum_voronoiIncidences_eq Γ a (fun p q => volume.real (voronoiSector (periodicSites Γ a) p q)),
    ← sum_volume_real_voronoiCell Γ a ha]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hp := mem_periodicSites Γ a i
  have hN : ∀ q ∈ (finite_isVoronoiNeighbor hP hp).toFinset,
      IsVoronoiNeighbor (periodicSites Γ a) (a i) q := fun q hq =>
    (Set.Finite.mem_toFinset (finite_isVoronoiNeighbor hP hp)).1 hq
  have hfin : ∀ q ∈ (finite_isVoronoiNeighbor hP hp).toFinset,
      volume (voronoiSector (periodicSites Γ a) (a i) q) ≠ ⊤ := fun q hq =>
    ((measure_mono (voronoiSector_subset_voronoiCell hP (hN q hq))).trans_lt
      (isCompact_voronoiCell Γ a hp).measure_lt_top).ne
  rw [measureReal_def, volume_voronoiCell_eq_sum_voronoiSector hP hp, ENNReal.toReal_sum hfin]
  simp only [measureReal_def]

end Periodic

end SandierSerfaty

end
