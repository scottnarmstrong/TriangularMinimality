/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.Glue
public import SandierSerfaty.Geometry.VoronoiSectorTotals
public import SandierSerfaty.Analysis.WeylCalculus
public import SandierSerfaty.Torus.PotentialLocal

/-!
# Smoothness of the glued potential on open sectors, and its expansion at the sites

On the open sector `voronoiSector P p q` the gauge is the linear form `gaugeLin p q`, so
`gluedH` coincides there with `Hsec R p q z = Fpair R (‖z - p‖, gaugeLin p q (z - p))`.
This is the sector formula `H(r, φ) = B(r) + ∑ᵢ (r/t(φ))^{kᵢ} Dᵢ(t(φ))`, `t = d sec φ`
(paper `dual:trial`).

* `hasFDerivAt_Hsec`: differentiability of `Hsec` at points of the open sector, with the derivative
  `B'(r) ∇r + ∑ᵢ (termDeriv R i)(Ψ z) ∘ Ψ'`, `Ψ z = (‖z - p‖, gaugeLin p q (z - p))`
  (termwise differentiation of the series on the sector; paper proof of `dual:gluing`);
* `norm_fderiv_Hsec_sub_le`: `‖∇H + e_r / r‖ ≤ C r` (paper `(dual:singularity)`, gradient part);
* `abs_gluedH_add_log_le`: `|H + log r| ≤ C r²` on the cells (value part);
* `lipschitzOnWith_gluedH_add_log`: `H + log ‖· - p‖` extends to a Lipschitz function across the site
  with value `0` (so `H = -log r + O(r²)` with zero constant term, and `h - H` is Lipschitz near `p`).
-/

open Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Dual

variable {ι : Type*} {R : RadialData ι} {P : Set ℂ} {d₀ : ℝ} {p q z : ℂ}

theorem exists_bnd (hR : R.IsAdmissible d₀) (hS : SepSites P d₀) :
    ∃ (R₁ T₀ : ℝ) (M : ι → ℝ), (∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁) ∧ R₁ ≤ T₀ ∧
      d₀ < T₀ ∧ Bnd R d₀ T₀ M := by
  obtain ⟨R₁, hR₁⟩ := hS.bdd
  obtain ⟨M, hMs, hMb⟩ := hR.summable (max R₁ (d₀ + 1))
    (lt_of_lt_of_le (by linarith) (le_max_right _ _))
  exact ⟨R₁, max R₁ (d₀ + 1), M, hR₁, le_max_left _ _,
    lt_of_lt_of_le (by linarith) (le_max_right _ _), hMs, hMb⟩

/-- The sector formula: the trial function on the sector of `(p, q)`. -/
@[expose] noncomputable def Hsec (R : RadialData ι) (p q z : ℂ) : ℝ :=
  Fpair R (‖z - p‖, gaugeLin p q (z - p))

theorem gluedH_eq_Hsec (hS : SepSites P d₀) (h : IsVoronoiNeighbor P p q)
    (hz : z ∈ voronoiSector P p q) : gluedH R P z = Hsec R p q z := by
  have hSS := hS.isVoronoiSiteSet
  rw [gluedH_eq_cellH hS h.1 (voronoiSector_subset_voronoiCell hSS h hz)]
  unfold cellH Hsec
  rw [gauge_eq_gaugeLin_of_mem_sector hS h.1 h hz]

theorem isOpen_voronoiSector (h : IsVoronoiNeighbor P p q) : IsOpen (voronoiSector P p q) := by
  have hu := pairAxis_ne_zero h.ne
  have : voronoiSector P p q = (fun z => p + pairAxis p q * z) ''
      modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q) := rfl
  rw [this]
  have h1 := (Homeomorph.mulLeft₀ (pairAxis p q) hu).isOpenMap
  have h2 := (Homeomorph.addLeft p).isOpenMap
  have := h2 _ (h1 _ (isOpen_modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q)))
  convert this using 1
  ext z; simp [Set.image_image]

theorem convex_modelSector (d α β : ℝ) : Convex ℝ (modelSector d α β) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4⟩ := hy
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp
  show 0 < (a • x + b • y).re ∧ (a • x + b • y).re < d ∧
    -Real.tan α * (a • x + b • y).re < (a • x + b • y).im ∧
    (a • x + b • y).im < Real.tan β * (a • x + b • y).re
  rw [hre, him]
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this
    simp only [zero_mul, zero_add, one_mul]
    exact ⟨hy1, hy2, hy3, hy4⟩
  · refine ⟨by linarith [mul_pos ha' hx1, mul_nonneg hb hy1.le],
      by nlinarith [mul_pos ha' (sub_pos.2 hx2), mul_nonneg hb (sub_pos.2 hy2).le],
      by linarith [mul_pos ha' (sub_pos.2 hx3), mul_nonneg hb (sub_pos.2 hy3).le],
      by linarith [mul_pos ha' (sub_pos.2 hx4), mul_nonneg hb (sub_pos.2 hy4).le]⟩

theorem convex_voronoiSector : Convex ℝ (voronoiSector P p q) := by
  have : voronoiSector P p q = (fun z => p + pairAxis p q * z) ''
      modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q) := rfl
  rw [this]
  have hlin : IsLinearMap ℝ (fun z : ℂ => pairAxis p q * z) :=
    ⟨fun x y => mul_add _ _ _, fun c x => by simp [mul_left_comm]⟩
  have := ((convex_modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q)).is_linear_image
    hlin).translate p
  convert this using 1
  ext z; simp [Set.image_image]

/-- The derivative of the norm away from the centre. -/
theorem hasFDerivAt_norm_sub {c y : ℂ} (hy : y ≠ c) :
    HasFDerivAt (fun z : ℂ => ‖z - c‖) ((‖y - c‖)⁻¹ • innerSL ℝ (y - c)) y := by
  have hn : 0 < ‖y - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have h1 := (Weyl.hasFDerivAt_normSq_sub c y).sqrt (by positivity)
  have e : (fun z : ℂ => Real.sqrt (‖z - c‖ ^ 2)) = fun z => ‖z - c‖ := by
    funext z; exact Real.sqrt_sq (norm_nonneg _)
  rw [e] at h1
  convert h1 using 1
  rw [Real.sqrt_sq hn.le]
  ext w
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- The linear form `gaugeLin p q` as a continuous linear functional. -/
@[expose] noncomputable def gaugeCLM (p q : ℂ) : ℂ →L[ℝ] ℝ :=
  (2 / ‖q - p‖ ^ 2) • innerSL ℝ (q - p)

theorem gaugeCLM_apply (p q w : ℂ) : gaugeCLM p q w = gaugeLin p q w := by
  simp only [gaugeCLM, gaugeLin, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [Complex.inner, mul_comm w]
  ring

/-- The map `z ↦ (‖z - p‖, gaugeLin p q (z - p))` of the sector variables. -/
@[expose] noncomputable def Psi (p q z : ℂ) : ℝ × ℝ := (‖z - p‖, gaugeLin p q (z - p))

theorem ne_of_mem_voronoiSector (h : IsVoronoiNeighbor P p q) (hz : z ∈ voronoiSector P p q) :
    z ≠ p := by
  obtain ⟨w, ⟨hw0, -⟩, rfl⟩ := hz
  intro h0
  have hu := pairAxis_ne_zero h.ne
  have : pairAxis p q * w = 0 := by linear_combination h0
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hu h1
  · rw [h1] at hw0; simp at hw0

theorem lipschitzWith_gaugeLin_sub (hS : SepSites P d₀) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    LipschitzWith (Real.toNNReal (1 / d₀)) (fun z : ℂ => gaugeLin p q (z - p)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (by have := hS.pos; positivity)]
  have e : gaugeLin p q (x - p) - gaugeLin p q (y - p) = gaugeLin p q (x - y) := by
    rw [← gaugeCLM_apply, ← gaugeCLM_apply, ← gaugeCLM_apply, ← map_sub]; congr 1; ring
  rw [e, one_div, inv_mul_eq_div]
  exact (abs_gaugeLin_le hpq (hS.sep p hp q hq hpq) hS.pos _)

theorem lipschitzWith_Psi (hS : SepSites P d₀) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    LipschitzWith (max 1 (Real.toNNReal (1 / d₀))) (Psi p q) :=
  (lipschitzWith_norm_sub p).prodMk (lipschitzWith_gaugeLin_sub hS hp hq hpq)

theorem hasFDerivAt_Psi (hz : z ≠ p) :
    HasFDerivAt (Psi p q) (((‖z - p‖)⁻¹ • innerSL ℝ (z - p)).prod (gaugeCLM p q)) z := by
  have h1 := hasFDerivAt_norm_sub (c := p) hz
  have h2 : HasFDerivAt (fun y : ℂ => gaugeLin p q (y - p)) (gaugeCLM p q) z := by
    have := (gaugeCLM p q).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const p)
    simpa [Function.comp_def, gaugeCLM_apply] using this
  exact h1.prodMk h2

theorem norm_fderiv_Psi_le (hS : SepSites P d₀) (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    (hz : z ≠ p) : ‖((‖z - p‖)⁻¹ • innerSL ℝ (z - p)).prod (gaugeCLM p q)‖ ≤
      max 1 (Real.toNNReal (1 / d₀)) :=
  (hasFDerivAt_Psi hz).le_of_lipschitz (lipschitzWith_Psi hS hp hq hpq)

theorem Psi_mem_cone (hS : SepSites P d₀) (h : IsVoronoiNeighbor P p q) {R₁ T₀ : ℝ}
    (hR₁ : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁) (hT : R₁ ≤ T₀)
    (hz : z ∈ voronoiSector P p q) : Psi p q z ∈ cone d₀ T₀ := by
  have := mem_cone_of_mem_cell hS h.1 hR₁ hT
    (voronoiSector_subset_voronoiCell hS.isVoronoiSiteSet h hz) (ne_of_mem_voronoiSector h hz)
  rwa [gauge_eq_gaugeLin_of_mem_sector hS h.1 h hz] at this

/-- **Termwise differentiation on the open sector** (paper proof of `dual:gluing`). -/
theorem hasFDerivAt_serF_Psi (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    (h : IsVoronoiNeighbor P p q) {R₁ T₀ : ℝ} (hR₁ : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁)
    (hT : R₁ ≤ T₀) {M : ι → ℝ} (hM : Bnd R d₀ T₀ M) (hz : z ∈ voronoiSector P p q) :
    HasFDerivAt (fun y => serF R (Psi p q y))
      (∑' i, (termDeriv R i (Psi p q z)).comp
        (((‖z - p‖)⁻¹ • innerSL ℝ (z - p)).prod (gaugeCLM p q))) z := by
  set K : NNReal := max 1 (Real.toNNReal (1 / d₀)) with hK
  have hMn : ∀ i, 0 ≤ M i := fun i => hM.nonneg hS.pos (by
    have := (div_mem_Icc_of_mem_cone (Psi_mem_cone hS h hR₁ hT hz)); linarith [this.1, this.2]) i
  have hu : Summable fun i => (2 + 1 / d₀) * M i * (K : ℝ) :=
    (hM.summable.mul_left (2 + 1 / d₀)).mul_right _
  have hpne : ∀ y ∈ voronoiSector P p q, y ≠ p := fun y hy => ne_of_mem_voronoiSector h hy
  have hfd : ∀ i, ∀ y ∈ voronoiSector P p q, HasFDerivAt (fun y => termFn R i (Psi p q y))
      ((termDeriv R i (Psi p q y)).comp
        (((‖y - p‖)⁻¹ • innerSL ℝ (y - p)).prod (gaugeCLM p q))) y := by
    intro i y hy
    have hc := Psi_mem_cone hS h hR₁ hT hy
    have h1 : HasFDerivAt (termFn R i) (termDeriv R i (Psi p q y)) (Psi p q y) :=
      hasFDerivAt_termFn' R hR.contDiffOn_D hc.1 (by
        obtain ⟨h1, -, h3, -⟩ := hc; have := hS.pos; simp only [Psi] at *; nlinarith)
    exact h1.comp y (hasFDerivAt_Psi (hpne y hy))
  have := hasFDerivAt_tsum_of_isPreconnected (f := fun i y => termFn R i (Psi p q y))
    (f' := fun i y => (termDeriv R i (Psi p q y)).comp
        (((‖y - p‖)⁻¹ • innerSL ℝ (y - p)).prod (gaugeCLM p q)))
    (u := fun i => (2 + 1 / d₀) * M i * (K : ℝ)) (s := voronoiSector P p q)
    (x₀ := z) (x := z) hu (isOpen_voronoiSector h) (convex_voronoiSector.isPreconnected) hfd
    (fun i y hy => by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have h1 := norm_termDeriv_le hR hM hS.pos i (Psi_mem_cone hS h hR₁ hT hy)
      have h2 := norm_fderiv_Psi_le hS h.1 h.2.1 h.2.2.1 (hpne y hy)
      have hp1 : (Psi p q y).2 ^ (R.k i - 1) ≤ 1 :=
        pow_le_one₀ (Psi_mem_cone hS h hR₁ hT hy).1.le (Psi_mem_cone hS h hR₁ hT hy).2.1
      have h3 : ‖termDeriv R i (Psi p q y)‖ ≤ (2 + 1 / d₀) * M i := by
        refine h1.trans ?_
        have : 0 ≤ (2 + 1 / d₀) * M i := mul_nonneg (by have := hS.pos; positivity) (hMn i)
        linarith [mul_nonneg (mul_nonneg (by have := hS.pos; positivity : (0:ℝ) ≤ 2 + 1 / d₀) (hMn i))
          (sub_nonneg.2 hp1)]
      exact mul_le_mul h3 h2 (norm_nonneg _) (mul_nonneg (by have := hS.pos; positivity) (hMn i)))
    hz (summable_termFn hM hR hS.pos (Psi_mem_cone hS h hR₁ hT hz)) hz
  simpa [serF] using this

theorem hasFDerivAt_Hsec (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    (h : IsVoronoiNeighbor P p q) {R₁ T₀ : ℝ} (hR₁ : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁)
    (hT : R₁ ≤ T₀) {M : ι → ℝ} (hM : Bnd R d₀ T₀ M) (hz : z ∈ voronoiSector P p q) :
    HasFDerivAt (Hsec R p q)
      (deriv R.B ‖z - p‖ • ((‖z - p‖)⁻¹ • innerSL ℝ (z - p)) +
        ∑' i, (termDeriv R i (Psi p q z)).comp
          (((‖z - p‖)⁻¹ • innerSL ℝ (z - p)).prod (gaugeCLM p q))) z := by
  have hzp := ne_of_mem_voronoiSector h hz
  have hr : 0 < ‖z - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hzp)
  have hB : HasDerivAt R.B (deriv R.B ‖z - p‖) ‖z - p‖ :=
    (((hR.contDiffOn_B).contDiffAt (isOpen_Ioi.mem_nhds hr)).differentiableAt one_ne_zero).hasDerivAt
  have h1 := hB.comp_hasFDerivAt z (hasFDerivAt_norm_sub (c := p) hzp)
  exact h1.add (hasFDerivAt_serF_Psi hR hS h hR₁ hT hM hz)

theorem norm_inv_smul_innerSL {w : ℂ} (hw : w ≠ 0) :
    ‖(‖w‖)⁻¹ • innerSL ℝ w‖ = 1 := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  rw [norm_smul, norm_inv, norm_norm, innerSL_apply_norm]
  field_simp

/-- The series part of the derivative is `O(r⁵)`. -/
theorem norm_series_deriv_le (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    (h : IsVoronoiNeighbor P p q) {R₁ T₀ : ℝ} (hR₁ : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁)
    (hT : R₁ ≤ T₀) {M : ι → ℝ} (hM : Bnd R d₀ T₀ M) (hz : z ∈ voronoiSector P p q) :
    ‖∑' i, (termDeriv R i (Psi p q z)).comp
      (((‖z - p‖)⁻¹ • innerSL ℝ (z - p)).prod (gaugeCLM p q))‖ ≤
      (2 + 1 / d₀) * (max 1 (Real.toNNReal (1 / d₀)) : NNReal) *
        ((‖z - p‖ / d₀) ^ 5 * ∑' i, M i) := by
  set K : NNReal := max 1 (Real.toNNReal (1 / d₀)) with hK
  have hd := hS.pos
  have hc := Psi_mem_cone hS h hR₁ hT hz
  have hMn : ∀ i, 0 ≤ M i := fun i => hM.nonneg hd (by
    have := (div_mem_Icc_of_mem_cone hc); linarith [this.1, this.2]) i
  have hpne := ne_of_mem_voronoiSector h hz
  have hg1 : (Psi p q z).2 ≤ 1 := hc.2.1
  have hg0 : 0 ≤ (Psi p q z).2 := hc.1.le
  have hgr : (Psi p q z).2 ≤ ‖z - p‖ / d₀ := by
    have := (le_abs_self _).trans (abs_gaugeLin_le h.ne (hS.sep p h.1 q h.2.1 h.ne) hd (z - p))
    simpa [Psi] using this
  have hsum : Summable fun i => (2 + 1 / d₀) * (K : ℝ) * ((‖z - p‖ / d₀) ^ 5 * M i) :=
    (hM.summable.mul_left _).mul_left _
  have key : ∀ i, ‖(termDeriv R i (Psi p q z)).comp
      (((‖z - p‖)⁻¹ • innerSL ℝ (z - p)).prod (gaugeCLM p q))‖ ≤
      (2 + 1 / d₀) * (K : ℝ) * ((‖z - p‖ / d₀) ^ 5 * M i) := by
    intro i
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := norm_termDeriv_le hR hM hd i hc
    have h2 := norm_fderiv_Psi_le hS h.1 h.2.1 h.2.2.1 hpne
    have hk : 5 ≤ R.k i - 1 := by have := hR.six_le i; omega
    have hp5 : (Psi p q z).2 ^ (R.k i - 1) ≤ (‖z - p‖ / d₀) ^ 5 :=
      (pow_le_pow_of_le_one hg0 hg1 hk).trans (pow_le_pow_left₀ hg0 hgr 5)
    have h3 : ‖termDeriv R i (Psi p q z)‖ ≤ (2 + 1 / d₀) * ((‖z - p‖ / d₀) ^ 5 * M i) := by
      refine h1.trans ?_
      have : 0 ≤ (2 + 1 / d₀) * M i := mul_nonneg (by positivity) (hMn i)
      calc (Psi p q z).2 ^ (R.k i - 1) * (2 + 1 / d₀) * M i
          = ((Psi p q z).2 ^ (R.k i - 1)) * ((2 + 1 / d₀) * M i) := by ring
        _ ≤ (‖z - p‖ / d₀) ^ 5 * ((2 + 1 / d₀) * M i) :=
            mul_le_mul_of_nonneg_right hp5 this
        _ = (2 + 1 / d₀) * ((‖z - p‖ / d₀) ^ 5 * M i) := by ring
    calc _ ≤ ((2 + 1 / d₀) * ((‖z - p‖ / d₀) ^ 5 * M i)) * (K : ℝ) :=
          mul_le_mul h3 h2 (norm_nonneg _) (mul_nonneg (by positivity)
            (mul_nonneg (by positivity) (hMn i)))
      _ = _ := by ring
  have := tsum_of_norm_bounded hsum.hasSum key
  refine this.trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_mul_left]

/-- **`∇H = -e_r / r + O(r)` on a sector** (derivative part of `(dual:singularity)`). -/
theorem norm_fderiv_Hsec_add_le (hR : R.IsAdmissible d₀) (hS : SepSites P d₀)
    (h : IsVoronoiNeighbor P p q) {R₁ T₀ : ℝ} (hR₁ : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁)
    (hT : R₁ ≤ T₀) {M : ι → ℝ} (hM : Bnd R d₀ T₀ M) (hz : z ∈ voronoiSector P p q) :
    ‖fderiv ℝ (Hsec R p q) z + innerSL ℝ ((1 / ‖z - p‖ ^ 2 : ℝ) • (z - p))‖ ≤
      |deriv R.B ‖z - p‖ + 1 / ‖z - p‖| +
        (2 + 1 / d₀) * (max 1 (Real.toNNReal (1 / d₀)) : NNReal) *
          ((‖z - p‖ / d₀) ^ 5 * ∑' i, M i) := by
  set r := ‖z - p‖ with hrdef
  have hzp := ne_of_mem_voronoiSector h hz
  have hr : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hzp)
  have hD := hasFDerivAt_Hsec hR hS h hR₁ hT hM hz
  rw [hD.fderiv]
  set Ser := ∑' i, (termDeriv R i (Psi p q z)).comp
          (((r)⁻¹ • innerSL ℝ (z - p)).prod (gaugeCLM p q)) with hSer
  have e : deriv R.B r • (r⁻¹ • innerSL ℝ (z - p)) + Ser + innerSL ℝ ((1 / r ^ 2 : ℝ) • (z - p)) =
      (deriv R.B r + 1 / r) • (r⁻¹ • innerSL ℝ (z - p)) + Ser := by
    have : innerSL ℝ ((1 / r ^ 2 : ℝ) • (z - p)) = (1 / r) • (r⁻¹ • innerSL ℝ (z - p)) := by
      rw [map_smul, smul_smul]; congr 1; field_simp
    rw [this, add_smul]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have := norm_smul (deriv R.B r + 1 / r) (r⁻¹ • innerSL ℝ (z - p))
    rw [norm_inv_smul_innerSL (sub_ne_zero.2 hzp), Real.norm_eq_abs, mul_one] at this
    exact this.le
  · exact norm_series_deriv_le hR hS h hR₁ hT hM hz

/-- **`H = -log r + O(r²)` on a cell** (value part of `(dual:singularity)`). -/
theorem abs_cellH_add_log_le (hR : R.IsAdmissible d₀) (hS : SepSites P d₀) (hp : p ∈ P)
    {R₁ T₀ : ℝ} (hR₁ : ∀ p ∈ P, voronoiCell P p ⊆ closedBall p R₁) (hT : R₁ ≤ T₀)
    {M : ι → ℝ} (hM : Bnd R d₀ T₀ M) {C ρ : ℝ} (hCρ : ∀ r ∈ Ioo 0 ρ, |R.B r + Real.log r| ≤ C * r ^ 2)
    (hz : z ∈ voronoiCell P p) (hr0 : 0 < ‖z - p‖) (hr : ‖z - p‖ < ρ) (hr1 : ‖z - p‖ ≤ 1) :
    |cellH R P p z + Real.log ‖z - p‖| ≤ (C + (∑' i, M i) / d₀ ^ 6) * ‖z - p‖ ^ 2 := by
  have hd := hS.pos
  have hzp : z ≠ p := by intro h; subst h; simp at hr0
  have hc := mem_cone_of_mem_cell hS hp hR₁ hT hz hzp
  have h1 := abs_serF_le hM hR hd hc
  have hgr : gauge P p (z - p) ≤ ‖z - p‖ / d₀ := gauge_le_norm_div hS hp _
  have hg0 : 0 ≤ gauge P p (z - p) := gauge_nonneg hS hp _
  have hsumn : 0 ≤ ∑' i, M i := tsum_nonneg fun i => hM.nonneg hd (by
    have := (div_mem_Icc_of_mem_cone hc); linarith [this.1, this.2]) i
  have h2 : |serF R (‖z - p‖, gauge P p (z - p))| ≤ ((‖z - p‖ / d₀) ^ 6) * ∑' i, M i := by
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg0 hgr 6) hsumn
  have h3 : ((‖z - p‖ / d₀) ^ 6) * ∑' i, M i ≤ ((∑' i, M i) / d₀ ^ 6) * ‖z - p‖ ^ 2 := by
    have : (‖z - p‖ / d₀) ^ 6 = ‖z - p‖ ^ 6 / d₀ ^ 6 := by rw [div_pow]
    rw [this]
    have h4 : ‖z - p‖ ^ 6 ≤ ‖z - p‖ ^ 2 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
    calc ‖z - p‖ ^ 6 / d₀ ^ 6 * ∑' i, M i = (‖z - p‖ ^ 6) * ((∑' i, M i) / d₀ ^ 6) := by ring
      _ ≤ ‖z - p‖ ^ 2 * ((∑' i, M i) / d₀ ^ 6) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
      _ = _ := by ring
  have h5 := hCρ ‖z - p‖ ⟨hr0, hr⟩
  have : cellH R P p z + Real.log ‖z - p‖ =
      (R.B ‖z - p‖ + Real.log ‖z - p‖) + serF R (‖z - p‖, gauge P p (z - p)) := by
    unfold cellH Fpair; ring
  rw [this]
  calc _ ≤ |R.B ‖z - p‖ + Real.log ‖z - p‖| + |serF R (‖z - p‖, gauge P p (z - p))| := abs_add_le _ _
    _ ≤ C * ‖z - p‖ ^ 2 + ((∑' i, M i) / d₀ ^ 6) * ‖z - p‖ ^ 2 := add_le_add h5 (h2.trans h3)
    _ = _ := by ring

end Dual

end SandierSerfaty

end
