/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.DualIdentityMain

/-!
# The sector functional of a model sector

The paper (`geo:sector`) states the sector bound `(dual:sector-input)` for
the *model* sector `S(d, α, β) = {0 < Re w < d, -tan α · Re w < Im w < tan β · Re w}` with the trial function
`H(w) = B(|w|) + ∑ᵢ (|w| / t)^{kᵢ} Dᵢ(t)`, `t = d |w| / Re w` (so `|w| / t = Re w / d`). Here:

* `modelH R d w = Fpair R (‖w‖, w.re / d)`;
* `modelSectorRen R d α β = lim_{η ↓ 0} [∫_{S ∩ {|w| > η}} |∇H|² + (α + β) log η]`;
* `modelSectorJ R d α β = -2π ∫_S H - ½ modelSectorRen R d α β` (the paper's `J(S(d, α, β))`);
* `sectorJ_eq_modelSectorJ`: for an incidence `(p, q)` of a site set `P` the functional `sectorJ R P p q` of the
  Voronoi sector equals `modelSectorJ R d α β` with `d = pairHalfDist p q`, `α = sectorAlpha P p q`,
  `β = sectorBeta P p q`: the sector is the image of `S(d, α, β)` under the rigid motion `w ↦ p + u w`
  (`u = pairAxis p q`), on which `H` and `|∇H|²` correspond (`gradSq_comp_mul_add`).
-/

open MeasureTheory Set Filter Topology Metric

public section

namespace SandierSerfaty

namespace Dual

open Analysis

variable {ι : Type*} {R : RadialData ι} {P : Set ℂ} {d₀ : ℝ} {p q : ℂ}

/-- The trial function on the model sector, `H(w) = B(|w|) + ∑ᵢ (Re w / d)^{kᵢ} Dᵢ(d |w| / Re w)`. -/
@[expose] noncomputable def modelH (R : RadialData ι) (d : ℝ) (w : ℂ) : ℝ :=
  Fpair R (‖w‖, w.re / d)

/-- The renormalized Dirichlet integral `∫_S^ren |∇H|²` of the model sector. -/
@[expose] noncomputable def modelSectorRen (R : RadialData ι) (d α β : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun η : ℝ =>
    (∫ w in modelSector d α β ∩ {w | η < ‖w‖}, gradSq (modelH R d) w) + (α + β) * Real.log η

/-- The functional `J(S(d, α, β)) = -2π ∫_S H - ½ ∫_S^ren |∇H|²` of the model sector. -/
@[expose] noncomputable def modelSectorJ (R : RadialData ι) (d α β : ℝ) : ℝ :=
  -(2 * Real.pi) * (∫ w in modelSector d α β, modelH R d w) - (1 / 2 : ℝ) * modelSectorRen R d α β

/-- The gradient energy density is invariant under the rigid motions `w ↦ c + u w`, `|u| = 1`. -/
theorem norm_fderiv_comp_mul_add {u : ℂ} (hu : ‖u‖ = 1) (c : ℂ) (f : ℂ → ℝ) (w : ℂ) :
    ‖fderiv ℝ (fun ζ => f (c + u * ζ)) w‖ = ‖fderiv ℝ f (c + u * w)‖ := by
  obtain ⟨a, rfl⟩ : ∃ a : Circle, (a : ℂ) = u := ⟨⟨u, mem_sphere_zero_iff_norm.2 hu⟩, rfl⟩
  set T : ℂ → ℂ := fun ζ => c + (a : ℂ) * ζ with hT
  have hTd : ∀ x, HasFDerivAt T ((rotation a).toContinuousLinearEquiv.toContinuousLinearMap) x :=
    fun x => by
      have := ((rotation a).toContinuousLinearEquiv.hasFDerivAt (x := x)).const_add c
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp [hT]
  by_cases hf : DifferentiableAt ℝ f (T w)
  · have := hf.hasFDerivAt.comp w (hTd w)
    have e : (fun ζ => f (c + (a : ℂ) * ζ)) = f ∘ T := rfl
    rw [e, this.fderiv]
    exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _
  · have h2 : ¬ DifferentiableAt ℝ (fun ζ => f (c + (a : ℂ) * ζ)) w := by
      intro hd
      apply hf
      have hT' : DifferentiableAt ℝ (fun x : ℂ => (starRingEnd ℂ (a : ℂ)) * (x - c)) (T w) :=
        (differentiableAt_const _).mul (differentiableAt_id.sub_const c)
      have haa : (a : ℂ) * (starRingEnd ℂ) (a : ℂ) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]; simp
      have hpt : (starRingEnd ℂ (a : ℂ)) * (T w - c) = w := by
        simp only [hT, add_sub_cancel_left]
        linear_combination w * haa
      have hd' : DifferentiableAt ℝ (fun ζ => f (c + (a : ℂ) * ζ))
          ((starRingEnd ℂ (a : ℂ)) * (T w - c)) := by rw [hpt]; exact hd
      have := hd'.comp (T w) hT'
      refine this.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      simp only [Function.comp_apply]
      congr 1
      rw [← mul_assoc, haa]; ring
    rw [fderiv_zero_of_not_differentiableAt h2, fderiv_zero_of_not_differentiableAt hf]

theorem gradSq_comp_mul_add {u : ℂ} (hu : ‖u‖ = 1) (c : ℂ) (f : ℂ → ℝ) (w : ℂ) :
    gradSq (fun ζ => f (c + u * ζ)) w = gradSq f (c + u * w) := by
  rw [gradSq_eq_norm_fderiv_sq, gradSq_eq_norm_fderiv_sq, norm_fderiv_comp_mul_add hu]

/-- On the frame of the pair `(p, q)`, the sector formula `Hsec` is the model trial function. -/
theorem Hsec_pairAxis_mul (h : p ≠ q) (w : ℂ) :
    Hsec R p q (p + pairAxis p q * w) = modelH R (pairHalfDist p q) w := by
  have hu := norm_pairAxis h
  unfold Hsec modelH
  congr 2
  · simp [hu]
  · rw [add_sub_cancel_left, gaugeLin_eq_re_div h]
    have : (pairAxis p q * w * (starRingEnd ℂ) (pairAxis p q)).re = w.re := by
      have h1 : pairAxis p q * (starRingEnd ℂ) (pairAxis p q) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
      rw [mul_right_comm, h1, one_mul]
    rw [this]

section Transfer

variable (hS : SepSites P d₀) (h : IsVoronoiNeighbor P p q)
include hS h

theorem integral_voronoiSector_gluedH :
    ∫ z in voronoiSector P p q, gluedH R P z =
      ∫ w in modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q),
        modelH R (pairHalfDist p q) w := by
  have hu := norm_pairAxis h.ne
  unfold voronoiSector
  rw [integral_comp_affine_image hu p]
  refine setIntegral_congr_fun (measurableSet_modelSector _ _ _) fun w hw => ?_
  have hz : p + pairAxis p q * w ∈ voronoiSector P p q := mem_image_of_mem _ hw
  rw [gluedH_eq_Hsec hS h hz, Hsec_pairAxis_mul h.ne]

theorem integral_voronoiSector_inter_gradSq (η : ℝ) :
    ∫ z in voronoiSector P p q ∩ {z | η < ‖z - p‖}, gradSq (gluedH R P) z =
      ∫ w in modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q) ∩ {w | η < ‖w‖},
        gradSq (modelH R (pairHalfDist p q)) w := by
  have hu := norm_pairAxis h.ne
  have hpre : (fun ζ => p + pairAxis p q * ζ) ⁻¹' {z | η < ‖z - p‖} = {w | η < ‖w‖} := by
    ext w; simp [hu]
  have himg : voronoiSector P p q ∩ {z | η < ‖z - p‖} = (fun ζ => p + pairAxis p q * ζ) ''
      (modelSector (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q) ∩ {w | η < ‖w‖}) := by
    rw [← hpre, Set.image_inter_preimage]; rfl
  rw [himg, integral_comp_affine_image hu p]
  refine setIntegral_congr_fun ((measurableSet_modelSector _ _ _).inter
    (measurableSet_lt measurable_const measurable_norm)) fun w hw => ?_
  have hz : p + pairAxis p q * w ∈ voronoiSector P p q := mem_image_of_mem _ hw.1
  have hcont : Continuous fun ζ : ℂ => p + pairAxis p q * ζ := by fun_prop
  have hev : (fun ζ => gluedH R P (p + pairAxis p q * ζ)) =ᶠ[𝓝 w] modelH R (pairHalfDist p q) := by
    have := (eventuallyEq_gluedH_Hsec (R := R) hS h hz).comp_tendsto (hcont.tendsto w)
    refine this.trans (Eventually.of_forall fun y => ?_)
    exact Hsec_pairAxis_mul h.ne y
  rw [← gradSq_comp_mul_add hu p (gluedH R P) w, gradSq_eq_norm_fderiv_sq, gradSq_eq_norm_fderiv_sq,
    hev.fderiv_eq]

/-- **Transfer to the model sector.** The renormalized Dirichlet integral of the sector of `(p, q)` is
that of the model sector `S(d, α, β)`. -/
theorem sectorRen_eq_modelSectorRen :
    sectorRen R P p q =
      modelSectorRen R (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q) := by
  unfold sectorRen modelSectorRen
  congr 1
  funext η
  rw [integral_voronoiSector_inter_gradSq hS h η]

/-- **Transfer to the model sector.** `J` of the Voronoi sector of `(p, q)` equals
`J(S(d, α, β))`, `d = pairHalfDist p q`, `α = sectorAlpha P p q`, `β = sectorBeta P p q`. -/
theorem sectorJ_eq_modelSectorJ :
    sectorJ R P p q =
      modelSectorJ R (pairHalfDist p q) (sectorAlpha P p q) (sectorBeta P p q) := by
  unfold sectorJ modelSectorJ
  rw [integral_voronoiSector_gluedH hS h, sectorRen_eq_modelSectorRen hS h]

end Transfer

end Dual

end SandierSerfaty

end
