/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ProjectionGradient
public import SandierSerfaty.Screening.LocEnergy
public import SandierSerfaty.Statements.Torus.Theorems.TendstoTorusEnergy
public import SandierSerfaty.Jellium.TriangularLocal
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Projection onto the torus `T_N` (interface I5)

**Theorem** (`torusEnergy_le_locEnergy`; I5;
screening note, Theorem `thm:I5`). Let `N ≥ 1`, `Q = sq c √N` (closed square of side `√N`), `a : Fin N → ℂ`
injective with values in `int Q`, radii `ρ(aᵢ) > 0` with `B̄(aᵢ, ρ(aᵢ)) ⊆ int Q` and
`ρ(aᵢ) + ρ(aⱼ) ≤ |aᵢ - aⱼ|` (`i ≠ j`), and `E'` a zero-flux charge field on `Q` with density `1`
and charges `{aᵢ}` (`IsNeumannChargeField`). Then
```
torusEnergy (squareLattice N) a ≤ locEnergy 1 (range a) ρ E' Q.
```
The torus is `T_N = ℂ/√N ℤ[i]` itself, the lattice of the square-torus bound, paper Theorem 1.2 (no reflection: `Q` is
a fundamental domain of `squareLattice N`), and the configuration is `a` itself.

**Proof** (screening note, §5, with the truncated potential split into admissible test functions,
`ProjectionGradient`). Let `H = torusPotential`, `X = E' - ∇H` on `Q`.

1. *Orthogonality* (`setIntegral_inner_sub_gradient_eq_zero`): `∫_Q ⟪X, ∇F⟫ = 0` for
   `F = projPer + projLoc`, because `E'` (Neumann identity) and `∇H` (periodic pairing on the cell
   and the charge-field identity in `int Q`) satisfy the same identity against `projPer` (smooth,
   periodic) and `projLoc` (Lipschitz, supported in `int Q`).
2. *Energy* (`ofReal_integral_le_lintegral_truncField`): `∇F = (∇H)_ρ` a.e. on `Q` and
   `E'_ρ = ∇F + X`, so `∫_Q |E'_ρ|² ≥ ∫_Q |(∇H)_ρ|²`.
3. *Lemma 4.13* (`locEnergy_gradient_torusPotential_eq`): `G_Q(ρ)[∇H] = G_Q(η)[∇H]` for small `η`
   (disjoint balls, zero interaction).
4. *Puncture comparison* (`puncture_le`): the puncture expression of `torusEnergy` at `η` is at most
   `G_Q(η)[∇H] + N π² η²`, and `η ↓ 0` (`tendsto_torusEnergy`).
-/

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal Real Pointwise

public section

namespace SandierSerfaty

namespace Screening

open Torus

/-! ### Generic helpers -/

theorem integrableOn_inner_of_bounded {G g : ℂ → ℂ} {S : Set ℂ} (hG : IntegrableOn G S)
    (hg : AEStronglyMeasurable g volume) {B : ℝ} (hgB : ∀ x, ‖g x‖ ≤ B) :
    IntegrableOn (fun x => inner ℝ (G x) (g x)) S := by
  refine Integrable.mono' (hG.norm.const_mul B) (hG.aestronglyMeasurable.inner hg.restrict)
    (Eventually.of_forall fun x => ?_)
  refine (norm_inner_le_norm _ _).trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hgB x) (norm_nonneg _)

theorem ofReal_integral_le_lintegral {f : ℂ → ℝ} {S : Set ℂ} (hf : IntegrableOn f S) :
    ENNReal.ofReal (∫ x in S, f x) ≤ ∫⁻ x in S, ENNReal.ofReal (f x) := by
  have hpos : IntegrableOn (fun x => max (f x) 0) S := hf.sup (integrableOn_zero)
  calc ENNReal.ofReal (∫ x in S, f x)
      ≤ ENNReal.ofReal (∫ x in S, max (f x) 0) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hpos fun x => le_max_left _ _)
    _ = ∫⁻ x in S, ENNReal.ofReal (max (f x) 0) :=
        ofReal_integral_eq_lintegral_ofReal hpos (Eventually.of_forall fun x => le_max_right _ _)
    _ = ∫⁻ x in S, ENNReal.ofReal (f x) := by
        congr 1; ext x; rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_zero]

theorem locEnergy_eq_coe {m : ℝ} {C : Set ℂ} {α : ℂ → ℝ} {E : ℂ → ℂ} {D : Set ℂ}
    (hL : ∫⁻ x in D, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) ≠ ⊤) :
    locEnergy m C α E D = ((1 / 2 * (∫⁻ x in D, ENNReal.ofReal (‖truncField C α E x‖ ^ 2)).toReal +
      ∑ᶠ p ∈ C ∩ D, tauM m (α p) : ℝ) : EReal) := by
  unfold locEnergy
  rw [← ENNReal.ofReal_toReal hL, coe_ennreal_ofReal_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  norm_cast

theorem locEnergy_eq_top {m : ℝ} {C : Set ℂ} {α : ℂ → ℝ} {E : ℂ → ℂ} {D : Set ℂ}
    (hL : ∫⁻ x in D, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) = ⊤) : locEnergy m C α E D = ⊤ := by
  unfold locEnergy
  rw [hL, EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by norm_num), EReal.top_add_coe]

/-! ### The setting -/

variable {N : ℕ} [NeZero N] {c : ℂ} {a : Fin N → ℂ}

omit [NeZero N] in
theorem tau_sum_eq (haQ : ∀ i, a i ∈ interior (sq c √N)) (ha : Function.Injective a) (m : ℝ)
    (r : ℂ → ℝ) : ∑ᶠ p ∈ range a ∩ sq c √N, tauM m (r p) = ∑ i, tauM m (r (a i)) := by
  have : range a ∩ sq c √N = range a :=
    inter_eq_left.2 (range_subset_iff.2 fun i => interior_subset (haQ i))
  rw [this, finsum_range_eq, sum_image_eq ha]

omit [NeZero N] in
theorem mem_interior_of_mem_sq_of_notMem_frontier {x : ℂ} (hx : x ∈ sq c √N)
    (hxf : x ∉ frontier (sq c √N)) : x ∈ interior (sq c √N) := by
  by_contra h
  exact hxf ⟨subset_closure hx, h⟩

/-- Almost every point of `Q` is interior, off the charges and off the circles `|x - aᵢ| = r(aᵢ)`. -/
theorem ae_good (r : ℂ → ℝ) :
    ∀ᵐ x ∂volume, x ∈ sq c √N → x ∈ interior (sq c √N) ∧
      x ∉ chargeSet (squareLattice N) a ∧ ∀ i, ‖x - a i‖ ≠ r (a i) := by
  have h1 : ∀ᵐ x ∂volume, x ∉ frontier (sq c √N) :=
    measure_eq_zero_iff_ae_notMem.1 ((convex_sq c _).addHaar_frontier volume)
  have h2 : ∀ᵐ x ∂volume, x ∉ chargeSet (squareLattice N) a :=
    (countable_chargeSet _ a).ae_notMem volume
  have h3 : ∀ᵐ x ∂volume, ∀ i, x ∉ sphere (a i) (r (a i)) :=
    ae_all_iff.2 fun i => measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume _ _)
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3 hxQ
  refine ⟨mem_interior_of_mem_sq_of_notMem_frontier hxQ hx1, hx2, fun i h => hx3 i ?_⟩
  rw [mem_sphere, dist_eq_norm, h]

/-! ### Step 1: orthogonality -/

/-- The test function `F = projPer + projLoc`. -/
@[expose] noncomputable def projTest (a : Fin N → ℂ) (b : ContDiffBump (0 : ℂ)) (η : ℝ)
    (r : ℂ → ℝ) (x : ℂ) : ℝ :=
  projPer (squareLattice N) a b x + projLoc (squareLattice N) a b η r x

/-- Standing hypotheses on the cut-off scale `η` and the radius family `r`. -/
structure ProjScale (c : ℂ) (a : Fin N → ℂ) (η : ℝ) (r : ℂ → ℝ) : Prop where
  pos : 0 < η
  three_le : 3 * η ≤ √(N : ℝ)
  ball_two : ∀ i, closedBall (a i) (2 * η) ⊆ interior (sq c √N)
  le_r : ∀ i, η ≤ r (a i)
  ball_r : ∀ i, closedBall (a i) (r (a i)) ⊆ interior (sq c √N)

namespace ProjScale

variable {η : ℝ} {r : ℂ → ℝ} (h : ProjScale c a η r)
include h

omit [NeZero N] in
theorem bump_hb : (projBump h.pos).rIn + (projBump h.pos).rOut ≤ √(N : ℝ) := by
  simp only [projBump]; linarith [h.three_le]

omit [NeZero N] in
theorem bump_hbN : (projBump h.pos).rOut < √(N : ℝ) := by
  simp only [projBump]; linarith [h.three_le, h.pos]

omit [NeZero N] in
theorem bump_hbQ : ∀ i, closedBall (a i) (projBump h.pos).rOut ⊆ interior (sq c √N) :=
  h.ball_two

theorem exists_lipschitzWith : ∃ K, LipschitzWith K (projTest a (projBump h.pos) η r) := by
  obtain ⟨KP, hKP⟩ := exists_lipschitzWith_projPer a (projBump h.pos) h.bump_hb
  obtain ⟨KL, hKL⟩ := exists_lipschitzWith_projLoc a (projBump h.pos) h.bump_hbN h.pos h.le_r
  exact ⟨KP + KL, hKP.add hKL⟩

omit [NeZero N] in
theorem tsupport_projLoc_subset_interior :
    tsupport (projLoc (squareLattice N) a (projBump h.pos) η r) ⊆ interior (sq c √N) := by
  refine (tsupport_projLoc_subset a _ η r).trans (iUnion_subset fun i => ?_)
  rcases max_choice (projBump h.pos).rOut (r (a i)) with hm | hm <;> rw [hm]
  · exact h.bump_hbQ i
  · exact h.ball_r i

/-- `∇F = (∇H)_r` almost everywhere on `Q`. -/
theorem ae_gradient_projTest (ha : Function.Injective a) (haQ : ∀ i, a i ∈ interior (sq c √N)) :
    ∀ᵐ x ∂volume, x ∈ sq c √N → gradient (projTest a (projBump h.pos) η r) x =
      truncField (range a) r (gradient (torusPotential (squareLattice N) a)) x := by
  filter_upwards [ae_good (c := c) (a := a) r] with x hx hxQ
  obtain ⟨hxi, hxP, hxr⟩ := hx hxQ
  exact gradient_projPer_add_projLoc ha haQ h.pos _ le_rfl h.bump_hbQ h.le_r hxi hxP hxr

end ProjScale

variable {E' : ℂ → ℂ}

/-- **Orthogonality**: `∫_Q ⟪E' - ∇H, ∇F⟫ = 0`. -/
theorem setIntegral_inner_sub_gradient_eq_zero (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √N))
    (hE' : IsNeumannChargeField (sq c √N) 1 (Finset.univ.image a) E') {η : ℝ} {r : ℂ → ℝ}
    (h : ProjScale c a η r) :
    ∫ x in sq c √N, inner ℝ (E' x - gradient (torusPotential (squareLattice N) a) x)
      (gradient (projTest a (projBump h.pos) η r) x) = 0 := by
  set b := projBump h.pos
  set P := projPer (squareLattice N) a b with hP
  set L := projLoc (squareLattice N) a b η r with hL
  set G := gradient (torusPotential (squareLattice N) a) with hG
  obtain ⟨KP, hKP⟩ := exists_lipschitzWith_projPer a b h.bump_hb
  obtain ⟨KL, hKL⟩ := exists_lipschitzWith_projLoc a b h.bump_hbN h.pos h.le_r
  have hPs : ContDiff ℝ ∞ P := contDiff_projPer a b h.bump_hb
  have hLc : HasCompactSupport L := hasCompactSupport_projLoc a b η r
  have hQm := measurableSet_sq c √(N : ℝ)
  have e1 := hE'.setIntegral_inner_gradient_of_contDiff hQm (isBounded_sq c _) hPs
  have e2 := hE'.setIntegral_inner_gradient_lipschitz hQm hKL hLc
  have e3 := setIntegral_inner_gradient_torusPotential_periodic ha haQ hKP
    fun γ hγ x => projPer_add_period a b hγ x
  have e4 := setIntegral_inner_gradient_torusPotential_lipschitz ha haQ hKL hLc
    h.tsupport_projLoc_subset_interior
  have hE'i : IntegrableOn E' (sq c √N) := hE'.1
  have hGi : IntegrableOn G (sq c √N) :=
    integrableOn_gradient_torusPotential ha haQ _ (isCompact_sq c _)
  have hbP : ∀ x, ‖gradient P x‖ ≤ KP := norm_gradient_le_of_lipschitz hKP
  have hbL : ∀ x, ‖gradient L x‖ ≤ KL := norm_gradient_le_of_lipschitz hKL
  have i1 := integrableOn_inner_of_bounded hE'i (aestronglyMeasurable_gradient P) hbP
  have i2 := integrableOn_inner_of_bounded hE'i (aestronglyMeasurable_gradient L) hbL
  have i3 := integrableOn_inner_of_bounded hGi (aestronglyMeasurable_gradient P) hbP
  have i4 := integrableOn_inner_of_bounded hGi (aestronglyMeasurable_gradient L) hbL
  have hgrad : ∀ᵐ x ∂volume, gradient (projTest a b η r) x = gradient P x + gradient L x := by
    filter_upwards [hKL.ae_differentiableAt (μ := volume)] with x hx
    have hPd : DifferentiableAt ℝ P x := (hPs.differentiable (by simp)) x
    have e : projTest a b η r = fun y => P y + L y := rfl
    simp only [gradient]
    rw [e, fderiv_fun_add hPd hx, map_add]
  have hcongr : ∫ x in sq c √N, inner ℝ (E' x - G x) (gradient (projTest a b η r) x) =
      ∫ x in sq c √N, ((inner ℝ (E' x) (gradient P x) + inner ℝ (E' x) (gradient L x)) -
        (inner ℝ (G x) (gradient P x) + inner ℝ (G x) (gradient L x))) := by
    refine setIntegral_congr_ae hQm (hgrad.mono fun x hx _ => ?_)
    rw [hx, inner_sub_left, inner_add_right, inner_add_right]
  have i12 : IntegrableOn (fun x => inner ℝ (E' x) (gradient P x) +
      inner ℝ (E' x) (gradient L x)) (sq c √N) := i1.add i2
  have i34 : IntegrableOn (fun x => inner ℝ (G x) (gradient P x) +
      inner ℝ (G x) (gradient L x)) (sq c √N) := i3.add i4
  rw [hcongr, integral_sub i12 i34, integral_add i1 i2, integral_add i3 i4, e1, e2, e3, e4,
    sub_self]

/-! ### Step 2: the energy inequality -/

theorem ProjScale.integrableOn_norm_gradient_sq {η : ℝ} {r : ℂ → ℝ} (h : ProjScale c a η r) :
    IntegrableOn (fun x => ‖gradient (projTest a (projBump h.pos) η r) x‖ ^ 2) (sq c √N) := by
  obtain ⟨K, hK⟩ := h.exists_lipschitzWith
  refine Measure.integrableOn_of_bounded (M := (K : ℝ) ^ 2) (isCompact_sq c _).measure_lt_top.ne
    ((aestronglyMeasurable_gradient _).norm.pow 2) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitz hK x) 2

/-- `∫_Q |(∇H)_r|² = ∫_Q |∇F|² < ∞`. -/
theorem lintegral_truncField_gradient_eq (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √N)) {η : ℝ} {r : ℂ → ℝ} (h : ProjScale c a η r) :
    ∫⁻ x in sq c √N, ENNReal.ofReal
        (‖truncField (range a) r (gradient (torusPotential (squareLattice N) a)) x‖ ^ 2) =
      ENNReal.ofReal (∫ x in sq c √N, ‖gradient (projTest a (projBump h.pos) η r) x‖ ^ 2) := by
  rw [ofReal_integral_eq_lintegral_ofReal h.integrableOn_norm_gradient_sq
    (Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr_ae (((ae_restrict_iff' (measurableSet_sq c _)).2
    (h.ae_gradient_projTest ha haQ)).mono fun x hx => by simp only [hx])

theorem lintegral_truncField_gradient_ne_top (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √N)) {η : ℝ} {r : ℂ → ℝ} (h : ProjScale c a η r) :
    ∫⁻ x in sq c √N, ENNReal.ofReal
        (‖truncField (range a) r (gradient (torusPotential (squareLattice N) a)) x‖ ^ 2) ≠ ⊤ := by
  rw [lintegral_truncField_gradient_eq ha haQ h]; exact ENNReal.ofReal_ne_top

/-- **The energy inequality**: `∫_Q |(∇H)_r|² ≤ ∫_Q |E'_r|²`. -/
theorem lintegral_truncField_le (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √N))
    (hE' : IsNeumannChargeField (sq c √N) 1 (Finset.univ.image a) E') {η : ℝ} {r : ℂ → ℝ}
    (h : ProjScale c a η r) :
    ∫⁻ x in sq c √N, ENNReal.ofReal
        (‖truncField (range a) r (gradient (torusPotential (squareLattice N) a)) x‖ ^ 2) ≤
      ∫⁻ x in sq c √N, ENNReal.ofReal (‖truncField (range a) r E' x‖ ^ 2) := by
  set F := projTest a (projBump h.pos) η r
  set G := gradient (torusPotential (squareLattice N) a) with hG
  obtain ⟨K, hK⟩ := h.exists_lipschitzWith
  have hbF : ∀ x, ‖gradient F x‖ ≤ K := norm_gradient_le_of_lipschitz hK
  have haeQ : ∀ᵐ x ∂(volume.restrict (sq c √N)), gradient F x = truncField (range a) r G x :=
    (ae_restrict_iff' (measurableSet_sq c _)).2 (h.ae_gradient_projTest ha haQ)
  have hFsq := h.integrableOn_norm_gradient_sq
  rw [lintegral_truncField_gradient_eq ha haQ h]
  have hX : IntegrableOn (fun x => E' x - G x) (sq c √N) :=
    hE'.1.sub (integrableOn_gradient_torusPotential ha haQ _ (isCompact_sq c _))
  have hcross := integrableOn_inner_of_bounded hX (aestronglyMeasurable_gradient F) hbF
  have horth := setIntegral_inner_sub_gradient_eq_zero ha haQ hE' h
  have hsum : IntegrableOn (fun x => ‖gradient F x‖ ^ 2 +
      2 * inner ℝ (E' x - G x) (gradient F x)) (sq c √N) := hFsq.add (hcross.const_mul 2)
  calc ENNReal.ofReal (∫ x in sq c √N, ‖gradient F x‖ ^ 2)
      = ENNReal.ofReal (∫ x in sq c √N, (‖gradient F x‖ ^ 2 +
          2 * inner ℝ (E' x - G x) (gradient F x))) := by
        rw [integral_add hFsq (hcross.const_mul 2), integral_const_mul, horth, mul_zero, add_zero]
    _ ≤ ∫⁻ x in sq c √N, ENNReal.ofReal (‖gradient F x‖ ^ 2 +
          2 * inner ℝ (E' x - G x) (gradient F x)) := ofReal_integral_le_lintegral hsum
    _ ≤ ∫⁻ x in sq c √N, ENNReal.ofReal (‖truncField (range a) r E' x‖ ^ 2) := by
        refine lintegral_mono_ae (haeQ.mono fun x hx => ENNReal.ofReal_le_ofReal ?_)
        have e : truncField (range a) r E' x = gradient F x + (E' x - G x) := by
          rw [hx]; unfold truncField; abel
        rw [e, norm_add_sq_real, real_inner_comm]
        nlinarith [sq_nonneg ‖E' x - G x‖]

/-! ### Step 3: Lemma 4.13 for `∇H` -/

/-- `G_Q(ρ)[∇H] = G_Q(η)[∇H]` (disjoint balls, zero interaction). -/
theorem locEnergy_gradient_torusPotential_eq (ha : Function.Injective a)
    (haQ : ∀ i, a i ∈ interior (sq c √N)) {η : ℝ} {ρ : ℂ → ℝ} (h : ProjScale c a η ρ)
    (hdisj : ∀ i j, i ≠ j → ρ (a i) + ρ (a j) ≤ ‖a i - a j‖) :
    locEnergy 1 (range a) ρ (gradient (torusPotential (squareLattice N) a)) (sq c √N) =
      locEnergy 1 (range a) (fun _ => η) (gradient (torusPotential (squareLattice N) a))
        (sq c √N) := by
  have hη : ProjScale c a η (fun _ => η) :=
    ⟨h.pos, h.three_le, h.ball_two, fun _ => le_rfl, fun i =>
      (closedBall_subset_closedBall (by linarith [h.pos])).trans (h.ball_two i)⟩
  have hL2 := lintegral_truncField_gradient_ne_top ha haQ hη
  have hC : ∀ R : ℝ, (range a ∩ closedBall 0 R).Finite := fun R =>
    (finite_range a).subset inter_subset_left
  have hα : ∀ p ∈ range a, 0 < (fun _ : ℂ => η) p := fun _ _ => h.pos
  have hαβ : ∀ p ∈ range a, (fun _ : ℂ => η) p ≤ ρ p := by
    rintro p ⟨i, rfl⟩; exact h.le_r i
  have hβb : ∃ M, ∀ p ∈ range a, ρ p ≤ M := ⟨∑ i, |ρ (a i)|, by
    rintro p ⟨i, rfl⟩
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |ρ (a i)|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i))⟩
  have hball : ∀ p ∈ range a, (fun _ : ℂ => η) p < ρ p →
      closedBall p (ρ p) ⊆ interior (sq c √N) ∩ sq c √N := by
    rintro p ⟨i, rfl⟩ -
    exact subset_inter (h.ball_r i) ((h.ball_r i).trans interior_subset)
  rw [locEnergy_eq_add_truncInteraction isOpen_interior (measurableSet_sq c _) (isBounded_sq c _)
    hC (isChargeField_gradient_torusPotential ha haQ) hα hαβ hβb hball hL2,
    truncInteraction_eq_zero _ _ _ hα hαβ ?_, EReal.coe_zero, add_zero]
  rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩ hne -
  exact hdisj i j fun hij => hne (by rw [hij])

/-! ### Step 4: the puncture comparison -/

omit [NeZero N] in
/-- The periodic union of the punctures is invariant under the lattice. -/
theorem mem_punctures_add {Γ : Submodule ℤ ℂ} {η : ℝ} {γ : ℂ} (hγ : γ ∈ Γ) {x : ℂ}
    (hx : x ∈ ⋃ i, ⋃ γ' ∈ Γ, ball (a i + γ') η) : γ + x ∈ ⋃ i, ⋃ γ' ∈ Γ, ball (a i + γ') η := by
  simp only [mem_iUnion, mem_ball, exists_prop] at hx ⊢
  obtain ⟨i, γ', hγ', hx⟩ := hx
  refine ⟨i, γ' + γ, Γ.add_mem hγ' hγ, ?_⟩
  rwa [dist_eq_norm, show γ + x - (a i + (γ' + γ)) = x - (a i + γ') by ring, ← dist_eq_norm]

/-- **The puncture comparison**: the field integral in the puncture expression of `torusEnergy` at
radius `η` is at most `∫_Q |(∇H)_η|²`. -/
theorem integral_puncture_le (ha : Function.Injective a) (haQ : ∀ i, a i ∈ interior (sq c √N))
    {η : ℝ} (h : ProjScale c a η (fun _ => η)) :
    ∫ x in torusDomain (squareLattice N) \ ⋃ i, ⋃ γ ∈ squareLattice N, ball (a i + γ) η,
        ‖gradient (torusPotential (squareLattice N) a) x‖ ^ 2 ≤
      (∫⁻ x in sq c √N, ENNReal.ofReal (‖truncField (range a) (fun _ => η)
        (gradient (torusPotential (squareLattice N) a)) x‖ ^ 2)).toReal := by
  set Γ := squareLattice N with hΓ
  set H := torusPotential Γ a with hH
  set U := ⋃ i, ⋃ γ ∈ Γ, ball (a i + γ) η with hU
  have hUm : MeasurableSet U :=
    (isOpen_iUnion fun i => isOpen_biUnion fun γ _ => isOpen_ball).measurableSet
  have hHper := (isTorusPotential_torusPotential_sq ha haQ).1
  set g : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (‖gradient H x‖ ^ 2) with hg
  have hper : ∀ (γ : Γ) (x : ℂ), Uᶜ.indicator g (γ +ᵥ x) = Uᶜ.indicator g x := by
    intro γ x
    rw [lattice_vadd_eq]
    have hiff : (γ : ℂ) + x ∈ U ↔ x ∈ U := ⟨fun hx => by
      have := mem_punctures_add (a := a) (Γ.neg_mem γ.2) hx
      rwa [neg_add_cancel_left] at this, fun hx => mem_punctures_add γ.2 hx⟩
    have hgg : g ((γ : ℂ) + x) = g x := by
      simp only [hg]; rw [add_comm, Torus.gradient_add_periodic hHper γ.2 x]
    by_cases hx : x ∈ U
    · rw [indicator_of_notMem (notMem_compl_iff.2 (hiff.2 hx)),
        indicator_of_notMem (notMem_compl_iff.2 hx)]
    · rw [indicator_of_mem (mem_compl fun h => hx (hiff.1 h)), indicator_of_mem (mem_compl hx), hgg]
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖gradient H x‖ ^ 2)
    (Eventually.of_forall fun x => by positivity)
    ((aestronglyMeasurable_gradient H).norm.pow 2).restrict]
  refine ENNReal.toReal_mono (lintegral_truncField_gradient_ne_top ha haQ h) ?_
  have e1 : ∫⁻ x in torusDomain Γ \ U, g x = ∫⁻ x in torusDomain Γ, Uᶜ.indicator g x := by
    rw [lintegral_indicator hUm.compl, Measure.restrict_restrict hUm.compl, inter_comm, sdiff_eq]
  rw [e1, (torusDomain_spec Γ).1.setLIntegral_eq (isAddFundamentalDomain_sq c) _ hper]
  refine lintegral_mono_ae ((ae_restrict_iff' (measurableSet_sq c _)).2 ?_)
  have hsph : ∀ᵐ x ∂volume, ∀ i, x ∉ sphere (a i) η :=
    ae_all_iff.2 fun i => measure_eq_zero_iff_ae_notMem.1 (Measure.addHaar_sphere volume _ _)
  filter_upwards [hsph] with x hx _
  by_cases hxU : x ∈ U
  · rw [indicator_of_notMem (notMem_compl_iff.2 hxU)]; exact bot_le
  · rw [indicator_of_mem (mem_compl hxU)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    have hgt : ∀ i, η < ‖x - a i‖ := fun i => by
      have h1 : η ≤ ‖x - a i‖ := by
        by_contra hlt
        exact hxU (mem_iUnion.2 ⟨i, mem_iUnion₂.2 ⟨0, Γ.zero_mem, by
          rw [add_zero, mem_ball, dist_eq_norm]; exact not_le.1 hlt⟩⟩)
      exact lt_of_le_of_ne h1 fun h2 => hx i (by rw [mem_sphere, dist_eq_norm, h2])
    unfold truncField
    rw [finsum_mem_eq_zero_of_forall_eq_zero, sub_zero]
    rintro p ⟨i, rfl⟩
    exact Screening.gradient_truncLog_of_gt h.pos (hgt i)

theorem locEnergy_mono_lintegral {m : ℝ} {C : Set ℂ} {α : ℂ → ℝ} {E E₁ : ℂ → ℂ} {D : Set ℂ}
    (h : ∫⁻ x in D, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) ≤
      ∫⁻ x in D, ENNReal.ofReal (‖truncField C α E₁ x‖ ^ 2)) :
    locEnergy m C α E D ≤ locEnergy m C α E₁ D := by
  unfold locEnergy
  exact add_le_add_left (mul_le_mul_of_nonneg_left (EReal.coe_ennreal_le_coe_ennreal_iff.2 h)
    (show (0 : EReal) ≤ ((1 / 2 : ℝ) : EReal) from EReal.coe_nonneg.2 (by norm_num))) _

end Screening

open Screening Torus

/-- **I5: projection onto the torus `T_N = ℂ/√N ℤ[i]`** (the screening note's Theorem
`thm:I5`; book Lemma 7.5 / Prop. 11.11 projection step). A zero-flux charge field `E'` of density
`1` on the closed square `Q = sq c √N` with `N` distinct charges `a i ∈ int Q` has local energy at
least `torusEnergy` of the same configuration on the square torus
`ℂ/squareLattice N` (no reflection), for every family of disjoint truncation radii in `int Q`. -/
theorem torusEnergy_le_locEnergy {N : ℕ} (hN : 1 ≤ N) (c : ℂ) (a : Fin N → ℂ)
    (ha : Function.Injective a) (haQ : ∀ i, a i ∈ interior (sq c √(N : ℝ)))
    (ρ : ℂ → ℝ) (hρ : ∀ i, 0 < ρ (a i))
    (hρQ : ∀ i, closedBall (a i) (ρ (a i)) ⊆ interior (sq c √(N : ℝ)))
    (hdisj : ∀ i j, i ≠ j → ρ (a i) + ρ (a j) ≤ ‖a i - a j‖) {E' : ℂ → ℂ}
    (hE' : IsNeumannChargeField (sq c √(N : ℝ)) 1 (Finset.univ.image a) E') :
    ((torusEnergy (squareLattice N) a : ℝ) : EReal) ≤
      locEnergy 1 (Set.range a) ρ E' (sq c √(N : ℝ)) := by
  have : NeZero N := ⟨by omega⟩
  set Γ := squareLattice N with hΓ
  set Q := sq c √(N : ℝ) with hQ
  set H := torusPotential Γ a with hH
  set Λ := locEnergy 1 (Set.range a) ρ E' Q with hΛ
  set J : ℝ → ℝ := fun η => (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ,
    Metric.ball (a i + γ) η, ‖gradient H x‖ ^ 2) + Real.pi * N * Real.log η with hJ
  -- admissible scales
  have hN0 : (0 : ℝ) < √(N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hscale : ∀ᶠ η in 𝓝[>] (0 : ℝ), ProjScale c a η ρ := by
    have h1 : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η := self_mem_nhdsWithin
    have h2 : ∀ᶠ η in 𝓝[>] (0 : ℝ), η < √(N : ℝ) / 3 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < √(N : ℝ) / 3 by positivity)] with η hη
      exact hη.2
    have h3 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i, closedBall (a i) (2 * η) ⊆ interior Q := by
      refine eventually_all.2 fun i => ?_
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior (a i) (haQ i)
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ε / 2 by positivity)] with η hη
      exact (closedBall_subset_ball (by linarith [hη.2])).trans hball
    have h4 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ∀ i, η ≤ ρ (a i) :=
      eventually_all.2 fun i => by
        filter_upwards [Ioo_mem_nhdsGT (hρ i)] with η hη using hη.2.le
    filter_upwards [h1, h2, h3, h4] with η h1 h2 h3 h4
    exact ⟨h1, by linarith, h3, h4, hρQ⟩
  by_cases hΛtop : Λ = ⊤
  · rw [hΛtop]; exact le_top
  have key : ∀ᶠ η in 𝓝[>] (0 : ℝ),
      ((J η - N * Real.pi ^ 2 * η ^ 2 : ℝ) : EReal) ≤ Λ := by
    filter_upwards [hscale] with η h
    have hη : ProjScale c a η (fun _ => η) :=
      ⟨h.pos, h.three_le, h.ball_two, fun _ => le_rfl, fun i =>
        (closedBall_subset_closedBall (by linarith [h.pos])).trans (h.ball_two i)⟩
    have hfin := lintegral_truncField_gradient_ne_top ha haQ hη
    have hmono : locEnergy 1 (range a) ρ (gradient H) Q ≤ Λ :=
      locEnergy_mono_lintegral (lintegral_truncField_le ha haQ hE' h)
    rw [locEnergy_gradient_torusPotential_eq ha haQ h hdisj, locEnergy_eq_coe hfin,
      tau_sum_eq haQ ha] at hmono
    refine le_trans ?_ hmono
    have hp := integral_puncture_le ha haQ hη
    rw [EReal.coe_le_coe_iff]
    simp only [hJ, tauM, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [hp]
  obtain ⟨η₀, hη₀⟩ := key.exists
  have hΛbot : Λ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hη₀
  have hΛr : Λ = ((Λ.toReal : ℝ) : EReal) := (EReal.coe_toReal hΛtop hΛbot).symm
  have key' : ∀ᶠ η in 𝓝[>] (0 : ℝ), J η - N * Real.pi ^ 2 * η ^ 2 ≤ Λ.toReal :=
    key.mono fun η hη => by rw [hΛr] at hη; exact_mod_cast hη
  have hlim : Tendsto (fun η => J η - N * Real.pi ^ 2 * η ^ 2) (𝓝[>] 0)
      (𝓝 (torusEnergy Γ a)) := by
    have hT := tendsto_torusEnergy Γ (covolume_squareLattice N) a
      (sub_mem_squareLattice_imp_eq ha haQ)
    have h2 : Tendsto (fun η : ℝ => (N : ℝ) * Real.pi ^ 2 * η ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => (N : ℝ) * Real.pi ^ 2 * η ^ 2) (𝓝 0)
          (𝓝 ((N : ℝ) * Real.pi ^ 2 * 0 ^ 2)) :=
        (continuous_const.mul (continuous_id.pow 2)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have := hT.sub h2
    rw [sub_zero] at this
    exact this
  rw [hΛr]
  exact_mod_cast le_of_tendsto hlim key'

end SandierSerfaty

end
