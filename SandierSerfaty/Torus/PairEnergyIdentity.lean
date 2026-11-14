/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.GreenRegularity
public import SandierSerfaty.Analysis.LocalGreen
public import SandierSerfaty.Analysis.PunctureAsymptotics
public import SandierSerfaty.Torus.PairEnergyGeometry

/-!
# The cell identity for the truncated energy

For `0 < η ≤ ρ`, with `u = greenSum Γ a` and `g = 1_{(punctureSet η)ᶜ} |∇u|²`:
```
∫ x in D, g x = ∑ i, (-circleTerm u (a i) η + 2π ∫ x in B(a i, η), u x).
```
The proof splits `g = (1 - B) |∇u|² + B g` with the smooth periodized bump `B`, applies the periodic
Green identity (`SandierSerfaty.Analysis.periodic_green`) to the first part, and unfolds the second
part into the plane integrals `∫ β i g`, to which the local Green identity at the puncture
(`SandierSerfaty.Analysis.local_green`) applies.
-/

open MeasureTheory Filter Topology Metric Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

open Analysis

/-- The standing data: covolume `N`, distinct charges, separation radius `ρ`. -/
structure PairData (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (ρ : ℝ) : Prop where
  covol : ZLattice.covolume Γ = N
  distinct : ∀ i j, a i - a j ∈ Γ → i = j
  sep : ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ρ ≤ ‖q - a i‖
  pos : 0 < ρ

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ} {ρ : ℝ}

/-- The truncated gradient energy density. -/
@[expose] noncomputable def energyDensity (Γ : Submodule ℤ ℂ) (a : Fin N → ℂ) (η : ℝ) (x : ℂ) : ℝ :=
  Set.indicator (punctureSet Γ a η)ᶜ (gradSq (greenSum Γ a)) x

theorem energyDensity_add_period (η : ℝ) {γ : ℂ} (hγ : γ ∈ Γ) (x : ℂ) :
    energyDensity Γ a η (x + γ) = energyDensity Γ a η x := by
  unfold energyDensity
  have hpd : ∀ v, fderiv ℝ (greenSum Γ a) (x + γ) v = fderiv ℝ (greenSum Γ a) x v := fun v => by
    rw [fderiv_periodic Γ (fun δ hδ y => greenSum_add_period hδ y) hγ]
  have : gradSq (greenSum Γ a) (x + γ) = gradSq (greenSum Γ a) x := by
    simp only [gradSq, pd₁, pd₂, hpd]
  by_cases hx : x ∈ punctureSet Γ a η
  · have : x + γ ∈ punctureSet Γ a η := (punctureSet_add_period hγ x).2 hx
    simp [hx, this]
  · have : x + γ ∉ punctureSet Γ a η := fun h => hx ((punctureSet_add_period hγ x).1 h)
    simp [hx, this, ‹gradSq (greenSum Γ a) (x + γ) = _›]

theorem measurable_gradSq (u : ℂ → ℝ) : Measurable (gradSq u) := by
  have h1 : Measurable fun x => fderiv ℝ u x 1 := measurable_fderiv_apply_const ℝ u 1
  have h2 : Measurable fun x => fderiv ℝ u x Complex.I := measurable_fderiv_apply_const ℝ u Complex.I
  exact (h1.pow_const 2).add (h2.pow_const 2)

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem measurable_energyDensity (η : ℝ) : Measurable (energyDensity Γ a η) :=
  (measurable_gradSq _).indicator (isOpen_punctureSet η).isClosed_compl.measurableSet

namespace PairData

variable (h : PairData Γ a ρ)
include h

omit h in
theorem u_contDiffAt {x : ℂ} (hx : x ∉ chargeSet Γ a) : ContDiffAt ℝ 2 (greenSum Γ a) x :=
  (contDiffAt_greenSum hx).of_le (by norm_cast)

theorem u_laplacian {x : ℂ} (hx : x ∉ chargeSet Γ a) : Δ (greenSum Γ a) x = 2 * Real.pi :=
  laplacian_greenSum h.covol hx

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem bump_zero_near {i : Fin N} {x : ℂ} (hx : x ∈ chargeSet Γ a) (hxi : x ≠ a i) :
    bumpFn ρ h.pos (a i) =ᶠ[𝓝 x] fun _ => 0 := by
  have h4 := h.sep i x hx hxi
  filter_upwards [ball_mem_nhds x (by linarith [h.pos] : (0 : ℝ) < 2 * ρ)] with y hy
  refine bumpFn_eq_zero h.pos ?_
  have h1 : ‖y - x‖ < 2 * ρ := by simpa [dist_eq_norm] using hy
  have h2 : ‖x - a i‖ ≤ ‖y - a i‖ + ‖y - x‖ := by
    calc ‖x - a i‖ = ‖(y - a i) - (y - x)‖ := by ring_nf
      _ ≤ ‖y - a i‖ + ‖y - x‖ := norm_sub_le _ _
  linarith

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem bump_one_near (i : Fin N) :
    bumpFn ρ h.pos (a i) =ᶠ[𝓝 (a i)] fun _ => 1 := by
  filter_upwards [ball_mem_nhds (a i) h.pos] with y hy
  have hlt : ‖y - a i‖ < ρ := by simpa [dist_eq_norm] using hy
  exact bumpFn_eq_one h.pos hlt.le

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem oneSubB_zero_near {x : ℂ} (hx : x ∈ chargeSet Γ a) :
    (fun y => 1 - periodizedBump Γ h.pos a y) =ᶠ[𝓝 x] fun _ => 0 := by
  filter_upwards [ball_mem_nhds x h.pos] with y hy
  have : periodizedBump Γ h.pos a y = 1 :=
    periodizedBump_eq_one h.pos h.sep h.distinct hx (by simpa [dist_eq_norm] using hy)
  simp [this]

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem bump_pd_zero_near (i : Fin N) {x : ℂ} (hx : x ∈ chargeSet Γ a) (v : ℂ) :
    (fun y => fderiv ℝ (bumpFn ρ h.pos (a i)) y v) =ᶠ[𝓝 x] fun _ => 0 := by
  by_cases hxi : x = a i
  · subst hxi
    exact pd_eventuallyEq_zero_of_const (h.bump_one_near i) v
  · exact pd_eventuallyEq_zero (h.bump_zero_near hx hxi) v

/-- The exterior of the `η`-disc about `a i`. -/
def S (a : Fin N → ℂ) (η : ℝ) (i : Fin N) : Set ℂ := {x : ℂ | η ≤ ‖x - a i‖}

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] h in
theorem measurableSet_S (η : ℝ) (i : Fin N) : MeasurableSet (S a η i) :=
  (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem contDiff_bump (i : Fin N) : ContDiff ℝ ∞ (bumpFn ρ h.pos (a i)) := contDiff_bumpFn h.pos _

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem bump_hasCompactSupport (i : Fin N) : HasCompactSupport (bumpFn ρ h.pos (a i)) :=
  HasCompactSupport.intro (isCompact_closedBall (a i) (2 * ρ)) fun x hx => by
    refine bumpFn_eq_zero h.pos ?_
    by_contra hlt
    exact hx (by simpa [dist_eq_norm] using (not_le.1 hlt).le)

theorem integrable_bump_mul_u (i : Fin N) :
    Integrable (fun x => bumpFn ρ h.pos (a i) x * greenSum Γ a x) volume :=
  (locallyIntegrable_greenSum (Γ := Γ) (a := a)).integrable_smul_left_of_hasCompactSupport
    (h.contDiff_bump i).continuous (h.bump_hasCompactSupport i)

/-- Away from `a i`, the Green data is regular against the bump `β i`. -/
theorem reg_away {i : Fin N} {x : ℂ} (hx : x ≠ a i) :
    ContDiffAt ℝ 2 (greenSum Γ a) x ∨ bumpFn ρ h.pos (a i) =ᶠ[𝓝 x] fun _ => 0 := by
  by_cases hxP : x ∈ chargeSet Γ a
  · exact Or.inr (h.bump_zero_near hxP hx)
  · exact Or.inl (u_contDiffAt hxP)

theorem continuousAt_piece₁ {i : Fin N} {x : ℂ} (hx : x ≠ a i) :
    ContinuousAt (fun y => bumpFn ρ h.pos (a i) y * gradSq (greenSum Γ a) y) x :=
  (contDiffAt_green_pieces (h.contDiff_bump i) (h.reg_away hx)).1.continuousAt

theorem continuousAt_piece₃ {i : Fin N} {x : ℂ} (hx : x ≠ a i) :
    ContinuousAt (fun y => bumpFn ρ h.pos (a i) y * greenSum Γ a y) x :=
  (contDiffAt_green_pieces (h.contDiff_bump i) (h.reg_away hx)).2.2.continuousAt

theorem contDiffAt_piece₂ (i : Fin N) (x : ℂ) :
    ContDiffAt ℝ 1 (fun y => greenSum Γ a y * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) y) x := by
  by_cases hxP : x ∈ chargeSet Γ a
  · exact contDiffAt_green_piece₂ (h.contDiff_bump i) (Or.inr (h.bump_pd_zero_near i hxP))
  · exact contDiffAt_green_piece₂ (h.contDiff_bump i) (Or.inl (u_contDiffAt hxP))

theorem integrable_piece₂ (i : Fin N) :
    Integrable (fun y => greenSum Γ a y * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) y) volume := by
  refine Continuous.integrable_of_hasCompactSupport
    (continuous_iff_continuousAt.2 fun x => (h.contDiffAt_piece₂ i x).continuousAt) ?_
  refine HasCompactSupport.intro (isCompact_closedBall (a i) (3 * ρ)) fun x hx => ?_
  have hx' : 3 * ρ < ‖x - a i‖ := by
    by_contra hlt
    exact hx (by simpa [dist_eq_norm] using not_lt.1 hlt)
  have h0 : bumpFn ρ h.pos (a i) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [ball_mem_nhds x h.pos] with y hy
    refine bumpFn_eq_zero h.pos ?_
    have h1 : ‖y - x‖ < ρ := by simpa [dist_eq_norm] using hy
    have h2 : ‖x - a i‖ ≤ ‖y - a i‖ + ‖y - x‖ := by
      calc ‖x - a i‖ = ‖(y - a i) - (y - x)‖ := by ring_nf
        _ ≤ ‖y - a i‖ + ‖y - x‖ := norm_sub_le _ _
    linarith
  have h1 := (pd_eventuallyEq_zero h0 1).self_of_nhds
  have h2 := (pd_eventuallyEq_zero h0 Complex.I).self_of_nhds
  simp [gradDot, pd₁, pd₂, h1, h2]

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem bump_mul_density (i : Fin N) {η : ℝ} (hηρ : η ≤ ρ) (x : ℂ) :
    bumpFn ρ h.pos (a i) x * energyDensity Γ a η x =
      Set.indicator (S a η i) (fun y => bumpFn ρ h.pos (a i) y * gradSq (greenSum Γ a) y) x := by
  by_cases hx : ‖x - a i‖ < 2 * ρ
  · have hiff := mem_punctureSet_iff_of_near h.sep hηρ h.pos i hx
    by_cases hxS : x ∈ S a η i
    · have hxS' : η ≤ ‖x - a i‖ := hxS
      have : x ∉ punctureSet Γ a η := fun hm => absurd ((hiff.1 hm)) (not_lt.2 hxS')
      simp [energyDensity, Set.indicator_of_mem hxS, this]
    · have hxS' : ‖x - a i‖ < η := not_le.1 hxS
      have : x ∈ punctureSet Γ a η := hiff.2 hxS'
      simp [energyDensity, Set.indicator_of_notMem hxS, this]
  · have hz : bumpFn ρ h.pos (a i) x = 0 := bumpFn_eq_zero h.pos (not_lt.1 hx)
    have hxS : x ∈ S a η i := by
      show η ≤ ‖x - a i‖
      linarith [not_lt.1 hx, h.pos]
    rw [Set.indicator_of_mem hxS]
    simp [hz]

theorem integrableOn_piece₁ (i : Fin N) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun y => bumpFn ρ h.pos (a i) y * gradSq (greenSum Γ a) y) (S a η i) := by
  refine integrableOn_exterior_of_zero (R := 2 * ρ) hη (fun x hx => ?_) fun x hx => ?_
  · refine h.continuousAt_piece₁ ?_
    intro hxa; rw [hxa, sub_self, norm_zero] at hx; exact absurd hx (not_le.2 hη)
  · simp [bumpFn_eq_zero h.pos hx]

theorem integrableOn_piece₃ (i : Fin N) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun y => bumpFn ρ h.pos (a i) y * greenSum Γ a y) (S a η i) := by
  refine integrableOn_exterior_of_zero (R := 2 * ρ) hη (fun x hx => ?_) fun x hx => ?_
  · refine h.continuousAt_piece₃ ?_
    intro hxa; rw [hxa, sub_self, norm_zero] at hx; exact absurd hx (not_le.2 hη)
  · simp [bumpFn_eq_zero h.pos hx]

/-- The local Green identity at the charge `a i`, split into its three integrals. -/
theorem local_identity (i : Fin N) {η : ℝ} (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∫ x in S a η i, bumpFn ρ h.pos (a i) x * gradSq (greenSum Γ a) x =
      -circleTerm (greenSum Γ a) (a i) η -
        (∫ x in S a η i, greenSum Γ a x * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) x) -
        2 * Real.pi * ∫ x in S a η i, bumpFn ρ h.pos (a i) x * greenSum Γ a x := by
  have key := local_green (u := greenSum Γ a) (β := bumpFn ρ h.pos (a i)) (p := a i) (S := chargeSet Γ a)
    hη hηρ (fun x hx => u_contDiffAt hx) (fun x hx => h.u_laplacian hx) (h.contDiff_bump i)
    (fun x hx => bumpFn_eq_one h.pos hx) (fun x hx => bumpFn_eq_zero h.pos hx)
    (fun x hx hxi => h.bump_zero_near hx hxi)
  have i₁ := h.integrableOn_piece₁ i hη
  have i₃ := h.integrableOn_piece₃ i hη
  have i₂ : IntegrableOn
      (fun y => greenSum Γ a y * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) y) (S a η i) :=
    (h.integrable_piece₂ i).integrableOn
  have hS : {x : ℂ | η ≤ ‖x - a i‖} = S a η i := rfl
  rw [hS] at key
  have i12 : IntegrableOn (fun y => bumpFn ρ h.pos (a i) y * gradSq (greenSum Γ a) y +
      greenSum Γ a y * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) y) (S a η i) := i₁.add i₂
  have i3' : IntegrableOn (fun y => 2 * Real.pi * (bumpFn ρ h.pos (a i) y * greenSum Γ a y))
      (S a η i) := i₃.const_mul (2 * Real.pi)
  rw [integral_add i12 i3', integral_add i₁ i₂, integral_const_mul] at key
  simp only [circleTerm]
  linarith

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem setIntegral_piece₂ (i : Fin N) {η : ℝ} (hηρ : η ≤ ρ) :
    ∫ x in S a η i, greenSum Γ a x * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) x =
      ∫ x, greenSum Γ a x * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) x := by
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
  have hx' : ‖x - a i‖ < η := not_le.1 hx
  have h0 : bumpFn ρ h.pos (a i) =ᶠ[𝓝 x] fun _ => 1 := by
    filter_upwards [ball_mem_nhds x (by linarith : 0 < ρ - ‖x - a i‖)] with y hy
    refine bumpFn_eq_one h.pos ?_
    have h1 : ‖y - x‖ < ρ - ‖x - a i‖ := by simpa [dist_eq_norm] using hy
    have h2 : ‖y - a i‖ ≤ ‖y - x‖ + ‖x - a i‖ := by
      calc ‖y - a i‖ = ‖(y - x) + (x - a i)‖ := by ring_nf
        _ ≤ ‖y - x‖ + ‖x - a i‖ := norm_add_le _ _
    linarith
  have h1 := (pd_eventuallyEq_zero_of_const h0 1).self_of_nhds
  have h2 := (pd_eventuallyEq_zero_of_const h0 Complex.I).self_of_nhds
  simp [gradDot, pd₁, pd₂, h1, h2]

theorem integral_bump_mul_u_split (i : Fin N) {η : ℝ} (hηρ : η ≤ ρ) :
    (∫ x, bumpFn ρ h.pos (a i) x * greenSum Γ a x) -
        ∫ x in S a η i, bumpFn ρ h.pos (a i) x * greenSum Γ a x =
      ∫ x in ball (a i) η, greenSum Γ a x := by
  have hsplit := integral_add_compl (measurableSet_S (a := a) η i) (h.integrable_bump_mul_u i)
  have hc : (S a η i)ᶜ = ball (a i) η := by
    ext x; simp [S, mem_ball, dist_eq_norm]
  rw [hc] at hsplit
  have : ∫ x in ball (a i) η, bumpFn ρ h.pos (a i) x * greenSum Γ a x =
      ∫ x in ball (a i) η, greenSum Γ a x := by
    refine setIntegral_congr_fun measurableSet_ball fun x hx => ?_
    have : ‖x - a i‖ ≤ ρ := by
      have := (mem_ball.1 hx); rw [dist_eq_norm] at this; linarith
    simp [bumpFn_eq_one h.pos this]
  linarith

omit [IsZLattice ℝ Γ] in
/-- The periodized bump. -/
theorem contDiff_B : ContDiff ℝ ∞ (periodizedBump Γ h.pos a) := contDiff_periodizedBump h.pos a

omit [IsZLattice ℝ Γ] in
theorem contDiff_oneSubB : ContDiff ℝ ∞ (fun x => 1 - periodizedBump Γ h.pos a x) :=
  contDiff_const.sub h.contDiff_B

omit h in
theorem u_periodic : ∀ γ ∈ Γ, ∀ x, greenSum Γ a (x + γ) = greenSum Γ a x :=
  fun _ hγ x => greenSum_add_period hγ x

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem B_periodic : ∀ γ ∈ Γ, ∀ x, periodizedBump Γ h.pos a (x + γ) = periodizedBump Γ h.pos a x :=
  fun _ hγ x => periodizedBump_add_period h.pos a hγ x

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem oneSubB_periodic :
    ∀ γ ∈ Γ, ∀ x, (fun y => 1 - periodizedBump Γ h.pos a y) (x + γ) =
      (fun y => 1 - periodizedBump Γ h.pos a y) x := by
  intro γ hγ x; simp only [h.B_periodic γ hγ x]

omit h in
theorem pd_u_periodic (v : ℂ) : ∀ γ ∈ Γ, ∀ x,
    fderiv ℝ (greenSum Γ a) (x + γ) v = fderiv ℝ (greenSum Γ a) x v := by
  intro γ hγ x
  rw [fderiv_periodic Γ (fun δ hδ y => greenSum_add_period hδ y) hγ]

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem pd_B_periodic (v : ℂ) : ∀ γ ∈ Γ, ∀ x,
    fderiv ℝ (periodizedBump Γ h.pos a) (x + γ) v = fderiv ℝ (periodizedBump Γ h.pos a) x v := by
  intro γ hγ x
  rw [fderiv_periodic Γ (fun δ hδ y => h.B_periodic δ hδ y) hγ]

theorem u_regOneSubB (x : ℂ) :
    ContDiffAt ℝ 2 (greenSum Γ a) x ∨
      (fun y => 1 - periodizedBump Γ h.pos a y) =ᶠ[𝓝 x] fun _ => 0 := by
  by_cases hx : x ∈ chargeSet Γ a
  · exact Or.inr (h.oneSubB_zero_near hx)
  · exact Or.inl (u_contDiffAt hx)

omit [IsZLattice ℝ Γ] in
theorem gradDot_oneSubB (x : ℂ) :
    gradDot (fun y => 1 - periodizedBump Γ h.pos a y) (greenSum Γ a) x =
      -gradDot (periodizedBump Γ h.pos a) (greenSum Γ a) x := by
  have hd : DifferentiableAt ℝ (periodizedBump Γ h.pos a) x :=
    (h.contDiff_B.differentiable (by simp)) x
  have e : ∀ v, fderiv ℝ (fun y => 1 - periodizedBump Γ h.pos a y) x v =
      -fderiv ℝ (periodizedBump Γ h.pos a) x v := by
    intro v
    rw [fderiv_const_sub]; rfl
  simp only [gradDot, pd₁, pd₂, e]
  ring

/-- Green's identity on the cell for the cut-off `1 - B`. -/
theorem cell_green :
    ∫ x in torusDomain Γ, (1 - periodizedBump Γ h.pos a x) * gradSq (greenSum Γ a) x =
      (∫ x in torusDomain Γ, greenSum Γ a x * gradDot (periodizedBump Γ h.pos a) (greenSum Γ a) x) +
        2 * Real.pi * ∫ x in torusDomain Γ, periodizedBump Γ h.pos a x * greenSum Γ a x := by
  have hG := periodic_green Γ (u := greenSum Γ a) (φ := fun x => 1 - periodizedBump Γ h.pos a x)
    (S := chargeSet Γ a) u_periodic
    (fun x hx => u_contDiffAt hx) (fun x hx => h.u_laplacian hx)
    (h.contDiff_oneSubB.of_le (by norm_cast)) h.oneSubB_periodic
    (fun x hx => h.oneSubB_zero_near hx)
  -- periodicity of the integrands
  have gper : ∀ γ ∈ Γ, ∀ x, gradSq (greenSum Γ a) (x + γ) = gradSq (greenSum Γ a) x := by
    intro γ hγ x
    simp only [gradSq, pd₁, pd₂]
    rw [pd_u_periodic 1 γ hγ x, pd_u_periodic Complex.I γ hγ x]
  have dper : ∀ γ ∈ Γ, ∀ x, gradDot (periodizedBump Γ h.pos a) (greenSum Γ a) (x + γ) =
      gradDot (periodizedBump Γ h.pos a) (greenSum Γ a) x := by
    intro γ hγ x
    simp only [gradDot, pd₁, pd₂]
    rw [pd_u_periodic 1 γ hγ x, pd_u_periodic Complex.I γ hγ x,
      h.pd_B_periodic 1 γ hγ x, h.pd_B_periodic Complex.I γ hγ x]
  have iA : IntegrableOn (fun x => (1 - periodizedBump Γ h.pos a x) * gradSq (greenSum Γ a) x)
      (torusDomain Γ) := by
    refine integrableOn_torusDomain_of_periodic Γ
      (continuous_iff_continuousAt.2 fun x =>
        (contDiffAt_green_pieces (u := greenSum Γ a) (φ := fun x => 1 - periodizedBump Γ h.pos a x)
          h.contDiff_oneSubB (h.u_regOneSubB x)).1.continuousAt) fun γ hγ x => ?_
    simp only [h.B_periodic γ hγ x, gper γ hγ x]
  have iB : IntegrableOn (fun x => greenSum Γ a x *
      gradDot (fun y => 1 - periodizedBump Γ h.pos a y) (greenSum Γ a) x) (torusDomain Γ) := by
    refine integrableOn_torusDomain_of_periodic Γ
      (continuous_iff_continuousAt.2 fun x => ?_) fun γ hγ x => ?_
    · by_cases hx : x ∈ chargeSet Γ a
      · exact (contDiffAt_green_piece₂ (u := greenSum Γ a)
          (φ := fun x => 1 - periodizedBump Γ h.pos a x) h.contDiff_oneSubB
          (Or.inr (fun v => pd_eventuallyEq_zero (h.oneSubB_zero_near hx) v))).continuousAt
      · exact (contDiffAt_green_piece₂ (u := greenSum Γ a)
          (φ := fun x => 1 - periodizedBump Γ h.pos a x) h.contDiff_oneSubB
          (Or.inl (u_contDiffAt hx))).continuousAt
    · simp only [h.gradDot_oneSubB, u_periodic γ hγ x, dper γ hγ x]
  have iC : IntegrableOn (fun x => (1 - periodizedBump Γ h.pos a x) * greenSum Γ a x)
      (torusDomain Γ) := by
    refine integrableOn_torusDomain_of_periodic Γ
      (continuous_iff_continuousAt.2 fun x =>
        (contDiffAt_green_pieces (u := greenSum Γ a) (φ := fun x => 1 - periodizedBump Γ h.pos a x)
          h.contDiff_oneSubB (h.u_regOneSubB x)).2.2.continuousAt) fun γ hγ x => ?_
    simp only [h.B_periodic γ hγ x, u_periodic γ hγ x]
  have iC' : IntegrableOn (fun x => 2 * Real.pi *
      ((1 - periodizedBump Γ h.pos a x) * greenSum Γ a x)) (torusDomain Γ) := iC.const_mul _
  have iAB : IntegrableOn (fun x => (1 - periodizedBump Γ h.pos a x) * gradSq (greenSum Γ a) x +
      greenSum Γ a x * gradDot (fun y => 1 - periodizedBump Γ h.pos a y) (greenSum Γ a) x)
      (torusDomain Γ) := iA.add iB
  rw [integral_add iAB iC', integral_add iA iB, integral_const_mul] at hG
  -- `B u` is integrable
  obtain ⟨MB, hMB⟩ := exists_bound_of_periodic Γ h.contDiff_B.continuous h.B_periodic
  have iBu : IntegrableOn (fun x => periodizedBump Γ h.pos a x * greenSum Γ a x) (torusDomain Γ) :=
    Integrable.bdd_mul (c := MB) (integrableOn_greenSum (Γ := Γ) (a := a))
      h.contDiff_B.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hMB x)
  have e1 : ∫ x in torusDomain Γ, (1 - periodizedBump Γ h.pos a x) * greenSum Γ a x =
      -∫ x in torusDomain Γ, periodizedBump Γ h.pos a x * greenSum Γ a x := by
    have : ∀ x, (1 - periodizedBump Γ h.pos a x) * greenSum Γ a x =
        greenSum Γ a x - periodizedBump Γ h.pos a x * greenSum Γ a x := fun x => by ring
    simp_rw [this]
    rw [integral_sub integrableOn_greenSum iBu, integral_greenSum]
    ring
  have e2 : ∫ x in torusDomain Γ, greenSum Γ a x *
      gradDot (fun y => 1 - periodizedBump Γ h.pos a y) (greenSum Γ a) x =
      -∫ x in torusDomain Γ, greenSum Γ a x * gradDot (periodizedBump Γ h.pos a) (greenSum Γ a) x := by
    simp_rw [h.gradDot_oneSubB, mul_neg]
    rw [integral_neg]
  rw [e1, e2] at hG
  linarith

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem bumpSum_far {y : ℂ} (hy : (∑ i, ‖a i‖) + 2 * ρ < ‖y - 0‖) : bumpSum ρ h.pos a y = 0 :=
  bumpSum_eq_zero h.pos a (by simpa using hy)

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem fderiv_bumpSum (y v : ℂ) :
    fderiv ℝ (bumpSum ρ h.pos a) y v = ∑ i, fderiv ℝ (bumpFn ρ h.pos (a i)) y v := by
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      DifferentiableAt ℝ (bumpFn ρ h.pos (a i)) y := fun i _ =>
    ((h.contDiff_bump i).differentiable (by simp)) y
  have : bumpSum ρ h.pos a = fun y => ∑ i, bumpFn ρ h.pos (a i) y := rfl
  rw [this, fderiv_fun_sum hd]
  simp [sum_apply]

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem gradDot_bumpSum (y : ℂ) :
    gradDot (bumpSum ρ h.pos a) (greenSum Γ a) y =
      ∑ i, gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) y := by
  simp only [gradDot, pd₁, pd₂, h.fderiv_bumpSum, Finset.sum_mul, Finset.sum_add_distrib]

theorem integrable_u_gradDot_bumpSum :
    Integrable (fun y => greenSum Γ a y * gradDot (bumpSum ρ h.pos a) (greenSum Γ a) y) volume := by
  simp_rw [h.gradDot_bumpSum, Finset.mul_sum]
  exact integrable_finsetSum _ fun i _ => h.integrable_piece₂ i

theorem tsum_cell_gradDot (x : ℂ) :
    ∑' γ : Γ, (greenSum Γ a ((γ : ℂ) + x) *
        gradDot (bumpSum ρ h.pos a) (greenSum Γ a) ((γ : ℂ) + x)) =
      greenSum Γ a x * gradDot (periodizedBump Γ h.pos a) (greenSum Γ a) x := by
  have hs : ∀ v : ℂ, Summable (fun γ : Γ => fderiv ℝ (bumpSum ρ h.pos a) ((γ : ℂ) + x) v) := by
    intro v
    refine summable_translates (Γ := Γ) (f := fun y => fderiv ℝ (bumpSum ρ h.pos a) y v) (c := 0) (ρ := (∑ i, ‖a i‖) + 2 * ρ) (fun y hy => ?_) x
    exact fderiv_eq_zero_of_far (fun z hz => h.bumpSum_far hz) hy v
  have hper : ∀ γ : Γ, greenSum Γ a ((γ : ℂ) + x) = greenSum Γ a x := fun γ => by
    rw [add_comm]; exact u_periodic γ γ.2 x
  have hpd : ∀ (γ : Γ) (v : ℂ), fderiv ℝ (greenSum Γ a) ((γ : ℂ) + x) v =
      fderiv ℝ (greenSum Γ a) x v := fun γ v => by
    rw [add_comm]; exact pd_u_periodic v γ γ.2 x
  have hterm : ∀ γ : Γ, greenSum Γ a ((γ : ℂ) + x) *
      gradDot (bumpSum ρ h.pos a) (greenSum Γ a) ((γ : ℂ) + x) =
      (greenSum Γ a x * fderiv ℝ (greenSum Γ a) x 1) * fderiv ℝ (bumpSum ρ h.pos a) ((γ : ℂ) + x) 1 +
      (greenSum Γ a x * fderiv ℝ (greenSum Γ a) x Complex.I) *
        fderiv ℝ (bumpSum ρ h.pos a) ((γ : ℂ) + x) Complex.I := fun γ => by
    simp only [gradDot, pd₁, pd₂, hper γ, hpd γ]
    ring
  simp_rw [hterm]
  rw [Summable.tsum_add ((hs 1).mul_left _) ((hs Complex.I).mul_left _), tsum_mul_left, tsum_mul_left]
  have e1 := fderiv_periodizedBump (Γ := Γ) h.pos a x 1
  have e2 := fderiv_periodizedBump (Γ := Γ) h.pos a x Complex.I
  rw [← e1, ← e2]
  simp only [gradDot, pd₁, pd₂]
  ring

theorem integral_cell_gradDot :
    ∫ x in torusDomain Γ, greenSum Γ a x * gradDot (periodizedBump Γ h.pos a) (greenSum Γ a) x =
      ∑ i, ∫ x, greenSum Γ a x * gradDot (bumpFn ρ h.pos (a i)) (greenSum Γ a) x := by
  simp_rw [← h.tsum_cell_gradDot]
  rw [integral_torusDomain_tsum Γ h.integrable_u_gradDot_bumpSum]
  simp_rw [h.gradDot_bumpSum, Finset.mul_sum]
  exact integral_finsetSum _ fun i _ => h.integrable_piece₂ i

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem integrable_bumpSum_mul (F : ℂ → ℝ)
    (hF : ∀ i, Integrable (fun y => bumpFn ρ h.pos (a i) y * F y) volume) :
    Integrable (fun y => bumpSum ρ h.pos a y * F y) volume := by
  have : (fun y => bumpSum ρ h.pos a y * F y) = fun y => ∑ i, bumpFn ρ h.pos (a i) y * F y := by
    funext y; simp [bumpSum, Finset.sum_mul]
  rw [this]
  exact integrable_finsetSum _ fun i _ => hF i

theorem integral_cell_B_mul_u :
    ∫ x in torusDomain Γ, periodizedBump Γ h.pos a x * greenSum Γ a x =
      ∑ i, ∫ x, bumpFn ρ h.pos (a i) x * greenSum Γ a x := by
  have hint := h.integrable_bumpSum_mul (greenSum Γ a) h.integrable_bump_mul_u
  have := integral_periodize_mul (Γ := Γ) (f := bumpSum ρ h.pos a) (F := greenSum Γ a) u_periodic hint
  have e : periodizedBump Γ h.pos a = periodize Γ (bumpSum ρ h.pos a) := rfl
  rw [e, this]
  have : (fun y => bumpSum ρ h.pos a y * greenSum Γ a y) =
      fun y => ∑ i, bumpFn ρ h.pos (a i) y * greenSum Γ a y := by
    funext y; simp [bumpSum, Finset.sum_mul]
  rw [this]
  exact integral_finsetSum _ fun i _ => h.integrable_bump_mul_u i

/-- Integrability of the truncated density against the bump `β i`, on the plane. -/
theorem integrable_bump_mul_density (i : Fin N) {η : ℝ} (hη : 0 < η) (hηρ : η ≤ ρ) :
    Integrable (fun y => bumpFn ρ h.pos (a i) y * energyDensity Γ a η y) volume := by
  have : (fun y => bumpFn ρ h.pos (a i) y * energyDensity Γ a η y) =
      Set.indicator (S a η i) (fun y => bumpFn ρ h.pos (a i) y * gradSq (greenSum Γ a) y) := by
    funext y; exact h.bump_mul_density i hηρ y
  rw [this, integrable_indicator_iff (measurableSet_S (a := a) η i)]
  exact h.integrableOn_piece₁ i hη

theorem integral_cell_B_mul_density {η : ℝ} (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∫ x in torusDomain Γ, periodizedBump Γ h.pos a x * energyDensity Γ a η x =
      ∑ i, ∫ x in S a η i, bumpFn ρ h.pos (a i) x * gradSq (greenSum Γ a) x := by
  have hint := h.integrable_bumpSum_mul (energyDensity Γ a η)
    (fun i => h.integrable_bump_mul_density i hη hηρ)
  have hper : ∀ γ ∈ Γ, ∀ x, energyDensity Γ a η (x + γ) = energyDensity Γ a η x :=
    fun _ hγ x => energyDensity_add_period η hγ x
  have := integral_periodize_mul (Γ := Γ) (f := bumpSum ρ h.pos a) (F := energyDensity Γ a η) hper hint
  have e : periodizedBump Γ h.pos a = periodize Γ (bumpSum ρ h.pos a) := rfl
  rw [e, this]
  have h1 : (fun y => bumpSum ρ h.pos a y * energyDensity Γ a η y) =
      fun y => ∑ i, bumpFn ρ h.pos (a i) y * energyDensity Γ a η y := by
    funext y; simp [bumpSum, Finset.sum_mul]
  rw [h1, integral_finsetSum _ fun i _ => h.integrable_bump_mul_density i hη hηρ]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun y => bumpFn ρ h.pos (a i) y * energyDensity Γ a η y) =
      Set.indicator (S a η i) (fun y => bumpFn ρ h.pos (a i) y * gradSq (greenSum Γ a) y) := by
    funext y; exact h.bump_mul_density i hηρ y
  rw [this, integral_indicator (measurableSet_S (a := a) η i)]

omit h in
theorem gradSq_u_periodic : ∀ γ ∈ Γ, ∀ x, gradSq (greenSum Γ a) (x + γ) = gradSq (greenSum Γ a) x := by
  intro γ hγ x
  simp only [gradSq, pd₁, pd₂]
  rw [pd_u_periodic 1 γ hγ x, pd_u_periodic Complex.I γ hγ x]

theorem integrableOn_oneSubB_gradSq :
    IntegrableOn (fun x => (1 - periodizedBump Γ h.pos a x) * gradSq (greenSum Γ a) x)
      (torusDomain Γ) := by
  refine integrableOn_torusDomain_of_periodic Γ
    (continuous_iff_continuousAt.2 fun x =>
      (contDiffAt_green_pieces (u := greenSum Γ a) (φ := fun x => 1 - periodizedBump Γ h.pos a x)
        h.contDiff_oneSubB (h.u_regOneSubB x)).1.continuousAt) fun γ hγ x => ?_
  simp only [h.B_periodic γ hγ x, gradSq_u_periodic γ hγ x]

theorem integrableOn_B_mul_density {η : ℝ} (hη : 0 < η) (hηρ : η ≤ ρ) :
    IntegrableOn (fun x => periodizedBump Γ h.pos a x * energyDensity Γ a η x) (torusDomain Γ) := by
  have hint := h.integrable_bumpSum_mul (energyDensity Γ a η)
    (fun i => h.integrable_bump_mul_density i hη hηρ)
  exact integrableOn_periodize_mul (Γ := Γ) (f := bumpSum ρ h.pos a) (F := energyDensity Γ a η)
    h.contDiff_B.continuous (measurable_energyDensity η).aestronglyMeasurable
    (fun _ hγ x => energyDensity_add_period η hγ x) hint

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem energyDensity_decomp {η : ℝ} (hηρ : η ≤ ρ) (x : ℂ) :
    energyDensity Γ a η x = (1 - periodizedBump Γ h.pos a x) * gradSq (greenSum Γ a) x +
      periodizedBump Γ h.pos a x * energyDensity Γ a η x := by
  by_cases hx : x ∈ punctureSet Γ a η
  · have hB := periodizedBump_eq_one_of_mem_punctureSet h.pos h.sep h.distinct hηρ hx
    simp [energyDensity, hx, hB]
  · simp only [energyDensity, hx, not_false_eq_true, Set.indicator_of_mem, Set.mem_compl_iff]
    ring

/-- **The cell identity for the truncated energy.** -/
theorem energy_identity {η : ℝ} (hη : 0 < η) (hηρ : η ≤ ρ) :
    ∫ x in torusDomain Γ, energyDensity Γ a η x =
      ∑ i, (-circleTerm (greenSum Γ a) (a i) η + 2 * Real.pi * ∫ x in ball (a i) η, greenSum Γ a x) := by
  have e : ∀ x, energyDensity Γ a η x = (1 - periodizedBump Γ h.pos a x) * gradSq (greenSum Γ a) x +
      periodizedBump Γ h.pos a x * energyDensity Γ a η x := h.energyDensity_decomp hηρ
  rw [integral_congr_ae (Filter.Eventually.of_forall e),
    integral_add h.integrableOn_oneSubB_gradSq (h.integrableOn_B_mul_density hη hηρ),
    h.cell_green, h.integral_cell_B_mul_density hη hηρ, h.integral_cell_gradDot,
    h.integral_cell_B_mul_u, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := h.local_identity i hη hηρ
  have h2 := h.setIntegral_piece₂ i hηρ
  have h3 := h.integral_bump_mul_u_split i hηρ
  rw [h1, h2, ← h3]
  ring

end PairData

end Torus

end SandierSerfaty

end
