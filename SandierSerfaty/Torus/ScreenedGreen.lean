/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Torus.ScreenProfile
public import SandierSerfaty.Torus.GreenBounds
public import SandierSerfaty.Torus.PotentialLocal
public import SandierSerfaty.Analysis.LaplacianLocalMin

/-!
# The screened Green function of the square torus

Paper proof of Lemma `geo:separation`. With `G = G_n` the Green function,
`r_* = 1/√π` and `φ` the screening profile (`SandierSerfaty.Torus.screenProfile`), the *screened Green
function* is `K = G - Σ_{γ ∈ Γ} φ(· - γ)`, in which the logarithmic poles cancel: `K` is continuous on `ℂ`
and `Γ`-periodic.

* `SandierSerfaty.Torus.greenReg`: the regular part `G + log ‖·‖` of `G` at `0` (value `R` at `0`),
  smooth near `0` and off the nonzero lattice points, with `Δ = 2π / covol`;
* `SandierSerfaty.Torus.screenedLocal`: the smooth local model `reg - log r_* - (π/2)(‖w‖² - r_*²)`
  of `K` near a lattice point, with `Δ = 2π/covol - 2π`;
* `SandierSerfaty.Torus.screenedGreen`: `K`, defined by `K z = G z - φ(dist(z, Γ))` off `Γ` and
  `K γ = R - log r_* + 1/2`; it equals the local model within distance `r_*` of a lattice point
  (`screenedGreen_eq_local`).
-/

open Filter Topology Metric Set Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Torus

section Reg

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]

/-- The regular part `G_Γ w + log ‖w‖` of the Green function at `0`, with the value `R_Γ` at `w = 0`. -/
@[expose] noncomputable def greenReg (w : ℂ) : ℝ :=
  if w = 0 then torusRobin Γ else torusGreen Γ w + Real.log ‖w‖

theorem contDiffAt_greenReg_zero : ContDiffAt ℝ ∞ (greenReg Γ) 0 := by
  obtain ⟨r, hr, hr0, hev⟩ := torusGreen_localForm Γ
  refine hr.congr_of_eventuallyEq ?_
  rw [eventually_nhdsWithin_iff] at hev
  filter_upwards [hev] with z hz
  by_cases h0 : z = 0
  · subst h0; simp [greenReg, hr0]
  · simp only [greenReg, h0, ite_false]
    rw [hz h0]; ring

theorem contDiffAt_greenReg_of_ne {w : ℂ} (hw : w ≠ 0) (hwΓ : w ∉ Γ) :
    ContDiffAt ℝ ∞ (greenReg Γ) w := by
  have h1 : ContDiffAt ℝ ∞ (fun z : ℂ => torusGreen Γ z + Real.log ‖z‖) w :=
    (contDiffAt_torusGreen Γ hwΓ).add ((contDiffAt_norm ℝ hw).log (norm_ne_zero_iff.2 hw))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with z hz
  simp [greenReg, hz]

theorem contDiffAt_greenReg {w : ℂ} (hw : w = 0 ∨ w ∉ Γ) : ContDiffAt ℝ ∞ (greenReg Γ) w := by
  rcases hw with rfl | hw
  · exact contDiffAt_greenReg_zero Γ
  · by_cases h0 : w = 0
    · subst h0; exact contDiffAt_greenReg_zero Γ
    · exact contDiffAt_greenReg_of_ne Γ h0 hw

theorem laplacian_greenReg_of_ne {w : ℂ} (hw : w ≠ 0) (hwΓ : w ∉ Γ) :
    Δ (greenReg Γ) w = 2 * Real.pi / ZLattice.covolume Γ := by
  have h1 : ContDiffAt ℝ 2 (fun z : ℂ => torusGreen Γ z) w :=
    (contDiffAt_torusGreen Γ hwΓ).of_le (by norm_cast)
  have h2 : ContDiffAt ℝ 2 (fun z : ℂ => Real.log ‖z‖) w :=
    ((contDiffAt_norm ℝ hw).log (norm_ne_zero_iff.2 hw)).of_le (by norm_cast)
  have hev : greenReg Γ =ᶠ[𝓝 w] fun z => torusGreen Γ z + Real.log ‖z‖ := by
    filter_upwards [isOpen_ne.mem_nhds hw] with z hz
    simp [greenReg, hz]
  rw [(InnerProductSpace.laplacian_congr_nhds hev).self_of_nhds]
  have e : (fun z : ℂ => torusGreen Γ z + Real.log ‖z‖) =
      (fun z : ℂ => torusGreen Γ z) + (fun z : ℂ => Real.log ‖z‖) := rfl
  rw [e, ContDiffAt.laplacian_add h1 h2, laplacian_torusGreen Γ hwΓ]
  have := laplacian_log_norm_sub (p := 0) hw
  simp only [sub_zero] at this
  rw [this, add_zero]

theorem laplacian_greenReg {w : ℂ} (hw : w = 0 ∨ w ∉ Γ) :
    Δ (greenReg Γ) w = 2 * Real.pi / ZLattice.covolume Γ := by
  by_cases h0 : w = 0
  · subst h0
    have hc : ContinuousAt (Δ (greenReg Γ)) 0 :=
      Analysis.continuousAt_laplacian
        ((contDiffAt_greenReg_zero Γ).of_le (by norm_cast))
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), Δ (greenReg Γ) z = 2 * Real.pi / ZLattice.covolume Γ := by
      filter_upwards [eventually_notMem_lattice Γ, self_mem_nhdsWithin] with z hz hz0
      exact laplacian_greenReg_of_ne Γ hz0 hz
    have h1 : Tendsto (Δ (greenReg Γ)) (𝓝[≠] (0 : ℂ)) (𝓝 (Δ (greenReg Γ) 0)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (Δ (greenReg Γ)) (𝓝[≠] (0 : ℂ)) (𝓝 (2 * Real.pi / ZLattice.covolume Γ)) :=
      tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
    exact tendsto_nhds_unique h1 h2
  · exact laplacian_greenReg_of_ne Γ h0 (hw.resolve_left h0)

/-- The smooth local model of the screened Green function near a lattice point. -/
@[expose] noncomputable def screenedLocal (w : ℂ) : ℝ :=
  greenReg Γ w - Real.log rStar - Real.pi / 2 * (‖w‖ ^ 2 - rStar ^ 2)

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem screenedLocal_eq_sub (w : ℂ) :
    screenedLocal Γ w = greenReg Γ w -
      ((Real.pi / 2) • ‖w‖ ^ 2 + (Real.log rStar - Real.pi / 2 * rStar ^ 2)) := by
  simp only [screenedLocal, smul_eq_mul]; ring

theorem contDiffAt_screenedLocal {w : ℂ} (hw : w = 0 ∨ w ∉ Γ) :
    ContDiffAt ℝ ∞ (screenedLocal Γ) w := by
  have : screenedLocal Γ = fun w => greenReg Γ w -
      ((Real.pi / 2) • ‖w‖ ^ 2 + (Real.log rStar - Real.pi / 2 * rStar ^ 2)) := by
    funext w; exact screenedLocal_eq_sub Γ w
  rw [this]
  refine (contDiffAt_greenReg Γ hw).sub ?_
  exact ((contDiff_norm_sq ℝ).contDiffAt.const_smul _).add contDiffAt_const

theorem laplacian_screenedLocal {w : ℂ} (hw : w = 0 ∨ w ∉ Γ) :
    Δ (screenedLocal Γ) w = 2 * Real.pi / ZLattice.covolume Γ - 2 * Real.pi := by
  have hq : ContDiffAt ℝ 2 (fun w : ℂ => (Real.pi / 2) • ‖w‖ ^ 2 +
      (Real.log rStar - Real.pi / 2 * rStar ^ 2)) w :=
    ((contDiff_norm_sq ℝ).contDiffAt.const_smul _).add contDiffAt_const
  have hr : ContDiffAt ℝ 2 (greenReg Γ) w :=
    (contDiffAt_greenReg Γ hw).of_le (by norm_cast)
  have : screenedLocal Γ = fun w => greenReg Γ w -
      ((Real.pi / 2) • ‖w‖ ^ 2 + (Real.log rStar - Real.pi / 2 * rStar ^ 2)) := by
    funext w; exact screenedLocal_eq_sub Γ w
  have e : (fun w : ℂ => greenReg Γ w -
      ((Real.pi / 2) • ‖w‖ ^ 2 + (Real.log rStar - Real.pi / 2 * rStar ^ 2))) =
      greenReg Γ - fun w : ℂ => (Real.pi / 2) • ‖w‖ ^ 2 +
        (Real.log rStar - Real.pi / 2 * rStar ^ 2) := rfl
  have hΔq : Δ (fun w : ℂ => ((Real.pi / 2) • ‖w‖ ^ 2 +
      (Real.log rStar - Real.pi / 2 * rStar ^ 2) : ℝ)) w = 2 * Real.pi := by
    have e2 : (fun w : ℂ => (Real.pi / 2) • ‖w‖ ^ 2 + (Real.log rStar - Real.pi / 2 * rStar ^ 2)) =
        (fun w : ℂ => (Real.pi / 2) • ‖w‖ ^ 2) + fun _ => (Real.log rStar - Real.pi / 2 * rStar ^ 2) :=
      rfl
    have e3 : (fun w : ℂ => (Real.pi / 2) • ‖w‖ ^ 2) = (Real.pi / 2) • fun w : ℂ => ‖w‖ ^ 2 := rfl
    rw [e2, ContDiffAt.laplacian_add ((contDiff_norm_sq ℝ).contDiffAt.const_smul _) contDiffAt_const,
      InnerProductSpace.laplacian_const, Pi.zero_apply, add_zero, e3, InnerProductSpace.laplacian_smul _ (contDiff_norm_sq ℝ).contDiffAt,
      Analysis.laplacian_norm_sq]
    simp
    ring
  rw [this, e, ContDiffAt.laplacian_sub hr hq, laplacian_greenReg Γ hw]
  simp only [hΔq]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem screenedLocal_zero :
    screenedLocal Γ 0 = torusRobin Γ - Real.log rStar + 1 / 2 := by
  have := pi_mul_rStar_sq
  simp only [screenedLocal, greenReg, ite_true, norm_zero]
  nlinarith [this]

end Reg

section Screened

variable (Γ : Submodule ℤ ℂ)

/-- The screening `Σ_γ φ(· - γ)` of the lattice points: `φ` of the lattice distance. -/
@[expose] noncomputable def screenFn (z : ℂ) : ℝ := screenProfile (infDist z (Γ : Set ℂ))

/-- The screened Green function `K`: `G - Σ_γ φ(· - γ)`, with the removable value at lattice points. -/
@[expose] noncomputable def screenedGreen (z : ℂ) : ℝ :=
  open Classical in
  if z ∈ Γ then torusRobin Γ - Real.log rStar + 1 / 2 else torusGreen Γ z - screenFn Γ z

theorem screenedGreen_of_notMem {z : ℂ} (hz : z ∉ Γ) :
    screenedGreen Γ z = torusGreen Γ z - screenFn Γ z := by
  classical
  simp [screenedGreen, hz]

theorem screenedGreen_of_mem {z : ℂ} (hz : z ∈ Γ) :
    screenedGreen Γ z = torusRobin Γ - Real.log rStar + 1 / 2 := by
  classical
  simp [screenedGreen, hz]

variable [DiscreteTopology Γ]

theorem screenFn_nonneg {z : ℂ} (hz : z ∉ Γ) : 0 ≤ screenFn Γ z :=
  screenProfile_nonneg (infDist_pos_of_notMem Γ hz)

theorem screenFn_pos {z : ℂ} (hz : z ∉ Γ) (h : infDist z (Γ : Set ℂ) < rStar) :
    0 < screenFn Γ z :=
  screenProfile_pos (infDist_pos_of_notMem Γ hz) h

omit [DiscreteTopology Γ] in
theorem screenFn_eq_zero {z : ℂ} (h : rStar ≤ infDist z (Γ : Set ℂ)) : screenFn Γ z = 0 :=
  screenProfile_of_le h

theorem screenedGreen_add_period [IsZLattice ℝ Γ] {γ : ℂ} (hγ : γ ∈ Γ) (z : ℂ) :
    screenedGreen Γ (z + γ) = screenedGreen Γ z := by
  by_cases hz : z ∈ Γ
  · rw [screenedGreen_of_mem Γ hz, screenedGreen_of_mem Γ (Γ.add_mem hz hγ)]
  · have hz' : z + γ ∉ Γ := fun h => hz (by simpa using Γ.sub_mem h hγ)
    rw [screenedGreen_of_notMem Γ hz, screenedGreen_of_notMem Γ hz', torusGreen_add_period Γ hγ]
    simp only [screenFn, infDist_add_mem Γ hγ]

end Screened

section Square

variable (n : ℕ) [NeZero n]

/-- Near a lattice point `γ₀` (within `r_*`) the screened Green function is the smooth local model. -/
theorem screenedGreen_eq_local (hn : 2 ≤ n) {z γ₀ : ℂ} (hγ₀ : γ₀ ∈ squareLattice n)
    (hz : ‖z - γ₀‖ < rStar) :
    screenedGreen (squareLattice n) z = screenedLocal (squareLattice n) (z - γ₀) := by
  set Γ := squareLattice n with hΓ
  have hlt := rStar_lt_sqrt_div_two hn
  have hr := rStar_pos
  have hL : (0 : ℝ) < √n := by linarith
  by_cases hzΓ : z ∈ Γ
  · have hw0 : z - γ₀ = 0 := by
      by_contra h
      have := sqrt_le_norm_of_mem_squareLattice (Γ.sub_mem hzΓ hγ₀) h
      linarith
    rw [screenedGreen_of_mem Γ hzΓ, hw0, screenedLocal_zero]
  · have hw0 : z - γ₀ ≠ 0 := fun h => hzΓ (by rw [sub_eq_zero.1 h]; exact hγ₀)
    have ht : 0 < ‖z - γ₀‖ := norm_pos_iff.2 hw0
    have hinf : infDist z (Γ : Set ℂ) = ‖z - γ₀‖ :=
      infDist_eq_norm_sub hγ₀ (by linarith)
    rw [screenedGreen_of_notMem Γ hzΓ]
    unfold screenFn
    rw [hinf, screenProfile_of_lt hz]
    have hG : torusGreen Γ z = torusGreen Γ (z - γ₀) := (torusGreen_sub_period Γ hγ₀ z).symm
    rw [hG]
    simp only [screenedLocal, greenReg, hw0, ite_false, screenFormula]
    rw [Real.log_div ht.ne' hr.ne']
    ring

theorem continuousAt_screenedLocal_zero : ContinuousAt (screenedLocal (squareLattice n)) 0 :=
  (contDiffAt_screenedLocal _ (Or.inl rfl)).continuousAt

/-- The screened Green function is continuous on `ℂ`. -/
theorem continuous_screenedGreen (hn : 2 ≤ n) : Continuous (screenedGreen (squareLattice n)) := by
  set Γ := squareLattice n with hΓ
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ Γ
  · have hcomp : ContinuousAt (fun z' : ℂ => screenedLocal Γ (z' - z)) z := by
      have h1 : ContinuousAt (screenedLocal Γ) (z - z) := by
        rw [sub_self]; exact continuousAt_screenedLocal_zero n
      exact h1.comp (f := fun z' : ℂ => z' - z) (by fun_prop)
    refine hcomp.congr ?_
    filter_upwards [ball_mem_nhds z rStar_pos] with z' hz'
    exact (screenedGreen_eq_local n hn hz (by simpa [dist_eq_norm] using hz')).symm
  · have hopen : ∀ᶠ z' in 𝓝 z, z' ∉ Γ := (isClosed_lattice Γ).isOpen_compl.mem_nhds hz
    have hG : ContinuousAt (torusGreen Γ) z := (contDiffAt_torusGreen Γ hz).continuousAt
    have hS : ContinuousAt (screenFn Γ) z :=
      (continuousAt_screenProfile (infDist_pos_of_notMem Γ hz)).comp
        (f := fun z : ℂ => infDist z (Γ : Set ℂ)) (continuous_infDist_lattice Γ).continuousAt
    refine (hG.sub hS).congr ?_
    filter_upwards [hopen] with z' hz'
    exact (screenedGreen_of_notMem Γ hz').symm

end Square

end Torus

end SandierSerfaty

end
