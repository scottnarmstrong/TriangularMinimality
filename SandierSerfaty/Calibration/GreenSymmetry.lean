/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Coeff
public import SandierSerfaty.Torus.GreenRepr
public import SandierSerfaty.Torus.PotentialUnique
public import SandierSerfaty.ClosedForm.HexLattice

/-!
# Symmetry and normalisation of the theta Green function of the hexagonal lattice

Ingredients of the proof of `cal:green-expansion`, part 1.

* `exists_const_sub_of_periodic`: two `Γ`-periodic functions that are smooth off `Γ`, have the same
  constant Laplacian there and a `-log` singularity at `0` differ by a constant off `Γ`
  (a one-charge instance of `Torus.exists_const_of_periodic_harmonic`).
* `thetaGreen0_rho_mul`: the theta Green function `Ĝ = thetaGreen0 ρ` of `ℤ + ℤρ` (`ρ = e^{πi/3}`) is
  invariant under `w ↦ ρ w` off the lattice. By the lemma above `Ĝ (ρ w) - Ĝ w` is a constant `C`,
  and `ρ⁶ = 1` forces `6 C = 0`. This is the rotation symmetry of the paper's proof; it replaces the
  paper's "invariance of `h_△` under `z ↦ ω z`".
* `exists_torusGreen_eq_greenOne_sub`: the mean-zero Green function of the triangular lattice is
  `greenOne a ρ - c` off the lattice, where `greenOne a ρ z = Ĝ (z / a)`.
-/

open Filter Topology Laplacian
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm Torus

/-- Two periodic functions with the same constant Laplacian off `Γ` and `-log` singularities at `0`
differ by a constant off `Γ`. -/
theorem exists_const_sub_of_periodic (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {f₁ f₂ : ℂ → ℝ} {c : ℝ}
    (hp₁ : ∀ γ ∈ Γ, ∀ x, f₁ (x + γ) = f₁ x) (hp₂ : ∀ γ ∈ Γ, ∀ x, f₂ (x + γ) = f₂ x)
    (hs₁ : ∀ x, x ∉ Γ → ContDiffAt ℝ ∞ f₁ x) (hs₂ : ∀ x, x ∉ Γ → ContDiffAt ℝ ∞ f₂ x)
    (hΔ₁ : ∀ x, x ∉ Γ → Δ f₁ x = c) (hΔ₂ : ∀ x, x ∉ Γ → Δ f₂ x = c)
    (hl₁ : ∃ L, Tendsto (fun z => f₁ z + Real.log ‖z‖) (𝓝[≠] 0) (𝓝 L))
    (hl₂ : ∃ L, Tendsto (fun z => f₂ z + Real.log ‖z‖) (𝓝[≠] 0) (𝓝 L)) :
    ∃ C : ℝ, ∀ x, x ∉ Γ → f₁ x - f₂ x = C := by
  obtain ⟨L₁, h₁⟩ := hl₁
  obtain ⟨L₂, h₂⟩ := hl₂
  set a : Fin 1 → ℂ := fun _ => 0 with ha
  have hP : chargeSet Γ a = (Γ : Set ℂ) := chargeSet_zero Γ
  have hPc : (chargeSet Γ a)ᶜ = (Γ : Set ℂ)ᶜ := by rw [hP]
  have hper : ∀ γ ∈ Γ, ∀ x, (f₁ - f₂) (x + γ) = (f₁ - f₂) x := fun γ hγ x => by
    simp [hp₁ γ hγ x, hp₂ γ hγ x]
  have hharm : InnerProductSpace.HarmonicOnNhd (f₁ - f₂) (chargeSet Γ a)ᶜ := by
    rw [hPc]
    intro x hx
    have hx' : x ∉ Γ := hx
    have hc₁ : ContDiffAt ℝ 2 f₁ x := (hs₁ x hx').of_le (by norm_cast)
    have hc₂ : ContDiffAt ℝ 2 f₂ x := (hs₂ x hx').of_le (by norm_cast)
    refine ⟨hc₁.sub hc₂, ?_⟩
    filter_upwards [hc₁.laplacian_sub_nhds hc₂, (isOpen_lattice_compl Γ).mem_nhds hx] with y hy hyP
    have hy' : y ∉ Γ := hyP
    rw [hy, Pi.sub_apply, hΔ₁ y hy', hΔ₂ y hy']
    simp
  have hlim0 : Tendsto (f₁ - f₂) (𝓝[≠] 0) (𝓝 (L₁ - L₂)) := by
    refine (h₁.sub h₂).congr fun z => ?_
    simp
  have hlim : ∀ p ∈ chargeSet Γ a, ∃ L : ℝ, Tendsto (f₁ - f₂) (𝓝[≠] p) (𝓝 L) := by
    intro p hp
    rw [hP] at hp
    have hmap : Tendsto (fun y => y - p) (𝓝[≠] p) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun y : ℂ => y - p) (𝓝 p) (𝓝 (p - p)) :=
          (continuous_id.sub continuous_const).tendsto p
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        exact sub_ne_zero.2 hy
    refine ⟨L₁ - L₂, (hlim0.comp hmap).congr fun y => ?_⟩
    have := hper p hp (y - p)
    rw [sub_add_cancel] at this
    simpa [Function.comp] using this.symm
  obtain ⟨C, hC⟩ := exists_const_of_periodic_harmonic Γ a hper hharm hlim
  refine ⟨C, fun x hx => ?_⟩
  have hx' : x ∉ chargeSet Γ a := by rw [hP]; exact hx
  simpa using hC x hx'

/-- The properties of `greenOne p ρ` for a lattice `Γ = p (ℤ + ℤ ρ)`. -/
theorem greenOne_data {Γ : Submodule ℤ ℂ} {p : ℂ} (hp : p ≠ 0)
    (hmem : ∀ z, z ∈ Γ ↔ ∃ m n : ℤ, z = p * (m + n * rho)) :
    (∀ γ ∈ Γ, ∀ x, greenOne p rho (x + γ) = greenOne p rho x) ∧
    (∀ x, x ∉ Γ → ContDiffAt ℝ ∞ (greenOne p rho) x) ∧
    (∀ x, x ∉ Γ → Δ (greenOne p rho) x = 2 * Real.pi / (‖p‖ ^ 2 * rho.im)) ∧
    ∃ L : ℝ, Tendsto (fun z => greenOne p rho z + Real.log ‖z‖) (𝓝[≠] 0) (𝓝 L) := by
  have hτ : 0 < rho.im := rho_im_pos
  have hnz : ∀ z, z ∉ Γ → theta rho (z / p) ≠ 0 := by
    intro z hz h
    obtain ⟨m, n, hmn⟩ := (theta_eq_zero_iff hτ _).1 h
    apply hz
    rw [hmem]
    exact ⟨m, n, by rw [← hmn]; field_simp⟩
  refine ⟨?_, ?_, ?_, tendsto_greenOne_add_log hτ hp⟩
  · intro γ hγ z
    obtain ⟨m, n, rfl⟩ := (hmem γ).1 hγ
    exact greenOne_add_period hτ hp z m n
  · intro z hz
    exact contDiffAt_greenOne hτ (hnz z hz)
  · intro z hz
    exact laplacian_greenOne hτ hp (hnz z hz)

theorem norm_rho : ‖rho‖ = 1 := by
  have h : ‖rho‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, rho_re, rho_im]
    have : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
    nlinarith
  have h0 : 0 ≤ ‖rho‖ := norm_nonneg _
  nlinarith

theorem rho_pow_six : rho ^ 6 = 1 := by
  have : rho ^ 6 = (rho ^ 3) ^ 2 := by ring
  rw [this, rho_cube]; norm_num

theorem rho_inv : rho⁻¹ = 1 - rho := by
  have : rho * (1 - rho) = 1 := rho_mul_one_sub
  exact inv_eq_of_mul_eq_one_right this

theorem rho_mul_mem_iff {x : ℂ} : rho * x ∈ hexPair.lattice ↔ x ∈ hexPair.lattice := by
  refine ⟨fun h => ?_, rho_mul_mem⟩
  have := one_sub_rho_mul_mem h
  rwa [← mul_assoc, mul_comm (1 - rho) rho, rho_mul_one_sub, one_mul] at this

/-- The lattice `ℤ + ℤ ρ` is `1 * (ℤ + ℤ ρ)`. -/
theorem hex_mem_one (z : ℂ) :
    z ∈ hexPair.lattice ↔ ∃ m n : ℤ, z = 1 * (m + n * rho) := by
  rw [mem_hexPair_lattice]
  constructor
  · rintro ⟨m, n, h⟩
    exact ⟨n, m, by rw [← h]; ring⟩
  · rintro ⟨m, n, h⟩
    exact ⟨n, m, by rw [h]; ring⟩

/-- The lattice `ℤ + ℤ ρ` is `ρ⁻¹ * (ℤ + ℤ ρ)`. -/
theorem hex_mem_rho_inv (z : ℂ) :
    z ∈ hexPair.lattice ↔ ∃ m n : ℤ, z = rho⁻¹ * (m + n * rho) := by
  have hρ : rho ≠ 0 := rho_ne_zero
  constructor
  · intro h
    obtain ⟨m, n, hmn⟩ := mem_hexPair_lattice.1 (rho_mul_mem h)
    refine ⟨n, m, ?_⟩
    field_simp
    linear_combination (-1 : ℂ) * hmn
  · rintro ⟨m, n, rfl⟩
    rw [rho_inv]
    apply one_sub_rho_mul_mem
    exact mem_hexPair_lattice.2 ⟨n, m, by ring⟩

/-- The theta Green function is invariant under `w ↦ ρ w` modulo a constant. -/
theorem exists_const_thetaGreen0_rho_mul :
    ∃ C : ℝ, ∀ w, w ∉ hexPair.lattice →
      thetaGreen0 rho (rho * w) - thetaGreen0 rho w = C := by
  have hρ : rho ≠ 0 := rho_ne_zero
  have hρ' : rho⁻¹ ≠ 0 := inv_ne_zero hρ
  obtain ⟨hp₁, hs₁, hΔ₁, hl₁⟩ := greenOne_data (Γ := hexPair.lattice) hρ' hex_mem_rho_inv
  obtain ⟨hp₂, hs₂, hΔ₂, hl₂⟩ := greenOne_data (Γ := hexPair.lattice) one_ne_zero hex_mem_one
  obtain ⟨C, hC⟩ := exists_const_sub_of_periodic hexPair.lattice hp₁ hp₂ hs₁ hs₂ hΔ₁
    (fun x hx => (hΔ₂ x hx).trans (by simp [norm_rho])) hl₁ hl₂
  refine ⟨C, fun w hw => ?_⟩
  have := hC w hw
  simpa [greenOne, div_inv_eq_mul, mul_comm] using this

theorem rho_pow_mul_mem_iff (k : ℕ) {x : ℂ} :
    rho ^ k * x ∈ hexPair.lattice ↔ x ∈ hexPair.lattice := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_comm (rho ^ k) rho, mul_assoc, rho_mul_mem_iff, ih]

/-- **Rotation symmetry** of the theta Green function of `ℤ + ℤ ρ`: `Ĝ (ρ w) = Ĝ w` off the
lattice. -/
theorem thetaGreen0_rho_mul {w : ℂ} (hw : w ∉ hexPair.lattice) :
    thetaGreen0 rho (rho * w) = thetaGreen0 rho w := by
  obtain ⟨C, hC⟩ := exists_const_thetaGreen0_rho_mul
  have key : ∀ k : ℕ, thetaGreen0 rho (rho ^ k * w) = thetaGreen0 rho w + k * C := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : rho ^ k * w ∉ hexPair.lattice := fun h => hw ((rho_pow_mul_mem_iff k).1 h)
      have := hC _ hk
      rw [pow_succ, mul_comm (rho ^ k) rho, mul_assoc, ih] at *
      push_cast
      linarith
  have h6 := key 6
  rw [rho_pow_six, one_mul] at h6
  have hC0 : C = 0 := by norm_num at h6; linarith
  have := hC w hw
  rw [hC0] at this
  linarith

/-- The mean-zero Green function of the triangular lattice is `greenOne a ρ` up to a constant. -/
theorem exists_torusGreen_eq_greenOne_sub :
    ∃ c : ℝ, ∀ z, z ∉ triangularLattice →
      torusGreen triangularLattice z = greenOne (a : ℂ) rho z - c := by
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  have hmem : ∀ z, z ∈ triangularLattice ↔ ∃ m n : ℤ, z = (a : ℂ) * (m + n * rho) := by
    intro z
    rw [← triPair_lattice, PeriodPair.mem_lattice, triPair_ω₁, triPair_ω₂]
    constructor
    · rintro ⟨m, n, h⟩
      exact ⟨m, n, by rw [← h]; ring⟩
    · rintro ⟨m, n, h⟩
      exact ⟨m, n, by rw [h]; ring⟩
  obtain ⟨hp₂, hs₂, hΔ₂, hl₂⟩ := greenOne_data (Γ := triangularLattice) ha hmem
  have hc : 2 * Real.pi / (‖(a : ℂ)‖ ^ 2 * rho.im) = 2 * Real.pi := by
    have h1 : ‖(a : ℂ)‖ ^ 2 * rho.im = 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg a_pos.le, a_sq, rho_im]
      have := sqrt_three_pos
      field_simp
    rw [h1, div_one]
  obtain ⟨C, hC⟩ := exists_const_sub_of_periodic triangularLattice
    (fun γ hγ x => torusGreen_add_period triangularLattice hγ x) hp₂
    (fun x hx => contDiffAt_torusGreen triangularLattice hx) hs₂
    (c := 2 * Real.pi)
    (fun x hx => by
      rw [laplacian_torusGreen triangularLattice hx, Torus.covolume_triangularLattice, div_one])
    (fun x hx => (hΔ₂ x hx).trans hc)
    ⟨_, tendsto_torusGreen_add_log triangularLattice⟩ hl₂
  refine ⟨-C, fun z hz => ?_⟩
  have := hC z hz
  linarith

end Calibration

end SandierSerfaty

end
