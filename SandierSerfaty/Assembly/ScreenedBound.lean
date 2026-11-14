/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Assembly.Statements
public import SandierSerfaty.Assembly.CubeRadiusData
public import SandierSerfaty.Screening.TorusProjection
public import SandierSerfaty.Screening.ProjectionTorus

/-!
# One step of I6: screening on `□_{√N}`, projection to `T_N`, and the square-torus bound

`screened_bound` is the deterministic core of the screening note's Proposition `prop:I6`. For one `N ≥ 2`, with `ℓ = √N = s⁴`,
`ℓc = s²`, `ℓt = s³`, the screening data (`ScreeningData 1 1 ℓ₀ C_scr C_S`) applied to `E ∈ elec C`
with `α = r̃ = cubeRadius C ℓ`, then the projection `torusEnergy_le_locEnergy` (I5) and the assumed square-torus bound
(`TorusBoundStatement`) give
```
N W_△ ≤ 2π F^{□_ℓ}(E) + C_S ((A + 1) s⁷ + n_∂),   n_∂ = #(C ∩ □_ℓ ∖ □_{ℓ-4s³}),
```
whenever `F^{□_ℓ} ≠ ⊤` and `∫_{□_ℓ} |E_{1/4}|² ≤ A ℓ²`.
-/

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal Real

public section

namespace SandierSerfaty

namespace Assembly

theorem screened_bound {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C) (hR1 : TorusBoundStatement)
    {ℓ₀ C_scr C_S A : ℝ} (hCscr : 0 < C_scr) (hCS : 0 < C_S)
    (hdata : ScreeningData 1 1 ℓ₀ C_scr C_S) (hA0 : 0 ≤ A)
    {N : ℕ} (hN : 2 ≤ N) {s : ℝ} (hℓ : √(N : ℝ) = s ^ 4) (hs8 : 8 ≤ s) (hsℓ : ℓ₀ ≤ s ^ 2)
    (hsA : A * C_scr ≤ s) (hF : cubeEnergy C E (√(N : ℝ)) ≠ ⊤)
    (hI : ∫⁻ x in cube (√(N : ℝ)),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤
        ENNReal.ofReal (A * (√(N : ℝ)) ^ 2)) :
    ∃ f : ℝ, cubeEnergy C E (√(N : ℝ)) = (f : EReal) ∧
      (N : ℝ) * triangularEnergy ≤ 2 * π * f +
        C_S * ((A + 1) * s ^ 7 +
          ((C ∩ (cube (√(N : ℝ)) \ cube (√(N : ℝ) - 4 * s ^ 3))).ncard : ℝ)) := by
  have hC := hE.1
  set ℓ : ℝ := √(N : ℝ) with hℓdef
  have hℓN : ℓ ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
  have hspos : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  have hs3 : 2 ≤ s ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8) hs8 3]
  have hs23 : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs1 (by norm_num)
  have h8 : 8 * s ^ 3 ≤ ℓ := by
    rw [hℓ]; nlinarith [pow_pos hspos 3]
  obtain ⟨f, hf⟩ : ∃ f : ℝ, cubeEnergy C E ℓ = f :=
    ⟨_, (EReal.coe_toReal hF (Screening.cubeEnergy_ne_bot C E ℓ)).symm⟩
  refine ⟨f, hf, ?_⟩
  -- the strip integral
  have hSsub : sq 0 (ℓ - s ^ 3) \ sq 0 (ℓ - 4 * s ^ 3) ⊆ cube ℓ := by
    refine Set.sdiff_subset.trans ?_
    rw [Screening.sq_zero]
    exact cube_mono (by linarith [pow_pos hspos 3])
  have hSI : ∫⁻ x in sq 0 (ℓ - s ^ 3) \ sq 0 (ℓ - 4 * s ^ 3),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2) ≤ ENNReal.ofReal (A * ℓ ^ 2) :=
    (lintegral_mono_set hSsub).trans hI
  have hSfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSI
  have hSreal : (∫⁻ x in sq 0 (ℓ - s ^ 3) \ sq 0 (ℓ - 4 * s ^ 3),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal ≤ A * ℓ ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hSI
  have hS0 : 0 ≤ (∫⁻ x in sq 0 (ℓ - s ^ 3) \ sq 0 (ℓ - 4 * s ^ 3),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal := ENNReal.toReal_nonneg
  have hSle : (∫⁻ x in sq 0 (ℓ - s ^ 3) \ sq 0 (ℓ - 4 * s ^ 3),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal ≤
        (s ^ 2) ^ 3 * s ^ 3 / C_scr := by
    rw [le_div_iff₀ hCscr]
    have h1 : A * ℓ ^ 2 * C_scr ≤ (s ^ 2) ^ 3 * s ^ 3 := by
      have : ℓ ^ 2 = s ^ 8 := by rw [hℓ]; ring
      rw [this]
      have : A * s ^ 8 * C_scr = (A * C_scr) * s ^ 8 := by ring
      rw [this]
      calc (A * C_scr) * s ^ 8 ≤ s * s ^ 8 := by gcongr
        _ = (s ^ 2) ^ 3 * s ^ 3 := by ring
    exact (mul_le_mul_of_nonneg_right hSreal hCscr.le).trans h1
  have hres := hdata 0 ℓ 1 (s ^ 2) (s ^ 3) N C (cubeRadius C ℓ) E le_rfl le_rfl
    (by rw [one_mul, hℓN]) hsℓ hs23 h8 hC (isChargeField_of_mem_elec hE _)
    (fun p _ => ⟨Screening.cubeRadius_pos hC ℓ p, Screening.cubeRadius_le C ℓ p⟩)
    (fun p _ hp => cubeRadius_eq_quarter_of_notMem C (by rwa [Screening.sq_zero] at hp))
    (fun p hp q hq hpq => cubeRadius_add_le C (s := s ^ 3) hs3 hp.1 hq.1
      (by have := hp.2; rwa [Screening.sq_zero] at this)
      (by have := hq.2; rwa [Screening.sq_zero] at this) hpq)
    (by rw [Screening.sq_zero]; exact lintegral_cubeRadius_ne_top hC E hF) hSfin hSle
  obtain ⟨Y, ρ, E', hYcard, hYmem, hρ, hdisj, hE', hen⟩ := hres
  -- enumerate `Y`
  let e := Finset.equivFinOfCardEq hYcard
  set a : Fin N → ℂ := fun i => ((e.symm i : Y) : ℂ) with ha
  have hainj : Function.Injective a := fun i j h => e.symm.injective (Subtype.ext h)
  have hrange : Set.range a = (Y : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i).2
    · intro hz
      exact ⟨e ⟨z, hz⟩, by simp [ha]⟩
  have himage : Finset.univ.image a = Y := by
    apply Finset.coe_injective
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, hrange]
  have haQ : ∀ i, a i ∈ interior (sq 0 √(N : ℝ)) := fun i => hYmem _ (e.symm i).2
  have hρ0 : ∀ i, 0 < ρ (a i) := fun i => (hρ _ (e.symm i).2).1
  have hρQ : ∀ i, closedBall (a i) (ρ (a i)) ⊆ interior (sq 0 √(N : ℝ)) :=
    fun i => (hρ _ (e.symm i).2).2.2
  have hdisj' : ∀ i j, i ≠ j → ρ (a i) + ρ (a j) ≤ ‖a i - a j‖ := fun i j hij =>
    hdisj _ (e.symm i).2 _ (e.symm j).2 (hainj.ne hij)
  have hE'' : IsNeumannChargeField (sq 0 √(N : ℝ)) 1 (Finset.univ.image a) E' := by
    rw [himage]; exact hE'
  have hproj := torusEnergy_le_locEnergy (by omega : 1 ≤ N) 0 a hainj haQ ρ hρ0 hρQ hdisj' hE''
  have hR := hR1 N hN a (Screening.sub_mem_squareLattice_imp_eq hainj haQ)
  rw [hrange] at hproj
  have hchain := ((EReal.coe_le_coe_iff.2 hR).trans hproj).trans hen
  -- the right-hand side
  have hloc : locEnergy 1 C (cubeRadius C ℓ) E (sq 0 ℓ) = ((2 * π * f : ℝ) : EReal) := by
    rw [Screening.sq_zero, ← two_pi_mul_cubeEnergy hC E ℓ, hf, ← EReal.coe_mul]
  rw [hloc, ← EReal.coe_add, EReal.coe_le_coe_iff] at hchain
  refine hchain.trans ?_
  have hcount : (C ∩ (sq 0 ℓ \ sq 0 (ℓ - 4 * s ^ 3))).ncard =
      (C ∩ (cube ℓ \ cube (ℓ - 4 * s ^ 3))).ncard := by
    rw [Screening.sq_zero, Screening.sq_zero]
  rw [hcount]
  gcongr
  -- `ℓc * S / ℓt + t * ℓt ≤ (A + 1) s⁷`
  have hS' : (s ^ 2) * (∫⁻ x in sq 0 (ℓ - s ^ 3) \ sq 0 (ℓ - 4 * s ^ 3),
      ENNReal.ofReal (‖truncField C (fun _ ↦ 1 / 4) E x‖ ^ 2)).toReal / s ^ 3 ≤ A * s ^ 7 := by
    rw [div_le_iff₀ (by positivity)]
    have : ℓ ^ 2 = s ^ 8 := by rw [hℓ]; ring
    have h2 := mul_le_mul_of_nonneg_left hSreal (by positivity : (0 : ℝ) ≤ s ^ 2)
    rw [this] at h2
    calc _ ≤ s ^ 2 * (A * s ^ 8) := h2
      _ = A * s ^ 7 * s ^ 3 := by ring
  have hts : ℓ * s ^ 3 = s ^ 7 := by rw [hℓ]; ring
  rw [hts]
  linarith [hS']

end Assembly

end SandierSerfaty

end
