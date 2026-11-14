/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.InversionEnergy
public import SandierSerfaty.Sphere.Scaling

/-!
# The two-chart decomposition (sphere note, Proposition 3.9)

For `X ∈ ℂⁿ` pairwise distinct with all `xᵢ ≠ 0` and `r > 0` with `|xᵢ| ≠ r`, write
`S = {i | |xᵢ| < r}`, `N = {i | |xᵢ| > r}`, `X̃ = ι(X)`, `s = s_n`, `D = B(0, r s)`, `D̃ = B(0, s / r)`,
`H = h_X(·/s)`, `H̃ = h_{X̃}(·/s)`. Then
```
π 𝔎(T X) = [W_D(H) + π ∑_{i ∈ S} log λ(xᵢ)] + [W_{D̃}(H̃) + π ∑_{i ∈ N} log λ(x̃ᵢ)] - π n log κ.
```
(`Sphere.two_chart_decomposition`). The proof combines the splitting identity (Prop 3.4), additivity of
the puncture energy across `∂D` (`punctureEnergy_split_ball`), the inversion case of Lemma 3.5
(`punctureEnergy_inv`, with Lemma 3.8 for `H ∘ ι = H̃ + const`) and the scaling case of Lemma 3.5.
-/

open MeasureTheory Set Filter Topology Metric
open scoped Pointwise

public section

namespace SandierSerfaty

namespace Sphere

theorem invC_injective : Function.Injective invC := fun a b h => by
  have := congrArg invC h
  rwa [invC_invC, invC_invC] at this

theorem innerPunct_image {n : ℕ} (X : Fin n → ℂ) (R : ℝ) :
    innerPunct (Finset.univ.image X) R = (Finset.univ.filter fun i => ‖X i‖ < R).image X := by
  ext p
  simp only [mem_innerPunct, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨⟨i, rfl⟩, h⟩; exact ⟨i, h, rfl⟩
  · rintro ⟨i, h, rfl⟩; exact ⟨⟨i, rfl⟩, h⟩

theorem outerPunct_image {n : ℕ} (X : Fin n → ℂ) (R : ℝ) :
    outerPunct (Finset.univ.image X) R = (Finset.univ.filter fun i => R < ‖X i‖).image X := by
  ext p
  simp only [mem_outerPunct, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨⟨i, rfl⟩, h⟩; exact ⟨i, h, rfl⟩
  · rintro ⟨i, h, rfl⟩; exact ⟨⟨i, rfl⟩, h⟩

/-- **Proposition 3.9** (two-chart decomposition). -/
theorem two_chart_decomposition {n : ℕ} (hn : 0 < n) (X : Fin n → ℂ) (hX : Function.Injective X)
    (hX0 : ∀ i, X i ≠ 0) {r : ℝ} (hr : 0 < r) (hrX : ∀ i, ‖X i‖ ≠ r) :
    Real.pi * normalizedEnergy (fun i => stereo (X i)) =
      (punctureEnergy (ball (0 : ℂ) (r * blowupScale n))
          ((Finset.univ.filter fun i => ‖X i‖ < r).image fun i => blowupScale n • X i)
          (blowupPot X) +
        Real.pi * ∑ i ∈ Finset.univ.filter fun i => ‖X i‖ < r, Real.log (lam (X i))) +
      (punctureEnergy (ball (0 : ℂ) (blowupScale n / r))
          ((Finset.univ.filter fun i => r < ‖X i‖).image fun i => blowupScale n • invC (X i))
          (blowupPot fun i => invC (X i)) +
        Real.pi * ∑ i ∈ Finset.univ.filter fun i => r < ‖X i‖, Real.log (lam (invC (X i)))) -
      Real.pi * n * Real.log blowupKappa := by
  classical
  have hs0 := blowupScale_pos hn
  set s := blowupScale n with hs
  set P := Finset.univ.image X with hP
  set S := Finset.univ.filter fun i => ‖X i‖ < r with hS
  set N := Finset.univ.filter fun i => r < ‖X i‖ with hN
  set Xt : Fin n → ℂ := fun i => invC (X i) with hXt
  have hXtinj : Function.Injective Xt := fun a b h => hX (invC_injective h)
  have hPne : ∀ p ∈ P, ‖p‖ ≠ r := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact hrX i
  have hadm := chartPot_admissible X hX
  have hadmt := chartPot_admissible Xt hXtinj
  -- additivity across the circle
  have hA := punctureEnergy_split_ball hadm hPne
  have hin : innerPunct P r = S.image X := innerPunct_image X r
  have hout : outerPunct P r = N.image X := outerPunct_image X r
  -- the inner part of the tilde chart
  have hPt : ∀ q ∈ Finset.univ.image Xt, ‖q‖ ≠ r⁻¹ := by
    intro q hq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hq
    simp only [hXt, norm_invC]
    exact fun h => hrX i (by simpa using congrArg (·⁻¹) h)
  have hinTilde : innerPunct (Finset.univ.image Xt) r⁻¹ = (N.image X).image invC := by
    rw [innerPunct_image, Finset.image_image]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hXt, norm_invC, hN]
    have hpos : 0 < ‖X i‖ := norm_pos_iff.2 (hX0 i)
    exact inv_lt_inv₀ hpos hr
  have hadmTilde : PunctureAdmissible (ball (0 : ℂ) r⁻¹) ((N.image X).image invC) (chartPot Xt) := by
    have := admissible_inner hadmt hPt
    rwa [hinTilde] at this
  -- Lemma 3.8
  have hcomp : ∀ z ∈ ball (0 : ℂ) r⁻¹, z ≠ 0 → z ∉ (N.image X).image invC →
      chartPot X (invC z) = chartPot Xt z + (-∑ i, Real.log ‖X i‖) := by
    intro z hz hz0 hzP
    have hzn : ‖z‖ < r⁻¹ := by simpa using hz
    have hne : ∀ i, z ≠ invC (X i) := by
      intro i hzi
      by_cases hi : r < ‖X i‖
      · exact hzP (Finset.mem_image.2 ⟨X i, Finset.mem_image.2 ⟨i, by simp [hN, hi], rfl⟩, hzi.symm⟩)
      · have hle : ‖X i‖ < r := lt_of_le_of_ne (not_lt.1 hi) (hrX i)
        have hpos : 0 < ‖X i‖ := norm_pos_iff.2 (hX0 i)
        rw [hzi, norm_invC] at hzn
        have := (inv_lt_inv₀ hr hpos).2 hle
        linarith
    rw [chartPot_invC X hX0 hz0 hne]
    ring
  have hB := punctureEnergy_inv hr (P := outerPunct P r) (H' := chartPot Xt)
    (c := -∑ i, Real.log ‖X i‖) (fun p hp => (mem_outerPunct.1 hp).2)
    (admissible_outer hadm hPne) (by rw [hout]; exact hadmTilde) (by rw [hout]; exact hcomp)
  rw [hout] at hB hA
  rw [hin] at hA
  -- scaling of both pieces
  have hinj_card : (S.image X).card = S.card := Finset.card_image_of_injective _ hX
  have hnc : ((N.image X).image invC).card = N.card := by
    rw [Finset.card_image_of_injective _ invC_injective, Finset.card_image_of_injective _ hX]
  have hsmulball : ∀ ρ : ℝ, s • ball (0 : ℂ) ρ = ball (0 : ℂ) (s * ρ) := by
    intro ρ
    rw [smul_ball hs0.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hs0]
  have hC1 := punctureEnergy_smul hs0 (G := ball (0 : ℂ) r) (P := S.image X) (H := chartPot X)
    (by have := (admissible_inner hadm hPne).tendsto_punctureEnergy; rwa [hin] at this)
  have hC2 := punctureEnergy_smul hs0 (G := ball (0 : ℂ) r⁻¹) (P := (N.image X).image invC)
    (H := chartPot Xt) hadmTilde.tendsto_punctureEnergy
  rw [hsmulball, Finset.image_image, hinj_card] at hC1
  rw [hsmulball, Finset.image_image, hnc] at hC2
  have e1 : (fun i => s • X i) = (fun p => s • p) ∘ X := rfl
  have hpot1 : blowupPot X = fun z => chartPot X ((s⁻¹ : ℝ) • z) := rfl
  have hpot2 : (blowupPot fun i => invC (X i)) = fun z => chartPot Xt ((s⁻¹ : ℝ) • z) := rfl
  have hdiv : s / r = s * r⁻¹ := div_eq_mul_inv s r
  rw [hdiv, hpot1, hpot2]
  have hC1' : punctureEnergy (ball (0 : ℂ) (s * r)) (S.image fun i => s • X i)
      (fun z => chartPot X ((s⁻¹ : ℝ) • z)) = punctureEnergy (ball (0 : ℂ) r) (S.image X) (chartPot X) +
        Real.pi * S.card * Real.log s := by
    exact hC1
  have hC2' : punctureEnergy (ball (0 : ℂ) (s * r⁻¹)) (N.image fun i => s • invC (X i))
      (fun z => chartPot Xt ((s⁻¹ : ℝ) • z)) =
      punctureEnergy (ball (0 : ℂ) r⁻¹) ((N.image X).image invC) (chartPot Xt) +
        Real.pi * N.card * Real.log s := by
    rw [Finset.image_image] at hC2
    exact hC2
  rw [mul_comm r s, hC1', hC2']
  -- Proposition 3.4 and bookkeeping
  have h34 := (splitting_identity X hX).2
  have hsplit : ∑ i, Real.log (lam (X i)) =
      ∑ i ∈ S, Real.log (lam (X i)) + ∑ i ∈ N, Real.log (lam (X i)) := by
    have hNe : N = Finset.univ.filter fun i => ¬ ‖X i‖ < r := by
      refine Finset.filter_congr fun i _ => ?_
      constructor
      · intro h; exact not_lt.2 h.le
      · intro h; exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm (hrX i))
    rw [hNe, hS, Finset.sum_filter_add_sum_filter_not]
  have hcardsum : (S.card : ℝ) + N.card = n := by
    have hNe : N = Finset.univ.filter fun i => ¬ ‖X i‖ < r := by
      refine Finset.filter_congr fun i _ => ?_
      constructor
      · intro h; exact not_lt.2 h.le
      · intro h; exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm (hrX i))
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i => ‖X i‖ < r)
    rw [← hNe, ← hS] at this
    rw [← Nat.cast_add, this]
    simp
  have hlamN : ∀ i ∈ N, Real.log (lam (invC (X i))) = Real.log (‖X i‖ ^ 2) + Real.log (lam (X i)) := by
    intro i _
    rw [lam_invC (hX0 i), Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (hX0 i)))
      (lam_pos _).ne']
  have hsumN : ∑ p ∈ N.image X, Real.log (‖p‖ ^ 2) = ∑ i ∈ N, Real.log (‖X i‖ ^ 2) :=
    Finset.sum_image (fun a _ b _ h => hX h)
  have hlogs := log_blowupScale hn
  rw [Finset.sum_congr rfl hlamN, Finset.sum_add_distrib]
  rw [hsumN] at hB
  unfold normalizedEnergy
  have hpi := Real.pi_pos
  have hmul : Real.pi * (S.card : ℝ) * Real.log s + Real.pi * N.card * Real.log s =
      Real.pi * n * Real.log s := by rw [← hcardsum]; ring
  have hmul2 : Real.pi * n * Real.log s =
      Real.pi * n * Real.log blowupKappa + Real.pi * n * Real.log n / 2 := by
    rw [hlogs]; ring
  have hE' : Real.pi * sphereEnergy (fun i => stereo (X i)) =
      Real.pi * ((1 / 2 - Real.log 2) * (n : ℝ) ^ 2) +
        (punctureEnergy Set.univ (Finset.univ.image X) (chartPot X) +
          Real.pi * ∑ i, Real.log (lam (X i))) := by
    rw [h34]
    field_simp
  rw [hsplit] at hE'
  linarith

end Sphere

end SandierSerfaty

end
