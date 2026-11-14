/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Whole.LayerCake
public import SandierSerfaty.Screening.LocEnergy
public import SandierSerfaty.Screening.CubeEnergyBound
public import SandierSerfaty.Screening.CubeCutoff

/-!
# The layered inequality (comparison note, Definition `def:layerradii`, Lemma `lem:layerradii`, Proposition
`prop:layered`(i))

Book sign throughout: `Ẽ ∈ elec Λ` (the paper's `E ∈ 𝒜₁` gives `Ẽ = -E`). Fix a function `χ` with
`χ ≤ 1`, `L`-Lipschitz (`L ≥ 1`), `χ = 1` on `K_{R-1} = □_{2(R-1)}` and `χ = 0` off `K_R = □_{2R}`, a
square side `ℓ > 0` with `ℓ/2 + 4 ≤ R`, a level `t ∈ (0, 1)` and a radius `η ∈ (0, ¼]` below the book radii
`r̃_p` of the points of `□_{ℓ+1}`. On the open layer set `A_t = {χ > t}` put `d_p = dist(p, ℂ ∖ A_t)` and
```
ρ_p = r̃_p                  if p ∈ □_{ℓ+1},
ρ_p = min(¼, d_p/2)         if p ∉ □_{ℓ+1}, p ∈ A_t, d_p ≥ 2η,
ρ_p = η                     otherwise.
```

**Theorem** (`twoPi_mul_cubeEnergy_le_locEnergy_layer`).
`2π F^{□_ℓ}(Ẽ, 1) - ∑_{p ∈ Λ ∩ K_R ∖ □_ℓ} 1_{t < χ(p)} (c₀ + π log (L / (χ(p) - t))) ≤ G_{A_t}(η)`,
where `G_{A_t}(η)` is the book's local energy of `Ẽ` with all radii `η` and `c₀ = π log 4 + π²/16`.

## Proof

`G_{A_t}(η) ≥ G_{A_t}(ρ)` by Lemma 4.13 in field form (`locEnergy_le`: `η ≤ ρ`, and the changed balls
`B̄(p, ρ_p)` lie in `A_t`). On `□_ℓ` the truncations at `ρ` and at `r̃` agree (they differ only for points
outside `□_{ℓ+1}`, whose balls of radius `≤ ¼` miss `□_ℓ`), so `G_{A_t}(ρ) ≥ G_{□_ℓ}(r̃) + ∑_{A_t ∖ □_ℓ} τ(ρ_p)`,
and `G_{□_ℓ}(r̃) = 2π F^{□_ℓ}` (`two_pi_mul_cubeEnergy`). Finally `τ(ρ_p) ≥ -c₀ - π log (L/(χ(p) - t))`,
because `(χ(p) - t)/(4L) ≤ ρ_p ≤ ¼` (`d_p ≥ (χ(p) - t)/L` by the Lipschitz bound).
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

public section

namespace SandierSerfaty

namespace Whole

open Screening

/-- The layer radii (comparison note, Definition `def:layerradii`, with `Q = □_ℓ` and the rule for the points near
`Q` absorbed into `p ∈ □_{ℓ+1}`). -/
@[expose] noncomputable def layerRadius (Λ : Set ℂ) (ℓ : ℝ) (A : Set ℂ) (η : ℝ) (p : ℂ) : ℝ :=
  open scoped Classical in
  if p ∈ cube (ℓ + 1) then cubeRadius Λ ℓ p
  else if p ∈ A ∧ 2 * η ≤ infDist p Aᶜ then min (1 / 4) (infDist p Aᶜ / 2) else η

theorem layerRadius_le {Λ : Set ℂ} {ℓ : ℝ} {A : Set ℂ} {η : ℝ} (hη4 : η ≤ 1 / 4) (p : ℂ) :
    layerRadius Λ ℓ A η p ≤ 1 / 4 := by
  unfold layerRadius
  split_ifs
  · exact cubeRadius_le Λ ℓ p
  · exact min_le_left _ _
  · exact hη4

theorem cubeRadius_eq_quarter_of_notMem {Λ : Set ℂ} {ℓ : ℝ} {p : ℂ} (hp : p ∉ cube ℓ) :
    cubeRadius Λ ℓ p = 1 / 4 := by
  unfold cubeRadius
  simp [hp]

theorem tauM_one_quarter : tauM 1 (1 / 4) = -cQuarter 1 := by
  rw [cQuarter, neg_neg]

/-- `τ(ρ) ≥ -c₀ - π log (L / a)` when `a/(4L) ≤ ρ ≤ ¼`, `0 < a ≤ 1 ≤ L`. -/
theorem neg_cQuarter_sub_le_tauM {a L ρ : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (hρ1 : a / (4 * L) ≤ ρ)
    (hρ2 : ρ ≤ 1 / 4) : -cQuarter 1 - Real.pi * Real.log (L / a) ≤ tauM 1 ρ := by
  have hL0 : 0 < L := by linarith
  have hb : 0 < a / (4 * L) := by positivity
  have hlog : Real.log (a / (4 * L)) ≤ Real.log ρ := Real.log_le_log hb hρ1
  have e1 : Real.log (a / (4 * L)) = Real.log a - Real.log 4 - Real.log L := by
    rw [Real.log_div ha.ne' (by positivity), Real.log_mul (by norm_num) hL0.ne']; ring
  have e2 : Real.log (L / a) = Real.log L - Real.log a := Real.log_div hL0.ne' ha.ne'
  have hρ0 : 0 ≤ ρ := hb.le.trans hρ1
  have hsq : ρ ^ 2 ≤ (1 / 4) ^ 2 := pow_le_pow_left₀ hρ0 hρ2 2
  rw [cQuarter_eq, tauM, e2]
  have := Real.pi_pos
  nlinarith [mul_le_mul_of_nonneg_left hlog this.le, mul_le_mul_of_nonneg_left hsq (sq_nonneg Real.pi)]

/-- **The layered inequality** (comparison note, Proposition `prop:layered`(i), before integration in `t`). -/
theorem twoPi_mul_cubeEnergy_le_locEnergy_layer {Λ : Set ℂ} {Et : ℂ → ℂ} (hEt : Et ∈ elec Λ)
    {χ : ℂ → ℝ} (hχc : Continuous χ) (hχ1 : ∀ x, χ x ≤ 1) {L : ℝ} (hL : 1 ≤ L)
    (hχL : ∀ x y, |χ x - χ y| ≤ L * ‖x - y‖) {ℓ R : ℝ} (hR : ℓ / 2 + 4 ≤ R)
    (hχone : ∀ x ∈ cube (2 * (R - 1)), χ x = 1) (hχzero : ∀ x ∉ cube (2 * R), χ x = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hηr : ∀ p ∈ Λ, p ∈ cube (ℓ + 1) → η ≤ cubeRadius Λ ℓ p)
    {S' : Finset ℂ} (hS' : ∀ p, p ∈ S' ↔ p ∈ Λ ∧ p ∈ cube (2 * R) ∧ p ∉ cube ℓ) :
    ((2 * Real.pi : ℝ) : EReal) * cubeEnergy Λ Et ℓ +
        ((-∑ p ∈ S', logLayer (cQuarter 1) L (χ p) t : ℝ) : EReal) ≤
      locEnergy 1 Λ (fun _ => η) Et {x | t < χ x} := by
  have hC := hEt.1
  set A : Set ℂ := {x | t < χ x} with hAdef
  have hAopen : IsOpen A := isOpen_lt continuous_const hχc
  have hAsub : A ⊆ cube (2 * R) := fun x hx => by
    by_contra h
    have : t < χ x := hx
    rw [hχzero x h] at this
    linarith
  have hcubeA : cube (2 * (R - 1)) ⊆ A := fun x hx => by
    show t < χ x
    rw [hχone x hx]; exact ht1
  have hAbdd : Bornology.IsBounded A := (isCompact_cube (2 * R)).isBounded.subset hAsub
  have hAc : (Aᶜ).Nonempty := by
    refine ⟨((R + 1 : ℝ) : ℂ), fun h => ?_⟩
    have h1 := hAsub h
    rw [mem_cube_iff_cubeNorm, cubeNorm] at h1
    have : |(((R + 1 : ℝ) : ℂ)).re| ≤ 2 * R / 2 := (le_max_left _ _).trans h1
    rw [Complex.ofReal_re] at this
    have := le_abs_self (R + 1)
    linarith
  -- the Lipschitz lower bound for `d_p`
  have hd : ∀ p ∈ A, (χ p - t) / L ≤ infDist p Aᶜ := by
    intro p _
    rw [le_infDist hAc]
    intro y hy
    have hyt : χ y ≤ t := not_lt.1 hy
    rw [div_le_iff₀ (by linarith), dist_eq_norm]
    have := hχL p y
    have := le_abs_self (χ p - χ y)
    linarith
  set ρ : ℂ → ℝ := layerRadius Λ ℓ A η with hρdef
  have hρη : ∀ p, η ≤ ρ p ∨ p ∈ cube (ℓ + 1) := by
    intro p
    by_cases h1 : p ∈ cube (ℓ + 1)
    · exact Or.inr h1
    · left
      simp only [hρdef, layerRadius, h1, ↓reduceIte]
      split_ifs with h2
      · exact le_min hη4 (by linarith [h2.2])
      · exact le_rfl
  have hαβ : ∀ p ∈ Λ, η ≤ ρ p := by
    intro p hp
    rcases hρη p with h | h
    · exact h
    · simp only [hρdef, layerRadius, h, ↓reduceIte]; exact hηr p hp h
  have hρ4 : ∀ p, ρ p ≤ 1 / 4 := layerRadius_le hη4
  -- the changed balls lie in `A`
  have hquarter : ∀ p ∈ cube (ℓ + 1), closedBall p (1 / 4) ⊆ A := by
    intro p hp y hy
    refine hcubeA ?_
    rw [mem_cube_iff_cubeNorm] at hp ⊢
    have h1 := abs_cubeNorm_sub_le y p
    rw [mem_closedBall, dist_eq_norm] at hy
    have := (abs_le.1 h1).2
    linarith
  have hball : ∀ p ∈ Λ, η < ρ p → closedBall p (ρ p) ⊆ univ ∩ A := by
    intro p _ hlt
    refine fun y hy => ⟨mem_univ _, ?_⟩
    by_cases h1 : p ∈ cube (ℓ + 1)
    · refine hquarter p h1 (closedBall_subset_closedBall (hρ4 p) hy)
    · have hlt' := hlt
      simp only [hρdef, layerRadius, h1, ↓reduceIte] at hlt' hy
      split_ifs at hlt' hy with h2
      · by_contra hyA
        have h3 := infDist_le_dist_of_mem (x := p) (show y ∈ Aᶜ from hyA)
        rw [mem_closedBall, dist_comm] at hy
        have h4 := min_le_right (1 / 4 : ℝ) (infDist p Aᶜ / 2)
        have h5 : 0 < infDist p Aᶜ := by linarith [h2.2]
        linarith
      · exact absurd hlt' (lt_irrefl _)
  -- monotonicity in the radii (Lemma 4.13)
  have hmono := locEnergy_le isOpen_univ hAopen.measurableSet hAbdd hC
    (isChargeField_of_mem_elec hEt univ) (α := fun _ => η) (β := ρ) (fun _ _ => hη) hαβ
    ⟨1 / 4, fun p _ => hρ4 p⟩ hball
  refine le_trans ?_ hmono
  -- the truncations at `ρ` and at `r̃` agree on `□_ℓ`
  have hρpos : ∀ p ∈ Λ, 0 < ρ p := fun p hp => hη.trans_le (hαβ p hp)
  have htrunc : ∀ x ∈ cube ℓ, truncField Λ ρ Et x = truncField Λ (cubeRadius Λ ℓ) Et x := by
    intro x hx
    unfold truncField
    congr 1
    refine finsum_mem_congr rfl fun p hp => ?_
    by_cases h1 : p ∈ cube (ℓ + 1)
    · simp only [hρdef, layerRadius, h1, ↓reduceIte]
    · have hfar : 1 / 4 < ‖x - p‖ := by
        rw [mem_cube_iff_cubeNorm] at hx h1
        have := (abs_le.1 (abs_cubeNorm_sub_le p x)).2
        rw [norm_sub_rev] at this
        linarith
      rw [Screening.gradient_truncLog_of_gt (hρpos p hp) (lt_of_le_of_lt (hρ4 p) hfar),
        Screening.gradient_truncLog_of_gt (cubeRadius_pos hC ℓ p)
          (lt_of_le_of_lt (cubeRadius_le Λ ℓ p) hfar)]
  -- the sums
  have hcubeA' : cube ℓ ⊆ A := fun x hx => hcubeA (by
    rw [mem_cube_iff_cubeNorm] at hx ⊢; linarith)
  have hfinA : (Λ ∩ A).Finite := (finite_inter_cube hC (2 * R)).subset
    (inter_subset_inter_right _ hAsub)
  have hsplit : Λ ∩ A = (Λ ∩ cube ℓ) ∪ (Λ ∩ (A \ cube ℓ)) := by
    ext p
    simp only [mem_inter_iff, mem_union, Set.mem_sdiff]
    constructor
    · rintro ⟨hp, hpA⟩
      by_cases hq : p ∈ cube ℓ
      · exact Or.inl ⟨hp, hq⟩
      · exact Or.inr ⟨hp, hpA, hq⟩
    · rintro (⟨hp, hq⟩ | ⟨hp, hpA, _⟩)
      · exact ⟨hp, hcubeA' hq⟩
      · exact ⟨hp, hpA⟩
  have hdisj : Disjoint (Λ ∩ cube ℓ) (Λ ∩ (A \ cube ℓ)) :=
    disjoint_left.2 fun p hp hp' => hp'.2.2 hp.2
  have hsum : ∑ᶠ p ∈ Λ ∩ A, tauM 1 (ρ p) =
      ∑ᶠ p ∈ Λ ∩ cube ℓ, tauM 1 (cubeRadius Λ ℓ p) + ∑ᶠ p ∈ Λ ∩ (A \ cube ℓ), tauM 1 (ρ p) := by
    rw [hsplit, finsum_mem_union hdisj (hfinA.subset (by rw [hsplit]; exact subset_union_left))
      (hfinA.subset (by rw [hsplit]; exact subset_union_right))]
    congr 1
    refine finsum_mem_congr rfl fun p hp => ?_
    have h1 : p ∈ cube (ℓ + 1) := by
      have := hp.2; rw [mem_cube_iff_cubeNorm] at this ⊢; linarith
    simp only [hρdef, layerRadius, h1, ↓reduceIte]
  -- the lower bound for the layer terms
  have hτ : ∀ p ∈ Λ ∩ (A \ cube ℓ), -logLayer (cQuarter 1) L (χ p) t ≤ tauM 1 (ρ p) := by
    intro p hp
    obtain ⟨_, hpA, hpℓ⟩ := hp
    have hpt : t < χ p := hpA
    have ha : 0 < χ p - t := by linarith
    have ha1 : χ p - t ≤ 1 := by linarith [hχ1 p]
    have hlayer : logLayer (cQuarter 1) L (χ p) t =
        cQuarter 1 + Real.pi * Real.log (L / (χ p - t)) := by
      unfold logLayer; rw [indicator_of_mem (mem_Iio.2 hpt)]
    rw [hlayer, neg_add]
    by_cases h1 : p ∈ cube (ℓ + 1)
    · simp only [hρdef, layerRadius, h1, ↓reduceIte, cubeRadius_eq_quarter_of_notMem hpℓ,
        tauM_one_quarter]
      have : 0 ≤ Real.log (L / (χ p - t)) :=
        Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
      have := Real.pi_pos
      nlinarith
    · refine neg_cQuarter_sub_le_tauM ha hL ?_ (hρ4 p)
      have hdp := hd p hpA
      have hL0 : 0 < L := by linarith
      have hq : (χ p - t) / (4 * L) ≤ (χ p - t) / L / 2 := by
        rw [div_div, div_le_div_iff_of_pos_left ha (by positivity) (by positivity)]; linarith
      simp only [hρdef, layerRadius, h1, ↓reduceIte]
      split_ifs with h2
      · refine le_min ?_ (hq.trans (by linarith))
        rw [div_le_iff₀ (by positivity)]; linarith
      · have h3 : infDist p Aᶜ < 2 * η := by
          by_contra h4; exact h2 ⟨hpA, not_lt.1 h4⟩
        linarith
  have hsumlow : (-∑ p ∈ S', logLayer (cQuarter 1) L (χ p) t) ≤
      ∑ᶠ p ∈ Λ ∩ (A \ cube ℓ), tauM 1 (ρ p) := by
    have hfin : (Λ ∩ (A \ cube ℓ)).Finite := hfinA.subset fun p hp => ⟨hp.1, hp.2.1⟩
    have hsupp : ∀ p, logLayer (cQuarter 1) L (χ p) t ≠ 0 → p ∈ A := by
      intro p hp
      by_contra h
      apply hp
      unfold logLayer
      exact indicator_of_notMem (fun h' => h (mem_Iio.1 h')) _
    have heq : (-∑ p ∈ S', logLayer (cQuarter 1) L (χ p) t) =
        ∑ᶠ p ∈ Λ ∩ (A \ cube ℓ), -logLayer (cQuarter 1) L (χ p) t := by
      rw [← Finset.sum_neg_distrib, ← finsum_mem_coe_finset]
      apply finsum_mem_inter_support_eq
      ext p
      simp only [mem_inter_iff, Finset.mem_coe, hS', Function.mem_support, ne_eq, neg_eq_zero,
        Set.mem_sdiff]
      constructor
      · rintro ⟨⟨hpΛ, _, hpℓ⟩, hp0⟩
        exact ⟨⟨hpΛ, hsupp p hp0, hpℓ⟩, hp0⟩
      · rintro ⟨⟨hpΛ, hpA, hpℓ⟩, hp0⟩
        exact ⟨⟨hpΛ, hAsub hpA, hpℓ⟩, hp0⟩
    rw [heq, finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
    exact Finset.sum_le_sum fun p hp => hτ p ((Set.Finite.mem_toFinset _).1 hp)
  -- assembling
  rw [two_pi_mul_cubeEnergy hC Et ℓ]
  unfold locEnergy
  rw [hsum]
  have hint : (∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField Λ (cubeRadius Λ ℓ) Et x‖ ^ 2)) ≤
      ∫⁻ x in A, ENNReal.ofReal (‖truncField Λ ρ Et x‖ ^ 2) := by
    have := setLIntegral_congr_fun (μ := volume) (isCompact_cube ℓ).measurableSet
      (f := fun x => ENNReal.ofReal (‖truncField Λ ρ Et x‖ ^ 2))
      (g := fun x => ENNReal.ofReal (‖truncField Λ (cubeRadius Λ ℓ) Et x‖ ^ 2))
      fun x hx => by simp only [htrunc x hx]
    rw [← this]
    exact lintegral_mono_set hcubeA'
  set s₁ := ∑ᶠ p ∈ Λ ∩ cube ℓ, tauM 1 (cubeRadius Λ ℓ p)
  set s₂ := ∑ᶠ p ∈ Λ ∩ (A \ cube ℓ), tauM 1 (ρ p)
  rw [add_assoc, ← EReal.coe_add]
  gcongr
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hint

end Whole

end SandierSerfaty

end
