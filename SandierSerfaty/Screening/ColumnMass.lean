/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.Pinwheel
public import SandierSerfaty.Screening.ColumnPartition

/-!
# Column masses in the pinwheel (screening note Def 4.15, Lemma 4.17 core, Lemma 4.18(c),(d))

The screening note, §4.7 (`def:columns`, `lem:strip`, `lem:cuts`).
The source `g` of the soft cut (screening note Def 4.10) enters only through the hypotheses bundled in
`Pinwheel.CutHyp` (one structure instead of a dozen binders):

* `g` is integrable on the frame `F` and `∫_F g = 2π n_tot` with `n_tot ∈ ℤ` (Lemma 4.11(c),(d):
  `g = 0` on `Ω_c`, `∫_Q g = 2π(N - #K)`);
* `g = 2πm` a.e. on the bottom parts `Ψ_j([0, L] × [0, d - 1]) ⊆ O_-` (Lemma 4.11(c), Lemma 4.14(c));
* the **strip bound** `∫_{T_I} |g| ≤ (π/2) m w ℓc - 2π` on every top strip `T_I = Ψ_j(I × [d - 1, w_f])`,
  `|I| = w ∈ [ℓc, 3ℓc]`. This is Lemma 4.17 for `κ = 0` with the slack `2π` reserved for the carry
  (`strip_of_bound` derives it from the ring estimate of Lemma 4.12(d) and condition (K1));
* (K2) `1/ℓc ≤ m/8`, (K4) `ℓc ≥ 36`, `d ≥ 8ℓc`, `a□ > 0`, `L ≥ 3ℓc`.

Main results:

* `CutHyp.integral_col_eq_bot_add_top`: `∫_{Col} g = 2πm w (d - 1) + ∫_{T_I} g`;
* `CutHyp.col_mass_ge`: every column of width `w ∈ [ℓc, 3ℓc]` has `g`-mass `≥ 2π(6mwℓc + 1)`;
* `tildeG`: the source with carries, `g̃ = g - ∑_j (2πθ_j / w'_j)(1_{A_j} - 1_{A'_j})`, and
  `CutHyp.integral_col_tildeG`: its mass on a column of `R_j` in terms of the `g`-mass, the carry
  out of `R_j` (`A_j`) and the carry into `R_j` (`A'_{j-1}`);
* `Theta`, `IsK1`, `strip_of_bound`: Definition 4.16 and Lemma 4.17.
-/

open MeasureTheory Set Real
open scoped ENNReal

public section

namespace SandierSerfaty.Screening.Pinwheel

/-- **Hypotheses of the column cut** (screening note, Lemma 4.18), abstracted from the screening data. -/
structure CutHyp (c : ℂ) (t d m ℓ : ℝ) (g : ℂ → ℝ) (ntot : ℤ) : Prop where
  m_pos : 0 < m
  /-- (K2) -/
  K2 : 1 / ℓ ≤ m / 8
  /-- (K4) -/
  K4 : 36 ≤ ℓ
  d_ge : 8 * ℓ ≤ d
  offset_pos : 0 < offset t d
  side_ge : 3 * ℓ ≤ side t d
  integrableOn : IntegrableOn g (frameSet c t d)
  /-- `g = 2πm` on the bottom parts (`⊆ O_-`). -/
  low : ∀ j, ∀ᵐ x, x ∈ (rect c t d j).box (Icc 0 (side t d)) (Icc 0 (d - 1)) → g x = 2 * π * m
  /-- the strip bound (Lemma 4.17 with `κ = 0`, slack `2π` kept for the carry) -/
  strip : ∀ j x w, 0 ≤ x → x + w ≤ side t d → w ∈ Icc ℓ (3 * ℓ) →
    ∫ z in (rect c t d j).box (Icc x (x + w)) (Icc (d - 1) (d + 8)), |g z| ≤
      π / 2 * m * w * ℓ - 2 * π
  /-- `∫_F g = 2π n_tot` -/
  total : ∫ x in frameSet c t d, g x = 2 * π * ntot

/-- The line mass `λ_j(s) = ∫_0^{w_f} g(Ψ_j(s, r)) dr` of the columns of `R_j`. -/
@[expose] noncomputable def lineMass (c : ℂ) (t d : ℝ) (g : ℂ → ℝ) (j : Fin 4) (s : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..(d + 8), g ((rect c t d j).chart ⟨s, r⟩)

/-- The cumulative mass `Λ_j(y) = (2π)⁻¹ ∫_0^y λ_j + θ_{j-1} min(y, 1)` of `g̃^{(j)}` (screening note
Lemma 4.18, proof: `μ(u)`, the incoming carry `θ_{j-1}` being spread on `A'_{j-1}`). -/
@[expose] noncomputable def cumMass (c : ℂ) (t d : ℝ) (g : ℂ → ℝ) (j : Fin 4) (θp y : ℝ) : ℝ :=
  (2 * π)⁻¹ * (∫ s in (0 : ℝ)..y, lineMass c t d g j s) + θp * min y 1

/-- The source with carries `g̃ = g - ∑_j (2πθ_j/w'_j)(1_{A_j} - 1_{A'_j})` (screening note, Lemma 4.18). -/
@[expose] noncomputable def tildeG (c : ℂ) (t d : ℝ) (g : ℂ → ℝ) (θ w : Fin 4 → ℝ) (x : ℂ) : ℝ :=
  g x - ∑ i, 2 * π * θ i / w i *
    ((carryA c t d i (w i)).indicator 1 x - (carryA' c t d i (w i)).indicator 1 x)

theorem measurableSet_carryA {c : ℂ} {t d : ℝ} {j : Fin 4} {w : ℝ} :
    MeasurableSet (carryA c t d j w) :=
  Rect.measurableSet_box measurableSet_Icc measurableSet_Icc

theorem measurableSet_carryA' {c : ℂ} {t d : ℝ} {j : Fin 4} {w : ℝ} :
    MeasurableSet (carryA' c t d j w) :=
  Rect.measurableSet_box measurableSet_Icc measurableSet_Icc

theorem volume_real_Icc_inter_Icc_zero_one {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    volume.real (Icc x y ∩ Icc 0 1) = min y 1 - min x 1 := by
  rw [Icc_inter_Icc, max_eq_left hx, Real.volume_real_Icc]
  rcases le_total x 1 with h | h
  · rw [min_eq_left h, max_eq_left (by simp [h, hxy])]
  · rw [min_eq_right h, min_eq_right (h.trans hxy), max_eq_right (by linarith), sub_self]

/-- **`g̃` on a set of finite measure**: `∫_S g̃ = ∫_S g - ∑_i κ_i (|S ∩ A_i| - |S ∩ A'_i|)`. -/
theorem integral_tildeG {c : ℂ} {t d : ℝ} {g : ℂ → ℝ} (θ w : Fin 4 → ℝ) {S : Set ℂ}
    (hSf : volume S ≠ ⊤) (hg : IntegrableOn g S) :
    ∫ x in S, tildeG c t d g θ w x = (∫ x in S, g x) - ∑ i, 2 * π * θ i / w i *
      (volume.real (S ∩ carryA c t d i (w i)) - volume.real (S ∩ carryA' c t d i (w i))) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hSf
  have hind : ∀ A : Set ℂ, MeasurableSet A → IntegrableOn (A.indicator (1 : ℂ → ℝ)) S :=
    fun A hA => (integrable_const (1 : ℝ)).indicator hA
  have hterm : ∀ i : Fin 4, IntegrableOn (fun x => 2 * π * θ i / w i *
      ((carryA c t d i (w i)).indicator 1 x - (carryA' c t d i (w i)).indicator 1 x)) S :=
    fun i => ((hind _ measurableSet_carryA).sub (hind _ measurableSet_carryA')).const_mul _
  have hreal : ∀ A : Set ℂ, MeasurableSet A →
      ∫ x in S, A.indicator (1 : ℂ → ℝ) x = volume.real (S ∩ A) := by
    intro A hA
    rw [integral_indicator_one hA, measureReal_restrict_apply hA, inter_comm]
  unfold tildeG
  rw [integral_sub hg (integrable_finsetSum _ fun i _ => hterm i), integral_finsetSum _
    fun i _ => hterm i]
  rw [sub_right_inj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_sub (hind _ measurableSet_carryA) (hind _ measurableSet_carryA'),
    hreal _ measurableSet_carryA, hreal _ measurableSet_carryA']

/-! ### Definition 4.16 and Lemma 4.17 -/

/-- `n_D^max(w) = 21(2w+3)a₁ + b₁ √(21(2w+3) M₁ · 32ℓc³/C₁)` (screening note Def 4.16). -/
@[expose] noncomputable def nDmax (a₁ b₁ M₁ C₁ ℓ w : ℝ) : ℝ :=
  21 * (2 * w + 3) * a₁ + b₁ * √(21 * (2 * w + 3) * M₁ * (32 * ℓ ^ 3 / C₁))

/-- `Θ(w) = 18πmw + (13π/6) n_D^max(w) + √(64 w ℓc³/C₁) + 2π` (screening note Def 4.16). -/
@[expose] noncomputable def Theta (m a₁ b₁ M₁ C₁ ℓ w : ℝ) : ℝ :=
  18 * π * m * w + 13 * π / 6 * nDmax a₁ b₁ M₁ C₁ ℓ w + √(64 * w * ℓ ^ 3 / C₁) + 2 * π

/-- Condition **(K1)** of the screening note Def 4.16: `Θ(w) ≤ (π/2) m w ℓc` for every `w ∈ [ℓc, 3ℓc]`. -/
@[expose] def IsK1 (m a₁ b₁ M₁ C₁ ℓ : ℝ) : Prop :=
  ∀ w ∈ Icc ℓ (3 * ℓ), Theta m a₁ b₁ M₁ C₁ ℓ w ≤ π / 2 * m * w * ℓ

/-- **Lemma 4.17** (strip estimate), from the bound `∫_{T_I} |g| ≤ 18πmw + (13π/6) n_D + √(2w S_d)`
of its proof (ring estimates, Lemma 4.12(d)), `n_D ≤ n_D^max(w)`, `S_d ≤ 32ℓc³/C₁` and (K1):
`∫_{T_I} |g - κ 1_{A♭}| ≤ Θ(w) ≤ (π/2) m w ℓc` whenever `κ ≥ 0`, `κ |A♭| ≤ 2π`; in particular
`∫_{T_I} |g| ≤ (π/2) m w ℓc - 2π` (the field `CutHyp.strip`). -/
theorem strip_of_bound {m a₁ b₁ M₁ C₁ ℓ w nD Sd : ℝ} (hK1 : IsK1 m a₁ b₁ M₁ C₁ ℓ)
    (hw : w ∈ Icc ℓ (3 * ℓ)) (hnD : nD ≤ nDmax a₁ b₁ M₁ C₁ ℓ w) (hSd : Sd ≤ 32 * ℓ ^ 3 / C₁)
    {T : Set ℂ} {g : ℂ → ℝ}
    (hg : ∫ z in T, |g z| ≤ 18 * π * m * w + 13 * π / 6 * nD + √(2 * w * Sd))
    (hℓ : 0 ≤ ℓ) :
    ∫ z in T, |g z| ≤ π / 2 * m * w * ℓ - 2 * π ∧
      ∀ {A : Set ℂ} {κ : ℝ}, MeasurableSet A → A ⊆ T → IntegrableOn g T → volume A ≠ ⊤ →
        0 ≤ κ → κ * volume.real A ≤ 2 * π →
        ∫ z in T, |g z - κ * A.indicator 1 z| ≤ Theta m a₁ b₁ M₁ C₁ ℓ w ∧
          Theta m a₁ b₁ M₁ C₁ ℓ w ≤ π / 2 * m * w * ℓ := by
  have hw0 : 0 ≤ w := hℓ.trans hw.1
  have hsq : √(2 * w * Sd) ≤ √(64 * w * ℓ ^ 3 / C₁) := by
    refine Real.sqrt_le_sqrt ?_
    calc 2 * w * Sd ≤ 2 * w * (32 * ℓ ^ 3 / C₁) := by gcongr
      _ = 64 * w * ℓ ^ 3 / C₁ := by ring
  have hgΘ : ∫ z in T, |g z| ≤ Theta m a₁ b₁ M₁ C₁ ℓ w - 2 * π := by
    unfold Theta
    have : 13 * π / 6 * nD ≤ 13 * π / 6 * nDmax a₁ b₁ M₁ C₁ ℓ w := by gcongr
    linarith
  have hK := hK1 w hw
  refine ⟨by linarith, fun {A κ} hA hAT hgT hAf hκ hκA => ⟨?_, hK⟩⟩
  have hA1 : Integrable (A.indicator (1 : ℂ → ℝ)) :=
    (integrable_indicator_iff hA).2 (integrableOn_const hAf)
  have hAi : IntegrableOn (fun z => κ * A.indicator (1 : ℂ → ℝ) z) T := (hA1.const_mul κ).integrableOn
  have hpt : ∀ z, |g z - κ * A.indicator 1 z| ≤ |g z| + κ * A.indicator 1 z := by
    intro z
    have h0 : 0 ≤ κ * A.indicator (1 : ℂ → ℝ) z :=
      mul_nonneg hκ (by by_cases hz : z ∈ A <;> simp [hz])
    refine (abs_sub _ _).trans (le_of_eq ?_)
    rw [abs_of_nonneg h0]
  have hint : ∫ z in T, κ * A.indicator (1 : ℂ → ℝ) z = κ * volume.real A := by
    rw [integral_const_mul, integral_indicator_one hA, measureReal_restrict_apply hA,
      inter_eq_left.2 hAT]
  calc ∫ z in T, |g z - κ * A.indicator 1 z|
      ≤ ∫ z in T, (|g z| + κ * A.indicator 1 z) :=
        integral_mono (hgT.sub hAi).abs (hgT.abs.add hAi) hpt
    _ = (∫ z in T, |g z|) + κ * volume.real A := by rw [integral_add hgT.abs hAi, hint]
    _ ≤ Theta m a₁ b₁ M₁ C₁ ℓ w := by linarith

/-! ### Consequences of the hypotheses -/

namespace CutHyp

variable {c : ℂ} {t d m ℓ : ℝ} {g : ℂ → ℝ} {ntot : ℤ} (h : CutHyp c t d m ℓ g ntot)
include h

theorem ℓ_pos : 0 < ℓ := by linarith [h.K4]

theorem eight_le_mul : 8 ≤ m * ℓ := by
  have h1 := h.K2
  rw [div_le_div_iff₀ h.ℓ_pos (by norm_num : (0 : ℝ) < 8)] at h1
  linarith

theorem d_pos : 0 < d := by linarith [h.d_ge, h.K4]

theorem side_pos : 0 < side t d := by linarith [h.side_ge, h.K4]

theorem rect_subset_frameSet (j : Fin 4) : (rect c t d j).carrier ⊆ frameSet c t d := by
  rw [← iUnion_rect h.offset_pos.le]; exact subset_iUnion (fun j => (rect c t d j).carrier) j

omit h in
theorem box_subset_rect (j : Fin 4) {x y v₁ v₂ : ℝ} (hx : 0 ≤ x) (hy : y ≤ side t d) (hv₁ : 0 ≤ v₁)
    (hv₂ : v₂ ≤ d + 8) : (rect c t d j).box (Icc x y) (Icc v₁ v₂) ⊆ (rect c t d j).carrier :=
  Rect.box_mono (Icc_subset_Icc hx hy) (Icc_subset_Icc hv₁ hv₂)

theorem integrableOn_box (j : Fin 4) {x y v₁ v₂ : ℝ} (hx : 0 ≤ x) (hy : y ≤ side t d) (hv₁ : 0 ≤ v₁)
    (hv₂ : v₂ ≤ d + 8) : IntegrableOn g ((rect c t d j).box (Icc x y) (Icc v₁ v₂)) :=
  h.integrableOn.mono_set ((box_subset_rect j hx hy hv₁ hv₂).trans (h.rect_subset_frameSet j))

/-- `∫_{Ψ_j([x, y] × [0, w_f])} g = ∫_x^y λ_j`. -/
theorem integral_col (j : Fin 4) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ side t d) :
    ∫ z in (rect c t d j).box (Icc x y) (Icc 0 (d + 8)), g z = ∫ s in x..y, lineMass c t d g j s :=
  Rect.setIntegral_box_Icc _ hxy (by linarith [h.d_pos])
    (h.integrableOn_box j hx hy le_rfl le_rfl)

theorem integrableOn_lineMass (j : Fin 4) : IntegrableOn (lineMass c t d g j) (Icc 0 (side t d)) :=
  Rect.integrableOn_line_box _ (by linarith [h.d_pos])
    (h.integrableOn_box j le_rfl le_rfl le_rfl le_rfl)

theorem intervalIntegrable_lineMass (j : Fin 4) {x y : ℝ} (hx : x ∈ Icc 0 (side t d))
    (hy : y ∈ Icc 0 (side t d)) : IntervalIntegrable (lineMass c t d g j) volume x y :=
  ((h.integrableOn_lineMass j).mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable

theorem continuousOn_cumMass (j : Fin 4) (θp : ℝ) :
    ContinuousOn (cumMass c t d g j θp) (Icc 0 (side t d)) := by
  have h1 : ContinuousOn (fun y => ∫ s in (0 : ℝ)..y, lineMass c t d g j s) (Icc 0 (side t d)) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0)
      (b := side t d) (f := lineMass c t d g j)
      (by rw [uIcc_of_le h.side_pos.le]; exact h.integrableOn_lineMass j)
    rwa [uIcc_of_le h.side_pos.le] at this
  exact (continuousOn_const.mul h1).add (continuousOn_const.mul
    (continuous_id.min continuous_const).continuousOn)

omit h in
theorem cumMass_zero (j : Fin 4) (θp : ℝ) : cumMass c t d g j θp 0 = 0 := by
  simp [cumMass]

/-- Increments of the cumulative mass. -/
theorem cumMass_sub (j : Fin 4) (θp : ℝ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ side t d) :
    cumMass c t d g j θp y - cumMass c t d g j θp x =
      (2 * π)⁻¹ * (∫ z in (rect c t d j).box (Icc x y) (Icc 0 (d + 8)), g z) +
        θp * (min y 1 - min x 1) := by
  have hx' : x ∈ Icc 0 (side t d) := ⟨hx, hxy.trans hy⟩
  have hy' : y ∈ Icc 0 (side t d) := ⟨hx.trans hxy, hy⟩
  have h0 : (0 : ℝ) ∈ Icc 0 (side t d) := ⟨le_rfl, h.side_pos.le⟩
  rw [h.integral_col j hx hxy hy, ← intervalIntegral.integral_interval_sub_left
    (h.intervalIntegrable_lineMass j h0 hy') (h.intervalIntegrable_lineMass j h0 hx')]
  unfold cumMass
  ring

/-- **Bottom and top of a column**: `∫_{Col} g = 2πm (y - x)(d - 1) + ∫_{T_{[x,y]}} g`. -/
theorem integral_col_eq_bot_add_top (j : Fin 4) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ side t d) :
    ∫ z in (rect c t d j).box (Icc x y) (Icc 0 (d + 8)), g z =
      2 * π * m * ((y - x) * (d - 1)) +
        ∫ z in (rect c t d j).box (Icc x y) (Icc (d - 1) (d + 8)), g z := by
  have hd := h.d_pos
  have hd1 : (0 : ℝ) ≤ d - 1 := by linarith [h.d_ge, h.K4]
  rw [← Icc_union_Icc_eq_Icc hd1 (by linarith : d - 1 ≤ d + 8), Rect.box_union_right]
  have hdisj : AEDisjoint volume ((rect c t d j).box (Icc x y) (Icc 0 (d - 1)))
      ((rect c t d j).box (Icc x y) (Icc (d - 1) (d + 8))) := by
    refine measure_mono_null ?_ ((rect c t d j).volume_box_singleton_right (Icc x y) (d - 1))
    rw [Rect.box_inter, inter_self]
    refine Rect.box_mono subset_rfl ?_
    rintro r ⟨⟨_, h1⟩, h2, _⟩
    exact le_antisymm h1 h2
  rw [setIntegral_union₀ hdisj
    (Rect.measurableSet_box measurableSet_Icc measurableSet_Icc).nullMeasurableSet
    (h.integrableOn_box j hx hy le_rfl (by linarith))
    (h.integrableOn_box j hx hy hd1 le_rfl)]
  congr 1
  have hlow : ∀ᵐ z ∂volume, z ∈ (rect c t d j).box (Icc x y) (Icc 0 (d - 1)) →
      g z = 2 * π * m := by
    filter_upwards [h.low j] with z hz hzb
    exact hz (Rect.box_mono (Icc_subset_Icc hx hy) subset_rfl hzb)
  rw [setIntegral_congr_ae (Rect.measurableSet_box measurableSet_Icc measurableSet_Icc) hlow,
    setIntegral_const, Rect.volume_real_box, Real.volume_real_Icc, Real.volume_real_Icc,
    max_eq_left (by linarith), max_eq_left (by linarith), smul_eq_mul, sub_zero]
  ring

/-- **Column masses** (screening note, Lemma 4.18(d), for `g`): a column of width `w ∈ [ℓc, 3ℓc]` has
`(2π)⁻¹ ∫_{Col} g ≥ 6mwℓc + 1`. -/
theorem col_mass_ge (j : Fin 4) {x w : ℝ} (hx : 0 ≤ x) (hxw : x + w ≤ side t d)
    (hw : w ∈ Icc ℓ (3 * ℓ)) :
    6 * m * w * ℓ + 1 ≤
      (2 * π)⁻¹ * ∫ z in (rect c t d j).box (Icc x (x + w)) (Icc 0 (d + 8)), g z := by
  have hℓ := h.ℓ_pos
  have hw0 : 0 < w := hℓ.trans_le hw.1
  rw [h.integral_col_eq_bot_add_top j hx (by linarith) hxw]
  have htop := h.strip j x w hx hxw hw
  have habs := abs_integral_le_integral_abs (μ := volume.restrict
    ((rect c t d j).box (Icc x (x + w)) (Icc (d - 1) (d + 8)))) (f := g)
  have hlow := (abs_le.1 (habs.trans htop)).1
  have hπ := Real.pi_pos
  have key : 0 ≤ m * w * (d - 1 - 6 * ℓ - ℓ / 4) := by
    have : 0 ≤ d - 1 - 6 * ℓ - ℓ / 4 := by linarith [h.d_ge, h.K4]
    have := h.m_pos
    positivity
  have e : (2 * π)⁻¹ * (2 * π * m * ((x + w - x) * (d - 1)) +
      ∫ z in (rect c t d j).box (Icc x (x + w)) (Icc (d - 1) (d + 8)), g z) =
      m * w * (d - 1) + (2 * π)⁻¹ *
        ∫ z in (rect c t d j).box (Icc x (x + w)) (Icc (d - 1) (d + 8)), g z := by
    field_simp; ring
  have e2 : (2 * π)⁻¹ * (-(π / 2 * m * w * ℓ - 2 * π)) ≤ (2 * π)⁻¹ *
      ∫ z in (rect c t d j).box (Icc x (x + w)) (Icc (d - 1) (d + 8)), g z := by
    gcongr
  have e3 : (2 * π)⁻¹ * (-(π / 2 * m * w * ℓ - 2 * π)) = 1 - m * w * ℓ / 4 := by
    field_simp; ring
  rw [e]
  linarith

/-- Increments of `Λ_j` over windows of width `w ∈ [ℓc, 3ℓc]` are at least `6mwℓc + 1`. -/
theorem cumMass_sub_ge (j : Fin 4) {θp : ℝ} (hθp : 0 ≤ θp) {x w : ℝ} (hx : 0 ≤ x)
    (hxw : x + w ≤ side t d) (hw : w ∈ Icc ℓ (3 * ℓ)) :
    6 * m * w * ℓ + 1 ≤ cumMass c t d g j θp (x + w) - cumMass c t d g j θp x := by
  have hw0 : 0 ≤ w := h.ℓ_pos.le.trans hw.1
  rw [h.cumMass_sub j θp hx (by linarith) hxw]
  have := h.col_mass_ge j hx hxw hw
  have : 0 ≤ θp * (min (x + w) 1 - min x 1) :=
    mul_nonneg hθp (sub_nonneg.2 (min_le_min_right _ (by linarith)))
  linarith

/-- **The cut of one rectangle** (screening note, Lemma 4.18, construction): a partition of `[0, L]` with
`Λ_j` having integer increments on all non-last columns. -/
theorem exists_rect_cut (j : Fin 4) {θp : ℝ} (hθp : 0 ≤ θp) :
    ∃ K u, IsPartition ℓ 0 (side t d) K u ∧
      ∀ k, k + 1 < K → ∃ z : ℤ,
        cumMass c t d g j θp (u (k + 1)) - cumMass c t d g j θp (u k) = z := by
  refine exists_partition h.ℓ_pos (h.continuousOn_cumMass j θp) (fun y hy hyL => ?_)
    (by linarith [h.side_ge, h.ℓ_pos])
  have hℓ := h.ℓ_pos
  have := h.cumMass_sub_ge j hθp (x := y + ℓ) (w := ℓ) (by linarith) (by linarith)
    ⟨le_rfl, by linarith⟩
  rw [show y + ℓ + ℓ = y + 2 * ℓ by ring] at this
  have : 0 ≤ 6 * m * ℓ * ℓ := by have := h.m_pos; positivity
  linarith

/-! ### The source with carries on a column -/

variable {θ w : Fin 4 → ℝ}

theorem carryA_subset (hw : ∀ i, w i ∈ Icc 0 (3 * ℓ)) (i : Fin 4) :
    carryA c t d i (w i) ⊆ (rect c t d i).carrier :=
  carryA_subset_rect ((hw i).2.trans h.side_ge) (by linarith [h.d_pos])

theorem carryA'_subset (hw : ∀ i, w i ∈ Icc 0 (3 * ℓ)) (i : Fin 4) :
    carryA' c t d i (w i) ⊆ (rect c t d (i + 1)).carrier :=
  carryA'_subset_rect (by linarith [h.side_ge, h.K4]) ((hw i).2.trans (by linarith [h.d_ge, h.K4]))

/-- **`g̃` on a column of `R_j`**: the outgoing carry `A_j` and the incoming carry `A'_{j-1}`. -/
theorem integral_col_tildeG (j : Fin 4) (hw : ∀ i, w i ∈ Icc 0 (3 * ℓ)) {x y : ℝ} (hx : 0 ≤ x)
    (hy : y ≤ side t d) :
    ∫ z in (rect c t d j).box (Icc x y) (Icc 0 (d + 8)), tildeG c t d g θ w z =
      (∫ z in (rect c t d j).box (Icc x y) (Icc 0 (d + 8)), g z) -
        2 * π * θ j / w j * volume.real (Icc x y ∩ Icc (side t d - w j) (side t d)) +
        2 * π * θ (j - 1) / w (j - 1) * (volume.real (Icc x y ∩ Icc 0 1) * w (j - 1)) := by
  set S := (rect c t d j).box (Icc x y) (Icc 0 (d + 8))
  have hSR : S ⊆ (rect c t d j).carrier := box_subset_rect j hx hy le_rfl le_rfl
  have hSf : volume S ≠ ⊤ := by
    rw [Rect.volume_box_Icc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  rw [integral_tildeG θ w hSf (h.integrableOn_box j hx hy le_rfl le_rfl)]
  have hA : ∀ i, volume.real (S ∩ carryA c t d i (w i)) =
      if i = j then volume.real (Icc x y ∩ Icc (side t d - w j) (side t d)) else 0 := by
    intro i
    split_ifs with hij
    · subst hij
      rw [carryA, Rect.box_inter, Rect.volume_real_box, Icc_inter_Icc (a₁ := 0),
        max_eq_right (by linarith [h.d_pos]), min_self, Real.volume_real_Icc]
      norm_num
    · have : volume (S ∩ carryA c t d i (w i)) = 0 :=
        measure_mono_null (inter_subset_inter hSR (h.carryA_subset hw i))
          (aedisjoint_rect h.offset_pos (Ne.symm hij))
      simp [Measure.real, this]
  have hA' : ∀ i, volume.real (S ∩ carryA' c t d i (w i)) =
      if i = j - 1 then volume.real (Icc x y ∩ Icc 0 1) * w (j - 1) else 0 := by
    intro i
    split_ifs with hij
    · subst hij
      have hw1 := hw (j - 1)
      rw [carryA', sub_add_cancel, Rect.box_inter, Rect.volume_real_box, Icc_inter_Icc (a₁ := 0),
        max_self, min_eq_right (by linarith [h.d_ge, hw1.2, h.K4]), Real.volume_real_Icc, sub_zero,
        max_eq_left hw1.1]
    · have hne : j ≠ i + 1 := fun e => hij (by rw [e, add_sub_cancel_right])
      have : volume (S ∩ carryA' c t d i (w i)) = 0 :=
        measure_mono_null (inter_subset_inter hSR (h.carryA'_subset hw i))
          (aedisjoint_rect h.offset_pos hne)
      simp [Measure.real, this]
  simp only [hA, hA', mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  ring

end CutHyp

end SandierSerfaty.Screening.Pinwheel

end
