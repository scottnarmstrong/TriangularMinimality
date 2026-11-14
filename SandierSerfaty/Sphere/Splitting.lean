/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Puncture
public import SandierSerfaty.Sphere.Chordal

/-!
# The exact splitting identity, first part (sphere note, Proposition 3.4)

For pairwise distinct `X = (x₁, …, xₙ) ∈ ℂⁿ`,
`W_ℂ(h_X) = π [∑_{i ≠ j} g(xᵢ - xⱼ) + n ∑ᵢ V(xᵢ) - n²/2]`:

* `Sphere.chartPot_local_form`: near `xᵢ`, `h_X = s - log |· - xᵢ|` with `s` smooth;
* `Sphere.tendsto_punctureTrunc_chartPot`: the truncated energies converge to the stated value;
* `Sphere.punctureEnergy_chartPot`: the first identity of Proposition 3.4.
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

/-- The smooth part of `h_X` at `xᵢ`. -/
@[expose] noncomputable def chartSmooth {n : ℕ} (X : Fin n → ℂ) (i : Fin n) (x : ℂ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, gKer (x - X j) + (n : ℝ) / 2 * potV x

theorem chartPot_eq_smooth_sub_log {n : ℕ} (X : Fin n → ℂ) (i : Fin n) (x : ℂ) :
    chartPot X x = chartSmooth X i x - Real.log ‖x - X i‖ := by
  unfold chartPot chartSmooth
  rw [← Finset.add_sum_erase Finset.univ (fun j => gKer (x - X j)) (Finset.mem_univ i)]
  simp only [gKer]
  ring

theorem contDiffAt_chartSmooth {n : ℕ} (X : Fin n → ℂ) (hX : Function.Injective X) (i : Fin n) :
    ContDiffAt ℝ 1 (chartSmooth X i) (X i) := by
  unfold chartSmooth
  refine (ContDiffAt.sum fun j hj => ?_).add (contDiffAt_const.mul (contDiff_potV.of_le (by norm_cast)).contDiffAt)
  have hne : X i ≠ X j := fun h => (Finset.ne_of_mem_erase hj) (hX h).symm
  exact (contDiffAt_gKer_sub hne).of_le (by norm_cast)

theorem chartSmooth_apply {n : ℕ} (X : Fin n → ℂ) (i : Fin n) :
    chartSmooth X i (X i) =
      ∑ j ∈ Finset.univ.erase i, gKer (X i - X j) + (n : ℝ) / 2 * potV (X i) := rfl

theorem eventually_differentiableAt_chartPot {n : ℕ} (X : Fin n → ℂ) (i : Fin n) :
    ∀ᶠ x in 𝓝[≠] (X i), DifferentiableAt ℝ (chartPot X) x := by
  have hfin : IsClosed (((Finset.univ.image X).erase (X i) : Finset ℂ) : Set ℂ) :=
    (Finset.finite_toSet _).isClosed
  have hmem : (((Finset.univ.image X).erase (X i) : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 (X i) :=
    hfin.isOpen_compl.mem_nhds (by simp)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hmem, self_mem_nhdsWithin] with x hx hx'
  refine (contDiffAt_chartPot X fun j h => ?_).differentiableAt (by norm_num)
  by_cases hji : X j = X i
  · exact hx' (h.trans hji)
  · exact hx (by simp [h, hji])

theorem tendsto_circleTerm_chartPot {n : ℕ} (X : Fin n → ℂ) (hX : Function.Injective X) (i : Fin n) :
    Tendsto (fun η => circleTerm (chartPot X) (X i) η - 2 * Real.pi * Real.log η) (𝓝[>] 0)
      (𝓝 (-(2 * Real.pi) * chartSmooth X i (X i))) :=
  tendsto_circleTerm_sub_log (contDiffAt_chartSmooth X hX i)
    (Filter.Eventually.of_forall fun x => chartPot_eq_smooth_sub_log X i x)
    (eventually_differentiableAt_chartPot X i)

theorem tendsto_integral_Omega_lap {n : ℕ} (X : Fin n → ℂ) :
    Tendsto (fun η : ℝ => ∫ x in Omega (Finset.univ.image X) η, chartPot X x * chartLap n x)
      (𝓝[>] 0) (𝓝 (∫ x, chartPot X x * chartLap n x)) := by
  have hint : Integrable fun x => chartPot X x * chartLap n x :=
    (integrableOn_chartPot_lap X Set.univ).integrable_of_forall_notMem_eq_zero (fun x hx => absurd trivial hx)
      |>.mono_measure le_rfl
  have e : ∀ η : ℝ, (∫ x in Omega (Finset.univ.image X) η, chartPot X x * chartLap n x) =
      ∫ x, (Omega (Finset.univ.image X) η).indicator (fun x => chartPot X x * chartLap n x) x :=
    fun η => (integral_indicator (isClosed_Omega _ η).measurableSet).symm
  simp only [e]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => ‖chartPot X x * chartLap n x‖)
    ?_ ?_ hint.norm ?_
  · refine Filter.Eventually.of_forall fun η => ?_
    have hL : Measurable (chartLap n) := measurable_const.mul continuous_dens.measurable
    exact (((measurable_chartPot X).mul hL).indicator (isClosed_Omega _ η).measurableSet).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun η => Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ Omega (Finset.univ.image X) η
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
  · filter_upwards [(Finset.univ.image X).finite_toSet.countable.ae_notMem volume] with x hx
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), x ∈ Omega (Finset.univ.image X) η := by
      unfold Omega
      simp only [Set.mem_ofPred_eq]
      rw [Filter.eventually_all_finset]
      intro p hp
      have hpos : 0 < ‖x - p‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hx (h ▸ hp))
      exact mem_nhdsWithin_of_mem_nhds
        (Filter.mem_of_superset (Iio_mem_nhds hpos) fun η hη => le_of_lt hη)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with η hη
    rw [Set.indicator_of_mem hη]

/-- The value `π [∑_{i ≠ j} g(xᵢ - xⱼ) + n ∑ᵢ V(xᵢ) - n²/2]` of the puncture energy of `h_X`. -/
@[expose] noncomputable def splittingValue {n : ℕ} (X : Fin n → ℂ) : ℝ :=
  Real.pi * (∑ i, ∑ j ∈ Finset.univ.erase i, gKer (X i - X j) +
    (n : ℝ) * ∑ i, potV (X i) - (n : ℝ) ^ 2 / 2)

theorem integral_chartPot_lap {n : ℕ} (X : Fin n → ℂ) :
    ∫ x, chartPot X x * chartLap n x =
      2 * Real.pi * n * (-(1 / 2) * ∑ i, potV (X i) + (n : ℝ) / 2) := by
  have : (fun x => chartPot X x * chartLap n x) = fun x => 2 * Real.pi * n * (chartPot X x * dens x) := by
    funext x; simp only [chartLap]; ring
  rw [this, integral_const_mul, integral_chartPot_dens]

/-- **Proposition 3.4, first identity** (as a limit): the truncated energies of `h_X` converge to
`π [∑_{i ≠ j} g(xᵢ - xⱼ) + n ∑ᵢ V(xᵢ) - n²/2]`. -/
theorem tendsto_punctureTrunc_chartPot {n : ℕ} (X : Fin n → ℂ) (hX : Function.Injective X) :
    Tendsto (punctureTrunc Set.univ (Finset.univ.image X) (chartPot X)) (𝓝[>] 0)
      (𝓝 (splittingValue X)) := by
  obtain ⟨ρ, hρ, hsep⟩ := exists_separation (Finset.univ.image X)
  have heq : ∀ᶠ η in 𝓝[>] (0 : ℝ), punctureTrunc Set.univ (Finset.univ.image X) (chartPot X) η =
      -(1 / 2) * ∑ i, (circleTerm (chartPot X) (X i) η - 2 * Real.pi * Real.log η) -
        (1 / 2) * ∫ x in Omega (Finset.univ.image X) η, chartPot X x * chartLap n x := by
    filter_upwards [Ioc_mem_nhdsGT hρ] with η hη
    rw [punctureTrunc_univ_eq, Finset.card_image_of_injective _ hX, Finset.card_univ,
      Fintype.card_fin]
    have hg := green_plane_exterior X hρ hsep hη.1 hη.2
    rw [integral_add (integrableOn_gradSq_chartPot X hη.1) (integrableOn_chartPot_lap X _),
      Finset.sum_image (fun a _ b _ h => hX h)] at hg
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    linarith
  have hT1 := tendsto_finsetSum (Finset.univ : Finset (Fin n))
    (fun i _ => tendsto_circleTerm_chartPot X hX i)
  have hT2 := tendsto_integral_Omega_lap X
  have hlim := ((hT1.const_mul (-(1 / 2 : ℝ))).sub (hT2.const_mul (1 / 2 : ℝ)))
  have hval : -(1 / 2 : ℝ) * ∑ c, -(2 * Real.pi) * chartSmooth X c (X c) -
      1 / 2 * ∫ x, chartPot X x * chartLap n x = splittingValue X := by
    unfold splittingValue
    rw [integral_chartPot_lap]
    simp only [chartSmooth_apply]
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [hval] at hlim
  exact hlim.congr' (heq.mono fun η h => h.symm)

/-- **Proposition 3.4, first identity.** -/
theorem punctureEnergy_chartPot {n : ℕ} (X : Fin n → ℂ) (hX : Function.Injective X) :
    punctureEnergy Set.univ (Finset.univ.image X) (chartPot X) = splittingValue X :=
  (tendsto_punctureTrunc_chartPot X hX).limUnder_eq

/-- The chart potential is admissible on `(ℂ, X)` (Definition 3.3). -/
theorem chartPot_admissible {n : ℕ} (X : Fin n → ℂ) (hX : Function.Injective X) :
    PunctureAdmissible Set.univ (Finset.univ.image X) (chartPot X) where
  isOpen := isOpen_univ
  subset := Set.subset_univ _
  c2 x _ hx := (contDiffAt_chartPot X fun i h => hx (by simp [h])).of_le (by norm_cast)
  local_form p hp := by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨chartSmooth X i, contDiffAt_chartSmooth X hX i,
      Filter.Eventually.of_forall fun x => chartPot_eq_smooth_sub_log X i x⟩
  finite_energy ε hε := by
    have h := integrableOn_gradSq_chartPot X hε
    rw [← univ_sdiff_iUnion_ball] at h
    exact h.congr_fun (fun x _ => (norm_gradient_sq _ x).symm)
      (MeasurableSet.univ.diff (Finset.measurableSet_biUnion _ fun p _ => measurableSet_ball))

theorem sum_erase_eq {n : ℕ} (f : Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f j = ((n : ℝ) - 1) * ∑ j, f j := by
  have : ∀ i : Fin n, ∑ j ∈ Finset.univ.erase i, f j = ∑ j, f j - f i := fun i =>
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

theorem log_lam (x : ℂ) : Real.log (lam x) = Real.log 2 - potV x := by
  unfold lam potV
  rw [Real.log_div (by norm_num) (by positivity)]

theorem neg_log_norm_stereo_sub {x y : ℂ} (h : x ≠ y) :
    -Real.log ‖stereo x - stereo y‖ =
      gKer (x - y) - Real.log (lam x) / 2 - Real.log (lam y) / 2 := by
  have hxy : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 h)
  have hl := lam_pos x
  have hl' := lam_pos y
  rw [norm_stereo_sub, Real.log_mul (by positivity) hxy.ne', Real.log_sqrt (by positivity),
    Real.log_mul hl.ne' hl'.ne']
  unfold gKer
  ring

/-- **Proposition 3.4, second identity**, in terms of the value of the puncture energy. -/
theorem sphereEnergy_stereo_eq {n : ℕ} (X : Fin n → ℂ) (hX : Function.Injective X) :
    sphereEnergy (fun i => stereo (X i)) =
      (1 / 2 - Real.log 2) * (n : ℝ) ^ 2 +
        (1 / Real.pi) * (splittingValue X + Real.pi * ∑ i, Real.log (lam (X i))) := by
  have hpi := Real.pi_pos
  have h1 : sphereEnergy (fun i => stereo (X i)) =
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        (gKer (X i - X j) - Real.log (lam (X i)) / 2 - Real.log (lam (X j)) / 2) := by
    unfold sphereEnergy
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    exact neg_log_norm_stereo_sub fun h => (Finset.ne_of_mem_erase hj) (hX h).symm
  rw [h1]
  simp only [Finset.sum_sub_distrib]
  rw [sum_erase_eq (fun j => Real.log (lam (X j)) / 2)]
  have h2 : ∑ i, ∑ j ∈ Finset.univ.erase i, Real.log (lam (X i)) / 2 =
      ((n : ℝ) - 1) * ∑ i, Real.log (lam (X i)) / 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (Fin.pos i)]
    simp
  rw [h2]
  have hsplit : splittingValue X = Real.pi * (∑ i, ∑ j ∈ Finset.univ.erase i, gKer (X i - X j) +
      (n : ℝ) * ∑ i, potV (X i) - (n : ℝ) ^ 2 / 2) := rfl
  rw [hsplit]
  simp only [log_lam, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_div]
  field_simp
  ring

/-- **Proposition 3.4.** For pairwise distinct `X ∈ ℂⁿ`, with `W_ℂ(h_X)` the puncture energy,
`W_ℂ(h_X) = π [∑_{i ≠ j} g(xᵢ - xⱼ) + n ∑ᵢ V(xᵢ) - n²/2]` and
`E(T X) = (½ - log 2) n² + (1/π) [W_ℂ(h_X) + π ∑ᵢ log λ(xᵢ)]`. -/
theorem splitting_identity {n : ℕ} (X : Fin n → ℂ) (hX : Function.Injective X) :
    punctureEnergy Set.univ (Finset.univ.image X) (chartPot X) =
        Real.pi * (∑ i, ∑ j ∈ Finset.univ.erase i, gKer (X i - X j) +
          (n : ℝ) * ∑ i, potV (X i) - (n : ℝ) ^ 2 / 2) ∧
      sphereEnergy (fun i => stereo (X i)) =
        (1 / 2 - Real.log 2) * (n : ℝ) ^ 2 +
          (1 / Real.pi) * (punctureEnergy Set.univ (Finset.univ.image X) (chartPot X) +
            Real.pi * ∑ i, Real.log (lam (X i))) := by
  refine ⟨punctureEnergy_chartPot X hX, ?_⟩
  rw [punctureEnergy_chartPot X hX]
  exact sphereEnergy_stereo_eq X hX

end Sphere

end SandierSerfaty

end
