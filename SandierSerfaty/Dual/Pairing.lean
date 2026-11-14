/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.PairingBump
public import SandierSerfaty.Dual.PairingLocal
public import SandierSerfaty.Torus.PotentialLocal
public import SandierSerfaty.Torus.Green

/-!
# The pairing identity on the torus

**Theorem** (`pairing_identity`). Let `Γ` be a lattice of covolume `N`, `a : Fin N → ℂ` with distinct
classes, `u = greenSum Γ a` (the mean-zero torus potential off the charges), and `w` a Lipschitz
`Γ`-periodic function. Then `∇w · ∇u` is integrable over the cell and
```
∫_D ⟨∇w, ∇u⟩ = 2π ∑ᵢ w(aᵢ) − 2π ∫_D w.
```
This is the Green identity of the dual identity (paper proof of `dual:identity`) for the piecewise-`C¹` function
`h − H`, with the Lipschitz regularity of the gluing lemma replacing smoothness: it is proved by the
divergence theorem for the periodic Lipschitz field `w φ_ε ∇u`, `φ_ε = 1 − Bper ε`, and the limit
`ε ↓ 0` (`cell_pairing_cutoff`, `local_pairing_estimate`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Dual

open Analysis Torus

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ} {a : Fin N → ℂ} {ε : ℝ}

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem Bper_nonneg (x : ℂ) : 0 ≤ Bper Γ ε a x := by
  unfold Bper periodize Bsum
  exact tsum_nonneg fun γ => Finset.sum_nonneg fun i _ => cutBump_nonneg

omit [DiscreteTopology ↥Γ] [IsZLattice ℝ Γ] in
theorem Bper_le_one (hε : 0 < ε) (hsep : ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ε ≤ ‖q - a i‖)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) (x : ℂ) : Bper Γ ε a x ≤ 1 := by
  classical
  by_cases hex : ∃ (γ : Γ) (i : Fin N), cutBump ε (a i) ((γ : ℂ) + x) ≠ 0
  · obtain ⟨γ₀, i₀, h0⟩ := hex
    have hlt₀ : ‖(γ₀ : ℂ) + x - a i₀‖ < 2 * ε := by
      by_contra h; exact h0 (cutBump_eq_zero hε (not_lt.1 h))
    have hvan : ∀ (γ : Γ) (i : Fin N), (γ ≠ γ₀ ∨ i ≠ i₀) → cutBump ε (a i) ((γ : ℂ) + x) = 0 := by
      intro γ i hne
      by_contra hnz
      have hlt : ‖(γ : ℂ) + x - a i‖ < 2 * ε := by
        by_contra h; exact hnz (cutBump_eq_zero hε (not_lt.1 h))
      have hP : a i + ((γ₀ : ℂ) - γ) ∈ chargeSet Γ a :=
        ⟨i, by simpa using Γ.sub_mem γ₀.2 γ.2⟩
      have hclose : ‖a i + ((γ₀ : ℂ) - γ) - a i₀‖ < 4 * ε := by
        have : a i + ((γ₀ : ℂ) - γ) - a i₀ = ((γ₀ : ℂ) + x - a i₀) - ((γ : ℂ) + x - a i) := by ring
        rw [this]
        calc _ ≤ ‖(γ₀ : ℂ) + x - a i₀‖ + ‖(γ : ℂ) + x - a i‖ := norm_sub_le _ _
          _ < 2 * ε + 2 * ε := add_lt_add hlt₀ hlt
          _ = 4 * ε := by ring
      have heq : a i + ((γ₀ : ℂ) - γ) = a i₀ := by
        by_contra hne'
        have := hsep i₀ _ hP hne'
        linarith
      have hmem : a i - a i₀ ∈ Γ := by
        have : a i - a i₀ = (γ : ℂ) - γ₀ := by linear_combination heq
        rw [this]; exact Γ.sub_mem γ.2 γ₀.2
      have hii : i = i₀ := ha i i₀ hmem
      subst hii
      have hγ : (γ : ℂ) = γ₀ := by linear_combination -heq
      rcases hne with h | h
      · exact h (Subtype.ext hγ)
      · exact h rfl
    unfold Bper periodize Bsum
    rw [tsum_eq_single γ₀]
    · rw [Finset.sum_eq_single i₀]
      · exact cutBump_le_one
      · intro i _ hi; exact hvan γ₀ i (Or.inr hi)
      · intro h; exact absurd (Finset.mem_univ i₀) h
    · intro γ hγ
      exact Finset.sum_eq_zero fun i _ => hvan γ i (Or.inl hγ)
  · push Not at hex
    have : Bper Γ ε a x = 0 := by
      unfold Bper periodize Bsum
      simp [hex]
    rw [this]; exact zero_le_one

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem Bper_eq_zero_of_far (hε : 0 < ε) {x : ℂ} (hx : ∀ q ∈ chargeSet Γ a, 2 * ε ≤ ‖x - q‖) :
    Bper Γ ε a x = 0 := by
  unfold Bper periodize Bsum
  have : ∀ (γ : Γ) (i : Fin N), cutBump ε (a i) ((γ : ℂ) + x) = 0 := by
    intro γ i
    refine cutBump_eq_zero hε ?_
    have hq : a i - γ ∈ chargeSet Γ a := ⟨i, by simp⟩
    have := hx _ hq
    have e : (γ : ℂ) + x - a i = x - (a i - γ) := by ring
    rw [e]; exact this
  simp [this]

omit [IsZLattice ℝ Γ] in
theorem eventually_Bper_eq_zero {x : ℂ} (hx : x ∉ chargeSet Γ a) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Bper Γ ε a x = 0 := by
  by_cases hne : (chargeSet Γ a).Nonempty
  · have hpos : 0 < infDist x (chargeSet Γ a) :=
      ((isClosed_chargeSet Γ a).notMem_iff_infDist_pos hne).1 hx
    filter_upwards [Ioo_mem_nhdsGT (half_pos hpos), self_mem_nhdsWithin] with ε hε hε0
    refine Bper_eq_zero_of_far hε0 fun q hq => ?_
    have := infDist_le_dist_of_mem (x := x) hq
    rw [dist_eq_norm] at this
    linarith [hε.2]
  · filter_upwards [self_mem_nhdsWithin] with ε hε0
    exact Bper_eq_zero_of_far hε0 fun q hq => absurd ⟨q, hq⟩ hne

theorem abs_fderiv_one_le (f : ℂ → ℝ) (x : ℂ) : |fderiv ℝ f x 1| ≤ ‖fderiv ℝ f x‖ := by
  have := (fderiv ℝ f x).le_opNorm 1
  simpa using this

theorem abs_fderiv_I_le (f : ℂ → ℝ) (x : ℂ) : |fderiv ℝ f x Complex.I| ≤ ‖fderiv ℝ f x‖ := by
  have := (fderiv ℝ f x).le_opNorm Complex.I
  simpa using this

open scoped Classical in
theorem integrableOn_norm_fderiv_greenSum (hΓ : ZLattice.covolume Γ = N)
    (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    IntegrableOn (fun x => ‖fderiv ℝ (greenSum Γ a) x‖) (torusDomain Γ) := by
  have hP := isTorusPotential_greenSum hΓ ha
  have hloc := hP.locallyIntegrable_gradient
  have hloc' : LocallyIntegrable (fun x => ‖fderiv ℝ (greenSum Γ a) x‖) volume := by
    refine hloc.mono ((measurable_fderiv ℝ (greenSum Γ a)).norm.aestronglyMeasurable) ?_
    filter_upwards [(countable_chargeSet Γ a).ae_notMem volume] with x hx
    have hev : (fun y => if y ∈ chargeSet Γ a then (0 : ℝ) else greenSum Γ a y) =ᶠ[𝓝 x]
        greenSum Γ a := by
      filter_upwards [(isClosed_chargeSet Γ a).isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ chargeSet Γ a := hy
      simp [hy']
    have : gradient (fun y => if y ∈ chargeSet Γ a then (0 : ℝ) else greenSum Γ a y) x =
        gradient (greenSum Γ a) x := by
      simp only [gradient, hev.fderiv_eq]
    rw [this, norm_norm, norm_gradient_eq]
  refine integrableOn_torusDomain_of_locallyIntegrable Γ hloc' fun γ hγ x => ?_
  rw [fderiv_periodic Γ (fun δ hδ y => greenSum_add_period hδ y) hγ]

theorem fderiv_Bsum_apply (hε : 0 < ε) (y v : ℂ) :
    fderiv ℝ (Bsum ε a) y v = ∑ i, fderiv ℝ (cutBump ε (a i)) y v := by
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin N)), DifferentiableAt ℝ (cutBump ε (a i)) y :=
    fun i _ => ((contDiff_cutBump hε).differentiable (by simp)) y
  have : Bsum ε a = fun y => ∑ i, cutBump ε (a i) y := rfl
  rw [this, fderiv_fun_sum hd]
  simp [sum_apply]

theorem gradDot_Bsum (hε : 0 < ε) (u : ℂ → ℝ) (y : ℂ) :
    gradDot (Bsum ε a) u y = ∑ i, gradDot (cutBump ε (a i)) u y := by
  simp only [gradDot, pd₁, pd₂, fderiv_Bsum_apply hε, Finset.sum_mul, Finset.sum_add_distrib]

/-- **Unfolding** of the periodized cut-off: the cell integral of `w ⟨∇B, ∇u⟩` is the sum over the
charges of the plane integrals of `w ⟨∇β_i, ∇u⟩`. -/
theorem integral_cell_w_gradDot_Bper (_hΓ : ZLattice.covolume Γ = N) (hε : 0 < ε) {w : ℂ → ℝ}
    (hwper : ∀ γ ∈ Γ, ∀ x, w (x + γ) = w x)
    (hint : ∀ i, Integrable (fun x => w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x) volume) :
    ∫ x in torusDomain Γ, w x * gradDot (Bper Γ ε a) (greenSum Γ a) x =
      ∑ i, ∫ x, w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x := by
  set u := greenSum Γ a with hu
  set g : ℂ → ℝ := fun y => w y * gradDot (Bsum ε a) u y with hg
  have hgsum : ∀ y, g y = ∑ i, w y * gradDot (cutBump ε (a i)) u y := fun y => by
    simp only [hg, gradDot_Bsum hε, Finset.mul_sum]
  have hgint : Integrable g volume := by
    have : g = fun y => ∑ i, w y * gradDot (cutBump ε (a i)) u y := funext hgsum
    rw [this]
    exact integrable_finsetSum _ fun i _ => hint i
  have hsupp : ∀ y, (∑ i, ‖a i‖) + 2 * ε < ‖y - 0‖ → Bsum ε a y = 0 := fun y hy =>
    Bsum_eq_zero hε hy
  have hsum : ∀ x v : ℂ, Summable (fun γ : Γ => fderiv ℝ (Bsum ε a) ((γ : ℂ) + x) v) := by
    intro x v
    exact summable_translates (Γ := Γ) (f := fun y => fderiv ℝ (Bsum ε a) y v) (c := 0)
      (ρ := (∑ i, ‖a i‖) + 2 * ε) (fun y hy => fderiv_eq_zero_of_far hsupp hy v) x
  have hper_eq : ∀ x, w x * gradDot (Bper Γ ε a) u x = ∑' γ : Γ, g ((γ : ℂ) + x) := by
    intro x
    have hpu : ∀ (γ : Γ) (v : ℂ), fderiv ℝ u ((γ : ℂ) + x) v = fderiv ℝ u x v := fun γ v => by
      rw [add_comm, fderiv_periodic Γ (fun δ hδ y => greenSum_add_period hδ y) γ.2]
    have hwp : ∀ γ : Γ, w ((γ : ℂ) + x) = w x := fun γ => by
      rw [add_comm]; exact hwper γ γ.2 x
    have hterm : ∀ γ : Γ, g ((γ : ℂ) + x) = w x * (fderiv ℝ u x 1 * fderiv ℝ (Bsum ε a) ((γ : ℂ) + x) 1 +
        fderiv ℝ u x Complex.I * fderiv ℝ (Bsum ε a) ((γ : ℂ) + x) Complex.I) := fun γ => by
      simp only [hg, gradDot, pd₁, pd₂, hpu γ, hwp γ]; ring
    simp_rw [hterm]
    rw [tsum_mul_left, Summable.tsum_add ((hsum x 1).mul_left _) ((hsum x Complex.I).mul_left _),
      tsum_mul_left, tsum_mul_left]
    have e1 := fderiv_periodize (Γ := Γ) (contDiff_Bsum hε) hsupp x 1
    have e2 := fderiv_periodize (Γ := Γ) (contDiff_Bsum hε) hsupp x Complex.I
    have eB : Bper Γ ε a = periodize Γ (Bsum ε a) := rfl
    simp only [gradDot, pd₁, pd₂, eB, e1, e2]
    ring
  simp_rw [hper_eq]
  rw [integral_torusDomain_tsum Γ hgint]
  have : g = fun y => ∑ i, w y * gradDot (cutBump ε (a i)) u y := funext hgsum
  rw [this, integral_finsetSum _ fun i _ => hint i]

theorem exists_sep_cutoff (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {N : ℕ}
    (a : Fin N → ℂ) : ∃ ρ > 0, ∀ ε, 0 < ε → ε ≤ ρ →
      ∀ i, ∀ q ∈ chargeSet Γ a, q ≠ a i → 4 * ε ≤ ‖q - a i‖ := by
  obtain ⟨ρ, hρ, hsep⟩ := exists_sep Γ a
  exact ⟨ρ, hρ, fun ε _ hερ i q hq hne => (by linarith : 4 * ε ≤ 4 * ρ).trans (hsep i q hq hne)⟩

/-- **Dominated convergence for the cut-off:** `∫_D (1 - Bper ε) f → ∫_D f` for integrable `f`. -/
theorem tendsto_integral_one_sub_Bper_mul (ha : ∀ i j, a i - a j ∈ Γ → i = j) {f : ℂ → ℝ}
    (hf : IntegrableOn f (torusDomain Γ)) :
    Tendsto (fun ε : ℝ => ∫ x in torusDomain Γ, (1 - Bper Γ ε a x) * f x) (𝓝[>] 0)
      (𝓝 (∫ x in torusDomain Γ, f x)) := by
  obtain ⟨ρ, hρ, hsep⟩ := exists_sep_cutoff Γ a
  refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (torusDomain Γ))
    (fun x => ‖f x‖) ?_ ?_ hf.norm ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hc : Continuous (Bper Γ ε a) := (contDiff_Bper (Γ := Γ) hε).continuous
    exact ((continuous_const.sub hc).aestronglyMeasurable).mul hf.1
  · filter_upwards [Ioc_mem_nhdsGT hρ, self_mem_nhdsWithin] with ε hε hε0
    refine Eventually.of_forall fun x => ?_
    have h0 := Bper_nonneg (Γ := Γ) (ε := ε) (a := a) x
    have h1 := Bper_le_one hε0 (hsep ε hε0 hε.2) ha x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - Bper Γ ε a x)]
    have : 1 - Bper Γ ε a x ≤ 1 := by linarith
    calc (1 - Bper Γ ε a x) * ‖f x‖ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖f x‖ := one_mul _
  · filter_upwards [ae_restrict_of_ae ((countable_chargeSet Γ a).ae_notMem volume)] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_Bper_eq_zero (Γ := Γ) (a := a) hx] with ε hε
    simp [hε]

theorem gradDot_one_sub (B u : ℂ → ℝ) {x : ℂ} (_hB : DifferentiableAt ℝ B x) :
    gradDot (fun y => 1 - B y) u x = -gradDot B u x := by
  have e : ∀ v, fderiv ℝ (fun y => 1 - B y) x v = -fderiv ℝ B x v := fun v => by
    rw [fderiv_const_sub]; rfl
  simp only [gradDot, pd₁, pd₂, e]; ring

/-- The plane integral of the local pairing converges: the cell integral of `w ⟨∇B_ε, ∇u⟩`. -/
theorem exists_pairing_bound (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    {w : ℂ → ℝ} {K : NNReal} (hw : LipschitzWith K w) (hwper : ∀ γ ∈ Γ, ∀ x, w (x + γ) = w x) :
    ∃ (C ε₁ : ℝ), 0 < ε₁ ∧ ∀ ε ∈ Ioc 0 ε₁,
      |(∫ x in torusDomain Γ, w x * gradDot (Bper Γ ε a) (greenSum Γ a) x) -
        2 * Real.pi * ∑ i, w (a i)| ≤ C * ε := by
  classical
  obtain ⟨L, hL0, hL⟩ := exists_lipschitzWith_cutBump
  obtain ⟨Mw, hMw⟩ := Torus.exists_bound_of_periodic Γ hw.continuous hwper
  have hP := isTorusPotential_greenSum hΓ ha
  have hloc : ∀ i, ∃ r > 0, ∃ v : ℂ → ℝ, ContDiffOn ℝ ∞ v (ball (a i) r) ∧
      ∀ x ∈ ball (a i) r, x ≠ a i → fderiv ℝ (greenSum Γ a) x =
        fderiv ℝ v x - (‖x - a i‖ ^ 2)⁻¹ • innerSL ℝ (x - a i) := by
    intro i
    obtain ⟨r, hr, v, hv, -, hvloc⟩ := hP.exists_local_form (p := a i) ⟨i, by simp⟩
    refine ⟨r, hr, v, hv, fun x hx hxp => ?_⟩
    obtain ⟨hxn, hxeq⟩ := hvloc x hx hxp
    have hloc' : ∀ y ∈ ball (a i) r, y ≠ a i → greenSum Γ a y = v y - Real.log ‖y - a i‖ := by
      intro y hy hyp
      obtain ⟨hyn, hyeq⟩ := hvloc y hy hyp
      simpa [hyn] using hyeq
    exact Torus.fderiv_eq_of_eq_sub_log hv hloc' hx hxp
  choose r hr v hv hu using hloc
  obtain ⟨C, hC⟩ : ∃ C : Fin N → ℝ, ∀ i, ∀ ε ∈ Ioc 0 (r i / 4),
      Integrable (fun x => w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x) ∧
      |(∫ x, w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x) - 2 * Real.pi * w (a i)| ≤
        C i * ε := by
    have := fun i => local_pairing_estimate (c := a i) hL0 hL hw hMw (hr i) (hv i) (hu i)
    choose C hC using this
    exact ⟨C, hC⟩
  obtain ⟨ρ, hρ, hsep⟩ := exists_sep_cutoff Γ a
  obtain ⟨r₀, hr₀, hr₀le⟩ : ∃ r₀ > 0, ∀ i, r₀ ≤ r i := by
    have : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, t < r i :=
      eventually_all.2 fun i => (eventually_lt_nhds (hr i)).filter_mono nhdsWithin_le_nhds
    obtain ⟨t, ht, ht0⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨t, ht0, fun i => (ht i).le⟩
  refine ⟨∑ i, C i, min ρ (r₀ / 4), lt_min hρ (by positivity), fun ε hε => ?_⟩
  obtain ⟨hε0, hε1⟩ := hε
  have hεr : ∀ i, ε ∈ Ioc 0 (r i / 4) := fun i =>
    ⟨hε0, hε1.trans ((min_le_right _ _).trans (by linarith [hr₀le i]))⟩
  have hint : ∀ i, Integrable (fun x => w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x) volume :=
    fun i => (hC i ε (hεr i)).1
  rw [integral_cell_w_gradDot_Bper hΓ hε0 hwper hint]
  have : (∑ i, ∫ x, w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x) - 2 * Real.pi * ∑ i, w (a i) =
      ∑ i, ((∫ x, w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x) - 2 * Real.pi * w (a i)) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [this]
  calc _ ≤ ∑ i, |(∫ x, w x * gradDot (cutBump ε (a i)) (greenSum Γ a) x) - 2 * Real.pi * w (a i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C i * ε := Finset.sum_le_sum fun i _ => (hC i ε (hεr i)).2
    _ = (∑ i, C i) * ε := by rw [Finset.sum_mul]

/-- **The pairing identity** (paper proof of `dual:identity`, with a Lipschitz test function):
`∫_D ⟨∇w, ∇u⟩ = 2π ∑ᵢ w(aᵢ) − 2π ∫_D w`. -/
theorem pairing_identity (hΓ : ZLattice.covolume Γ = N) (ha : ∀ i j, a i - a j ∈ Γ → i = j)
    {w : ℂ → ℝ} {K : NNReal} (hw : LipschitzWith K w) (hwper : ∀ γ ∈ Γ, ∀ x, w (x + γ) = w x) :
    IntegrableOn (fun x => gradDot w (greenSum Γ a) x) (torusDomain Γ) ∧
      ∫ x in torusDomain Γ, gradDot w (greenSum Γ a) x =
        2 * Real.pi * ∑ i, w (a i) - 2 * Real.pi * ∫ x in torusDomain Γ, w x := by
  set u := greenSum Γ a with hu
  set D := torusDomain Γ with hD
  obtain ⟨C, ε₁, hε₁, hCε⟩ := exists_pairing_bound hΓ ha hw hwper
  obtain ⟨ρ, hρ, hsep⟩ := exists_sep_cutoff Γ a
  obtain ⟨Mw, hMw⟩ := Torus.exists_bound_of_periodic Γ hw.continuous hwper
  -- integrability of the gradient pairing
  have hnorm := integrableOn_norm_fderiv_greenSum hΓ ha
  have hgint : IntegrableOn (fun x => gradDot w u x) D := by
    refine Integrable.mono' (hnorm.const_mul (2 * K)) ?_ ?_
    · have : Measurable fun x => gradDot w u x := by
        simp only [gradDot, pd₁, pd₂]
        exact ((measurable_fderiv_apply_const ℝ w 1).mul (measurable_fderiv_apply_const ℝ u 1)).add
          ((measurable_fderiv_apply_const ℝ w Complex.I).mul (measurable_fderiv_apply_const ℝ u Complex.I))
      exact this.aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      have hK : ‖fderiv ℝ w x‖ ≤ K := norm_fderiv_le_of_lipschitz ℝ hw
      simp only [gradDot, pd₁, pd₂, Real.norm_eq_abs]
      calc |fderiv ℝ w x 1 * fderiv ℝ u x 1 + fderiv ℝ w x Complex.I * fderiv ℝ u x Complex.I|
          ≤ |fderiv ℝ w x 1| * |fderiv ℝ u x 1| + |fderiv ℝ w x Complex.I| * |fderiv ℝ u x Complex.I| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]
        _ ≤ K * ‖fderiv ℝ u x‖ + K * ‖fderiv ℝ u x‖ := by
            gcongr
            · exact (abs_fderiv_one_le w x).trans hK
            · exact abs_fderiv_one_le u x
            · exact (abs_fderiv_I_le w x).trans hK
            · exact abs_fderiv_I_le u x
        _ = 2 * K * ‖fderiv ℝ u x‖ := by ring
  refine ⟨hgint, ?_⟩
  have hwint : IntegrableOn w D := Torus.integrableOn_torusDomain_of_periodic Γ hw.continuous hwper
  -- limits of the three terms
  have hL1 := tendsto_integral_one_sub_Bper_mul (Γ := Γ) (a := a) ha hgint
  have hL2 := (tendsto_integral_one_sub_Bper_mul (Γ := Γ) (a := a) ha hwint).const_mul (2 * Real.pi)
  have hM : Tendsto (fun ε : ℝ => ∫ x in D, w x * gradDot (Bper Γ ε a) u x) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * ∑ i, w (a i))) := by
    have h0 : Tendsto (fun ε : ℝ => (∫ x in D, w x * gradDot (Bper Γ ε a) u x) -
        2 * Real.pi * ∑ i, w (a i)) (𝓝[>] 0) (𝓝 0) := by
      have hCt : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
        have hC : Continuous fun ε : ℝ => C * ε := by fun_prop
        have := (hC.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
        simpa using this
      refine squeeze_zero_norm' ?_ hCt
      filter_upwards [Ioc_mem_nhdsGT hε₁] with ε hε
      rw [Real.norm_eq_abs]; exact hCε ε ⟨hε.1, hε.2⟩
    exact tendsto_sub_nhds_zero_iff.1 h0
  -- the cell identity at each scale
  have hid : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ x in D, (1 - Bper Γ ε a x) * gradDot w u x) -
        (∫ x in D, w x * gradDot (Bper Γ ε a) u x) +
        2 * Real.pi * ∫ x in D, (1 - Bper Γ ε a x) * w x = 0 := by
    filter_upwards [Ioc_mem_nhdsGT (lt_min hρ hε₁), self_mem_nhdsWithin] with ε hε hε0
    set B := Bper Γ ε a with hB
    have hsep' := hsep ε hε0 (hε.2.trans (min_le_left _ _))
    have hcut := cutOff_Bper (Γ := Γ) hε0 hsep' ha
    obtain ⟨hTint, hT0⟩ := cell_pairing_cutoff hΓ hcut hw hwper
    have hBc : Continuous B := (contDiff_Bper (Γ := Γ) hε0).continuous
    have hB0 := Bper_nonneg (Γ := Γ) (ε := ε) (a := a)
    have hB1 := Bper_le_one hε0 hsep' ha
    have hT1 : IntegrableOn (fun x => (1 - B x) * gradDot w u x) D := by
      refine Integrable.mono' hgint.norm ((continuous_const.sub hBc).aestronglyMeasurable.mul hgint.1) ?_
      refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hB1 x] : 0 ≤ 1 - B x)]
      calc (1 - B x) * ‖gradDot w u x‖ ≤ 1 * ‖gradDot w u x‖ :=
            mul_le_mul_of_nonneg_right (by linarith [hB0 x]) (norm_nonneg _)
        _ = _ := one_mul _
    have hP3 : IntegrableOn (fun x => (1 - B x) * w x) D := by
      refine Torus.integrableOn_torusDomain_of_periodic Γ ?_ fun γ hγ x => ?_
      · exact (continuous_const.sub hBc).mul hw.continuous
      · show (1 - Bper Γ ε a (x + γ)) * w (x + γ) = (1 - Bper Γ ε a x) * w x
        rw [hwper γ hγ, hcut.periodic γ hγ]
    have hT3 : IntegrableOn (fun x => 2 * Real.pi * ((1 - B x) * w x)) D := hP3.const_mul _
    have hT2 : IntegrableOn (fun x => w x * gradDot (fun y => 1 - B y) u x) D := by
      refine ((hTint.sub hT1).sub hT3).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]; ring
    have hsplit : ∫ x in D, ((1 - B x) * gradDot w u x + w x * gradDot (fun y => 1 - B y) u x +
        2 * Real.pi * ((1 - B x) * w x)) =
        (∫ x in D, (1 - B x) * gradDot w u x) +
        (∫ x in D, w x * gradDot (fun y => 1 - B y) u x) +
        ∫ x in D, 2 * Real.pi * ((1 - B x) * w x) := by
      have e2 : ∫ x in D, ((1 - B x) * gradDot w u x + w x * gradDot (fun y => 1 - B y) u x) =
          (∫ x in D, (1 - B x) * gradDot w u x) +
            ∫ x in D, w x * gradDot (fun y => 1 - B y) u x := integral_add hT1 hT2
      have e1 := integral_add (μ := volume.restrict D)
        (f := fun x => (1 - B x) * gradDot w u x + w x * gradDot (fun y => 1 - B y) u x)
        (g := fun x => 2 * Real.pi * ((1 - B x) * w x))
        (show Integrable (fun x => (1 - B x) * gradDot w u x +
          w x * gradDot (fun y => 1 - B y) u x) (volume.restrict D) from Integrable.add hT1 hT2) hT3
      rw [e1, e2]
    have hT2eq : ∫ x in D, w x * gradDot (fun y => 1 - B y) u x =
        -∫ x in D, w x * gradDot B u x := by
      rw [← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have hBd : DifferentiableAt ℝ B x :=
        (((contDiff_Bper (Γ := Γ) hε0).of_le (by norm_cast)).differentiable one_ne_zero) x
      simp only [gradDot_one_sub B u hBd, mul_neg]
    have hT3eq : ∫ x in D, 2 * Real.pi * ((1 - B x) * w x) =
        2 * Real.pi * ∫ x in D, (1 - B x) * w x := integral_const_mul _ _
    rw [hsplit, hT2eq, hT3eq] at hT0
    linarith
  -- pass to the limit
  have hlim : Tendsto (fun ε : ℝ => (∫ x in D, (1 - Bper Γ ε a x) * gradDot w u x) -
        (∫ x in D, w x * gradDot (Bper Γ ε a) u x) +
        2 * Real.pi * ∫ x in D, (1 - Bper Γ ε a x) * w x) (𝓝[>] 0)
      (𝓝 ((∫ x in D, gradDot w u x) - 2 * Real.pi * ∑ i, w (a i) +
        2 * Real.pi * ∫ x in D, w x)) := (hL1.sub hM).add hL2
  have h0 : Tendsto (fun ε : ℝ => (∫ x in D, (1 - Bper Γ ε a x) * gradDot w u x) -
        (∫ x in D, w x * gradDot (Bper Γ ε a) u x) +
        2 * Real.pi * ∫ x in D, (1 - Bper Γ ε a x) * w x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hid.mono fun ε h => h.symm)
  have := tendsto_nhds_unique hlim h0
  linarith

end Dual

end SandierSerfaty

end
