/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.Weyl
public import SandierSerfaty.Analysis.RemovableCapacity

/-!
# Removable singularities for the Poisson equation in the plane

**Theorem** (`Weyl.removable_singularity`). Let `U ⊆ ℂ` be open, `c ∈ U`, `k : ℝ`, and `u : ℂ → ℝ` of
class `C²` on `U \ {c}` with `Δ u = k` there and bounded near `c`. Then there is `v` smooth on `U`,
equal to `u` on `U \ {c}`, with `Δ v = k` on `U`.

Proof. Subtract `k ‖x - c‖² / 4` (whose Laplacian is `k`), so that `k = 0`. A bounded harmonic function
`h` on the punctured set is weakly harmonic across `c` (`Weyl.isWeaklyHarmonicOn_of_bounded`): for a
test function `ψ`, split `ψ = ψ (1 - η) + ψ η` with the logarithmic cutoff `η` of
`SandierSerfaty.Analysis.RemovableCutoff`; Green's identity on `U \ {c}` kills `ψ (1 - η)`, and the
other term is `O(k)` by the capacity estimate (`SandierSerfaty.Analysis.RemovableCapacity`) and the
bound on `h`. Then Weyl's lemma (`SandierSerfaty.Analysis.Weyl`) applies.
-/

open MeasureTheory Laplacian InnerProductSpace Filter Topology Set Metric
open scoped ContDiff

public section

namespace SandierSerfaty.Weyl

/-- A function that is continuous off `c` and bounded near `c` is locally integrable on `U`. -/
theorem locallyIntegrableOn_of_bounded {U : Set ℂ} (hU : IsOpen U) {c : ℂ} (hc : c ∈ U)
    {h : ℂ → ℝ} (hcont : ContinuousOn h (U \ {c})) {M ρ : ℝ} (hρ : 0 < ρ)
    (hbd : ∀ x ∈ ball c ρ, x ≠ c → |h x| ≤ M) : LocallyIntegrableOn h U volume := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro K hKU hK
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.mp hU c hc
  set r : ℝ := min ρ r₀ with hr
  have hr0 : 0 < r := lt_min hρ hr₀
  have hBU : ball c r ⊆ U := (ball_subset_ball (min_le_right _ _)).trans hr₀U
  have hBρ : ball c r ⊆ ball c ρ := ball_subset_ball (min_le_left _ _)
  have hB : IntegrableOn h (ball c r) volume := by
    have hmeas : AEStronglyMeasurable h (volume.restrict (ball c r)) := by
      have h1 : AEStronglyMeasurable h (volume.restrict (ball c r \ {c})) :=
        (hcont.mono (fun x hx => ⟨hBU hx.1, hx.2⟩)).aestronglyMeasurable
          (measurableSet_ball.diff (measurableSet_singleton c))
      have h2 : volume.restrict (ball c r \ {c}) = volume.restrict (ball c r) :=
        Measure.restrict_congr_set (sdiff_null_ae_eq_self (by simp))
      rwa [h2] at h1
    have hae : ∀ᵐ x ∂(volume.restrict (ball c r)), ‖h x‖ ≤ M := by
      rw [ae_restrict_iff' measurableSet_ball]
      have hne : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ c := by rw [ae_iff]; simp
      filter_upwards [hne] with x hx hxb
      rw [Real.norm_eq_abs]
      exact hbd x (hBρ hxb) hx
    exact Integrable.mono' (integrableOn_const measure_ball_lt_top.ne) hmeas hae
  have hK1 : IsCompact (K \ ball c r) := hK.diff isOpen_ball
  have h1 : IntegrableOn h (K \ ball c r) volume :=
    (hcont.mono (fun x hx => ⟨hKU hx.1, fun hxc => hx.2 (by
      rw [Set.mem_singleton_iff] at hxc; rw [hxc]; exact mem_ball_self hr0)⟩)).integrableOn_compact hK1
  have h2 : IntegrableOn h (K ∩ ball c r) volume := hB.mono_set inter_subset_right
  have := h1.union h2
  rwa [sdiff_union_inter] at this

/-- The product of a locally integrable function with a continuous function vanishing off a compact
subset of `U` is integrable. -/
theorem integrable_mul_of_locallyIntegrableOn {U : Set ℂ} {h : ℂ → ℝ}
    (hloc : LocallyIntegrableOn h U volume) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ x ∉ K, g x = 0) :
    Integrable (fun x => h x * g x) volume := by
  have := (hloc.integrableOn_compact_subset hKU hK).mul_continuousOn hg.continuousOn hK
  exact this.integrable_of_forall_notMem_eq_zero (fun x hx => by simp [hg0 x hx])

theorem exists_test_bounds {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∃ Cψ Cg CΔ : ℝ, 0 ≤ Cψ ∧ 0 ≤ Cg ∧ 0 ≤ CΔ ∧ (∀ x, |ψ x| ≤ Cψ) ∧
      (∀ x, |pd 1 ψ x| ≤ Cg ∧ |pd Complex.I ψ x| ≤ Cg) ∧ ∀ x, |Δ ψ x| ≤ CΔ := by
  have hK : IsCompact (tsupport ψ) := hc
  have hψ0 : ∀ x ∉ tsupport ψ, ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hp : ∀ v : ℂ, Continuous (pd v ψ) ∧ HasCompactSupport (pd v ψ) := fun v =>
    ⟨(contDiff_pd (m := 0) hψ (by norm_num) v).continuous,
      HasCompactSupport.intro hK (pd_eq_zero_of_notMem hK hψ0 v)⟩
  have hL : Continuous (Δ ψ) := continuous_lap (hψ.of_le (by norm_num))
  have hLc : HasCompactSupport (Δ ψ) :=
    HasCompactSupport.intro hK fun x hx => lap_eq_zero_of_notMem_tsupport hx
  obtain ⟨C0, hC0⟩ := hc.exists_bound_of_continuous hψ.continuous
  obtain ⟨C1, hC1⟩ := (hp 1).2.exists_bound_of_continuous (hp 1).1
  obtain ⟨C2, hC2⟩ := (hp Complex.I).2.exists_bound_of_continuous (hp Complex.I).1
  obtain ⟨C3, hC3⟩ := hLc.exists_bound_of_continuous hL
  refine ⟨max C0 0, max (max C1 C2) 0, max C3 0, le_max_right _ _, le_max_right _ _,
    le_max_right _ _, fun x => ?_, fun x => ⟨?_, ?_⟩, fun x => ?_⟩
  · have := hC0 x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have := hC1 x
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left C1 C2).trans (le_max_left _ _))
  · have := hC2 x
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right C1 C2).trans (le_max_left _ _))
  · have := hC3 x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

theorem lap_mul_eta_eq_zero {ψ : ℂ → ℝ} {k : ℝ} (hk : 0 < k) {c z : ℂ}
    (hz : Real.exp (-1 / (2 * k)) < ‖z - c‖) : Δ (fun y => ψ y * eta k c y) z = 0 := by
  apply lap_eq_zero_of_notMem_tsupport
  intro hmem
  have : tsupport (fun y => ψ y * eta k c y) ⊆ closedBall c (Real.exp (-1 / (2 * k))) := by
    refine closure_minimal (fun y hy => ?_) isClosed_closedBall
    by_contra hy'
    apply hy
    have : Real.exp (-1 / (2 * k)) ≤ ‖y - c‖ := by
      rw [mem_closedBall, dist_eq_norm, not_le] at hy'; exact hy'.le
    simp [eta_eq_zero hk this]
  have := this hmem
  rw [mem_closedBall, dist_eq_norm] at this
  linarith

theorem abs_lap_mul_eta_le {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {k : ℝ} (hk : 0 < k) {A B : ℝ}
    (hA : ∀ t, |deriv theta t| ≤ A) (hB : ∀ t, |deriv (deriv theta) t| ≤ B)
    {Cψ Cg CΔ : ℝ} (hψb : ∀ x, |ψ x| ≤ Cψ)
    (hgb : ∀ x, |pd 1 ψ x| ≤ Cg ∧ |pd Complex.I ψ x| ≤ Cg) (hLb : ∀ x, |Δ ψ x| ≤ CΔ)
    (c : ℂ) {z : ℂ} (hz : z ≠ c) :
    |Δ (fun y => ψ y * eta k c y) z| ≤
      (closedBall c k).indicator (fun _ => CΔ) z + (4 * B * Cψ + 8 * A * Cg) * Lam k ‖z - c‖ := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hCψ : 0 ≤ Cψ := (abs_nonneg _).trans (hψb 0)
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hgb 0).1
  have hCΔ : 0 ≤ CΔ := (abs_nonneg _).trans (hLb 0)
  have hLam := Lam_nonneg k ‖z - c‖
  by_cases hfar : Real.exp (-1 / (2 * k)) < ‖z - c‖
  · rw [lap_mul_eta_eq_zero hk hfar, abs_zero]
    have : 0 ≤ (closedBall c k).indicator (fun _ => CΔ) z :=
      Set.indicator_nonneg (fun _ _ => hCΔ) z
    have h2 : 0 ≤ (4 * B * Cψ + 8 * A * Cg) * Lam k ‖z - c‖ := by positivity
    linarith
  · have hzk : z ∈ closedBall c k := by
      rw [mem_closedBall, dist_eq_norm]
      exact (not_lt.mp hfar).trans (exp_neg_inv_le hk)
    rw [Set.indicator_of_mem hzk]
    have hη : ContDiff ℝ ∞ (eta k c) := contDiff_eta hk c
    rw [lap_mul (hψ.contDiffAt.of_le (by norm_num)) (hη.contDiffAt.of_le (by norm_num))]
    have e1 := abs_lap_eta_le hk hB hz
    have e2 := abs_pd_eta_le hk hA (c := c) hz (v := 1) (by simp)
    have e3 := abs_pd_eta_le hk hA (c := c) hz (v := Complex.I) (by simp)
    have hη0 : 0 ≤ eta k c z := Theta_nonneg _ _
    have hη1 : eta k c z ≤ 1 := Theta_le_one _ _
    have t1 : |Δ ψ z * eta k c z| ≤ CΔ := by
      rw [abs_mul, abs_of_nonneg hη0]
      calc |Δ ψ z| * eta k c z ≤ CΔ * 1 := by
            exact mul_le_mul (hLb z) hη1 hη0 hCΔ
        _ = CΔ := mul_one _
    have t2 : |ψ z * Δ (eta k c) z| ≤ Cψ * (4 * B * Lam k ‖z - c‖) := by
      rw [abs_mul]; exact mul_le_mul (hψb z) e1 (abs_nonneg _) hCψ
    have t3 : |pd 1 ψ z * pd 1 (eta k c) z| ≤ Cg * (2 * A * Lam k ‖z - c‖) := by
      rw [abs_mul]; exact mul_le_mul (hgb z).1 e2 (abs_nonneg _) hCg
    have t4 : |pd Complex.I ψ z * pd Complex.I (eta k c) z| ≤ Cg * (2 * A * Lam k ‖z - c‖) := by
      rw [abs_mul]; exact mul_le_mul (hgb z).2 e3 (abs_nonneg _) hCg
    calc |Δ ψ z * eta k c z + ψ z * Δ (eta k c) z +
          2 * (pd 1 ψ z * pd 1 (eta k c) z + pd Complex.I ψ z * pd Complex.I (eta k c) z)|
        ≤ |Δ ψ z * eta k c z| + |ψ z * Δ (eta k c) z| +
          |2 * (pd 1 ψ z * pd 1 (eta k c) z + pd Complex.I ψ z * pd Complex.I (eta k c) z)| := by
          have s1 := abs_add_le (Δ ψ z * eta k c z + ψ z * Δ (eta k c) z)
            (2 * (pd 1 ψ z * pd 1 (eta k c) z + pd Complex.I ψ z * pd Complex.I (eta k c) z))
          have s2 := abs_add_le (Δ ψ z * eta k c z) (ψ z * Δ (eta k c) z)
          linarith
      _ ≤ CΔ + Cψ * (4 * B * Lam k ‖z - c‖) +
          2 * (Cg * (2 * A * Lam k ‖z - c‖) + Cg * (2 * A * Lam k ‖z - c‖)) := by
          have : |2 * (pd 1 ψ z * pd 1 (eta k c) z + pd Complex.I ψ z * pd Complex.I (eta k c) z)|
              ≤ 2 * (Cg * (2 * A * Lam k ‖z - c‖) + Cg * (2 * A * Lam k ‖z - c‖)) := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            have := (abs_add_le (pd 1 ψ z * pd 1 (eta k c) z)
              (pd Complex.I ψ z * pd Complex.I (eta k c) z)).trans (add_le_add t3 t4)
            linarith
          linarith
      _ = CΔ + (4 * B * Cψ + 8 * A * Cg) * Lam k ‖z - c‖ := by ring

/-- **A bounded harmonic function on the punctured set is weakly harmonic across the puncture.** -/
theorem isWeaklyHarmonicOn_of_bounded {U : Set ℂ} (hU : IsOpen U) {c : ℂ} (hc : c ∈ U)
    {h : ℂ → ℝ} (hh : ContDiffOn ℝ 2 h (U \ {c})) (hΔ : ∀ x ∈ U \ {c}, Δ h x = 0)
    {M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 < ρ) (hbd : ∀ x ∈ ball c ρ, x ≠ c → |h x| ≤ M) :
    IsWeaklyHarmonicOn U h := by
  intro ψ hψ hψc hψU
  rw [setIntegral_mul_lap_eq_integral h hψU]
  have hloc := locallyIntegrableOn_of_bounded hU hc hh.continuousOn hρ hbd
  have hK : IsCompact (tsupport ψ) := hψc
  obtain ⟨Cψ, Cg, CΔ, hCψ, hCg, hCΔ, hψb, hgb, hLb⟩ := exists_test_bounds hψ hψc
  obtain ⟨A, B, hA0, hB0, hAB⟩ := exists_theta_bounds
  have hA : ∀ t, |deriv theta t| ≤ A := fun t => (hAB t).1
  have hB : ∀ t, |deriv (deriv theta) t| ≤ B := fun t => (hAB t).2
  obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.mp hU c hc
  set r₁ : ℝ := min ρ r₀ with hr₁
  have hr₁0 : 0 < r₁ := lt_min hρ hr₀
  set Ctot : ℝ := 4 * B * Cψ + 8 * A * Cg with hCtot
  set V : ℝ := volume.real (ball (0 : ℂ) 1) with hV
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by norm_num)
  have key : ∀ k : ℝ, 0 < k → k < r₁ → k ≤ 1 →
      |∫ x, h x * Δ ψ x| ≤ M * (CΔ * (k ^ 2 * V) + Ctot * (polarConst * (k / 2))) := by
    intro k hk hkr hk1
    have hη : ContDiff ℝ ∞ (eta k c) := contDiff_eta hk c
    have hψL : ContDiff ℝ ∞ (fun z => ψ z * (1 - eta k c z)) := hψ.mul (contDiff_const.sub hη)
    have hψη : ContDiff ℝ ∞ (fun z => ψ z * eta k c z) := hψ.mul hη
    -- Green's identity for the part away from `c`
    have hKL : IsCompact (tsupport ψ ∩ {z | Real.exp (-1 / k) ≤ ‖z - c‖}) :=
      hK.inter_right (isClosed_le continuous_const (continuous_norm.comp
        (continuous_id.sub continuous_const)))
    have hKLW : tsupport ψ ∩ {z | Real.exp (-1 / k) ≤ ‖z - c‖} ⊆ U \ {c} := by
      intro z hz
      refine ⟨hψU hz.1, fun hzc => ?_⟩
      have := hz.2
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff.mp hzc, sub_self, norm_zero] at this
      exact (Real.exp_pos _).not_ge this
    have hψL0 : ∀ z ∉ tsupport ψ ∩ {z | Real.exp (-1 / k) ≤ ‖z - c‖},
        ψ z * (1 - eta k c z) = 0 := by
      intro z hz
      by_cases h0 : ψ z = 0
      · simp [h0]
      · have hzK : z ∈ tsupport ψ := subset_tsupport ψ h0
        have : ‖z - c‖ ≤ Real.exp (-1 / k) := by
          by_contra hlt
          exact hz ⟨hzK, (not_le.mp hlt).le⟩
        simp [eta_eq_one hk this]
    have hGreen := integral_mul_lap_eq (u := h) (W := U \ {c}) hKL hKLW
      (hU.sdiff isClosed_singleton) hh (hψL.of_le (by norm_num)) hψL0
    have hGreen0 : ∫ x, h x * Δ (fun z => ψ z * (1 - eta k c z)) x = 0 := by
      rw [hGreen]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ tsupport ψ ∩ {z | Real.exp (-1 / k) ≤ ‖z - c‖}
      · simp [hΔ x (hKLW hx)]
      · simp [hψL0 x hx]
    -- splitting the Laplacian
    have hsplit : ∀ x, Δ ψ x =
        Δ (fun z => ψ z * (1 - eta k c z)) x + Δ (fun z => ψ z * eta k c z) x := by
      intro x
      have hfun : ψ = (fun z => ψ z * (1 - eta k c z)) + (fun z => ψ z * eta k c z) := by
        funext z; simp only [Pi.add_apply]; ring
      conv_lhs => rw [hfun]
      exact ContDiffAt.laplacian_add (hψL.contDiffAt.of_le (by norm_num))
        (hψη.contDiffAt.of_le (by norm_num))
    -- integrability
    have hgc : Continuous (Δ (fun z => ψ z * eta k c z)) :=
      continuous_lap (hψη.of_le (by norm_num))
    have hg0 : ∀ x ∉ closedBall c k, Δ (fun z => ψ z * eta k c z) x = 0 := by
      intro x hx
      apply lap_mul_eta_eq_zero hk
      rw [mem_closedBall, dist_eq_norm, not_le] at hx
      exact lt_of_le_of_lt (exp_neg_inv_le hk) hx
    have hkr₀ : k < r₀ := lt_of_lt_of_le hkr (min_le_right _ _)
    have hkρ : k < ρ := lt_of_lt_of_le hkr (min_le_left _ _)
    have hcb : closedBall c k ⊆ U := (closedBall_subset_ball hkr₀).trans hr₀U
    have hcbρ : closedBall c k ⊆ ball c ρ := closedBall_subset_ball hkρ
    have hint1 : Integrable (fun x => h x * Δ ψ x) volume :=
      integrable_mul_of_locallyIntegrableOn hloc hK hψU (continuous_lap hψ2)
        (fun x hx => lap_eq_zero_of_notMem_tsupport hx)
    have hint2 : Integrable (fun x => h x * Δ (fun z => ψ z * eta k c z) x) volume :=
      integrable_mul_of_locallyIntegrableOn hloc (isCompact_closedBall c k) hcb hgc hg0
    have hint3 : Integrable (fun x => h x * Δ (fun z => ψ z * (1 - eta k c z)) x) volume := by
      have := hint1.sub hint2
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      rw [hsplit x]; ring
    have hI : ∫ x, h x * Δ ψ x = ∫ x, h x * Δ (fun z => ψ z * eta k c z) x := by
      have : ∀ x, h x * Δ ψ x =
          h x * Δ (fun z => ψ z * (1 - eta k c z)) x + h x * Δ (fun z => ψ z * eta k c z) x := by
        intro x; rw [hsplit x]; ring
      simp_rw [this]
      rw [integral_add hint3 hint2, hGreen0, zero_add]
    rw [hI]
    -- the capacity estimate
    set g : ℂ → ℝ := Δ (fun z => ψ z * eta k c z) with hgdef
    have hgint : Integrable (fun x => ‖g x‖) volume :=
      (hgc.integrable_of_hasCompactSupport
        (HasCompactSupport.intro (isCompact_closedBall c k) hg0)).norm
    have hMg : Integrable (fun x => M * ‖g x‖) volume := hgint.const_mul M
    have h1 : ‖∫ x, h x * g x‖ ≤ ∫ x, M * ‖g x‖ := by
      refine norm_integral_le_of_norm_le hMg ?_
      have hne : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ c := by rw [ae_iff]; simp
      filter_upwards [hne] with x hx
      by_cases hxb : x ∈ closedBall c k
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbd x (hcbρ hxb) hx) (norm_nonneg _)
      · rw [hg0 x hxb]; simp
    set bnd : ℂ → ℝ := fun z => (closedBall c k).indicator (fun _ => CΔ) z +
      Ctot * Lam k ‖z - c‖ with hbnd
    have hbndint : Integrable bnd volume := by
      refine Integrable.add ?_ ?_
      · exact (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
          measurableSet_closedBall
      · exact (integrable_lam_comp c k).const_mul Ctot
    have h2 : ∫ x, ‖g x‖ ≤ ∫ x, bnd x := by
      refine integral_mono_ae hgint hbndint ?_
      have hne : ∀ᵐ x ∂(volume : Measure ℂ), x ≠ c := by rw [ae_iff]; simp
      filter_upwards [hne] with x hx
      rw [Real.norm_eq_abs]
      exact abs_lap_mul_eta_le hψ hk hA hB hψb hgb hLb c hx
    have h3 : ∫ x, bnd x = CΔ * (k ^ 2 * V) + Ctot * (polarConst * (k / 2)) := by
      rw [hbnd, integral_add, integral_indicator_const _ measurableSet_closedBall, integral_const_mul,
        integral_lam_comp c hk]
      · congr 1
        rw [Measure.real, Measure.addHaar_closedBall volume c hk.le, Complex.finrank_real_complex,
          ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
        simp [hV, Measure.real, smul_eq_mul]
        ring
      · exact (integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
          measurableSet_closedBall
      · exact (integrable_lam_comp c k).const_mul Ctot
    rw [Real.norm_eq_abs] at h1
    calc |∫ x, h x * g x| ≤ ∫ x, M * ‖g x‖ := h1
      _ = M * ∫ x, ‖g x‖ := integral_const_mul _ _
      _ ≤ M * ∫ x, bnd x := mul_le_mul_of_nonneg_left h2 hM
      _ = _ := by rw [h3]
  -- let the scale tend to zero
  set D : ℝ := M * (CΔ * V + Ctot * (polarConst / 2)) with hD
  have hkD : ∀ k : ℝ, 0 < k → k < r₁ → k ≤ 1 → |∫ x, h x * Δ ψ x| ≤ D * k := by
    intro k hk hkr hk1
    refine (key k hk hkr hk1).trans ?_
    have hV0 : 0 ≤ V := measureReal_nonneg
    have hP0 : 0 ≤ polarConst := by unfold polarConst; positivity
    have hk2 : k ^ 2 ≤ k := by linarith [mul_le_mul_of_nonneg_left hk1 hk.le]
    calc M * (CΔ * (k ^ 2 * V) + Ctot * (polarConst * (k / 2)))
        ≤ M * (CΔ * (k * V) + Ctot * (polarConst * (k / 2))) := by
          gcongr
      _ = D * k := by rw [hD]; ring
  have hCtot0 : 0 ≤ Ctot := by positivity
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hP0 : 0 ≤ polarConst := by unfold polarConst; positivity
  have hD0 : 0 ≤ D := by positivity
  by_contra hne
  have hpos : 0 < |∫ x, h x * Δ ψ x| := abs_pos.2 hne
  set k : ℝ := min (min (r₁ / 2) 1) (|∫ x, h x * Δ ψ x| / (2 * (D + 1))) with hkdef
  have hk0 : 0 < k := lt_min (lt_min (by positivity) one_pos) (by positivity)
  have hk1 : k < r₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by linarith)
  have hk2 : k ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hk3 : k ≤ |∫ x, h x * Δ ψ x| / (2 * (D + 1)) := min_le_right _ _
  have h1 := hkD k hk0 hk1 hk2
  have h2 : D * k ≤ D * (|∫ x, h x * Δ ψ x| / (2 * (D + 1))) := mul_le_mul_of_nonneg_left hk3 hD0
  have h3 : D * (|∫ x, h x * Δ ψ x| / (2 * (D + 1))) < |∫ x, h x * Δ ψ x| := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    linarith [mul_pos hpos (by linarith : (0 : ℝ) < D + 2)]
  linarith

/-- The Laplacian of `x ↦ κ ‖x - c‖² / 4` is the constant `κ`. -/
theorem lap_quadratic (κ : ℝ) (c x : ℂ) :
    (Δ (fun y : ℂ => (κ / 4 * ‖y - c‖ ^ 2 : ℝ)) : ℂ → ℝ) x = κ := by
  have hG : ContDiff ℝ 2 (fun s : ℝ => κ / 4 * s) := contDiff_const.mul contDiff_id
  have := lap_comp_normSq_sub hG c x
  have h1 : deriv (fun s : ℝ => κ / 4 * s) = fun _ => κ / 4 := by
    funext s; simp
  simp only [h1, deriv_const] at this
  rw [this]; ring

/-- **Removable singularity theorem for the Poisson equation in the plane.**

Let `U ⊆ ℂ` be open, `c ∈ U`, `κ : ℝ`, and `u : ℂ → ℝ` of class `C²` on `U \ {c}` with `Δ u = κ`
there and bounded near `c`. Then there is `v`, smooth on `U`, equal to `u` on `U \ {c}`, with
`Δ v = κ` on `U`. -/
theorem removable_singularity {U : Set ℂ} (hU : IsOpen U) {c : ℂ} (hc : c ∈ U) (κ : ℝ)
    {u : ℂ → ℝ} (hu : ContDiffOn ℝ 2 u (U \ {c})) (hΔ : ∀ x ∈ U \ {c}, Δ u x = κ)
    (hbd : ∃ M : ℝ, ∀ᶠ x in 𝓝[≠] c, |u x| ≤ M) :
    ∃ v : ℂ → ℝ, ContDiffOn ℝ ∞ v U ∧ EqOn v u (U \ {c}) ∧ ∀ x ∈ U, Δ v x = κ := by
  obtain ⟨M, hM⟩ := hbd
  set q : ℂ → ℝ := fun y => κ / 4 * ‖y - c‖ ^ 2 with hqdef
  have hq : ContDiff ℝ ∞ q := contDiff_const.mul ((contDiff_norm_sq ℝ).comp
    (contDiff_id.sub contDiff_const))
  have hW : IsOpen (U \ {c}) := hU.sdiff isClosed_singleton
  set h : ℂ → ℝ := fun y => u y - q y with hhdef
  have hh : ContDiffOn ℝ 2 h (U \ {c}) :=
    hu.sub (hq.of_le (by norm_num)).contDiffOn
  have hΔh : ∀ x ∈ U \ {c}, Δ h x = 0 := by
    intro x hx
    have := ContDiffAt.laplacian_sub (hu.contDiffAt (hW.mem_nhds hx))
      ((hq.of_le (by norm_num)).contDiffAt (x := x))
    show Δ (fun y => u y - q y) x = 0
    have e : (fun y => u y - q y) = u - q := rfl
    rw [e, this, hΔ x hx, hqdef, lap_quadratic]
    ring
  -- boundedness of `h` near `c`
  obtain ⟨ρ, hρ, hρb⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hM)
  set ρ' : ℝ := min ρ 1 with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ one_pos
  set M' : ℝ := max (M + |κ| / 4) 0 with hM'
  have hbdh : ∀ x ∈ ball c ρ', x ≠ c → |h x| ≤ M' := by
    intro x hx hxc
    have hxd : dist x c < ρ := lt_of_lt_of_le hx (min_le_left _ _)
    have hu1 : |u x| ≤ M := hρb hxd hxc
    have hxn : ‖x - c‖ < 1 := by
      rw [mem_ball, dist_eq_norm] at hx
      exact lt_of_lt_of_le hx (min_le_right _ _)
    have hq1 : |q x| ≤ |κ| / 4 := by
      have hn0 := norm_nonneg (x - c)
      have hsq : ‖x - c‖ ^ 2 ≤ 1 := by linarith [mul_le_mul_of_nonneg_left hxn.le hn0]
      simp only [hqdef]
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_nonneg (sq_nonneg ‖x - c‖)]
      calc |κ| / 4 * ‖x - c‖ ^ 2 ≤ |κ| / 4 * 1 := by gcongr
        _ = |κ| / 4 := mul_one _
    calc |h x| = |u x - q x| := rfl
      _ ≤ |u x| + |q x| := abs_sub _ _
      _ ≤ M + |κ| / 4 := add_le_add hu1 hq1
      _ ≤ M' := le_max_left _ _
  have hw := isWeaklyHarmonicOn_of_bounded hU hc hh hΔh (le_max_right _ _) hρ'0 hbdh
  have hloc := locallyIntegrableOn_of_bounded hU hc hh.continuousOn hρ'0 hbdh
  obtain ⟨v₀, hv₀, hae, hlap⟩ := weyl_lemma hU hloc hw
  refine ⟨fun x => v₀ x + q x, ?_, ?_, ?_⟩
  · exact hv₀.add hq.contDiffOn
  · intro x hx
    have hae' : v₀ =ᵐ[volume.restrict (U \ {c})] h :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset hae
    have := Measure.eqOn_open_of_ae_eq hae' hW
      (hv₀.continuousOn.mono sdiff_subset) hh.continuousOn hx
    show v₀ x + q x = u x
    rw [this]; simp only [hhdef]; ring
  · intro x hx
    have hv2 : ContDiffAt ℝ 2 v₀ x := (hv₀.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
    have := ContDiffAt.laplacian_add hv2 ((hq.of_le (by norm_num)).contDiffAt (x := x))
    show Δ (fun y => v₀ y + q y) x = κ
    have e : (fun y => v₀ y + q y) = v₀ + q := rfl
    rw [e, this, hlap x hx, hqdef, lap_quadratic]
    ring

end SandierSerfaty.Weyl

end
