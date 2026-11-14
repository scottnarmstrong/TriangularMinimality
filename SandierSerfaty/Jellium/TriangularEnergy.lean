/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Jellium.TriangularEnergyLimit
public import SandierSerfaty.Jellium.TriangularRadii
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
public import SandierSerfaty.Statements.Jellium.Defs.TriangularField
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy

/-!
# The neutral energy of the triangular field

For a lattice `Γ` of covolume `1` all of whose nonzero points have norm `≥ 1` and a torus potential `h` of the
charge at `0`, the neutral energy `W^neu(∇h, 1)` is `(1/4π) J + ½ log ¼ - π/32`, where
`J = ∫_F ‖E_{¼}‖²` is the cell integral of the truncated field (`neutralEnergy_eq`). Combined with the
puncture limit (`SandierSerfaty.Torus.tendsto_puncture`) this is `W/(2π)`, with `W` the puncture
energy (`neutralEnergy_triangularField`).
-/

open MeasureTheory Filter Topology Laplacian Metric InnerProductSpace Set
open scoped ContDiff ENNReal

public section

namespace SandierSerfaty

namespace Torus

section CubeEnergy

variable {Γ : Submodule ℤ ℂ} [DiscreteTopology Γ] [IsZLattice ℝ Γ]

theorem finsum_mem_const_real {s : Set ℂ} (hs : s.Finite) (c : ℝ) :
    ∑ᶠ _p ∈ s, c = s.ncard * c := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, nsmul_eq_mul,
    ← Set.ncard_eq_toFinset_card s hs]

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem truncField_cubeRadius (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) (h : ℂ → ℝ) (ℓ : ℝ) :
    truncField (Γ : Set ℂ) (cubeRadius (Γ : Set ℂ) ℓ) (gradient h) = tField Γ h := by
  funext x
  unfold truncField tField
  congr 1
  exact finsum_mem_congr rfl fun p hp => by rw [cubeRadius_eq_quarter hmin hp ℓ]

omit [IsZLattice ℝ Γ] in
/-- **The cube energy of the truncated field** (all radii equal `¼`). -/
theorem mul_cubeEnergy_eq (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) {h : ℂ → ℝ} (ℓ : ℝ)
    (hL : ∫⁻ x in cube ℓ, ENNReal.ofReal (‖tField Γ h x‖ ^ 2) ≠ ⊤) :
    (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy (Γ : Set ℂ) (gradient h) ℓ =
      (((ℓ ^ 2)⁻¹ * ((1 / (4 * Real.pi)) *
          (∫⁻ x in cube ℓ, ENNReal.ofReal (‖tField Γ h x‖ ^ 2)).toReal +
        (((Γ : Set ℂ) ∩ cube ℓ).ncard : ℝ) *
          (1 / 2 * Real.log (1 / 4) - Real.pi * (1 / 4) ^ 2 / 2)) : ℝ) : EReal) := by
  have hfin : ((Γ : Set ℂ) ∩ cube ℓ).Finite := finite_lattice_inter (isBounded_cube ℓ)
  have hs1 : ∑ᶠ p ∈ (Γ : Set ℂ) ∩ cube ℓ, -Real.log (cubeRadius (Γ : Set ℂ) ℓ p) =
      (((Γ : Set ℂ) ∩ cube ℓ).ncard : ℝ) * (-Real.log (1 / 4)) := by
    rw [← finsum_mem_const_real hfin]
    exact finsum_mem_congr rfl fun p hp => by rw [cubeRadius_eq_quarter hmin hp.1 ℓ]
  have hs2 : ∑ᶠ p ∈ (Γ : Set ℂ) ∩ cube ℓ, ∫ x, truncLog (cubeRadius (Γ : Set ℂ) ℓ p) (x - p) =
      (((Γ : Set ℂ) ∩ cube ℓ).ncard : ℝ) * (Real.pi * (1 / 4) ^ 2 / 2) := by
    rw [← finsum_mem_const_real hfin]
    refine finsum_mem_congr rfl fun p hp => ?_
    rw [cubeRadius_eq_quarter hmin hp.1 ℓ, integral_sub_right_eq_self (truncLog (1 / 4)) p,
      integral_truncLog (by norm_num)]
  unfold cubeEnergy
  rw [truncField_cubeRadius hmin h ℓ, hs1, hs2, ← EReal.coe_ennreal_toReal hL]
  rw [← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_mul]
  congr 1
  ring

/-- **The neutral energy of the truncated field.** -/
theorem neutralEnergy_eq (hmin : ∀ γ ∈ Γ, γ ≠ 0 → 1 ≤ ‖γ‖) (hΓ : ZLattice.covolume Γ = 1)
    {h : ℂ → ℝ} (hper : ∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) {F : Set ℂ}
    (hF : IsAddFundamentalDomain Γ F volume) (hFm : MeasurableSet F)
    (hFb : Bornology.IsBounded F) (hcov : ∀ x : ℂ, ∃ γ ∈ Γ, x - γ ∈ F)
    (hJ : ∫⁻ x in F, ENNReal.ofReal (‖tField Γ h x‖ ^ 2) ≠ ⊤) :
    neutralEnergy (Γ : Set ℂ) (gradient h) =
      ((1 / (4 * Real.pi) * (∫⁻ x in F, ENNReal.ofReal (‖tField Γ h x‖ ^ 2)).toReal +
        (1 / 2 * Real.log (1 / 4) - Real.pi * (1 / 4) ^ 2 / 2) : ℝ) : EReal) := by
  obtain ⟨d, hd⟩ := hFb.subset_closedBall (0 : ℂ)
  have hGper : ∀ γ ∈ Γ, ∀ x, ENNReal.ofReal (‖tField Γ h (x + γ)‖ ^ 2) =
      ENNReal.ofReal (‖tField Γ h x‖ ^ 2) := fun γ hγ x => by rw [tField_add hper hγ x]
  have hdens := tendsto_ncard_inter_cube_div Γ hΓ
  have hlim := tendsto_lintegral_cube_div hΓ hF hFm hd hcov
    (G := fun x => ENNReal.ofReal (‖tField Γ h x‖ ^ 2)) hGper
  have hLfin := fun ℓ => lintegral_cube_ne_top hF hFm hd hcov
    (G := fun x => ENNReal.ofReal (‖tField Γ h x‖ ^ 2)) hGper hJ ℓ
  set J : ℝ≥0∞ := ∫⁻ x in F, ENNReal.ofReal (‖tField Γ h x‖ ^ 2) with hJdef
  -- the real-valued limit
  have hreal : Tendsto (fun ℓ : ℝ => (ℓ ^ 2)⁻¹ *
      (∫⁻ x in cube ℓ, ENNReal.ofReal (‖tField Γ h x‖ ^ 2)).toReal) atTop (𝓝 J.toReal) := by
    have := (ENNReal.tendsto_toReal hJ).comp hlim
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    simp only [Function.comp_apply]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hx : Tendsto (fun ℓ : ℝ => (ℓ ^ 2)⁻¹ * ((1 / (4 * Real.pi)) *
          (∫⁻ x in cube ℓ, ENNReal.ofReal (‖tField Γ h x‖ ^ 2)).toReal +
        (((Γ : Set ℂ) ∩ cube ℓ).ncard : ℝ) *
          (1 / 2 * Real.log (1 / 4) - Real.pi * (1 / 4) ^ 2 / 2))) atTop
      (𝓝 (1 / (4 * Real.pi) * J.toReal +
        (1 / 2 * Real.log (1 / 4) - Real.pi * (1 / 4) ^ 2 / 2))) := by
    have h1 := (hreal.const_mul (1 / (4 * Real.pi))).add
      (hdens.mul_const (1 / 2 * Real.log (1 / 4) - Real.pi * (1 / 4) ^ 2 / 2))
    rw [one_mul] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with ℓ hℓ
    field_simp
  have hdens' : Tendsto (fun ℓ : ℝ => (((Γ : Set ℂ) ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1) :=
    hdens
  unfold neutralEnergy
  simp only [hdens', ↓reduceIte]
  rw [limsup_congr (Eventually.of_forall fun ℓ => mul_cubeEnergy_eq hmin ℓ (hLfin ℓ))]
  exact (EReal.tendsto_coe.2 hx).limsup_eq

theorem lintegral_ball_gradSq {h v : ℂ → ℝ} (hv : IsLocalPart h v) :
    ∫⁻ y in ball (0 : ℂ) (1 / 4), cellGradSq v y = ENNReal.ofReal (Vint v (1 / 4)) := by
  have hint : IntegrableOn (fun y : ℂ => ‖gradient v y‖ ^ 2) (ball (0 : ℂ) (1 / 4)) :=
    (((continuousOn_gradient hv.1).mono closedBall_quarter_subset).norm.pow 2
      |>.integrableOn_compact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  exact (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun y => by positivity)).symm

end CubeEnergy

end Torus

/-- **`W^neu(E_tri, 1) = W_tri / (2π)`**: the second conjunct of `triangularField_spec`. -/
theorem neutralEnergy_triangularField :
    neutralEnergy (triangularLattice : Set ℂ) triangularField =
      ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) := by
  have hmin : ∀ γ ∈ triangularLattice, γ ≠ 0 → 1 ≤ ‖γ‖ := fun γ hγ h0 =>
    triangularLattice_norm_ge_one hγ h0
  have hcov1 : ZLattice.covolume triangularLattice = 1 := Torus.covolume_triangularLattice
  have hcovN : ZLattice.covolume triangularLattice = ((1 : ℕ) : ℝ) := by simpa using hcov1
  set h : ℂ → ℝ := torusPotential triangularLattice Torus.zeroCharge with hh
  have hP : IsTorusPotential triangularLattice Torus.zeroCharge h :=
    isTorusPotential_torusPotential triangularLattice hcovN Torus.zeroCharge
      (fun i j _ => Subsingleton.elim i j)
  have hfield : triangularField = gradient h := rfl
  obtain ⟨v, hv1, hv2, hv3⟩ := Torus.exists_local_form_ball hmin hP
  have hv : Torus.IsLocalPart h v := ⟨hv1, hv2, hv3⟩
  obtain ⟨F, hF, hFm, hFb, hcov⟩ := Torus.exists_fundamentalDomain triangularLattice
  have hcell := Torus.lintegral_cell hmin hP.1 hv hF
  rw [Torus.lintegral_ball_gradSq hv] at hcell
  have hAfin := Torus.lintegral_far_ne_top hP hFb hcov (ε := 1 / 4) (by norm_num)
  have hJ : ∫⁻ x in F, ENNReal.ofReal (‖Torus.tField triangularLattice h x‖ ^ 2) ≠ ⊤ := by
    rw [hcell]; exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hAfin⟩
  have hneu := Torus.neutralEnergy_eq hmin hcov1 hP.1 hF hFm hFb hcov hJ
  have hen : triangularEnergy = 1 / 2 * (∫⁻ x in F, (Torus.farSet triangularLattice (1 / 4)).indicator
        (Torus.cellGradSq h) x).toReal + 1 / 2 * Torus.Vint v (1 / 4) + Real.pi * Real.log (1 / 4) -
        Real.pi ^ 2 * (1 / 4) ^ 2 :=
    (Torus.tendsto_puncture hmin hP hv hF hFb hcov).limUnder_eq
  rw [hfield, hneu, hen, hcell, ENNReal.toReal_add ENNReal.ofReal_ne_top hAfin,
    ENNReal.toReal_ofReal (Torus.Vint_nonneg v _)]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  congr 1
  field_simp
  ring

end SandierSerfaty

end
