/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenSign
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The truncated screened field, pointwise (screening note, Proposition 4.27, first part)

The screening note, proof of Proposition 4.27 (`prop:energy`). For `A : Asm`
with `A.Good D` under `D.Hyp`, `E'_ρ = E' - ∑_{y ∈ Y} ∇f_{ρ_y}(· - y)` (`Asm.Erho`) is

* `E_β + Y_F` on `Ω₊ = {δ > d}` (`Good.Erho_of_gt`),
* `ψX + ∑_k V_k` on `A = {d - 1 < δ ≤ d}` (`Good.Erho_of_mem_ramp`),
* `∑_k V_k + ∑_j V^c_j + ∑_P (Ψ_P - ∇f_{r₀}(· - z_P))` on `O₋ = {δ ≤ d - 1}` (`Good.Erho_of_le`).

With the cross term `c = ∑_{p ∈ K} Y_F · ∇F_p` (`Asm.cross`, of nonnegative integral by Lemma 4.26)
and the nonnegative majorant `B = ½ 1_{Ω₊}|E_β|² + 2·1_{R_d}|Φ|² + 2|∑V_k|² + 32 n² + 6 ∑_j |V^c_j|²
+ 2 ∑_P |Ψ_P - ∇f_{r₀}(· - z_P)|²` (`Asm.bound`), **`½|E'_ρ|² ≤ B - c` a.e.**
(`Good.ae_half_norm_sq_Erho_le`). This is the screening note's region-by-region estimate, with
`E_β · Y_F = Φ · Y_F - c` and `Φ · Y_F ≤ ½ 1_{R_d}|Φ|² + ½|Y_F|²` on `Ω₊` (`Y_F = 0` on `Ω₊ \ R_d`).
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

theorem half_norm_add_sq_le (a b : ℂ) : 1 / 2 * ‖a + b‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  linarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem norm_add_sq_le_two (a b : ℂ) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  linarith [half_norm_add_sq_le a b]

theorem norm_add3_sq_le (a b e : ℂ) : ‖a + b + e‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖e‖ ^ 2) := by
  have h1 : ‖a + b + e‖ ≤ ‖a‖ + ‖b‖ + ‖e‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖e‖), sq_nonneg (‖b‖ - ‖e‖)]

theorem norm_sum_sq_le_card {ι : Type*} (s : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ s, v i‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖v i‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans (sq_sum_le_card_mul_sum_sq ..)

namespace Scr

open Pinwheel

namespace Asm

/-- The truncated screened field `E'_ρ = E' - ∑_{y ∈ Y} ∇f_{ρ_y}(· - y)`. -/
@[expose] noncomputable def Erho (D : Data) (A : Asm) (x : ℂ) : ℂ :=
  truncField (A.Y D : Set ℂ) (Asm.rho D) (A.E' D) x

/-- `Ψ_P - ∇f_{r₀}(· - z_P)`. -/
@[expose] noncomputable def Pdiff (D : Data) (A : Asm) (i : Fin 4 × ℕ × (ℕ × ℕ)) (x : ℂ) : ℂ :=
  A.Pfield D i x - gradient (truncLog D.r₀) (x - (A.pc i).centre)

/-- `∑_{p ∈ K} ∇f_{α_p}(· - p)`. -/
@[expose] noncomputable def kSum (D : Data) (x : ℂ) : ℂ :=
  ∑ p ∈ D.K, gradient (truncLog (D.α p)) (x - p)

/-- The cross term `c = ∑_{p ∈ K} Y_F · ∇F_p`. -/
@[expose] noncomputable def cross (D : Data) (A : Asm) (x : ℂ) : ℝ :=
  ∑ p ∈ D.K, inner ℝ (A.YF D x) (gradient (Fp D p) x)

/-- The region `Ω₊ = {δ > d}`. -/
@[expose] def Ωp (D : Data) : Set ℂ := {x | D.d < D.dep x}

/-- The nonnegative majorant `B` of `½|E'_ρ|² + c`. -/
@[expose] noncomputable def bound (D : Data) (A : Asm) (x : ℂ) : ℝ :=
  1 / 2 * (Ωp D).indicator (fun y => ‖D.Eβ y‖ ^ 2) x + 2 * D.R.indicator (fun y => ‖D.Φ y‖ ^ 2) x +
    2 * ‖A.Vflux D x‖ ^ 2 + 32 * D.nD x ^ 2 +
    6 * ∑ j : Fin 4, ‖carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x‖ ^ 2 +
    2 * ∑ i ∈ A.pcs, ‖A.Pdiff D i x‖ ^ 2

variable {D : Data} {A : Asm}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

/-- `E'_ρ = ψX - ∑_K ∇f_{α_p}(· - p) + ∑_k V_k + ∑_j V^c_j + ∑_P (Ψ_P - ∇f_{r₀}(· - z_P))`. -/
theorem Erho_eq (x : ℂ) :
    A.Erho D x = D.psiX x - kSum D x + A.Vflux D x + A.Vcarry D x +
      ∑ i ∈ A.pcs, A.Pdiff D i x := by
  classical
  have hY : (A.Y D : Set ℂ) = ((D.K ∪ A.Z : Finset ℂ) : Set ℂ) := rfl
  have hinj : Set.InjOn (fun i => (A.pc i).centre) (A.pcs : Set (Fin 4 × ℕ × (ℕ × ℕ))) := by
    intro i hi i' hi' heq
    by_contra hne
    exact hA.centre_ne h hi hi' hne heq
  have hK : ∑ p ∈ D.K, gradient (truncLog (Asm.rho D p)) (x - p) = kSum D x :=
    Finset.sum_congr rfl fun p hp => by rw [rho_of_mem_K hp]
  have hZ : ∑ z ∈ A.Z, gradient (truncLog (Asm.rho D z)) (x - z) =
      ∑ i ∈ A.pcs, gradient (truncLog D.r₀) (x - (A.pc i).centre) := by
    rw [Z, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [rho_of_notMem_K (hA.notMem_K_of_mem_Z h (Finset.mem_image_of_mem _ hi))]
  rw [Erho, truncField, hY, finsum_mem_coe_finset, Finset.sum_union (hA.disjoint_K_Z h), hK, hZ]
  simp only [E', Vpiece, Pdiff, Finset.sum_sub_distrib]
  abel

/-! ### Supports -/

omit hA in
theorem kSum_eq_zero {x : ℂ} (hx : D.dep x ≤ D.d + 5) : kSum D x = 0 := by
  refine Finset.sum_eq_zero fun p hp => gradient_truncLog_of_gt (h.hα p (h.K_subset_C hp)).1 ?_
  have h1 := Data.dep_le_add (D := D) p x
  have h2 := (h.mem_K.1 hp).2
  have h3 := (h.hα p (h.K_subset_C hp)).2
  rw [norm_sub_rev] at h1
  linarith

theorem Vcarry_eq_zero {x : ℂ} (hx : D.d - 1 < D.dep x) : A.Vcarry D x = 0 := by
  refine Finset.sum_eq_zero fun j _ => t2Field_eq_zero_of_notMem _ _ fun hxc => ?_
  have := (h.cutHyp.sqDepth_mem_of_mem_carryRect hA.isCut j hxc).2
  change D.dep x ≤ D.d - 1 at this
  linarith

theorem Pdiff_eq_zero_of_notMem {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) {x : ℂ}
    (hx : x ∉ (A.pc i).carrier) : A.Pdiff D i x = 0 := by
  have hr : D.r₀ < ‖x - (A.pc i).centre‖ := by
    by_contra hle
    push Not at hle
    exact hx (hA.closedBall_subset_pc h hi (by rw [mem_closedBall, dist_eq_norm]; exact hle))
  rw [Pdiff, hA.Pfield_eq_zero h hi hx, gradient_truncLog_of_gt h.r₀_pos hr, sub_zero]

theorem sum_Pdiff_eq_zero {x : ℂ} (hx : D.d - 1 < D.dep x) : ∑ i ∈ A.pcs, A.Pdiff D i x = 0 :=
  Finset.sum_eq_zero fun i hi => hA.Pdiff_eq_zero_of_notMem h hi fun hxp => by
    have := hA.dep_le_of_mem_pc h hi hxp
    linarith

theorem Vflux_eq_zero {x : ℂ} (hx : D.d + 8 < D.dep x) : A.Vflux D x = 0 := by
  have hF : x ∉ frameSet D.c D.t D.d := fun h' => by
    have := h'.2
    change D.dep x ≤ D.d + 8 at this
    linarith
  exact Finset.sum_eq_zero fun jk hjk => Good.fluxV_eq_zero h fun h' => hF (hA.col_subset_frame h hjk h')

theorem YF_eq_zero {x : ℂ} (hx : D.d + 11 < D.dep x) : A.YF D x = 0 := by
  rw [YF, hA.Vflux_eq_zero h (by linarith), zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun q hq => radialW_of_notMem ?_
  rw [mem_ball, dist_zero_right, not_lt]
  have h1 := Data.dep_le_add (D := D) x q
  have h2 := (h.mem_Ds.1 hq).2.2
  linarith

omit h hA in
theorem gradient_Fp_eq_zero {p x : ℂ} (hx : 1 / 4 < ‖x - p‖) : gradient (Fp D p) x = 0 := by
  have hev : Fp D p =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx]
      with z hz
    exact truncDiff_eq_zero (le_of_lt hz)
  rw [gradient_congr_nhds hev]
  simp [gradient]

omit hA in
theorem cross_eq_zero {x : ℂ} (hx : D.dep x ≤ D.d + 5) : A.cross D x = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [gradient_Fp_eq_zero, inner_zero_right]
  have h1 := Data.dep_le_add (D := D) p x
  have h2 := (h.mem_K.1 hp).2
  rw [norm_sub_rev] at h1
  linarith

/-! ### The three regions -/

/-- On `Ω₊ = {δ > d}`: `E'_ρ = E_β + Y_F`. -/
theorem Erho_of_gt {x : ℂ} (hx : D.d < D.dep x) : A.Erho D x = D.Eβ x + A.YF D x := by
  rw [hA.Erho_eq h, hA.Vcarry_eq_zero h (by linarith), hA.sum_Pdiff_eq_zero h (by linarith),
    Data.psiX, Data.psi_eq_one hx.le, one_smul, Data.X, h.Eβ_eq, YF, kSum, Finset.sum_sub_distrib]
  abel

/-- On the ramp `{d - 1 < δ ≤ d}`: `E'_ρ = ψX + ∑_k V_k`. -/
theorem Erho_of_mem_ramp {x : ℂ} (h1 : D.d - 1 < D.dep x) (h2 : D.dep x ≤ D.d) :
    A.Erho D x = D.psiX x + A.Vflux D x := by
  rw [hA.Erho_eq h, hA.Vcarry_eq_zero h h1, hA.sum_Pdiff_eq_zero h h1,
    kSum_eq_zero h (by linarith)]
  abel

/-- On `O₋ = {δ ≤ d - 1}`: `E'_ρ = ∑_k V_k + ∑_j V^c_j + ∑_P (Ψ_P - ∇f_{r₀}(· - z_P))`. -/
theorem Erho_of_le {x : ℂ} (hx : D.dep x ≤ D.d - 1) :
    A.Erho D x = A.Vflux D x + A.Vcarry D x + ∑ i ∈ A.pcs, A.Pdiff D i x := by
  rw [hA.Erho_eq h, kSum_eq_zero h (by linarith), Data.psiX, Data.psi_eq_zero hx, zero_smul]
  abel

/-! ### The pointwise bound -/

omit hA in
theorem ae_Eβ_eq :
    ∀ᵐ x, D.Eβ x = D.Φ x - ∑ p ∈ D.K, gradient (Fp D p) x := by
  have hae : ∀ᵐ x, ∀ p ∈ D.K, gradient (Fp D p) x =
      gradient (truncLog (D.α p)) (x - p) - gradient (truncLog (1 / 4)) (x - p) :=
    (eventually_all_finset _).2 fun p hp =>
      ae_gradient_truncDiff_sub (h.hα p (h.K_subset_C hp)).1 (h.hα p (h.K_subset_C hp)).2 p
  filter_upwards [hae] with x hx
  rw [h.Eβ_eq, Finset.sum_congr rfl hx, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_congr rfl fun p _ => (neg_sub _ _).symm

/-- **The pointwise bound**: `½|E'_ρ|² ≤ B - c` a.e. -/
theorem ae_half_norm_sq_Erho_le : ∀ᵐ x, 1 / 2 * ‖A.Erho D x‖ ^ 2 ≤ A.bound D x - A.cross D x := by
  have hat := ae_atMostOne A.pcs (fun i => (A.pc i).carrier) fun _ hi _ hj hne =>
    hA.volume_pc_inter h hi hj hne
  filter_upwards [ae_Eβ_eq h, hat] with x hEβ hx
  have hI1 : 0 ≤ (Ωp D).indicator (fun y => ‖D.Eβ y‖ ^ 2) x :=
    indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hI2 : 0 ≤ D.R.indicator (fun y => ‖D.Φ y‖ ^ 2) x := indicator_nonneg (fun _ _ => sq_nonneg _) x
  have hC3 : 0 ≤ ∑ j : Fin 4, ‖carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hP4 : 0 ≤ ∑ i ∈ A.pcs, ‖A.Pdiff D i x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn := Data.nD_nonneg (D := D) x
  have hV := sq_nonneg ‖A.Vflux D x‖
  have hW := Data.norm_sum_radialW_le (D := D) x
  unfold bound
  rcases lt_or_ge D.d (D.dep x) with hgt | hle
  · -- `Ω₊`
    rw [hA.Erho_of_gt h hgt, indicator_of_mem (show x ∈ Ωp D from hgt)]
    set e := D.Eβ x
    set y := A.YF D x
    have hc : A.cross D x = inner ℝ (D.Φ x) y - inner ℝ e y := by
      rw [hEβ, inner_sub_left, sum_inner, cross]
      simp only [real_inner_comm y]
      ring
    have hΦy : inner ℝ (D.Φ x) y ≤ 1 / 2 * D.R.indicator (fun y => ‖D.Φ y‖ ^ 2) x + 1 / 2 * ‖y‖ ^ 2 := by
      by_cases hR : x ∈ D.R
      · rw [indicator_of_mem hR]
        have := real_inner_le_norm (D.Φ x) y
        linarith [sq_nonneg (‖D.Φ x‖ - ‖y‖)]
      · have hy : y = 0 := hA.YF_eq_zero h (by
          rw [Data.mem_R_iff] at hR
          push Not at hR
          exact hR (by linarith))
        rw [hy, inner_zero_right]
        positivity
    have hy2 : ‖y‖ ^ 2 ≤ 2 * ‖A.Vflux D x‖ ^ 2 + 32 * D.nD x ^ 2 := by
      have h1 := norm_add_sq_le_two (A.Vflux D x) (-∑ q ∈ D.Ds, radialW (1 / 4) (x - q))
      rw [← sub_eq_add_neg, norm_neg] at h1
      have h2 : ‖∑ q ∈ D.Ds, radialW (1 / 4) (x - q)‖ ^ 2 ≤ (4 * D.nD x) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hW 2
      change ‖A.Vflux D x - _‖ ^ 2 ≤ _ at h1
      have : y = A.Vflux D x - ∑ q ∈ D.Ds, radialW (1 / 4) (x - q) := rfl
      rw [this]
      linarith
    have hexp : ‖e + y‖ ^ 2 = ‖e‖ ^ 2 + 2 * inner ℝ e y + ‖y‖ ^ 2 := norm_add_sq_real e y
    rw [hexp]
    linarith
  · rcases lt_or_ge (D.d - 1) (D.dep x) with hgt' | hle'
    · -- the ramp
      rw [hA.Erho_of_mem_ramp h hgt' hle, cross_eq_zero h (by linarith),
        indicator_of_notMem (show x ∉ Ωp D from not_lt.2 hle),
        indicator_of_mem (show x ∈ D.R from Data.mem_R_iff.2 ⟨by linarith, by linarith⟩)]
      have h1 := half_norm_add_sq_le (D.psiX x) (A.Vflux D x)
      have h2 : ‖D.psiX x‖ ≤ ‖D.Φ x‖ + 4 * D.nD x := by
        rw [Data.psiX, norm_smul, Real.norm_of_nonneg (Data.psi_nonneg x)]
        calc D.psi x * ‖D.X x‖ ≤ 1 * ‖D.X x‖ :=
              mul_le_mul_of_nonneg_right (Data.psi_le_one x) (norm_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact h.norm_X_le (by linarith)
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
      linarith [sq_nonneg (‖D.Φ x‖ - 4 * D.nD x)]
    · -- `O₋`
      rw [hA.Erho_of_le h hle', cross_eq_zero h (by linarith),
        indicator_of_notMem (show x ∉ Ωp D from fun h' => by
          change D.d < D.dep x at h'
          linarith)]
      have h1 := norm_add3_sq_le (A.Vflux D x) (A.Vcarry D x) (∑ i ∈ A.pcs, A.Pdiff D i x)
      have h2 := norm_sum_sq_le_card (Finset.univ : Finset (Fin 4))
        fun j => carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x
      rw [Finset.card_univ, Fintype.card_fin] at h2
      have h3 : ‖∑ i ∈ A.pcs, A.Pdiff D i x‖ ^ 2 = ∑ i ∈ A.pcs, ‖A.Pdiff D i x‖ ^ 2 :=
        norm_sq_sum_of_atMostOne hx fun i hi hxi => hA.Pdiff_eq_zero_of_notMem h hi hxi
      have h4 : A.Vcarry D x = ∑ j : Fin 4, carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x :=
        rfl
      rw [← h4] at h2
      push_cast at h2
      nlinarith

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
