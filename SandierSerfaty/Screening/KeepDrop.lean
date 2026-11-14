/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.SoftCut
public import SandierSerfaty.Screening.LocEnergy
public import SandierSerfaty.Screening.Monotonicity

/-!
# Keep and drop (screening note, Lemma 4.9)

The screening note, Definition 4.8 and Lemma 4.9 (`lem:keep`), for the data
`Scr.Data` under `Scr.Data.Hyp`. The radii `β = α` on the kept charges `K`, `β = ¼` elsewhere
(`Data.beta`):

* `Hyp.locEnergy_beta_le`: `G_Q(β) ≤ G_Q(α)` (I2 = Lemma 4.13, `locEnergy_le`: the changed charges
  have `δ ≥ 1` by (H3), so their `¼`-discs lie in `U ∩ Q`);
* `Hyp.locEnergy_beta_eq`: `G_Q(β) = ½ ∫_Q |E_β|² + ∑_K τ_m(α_p) - c_m #((C ∩ Q) \ K)`, with
  `E_β ∈ L²(Q)`;
* `Hyp.half_add_tau_le`: **Lemma 4.9(c)**, `½ ∫_Q |E_β|² + ∑_K τ_m(α_p) ≤ G_Q(α) + c_m n_∂`, in
  `EReal`, with `n_∂ = #(C ∩ (Q \ sq c (t - 4ℓt)))`;
* `Hyp.truncField_beta_eq`: **Lemma 4.9(d)**, `E_β = Φ + ∑_K (∇f_{1/4} - ∇f_{α_p})(· - p)`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening.Scr

namespace Data

variable (D : Data)

open scoped Classical in
/-- The radii `β`: `α` on the kept charges, `¼` elsewhere. -/
@[expose] noncomputable def beta (x : ℂ) : ℝ := if x ∈ D.K then D.α x else 1 / 4

/-- The number of charges of `Q` in the layer `Q \ sq c (t - 4ℓt)`. -/
@[expose] noncomputable def nBd : ℕ := (D.C ∩ (sq D.c D.t \ sq D.c (D.t - 4 * D.ℓt))).ncard

/-- `E_β`. -/
@[expose] noncomputable def Eβ (x : ℂ) : ℂ := truncField D.C D.beta D.E x

variable {D}

theorem beta_of_mem {x : ℂ} (hx : x ∈ D.K) : D.beta x = D.α x := by
  classical
  rw [beta, ite_eq_left_iff.2 (fun h' => absurd hx h')]

theorem beta_of_notMem {x : ℂ} (hx : x ∉ D.K) : D.beta x = 1 / 4 := by
  classical
  rw [beta, ite_eq_right_iff.2 (fun h' => absurd h' hx)]

/-- `locEnergy` as a real number when the field integral is finite. -/
theorem locEnergy_eq_coe {m : ℝ} {C : Set ℂ} {α : ℂ → ℝ} {E : ℂ → ℂ} {S : Set ℂ}
    (hL : ∫⁻ x in S, ENNReal.ofReal (‖truncField C α E x‖ ^ 2) ≠ ⊤) :
    locEnergy m C α E S = (((1 / 2) * (∫⁻ x in S, ENNReal.ofReal (‖truncField C α E x‖ ^ 2)).toReal +
      ∑ᶠ p ∈ C ∩ S, tauM m (α p) : ℝ) : EReal) := by
  rw [locEnergy, ← ENNReal.ofReal_toReal hL, coe_ennreal_ofReal_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg, ← EReal.coe_mul, ← EReal.coe_add]

theorem tauM_quarter (m : ℝ) : tauM m (1 / 4) = -cQuarter m := by rw [cQuarter, neg_neg]

theorem cQuarter_pos {m : ℝ} (hm : 0 < m) : 0 < cQuarter m := by
  rw [cQuarter_eq]
  have : 0 < Real.log 4 := Real.log_pos (by norm_num)
  positivity

namespace Hyp

variable (h : D.Hyp)
include h

theorem beta_pos {p : ℂ} (hp : p ∈ D.C) : 0 < D.beta p := by
  by_cases hK : p ∈ D.K
  · rw [beta_of_mem hK]; exact (h.hα p hp).1
  · rw [beta_of_notMem hK]; norm_num

theorem beta_le {p : ℂ} : D.beta p ≤ 1 / 4 := by
  by_cases hK : p ∈ D.K
  · rw [beta_of_mem hK]; exact (h.hα p (h.K_subset_C hK)).2
  · rw [beta_of_notMem hK]

theorem alpha_le_beta {p : ℂ} (hp : p ∈ D.C) : D.α p ≤ D.beta p := by
  by_cases hK : p ∈ D.K
  · rw [beta_of_mem hK]
  · rw [beta_of_notMem hK]; exact (h.hα p hp).2

/-- The changed charges lie in `{δ ≥ 1}`, so their `¼`-discs lie in `U ∩ Q`. -/
theorem closedBall_subset_of_lt {p : ℂ} (hp : p ∈ D.C) (hlt : D.α p < D.beta p) :
    closedBall p (D.beta p) ⊆ D.U ∩ D.Q := by
  have hK : p ∉ D.K := fun hK => by rw [beta_of_mem hK] at hlt; exact lt_irrefl _ hlt
  rw [beta_of_notMem hK] at hlt ⊢
  have hδ : 1 ≤ D.dep p := by
    by_contra hc
    have : p ∉ sq D.c (D.t - 2) := by
      rw [show D.t - 2 = D.t - 2 * 1 by ring, mem_sq_iff_le_sqDepth]; exact hc
    rw [h.hα4 p hp this] at hlt; exact lt_irrefl _ hlt
  intro y hy
  rw [mem_closedBall, dist_eq_norm] at hy
  have := dep_le_add (D := D) p y
  rw [norm_sub_rev] at this
  exact ⟨mem_U_iff.2 (by linarith), mem_Q_iff.2 (by linarith)⟩

omit h in
theorem isBounded_Q : Bornology.IsBounded D.Q := isBounded_sq _ _

/-- `G_Q(β) ≤ G_Q(α)` (Lemma 4.13). -/
theorem locEnergy_beta_le : locEnergy D.m D.C D.beta D.E D.Q ≤ locEnergy D.m D.C D.α D.E D.Q :=
  locEnergy_le isOpen_U measurableSet_Q isBounded_Q h.hC h.hE (fun p hp => (h.hα p hp).1)
    (fun _ hp => h.alpha_le_beta hp) ⟨1 / 4, fun _ _ => h.beta_le⟩
    (fun _ hp hlt => h.closedBall_subset_of_lt hp hlt)

theorem finite_C_inter_Q : (D.C ∩ D.Q).Finite := by
  obtain ⟨R, hR⟩ := isBounded_Q.subset_closedBall 0
  exact (h.hC R).subset fun p hp => ⟨hp.1, hR hp.2⟩

/-- `E_β ∈ L²(Q)`. -/
theorem lintegral_Eβ_ne_top : ∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2) ≠ ⊤ := by
  intro htop
  have hle := h.locEnergy_beta_le
  rw [locEnergy_eq_coe h.hL2] at hle
  have : locEnergy D.m D.C D.beta D.E D.Q = ⊤ := by
    unfold locEnergy
    rw [show (∫⁻ x in D.Q, ENNReal.ofReal (‖truncField D.C D.beta D.E x‖ ^ 2)) = ⊤ from htop,
      EReal.coe_ennreal_top, EReal.coe_mul_top_of_pos (by norm_num), EReal.top_add_coe]
  rw [this] at hle
  exact EReal.coe_ne_top _ (top_le_iff.1 hle)

/-- The kept charges lie in `C ∩ Q`. -/
theorem K_subset_CQ : (D.K : Set ℂ) ⊆ D.C ∩ D.Q := fun p hp =>
  ⟨h.K_subset_C hp, mem_Q_iff.2 (by linarith [(h.mem_K.1 hp).2, h.d_pos])⟩

/-- The `τ`-sum of `β`: `∑_{C ∩ Q} τ_m(β) = ∑_K τ_m(α) - c_m #((C ∩ Q) \ K)`. -/
theorem finsum_tau_beta :
    ∑ᶠ p ∈ D.C ∩ D.Q, tauM D.m (D.beta p) =
      ∑ p ∈ D.K, tauM D.m (D.α p) - cQuarter D.m * (h.finite_C_inter_Q.toFinset \ D.K).card := by
  classical
  set F := h.finite_C_inter_Q.toFinset
  have hKF : D.K ⊆ F := fun p hp => by
    rw [Set.Finite.mem_toFinset]; exact h.K_subset_CQ hp
  rw [finsum_mem_eq_finsetSum (S := F) (by rw [Set.Finite.coe_toFinset])
    (fun p hp hpF => absurd (by rw [Set.Finite.mem_toFinset]; exact hp) hpF)]
  rw [← Finset.sum_sdiff hKF, add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun p hp => by rw [beta_of_mem hp]
  · rw [Finset.sum_congr rfl fun p hp => by rw [beta_of_notMem (Finset.mem_sdiff.1 hp).2,
      tauM_quarter], Finset.sum_const, nsmul_eq_mul]
    ring

/-- The dropped charges of `Q` lie in the boundary layer: `#((C ∩ Q) \ K) ≤ n_∂`. -/
theorem card_sdiff_le : ((h.finite_C_inter_Q.toFinset \ D.K).card : ℝ) ≤ D.nBd := by
  classical
  have hsub : ((h.finite_C_inter_Q.toFinset \ D.K : Finset ℂ) : Set ℂ) ⊆
      D.C ∩ (sq D.c D.t \ sq D.c (D.t - 4 * D.ℓt)) := by
    intro p hp
    rw [Finset.coe_sdiff, Set.Finite.coe_toFinset] at hp
    obtain ⟨⟨hpC, hpQ⟩, hpK⟩ := hp
    refine ⟨hpC, hpQ, fun hp4 => hpK ?_⟩
    rw [show D.t - 4 * D.ℓt = D.t - 2 * (2 * D.ℓt) by ring, mem_sq_iff_le_sqDepth] at hp4
    rw [Finset.mem_coe, h.mem_K]
    exact ⟨hpC, by rw [dep_def]; linarith [h.d_le, h.ℓt_ge]⟩
  have hfin : (D.C ∩ (sq D.c D.t \ sq D.c (D.t - 4 * D.ℓt))).Finite :=
    h.finite_C_inter_Q.subset fun p hp => ⟨hp.1, hp.2.1⟩
  rw [nBd, ← Set.ncard_coe_finset]
  exact_mod_cast Set.ncard_le_ncard hsub hfin

/-- **Lemma 4.9(c)**: `½ ∫_Q |E_β|² + ∑_K τ_m(α_p) ≤ G_Q(α) + c_m n_∂`. -/
theorem half_add_tau_le :
    (((1 / 2) * (∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2)).toReal +
      ∑ p ∈ D.K, tauM D.m (D.α p) : ℝ) : EReal) ≤
      locEnergy D.m D.C D.α D.E D.Q + ((cQuarter D.m * D.nBd : ℝ) : EReal) := by
  have hle := h.locEnergy_beta_le
  rw [locEnergy_eq_coe h.lintegral_Eβ_ne_top, h.finsum_tau_beta] at hle
  have hc := (cQuarter_pos h.m_pos).le
  have hcard := h.card_sdiff_le
  calc (((1 / 2) * (∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2)).toReal +
        ∑ p ∈ D.K, tauM D.m (D.α p) : ℝ) : EReal)
      = (((1 / 2) * (∫⁻ x in D.Q, ENNReal.ofReal (‖D.Eβ x‖ ^ 2)).toReal +
          (∑ p ∈ D.K, tauM D.m (D.α p) - cQuarter D.m *
            (h.finite_C_inter_Q.toFinset \ D.K).card) : ℝ) : EReal) +
          ((cQuarter D.m * (h.finite_C_inter_Q.toFinset \ D.K).card : ℝ) : EReal) := by
        rw [← EReal.coe_add]; ring_nf
    _ ≤ locEnergy D.m D.C D.α D.E D.Q + ((cQuarter D.m * D.nBd : ℝ) : EReal) := by
        gcongr
        exact hle

/-- **Lemma 4.9(d)**: `E_β = Φ + ∑_K (∇f_{1/4} - ∇f_{α_p})(· - p)`. -/
theorem Eβ_eq (x : ℂ) :
    D.Eβ x = D.Φ x + ∑ p ∈ D.K,
      (gradient (truncLog (1 / 4)) (x - p) - gradient (truncLog (D.α p)) (x - p)) := by
  classical
  set IF := D.K.filter fun p => D.α p < 1 / 4
  have hIF : ∀ p, p ∈ IF ↔ p ∈ D.C ∧ D.beta p < 1 / 4 := by
    intro p
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨hK, hlt⟩; exact ⟨h.K_subset_C hK, by rwa [beta_of_mem hK]⟩
    · rintro ⟨hC, hlt⟩
      by_cases hK : p ∈ D.K
      · exact ⟨hK, by rwa [beta_of_mem hK] at hlt⟩
      · rw [beta_of_notMem hK] at hlt; exact absurd hlt (lt_irrefl _)
  have key := truncField_eq_add h.hC (α := D.beta) (β := fun _ => 1 / 4)
    (fun p hp => h.beta_pos hp) (fun p _ => h.beta_le) (M := 1 / 4) (fun _ _ => le_rfl) D.E hIF x
  rw [Eβ]
  change D.Φ x = _ + _ at key
  have hsum : ∑ i ∈ IF, (gradient (truncLog (D.beta i)) (x - i) - gradient (truncLog (1 / 4)) (x - i)) =
      -∑ p ∈ D.K, (gradient (truncLog (1 / 4)) (x - p) - gradient (truncLog (D.α p)) (x - p)) := by
    rw [← Finset.sum_neg_distrib, Finset.sum_filter]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [beta_of_mem hp]
    split_ifs with hlt
    · rw [neg_sub]
    · have : D.α p = 1 / 4 := le_antisymm (h.hα p (h.K_subset_C hp)).2 (not_lt.1 hlt)
      rw [this, sub_self, neg_zero]
  rw [key, hsum]
  ring

end Hyp

end Data

end SandierSerfaty.Screening.Scr

end
