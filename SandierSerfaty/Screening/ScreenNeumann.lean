/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenAssembly

/-!
# The Neumann identity of the screened field (screening note, Lemmas 4.24, 4.25)

The screening note, Lemma 4.24 (`lem:points`, the separation of the new
charges) and Lemma 4.25 (`lem:neumann`). For `A : Asm` with `A.Good D` under `D.Hyp`:

* `Good.two_mul_r₀_le`: distinct piece centres are `2r₀` apart (the `r₀`-discs lie in the open
  pieces, which overlap in null sets);
* `Good.src_ae_eq`: **the source identity** `∑ 1_{H_k} f_k + ∑ f^c_j + ∑_P 2πμ 1_P = g 1_Q` a.e.
  (on `T_k`: `f_k = g̃`; on `H'_k`: `2π(m - μ_k) + 2πμ_k = 2πm = g̃`; on `P_k \ H'_k`: `2πμ = g̃`;
  the carries make up `g - g̃`; `g = 0` on `Q \ F`);
* `Good.isFieldPiece_E'`: `E'` is a field piece with charges `Y = K ∪ Z`;
* `Good.isNeumannChargeField`: **Lemma 4.25**, `E'` is a Neumann charge field on `Q` with density
  `m` and charges `Y`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

/-- Two closed discs of radius `r` inside sets with null intersection are `2r` apart. -/
theorem two_mul_le_norm_sub_of_null {S S' : Set ℂ} {z z' : ℂ} {r : ℝ}
    (hz : closedBall z r ⊆ S) (hz' : closedBall z' r ⊆ S') (h0 : volume (S ∩ S') = 0) :
    2 * r ≤ ‖z - z'‖ := by
  by_contra hlt
  push Not at hlt
  set w := (z + z') / 2
  set ε := r - ‖z - z'‖ / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  have hwz : ‖w - z‖ = ‖z - z'‖ / 2 := by
    rw [show w - z = (z' - z) / 2 by simp only [w]; ring, norm_div, norm_sub_rev]; simp
  have hwz' : ‖w - z'‖ = ‖z - z'‖ / 2 := by
    rw [show w - z' = (z - z') / 2 by simp only [w]; ring, norm_div]; simp
  have hsub : ball w ε ⊆ S ∩ S' := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h1 : ‖y - z‖ ≤ ‖y - w‖ + ‖w - z‖ := by
      calc ‖y - z‖ = ‖(y - w) + (w - z)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖y - z'‖ ≤ ‖y - w‖ + ‖w - z'‖ := by
      calc ‖y - z'‖ = ‖(y - w) + (w - z')‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    exact ⟨hz (by rw [mem_closedBall, dist_eq_norm]; simp only [ε] at hy; linarith),
      hz' (by rw [mem_closedBall, dist_eq_norm]; simp only [ε] at hy; linarith)⟩
  exact (measure_ball_pos volume w hε).ne' (measure_mono_null hsub h0)

namespace Scr

open Pinwheel

namespace Asm

variable {D : Data} {A : Asm}

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

theorem isFillerPiece {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) :
    (A.pc i).IsFillerPiece D.m (A.μ D i) := by
  have hk := (mem_pcs.1 hi).1
  exact (hA.filler i.1 i.2.1 hk).isFillerPiece h.m_pos
    (h.cutHyp.aestronglyMeasurable_fillDensity hA.isCut hk)
    (h.cutHyp.ae_fillDensity_mem hA.isCut hk) (mem_pcs.1 hi).2

theorem closedBall_subset_pc {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) :
    closedBall (A.pc i).centre D.r₀ ⊆ (A.pc i).carrier :=
  ((hA.isFillerPiece h hi).closedBall_subset_openCarrier h.r₀_pos h.r₀_le').trans
    (A.pc i).openCarrier_subset_carrier

/-- **Separation of the new charges** (Lemma 4.24): distinct piece centres are `2r₀` apart. -/
theorem two_mul_r₀_le {i i' : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) (hi' : i' ∈ A.pcs)
    (hne : i ≠ i') : 2 * D.r₀ ≤ ‖(A.pc i).centre - (A.pc i').centre‖ :=
  two_mul_le_norm_sub_of_null (hA.closedBall_subset_pc h hi) (hA.closedBall_subset_pc h hi')
    (hA.volume_pc_inter h hi hi' hne)

theorem centre_ne {i i' : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) (hi' : i' ∈ A.pcs)
    (hne : i ≠ i') : (A.pc i).centre ≠ (A.pc i').centre := fun heq => by
  have := hA.two_mul_r₀_le h hi hi' hne
  rw [heq, sub_self, norm_zero] at this
  linarith [h.r₀_pos]

/-- The pieces lie in `{δ ≤ d - 1}`. -/
theorem dep_le_of_mem_pc {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) {x : ℂ}
    (hx : x ∈ (A.pc i).carrier) : D.dep x ≤ D.d - 1 := by
  have hx' := hA.pc_subset_fillRect hi hx
  have hb := h.cutHyp.fillRect_subset_bottom hA.isCut (mem_pcs.1 hi).1 hx'
  exact (sqDepth_mem_of_mem_bottom h.offset_pos.le hb).2

theorem centre_mem_pc {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) :
    (A.pc i).centre ∈ (A.pc i).carrier :=
  hA.closedBall_subset_pc h hi (mem_closedBall_self h.r₀_pos.le)

theorem disjoint_K_Z : Disjoint D.K A.Z := by
  rw [Finset.disjoint_left]
  intro p hpK hpZ
  rw [Z, Finset.mem_image] at hpZ
  obtain ⟨i, hi, rfl⟩ := hpZ
  have h1 := hA.dep_le_of_mem_pc h hi (hA.centre_mem_pc h hi)
  linarith [(h.mem_K.1 hpK).2]

/-! ### Supports -/

omit hA in
theorem fluxV_eq_zero {jk : Fin 4 × ℕ} {x : ℂ} (hx : x ∉ A.col D jk) :
    A.cut.fluxV D.c D.t D.d D.ℓ D.g jk.1 jk.2 x = 0 :=
  t2Field_eq_zero_of_notMem _ _ fun hx' => hx (Good.fluxRect_subset_col h hx')

theorem Pfield_eq_zero {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) {x : ℂ}
    (hx : x ∉ (A.pc i).carrier) : A.Pfield D i x = 0 := by
  have hr : D.r₀ < ‖x - (A.pc i).centre‖ := by
    by_contra hle
    push Not at hle
    exact hx (hA.closedBall_subset_pc h hi (by rw [mem_closedBall, dist_eq_norm]; exact hle))
  rw [Pfield, Rect.pieceField, radialK_eq_zero_of_lt h.r₀_pos hr, t2Field_eq_zero_of_notMem _ _ hx,
    add_zero]

omit h in
theorem lastWidth_mem (j : Fin 4) : A.cut.lastWidth j ∈ Icc D.ℓ (3 * D.ℓ) :=
  ⟨(hA.isCut.lastWidth_mem j).1, (hA.isCut.lastWidth_mem j).2.le⟩

theorem carryRect_subset_frame (j : Fin 4) :
    (carryRect D.c D.t D.d j (A.cut.lastWidth j)).carrier ⊆ frameSet D.c D.t D.d := by
  intro x hx
  have := h.cutHyp.sqDepth_mem_of_mem_carryRect hA.isCut j hx
  exact ⟨this.1.1, by linarith [this.2]⟩

theorem carrySrc_eq_zero {j : Fin 4} {x : ℂ} (hx : x ∉ frameSet D.c D.t D.d) :
    carrySrc D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x = 0 :=
  carrySrc_eq_zero_of_notMem fun hx' => hx (hA.carryRect_subset_frame h j hx')

theorem carryField_eq_zero {j : Fin 4} {x : ℂ} (hx : x ∉ frameSet D.c D.t D.d) :
    carryField D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x = 0 :=
  t2Field_eq_zero_of_notMem _ _ fun hx' => hx (hA.carryRect_subset_frame h j hx')

/-! ### The source identity -/

/-- The flux-cell source `1_{H_k} f_k` of the column `jk`. -/
@[expose] noncomputable def fluxSrc (D : Data) (A : Asm) (jk : Fin 4 × ℕ) : ℂ → ℝ :=
  (A.fluxRect D jk).carrier.indicator ((A.fluxRect D jk).fluxSrc D.ℓ (A.cut.src D.c D.t D.d D.g))

/-- The piece source `2πμ 1_P`. -/
@[expose] noncomputable def pieceSrc (D : Data) (A : Asm) (i : Fin 4 × ℕ × (ℕ × ℕ)) : ℂ → ℝ :=
  (A.pc i).carrier.indicator fun x => 2 * π * A.μ D i x

/-- The column identity `1_{H_k} f_k + 1_{P_k} 2πμ_k = g̃` on `Col_k`, a.e. -/
theorem ae_col_identity {jk : Fin 4 × ℕ} (hjk : jk ∈ A.cols) :
    ∀ᵐ x, x ∈ A.col D jk →
      fluxSrc D A jk x + (A.fillRect D jk).carrier.indicator
        (fun x => 2 * π * A.cut.fillDensity D.c D.t D.d D.m D.ℓ D.g jk.1 jk.2 x) x =
        A.cut.src D.c D.t D.d D.g x := by
  have hk := mem_cols.1 hjk
  filter_upwards [h.cutHyp.ae_fluxSrc_col_comp hA.isCut hk, h.cutHyp.ae_src_comp hA.isCut hk]
    with x hflux hsrc hx
  have hπ : (2 * π) ≠ 0 := by positivity
  have hℓ := h.ℓ_pos
  have hd := h.d_ge_ℓ
  rw [col, ColumnCut.col, Rect.mem_box] at hx
  simp only [fluxSrc, fluxRect, fillRect]
  set v := ((rect D.c D.t D.d jk.1).coords x).im
  have hH : x ∈ (A.cut.fluxRect D.c D.t D.d D.ℓ jk.1 jk.2).carrier ↔ D.d - 1 - D.ℓ ≤ v := by
    rw [ColumnCut.carrier_fluxRect, Rect.mem_box]
    exact ⟨fun h' => h'.2.1, fun h' => ⟨hx.1, h', hx.2.2⟩⟩
  have hF : x ∈ (A.cut.fillRect D.c D.t D.d jk.1 jk.2).carrier ↔ v ≤ D.d - 1 := by
    rw [ColumnCut.carrier_fillRect, Rect.mem_box]
    exact ⟨fun h' => h'.2.2, fun h' => ⟨hx.1, hx.2.1, h'⟩⟩
  have hlow : x ∈ ColumnCut.lowSet D.c D.t D.d D.ℓ jk.1 ↔ v < D.d - 1 - D.ℓ := by
    rw [ColumnCut.lowSet, Rect.mem_box]; simp only [mem_univ, mem_Iio, true_and, v]
  by_cases h1 : D.d - 1 - D.ℓ ≤ v
  · by_cases h2 : v ≤ D.d - 1
    · -- the compensation strip
      have hcomp : x ∈ A.cut.comp D.c D.t D.d D.ℓ jk.1 jk.2 := by
        rw [ColumnCut.comp, Rect.mem_box]; exact ⟨hx.1, h1, h2⟩
      rw [indicator_of_mem (hH.2 h1), indicator_of_mem (hF.2 h2), hflux hcomp,
        ColumnCut.fillDensity_of_notMem (fun h' => absurd (hlow.1 h') (not_lt.2 h1)), hsrc hcomp]
      ring
    · -- the top part
      push Not at h2
      have htop : x ∈ A.cut.top D.c D.t D.d jk.1 jk.2 := by
        rw [ColumnCut.top, Rect.mem_box]; exact ⟨hx.1, h2.le, hx.2.2⟩
      rw [indicator_of_mem (hH.2 h1), indicator_of_notMem (fun h' => absurd (hF.1 h') (not_le.2 h2)),
        add_zero]
      exact Pinwheel.CutHyp.fluxSrc_col_of_mem_top htop
  · -- below the compensation strip
    push Not at h1
    rw [indicator_of_notMem (fun h' => absurd (hH.1 h') (not_le.2 h1)), zero_add,
      indicator_of_mem (hF.2 (by linarith)), ColumnCut.fillDensity_of_mem (hlow.2 h1)]
    field_simp

/-- **The source identity**: `∑ 1_{H_k} f_k + ∑ f^c_j + ∑_P 2πμ 1_P = g 1_Q` a.e. -/
theorem src_ae_eq :
    ∀ᵐ x, (∑ jk ∈ A.cols, fluxSrc D A jk x) +
        (∑ j : Fin 4, carrySrc D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x) +
          (∑ i ∈ A.pcs, pieceSrc D A i x) = D.Q.indicator D.g x := by
  have hcols := ae_atMostOne A.cols (A.col D) fun _ hi _ hj hne => hA.volume_col_inter h hi hj hne
  have hpcs := ae_atMostOne A.pcs (fun i => (A.pc i).carrier) fun _ hi _ hj hne =>
    hA.volume_pc_inter h hi hj hne
  have hcolid : ∀ᵐ x, ∀ jk ∈ A.cols, x ∈ A.col D jk →
      fluxSrc D A jk x + (A.fillRect D jk).carrier.indicator
        (fun x => 2 * π * A.cut.fillDensity D.c D.t D.d D.m D.ℓ D.g jk.1 jk.2 x) x =
        A.cut.src D.c D.t D.d D.g x :=
    (eventually_all_finset _).2 fun jk hjk => hA.ae_col_identity h hjk
  filter_upwards [hcols, hpcs, hcolid] with x hxc hxp hxid
  -- terms vanish off their columns
  have hflux0 : ∀ jk ∈ A.cols, x ∉ A.col D jk → fluxSrc D A jk x = 0 := fun jk _ hx =>
    indicator_of_notMem (fun h' => hx (Good.fluxRect_subset_col h h')) _
  have hpc0 : ∀ i ∈ A.pcs, x ∉ (A.pc i).carrier → pieceSrc D A i x = 0 := fun i _ hx =>
    indicator_of_notMem hx _
  by_cases hF : x ∈ frameSet D.c D.t D.d
  · obtain ⟨jk₀, hjk₀, hx₀⟩ := hA.exists_mem_col h hF
    rw [sum_eq_of_atMostOne hxc hflux0 hjk₀ hx₀]
    -- the pieces
    have hpiece : ∑ i ∈ A.pcs, pieceSrc D A i x = (A.fillRect D jk₀).carrier.indicator
        (fun x => 2 * π * A.cut.fillDensity D.c D.t D.d D.m D.ℓ D.g jk₀.1 jk₀.2 x) x := by
      by_cases hP : ∃ i ∈ A.pcs, x ∈ (A.pc i).carrier
      · obtain ⟨i₀, hi₀, hxi₀⟩ := hP
        have hcol : (i₀.1, i₀.2.1) = jk₀ :=
          hxc _ (Good.col_mem_cols hi₀) _ hjk₀ (hA.pc_subset_col hi₀ hxi₀) hx₀
        rw [sum_eq_of_atMostOne hxp hpc0 hi₀ hxi₀, pieceSrc, indicator_of_mem hxi₀, ← hcol,
          indicator_of_mem (hA.pc_subset_fillRect hi₀ hxi₀)]
        rfl
      · push Not at hP
        rw [sum_eq_zero_of_notMem hpc0 hP, indicator_of_notMem]
        intro hxF
        have hk₀ := mem_cols.1 hjk₀
        have hcov := (hA.filler jk₀.1 jk₀.2 hk₀).cover
        have hxF' : x ∈ (A.cut.fillRect D.c D.t D.d jk₀.1 jk₀.2).carrier := hxF
        rw [← hcov, mem_iUnion₂] at hxF'
        obtain ⟨p, hp, hxp'⟩ := hxF'
        exact hP (jk₀.1, jk₀.2, p) (mem_pcs.2 ⟨hk₀, hp⟩) hxp'
    rw [hpiece, add_right_comm, hxid jk₀ hjk₀ hx₀, indicator_of_mem (Data.Hyp.frameSet_subset_Q hF)]
    -- `g̃ + ∑ carries = g`
    simp only [ColumnCut.src, tildeG, carrySrc]
    ring_nf
  · have h1 : ∀ jk ∈ A.cols, x ∉ A.col D jk := fun jk hjk hx => hF (hA.col_subset_frame h hjk hx)
    have h2 : ∀ i ∈ A.pcs, x ∉ (A.pc i).carrier := fun i hi hx =>
      h1 _ (Good.col_mem_cols hi) (hA.pc_subset_col hi hx)
    rw [sum_eq_zero_of_notMem hflux0 h1, sum_eq_zero_of_notMem hpc0 h2,
      Finset.sum_eq_zero fun j _ => hA.carrySrc_eq_zero h hF]
    by_cases hQ : x ∈ D.Q
    · rw [indicator_of_mem hQ, h.g_eq_zero_of_lt]
      · ring
      · simp only [frameSet, mem_ofPred_eq, not_and_or, not_le] at hF
        rcases hF with hF | hF
        · exact absurd (Data.mem_Q_iff.1 hQ) (not_le.2 hF)
        · exact hF
    · rw [indicator_of_notMem hQ]; ring

/-! ### The field pieces -/

theorem isFieldPiece_Vflux : IsFieldPiece (A.Vflux D) ∅ fun x => ∑ jk ∈ A.cols, fluxSrc D A jk x := by
  have hs := isFieldPiece_finsetSum A.cols (Y := fun _ => (∅ : Finset ℂ))
    (fun jk hjk => h.cutHyp.isFieldPiece_fluxV hA.isCut (mem_cols.1 hjk))
    (fun _ _ _ _ _ => Finset.disjoint_empty_left _)
  have he : A.cols.biUnion (fun _ => (∅ : Finset ℂ)) = ∅ := by ext; simp [Finset.mem_biUnion]
  rw [he] at hs
  convert hs using 1
  · funext x; rw [Vflux, Finset.sum_apply]
  · funext x; rw [Finset.sum_apply]; rfl

theorem isFieldPiece_Vcarry :
    IsFieldPiece (A.Vcarry D) ∅
      fun x => ∑ j : Fin 4, carrySrc D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x := by
  have hs := isFieldPiece_finsetSum Finset.univ (Y := fun _ => (∅ : Finset ℂ))
    (fun j _ => isFieldPiece_carryField (c := D.c) (t := D.t) (d := D.d) (j := j)
      (θ := A.cut.θ j) (h.ℓ_pos.trans_le (hA.lastWidth_mem j).1))
    (fun _ _ _ _ _ => Finset.disjoint_empty_left _)
  have he : (Finset.univ : Finset (Fin 4)).biUnion (fun _ => (∅ : Finset ℂ)) = ∅ := by
    ext; simp [Finset.mem_biUnion]
  rw [he] at hs
  convert hs using 1
  · funext x; rw [Vcarry, Finset.sum_apply]
  · funext x; rw [Finset.sum_apply]

theorem isFieldPiece_Vpiece : IsFieldPiece (A.Vpiece D) A.Z fun x => ∑ i ∈ A.pcs, pieceSrc D A i x := by
  classical
  have hs := isFieldPiece_finsetSum A.pcs (Y := fun i => ({(A.pc i).centre} : Finset ℂ))
    (fun i hi => (hA.isFillerPiece h hi).isFieldPiece_pieceField h.r₀_pos h.r₀_le')
    (fun i hi i' hi' hne => Finset.disjoint_singleton.2 (hA.centre_ne h hi hi' hne))
  have hZ : A.pcs.biUnion (fun i => ({(A.pc i).centre} : Finset ℂ)) = A.Z := by
    ext y; simp [Z, Finset.mem_biUnion, Finset.mem_image, eq_comm]
  rw [hZ] at hs
  convert hs using 1
  · funext x; rw [Vpiece, Finset.sum_apply]; rfl
  · funext x; rw [Finset.sum_apply]; rfl

/-- `E'` is a field piece with charges `Y = K ∪ Z`. -/
theorem isFieldPiece_E' :
    IsFieldPiece (A.E' D) (A.Y D) fun x => D.rho0 x + ((∑ jk ∈ A.cols, fluxSrc D A jk x) +
      (∑ j : Fin 4, carrySrc D.c D.t D.d j (A.cut.θ j) (A.cut.lastWidth j) x) +
        (∑ i ∈ A.pcs, pieceSrc D A i x)) := by
  have h1 := (h.isFieldPiece_psiX.add (hA.isFieldPiece_Vflux h) (Finset.disjoint_empty_right _))
  rw [Finset.union_empty] at h1
  have h2 := h1.add (hA.isFieldPiece_Vcarry h) (Finset.disjoint_empty_right _)
  rw [Finset.union_empty] at h2
  have h3 := h2.add (hA.isFieldPiece_Vpiece h) (hA.disjoint_K_Z h)
  have hY : A.Y D = D.K ∪ A.Z := rfl
  have hE : A.E' D = D.psiX + A.Vflux D + A.Vcarry D + A.Vpiece D := by
    funext x; simp only [E', Pi.add_apply]
  rw [hY, hE]
  convert h3 using 1
  funext x; simp only [Pi.add_apply]; ring

/-- `E'` vanishes off `Q`. -/
theorem E'_eq_zero {x : ℂ} (hx : x ∉ D.Q) : A.E' D x = 0 := by
  have hF : x ∉ frameSet D.c D.t D.d := fun h' => hx (Data.Hyp.frameSet_subset_Q h')
  have hψ : D.psiX x = 0 := by
    rw [Data.psiX, Data.psi_eq_zero, zero_smul]
    rw [Data.mem_Q_iff, not_le] at hx; linarith [h.d_pos]
  have h1 : A.Vflux D x = 0 := Finset.sum_eq_zero fun jk hjk =>
    Good.fluxV_eq_zero h fun h' => hF (hA.col_subset_frame h hjk h')
  have h2 : A.Vcarry D x = 0 := Finset.sum_eq_zero fun j _ => hA.carryField_eq_zero h hF
  have h3 : A.Vpiece D x = 0 := Finset.sum_eq_zero fun i hi =>
    hA.Pfield_eq_zero h hi fun h' => hF (hA.col_subset_frame h (Good.col_mem_cols hi)
      (hA.pc_subset_col hi h'))
  rw [E', hψ, h1, h2, h3]; simp

/-- **Lemma 4.25**: `E'` is a Neumann charge field on `Q` with density `m` and charges `Y`. -/
theorem isNeumannChargeField : IsNeumannChargeField D.Q D.m (A.Y D) (A.E' D) := by
  refine (hA.isFieldPiece_E' h).isNeumannChargeField Data.measurableSet_Q
    (Eventually.of_forall fun x hx => hA.E'_eq_zero h hx) ?_
  filter_upwards [hA.src_ae_eq h] with x hx
  rw [hx]
  by_cases hQ : x ∈ D.Q
  · rw [indicator_of_mem hQ, indicator_of_mem hQ, Data.rho0_eq]; ring
  · rw [indicator_of_notMem hQ, indicator_of_notMem hQ, h.rho0_eq_zero_of_notMem_Q hQ, add_zero]

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
