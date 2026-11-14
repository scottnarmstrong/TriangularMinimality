/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ScreenNeumann

/-!
# The screened charges (screening note, Lemma 4.24)

The screening note, Lemma 4.24 (`lem:points`). For `A : Asm` with
`A.Good D` under `D.Hyp`, the screened charges `Y = K ∪ Z` and radii `ρ` (`α` on `K`, `r₀` on `Z`):

* `Good.card_Y`: `#Y = N` (the column masses `n_k` add up to `N - #K`, and the pieces have distinct
  centres);
* `Good.mem_interior_Q`, `Good.rho_mem`, `Good.closedBall_subset_interior`: `Y ⊆ int Q`,
  `0 < ρ ≤ ¼` and `B̄(y, ρ_y) ⊆ int Q`;
* `Good.rho_add_rho_le`: `ρ_y + ρ_{y'} ≤ |y - y'|` for distinct `y, y' ∈ Y` (kept charges by (H4);
  a kept and a new charge are `7` apart; new charges are `2r₀` apart).
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening

theorem Rect.isOpen_openCarrier (H : Rect) : IsOpen H.openCarrier :=
  (isOpen_Ioo.reProdIm isOpen_Ioo).preimage H.continuous_coords

namespace Scr

open Pinwheel

namespace Asm

variable {D : Data} {A : Asm}

theorem rho_of_mem_K {x : ℂ} (hx : x ∈ D.K) : Asm.rho D x = D.α x := by
  classical
  rw [rho, ite_eq_left_iff.2 fun h' => absurd hx h']

theorem rho_of_notMem_K {x : ℂ} (hx : x ∉ D.K) : Asm.rho D x = D.r₀ := by
  classical
  rw [rho, ite_eq_right_iff.2 fun h' => absurd h' hx]

theorem mem_Z {y : ℂ} : y ∈ A.Z ↔ ∃ i ∈ A.pcs, (A.pc i).centre = y := by
  rw [Z, Finset.mem_image]

namespace Good

variable (h : D.Hyp) (hA : A.Good D)
include h hA

theorem notMem_K_of_mem_Z {y : ℂ} (hy : y ∈ A.Z) : y ∉ D.K :=
  Finset.disjoint_right.1 (hA.disjoint_K_Z h) hy

omit h in
/-- The number of pieces is the sum of the column masses. -/
theorem card_pcs : A.pcs.card = ∑ jk ∈ A.cols, A.n jk.1 jk.2 := by
  classical
  rw [pcs, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun jk hjk => ?_
    rw [Finset.card_image_of_injective _ fun p p' hpp' => by simpa using hpp',
      (hA.filler jk.1 jk.2 (mem_cols.1 hjk)).card]
  · intro jk _ jk' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_image] at hi hi'
    obtain ⟨p, _, rfl⟩ := hi
    obtain ⟨p', _, he⟩ := hi'
    exact hne (Prod.ext (congrArg Prod.fst he).symm (congrArg (fun q => q.2.1) he).symm)

omit h hA in
theorem sum_cols {f : Fin 4 × ℕ → ℝ} :
    ∑ jk ∈ A.cols, f jk = ∑ j : Fin 4, ∑ k ∈ Finset.range (A.cut.K j), f (j, k) := by
  classical
  rw [cols, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_image fun k _ k' _ hkk' => by simpa using hkk']
  · intro j _ j' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_image] at hi hi'
    obtain ⟨k, _, rfl⟩ := hi
    obtain ⟨k', _, he⟩ := hi'
    exact hne (congrArg Prod.fst he).symm

omit h in
/-- `∑ n_k = N - #K`. -/
theorem sum_n : (∑ jk ∈ A.cols, (A.n jk.1 jk.2 : ℝ)) = (D.N : ℝ) - D.K.card := by
  have htot := hA.isCut.total
  have hmass : ∀ j, ∀ k ∈ Finset.range (A.cut.K j),
      ∫ z in A.cut.col D.c D.t D.d j k, A.cut.src D.c D.t D.d D.g z = 2 * π * A.n j k :=
    fun j k hk => (hA.mass j k (Finset.mem_range.1 hk)).2
  simp_rw [Finset.sum_congr rfl (hmass _)] at htot
  rw [sum_cols (f := fun jk => (A.n jk.1 jk.2 : ℝ))]
  have hπ : (2 * π) ≠ 0 := by positivity
  simp only [← Finset.mul_sum] at htot
  have := mul_left_cancel₀ hπ htot
  rw [this]; push_cast; ring

/-- The pieces have distinct centres: `#Z = #pcs`. -/
theorem card_Z : A.Z.card = A.pcs.card :=
  Finset.card_image_of_injOn fun i hi i' hi' he => by
    by_contra hne; exact hA.centre_ne h hi hi' hne he

/-- **`#Y = N`** (Lemma 4.24). -/
theorem card_Y : (A.Y D).card = D.N := by
  rw [Y, Finset.card_union_of_disjoint (hA.disjoint_K_Z h), hA.card_Z h, hA.card_pcs]
  have := hA.sum_n
  have hcast : ((∑ jk ∈ A.cols, A.n jk.1 jk.2 : ℕ) : ℝ) = (D.N : ℝ) - D.K.card := by
    push_cast; exact this
  have : ((D.K.card + ∑ jk ∈ A.cols, A.n jk.1 jk.2 : ℕ) : ℝ) = D.N := by
    push_cast at hcast ⊢; linarith
  exact_mod_cast this

theorem openCarrier_subset_interior {i : Fin 4 × ℕ × (ℕ × ℕ)} (hi : i ∈ A.pcs) :
    (A.pc i).openCarrier ⊆ interior D.Q :=
  interior_maximal ((A.pc i).openCarrier_subset_carrier.trans
    ((hA.pc_subset_col hi).trans ((hA.col_subset_frame h (Good.col_mem_cols hi)).trans
      Data.Hyp.frameSet_subset_Q))) (A.pc i).isOpen_openCarrier

theorem closedBall_subset_interior {y : ℂ} (hy : y ∈ A.Y D) :
    closedBall y (Asm.rho D y) ⊆ interior D.Q := by
  rw [Y, Finset.mem_union] at hy
  rcases hy with hK | hZ
  · rw [rho_of_mem_K hK]
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have h1 := Data.dep_le_add (D := D) y x
    rw [norm_sub_rev] at h1
    have h2 := (h.mem_K.1 hK).2
    have h3 := (h.hα y (h.K_subset_C hK)).2
    rw [Data.mem_interior_Q_iff]; linarith [h.d_pos]
  · rw [rho_of_notMem_K (hA.notMem_K_of_mem_Z h hZ)]
    obtain ⟨i, hi, rfl⟩ := mem_Z.1 hZ
    exact ((hA.isFillerPiece h hi).closedBall_subset_openCarrier h.r₀_pos h.r₀_le').trans
      (hA.openCarrier_subset_interior h hi)

theorem rho_mem {y : ℂ} (hy : y ∈ A.Y D) : 0 < Asm.rho D y ∧ Asm.rho D y ≤ 1 / 4 := by
  rw [Y, Finset.mem_union] at hy
  rcases hy with hK | hZ
  · rw [rho_of_mem_K hK]; exact h.hα y (h.K_subset_C hK)
  · rw [rho_of_notMem_K (hA.notMem_K_of_mem_Z h hZ)]; exact ⟨h.r₀_pos, h.r₀_le⟩

theorem mem_interior_Q {y : ℂ} (hy : y ∈ A.Y D) : y ∈ interior D.Q :=
  hA.closedBall_subset_interior h hy (mem_closedBall_self (hA.rho_mem h hy).1.le)

/-- **Separation** (Lemma 4.24): `ρ_y + ρ_{y'} ≤ |y - y'|` for distinct `y, y' ∈ Y`. -/
theorem rho_add_rho_le {y y' : ℂ} (hy : y ∈ A.Y D) (hy' : y' ∈ A.Y D) (hne : y ≠ y') :
    Asm.rho D y + Asm.rho D y' ≤ ‖y - y'‖ := by
  have hρ := hA.rho_mem h hy
  have hρ' := hA.rho_mem h hy'
  -- kept charges lie in the zone of (H4)
  have hKℓ : ∀ p ∈ D.K, p ∈ D.C ∩ sq D.c (D.t - 2 * D.ℓt) := fun p hp =>
    ⟨h.K_subset_C hp, mem_sq_iff_le_sqDepth.2 (by
      have := (h.mem_K.1 hp).2; rw [Data.dep_def] at this; linarith [h.d_ge])⟩
  -- a kept charge and a new one are `7` apart
  have hKZ : ∀ p ∈ D.K, ∀ z ∈ A.Z, 7 ≤ ‖p - z‖ := by
    intro p hp z hz
    obtain ⟨i, hi, rfl⟩ := mem_Z.1 hz
    have h1 := hA.dep_le_of_mem_pc h hi (hA.centre_mem_pc h hi)
    have h2 := Data.dep_le_add (D := D) p (A.pc i).centre
    linarith [(h.mem_K.1 hp).2]
  rw [Y, Finset.mem_union] at hy hy'
  rcases hy with hK | hZ <;> rcases hy' with hK' | hZ'
  · rw [rho_of_mem_K hK, rho_of_mem_K hK']
    exact h.hdisj y (hKℓ y hK) y' (hKℓ y' hK') hne
  · have := hKZ y hK y' hZ'; linarith [hρ.2, hρ'.2]
  · have := hKZ y' hK' y hZ; rw [norm_sub_rev] at this; linarith [hρ.2, hρ'.2]
  · rw [rho_of_notMem_K (hA.notMem_K_of_mem_Z h hZ), rho_of_notMem_K (hA.notMem_K_of_mem_Z h hZ')]
    obtain ⟨i, hi, rfl⟩ := mem_Z.1 hZ
    obtain ⟨i', hi', rfl⟩ := mem_Z.1 hZ'
    have hii' : i ≠ i' := fun he => hne (by rw [he])
    linarith [hA.two_mul_r₀_le h hi hi' hii']

end Good

end Asm

end Scr

end SandierSerfaty.Screening

end
