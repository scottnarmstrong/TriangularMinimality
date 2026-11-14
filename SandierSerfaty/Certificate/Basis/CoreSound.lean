/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Core
public import SandierSerfaty.Certificate.Basis.Sound
public import SandierSerfaty.Certificate.Basis.Deriv

/-!
# Soundness of the finite-core test (assertion A2)

`coreSegCheck_sound`: if the basis constants are valid and `coreSegCheck d j cells = true` (`j ≤ 5`), then for
every `t ∈ [κ_j, κ_{j+1}]`

  `|∑_{i ≤ 38} (Piece.u i j)'(t) + 1/t| + |∑ (Piece.u i j)''(t) - 1/t²| + |∑ (Piece.u i j)'''(t) + 2/t³|/2 < 6000`

(this is `|B̃₁|_{2,t}`, `B̃₁ = B̃' + 1/t`) and

  `∑_{i ≤ 38} (k_i + 1)³ (|D| + |D'| + |D''|/2 + |D'''|/6)(t) < 2·10⁶`  (`D = Piece.D i j`),

with the classical iterated derivatives of the pieces (`iteratedDeriv`). These are the two fields `B₁_lt` and
`D_lt` of the finite-core premise `Tails.FiniteCore`, written out (`pnormB₁ j t`, `pnormD j i t`):
`coreBounds_of_checks` gives them for every `j ≤ 5`, `t ∈ seg j`, `b ≤ t ≤ l`. The third field `|c_1| < 1`
is assertion A1 (`absLtOneB_sound`).

Ingredients: the basis soundness `basis_sound`; uniqueness of derivatives within a nondegenerate cell
(`jet3_eq_on_Icc`), which identifies the jet witnesses with the iterated derivatives of the pieces
(`jet3_iteratedDeriv`, the pieces being smooth on `(0, ∞)`) and with the explicit derivatives of `log`; the
endpoint magnitudes `magHi`; the covering test `coverB`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Calibration
open SandierSerfaty.Tails

/-! ### Jets on a nondegenerate cell -/

/-- Two jets of the same function on `[a, b]` (`a < b`) have the same witnesses on `[a, b]`. -/
theorem jet3_eq_on_Icc {a b : ℝ} (hab : a < b) {F F₁ F₂ F₃ G₁ G₂ G₃ : ℝ → ℝ}
    (hF : Jet3 (Icc a b) F F₁ F₂ F₃) (hG : Jet3 (Icc a b) F G₁ G₂ G₃) :
    ∀ x ∈ Icc a b, F₁ x = G₁ x ∧ F₂ x = G₂ x ∧ F₃ x = G₃ x := by
  have hu : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have s1 : ∀ x ∈ Icc a b, F₁ x = G₁ x := fun x hx => (hF.d0 x hx).unique (hG.d0 x hx)
  have s2 : ∀ x ∈ Icc a b, F₂ x = G₂ x := fun x hx =>
    (hu x hx).eq_deriv _ (hF.d1 x hx).hasDerivWithinAt
      ((hG.d1 x hx).hasDerivWithinAt.congr (fun y hy => s1 y hy) (s1 x hx))
  have s3 : ∀ x ∈ Icc a b, F₃ x = G₃ x := fun x hx =>
    (hu x hx).eq_deriv _ (hF.d2 x hx).hasDerivWithinAt
      ((hG.d2 x hx).hasDerivWithinAt.congr (fun y hy => s2 y hy) (s2 x hx))
  exact fun x hx => ⟨s1 x hx, s2 x hx, s3 x hx⟩

/-- A jet enclosure on a nondegenerate cell encloses any jet witnesses of the function. -/
theorem jetEncl_witness_mem {X : IV 128} (hlt : SInt.blt X.lo X.hi = true) {F G₁ G₂ G₃ : ℝ → ℝ}
    (hG : Jet3 {t | IV.Mem t X} F G₁ G₂ G₃) {J : IJet 128} (h : JetEncl {t | IV.Mem t X} F J) {t : ℝ}
    (ht : IV.Mem t X) :
    IV.Mem (F t) J.c0 ∧ IV.Mem (G₁ t) J.c1 ∧ IV.Mem (G₂ t / 2) J.c2 ∧ IV.Mem (G₃ t / 6) J.c3 := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := h
  rw [setOf_mem_eq_Icc] at hj hG
  have ht' : t ∈ Icc (((X.lo.toInt : ℤ) : ℝ) / 2 ^ 128) (((X.hi.toInt : ℤ) : ℝ) / 2 ^ 128) := by
    rw [← setOf_mem_eq_Icc]; exact ht
  obtain ⟨e1, e2, e3⟩ := jet3_eq_on_Icc (cell_lt hlt) hj hG t ht'
  obtain ⟨b0, b1, b2, b3⟩ := hb t ht
  exact ⟨b0, e1 ▸ b1, e2 ▸ b2, e3 ▸ b3⟩

/-- On an open set where `F` is `C³`, the iterated derivatives are jet witnesses. -/
theorem jet3_iteratedDeriv {F : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 3 F U) :
    Jet3 U F (iteratedDeriv 1 F) (iteratedDeriv 2 F) (iteratedDeriv 3 F) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · have := (differentiableAt_iteratedDeriv hU hF (m := 0) (by norm_num) hx).hasDerivAt
    simpa [iteratedDeriv_one] using this
  · have := (differentiableAt_iteratedDeriv hU hF (m := 1) (by norm_num) hx).hasDerivAt
    rwa [← iteratedDeriv_succ] at this
  · have := (differentiableAt_iteratedDeriv hU hF (m := 2) (by norm_num) hx).hasDerivAt
    rwa [← iteratedDeriv_succ] at this

theorem jet3_sum {U : Set ℝ} {ι : Type*} (s : Finset ι) {f f₁ f₂ f₃ : ι → ℝ → ℝ}
    (h : ∀ i ∈ s, Jet3 U (f i) (f₁ i) (f₂ i) (f₃ i)) :
    Jet3 U (fun x => ∑ i ∈ s, f i x) (fun x => ∑ i ∈ s, f₁ i x) (fun x => ∑ i ∈ s, f₂ i x)
      (fun x => ∑ i ∈ s, f₃ i x) :=
  ⟨fun x hx => HasDerivAt.fun_sum fun i hi => (h i hi).d0 x hx,
    fun x hx => HasDerivAt.fun_sum fun i hi => (h i hi).d1 x hx,
    fun x hx => HasDerivAt.fun_sum fun i hi => (h i hi).d2 x hx⟩

/-- The jet of `log` on `(0, ∞)`: `(1/t, -1/t², 2/t³)`. -/
theorem jet3_log : Jet3 (Ioi 0) Real.log (fun t => t⁻¹) (fun t => -t⁻¹ ^ 2) (fun t => 2 * t⁻¹ ^ 3) := by
  refine ⟨fun x hx => Real.hasDerivAt_log (ne_of_gt hx), fun x hx => ?_, fun x hx => ?_⟩
  · have := hasDerivAt_inv (ne_of_gt (show (0 : ℝ) < x from hx))
    refine this.congr_deriv ?_
    rw [inv_pow]
  · have := (hasDerivAt_inv_pow_succ (ne_of_gt (show (0 : ℝ) < x from hx)) 1).neg
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · push_cast; ring
    · simp

/-! ### Magnitudes -/

theorem magHi_eq {P : ℕ} (a : IV P) : magHi a = max a.lo.mag a.hi.mag := by
  unfold magHi
  cases h : Nat.ble a.lo.mag a.hi.mag
  · have := Nat.not_le.mp (fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; exact absurd h (by simp))
    simp [max_eq_left this.le]
  · simp [max_eq_right (Nat.le_of_ble_eq_true h)]

theorem abs_mul_le_magHi {P : ℕ} {x : ℝ} {a : IV P} (h : IV.Mem x a) : |x| * 2 ^ P ≤ (magHi a : ℝ) := by
  have hp := IV.two_pow_pos' P
  have h1 := abs_le_magR h
  unfold magR at h1
  rw [le_div_iff₀ hp] at h1
  refine h1.trans (le_of_eq ?_)
  rw [magHi_eq, ← Int.cast_abs, ← Int.cast_abs, SInt.abs_toInt, SInt.abs_toInt]
  push_cast
  rfl

theorem abs_le_magHi {P : ℕ} {x : ℝ} {a : IV P} (h : IV.Mem x a) : |x| ≤ (magHi a : ℝ) / 2 ^ P := by
  rw [le_div_iff₀ (IV.two_pow_pos' P)]; exact abs_mul_le_magHi h

theorem norm3_bound {X : IV 128} (hlt : SInt.blt X.lo X.hi = true) {F G₁ G₂ G₃ : ℝ → ℝ}
    (hG : Jet3 {t | IV.Mem t X} F G₁ G₂ G₃) {J : IJet 128} (h : JetEncl {t | IV.Mem t X} F J) {t : ℝ}
    (ht : IV.Mem t X) : |F t| + |G₁ t| + |G₂ t| / 2 + |G₃ t| / 6 ≤ (norm3 J : ℝ) / 2 ^ 128 := by
  obtain ⟨m0, m1, m2, m3⟩ := jetEncl_witness_mem hlt hG h ht
  have b0 := abs_le_magHi m0
  have b1 := abs_le_magHi m1
  have b2 := abs_le_magHi m2
  have b3 := abs_le_magHi m3
  rw [abs_div, abs_two] at b2
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)] at b3
  simp only [norm3, Nat.add_eq]
  push_cast
  rw [add_div, add_div, add_div]
  linarith

/-! ### The cell test -/

theorem dsLoop_length (cx : Ctx) (j : ℕ) : ∀ (mds : List ModeData) (tk : IJet 128),
    (dsLoop cx j mds tk).length = mds.length
  | [], _ => rfl
  | _ :: mds, tk => by simp [dsLoop, dsLoop_length cx j mds]

theorem ksOf_length : ∀ mds : List ModeData, (ksOf mds).length = mds.length
  | [] => rfl
  | _ :: mds => by simp [ksOf, ksOf_length mds]

theorem piece_jet3 {F : ℝ → ℝ} (hF : ContDiffOn ℝ ⊤ F (Ioi 0)) {X : IV 128} (hX : IV.posB X = true) :
    Jet3 {t | IV.Mem t X} F (iteratedDeriv 1 F) (iteratedDeriv 2 F) (iteratedDeriv 3 F) :=
  (jet3_iteratedDeriv isOpen_Ioi (hF.of_le (by norm_cast))).mono
    fun t ht => IV.posB_sound hX ht

/-- The weighted norm `(k_q + 1)³ |D_q|_{3,t}` of the piece `Piece.D q j`. -/
@[expose] noncomputable def dTerm (j : ℕ) (t : ℝ) (q : ℕ) : ℝ :=
  ((k q : ℝ) + 1) ^ 3 * (|Piece.D q j t| + |iteratedDeriv 1 (Piece.D q j) t| +
    |iteratedDeriv 2 (Piece.D q j) t| / 2 + |iteratedDeriv 3 (Piece.D q j) t| / 6)

theorem dsumLoop_bound {X : IV 128} (hX : IV.posB X = true) (hlt : SInt.blt X.lo X.hi = true) {j : ℕ}
    {t : ℝ} (ht : IV.Mem t X) :
    ∀ (ks : List ℕ) (ds : List (IJet 128)) (m : ℕ), KList m ks →
      JetEnclFrom {t | IV.Mem t X} (fun n => Piece.D n j) m ds → ks.length = ds.length →
      ∑ n ∈ Finset.range ds.length, dTerm j t (m + n) ≤ (dsumLoop ks ds : ℝ) / 2 ^ 128
  | [], [], _, _, _, _ => by simp [dsumLoop]
  | [], _ :: _, _, _, _, hl => by simp at hl
  | _ :: _, [], _, _, _, hl => by simp at hl
  | x :: ks, D :: ds, m, ⟨hx, hks⟩, ⟨hD, hds⟩, hl => by
    have ih := dsumLoop_bound hX hlt ht ks ds (m + 1) hks hds (by simpa using hl)
    have hb := norm3_bound hlt (piece_jet3 (contDiffOn_Piece_D m j) hX) hD ht
    subst hx
    have eD : ((dsumLoop (k m :: ks) (D :: ds) : ℕ) : ℝ) =
        ((k m : ℝ) + 1) ^ 3 * (norm3 D : ℝ) + (dsumLoop ks ds : ℝ) := by
      show ((Nat.add (Nat.mul (Nat.pow (Nat.add (k m) 1) 3) (norm3 D)) (dsumLoop ks ds) : ℕ) : ℝ) = _
      rw [Nat.add_eq, Nat.mul_eq, Nat.pow_eq, Nat.add_eq]
      push_cast; ring
    have hs : ∑ n ∈ Finset.range ds.length, dTerm j t (m + (n + 1)) =
        ∑ n ∈ Finset.range ds.length, dTerm j t (m + 1 + n) :=
      Finset.sum_congr rfl fun n _ => by rw [show m + (n + 1) = m + 1 + n by omega]
    rw [List.length_cons, Finset.sum_range_succ', hs, eD, add_div, add_zero]
    have hk : (0 : ℝ) ≤ ((k m : ℝ) + 1) ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left hb hk
    rw [mul_div_assoc'] at this
    have e0 : dTerm j t m = ((k m : ℝ) + 1) ^ 3 * (|Piece.D m j t| + |iteratedDeriv 1 (Piece.D m j) t| +
        |iteratedDeriv 2 (Piece.D m j) t| / 2 + |iteratedDeriv 3 (Piece.D m j) t| / 6) := rfl
    linarith

/-- **Soundness of the core test of one cell.** -/
theorem coreCellCheck_sound {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) {X : IV 128}
    (hc : coreCellCheck d j X = true) {t : ℝ} (ht : IV.Mem t X) :
    |∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) t + 1 / t| +
        |∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) t - 1 / t ^ 2| +
        |∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) t + 2 / t ^ 3| / 2 < 6000 ∧
      ∑ i ∈ Finset.range 39, ((k i : ℝ) + 1) ^ 3 *
        (|Piece.D i j t| + |iteratedDeriv 1 (Piece.D i j) t| + |iteratedDeriv 2 (Piece.D i j) t| / 2 +
          |iteratedDeriv 3 (Piece.D i j) t| / 6) < 2000000 := by
  simp only [coreCellCheck, coreOutCheck, Bool.and_eq_true] at hc
  obtain ⟨⟨hX, hlt⟩, h1, h2⟩ := hc
  have hT : ∀ s, IV.Mem s X → s ∈ Ioi (0 : ℝ) := fun s hs => IV.posB_sound hX hs
  obtain ⟨hB, hDs, hks⟩ := basis_sound hd hX hj
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  refine ⟨?_, ?_⟩
  · -- the jet of `B̃ + log t` and its witnesses
    have hA := hB.add ((JetEncl.var (T := {t | IV.Mem t X}) (x := X) fun s hs => hs).log hX)
    have hG : Jet3 {t | IV.Mem t X} (fun s => ∑ i ∈ Finset.range 39, Piece.u i j s + Real.log s)
        (fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) s + s⁻¹)
        (fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) s + -s⁻¹ ^ 2)
        (fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) s + 2 * s⁻¹ ^ 3) :=
      (jet3_sum _ fun i _ => piece_jet3 (contDiffOn_Piece_u i j) hX).add (jet3_log.mono hT)
    obtain ⟨-, m1, m2, m3⟩ := jetEncl_witness_mem hlt hG hA ht
    have b1 := abs_le_magHi m1
    have b2 := abs_le_magHi (IV.mem_mulNat m2 2)
    have b3 := abs_le_magHi (IV.mem_mulNat m3 3)
    have hN : ((norm2 (b1Jet (basis d j X) X) : ℕ) : ℝ) < 6000 * 2 ^ 128 := by
      rw [Nat.blt_eq, Nat.mul_eq, SInt.nat_shiftLeft_eq, one_mul] at h1
      exact_mod_cast h1
    simp only [norm2, b1Jet, IJet.der, Nat.add_eq] at hN
    push_cast at hN b2 b3
    have ht0 : 0 < t := hT t ht
    have e1 : (1 : ℝ) / t = t⁻¹ := one_div t
    have e2 : -(1 : ℝ) / t ^ 2 = -t⁻¹ ^ 2 := by field_simp
    have e3 : (2 : ℝ) / t ^ 3 = 2 * t⁻¹ ^ 3 := by field_simp
    rw [e1, sub_eq_add_neg, ← neg_div, e2, e3]
    have q2 : |(∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) t + -t⁻¹ ^ 2) / 2 * 2| =
        |∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) t + -t⁻¹ ^ 2| := by
      rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    have q3 : |(∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) t + 2 * t⁻¹ ^ 3) / 6 * 3| =
        |∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) t + 2 * t⁻¹ ^ 3| / 2 := by
      rw [show ∀ x : ℝ, x / 6 * 3 = x / 2 from fun x => by ring, abs_div, abs_two]
    rw [q2] at b2
    rw [q3] at b3
    have : ((magHi (IJet.add (basis d j X).bsum (IJet.log (IJet.var X))).c1 : ℕ) : ℝ) / 2 ^ 128 +
        ((magHi (IV.mulNat (IJet.add (basis d j X).bsum (IJet.log (IJet.var X))).c2 2) : ℕ) : ℝ) / 2 ^ 128 +
        ((magHi (IV.mulNat (IJet.add (basis d j X).bsum (IJet.log (IJet.var X))).c3 3) : ℕ) : ℝ) /
          2 ^ 128 < 6000 := by
      rw [← add_div, ← add_div, div_lt_iff₀ hp]; exact hN
    linarith
  · have hl : (basis d j X).ds.length = 39 := by
      simp [basis, basisWith, dsLoop_length, hd.len]
    have hlk : (basis d j X).ks.length = (basis d j X).ds.length := by
      simp [basis, basisWith, dsLoop_length, ksOf_length]
    have hb := dsumLoop_bound hX hlt ht _ _ 0 hks hDs hlk
    rw [hl] at hb
    simp only [zero_add, dTerm] at hb
    have hN : ((dsumLoop (basis d j X).ks (basis d j X).ds : ℕ) : ℝ) < 2000000 * 2 ^ 128 := by
      rw [Nat.blt_eq, Nat.mul_eq, SInt.nat_shiftLeft_eq, one_mul] at h2
      exact_mod_cast h2
    have : ((dsumLoop (basis d j X).ks (basis d j X).ds : ℕ) : ℝ) / 2 ^ 128 < 2000000 := by
      rw [div_lt_iff₀ hp]; exact hN
    linarith

/-! ### Covering and segments -/

theorem coverB_sound {P : ℕ} {a b : SInt} : ∀ (cells : List (IV P)), coverB a b cells = true →
    ∀ t : ℝ, ((a.toInt : ℤ) : ℝ) ≤ t * 2 ^ P → t * 2 ^ P ≤ ((b.toInt : ℤ) : ℝ) → ∃ X ∈ cells, IV.Mem t X
  | [], h, _, _, _ => by simp [coverB] at h
  | X :: rest, h, t, ha, hb => by
    simp only [coverB, Bool.and_eq_true, Bool.or_eq_true, SInt.ble_iff] at h
    obtain ⟨hXa, hor⟩ := h
    have hXa' : ((X.lo.toInt : ℤ) : ℝ) ≤ ((a.toInt : ℤ) : ℝ) := by exact_mod_cast hXa
    by_cases htX : t * 2 ^ P ≤ ((X.hi.toInt : ℤ) : ℝ)
    · exact ⟨X, List.mem_cons_self .., le_trans hXa' ha, htX⟩
    · rcases hor with hbX | hrest
      · have : ((b.toInt : ℤ) : ℝ) ≤ ((X.hi.toInt : ℤ) : ℝ) := by exact_mod_cast hbX
        exact absurd (hb.trans this) htX
      · obtain ⟨Y, hY, hm⟩ := coverB_sound rest hrest t (le_of_lt (not_le.mp htX)) hb
        exact ⟨Y, List.mem_cons_of_mem _ hY, hm⟩

theorem allCells_mem {d : BasisData} {j : ℕ} : ∀ {cells : List (IV 128)}, allCells d j cells = true →
    ∀ X ∈ cells, coreCellCheck d j X = true
  | [], _, _, hX => by simp at hX
  | Y :: rest, h, X, hX => by
    simp only [allCells, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hX with rfl | hX'
    · exact h.1
    · exact allCells_mem h.2 X hX'

theorem mem_knotIV {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) : IV.Mem (knot j) (knotIV d j) := by
  have h3 : IV.Mem (R₀ + 3 / 40) (IV.add d.r0 (frac false 3 40)) :=
    IV.mem_add hd.mr0 (by simpa using mem_frac_pos 3 40 (by norm_num))
  have h6 : IV.Mem (R₀ + 19 / 250) (IV.add d.r0 (frac false 19 250)) :=
    IV.mem_add hd.mr0 (by simpa using mem_frac_pos 19 250 (by norm_num))
  interval_cases j <;> simp only [knotIV, knot] <;> simp
  · simpa [b] using mem_frac_pos 28209 100000 (by norm_num)
  · exact hd.mpc
  · exact hd.mp
  · exact hd.mr0
  · simpa using hd.mr1
  · simpa [hs] using h3
  · simpa [l] using h6

/-- **Soundness of assertion A2 on segment `j`.** -/
theorem coreSegCheck_sound {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 5) {cells : List (IV 128)}
    (hc : coreSegCheck d j cells = true) {t : ℝ} (ht : t ∈ Icc (knot j) (knot (j + 1))) :
    |∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) t + 1 / t| +
        |∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) t - 1 / t ^ 2| +
        |∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) t + 2 / t ^ 3| / 2 < 6000 ∧
      ∑ i ∈ Finset.range 39, ((k i : ℝ) + 1) ^ 3 *
        (|Piece.D i j t| + |iteratedDeriv 1 (Piece.D i j) t| + |iteratedDeriv 2 (Piece.D i j) t| / 2 +
          |iteratedDeriv 3 (Piece.D i j) t| / 6) < 2000000 := by
  simp only [coreSegCheck, Bool.and_eq_true] at hc
  have hlo := (mem_knotIV hd (j := j) (by omega)).1
  have hhi := (mem_knotIV hd (j := j + 1) (by omega)).2
  have hp := IV.two_pow_pos' 128
  rw [show Nat.add j 1 = j + 1 from rfl] at hc
  obtain ⟨X, hX, htX⟩ := coverB_sound cells hc.1 t
    (hlo.trans (mul_le_mul_of_nonneg_right ht.1 hp.le))
    ((mul_le_mul_of_nonneg_right ht.2 hp.le).trans hhi)
  exact coreCellCheck_sound hd (by omega) (allCells_mem hc.2 X hX) htX

/-- **Assertion A2** in the form of the finite-core premise (`Tails.FiniteCore.B₁_lt`, `.D_lt` with
`pnormB₁`, `pnormD` written out): from the six segment checks, the bounds hold at every `t ∈ seg j ∩ [b, l]`,
`j ≤ 5`. -/
theorem coreBounds_of_checks {d : BasisData} (hd : d.Valid) {cells : ℕ → List (IV 128)}
    (hc : ∀ j, j ≤ 5 → coreSegCheck d j (cells j) = true) :
    ∀ j, j ≤ 5 → ∀ t ∈ seg j, b ≤ t → t ≤ l →
      |∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) t + 1 / t| +
          |∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) t - 1 / t ^ 2| +
          |∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) t + 2 / t ^ 3| / 2 < 6000 ∧
        ∑ i ∈ Finset.range 39, ((k i : ℝ) + 1) ^ 3 *
          (|Piece.D i j t| + |iteratedDeriv 1 (Piece.D i j) t| + |iteratedDeriv 2 (Piece.D i j) t| / 2 +
            |iteratedDeriv 3 (Piece.D i j) t| / 6) < 2000000 := by
  intro j hj t hts hb _
  refine coreSegCheck_sound hd hj (hc j hj) ?_
  interval_cases j
  · exact ⟨hb, hts.2⟩
  all_goals exact hts

end SandierSerfaty.Certificate.Basis
