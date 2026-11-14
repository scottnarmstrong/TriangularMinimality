/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.CoeffEval
public import SandierSerfaty.Certificate.Arith.IVLemmas
public import SandierSerfaty.Tails.Coefficient

/-!
# Soundness of the coefficient enclosures (assertion A1)

`coeffsCheck_sound`: if `coeffsCheck l h m₀ D cos = true` with `1 ≤ m₀` and `1 ≤ D`, the literal intervals
`cos` enclose `Cal.coeff m₀, Cal.coeff (m₀ + 1), …` (`EnclFrom`). The steps:

* `Z3.val`: `ℤ[√-3] → ℂ`, multiplicative (`Z3.val_mul`, `Z3.val_pow`);
* `cterm_eq`: for `x = (n, q) ≠ 0`, `Re (n ρ + q)^{-k} = 2^k X_k / W^k` with `X_k` the rational part of
  `(A + i√3 B)^k`, `A = n + 2q`, `B = n`, `W = A² + 3B²` (the integer form of `comp:coefficient-summand`);
* the loops `accTerms`, `rowLoop`, `boxLoop` accumulate enclosures of the partial sums, so `boxSums` encloses
  the box sum `boxSumR m D` (`enclFrom_boxSums`);
* `abs_coeff_sub_boxSumR_le`, the bound `tail:coefficient-square` of `Tails.abs_coeff_sub_boxSum_le` restated
  for the exposed box sum `boxSumR` (the body of `Tails.boxSum` is not exported), and `a^{-6m} = (√3/2)^{3m}`
  give the enclosure of `c_m` (`mem_coeffEncl`).

`absLtOneB_sound` turns the test `absLtOneB` into `|x| < 1`.
-/

open Complex Finset

public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Tails SandierSerfaty.Calibration
open SandierSerfaty.ClosedForm

variable {P : ℕ}

/-! ### `ℤ[√-3]` -/

/-- The complex value `re + i√3 im`. -/
@[expose] noncomputable def Z3.val (z : Z3) : ℂ :=
  ((z.re.toInt : ℤ) : ℂ) + I * ((√3 : ℝ) : ℂ) * ((z.im.toInt : ℤ) : ℂ)

theorem sqrt3_sq_C : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem Z3.val_mul (a b : Z3) : (Z3.mul a b).val = a.val * b.val := by
  simp only [Z3.val, Z3.mul, SInt.toInt_sub, SInt.toInt_mul, SInt.toInt_mulNat, SInt.toInt_add]
  push_cast
  linear_combination (-(((a.im.toInt : ℤ) : ℂ) * ((b.im.toInt : ℤ) : ℂ)) * I ^ 2) * sqrt3_sq_C +
    (-3 * ((a.im.toInt : ℤ) : ℂ) * ((b.im.toInt : ℤ) : ℂ)) * I_sq

theorem Z3.val_pow (a : Z3) (n : ℕ) : (Z3.pow a n).val = a.val ^ n := by
  induction n with
  | zero => simp [Z3.pow, Z3.one, Z3.val, SInt.toInt_mk]
  | succ n ih => rw [Z3.pow, Z3.val_mul, ih, pow_succ]

theorem Z3.re_val (z : Z3) : z.val.re = ((z.re.toInt : ℤ) : ℝ) := by
  simp [Z3.val]

theorem Z3.normSq_val (A B : SInt) :
    Complex.normSq (Z3.val ⟨A, B⟩) = ((A.toInt : ℤ) : ℝ) ^ 2 + 3 * ((B.toInt : ℤ) : ℝ) ^ 2 := by
  simp only [Z3.val, Complex.normSq_apply]
  simp
  have := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  nlinarith [this]

/-! ### The terms -/

/-- The summand `Re (n ρ + q)^{-6m}` of the box sums. -/
@[expose] noncomputable def cterm (m : ℕ) (x : ℤ × ℤ) : ℝ := ((((x.1 : ℂ) * rho + x.2) ^ (6 * m))⁻¹).re

/-- The box sum `∑_{|n|,|q| ≤ D} Re (n ρ + q)^{-6m}` (the exposed form of `Tails.boxSum`). -/
@[expose] noncomputable def boxSumR (m D : ℕ) : ℝ := ∑ x ∈ box D, cterm m x

theorem rho_point (x : ℤ × ℤ) {A B : SInt} (hA : A.toInt = x.1 + 2 * x.2) (hB : B.toInt = x.1) :
    (x.1 : ℂ) * rho + x.2 = Z3.val ⟨A, B⟩ / 2 := by
  rw [rho_eq]
  simp only [Z3.val, hA, hB]
  apply Complex.ext <;> simp <;> ring

theorem ptW_cast (A B : SInt) :
    ((ptW A B : ℕ) : ℝ) = ((A.toInt : ℤ) : ℝ) ^ 2 + 3 * ((B.toInt : ℤ) : ℝ) ^ 2 := by
  have hA : ((A.toInt : ℤ) : ℝ) ^ 2 = (A.mag : ℝ) ^ 2 := by
    rw [← sq_abs, ← Int.cast_abs, SInt.abs_toInt]; simp
  have hB : ((B.toInt : ℤ) : ℝ) ^ 2 = (B.mag : ℝ) ^ 2 := by
    rw [← sq_abs, ← Int.cast_abs, SInt.abs_toInt]; simp
  rw [hA, hB]
  simp [ptW]; ring

theorem cterm_eq (m : ℕ) (x : ℤ × ℤ) {A B : SInt} (hA : A.toInt = x.1 + 2 * x.2) (hB : B.toInt = x.1)
    {z : Z3} (hz : z.val = Z3.val ⟨A, B⟩ ^ (6 * m)) :
    cterm m x = (((SInt.shiftLeft z.re (6 * m)).toInt : ℤ) : ℝ) /
      ((Nat.pow (ptW A B) (6 * m) : ℕ) : ℝ) := by
  have hk : ((Z3.val ⟨A, B⟩ / 2) ^ (6 * m))⁻¹ = z.val⁻¹ * (((2 : ℝ) ^ (6 * m) : ℝ) : ℂ) := by
    rw [div_pow, inv_div, hz]; push_cast; ring
  unfold cterm
  rw [rho_point x hA hB, hk, Complex.re_mul_ofReal, Complex.inv_re, Z3.re_val, hz, map_pow, Z3.normSq_val,
    ← ptW_cast]
  simp only [SInt.toInt_shiftLeft, Nat.pow_eq]
  push_cast
  ring

theorem mem_termIV (m : ℕ) (x : ℤ × ℤ) {A B : SInt} (hA : A.toInt = x.1 + 2 * x.2) (hB : B.toInt = x.1)
    {z : Z3} (hz : z.val = Z3.val ⟨A, B⟩ ^ (6 * m)) (hW : ptW A B ≠ 0) :
    IV.Mem (cterm m x) (termIV z.re (6 * m) (ptW A B) : IV P) := by
  rw [cterm_eq m x hA hB hz]
  exact IV.mem_ofFrac _ (by rw [Nat.pow_eq]; exact Nat.pow_pos (Nat.pos_of_ne_zero hW))

/-! ### Enclosures of a sequence by a list -/

/-- The list `l` encloses `g m, g (m + 1), …` termwise. -/
@[expose] def EnclFrom (g : ℕ → ℝ) : ℕ → List (IV P) → Prop
  | _, [] => True
  | m, a :: as => IV.Mem (g m) a ∧ EnclFrom g (m + 1) as

theorem EnclFrom.congr {g g' : ℕ → ℝ} : ∀ {m : ℕ} {l : List (IV P)}, (∀ j, m ≤ j → g j = g' j) →
    EnclFrom g m l → EnclFrom g' m l
  | _, [], _, _ => trivial
  | m, a :: as, h, ⟨h1, h2⟩ =>
    ⟨h m le_rfl ▸ h1, EnclFrom.congr (fun j hj => h j (by omega)) h2⟩

theorem enclFrom_of_subsetList {g : ℕ → ℝ} : ∀ {m : ℕ} {as bs : List (IV P)}, subsetList as bs = true →
    EnclFrom g m as → EnclFrom g m bs
  | _, [], [], _, _ => trivial
  | _, [], _ :: _, h, _ => by simp [subsetList] at h
  | _, _ :: _, [], h, _ => by simp [subsetList] at h
  | m, a :: as, b :: bs, h, ⟨h1, h2⟩ => by
    simp only [subsetList, Bool.and_eq_true] at h
    exact ⟨IV.mem_of_subsetB h.1 h1, enclFrom_of_subsetList h.2 h2⟩

theorem enclFrom_zeros (m cnt : ℕ) : EnclFrom (fun _ => (0 : ℝ)) m (zeros cnt : List (IV P)) := by
  induction cnt generalizing m with
  | zero => trivial
  | succ n ih => exact ⟨by simp [IV.Mem, SInt.zero, SInt.toInt_mk], ih (m + 1)⟩

/-! ### The loops -/

theorem enclFrom_accTerms {g : ℕ → ℝ} (x : ℤ × ℤ) {A B : SInt} (hA : A.toInt = x.1 + 2 * x.2)
    (hB : B.toInt = x.1) (hW : ptW A B ≠ 0) :
    ∀ (accs : List (IV P)) (m : ℕ) (z : Z3), z.val = Z3.val ⟨A, B⟩ ^ (6 * m) → EnclFrom g m accs →
      EnclFrom (fun j => g j + cterm j x) m (accTerms (Z3.pow ⟨A, B⟩ 6) (ptW A B) z (6 * m) accs)
  | [], _, _, _, _ => trivial
  | a :: as, m, z, hz, ⟨h1, h2⟩ => by
    have e : Nat.add (6 * m) 6 = 6 * (m + 1) := by rw [Nat.add_eq]; ring
    have hz' : (Z3.mul z (Z3.pow ⟨A, B⟩ 6)).val = Z3.val ⟨A, B⟩ ^ (6 * (m + 1)) := by
      rw [Z3.val_mul, Z3.val_pow, hz, ← pow_add]; ring_nf
    have := enclFrom_accTerms x hA hB hW as (m + 1) _ hz' h2
    simp only [accTerms, e]
    exact ⟨IV.mem_add h1 (mem_termIV m x hA hB hz hW), this⟩

theorem ptW_eq_zero {A B : SInt} (h : ptW A B = 0) : A.toInt = 0 ∧ B.toInt = 0 := by
  have h' : A.mag * A.mag + 3 * (B.mag * B.mag) = 0 := h
  have h1 : A.mag = 0 := by
    rcases Nat.eq_zero_or_pos A.mag with h0 | h0
    · exact h0
    · have : 0 < A.mag * A.mag := Nat.mul_pos h0 h0
      omega
  have h2 : B.mag = 0 := by
    rcases Nat.eq_zero_or_pos B.mag with h0 | h0
    · exact h0
    · have : 0 < B.mag * B.mag := Nat.mul_pos h0 h0
      omega
  constructor
  · have := SInt.abs_toInt A; rw [h1] at this; simpa using this
  · have := SInt.abs_toInt B; rw [h2] at this; simpa using this

theorem cterm_zero {j : ℕ} (hj : 1 ≤ j) : cterm j (0, 0) = 0 := by
  simp [cterm, zero_pow (show 6 * j ≠ 0 by omega)]

theorem enclFrom_pointStep {g : ℕ → ℝ} {m0 : ℕ} (hm : 1 ≤ m0) (n q : SInt) {accs : List (IV P)}
    (h : EnclFrom g m0 accs) :
    EnclFrom (fun j => g j + cterm j (n.toInt, q.toInt)) m0 (pointStep m0 n q accs) := by
  have hA : (ptA n q).toInt = (n.toInt, q.toInt).1 + 2 * (n.toInt, q.toInt).2 := by
    simp [ptA]; ring
  have hB : n.toInt = (n.toInt, q.toInt).1 := rfl
  unfold pointStep pointStepAux
  rcases Nat.eq_zero_or_pos (ptW (ptA n q) n) with hW | hW
  · rw [hW]
    obtain ⟨e1, e2⟩ := ptW_eq_zero hW
    have hq : q.toInt = 0 := by rw [hA, e2] at e1; simp at e1; omega
    refine EnclFrom.congr (fun j hj => ?_) h
    rw [e2, hq, cterm_zero (by omega), add_zero]
  · have hW' : ptW (ptA n q) n ≠ 0 := hW.ne'
    have hb : Nat.beq (ptW (ptA n q) n) 0 = false :=
      Bool.eq_false_iff.mpr (fun h => hW' (Nat.eq_of_beq_eq_true h))
    rw [hb]
    exact enclFrom_accTerms (n.toInt, q.toInt) hA hB hW' accs m0 _
      (by rw [Z3.val_pow, Z3.val_pow, ← pow_mul]) h

theorem toInt_sub_nat (c D : ℕ) : (SInt.sub ⟨false, c⟩ ⟨false, D⟩).toInt = (c : ℤ) - D := by
  simp [SInt.toInt_mk]

theorem enclFrom_rowLoop {m0 : ℕ} (hm : 1 ≤ m0) (D : ℕ) (n : SInt) :
    ∀ (cnt : ℕ) (g : ℕ → ℝ) (accs : List (IV P)), EnclFrom g m0 accs →
      EnclFrom (fun j => g j + ∑ c ∈ range cnt, cterm j (n.toInt, (c : ℤ) - D)) m0
        (rowLoop m0 D n cnt accs)
  | 0, g, accs, h => by simpa [rowLoop] using h
  | c + 1, g, accs, h => by
    have h1 := enclFrom_pointStep hm n (SInt.sub ⟨false, c⟩ ⟨false, D⟩) h
    rw [toInt_sub_nat] at h1
    have := enclFrom_rowLoop hm D n c _ _ h1
    refine EnclFrom.congr (fun j _ => ?_) this
    rw [Finset.sum_range_succ _ c]; ring

theorem enclFrom_boxLoop {m0 : ℕ} (hm : 1 ≤ m0) (D : ℕ) :
    ∀ (cnt : ℕ) (g : ℕ → ℝ) (accs : List (IV P)), EnclFrom g m0 accs →
      EnclFrom (fun j => g j + ∑ c ∈ range cnt, ∑ c' ∈ range (2 * D + 1),
        cterm j ((c : ℤ) - D, (c' : ℤ) - D)) m0 (boxLoop m0 D cnt accs)
  | 0, g, accs, h => by simpa [boxLoop] using h
  | c + 1, g, accs, h => by
    have h1 := enclFrom_rowLoop hm D (SInt.sub ⟨false, c⟩ ⟨false, D⟩) (Nat.add (Nat.mul 2 D) 1) g accs h
    rw [toInt_sub_nat, show Nat.add (Nat.mul 2 D) 1 = 2 * D + 1 from rfl] at h1
    have := enclFrom_boxLoop hm D c _ _ h1
    refine EnclFrom.congr (fun j _ => ?_) this
    rw [Finset.sum_range_succ _ c]; ring

theorem sum_range_shift (f : ℤ → ℝ) (D : ℕ) :
    ∑ c ∈ range (2 * D + 1), f ((c : ℤ) - D) = ∑ i ∈ Icc (-(D : ℤ)) D, f i := by
  apply Finset.sum_nbij' (fun c : ℕ => (c : ℤ) - D) (fun i : ℤ => (i + D).toNat)
  · intro c hc; simp only [mem_range] at hc; simp only [mem_Icc]; omega
  · intro i hi; simp only [mem_Icc] at hi; simp only [mem_range]; omega
  · intro c _; simp
  · intro i hi; simp only [mem_Icc] at hi; omega
  · intro c _; rfl

theorem boxSumR_eq (m D : ℕ) :
    boxSumR m D =
      ∑ c ∈ range (2 * D + 1), ∑ c' ∈ range (2 * D + 1), cterm m ((c : ℤ) - D, (c' : ℤ) - D) := by
  unfold boxSumR Tails.box
  rw [sum_product, ← sum_range_shift]
  refine sum_congr rfl fun c _ => ?_
  rw [← sum_range_shift (fun i => cterm m ((c : ℤ) - D, i))]

/-- The box sums enclose `boxSumR m D` for `m = m₀, …, m₀ + cnt - 1`. -/
theorem enclFrom_boxSums {m0 : ℕ} (hm : 1 ≤ m0) (cnt D : ℕ) :
    EnclFrom (fun j => boxSumR j D) m0 (boxSums m0 cnt D : List (IV P)) := by
  have := enclFrom_boxLoop hm D (Nat.add (Nat.mul 2 D) 1) _ _ (enclFrom_zeros (P := P) m0 cnt)
  refine EnclFrom.congr (fun j _ => ?_) this
  rw [boxSumR_eq, zero_add]; rfl

/-! ### The tail and the coefficient -/

/-- `tail:coefficient-square` for the box sum: `Tails.abs_coeff_sub_boxSum_le` restated for the exposed
`boxSumR` (same proof). -/
theorem abs_coeff_sub_boxSumR_le {m D : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) :
    |coeff m - (a ^ (6 * m))⁻¹ * boxSumR m D / ((6 * m : ℕ) : ℝ)| ≤
      (1 / ((6 * m : ℕ) * a ^ (6 * m))) *
        (8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ)) := by
  set f : ℤ × ℤ → ℂ := fun v => (((v.1 : ℂ) * rho + v.2) ^ (6 * m))⁻¹ with hf
  have hnorm : ∀ v, ‖f v‖ = hexTerm m v := norm_hexTerm m
  set g : ℤ × ℤ → ℂ := fun v => if D < supIdx v then f v else 0 with hg
  set h : ℤ × ℤ → ℂ := fun v => if supIdx v ≤ D then f v else 0 with hh
  have hfgh : ∀ v, f v = g v + h v := fun v => by
    by_cases hv : D < supIdx v
    · simp [hg, hh, hv, not_le.2 hv]
    · simp [hg, hh, hv, not_lt.1 hv]
  have hnormg : ∀ v, ‖g v‖ = tailTerm m D v := fun v => by
    by_cases hv : D < supIdx v
    · simp [hg, tailTerm, hv, hnorm]
    · simp [hg, tailTerm, hv]
  have hsg : Summable g := Summable.of_norm
    (by simpa only [hnormg] using (coefficient_square (D := D) hm hD).1)
  have hsh : Summable h := summable_of_ne_finset_zero (s := Tails.box D) fun x hx => by
    rw [mem_box] at hx; simp [hh, hx]
  have hth : ∑' v, h v = ∑ x ∈ Tails.box D, f x := by
    rw [tsum_eq_sum (s := Tails.box D)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [mem_box] at hx; simp [hh, hx]
    · intro x hx; rw [mem_box] at hx; simp [hh, hx]
  have hG : ClosedForm.hexPair.G (6 * m) = ∑ x ∈ Tails.box D, f x + ∑' v, g v := by
    rw [hexG_eq_tsum_prod]
    have : ∑' v, f v = ∑' v, g v + ∑' v, h v := by
      rw [← hsg.tsum_add hsh]; exact tsum_congr hfgh
    rw [this, hth]; ring
  have hre : (triPair.G (6 * m)).re = (a ^ (6 * m))⁻¹ * (boxSumR m D + (∑' v, g v).re) := by
    rw [triPair_G, hG]
    have : ((a : ℂ) ^ (6 * m))⁻¹ = (((a ^ (6 * m))⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.re_ofReal_mul, Complex.add_re, Complex.re_sum]
    rfl
  have hT : ‖∑' v, g v‖ ≤ 8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ) := by
    refine (norm_tsum_le_tsum_norm
      (by simpa only [hnormg] using (coefficient_square (D := D) hm hD).1)).trans ?_
    simp only [hnormg]
    exact (coefficient_square hm hD).2
  have hpos : (0 : ℝ) < ((6 * m : ℕ) : ℝ) := by positivity
  have := a_pos
  have hpa : (0 : ℝ) < (a ^ (6 * m))⁻¹ := by positivity
  have e : coeff m - (a ^ (6 * m))⁻¹ * boxSumR m D / ((6 * m : ℕ) : ℝ) =
      (a ^ (6 * m))⁻¹ * (∑' v, g v).re / ((6 * m : ℕ) : ℝ) := by
    unfold coeff
    rw [hre]; ring
  rw [e, abs_div, abs_of_pos hpos, abs_mul, abs_of_pos hpa, div_le_iff₀ hpos]
  have h1 : |(∑' v, g v).re| ≤ ‖∑' v, g v‖ := Complex.abs_re_le_norm _
  calc (a ^ (6 * m))⁻¹ * |(∑' v, g v).re|
      ≤ (a ^ (6 * m))⁻¹ * (8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (h1.trans hT) hpa.le
    _ = _ := by field_simp

theorem mem_ivPow {y : ℝ} {a : IV P} (ha : IV.Mem y a) : ∀ n, IV.Mem (y ^ n) (ivPow a n)
  | 0 => by simpa [ivPow] using IV.mem_ofNat (P := P) 1
  | n + 1 => by rw [pow_succ]; exact IV.mem_mul (mem_ivPow ha n) ha

theorem a_inv_pow (m : ℕ) : (a ^ (6 * m))⁻¹ = (√3 / 2) ^ (3 * m) := by
  rw [show 6 * m = 2 * (3 * m) by ring, pow_mul, a_sq, ← inv_pow, inv_div]

theorem tailRad_ge {m D : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D) :
    8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ) * 2 ^ P ≤ (tailRad P m D : ℝ) := by
  have h62 : 0 < 6 * m - 2 := by omega
  set den : ℕ := 3 ^ (3 * m) * D ^ (6 * m - 2) * (6 * m - 2) with hden
  have hd : 0 < den := by rw [hden]; positivity
  have key := SInt.le_cdivNat_mul (8 * 4 ^ (3 * m) * 2 ^ P) den hd
  have hdR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hd
  have key' : ((8 * 4 ^ (3 * m) * 2 ^ P : ℕ) : ℝ) / den ≤ (SInt.cdivNat (8 * 4 ^ (3 * m) * 2 ^ P) den : ℝ) := by
    rw [div_le_iff₀ hdR]; exact_mod_cast key
  have e : tailRad P m D = SInt.cdivNat (8 * 4 ^ (3 * m) * 2 ^ P) den := by
    simp only [tailRad, hden, SInt.nat_shiftLeft_eq, Nat.pow_eq, Nat.mul_eq, Nat.sub_eq]
  rw [e]
  refine le_of_eq_of_le ?_ key'
  rw [hden]
  have hD' : (0 : ℝ) < (D : ℝ) ^ (6 * m - 2) := by positivity
  have h6 : (0 : ℝ) < ((6 * m - 2 : ℕ) : ℝ) := by exact_mod_cast h62
  simp only [shellK]
  push_cast
  rw [div_pow]
  field_simp

theorem mem_coeffEncl {s3h : IV P} (hs : IV.Mem (√3 / 2) s3h) {m D : ℕ} (hm : 1 ≤ m) (hD : 1 ≤ D)
    {S : IV P} (hS : IV.Mem (boxSumR m D) S) : IV.Mem (coeff m) (coeffEncl s3h m D S) := by
  have := a_pos
  have hd0 : (0 : ℝ) < ((6 * m : ℕ) : ℝ) := by positivity
  have had : 0 < a ^ (6 * m) := by positivity
  set d : ℝ := ((6 * m : ℕ) : ℝ) with hd
  set t : ℝ := coeff m * d * a ^ (6 * m) - boxSumR m D with ht
  have hbound := abs_coeff_sub_boxSumR_le hm hD
  have htE : |t| ≤ 8 * shellK m * (((D : ℝ) ^ (6 * m - 2))⁻¹) / ((6 * m - 2 : ℕ) : ℝ) := by
    have e : t = (coeff m - (a ^ (6 * m))⁻¹ * boxSumR m D / d) * (d * a ^ (6 * m)) := by
      rw [ht]; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < d * a ^ (6 * m))]
    have := mul_le_mul_of_nonneg_right hbound (by positivity : (0 : ℝ) ≤ d * a ^ (6 * m))
    refine this.trans (le_of_eq ?_)
    rw [hd]; field_simp
  have h1 : IV.Mem (boxSumR m D + t) (IV.addRad S (tailRad P m D)) := by
    refine IV.mem_addRad hS ?_
    rw [add_sub_cancel_left]
    exact (mul_le_mul_of_nonneg_right htE (IV.two_pow_pos' P).le).trans (tailRad_ge hm hD)
  have h2 := IV.mem_divNat h1 (show 0 < Nat.mul 6 m by simp only [Nat.mul_eq]; omega)
  have h3 := IV.mem_mul (mem_ivPow hs (Nat.mul 3 m)) h2
  unfold coeffEncl
  have e1 : boxSumR m D + t = coeff m * d * a ^ (6 * m) := by rw [ht]; ring
  have e2 : ((Nat.mul 6 m : ℕ) : ℝ) = d := rfl
  rw [e1, e2, show Nat.mul 3 m = 3 * m from rfl, ← a_inv_pow] at h3
  convert h3 using 1
  field_simp

theorem enclFrom_coeffsFrom {s3h : IV P} (hs : IV.Mem (√3 / 2) s3h) {D : ℕ} (hD : 1 ≤ D) :
    ∀ {m : ℕ} {Ss : List (IV P)}, 1 ≤ m → EnclFrom (fun j => boxSumR j D) m Ss →
      EnclFrom coeff m (coeffsFrom s3h D m Ss)
  | _, [], _, _ => trivial
  | m, S :: Ss, hm, ⟨h1, h2⟩ =>
    ⟨mem_coeffEncl hs hm hD h1, enclFrom_coeffsFrom hs hD (by omega) h2⟩

/-- **Soundness of assertion A1** (one block): if `coeffsCheck l h m₀ D cos = true`, `1 ≤ m₀` and `1 ≤ D`,
then `cos` encloses `coeff m₀, coeff (m₀ + 1), …`. -/
theorem coeffsCheck_sound {l h m0 D : ℕ} {cos : List (IV P)} (hc : coeffsCheck l h m0 D cos = true)
    (hm : 1 ≤ m0) (hD : 1 ≤ D) : EnclFrom coeff m0 cos := by
  simp only [coeffsCheck, Bool.and_eq_true] at hc
  have h3 := IV.mem_sqrt_of_sqrtCheck hc.1 (IV.mem_ofNat (P := P) 3)
  have hs : IV.Mem (√3 / 2) (sqrt3Half l h : IV P) := by
    have := IV.mem_divPow2 (by simpa using h3) 1
    simpa [sqrt3Half] using this
  exact enclFrom_of_subsetList hc.2 (enclFrom_coeffsFrom hs hD hm (enclFrom_boxSums hm _ D))

/-- The test `|c_1| < 1`. -/
theorem absLtOneB_sound {x : ℝ} {a : IV P} (h : absLtOneB a = true) (ha : IV.Mem x a) : |x| < 1 := by
  simp only [absLtOneB, Bool.and_eq_true, SInt.blt_iff, SInt.toInt_mk] at h
  have hp := IV.two_pow_pos' P
  obtain ⟨h1, h2⟩ := ha
  have e : ((Nat.shiftLeft 1 P : ℕ) : ℝ) = 2 ^ P := by rw [SInt.nat_shiftLeft_eq]; push_cast; ring
  have l1 : -(2 : ℝ) ^ P < ((a.lo.toInt : ℤ) : ℝ) := by
    have : ((-(Nat.shiftLeft 1 P : ℤ) : ℤ) : ℝ) < ((a.lo.toInt : ℤ) : ℝ) := by exact_mod_cast h.1
    push_cast at this; rw [e] at this; linarith
  have l2 : ((a.hi.toInt : ℤ) : ℝ) < 2 ^ P := by
    have : ((a.hi.toInt : ℤ) : ℝ) < ((Nat.shiftLeft 1 P : ℕ) : ℝ) := by exact_mod_cast h.2
    rwa [e] at this
  rw [abs_lt]
  constructor <;> nlinarith

end SandierSerfaty.Certificate.Basis
