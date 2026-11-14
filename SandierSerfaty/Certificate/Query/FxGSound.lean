/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.FxG
public import SandierSerfaty.Certificate.Query.FxGReal
public import SandierSerfaty.Certificate.Query.Table
public import SandierSerfaty.Tails.Uniform

/-!
# The static error budget of the value-`G` query

`evalG_sound`: if every cell of the table is valid (`Query.CellValid`: the Taylor data approximate the truncated
`f̃₀`, `ẽ` with radii `rf/2^128`, `re/2^128` on the range they serve), `λ̂, μ̂` approximate the exact `λ, μ` within
`rlam`, `rmu`, and the finite-core premise holds (it transfers `f̃₀, ẽ` to the infinite-mode `f₀, e` with error
`< 10⁻¹¹`, `Tails.uniform_error_of_finiteCore`), then for every dyadic `(d, s)` with `d ≥ b` and every query
`evalG T lam mu i d s = some v`,

  `|v - G(d, s)| ≤ deltaG rf re rlam rmu = (rf + re)/(b·2^128) + (2ε + rmu + rlam/4)/b + 2^-60`,   `ε = 10⁻¹¹`.

This is the error budget `δ_G = A_max (r_f + ι_f + ε) + B_max (r_e + ι_e + ε) + c 2^{-P}` with `A_max = B_max = 1/b`
(the interpolation bounds `ι` are inside the cell radii `rf`, `re`, checked once per cell by
`Query.Cell.cellCheck`) and the radii of `λ̂, μ̂`; the rounding allowance is `2^-60` (the proof gives `2^-87`).
No query is evaluated on intervals: only the cell and square-root checks of `evalG` and the table validity are
used.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The error budget of one value-`G` query. -/
@[expose] noncomputable def deltaG (rf re : ℕ) (rlam rmu : ℝ) : ℝ :=
  ((rf : ℝ) / 2 ^ 128 + (re : ℝ) / 2 ^ 128 + 2 * epsTail + rmu + rlam / 4) / Calibration.b + 1 / 2 ^ 60

/-! ### Unfolding the checks -/

theorem evalAt_some {T : QTable} {lam mu : Fx 128} {i : ℕ} {d ss T2 t v : Fx 128}
    (h : evalAt T lam mu i d ss T2 t = some v) :
    i < T.n ∧ inRange (T.cell i) t = true ∧ v = evalCell (T.cell i) lam mu d ss T2 t := by
  unfold evalAt at h
  cases h1 : Nat.blt i T.n <;> simp only [h1, Bool.cond_false, Bool.cond_true] at h
  · exact absurd h (by simp)
  · cases h2 : inRange (T.cell i) t <;> simp only [h2, Bool.cond_false, Bool.cond_true] at h
    · exact absurd h (by simp)
    · exact ⟨Nat.blt_eq.mp h1, rfl, (Option.some.inj h).symm⟩

theorem evalWith_some {T : QTable} {lam mu : Fx 128} {i : ℕ} {d ss T2 v : Fx 128} {s : ℕ}
    (h : evalWith T lam mu i d ss T2 s = some v) :
    Fx.sqrtCheck T2 s = true ∧ evalAt T lam mu i d ss T2 (Fx.ofSInt ⟨false, s⟩) = some v := by
  unfold evalWith at h
  cases h1 : Fx.sqrtCheck T2 s <;> simp only [h1, Bool.cond_false, Bool.cond_true] at h
  · exact absurd h (by simp)
  · exact ⟨rfl, h⟩

theorem margin_val : (margin : Fx 128).val = 16 / 2 ^ 128 := by
  simp [margin, Fx.val_def]

theorem inRange_sound {c : QCell} {t : Fx 128} (h : inRange c t = true) :
    c.lo.val + 16 / 2 ^ 128 ≤ t.val ∧ t.val + 16 / 2 ^ 128 ≤ c.hi.val := by
  simp only [inRange, Bool.and_eq_true, Fx.ble_iff, Fx.val_add, margin_val] at h
  exact h

theorem mag_ne_zero_of_pos {a : Fx 128} (h : 0 < a.val) : a.v.mag ≠ 0 := by
  intro h0
  have : a.v.toInt = 0 := by
    have := SInt.abs_toInt a.v
    rw [h0] at this
    simpa using this
  rw [Fx.val_def, this] at h
  simp at h

/-! ### The error of the Taylor value, of the adjustment and of the combination -/

theorem taylorVal_err (b f1 tb th : Fx 128) {t : ℝ} (hf1 : |f1.val| ≤ 2 ^ 20)
    (ht : |th.val - t| ≤ 9 * (1 / 2 ^ 128)) :
    |(taylorVal b f1 tb th).val - (b.val + f1.val * (t - tb.val))| ≤ 2 ^ 24 * (1 / 2 ^ 128) := by
  have h1 := Fx.abs_val_mul_sub_lt f1 (Fx.sub th tb)
  simp only [Fx.val_sub] at h1
  have e : (taylorVal b f1 tb th).val - (b.val + f1.val * (t - tb.val)) =
      ((Fx.mul f1 (Fx.sub th tb)).val - f1.val * (th.val - tb.val)) + f1.val * (th.val - t) := by
    simp only [taylorVal, Fx.val_add]; ring
  rw [e]
  have h2 : |f1.val * (th.val - t)| ≤ 2 ^ 20 * (9 * (1 / 2 ^ 128)) := by
    rw [abs_mul]; exact mul_le_mul hf1 ht (abs_nonneg _) (by norm_num)
  have h3 : (1 : ℝ) / 2 ^ 128 > 0 := by positivity
  calc _ ≤ |(Fx.mul f1 (Fx.sub th tb)).val - f1.val * (th.val - tb.val)| + |f1.val * (th.val - t)| :=
        abs_add_le _ _
    _ ≤ 1 / 2 ^ 128 + 2 ^ 20 * (9 * (1 / 2 ^ 128)) := add_le_add h1.le h2
    _ ≤ 2 ^ 24 * (1 / 2 ^ 128) := by nlinarith

theorem taylorVal_abs (b f1 tb th : Fx 128) (hb : |b.val| ≤ 2 ^ 8) (hf1 : |f1.val| ≤ 2 ^ 20)
    (htb : |tb.val| ≤ 1) (hth : |th.val| ≤ 1) : |(taylorVal b f1 tb th).val| ≤ 2 ^ 22 := by
  have h1 := Fx.abs_val_mul_sub_lt f1 (Fx.sub th tb)
  simp only [Fx.val_sub] at h1
  have h2 : |f1.val * (th.val - tb.val)| ≤ 2 ^ 20 * 2 := by
    rw [abs_mul]
    refine mul_le_mul hf1 ?_ (abs_nonneg _) (by norm_num)
    exact (abs_sub _ _).trans (by linarith)
  have h3 : (1 : ℝ) / 2 ^ 128 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have e : (taylorVal b f1 tb th).val = b.val + (Fx.mul f1 (Fx.sub th tb)).val := by
    simp only [taylorVal, Fx.val_add]
  rw [e]
  have h4 : |(Fx.mul f1 (Fx.sub th tb)).val| ≤ 2 ^ 20 * 2 + 1 := by
    have := abs_sub_abs_le_abs_sub (Fx.mul f1 (Fx.sub th tb)).val (f1.val * (th.val - tb.val))
    have h5 := h1.le
    linarith
  calc _ ≤ |b.val| + |(Fx.mul f1 (Fx.sub th tb)).val| := abs_add_le _ _
    _ ≤ 2 ^ 22 := by norm_num at *; linarith

theorem adjustF_err (lam mu T2 fv : Fx 128) :
    |(adjustF lam mu T2 fv).val - (fv.val - lam.val * T2.val / 2 - mu.val)| ≤ 2 * (1 / 2 ^ 128) := by
  have h1 := Fx.abs_val_mul_sub_lt lam T2
  have h2 := Fx.abs_val_divPow2_sub_lt (Fx.mul lam T2) 1
  have e : (adjustF lam mu T2 fv).val - (fv.val - lam.val * T2.val / 2 - mu.val) =
      -(((Fx.divPow2 (Fx.mul lam T2) 1).val - (Fx.mul lam T2).val / 2 ^ 1) +
        ((Fx.mul lam T2).val - lam.val * T2.val) / 2) := by
    simp only [adjustF, Fx.val_sub]; ring
  rw [e, abs_neg]
  have h3 : |((Fx.mul lam T2).val - lam.val * T2.val) / 2| ≤ 1 / 2 ^ 128 / 2 := by
    rw [abs_div, abs_two]; exact div_le_div_of_nonneg_right h1.le (by norm_num)
  have h4 : (0 : ℝ) < 1 / 2 ^ 128 := by positivity
  calc _ ≤ |(Fx.divPow2 (Fx.mul lam T2) 1).val - (Fx.mul lam T2).val / 2 ^ 1| +
        |((Fx.mul lam T2).val - lam.val * T2.val) / 2| := abs_add_le _ _
    _ ≤ 1 / 2 ^ 128 + 1 / 2 ^ 128 / 2 := add_le_add h2.le h3
    _ ≤ 2 * (1 / 2 ^ 128) := by linarith

/-! ### The error theorem -/

theorem exact_G_eq {d s : ℝ} (hd : 0 < d) :
    G d s = (d * f (tt d s) - s ^ 2 / d * e (tt d s)) / tt d s ^ 2 := by
  have ht : 0 < tt d s := tt_pos hd
  unfold G
  field_simp

/-- **Stage A: the square root.** `T2 ≈ t²` within `2u` and the checked root is within `9u` of `t = tt d s`. -/
theorem sqrt_stage {d s dd ss T2 : Fx 128} {sN : ℕ} (hd : Calibration.b ≤ d.val)
    (hdd : |dd.val - d.val * d.val| ≤ 1 / 2 ^ 128) (hss : |ss.val - s.val * s.val| ≤ 1 / 2 ^ 128)
    (hT2 : T2 = Fx.add dd ss) (hsq : Fx.sqrtCheck T2 sN = true) :
    |T2.val - tt d.val s.val ^ 2| ≤ 2 * (1 / 2 ^ 128) ∧
      |(Fx.ofSInt ⟨false, sN⟩ : Fx 128).val - tt d.val s.val| ≤ 9 * (1 / 2 ^ 128) := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / 2 ^ 128 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu100 : u ≤ 1 / 2 ^ 100 := by
    rw [hu]; exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hu1000 : u ≤ 1 / 1000 := hu100.trans (by norm_num)
  have hbq : (1 : ℝ) / 4 ≤ Calibration.b := by unfold Calibration.b; norm_num
  rw [← hu] at hdd hss ⊢
  have hdv0 : 0 < d.val := by linarith
  have hT2v : |T2.val - (d.val ^ 2 + s.val ^ 2)| ≤ 2 * u := by
    rw [hT2, Fx.val_add]
    have : dd.val + ss.val - (d.val ^ 2 + s.val ^ 2) = (dd.val - d.val * d.val) + (ss.val - s.val * s.val) := by
      ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith only [hdd, hss]
  have ht2 : tt d.val s.val ^ 2 = d.val ^ 2 + s.val ^ 2 := tt_sq hdv0
  have hdt : d.val ≤ tt d.val s.val := by
    rw [tt]
    exact Real.le_sqrt_of_sq_le (by nlinarith only [sq_nonneg s.val])
  have ht0 : 0 < tt d.val s.val := by linarith only [hdt, hdv0]
  have hτ16 : 1 / 16 ≤ tt d.val s.val ^ 2 := by nlinarith only [hdt, hbq, hd]
  refine ⟨by rw [ht2]; exact hT2v, ?_⟩
  have hT2lo : 0 ≤ T2.val := by
    have := (abs_le.1 hT2v).1
    nlinarith only [this, ht2, hτ16, hu1000]
  have h1 := Fx.abs_sqrt_sub_lt_of_sqrtCheck hsq
  rw [← hu] at h1
  have h2 := abs_sqrt_sub_sqrt_le hT2lo (show 0 < d.val ^ 2 + s.val ^ 2 by nlinarith only [hτ16, ht2])
  have hts : Real.sqrt (d.val ^ 2 + s.val ^ 2) = tt d.val s.val := by
    rw [← ht2]; exact Real.sqrt_sq ht0.le
  rw [hts] at h2
  have h3 : |T2.val - (d.val ^ 2 + s.val ^ 2)| / tt d.val s.val ≤ 8 * u := by
    rw [div_le_iff₀ ht0]
    nlinarith only [hT2v, hdt, hbq, hd, hu0]
  have : (Fx.ofSInt ⟨false, sN⟩ : Fx 128).val - tt d.val s.val =
      ((Fx.ofSInt ⟨false, sN⟩ : Fx 128).val - Real.sqrt T2.val) + (Real.sqrt T2.val - tt d.val s.val) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  linarith only [h1.le, h2.trans h3]

/-- The cell range puts `t ∈ [b, l]` and `|th| ≤ 1`. -/
theorem range_stage {c : QCell} {rf re : ℕ} (hcv : CellValid c rf re) {th : Fx 128} {t : ℝ}
    (hlot : c.lo.val ≤ t) (hhit : t ≤ c.hi.val) (hth : |th.val - t| ≤ 9 * (1 / 2 ^ 128)) :
    Calibration.b ≤ t ∧ t ≤ 7 / 10 ∧ |th.val| ≤ 1 := by
  obtain ⟨hbt, htl⟩ := hcv.rng t hlot hhit
  have hbl := Calibration.l_lt
  have hu : (1 : ℝ) / 2 ^ 128 ≤ 1 / 1000 :=
    (one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num :
      (100 : ℕ) ≤ 128))).trans (by norm_num)
  have hbq : (1 : ℝ) / 4 ≤ Calibration.b := by unfold Calibration.b; norm_num
  have h1 := abs_le.1 hth
  refine ⟨hbt, by linarith only [htl, hbl], ?_⟩
  rw [abs_le]; constructor <;> linarith only [h1.1, h1.2, hu, hbt, hbq, htl, hbl]

/-- **Stage B: the adjusted radial function.** -/
theorem fa_stage (hc : FiniteCore) {c : QCell} {rf re : ℕ} (hcv : CellValid c rf re)
    {lam mu T2 th : Fx 128} {rlam rmu : ℝ} {t : ℝ} (hlot : c.lo.val ≤ t) (hhit : t ≤ c.hi.val)
    (hth : |th.val - t| ≤ 9 * (1 / 2 ^ 128)) (hT2 : |T2.val - t ^ 2| ≤ 2 * (1 / 2 ^ 128))
    (hlam : |Calibration.lam - lam.val| ≤ rlam) (hmu : |Calibration.mu - mu.val| ≤ rmu)
    (hlam8 : |lam.val| ≤ 8) (hmu8 : |mu.val| ≤ 8) :
    |(adjustF lam mu T2 (taylorVal c.fb c.f1 c.tb th)).val - Calibration.f t| ≤
        (rf : ℝ) / 2 ^ 128 + epsTail + rlam / 4 + rmu + (2 ^ 24 + 10) * (1 / 2 ^ 128) ∧
      |(adjustF lam mu T2 (taylorVal c.fb c.f1 c.tb th)).val| ≤ 2 ^ 23 := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / 2 ^ 128 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu100 : u ≤ 1 / 2 ^ 100 := by
    rw [hu]; exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hu1000 : u ≤ 1 / 1000 := hu100.trans (by norm_num)
  rw [← hu] at hth hT2 ⊢
  obtain ⟨hbt, ht7, hthabs⟩ := range_stage (th := th) hcv hlot hhit (by rw [← hu]; exact hth)
  have hbq : (1 : ℝ) / 4 ≤ Calibration.b := by unfold Calibration.b; norm_num
  have ht0 : 0 < t := by linarith only [hbt, hbq]
  have htl : t ≤ Calibration.l := (hcv.rng t hlot hhit).2
  obtain ⟨uf, -⟩ := uniform_error_of_finiteCore hc ⟨hbt, htl⟩
  have hfvT := taylorVal_err c.fb c.f1 c.tb th hcv.f1_cap (t := t) (by rw [← hu]; exact hth)
  rw [← hu] at hfvT
  have hfvA := taylorVal_abs c.fb c.f1 c.tb th hcv.fb_cap hcv.f1_cap hcv.tb_cap hthabs
  have hadj := adjustF_err lam mu T2 (taylorVal c.fb c.f1 c.tb th)
  rw [← hu] at hadj
  obtain ⟨fv, hfvdef⟩ : ∃ fv, fv = taylorVal c.fb c.f1 c.tb th := ⟨_, rfl⟩
  rw [← hfvdef] at hfvT hfvA hadj ⊢
  obtain ⟨fa, hfadef⟩ : ∃ fa, fa = adjustF lam mu T2 fv := ⟨_, rfl⟩
  rw [← hfadef] at hadj ⊢
  have ht2le : t ^ 2 ≤ 1 / 2 := by
    have := pow_le_pow_left₀ ht0.le ht7 2
    linarith only [this]
  have hT2le : T2.val ≤ 1 := by
    have := (abs_le.1 hT2).2
    linarith only [this, ht2le, hu1000]
  have hρl0 : 0 ≤ rlam := (abs_nonneg _).trans hlam
  have hρf0 : 0 ≤ (rf : ℝ) / 2 ^ 128 := by positivity
  have happ := hcv.f_app t hlot hhit
  have hff : Calibration.f t = f₀ t - Calibration.lam * t ^ 2 / 2 - Calibration.mu := rfl
  have e1 : fa.val - Calibration.f t =
      (fa.val - (fv.val - lam.val * T2.val / 2 - mu.val)) + (fv.val - Trunc.f₀ t) +
      (Trunc.f₀ t - f₀ t) + ((Calibration.lam - lam.val) * t ^ 2 / 2) +
      (lam.val * (t ^ 2 - T2.val) / 2) + (Calibration.mu - mu.val) := by
    rw [hff]; ring
  have b1 : |fv.val - Trunc.f₀ t| ≤ (rf : ℝ) / 2 ^ 128 + 2 ^ 24 * u := by
    have : fv.val - Trunc.f₀ t = (fv.val - (c.fb.val + c.f1.val * (t - c.tb.val))) -
        (Trunc.f₀ t - (c.fb.val + c.f1.val * (t - c.tb.val))) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    linarith only [hfvT, happ]
  have b2 : |Trunc.f₀ t - f₀ t| ≤ epsTail := by rw [abs_sub_comm]; exact uf.le
  have b3 : |(Calibration.lam - lam.val) * t ^ 2 / 2| ≤ rlam / 4 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg t), abs_two]
    have h1 : |Calibration.lam - lam.val| * t ^ 2 ≤ rlam * (1 / 2) :=
      mul_le_mul hlam ht2le (sq_nonneg t) hρl0
    linarith only [h1]
  have b4 : |lam.val * (t ^ 2 - T2.val) / 2| ≤ 8 * u := by
    rw [abs_div, abs_mul, abs_two, abs_sub_comm]
    have h1 : |lam.val| * |T2.val - t ^ 2| ≤ 8 * (2 * u) :=
      mul_le_mul hlam8 hT2 (abs_nonneg _) (by norm_num)
    linarith only [h1]
  refine ⟨?_, ?_⟩
  · rw [e1]
    have hs := abs_add_le (fa.val - (fv.val - lam.val * T2.val / 2 - mu.val) + (fv.val - Trunc.f₀ t) +
        (Trunc.f₀ t - f₀ t) + ((Calibration.lam - lam.val) * t ^ 2 / 2) + (lam.val * (t ^ 2 - T2.val) / 2))
      (Calibration.mu - mu.val)
    have hs2 := abs_add_le (fa.val - (fv.val - lam.val * T2.val / 2 - mu.val) + (fv.val - Trunc.f₀ t) +
        (Trunc.f₀ t - f₀ t) + ((Calibration.lam - lam.val) * t ^ 2 / 2)) (lam.val * (t ^ 2 - T2.val) / 2)
    have hs3 := abs_add_le (fa.val - (fv.val - lam.val * T2.val / 2 - mu.val) + (fv.val - Trunc.f₀ t) +
        (Trunc.f₀ t - f₀ t)) ((Calibration.lam - lam.val) * t ^ 2 / 2)
    have hs4 := abs_add_le (fa.val - (fv.val - lam.val * T2.val / 2 - mu.val) + (fv.val - Trunc.f₀ t))
        (Trunc.f₀ t - f₀ t)
    have hs5 := abs_add_le (fa.val - (fv.val - lam.val * T2.val / 2 - mu.val)) (fv.val - Trunc.f₀ t)
    linarith only [hs, hs2, hs3, hs4, hs5, hadj, b1, b2, b3, b4, hmu]
  · have hlt : |lam.val * T2.val / 2| ≤ 4 := by
      have ht2lo : (1 : ℝ) / 16 ≤ t ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (hbq.trans hbt) 2
        linarith only [this]
      rw [abs_div, abs_mul, abs_two, abs_of_nonneg (by linarith only [(abs_le.1 hT2).1, ht2lo, hu1000] :
        (0 : ℝ) ≤ T2.val)]
      nlinarith only [hlam8, hT2le, abs_nonneg lam.val]
    have h1 := abs_sub_abs_le_abs_sub fa.val (fv.val - lam.val * T2.val / 2 - mu.val)
    have h2 : |fv.val - lam.val * T2.val / 2 - mu.val| ≤ 2 ^ 22 + 4 + 8 := by
      refine (abs_sub _ _).trans ?_
      have := abs_sub (fv.val) (lam.val * T2.val / 2)
      linarith only [this, hfvA, hlt, hmu8]
    have : (2 : ℝ) ^ 22 + 4 + 8 + 2 * u ≤ 2 ^ 23 := by
      have : (2 : ℝ) ^ 23 = 2 * 2 ^ 22 := by norm_num
      nlinarith only [hu1000, this]
    linarith only [h1, h2, hadj, this]

/-- **Stage C: the angular coefficient.** -/
theorem ev_stage (hc : FiniteCore) {c : QCell} {rf re : ℕ} (hcv : CellValid c rf re) {th : Fx 128} {t : ℝ}
    (hlot : c.lo.val ≤ t) (hhit : t ≤ c.hi.val) (hth : |th.val - t| ≤ 9 * (1 / 2 ^ 128)) :
    |(taylorVal c.eb c.e1 c.tb th).val - Calibration.e t| ≤
        (re : ℝ) / 2 ^ 128 + epsTail + 2 ^ 24 * (1 / 2 ^ 128) ∧
      |(taylorVal c.eb c.e1 c.tb th).val| ≤ 2 ^ 23 := by
  obtain ⟨hbt, ht7, hthabs⟩ := range_stage (th := th) hcv hlot hhit hth
  have htl : t ≤ Calibration.l := (hcv.rng t hlot hhit).2
  obtain ⟨-, ue, -⟩ := uniform_error_of_finiteCore hc ⟨hbt, htl⟩
  have hevT := taylorVal_err c.eb c.e1 c.tb th hcv.e1_cap hth
  have hevA := taylorVal_abs c.eb c.e1 c.tb th hcv.eb_cap hcv.e1_cap hcv.tb_cap hthabs
  have happ := hcv.e_app t hlot hhit
  refine ⟨?_, hevA.trans (by norm_num)⟩
  have : (taylorVal c.eb c.e1 c.tb th).val - Calibration.e t =
      ((taylorVal c.eb c.e1 c.tb th).val - (c.eb.val + c.e1.val * (t - c.tb.val))) -
      (Trunc.e t - (c.eb.val + c.e1.val * (t - c.tb.val))) + (Trunc.e t - Calibration.e t) := by ring
  rw [this]
  have h2 : |Trunc.e t - Calibration.e t| ≤ epsTail := by rw [abs_sub_comm]; exact ue.le
  have h3 := abs_add_le (((taylorVal c.eb c.e1 c.tb th).val - (c.eb.val + c.e1.val * (t - c.tb.val))) -
      (Trunc.e t - (c.eb.val + c.e1.val * (t - c.tb.val)))) (Trunc.e t - Calibration.e t)
  have h4 := abs_sub ((taylorVal c.eb c.e1 c.tb th).val - (c.eb.val + c.e1.val * (t - c.tb.val)))
      (Trunc.e t - (c.eb.val + c.e1.val * (t - c.tb.val)))
  linarith only [h3, h4, h2, hevT, happ]

/-- **The error theorem, core**: from the stages. -/
theorem evalAt_sound (hc : FiniteCore) {T : QTable} {rf re : ℕ}
    (hT : ∀ i, i < T.n → CellValid (T.cell i) rf re) {lam mu : Fx 128} {rlam rmu : ℝ}
    (hlam : |Calibration.lam - lam.val| ≤ rlam) (hmu : |Calibration.mu - mu.val| ≤ rmu)
    (hlam8 : |lam.val| ≤ 8) (hmu8 : |mu.val| ≤ 8)
    (hsmall : (rf : ℝ) / 2 ^ 128 + (re : ℝ) / 2 ^ 128 + rlam + rmu ≤ 1 / 2)
    {i : ℕ} {d s dd ss T2 v : Fx 128} {sN : ℕ} (hd : Calibration.b ≤ d.val)
    (hdd : |dd.val - d.val * d.val| ≤ 1 / 2 ^ 128) (hss : |ss.val - s.val * s.val| ≤ 1 / 2 ^ 128)
    (hT2 : T2 = Fx.add dd ss) (hsq : Fx.sqrtCheck T2 sN = true)
    (hat : evalAt T lam mu i d ss T2 (Fx.ofSInt ⟨false, sN⟩) = some v) :
    |v.val - Calibration.G d.val s.val| ≤ deltaG rf re rlam rmu := by
  obtain ⟨hi, hrg, hveq⟩ := evalAt_some hat
  have hcv := hT i hi
  obtain ⟨hT2v, hth⟩ := sqrt_stage hd hdd hss hT2 hsq
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / 2 ^ 128 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu100 : u ≤ 1 / 2 ^ 100 := by
    rw [hu]; exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hu1000 : u ≤ 1 / 1000 := hu100.trans (by norm_num)
  have e16 : (16 : ℝ) / 2 ^ 128 = 16 * u := by rw [hu]; ring
  have hbq : (1 : ℝ) / 4 ≤ Calibration.b := by unfold Calibration.b; norm_num
  obtain ⟨hlo, hhi⟩ := inRange_sound hrg
  rw [e16] at hlo hhi
  obtain ⟨th, hthdef⟩ : ∃ th : Fx 128, th = Fx.ofSInt ⟨false, sN⟩ := ⟨_, rfl⟩
  rw [← hthdef] at hth hlo hhi hat hveq
  rw [← hu] at hth hT2v
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = tt d.val s.val := ⟨_, rfl⟩
  rw [← htdef] at hth hT2v
  have hlot : (T.cell i).lo.val ≤ t := by have := (abs_le.1 hth).2; linarith only [this, hlo, hu0]
  have hhit : t ≤ (T.cell i).hi.val := by have := (abs_le.1 hth).1; linarith only [this, hhi, hu0]
  have hth' : |th.val - t| ≤ 9 * (1 / 2 ^ 128) := by rw [← hu]; exact hth
  have hT2' : |T2.val - t ^ 2| ≤ 2 * (1 / 2 ^ 128) := by rw [← hu]; exact hT2v
  obtain ⟨hfa, hfaM⟩ := fa_stage hc hcv hlot hhit hth' hT2' hlam hmu hlam8 hmu8
  obtain ⟨hev, hevM⟩ := ev_stage hc hcv hlot hhit hth'
  obtain ⟨hbt, ht7, -⟩ := range_stage (th := th) hcv hlot hhit hth'
  rw [← hu] at hfa hev
  -- the evaluated quantities
  have hdv0 : 0 < d.val := by linarith only [hd, hbq]
  have hdt : d.val ≤ t := by
    rw [htdef, tt]
    exact Real.le_sqrt_of_sq_le (by nlinarith only [sq_nonneg s.val])
  have ht2 : t ^ 2 = d.val ^ 2 + s.val ^ 2 := by rw [htdef]; exact tt_sq hdv0
  have ht0 : 0 < t := by linarith only [hdt, hdv0]
  have hτ16 : (1 : ℝ) / 16 ≤ t ^ 2 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 4) (hbq.trans hbt) 2
    linarith only [this]
  have hT2pos : 0 < T2.val := by linarith only [(abs_le.1 hT2v).1, hτ16, hu1000]
  obtain ⟨fa, hfadef⟩ : ∃ fa : Fx 128, fa = adjustF lam mu T2 (taylorVal (T.cell i).fb (T.cell i).f1
      (T.cell i).tb th) := ⟨_, rfl⟩
  obtain ⟨ev, hevdef⟩ : ∃ ev : Fx 128, ev = taylorVal (T.cell i).eb (T.cell i).e1 (T.cell i).tb th :=
    ⟨_, rfl⟩
  rw [← hfadef] at hfa hfaM
  rw [← hevdef] at hev hevM
  have hv : v = combG d ss T2 fa ev := by rw [hveq, evalCell, hfadef, hevdef]
  -- the rounding steps
  have hA := Fx.abs_val_mul_sub_lt d fa
  have hq0 := Fx.abs_val_div_sub_lt ss d (mag_ne_zero_of_pos hdv0)
  have hB := Fx.abs_val_mul_sub_lt (Fx.div ss d) ev
  have hV := Fx.abs_val_div_sub_lt (Fx.sub (Fx.mul d fa) (Fx.mul (Fx.div ss d) ev)) T2
    (mag_ne_zero_of_pos hT2pos)
  have hv' : v = Fx.div (Fx.sub (Fx.mul d fa) (Fx.mul (Fx.div ss d) ev)) T2 := hv
  rw [← hv', Fx.val_sub] at hV
  rw [← hu] at hA hq0 hB hV hss
  have hq : |(Fx.div ss d).val - s.val ^ 2 / d.val| ≤ 5 * u := by
    have e : ss.val / d.val - s.val ^ 2 / d.val = (ss.val - s.val * s.val) / d.val := by ring
    have h1 : |ss.val / d.val - s.val ^ 2 / d.val| ≤ 4 * u := by
      rw [e, abs_div, abs_of_pos hdv0, div_le_iff₀ hdv0]
      nlinarith only [hss, hd, hbq, hu0]
    have h2 := abs_add_le ((Fx.div ss d).val - ss.val / d.val) (ss.val / d.val - s.val ^ 2 / d.val)
    have e2 : (Fx.div ss d).val - s.val ^ 2 / d.val =
        ((Fx.div ss d).val - ss.val / d.val) + (ss.val / d.val - s.val ^ 2 / d.val) := by ring
    rw [e2]
    linarith only [h2, hq0.le, h1]
  -- the radii
  have hεv : epsTail = 1 / 10 ^ 11 := rfl
  have hε0 : 0 < epsTail := by rw [hεv]; positivity
  have hεs : epsTail ≤ 1 / 1000 := by rw [hεv]; norm_num
  have hρf0 : 0 ≤ (rf : ℝ) / 2 ^ 128 := by positivity
  have hρe0 : 0 ≤ (re : ℝ) / 2 ^ 128 := by positivity
  have hρl0 : 0 ≤ rlam := (abs_nonneg _).trans hlam
  have hρm0 : 0 ≤ rmu := (abs_nonneg _).trans hmu
  have hK : (2 ^ 24 + 10 : ℝ) * u ≤ 1 / 1000 := by
    have : (2 ^ 24 + 10 : ℝ) * u ≤ (2 ^ 24 + 10) * (1 / 2 ^ 100) := mul_le_mul_of_nonneg_left hu100 (by positivity)
    exact this.trans (by norm_num)
  have hK' : (2 ^ 24 : ℝ) * u ≤ 1 / 1000 := by
    have : (0 : ℝ) ≤ 10 * u := by positivity
    linarith only [hK, this]
  have hc1 := combine_error (u := u) (dv := d.val) (sv := s.val) (t := t) (f := Calibration.f t)
    (e := Calibration.e t) (T2 := T2.val) (A := (Fx.mul d fa).val) (q := (Fx.div ss d).val)
    (Bq := (Fx.mul (Fx.div ss d) ev).val) (fa := fa.val) (ev := ev.val) (V := v.val)
    (bb := Calibration.b) (ρF := (rf : ℝ) / 2 ^ 128 + epsTail + rlam / 4 + rmu + (2 ^ 24 + 10) * u)
    (ρE := (re : ℝ) / 2 ^ 128 + epsTail + 2 ^ 24 * u) hu0 hu100 hbq hd hdt ht7 ht2 hT2v hfa hev
    (by linarith only [hsmall, hεs, hK, hρf0, hρe0, hρl0, hρm0]) (by linarith only [hsmall, hεs, hK', hρf0, hρe0, hρl0, hρm0])
    hfaM hevM hA.le hq hB.le hV.le
  rw [exact_G_eq hdv0, ← htdef]
  refine hc1.trans ?_
  unfold deltaG
  have hb0 : 0 < Calibration.b := by linarith only [hbq]
  have hsplit : ((rf : ℝ) / 2 ^ 128 + epsTail + rlam / 4 + rmu + (2 ^ 24 + 10) * u +
      ((re : ℝ) / 2 ^ 128 + epsTail + 2 ^ 24 * u)) / Calibration.b =
      ((rf : ℝ) / 2 ^ 128 + (re : ℝ) / 2 ^ 128 + 2 * epsTail + rmu + rlam / 4) / Calibration.b +
        (2 ^ 25 + 10) * u / Calibration.b := by ring
  rw [hsplit]
  have h1 : (2 ^ 25 + 10 : ℝ) * u / Calibration.b ≤ 4 * ((2 ^ 25 + 10) * u) := by
    rw [div_le_iff₀ hb0]
    have : (0 : ℝ) ≤ (2 ^ 25 + 10) * u := by positivity
    nlinarith only [hbq, this]
  have h2 : 4 * ((2 ^ 25 + 10 : ℝ) * u) + 2 ^ 40 * u ≤ 1 / 2 ^ 60 := by
    rw [hu]; norm_num
  linarith only [h1, h2]

/-- **The static error budget of the value-`G` query**: every successful query
`evalG T lam mu i d s = some v` at a dyadic point with `d ≥ b` is within `deltaG` of the exact
`Calibration.G`, given valid cells, `λ̂, μ̂` within `rlam, rmu` of the exact constants, and the finite-core
premise (`Tails.uniform_error_of_finiteCore`). -/
theorem evalG_sound (hc : FiniteCore) {T : QTable} {rf re : ℕ}
    (hT : ∀ i, i < T.n → CellValid (T.cell i) rf re) {lam mu : Fx 128} {rlam rmu : ℝ}
    (hlam : |Calibration.lam - lam.val| ≤ rlam) (hmu : |Calibration.mu - mu.val| ≤ rmu)
    (hlam8 : |lam.val| ≤ 8) (hmu8 : |mu.val| ≤ 8)
    (hsmall : (rf : ℝ) / 2 ^ 128 + (re : ℝ) / 2 ^ 128 + rlam + rmu ≤ 1 / 2)
    {i : ℕ} {d s v : Fx 128} (hd : Calibration.b ≤ d.val) (hv : evalG T lam mu i d s = some v) :
    |v.val - Calibration.G d.val s.val| ≤ deltaG rf re rlam rmu := by
  unfold evalG evalG0 evalG1 at hv
  obtain ⟨hsq, hat⟩ := evalWith_some hv
  exact evalAt_sound hc hT hlam hmu hlam8 hmu8 hsmall hd
    (by have := Fx.abs_val_mul_sub_lt d d; exact this.le)
    (by have := Fx.abs_val_mul_sub_lt s s; exact this.le) rfl hsq hat

end SandierSerfaty.Certificate.Query
