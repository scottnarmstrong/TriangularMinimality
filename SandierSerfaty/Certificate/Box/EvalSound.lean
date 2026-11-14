/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Eval
public import SandierSerfaty.Certificate.Query.FxGSound
public import SandierSerfaty.Calibration.Exterior

/-!
# Soundness of the box evaluator (`Box.Eval`): the static error budget of one value of `G`

* `evalExt_sound`: for `t² ≥ l²` the exterior formula `evalExt` evaluates `G(d, s) = dκ + d c/(d² + s²)` within
  `deltaExt rκ rc = rκ + 4 rc + 2⁻¹⁰⁰` (rounding allowance included), given `κ̂ ≈ κ`, `ĉ ≈ c`;
* `G_exterior_eq`: the exact identity `G(d, s) = dκ + d c/(d² + s²)` for `√(d² + s²) ≥ l` (`tail:exterior-formula`);
* `evalMid_sound`: `|v - G(d, s)| ≤ max (deltaG …) (deltaExt …)` for every successful `evalMid` (the exterior branch
  or `Query.evalG_sound`);
* `midVal_sound`: the value at the midpoint of cell `j` of a row is within that bound of `G(dm/2^128,
  (σ_j + σ_{j+1})/2)`, with `σ_k = sm k/2^128`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The exterior slope `κ = -π B(l) - λ/2` and the exterior constant `c = f(l) - κ l²`. -/
@[expose] noncomputable def extSlope : ℝ := -Real.pi * B l - lam / 2

/-- `c = f(l) - κ l²`. -/
@[expose] noncomputable def extConst : ℝ := f l - extSlope * l ^ 2

/-- The error budget of one exterior value. -/
@[expose] noncomputable def deltaExt (rκ rc : ℝ) : ℝ := rκ + 4 * rc + 1 / 2 ^ 100

/-- **`G` on the exterior** (`t ≥ l`): `G(d, s) = dκ + d c/(d² + s²)`. -/
theorem G_exterior_eq {d s : ℝ} (hd : 0 < d) (ht : l ≤ tt d s) :
    G d s = d * extSlope + d * extConst / (d ^ 2 + s ^ 2) := by
  obtain ⟨he, hf₀⟩ := exterior_formula ht
  have h2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd
  have hpos : 0 < d ^ 2 + s ^ 2 := by positivity
  have hf : f (tt d s) = f l + extSlope * (tt d s ^ 2 - l ^ 2) := by
    unfold f extSlope
    rw [hf₀]
    ring
  unfold G
  rw [he, hf, h2, extConst]
  field_simp
  ring

theorem two_pow_pos' : (0 : ℝ) < 2 ^ 128 := by positivity

theorem abs_add6_le (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)

theorem ext_split {A1 q A2 T D kp cc κ c dv : ℝ} (hT : T ≠ 0) (hD : D ≠ 0) :
    A1 + q - (dv * κ + dv * c / D) = (A1 - kp * dv) + (kp - κ) * dv + (q - A2 / T) + (A2 - cc * dv) / T +
      (cc - c) * dv / T + c * dv * (D - T) / (T * D) := by
  field_simp
  ring

/-- The real-number core of the exterior error: all roundings `≤ u`. -/
theorem ext_error_real {A1 A2 q T D kp cc κ c dv u rκ rc : ℝ} (hu0 : 0 < u) (hd0 : 0 < dv) (hd1 : dv ≤ 1)
    (hT : (1 : ℝ) / 4 ≤ T) (hD : (1 : ℝ) / 5 ≤ D) (hTD : |T - D| ≤ 2 * u) (hκ : |κ - kp| ≤ rκ)
    (hc : |c - cc| ≤ rc) (hc1 : |c| ≤ 1) (a1 : |A1 - kp * dv| < u) (a2 : |A2 - cc * dv| < u)
    (a3 : |q - A2 / T| < u) :
    |A1 + q - (dv * κ + dv * c / D)| ≤ rκ + 4 * rc + 46 * u := by
  have hTpos : 0 < T := by linarith
  have hDpos : 0 < D := by linarith
  rw [ext_split (A2 := A2) (cc := cc) hTpos.ne' hDpos.ne']
  have b1 : |(kp - κ) * dv| ≤ rκ := by
    rw [abs_mul, abs_of_pos hd0, abs_sub_comm]
    have : |κ - kp| * dv ≤ rκ * 1 := mul_le_mul hκ hd1 hd0.le ((abs_nonneg _).trans hκ)
    linarith
  have b2 : |(A2 - cc * dv) / T| ≤ 4 * u := by
    rw [abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]
    nlinarith [abs_nonneg (A2 - cc * dv)]
  have b3 : |(cc - c) * dv / T| ≤ 4 * rc := by
    rw [abs_div, abs_mul, abs_of_pos hTpos, abs_of_pos hd0, div_le_iff₀ hTpos, abs_sub_comm]
    have : |c - cc| * dv ≤ rc * 1 := mul_le_mul hc hd1 hd0.le ((abs_nonneg _).trans hc)
    nlinarith [abs_nonneg (c - cc)]
  have b4 : |c * dv * (D - T) / (T * D)| ≤ 40 * u := by
    have hTD' : (1 : ℝ) / 20 ≤ T * D := by nlinarith
    rw [abs_div, abs_of_pos (by positivity : 0 < T * D), div_le_iff₀ (by positivity)]
    have h5 : |c * dv * (D - T)| ≤ 1 * 1 * (2 * u) := by
      rw [abs_mul, abs_mul, abs_of_pos hd0, abs_sub_comm]
      have h6 : |c| * dv ≤ 1 * 1 := mul_le_mul hc1 hd1 hd0.le (by norm_num)
      exact mul_le_mul h6 hTD (abs_nonneg _) (by norm_num)
    have : 2 * u ≤ 40 * u * (T * D) := by nlinarith
    linarith
  refine (abs_add6_le _ _ _ _ _ _).trans ?_
  calc _ ≤ u + rκ + u + 4 * u + 4 * rc + 40 * u :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add a1.le b1) a3.le) b2) b3) b4
    _ = _ := by ring

/-- **The exterior evaluation error.** -/
theorem evalExt_sound {E : EvalData} {d s T2 : Fx 128} {κ c rκ rc : ℝ} (hκ : |κ - E.kap.val| ≤ rκ)
    (hc : |c - E.cc.val| ≤ rc) (hc1 : |c| ≤ 1) (hd0 : 0 < d.val) (hd1 : d.val ≤ 1) (hT2 : T2 = t2Of d s)
    (hT : (1 : ℝ) / 4 ≤ T2.val) :
    |(evalExt E d T2).val - (d.val * κ + d.val * c / (d.val ^ 2 + s.val ^ 2))| ≤ deltaExt rκ rc := by
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = 1 / 2 ^ 128 := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1000 : u ≤ 1 / 1000 := by rw [hu]; norm_num
  have hdd := Fx.abs_val_mul_sub_lt d d
  have hss := Fx.abs_val_mul_sub_lt s s
  rw [← hu] at hdd hss
  have hT2v : |T2.val - (d.val ^ 2 + s.val ^ 2)| ≤ 2 * u := by
    rw [hT2]
    simp only [t2Of, Fx.val_add]
    have : (Fx.mul d d).val + (Fx.mul s s).val - (d.val ^ 2 + s.val ^ 2) =
        ((Fx.mul d d).val - d.val * d.val) + ((Fx.mul s s).val - s.val * s.val) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    linarith only [hdd, hss]
  have hD : (1 : ℝ) / 5 ≤ d.val ^ 2 + s.val ^ 2 := by
    have := (abs_le.1 hT2v).2
    linarith only [this, hT, hu1000]
  have hTpos : 0 < T2.val := by linarith
  have a1 := Fx.abs_val_mul_sub_lt E.kap d
  have a2 := Fx.abs_val_mul_sub_lt E.cc d
  have a3 := Fx.abs_val_div_sub_lt (Fx.mul E.cc d) T2 (mag_ne_zero_of_pos hTpos)
  rw [← hu] at a1 a2 a3
  have hv : (evalExt E d T2).val = (Fx.mul E.kap d).val + (Fx.div (Fx.mul E.cc d) T2).val := by
    unfold evalExt; rw [Fx.val_add]
  rw [hv]
  have := ext_error_real (A1 := (Fx.mul E.kap d).val) (A2 := (Fx.mul E.cc d).val)
    (q := (Fx.div (Fx.mul E.cc d) T2).val) (T := T2.val) (D := d.val ^ 2 + s.val ^ 2) (kp := E.kap.val)
    (cc := E.cc.val) (κ := κ) (c := c) (dv := d.val) (u := u) (rκ := rκ) (rc := rc) hu0 hd0 hd1 hT hD hT2v hκ hc hc1
    a1 a2 a3
  have h46 : 46 * u ≤ 1 / 2 ^ 100 := by rw [hu]; norm_num
  unfold deltaExt
  linarith

/-! ### One value of `G` -/

/-- The hypotheses on the evaluator data: the table cells are valid (`Query.CellValid`), `λ̂, μ̂` approximate the
exact constants within `rlam`, `rmu`, `κ̂, ĉ` approximate `κ = -π B(l) - λ/2`, `c = f(l) - κ l²` within `rκ`, `rc`,
and `lsq` is a safe threshold for `t̂² ≥ l²`. -/
structure EvalHyp (E : EvalData) (rf re : ℕ) (rlam rmu rκ rc : ℝ) : Prop where
  /-- Every cell of the query table is valid. -/
  cells : ∀ i, i < E.T.n → CellValid (E.T.cell i) rf re
  /-- `λ̂ ≈ λ`. -/
  lam_r : |Calibration.lam - E.lam.val| ≤ rlam
  /-- `μ̂ ≈ μ`. -/
  mu_r : |Calibration.mu - E.mu.val| ≤ rmu
  /-- `|λ̂| ≤ 8`. -/
  lam8 : |E.lam.val| ≤ 8
  /-- `|μ̂| ≤ 8`. -/
  mu8 : |E.mu.val| ≤ 8
  /-- The radii are small. -/
  small : (rf : ℝ) / 2 ^ 128 + (re : ℝ) / 2 ^ 128 + rlam + rmu ≤ 1 / 2
  /-- `κ̂ ≈ κ`. -/
  kap_r : |extSlope - E.kap.val| ≤ rκ
  /-- `ĉ ≈ c`. -/
  cc_r : |extConst - E.cc.val| ≤ rc
  /-- `|c| ≤ 1`. -/
  c_le : |extConst| ≤ 1
  /-- `lsq ≥ l² + 2⁻¹²⁷`. -/
  lsq_ge : Calibration.l ^ 2 + 1 / 2 ^ 127 ≤ E.lsq.val
  /-- `lsq ≥ 1/4`. -/
  lsq_quarter : (1 : ℝ) / 4 ≤ E.lsq.val

/-- The error bound of a value of `G`: the larger of the interior and exterior budgets. -/
@[expose] noncomputable def deltaMax (rf re : ℕ) (rlam rmu rκ rc : ℝ) : ℝ :=
  max (deltaG rf re rlam rmu) (deltaExt rκ rc)

theorem t2Of_err (d s : Fx 128) : |(t2Of d s).val - (d.val ^ 2 + s.val ^ 2)| ≤ 1 / 2 ^ 127 := by
  have hdd := Fx.abs_val_mul_sub_lt d d
  have hss := Fx.abs_val_mul_sub_lt s s
  simp only [t2Of, Fx.val_add]
  have : (Fx.mul d d).val + (Fx.mul s s).val - (d.val ^ 2 + s.val ^ 2) =
      ((Fx.mul d d).val - d.val * d.val) + ((Fx.mul s s).val - s.val * s.val) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  have : (1 : ℝ) / 2 ^ 127 = 1 / 2 ^ 128 + 1 / 2 ^ 128 := by norm_num
  rw [this]
  linarith only [hdd, hss]

/-- **One value of `G`**: every successful `evalMid` is within `deltaMax` of the exact `G`. -/
theorem evalMid_sound (hc : FiniteCore) {E : EvalData} {rf re : ℕ} {rlam rmu rκ rc : ℝ}
    (H : EvalHyp E rf re rlam rmu rκ rc) {i : ℕ} {d s v : Fx 128} (hd : Calibration.b ≤ d.val)
    (hd1 : d.val ≤ 1) (hv : evalMid E i d s = some v) :
    |v.val - G d.val s.val| ≤ deltaMax rf re rlam rmu rκ rc := by
  have hb0 : (0 : ℝ) < Calibration.b := Calibration.b_pos
  have hd0 : 0 < d.val := lt_of_lt_of_le hb0 hd
  unfold evalMid at hv
  cases hb : Fx.ble E.lsq (t2Of d s)
  · simp only [hb, Bool.cond_false] at hv
    exact (evalG_sound hc H.cells H.lam_r H.mu_r H.lam8 H.mu8 H.small hd hv).trans (le_max_left _ _)
  · simp only [hb, Bool.cond_true, Option.some.injEq] at hv
    subst hv
    have h1 := (Fx.ble_iff _ _).1 hb
    have hT := t2Of_err d s
    have hD : Calibration.l ^ 2 ≤ d.val ^ 2 + s.val ^ 2 := by
      have := (abs_le.1 hT).2
      have := H.lsq_ge
      linarith
    have ht : Calibration.l ≤ tt d.val s.val := Real.le_sqrt_of_sq_le hD
    have hG := G_exterior_eq hd0 ht
    rw [hG]
    exact (evalExt_sound H.kap_r H.cc_r H.c_le hd0 hd1 rfl (H.lsq_quarter.trans h1)).trans (le_max_right _ _)

theorem fxM_val (m : ℕ) : (fxM m).val = (m : ℝ) / 2 ^ 128 := by
  simp [fxM, Fx.val_def]

/-- **The value at the midpoint of cell `j` of a row**: the sum of the nodes is even and the value is within
`deltaMax` of `G(d, (σ_j + σ_{j+1})/2)`, `d = dm/2^128`, `σ_k = sm k/2^128`. -/
theorem midVal_sound (hc : FiniteCore) {E : EvalData} {rf re : ℕ} {rlam rmu rκ rc : ℝ}
    (H : EvalHyp E rf re rlam rmu rκ rc) {idx : ℕ → ℕ} {dm : ℕ} {sm : ℕ → ℕ} {j : ℕ} {v : Fx 128}
    (hd : Calibration.b ≤ (dm : ℝ) / 2 ^ 128) (hd1 : (dm : ℝ) / 2 ^ 128 ≤ 1)
    (hv : midVal E idx dm sm j = some v) :
    (sm j + sm (j + 1)) % 2 = 0 ∧
      |v.val - G ((dm : ℝ) / 2 ^ 128) (((sm j : ℝ) / 2 ^ 128 + (sm (j + 1) : ℝ) / 2 ^ 128) / 2)| ≤
        deltaMax rf re rlam rmu rκ rc := by
  unfold midVal at hv
  cases hb : Nat.beq (Nat.mod (Nat.add (sm j) (sm (Nat.succ j))) 2) 0
  · rw [hb] at hv
    simp only [Bool.cond_false] at hv
    exact absurd hv (by simp)
  · rw [hb] at hv
    simp only [Bool.cond_true] at hv
    have hmod : (sm j + sm (j + 1)) % 2 = 0 := Nat.eq_of_beq_eq_true hb
    refine ⟨hmod, ?_⟩
    have hmid : ((midM sm j : ℕ) : ℝ) = ((sm j : ℝ) + sm (j + 1)) / 2 := by
      have h2 : 2 * midM sm j = sm j + sm (j + 1) := by
        show 2 * ((sm j + sm (j + 1)) / 2) = sm j + sm (j + 1)
        omega
      have : (2 : ℝ) * (midM sm j : ℝ) = (sm j : ℝ) + sm (j + 1) := by exact_mod_cast h2
      linarith
    have := evalMid_sound hc H (d := fxM dm) (s := fxM (midM sm j)) (by rwa [fxM_val]) (by rwa [fxM_val]) hv
    rw [fxM_val, fxM_val, hmid] at this
    have e : ((sm j : ℝ) / 2 ^ 128 + (sm (j + 1) : ℝ) / 2 ^ 128) / 2 = (((sm j : ℝ) + sm (j + 1)) / 2) / 2 ^ 128 := by
      ring
    rw [e]
    exact this

end SandierSerfaty.Certificate.Box
