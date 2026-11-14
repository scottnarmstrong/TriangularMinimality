/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Lam
public import SandierSerfaty.Certificate.Query.LookupSound
public import SandierSerfaty.Certificate.Query.ConstSound
public import SandierSerfaty.Certificate.Basis.Sound
public import SandierSerfaty.Certificate.Jet.Comp
public import SandierSerfaty.Calibration.Stationarity
public import SandierSerfaty.Calibration.LambdaOrigin

/-!
# Soundness of the coarse enclosure of `λ`

`lamEnc_sound`: if the lookup table realizes the stored tuples (`ITable.Encl`), the basis constants are valid
(`d.Valid`), the finite-core premise holds (it makes the infinite-mode `f₀', e'` agree with the truncated ones
within `10⁻¹¹`, `Tails.uniform_error_of_finiteCore`) and `lamEnc T d N rad = some I` with `rad ≥ 10⁻¹¹·2^128`,
`N > 0`, then `Cal.lam ∈ I`.

* `lam_mul_x₀_eq_integral`: `λ x₀ = ∫₀^{x₀} Φ`, `Φ = f₀'(t)/t - s² e'(t)/(p² t)`, from
  `Calibration.integral_Aint_eq_zero`;
* `mem_phiOf`: on `[s_j, s_{j+1}]`, `Φ(s)` lies in the interval of `Query.Lam.phiOf`;
* `integral_term_mem`: the integral over the subinterval lies in the term `(x₀/N) Φ_j`;
* `phiSum_mem`: induction over the terms.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-! ### The integral formula for `λ` -/

/-- `Φ(s) = f₀'(t)/t - s² e'(t)/(p² t)` with `t = tt p s`. -/
@[expose] noncomputable def Phi (s : ℝ) : ℝ :=
  deriv f₀ (tt p s) / tt p s - s ^ 2 * deriv e (tt p s) / (p ^ 2 * tt p s)

theorem Phi_eq (s : ℝ) : Phi s = Aint p s + lam := by
  have ht : 0 < tt p s := tt_pos p_pos
  unfold Phi Aint df
  field_simp
  ring

theorem continuous_Phi : Continuous Phi := by
  have : Phi = fun s => Aint p s + lam := funext Phi_eq
  rw [this]
  exact continuous_Aint_p.add continuous_const

theorem lam_mul_x₀_eq_integral : lam * x₀ = ∫ s in (0 : ℝ)..x₀, Phi s := by
  have h : ∫ s in (0 : ℝ)..x₀, Phi s = ∫ s in (0 : ℝ)..x₀, (Aint p s + lam) :=
    intervalIntegral.integral_congr fun s _ => Phi_eq s
  rw [h, intervalIntegral.integral_add (continuous_Aint_p.intervalIntegrable (μ := volume) 0 x₀)
    (continuous_const.intervalIntegrable (μ := volume) 0 x₀), integral_Aint_eq_zero]
  simp [mul_comm]

/-! ### Interval facts -/

/-- A real between two enclosed reals lies in the hull of the enclosures. -/
theorem mem_hull_between {a b x : ℝ} {A B : IV 128} (ha : IV.Mem a A) (hb : IV.Mem b B) (hax : a ≤ x)
    (hxb : x ≤ b) : IV.Mem x (IV.hull A B) := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  have h1 : a * 2 ^ 128 ≤ x * 2 ^ 128 := mul_le_mul_of_nonneg_right hax hN.le
  have h2 : x * 2 ^ 128 ≤ b * 2 ^ 128 := mul_le_mul_of_nonneg_right hxb hN.le
  simp only [IV.Mem, IV.hull, SInt.toInt_min, SInt.toInt_max, Int.cast_min, Int.cast_max]
  exact ⟨(min_le_left _ _).trans (ha.1.trans h1), (h2.trans hb.2).trans (le_max_right _ _)⟩

theorem integral_bounds {F : ℝ → ℝ} (hF : Continuous F) {a b lo hi : ℝ} (hab : a ≤ b)
    (h : ∀ s ∈ Icc a b, lo ≤ F s ∧ F s ≤ hi) :
    (b - a) * lo ≤ ∫ s in a..b, F s ∧ ∫ s in a..b, F s ≤ (b - a) * hi := by
  constructor
  · have := intervalIntegral.integral_mono_on hab (f := fun _ => lo) (g := F)
      (continuous_const.intervalIntegrable (μ := volume) a b) (hF.intervalIntegrable (μ := volume) a b) fun s hs => (h s hs).1
    simpa using this
  · have := intervalIntegral.integral_mono_on hab (f := F) (g := fun _ => hi)
      (hF.intervalIntegrable (μ := volume) a b) (continuous_const.intervalIntegrable (μ := volume) a b) fun s hs => (h s hs).2
    simpa using this

/-- The integral of a continuous function that lies in an interval `I` on `[a, b]` is `(b - a) c` with
`c ∈ I`; hence it lies in `W · I` for any `W ∋ b - a`. -/
theorem integral_mem_mul {F : ℝ → ℝ} (hF : Continuous F) {a b : ℝ} (hab : a < b) {I W : IV 128}
    (h : ∀ s ∈ Icc a b, IV.Mem (F s) I) (hW : IV.Mem (b - a) W) :
    IV.Mem (∫ s in a..b, F s) (IV.mul W I) := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  have hw : 0 < b - a := by linarith
  obtain ⟨h1, h2⟩ := integral_bounds hF hab.le (lo := ((I.lo.toInt : ℤ) : ℝ) / 2 ^ 128)
    (hi := ((I.hi.toInt : ℤ) : ℝ) / 2 ^ 128) fun s hs => by
      have := h s hs
      constructor
      · rw [div_le_iff₀ hN]; exact this.1
      · rw [le_div_iff₀ hN]; exact this.2
  have hc : IV.Mem ((∫ s in a..b, F s) / (b - a)) I := by
    constructor
    · have e1 : ((I.lo.toInt : ℤ) : ℝ) / 2 ^ 128 ≤ (∫ s in a..b, F s) / (b - a) := by
        rw [le_div_iff₀ hw, mul_comm]; exact h1
      exact (div_le_iff₀ hN).1 e1
    · have e2 : (∫ s in a..b, F s) / (b - a) ≤ ((I.hi.toInt : ℤ) : ℝ) / 2 ^ 128 := by
        rw [div_le_iff₀ hw, mul_comm]; exact h2
      exact (le_div_iff₀ hN).1 e2
  have := IV.mem_mul hW hc
  rwa [mul_div_cancel₀ _ hw.ne'] at this

/-! ### One term -/

theorem termChk_some {T : ITable} {p2 x0 : IV 128} {N rad : ℕ} {Xs t2 : IV 128} {lh : ℕ × ℕ} {b : IV 128}
    (h : termChk T p2 x0 N rad Xs t2 lh = some b) :
    IV.sqrtCheck t2 lh.1 lh.2 = true ∧ IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2) = true ∧
      ∃ c, lookup T (IV.ofNatPair lh.1 lh.2) = some c ∧
        b = IV.mul (IV.divNat x0 N) (phiOf p2 (IV.sq Xs) (IV.addRad c.f1 rad) (IV.addRad c.e1 rad)
          (IV.ofNatPair lh.1 lh.2)) := by
  unfold termChk at h
  cases h1 : (and (IV.sqrtCheck t2 lh.1 lh.2) (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2)))
  · simp [h1] at h
  · simp only [h1, Bool.cond_true] at h
    simp only [Bool.and_eq_true] at h1
    refine ⟨h1.1, h1.2, ?_⟩
    unfold termFrom at h
    cases hl : lookup T (IV.ofNatPair lh.1 lh.2) with
    | none => simp [hl] at h
    | some c =>
      simp only [hl, Option.some.injEq] at h
      exact ⟨c, rfl, h.symm⟩

/-- On `[s_j, s_{j+1}]`, `Φ(s)` lies in the interval `phiOf` of the term. -/
theorem mem_phiOf (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {d : BasisData} (hd : d.Valid)
    (hp2 : IV.posB d.p2 = true) {Xs t2 : IV 128} {l h : ℕ} {c : Tup} {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) (hsq : IV.sqrtCheck t2 l h = true)
    (hpos : IV.posB (IV.ofNatPair (P := 128) l h) = true) (hlk : lookup T (IV.ofNatPair l h) = some c)
    {s : ℝ} (hs : IV.Mem s Xs) (ht2 : IV.Mem (p ^ 2 + s ^ 2) t2) (hs0 : 0 ≤ s) (hsx : s ≤ x₀) :
    IV.Mem (Phi s) (phiOf d.p2 (IV.sq Xs) (IV.addRad c.f1 rad) (IV.addRad c.e1 rad) (IV.ofNatPair l h)) := by
  have htI : IV.Mem (tt p s) (IV.ofNatPair (P := 128) l h) := IV.mem_sqrt_of_sqrtCheck hsq ht2
  have hb : Calibration.b ≤ tt p s := (Calibration.b_lt_p.trans_le (p_le_tt s)).le
  have hl : tt p s ≤ Calibration.l := by
    have := tt_mono hs0 hsx
    rw [tt_p_x₀] at this
    exact this.trans Calibration.R₀_lt_l.le
  have ht : tt p s ∈ Icc Calibration.b Calibration.l := ⟨hb, hl⟩
  obtain ⟨c1, hc1, hf1⟩ := lookup_f1 hT ht htI
  obtain ⟨c2, hc2, he1⟩ := lookup_e1 hT ht htI
  rw [hlk] at hc1 hc2
  have e1 : c1 = c := (Option.some.inj hc1).symm
  have e2 : c2 = c := (Option.some.inj hc2).symm
  rw [e1] at hf1
  rw [e2] at he1
  obtain ⟨-, -, uf1, ue1, -⟩ := uniform_error_of_finiteCore hc ht
  have hF1 : IV.Mem (deriv f₀ (tt p s)) (IV.addRad c.f1 rad) := mem_of_abs_lt hf1 uf1 hrad
  have hE1 : IV.Mem (deriv e (tt p s)) (IV.addRad c.e1 rad) := mem_of_abs_lt he1 ue1 hrad
  have hinv := Jet.mem_invPos hpos htI
  have hS2 := IV.mem_sq hs
  have hP2 := hd.mp2
  have hmem := IV.mem_sub (IV.mem_mul hF1 hinv)
    (IV.mem_divPos hp2 (IV.mem_mul hS2 (IV.mem_mul hE1 hinv)) hP2)
  have htp : 0 < tt p s := tt_pos p_pos
  have hpp : 0 < p := p_pos
  have eq : Phi s = deriv f₀ (tt p s) * (tt p s)⁻¹ -
      s ^ 2 * (deriv e (tt p s) * (tt p s)⁻¹) / p ^ 2 := by
    unfold Phi; field_simp
  rw [eq]
  exact hmem

theorem sNode_mem {x0 : IV 128} (hx0 : IV.Mem x₀ x0) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    IV.Mem (x₀ * (j : ℝ) / N) (sNode x0 N j) :=
  IV.mem_divNat (IV.mem_mulNat hx0 j) hN

/-- **One term**: the integral of `Φ` over `[s_j, s_{j+1}]` lies in the term of the sum. -/
theorem phiTerm_mem (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {d : BasisData}
    (hd : d.Valid) (hp2 : IV.posB d.p2 = true) {x0 : IV 128} (hx0 : IV.Mem x₀ x0) {N rad j : ℕ}
    (hN : 0 < N) (hj : j < N) (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {b : IV 128}
    (hb : phiTerm T d.p2 x0 N rad j = some b) :
    IV.Mem (∫ s in (x₀ * (j : ℝ) / N)..(x₀ * ((j + 1 : ℕ) : ℝ) / N), Phi s) b := by
  unfold phiTerm at hb
  obtain ⟨hsq, hpos, c, hlk, hbeq⟩ := termChk_some hb
  subst hbeq
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : 0 < x₀ := x₀_pos
  have hjN : ((j + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hj
  have hab : x₀ * (j : ℝ) / N < x₀ * ((j + 1 : ℕ) : ℝ) / N := by
    rw [div_lt_div_iff_of_pos_right hNr]
    push_cast
    nlinarith
  have hW : IV.Mem (x₀ * ((j + 1 : ℕ) : ℝ) / N - x₀ * (j : ℝ) / N) (IV.divNat x0 N) := by
    have := IV.mem_divNat hx0 hN
    convert this using 1
    push_cast; ring
  refine integral_mem_mul continuous_Phi hab (fun s hs => ?_) hW
  have hXs : IV.Mem s (sHull x0 N j) :=
    mem_hull_between (sNode_mem hx0 hN j) (sNode_mem hx0 hN (j + 1)) hs.1 hs.2
  have hs0 : 0 ≤ s := hs.1.trans' (by positivity)
  have hsx : s ≤ x₀ := by
    refine hs.2.trans ?_
    rw [div_le_iff₀ hNr]
    nlinarith
  exact mem_phiOf hc hT hd hp2 hrad hsq hpos hlk hXs (IV.mem_add hd.mp2 (IV.mem_sq hXs)) hs0 hsx

/-- **The sum**: the integral of `Φ` over `[0, s_k]` lies in the sum of the first `k` terms. -/
theorem phiSum_mem (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {d : BasisData}
    (hd : d.Valid) (hp2 : IV.posB d.p2 = true) {x0 : IV 128} (hx0 : IV.Mem x₀ x0) {N rad : ℕ}
    (hN : 0 < N) (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) :
    ∀ k, k ≤ N → ∀ S, phiSum T d.p2 x0 N rad k = some S →
      IV.Mem (∫ s in (0 : ℝ)..(x₀ * (k : ℝ) / N), Phi s) S
  | 0, _, S, hS => by
    simp only [phiSum, Option.some.injEq] at hS
    subst hS
    simpa using IV.mem_ofNat (P := 128) 0
  | k + 1, hk, S, hS => by
    simp only [phiSum] at hS
    cases h1 : phiSum T d.p2 x0 N rad k with
    | none => simp [h1] at hS
    | some A =>
      cases h2 : phiTerm T d.p2 x0 N rad k with
      | none => simp [h1, h2] at hS
      | some B =>
        simp only [h1, h2, Option.some.injEq] at hS
        subst hS
        have hA := phiSum_mem hc hT hd hp2 hx0 hN hrad k (by omega) A h1
        have hB := phiTerm_mem hc hT hd hp2 hx0 hN (by omega) hrad h2
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (continuous_Phi.intervalIntegrable (μ := volume) 0 (x₀ * (k : ℝ) / N))
          (continuous_Phi.intervalIntegrable (μ := volume) (x₀ * (k : ℝ) / N)
            (x₀ * ((k + 1 : ℕ) : ℝ) / N))]
        exact IV.mem_add hA hB

/-- **The coarse enclosure of `λ`.** -/
theorem lamEnc_sound (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {d : BasisData}
    (hd : d.Valid) (hp2 : IV.posB d.p2 = true) {N rad : ℕ} (hN : 0 < N)
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {I : IV 128} (hI : lamEnc T d N rad = some I) :
    IV.Mem lam I := by
  unfold lamEnc at hI
  have hx0 : IV.Mem x₀ (IV.divPow2 d.r0 1) := by
    have := IV.mem_divPow2 hd.mr0 1
    convert this using 1
    unfold x₀; norm_num
  cases hS : phiSum T d.p2 (IV.divPow2 d.r0 1) N rad N with
  | none => simp [lamDiv, hS] at hI
  | some S =>
    simp only [lamDiv, hS] at hI
    cases hpos : IV.posB (IV.divPow2 d.r0 1) with
    | false => simp [hpos] at hI
    | true =>
      simp only [hpos, Bool.cond_true, Option.some.injEq] at hI
      subst hI
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hint := phiSum_mem hc hT hd hp2 hx0 hN hrad N le_rfl S hS
      rw [mul_div_assoc, div_self hN', mul_one] at hint
      have hx : x₀ ≠ 0 := x₀_pos.ne'
      have := IV.mem_divPos hpos (lam_mul_x₀_eq_integral ▸ hint) hx0
      rwa [mul_div_cancel_right₀ _ hx] at this

end SandierSerfaty.Certificate.Query
