/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Lambda.Point

/-!
# Soundness of the two midpoint sums of the fine `λ` quadrature

On the real grid `σ_k = A + W k/N` (`gr`):

* `runLoop_sound`: if every term `k < N` of `step` encloses `∫_{σ_k}^{σ_{k+1}} f`, the loop encloses
  `∫_{σ_0}^{σ_N} f`;
* `qTerm_sound`: the term of the first integrand encloses `∫_{σ_k}^{σ_{k+1}} q` (midpoint value from `fAt_sound`,
  error from `Table.abs_integral_sub_midpoint_le` and `abs_qq2_le` with `s ≥ σ_k`);
* `eTerm_sound`: the term of the second integrand encloses `∫_{σ_k}^{σ_{k+1}} e(t(s)) ds` (error from
  `abs_integral_sub_midpoint_le_of_lip` and `lip_Y1`);
* `qSum_sound`, `eSum_sound`: `∫_{s₀}^{x₀} q` and `∫₀^{x₀} e(t(s)) ds`.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-! ### The loop -/

theorem intervalIntegrable_grid {f : ℝ → ℝ} {σ : ℕ → ℝ} {N : ℕ}
    (hint : ∀ k, k < N → IntervalIntegrable f volume (σ k) (σ (k + 1))) :
    ∀ k, k ≤ N → IntervalIntegrable f volume (σ 0) (σ k)
  | 0, _ => IntervalIntegrable.refl
  | k + 1, hk => (intervalIntegrable_grid hint k (by omega)).trans (hint k (by omega))

/-- **The loop encloses the integral over the grid.** -/
theorem runLoop_sound {step : ℕ → ℕ → Option (ℕ × IV 128)} {f : ℝ → ℝ} {σ : ℕ → ℝ} {N : ℕ}
    (hstep : ∀ k i r, k < N → step k i = some r → IV.Mem (∫ s in σ k..σ (k + 1), f s) r.2)
    (hint : ∀ k, k < N → IntervalIntegrable f volume (σ k) (σ (k + 1))) :
    ∀ n k i acc S, k + n ≤ N → runLoop step n k i acc = some S →
      IV.Mem (∫ s in σ 0..σ k, f s) acc → IV.Mem (∫ s in σ 0..σ (k + n), f s) S
  | 0, k, i, acc, S, _, h, hacc => by
    simp only [runLoop, Option.some.injEq] at h
    subst h; simpa using hacc
  | n + 1, k, i, acc, S, hkn, h, hacc => by
    cases hs : step k i with
    | none => simp [runLoop, hs] at h
    | some r =>
      simp only [runLoop, hs] at h
      have hr := hstep k i r (by omega) hs
      have hacc' : IV.Mem (∫ s in σ 0..σ (k + 1), f s) (IV.add acc r.2) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_grid hint k (by omega)) (hint k (by omega))]
        exact IV.mem_add hacc hr
      have := runLoop_sound hstep hint n (k + 1) r.1 (IV.add acc r.2) S (by omega) h hacc'
      rwa [show k + 1 + n = k + (n + 1) by omega] at this

/-! ### The grid -/

/-- The real grid node `A + W k/N`. -/
@[expose] noncomputable def gr (A W : ℝ) (N k : ℕ) : ℝ := A + W * k / N

theorem mem_gNode {A W : ℝ} {AI WI : IV 128} (hA : IV.Mem A AI) (hW : IV.Mem W WI) {N : ℕ} (hN : 0 < N)
    (k : ℕ) : IV.Mem (gr A W N k) (gNode AI WI N k) :=
  IV.mem_add hA (IV.mem_divNat (IV.mem_mulNat hW k) hN)

theorem mem_gMid {A W : ℝ} {AI WI : IV 128} (hA : IV.Mem A AI) (hW : IV.Mem W WI) {N : ℕ} (hN : 0 < N)
    (k : ℕ) : IV.Mem ((gr A W N k + gr A W N (k + 1)) / 2) (gMid AI WI N k) := by
  have := IV.mem_add hA (IV.mem_divNat (IV.mem_mulNat hW (Nat.add (Nat.mul 2 k) 1)) (by show 0 < 2 * N; omega))
  refine mem_of_mem_iff this ?_
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [gr, Nat.add_eq, Nat.mul_eq]
  push_cast
  field_simp
  ring

theorem gr_succ_sub (A W : ℝ) {N : ℕ} (hN : 0 < N) (k : ℕ) : gr A W N (k + 1) - gr A W N k = W / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold gr; push_cast; field_simp; ring

theorem gr_zero (A W : ℝ) (N : ℕ) : gr A W N 0 = A := by simp [gr]

theorem gr_N (A W : ℝ) {N : ℕ} (hN : 0 < N) : gr A W N N = A + W := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold gr; field_simp

theorem gr_mem {A W : ℝ} (hW : 0 ≤ W) {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) : gr A W N k ∈ Icc A (A + W) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
  unfold gr
  constructor
  · have : 0 ≤ W * k / N := by positivity
    linarith
  · have : W * k / N ≤ W := by rw [div_le_iff₀ hNr]; nlinarith
    linarith

/-! ### The terms -/

theorem qTermX_some {F : FTable} {c : QCtx} {k : ℕ} {M X : IV 128} {j : ℕ} {r : ℕ × IV 128}
    (h : qTermX F c k M X j = some r) :
    pairOK F j X = true ∧ IV.posB (IV.sq M) = true ∧ IV.posB (IV.mul c.p (IV.sq (gNode c.A c.W c.N k))) = true ∧
      IV.posB c.p2 = true ∧ r = (j, qVal F c k j M X) := by
  unfold qTermX at h
  cases h1 : pairOK F j X <;> cases h2 : IV.posB (IV.sq M) <;>
    cases h3 : IV.posB (IV.mul c.p (IV.sq (gNode c.A c.W c.N k))) <;> cases h4 : IV.posB c.p2 <;>
    simp [h1, h2, h3, h4] at h
  exact ⟨rfl, rfl, rfl, rfl, h.symm⟩

theorem qTerm_some {F : FTable} {c : QCtx} {k i : ℕ} {r : ℕ × IV 128} (h : qTerm F c k i = some r) :
    ∃ l hh : ℕ, IV.sqrtCheck (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k))) l hh = true ∧
      qTermX F c k (gMid c.A c.W c.N k) (IV.ofNatPair l hh)
        (locate F (IV.ofNatPair l hh) i) = some r := by
  unfold qTerm qTermL at h
  refine ⟨(IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).1, (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).2, ?_⟩
  cases hs : IV.sqrtCheck (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k))) (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).1 (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).2 <;>
    simp only [hs, Bool.cond_false, Bool.cond_true, reduceCtorEq] at h
  exact ⟨rfl, h⟩

/-- **The term of the first integrand.** -/
theorem qTerm_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (hF : FRealized F a) {c : QCtx}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ c.rad) (hp : IV.Mem p c.p) (hp2 : IV.Mem (p ^ 2) c.p2) {s₀ : ℝ}
    (hA : IV.Mem s₀ c.A) (hW : IV.Mem (x₀ - s₀) c.W) (hN : 0 < c.N) (hs0 : 0 < s₀) (hs0x : s₀ ≤ x₀)
    (hF0 : IV.Mem (f₀ p) c.F0) {C C' : ℝ} (hB1 : IV.Mem C c.B1) (hB2 : IV.Mem C' c.B2)
    (hC : ∀ t ∈ Icc p R₀, |deriv f₀ t| ≤ C) (hC' : ∀ t ∈ Icc p R₀, |deriv (deriv f₀) t| ≤ C')
    {k i : ℕ} {r : ℕ × IV 128} (hk : k < c.N) (h : qTerm F c k i = some r) :
    IV.Mem (∫ s in gr s₀ (x₀ - s₀) c.N k..gr s₀ (x₀ - s₀) c.N (k + 1), qq s) r.2 := by
  obtain ⟨l, hh, hsq, hX⟩ := qTerm_some h
  obtain ⟨hpair, hposM, hposS, hposp2, rfl⟩ := qTermX_some hX
  have hW0 : 0 ≤ x₀ - s₀ := by linarith
  have hσI := gr_mem (A := s₀) hW0 hN hk.le
  have hσI' := gr_mem (A := s₀) hW0 hN (show k + 1 ≤ c.N by omega)
  rw [show s₀ + (x₀ - s₀) = x₀ by ring] at hσI hσI'
  have hgap := gr_succ_sub s₀ (x₀ - s₀) hN k
  have hm := mem_gMid hA hW hN k
  have hstep : 0 ≤ (x₀ - s₀) / c.N := by positivity
  set σ := gr s₀ (x₀ - s₀) c.N k with hσ
  set σ' := gr s₀ (x₀ - s₀) c.N (k + 1) with hσ'
  set m := (σ + σ') / 2 with hmdef
  have hσpos : 0 < σ := lt_of_lt_of_le hs0 hσI.1
  have hσσ : σ ≤ σ' := by linarith
  have hmpos : 0 < m := by rw [hmdef]; linarith
  -- the value at the midpoint
  have ht : IV.Mem (tt p m) (IV.ofNatPair (P := 128) l hh) :=
    IV.mem_sqrt_of_sqrtCheck hsq (IV.mem_add hp2 (IV.mem_sq hm))
  have hf := fAt_sound hc hF hrad hpair ht
  have hq : IV.Mem (qq m) (IV.divPos (IV.sub (fAt F c.rad (locate F (IV.ofNatPair l hh) i)
      (IV.ofNatPair l hh)) c.F0) (IV.sq (gMid c.A c.W c.N k))) :=
    IV.mem_divPos hposM (IV.mem_sub hf hF0) (IV.mem_sq hm)
  -- the midpoint error
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC p ⟨le_rfl, p_lt_R₀.le⟩)
  have hpp := p_pos
  set Mk := C' / p ^ 2 + 8 * C / (p * σ ^ 2) with hMk
  have herr := abs_integral_sub_midpoint_le (f := qq) (f₁ := qq1) (f₂ := qq2) (a := σ) (b := σ') (M := Mk)
    (U := Ioi 0) isOpen_Ioi hσσ (fun x hx => lt_of_lt_of_le hσpos hx.1)
    (fun x hx => hasDerivAt_qq (ne_of_gt hx)) (fun x hx => hasDerivAt_qq1 (ne_of_gt hx)) (fun x hx => by
      have hx0 : 0 < x := lt_of_lt_of_le hσpos hx.1
      refine (abs_qq2_le hC hC' hx0 (hx.2.trans hσI'.2)).trans ?_
      have : 8 * C / (p * x ^ 2) ≤ 8 * C / (p * σ ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσpos.le hx.1 2) hpp.le)
      linarith)
  rw [hgap, ← hmdef] at herr
  -- the enclosure
  have hh' : IV.Mem ((x₀ - s₀) / c.N) c.h := IV.mem_divNat hW hN
  have hS := mem_gNode hA hW hN k
  have hBd : IV.Mem Mk (qBound c (gNode c.A c.W c.N k)) := by
    have := IV.mem_add (IV.mem_divPos hposp2 hB2 hp2)
      (IV.mem_divPos hposS (IV.mem_mulNat hB1 8) (IV.mem_mul hp (IV.mem_sq hS)))
    exact mem_of_mem_iff this (by rw [hMk]; ring)
  have hE : IV.Mem (((x₀ - s₀) / c.N) ^ 3 / 24 * Mk) (IV.mul (cube24 c.h) (qBound c (gNode c.A c.W c.N k))) := by
    have h3 : IV.Mem (((x₀ - s₀) / c.N) ^ 3 / 24) (cube24 c.h) :=
      mem_of_mem_iff (IV.mem_divNat (IV.mem_mul (IV.mem_sq hh') hh') (by norm_num : 0 < 24)) (by push_cast; ring)
    exact IV.mem_mul h3 hBd
  have := IV.mem_add (IV.mem_mul hh' hq) (mem_symHi hE herr)
  exact mem_of_mem_iff this (by ring)

theorem eTerm_some {F : FTable} {c : QCtx} {k i : ℕ} {r : ℕ × IV 128} (h : eTerm F c k i = some r) :
    ∃ l hh : ℕ, IV.sqrtCheck (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k))) l hh = true ∧
      pairOK F (locate F (IV.ofNatPair l hh) i) (IV.ofNatPair l hh) = true ∧ IV.posB c.p = true ∧
      r = (locate F (IV.ofNatPair l hh) i, eVal F c (locate F (IV.ofNatPair l hh) i) (IV.ofNatPair l hh)) := by
  unfold eTerm eTermL eTermX at h
  refine ⟨(IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).1, (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).2, ?_⟩
  cases hs : IV.sqrtCheck (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))
    (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).1
    (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).2 <;> simp only [hs, Bool.cond_false,
      Bool.cond_true, reduceCtorEq] at h
  cases h1 : pairOK F (locate F (IV.ofNatPair (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).1
    (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).2) i)
    (IV.ofNatPair (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).1
      (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))).2) <;>
    cases h2 : IV.posB c.p <;> simp [h1, h2] at h
  exact ⟨rfl, rfl, rfl, h.symm⟩

/-- **The term of the second integrand.** -/
theorem eTerm_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (hF : FRealized F a) {c : QCtx}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ c.rad) (hp : IV.Mem p c.p) (hp2 : IV.Mem (p ^ 2) c.p2)
    (hA : IV.Mem 0 c.A) (hW : IV.Mem x₀ c.W) (hN : 0 < c.N) {E E' : ℝ} (hB1 : IV.Mem E c.B1)
    (hB2 : IV.Mem E' c.B2) (hE : ∀ t ∈ Icc p R₀, |deriv e t| ≤ E)
    (hE' : ∀ t ∈ Ico p R₀, ∃ E₂, HasDerivWithinAt (deriv e) E₂ (Ici t) t ∧ |E₂| ≤ E')
    {k i : ℕ} {r : ℕ × IV 128} (hk : k < c.N) (h : eTerm F c k i = some r) :
    IV.Mem (∫ s in gr 0 x₀ c.N k..gr 0 x₀ c.N (k + 1), e (tt p s)) r.2 := by
  obtain ⟨l, hh, hsq, hpair, hposp, rfl⟩ := eTerm_some h
  have hσI := gr_mem (A := 0) x₀_pos.le hN hk.le
  have hσI' := gr_mem (A := 0) x₀_pos.le hN (show k + 1 ≤ c.N by omega)
  rw [zero_add] at hσI hσI'
  have hgap := gr_succ_sub 0 x₀ hN k
  have hm := mem_gMid hA hW hN k
  have hstep : 0 ≤ x₀ / c.N := by have := x₀_pos; positivity
  set σ := gr 0 x₀ c.N k with hσ
  set σ' := gr 0 x₀ c.N (k + 1) with hσ'
  set m := (σ + σ') / 2 with hmdef
  have hσσ : σ ≤ σ' := by linarith
  have ht : IV.Mem (tt p m) (IV.ofNatPair (P := 128) l hh) :=
    IV.mem_sqrt_of_sqrtCheck hsq (IV.mem_add hp2 (IV.mem_sq hm))
  have hv := eAt_sound hc hF hrad hpair ht
  have herr := abs_integral_sub_midpoint_le_of_lip (f := fun s => e (tt p s)) (f₁ := Y1) (a := σ) (b := σ')
    (M := E' + E / p) (U := univ) isOpen_univ hσσ (subset_univ _) continuous_eY.continuousOn
    (fun x _ => hasDerivAt_eY x) (lip_Y1 hE hE' hσI.1 hσI'.2)
  rw [hgap, ← hmdef] at herr
  have hh' : IV.Mem (x₀ / c.N) c.h := IV.mem_divNat hW hN
  have hBd : IV.Mem (E' + E / p) (eBound c) := IV.mem_add hB2 (IV.mem_divPos hposp hB1 hp)
  have hEr : IV.Mem ((x₀ / c.N) ^ 3 / 24 * (E' + E / p)) (IV.mul (cube24 c.h) (eBound c)) := by
    have h3 : IV.Mem ((x₀ / c.N) ^ 3 / 24) (cube24 c.h) :=
      mem_of_mem_iff (IV.mem_divNat (IV.mem_mul (IV.mem_sq hh') hh') (by norm_num : 0 < 24)) (by push_cast; ring)
    exact IV.mem_mul h3 hBd
  have := IV.mem_add (IV.mem_mul hh' hv) (mem_symHi hEr herr)
  exact mem_of_mem_iff this (by ring)

/-! ### The sums -/

/-- **The midpoint sum of the first integrand** encloses `∫_{s₀}^{x₀} q`. -/
theorem qSum_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (hF : FRealized F a) {c : QCtx}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ c.rad) (hp : IV.Mem p c.p) (hp2 : IV.Mem (p ^ 2) c.p2) {s₀ : ℝ}
    (hA : IV.Mem s₀ c.A) (hW : IV.Mem (x₀ - s₀) c.W) (hN : 0 < c.N) (hs0 : 0 < s₀) (hs0x : s₀ ≤ x₀)
    (hF0 : IV.Mem (f₀ p) c.F0) {C C' : ℝ} (hB1 : IV.Mem C c.B1) (hB2 : IV.Mem C' c.B2)
    (hC : ∀ t ∈ Icc p R₀, |deriv f₀ t| ≤ C) (hC' : ∀ t ∈ Icc p R₀, |deriv (deriv f₀) t| ≤ C')
    {S : IV 128} (h : qSum F c = some S) : IV.Mem (∫ s in s₀..x₀, qq s) S := by
  have hW0 : 0 ≤ x₀ - s₀ := by linarith
  have hint : ∀ k, k < c.N → IntervalIntegrable qq volume (gr s₀ (x₀ - s₀) c.N k) (gr s₀ (x₀ - s₀) c.N (k + 1)) :=
    fun k hk => by
      refine ContinuousOn.intervalIntegrable (continuousOn_qq.mono fun x hx => ?_)
      have h1 := (gr_mem (A := s₀) hW0 hN hk.le).1
      have h2 := (gr_mem (A := s₀) hW0 hN (show k + 1 ≤ c.N by omega)).1
      rw [mem_uIcc] at hx
      show 0 < x
      rcases hx with hx | hx <;> linarith [hx.1]
  have := runLoop_sound (step := qTerm F c) (f := qq) (σ := gr s₀ (x₀ - s₀) c.N) (N := c.N)
    (fun k i r hk hr => qTerm_sound hc hF hrad hp hp2 hA hW hN hs0 hs0x hF0 hB1 hB2 hC hC' hk hr) hint
    c.N 0 0 (IV.ofNat 0) S (by omega) h (by simpa using IV.mem_ofNat (P := 128) 0)
  rwa [zero_add, gr_zero, gr_N _ _ hN, show s₀ + (x₀ - s₀) = x₀ by ring] at this

/-- **The midpoint sum of the second integrand** encloses `∫₀^{x₀} e(t(s)) ds`. -/
theorem eSum_sound (hc : FiniteCore) {F : FTable} {a : ℕ → ℝ} (hF : FRealized F a) {c : QCtx}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ c.rad) (hp : IV.Mem p c.p) (hp2 : IV.Mem (p ^ 2) c.p2)
    (hA : IV.Mem 0 c.A) (hW : IV.Mem x₀ c.W) (hN : 0 < c.N) {E E' : ℝ} (hB1 : IV.Mem E c.B1)
    (hB2 : IV.Mem E' c.B2) (hE : ∀ t ∈ Icc p R₀, |deriv e t| ≤ E)
    (hE' : ∀ t ∈ Ico p R₀, ∃ E₂, HasDerivWithinAt (deriv e) E₂ (Ici t) t ∧ |E₂| ≤ E')
    {S : IV 128} (h : eSum F c = some S) : IV.Mem (∫ s in (0 : ℝ)..x₀, e (tt p s)) S := by
  have := runLoop_sound (step := eTerm F c) (f := fun s => e (tt p s)) (σ := gr 0 x₀ c.N) (N := c.N)
    (fun k i r hk hr => eTerm_sound hc hF hrad hp hp2 hA hW hN hB1 hB2 hE hE' hk hr)
    (fun k _ => continuous_eY.intervalIntegrable _ _)
    c.N 0 0 (IV.ofNat 0) S (by omega) h (by simpa using IV.mem_ofNat (P := 128) 0)
  rwa [zero_add, gr_zero, gr_N _ _ hN, zero_add] at this

end SandierSerfaty.Certificate.Lambda
