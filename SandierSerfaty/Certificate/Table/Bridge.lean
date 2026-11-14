/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.StepSound
public import SandierSerfaty.Calibration.SectorInt
public import SandierSerfaty.Calibration.Trunc

/-!
# The table model is the truncated calibration (`Cal.Trunc`)

The soundness of a table chunk (`chunkCheck_sound`) is stated for any sector functions satisfying the radial ODEs
of the segment (`SectorODE`), through the model `F0m`, `Em` built from the pieces `Cal.Piece.*`. This module
identifies the model with the truncated objects of `Cal.Trunc` (paper §6, §7.2):

* `Trunc.B = B - Btail` and `Trunc.B₁ = B₁ - Btail'` on `(0, ∞)`, with `Btail`, `Btail'` bounded by the summable
  majorants of the omitted modes; so the truncated integrands are dominated near `0` (`NearZero`) and
  `Trunc.S₁`, `Trunc.S₂`, `Trunc.H k` have the derivatives of `comp:radial-odes` on `(0, ∞)`;
* on a closed segment `seg j` the splines are the pieces: `Trunc.B = Bp j`, `Trunc.B₁ = B1p j`, so the truncated
  sector functions satisfy `SectorODE j (seg j)` (`sectorODE_trunc`), and `Trunc.f₀ = F0m j …`,
  `Trunc.e = Em j` there (`trunc_f₀_eq_F0m`, `trunc_e_eq_Em`);
* `chunkCheck_sound_trunc`: a chunk of segment `j` whose cells lie in `seg j`, started from a checkpoint
  enclosing `Trunc.S₁, Trunc.S₂, Trunc.H` at its first node, encloses `Trunc.f₀`, `Trunc.e` (values on the
  cells and at the nodes, `TruncEncloses`) and ends in a checkpoint enclosing the truncated sector functions at
  its last node.
-/

open Set MeasureTheory

public section

namespace SandierSerfaty.Certificate.Table

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis
open SandierSerfaty.Calibration

/-- The truncated `H̃_{k_i}`, indexed by the mode `i`. -/
@[expose] noncomputable def TH (i : ℕ) : ℝ → ℝ := Trunc.H (k i)

/-! ### The omitted modes -/

/-- The majorant of the omitted modes. -/
@[expose] noncomputable def tailM : ℝ := ∑' m : ℕ, Tails.wk (6 * (m + 39))

theorem trunc_B_eq : Trunc.B = Bfin := rfl

theorem deriv_Btail_eq {t : ℝ} (ht : 0 < t) : deriv Btail t = ∑' m : ℕ, deriv (u (m + 39)) t :=
  (tsum_contDiffOn_two (g := fun m => u (m + 39)) (M₀ := fun m => Tails.wk (6 * (m + 39)))
    (M₁ := fun m => Tails.wk (6 * (m + 39))) (M₂ := fun m => Tails.wk (6 * (m + 39)))
    isOpen_Ioi isPreconnected_Ioi summable_wk_tail summable_wk_tail summable_wk_tail
    (fun m => contDiffOn_u (m + 39))
    (fun m x hx => (u_bounds (by omega) hx).1)
    (fun m x hx => (u_bounds (by omega) hx).2.1)
    (fun m x hx => (u_bounds (by omega) hx).2.2)).2.1 t ht

theorem abs_Btail_le {t : ℝ} (ht : 0 < t) : |Btail t| ≤ tailM := by
  rw [← Real.norm_eq_abs]
  exact tsum_of_norm_bounded summable_wk_tail.hasSum fun m => by
    rw [Real.norm_eq_abs]; exact (u_bounds (by omega) ht).1

theorem abs_deriv_Btail_le {t : ℝ} (ht : 0 < t) : |deriv Btail t| ≤ tailM := by
  rw [deriv_Btail_eq ht, ← Real.norm_eq_abs]
  exact tsum_of_norm_bounded summable_wk_tail.hasSum fun m => by
    rw [Real.norm_eq_abs]; exact (u_bounds (by omega) ht).2.1

theorem tailM_nonneg : 0 ≤ tailM := (abs_nonneg _).trans (abs_Btail_le (t := 1) one_pos)

theorem trunc_B_eq_sub {t : ℝ} (ht : 0 < t) : Trunc.B t = B t - Btail t := by
  rw [B_eq_fin_add_tail ht, trunc_B_eq]; ring

theorem deriv_trunc_B_eq_sub {t : ℝ} (ht : 0 < t) : deriv Trunc.B t = deriv B t - deriv Btail t := by
  have hB : DifferentiableAt ℝ B t :=
    (contDiffOn_B.differentiableOn (by norm_num) t ht).differentiableAt (Ioi_mem_nhds ht)
  have hT : DifferentiableAt ℝ Btail t :=
    (contDiffOn_Btail.differentiableOn (by norm_num) t ht).differentiableAt (Ioi_mem_nhds ht)
  have he : Trunc.B =ᶠ[nhds t] fun x => B x - Btail x :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun x hx => trunc_B_eq_sub hx
  rw [he.deriv_eq]
  exact deriv_sub hB hT

theorem trunc_B₁_eq_sub {t : ℝ} (ht : 0 < t) : Trunc.B₁ t = B₁ t - deriv Btail t := by
  simp only [Trunc.B₁, B₁, deriv_trunc_B_eq_sub ht]; ring

theorem contDiffOn_trunc_B : ContDiffOn ℝ 2 Trunc.B (Ioi 0) := by
  rw [trunc_B_eq]; exact contDiffOn_Bfin

theorem contDiffOn_trunc_B₁ : ContDiffOn ℝ 1 Trunc.B₁ (Ioi 0) := by
  have h : ContDiffOn ℝ 1 (deriv Trunc.B) (Ioi 0) :=
    contDiffOn_trunc_B.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
  exact h.add (contDiffOn_const.div contDiffOn_id fun x hx => ne_of_gt hx)

theorem continuousOn_trunc_B : ContinuousOn Trunc.B (Ioi 0) := contDiffOn_trunc_B.continuousOn

theorem continuousOn_trunc_B₁ : ContinuousOn Trunc.B₁ (Ioi 0) := contDiffOn_trunc_B₁.continuousOn

/-- Near `0`: `|B̃₁ r| ≤ C` and `|B̃ r| ≤ |log r| + C` on `(0, 1/4]`. -/
theorem trunc_near_zero_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Ioc (0 : ℝ) (1 / 4),
    |Trunc.B₁ r| ≤ C ∧ |Trunc.B r| ≤ |Real.log r| + C := by
  obtain ⟨C, hC0, hC⟩ := near_zero_bounds
  refine ⟨C + tailM, add_nonneg hC0 tailM_nonneg, fun r hr => ⟨?_, ?_⟩⟩
  · rw [trunc_B₁_eq_sub hr.1]
    have h1 : |B₁ r| ≤ C := (hC r hr).1.trans (by nlinarith [hr.1, hr.2])
    calc |B₁ r - deriv Btail r| ≤ |B₁ r| + |deriv Btail r| := abs_sub _ _
      _ ≤ C + tailM := add_le_add h1 (abs_deriv_Btail_le hr.1)
  · rw [trunc_B_eq_sub hr.1]
    calc |B r - Btail r| ≤ |B r| + |Btail r| := abs_sub _ _
      _ ≤ |Real.log r| + C + tailM := add_le_add (hC r hr).2 (abs_Btail_le hr.1)
      _ = _ := by ring

/-! ### The radial ODEs of the truncated sector functions -/

theorem intervalIntegrable_trunc_S₁ {t : ℝ} (ht : 0 < t) :
    IntervalIntegrable (fun r => Trunc.B r * r) volume 0 t := by
  have h2 : NearZero fun r => Btail r * r :=
    nearZero_const_bound (contDiffOn_Btail.continuousOn.mul continuousOn_id) tailM fun r hr => by
      rw [abs_mul, abs_of_pos hr.1]
      have hr1 : r ≤ 1 := by linarith [hr.2]
      calc |Btail r| * r ≤ tailM * 1 :=
            mul_le_mul (abs_Btail_le hr.1) hr1 hr.1.le tailM_nonneg
        _ = tailM := mul_one _
  have h3 := (nearZero_S₁.intervalIntegrable ht).sub (h2.intervalIntegrable ht)
  rw [intervalIntegrable_iff] at h3 ⊢
  refine h3.congr_fun (fun r hr => ?_) measurableSet_uIoc
  have hr0 : 0 < r := by rw [uIoc_of_le ht.le] at hr; exact hr.1
  simp only [trunc_B_eq_sub hr0]
  ring

theorem nearZero_trunc_S₂ : NearZero fun r => -2 * Trunc.B₁ r + r * Trunc.B₁ r ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := trunc_near_zero_bounds
  refine nearZero_const_bound ?_ (2 * C + C ^ 2) fun r hr => ?_
  · exact (continuousOn_trunc_B₁.const_smul (-2 : ℝ)).add (continuousOn_id.mul (continuousOn_trunc_B₁.pow 2))
  · have hb := (hC r hr).1
    have hr1 : r ≤ 1 := by linarith [hr.2]
    have h2 : Trunc.B₁ r ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have h3 : r * Trunc.B₁ r ^ 2 ≤ C ^ 2 := by nlinarith [hr.1, sq_nonneg (Trunc.B₁ r)]
    have h4 : 0 ≤ r * Trunc.B₁ r ^ 2 := mul_nonneg hr.1.le (sq_nonneg _)
    calc |-2 * Trunc.B₁ r + r * Trunc.B₁ r ^ 2| ≤ |-2 * Trunc.B₁ r| + |r * Trunc.B₁ r ^ 2| := abs_add_le _ _
      _ ≤ 2 * C + C ^ 2 := by
          rw [abs_mul, abs_of_nonneg h4]
          norm_num
          linarith

theorem nearZero_trunc_Ik (n : ℕ) : NearZero fun r => Trunc.B₁ r * r ^ n := by
  obtain ⟨C, _, hC⟩ := trunc_near_zero_bounds
  refine nearZero_const_bound (continuousOn_trunc_B₁.mul (continuousOn_id.pow n)) C fun r hr => ?_
  have hb := (hC r hr).1
  have hr1 : r ≤ 1 := by linarith [hr.2]
  rw [abs_mul, abs_pow, abs_of_pos hr.1]
  calc |Trunc.B₁ r| * r ^ n ≤ |Trunc.B₁ r| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hr.1.le hr1) (abs_nonneg _)
    _ ≤ C := by simpa using hb

theorem hasDerivAt_trunc_S₁ {t : ℝ} (ht : 0 < t) : HasDerivAt Trunc.S₁ (Trunc.B t * t) t :=
  intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_trunc_S₁ ht)
    ((continuousOn_trunc_B.mul continuousOn_id).stronglyMeasurableAtFilter isOpen_Ioi t ht)
    ((continuousOn_trunc_B.mul continuousOn_id).continuousAt (Ioi_mem_nhds ht))

theorem hasDerivAt_trunc_S₂ {t : ℝ} (ht : 0 < t) :
    HasDerivAt Trunc.S₂ (-2 * Trunc.B₁ t + t * Trunc.B₁ t ^ 2) t :=
  hasDerivAt_primitive nearZero_trunc_S₂ ht

/-- `H̃_k' = B̃₁ - (k/t) H̃_k`. -/
theorem hasDerivAt_trunc_H (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (Trunc.H n) (Trunc.B₁ t - n / t * Trunc.H n t) t := by
  have hI : HasDerivAt (fun x => ∫ r in (0 : ℝ)..x, Trunc.B₁ r * r ^ n) (Trunc.B₁ t * t ^ n) t :=
    hasDerivAt_primitive (nearZero_trunc_Ik n) ht
  have h2 := ((hasDerivAt_pow n t).inv (pow_ne_zero n ht.ne')).mul hI
  refine h2.congr_deriv ?_
  simp only [Pi.inv_apply, Trunc.H]
  rcases n with _ | m
  · simp
  · have hs : t ^ m ≠ 0 := pow_ne_zero m ht.ne'
    simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    field_simp
    ring

/-! ### On a segment the truncated data are the pieces -/

theorem trunc_B_eq_Bp {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : t ∈ seg j) : Trunc.B t = Bp j t := by
  simp only [Trunc.B, Trunc.modes, Bp]
  exact Finset.sum_congr rfl fun i _ => eqOn_u i hj ht

theorem trunc_B₁_eq_B1p {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : t ∈ seg j) : Trunc.B₁ t = B1p j t := by
  have ht0 : 0 < t := seg_subset_Ioi ht
  have hd : ∀ i ∈ Finset.range (Trunc.modes + 1), DifferentiableAt ℝ (u i) t := fun i _ =>
    ((contDiffOn_u i).differentiableOn (by norm_num) t ht0).differentiableAt (Ioi_mem_nhds ht0)
  have hsum : deriv Trunc.B t = ∑ i ∈ Finset.range (Trunc.modes + 1), deriv (u i) t := by
    have : Trunc.B = fun x => ∑ i ∈ Finset.range (Trunc.modes + 1), u i x := rfl
    rw [this]
    exact deriv_sum hd
  simp only [Trunc.B₁, B1p, hsum, one_div, Trunc.modes]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [iteratedDeriv_one]; exact (deriv_u_eq_piece i hj).1 ht

/-- **The truncated sector functions satisfy the radial ODEs of segment `j`** on `seg j`. -/
theorem sectorODE_trunc {j : ℕ} (hj : j ≤ 6) : SectorODE j (seg j) Trunc.S₁ Trunc.S₂ TH := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun i _ t ht => ?_⟩
  · refine (hasDerivAt_trunc_S₁ (seg_subset_Ioi ht)).congr_deriv ?_
    rw [Y1, trunc_B_eq_Bp hj ht, mul_comm]
  · refine (hasDerivAt_trunc_S₂ (seg_subset_Ioi ht)).congr_deriv ?_
    rw [Y2, trunc_B₁_eq_B1p hj ht]; ring
  · refine (hasDerivAt_trunc_H (k i) (seg_subset_Ioi ht)).congr_deriv ?_
    rw [trunc_B₁_eq_B1p hj ht, TH]; ring

theorem Q_eq_Qm (i : ℕ) {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : t ∈ seg j) : Q i t = Qm i j t := by
  simp only [Q, Qm, D1, iteratedDeriv_one, (deriv_D_eq_piece i hj).1 ht, eqOn_D i hj ht]

/-- **`f̃₀` is the model on segment `j`.** -/
theorem trunc_f₀_eq_F0m {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : t ∈ seg j) :
    Trunc.f₀ t = F0m j Trunc.S₁ Trunc.S₂ TH t := by
  have hD : ∀ i, D i t = Piece.D i j t := fun i => eqOn_D i hj ht
  have e1 : ∑ i ∈ Finset.range (Trunc.modes + 1), D i t / ((k i : ℝ) + 2) = dsumR j 0 39 t := by
    simp only [dsumR, zero_add, Trunc.modes]
    exact Finset.sum_congr rfl fun i _ => by rw [hD]; ring
  have e2 : ∑ i ∈ Finset.range (Trunc.modes + 1), (-2 * D i t + 2 * (k i : ℝ) * D i t * Trunc.H (k i) t) =
      linR j TH 0 39 t := by
    simp only [linR, zero_add, Trunc.modes, TH]
    exact Finset.sum_congr rfl fun i _ => by rw [hD]; ring
  have e3 : ∑ i ∈ Finset.range (Trunc.modes + 1), ∑ j' ∈ Finset.range (Trunc.modes + 1),
      (k i : ℝ) * (k j' : ℝ) / ((k i : ℝ) + (k j' : ℝ)) * D i t * D j' t = quadR j 0 39 t := by
    simp only [quadR, quadInR, zero_add, Trunc.modes, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [hD, hD]; push_cast; ring
  simp only [Trunc.f₀, F0m, e1, e2, e3]
  ring

/-- **`ẽ` is the model on segment `j`.** -/
theorem trunc_e_eq_Em {j : ℕ} (hj : j ≤ 6) {t : ℝ} (ht : t ∈ seg j) : Trunc.e t = Em j t := by
  have e : ∑ i ∈ Finset.range (Trunc.modes + 1), ∑ i' ∈ Finset.range (Trunc.modes + 1),
      Q i t * Q i' t / ((k i : ℝ) + (k i' : ℝ)) = eR j 0 39 t := by
    simp only [eR, eInR, zero_add, Trunc.modes, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [Q_eq_Qm i hj ht, Q_eq_Qm i' hj ht]; push_cast; ring
  rw [Trunc.e, Em, e]

/-! ### Chunks enclose the truncated calibration -/

/-- Along the real nodes `τs` of a chunk, each stored cell tuple encloses the values of `f̃₀ = Trunc.f₀` and
`ẽ = Trunc.e` on its cell, and each stored node tuple their values at its node. -/
@[expose] def TruncEncloses : List ℝ → List Tup → List Tup → Prop
  | a :: b :: rest, ct :: cts, nt :: nts =>
    (∀ t ∈ Icc a b, IV.Mem (Trunc.f₀ t) ct.f0 ∧ IV.Mem (Trunc.e t) ct.e0) ∧
      (IV.Mem (Trunc.f₀ b) nt.f0 ∧ IV.Mem (Trunc.e b) nt.e0) ∧ TruncEncloses (b :: rest) cts nts
  | _, _, _ => True

theorem TupEncl.mem_trunc {j : ℕ} (hj : j ≤ 6) {T : Set ℝ} (hT : T ⊆ seg j) {tp : Tup}
    (h : TupEncl T (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) tp) {t : ℝ} (ht : t ∈ T) :
    IV.Mem (Trunc.f₀ t) tp.f0 ∧ IV.Mem (Trunc.e t) tp.e0 := by
  obtain ⟨_, _, _, _, _, hm⟩ := h
  obtain ⟨m0, -, -, n0, -, -⟩ := hm t ht
  rw [trunc_f₀_eq_F0m hj (hT ht), trunc_e_eq_Em hj (hT ht)]
  exact ⟨m0, n0⟩

/-- The real nodes are nondecreasing. -/
@[expose] def NodesUp : List ℝ → Prop
  | a :: b :: rest => a ≤ b ∧ NodesUp (b :: rest)
  | _ => True

theorem le_lastR_of_nodesUp : ∀ (a : ℝ) (τs : List ℝ), NodesUp (a :: τs) → a ≤ lastR a τs
  | _, [], _ => le_rfl
  | _, b :: τs, ⟨hab, h⟩ => hab.trans (le_lastR_of_nodesUp b τs h)

theorem chunk_nodesUp {d : BasisData} {j : ℕ} : ∀ (S : SState) (v : IV 128) (vs : List (IV 128))
    (cts nts : List Tup) (S' : SState) (a : ℝ) (τs : List ℝ),
    chunkCheck d j S (v :: vs) cts nts S' = true → IV.Mem a v → List.Forall₂ IV.Mem τs vs → NodesUp (a :: τs)
  | _, _, _, _, _, _, _, [], _, _, _ => trivial
  | S, v, u :: vs, ct :: cts, nt :: nts, S', a, b :: τs, hc, ha, List.Forall₂.cons hb hbs => by
    simp only [chunkCheck, Bool.and_eq_true] at hc
    have hsep : SInt.blt v.hi u.lo = true := by
      simp only [stepCheck, stepCheckWith, Bool.and_eq_true] at hc; exact hc.1.1.1
    have hab : a < b := by
      have : ((v.hi.toInt : ℤ) : ℝ) < ((u.lo.toInt : ℤ) : ℝ) := by exact_mod_cast (SInt.blt_iff _ _).mp hsep
      have hp : (0 : ℝ) < 2 ^ 128 := by positivity
      nlinarith [ha.2, hb.1]
    exact ⟨hab.le, chunk_nodesUp _ u vs cts nts S' b τs hc.2 hb hbs⟩
  | _, _, _ :: _, [], _, _, _, _ :: _, hc, _, List.Forall₂.cons _ _ => by simp [chunkCheck] at hc
  | _, _, _ :: _, _ :: _, [], _, _, _ :: _, hc, _, List.Forall₂.cons _ _ => by simp [chunkCheck] at hc

theorem truncEncloses_of {j : ℕ} (hj : j ≤ 6) :
    ∀ (a : ℝ) (τs : List ℝ) (cts nts : List Tup), Icc a (lastR a τs) ⊆ seg j → NodesUp (a :: τs) →
      TableEncloses j Trunc.S₁ Trunc.S₂ TH (a :: τs) cts nts → TruncEncloses (a :: τs) cts nts
  | a, b :: rest, ct :: cts, nt :: nts, hseg, ⟨hab, hup⟩, ⟨hc, hn, hr⟩ => by
    have hlast : b ≤ lastR b rest := le_lastR_of_nodesUp b rest hup
    have hsub : Icc a b ⊆ seg j := fun t ht => hseg ⟨ht.1, ht.2.trans hlast⟩
    refine ⟨fun t ht => hc.mem_trunc hj hsub ht, hn.mem_trunc hj (fun t ht => ?_) rfl, ?_⟩
    · rw [ht]; exact hsub ⟨hab, le_rfl⟩
    · exact truncEncloses_of hj b rest cts nts (fun t ht => hseg ⟨hab.trans ht.1, ht.2⟩) hup hr
  | _, [], _, _, _, _, _ => trivial
  | _, _ :: _, [], _, _, _, _ => trivial
  | _, _ :: _, _ :: _, [], _, _, _ => trivial

/-- **Soundness of a chunk for the truncated calibration.** If the chunk check of segment `j` passes, the real
nodes `a :: τs` lie in the node intervals, `[a, last] ⊆ seg j`, and the checkpoint `S` encloses `Trunc.S₁`,
`Trunc.S₂`, `Trunc.H (k i)` at `a`, then the stored tuples enclose the model of `f̃₀, ẽ` (with derivatives) on
every cell and at every node, the values of `Trunc.f₀`, `Trunc.e` there, and the final checkpoint `S'` encloses the
truncated sector functions at the last node. -/
theorem chunkCheck_sound_trunc {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) {S : SState} {v : IV 128}
    {vs : List (IV 128)} {cts nts : List Tup} {S' : SState} {a : ℝ} {τs : List ℝ}
    (hc : chunkCheck d j S (v :: vs) cts nts S' = true) (ha : IV.Mem a v) (hτ : List.Forall₂ IV.Mem τs vs)
    (hseg : Icc a (lastR a τs) ⊆ seg j) (hS : StateOn {a} Trunc.S₁ Trunc.S₂ TH S) :
    TableEncloses j Trunc.S₁ Trunc.S₂ TH (a :: τs) cts nts ∧ TruncEncloses (a :: τs) cts nts ∧
      StateOn {lastR a τs} Trunc.S₁ Trunc.S₂ TH S' := by
  obtain ⟨hT, hS'⟩ := chunkCheck_sound hd hj S v vs cts nts S' a τs hc ha hτ ((sectorODE_trunc hj).mono hseg) hS
  exact ⟨hT, truncEncloses_of hj a τs cts nts hseg (chunk_nodesUp S v vs cts nts S' a τs hc ha hτ) hT, hS'⟩

/-- **Induction over the chunks of a segment**: if every chunk `c < N` of segment `j` passes its
check from the literal checkpoint `ckpt c` to `ckpt (c + 1)`, its real nodes `a c :: τs c` lie in its node
intervals and in `seg j`, consecutive chunks share their end node, and `ckpt 0` encloses the truncated sector
functions at `a 0`, then every checkpoint `ckpt c`, `c ≤ N`, encloses them at `a c`. -/
theorem chunks_stateOn_trunc {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) {ckpt : ℕ → SState}
    {v : ℕ → IV 128} {vs : ℕ → List (IV 128)} {cts nts : ℕ → List Tup} {a : ℕ → ℝ} {τs : ℕ → List ℝ} {N : ℕ}
    (hc : ∀ c < N, chunkCheck d j (ckpt c) (v c :: vs c) (cts c) (nts c) (ckpt (c + 1)) = true)
    (ha : ∀ c < N, IV.Mem (a c) (v c)) (hτ : ∀ c < N, List.Forall₂ IV.Mem (τs c) (vs c))
    (hlink : ∀ c < N, lastR (a c) (τs c) = a (c + 1)) (hseg : ∀ c < N, Icc (a c) (lastR (a c) (τs c)) ⊆ seg j)
    (h0 : StateOn {a 0} Trunc.S₁ Trunc.S₂ TH (ckpt 0)) :
    ∀ c ≤ N, StateOn {a c} Trunc.S₁ Trunc.S₂ TH (ckpt c)
  | 0, _ => h0
  | c + 1, hcN => by
    have hc' : c < N := by omega
    have ih := chunks_stateOn_trunc hd hj hc ha hτ hlink hseg h0 c hc'.le
    have := (chunkCheck_sound_trunc hd hj (hc c hc') (ha c hc') (hτ c hc') (hseg c hc') ih).2.2
    rwa [hlink c hc'] at this

/-- **The chunks of a segment enclose the truncated calibration**: under the hypotheses of
`chunks_stateOn_trunc`, every chunk `c < N` satisfies `TableEncloses` (the model with its derivatives) and
`TruncEncloses` (the values of `Trunc.f₀`, `Trunc.e`) on its cells and nodes. -/
theorem chunks_sound_trunc {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) {ckpt : ℕ → SState}
    {v : ℕ → IV 128} {vs : ℕ → List (IV 128)} {cts nts : ℕ → List Tup} {a : ℕ → ℝ} {τs : ℕ → List ℝ} {N : ℕ}
    (hc : ∀ c < N, chunkCheck d j (ckpt c) (v c :: vs c) (cts c) (nts c) (ckpt (c + 1)) = true)
    (ha : ∀ c < N, IV.Mem (a c) (v c)) (hτ : ∀ c < N, List.Forall₂ IV.Mem (τs c) (vs c))
    (hlink : ∀ c < N, lastR (a c) (τs c) = a (c + 1)) (hseg : ∀ c < N, Icc (a c) (lastR (a c) (τs c)) ⊆ seg j)
    (h0 : StateOn {a 0} Trunc.S₁ Trunc.S₂ TH (ckpt 0)) (c : ℕ) (hcN : c < N) :
    TableEncloses j Trunc.S₁ Trunc.S₂ TH (a c :: τs c) (cts c) (nts c) ∧
      TruncEncloses (a c :: τs c) (cts c) (nts c) := by
  have hS := chunks_stateOn_trunc hd hj hc ha hτ hlink hseg h0 c hcN.le
  obtain ⟨h1, h2, -⟩ := chunkCheck_sound_trunc hd hj (hc c hcN) (ha c hcN) (hτ c hcN) (hseg c hcN) hS
  exact ⟨h1, h2⟩

end SandierSerfaty.Certificate.Table
