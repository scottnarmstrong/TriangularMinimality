/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.Model
public import SandierSerfaty.Certificate.Table.Midpoint

/-!
# Soundness of the propagation and of a table chunk (`TableEncloses`)

For real nodes `a < b` in the node intervals `v`, `u` of segment `j`, sector functions `S1, S2, H` satisfying
the ODEs of the segment on `[a, b]` (`SectorODE`), and a state enclosing their values at `a`:

* `mem_midStep`: the midpoint rule with its error `(b - a)³/24 · sup|Y''|` (`comp:midpoint`) encloses
  `S1 b`, `S2 b`; for `H̃_k` the same rule is applied to the antiderivative `r ↦ (r/b)^k H(r)` of
  `(r/b)^k B̃₁(r)` (`comp:propagation`), so the new state encloses the values at `b`
  (`stepState_sound`);
* `cellState_sound`: by the mean value theorem, the cell state encloses the values on all of `[a, b]`
  (`comp:cell-integrals`);
* `stepCheck_sound`: one step of the chunk check gives `a < b`, the state at `b`, the cell tuple on `[a, b]` and
  the node tuple at `b` (`fh_sound`);
* `chunkCheck_sound`: along a whole chunk, from the checkpoint at the first node to the checkpoint at the last
  one: `TableEncloses j S1 S2 H τs cellTups nodeTups` and the final state.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Table

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-! ### Elementary interval facts -/

theorem hi_mag_of_pos {X : IV 128} {x : ℝ} (hx : IV.Mem x X) (hpos : 0 < x) :
    ((X.hi.toInt : ℤ) : ℝ) = X.hi.mag ∧ x * 2 ^ 128 ≤ X.hi.mag := by
  have h2 := hx.2
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hneg : X.hi.isNeg = false := by
    cases hc : X.hi.isNeg
    · rfl
    · have : ((X.hi.toInt : ℤ) : ℝ) ≤ 0 := by exact_mod_cast SInt.toInt_nonpos_of_isNeg_true hc
      nlinarith
  have e : ((X.hi.toInt : ℤ) : ℝ) = X.hi.mag := by rw [SInt.toInt_eq, hneg]; simp
  exact ⟨e, e ▸ h2⟩

theorem abs_le_two_magHi {x : ℝ} {c : IV 128} (h : IV.Mem (x / 2) c) : |x| ≤ 2 * ((magHi c : ℝ) / 2 ^ 128) := by
  have := abs_le_magHi h
  rw [abs_div, abs_two] at this
  linarith

theorem le_cdivNat {m d : ℕ} (hd : 0 < d) : (m : ℝ) / d ≤ (SInt.cdivNat m d : ℝ) := by
  have := SInt.le_cdivNat_mul m d hd
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast this

/-! ### The midpoint step -/

theorem mem_midStep {F f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {Tc : Set ℝ} (hsub : Icc a b ⊆ Tc)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x) {yc : IJet2 128} (hyc : JetEncl2 Tc f yc)
    {S Hiv ym : IV 128} (hS : IV.Mem (F a) S) (hH : IV.Mem (b - a) Hiv) (hm : IV.Mem (f ((a + b) / 2)) ym) :
    IV.Mem (F b) (midStep S Hiv ym yc) := by
  obtain ⟨f₁, f₂, d0, d1, hb⟩ := hyc
  set M : ℝ := 2 * ((magHi yc.c2 : ℝ) / 2 ^ 128) with hM
  have hbd : ∀ x ∈ Icc a b, |f₂ x| ≤ M := fun x hx => abs_le_two_magHi (hb x (hsub hx)).2.2
  have key := abs_sub_midpoint_le hab.le hF (fun x hx => d0 x (hsub hx)) (fun x hx => d1 x (hsub hx)) hbd
  obtain ⟨eH, hH'⟩ := hi_mag_of_pos hH (by linarith)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  set Hm : ℝ := (Hiv.hi.mag : ℝ) with hHm
  have hba : b - a ≤ Hm / 2 ^ 128 := by rw [le_div_iff₀ hp]; exact hH'
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  refine IV.mem_addRad (IV.mem_add hS (IV.mem_mul hH hm)) ?_
  have e1 : |F b - (F a + (b - a) * f ((a + b) / 2))| = |F b - F a - (b - a) * f ((a + b) / 2)| := by
    congr 1; ring
  rw [e1]
  have hcube : (b - a) ^ 3 ≤ (Hm / 2 ^ 128) ^ 3 := pow_le_pow_left₀ (by linarith) hba 3
  have h2 : (b - a) ^ 3 / 24 * M * 2 ^ 128 ≤ (Hm ^ 3 * (magHi yc.c2 : ℝ)) / (12 * 2 ^ 384) := by
    have : (b - a) ^ 3 / 24 * M * 2 ^ 128 ≤ (Hm / 2 ^ 128) ^ 3 / 24 * M * 2 ^ 128 := by gcongr
    refine this.trans (le_of_eq ?_)
    rw [hM]; field_simp; ring
  refine (mul_le_mul_of_nonneg_right key hp.le).trans (h2.trans ?_)
  have hd : 0 < Nat.mul 12 (Nat.shiftLeft 1 384) := by simp only [Nat.mul_eq, SInt.nat_shiftLeft_eq]; positivity
  have := le_cdivNat (m := Nat.mul (Nat.pow Hiv.hi.mag 3) (magHi yc.c2)) hd
  simp only [Nat.mul_eq, Nat.pow_eq, SInt.nat_shiftLeft_eq, one_mul] at this
  push_cast [-Nat.reducePow] at this
  unfold errRad
  simp only [Nat.mul_eq, Nat.pow_eq, SInt.nat_shiftLeft_eq, one_mul]
  exact this

/-! ### Powers -/

theorem hasDerivAt_pow_mul {H : ℝ → ℝ} {x c : ℝ} (hx : 0 < x) (kk : ℕ) (hk : 1 ≤ kk) (B : ℝ)
    (hH : HasDerivAt H (B - (kk : ℝ) * H x / x) x) :
    HasDerivAt (fun r => (r * c) ^ kk * H r) ((x * c) ^ kk * B) x := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h1 : HasDerivAt (fun r => (r * c) ^ (1 + n)) (((1 + n : ℕ) : ℝ) * (x * c) ^ n * c) x := by
    have := ((hasDerivAt_id x).mul_const c).pow (1 + n)
    simp only [id] at this
    refine this.congr_deriv ?_
    simp [add_comm 1 n]
  have := h1.mul hH
  refine this.congr_deriv ?_
  rw [pow_add, pow_one]
  field_simp
  push_cast
  ring

theorem ratioJ_sound {j : ℕ} {T : Set ℝ} {pt : Pt} (hp : PtValid j T pt) {b : ℝ} {ui : IV 128}
    (hb : IV.Mem b ui) (hpos : IV.posB ui = true) : JetEncl2 T (fun r => r * b⁻¹) (ratioJ pt ui) :=
  jetEncl2_of_eq (JetEncl2.scale (mem_invPos hpos hb) hp.t) fun t => by ring

theorem pow6J_sound {T : Set ℝ} {g : ℝ → ℝ} {J : IJet2 128} (h : JetEncl2 T g J) :
    JetEncl2 T (fun r => g r ^ 6) (pow6J J) :=
  jetEncl2_of_eq (((h.mul h).mul h).mul ((h.mul h).mul h)) fun t => by ring

/-! ### The new state -/

section Step

variable {j : ℕ} {a b : ℝ} {S1 S2 : ℝ → ℝ} {H : ℕ → ℝ → ℝ}

/-- One `H̃_k` value: the midpoint rule for `r ↦ (r/b)^k H(r)`. -/
theorem mem_hNew (hab : a < b) (ha0 : 0 < a) {Tm Tc : Set ℝ} {ptm ptc : Pt} (hpm : PtValid j Tm ptm)
    (hpc : PtValid j Tc ptc) (hmid : (a + b) / 2 ∈ Tm) (hsub : Icc a b ⊆ Tc) {i : ℕ} (hk1 : 1 ≤ k i)
    (hH : ∀ x ∈ Icc a b, HasDerivAt (H i) (B1p j x - (k i : ℝ) * H i x / x) x)
    {Hiv sv h : IV 128} (hHiv : IV.Mem (b - a) Hiv) (hsv : IV.Mem ((a * b⁻¹) ^ k i) sv) (hh : IV.Mem (H i a) h)
    {pm pc : IJet2 128} (hpmJ : JetEncl2 Tm (fun r => (r * b⁻¹) ^ k i) pm)
    (hpcJ : JetEncl2 Tc (fun r => (r * b⁻¹) ^ k i) pc) :
    IV.Mem (H i b) (hNew Hiv ptm ptc sv pm pc h) := by
  have hb0 : 0 < b := by linarith
  have hF : ∀ x ∈ Icc a b, HasDerivAt (fun r => (r * b⁻¹) ^ k i * H i r)
      ((fun r => (r * b⁻¹) ^ k i * B1p j r) x) x := fun x hx =>
    hasDerivAt_pow_mul (by linarith [hx.1]) (k i) hk1 _ (hH x hx)
  obtain ⟨_, _, _, _, hbm⟩ := hpmJ.mul hpm.b1
  have hm : IV.Mem ((fun r => (r * b⁻¹) ^ k i * B1p j r) ((a + b) / 2)) (IJet2.mul pm ptm.b1).c0 :=
    (hbm _ hmid).1
  have := mem_midStep hab hsub hF (hpcJ.mul hpc.b1) (IV.mem_mul hsv hh) hHiv hm
  have e : (b * b⁻¹) ^ k i * H i b = H i b := by rw [mul_inv_cancel₀ hb0.ne', one_pow, one_mul]
  rw [e] at this
  exact this

theorem hLoop_length (Hiv : IV 128) (ptm ptc : Pt) (sv6 : IV 128) (pm6 pc6 : IJet2 128) :
    ∀ (sv : IV 128) (pm pc : IJet2 128) (hs : List (IV 128)),
      (hLoop Hiv ptm ptc sv6 pm6 pc6 sv pm pc hs).length = hs.length
  | _, _, _, [] => rfl
  | sv, pm, pc, _ :: hs => by simp [hLoop, hLoop_length Hiv ptm ptc sv6 pm6 pc6 _ _ _ hs]

theorem hsStep_length (Hiv : IV 128) (ptm ptc : Pt) (sv6 : IV 128) (pm6 pc6 : IJet2 128) :
    ∀ hs : List (IV 128), (hsStep Hiv ptm ptc sv6 pm6 pc6 hs).length = hs.length
  | [] => rfl
  | _ :: hs => by simp [hsStep, hLoop_length]

theorem hLoop_sound (hab : a < b) (ha0 : 0 < a) {Tm Tc : Set ℝ} {ptm ptc : Pt} (hpm : PtValid j Tm ptm)
    (hpc : PtValid j Tc ptc) (hmid : (a + b) / 2 ∈ Tm) (hsub : Icc a b ⊆ Tc)
    (hode : SectorODE j (Icc a b) S1 S2 H) {Hiv : IV 128} (hHiv : IV.Mem (b - a) Hiv) {sv6 : IV 128}
    (hsv6 : IV.Mem ((a * b⁻¹) ^ 6) sv6) {pm6 pc6 : IJet2 128}
    (hpm6 : JetEncl2 Tm (fun r => (r * b⁻¹) ^ 6) pm6) (hpc6 : JetEncl2 Tc (fun r => (r * b⁻¹) ^ 6) pc6) :
    ∀ (hs : List (IV 128)) (m : ℕ) (sv : IV 128) (pm pc : IJet2 128), 1 ≤ m → m + hs.length ≤ 39 →
      IV.Mem ((a * b⁻¹) ^ (6 * m)) sv → JetEncl2 Tm (fun r => (r * b⁻¹) ^ (6 * m)) pm →
      JetEncl2 Tc (fun r => (r * b⁻¹) ^ (6 * m)) pc → EnclFrom (fun i => H i a) m hs →
      EnclFrom (fun i => H i b) m (hLoop Hiv ptm ptc sv6 pm6 pc6 sv pm pc hs)
  | [], _, _, _, _, _, _, _, _, _, _ => trivial
  | h :: hs, m, sv, pm, pc, hm, hl, hsv, hpmJ, hpcJ, ⟨hh, hhs⟩ => by
    have hk : k m = 6 * m := k_of_pos (by omega)
    refine ⟨?_, ?_⟩
    · rw [← hk] at hsv hpmJ hpcJ
      exact mem_hNew hab ha0 hpm hpc hmid hsub (by rw [hk]; omega) (hode.h m (by simp at hl; omega))
        hHiv hsv hh hpmJ hpcJ
    · have e : 6 * (m + 1) = 6 * m + 6 := by ring
      refine hLoop_sound hab ha0 hpm hpc hmid hsub hode hHiv hsv6 hpm6 hpc6 hs (m + 1) _ _ _ (by omega)
        (by simp at hl; omega) ?_ ?_ ?_ hhs
      · exact mem_of_eq (IV.mem_mul hsv hsv6) (by rw [e, pow_add])
      · exact jetEncl2_of_eq (hpmJ.mul hpm6) fun t => by rw [e, pow_add]
      · exact jetEncl2_of_eq (hpcJ.mul hpc6) fun t => by rw [e, pow_add]

theorem hsStep_sound (hab : a < b) (ha0 : 0 < a) {Tm Tc : Set ℝ} {ptm ptc : Pt} (hpm : PtValid j Tm ptm)
    (hpc : PtValid j Tc ptc) (hmid : (a + b) / 2 ∈ Tm) (hsub : Icc a b ⊆ Tc)
    (hode : SectorODE j (Icc a b) S1 S2 H) {Hiv : IV 128} (hHiv : IV.Mem (b - a) Hiv) {sv6 : IV 128}
    (hsv6 : IV.Mem ((a * b⁻¹) ^ 6) sv6) {pm6 pc6 : IJet2 128}
    (hpm6 : JetEncl2 Tm (fun r => (r * b⁻¹) ^ 6) pm6) (hpc6 : JetEncl2 Tc (fun r => (r * b⁻¹) ^ 6) pc6)
    {hs : List (IV 128)} (hlen : hs.length = 39) (hH : EnclFrom (fun i => H i a) 0 hs) :
    EnclFrom (fun i => H i b) 0 (hsStep Hiv ptm ptc sv6 pm6 pc6 hs) := by
  match hs, hlen, hH with
  | h :: hs, hlen, ⟨hh, hhs⟩ =>
    have hk : k 0 = 6 := rfl
    refine ⟨?_, ?_⟩
    · rw [← hk] at hsv6 hpm6 hpc6
      exact mem_hNew hab ha0 hpm hpc hmid hsub (by rw [hk]; omega) (hode.h 0 (by omega)) hHiv hsv6 hh hpm6 hpc6
    · exact hLoop_sound hab ha0 hpm hpc hmid hsub hode hHiv hsv6 hpm6 hpc6 hs 1 _ _ _ le_rfl
        (by simp at hlen; omega) (by simpa using hsv6) (by simpa using hpm6) (by simpa using hpc6) hhs

/-! ### The cell state -/

/-- Mean value bound: `F t ∈ F a + [0, b - a]·range f` on `[a, b]`. -/
theorem mem_cell_of_deriv {F f : ℝ → ℝ} (hab : a < b) (hF : ∀ x ∈ Icc a b, HasDerivAt F (f x) x)
    {c0 S Hiv : IV 128} (hf : ∀ x ∈ Icc a b, IV.Mem (f x) c0) (hS : IV.Mem (F a) S) (hHiv : IV.Mem (b - a) Hiv)
    {t : ℝ} (ht : t ∈ Icc a b) : IV.Mem (F t) (IV.add S (IV.mul (zeroTo Hiv) c0)) := by
  obtain ⟨eH, hH'⟩ := hi_mag_of_pos hHiv (by linarith)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hz : ∀ s, 0 ≤ s → s ≤ b - a → IV.Mem s (zeroTo Hiv) := fun s h0 h1 => by
    refine ⟨?_, ?_⟩
    · simp [zeroTo, SInt.zero, SInt.toInt_mk]; positivity
    · simp only [zeroTo]; rw [eH]; nlinarith
  rcases ht.1.eq_or_lt with rfl | hlt
  · have := IV.mem_add hS (IV.mem_mul (hz 0 le_rfl (by linarith)) (hf a ⟨le_rfl, hab.le⟩))
    simpa using this
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope F f hlt
      (fun x hx => (hF x ⟨hx.1, hx.2.trans ht.2⟩).continuousAt.continuousWithinAt)
      (fun x hx => hF x ⟨hx.1.le, hx.2.le.trans ht.2⟩)
    have hξ' : ξ ∈ Icc a b := ⟨hξ.1.le, hξ.2.le.trans ht.2⟩
    have e : F t = F a + (t - a) * f ξ := by
      rw [hslope]; field_simp [(sub_pos.2 hlt).ne']; ring
    rw [e]
    exact IV.mem_add hS (IV.mem_mul (hz _ (by linarith) (by linarith [ht.2])) (hf ξ hξ'))

/-- The cell value of `H̃_k`: `(a/t)^k H(a) ± (b - a) sup|B̃₁|`. -/
theorem mem_hCell (hab : a < b) (ha0 : 0 < a) {i : ℕ} (hk1 : 1 ≤ k i)
    (hH : ∀ x ∈ Icc a b, HasDerivAt (H i) (B1p j x - (k i : ℝ) * H i x / x) x) {c0 Hiv cv h : IV 128}
    (hb1 : ∀ x ∈ Icc a b, IV.Mem (B1p j x) c0) (hHiv : IV.Mem (b - a) Hiv) (hh : IV.Mem (H i a) h)
    {t : ℝ} (ht : t ∈ Icc a b) (hcv : IV.Mem ((a * t⁻¹) ^ k i) cv) :
    IV.Mem (H i t) (IV.addRad (IV.mul cv h) (SInt.cdivNat (Nat.mul Hiv.hi.mag (magHi c0)) (Nat.shiftLeft 1 128))) := by
  obtain ⟨eH, hH'⟩ := hi_mag_of_pos hHiv (by linarith)
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have ht0 : 0 < t := by linarith [ht.1]
  have hG : ∀ x ∈ Icc a b, HasDerivAt (fun r => (r * 1) ^ k i * H i r) ((x * 1) ^ k i * B1p j x) x :=
    fun x hx => hasDerivAt_pow_mul (by linarith [hx.1]) (k i) hk1 _ (hH x hx)
  -- `t^k H(t) = a^k H(a) + (t - a) ξ^k B̃₁(ξ)`
  obtain ⟨ξ, hξ, hrem⟩ : ∃ ξ ∈ Icc a t, t ^ k i * H i t = a ^ k i * H i a + (t - a) * (ξ ^ k i * B1p j ξ) := by
    obtain h | hlt := ht.1.eq_or_lt
    · subst h; exact ⟨_, ⟨le_rfl, le_rfl⟩, by ring⟩
    · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun r => (r * 1) ^ k i * H i r)
        (fun x => (x * 1) ^ k i * B1p j x) hlt
        (fun x hx => (hG x ⟨hx.1, hx.2.trans ht.2⟩).continuousAt.continuousWithinAt)
        (fun x hx => hG x ⟨hx.1.le, hx.2.le.trans ht.2⟩)
      refine ⟨ξ, ⟨hξ.1.le, hξ.2.le⟩, ?_⟩
      simp only [mul_one] at hslope
      rw [hslope]; field_simp [(sub_pos.2 hlt).ne']; ring
  have hξab : ξ ∈ Icc a b := ⟨hξ.1, hξ.2.trans ht.2⟩
  have hξ0 : 0 < ξ := by linarith [hξ.1]
  have hq : 0 ≤ (ξ * t⁻¹) ^ k i ∧ (ξ * t⁻¹) ^ k i ≤ 1 := by
    have h0 : 0 ≤ ξ * t⁻¹ := by positivity
    have h1 : ξ * t⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one ht0]; exact hξ.2
    exact ⟨pow_nonneg h0 _, pow_le_one₀ h0 h1⟩
  have eHt : H i t = (a * t⁻¹) ^ k i * H i a + (t - a) * ((ξ * t⁻¹) ^ k i * B1p j ξ) := by
    have htk : (t ^ k i) ≠ 0 := pow_ne_zero _ ht0.ne'
    rw [mul_pow, mul_pow, inv_pow]
    field_simp
    linear_combination hrem
  refine IV.mem_addRad (IV.mem_mul hcv hh) ?_
  rw [eHt, add_sub_cancel_left, abs_mul, abs_mul, abs_of_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t - a),
    abs_of_nonneg hq.1]
  have hB := abs_le_magHi (hb1 ξ hξab)
  have hta : t - a ≤ (Hiv.hi.mag : ℝ) / 2 ^ 128 := by
    rw [le_div_iff₀ hp]; nlinarith [ht.2]
  have hd : 0 < Nat.shiftLeft 1 128 := by rw [SInt.nat_shiftLeft_eq]; positivity
  have hN : ((Nat.shiftLeft 1 128 : ℕ) : ℝ) = 2 ^ 128 := by rw [SInt.nat_shiftLeft_eq]; push_cast; ring
  have hB0 : 0 ≤ (magHi c0 : ℝ) / 2 ^ 128 := by positivity
  calc (t - a) * ((ξ * t⁻¹) ^ k i * |B1p j ξ|) * 2 ^ 128
      ≤ ((Hiv.hi.mag : ℝ) / 2 ^ 128) * (1 * ((magHi c0 : ℝ) / 2 ^ 128)) * 2 ^ 128 := by
        gcongr
        exact hq.2
    _ = ((Nat.mul Hiv.hi.mag (magHi c0) : ℕ) : ℝ) / ((Nat.shiftLeft 1 128 : ℕ) : ℝ) := by
        rw [hN, Nat.mul_eq, Nat.cast_mul]; field_simp
    _ ≤ _ := le_cdivNat hd

theorem hCellLoop_length (rad : ℕ) (cv6 : IV 128) :
    ∀ (cv : IV 128) (hs : List (IV 128)), (hCellLoop rad cv6 cv hs).length = hs.length
  | _, [] => rfl
  | cv, _ :: hs => by simp [hCellLoop, hCellLoop_length rad cv6 _ hs]

theorem hsCell_length (rad : ℕ) (cv6 : IV 128) : ∀ hs : List (IV 128), (hsCell rad cv6 hs).length = hs.length
  | [] => rfl
  | _ :: hs => by simp [hsCell, hCellLoop_length]

theorem hCellLoop_sound (hab : a < b) (ha0 : 0 < a) (hode : SectorODE j (Icc a b) S1 S2 H) {c0 Hiv : IV 128}
    (hb1 : ∀ x ∈ Icc a b, IV.Mem (B1p j x) c0) (hHiv : IV.Mem (b - a) Hiv) {cv6 : IV 128} {t : ℝ}
    (ht : t ∈ Icc a b) (hcv6 : IV.Mem ((a * t⁻¹) ^ 6) cv6) :
    ∀ (hs : List (IV 128)) (m : ℕ) (cv : IV 128), 1 ≤ m → m + hs.length ≤ 39 →
      IV.Mem ((a * t⁻¹) ^ (6 * m)) cv → EnclFrom (fun i => H i a) m hs →
      EnclFrom (fun i => H i t) m
        (hCellLoop (SInt.cdivNat (Nat.mul Hiv.hi.mag (magHi c0)) (Nat.shiftLeft 1 128)) cv6 cv hs)
  | [], _, _, _, _, _, _ => trivial
  | h :: hs, m, cv, hm, hl, hcv, ⟨hh, hhs⟩ => by
    have hk : k m = 6 * m := k_of_pos (by omega)
    refine ⟨?_, hCellLoop_sound hab ha0 hode hb1 hHiv ht hcv6 hs (m + 1) _ (by omega) (by simp at hl; omega)
      (mem_of_eq (IV.mem_mul hcv hcv6) (by rw [show 6 * (m + 1) = 6 * m + 6 by ring, pow_add])) hhs⟩
    rw [← hk] at hcv
    exact mem_hCell hab ha0 (by rw [hk]; omega) (hode.h m (by simp at hl; omega)) hb1 hHiv hh ht hcv

/-- **The cell state** encloses the sector functions on all of `[a, b]`. -/
theorem cellState_sound (hab : a < b) (ha0 : 0 < a) {Tc : Set ℝ} {ptc : Pt} (hpc : PtValid j Tc ptc)
    (hsub : Icc a b ⊆ Tc) (hode : SectorODE j (Icc a b) S1 S2 H) {Hiv : IV 128} (hHiv : IV.Mem (b - a) Hiv)
    {cv6 : IV 128} (hcv6 : ∀ t ∈ Icc a b, IV.Mem ((a * t⁻¹) ^ 6) cv6) {S : SState}
    (hS : StateOn {a} S1 S2 H S) : StateOn (Icc a b) S1 S2 H (cellState Hiv ptc cv6 S) := by
  have hy1 : ∀ x ∈ Icc a b, IV.Mem (Y1 j x) ptc.y1.c0 := fun x hx => by
    obtain ⟨_, _, _, _, hb⟩ := hpc.y1; exact (hb x (hsub hx)).1
  have hy2 : ∀ x ∈ Icc a b, IV.Mem (Y2 j x) ptc.y2.c0 := fun x hx => by
    obtain ⟨_, _, _, _, hb⟩ := hpc.y2; exact (hb x (hsub hx)).1
  have hb1 : ∀ x ∈ Icc a b, IV.Mem (B1p j x) ptc.b1.c0 := fun x hx => by
    obtain ⟨_, _, _, _, hb⟩ := hpc.b1; exact (hb x (hsub hx)).1
  have ha : a ∈ ({a} : Set ℝ) := rfl
  refine ⟨fun t ht => mem_cell_of_deriv hab hode.s1 hy1 (hS.s1 a ha) hHiv ht,
    fun t ht => mem_cell_of_deriv hab hode.s2 hy2 (hS.s2 a ha) hHiv ht, fun t ht => ?_, ?_⟩
  · have hH := hS.hs a ha
    have hlen := hS.len
    simp only [cellState]
    match hs : S.hs, hlen, hH with
    | h :: hs', hlen', ⟨hh, hhs⟩ =>
      refine ⟨mem_hCell hab ha0 (by simp [k]) (hode.h 0 (by omega)) hb1 hHiv hh ht (hcv6 t ht), ?_⟩
      exact hCellLoop_sound hab ha0 hode hb1 hHiv ht (hcv6 t ht) hs' 1 _ le_rfl (by simp at hlen'; omega)
        (by simpa using hcv6 t ht) hhs
  · simp only [cellState, hsCell_length, hS.len]

/-- **The state at the next node.** -/
theorem stepWith_sound (hab : a < b) (ha0 : 0 < a) {Tm Tc : Set ℝ} {ptm ptc : Pt} (hpm : PtValid j Tm ptm)
    (hpc : PtValid j Tc ptc) (hmid : (a + b) / 2 ∈ Tm) (hsub : Icc a b ⊆ Tc)
    (hode : SectorODE j (Icc a b) S1 S2 H) {Hiv : IV 128} (hHiv : IV.Mem (b - a) Hiv) {sv6 : IV 128}
    (hsv6 : IV.Mem ((a * b⁻¹) ^ 6) sv6) {pm6 pc6 : IJet2 128}
    (hpm6 : JetEncl2 Tm (fun r => (r * b⁻¹) ^ 6) pm6) (hpc6 : JetEncl2 Tc (fun r => (r * b⁻¹) ^ 6) pc6)
    {S : SState} (hS : StateOn {a} S1 S2 H S) :
    StateOn {b} S1 S2 H (stepWith Hiv ptm ptc sv6 pm6 pc6 S) := by
  have ha : a ∈ ({a} : Set ℝ) := rfl
  have hy1m : IV.Mem (Y1 j ((a + b) / 2)) ptm.y1.c0 := by
    obtain ⟨_, _, _, _, hb⟩ := hpm.y1; exact (hb _ hmid).1
  have hy2m : IV.Mem (Y2 j ((a + b) / 2)) ptm.y2.c0 := by
    obtain ⟨_, _, _, _, hb⟩ := hpm.y2; exact (hb _ hmid).1
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [hx]; exact mem_midStep hab hsub hode.s1 (hpc.y1) (hS.s1 a ha) hHiv hy1m
  · rw [hx]; exact mem_midStep hab hsub hode.s2 (hpc.y2) (hS.s2 a ha) hHiv hy2m
  · rw [hx]
    exact hsStep_sound hab ha0 hpm hpc hmid hsub hode hHiv hsv6 hpm6 hpc6 hS.len (hS.hs a ha)
  · simp only [stepWith, hsStep_length, hS.len]

end Step

/-! ### One step and a chunk -/

theorem okSet_sound {X : IV 128} (h : okSet X = true) : IV.posB X = true ∧ SInt.blt X.lo X.hi = true := by
  simpa [okSet] using h

/-- **One step of the chunk check.** -/
theorem stepCheck_sound {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) {v u : IV 128} {S : SState}
    {ct nt : Tup} (hc : stepCheck d j v u S ct nt = true) {a b : ℝ} (ha : IV.Mem a v) (hb : IV.Mem b u)
    {S1 S2 : ℝ → ℝ} {H : ℕ → ℝ → ℝ} (hode : SectorODE j (Icc a b) S1 S2 H) (hS : StateOn {a} S1 S2 H S) :
    StateOn {b} S1 S2 H (stepNext d j v u S) ∧ TupEncl (Icc a b) (F0m j S1 S2 H) (Em j) ct ∧
      TupEncl {b} (F0m j S1 S2 H) (Em j) nt := by
  simp only [stepCheck, stepCheckWith, Bool.and_eq_true] at hc
  obtain ⟨⟨hsep, hokm, hokc, hoku⟩, hct, hnt⟩ := hc
  have hab : a < b := by
    have h1 := ha.2
    have h2 := hb.1
    have : ((v.hi.toInt : ℤ) : ℝ) < ((u.lo.toInt : ℤ) : ℝ) := by exact_mod_cast (SInt.blt_iff _ _).mp hsep
    have hp : (0 : ℝ) < 2 ^ 128 := by positivity
    nlinarith
  have hp0 : (0 : ℝ) < 2 ^ 128 := by positivity
  have ha0 : 0 < a := IV.posB_sound (okSet_sound hokc).1
    (show IV.Mem a (mkIV v.lo u.hi) from ⟨ha.1, (mul_le_mul_of_nonneg_right hab.le hp0.le).trans hb.2⟩)
  have hpm := mkPt_valid hd hj hokm
  have hpc := mkPt_valid hd hj hokc
  have hpu := mkPt_valid hd hj hoku
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hsub : Icc a b ⊆ {t | IV.Mem t (mkIV v.lo u.hi)} := fun t ht =>
    ⟨ha.1.trans (mul_le_mul_of_nonneg_right ht.1 hp.le),
      (mul_le_mul_of_nonneg_right ht.2 hp.le).trans hb.2⟩
  have hmid : (a + b) / 2 ∈ {t | IV.Mem t (IV.divPow2 (IV.add v u) 1)} := by
    have := IV.mem_divPow2 (IV.mem_add ha hb) 1
    simpa using this
  have hHiv : IV.Mem (b - a) (IV.sub u v) := IV.mem_sub hb ha
  have hupos := (okSet_sound hoku).1
  have hcpos := (okSet_sound hokc).1
  have hsv6 : IV.Mem ((a * b⁻¹) ^ 6) (ivPow (IV.divPos v u) 6) :=
    mem_of_eq (mem_ivPow (IV.mem_divPos hupos ha hb) 6) (by rw [div_eq_mul_inv])
  have hcv6 : ∀ t ∈ Icc a b, IV.Mem ((a * t⁻¹) ^ 6) (ivPow (IV.divPos v (mkIV v.lo u.hi)) 6) := fun t ht =>
    mem_of_eq (mem_ivPow (IV.mem_divPos hcpos ha (hsub ht)) 6) (by rw [div_eq_mul_inv])
  have hS' := stepWith_sound hab ha0 hpm hpc hmid hsub hode hHiv hsv6
    (pow6J_sound (ratioJ_sound hpm hb hupos)) (pow6J_sound (ratioJ_sound hpc hb hupos)) hS
  refine ⟨hS', ?_, ?_⟩
  · have hcs := cellState_sound hab ha0 hpc hsub hode hHiv hcv6 hS
    exact (fh_sound (hpc.mono hsub) hd.mpi hode hcs).of_tupSub hct
  · have hbT : ({b} : Set ℝ) ⊆ {t | IV.Mem t u} := fun t ht => by rw [ht]; exact hb
    have hode' : SectorODE j {b} S1 S2 H := hode.mono fun t ht => by rw [ht]; exact ⟨hab.le, le_rfl⟩
    exact (fh_sound (hpu.mono hbT) hd.mpi hode' hS').of_tupSub hnt

theorem subList_length : ∀ {as bs : List (IV 128)}, subList as bs = true → as.length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [subList] at h
  | _ :: _, [], h => by simp [subList] at h
  | _ :: _, _ :: _, h => by
    simp only [subList, Bool.and_eq_true] at h
    simp [subList_length h.2]

theorem enclFrom_of_subList {g : ℕ → ℝ} : ∀ {m : ℕ} {as bs : List (IV 128)}, subList as bs = true →
    EnclFrom g m as → EnclFrom g m bs
  | _, [], [], _, _ => trivial
  | _, [], _ :: _, h, _ => by simp [subList] at h
  | _, _ :: _, [], h, _ => by simp [subList] at h
  | _, _ :: _, _ :: _, h, ⟨h1, h2⟩ => by
    simp only [subList, Bool.and_eq_true] at h
    exact ⟨IV.mem_of_subsetB h.1 h1, enclFrom_of_subList h.2 h2⟩

/-- The last element of `a :: l`. -/
@[expose] def lastR : ℝ → List ℝ → ℝ
  | a, [] => a
  | _, b :: l => lastR b l

/-- **`TableEncloses`**: along the real nodes `τs` of a chunk of segment `j`, each stored cell tuple encloses
`(f̃₀, f̃₀', f̃₀'', ẽ, ẽ', ẽ'')` of the model on the cell `[τ_i, τ_{i+1}]` and each stored node tuple at
`τ_{i+1}`. -/
@[expose] def TableEncloses (j : ℕ) (S1 S2 : ℝ → ℝ) (H : ℕ → ℝ → ℝ) : List ℝ → List Tup → List Tup → Prop
  | a :: b :: rest, ct :: cts, nt :: nts =>
    TupEncl (Icc a b) (F0m j S1 S2 H) (Em j) ct ∧ TupEncl {b} (F0m j S1 S2 H) (Em j) nt ∧
      TableEncloses j S1 S2 H (b :: rest) cts nts
  | _, _, _ => True

theorem chunk_sep {d : BasisData} {j : ℕ} : ∀ (S : SState) (nodes : List (IV 128)) (cts nts : List Tup)
    (S' : SState) (a : ℝ) (τs : List ℝ) (v : IV 128) (vs : List (IV 128)), nodes = v :: vs →
    chunkCheck d j S nodes cts nts S' = true → IV.Mem a v → List.Forall₂ IV.Mem τs vs → a ≤ lastR a τs
  | _, _, _, _, _, a, [], _, _, _, _, _, _ => le_rfl
  | S, _, ct :: cts, nt :: nts, S', a, b :: τs, v, u :: vs, rfl, hc, ha, List.Forall₂.cons hb hbs => by
    simp only [chunkCheck, Bool.and_eq_true] at hc
    have hsep : SInt.blt v.hi u.lo = true := by
      simp only [stepCheck, stepCheckWith, Bool.and_eq_true] at hc; exact hc.1.1.1
    have hab : a < b := by
      have : ((v.hi.toInt : ℤ) : ℝ) < ((u.lo.toInt : ℤ) : ℝ) := by exact_mod_cast (SInt.blt_iff _ _).mp hsep
      have hp : (0 : ℝ) < 2 ^ 128 := by positivity
      nlinarith [ha.2, hb.1]
    exact hab.le.trans (chunk_sep _ (u :: vs) cts nts S' b τs u vs rfl hc.2 hb hbs)
  | _, _, [], _, _, _, _ :: _, _, _ :: _, rfl, hc, _, _ => by simp [chunkCheck] at hc
  | _, _, _ :: _, [], _, _, _ :: _, _, _ :: _, rfl, hc, _, _ => by simp [chunkCheck] at hc

/-- **Soundness of a chunk.** If the chunk check passes, the real nodes `a :: τs` lie in the node intervals,
the sector functions satisfy the ODEs of segment `j` on `[a, last]` and the checkpoint `S` encloses them at
`a`, then the stored tuples enclose the model on every cell and at every node (`TableEncloses`) and the final
checkpoint `S'` encloses the sector functions at the last node. -/
theorem chunkCheck_sound {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) {S1 S2 : ℝ → ℝ}
    {H : ℕ → ℝ → ℝ} : ∀ (S : SState) (v : IV 128) (vs : List (IV 128)) (cts nts : List Tup) (S' : SState)
    (a : ℝ) (τs : List ℝ), chunkCheck d j S (v :: vs) cts nts S' = true → IV.Mem a v →
    List.Forall₂ IV.Mem τs vs → SectorODE j (Icc a (lastR a τs)) S1 S2 H → StateOn {a} S1 S2 H S →
    TableEncloses j S1 S2 H (a :: τs) cts nts ∧ StateOn {lastR a τs} S1 S2 H S'
  | S, v, [], [], [], S', a, [], hc, _, _, _, hS => by
    simp only [chunkCheck] at hc
    refine ⟨trivial, ?_⟩
    simp only [stateSub, Bool.and_eq_true] at hc
    obtain ⟨⟨h1, h2⟩, h3⟩ := hc
    exact ⟨fun x hx => IV.mem_of_subsetB h1 (hS.s1 x hx), fun x hx => IV.mem_of_subsetB h2 (hS.s2 x hx),
      fun x hx => enclFrom_of_subList h3 (hS.hs x hx), (subList_length h3).symm.trans hS.len⟩
  | _, _, [], _ :: _, _, _, _, _, hc, _, _, _, _ => by simp [chunkCheck] at hc
  | _, _, [], _, _ :: _, _, _, _, hc, _, _, _, _ => by simp [chunkCheck] at hc
  | _, _, _ :: _, [], _, _, _, _, hc, _, _, _, _ => by simp [chunkCheck] at hc
  | _, _, _ :: _, _ :: _, [], _, _, _, hc, _, _, _, _ => by simp [chunkCheck] at hc
  | S, v, u :: vs, ct :: cts, nt :: nts, S', a, b :: τs, hc, ha, List.Forall₂.cons hb hbs, hode, hS => by
    have hc' := hc
    simp only [chunkCheck, Bool.and_eq_true] at hc
    have hz := chunk_sep (d := d) (j := j) S (v :: u :: vs) (ct :: cts) (nt :: nts) S' a (b :: τs) v (u :: vs)
      rfl hc' ha (List.Forall₂.cons hb hbs)
    have hbz := chunk_sep (d := d) (j := j) _ (u :: vs) cts nts S' b τs u vs rfl hc.2 hb hbs
    have hsep : a < b := by
      have hsep : SInt.blt v.hi u.lo = true := by
        simp only [stepCheck, stepCheckWith, Bool.and_eq_true] at hc; exact hc.1.1.1
      have : ((v.hi.toInt : ℤ) : ℝ) < ((u.lo.toInt : ℤ) : ℝ) := by exact_mod_cast (SInt.blt_iff _ _).mp hsep
      have hp : (0 : ℝ) < 2 ^ 128 := by positivity
      nlinarith [ha.2, hb.1]
    have hodeab : SectorODE j (Icc a b) S1 S2 H := hode.mono (Icc_subset_Icc le_rfl hbz)
    obtain ⟨hSb, hct, hnt⟩ := stepCheck_sound hd hj hc.1 ha hb hodeab hS
    have hodeb : SectorODE j (Icc b (lastR b τs)) S1 S2 H := hode.mono (Icc_subset_Icc hsep.le le_rfl)
    obtain ⟨hT, hlast⟩ := chunkCheck_sound hd hj _ u vs cts nts S' b τs hc.2 hb hbs hodeb hSb
    exact ⟨⟨hct, hnt, hT⟩, hlast⟩

end SandierSerfaty.Certificate.Table
