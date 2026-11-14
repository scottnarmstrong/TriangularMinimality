/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.HessDef
public import SandierSerfaty.Certificate.Box.HessLocal
public import SandierSerfaty.Certificate.Box.A7

/-!
# Soundness of the Hessian check (A10): `LocalHess` on a convex set from the rows

`HessEnv` bundles the premises that tie the interval data to the exact calibration objects (the same as for the
derivative assertion A7: `FiniteCore`, the table realization, the enclosures of `l`, `f₀(l)`, `-π B(l)`, `l²`, `λ`, `μ`).

* `cell_*`: for a successful rectangle context `c` of `D × S`: the difference quotients of `gd` in `x`, of `G` in `d`
  and `x` lie in `gdOf`, `gdOf`, `gsOf`; the increment of `gd(d', ·) - gd(d, ·)` over a sub-interval of `S` is the
  length times a number of `gddOf c` (right derivatives of `G_d(·, s)` are enclosed by `gddOf`; `Box.CtxSound2`);
* `rowAuxG_sound`: the accumulator `acc_i` of a passing row encloses `(gd d' σ_i - gd d σ_i)/(d' - d)` for every
  `d < d'` of the `d` cell, and every tested cell is a `CellHess` (`A_i = acc_i + [0, |S_i|] F₁`);
* `hess_localHess`: `LocalHess S` for a set `S ⊆ [dpt 0, dpt nd] × [σ jmin, σ nx]` from `H.rows nd = true`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- The `d` node `i` of the partition of `H`. -/
@[expose] noncomputable def dpt (H : HessData) (i : ℕ) : ℝ := (H.dp i : ℝ) / 2 ^ 128

/-- The `s` node `k` of the partition of `H`. -/
@[expose] noncomputable def sgm (H : HessData) (k : ℕ) : ℝ := (H.sp k : ℝ) / 2 ^ 128

/-- The `d` difference quotient of `gd`. -/
@[expose] noncomputable def Rq (d d' y : ℝ) : ℝ := (gd d' y - gd d y) / (d' - d)

/-- The premises tying the interval data of a Hessian check to the exact calibration objects. -/
structure HessEnv (H : HessData) (a : ℕ → ℝ) : Prop where
  /-- The finite-core premise of §6. -/
  fc : FiniteCore
  /-- The table is realized by the real nodes `a`. -/
  encl : Encl2 H.T a
  /-- The table widening. -/
  rad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ H.rad
  /-- `l`. -/
  hl : IV.Mem Calibration.l H.lI
  /-- `f₀(l)`. -/
  hf0l : IV.Mem (f₀ Calibration.l) H.f0lI
  /-- `-π B(l)`. -/
  hk0 : IV.Mem (-(Real.pi * B Calibration.l)) H.k0I
  /-- `l²`. -/
  hlsq : IV.Mem (Calibration.l ^ 2) H.lsqI
  /-- `λ`. -/
  hlam : IV.Mem lam H.lamI
  /-- `μ`. -/
  hmu : IV.Mem mu H.muI

variable {H : HessData} {a : ℕ → ℝ}

theorem ctx_pt (E : HessEnv H a) {ad i : ℕ} {c : DCtx2} (hm : H.ctx ad i = some c) {d s : ℝ}
    (hbd : Calibration.b ≤ d) (hd : d ∈ Icc (dpt H ad) (dpt H (ad + 1))) (hs : s ∈ Icc (sgm H i) (sgm H (i + 1))) :
    0 < d ∧ DMem2 d s c :=
  mkDCtx2_sound E.fc E.encl E.rad E.hl E.hf0l E.hk0 E.hlsq E.hlam E.hmu hm hbd (mem_ofNatPair hd.1 hd.2)
    (mem_ofNatPair hs.1 hs.2)

/-- **A rectangle context `c` of `D_ad × S_i` is valid at every point** of the rectangle with `d ≥ b`
(`DMem2`): the property of a successful `mkDCtx2` (`ctx_pt_of`) and of a successful checked-index `mkDCtx2I`
(`Box.HessIdxSound`) from which the cell lemmas below are derived. -/
@[expose] def CtxPt (H : HessData) (ad i : ℕ) (c : DCtx2) : Prop :=
  ∀ d s : ℝ, Calibration.b ≤ d → d ∈ Icc (dpt H ad) (dpt H (ad + 1)) → s ∈ Icc (sgm H i) (sgm H (i + 1)) →
    0 < d ∧ DMem2 d s c

theorem ctx_pt_of (E : HessEnv H a) {ad i : ℕ} {c : DCtx2} (hm : H.ctx ad i = some c) : CtxPt H ad i c :=
  fun _ _ hbd hd hs => ctx_pt E hm hbd hd hs

section cell

variable {ad i : ℕ} {c : DCtx2} (hm : CtxPt H ad i c) (hbD : Calibration.b ≤ dpt H ad)

include hm hbD

theorem cell_pt {d s : ℝ} (hd : d ∈ Icc (dpt H ad) (dpt H (ad + 1))) (hs : s ∈ Icc (sgm H i) (sgm H (i + 1))) :
    0 < d ∧ DMem2 d s c := hm d s (hbD.trans hd.1) hd hs

theorem cell_B1 : ∀ d ∈ Icc (dpt H ad) (dpt H (ad + 1)), ∀ y ∈ Icc (sgm H i) (sgm H (i + 1)),
    ∀ y' ∈ Icc (sgm H i) (sgm H (i + 1)), y < y' →
    IV.Mem ((gd d y' - gd d y) / (y' - y)) (gdOf c.toDCtx) := by
  intro d hd y hy y' hy' hyy
  obtain ⟨hd0, -⟩ := cell_pt hm hbD hd hy
  have hcont : ContinuousOn (Gd d) (Icc y y') := (continuous_Gd_of hd0).continuousOn
  obtain ⟨q, hq, hqe⟩ := integral_avg_mem (f := Gd d) hyy.le hcont (fun s hs => by
    obtain ⟨h0, h1⟩ := cell_pt hm hbD hd ⟨hy.1.trans hs.1, hs.2.trans hy'.2⟩
    exact gdOf_mem h0 h1.toDMem)
  have hint := continuous_Gd_of hd0
  have : gd d y' - gd d y = ∫ s in y..y', Gd d s := by
    unfold gd
    rw [intervalIntegral.integral_interval_sub_left (hint.intervalIntegrable 0 y') (hint.intervalIntegrable 0 y)]
  rw [this, hqe]
  have : y' - y ≠ 0 := (sub_pos.2 hyy).ne'
  rwa [mul_div_cancel_left₀ _ this]

theorem cell_B2 : ∀ y ∈ Icc (sgm H i) (sgm H (i + 1)), ∀ d ∈ Icc (dpt H ad) (dpt H (ad + 1)),
    ∀ d' ∈ Icc (dpt H ad) (dpt H (ad + 1)), d < d' →
    IV.Mem ((G d' y - G d y) / (d' - d)) (gdOf c.toDCtx) := by
  intro y hy d hd d' hd' hdd
  have hsub : Icc d d' ⊆ Icc (dpt H ad) (dpt H (ad + 1)) := Icc_subset_Icc hd.1 hd'.2
  have hpos : ∀ x ∈ Icc d d', 0 < x := fun x hx => (cell_pt hm hbD (hsub hx) hy).1
  exact slope_mem (f := fun u => G u y) (f' := fun u => Gd u y) hdd
    (fun x hx => (hasDerivAt_G_d (hpos x hx) y).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_G_d (hpos x (Ico_subset_Icc_self hx)) y).hasDerivWithinAt)
    (fun x hx => gdOf_mem (hpos x (Ico_subset_Icc_self hx))
      (cell_pt hm hbD (hsub (Ico_subset_Icc_self hx)) hy).2.toDMem)

theorem cell_C : ∀ d ∈ Icc (dpt H ad) (dpt H (ad + 1)), ∀ y ∈ Icc (sgm H i) (sgm H (i + 1)),
    ∀ y' ∈ Icc (sgm H i) (sgm H (i + 1)), y < y' →
    IV.Mem ((G d y' - G d y) / (y' - y)) (gsOf c.toDCtx) := by
  intro d hd y hy y' hy' hyy
  have hsub : Icc y y' ⊆ Icc (sgm H i) (sgm H (i + 1)) := Icc_subset_Icc hy.1 hy'.2
  have hd0 : 0 < d := (cell_pt hm hbD hd hy).1
  exact slope_mem (f := G d) (f' := fun s => Gs d s) hyy
    (fun x _ => (hasDerivAt_G_s hd0 x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_G_s hd0 x).hasDerivWithinAt)
    (fun x hx => gsOf_mem hd0 (cell_pt hm hbD hd (hsub (Ico_subset_Icc_self hx))).2.toDMem)

/-- The `d` quotient of `gd` grows over a sub-interval of `S` by its length times a number of `gddOf c`. -/
theorem cell_A : ∀ d ∈ Icc (dpt H ad) (dpt H (ad + 1)), ∀ d' ∈ Icc (dpt H ad) (dpt H (ad + 1)), d < d' →
    ∀ y ∈ Icc (sgm H i) (sgm H (i + 1)), ∀ y' ∈ Icc (sgm H i) (sgm H (i + 1)), y ≤ y' →
    ∃ q, IV.Mem q (gddOf c) ∧ Rq d d' y' = Rq d d' y + (y' - y) * q := by
  intro d hd d' hd' hdd y hy y' hy' hyy
  have hsub : Icc d d' ⊆ Icc (dpt H ad) (dpt H (ad + 1)) := Icc_subset_Icc hd.1 hd'.2
  have hd0 : 0 < d := (cell_pt hm hbD hd hy).1
  have hd0' : 0 < d' := (cell_pt hm hbD hd' hy).1
  have hp : 0 < d' - d := sub_pos.2 hdd
  -- pointwise: the quotient of `G_d(·, s)` is enclosed by `gddOf c`
  have hpt : ∀ s ∈ Icc y y', IV.Mem ((Gd d' s - Gd d s) / (d' - d)) (gddOf c) := by
    intro s hs
    have hsS : s ∈ Icc (sgm H i) (sgm H (i + 1)) := ⟨hy.1.trans hs.1, hs.2.trans hy'.2⟩
    have h1 : ∀ x ∈ Ico d d', ∃ F, HasDerivWithinAt (fun u => Gd u s) F (Ici x) x ∧ IV.Mem F (gddOf c) := by
      intro x hx
      obtain ⟨hx0, hmx⟩ := cell_pt hm hbD (hsub (Ico_subset_Icc_self hx)) hsS
      exact gddOf_mem hmx hx0
    choose! F hF using h1
    have hcont : ContinuousOn (fun u => Gd u s) (Icc d d') := by
      have h := continuousOn_Gd.comp (g := fun q : ℝ × ℝ => Gd q.1 q.2) (f := fun u : ℝ => (u, s))
        (s := Icc d d') (Continuous.continuousOn (Continuous.prodMk continuous_id continuous_const))
        (fun u hu => ⟨(cell_pt hm hbD (hsub hu) hsS).1, mem_univ _⟩)
      simpa [Function.comp_def] using h
    exact slope_mem (f := fun u => Gd u s) (f' := F) hdd hcont (fun x hx => (hF x hx).1) (fun x hx => (hF x hx).2)
  have hcρ : Continuous (fun s => (Gd d' s - Gd d s) / (d' - d)) :=
    ((continuous_Gd_of hd0').sub (continuous_Gd_of hd0)).div_const _
  obtain ⟨q, hq, hqe⟩ := integral_avg_mem (f := fun s => (Gd d' s - Gd d s) / (d' - d)) hyy hcρ.continuousOn hpt
  refine ⟨q, hq, ?_⟩
  have hi1 := continuous_Gd_of hd0'
  have hi2 := continuous_Gd_of hd0
  have e1 : gd d' y' - gd d' y = ∫ s in y..y', Gd d' s := by
    unfold gd
    rw [intervalIntegral.integral_interval_sub_left (hi1.intervalIntegrable 0 y') (hi1.intervalIntegrable 0 y)]
  have e2 : gd d y' - gd d y = ∫ s in y..y', Gd d s := by
    unfold gd
    rw [intervalIntegral.integral_interval_sub_left (hi2.intervalIntegrable 0 y') (hi2.intervalIntegrable 0 y)]
  have e3 : ∫ s in y..y', (Gd d' s - Gd d s) / (d' - d) =
      ((gd d' y' - gd d' y) - (gd d y' - gd d y)) / (d' - d) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hi1.intervalIntegrable y y')
      (hi2.intervalIntegrable y y'), e1, e2]
  rw [e3] at hqe
  unfold Rq
  have : (gd d' y' - gd d y') / (d' - d) = (gd d' y - gd d y) / (d' - d) + (y' - y) * q := by
    rw [← hqe]; field_simp; ring
  exact this

end cell

theorem sgm_mono_of {i : ℕ} (h : Nat.ble (H.sp i) (H.sp (i + 1)) = true) : sgm H i ≤ sgm H (i + 1) := by
  unfold sgm
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.ble_eq.mp h) (by positivity)

theorem widthN_cast {i : ℕ} (h : Nat.ble (H.sp i) (H.sp (i + 1)) = true) :
    ((widthN H.sp i : ℕ) : ℝ) / 2 ^ 128 = sgm H (i + 1) - sgm H i := by
  have e : widthN H.sp i = H.sp (i + 1) - H.sp i := rfl
  unfold sgm
  rw [e, Nat.cast_sub (Nat.ble_eq.mp h)]
  ring

/-- **The soundness of one row** (induction over the cells): the accumulator encloses the quotient of `gd` at the
current node, and every tested cell is a `CellHess`. -/
theorem rowAuxG_sound (ctxf : ℕ → ℕ → Option DCtx2) {ad : ℕ}
    (hctx : ∀ i c, ctxf ad i = some c → CtxPt H ad i c) (hbD : Calibration.b ≤ dpt H ad) :
    ∀ (n i : ℕ) (acc : IV 128), H.rowAuxG ctxf ad n i acc = true →
      (∀ d ∈ Icc (dpt H ad) (dpt H (ad + 1)), ∀ d' ∈ Icc (dpt H ad) (dpt H (ad + 1)), d < d' →
        IV.Mem (Rq d d' (sgm H i)) acc) →
      ∀ k, i ≤ k → k < i + n → H.jmin ≤ k →
        ∃ A B C : IV 128, CellHess (Icc (dpt H ad) (dpt H (ad + 1))) (Icc (sgm H k) (sgm H (k + 1))) A B C := by
  intro n
  induction n with
  | zero => intro i acc _ _ k h1 h2; omega
  | succ n ih =>
    intro i acc hrow hinv k hik hkn hjk
    simp only [HessData.rowAuxG] at hrow
    cases hm : ctxf ad i with
    | none => rw [hm] at hrow; simp at hrow
    | some c =>
      rw [hm] at hrow
      have hp := hctx i c hm
      simp only [Bool.and_eq_true] at hrow
      obtain ⟨⟨hsp, htest⟩, hrest⟩ := hrow
      have hspm := sgm_mono_of hsp
      have hwc := widthN_cast hsp
      -- the increment over the whole cell `i`
      have hstep : ∀ d ∈ Icc (dpt H ad) (dpt H (ad + 1)), ∀ d' ∈ Icc (dpt H ad) (dpt H (ad + 1)), d < d' →
          IV.Mem (Rq d d' (sgm H (i + 1)))
            (IV.add acc (IV.mul (IV.ofNatPair (widthN H.sp i) (widthN H.sp i)) (gddOf c))) := by
        intro d hd d' hd' hdd
        obtain ⟨q, hq, hqe⟩ := cell_A hp hbD d hd d' hd' hdd (sgm H i) ⟨le_rfl, hspm⟩ (sgm H (i + 1))
          ⟨hspm, le_rfl⟩ hspm
        rw [hqe]
        refine IV.mem_add (hinv d hd d' hd' hdd) (IV.mem_mul ?_ hq)
        exact mem_ofNatPair (by rw [hwc]) (by rw [hwc])
      rcases Nat.eq_or_lt_of_le hik with hki | hki
      · subst hki
        -- the cell `k = i`
        have hjk' : ¬ i < H.jmin := not_lt.2 hjk
        have htest' : hessTest (IV.add acc (IV.mul (IV.ofNatPair 0 (widthN H.sp i)) (gddOf c))) (gdOf c.toDCtx)
            (gsOf c.toDCtx) = true := by
          have hb : Nat.blt i H.jmin = false := by
            cases h : Nat.blt i H.jmin
            · rfl
            · exact absurd (Nat.blt_eq.mp h) hjk'
          simpa [hb] using htest
        simp only [hessTest, Bool.and_eq_true] at htest'
        obtain ⟨tA, tC, tD⟩ := htest'
        refine ⟨_, _, _, ⟨?_, cell_B1 hp hbD, cell_B2 hp hbD, cell_C hp hbD, tA, tC, tD⟩⟩
        intro y hy d hd d' hd' hdd
        obtain ⟨q, hq, hqe⟩ := cell_A hp hbD d hd d' hd' hdd (sgm H i) ⟨le_rfl, hspm⟩ y hy hy.1
        show IV.Mem (Rq d d' y) _
        rw [hqe]
        refine IV.mem_add (hinv d hd d' hd' hdd) (IV.mem_mul ?_ hq)
        exact mem_ofNatPair (by simpa using hy.1) (by rw [hwc]; linarith [hy.2])
      · exact ih (i + 1) _ hrest hstep k hki (by omega) hjk

/-- `rowsG n = true` iff every row passes. -/
theorem rowsG_iff (H : HessData) (ctxf : ℕ → ℕ → Option DCtx2) :
    ∀ n, H.rowsG ctxf n = true ↔ ∀ ad < n, H.rowG ctxf ad = true := by
  intro n
  induction n with
  | zero => simp [HessData.rowsG]
  | succ n ih =>
    simp only [HessData.rowsG, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ ad had
      rcases Nat.lt_succ_iff_lt_or_eq.1 had with h | h
      · exact h1 ad h
      · rw [h]; exact h2
    · intro h
      exact ⟨fun ad had => h ad (by omega), h n (by omega)⟩

theorem dpt_mono_ofG (H : HessData) (ctxf : ℕ → ℕ → Option DCtx2) {n : ℕ} (hrows : H.rowsG ctxf n = true) :
    ∀ i ≤ n, dpt H 0 ≤ dpt H i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih =>
    intro hi
    have hr := ((rowsG_iff H ctxf n).1 hrows) i (by omega)
    simp only [HessData.rowG, Bool.and_eq_true] at hr
    refine (ih (by omega)).trans ?_
    unfold dpt
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.ble_eq.mp hr.1) (by positivity)

/-- **`LocalHess` from the Hessian rows** (A10), for any context function `ctxf` whose successful contexts are valid
(`CtxPt`): the scanning lookup (`hess_localHess`) or the checked index (`hess_localHessI`). -/
theorem hess_localHessG (ctxf : ℕ → ℕ → Option DCtx2) (hctx : ∀ ad i c, ctxf ad i = some c → CtxPt H ad i c)
    {S : Set (ℝ × ℝ)} (hnd : 0 < H.nd) (hnx : H.jmin < H.nx)
    (hdp0 : Calibration.b ≤ dpt H 0) (hsp0 : H.sp 0 = 0)
    (hrows : H.rowsG ctxf H.nd = true)
    (hS : ∀ q ∈ S, q.1 ∈ Icc (dpt H 0) (dpt H H.nd) ∧ q.2 ∈ Icc (sgm H H.jmin) (sgm H H.nx)) :
    LocalHess S := by
  have hcell : ∀ i < H.nd, ∀ k, H.jmin ≤ k → k < H.nx → ∃ A B C : IV 128,
      CellHess (Icc (dpt H i) (dpt H (i + 1))) (Icc (sgm H k) (sgm H (k + 1))) A B C := by
    intro ad had k hjk hk
    have hr := ((rowsG_iff H ctxf H.nd).1 hrows) ad had
    simp only [HessData.rowG, Bool.and_eq_true] at hr
    have hbD : Calibration.b ≤ dpt H ad := hdp0.trans (dpt_mono_ofG H ctxf hrows ad had.le)
    refine rowAuxG_sound ctxf (fun i c hm => hctx ad i c hm) hbD H.nx 0 (IV.ofNatPair 0 0) hr.2 ?_ k
      (Nat.zero_le _) (by omega) hjk
    intro d _ d' _ _
    have hs0 : sgm H 0 = 0 := by simp [sgm, hsp0]
    have h0 : Rq d d' (sgm H 0) = 0 := by
      simp [Rq, hs0, gd]
    rw [h0]
    exact mem_ofNatPair (by simp) (by simp)
  choose! A B C hABC using hcell
  exact localHess_of_cells (A := A) (B := B) (C := C) hnd hnx hS hABC

/-- **`LocalHess` from the Hessian rows** (A10): for a set `S` inside the covered box. -/
theorem hess_localHess (E : HessEnv H a) {S : Set (ℝ × ℝ)} (hnd : 0 < H.nd) (hnx : H.jmin < H.nx)
    (hdp0 : Calibration.b ≤ dpt H 0) (hsp0 : H.sp 0 = 0)
    (hrows : H.rows H.nd = true)
    (hS : ∀ q ∈ S, q.1 ∈ Icc (dpt H 0) (dpt H H.nd) ∧ q.2 ∈ Icc (sgm H H.jmin) (sgm H H.nx)) :
    LocalHess S :=
  hess_localHessG H.ctx (fun _ _ _ hm => ctx_pt_of E hm) hnd hnx hdp0 hsp0 hrows hS

end SandierSerfaty.Certificate.Box
