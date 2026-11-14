/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.CtxSound2
public import SandierSerfaty.Certificate.Box.Grid

/-!
# The derivative assertion A7 from the rectangle checks (paper `comp:global-derivative-bounds`)

`derivBounds_of_a7`: if every rectangle `[dp j, dp (j+1)] × [sp k, sp (k+1)]` of a partition of `[b, dHi] × [0, xHi]`
passes `A7Data.rect` (a successful `mkDCtx2` and `|G_d| ≤ L₁`, `|G_s| ≤ L₂`, `|G_dd| ≤ L₃`, `|G_ss| ≤ L₄` on the
enclosures), then `DerivBounds b dHi xHi L₁ L₂ L₃ L₄`: the first derivatives are bounded pointwise, and the second
derivatives, which exist only as right derivatives at the spline knots, bound the Lipschitz constants of `G_d` in `d`
and of `G_s` in `s` (`Box.lip_of_right_deriv`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

theorem A7Data.row_iff {D : A7Data} {j : ℕ} : ∀ n, D.row j n = true ↔ ∀ k < n, D.rect j k = true := by
  intro n
  induction n with
  | zero => simp [A7Data.row]
  | succ n ih =>
    simp only [A7Data.row, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact h1 k h
      · rw [h]; exact h2
    · intro h
      exact ⟨fun k hk => h k (by omega), h n (by omega)⟩

theorem absLe_sound {x : ℝ} {I : IV 128} {L : ℕ} (h : absLe I L = true) (hx : IV.Mem x I) :
    |x| ≤ (L : ℝ) / 2 ^ 128 := by
  simp only [absLe, Bool.and_eq_true, SInt.ble_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  have a1 : (((⟨true, L⟩ : SInt).toInt : ℤ) : ℝ) ≤ ((I.lo.toInt : ℤ) : ℝ) := by exact_mod_cast h1
  have a2 : ((I.hi.toInt : ℤ) : ℝ) ≤ (((⟨false, L⟩ : SInt).toInt : ℤ) : ℝ) := by exact_mod_cast h2
  simp only [SInt.toInt_true, SInt.toInt_false] at a1 a2
  push_cast at a1 a2
  rw [abs_le]
  constructor
  · have h := (div_le_iff₀ hN).2 (show -(L : ℝ) ≤ x * 2 ^ 128 by linarith [hx.1])
    rw [neg_div] at h
    exact h
  · rw [le_div_iff₀ hN]; linarith [hx.2]

theorem mem_ofNatPair {x : ℝ} {l h : ℕ} (h1 : (l : ℝ) / 2 ^ 128 ≤ x) (h2 : x ≤ (h : ℝ) / 2 ^ 128) :
    IV.Mem x (IV.ofNatPair (P := 128) l h) := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [IV.ofNatPair, SInt.toInt_false]
    push_cast
    rw [div_le_iff₀ hN] at h1
    exact h1
  · simp only [IV.ofNatPair, SInt.toInt_false]
    push_cast
    rw [le_div_iff₀ hN] at h2
    exact h2

/-- **The pointwise facts of a passing rectangle** at every point of the box. -/
theorem A7Data.point (hc : FiniteCore) (D : A7Data) {a : ℕ → ℝ} (H : Encl2 D.T a)
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ D.rad) (hl : IV.Mem Calibration.l D.lI)
    (hf0l : IV.Mem (f₀ Calibration.l) D.f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) D.k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) D.lsqI) (hlam : IV.Mem lam D.lamI) (hmu : IV.Mem mu D.muI)
    {dHi xHi : ℝ} (hnj : 0 < D.nj) (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : dHi ≤ (D.dp D.nj : ℝ) / 2 ^ 128) (hsp0 : D.sp 0 = 0) (hspn : xHi ≤ (D.sp D.nk : ℝ) / 2 ^ 128)
    (hrows : ∀ j < D.nj, D.row j D.nk = true) {d s : ℝ} (hd : d ∈ Icc Calibration.b dHi)
    (hs : s ∈ Icc 0 xHi) :
    ∃ c : DCtx2, DMem2 d s c ∧ absLe (gdOf c.toDCtx) D.L1 = true ∧ absLe (gsOf c.toDCtx) D.L2 = true ∧
      absLe (gddOf c) D.L3 = true ∧ absLe (gssOf c) D.L4 = true := by
  obtain ⟨j, hj, hdj⟩ := exists_cell (a := fun j => (D.dp j : ℝ) / 2 ^ 128) hnj (hdp0.trans hd.1) (hd.2.trans hdpn)
  obtain ⟨k, hk, hsk⟩ := exists_cell (a := fun k => (D.sp k : ℝ) / 2 ^ 128) hnk
    (by simp [hsp0]; exact hs.1) (hs.2.trans hspn)
  have hrect := (A7Data.row_iff D.nk).1 (hrows j hj) k hk
  unfold A7Data.rect at hrect
  cases hm : mkDCtx2 D.T D.f0lI D.k0I D.lsqI D.lI D.lamI D.muI D.rad (IV.ofNatPair (D.dp j) (D.dp (Nat.succ j)))
      (IV.ofNatPair (D.sp k) (D.sp (Nat.succ k))) with
  | none => rw [hm] at hrect; exact absurd hrect (by simp)
  | some c =>
    rw [hm] at hrect
    simp only [Bool.and_eq_true] at hrect
    obtain ⟨⟨r1, r2⟩, r3, r4⟩ := hrect
    have hDd : IV.Mem d (IV.ofNatPair (P := 128) (D.dp j) (D.dp (Nat.succ j))) := mem_ofNatPair hdj.1 hdj.2
    have hSs : IV.Mem s (IV.ofNatPair (P := 128) (D.sp k) (D.sp (Nat.succ k))) := mem_ofNatPair hsk.1 hsk.2
    obtain ⟨-, hmem⟩ := mkDCtx2_sound hc H hrad hl hf0l hk0 hlsq hlam hmu hm hd.1 hDd hSs
    exact ⟨c, hmem, r1, r2, r3, r4⟩

/-- **`DerivBounds` from the pointwise facts**: if every point of `[b, dHi] × [0, xHi]` has a context `c` with
`DMem2 d s c` passing the four bounds of `D`, then `DerivBounds` (the part of A7 independent of how the contexts were
produced: scanning lookup `A7Data.rect` or checked index `A7Data.rectI`). -/
theorem derivBounds_of_pt (D : A7Data) {dHi xHi : ℝ}
    (pt : ∀ d s : ℝ, d ∈ Icc Calibration.b dHi → s ∈ Icc 0 xHi →
      ∃ c : DCtx2, DMem2 d s c ∧ absLe (gdOf c.toDCtx) D.L1 = true ∧ absLe (gsOf c.toDCtx) D.L2 = true ∧
        absLe (gddOf c) D.L3 = true ∧ absLe (gssOf c) D.L4 = true) :
    DerivBounds Calibration.b dHi xHi ((D.L1 : ℝ) / 2 ^ 128) ((D.L2 : ℝ) / 2 ^ 128) ((D.L3 : ℝ) / 2 ^ 128)
      ((D.L4 : ℝ) / 2 ^ 128) := by
  have hb0 : (0 : ℝ) < Calibration.b := Calibration.b_pos
  refine ⟨hb0, ⟨by positivity, by positivity, by positivity, by positivity⟩, ?_, ?_, ?_, ?_⟩
  · intro d hd s hs
    obtain ⟨c, hm, r1, -, -, -⟩ := pt d s hd hs
    exact absLe_sound r1 (gdOf_mem (lt_of_lt_of_le hb0 hd.1) hm.toDMem)
  · intro d hd s hs
    obtain ⟨c, hm, -, r2, -, -⟩ := pt d s hd hs
    exact absLe_sound r2 (gsOf_mem (lt_of_lt_of_le hb0 hd.1) hm.toDMem)
  · intro s hs
    have hcont : ContinuousOn (fun u => Gd u s) (Icc Calibration.b dHi) := by
      have h := continuousOn_Gd.comp (g := fun q : ℝ × ℝ => Gd q.1 q.2) (f := fun u : ℝ => (u, s))
        (s := Icc Calibration.b dHi) (Continuous.continuousOn (Continuous.prodMk continuous_id continuous_const))
        (fun u hu => ⟨lt_of_lt_of_le hb0 hu.1, mem_univ _⟩)
      simpa [Function.comp_def] using h
    have h1 : ∀ x ∈ Ico Calibration.b dHi, ∃ F, HasDerivWithinAt (fun u => Gd u s) F (Ici x) x ∧
        |F| ≤ (D.L3 : ℝ) / 2 ^ 128 := by
      intro x hx
      obtain ⟨c, hm, -, -, r3, -⟩ := pt x s ⟨hx.1, hx.2.le⟩ hs
      obtain ⟨F, hF, hFm⟩ := gddOf_mem hm (lt_of_lt_of_le hb0 hx.1)
      exact ⟨F, hF, absLe_sound r3 hFm⟩
    choose! F hF using h1
    intro d hd d' hd'
    exact lip_of_right_deriv hcont (fun x hx => (hF x hx).1) (fun x hx => (hF x hx).2) d hd d' hd'
  · intro d hd s hs s' hs'
    have hd0 : 0 < d := lt_of_lt_of_le hb0 hd.1
    have hcont : ContinuousOn (Gs d) (Icc 0 xHi) := (continuous_Gs_of hd0).continuousOn
    have h1 : ∀ x ∈ Ico (0 : ℝ) xHi, ∃ F, HasDerivWithinAt (Gs d) F (Ici x) x ∧ |F| ≤ (D.L4 : ℝ) / 2 ^ 128 := by
      intro x hx
      obtain ⟨c, hm, -, -, -, r4⟩ := pt d x hd ⟨hx.1, hx.2.le⟩
      obtain ⟨F, hF, hFm⟩ := gssOf_mem hm hd0 hx.1
      exact ⟨F, hF, absLe_sound r4 hFm⟩
    choose! F hF using h1
    exact lip_of_right_deriv hcont (fun x hx => (hF x hx).1) (fun x hx => (hF x hx).2) s hs s' hs'


/-- **A7**: `DerivBounds` from the rectangle checks. -/
theorem derivBounds_of_a7 (hc : FiniteCore) (D : A7Data) {a : ℕ → ℝ} (H : Encl2 D.T a)
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ D.rad) (hl : IV.Mem Calibration.l D.lI)
    (hf0l : IV.Mem (f₀ Calibration.l) D.f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) D.k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) D.lsqI) (hlam : IV.Mem lam D.lamI) (hmu : IV.Mem mu D.muI)
    {dHi xHi : ℝ} (hnj : 0 < D.nj) (hnk : 0 < D.nk) (hdp0 : (D.dp 0 : ℝ) / 2 ^ 128 ≤ Calibration.b)
    (hdpn : dHi ≤ (D.dp D.nj : ℝ) / 2 ^ 128) (hsp0 : D.sp 0 = 0) (hspn : xHi ≤ (D.sp D.nk : ℝ) / 2 ^ 128)
    (hrows : ∀ j < D.nj, D.row j D.nk = true) :
    DerivBounds Calibration.b dHi xHi ((D.L1 : ℝ) / 2 ^ 128) ((D.L2 : ℝ) / 2 ^ 128) ((D.L3 : ℝ) / 2 ^ 128)
      ((D.L4 : ℝ) / 2 ^ 128) :=
  derivBounds_of_pt D fun _ _ hd hs =>
    A7Data.point hc D H hrad hl hf0l hk0 hlsq hlam hmu hnj hnk hdp0 hdpn hsp0 hspn hrows hd hs

end SandierSerfaty.Certificate.Box
