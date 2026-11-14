/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.CtxIdx
public import SandierSerfaty.Certificate.Box.CtxSound2
public import SandierSerfaty.Certificate.Query.LookupIdxSound

/-!
# Soundness of the contexts with the checked-index lookup

The statements are those of `Box.CtxSound` / `Box.CtxSound2` with the checked index range `[i0, i1]` as extra
arguments of the check (not of any hypothesis on the table or on the range: the range is verified by the kernel,
`Query.coverOK`):

* `lookupIdx_trunc`: for `t ∈ [b, l)` and `X ∋ t`, a successful `lookupIdx` encloses the truncated radial functions
  at `t` (`TruncEncl`);
* `lookupXI_sound`: for `t ≥ b` in `X`, a successful `lookupXI` has a tuple with `ExactEncl t rad`;
* `mkDCtx2I_sound`: a successful `mkDCtx2I` has the enclosures of `DMem2` at every `(d, s) ∈ Dd × Ss`, `d ≥ b`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-- **The checked-index hull** encloses the truncated radial functions at `t ∈ [b, l)`, `t ∈ X`. -/
theorem lookupIdx_trunc {T : ITable} {a : ℕ → ℝ} (H : Encl2 T a) {X : IV 128} {i0 i1 : ℕ} {c : Tup}
    (h : lookupIdx T X i0 i1 = some c) {t : ℝ} (ht : t ∈ Ico Calibration.b Calibration.l) (hX : IV.Mem t X) :
    TruncEncl t c := by
  obtain ⟨hc, rfl⟩ := lookupIdx_some h
  obtain ⟨i, hi0, hi1, hat, hta⟩ := exists_cell_idx H.base hc ht hX
  obtain ⟨-, hn, -, -⟩ := coverOK_iff hc
  have hin : i < T.n := by omega
  have hti : t ∈ Icc (a i) (a (i + 1)) := ⟨hat, hta.le⟩
  have get : ∀ (proj : Tup → IV 128) (x : ℝ), (∀ a b, proj (hullTup a b) = IV.hull (proj a) (proj b)) →
      IV.Mem x (proj (T.cell i)) → IV.Mem x (proj (hullCells T i0 (i1 - i0))) :=
    fun proj x hh hx => hullCells_mem hh _ i0 i hi0 (by omega) hx
  obtain ⟨F, hF, m4⟩ := H.f2 i hin t hti
  obtain ⟨E, hE, m5⟩ := H.e2 i hin t ⟨hat, hta⟩
  have m4' : IV.Mem (deriv (deriv Trunc.f₀) t) (T.cell i).f2 := by rw [hF.deriv]; exact m4
  exact ⟨get Tup.f0 _ (fun _ _ => rfl) (H.base.f0 i hin t hti), get Tup.f1 _ (fun _ _ => rfl) (H.base.f1 i hin t hti),
    get Tup.e0 _ (fun _ _ => rfl) (H.base.e0 i hin t hti), get Tup.e1 _ (fun _ _ => rfl) (H.base.e1 i hin t hti),
    get Tup.f2 _ (fun _ _ => rfl) m4', E, hE, get Tup.e2 _ (fun _ _ => rfl) m5⟩

/-- **The soundness of the lookup with the exterior and the checked index**: for every `t ≥ b` in `X`. -/
theorem lookupXI_sound (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (H : Encl2 T a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {f0lI k0I lsqI lI X : IV 128} {t : ℝ} {i0 i1 : ℕ} {c : Tup}
    (hbt : Calibration.b ≤ t) (hX : IV.Mem t X) (hl : IV.Mem Calibration.l lI)
    (hf0l : IV.Mem (f₀ Calibration.l) f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) lsqI) (h : lookupXI T f0lI k0I lsqI lI X i0 i1 = some c) :
    ExactEncl t rad c := by
  have hN : (0 : ℝ) < 2 ^ 128 := by positivity
  unfold lookupXI at h
  cases hb : SInt.ble lI.hi X.lo
  · simp only [hb, Bool.cond_false] at h
    cases hk : lookupIdx T X i0 i1 with
    | none => simp [hk] at h
    | some c0 =>
      simp only [hk] at h
      rcases lt_or_ge t Calibration.l with hlt | hge
      · have h0 := lookupIdx_trunc H hk ⟨hbt, hlt⟩ hX
        cases hb2 : SInt.ble lI.lo X.hi
        · simp only [hb2, Bool.cond_false, Option.some.injEq] at h
          subst h
          exact h0.exact hc ⟨hbt, hlt⟩ hrad
        · simp only [hb2, Bool.cond_true, Option.some.injEq] at h
          subst h
          exact (h0.hull_left _).exact hc ⟨hbt, hlt⟩ hrad
      · have hb2 : SInt.ble lI.lo X.hi = true := by
          have h1 : Calibration.l * 2 ^ 128 ≤ t * 2 ^ 128 := mul_le_mul_of_nonneg_right hge hN.le
          simp only [SInt.ble_iff]
          have : ((lI.lo.toInt : ℤ) : ℝ) ≤ ((X.hi.toInt : ℤ) : ℝ) := by linarith [hl.1, hX.2]
          exact_mod_cast this
        simp only [hb2, Bool.cond_true, Option.some.injEq] at h
        subst h
        exact ((extTup_encl hge hX hf0l hk0 hlsq).hull_right c0).exact rad
  · simp only [hb, Bool.cond_true, Option.some.injEq] at h
    subst h
    have hge : Calibration.l ≤ t := by
      simp only [SInt.ble_iff] at hb
      have h1 : ((lI.hi.toInt : ℤ) : ℝ) ≤ ((X.lo.toInt : ℤ) : ℝ) := by exact_mod_cast hb
      have h2 : Calibration.l * 2 ^ 128 ≤ t * 2 ^ 128 := by linarith [hl.2, hX.1]
      exact le_of_mul_le_mul_right h2 hN
    exact (extTup_encl hge hX hf0l hk0 hlsq).exact rad

theorem mkChk2I_some {T : ITable} {f0lI k0I lsqI lI lamI muI : IV 128} {rad : ℕ} {Dd Ss t2 : IV 128} {lh : ℕ × ℕ}
    {i0 i1 : ℕ} {c : DCtx2} (h : mkChk2I T f0lI k0I lsqI lI lamI muI rad Dd Ss t2 lh i0 i1 = some c) :
    IV.posB Dd = true ∧ IV.sqrtCheck t2 lh.1 lh.2 = true ∧ IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2) = true ∧
      ∃ c', lookupXI T f0lI k0I lsqI lI (IV.ofNatPair lh.1 lh.2) i0 i1 = some c' ∧
        c = dctx2Of Dd Ss (IV.ofNatPair lh.1 lh.2) t2 lamI muI rad c' := by
  unfold mkChk2I at h
  cases h1 : (and (IV.posB Dd) (and (IV.sqrtCheck t2 lh.1 lh.2) (IV.posB (IV.ofNatPair (P := 128) lh.1 lh.2))))
  · simp [h1] at h
  · simp only [h1, Bool.cond_true] at h
    simp only [Bool.and_eq_true] at h1
    obtain ⟨h1, h2, h3⟩ := h1
    refine ⟨h1, h2, h3, ?_⟩
    cases hl : lookupXI T f0lI k0I lsqI lI (IV.ofNatPair lh.1 lh.2) i0 i1 with
    | none => simp [hl] at h
    | some c' =>
      simp only [hl, Option.some.injEq] at h
      exact ⟨c', rfl, h.symm⟩

/-- **Soundness of the second-order context with the checked index** of a rectangle. -/
theorem mkDCtx2I_sound (hc : FiniteCore) {T : ITable} {a : ℕ → ℝ} (H : Encl2 T a) {rad : ℕ}
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {f0lI k0I lsqI lI lamI muI : IV 128} (hl : IV.Mem Calibration.l lI)
    (hf0l : IV.Mem (f₀ Calibration.l) f0lI) (hk0 : IV.Mem (-(Real.pi * B Calibration.l)) k0I)
    (hlsq : IV.Mem (Calibration.l ^ 2) lsqI) (hlam : IV.Mem lam lamI) (hmu : IV.Mem mu muI) {Dd Ss : IV 128}
    {i0 i1 : ℕ} {c : DCtx2} (h : mkDCtx2I T f0lI k0I lsqI lI lamI muI rad Dd Ss i0 i1 = some c) {d s : ℝ}
    (hbd : Calibration.b ≤ d) (hd : IV.Mem d Dd) (hs : IV.Mem s Ss) : 0 < d ∧ DMem2 d s c := by
  unfold mkDCtx2I at h
  obtain ⟨h1, h2, h3, c', hlk, hc'⟩ := mkChk2I_some h
  have hd0 : 0 < d := lt_of_lt_of_le Calibration.b_pos hbd
  have ht2 : IV.Mem (d ^ 2 + s ^ 2) (IV.add (IV.sq Dd) (IV.sq Ss)) := IV.mem_add (IV.mem_sq hd) (IV.mem_sq hs)
  set lh := IV.sqrtProposal (IV.add (IV.sq Dd) (IV.sq Ss)) with hlh
  have htI : IV.Mem (tt d s) (IV.ofNatPair (P := 128) lh.1 lh.2) := IV.mem_sqrt_of_sqrtCheck h2 ht2
  have hdt : d ≤ tt d s := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
  have hbt : Calibration.b ≤ tt d s := hbd.trans hdt
  have htt2 : tt d s ^ 2 = d ^ 2 + s ^ 2 := tt_sq hd0
  have hex := lookupXI_sound hc H hrad hbt htI hl hf0l hk0 hlsq hlk
  obtain ⟨e0, e1, e2, e3, e4, E, hE, hE2⟩ := hex
  subst hc'
  refine ⟨hd0, ⟨⟨hd, hs, htI, ht2, Jet.mem_invPos h3 htI, ?_, Jet.mem_invPos h1 hd, ?_, ?_, e2, e3⟩, ?_, E, hE, hE2⟩⟩
  · have := IV.mem_sq (Jet.mem_invPos h3 htI)
    have e : (d ^ 2 + s ^ 2)⁻¹ = (tt d s)⁻¹ ^ 2 := by rw [← htt2, inv_pow]
    rw [e]
    exact this
  · have := IV.mem_sub (IV.mem_sub e0 (IV.mem_divPow2 (IV.mem_mul hlam ht2) 1)) hmu
    have e : f (tt d s) = f₀ (tt d s) - lam * (d ^ 2 + s ^ 2) / 2 ^ 1 - mu := by
      unfold f
      rw [htt2]
      ring
    rw [e]
    exact this
  · have := IV.mem_sub e1 (IV.mem_mul hlam htI)
    unfold df
    exact this
  · exact IV.mem_sub e4 hlam

end SandierSerfaty.Certificate.Box
