/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.StepSound

/-!
# The first segment of the table: the exact inner form

On the first segment `[b, p - c]` the table uses the exact identity `comp:inner-exact`,
`f̃₀(t) = (πt² - ½) log t - 3π²t⁴/8` and `ẽ = 0` (the full and the truncated `f₀, e` coincide with it there;
the identity itself is `Cal.inner_exact` for the full series, and its truncated form is part of the bridge of
the model to `Cal.Trunc`). `innerCheck_sound`: along separated positive nodes, the stored cell tuples enclose
`(F0inner, F0inner', F0inner'', 0, 0, 0)` on the cells and the stored node tuples at the nodes
(`InnerEncloses`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Table

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis

/-- The inner closed form `f̃₀(t) = (πt² - ½) log t - (3/8) π² t⁴` (`comp:inner-exact`). -/
@[expose] noncomputable def F0inner (t : ℝ) : ℝ :=
  (Real.pi * t ^ 2 - 1 / 2) * Real.log t - 3 / 8 * Real.pi ^ 2 * t ^ 4

theorem fInnerJ_sound {pi X : IV 128} (hpi : IV.Mem Real.pi pi) (hX : IV.posB X = true) :
    JetEncl2 {t | IV.Mem t X} F0inner (fInnerJ pi X) := by
  have hv : JetEncl {t | IV.Mem t X} (fun t => t) (IJet.var X) := JetEncl.var fun s hs => hs
  have h1 := (JetEncl2.scale hpi hv.sq.trunc).sub (JetEncl2.const (T := {t | IV.Mem t X})
    (by simpa using mem_frac_pos 1 2 (by norm_num)))
  have h3 : IV.Mem (3 / 8 * Real.pi ^ 2) (IV.mul (frac false 3 8) (IV.sq pi)) :=
    IV.mem_mul (by simpa using mem_frac_pos 3 8 (by norm_num)) (IV.mem_sq hpi)
  have := (h1.mul (hv.log hX).trunc).sub (JetEncl2.scale h3 (hv.pow 4).trunc)
  exact jetEncl2_of_eq this fun t => by simp [F0inner]

theorem fhInner_sound {pi X : IV 128} (hpi : IV.Mem Real.pi pi) (hX : IV.posB X = true) :
    TupEncl {t | IV.Mem t X} F0inner (fun _ => 0) (fhInner pi X) :=
  tupEncl_tupOf (fInnerJ_sound hpi hX) (JetEncl2.const mem_ivZero)

/-- Along the real nodes `τs` of the first segment, the stored tuples enclose the inner closed form. -/
@[expose] def InnerEncloses : List ℝ → List Tup → List Tup → Prop
  | a :: b :: rest, ct :: cts, nt :: nts =>
    TupEncl (Icc a b) F0inner (fun _ => 0) ct ∧ TupEncl {b} F0inner (fun _ => 0) nt ∧ InnerEncloses (b :: rest) cts nts
  | _, _, _ => True

/-- **Soundness of the first segment.** -/
theorem innerCheck_sound {pi : IV 128} (hpi : IV.Mem Real.pi pi) :
    ∀ (v : IV 128) (vs : List (IV 128)) (cts nts : List Tup) (a : ℝ) (τs : List ℝ),
      innerCheck pi (v :: vs) cts nts = true → IV.Mem a v → List.Forall₂ IV.Mem τs vs →
      InnerEncloses (a :: τs) cts nts
  | _, [], _, _, _, [], _, _, _ => by simp [InnerEncloses]
  | v, u :: vs, ct :: cts, nt :: nts, a, b :: τs, hc, ha, List.Forall₂.cons hb hbs => by
    simp only [innerCheck, Bool.and_eq_true] at hc
    obtain ⟨⟨hsep, hvpos, hu⟩, ⟨hct, hnt⟩, hrest⟩ := hc
    have hp : (0 : ℝ) < 2 ^ 128 := by positivity
    have hab : a ≤ b := by
      have : ((v.hi.toInt : ℤ) : ℝ) < ((u.lo.toInt : ℤ) : ℝ) := by exact_mod_cast (SInt.blt_iff _ _).mp hsep
      nlinarith [ha.2, hb.1]
    have hsub : Icc a b ⊆ {t | IV.Mem t (mkIV v.lo u.hi)} := fun t ht =>
      ⟨ha.1.trans (mul_le_mul_of_nonneg_right ht.1 hp.le), (mul_le_mul_of_nonneg_right ht.2 hp.le).trans hb.2⟩
    have hcpos : IV.posB (mkIV v.lo u.hi) = true := hvpos
    refine ⟨((fhInner_sound hpi hcpos).mono hsub).of_tupSub hct,
      ((fhInner_sound hpi hu).mono fun t ht => by rw [ht]; exact hb).of_tupSub hnt,
      innerCheck_sound hpi u vs cts nts b τs hrest hb hbs⟩
  | _, [], _ :: _, _, _, _, hc, _, _ => by simp [innerCheck] at hc
  | _, [], [], _ :: _, _, _, hc, _, _ => by simp [innerCheck] at hc
  | _, _ :: _, [], _, _, _, hc, _, _ => by simp [innerCheck] at hc
  | _, _ :: _, _ :: _, [], _, _, hc, _, _ => by simp [innerCheck] at hc
  | _, [], [], [], _, _ :: _, _, _, h => by cases h
  | _, _ :: _, _ :: _, _ :: _, _, [], _, _, h => by cases h

end SandierSerfaty.Certificate.Table
