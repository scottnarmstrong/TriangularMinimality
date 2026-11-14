/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Jet.Encl
public import SandierSerfaty.Certificate.Arith.LogLemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Composition of jets with `1/·`, `log` and `√`

* `jet3_comp`: the chain rule for `Tails.Jet3` with an outer function that has a jet on a set `V` only
  (`Tails.Jet3.comp` needs `V = univ`), as `log`, `√` and `1/·` require;
* `JetEncl.comp`: the order-three Faà di Bruno law of `IJet.comp`;
* the outer jets `invOuterOf`, `logOuterOf`, `sqrtOuterOf` enclose `1/·`, `log`, `√` and their derivatives
  over an interval of positive reals (`JetEncl.invOuterOf`, ...);
* the laws of `IJet.invPos`, `IJet.divPos`, `IJet.log` and `IJet.sqrtWith`/`IJet.sqrt` (the square root is
  sound when the Newton proposal passes the check by squaring, `IJet.sqrtOK`);
* `mem_invPos`, the inclusion law of the interval reciprocal `IV.invPos`.
-/

open Set Filter Real

public section

namespace SandierSerfaty.Certificate.Jet

open SandierSerfaty.Certificate.Arith SandierSerfaty.Tails

variable {P : ℕ}

/-! ### The interval reciprocal -/

/-- The inclusion law of `IV.invPos` (`0 < b.lo`, checked by `IV.posB`). -/
theorem mem_invPos {y : ℝ} {b : IV P} (hpos : IV.posB b = true) (hb : IV.Mem y b) :
    IV.Mem y⁻¹ (IV.invPos b) := by
  obtain ⟨hbm, hbn⟩ := SInt.pos_mag hpos
  have hp := IV.two_pow_pos' P
  obtain ⟨h1, h2⟩ := hb
  have eL : ((b.lo.toInt : ℤ) : ℝ) = b.lo.mag := by rw [SInt.toInt_eq, hbn]; simp
  have hL : (0 : ℝ) < b.lo.mag := by exact_mod_cast hbm
  have hY : 0 < y * 2 ^ P := by rw [eL] at h1; linarith
  have hhi : b.hi.isNeg = false := by
    cases hc : b.hi.isNeg
    · rfl
    · have h0 : ((b.hi.toInt : ℤ) : ℝ) ≤ 0 := by exact_mod_cast SInt.toInt_nonpos_of_isNeg_true hc
      linarith
  have eH : ((b.hi.toInt : ℤ) : ℝ) = b.hi.mag := by rw [SInt.toInt_eq, hhi]; simp
  have hy : 0 < y := pos_of_mul_pos_left hY hp.le
  have key : y⁻¹ * 2 ^ P = (2 : ℝ) ^ (P + P) / (y * 2 ^ P) := by
    field_simp; ring
  have eN : ((Nat.shiftLeft 1 (Nat.add P P) : ℕ) : ℝ) = (2 : ℝ) ^ (P + P) := by
    rw [SInt.nat_shiftLeft_eq, show Nat.add P P = P + P from rfl]; push_cast; ring
  simp only [IV.Mem, IV.invPos, SInt.toInt_false, Int.cast_natCast]
  rw [key]
  constructor
  · calc ((Nat.div (Nat.shiftLeft 1 (Nat.add P P)) b.hi.mag : ℕ) : ℝ)
          ≤ ((Nat.shiftLeft 1 (Nat.add P P) : ℕ) : ℝ) / b.hi.mag := by
            rw [SInt.nat_div_eq]; exact Nat.cast_div_le
        _ = (2 : ℝ) ^ (P + P) / b.hi.mag := by rw [eN]
        _ ≤ (2 : ℝ) ^ (P + P) / (y * 2 ^ P) :=
            div_le_div_of_nonneg_left (by positivity) hY (by rw [← eH]; exact h2)
  · calc (2 : ℝ) ^ (P + P) / (y * 2 ^ P) ≤ (2 : ℝ) ^ (P + P) / b.lo.mag :=
            div_le_div_of_nonneg_left (by positivity) hL (by rw [← eL]; exact h1)
        _ = ((Nat.shiftLeft 1 (Nat.add P P) : ℕ) : ℝ) / b.lo.mag := by rw [eN]
        _ ≤ ((SInt.cdivNat (Nat.shiftLeft 1 (Nat.add P P)) b.lo.mag : ℕ) : ℝ) := by
            rw [div_le_iff₀ hL]; exact_mod_cast SInt.le_cdivNat_mul _ _ hbm

/-! ### The chain rule on a set -/

/-- The chain rule for jets, with an outer jet on a set `V` containing the values of the inner function. -/
theorem jet3_comp {V T : Set ℝ} {g g₁ g₂ g₃ w w₁ w₂ w₃ : ℝ → ℝ} (hg : Jet3 V g g₁ g₂ g₃)
    (hw : Jet3 T w w₁ w₂ w₃) (hmaps : ∀ x ∈ T, w x ∈ V) :
    Jet3 T (fun x => g (w x)) (fun x => g₁ (w x) * w₁ x)
      (fun x => (g₂ (w x) * w₁ x) * w₁ x + g₁ (w x) * w₂ x)
      (fun x => (((g₃ (w x) * w₁ x) * w₁ x + g₂ (w x) * w₂ x) * w₁ x + (g₂ (w x) * w₁ x) * w₂ x) +
        ((g₂ (w x) * w₁ x) * w₂ x + g₁ (w x) * w₃ x)) := by
  refine ⟨fun x hx => (hg.d0 (w x) (hmaps x hx)).comp x (hw.d0 x hx), fun x hx => ?_,
    fun x hx => ?_⟩
  · exact ((hg.d1 (w x) (hmaps x hx)).comp x (hw.d0 x hx)).mul (hw.d1 x hx)
  · have a1 : HasDerivAt (fun x => g₂ (w x) * w₁ x)
        ((g₃ (w x) * w₁ x) * w₁ x + g₂ (w x) * w₂ x) x :=
      ((hg.d2 (w x) (hmaps x hx)).comp x (hw.d0 x hx)).mul (hw.d1 x hx)
    exact (a1.mul (hw.d1 x hx)).add
      (((hg.d1 (w x) (hmaps x hx)).comp x (hw.d0 x hx)).mul (hw.d2 x hx))

namespace JetEncl

variable {T V : Set ℝ} {F g : ℝ → ℝ} {A G : IJet P}

/-- The Faà di Bruno law: if `G` encloses the jet of `g` on `V` and `A` that of `F` on `T`, with `F(T) ⊆ V`,
then `IJet.comp G A` encloses the jet of `g ∘ F` on `T`. -/
theorem comp (hg : JetEncl V g G) (hA : JetEncl T F A) (hmaps : ∀ t ∈ T, F t ∈ V) :
    JetEncl T (fun t => g (F t)) (IJet.comp G A) := by
  obtain ⟨g₁, g₂, g₃, hj, hb⟩ := hg
  obtain ⟨F₁, F₂, F₃, hk, hc⟩ := hA
  refine ⟨_, _, _, jet3_comp hj hk hmaps, fun t ht => ?_⟩
  obtain ⟨b0, b1, b2, b3⟩ := hb (F t) (hmaps t ht)
  obtain ⟨a0, a1, a2, a3⟩ := hc t ht
  refine ⟨b0, IV.mem_mul b1 a1,
    mem_of_eq (IV.mem_add (IV.mem_mul b1 a2) (IV.mem_mul b2 (IV.mem_sq a1))) (by ring),
    mem_of_eq (IV.mem_add (IV.mem_add (IV.mem_mul b1 a3)
      (IV.mem_mulPow2 (IV.mem_mul b2 (IV.mem_mul a1 a2)) 1))
      (IV.mem_mul b3 (IV.mem_mul (IV.mem_sq a1) a1))) (by ring)⟩

end JetEncl

/-! ### Derivatives of the outer functions -/

theorem hasDerivAt_inv_pow_succ {y : ℝ} (hy : y ≠ 0) (n : ℕ) :
    HasDerivAt (fun y : ℝ => y⁻¹ ^ (n + 1)) (-((n : ℝ) + 1) * y⁻¹ ^ (n + 2)) y := by
  have h := (hasDerivAt_inv hy).fun_pow (n + 1)
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  rw [← inv_pow]
  push_cast
  ring

theorem hasDerivAt_sqrt_inv_pow_succ {y : ℝ} (hy : 0 < y) (n : ℕ) :
    HasDerivAt (fun y : ℝ => (√y)⁻¹ ^ (n + 1)) (-((n : ℝ) + 1) / 2 * (√y)⁻¹ ^ (n + 3)) y := by
  have hs : 0 < √y := Real.sqrt_pos.mpr hy
  have hq : HasDerivAt (fun y : ℝ => (√y)⁻¹) (-(1 / (2 * √y)) / √y ^ 2) y :=
    (Real.hasDerivAt_sqrt hy.ne').inv hs.ne'
  have h := hq.fun_pow (n + 1)
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  have key : ∀ s : ℝ, s ≠ 0 → ((n + 1 : ℕ) : ℝ) * s⁻¹ ^ n * (-(1 / (2 * s)) / s ^ 2) =
      -((n : ℝ) + 1) / 2 * s⁻¹ ^ (n + 3) := by
    intro s hs0
    rw [pow_add]
    push_cast
    field_simp
  exact key _ hs.ne'

/-! ### Outer jets -/

/-- `invOuterOf h` encloses the jet of `y ↦ 1/y` on `V`, if `h` encloses `1/y` there (`y ≠ 0`). -/
theorem JetEncl.invOuterOf {V : Set ℝ} {h : IV P} (hV : ∀ y ∈ V, y ≠ 0 ∧ IV.Mem y⁻¹ h) :
    JetEncl V (fun y => y⁻¹) (IJet.invOuterOf h) := by
  refine ⟨fun y => -(y⁻¹ ^ 2), fun y => 2 * y⁻¹ ^ 3, fun y => -6 * y⁻¹ ^ 4,
    ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · exact (hasDerivAt_inv (hV y hy).1).congr_deriv (by rw [inv_pow])
  · exact (hasDerivAt_inv_pow_succ (hV y hy).1 1).neg.congr_deriv (by push_cast; ring)
  · exact ((hasDerivAt_inv_pow_succ (hV y hy).1 2).const_mul 2).congr_deriv (by push_cast; ring)
  · have hh := (hV y hy).2
    exact ⟨hh, IV.mem_neg (IV.mem_sq hh), mem_of_eq (IV.mem_mul (IV.mem_sq hh) hh) (by ring),
      mem_of_eq (IV.mem_neg (IV.mem_sq (IV.mem_sq hh))) (by ring)⟩

/-- `logOuterOf L h` encloses the jet of `log` on `V ⊆ (0, ∞)`, if `L` encloses `log y` and `h` encloses
`1/y` there. -/
theorem JetEncl.logOuterOf {V : Set ℝ} {L h : IV P}
    (hV : ∀ y ∈ V, 0 < y ∧ IV.Mem (Real.log y) L ∧ IV.Mem y⁻¹ h) :
    JetEncl V Real.log (IJet.logOuterOf L h) := by
  refine ⟨fun y => y⁻¹, fun y => -(y⁻¹ ^ 2), fun y => 2 * y⁻¹ ^ 3,
    ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · exact Real.hasDerivAt_log (hV y hy).1.ne'
  · exact (hasDerivAt_inv (hV y hy).1.ne').congr_deriv (by rw [inv_pow])
  · exact (hasDerivAt_inv_pow_succ (hV y hy).1.ne' 1).neg.congr_deriv (by push_cast; ring)
  · obtain ⟨-, hL, hh⟩ := hV y hy
    exact ⟨hL, hh, mem_of_eq (IV.mem_neg (IV.mem_divNat (IV.mem_sq hh) two_pos)) (by push_cast; ring),
      mem_of_eq (IV.mem_divNat (IV.mem_mul (IV.mem_sq hh) hh) three_pos) (by push_cast; ring)⟩

/-- `sqrtOuterOf s k` encloses the jet of `√` on `V ⊆ (0, ∞)`, if `s` encloses `√y` and `k` encloses `1/√y`
there. -/
theorem JetEncl.sqrtOuterOf {V : Set ℝ} {s k : IV P}
    (hV : ∀ y ∈ V, 0 < y ∧ IV.Mem (√y) s ∧ IV.Mem (√y)⁻¹ k) :
    JetEncl V Real.sqrt (IJet.sqrtOuterOf s k) := by
  refine ⟨fun y => (√y)⁻¹ / 2, fun y => -((√y)⁻¹ ^ 3) / 4, fun y => 3 * (√y)⁻¹ ^ 5 / 8,
    ⟨fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩, fun y hy => ?_⟩
  · exact (Real.hasDerivAt_sqrt (hV y hy).1.ne').congr_deriv (by field_simp)
  · have h := (hasDerivAt_sqrt_inv_pow_succ (hV y hy).1 0).div_const 2
    simp only [zero_add, pow_one] at h
    exact h.congr_deriv (by push_cast; ring)
  · have h := ((hasDerivAt_sqrt_inv_pow_succ (hV y hy).1 2).neg).div_const 4
    exact h.congr_deriv (by push_cast; ring)
  · obtain ⟨-, hs, hk⟩ := hV y hy
    exact ⟨hs, mem_of_eq (IV.mem_divPow2 hk 1) (by ring),
      mem_of_eq (IV.mem_neg (IV.mem_divPow2 (IV.mem_mul (IV.mem_sq hk) hk) 3)) (by ring),
      mem_of_eq (IV.mem_divPow2 (IV.mem_mul (IV.mem_sq (IV.mem_sq hk)) hk) 4) (by ring)⟩

/-! ### Reciprocal, quotient, logarithm and square root of jets -/

namespace JetEncl

variable {T : Set ℝ} {F G : ℝ → ℝ} {A B : IJet P}

theorem invPos (hA : JetEncl T F A) (hpos : IJet.posB A = true) :
    JetEncl T (fun t => (F t)⁻¹) (IJet.invPos A) := by
  refine comp (V := {y | IV.Mem y A.c0}) (JetEncl.invOuterOf fun y hy => ⟨?_, ?_⟩) hA
    (fun t ht => hA.mem_c0 ht)
  · exact (IV.posB_sound hpos hy).ne'
  · exact mem_invPos hpos hy

theorem divPos (hA : JetEncl T F A) (hB : JetEncl T G B) (hpos : IJet.posB B = true) :
    JetEncl T (fun t => F t / G t) (IJet.divPos A B) := by
  show JetEncl T _ (IJet.mul A (IJet.invPos B))
  simpa only [div_eq_mul_inv] using hA.mul (hB.invPos hpos)

theorem log {A : IJet 128} (hA : JetEncl T F A) (hpos : IJet.posB A = true) :
    JetEncl T (fun t => Real.log (F t)) (IJet.log A) := by
  refine comp (V := {y | IV.Mem y A.c0}) (JetEncl.logOuterOf fun y hy => ⟨?_, ?_, ?_⟩) hA
    (fun t ht => hA.mem_c0 ht)
  · exact IV.posB_sound hpos hy
  · exact IV.mem_logPos hpos hy
  · exact mem_invPos hpos hy

theorem sqrtWith {l h : ℕ} (hA : JetEncl T F A) (hok : IJet.sqrtOK A l h = true) :
    JetEncl T (fun t => √(F t)) (IJet.sqrtWith A l h) := by
  simp only [IJet.sqrtOK, Bool.and_eq_true] at hok
  obtain ⟨hc, hl⟩ := hok
  have hS : IV.posB (IV.ofNatPair l h : IV P) = true := by
    simpa [IV.posB, IV.ofNatPair, SInt.pos] using hl
  refine comp (V := {y | IV.Mem y A.c0}) (JetEncl.sqrtOuterOf fun y hy => ⟨?_, ?_, ?_⟩) hA
    (fun t ht => hA.mem_c0 ht)
  · exact Real.sqrt_pos.mp (IV.posB_sound hS (IV.mem_sqrt_of_sqrtCheck hc hy))
  · exact IV.mem_sqrt_of_sqrtCheck hc hy
  · exact mem_invPos hS (IV.mem_sqrt_of_sqrtCheck hc hy)

theorem sqrt (hA : JetEncl T F A) (hok : IJet.sqrtB A = true) :
    JetEncl T (fun t => √(F t)) (IJet.sqrt A) :=
  hA.sqrtWith hok

end JetEncl

end SandierSerfaty.Certificate.Jet
