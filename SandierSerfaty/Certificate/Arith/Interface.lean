/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# The certified arithmetic interface

Ported from an earlier, unpublished interval-arithmetic formalization of Scott Armstrong and Zohar
Komargodski, renamed into `SandierSerfaty.Certificate.Arith`. The complex wrapper `CC` of the original is not ported (the certificate here
is real-valued).

`CertArith α` is the data of a certified arithmetic backend (the exact real denoted by each element and the
rounded operations with their error terms); `LawfulCertArith α` is the `Prop`-valued class of its soundness
laws. Definitions over `CertArith` are computational and law-free; every correctness theorem uses
`[LawfulCertArith α]`. The backends of this library are `CertFixed P` (`Int` fixed point, ported) and
`Fx P` (sign-magnitude fixed point, `SandierSerfaty.Certificate.Arith.FxLemmas`).
-/

@[expose] public section

namespace SandierSerfaty.Certificate.Arith

/-- A certified arithmetic backend (data only). `val a` is the exact real denoted by `a`.
`add`/`mul` may round (fixed point) or be exact (`ℚ`); `addErr`/`mulErr` bound the rounding error.
`upAdd`/`upMul` round upward and are used on nonnegative radii only. Comparisons are one-sided
tests. Definitions over `CertArith` are computational and law-free; every correctness theorem that
uses a value of `ofInt`, `neg`, `add`, `mul` or a comparison assumes `[LawfulCertArith α]`. -/
class CertArith (α : Type) where
  /-- The real denoted by an element. -/
  val : α → ℝ
  /-- The exact integer `z`. -/
  ofInt : ℤ → α
  /-- An upward conversion of an exact rational parameter. -/
  ofRatUp : ℚ → α
  /-- A downward conversion of an exact rational parameter. -/
  ofRatDown : ℚ → α
  /-- Rounded addition. -/
  add : α → α → α
  /-- Exact negation. -/
  neg : α → α
  /-- Rounded multiplication. -/
  mul : α → α → α
  /-- Exact absolute value. -/
  abs : α → α
  /-- A bound of the rounding error of `add`. -/
  addErr : α → α → α
  /-- A bound of the rounding error of `mul`. -/
  mulErr : α → α → α
  /-- Upward-rounded addition. -/
  upAdd : α → α → α
  /-- Upward-rounded multiplication (of nonnegative elements). -/
  upMul : α → α → α
  /-- A one-sided test of `≤`. -/
  ble : α → α → Bool
  /-- A one-sided test of `<`. -/
  blt : α → α → Bool
  /-- A one-sided test of `=`. -/
  beq : α → α → Bool

/-- Soundness of a backend (one `Prop`-valued class, proved once per backend). -/
class LawfulCertArith (α : Type) [CertArith α] : Prop where
  val_ofInt : ∀ z : ℤ, CertArith.val (CertArith.ofInt (α := α) z) = z
  ofRatUp_ge : ∀ q : ℚ, (q : ℝ) ≤ CertArith.val (CertArith.ofRatUp (α := α) q)
  ofRatDown_le : ∀ q : ℚ, CertArith.val (CertArith.ofRatDown (α := α) q) ≤ q
  add_err : ∀ a b : α, |CertArith.val (CertArith.add a b) - (CertArith.val a + CertArith.val b)| ≤
    CertArith.val (CertArith.addErr a b)
  val_neg : ∀ a : α, CertArith.val (CertArith.neg a) = -CertArith.val a
  mul_err : ∀ a b : α, |CertArith.val (CertArith.mul a b) - CertArith.val a * CertArith.val b| ≤
    CertArith.val (CertArith.mulErr a b)
  val_abs : ∀ a : α, CertArith.val (CertArith.abs a) = |CertArith.val a|
  upAdd_ge : ∀ a b : α, CertArith.val a + CertArith.val b ≤ CertArith.val (CertArith.upAdd a b)
  upMul_ge : ∀ a b : α, 0 ≤ CertArith.val a → 0 ≤ CertArith.val b →
    CertArith.val a * CertArith.val b ≤ CertArith.val (CertArith.upMul a b)
  ble_sound : ∀ a b : α, CertArith.ble a b = true → CertArith.val a ≤ CertArith.val b
  blt_sound : ∀ a b : α, CertArith.blt a b = true → CertArith.val a < CertArith.val b
  beq_sound : ∀ a b : α, CertArith.beq a b = true → CertArith.val a = CertArith.val b

end SandierSerfaty.Certificate.Arith
