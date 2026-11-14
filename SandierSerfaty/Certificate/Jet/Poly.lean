/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Jet.Encl

/-!
# Polynomials of jets: Horner evaluation, Taylor shift, `cpol`

`hornerR rs x = rs₀ + x (rs₁ + x (rs₂ + …))` is the real polynomial with coefficients `rs` (lowest degree
first). If the interval list `cs` encloses `rs` coefficientwise (`List.Forall₂ IV.Mem rs cs`) and `X` encloses
the jet of `F`, then

* `IJet.horner X cs` encloses the jet of `t ↦ hornerR rs (F t)` (`JetEncl.horner`);
* `IJet.tshift M cs` encloses the coefficients `tshiftR m rs` of `y ↦ hornerR rs (y + m)` for `m ∈ M`
  (`forall₂_tshift`, `hornerR_tshiftR`);
* `IJet.cpol cs X`, the polynomial re-expanded about the midpoint of the cell, encloses the jet of
  `t ↦ hornerR rs (F t)` as well (`JetEncl.cpol`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Jet

open SandierSerfaty.Certificate.Arith

variable {P : ℕ}

/-- The real polynomial `rs₀ + x (rs₁ + x (rs₂ + …))` (coefficients lowest degree first). -/
@[expose] def hornerR : List ℝ → ℝ → ℝ
  | [], _ => 0
  | r :: rs, x => hornerR rs x * x + r

/-- One step of the real Taylor shift (the real counterpart of `IJet.shiftAdd`). -/
@[expose] def shiftAddR (m prev : ℝ) : List ℝ → List ℝ
  | [] => [prev]
  | s :: ss => (prev + m * s) :: shiftAddR m s ss

/-- The real Taylor shift (the real counterpart of `IJet.tshift`). -/
@[expose] def tshiftR (m : ℝ) : List ℝ → List ℝ
  | [] => []
  | r :: rs => shiftAddR m r (tshiftR m rs)

@[simp] theorem hornerR_nil (x : ℝ) : hornerR [] x = 0 := rfl

@[simp] theorem hornerR_cons (r : ℝ) (rs : List ℝ) (x : ℝ) :
    hornerR (r :: rs) x = hornerR rs x * x + r := rfl

theorem hornerR_shiftAddR (m prev y : ℝ) (ss : List ℝ) :
    hornerR (shiftAddR m prev ss) y = prev + (m + y) * hornerR ss y := by
  induction ss generalizing prev with
  | nil => simp [shiftAddR]
  | cons s ss ih => simp only [shiftAddR, hornerR_cons, ih]; ring

/-- The Taylor shift: `tshiftR m rs` are the coefficients of `y ↦ hornerR rs (y + m)`. -/
theorem hornerR_tshiftR (m y : ℝ) (rs : List ℝ) : hornerR (tshiftR m rs) y = hornerR rs (y + m) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [tshiftR, hornerR_shiftAddR, ih, hornerR_cons]; ring

theorem forall₂_shiftAdd {m prev : ℝ} {M Pv : IV P} (hm : IV.Mem m M) (hp : IV.Mem prev Pv)
    {ss : List ℝ} {Ss : List (IV P)} (h : List.Forall₂ IV.Mem ss Ss) :
    List.Forall₂ IV.Mem (shiftAddR m prev ss) (IJet.shiftAdd M Pv Ss) := by
  induction h generalizing prev Pv with
  | nil => exact List.Forall₂.cons hp List.Forall₂.nil
  | cons hab _ ih => exact List.Forall₂.cons (IV.mem_add hp (IV.mem_mul hm hab)) (ih hab)

theorem forall₂_tshift {m : ℝ} {M : IV P} (hm : IV.Mem m M) {rs : List ℝ} {cs : List (IV P)}
    (h : List.Forall₂ IV.Mem rs cs) : List.Forall₂ IV.Mem (tshiftR m rs) (IJet.tshift M cs) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons hab _ ih => exact forall₂_shiftAdd hm hab ih

namespace JetEncl

variable {T : Set ℝ} {F : ℝ → ℝ} {X : IJet P}

theorem horner (hX : JetEncl T F X) {rs : List ℝ} {cs : List (IV P)} (h : List.Forall₂ IV.Mem rs cs) :
    JetEncl T (fun t => hornerR rs (F t)) (IJet.horner X cs) := by
  induction h with
  | nil =>
    show JetEncl T (fun t => hornerR [] (F t)) (IJet.const ivZero)
    simpa using const (T := T) (mem_ivZero (P := P))
  | @cons r c rs cs hab _ ih =>
    show JetEncl T (fun t => hornerR (r :: rs) (F t)) (IJet.addIV (IJet.mul (IJet.horner X cs) X) c)
    simpa only [hornerR_cons] using (ih.mul hX).addIV hab

/-- The polynomial re-expanded about the midpoint of the cell encloses the jet of the polynomial. -/
theorem cpol (hX : JetEncl T F X) {rs : List ℝ} {cs : List (IV P)} (h : List.Forall₂ IV.Mem rs cs) :
    JetEncl T (fun t => hornerR rs (F t)) (IJet.cpol cs X) := by
  have hm := mem_ivMid X.c0
  have := (hX.subIV hm).horner (forall₂_tshift hm h)
  show JetEncl T _ (IJet.horner (IJet.subIV X (ivMid X.c0)) (IJet.tshift (ivMid X.c0) cs))
  simpa only [hornerR_tshiftR, sub_add_cancel] using this

end JetEncl

end SandierSerfaty.Certificate.Jet
