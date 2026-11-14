/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.CellSound
public import SandierSerfaty.Certificate.Table.Bridge

/-!
# Validity of a query cell against the truncated calibration

`CellValid c rf re` is the real content of a checked query cell (`Query.Cell`): for every `t ∈ [c.lo, c.hi]`

* `t` lies in the table range `[b, l]`;
* `|f̃₀(t) - (fb + f1 (t - tb))| ≤ rf/2^128` and `|ẽ(t) - (eb + e1 (t - tb))| ≤ re/2^128`
  (`f̃₀ = Cal.Trunc.f₀`, `ẽ = Cal.Trunc.e`, the finite-mode objects of `05`/`06`);

and the stored numbers obey the magnitude caps `|fb|, |eb| ≤ 2^8`, `|f1|, |e1| ≤ 2^20`.

`cellCheck_sound`: from the cell check and the table soundness for one cell of segment `j` (`TupEncl` of the
cell and of its right node, the content of `Table.TableEncloses`), the cell is valid. The two channels
`f̃₀`, `ẽ` are the model functions `F0m j`, `Em j` of the segment, which equal `Trunc.f₀`, `Trunc.e` on it
(`Table.trunc_f₀_eq_F0m`, `Table.trunc_e_eq_Em`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Calibration

/-- The real content of a checked query cell. -/
structure CellValid (c : QCell) (rf re : ℕ) : Prop where
  /-- The cell serves only `t ∈ [b, l]`. -/
  rng : ∀ t : ℝ, c.lo.val ≤ t → t ≤ c.hi.val → Calibration.b ≤ t ∧ t ≤ Calibration.l
  /-- The Taylor approximation of `f̃₀`. -/
  f_app : ∀ t : ℝ, c.lo.val ≤ t → t ≤ c.hi.val →
    |Trunc.f₀ t - (c.fb.val + c.f1.val * (t - c.tb.val))| ≤ rf / 2 ^ 128
  /-- The Taylor approximation of `ẽ`. -/
  e_app : ∀ t : ℝ, c.lo.val ≤ t → t ≤ c.hi.val →
    |Trunc.e t - (c.eb.val + c.e1.val * (t - c.tb.val))| ≤ re / 2 ^ 128
  /-- `|fb| ≤ 2^8`. -/
  fb_cap : |c.fb.val| ≤ 2 ^ 8
  /-- `|eb| ≤ 2^8`. -/
  eb_cap : |c.eb.val| ≤ 2 ^ 8
  /-- `|f1| ≤ 2^20`. -/
  f1_cap : |c.f1.val| ≤ 2 ^ 20
  /-- `|e1| ≤ 2^20`. -/
  e1_cap : |c.e1.val| ≤ 2 ^ 20
  /-- `|tb| ≤ 1`. -/
  tb_cap : |c.tb.val| ≤ 1

theorem abs_val_le_of_mag {x : Fx 128} {k : ℕ} (h : Nat.ble x.v.mag (Nat.shiftLeft 1 (128 + k)) = true) :
    |x.val| ≤ 2 ^ k := by
  have h1 : x.v.mag ≤ 2 ^ (128 + k) := by
    have := Nat.ble_eq.mp h
    rwa [SInt.nat_shiftLeft_eq, one_mul] at this
  have h2 : (x.v.mag : ℝ) ≤ 2 ^ (128 + k) := by exact_mod_cast h1
  have hN := two_pow_pos128
  rw [Fx.val_def, abs_div, abs_of_pos hN, ← Int.cast_abs, SInt.abs_toInt, div_le_iff₀ hN]
  simpa [pow_add, mul_comm] using h2

theorem capsOK_sound {c : QCell} (h : capsOK c = true) :
    |c.fb.val| ≤ 2 ^ 8 ∧ |c.eb.val| ≤ 2 ^ 8 ∧ |c.f1.val| ≤ 2 ^ 20 ∧ |c.e1.val| ≤ 2 ^ 20 ∧ |c.tb.val| ≤ 1 := by
  simp only [capsOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := h
  refine ⟨abs_val_le_of_mag (k := 8) h1, abs_val_le_of_mag (k := 8) h2, abs_val_le_of_mag (k := 20) h3,
    abs_val_le_of_mag (k := 20) h4, ?_⟩
  simpa using abs_val_le_of_mag (k := 0) h5

/-- One channel of the cell check, with the derivative witness of the node tuple (which agrees with that of the
cell at `b`, by uniqueness of the derivative). -/
theorem channel_apply {F F₁ F₂ F₁' : ℝ → ℝ} {a b t : ℝ} {v u c2 n0 n1 : IV 128} {lo hi tb fb f1 : Fx 128}
    {r : ℕ} (hc : chanCheck v u c2 n0 n1 lo hi tb fb f1 r = true)
    (hF : ∀ x ∈ Icc a b, HasDerivAt F (F₁ x) x) (hF₁ : ∀ x ∈ Icc a b, HasDerivAt F₁ (F₂ x) x)
    (hF' : HasDerivAt F (F₁' b) b) (hc2 : ∀ x ∈ Icc a b, IV.Mem (F₂ x) c2) (hn0 : IV.Mem (F b) n0)
    (hn1 : IV.Mem (F₁' b) n1) (hv : IV.Mem a v) (hu : IV.Mem b u) (hlo : lo.val ≤ t) (hhi : t ≤ hi.val) :
    a ≤ t ∧ t ≤ b ∧ |F t - (fb.val + f1.val * (t - tb.val))| ≤ r / 2 ^ 128 := by
  obtain ⟨h3, h4⟩ := chanCheck_range hc hv hu hlo hhi
  have hbI : b ∈ Icc a b := ⟨h3.trans h4, le_rfl⟩
  have heq : F₁ b = F₁' b := (hF b hbI).unique hF'
  exact chanCheck_sound hc hF hF₁ hc2 hn0 (heq ▸ hn1) hv hu hlo hhi

/-- **Soundness of the cell check.** -/
theorem cellCheck_sound {j : ℕ} (hj : j ≤ 6) {a b : ℝ} {v u : IV 128} {ct nt : Tup} {c : QCell} {rf re : ℕ}
    (hc : cellCheck v u ct nt c rf re = true) (hseg : Icc a b ⊆ seg j)
    (hct : TupEncl (Icc a b) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) ct)
    (hnt : TupEncl {b} (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) nt) (hv : IV.Mem a v) (hu : IV.Mem b u)
    (hab : Calibration.b ≤ a) (hbl : b ≤ Calibration.l) : CellValid c rf re := by
  simp only [cellCheck, Bool.and_eq_true] at hc
  obtain ⟨hcf, hce, hcaps⟩ := hc
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := hct
  obtain ⟨F₁', F₂', E₁', E₂', hd', hm'⟩ := hnt
  obtain ⟨hcaps1, hcaps2, hcaps3, hcaps4, hcaps5⟩ := capsOK_sound hcaps
  have hb' : b ∈ ({b} : Set ℝ) := rfl
  refine ⟨fun t h1 h2 => ?_, fun t h1 h2 => ?_, fun t h1 h2 => ?_, hcaps1, hcaps2, hcaps3, hcaps4, hcaps5⟩
  · obtain ⟨h3, h4⟩ := chanCheck_range hcf hv hu h1 h2
    exact ⟨hab.trans h3, h4.trans hbl⟩
  · have h := channel_apply hcf (fun x hx => (hd x hx).1) (fun x hx => (hd x hx).2.1) (hd' b hb').1
      (fun x hx => (hm x hx).2.2.1) (hm' b hb').1 (hm' b hb').2.1 hv hu h1 h2
    simpa [trunc_f₀_eq_F0m hj (hseg ⟨h.1, h.2.1⟩)] using h.2.2
  · have h := channel_apply hce (fun x hx => (hd x hx).2.2.1) (fun x hx => (hd x hx).2.2.2)
      (hd' b hb').2.2.1 (fun x hx => (hm x hx).2.2.2.2.2) (hm' b hb').2.2.2.1 (hm' b hb').2.2.2.2.1 hv hu h1 h2
    simpa [trunc_e_eq_Em hj (hseg ⟨h.1, h.2.1⟩)] using h.2.2

end SandierSerfaty.Certificate.Query
