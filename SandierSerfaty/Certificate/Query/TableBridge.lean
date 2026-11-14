/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.LookupSound
public import SandierSerfaty.Certificate.Table.Bridge
public import SandierSerfaty.Tails.PropTrunc
public import SandierSerfaty.Tails.PropE

/-!
# From the table chunks to the cell enclosures of `ITable.Encl`

`Table.TableEncloses` (the output of `Table.chunkCheck_sound`) states the enclosures for the *model* functions
`F0m j`, `Em j` of a segment `j` and their derivative witnesses. On the closed segment `seg j` the truncated
`Trunc.f₀`, `Trunc.e` equal the models (`Table.trunc_f₀_eq_F0m`, `trunc_e_eq_Em`); both sides are differentiable
at the points of `seg j` (the truncated functions on `(0, ∞)`, `Tails.exists_jet_Trunc_f₀`,
`Tails.hasDerivAt_Trunc_e`), and `seg j` has unique derivatives, so the derivatives agree:

* `deriv_trunc_f₀_eq`, `deriv_trunc_e_eq`;
* `cell_enclosures`: from `TupEncl (Icc a b) (F0m j …) (Em j) ct` and `Icc a b ⊆ seg j`, every `t ∈ [a, b]` has
  `f̃₀ t, f̃₀' t, ẽ t, ẽ' t` in the corresponding components of `ct` — the cell fields of `ITable.Encl`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Calibration
open SandierSerfaty.Tails

theorem deriv_trunc_f₀_eq (hc : FiniteCore) {j : ℕ} (hj : j ≤ 6) {t F₁ : ℝ} (ht : t ∈ seg j)
    (hd : HasDerivAt (F0m j Trunc.S₁ Trunc.S₂ TH) F₁ t) : deriv Trunc.f₀ t = F₁ := by
  obtain ⟨G₁, G₂, jt⟩ := exists_jet_Trunc_f₀ hc
  have h1 : HasDerivAt Trunc.f₀ (G₁ t) t := jt.d0 t (seg_subset_Ioi ht)
  have h2 : HasDerivWithinAt Trunc.f₀ F₁ (seg j) t :=
    hd.hasDerivWithinAt.congr (fun y hy => trunc_f₀_eq_F0m hj hy) (trunc_f₀_eq_F0m hj ht)
  have := (uniqueDiffOn_seg hj t ht).eq_deriv (seg j) h1.hasDerivWithinAt h2
  rw [h1.deriv, this]

theorem deriv_trunc_e_eq {j : ℕ} (hj : j ≤ 6) {t E₁ : ℝ} (ht : t ∈ seg j)
    (hd : HasDerivAt (Em j) E₁ t) : deriv Trunc.e t = E₁ := by
  have h1 : HasDerivAt Trunc.e (sTe1 t) t := hasDerivAt_Trunc_e (seg_subset_Ioi ht)
  have h2 : HasDerivWithinAt Trunc.e E₁ (seg j) t :=
    hd.hasDerivWithinAt.congr (fun y hy => trunc_e_eq_Em hj hy) (trunc_e_eq_Em hj ht)
  have := (uniqueDiffOn_seg hj t ht).eq_deriv (seg j) h1.hasDerivWithinAt h2
  rw [h1.deriv, this]

/-- **The cell enclosures** of `ITable.Encl` from the table soundness of one cell. -/
theorem cell_enclosures (hc : FiniteCore) {j : ℕ} (hj : j ≤ 6) {a b : ℝ} (hseg : Icc a b ⊆ seg j)
    {ct : Tup} (h : TupEncl (Icc a b) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) ct) :
    ∀ t ∈ Icc a b, IV.Mem (Trunc.f₀ t) ct.f0 ∧ IV.Mem (deriv Trunc.f₀ t) ct.f1 ∧
      IV.Mem (Trunc.e t) ct.e0 ∧ IV.Mem (deriv Trunc.e t) ct.e1 := by
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := h
  intro t ht
  obtain ⟨m0, m1, -, n0, n1, -⟩ := hm t ht
  obtain ⟨d0, -, d2, -⟩ := hd t ht
  rw [trunc_f₀_eq_F0m hj (hseg ht), trunc_e_eq_Em hj (hseg ht), deriv_trunc_f₀_eq hc hj (hseg ht) d0,
    deriv_trunc_e_eq hj (hseg ht) d2]
  exact ⟨m0, m1, n0, n1⟩

end SandierSerfaty.Certificate.Query
