/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Lambda.Point
public import SandierSerfaty.Certificate.Box.EvalData
public import SandierSerfaty.Certificate.Table.InnerBridge
public import SandierSerfaty.Certificate.Basis.CoreSound

/-!
# The realization of the whole table by the segment models

`TableModel F a`: the real nodes `a` lie in the node intervals of `F`, increase strictly from `b` to `l`, and every
cell `i` lies in a closed segment `seg j` whose model (`F0m j`, `Em j` with the truncated sector functions)
is enclosed by the cell tuple on `[a_i, a_{i+1}]` and by the node tuple at `a_{i+1}` (the content of
`Table.TableEncloses` for the segments `1, …, 5`). The same `j` serves the cell and its right node, which is what
`Box.QRealizes` needs. From it:

* `TableModel.tableRealized`, `TableModel.fRealized`: the realizations `Box.TableRealized` (via `Box.CellModel`)
  and `Lambda.FRealized` (via `NodeEncl`) consumed by the A7, Hessian and fine-`λ` layers;
* `TableModel.qRealizes`: `Box.QRealizes` of a query table whose cells pass `Query.cellCheck` against the table.

The first segment is checked against the exact inner closed form `F0inner` (`Table.InnerBridge`), not the model
`F0m 0`; `TupEncl.model_of_inner` transfers its enclosures to the model: on `seg 0` the two agree
(`trunc_f₀_inner`, `trunc_f₀_eq_F0m`, and `ẽ = 0 = Em 0`), the model is differentiable at every `t > 0`
(`differentiableAt_F0m`, `differentiableAt_Em`), and `seg 0` has unique derivatives.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-! ### Differentiability of the segment models -/

theorem differentiableAt_Piece_D (i j : ℕ) {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ (Piece.D i j) x :=
  ((contDiffOn_Piece_D i j).differentiableOn (by simp)).differentiableAt (Ioi_mem_nhds hx)

theorem differentiableAt_D1 (i j : ℕ) {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ (D1 i j) x :=
  ((jet3_iteratedDeriv isOpen_Ioi ((contDiffOn_Piece_D i j).of_le (by norm_cast))).d1 x hx).differentiableAt

theorem differentiableAt_Qm (i j : ℕ) {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ (Qm i j) x := by
  unfold Qm
  exact (differentiableAt_id.mul (differentiableAt_D1 i j hx)).sub
    ((differentiableAt_const _).mul (differentiableAt_Piece_D i j hx))

/-- The model `f̃₀` of segment `j` with the truncated sector functions is differentiable at every `t > 0`. -/
theorem differentiableAt_F0m (j : ℕ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (F0m j Trunc.S₁ Trunc.S₂ TH) x := by
  have hD : ∀ m, DifferentiableAt ℝ (Piece.D m j) x := fun m => differentiableAt_Piece_D m j hx
  have hH : ∀ m, DifferentiableAt ℝ (TH m) x := fun m => (hasDerivAt_trunc_H (k m) hx).differentiableAt
  have hS1 : DifferentiableAt ℝ Trunc.S₁ x := (hasDerivAt_trunc_S₁ hx).differentiableAt
  have hS2 : DifferentiableAt ℝ Trunc.S₂ x := (hasDerivAt_trunc_S₂ hx).differentiableAt
  have hds : DifferentiableAt ℝ (dsumR j 0 39) x := by
    unfold dsumR
    exact DifferentiableAt.fun_sum fun n _ => (differentiableAt_const _).mul (hD _)
  have hlin : DifferentiableAt ℝ (linR j TH 0 39) x := by
    unfold linR
    exact DifferentiableAt.fun_sum fun n _ =>
      ((differentiableAt_const _).mul (hD _)).add ((differentiableAt_const _).mul ((hD _).mul (hH _)))
  have hqin : ∀ a, DifferentiableAt ℝ (quadInR j a 0 39) x := fun a => by
    unfold quadInR
    exact DifferentiableAt.fun_sum fun n _ => (differentiableAt_const _).mul (hD _)
  have hq : DifferentiableAt ℝ (quadR j 0 39) x := by
    unfold quadR
    exact DifferentiableAt.fun_sum fun n _ => (hD _).mul (hqin _)
  have hlog : DifferentiableAt ℝ Real.log x := Real.differentiableAt_log hx.ne'
  unfold F0m
  exact ((differentiableAt_const _).mul (hS1.add ((differentiableAt_id.mul differentiableAt_id).mul hds))).sub
    ((differentiableAt_const _).mul (((hlog.add hS2).add hlin).add hq))

/-- The model `ẽ` of segment `j` is differentiable at every `t > 0`. -/
theorem differentiableAt_Em (j : ℕ) {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ (Em j) x := by
  have hin : ∀ a, DifferentiableAt ℝ (eInR j a 0 39) x := fun a => by
    unfold eInR
    exact DifferentiableAt.fun_sum fun n _ => (differentiableAt_const _).mul (differentiableAt_Qm _ j hx)
  have he : DifferentiableAt ℝ (eR j 0 39) x := by
    unfold eR
    exact DifferentiableAt.fun_sum fun n _ => (differentiableAt_Qm _ j hx).mul (hin _)
  unfold Em
  exact (differentiableAt_const _).mul he

/-! ### The first segment: from the inner closed form to the model -/

/-- `F0m 0 = F0inner` on `seg 0`. -/
theorem F0m_zero_eq_inner {t : ℝ} (ht : t ∈ seg 0) : F0m 0 Trunc.S₁ Trunc.S₂ TH t = F0inner t := by
  rw [← trunc_f₀_eq_F0m (by norm_num) ht, trunc_f₀_inner ht]

/-- `Em 0 = 0` on `seg 0`. -/
theorem Em_zero_eq {t : ℝ} (ht : t ∈ seg 0) : Em 0 t = 0 := by
  rw [← trunc_e_eq_Em (by norm_num) ht, trunc_e_inner ht]

/-- A function differentiable at `x ∈ seg 0` agreeing on `seg 0` with a function of derivative `D` at `x` has
derivative `D` at `x`. -/
theorem hasDerivAt_of_eqOn_seg0 {f g : ℝ → ℝ} {x D : ℝ} (hx : x ∈ seg 0) (hf : DifferentiableAt ℝ f x)
    (hfg : ∀ t ∈ seg 0, f t = g t) (hg : HasDerivAt g D x) : HasDerivAt f D x := by
  have h1 : HasDerivWithinAt f D (seg 0) x :=
    hg.hasDerivWithinAt.congr (fun t ht => hfg t ht) (hfg x hx)
  have h2 := hf.hasDerivAt
  have e := (uniqueDiffOn_seg (j := 0) (by norm_num) x hx).eq_deriv (seg 0) h2.hasDerivWithinAt h1
  rwa [e] at h2

/-- **The inner enclosures are enclosures of the model `F0m 0`, `Em 0`** on any set inside `seg 0`. -/
theorem TupEncl.model_of_inner {T : Set ℝ} (hT : T ⊆ seg 0) {tp : Tup}
    (h : TupEncl T F0inner (fun _ => 0) tp) : TupEncl T (F0m 0 Trunc.S₁ Trunc.S₂ TH) (Em 0) tp := by
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := h
  refine ⟨F₁, F₂, E₁, E₂, fun x hx => ?_, fun t ht => ?_⟩
  · obtain ⟨d0, d1, d2, d3⟩ := hd x hx
    have hx0 : 0 < x := (hT hx).1
    exact ⟨hasDerivAt_of_eqOn_seg0 (hT hx) (differentiableAt_F0m 0 hx0) (fun t ht => F0m_zero_eq_inner ht) d0,
      d1, hasDerivAt_of_eqOn_seg0 (hT hx) (differentiableAt_Em 0 hx0) (fun t ht => Em_zero_eq ht) d2, d3⟩
  · obtain ⟨m0, m1, m2, m3, m4, m5⟩ := hm t ht
    refine ⟨?_, m1, m2, ?_, m4, m5⟩
    · rw [F0m_zero_eq_inner (hT ht)]; exact m0
    · rw [Em_zero_eq (hT ht)]; exact m3

/-! ### The model of the whole table -/

/-- **The table `F` is realized by the segment models** at the real nodes `a`. -/
structure TableModel (F : FTable) (a : ℕ → ℝ) : Prop where
  /-- `a i ∈ node i`. -/
  node : ∀ i, i ≤ F.T.n → IV.Mem (a i) (F.T.node i)
  /-- The real nodes increase strictly. -/
  lt : ∀ i, i < F.T.n → a i < a (i + 1)
  /-- The first node is `b`. -/
  first : a 0 = Calibration.b
  /-- The last node is `l`. -/
  last : a F.T.n = Calibration.l
  /-- Every cell lies in a closed segment whose model its cell tuple and its right node tuple enclose. -/
  cell : ∀ i, i < F.T.n → ∃ j, j ≤ 6 ∧ Icc (a i) (a (i + 1)) ⊆ seg j ∧
    TupEncl (Icc (a i) (a (i + 1))) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (F.T.cell i) ∧
    TupEncl {a (i + 1)} (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (F.nt i)

theorem TableModel.le_add {F : FTable} {a : ℕ → ℝ} (h : TableModel F a) {i : ℕ} :
    ∀ k, i + k ≤ F.T.n → a i ≤ a (i + k)
  | 0, _ => le_rfl
  | k + 1, hk => (h.le_add k (by omega)).trans (by
      have := h.lt (i + k) (by omega); rw [← add_assoc]; exact this.le)

theorem TableModel.mem_bl {F : FTable} {a : ℕ → ℝ} (h : TableModel F a) {i : ℕ} (hi : i ≤ F.T.n) :
    Calibration.b ≤ a i ∧ a i ≤ Calibration.l := by
  constructor
  · have := h.le_add (i := 0) i (by omega); rw [zero_add, h.first] at this; exact this
  · have := h.le_add (i := i) (F.T.n - i) (by omega)
    rw [show i + (F.T.n - i) = F.T.n by omega, h.last] at this; exact this

/-- **`Box.TableRealized`** from the table model. -/
theorem TableModel.tableRealized {F : FTable} {a : ℕ → ℝ} (h : TableModel F a) : TableRealized F.T a where
  node := h.node
  first := h.first
  last := h.last
  cell i hi := by
    obtain ⟨j, hj, hseg, hc, -⟩ := h.cell i hi
    exact ⟨j, ⟨hj, h.lt i hi, hseg, hc⟩⟩

/-- **`Lambda.FRealized`** from the table model. -/
theorem TableModel.fRealized {F : FTable} {a : ℕ → ℝ} (h : TableModel F a) : FRealized F a where
  tab := h.tableRealized
  nt i hi := by
    obtain ⟨j, hj, hseg, -, hn⟩ := h.cell i hi
    exact ⟨j, hj, hseg ⟨(h.lt i hi).le, le_rfl⟩, hn⟩

/-- **`Box.QRealizes`** of a query table whose first `Q.n ≤ n` cells pass `cellCheck` against the table. -/
theorem TableModel.qRealizes {F : FTable} {a : ℕ → ℝ} (h : TableModel F a) {Q : QTable} {rf re : ℕ}
    (hn : Q.n ≤ F.T.n)
    (hq : ∀ i, i < Q.n → cellCheck (F.T.node i) (F.T.node (i + 1)) (F.T.cell i) (F.nt i) (Q.cell i) rf re = true) :
    QRealizes Q rf re := by
  intro i hi
  obtain ⟨j, hj, hseg, hc, hnt⟩ := h.cell i (by omega)
  exact ⟨j, hj, a i, a (i + 1), F.T.node i, F.T.node (i + 1), F.T.cell i, F.nt i, hq i hi, hseg, hc, hnt,
    h.node i (by omega), h.node (i + 1) (by omega), (h.mem_bl (i := i) (by omega)).1,
    (h.mem_bl (i := i + 1) (by omega)).2⟩

end SandierSerfaty.Certificate.Lambda
