/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.FxG

/-!
# The row checks of the outer and negative-part assertions (A8, A9)

paper `comp:outer-grid`, `comp:negative-part`. A *row* is one `d` node (a dyadic
number `dm/2^128`) and the midpoint sums over the `s` partition `σ_k = sm k/2^128`:

* `midVal`: the value of `G` at the midpoint of cell `j` of the row: the midpoint is checked to be exact (even
  mantissa sum); if `t² ≥ lsq` (`lsq ≥ l²` with slack) the exterior formula `evalExt`
  (`G = dκ + d c/t²`, `e = 0`, `f = f(l) + κ(t² - l²)`, `c = f(l) - κ l²`) is used, otherwise the table query
  `Query.evalG` (checked square root and checked cell `idx j`, a *proposal* of the shard generator);
* `outerLoop`: one pass over the row with the exact accumulator `Q = ∑ (σ_{j+1} - σ_j) v_j` (units `2^-256`); at
  every node `k` outside the hole it tests `thr ≤ 2 Q_k` (`thr` a literal that encodes `K + E₀ + E_I + …`);
* `negLoop`: the same pass with the accumulator `N = ∑ (σ_{j+1} - σ_j) max 0 (-v_j)` and the final test `N ≤ thr`.

All arithmetic is exact (`SInt`), except the evaluation of `G`, whose error is bounded by the static budget
`deltaG`/`deltaExt` (`Box.EvalSound`). Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query

/-- The evaluator data: the query table, the constants `λ̂, μ̂` of the interior formula, the constants `κ̂ ≈ κ`,
`ĉ ≈ c = f(l) - κ l²` of the exterior formula and the exterior threshold `lsq` for `t²`. -/
structure EvalData where
  /-- The table of query cells. -/
  T : QTable
  /-- `λ̂`. -/
  lam : Fx 128
  /-- `μ̂`. -/
  mu : Fx 128
  /-- `κ̂ ≈ -π B(l) - λ/2`. -/
  kap : Fx 128
  /-- `ĉ ≈ f(l) - κ l²`. -/
  cc : Fx 128
  /-- Points with `t̂² ≥ lsq` use the exterior formula. -/
  lsq : Fx 128

/-- `t̂² = d·d + s·s` (each product truncated), the quantity `evalG` computes. -/
def t2Of (d s : Fx 128) : Fx 128 := Fx.add (Fx.mul d d) (Fx.mul s s)

/-- The exterior formula `G = d κ + d c/t²` (`e = 0`, `f(t) = f(l) + κ(t² - l²)`). -/
def evalExt (E : EvalData) (d T2 : Fx 128) : Fx 128 :=
  Fx.add (Fx.mul E.kap d) (Fx.div (Fx.mul E.cc d) T2)

/-- The value of `G` at a dyadic point: exterior formula for `t̂² ≥ lsq`, else the table query in cell `i`. -/
def evalMid (E : EvalData) (i : Nat) (d s : Fx 128) : Option (Fx 128) :=
  cond (Fx.ble E.lsq (t2Of d s)) (some (evalExt E d (t2Of d s))) (evalG E.T E.lam E.mu i d s)

/-- The fixed-point number with mantissa `m`. -/
def fxM (m : Nat) : Fx 128 := ⟨⟨false, m⟩⟩

/-- The mantissa of the midpoint of cell `j`. -/
def midM (sm : Nat → Nat) (j : Nat) : Nat := Nat.div (Nat.add (sm j) (sm (Nat.succ j))) 2

/-- The value at the midpoint of cell `j` of the row `dm` (`none` if the midpoint is inexact or a query fails). -/
def midVal (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (j : Nat) : Option (Fx 128) :=
  cond (Nat.beq (Nat.mod (Nat.add (sm j) (sm (Nat.succ j))) 2) 0)
    (evalMid E (idx j) (fxM dm) (fxM (midM sm j))) none

/-- The width of cell `j` (the mantissa difference; the check `sm j ≤ sm (j+1)` makes it exact). -/
def widthM (sm : Nat → Nat) (j : Nat) : Nat := Nat.sub (sm (Nat.succ j)) (sm j)

/-- The node `k` of a row lies in the hole: its row is a hole row and `kl < k < kr`. -/
def skipB (inRow : Bool) (kl kr k : Nat) : Bool := cond inRow (and (Nat.blt kl k) (Nat.blt k kr)) false

/-- The node test of the outer row: in the hole, or `thr ≤ 2 Q`. -/
def nodeOK (thr : SInt) (skip : Bool) (acc : SInt) : Bool :=
  or skip (SInt.ble thr (SInt.mulNat acc 2))

/-- **The outer row**: `outerLoop … n k acc` passes cells `k, …, k + n - 1` with the accumulator `acc`, testing every
node `k, …, k + n`. -/
def outerLoop (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (thr : SInt) (inRow : Bool)
    (kl kr : Nat) : Nat → Nat → SInt → Bool
  | 0, k, acc => nodeOK thr (skipB inRow kl kr k) acc
  | Nat.succ n, k, acc =>
    and (and (nodeOK thr (skipB inRow kl kr k) acc) (Nat.ble (sm k) (sm (Nat.succ k))))
      (match midVal E idx dm sm k with
        | none => false
        | some v => outerLoop E idx dm sm thr inRow kl kr n (Nat.succ k)
            (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ v.v)))

/-- `max 0 (-v)` of a fixed-point value. -/
def negPart (v : Fx 128) : SInt := SInt.max SInt.zero (SInt.neg v.v)

/-- **The negative-part row**: `negLoop … n k acc` ends with the test `acc ≤ thr`. -/
def negLoop (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (thr : SInt) : Nat → Nat → SInt → Bool
  | 0, _, acc => SInt.ble acc thr
  | Nat.succ n, k, acc =>
    and (Nat.ble (sm k) (sm (Nat.succ k)))
      (match midVal E idx dm sm k with
        | none => false
        | some v => negLoop E idx dm sm thr n (Nat.succ k) (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ (negPart v))))

/-- The literal data of the outer grid: `nd + 1` rows `dm 0, …, dm nd` (mantissas of the `d` nodes), `nx` cells of the `s`
partition (`sm`), the cell-index proposals `idx j k`, the hole `jl < j < jr`, `kl < k < kr`, and the threshold. -/
structure OuterGrid where
  /-- The index of the last `d` node. -/
  nd : Nat
  /-- The number of `s` cells. -/
  nx : Nat
  /-- The mantissas of the `d` nodes. -/
  dm : Nat → Nat
  /-- The mantissas of the `s` nodes. -/
  sm : Nat → Nat
  /-- The cell index proposed for the midpoint of cell `k` in row `j`. -/
  idx : Nat → Nat → Nat
  /-- Hole: the open range of rows. -/
  jl : Nat
  /-- Hole: the open range of rows. -/
  jr : Nat
  /-- Hole: the open range of nodes in a hole row. -/
  kl : Nat
  /-- Hole: the open range of nodes in a hole row. -/
  kr : Nat
  /-- The node threshold (units `2^-256`). -/
  thr : SInt

/-- Row `j` is a hole row: `jl < j < jr`. -/
def inRowB (jl jr j : Nat) : Bool := and (Nat.blt jl j) (Nat.blt j jr)

/-- **The check of row `j` of the outer grid** (assertion A8). -/
def OuterGrid.row (G : OuterGrid) (E : EvalData) (j : Nat) : Bool :=
  outerLoop E (G.idx j) (G.dm j) G.sm G.thr (inRowB G.jl G.jr j) G.kl G.kr G.nx 0 SInt.zero

/-- The literal data of the negative-part grid: rows `dm 0, …, dm nd`, `nx` cells (`sm`), the threshold. -/
structure NegGrid where
  /-- The index of the last `d` node. -/
  nd : Nat
  /-- The number of `s` cells. -/
  nx : Nat
  /-- The mantissas of the `d` nodes. -/
  dm : Nat → Nat
  /-- The mantissas of the `s` nodes. -/
  sm : Nat → Nat
  /-- The cell index proposed for the midpoint of cell `k` in row `j`. -/
  idx : Nat → Nat → Nat
  /-- The row threshold (units `2^-256`). -/
  thr : SInt

/-- **The check of row `j` of the negative-part grid** (assertion A9). -/
def NegGrid.row (G : NegGrid) (E : EvalData) (j : Nat) : Bool :=
  negLoop E (G.idx j) (G.dm j) G.sm G.thr G.nx 0 SInt.zero

end SandierSerfaty.Certificate.Box
