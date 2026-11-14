/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Eval

/-!
# The row check enclosing the constant `K = 2 g_p(x₀)` from above (paper `comp:K-quadrature`)

`sumLoop` is the pass of `negLoop` with the accumulator `Q = ∑ (σ_{j+1} - σ_j) v_j` of the plain values (not of
their negative parts) and the final test `Q ≤ thr` (units `2^-256`): one row at a dyadic `d` near `p` over a
partition `sm` of `[0, X]`, `X ≥ x₀`, bounds `g_d(X)`, hence `K = 2 g_p(x₀)`, from above
(`Box.KBound`). Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Query

/-- **The sum row**: `sumLoop … n k acc` passes the cells `k, …, k + n - 1`, ending with the test `acc ≤ thr`. -/
def sumLoop (E : EvalData) (idx : Nat → Nat) (dm : Nat) (sm : Nat → Nat) (thr : SInt) : Nat → Nat → SInt → Bool
  | 0, _, acc => SInt.ble acc thr
  | Nat.succ n, k, acc =>
    and (Nat.ble (sm k) (sm (Nat.succ k)))
      (match midVal E idx dm sm k with
        | none => false
        | some v => sumLoop E idx dm sm thr n (Nat.succ k) (SInt.add acc (SInt.mul ⟨false, widthM sm k⟩ v.v)))

/-- The literal data of the `K` row: the `d` node `dm`, `nx` cells (`sm`), the cell indices `idx`, the threshold. -/
structure KGrid where
  /-- The number of `s` cells. -/
  nx : Nat
  /-- The mantissa of the `d` node. -/
  dm : Nat
  /-- The mantissas of the `s` nodes. -/
  sm : Nat → Nat
  /-- The proposed cell indices. -/
  idx : Nat → Nat
  /-- The threshold (units `2^-256`). -/
  thr : SInt

/-- **The check of the `K` row.** -/
def KGrid.row (G : KGrid) (E : EvalData) : Bool := sumLoop E G.idx G.dm G.sm G.thr G.nx 0 SInt.zero

end SandierSerfaty.Certificate.Box
