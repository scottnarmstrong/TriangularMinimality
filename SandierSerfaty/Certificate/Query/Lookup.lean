/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.Eval

/-!
# The interval lookup in the table

`ITable` is the stored radial table as seen by the interval queries (derivative-`G`, the quadratures of `λ`):
`n` cells, the node intervals `node 0, …, node n` (`node i` encloses the real node `a_i`), and the cell tuples
`cell i` enclosing `(f̃₀, f̃₀', f̃₀'', ẽ, ẽ', ẽ'')` on the real cell `[a_i, a_{i+1}]`
(`SandierSerfaty.Certificate.Table`).

`lookup T X` is the hull of the cell tuples whose outward range `[node_i.lo, node_{i+1}.hi]` meets the query
interval `X` (the C++ `lookup`, paper §7.2); it fails (`none`) if no cell meets `X`. It scans every cell
(correct without any proof about the position of `X`; the hot loop's checked-index lookup is
`Query.FxG`). Soundness: `SandierSerfaty.Certificate.Query.LookupSound`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table

/-- The table of cells for interval queries. -/
structure ITable where
  /-- The number of cells. -/
  n : Nat
  /-- The node intervals `0, …, n`. -/
  node : Nat → IV 128
  /-- The cell tuples `0, …, n - 1`. -/
  cell : Nat → Tup

/-- The componentwise hull of two tuples. -/
def hullTup (a b : Tup) : Tup :=
  ⟨IV.hull a.f0 b.f0, IV.hull a.f1 b.f1, IV.hull a.f2 b.f2, IV.hull a.e0 b.e0, IV.hull a.e1 b.e1,
    IV.hull a.e2 b.e2⟩

/-- The outward range `[v.lo, u.hi]` of the cell between the nodes `v`, `u` meets `X`. -/
def meets (v u X : IV 128) : Bool := and (SInt.ble v.lo X.hi) (SInt.ble X.lo u.hi)

/-- Adds the tuple of cell `k` to the accumulator if the cell meets `X`. -/
def addCell (T : ITable) (X : IV 128) (k : Nat) (acc : Option Tup) : Option Tup :=
  cond (meets (T.node k) (T.node (Nat.succ k)) X)
    (some (match acc with
      | none => T.cell k
      | some a => hullTup a (T.cell k)))
    acc

/-- The hull of the tuples of the cells `0, …, k - 1` that meet `X`, joined with `acc`. -/
def lookupFrom (T : ITable) (X : IV 128) : Nat → Option Tup → Option Tup
  | 0, acc => acc
  | Nat.succ k, acc => lookupFrom T X k (addCell T X k acc)

/-- **The interval lookup**: the hull of the tuples of the cells meeting `X`. -/
def lookup (T : ITable) (X : IV 128) : Option Tup := lookupFrom T X T.n none

end SandierSerfaty.Certificate.Query
