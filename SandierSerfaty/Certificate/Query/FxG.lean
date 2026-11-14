/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Cell

/-!
# The value-`G` query of the hot loop (midpoint fixed point `Fx`)

`G(d, s) = d f(t)/t² - s² e(t)/(d t²)` with `t = √(d² + s²)` and `f = f₀ - λ t²/2 - μ`
(`Calibration.G`). The evaluator `evalG` works in
`Fx 128` (no intervals: one proved error bound for every query):

1. `T2 = d·d + s·s` (each product truncated), `t̂ = ⌊√T2 · 2^128⌋ / 2^128` proposed by `Fx.sqrtProposal` and
   *checked* by `Fx.sqrtCheck` (squaring);
2. the cell `i` is *proposed by the caller* (the shard supplies the index) and checked: `i < n` and
   `lo + 16 ulp ≤ t̂ ≤ hi - 16 ulp`;
3. `f̃ = fb + f1 (t̂ - tb)` and `ẽ = eb + e1 (t̂ - tb)` (the Taylor data of `Query.Cell`), `fa = f̃ - λ̂ T2/2 - μ̂`;
4. `V = (d·fa - (s·s/d)·ẽ) / T2`.

`evalG T lam mu i d s = some v` only when both checks pass; the error theorem
(`SandierSerfaty.Certificate.Query.FxGSound.evalG_sound`) bounds `|v - G d s|` by one number `deltaG`
depending only on the table's cell radii and the radii of `λ̂, μ̂`. Kernel rules: strict (Nat primitives,
`cond`, no `let`).
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith

/-- The table of query cells (`n` cells; `cell i` is read by the shard through a literal tree). -/
structure QTable where
  /-- The number of cells. -/
  n : Nat
  /-- The Taylor data of cell `i`. -/
  cell : Nat → QCell

/-- Sixteen units in the last place, the lookup margin. -/
def margin : Fx 128 := ⟨⟨false, 16⟩⟩

/-- `lo + 16 ulp ≤ t` and `t + 16 ulp ≤ hi`. -/
def inRange (c : QCell) (t : Fx 128) : Bool :=
  and (Fx.ble (Fx.add c.lo margin) t) (Fx.ble (Fx.add t margin) c.hi)

/-- The first-order Taylor value `b + f1 (t - tb)`. -/
def taylorVal (b f1 tb t : Fx 128) : Fx 128 := Fx.add b (Fx.mul f1 (Fx.sub t tb))

/-- `fa = fv - λ̂ T2/2 - μ̂` (the adjusted radial function at `T2 ≈ t²`). -/
def adjustF (lam mu T2 fv : Fx 128) : Fx 128 :=
  Fx.sub (Fx.sub fv (Fx.divPow2 (Fx.mul lam T2) 1)) mu

/-- `V = (d·fa - (ss/d)·ev) / T2`. -/
def combG (d ss T2 fa ev : Fx 128) : Fx 128 :=
  Fx.div (Fx.sub (Fx.mul d fa) (Fx.mul (Fx.div ss d) ev)) T2

/-- The evaluation of `G` in a cell, at the checked square root `t`. -/
def evalCell (c : QCell) (lam mu d ss T2 t : Fx 128) : Fx 128 :=
  combG d ss T2 (adjustF lam mu T2 (taylorVal c.fb c.f1 c.tb t)) (taylorVal c.eb c.e1 c.tb t)

/-- The cell and range checks, at the checked square root `t`. -/
def evalAt (T : QTable) (lam mu : Fx 128) (i : Nat) (d ss T2 t : Fx 128) : Option (Fx 128) :=
  cond (Nat.blt i T.n) (cond (inRange (T.cell i) t) (some (evalCell (T.cell i) lam mu d ss T2 t)) none) none

/-- The square-root check on `T2`, then `evalAt`. -/
def evalWith (T : QTable) (lam mu : Fx 128) (i : Nat) (d ss T2 : Fx 128) (s : Nat) : Option (Fx 128) :=
  cond (Fx.sqrtCheck T2 s) (evalAt T lam mu i d ss T2 (Fx.ofSInt ⟨false, s⟩)) none

/-- `evalWith` with the proposed square root. -/
def evalG1 (T : QTable) (lam mu : Fx 128) (i : Nat) (d ss T2 : Fx 128) : Option (Fx 128) :=
  evalWith T lam mu i d ss T2 (Fx.sqrtProposal T2)

/-- `evalG1` with `T2 = d·d + ss`. -/
def evalG0 (T : QTable) (lam mu : Fx 128) (i : Nat) (d ss dd : Fx 128) : Option (Fx 128) :=
  evalG1 T lam mu i d ss (Fx.add dd ss)

/-- **The value-`G` query** at the dyadic point `(d, s)`, in the cell `i`: `some v` if the square root and the
cell checks pass, with `v` within `deltaG` of `G d s` (`FxGSound.evalG_sound`). -/
def evalG (T : QTable) (lam mu : Fx 128) (i : Nat) (d s : Fx 128) : Option (Fx 128) :=
  evalG0 T lam mu i d (Fx.mul s s) (Fx.mul d d)

end SandierSerfaty.Certificate.Query
