/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.Eval
public import SandierSerfaty.Certificate.Arith.Fx

/-!
# Query cells: Taylor data of a table cell and the check tying it to the table

The hot loop of the certificate (value-`G` queries) reads the radial table through `QCell`s: for a
cell `[a, b]` of the table with node intervals `v ∋ a`, `u ∋ b`, cell tuple `ct` and node tuple `nt` at `b`
(`SandierSerfaty.Certificate.Table`), a `QCell` stores the dyadic numbers

* `lo ≤ hi`, the range of `t` the cell is used for (it must lie inside `[a, b]`),
* `tb ≈ b`, `fb ≈ f̃₀(b)`, `f1 ≈ f̃₀'(b)`, `eb ≈ ẽ(b)`, `e1 ≈ ẽ'(b)`,

so that `f̃₀(t) ≈ fb + f1 (t - tb)` and `ẽ(t) ≈ eb + e1 (t - tb)` on `[lo, hi]` with radii `rf`, `re`
(`Certificate.Query.CellSound`: `cellCheck_sound`).

`chanCheck` is the check of one channel `(f̃₀` or `ẽ)`: every comparison is an exact integer test on the scaled
endpoints (`2^128`-scaled), and the radius is the sum of the four terms of the proof
(`M (b - t)²/2 + w(n₀) + w(n₁)|t - b| + |f1| w(u)`, with `M = sup |F''|` from `ct`, `n₀, n₁` the node enclosures
of the value and the derivative at `b`, `w` the widths), compared with the literal `r` in one Nat inequality.
The kernel rules of `Arith.SInt` are followed (this module has no Mathlib import); `cellCheck` reads literals only.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Basis

/-- The Taylor data of a table cell, `2^-128`-dyadic numbers. -/
structure QCell where
  /-- The lower end of the range of `t` served by the cell. -/
  lo : Fx 128
  /-- The upper end of the range of `t` served by the cell. -/
  hi : Fx 128
  /-- The expansion point, a dyadic approximation of the right node `b`. -/
  tb : Fx 128
  /-- A dyadic approximation of `f̃₀(b)`. -/
  fb : Fx 128
  /-- A dyadic approximation of `f̃₀'(b)`. -/
  f1 : Fx 128
  /-- A dyadic approximation of `ẽ(b)`. -/
  eb : Fx 128
  /-- A dyadic approximation of `ẽ'(b)`. -/
  e1 : Fx 128
deriving Inhabited, Repr

/-- The magnitude of the difference of two scaled endpoints (`b - a` when `a ≤ b`). -/
def span (b a : SInt) : Nat := (SInt.sub b a).mag

/-- The numerator (over `2·2^(3·128)`) of the radius of one channel:
`M h² + 2 w₀ N² + 2 w₁ h N + 2 |f1| w_u N` with `M = magHi c2`, `h = u.hi - v.lo`, `N = 2^128`. -/
def chanErr (v u c2 n0 n1 : IV 128) (f1 : Fx 128) : Nat :=
  Nat.add
    (Nat.add (Nat.mul (magHi c2) (Nat.mul (span u.hi v.lo) (span u.hi v.lo)))
      (Nat.mul 2 (Nat.mul (span n0.hi n0.lo) (Nat.shiftLeft 1 256))))
    (Nat.add (Nat.mul 2 (Nat.mul (span n1.hi n1.lo) (Nat.mul (span u.hi v.lo) (Nat.shiftLeft 1 128))))
      (Nat.mul 2 (Nat.mul f1.v.mag (Nat.mul (span u.hi u.lo) (Nat.shiftLeft 1 128)))))

/-- **The check of one channel**: `v.hi ≤ lo`, `hi ≤ u.lo`, `tb ∈ u`, the node values `fb ∈ n0`, `f1 ∈ n1`, and
the radius `chanErr ≤ 2 r N²` (`r` the literal radius scaled by `N = 2^128`). -/
def chanCheck (v u c2 n0 n1 : IV 128) (lo hi tb fb f1 : Fx 128) (r : Nat) : Bool :=
  and (SInt.ble v.hi lo.v)
    (and (SInt.ble hi.v u.lo)
      (and (and (SInt.ble u.lo tb.v) (SInt.ble tb.v u.hi))
        (and (and (SInt.ble n0.lo fb.v) (SInt.ble fb.v n0.hi))
          (and (and (SInt.ble n1.lo f1.v) (SInt.ble f1.v n1.hi))
            (Nat.ble (chanErr v u c2 n0 n1 f1) (Nat.mul 2 (Nat.mul r (Nat.shiftLeft 1 256))))))))

/-- The magnitude caps: `|fb|, |eb| ≤ 2^8`, `|f1|, |e1| ≤ 2^20`, `|tb| ≤ 1`. -/
def capsOK (c : QCell) : Bool :=
  and (and (Nat.ble c.fb.v.mag (Nat.shiftLeft 1 136)) (Nat.ble c.eb.v.mag (Nat.shiftLeft 1 136)))
    (and (and (Nat.ble c.f1.v.mag (Nat.shiftLeft 1 148)) (Nat.ble c.e1.v.mag (Nat.shiftLeft 1 148)))
      (Nat.ble c.tb.v.mag (Nat.shiftLeft 1 128)))

/-- **The check of a cell**: the cell data `c` approximate `f̃₀` (radius `rf/N`) and `ẽ` (radius `re/N`) on
`[c.lo, c.hi] ⊆ [a, b]`, for nodes `a ∈ v`, `b ∈ u` with the stored tuples `ct` (cell) and `nt` (node `b`). -/
def cellCheck (v u : IV 128) (ct nt : Tup) (c : QCell) (rf re : Nat) : Bool :=
  and (chanCheck v u ct.f2 nt.f0 nt.f1 c.lo c.hi c.tb c.fb c.f1 rf)
    (and (chanCheck v u ct.e2 nt.e0 nt.e1 c.lo c.hi c.tb c.eb c.e1 re) (capsOK c))

end SandierSerfaty.Certificate.Query
