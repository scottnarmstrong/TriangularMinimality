/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumDef

/-!
# The nodes of the box grids as closed formulas

The grid nodes of the box assertions (mantissas over `2^128`) follow the C++ `grid_seq` scheme: on a segment
`[a, b]` cut into `m` cells the node `i` is `a + (b - a) i/m`, rounded down (`linNode`); the segment ends are the
literals rounded outward (`ceilLit`, `floorLit`), the `s` nodes of the value grids are even (exact midpoints,
`Box.midVal`). The literal data of the shards are these functions with a few literal parameters (`m₁, m₂, m₃`),
so no node table is stored; the generator builds its grids from the same definitions. Nothing here needs a
proof: the checks of `Box.NumCheck` (`monoB`, `stepB`, the literal comparisons) test the nodes as computed.

* `gridD3 m₁ m₂ m₃`: the `d` nodes of the outer and negative grids, `[b, d_l) ∪ [d_l, d_u) ∪ [d_u, .697]`;
* `gridS3 m₁ m₂ m₃`: the `s` nodes, `[0, s_l) ∪ [s_l, s_u) ∪ [s_u, .65]` (even);
* `a7D m`, `a7S m`: the A7 partitions of `[⌊b⌋, ⌈.697⌉]` and `[0, .65]`;
* `hessD m`, `hessS m₁ m₂`: the Hessian partitions of `[d_l, d_u]` and `[0, s_l) ∪ [s_l, s_u]`;
* `kS X m`: the `s` nodes of the `K` row on `[0, X]` (even).

Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

/-- `⌊2^128 (a + (b - a) i/m)⌋` for `a = an/ad ≤ b = bn/bd`. -/
def linNode (an ad bn bd m i : Nat) : Nat :=
  Nat.div (Nat.mul bigP (Nat.add (Nat.mul (Nat.mul an bd) m) (Nat.mul (Nat.sub (Nat.mul bn ad) (Nat.mul an bd)) i)))
    (Nat.mul (Nat.mul ad bd) m)

/-- `⌈2^128 n/d⌉`. -/
def ceilLit (n d : Nat) : Nat := Nat.div (Nat.add (Nat.mul n bigP) (Nat.sub d 1)) d

/-- `⌊2^128 n/d⌋`. -/
def floorLit (n d : Nat) : Nat := Nat.div (Nat.mul n bigP) d

/-- The even mantissa at or below `x`. -/
def evenDown (x : Nat) : Nat := Nat.sub x (Nat.mod x 2)

/-- The even mantissa at or above `x`. -/
def evenUp (x : Nat) : Nat := Nat.add x (Nat.mod x 2)

/-- The `d` nodes `0, …, m₁ + m₂ + m₃` of the outer and negative grids. -/
def gridD3 (m1 m2 m3 j : Nat) : Nat :=
  cond (Nat.beq j 0) (ceilLit 28209 100000)
    (cond (Nat.blt j m1) (linNode 28209 100000 52528 100000 m1 j)
      (cond (Nat.beq j m1) (ceilLit 52528 100000)
        (cond (Nat.blt j (Nat.add m1 m2)) (linNode 52528 100000 54930 100000 m2 (Nat.sub j m1))
          (cond (Nat.beq j (Nat.add m1 m2)) (floorLit 54930 100000)
            (cond (Nat.blt j (Nat.add (Nat.add m1 m2) m3))
              (linNode 54930 100000 697 1000 m3 (Nat.sub j (Nat.add m1 m2)))
              (ceilLit 697 1000))))))

/-- The `s` nodes `0, …, m₁ + m₂ + m₃` of the outer and negative grids (even mantissas). -/
def gridS3 (m1 m2 m3 k : Nat) : Nat :=
  cond (Nat.beq k 0) 0
    (cond (Nat.blt k m1) (evenDown (linNode 0 1 29420 100000 m1 k))
      (cond (Nat.beq k m1) (evenUp (ceilLit 29420 100000))
        (cond (Nat.blt k (Nat.add m1 m2)) (evenDown (linNode 29420 100000 32621 100000 m2 (Nat.sub k m1)))
          (cond (Nat.beq k (Nat.add m1 m2)) (evenDown (floorLit 32621 100000))
            (cond (Nat.blt k (Nat.add (Nat.add m1 m2) m3))
              (evenDown (linNode 32621 100000 65 100 m3 (Nat.sub k (Nat.add m1 m2))))
              (evenUp (ceilLit 65 100)))))))

/-- The A7 `d` partition `0, …, m` of `[⌊b⌋, ⌈.697⌉]`. -/
def a7D (m j : Nat) : Nat :=
  cond (Nat.beq j 0) (floorLit 28209 100000)
    (cond (Nat.blt j m) (linNode 28209 100000 697 1000 m j) (ceilLit 697 1000))

/-- The A7 `s` partition `0, …, m` of `[0, .65]` (top: the even ceiling, the top of the value grids). -/
def a7S (m k : Nat) : Nat :=
  cond (Nat.beq k 0) 0 (cond (Nat.blt k m) (linNode 0 1 65 100 m k) (evenUp (ceilLit 65 100)))

/-- The Hessian `d` partition `0, …, m` of `[⌊d_l⌋, ⌈d_u⌉]`. -/
def hessD (m j : Nat) : Nat :=
  cond (Nat.beq j 0) (floorLit 52528 100000)
    (cond (Nat.blt j m) (linNode 52528 100000 54930 100000 m j) (ceilLit 54930 100000))

/-- The Hessian `s` partition `0, …, m₁ + m₂` of `[0, s_l) ∪ [⌊s_l⌋, ⌈s_u⌉]`. -/
def hessS (m1 m2 k : Nat) : Nat :=
  cond (Nat.beq k 0) 0
    (cond (Nat.blt k m1) (linNode 0 1 29420 100000 m1 k)
      (cond (Nat.beq k m1) (floorLit 29420 100000)
        (cond (Nat.blt k (Nat.add m1 m2)) (linNode 29420 100000 32621 100000 m2 (Nat.sub k m1))
          (ceilLit 32621 100000))))

/-- The `s` nodes `0, …, m` of the `K` row on `[0, X]` (even). -/
def kS (X m k : Nat) : Nat :=
  cond (Nat.beq k 0) 0 (cond (Nat.blt k m) (evenDown (Nat.div (Nat.mul X k) m)) X)

end SandierSerfaty.Certificate.Box
