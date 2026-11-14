/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.CtxDef

/-!
# The Hessian assertion A10: the interval check (paper `comp:hessian`)

For a `d` cell `D = [dp a, dp (a+1)]` and the `s` partition `sp`, the check of the row `a` runs through the cells
`S_i = [sp i, sp (i+1)]`, `i = 0, 1, …`, with the accumulator `acc_i = ∑_{i' < i} |S_{i'}| · F₁(D, S_{i'})`
(`F₁ ⊇ G_dd` on `D × S_{i'}`, `gddOf`), starting from `0` (the accumulation in `s` begins at zero) and, for the cells
`i ≥ jmin` (above the node `sp jmin`, the lower end of `𝒟₀`), tests

  `inf A_i > 0`, `inf C_i > 0`, `inf (A_i C_i - B_i²) > 0`,

with `A_i = acc_i + [0, |S_i|] F₁(D, S_i)`, `B_i = F₂ = G_d` (`gdOf`), `C_i = F₃ = G_s` (`gsOf`)
(`comp:hessian-entries`, `comp:hessian-assertions`). Every cell is a successful `mkDCtx2`; the partitions are
monotone. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Table SandierSerfaty.Certificate.Query

/-- The literal data of the Hessian assertion: the table (interval form), the enclosures of the constants, the
partitions `dp` (`nd` cells) and `sp` (`nx` cells) of the `d` and `s` axes (mantissas, scaled by `2^128`) and the
first tested `s` cell `jmin`. -/
structure HessData where
  /-- The table of cells. -/
  T : ITable
  /-- An enclosure of `f₀(l)`. -/
  f0lI : IV 128
  /-- An enclosure of `-π B(l)`. -/
  k0I : IV 128
  /-- An enclosure of `l²`. -/
  lsqI : IV 128
  /-- An enclosure of `l`. -/
  lI : IV 128
  /-- An enclosure of `λ`. -/
  lamI : IV 128
  /-- An enclosure of `μ`. -/
  muI : IV 128
  /-- The widening of the table cells (`≥ 10⁻¹¹ 2^128`). -/
  rad : Nat
  /-- The number of `d` cells. -/
  nd : Nat
  /-- The number of `s` cells. -/
  nx : Nat
  /-- The first `s` cell at which the Hessian is tested. -/
  jmin : Nat
  /-- The mantissas of the `d` partition. -/
  dp : Nat → Nat
  /-- The mantissas of the `s` partition. -/
  sp : Nat → Nat

/-- The three interval tests of `comp:hessian-assertions`. -/
def hessTest (A B C : IV 128) : Bool :=
  and (IV.posB A) (and (IV.posB C) (IV.posB (IV.sub (IV.mul A C) (IV.sq B))))

/-- The context of the rectangle `D_a × S_i`. -/
def HessData.ctx (H : HessData) (a i : Nat) : Option DCtx2 :=
  mkDCtx2 H.T H.f0lI H.k0I H.lsqI H.lI H.lamI H.muI H.rad
    (IV.ofNatPair (H.dp a) (H.dp (Nat.succ a))) (IV.ofNatPair (H.sp i) (H.sp (Nat.succ i)))

/-- The width (mantissa) of the `s` cell `i`. -/
def widthN (sp : Nat → Nat) (i : Nat) : Nat := Nat.sub (sp (Nat.succ i)) (sp i)

/-- The cells `i, …, i + n - 1` of the row `a`, with the accumulator `acc`, for a function `ctxf a i` giving the context
of the rectangle `D_a × S_i` (the scanning `H.ctx`, or the checked-index `H.ctxI ix`). -/
def HessData.rowAuxG (H : HessData) (ctxf : Nat → Nat → Option DCtx2) (a : Nat) : Nat → Nat → IV 128 → Bool
  | 0, _, _ => true
  | Nat.succ n, i, acc =>
    match ctxf a i with
    | none => false
    | some c =>
      and (and (Nat.ble (H.sp i) (H.sp (Nat.succ i)))
          (or (Nat.blt i H.jmin)
            (hessTest (IV.add acc (IV.mul (IV.ofNatPair 0 (widthN H.sp i)) (gddOf c))) (gdOf c.toDCtx)
              (gsOf c.toDCtx))))
        (H.rowAuxG ctxf a n (Nat.succ i)
          (IV.add acc (IV.mul (IV.ofNatPair (widthN H.sp i) (widthN H.sp i)) (gddOf c))))

/-- **The check of the row `a`** (the `d` cell `D_a` against all `s` cells), for the context function `ctxf`. -/
def HessData.rowG (H : HessData) (ctxf : Nat → Nat → Option DCtx2) (a : Nat) : Bool :=
  and (Nat.ble (H.dp a) (H.dp (Nat.succ a))) (H.rowAuxG ctxf a H.nx 0 (IV.ofNatPair 0 0))

/-- The rows `0, …, n - 1`, for the context function `ctxf`. -/
def HessData.rowsG (H : HessData) (ctxf : Nat → Nat → Option DCtx2) : Nat → Bool
  | 0 => true
  | Nat.succ n => and (H.rowsG ctxf n) (H.rowG ctxf n)

/-- **The check of the row `a`** (the `d` cell `D_a` against all `s` cells; scanning lookup). -/
def HessData.row (H : HessData) (a : Nat) : Bool := H.rowG H.ctx a

/-- The rows `0, …, n - 1` (scanning lookup). -/
def HessData.rows (H : HessData) (n : Nat) : Bool := H.rowsG H.ctx n

end SandierSerfaty.Certificate.Box
