/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.NumDef
public import SandierSerfaty.Certificate.Box.CtxDef
public import SandierSerfaty.Certificate.Box.HessDef
public import SandierSerfaty.Certificate.Box.KRowDef

/-!
# The numeric side conditions of the five assertions as Booleans

`numFree` collects the free parameters of the assertions (all rationals with denominator `2^128`, given as `Nat`
numerators, except the budget `δ` and the threshold `Kc`, which are kept in `ℚ` by `NumScalar`). Each assertion has a
flat list of `Nat` checks (`andL`), soundness in `NumGoal`:

* `a7B`: the A7 rectangles cover the boxes (`hnj`, `hnk`, `hdp0`, `hsp0`, `hrows7`) and reach `.697`, `.65`;
* `outerGridB`: the outer grid (`hOdpn` … `hOrows`);
* `negGridB`: the negative-part grid (`hNdpn` … `hNrows`);
* `kRowB`: the `K` row, its node ranges and the closeness to `p` and `x₀` (`hKrow` … `hρx3`);
* `hessB`: the Hessian rows (`hnd` … `hx_hi`).
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

/-- The free `Nat` parameters (numerators over `2^128`): the steps `Sh, Dh` of the outer grid and `Sh', Dh'` of the
negative grid, the offset `ρ`, the step `ShK` of the `K` row and the radii `ρd, ρx`. -/
structure NumFree where
  /-- The outer `s` step. -/
  oSh : Nat
  /-- The outer `d` step. -/
  oDh : Nat
  /-- The outer offset `ρ` of the first `d` node from `b`. -/
  oRho : Nat
  /-- The negative-part `s` step. -/
  nSh : Nat
  /-- The negative-part `d` step. -/
  nDh : Nat
  /-- The `s` step of the `K` row. -/
  kSh : Nat
  /-- The radius `ρd` (closeness of the `K` row node to `p`). -/
  kRd : Nat
  /-- The radius `ρx` (closeness of the top node to `x₀`). -/
  kRx : Nat

/-- The A7 rectangles cover the boxes and reach `d = .697`, `s = .65`. -/
def a7B (A : A7Data) : Bool :=
  andL [Nat.blt 0 A.nj, Nat.blt 0 A.nk, leLitB (A.dp 0) 28209 100000, Nat.beq (A.sp 0) 0,
    allLt (fun j => A.row j A.nk) A.nj, geLitB (A.dp A.nj) 697 1000, geLitB (A.sp A.nk) 65 100]

/-- The outer grid (the hole `[jl, jr] × [kl, kr]` inside `𝒟₀`). -/
def outerGridB (A : A7Data) (G : OuterGrid) (E : EvalData) (par : NumFree) : Bool :=
  andL [Nat.ble (G.dm G.nd) (A.dp A.nj), Nat.ble (G.sm G.nx) (A.sp A.nk), monoB G.dm G.nd,
    geLitB (G.dm 0) 28209 100000, subLeB (G.dm 0) 28209 100000 par.oRho, stepB G.dm G.nd par.oDh,
    geLitB (G.dm G.nd) 697 1000, Nat.ble (G.dm G.nd) bigP, Nat.beq (G.sm 0) 0, monoB G.sm G.nx,
    stepB G.sm G.nx par.oSh, geLitB (G.sm G.nx) 65 100, Nat.blt 0 G.jl, Nat.ble G.jl G.nd, Nat.blt G.jr G.nd,
    Nat.blt 0 G.kl, Nat.ble G.kl G.nx, Nat.blt G.kr G.nx, geLitB (G.dm G.jl) 52528 100000,
    leLitB (G.dm G.jr) 54930 100000, geLitB (G.sm G.kl) 29420 100000, leLitB (G.sm G.kr) 32621 100000,
    allLt (fun j => G.row E j) (Nat.succ G.nd)]

/-- The negative-part grid. -/
def negGridB (A : A7Data) (G : NegGrid) (E : EvalData) (par : NumFree) : Bool :=
  andL [Nat.ble (G.dm G.nd) (A.dp A.nj), Nat.ble (G.sm G.nx) (A.sp A.nk), monoB G.dm G.nd,
    geLitB (G.dm 0) 28209 100000, nearB (G.dm 0) 28209 100000 par.nDh, stepB G.dm G.nd par.nDh,
    geLitB (G.dm G.nd) 697 1000, Nat.ble (G.dm G.nd) bigP, Nat.beq (G.sm 0) 0, monoB G.sm G.nx,
    stepB G.sm G.nx par.nSh, geLitB (G.sm G.nx) 65 100, allLt (fun j => G.row E j) (Nat.succ G.nd)]

/-- The `K` row: node ranges and the closeness of the node `dm` to `p` and of the top node to `x₀`. -/
def kRowB (G : KGrid) (E : EvalData) (par : NumFree) : Bool :=
  andL [G.row E, geLitB G.dm 28209 100000, leLitB G.dm 697 1000, Nat.beq (G.sm 0) 0,
    leLitB (G.sm G.nx) 65 100, stepB G.sm G.nx par.kSh, closeLoB G.dm par.kRd 12, closeHiB G.dm par.kRd 12,
    closeLoB (G.sm G.nx) par.kRx 108, closeHiB (G.sm G.nx) 0 108]

/-- The Hessian rows. -/
def hessB (H : HessData) : Bool :=
  andL [Nat.blt 0 H.nd, Nat.blt H.jmin H.nx, geLitB (H.dp 0) 28209 100000, Nat.beq (H.sp 0) 0, H.rows H.nd,
    leLitB (H.dp 0) 52528 100000, geLitB (H.dp H.nd) 54930 100000, leLitB (H.sp H.jmin) 29420 100000,
    geLitB (H.sp H.nx) 32621 100000]

end SandierSerfaty.Certificate.Box
