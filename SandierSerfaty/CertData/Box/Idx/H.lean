/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Idx.H00
public import SandierSerfaty.CertData.Box.Idx.H01
public import SandierSerfaty.CertData.Box.Idx.H02
public import SandierSerfaty.CertData.Box.Idx.H03

/-!
# Index-range proposals `h` (dispatch, data)

`hIx j k`: the index range of the query `k` of row `j` (checked-index lookup), from the packed row literals.
-/

@[expose] public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

/-- The packed rows, by page. -/
def hRowQ (p i : Nat) : Nat :=
  cond (Nat.blt p 2) (cond (Nat.blt p 1) (
    hRowP0 i) (
    hRowP1 i)) (cond (Nat.blt p 3) (
    hRowP2 i) (
    hRowP3 i))

/-- The packed row `j`. -/
def hRowAt (j : Nat) : Nat := hRowQ (Nat.div j 48) (Nat.mod j 48)

/-- The index range proposed for the query `k` of row `j`. -/
def hIx (j k : Nat) : Nat × Nat :=
  (Nat.land (Nat.shiftRight (hRowAt j) (Nat.mul 24 k)) 4095,
    Nat.land (Nat.shiftRight (hRowAt j) (Nat.add (Nat.mul 24 k) 12)) 4095)

end SandierSerfaty.CertData.Box
