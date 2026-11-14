/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Idx.O00
public import SandierSerfaty.CertData.Box.Idx.O01
public import SandierSerfaty.CertData.Box.Idx.O02
public import SandierSerfaty.CertData.Box.Idx.O03
public import SandierSerfaty.CertData.Box.Idx.O04
public import SandierSerfaty.CertData.Box.Idx.O05
public import SandierSerfaty.CertData.Box.Idx.O06
public import SandierSerfaty.CertData.Box.Idx.O07
public import SandierSerfaty.CertData.Box.Idx.O08
public import SandierSerfaty.CertData.Box.Idx.O09
public import SandierSerfaty.CertData.Box.Idx.O10
public import SandierSerfaty.CertData.Box.Idx.O11
public import SandierSerfaty.CertData.Box.Idx.O12
public import SandierSerfaty.CertData.Box.Idx.O13
public import SandierSerfaty.CertData.Box.Idx.O14
public import SandierSerfaty.CertData.Box.Idx.O15
public import SandierSerfaty.CertData.Box.Idx.O16
public import SandierSerfaty.CertData.Box.Idx.O17
public import SandierSerfaty.CertData.Box.Idx.O18
public import SandierSerfaty.CertData.Box.Idx.O19
public import SandierSerfaty.CertData.Box.Idx.O20
public import SandierSerfaty.CertData.Box.Idx.O21
public import SandierSerfaty.CertData.Box.Idx.O22
public import SandierSerfaty.CertData.Box.Idx.O23
public import SandierSerfaty.CertData.Box.Idx.O24
public import SandierSerfaty.CertData.Box.Idx.O25
public import SandierSerfaty.CertData.Box.Idx.O26
public import SandierSerfaty.CertData.Box.Idx.O27
public import SandierSerfaty.CertData.Box.Idx.O28
public import SandierSerfaty.CertData.Box.Idx.O29
public import SandierSerfaty.CertData.Box.Idx.O30
public import SandierSerfaty.CertData.Box.Idx.O31
public import SandierSerfaty.CertData.Box.Idx.O32
public import SandierSerfaty.CertData.Box.Idx.O33
public import SandierSerfaty.CertData.Box.Idx.O34
public import SandierSerfaty.CertData.Box.Idx.O35

/-!
# Cell-index proposals `o` (dispatch, data)

`oIdx j k`: the cell index of the query `k` of row `j`, from the packed row literals.
-/

@[expose] public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

/-- The packed rows, by page. -/
def oRowQ (p i : Nat) : Nat :=
  cond (Nat.blt p 18) (cond (Nat.blt p 9) (cond (Nat.blt p 4) (cond (Nat.blt p 2) (cond (Nat.blt p 1) (
    oRowP0 i) (
    oRowP1 i)) (cond (Nat.blt p 3) (
    oRowP2 i) (
    oRowP3 i))) (cond (Nat.blt p 6) (cond (Nat.blt p 5) (
    oRowP4 i) (
    oRowP5 i)) (cond (Nat.blt p 7) (
    oRowP6 i) (cond (Nat.blt p 8) (
    oRowP7 i) (
    oRowP8 i))))) (cond (Nat.blt p 13) (cond (Nat.blt p 11) (cond (Nat.blt p 10) (
    oRowP9 i) (
    oRowP10 i)) (cond (Nat.blt p 12) (
    oRowP11 i) (
    oRowP12 i))) (cond (Nat.blt p 15) (cond (Nat.blt p 14) (
    oRowP13 i) (
    oRowP14 i)) (cond (Nat.blt p 16) (
    oRowP15 i) (cond (Nat.blt p 17) (
    oRowP16 i) (
    oRowP17 i)))))) (cond (Nat.blt p 27) (cond (Nat.blt p 22) (cond (Nat.blt p 20) (cond (Nat.blt p 19) (
    oRowP18 i) (
    oRowP19 i)) (cond (Nat.blt p 21) (
    oRowP20 i) (
    oRowP21 i))) (cond (Nat.blt p 24) (cond (Nat.blt p 23) (
    oRowP22 i) (
    oRowP23 i)) (cond (Nat.blt p 25) (
    oRowP24 i) (cond (Nat.blt p 26) (
    oRowP25 i) (
    oRowP26 i))))) (cond (Nat.blt p 31) (cond (Nat.blt p 29) (cond (Nat.blt p 28) (
    oRowP27 i) (
    oRowP28 i)) (cond (Nat.blt p 30) (
    oRowP29 i) (
    oRowP30 i))) (cond (Nat.blt p 33) (cond (Nat.blt p 32) (
    oRowP31 i) (
    oRowP32 i)) (cond (Nat.blt p 34) (
    oRowP33 i) (cond (Nat.blt p 35) (
    oRowP34 i) (
    oRowP35 i))))))

/-- The packed row `j`. -/
def oRowAt (j : Nat) : Nat := oRowQ (Nat.div j 48) (Nat.mod j 48)

/-- The cell index proposed for the query `k` of row `j`. -/
def oIdx (j k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (oRowAt j) (Nat.mul 12 k)) 4095

end SandierSerfaty.CertData.Box
