/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.QPage00
public import SandierSerfaty.CertData.Box.QPage01
public import SandierSerfaty.CertData.Box.QPage02
public import SandierSerfaty.CertData.Box.QPage03

/-!
# The query cells (dispatch, data)

The query table `qTbl` of the value queries and the global radii `qRf`, `qRe` (`Query.cellCheck`).
-/

@[expose] public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

/-- The query cells, by block. -/
def qBlk (b k : Nat) : QCell :=
  cond (Nat.blt b 30) (cond (Nat.blt b 15) (cond (Nat.blt b 7) (cond (Nat.blt b 3) (cond (Nat.blt b 1) (
    qcB_0 k) (cond (Nat.blt b 2) (
    qcB_1 k) (
    qcB_2 k))) (cond (Nat.blt b 5) (cond (Nat.blt b 4) (
    qcB_3 k) (
    qcB_4 k)) (cond (Nat.blt b 6) (
    qcB_5 k) (
    qcB_6 k)))) (cond (Nat.blt b 11) (cond (Nat.blt b 9) (cond (Nat.blt b 8) (
    qcB_7 k) (
    qcB_8 k)) (cond (Nat.blt b 10) (
    qcB_9 k) (
    qcB_10 k))) (cond (Nat.blt b 13) (cond (Nat.blt b 12) (
    qcB_11 k) (
    qcB_12 k)) (cond (Nat.blt b 14) (
    qcB_13 k) (
    qcB_14 k))))) (cond (Nat.blt b 22) (cond (Nat.blt b 18) (cond (Nat.blt b 16) (
    qcB_15 k) (cond (Nat.blt b 17) (
    qcB_16 k) (
    qcB_17 k))) (cond (Nat.blt b 20) (cond (Nat.blt b 19) (
    qcB_18 k) (
    qcB_19 k)) (cond (Nat.blt b 21) (
    qcB_20 k) (
    qcB_21 k)))) (cond (Nat.blt b 26) (cond (Nat.blt b 24) (cond (Nat.blt b 23) (
    qcB_22 k) (
    qcB_23 k)) (cond (Nat.blt b 25) (
    qcB_24 k) (
    qcB_25 k))) (cond (Nat.blt b 28) (cond (Nat.blt b 27) (
    qcB_26 k) (
    qcB_27 k)) (cond (Nat.blt b 29) (
    qcB_28 k) (
    qcB_29 k)))))) (cond (Nat.blt b 45) (cond (Nat.blt b 37) (cond (Nat.blt b 33) (cond (Nat.blt b 31) (
    qcB_30 k) (cond (Nat.blt b 32) (
    qcB_31 k) (
    qcB_32 k))) (cond (Nat.blt b 35) (cond (Nat.blt b 34) (
    qcB_33 k) (
    qcB_34 k)) (cond (Nat.blt b 36) (
    qcB_35 k) (
    qcB_36 k)))) (cond (Nat.blt b 41) (cond (Nat.blt b 39) (cond (Nat.blt b 38) (
    qcB_37 k) (
    qcB_38 k)) (cond (Nat.blt b 40) (
    qcB_39 k) (
    qcB_40 k))) (cond (Nat.blt b 43) (cond (Nat.blt b 42) (
    qcB_41 k) (
    qcB_42 k)) (cond (Nat.blt b 44) (
    qcB_43 k) (
    qcB_44 k))))) (cond (Nat.blt b 53) (cond (Nat.blt b 49) (cond (Nat.blt b 47) (cond (Nat.blt b 46) (
    qcB_45 k) (
    qcB_46 k)) (cond (Nat.blt b 48) (
    qcB_47 k) (
    qcB_48 k))) (cond (Nat.blt b 51) (cond (Nat.blt b 50) (
    qcB_49 k) (
    qcB_50 k)) (cond (Nat.blt b 52) (
    qcB_51 k) (
    qcB_52 k)))) (cond (Nat.blt b 57) (cond (Nat.blt b 55) (cond (Nat.blt b 54) (
    qcB_53 k) (
    qcB_54 k)) (cond (Nat.blt b 56) (
    qcB_55 k) (
    qcB_56 k))) (cond (Nat.blt b 59) (cond (Nat.blt b 58) (
    qcB_57 k) (
    qcB_58 k)) (cond (Nat.blt b 60) (
    qcB_59 k) (
    qcB_60 k))))))

/-- The query cell `i`. -/
def qCell (i : Nat) : QCell := qBlk (Nat.div i 64) (Nat.mod i 64)

/-- The query table (one cell per table cell). -/
def qTbl : QTable := ⟨3848, qCell⟩

/-- The radius `rf` of the cells (`f̃₀`). -/
def qRf : Nat := 44708151300033489486905157843813

/-- The radius `re` of the cells (`ẽ`). -/
def qRe : Nat := 209615844054276131172016518662463

end SandierSerfaty.CertData.Box
