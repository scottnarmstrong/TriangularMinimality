/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 5 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `20`–`23`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_20_0 : allFrom (a7Dat.rectI aIx 20) 0 8 = true := by
  decide +kernel

theorem a7_20_8 : allFrom (a7Dat.rectI aIx 20) 8 8 = true := by
  decide +kernel

theorem a7_20_16 : allFrom (a7Dat.rectI aIx 20) 16 8 = true := by
  decide +kernel

theorem a7_20_24 : allFrom (a7Dat.rectI aIx 20) 24 8 = true := by
  decide +kernel

theorem a7_20_32 : allFrom (a7Dat.rectI aIx 20) 32 8 = true := by
  decide +kernel

theorem a7_20_40 : allFrom (a7Dat.rectI aIx 20) 40 8 = true := by
  decide +kernel

theorem a7_20_48 : allFrom (a7Dat.rectI aIx 20) 48 8 = true := by
  decide +kernel

theorem a7_20_56 : allFrom (a7Dat.rectI aIx 20) 56 8 = true := by
  decide +kernel

theorem a7_20_64 : allFrom (a7Dat.rectI aIx 20) 64 8 = true := by
  decide +kernel

theorem a7_20_72 : allFrom (a7Dat.rectI aIx 20) 72 8 = true := by
  decide +kernel

theorem a7_20_80 : allFrom (a7Dat.rectI aIx 20) 80 8 = true := by
  decide +kernel

theorem a7_20_88 : allFrom (a7Dat.rectI aIx 20) 88 8 = true := by
  decide +kernel

theorem a7_20_96 : allFrom (a7Dat.rectI aIx 20) 96 8 = true := by
  decide +kernel

theorem a7_20_104 : allFrom (a7Dat.rectI aIx 20) 104 8 = true := by
  decide +kernel

theorem a7_20_112 : allFrom (a7Dat.rectI aIx 20) 112 8 = true := by
  decide +kernel

theorem a7_20_120 : allFrom (a7Dat.rectI aIx 20) 120 8 = true := by
  decide +kernel

theorem a7_20_128 : allFrom (a7Dat.rectI aIx 20) 128 8 = true := by
  decide +kernel

theorem a7_row_20 : a7Dat.rowI aIx 20 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 20 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 20) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 20) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 20)) a7_20_0) a7_20_8) a7_20_16) a7_20_24) a7_20_32) a7_20_40) a7_20_48) a7_20_56) a7_20_64) a7_20_72) a7_20_80) a7_20_88) a7_20_96) a7_20_104) a7_20_112) a7_20_120) a7_20_128)

theorem a7_21_0 : allFrom (a7Dat.rectI aIx 21) 0 8 = true := by
  decide +kernel

theorem a7_21_8 : allFrom (a7Dat.rectI aIx 21) 8 8 = true := by
  decide +kernel

theorem a7_21_16 : allFrom (a7Dat.rectI aIx 21) 16 8 = true := by
  decide +kernel

theorem a7_21_24 : allFrom (a7Dat.rectI aIx 21) 24 8 = true := by
  decide +kernel

theorem a7_21_32 : allFrom (a7Dat.rectI aIx 21) 32 8 = true := by
  decide +kernel

theorem a7_21_40 : allFrom (a7Dat.rectI aIx 21) 40 8 = true := by
  decide +kernel

theorem a7_21_48 : allFrom (a7Dat.rectI aIx 21) 48 8 = true := by
  decide +kernel

theorem a7_21_56 : allFrom (a7Dat.rectI aIx 21) 56 8 = true := by
  decide +kernel

theorem a7_21_64 : allFrom (a7Dat.rectI aIx 21) 64 8 = true := by
  decide +kernel

theorem a7_21_72 : allFrom (a7Dat.rectI aIx 21) 72 8 = true := by
  decide +kernel

theorem a7_21_80 : allFrom (a7Dat.rectI aIx 21) 80 8 = true := by
  decide +kernel

theorem a7_21_88 : allFrom (a7Dat.rectI aIx 21) 88 8 = true := by
  decide +kernel

theorem a7_21_96 : allFrom (a7Dat.rectI aIx 21) 96 8 = true := by
  decide +kernel

theorem a7_21_104 : allFrom (a7Dat.rectI aIx 21) 104 8 = true := by
  decide +kernel

theorem a7_21_112 : allFrom (a7Dat.rectI aIx 21) 112 8 = true := by
  decide +kernel

theorem a7_21_120 : allFrom (a7Dat.rectI aIx 21) 120 8 = true := by
  decide +kernel

theorem a7_21_128 : allFrom (a7Dat.rectI aIx 21) 128 8 = true := by
  decide +kernel

theorem a7_row_21 : a7Dat.rowI aIx 21 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 21 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 21) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 21) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 21)) a7_21_0) a7_21_8) a7_21_16) a7_21_24) a7_21_32) a7_21_40) a7_21_48) a7_21_56) a7_21_64) a7_21_72) a7_21_80) a7_21_88) a7_21_96) a7_21_104) a7_21_112) a7_21_120) a7_21_128)

theorem a7_22_0 : allFrom (a7Dat.rectI aIx 22) 0 8 = true := by
  decide +kernel

theorem a7_22_8 : allFrom (a7Dat.rectI aIx 22) 8 8 = true := by
  decide +kernel

theorem a7_22_16 : allFrom (a7Dat.rectI aIx 22) 16 8 = true := by
  decide +kernel

theorem a7_22_24 : allFrom (a7Dat.rectI aIx 22) 24 8 = true := by
  decide +kernel

theorem a7_22_32 : allFrom (a7Dat.rectI aIx 22) 32 8 = true := by
  decide +kernel

theorem a7_22_40 : allFrom (a7Dat.rectI aIx 22) 40 8 = true := by
  decide +kernel

theorem a7_22_48 : allFrom (a7Dat.rectI aIx 22) 48 8 = true := by
  decide +kernel

theorem a7_22_56 : allFrom (a7Dat.rectI aIx 22) 56 8 = true := by
  decide +kernel

theorem a7_22_64 : allFrom (a7Dat.rectI aIx 22) 64 8 = true := by
  decide +kernel

theorem a7_22_72 : allFrom (a7Dat.rectI aIx 22) 72 8 = true := by
  decide +kernel

theorem a7_22_80 : allFrom (a7Dat.rectI aIx 22) 80 8 = true := by
  decide +kernel

theorem a7_22_88 : allFrom (a7Dat.rectI aIx 22) 88 8 = true := by
  decide +kernel

theorem a7_22_96 : allFrom (a7Dat.rectI aIx 22) 96 8 = true := by
  decide +kernel

theorem a7_22_104 : allFrom (a7Dat.rectI aIx 22) 104 8 = true := by
  decide +kernel

theorem a7_22_112 : allFrom (a7Dat.rectI aIx 22) 112 8 = true := by
  decide +kernel

theorem a7_22_120 : allFrom (a7Dat.rectI aIx 22) 120 8 = true := by
  decide +kernel

theorem a7_22_128 : allFrom (a7Dat.rectI aIx 22) 128 8 = true := by
  decide +kernel

theorem a7_row_22 : a7Dat.rowI aIx 22 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 22 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 22) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 22) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 22)) a7_22_0) a7_22_8) a7_22_16) a7_22_24) a7_22_32) a7_22_40) a7_22_48) a7_22_56) a7_22_64) a7_22_72) a7_22_80) a7_22_88) a7_22_96) a7_22_104) a7_22_112) a7_22_120) a7_22_128)

theorem a7_23_0 : allFrom (a7Dat.rectI aIx 23) 0 8 = true := by
  decide +kernel

theorem a7_23_8 : allFrom (a7Dat.rectI aIx 23) 8 8 = true := by
  decide +kernel

theorem a7_23_16 : allFrom (a7Dat.rectI aIx 23) 16 8 = true := by
  decide +kernel

theorem a7_23_24 : allFrom (a7Dat.rectI aIx 23) 24 8 = true := by
  decide +kernel

theorem a7_23_32 : allFrom (a7Dat.rectI aIx 23) 32 8 = true := by
  decide +kernel

theorem a7_23_40 : allFrom (a7Dat.rectI aIx 23) 40 8 = true := by
  decide +kernel

theorem a7_23_48 : allFrom (a7Dat.rectI aIx 23) 48 8 = true := by
  decide +kernel

theorem a7_23_56 : allFrom (a7Dat.rectI aIx 23) 56 8 = true := by
  decide +kernel

theorem a7_23_64 : allFrom (a7Dat.rectI aIx 23) 64 8 = true := by
  decide +kernel

theorem a7_23_72 : allFrom (a7Dat.rectI aIx 23) 72 8 = true := by
  decide +kernel

theorem a7_23_80 : allFrom (a7Dat.rectI aIx 23) 80 8 = true := by
  decide +kernel

theorem a7_23_88 : allFrom (a7Dat.rectI aIx 23) 88 8 = true := by
  decide +kernel

theorem a7_23_96 : allFrom (a7Dat.rectI aIx 23) 96 8 = true := by
  decide +kernel

theorem a7_23_104 : allFrom (a7Dat.rectI aIx 23) 104 8 = true := by
  decide +kernel

theorem a7_23_112 : allFrom (a7Dat.rectI aIx 23) 112 8 = true := by
  decide +kernel

theorem a7_23_120 : allFrom (a7Dat.rectI aIx 23) 120 8 = true := by
  decide +kernel

theorem a7_23_128 : allFrom (a7Dat.rectI aIx 23) 128 8 = true := by
  decide +kernel

theorem a7_row_23 : a7Dat.rowI aIx 23 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 23 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 23) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 23) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 23)) a7_23_0) a7_23_8) a7_23_16) a7_23_24) a7_23_32) a7_23_40) a7_23_48) a7_23_56) a7_23_64) a7_23_72) a7_23_80) a7_23_88) a7_23_96) a7_23_104) a7_23_112) a7_23_120) a7_23_128)

theorem a7_blk_20 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 20 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 20) a7_row_20 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 21) a7_row_21 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 22) a7_row_22 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 23) a7_row_23 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 24)))))

end SandierSerfaty.CertData.Box
