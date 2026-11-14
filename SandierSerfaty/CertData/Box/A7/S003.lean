/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 3 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `12`–`15`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_12_0 : allFrom (a7Dat.rectI aIx 12) 0 8 = true := by
  decide +kernel

theorem a7_12_8 : allFrom (a7Dat.rectI aIx 12) 8 8 = true := by
  decide +kernel

theorem a7_12_16 : allFrom (a7Dat.rectI aIx 12) 16 8 = true := by
  decide +kernel

theorem a7_12_24 : allFrom (a7Dat.rectI aIx 12) 24 8 = true := by
  decide +kernel

theorem a7_12_32 : allFrom (a7Dat.rectI aIx 12) 32 8 = true := by
  decide +kernel

theorem a7_12_40 : allFrom (a7Dat.rectI aIx 12) 40 8 = true := by
  decide +kernel

theorem a7_12_48 : allFrom (a7Dat.rectI aIx 12) 48 8 = true := by
  decide +kernel

theorem a7_12_56 : allFrom (a7Dat.rectI aIx 12) 56 8 = true := by
  decide +kernel

theorem a7_12_64 : allFrom (a7Dat.rectI aIx 12) 64 8 = true := by
  decide +kernel

theorem a7_12_72 : allFrom (a7Dat.rectI aIx 12) 72 8 = true := by
  decide +kernel

theorem a7_12_80 : allFrom (a7Dat.rectI aIx 12) 80 8 = true := by
  decide +kernel

theorem a7_12_88 : allFrom (a7Dat.rectI aIx 12) 88 8 = true := by
  decide +kernel

theorem a7_12_96 : allFrom (a7Dat.rectI aIx 12) 96 8 = true := by
  decide +kernel

theorem a7_12_104 : allFrom (a7Dat.rectI aIx 12) 104 8 = true := by
  decide +kernel

theorem a7_12_112 : allFrom (a7Dat.rectI aIx 12) 112 8 = true := by
  decide +kernel

theorem a7_12_120 : allFrom (a7Dat.rectI aIx 12) 120 8 = true := by
  decide +kernel

theorem a7_12_128 : allFrom (a7Dat.rectI aIx 12) 128 8 = true := by
  decide +kernel

theorem a7_row_12 : a7Dat.rowI aIx 12 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 12 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 12) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 12) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 12)) a7_12_0) a7_12_8) a7_12_16) a7_12_24) a7_12_32) a7_12_40) a7_12_48) a7_12_56) a7_12_64) a7_12_72) a7_12_80) a7_12_88) a7_12_96) a7_12_104) a7_12_112) a7_12_120) a7_12_128)

theorem a7_13_0 : allFrom (a7Dat.rectI aIx 13) 0 8 = true := by
  decide +kernel

theorem a7_13_8 : allFrom (a7Dat.rectI aIx 13) 8 8 = true := by
  decide +kernel

theorem a7_13_16 : allFrom (a7Dat.rectI aIx 13) 16 8 = true := by
  decide +kernel

theorem a7_13_24 : allFrom (a7Dat.rectI aIx 13) 24 8 = true := by
  decide +kernel

theorem a7_13_32 : allFrom (a7Dat.rectI aIx 13) 32 8 = true := by
  decide +kernel

theorem a7_13_40 : allFrom (a7Dat.rectI aIx 13) 40 8 = true := by
  decide +kernel

theorem a7_13_48 : allFrom (a7Dat.rectI aIx 13) 48 8 = true := by
  decide +kernel

theorem a7_13_56 : allFrom (a7Dat.rectI aIx 13) 56 8 = true := by
  decide +kernel

theorem a7_13_64 : allFrom (a7Dat.rectI aIx 13) 64 8 = true := by
  decide +kernel

theorem a7_13_72 : allFrom (a7Dat.rectI aIx 13) 72 8 = true := by
  decide +kernel

theorem a7_13_80 : allFrom (a7Dat.rectI aIx 13) 80 8 = true := by
  decide +kernel

theorem a7_13_88 : allFrom (a7Dat.rectI aIx 13) 88 8 = true := by
  decide +kernel

theorem a7_13_96 : allFrom (a7Dat.rectI aIx 13) 96 8 = true := by
  decide +kernel

theorem a7_13_104 : allFrom (a7Dat.rectI aIx 13) 104 8 = true := by
  decide +kernel

theorem a7_13_112 : allFrom (a7Dat.rectI aIx 13) 112 8 = true := by
  decide +kernel

theorem a7_13_120 : allFrom (a7Dat.rectI aIx 13) 120 8 = true := by
  decide +kernel

theorem a7_13_128 : allFrom (a7Dat.rectI aIx 13) 128 8 = true := by
  decide +kernel

theorem a7_row_13 : a7Dat.rowI aIx 13 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 13 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 13) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 13) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 13)) a7_13_0) a7_13_8) a7_13_16) a7_13_24) a7_13_32) a7_13_40) a7_13_48) a7_13_56) a7_13_64) a7_13_72) a7_13_80) a7_13_88) a7_13_96) a7_13_104) a7_13_112) a7_13_120) a7_13_128)

theorem a7_14_0 : allFrom (a7Dat.rectI aIx 14) 0 8 = true := by
  decide +kernel

theorem a7_14_8 : allFrom (a7Dat.rectI aIx 14) 8 8 = true := by
  decide +kernel

theorem a7_14_16 : allFrom (a7Dat.rectI aIx 14) 16 8 = true := by
  decide +kernel

theorem a7_14_24 : allFrom (a7Dat.rectI aIx 14) 24 8 = true := by
  decide +kernel

theorem a7_14_32 : allFrom (a7Dat.rectI aIx 14) 32 8 = true := by
  decide +kernel

theorem a7_14_40 : allFrom (a7Dat.rectI aIx 14) 40 8 = true := by
  decide +kernel

theorem a7_14_48 : allFrom (a7Dat.rectI aIx 14) 48 8 = true := by
  decide +kernel

theorem a7_14_56 : allFrom (a7Dat.rectI aIx 14) 56 8 = true := by
  decide +kernel

theorem a7_14_64 : allFrom (a7Dat.rectI aIx 14) 64 8 = true := by
  decide +kernel

theorem a7_14_72 : allFrom (a7Dat.rectI aIx 14) 72 8 = true := by
  decide +kernel

theorem a7_14_80 : allFrom (a7Dat.rectI aIx 14) 80 8 = true := by
  decide +kernel

theorem a7_14_88 : allFrom (a7Dat.rectI aIx 14) 88 8 = true := by
  decide +kernel

theorem a7_14_96 : allFrom (a7Dat.rectI aIx 14) 96 8 = true := by
  decide +kernel

theorem a7_14_104 : allFrom (a7Dat.rectI aIx 14) 104 8 = true := by
  decide +kernel

theorem a7_14_112 : allFrom (a7Dat.rectI aIx 14) 112 8 = true := by
  decide +kernel

theorem a7_14_120 : allFrom (a7Dat.rectI aIx 14) 120 8 = true := by
  decide +kernel

theorem a7_14_128 : allFrom (a7Dat.rectI aIx 14) 128 8 = true := by
  decide +kernel

theorem a7_row_14 : a7Dat.rowI aIx 14 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 14 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 14) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 14) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 14)) a7_14_0) a7_14_8) a7_14_16) a7_14_24) a7_14_32) a7_14_40) a7_14_48) a7_14_56) a7_14_64) a7_14_72) a7_14_80) a7_14_88) a7_14_96) a7_14_104) a7_14_112) a7_14_120) a7_14_128)

theorem a7_15_0 : allFrom (a7Dat.rectI aIx 15) 0 8 = true := by
  decide +kernel

theorem a7_15_8 : allFrom (a7Dat.rectI aIx 15) 8 8 = true := by
  decide +kernel

theorem a7_15_16 : allFrom (a7Dat.rectI aIx 15) 16 8 = true := by
  decide +kernel

theorem a7_15_24 : allFrom (a7Dat.rectI aIx 15) 24 8 = true := by
  decide +kernel

theorem a7_15_32 : allFrom (a7Dat.rectI aIx 15) 32 8 = true := by
  decide +kernel

theorem a7_15_40 : allFrom (a7Dat.rectI aIx 15) 40 8 = true := by
  decide +kernel

theorem a7_15_48 : allFrom (a7Dat.rectI aIx 15) 48 8 = true := by
  decide +kernel

theorem a7_15_56 : allFrom (a7Dat.rectI aIx 15) 56 8 = true := by
  decide +kernel

theorem a7_15_64 : allFrom (a7Dat.rectI aIx 15) 64 8 = true := by
  decide +kernel

theorem a7_15_72 : allFrom (a7Dat.rectI aIx 15) 72 8 = true := by
  decide +kernel

theorem a7_15_80 : allFrom (a7Dat.rectI aIx 15) 80 8 = true := by
  decide +kernel

theorem a7_15_88 : allFrom (a7Dat.rectI aIx 15) 88 8 = true := by
  decide +kernel

theorem a7_15_96 : allFrom (a7Dat.rectI aIx 15) 96 8 = true := by
  decide +kernel

theorem a7_15_104 : allFrom (a7Dat.rectI aIx 15) 104 8 = true := by
  decide +kernel

theorem a7_15_112 : allFrom (a7Dat.rectI aIx 15) 112 8 = true := by
  decide +kernel

theorem a7_15_120 : allFrom (a7Dat.rectI aIx 15) 120 8 = true := by
  decide +kernel

theorem a7_15_128 : allFrom (a7Dat.rectI aIx 15) 128 8 = true := by
  decide +kernel

theorem a7_row_15 : a7Dat.rowI aIx 15 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 15 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 15) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 15) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 15)) a7_15_0) a7_15_8) a7_15_16) a7_15_24) a7_15_32) a7_15_40) a7_15_48) a7_15_56) a7_15_64) a7_15_72) a7_15_80) a7_15_88) a7_15_96) a7_15_104) a7_15_112) a7_15_120) a7_15_128)

theorem a7_blk_12 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 12 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 12) a7_row_12 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 13) a7_row_13 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 14) a7_row_14 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 15) a7_row_15 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 16)))))

end SandierSerfaty.CertData.Box
