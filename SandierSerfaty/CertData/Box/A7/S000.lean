/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 0 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `0`–`3`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_0_0 : allFrom (a7Dat.rectI aIx 0) 0 8 = true := by
  decide +kernel

theorem a7_0_8 : allFrom (a7Dat.rectI aIx 0) 8 8 = true := by
  decide +kernel

theorem a7_0_16 : allFrom (a7Dat.rectI aIx 0) 16 8 = true := by
  decide +kernel

theorem a7_0_24 : allFrom (a7Dat.rectI aIx 0) 24 8 = true := by
  decide +kernel

theorem a7_0_32 : allFrom (a7Dat.rectI aIx 0) 32 8 = true := by
  decide +kernel

theorem a7_0_40 : allFrom (a7Dat.rectI aIx 0) 40 8 = true := by
  decide +kernel

theorem a7_0_48 : allFrom (a7Dat.rectI aIx 0) 48 8 = true := by
  decide +kernel

theorem a7_0_56 : allFrom (a7Dat.rectI aIx 0) 56 8 = true := by
  decide +kernel

theorem a7_0_64 : allFrom (a7Dat.rectI aIx 0) 64 8 = true := by
  decide +kernel

theorem a7_0_72 : allFrom (a7Dat.rectI aIx 0) 72 8 = true := by
  decide +kernel

theorem a7_0_80 : allFrom (a7Dat.rectI aIx 0) 80 8 = true := by
  decide +kernel

theorem a7_0_88 : allFrom (a7Dat.rectI aIx 0) 88 8 = true := by
  decide +kernel

theorem a7_0_96 : allFrom (a7Dat.rectI aIx 0) 96 8 = true := by
  decide +kernel

theorem a7_0_104 : allFrom (a7Dat.rectI aIx 0) 104 8 = true := by
  decide +kernel

theorem a7_0_112 : allFrom (a7Dat.rectI aIx 0) 112 8 = true := by
  decide +kernel

theorem a7_0_120 : allFrom (a7Dat.rectI aIx 0) 120 8 = true := by
  decide +kernel

theorem a7_0_128 : allFrom (a7Dat.rectI aIx 0) 128 8 = true := by
  decide +kernel

theorem a7_row_0 : a7Dat.rowI aIx 0 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 0 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 0) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 0) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 0)) a7_0_0) a7_0_8) a7_0_16) a7_0_24) a7_0_32) a7_0_40) a7_0_48) a7_0_56) a7_0_64) a7_0_72) a7_0_80) a7_0_88) a7_0_96) a7_0_104) a7_0_112) a7_0_120) a7_0_128)

theorem a7_1_0 : allFrom (a7Dat.rectI aIx 1) 0 8 = true := by
  decide +kernel

theorem a7_1_8 : allFrom (a7Dat.rectI aIx 1) 8 8 = true := by
  decide +kernel

theorem a7_1_16 : allFrom (a7Dat.rectI aIx 1) 16 8 = true := by
  decide +kernel

theorem a7_1_24 : allFrom (a7Dat.rectI aIx 1) 24 8 = true := by
  decide +kernel

theorem a7_1_32 : allFrom (a7Dat.rectI aIx 1) 32 8 = true := by
  decide +kernel

theorem a7_1_40 : allFrom (a7Dat.rectI aIx 1) 40 8 = true := by
  decide +kernel

theorem a7_1_48 : allFrom (a7Dat.rectI aIx 1) 48 8 = true := by
  decide +kernel

theorem a7_1_56 : allFrom (a7Dat.rectI aIx 1) 56 8 = true := by
  decide +kernel

theorem a7_1_64 : allFrom (a7Dat.rectI aIx 1) 64 8 = true := by
  decide +kernel

theorem a7_1_72 : allFrom (a7Dat.rectI aIx 1) 72 8 = true := by
  decide +kernel

theorem a7_1_80 : allFrom (a7Dat.rectI aIx 1) 80 8 = true := by
  decide +kernel

theorem a7_1_88 : allFrom (a7Dat.rectI aIx 1) 88 8 = true := by
  decide +kernel

theorem a7_1_96 : allFrom (a7Dat.rectI aIx 1) 96 8 = true := by
  decide +kernel

theorem a7_1_104 : allFrom (a7Dat.rectI aIx 1) 104 8 = true := by
  decide +kernel

theorem a7_1_112 : allFrom (a7Dat.rectI aIx 1) 112 8 = true := by
  decide +kernel

theorem a7_1_120 : allFrom (a7Dat.rectI aIx 1) 120 8 = true := by
  decide +kernel

theorem a7_1_128 : allFrom (a7Dat.rectI aIx 1) 128 8 = true := by
  decide +kernel

theorem a7_row_1 : a7Dat.rowI aIx 1 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 1 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 1) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 1) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 1)) a7_1_0) a7_1_8) a7_1_16) a7_1_24) a7_1_32) a7_1_40) a7_1_48) a7_1_56) a7_1_64) a7_1_72) a7_1_80) a7_1_88) a7_1_96) a7_1_104) a7_1_112) a7_1_120) a7_1_128)

theorem a7_2_0 : allFrom (a7Dat.rectI aIx 2) 0 8 = true := by
  decide +kernel

theorem a7_2_8 : allFrom (a7Dat.rectI aIx 2) 8 8 = true := by
  decide +kernel

theorem a7_2_16 : allFrom (a7Dat.rectI aIx 2) 16 8 = true := by
  decide +kernel

theorem a7_2_24 : allFrom (a7Dat.rectI aIx 2) 24 8 = true := by
  decide +kernel

theorem a7_2_32 : allFrom (a7Dat.rectI aIx 2) 32 8 = true := by
  decide +kernel

theorem a7_2_40 : allFrom (a7Dat.rectI aIx 2) 40 8 = true := by
  decide +kernel

theorem a7_2_48 : allFrom (a7Dat.rectI aIx 2) 48 8 = true := by
  decide +kernel

theorem a7_2_56 : allFrom (a7Dat.rectI aIx 2) 56 8 = true := by
  decide +kernel

theorem a7_2_64 : allFrom (a7Dat.rectI aIx 2) 64 8 = true := by
  decide +kernel

theorem a7_2_72 : allFrom (a7Dat.rectI aIx 2) 72 8 = true := by
  decide +kernel

theorem a7_2_80 : allFrom (a7Dat.rectI aIx 2) 80 8 = true := by
  decide +kernel

theorem a7_2_88 : allFrom (a7Dat.rectI aIx 2) 88 8 = true := by
  decide +kernel

theorem a7_2_96 : allFrom (a7Dat.rectI aIx 2) 96 8 = true := by
  decide +kernel

theorem a7_2_104 : allFrom (a7Dat.rectI aIx 2) 104 8 = true := by
  decide +kernel

theorem a7_2_112 : allFrom (a7Dat.rectI aIx 2) 112 8 = true := by
  decide +kernel

theorem a7_2_120 : allFrom (a7Dat.rectI aIx 2) 120 8 = true := by
  decide +kernel

theorem a7_2_128 : allFrom (a7Dat.rectI aIx 2) 128 8 = true := by
  decide +kernel

theorem a7_row_2 : a7Dat.rowI aIx 2 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 2 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 2) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 2) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 2)) a7_2_0) a7_2_8) a7_2_16) a7_2_24) a7_2_32) a7_2_40) a7_2_48) a7_2_56) a7_2_64) a7_2_72) a7_2_80) a7_2_88) a7_2_96) a7_2_104) a7_2_112) a7_2_120) a7_2_128)

theorem a7_3_0 : allFrom (a7Dat.rectI aIx 3) 0 8 = true := by
  decide +kernel

theorem a7_3_8 : allFrom (a7Dat.rectI aIx 3) 8 8 = true := by
  decide +kernel

theorem a7_3_16 : allFrom (a7Dat.rectI aIx 3) 16 8 = true := by
  decide +kernel

theorem a7_3_24 : allFrom (a7Dat.rectI aIx 3) 24 8 = true := by
  decide +kernel

theorem a7_3_32 : allFrom (a7Dat.rectI aIx 3) 32 8 = true := by
  decide +kernel

theorem a7_3_40 : allFrom (a7Dat.rectI aIx 3) 40 8 = true := by
  decide +kernel

theorem a7_3_48 : allFrom (a7Dat.rectI aIx 3) 48 8 = true := by
  decide +kernel

theorem a7_3_56 : allFrom (a7Dat.rectI aIx 3) 56 8 = true := by
  decide +kernel

theorem a7_3_64 : allFrom (a7Dat.rectI aIx 3) 64 8 = true := by
  decide +kernel

theorem a7_3_72 : allFrom (a7Dat.rectI aIx 3) 72 8 = true := by
  decide +kernel

theorem a7_3_80 : allFrom (a7Dat.rectI aIx 3) 80 8 = true := by
  decide +kernel

theorem a7_3_88 : allFrom (a7Dat.rectI aIx 3) 88 8 = true := by
  decide +kernel

theorem a7_3_96 : allFrom (a7Dat.rectI aIx 3) 96 8 = true := by
  decide +kernel

theorem a7_3_104 : allFrom (a7Dat.rectI aIx 3) 104 8 = true := by
  decide +kernel

theorem a7_3_112 : allFrom (a7Dat.rectI aIx 3) 112 8 = true := by
  decide +kernel

theorem a7_3_120 : allFrom (a7Dat.rectI aIx 3) 120 8 = true := by
  decide +kernel

theorem a7_3_128 : allFrom (a7Dat.rectI aIx 3) 128 8 = true := by
  decide +kernel

theorem a7_row_3 : a7Dat.rowI aIx 3 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 3 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 3) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 3) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 3)) a7_3_0) a7_3_8) a7_3_16) a7_3_24) a7_3_32) a7_3_40) a7_3_48) a7_3_56) a7_3_64) a7_3_72) a7_3_80) a7_3_88) a7_3_96) a7_3_104) a7_3_112) a7_3_120) a7_3_128)

theorem a7_blk_0 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 0 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 0) a7_row_0 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 1) a7_row_1 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 2) a7_row_2 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 3) a7_row_3 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 4)))))

end SandierSerfaty.CertData.Box
