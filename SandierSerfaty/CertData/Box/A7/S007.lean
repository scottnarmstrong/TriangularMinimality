/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 7 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `28`–`31`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_28_0 : allFrom (a7Dat.rectI aIx 28) 0 8 = true := by
  decide +kernel

theorem a7_28_8 : allFrom (a7Dat.rectI aIx 28) 8 8 = true := by
  decide +kernel

theorem a7_28_16 : allFrom (a7Dat.rectI aIx 28) 16 8 = true := by
  decide +kernel

theorem a7_28_24 : allFrom (a7Dat.rectI aIx 28) 24 8 = true := by
  decide +kernel

theorem a7_28_32 : allFrom (a7Dat.rectI aIx 28) 32 8 = true := by
  decide +kernel

theorem a7_28_40 : allFrom (a7Dat.rectI aIx 28) 40 8 = true := by
  decide +kernel

theorem a7_28_48 : allFrom (a7Dat.rectI aIx 28) 48 8 = true := by
  decide +kernel

theorem a7_28_56 : allFrom (a7Dat.rectI aIx 28) 56 8 = true := by
  decide +kernel

theorem a7_28_64 : allFrom (a7Dat.rectI aIx 28) 64 8 = true := by
  decide +kernel

theorem a7_28_72 : allFrom (a7Dat.rectI aIx 28) 72 8 = true := by
  decide +kernel

theorem a7_28_80 : allFrom (a7Dat.rectI aIx 28) 80 8 = true := by
  decide +kernel

theorem a7_28_88 : allFrom (a7Dat.rectI aIx 28) 88 8 = true := by
  decide +kernel

theorem a7_28_96 : allFrom (a7Dat.rectI aIx 28) 96 8 = true := by
  decide +kernel

theorem a7_28_104 : allFrom (a7Dat.rectI aIx 28) 104 8 = true := by
  decide +kernel

theorem a7_28_112 : allFrom (a7Dat.rectI aIx 28) 112 8 = true := by
  decide +kernel

theorem a7_28_120 : allFrom (a7Dat.rectI aIx 28) 120 8 = true := by
  decide +kernel

theorem a7_28_128 : allFrom (a7Dat.rectI aIx 28) 128 8 = true := by
  decide +kernel

theorem a7_row_28 : a7Dat.rowI aIx 28 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 28 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 28) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 28) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 28)) a7_28_0) a7_28_8) a7_28_16) a7_28_24) a7_28_32) a7_28_40) a7_28_48) a7_28_56) a7_28_64) a7_28_72) a7_28_80) a7_28_88) a7_28_96) a7_28_104) a7_28_112) a7_28_120) a7_28_128)

theorem a7_29_0 : allFrom (a7Dat.rectI aIx 29) 0 8 = true := by
  decide +kernel

theorem a7_29_8 : allFrom (a7Dat.rectI aIx 29) 8 8 = true := by
  decide +kernel

theorem a7_29_16 : allFrom (a7Dat.rectI aIx 29) 16 8 = true := by
  decide +kernel

theorem a7_29_24 : allFrom (a7Dat.rectI aIx 29) 24 8 = true := by
  decide +kernel

theorem a7_29_32 : allFrom (a7Dat.rectI aIx 29) 32 8 = true := by
  decide +kernel

theorem a7_29_40 : allFrom (a7Dat.rectI aIx 29) 40 8 = true := by
  decide +kernel

theorem a7_29_48 : allFrom (a7Dat.rectI aIx 29) 48 8 = true := by
  decide +kernel

theorem a7_29_56 : allFrom (a7Dat.rectI aIx 29) 56 8 = true := by
  decide +kernel

theorem a7_29_64 : allFrom (a7Dat.rectI aIx 29) 64 8 = true := by
  decide +kernel

theorem a7_29_72 : allFrom (a7Dat.rectI aIx 29) 72 8 = true := by
  decide +kernel

theorem a7_29_80 : allFrom (a7Dat.rectI aIx 29) 80 8 = true := by
  decide +kernel

theorem a7_29_88 : allFrom (a7Dat.rectI aIx 29) 88 8 = true := by
  decide +kernel

theorem a7_29_96 : allFrom (a7Dat.rectI aIx 29) 96 8 = true := by
  decide +kernel

theorem a7_29_104 : allFrom (a7Dat.rectI aIx 29) 104 8 = true := by
  decide +kernel

theorem a7_29_112 : allFrom (a7Dat.rectI aIx 29) 112 8 = true := by
  decide +kernel

theorem a7_29_120 : allFrom (a7Dat.rectI aIx 29) 120 8 = true := by
  decide +kernel

theorem a7_29_128 : allFrom (a7Dat.rectI aIx 29) 128 8 = true := by
  decide +kernel

theorem a7_row_29 : a7Dat.rowI aIx 29 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 29 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 29) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 29) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 29)) a7_29_0) a7_29_8) a7_29_16) a7_29_24) a7_29_32) a7_29_40) a7_29_48) a7_29_56) a7_29_64) a7_29_72) a7_29_80) a7_29_88) a7_29_96) a7_29_104) a7_29_112) a7_29_120) a7_29_128)

theorem a7_30_0 : allFrom (a7Dat.rectI aIx 30) 0 8 = true := by
  decide +kernel

theorem a7_30_8 : allFrom (a7Dat.rectI aIx 30) 8 8 = true := by
  decide +kernel

theorem a7_30_16 : allFrom (a7Dat.rectI aIx 30) 16 8 = true := by
  decide +kernel

theorem a7_30_24 : allFrom (a7Dat.rectI aIx 30) 24 8 = true := by
  decide +kernel

theorem a7_30_32 : allFrom (a7Dat.rectI aIx 30) 32 8 = true := by
  decide +kernel

theorem a7_30_40 : allFrom (a7Dat.rectI aIx 30) 40 8 = true := by
  decide +kernel

theorem a7_30_48 : allFrom (a7Dat.rectI aIx 30) 48 8 = true := by
  decide +kernel

theorem a7_30_56 : allFrom (a7Dat.rectI aIx 30) 56 8 = true := by
  decide +kernel

theorem a7_30_64 : allFrom (a7Dat.rectI aIx 30) 64 8 = true := by
  decide +kernel

theorem a7_30_72 : allFrom (a7Dat.rectI aIx 30) 72 8 = true := by
  decide +kernel

theorem a7_30_80 : allFrom (a7Dat.rectI aIx 30) 80 8 = true := by
  decide +kernel

theorem a7_30_88 : allFrom (a7Dat.rectI aIx 30) 88 8 = true := by
  decide +kernel

theorem a7_30_96 : allFrom (a7Dat.rectI aIx 30) 96 8 = true := by
  decide +kernel

theorem a7_30_104 : allFrom (a7Dat.rectI aIx 30) 104 8 = true := by
  decide +kernel

theorem a7_30_112 : allFrom (a7Dat.rectI aIx 30) 112 8 = true := by
  decide +kernel

theorem a7_30_120 : allFrom (a7Dat.rectI aIx 30) 120 8 = true := by
  decide +kernel

theorem a7_30_128 : allFrom (a7Dat.rectI aIx 30) 128 8 = true := by
  decide +kernel

theorem a7_row_30 : a7Dat.rowI aIx 30 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 30 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 30) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 30) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 30)) a7_30_0) a7_30_8) a7_30_16) a7_30_24) a7_30_32) a7_30_40) a7_30_48) a7_30_56) a7_30_64) a7_30_72) a7_30_80) a7_30_88) a7_30_96) a7_30_104) a7_30_112) a7_30_120) a7_30_128)

theorem a7_31_0 : allFrom (a7Dat.rectI aIx 31) 0 8 = true := by
  decide +kernel

theorem a7_31_8 : allFrom (a7Dat.rectI aIx 31) 8 8 = true := by
  decide +kernel

theorem a7_31_16 : allFrom (a7Dat.rectI aIx 31) 16 8 = true := by
  decide +kernel

theorem a7_31_24 : allFrom (a7Dat.rectI aIx 31) 24 8 = true := by
  decide +kernel

theorem a7_31_32 : allFrom (a7Dat.rectI aIx 31) 32 8 = true := by
  decide +kernel

theorem a7_31_40 : allFrom (a7Dat.rectI aIx 31) 40 8 = true := by
  decide +kernel

theorem a7_31_48 : allFrom (a7Dat.rectI aIx 31) 48 8 = true := by
  decide +kernel

theorem a7_31_56 : allFrom (a7Dat.rectI aIx 31) 56 8 = true := by
  decide +kernel

theorem a7_31_64 : allFrom (a7Dat.rectI aIx 31) 64 8 = true := by
  decide +kernel

theorem a7_31_72 : allFrom (a7Dat.rectI aIx 31) 72 8 = true := by
  decide +kernel

theorem a7_31_80 : allFrom (a7Dat.rectI aIx 31) 80 8 = true := by
  decide +kernel

theorem a7_31_88 : allFrom (a7Dat.rectI aIx 31) 88 8 = true := by
  decide +kernel

theorem a7_31_96 : allFrom (a7Dat.rectI aIx 31) 96 8 = true := by
  decide +kernel

theorem a7_31_104 : allFrom (a7Dat.rectI aIx 31) 104 8 = true := by
  decide +kernel

theorem a7_31_112 : allFrom (a7Dat.rectI aIx 31) 112 8 = true := by
  decide +kernel

theorem a7_31_120 : allFrom (a7Dat.rectI aIx 31) 120 8 = true := by
  decide +kernel

theorem a7_31_128 : allFrom (a7Dat.rectI aIx 31) 128 8 = true := by
  decide +kernel

theorem a7_row_31 : a7Dat.rowI aIx 31 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 31 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 31) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 31) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 31)) a7_31_0) a7_31_8) a7_31_16) a7_31_24) a7_31_32) a7_31_40) a7_31_48) a7_31_56) a7_31_64) a7_31_72) a7_31_80) a7_31_88) a7_31_96) a7_31_104) a7_31_112) a7_31_120) a7_31_128)

theorem a7_blk_28 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 28 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 28) a7_row_28 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 29) a7_row_29 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 30) a7_row_30 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 31) a7_row_31 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 32)))))

end SandierSerfaty.CertData.Box
