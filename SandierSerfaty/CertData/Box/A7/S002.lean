/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 2 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `8`–`11`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_8_0 : allFrom (a7Dat.rectI aIx 8) 0 8 = true := by
  decide +kernel

theorem a7_8_8 : allFrom (a7Dat.rectI aIx 8) 8 8 = true := by
  decide +kernel

theorem a7_8_16 : allFrom (a7Dat.rectI aIx 8) 16 8 = true := by
  decide +kernel

theorem a7_8_24 : allFrom (a7Dat.rectI aIx 8) 24 8 = true := by
  decide +kernel

theorem a7_8_32 : allFrom (a7Dat.rectI aIx 8) 32 8 = true := by
  decide +kernel

theorem a7_8_40 : allFrom (a7Dat.rectI aIx 8) 40 8 = true := by
  decide +kernel

theorem a7_8_48 : allFrom (a7Dat.rectI aIx 8) 48 8 = true := by
  decide +kernel

theorem a7_8_56 : allFrom (a7Dat.rectI aIx 8) 56 8 = true := by
  decide +kernel

theorem a7_8_64 : allFrom (a7Dat.rectI aIx 8) 64 8 = true := by
  decide +kernel

theorem a7_8_72 : allFrom (a7Dat.rectI aIx 8) 72 8 = true := by
  decide +kernel

theorem a7_8_80 : allFrom (a7Dat.rectI aIx 8) 80 8 = true := by
  decide +kernel

theorem a7_8_88 : allFrom (a7Dat.rectI aIx 8) 88 8 = true := by
  decide +kernel

theorem a7_8_96 : allFrom (a7Dat.rectI aIx 8) 96 8 = true := by
  decide +kernel

theorem a7_8_104 : allFrom (a7Dat.rectI aIx 8) 104 8 = true := by
  decide +kernel

theorem a7_8_112 : allFrom (a7Dat.rectI aIx 8) 112 8 = true := by
  decide +kernel

theorem a7_8_120 : allFrom (a7Dat.rectI aIx 8) 120 8 = true := by
  decide +kernel

theorem a7_8_128 : allFrom (a7Dat.rectI aIx 8) 128 8 = true := by
  decide +kernel

theorem a7_row_8 : a7Dat.rowI aIx 8 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 8 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 8) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 8) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 8)) a7_8_0) a7_8_8) a7_8_16) a7_8_24) a7_8_32) a7_8_40) a7_8_48) a7_8_56) a7_8_64) a7_8_72) a7_8_80) a7_8_88) a7_8_96) a7_8_104) a7_8_112) a7_8_120) a7_8_128)

theorem a7_9_0 : allFrom (a7Dat.rectI aIx 9) 0 8 = true := by
  decide +kernel

theorem a7_9_8 : allFrom (a7Dat.rectI aIx 9) 8 8 = true := by
  decide +kernel

theorem a7_9_16 : allFrom (a7Dat.rectI aIx 9) 16 8 = true := by
  decide +kernel

theorem a7_9_24 : allFrom (a7Dat.rectI aIx 9) 24 8 = true := by
  decide +kernel

theorem a7_9_32 : allFrom (a7Dat.rectI aIx 9) 32 8 = true := by
  decide +kernel

theorem a7_9_40 : allFrom (a7Dat.rectI aIx 9) 40 8 = true := by
  decide +kernel

theorem a7_9_48 : allFrom (a7Dat.rectI aIx 9) 48 8 = true := by
  decide +kernel

theorem a7_9_56 : allFrom (a7Dat.rectI aIx 9) 56 8 = true := by
  decide +kernel

theorem a7_9_64 : allFrom (a7Dat.rectI aIx 9) 64 8 = true := by
  decide +kernel

theorem a7_9_72 : allFrom (a7Dat.rectI aIx 9) 72 8 = true := by
  decide +kernel

theorem a7_9_80 : allFrom (a7Dat.rectI aIx 9) 80 8 = true := by
  decide +kernel

theorem a7_9_88 : allFrom (a7Dat.rectI aIx 9) 88 8 = true := by
  decide +kernel

theorem a7_9_96 : allFrom (a7Dat.rectI aIx 9) 96 8 = true := by
  decide +kernel

theorem a7_9_104 : allFrom (a7Dat.rectI aIx 9) 104 8 = true := by
  decide +kernel

theorem a7_9_112 : allFrom (a7Dat.rectI aIx 9) 112 8 = true := by
  decide +kernel

theorem a7_9_120 : allFrom (a7Dat.rectI aIx 9) 120 8 = true := by
  decide +kernel

theorem a7_9_128 : allFrom (a7Dat.rectI aIx 9) 128 8 = true := by
  decide +kernel

theorem a7_row_9 : a7Dat.rowI aIx 9 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 9 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 9) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 9) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 9)) a7_9_0) a7_9_8) a7_9_16) a7_9_24) a7_9_32) a7_9_40) a7_9_48) a7_9_56) a7_9_64) a7_9_72) a7_9_80) a7_9_88) a7_9_96) a7_9_104) a7_9_112) a7_9_120) a7_9_128)

theorem a7_10_0 : allFrom (a7Dat.rectI aIx 10) 0 8 = true := by
  decide +kernel

theorem a7_10_8 : allFrom (a7Dat.rectI aIx 10) 8 8 = true := by
  decide +kernel

theorem a7_10_16 : allFrom (a7Dat.rectI aIx 10) 16 8 = true := by
  decide +kernel

theorem a7_10_24 : allFrom (a7Dat.rectI aIx 10) 24 8 = true := by
  decide +kernel

theorem a7_10_32 : allFrom (a7Dat.rectI aIx 10) 32 8 = true := by
  decide +kernel

theorem a7_10_40 : allFrom (a7Dat.rectI aIx 10) 40 8 = true := by
  decide +kernel

theorem a7_10_48 : allFrom (a7Dat.rectI aIx 10) 48 8 = true := by
  decide +kernel

theorem a7_10_56 : allFrom (a7Dat.rectI aIx 10) 56 8 = true := by
  decide +kernel

theorem a7_10_64 : allFrom (a7Dat.rectI aIx 10) 64 8 = true := by
  decide +kernel

theorem a7_10_72 : allFrom (a7Dat.rectI aIx 10) 72 8 = true := by
  decide +kernel

theorem a7_10_80 : allFrom (a7Dat.rectI aIx 10) 80 8 = true := by
  decide +kernel

theorem a7_10_88 : allFrom (a7Dat.rectI aIx 10) 88 8 = true := by
  decide +kernel

theorem a7_10_96 : allFrom (a7Dat.rectI aIx 10) 96 8 = true := by
  decide +kernel

theorem a7_10_104 : allFrom (a7Dat.rectI aIx 10) 104 8 = true := by
  decide +kernel

theorem a7_10_112 : allFrom (a7Dat.rectI aIx 10) 112 8 = true := by
  decide +kernel

theorem a7_10_120 : allFrom (a7Dat.rectI aIx 10) 120 8 = true := by
  decide +kernel

theorem a7_10_128 : allFrom (a7Dat.rectI aIx 10) 128 8 = true := by
  decide +kernel

theorem a7_row_10 : a7Dat.rowI aIx 10 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 10 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 10) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 10) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 10)) a7_10_0) a7_10_8) a7_10_16) a7_10_24) a7_10_32) a7_10_40) a7_10_48) a7_10_56) a7_10_64) a7_10_72) a7_10_80) a7_10_88) a7_10_96) a7_10_104) a7_10_112) a7_10_120) a7_10_128)

theorem a7_11_0 : allFrom (a7Dat.rectI aIx 11) 0 8 = true := by
  decide +kernel

theorem a7_11_8 : allFrom (a7Dat.rectI aIx 11) 8 8 = true := by
  decide +kernel

theorem a7_11_16 : allFrom (a7Dat.rectI aIx 11) 16 8 = true := by
  decide +kernel

theorem a7_11_24 : allFrom (a7Dat.rectI aIx 11) 24 8 = true := by
  decide +kernel

theorem a7_11_32 : allFrom (a7Dat.rectI aIx 11) 32 8 = true := by
  decide +kernel

theorem a7_11_40 : allFrom (a7Dat.rectI aIx 11) 40 8 = true := by
  decide +kernel

theorem a7_11_48 : allFrom (a7Dat.rectI aIx 11) 48 8 = true := by
  decide +kernel

theorem a7_11_56 : allFrom (a7Dat.rectI aIx 11) 56 8 = true := by
  decide +kernel

theorem a7_11_64 : allFrom (a7Dat.rectI aIx 11) 64 8 = true := by
  decide +kernel

theorem a7_11_72 : allFrom (a7Dat.rectI aIx 11) 72 8 = true := by
  decide +kernel

theorem a7_11_80 : allFrom (a7Dat.rectI aIx 11) 80 8 = true := by
  decide +kernel

theorem a7_11_88 : allFrom (a7Dat.rectI aIx 11) 88 8 = true := by
  decide +kernel

theorem a7_11_96 : allFrom (a7Dat.rectI aIx 11) 96 8 = true := by
  decide +kernel

theorem a7_11_104 : allFrom (a7Dat.rectI aIx 11) 104 8 = true := by
  decide +kernel

theorem a7_11_112 : allFrom (a7Dat.rectI aIx 11) 112 8 = true := by
  decide +kernel

theorem a7_11_120 : allFrom (a7Dat.rectI aIx 11) 120 8 = true := by
  decide +kernel

theorem a7_11_128 : allFrom (a7Dat.rectI aIx 11) 128 8 = true := by
  decide +kernel

theorem a7_row_11 : a7Dat.rowI aIx 11 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 11 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 11) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 11) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 11)) a7_11_0) a7_11_8) a7_11_16) a7_11_24) a7_11_32) a7_11_40) a7_11_48) a7_11_56) a7_11_64) a7_11_72) a7_11_80) a7_11_88) a7_11_96) a7_11_104) a7_11_112) a7_11_120) a7_11_128)

theorem a7_blk_8 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 8 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 8) a7_row_8 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 9) a7_row_9 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 10) a7_row_10 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 11) a7_row_11 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 12)))))

end SandierSerfaty.CertData.Box
