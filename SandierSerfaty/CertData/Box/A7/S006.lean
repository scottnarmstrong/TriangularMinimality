/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 6 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `24`–`27`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_24_0 : allFrom (a7Dat.rectI aIx 24) 0 8 = true := by
  decide +kernel

theorem a7_24_8 : allFrom (a7Dat.rectI aIx 24) 8 8 = true := by
  decide +kernel

theorem a7_24_16 : allFrom (a7Dat.rectI aIx 24) 16 8 = true := by
  decide +kernel

theorem a7_24_24 : allFrom (a7Dat.rectI aIx 24) 24 8 = true := by
  decide +kernel

theorem a7_24_32 : allFrom (a7Dat.rectI aIx 24) 32 8 = true := by
  decide +kernel

theorem a7_24_40 : allFrom (a7Dat.rectI aIx 24) 40 8 = true := by
  decide +kernel

theorem a7_24_48 : allFrom (a7Dat.rectI aIx 24) 48 8 = true := by
  decide +kernel

theorem a7_24_56 : allFrom (a7Dat.rectI aIx 24) 56 8 = true := by
  decide +kernel

theorem a7_24_64 : allFrom (a7Dat.rectI aIx 24) 64 8 = true := by
  decide +kernel

theorem a7_24_72 : allFrom (a7Dat.rectI aIx 24) 72 8 = true := by
  decide +kernel

theorem a7_24_80 : allFrom (a7Dat.rectI aIx 24) 80 8 = true := by
  decide +kernel

theorem a7_24_88 : allFrom (a7Dat.rectI aIx 24) 88 8 = true := by
  decide +kernel

theorem a7_24_96 : allFrom (a7Dat.rectI aIx 24) 96 8 = true := by
  decide +kernel

theorem a7_24_104 : allFrom (a7Dat.rectI aIx 24) 104 8 = true := by
  decide +kernel

theorem a7_24_112 : allFrom (a7Dat.rectI aIx 24) 112 8 = true := by
  decide +kernel

theorem a7_24_120 : allFrom (a7Dat.rectI aIx 24) 120 8 = true := by
  decide +kernel

theorem a7_24_128 : allFrom (a7Dat.rectI aIx 24) 128 8 = true := by
  decide +kernel

theorem a7_row_24 : a7Dat.rowI aIx 24 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 24 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 24) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 24) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 24)) a7_24_0) a7_24_8) a7_24_16) a7_24_24) a7_24_32) a7_24_40) a7_24_48) a7_24_56) a7_24_64) a7_24_72) a7_24_80) a7_24_88) a7_24_96) a7_24_104) a7_24_112) a7_24_120) a7_24_128)

theorem a7_25_0 : allFrom (a7Dat.rectI aIx 25) 0 8 = true := by
  decide +kernel

theorem a7_25_8 : allFrom (a7Dat.rectI aIx 25) 8 8 = true := by
  decide +kernel

theorem a7_25_16 : allFrom (a7Dat.rectI aIx 25) 16 8 = true := by
  decide +kernel

theorem a7_25_24 : allFrom (a7Dat.rectI aIx 25) 24 8 = true := by
  decide +kernel

theorem a7_25_32 : allFrom (a7Dat.rectI aIx 25) 32 8 = true := by
  decide +kernel

theorem a7_25_40 : allFrom (a7Dat.rectI aIx 25) 40 8 = true := by
  decide +kernel

theorem a7_25_48 : allFrom (a7Dat.rectI aIx 25) 48 8 = true := by
  decide +kernel

theorem a7_25_56 : allFrom (a7Dat.rectI aIx 25) 56 8 = true := by
  decide +kernel

theorem a7_25_64 : allFrom (a7Dat.rectI aIx 25) 64 8 = true := by
  decide +kernel

theorem a7_25_72 : allFrom (a7Dat.rectI aIx 25) 72 8 = true := by
  decide +kernel

theorem a7_25_80 : allFrom (a7Dat.rectI aIx 25) 80 8 = true := by
  decide +kernel

theorem a7_25_88 : allFrom (a7Dat.rectI aIx 25) 88 8 = true := by
  decide +kernel

theorem a7_25_96 : allFrom (a7Dat.rectI aIx 25) 96 8 = true := by
  decide +kernel

theorem a7_25_104 : allFrom (a7Dat.rectI aIx 25) 104 8 = true := by
  decide +kernel

theorem a7_25_112 : allFrom (a7Dat.rectI aIx 25) 112 8 = true := by
  decide +kernel

theorem a7_25_120 : allFrom (a7Dat.rectI aIx 25) 120 8 = true := by
  decide +kernel

theorem a7_25_128 : allFrom (a7Dat.rectI aIx 25) 128 8 = true := by
  decide +kernel

theorem a7_row_25 : a7Dat.rowI aIx 25 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 25 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 25) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 25) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 25)) a7_25_0) a7_25_8) a7_25_16) a7_25_24) a7_25_32) a7_25_40) a7_25_48) a7_25_56) a7_25_64) a7_25_72) a7_25_80) a7_25_88) a7_25_96) a7_25_104) a7_25_112) a7_25_120) a7_25_128)

theorem a7_26_0 : allFrom (a7Dat.rectI aIx 26) 0 8 = true := by
  decide +kernel

theorem a7_26_8 : allFrom (a7Dat.rectI aIx 26) 8 8 = true := by
  decide +kernel

theorem a7_26_16 : allFrom (a7Dat.rectI aIx 26) 16 8 = true := by
  decide +kernel

theorem a7_26_24 : allFrom (a7Dat.rectI aIx 26) 24 8 = true := by
  decide +kernel

theorem a7_26_32 : allFrom (a7Dat.rectI aIx 26) 32 8 = true := by
  decide +kernel

theorem a7_26_40 : allFrom (a7Dat.rectI aIx 26) 40 8 = true := by
  decide +kernel

theorem a7_26_48 : allFrom (a7Dat.rectI aIx 26) 48 8 = true := by
  decide +kernel

theorem a7_26_56 : allFrom (a7Dat.rectI aIx 26) 56 8 = true := by
  decide +kernel

theorem a7_26_64 : allFrom (a7Dat.rectI aIx 26) 64 8 = true := by
  decide +kernel

theorem a7_26_72 : allFrom (a7Dat.rectI aIx 26) 72 8 = true := by
  decide +kernel

theorem a7_26_80 : allFrom (a7Dat.rectI aIx 26) 80 8 = true := by
  decide +kernel

theorem a7_26_88 : allFrom (a7Dat.rectI aIx 26) 88 8 = true := by
  decide +kernel

theorem a7_26_96 : allFrom (a7Dat.rectI aIx 26) 96 8 = true := by
  decide +kernel

theorem a7_26_104 : allFrom (a7Dat.rectI aIx 26) 104 8 = true := by
  decide +kernel

theorem a7_26_112 : allFrom (a7Dat.rectI aIx 26) 112 8 = true := by
  decide +kernel

theorem a7_26_120 : allFrom (a7Dat.rectI aIx 26) 120 8 = true := by
  decide +kernel

theorem a7_26_128 : allFrom (a7Dat.rectI aIx 26) 128 8 = true := by
  decide +kernel

theorem a7_row_26 : a7Dat.rowI aIx 26 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 26 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 26) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 26) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 26)) a7_26_0) a7_26_8) a7_26_16) a7_26_24) a7_26_32) a7_26_40) a7_26_48) a7_26_56) a7_26_64) a7_26_72) a7_26_80) a7_26_88) a7_26_96) a7_26_104) a7_26_112) a7_26_120) a7_26_128)

theorem a7_27_0 : allFrom (a7Dat.rectI aIx 27) 0 8 = true := by
  decide +kernel

theorem a7_27_8 : allFrom (a7Dat.rectI aIx 27) 8 8 = true := by
  decide +kernel

theorem a7_27_16 : allFrom (a7Dat.rectI aIx 27) 16 8 = true := by
  decide +kernel

theorem a7_27_24 : allFrom (a7Dat.rectI aIx 27) 24 8 = true := by
  decide +kernel

theorem a7_27_32 : allFrom (a7Dat.rectI aIx 27) 32 8 = true := by
  decide +kernel

theorem a7_27_40 : allFrom (a7Dat.rectI aIx 27) 40 8 = true := by
  decide +kernel

theorem a7_27_48 : allFrom (a7Dat.rectI aIx 27) 48 8 = true := by
  decide +kernel

theorem a7_27_56 : allFrom (a7Dat.rectI aIx 27) 56 8 = true := by
  decide +kernel

theorem a7_27_64 : allFrom (a7Dat.rectI aIx 27) 64 8 = true := by
  decide +kernel

theorem a7_27_72 : allFrom (a7Dat.rectI aIx 27) 72 8 = true := by
  decide +kernel

theorem a7_27_80 : allFrom (a7Dat.rectI aIx 27) 80 8 = true := by
  decide +kernel

theorem a7_27_88 : allFrom (a7Dat.rectI aIx 27) 88 8 = true := by
  decide +kernel

theorem a7_27_96 : allFrom (a7Dat.rectI aIx 27) 96 8 = true := by
  decide +kernel

theorem a7_27_104 : allFrom (a7Dat.rectI aIx 27) 104 8 = true := by
  decide +kernel

theorem a7_27_112 : allFrom (a7Dat.rectI aIx 27) 112 8 = true := by
  decide +kernel

theorem a7_27_120 : allFrom (a7Dat.rectI aIx 27) 120 8 = true := by
  decide +kernel

theorem a7_27_128 : allFrom (a7Dat.rectI aIx 27) 128 8 = true := by
  decide +kernel

theorem a7_row_27 : a7Dat.rowI aIx 27 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 27 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 27) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 27) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 27)) a7_27_0) a7_27_8) a7_27_16) a7_27_24) a7_27_32) a7_27_40) a7_27_48) a7_27_56) a7_27_64) a7_27_72) a7_27_80) a7_27_88) a7_27_96) a7_27_104) a7_27_112) a7_27_120) a7_27_128)

theorem a7_blk_24 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 24 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 24) a7_row_24 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 25) a7_row_25 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 26) a7_row_26 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 27) a7_row_27 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 28)))))

end SandierSerfaty.CertData.Box
