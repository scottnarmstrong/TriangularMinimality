/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 8 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `32`–`35`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_32_0 : allFrom (a7Dat.rectI aIx 32) 0 8 = true := by
  decide +kernel

theorem a7_32_8 : allFrom (a7Dat.rectI aIx 32) 8 8 = true := by
  decide +kernel

theorem a7_32_16 : allFrom (a7Dat.rectI aIx 32) 16 8 = true := by
  decide +kernel

theorem a7_32_24 : allFrom (a7Dat.rectI aIx 32) 24 8 = true := by
  decide +kernel

theorem a7_32_32 : allFrom (a7Dat.rectI aIx 32) 32 8 = true := by
  decide +kernel

theorem a7_32_40 : allFrom (a7Dat.rectI aIx 32) 40 8 = true := by
  decide +kernel

theorem a7_32_48 : allFrom (a7Dat.rectI aIx 32) 48 8 = true := by
  decide +kernel

theorem a7_32_56 : allFrom (a7Dat.rectI aIx 32) 56 8 = true := by
  decide +kernel

theorem a7_32_64 : allFrom (a7Dat.rectI aIx 32) 64 8 = true := by
  decide +kernel

theorem a7_32_72 : allFrom (a7Dat.rectI aIx 32) 72 8 = true := by
  decide +kernel

theorem a7_32_80 : allFrom (a7Dat.rectI aIx 32) 80 8 = true := by
  decide +kernel

theorem a7_32_88 : allFrom (a7Dat.rectI aIx 32) 88 8 = true := by
  decide +kernel

theorem a7_32_96 : allFrom (a7Dat.rectI aIx 32) 96 8 = true := by
  decide +kernel

theorem a7_32_104 : allFrom (a7Dat.rectI aIx 32) 104 8 = true := by
  decide +kernel

theorem a7_32_112 : allFrom (a7Dat.rectI aIx 32) 112 8 = true := by
  decide +kernel

theorem a7_32_120 : allFrom (a7Dat.rectI aIx 32) 120 8 = true := by
  decide +kernel

theorem a7_32_128 : allFrom (a7Dat.rectI aIx 32) 128 8 = true := by
  decide +kernel

theorem a7_row_32 : a7Dat.rowI aIx 32 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 32 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 32) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 32) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 32)) a7_32_0) a7_32_8) a7_32_16) a7_32_24) a7_32_32) a7_32_40) a7_32_48) a7_32_56) a7_32_64) a7_32_72) a7_32_80) a7_32_88) a7_32_96) a7_32_104) a7_32_112) a7_32_120) a7_32_128)

theorem a7_33_0 : allFrom (a7Dat.rectI aIx 33) 0 8 = true := by
  decide +kernel

theorem a7_33_8 : allFrom (a7Dat.rectI aIx 33) 8 8 = true := by
  decide +kernel

theorem a7_33_16 : allFrom (a7Dat.rectI aIx 33) 16 8 = true := by
  decide +kernel

theorem a7_33_24 : allFrom (a7Dat.rectI aIx 33) 24 8 = true := by
  decide +kernel

theorem a7_33_32 : allFrom (a7Dat.rectI aIx 33) 32 8 = true := by
  decide +kernel

theorem a7_33_40 : allFrom (a7Dat.rectI aIx 33) 40 8 = true := by
  decide +kernel

theorem a7_33_48 : allFrom (a7Dat.rectI aIx 33) 48 8 = true := by
  decide +kernel

theorem a7_33_56 : allFrom (a7Dat.rectI aIx 33) 56 8 = true := by
  decide +kernel

theorem a7_33_64 : allFrom (a7Dat.rectI aIx 33) 64 8 = true := by
  decide +kernel

theorem a7_33_72 : allFrom (a7Dat.rectI aIx 33) 72 8 = true := by
  decide +kernel

theorem a7_33_80 : allFrom (a7Dat.rectI aIx 33) 80 8 = true := by
  decide +kernel

theorem a7_33_88 : allFrom (a7Dat.rectI aIx 33) 88 8 = true := by
  decide +kernel

theorem a7_33_96 : allFrom (a7Dat.rectI aIx 33) 96 8 = true := by
  decide +kernel

theorem a7_33_104 : allFrom (a7Dat.rectI aIx 33) 104 8 = true := by
  decide +kernel

theorem a7_33_112 : allFrom (a7Dat.rectI aIx 33) 112 8 = true := by
  decide +kernel

theorem a7_33_120 : allFrom (a7Dat.rectI aIx 33) 120 8 = true := by
  decide +kernel

theorem a7_33_128 : allFrom (a7Dat.rectI aIx 33) 128 8 = true := by
  decide +kernel

theorem a7_row_33 : a7Dat.rowI aIx 33 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 33 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 33) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 33) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 33)) a7_33_0) a7_33_8) a7_33_16) a7_33_24) a7_33_32) a7_33_40) a7_33_48) a7_33_56) a7_33_64) a7_33_72) a7_33_80) a7_33_88) a7_33_96) a7_33_104) a7_33_112) a7_33_120) a7_33_128)

theorem a7_34_0 : allFrom (a7Dat.rectI aIx 34) 0 8 = true := by
  decide +kernel

theorem a7_34_8 : allFrom (a7Dat.rectI aIx 34) 8 8 = true := by
  decide +kernel

theorem a7_34_16 : allFrom (a7Dat.rectI aIx 34) 16 8 = true := by
  decide +kernel

theorem a7_34_24 : allFrom (a7Dat.rectI aIx 34) 24 8 = true := by
  decide +kernel

theorem a7_34_32 : allFrom (a7Dat.rectI aIx 34) 32 8 = true := by
  decide +kernel

theorem a7_34_40 : allFrom (a7Dat.rectI aIx 34) 40 8 = true := by
  decide +kernel

theorem a7_34_48 : allFrom (a7Dat.rectI aIx 34) 48 8 = true := by
  decide +kernel

theorem a7_34_56 : allFrom (a7Dat.rectI aIx 34) 56 8 = true := by
  decide +kernel

theorem a7_34_64 : allFrom (a7Dat.rectI aIx 34) 64 8 = true := by
  decide +kernel

theorem a7_34_72 : allFrom (a7Dat.rectI aIx 34) 72 8 = true := by
  decide +kernel

theorem a7_34_80 : allFrom (a7Dat.rectI aIx 34) 80 8 = true := by
  decide +kernel

theorem a7_34_88 : allFrom (a7Dat.rectI aIx 34) 88 8 = true := by
  decide +kernel

theorem a7_34_96 : allFrom (a7Dat.rectI aIx 34) 96 8 = true := by
  decide +kernel

theorem a7_34_104 : allFrom (a7Dat.rectI aIx 34) 104 8 = true := by
  decide +kernel

theorem a7_34_112 : allFrom (a7Dat.rectI aIx 34) 112 8 = true := by
  decide +kernel

theorem a7_34_120 : allFrom (a7Dat.rectI aIx 34) 120 8 = true := by
  decide +kernel

theorem a7_34_128 : allFrom (a7Dat.rectI aIx 34) 128 8 = true := by
  decide +kernel

theorem a7_row_34 : a7Dat.rowI aIx 34 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 34 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 34) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 34) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 34)) a7_34_0) a7_34_8) a7_34_16) a7_34_24) a7_34_32) a7_34_40) a7_34_48) a7_34_56) a7_34_64) a7_34_72) a7_34_80) a7_34_88) a7_34_96) a7_34_104) a7_34_112) a7_34_120) a7_34_128)

theorem a7_35_0 : allFrom (a7Dat.rectI aIx 35) 0 8 = true := by
  decide +kernel

theorem a7_35_8 : allFrom (a7Dat.rectI aIx 35) 8 8 = true := by
  decide +kernel

theorem a7_35_16 : allFrom (a7Dat.rectI aIx 35) 16 8 = true := by
  decide +kernel

theorem a7_35_24 : allFrom (a7Dat.rectI aIx 35) 24 8 = true := by
  decide +kernel

theorem a7_35_32 : allFrom (a7Dat.rectI aIx 35) 32 8 = true := by
  decide +kernel

theorem a7_35_40 : allFrom (a7Dat.rectI aIx 35) 40 8 = true := by
  decide +kernel

theorem a7_35_48 : allFrom (a7Dat.rectI aIx 35) 48 8 = true := by
  decide +kernel

theorem a7_35_56 : allFrom (a7Dat.rectI aIx 35) 56 8 = true := by
  decide +kernel

theorem a7_35_64 : allFrom (a7Dat.rectI aIx 35) 64 8 = true := by
  decide +kernel

theorem a7_35_72 : allFrom (a7Dat.rectI aIx 35) 72 8 = true := by
  decide +kernel

theorem a7_35_80 : allFrom (a7Dat.rectI aIx 35) 80 8 = true := by
  decide +kernel

theorem a7_35_88 : allFrom (a7Dat.rectI aIx 35) 88 8 = true := by
  decide +kernel

theorem a7_35_96 : allFrom (a7Dat.rectI aIx 35) 96 8 = true := by
  decide +kernel

theorem a7_35_104 : allFrom (a7Dat.rectI aIx 35) 104 8 = true := by
  decide +kernel

theorem a7_35_112 : allFrom (a7Dat.rectI aIx 35) 112 8 = true := by
  decide +kernel

theorem a7_35_120 : allFrom (a7Dat.rectI aIx 35) 120 8 = true := by
  decide +kernel

theorem a7_35_128 : allFrom (a7Dat.rectI aIx 35) 128 8 = true := by
  decide +kernel

theorem a7_row_35 : a7Dat.rowI aIx 35 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 35 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 35) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 35) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 35)) a7_35_0) a7_35_8) a7_35_16) a7_35_24) a7_35_32) a7_35_40) a7_35_48) a7_35_56) a7_35_64) a7_35_72) a7_35_80) a7_35_88) a7_35_96) a7_35_104) a7_35_112) a7_35_120) a7_35_128)

theorem a7_blk_32 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 32 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 32) a7_row_32 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 33) a7_row_33 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 34) a7_row_34 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 35) a7_row_35 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 36)))))

end SandierSerfaty.CertData.Box
