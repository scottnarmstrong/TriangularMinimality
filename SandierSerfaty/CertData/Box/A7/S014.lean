/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 14 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `56`–`59`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_56_0 : allFrom (a7Dat.rectI aIx 56) 0 8 = true := by
  decide +kernel

theorem a7_56_8 : allFrom (a7Dat.rectI aIx 56) 8 8 = true := by
  decide +kernel

theorem a7_56_16 : allFrom (a7Dat.rectI aIx 56) 16 8 = true := by
  decide +kernel

theorem a7_56_24 : allFrom (a7Dat.rectI aIx 56) 24 8 = true := by
  decide +kernel

theorem a7_56_32 : allFrom (a7Dat.rectI aIx 56) 32 8 = true := by
  decide +kernel

theorem a7_56_40 : allFrom (a7Dat.rectI aIx 56) 40 8 = true := by
  decide +kernel

theorem a7_56_48 : allFrom (a7Dat.rectI aIx 56) 48 8 = true := by
  decide +kernel

theorem a7_56_56 : allFrom (a7Dat.rectI aIx 56) 56 8 = true := by
  decide +kernel

theorem a7_56_64 : allFrom (a7Dat.rectI aIx 56) 64 8 = true := by
  decide +kernel

theorem a7_56_72 : allFrom (a7Dat.rectI aIx 56) 72 8 = true := by
  decide +kernel

theorem a7_56_80 : allFrom (a7Dat.rectI aIx 56) 80 8 = true := by
  decide +kernel

theorem a7_56_88 : allFrom (a7Dat.rectI aIx 56) 88 8 = true := by
  decide +kernel

theorem a7_56_96 : allFrom (a7Dat.rectI aIx 56) 96 8 = true := by
  decide +kernel

theorem a7_56_104 : allFrom (a7Dat.rectI aIx 56) 104 8 = true := by
  decide +kernel

theorem a7_56_112 : allFrom (a7Dat.rectI aIx 56) 112 8 = true := by
  decide +kernel

theorem a7_56_120 : allFrom (a7Dat.rectI aIx 56) 120 8 = true := by
  decide +kernel

theorem a7_56_128 : allFrom (a7Dat.rectI aIx 56) 128 8 = true := by
  decide +kernel

theorem a7_row_56 : a7Dat.rowI aIx 56 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 56 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 56) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 56) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 56)) a7_56_0) a7_56_8) a7_56_16) a7_56_24) a7_56_32) a7_56_40) a7_56_48) a7_56_56) a7_56_64) a7_56_72) a7_56_80) a7_56_88) a7_56_96) a7_56_104) a7_56_112) a7_56_120) a7_56_128)

theorem a7_57_0 : allFrom (a7Dat.rectI aIx 57) 0 8 = true := by
  decide +kernel

theorem a7_57_8 : allFrom (a7Dat.rectI aIx 57) 8 8 = true := by
  decide +kernel

theorem a7_57_16 : allFrom (a7Dat.rectI aIx 57) 16 8 = true := by
  decide +kernel

theorem a7_57_24 : allFrom (a7Dat.rectI aIx 57) 24 8 = true := by
  decide +kernel

theorem a7_57_32 : allFrom (a7Dat.rectI aIx 57) 32 8 = true := by
  decide +kernel

theorem a7_57_40 : allFrom (a7Dat.rectI aIx 57) 40 8 = true := by
  decide +kernel

theorem a7_57_48 : allFrom (a7Dat.rectI aIx 57) 48 8 = true := by
  decide +kernel

theorem a7_57_56 : allFrom (a7Dat.rectI aIx 57) 56 8 = true := by
  decide +kernel

theorem a7_57_64 : allFrom (a7Dat.rectI aIx 57) 64 8 = true := by
  decide +kernel

theorem a7_57_72 : allFrom (a7Dat.rectI aIx 57) 72 8 = true := by
  decide +kernel

theorem a7_57_80 : allFrom (a7Dat.rectI aIx 57) 80 8 = true := by
  decide +kernel

theorem a7_57_88 : allFrom (a7Dat.rectI aIx 57) 88 8 = true := by
  decide +kernel

theorem a7_57_96 : allFrom (a7Dat.rectI aIx 57) 96 8 = true := by
  decide +kernel

theorem a7_57_104 : allFrom (a7Dat.rectI aIx 57) 104 8 = true := by
  decide +kernel

theorem a7_57_112 : allFrom (a7Dat.rectI aIx 57) 112 8 = true := by
  decide +kernel

theorem a7_57_120 : allFrom (a7Dat.rectI aIx 57) 120 8 = true := by
  decide +kernel

theorem a7_57_128 : allFrom (a7Dat.rectI aIx 57) 128 8 = true := by
  decide +kernel

theorem a7_row_57 : a7Dat.rowI aIx 57 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 57 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 57) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 57) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 57)) a7_57_0) a7_57_8) a7_57_16) a7_57_24) a7_57_32) a7_57_40) a7_57_48) a7_57_56) a7_57_64) a7_57_72) a7_57_80) a7_57_88) a7_57_96) a7_57_104) a7_57_112) a7_57_120) a7_57_128)

theorem a7_58_0 : allFrom (a7Dat.rectI aIx 58) 0 8 = true := by
  decide +kernel

theorem a7_58_8 : allFrom (a7Dat.rectI aIx 58) 8 8 = true := by
  decide +kernel

theorem a7_58_16 : allFrom (a7Dat.rectI aIx 58) 16 8 = true := by
  decide +kernel

theorem a7_58_24 : allFrom (a7Dat.rectI aIx 58) 24 8 = true := by
  decide +kernel

theorem a7_58_32 : allFrom (a7Dat.rectI aIx 58) 32 8 = true := by
  decide +kernel

theorem a7_58_40 : allFrom (a7Dat.rectI aIx 58) 40 8 = true := by
  decide +kernel

theorem a7_58_48 : allFrom (a7Dat.rectI aIx 58) 48 8 = true := by
  decide +kernel

theorem a7_58_56 : allFrom (a7Dat.rectI aIx 58) 56 8 = true := by
  decide +kernel

theorem a7_58_64 : allFrom (a7Dat.rectI aIx 58) 64 8 = true := by
  decide +kernel

theorem a7_58_72 : allFrom (a7Dat.rectI aIx 58) 72 8 = true := by
  decide +kernel

theorem a7_58_80 : allFrom (a7Dat.rectI aIx 58) 80 8 = true := by
  decide +kernel

theorem a7_58_88 : allFrom (a7Dat.rectI aIx 58) 88 8 = true := by
  decide +kernel

theorem a7_58_96 : allFrom (a7Dat.rectI aIx 58) 96 8 = true := by
  decide +kernel

theorem a7_58_104 : allFrom (a7Dat.rectI aIx 58) 104 8 = true := by
  decide +kernel

theorem a7_58_112 : allFrom (a7Dat.rectI aIx 58) 112 8 = true := by
  decide +kernel

theorem a7_58_120 : allFrom (a7Dat.rectI aIx 58) 120 8 = true := by
  decide +kernel

theorem a7_58_128 : allFrom (a7Dat.rectI aIx 58) 128 8 = true := by
  decide +kernel

theorem a7_row_58 : a7Dat.rowI aIx 58 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 58 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 58) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 58) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 58)) a7_58_0) a7_58_8) a7_58_16) a7_58_24) a7_58_32) a7_58_40) a7_58_48) a7_58_56) a7_58_64) a7_58_72) a7_58_80) a7_58_88) a7_58_96) a7_58_104) a7_58_112) a7_58_120) a7_58_128)

theorem a7_59_0 : allFrom (a7Dat.rectI aIx 59) 0 8 = true := by
  decide +kernel

theorem a7_59_8 : allFrom (a7Dat.rectI aIx 59) 8 8 = true := by
  decide +kernel

theorem a7_59_16 : allFrom (a7Dat.rectI aIx 59) 16 8 = true := by
  decide +kernel

theorem a7_59_24 : allFrom (a7Dat.rectI aIx 59) 24 8 = true := by
  decide +kernel

theorem a7_59_32 : allFrom (a7Dat.rectI aIx 59) 32 8 = true := by
  decide +kernel

theorem a7_59_40 : allFrom (a7Dat.rectI aIx 59) 40 8 = true := by
  decide +kernel

theorem a7_59_48 : allFrom (a7Dat.rectI aIx 59) 48 8 = true := by
  decide +kernel

theorem a7_59_56 : allFrom (a7Dat.rectI aIx 59) 56 8 = true := by
  decide +kernel

theorem a7_59_64 : allFrom (a7Dat.rectI aIx 59) 64 8 = true := by
  decide +kernel

theorem a7_59_72 : allFrom (a7Dat.rectI aIx 59) 72 8 = true := by
  decide +kernel

theorem a7_59_80 : allFrom (a7Dat.rectI aIx 59) 80 8 = true := by
  decide +kernel

theorem a7_59_88 : allFrom (a7Dat.rectI aIx 59) 88 8 = true := by
  decide +kernel

theorem a7_59_96 : allFrom (a7Dat.rectI aIx 59) 96 8 = true := by
  decide +kernel

theorem a7_59_104 : allFrom (a7Dat.rectI aIx 59) 104 8 = true := by
  decide +kernel

theorem a7_59_112 : allFrom (a7Dat.rectI aIx 59) 112 8 = true := by
  decide +kernel

theorem a7_59_120 : allFrom (a7Dat.rectI aIx 59) 120 8 = true := by
  decide +kernel

theorem a7_59_128 : allFrom (a7Dat.rectI aIx 59) 128 8 = true := by
  decide +kernel

theorem a7_row_59 : a7Dat.rowI aIx 59 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 59 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 59) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 59) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 59)) a7_59_0) a7_59_8) a7_59_16) a7_59_24) a7_59_32) a7_59_40) a7_59_48) a7_59_56) a7_59_64) a7_59_72) a7_59_80) a7_59_88) a7_59_96) a7_59_104) a7_59_112) a7_59_120) a7_59_128)

theorem a7_blk_56 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 56 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 56) a7_row_56 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 57) a7_row_57 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 58) a7_row_58 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 59) a7_row_59 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 60)))))

end SandierSerfaty.CertData.Box
