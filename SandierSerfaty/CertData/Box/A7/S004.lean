/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 4 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `16`–`19`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_16_0 : allFrom (a7Dat.rectI aIx 16) 0 8 = true := by
  decide +kernel

theorem a7_16_8 : allFrom (a7Dat.rectI aIx 16) 8 8 = true := by
  decide +kernel

theorem a7_16_16 : allFrom (a7Dat.rectI aIx 16) 16 8 = true := by
  decide +kernel

theorem a7_16_24 : allFrom (a7Dat.rectI aIx 16) 24 8 = true := by
  decide +kernel

theorem a7_16_32 : allFrom (a7Dat.rectI aIx 16) 32 8 = true := by
  decide +kernel

theorem a7_16_40 : allFrom (a7Dat.rectI aIx 16) 40 8 = true := by
  decide +kernel

theorem a7_16_48 : allFrom (a7Dat.rectI aIx 16) 48 8 = true := by
  decide +kernel

theorem a7_16_56 : allFrom (a7Dat.rectI aIx 16) 56 8 = true := by
  decide +kernel

theorem a7_16_64 : allFrom (a7Dat.rectI aIx 16) 64 8 = true := by
  decide +kernel

theorem a7_16_72 : allFrom (a7Dat.rectI aIx 16) 72 8 = true := by
  decide +kernel

theorem a7_16_80 : allFrom (a7Dat.rectI aIx 16) 80 8 = true := by
  decide +kernel

theorem a7_16_88 : allFrom (a7Dat.rectI aIx 16) 88 8 = true := by
  decide +kernel

theorem a7_16_96 : allFrom (a7Dat.rectI aIx 16) 96 8 = true := by
  decide +kernel

theorem a7_16_104 : allFrom (a7Dat.rectI aIx 16) 104 8 = true := by
  decide +kernel

theorem a7_16_112 : allFrom (a7Dat.rectI aIx 16) 112 8 = true := by
  decide +kernel

theorem a7_16_120 : allFrom (a7Dat.rectI aIx 16) 120 8 = true := by
  decide +kernel

theorem a7_16_128 : allFrom (a7Dat.rectI aIx 16) 128 8 = true := by
  decide +kernel

theorem a7_row_16 : a7Dat.rowI aIx 16 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 16 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 16) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 16) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 16)) a7_16_0) a7_16_8) a7_16_16) a7_16_24) a7_16_32) a7_16_40) a7_16_48) a7_16_56) a7_16_64) a7_16_72) a7_16_80) a7_16_88) a7_16_96) a7_16_104) a7_16_112) a7_16_120) a7_16_128)

theorem a7_17_0 : allFrom (a7Dat.rectI aIx 17) 0 8 = true := by
  decide +kernel

theorem a7_17_8 : allFrom (a7Dat.rectI aIx 17) 8 8 = true := by
  decide +kernel

theorem a7_17_16 : allFrom (a7Dat.rectI aIx 17) 16 8 = true := by
  decide +kernel

theorem a7_17_24 : allFrom (a7Dat.rectI aIx 17) 24 8 = true := by
  decide +kernel

theorem a7_17_32 : allFrom (a7Dat.rectI aIx 17) 32 8 = true := by
  decide +kernel

theorem a7_17_40 : allFrom (a7Dat.rectI aIx 17) 40 8 = true := by
  decide +kernel

theorem a7_17_48 : allFrom (a7Dat.rectI aIx 17) 48 8 = true := by
  decide +kernel

theorem a7_17_56 : allFrom (a7Dat.rectI aIx 17) 56 8 = true := by
  decide +kernel

theorem a7_17_64 : allFrom (a7Dat.rectI aIx 17) 64 8 = true := by
  decide +kernel

theorem a7_17_72 : allFrom (a7Dat.rectI aIx 17) 72 8 = true := by
  decide +kernel

theorem a7_17_80 : allFrom (a7Dat.rectI aIx 17) 80 8 = true := by
  decide +kernel

theorem a7_17_88 : allFrom (a7Dat.rectI aIx 17) 88 8 = true := by
  decide +kernel

theorem a7_17_96 : allFrom (a7Dat.rectI aIx 17) 96 8 = true := by
  decide +kernel

theorem a7_17_104 : allFrom (a7Dat.rectI aIx 17) 104 8 = true := by
  decide +kernel

theorem a7_17_112 : allFrom (a7Dat.rectI aIx 17) 112 8 = true := by
  decide +kernel

theorem a7_17_120 : allFrom (a7Dat.rectI aIx 17) 120 8 = true := by
  decide +kernel

theorem a7_17_128 : allFrom (a7Dat.rectI aIx 17) 128 8 = true := by
  decide +kernel

theorem a7_row_17 : a7Dat.rowI aIx 17 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 17 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 17) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 17) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 17)) a7_17_0) a7_17_8) a7_17_16) a7_17_24) a7_17_32) a7_17_40) a7_17_48) a7_17_56) a7_17_64) a7_17_72) a7_17_80) a7_17_88) a7_17_96) a7_17_104) a7_17_112) a7_17_120) a7_17_128)

theorem a7_18_0 : allFrom (a7Dat.rectI aIx 18) 0 8 = true := by
  decide +kernel

theorem a7_18_8 : allFrom (a7Dat.rectI aIx 18) 8 8 = true := by
  decide +kernel

theorem a7_18_16 : allFrom (a7Dat.rectI aIx 18) 16 8 = true := by
  decide +kernel

theorem a7_18_24 : allFrom (a7Dat.rectI aIx 18) 24 8 = true := by
  decide +kernel

theorem a7_18_32 : allFrom (a7Dat.rectI aIx 18) 32 8 = true := by
  decide +kernel

theorem a7_18_40 : allFrom (a7Dat.rectI aIx 18) 40 8 = true := by
  decide +kernel

theorem a7_18_48 : allFrom (a7Dat.rectI aIx 18) 48 8 = true := by
  decide +kernel

theorem a7_18_56 : allFrom (a7Dat.rectI aIx 18) 56 8 = true := by
  decide +kernel

theorem a7_18_64 : allFrom (a7Dat.rectI aIx 18) 64 8 = true := by
  decide +kernel

theorem a7_18_72 : allFrom (a7Dat.rectI aIx 18) 72 8 = true := by
  decide +kernel

theorem a7_18_80 : allFrom (a7Dat.rectI aIx 18) 80 8 = true := by
  decide +kernel

theorem a7_18_88 : allFrom (a7Dat.rectI aIx 18) 88 8 = true := by
  decide +kernel

theorem a7_18_96 : allFrom (a7Dat.rectI aIx 18) 96 8 = true := by
  decide +kernel

theorem a7_18_104 : allFrom (a7Dat.rectI aIx 18) 104 8 = true := by
  decide +kernel

theorem a7_18_112 : allFrom (a7Dat.rectI aIx 18) 112 8 = true := by
  decide +kernel

theorem a7_18_120 : allFrom (a7Dat.rectI aIx 18) 120 8 = true := by
  decide +kernel

theorem a7_18_128 : allFrom (a7Dat.rectI aIx 18) 128 8 = true := by
  decide +kernel

theorem a7_row_18 : a7Dat.rowI aIx 18 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 18 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 18) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 18) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 18)) a7_18_0) a7_18_8) a7_18_16) a7_18_24) a7_18_32) a7_18_40) a7_18_48) a7_18_56) a7_18_64) a7_18_72) a7_18_80) a7_18_88) a7_18_96) a7_18_104) a7_18_112) a7_18_120) a7_18_128)

theorem a7_19_0 : allFrom (a7Dat.rectI aIx 19) 0 8 = true := by
  decide +kernel

theorem a7_19_8 : allFrom (a7Dat.rectI aIx 19) 8 8 = true := by
  decide +kernel

theorem a7_19_16 : allFrom (a7Dat.rectI aIx 19) 16 8 = true := by
  decide +kernel

theorem a7_19_24 : allFrom (a7Dat.rectI aIx 19) 24 8 = true := by
  decide +kernel

theorem a7_19_32 : allFrom (a7Dat.rectI aIx 19) 32 8 = true := by
  decide +kernel

theorem a7_19_40 : allFrom (a7Dat.rectI aIx 19) 40 8 = true := by
  decide +kernel

theorem a7_19_48 : allFrom (a7Dat.rectI aIx 19) 48 8 = true := by
  decide +kernel

theorem a7_19_56 : allFrom (a7Dat.rectI aIx 19) 56 8 = true := by
  decide +kernel

theorem a7_19_64 : allFrom (a7Dat.rectI aIx 19) 64 8 = true := by
  decide +kernel

theorem a7_19_72 : allFrom (a7Dat.rectI aIx 19) 72 8 = true := by
  decide +kernel

theorem a7_19_80 : allFrom (a7Dat.rectI aIx 19) 80 8 = true := by
  decide +kernel

theorem a7_19_88 : allFrom (a7Dat.rectI aIx 19) 88 8 = true := by
  decide +kernel

theorem a7_19_96 : allFrom (a7Dat.rectI aIx 19) 96 8 = true := by
  decide +kernel

theorem a7_19_104 : allFrom (a7Dat.rectI aIx 19) 104 8 = true := by
  decide +kernel

theorem a7_19_112 : allFrom (a7Dat.rectI aIx 19) 112 8 = true := by
  decide +kernel

theorem a7_19_120 : allFrom (a7Dat.rectI aIx 19) 120 8 = true := by
  decide +kernel

theorem a7_19_128 : allFrom (a7Dat.rectI aIx 19) 128 8 = true := by
  decide +kernel

theorem a7_row_19 : a7Dat.rowI aIx 19 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 19 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 19) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 19) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 19)) a7_19_0) a7_19_8) a7_19_16) a7_19_24) a7_19_32) a7_19_40) a7_19_48) a7_19_56) a7_19_64) a7_19_72) a7_19_80) a7_19_88) a7_19_96) a7_19_104) a7_19_112) a7_19_120) a7_19_128)

theorem a7_blk_16 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 16 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 16) a7_row_16 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 17) a7_row_17 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 18) a7_row_18 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 19) a7_row_19 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 20)))))

end SandierSerfaty.CertData.Box
