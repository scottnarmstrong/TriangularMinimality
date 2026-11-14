/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 1 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `4`–`7`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_4_0 : allFrom (a7Dat.rectI aIx 4) 0 8 = true := by
  decide +kernel

theorem a7_4_8 : allFrom (a7Dat.rectI aIx 4) 8 8 = true := by
  decide +kernel

theorem a7_4_16 : allFrom (a7Dat.rectI aIx 4) 16 8 = true := by
  decide +kernel

theorem a7_4_24 : allFrom (a7Dat.rectI aIx 4) 24 8 = true := by
  decide +kernel

theorem a7_4_32 : allFrom (a7Dat.rectI aIx 4) 32 8 = true := by
  decide +kernel

theorem a7_4_40 : allFrom (a7Dat.rectI aIx 4) 40 8 = true := by
  decide +kernel

theorem a7_4_48 : allFrom (a7Dat.rectI aIx 4) 48 8 = true := by
  decide +kernel

theorem a7_4_56 : allFrom (a7Dat.rectI aIx 4) 56 8 = true := by
  decide +kernel

theorem a7_4_64 : allFrom (a7Dat.rectI aIx 4) 64 8 = true := by
  decide +kernel

theorem a7_4_72 : allFrom (a7Dat.rectI aIx 4) 72 8 = true := by
  decide +kernel

theorem a7_4_80 : allFrom (a7Dat.rectI aIx 4) 80 8 = true := by
  decide +kernel

theorem a7_4_88 : allFrom (a7Dat.rectI aIx 4) 88 8 = true := by
  decide +kernel

theorem a7_4_96 : allFrom (a7Dat.rectI aIx 4) 96 8 = true := by
  decide +kernel

theorem a7_4_104 : allFrom (a7Dat.rectI aIx 4) 104 8 = true := by
  decide +kernel

theorem a7_4_112 : allFrom (a7Dat.rectI aIx 4) 112 8 = true := by
  decide +kernel

theorem a7_4_120 : allFrom (a7Dat.rectI aIx 4) 120 8 = true := by
  decide +kernel

theorem a7_4_128 : allFrom (a7Dat.rectI aIx 4) 128 8 = true := by
  decide +kernel

theorem a7_row_4 : a7Dat.rowI aIx 4 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 4 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 4) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 4) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 4)) a7_4_0) a7_4_8) a7_4_16) a7_4_24) a7_4_32) a7_4_40) a7_4_48) a7_4_56) a7_4_64) a7_4_72) a7_4_80) a7_4_88) a7_4_96) a7_4_104) a7_4_112) a7_4_120) a7_4_128)

theorem a7_5_0 : allFrom (a7Dat.rectI aIx 5) 0 8 = true := by
  decide +kernel

theorem a7_5_8 : allFrom (a7Dat.rectI aIx 5) 8 8 = true := by
  decide +kernel

theorem a7_5_16 : allFrom (a7Dat.rectI aIx 5) 16 8 = true := by
  decide +kernel

theorem a7_5_24 : allFrom (a7Dat.rectI aIx 5) 24 8 = true := by
  decide +kernel

theorem a7_5_32 : allFrom (a7Dat.rectI aIx 5) 32 8 = true := by
  decide +kernel

theorem a7_5_40 : allFrom (a7Dat.rectI aIx 5) 40 8 = true := by
  decide +kernel

theorem a7_5_48 : allFrom (a7Dat.rectI aIx 5) 48 8 = true := by
  decide +kernel

theorem a7_5_56 : allFrom (a7Dat.rectI aIx 5) 56 8 = true := by
  decide +kernel

theorem a7_5_64 : allFrom (a7Dat.rectI aIx 5) 64 8 = true := by
  decide +kernel

theorem a7_5_72 : allFrom (a7Dat.rectI aIx 5) 72 8 = true := by
  decide +kernel

theorem a7_5_80 : allFrom (a7Dat.rectI aIx 5) 80 8 = true := by
  decide +kernel

theorem a7_5_88 : allFrom (a7Dat.rectI aIx 5) 88 8 = true := by
  decide +kernel

theorem a7_5_96 : allFrom (a7Dat.rectI aIx 5) 96 8 = true := by
  decide +kernel

theorem a7_5_104 : allFrom (a7Dat.rectI aIx 5) 104 8 = true := by
  decide +kernel

theorem a7_5_112 : allFrom (a7Dat.rectI aIx 5) 112 8 = true := by
  decide +kernel

theorem a7_5_120 : allFrom (a7Dat.rectI aIx 5) 120 8 = true := by
  decide +kernel

theorem a7_5_128 : allFrom (a7Dat.rectI aIx 5) 128 8 = true := by
  decide +kernel

theorem a7_row_5 : a7Dat.rowI aIx 5 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 5 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 5) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 5) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 5)) a7_5_0) a7_5_8) a7_5_16) a7_5_24) a7_5_32) a7_5_40) a7_5_48) a7_5_56) a7_5_64) a7_5_72) a7_5_80) a7_5_88) a7_5_96) a7_5_104) a7_5_112) a7_5_120) a7_5_128)

theorem a7_6_0 : allFrom (a7Dat.rectI aIx 6) 0 8 = true := by
  decide +kernel

theorem a7_6_8 : allFrom (a7Dat.rectI aIx 6) 8 8 = true := by
  decide +kernel

theorem a7_6_16 : allFrom (a7Dat.rectI aIx 6) 16 8 = true := by
  decide +kernel

theorem a7_6_24 : allFrom (a7Dat.rectI aIx 6) 24 8 = true := by
  decide +kernel

theorem a7_6_32 : allFrom (a7Dat.rectI aIx 6) 32 8 = true := by
  decide +kernel

theorem a7_6_40 : allFrom (a7Dat.rectI aIx 6) 40 8 = true := by
  decide +kernel

theorem a7_6_48 : allFrom (a7Dat.rectI aIx 6) 48 8 = true := by
  decide +kernel

theorem a7_6_56 : allFrom (a7Dat.rectI aIx 6) 56 8 = true := by
  decide +kernel

theorem a7_6_64 : allFrom (a7Dat.rectI aIx 6) 64 8 = true := by
  decide +kernel

theorem a7_6_72 : allFrom (a7Dat.rectI aIx 6) 72 8 = true := by
  decide +kernel

theorem a7_6_80 : allFrom (a7Dat.rectI aIx 6) 80 8 = true := by
  decide +kernel

theorem a7_6_88 : allFrom (a7Dat.rectI aIx 6) 88 8 = true := by
  decide +kernel

theorem a7_6_96 : allFrom (a7Dat.rectI aIx 6) 96 8 = true := by
  decide +kernel

theorem a7_6_104 : allFrom (a7Dat.rectI aIx 6) 104 8 = true := by
  decide +kernel

theorem a7_6_112 : allFrom (a7Dat.rectI aIx 6) 112 8 = true := by
  decide +kernel

theorem a7_6_120 : allFrom (a7Dat.rectI aIx 6) 120 8 = true := by
  decide +kernel

theorem a7_6_128 : allFrom (a7Dat.rectI aIx 6) 128 8 = true := by
  decide +kernel

theorem a7_row_6 : a7Dat.rowI aIx 6 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 6 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 6) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 6) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 6)) a7_6_0) a7_6_8) a7_6_16) a7_6_24) a7_6_32) a7_6_40) a7_6_48) a7_6_56) a7_6_64) a7_6_72) a7_6_80) a7_6_88) a7_6_96) a7_6_104) a7_6_112) a7_6_120) a7_6_128)

theorem a7_7_0 : allFrom (a7Dat.rectI aIx 7) 0 8 = true := by
  decide +kernel

theorem a7_7_8 : allFrom (a7Dat.rectI aIx 7) 8 8 = true := by
  decide +kernel

theorem a7_7_16 : allFrom (a7Dat.rectI aIx 7) 16 8 = true := by
  decide +kernel

theorem a7_7_24 : allFrom (a7Dat.rectI aIx 7) 24 8 = true := by
  decide +kernel

theorem a7_7_32 : allFrom (a7Dat.rectI aIx 7) 32 8 = true := by
  decide +kernel

theorem a7_7_40 : allFrom (a7Dat.rectI aIx 7) 40 8 = true := by
  decide +kernel

theorem a7_7_48 : allFrom (a7Dat.rectI aIx 7) 48 8 = true := by
  decide +kernel

theorem a7_7_56 : allFrom (a7Dat.rectI aIx 7) 56 8 = true := by
  decide +kernel

theorem a7_7_64 : allFrom (a7Dat.rectI aIx 7) 64 8 = true := by
  decide +kernel

theorem a7_7_72 : allFrom (a7Dat.rectI aIx 7) 72 8 = true := by
  decide +kernel

theorem a7_7_80 : allFrom (a7Dat.rectI aIx 7) 80 8 = true := by
  decide +kernel

theorem a7_7_88 : allFrom (a7Dat.rectI aIx 7) 88 8 = true := by
  decide +kernel

theorem a7_7_96 : allFrom (a7Dat.rectI aIx 7) 96 8 = true := by
  decide +kernel

theorem a7_7_104 : allFrom (a7Dat.rectI aIx 7) 104 8 = true := by
  decide +kernel

theorem a7_7_112 : allFrom (a7Dat.rectI aIx 7) 112 8 = true := by
  decide +kernel

theorem a7_7_120 : allFrom (a7Dat.rectI aIx 7) 120 8 = true := by
  decide +kernel

theorem a7_7_128 : allFrom (a7Dat.rectI aIx 7) 128 8 = true := by
  decide +kernel

theorem a7_row_7 : a7Dat.rowI aIx 7 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 7 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 7) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 7) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 7)) a7_7_0) a7_7_8) a7_7_16) a7_7_24) a7_7_32) a7_7_40) a7_7_48) a7_7_56) a7_7_64) a7_7_72) a7_7_80) a7_7_88) a7_7_96) a7_7_104) a7_7_112) a7_7_120) a7_7_128)

theorem a7_blk_4 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 4 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 4) a7_row_4 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 5) a7_row_5 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 6) a7_row_6 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 7) a7_row_7 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 8)))))

end SandierSerfaty.CertData.Box
