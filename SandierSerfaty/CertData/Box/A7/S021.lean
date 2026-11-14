/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 21 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `84`–`86`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_84_0 : allFrom (a7Dat.rectI aIx 84) 0 8 = true := by
  decide +kernel

theorem a7_84_8 : allFrom (a7Dat.rectI aIx 84) 8 8 = true := by
  decide +kernel

theorem a7_84_16 : allFrom (a7Dat.rectI aIx 84) 16 8 = true := by
  decide +kernel

theorem a7_84_24 : allFrom (a7Dat.rectI aIx 84) 24 8 = true := by
  decide +kernel

theorem a7_84_32 : allFrom (a7Dat.rectI aIx 84) 32 8 = true := by
  decide +kernel

theorem a7_84_40 : allFrom (a7Dat.rectI aIx 84) 40 8 = true := by
  decide +kernel

theorem a7_84_48 : allFrom (a7Dat.rectI aIx 84) 48 8 = true := by
  decide +kernel

theorem a7_84_56 : allFrom (a7Dat.rectI aIx 84) 56 8 = true := by
  decide +kernel

theorem a7_84_64 : allFrom (a7Dat.rectI aIx 84) 64 8 = true := by
  decide +kernel

theorem a7_84_72 : allFrom (a7Dat.rectI aIx 84) 72 8 = true := by
  decide +kernel

theorem a7_84_80 : allFrom (a7Dat.rectI aIx 84) 80 8 = true := by
  decide +kernel

theorem a7_84_88 : allFrom (a7Dat.rectI aIx 84) 88 8 = true := by
  decide +kernel

theorem a7_84_96 : allFrom (a7Dat.rectI aIx 84) 96 8 = true := by
  decide +kernel

theorem a7_84_104 : allFrom (a7Dat.rectI aIx 84) 104 8 = true := by
  decide +kernel

theorem a7_84_112 : allFrom (a7Dat.rectI aIx 84) 112 8 = true := by
  decide +kernel

theorem a7_84_120 : allFrom (a7Dat.rectI aIx 84) 120 8 = true := by
  decide +kernel

theorem a7_84_128 : allFrom (a7Dat.rectI aIx 84) 128 8 = true := by
  decide +kernel

theorem a7_row_84 : a7Dat.rowI aIx 84 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 84 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 84) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 84) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 84)) a7_84_0) a7_84_8) a7_84_16) a7_84_24) a7_84_32) a7_84_40) a7_84_48) a7_84_56) a7_84_64) a7_84_72) a7_84_80) a7_84_88) a7_84_96) a7_84_104) a7_84_112) a7_84_120) a7_84_128)

theorem a7_85_0 : allFrom (a7Dat.rectI aIx 85) 0 8 = true := by
  decide +kernel

theorem a7_85_8 : allFrom (a7Dat.rectI aIx 85) 8 8 = true := by
  decide +kernel

theorem a7_85_16 : allFrom (a7Dat.rectI aIx 85) 16 8 = true := by
  decide +kernel

theorem a7_85_24 : allFrom (a7Dat.rectI aIx 85) 24 8 = true := by
  decide +kernel

theorem a7_85_32 : allFrom (a7Dat.rectI aIx 85) 32 8 = true := by
  decide +kernel

theorem a7_85_40 : allFrom (a7Dat.rectI aIx 85) 40 8 = true := by
  decide +kernel

theorem a7_85_48 : allFrom (a7Dat.rectI aIx 85) 48 8 = true := by
  decide +kernel

theorem a7_85_56 : allFrom (a7Dat.rectI aIx 85) 56 8 = true := by
  decide +kernel

theorem a7_85_64 : allFrom (a7Dat.rectI aIx 85) 64 8 = true := by
  decide +kernel

theorem a7_85_72 : allFrom (a7Dat.rectI aIx 85) 72 8 = true := by
  decide +kernel

theorem a7_85_80 : allFrom (a7Dat.rectI aIx 85) 80 8 = true := by
  decide +kernel

theorem a7_85_88 : allFrom (a7Dat.rectI aIx 85) 88 8 = true := by
  decide +kernel

theorem a7_85_96 : allFrom (a7Dat.rectI aIx 85) 96 8 = true := by
  decide +kernel

theorem a7_85_104 : allFrom (a7Dat.rectI aIx 85) 104 8 = true := by
  decide +kernel

theorem a7_85_112 : allFrom (a7Dat.rectI aIx 85) 112 8 = true := by
  decide +kernel

theorem a7_85_120 : allFrom (a7Dat.rectI aIx 85) 120 8 = true := by
  decide +kernel

theorem a7_85_128 : allFrom (a7Dat.rectI aIx 85) 128 8 = true := by
  decide +kernel

theorem a7_row_85 : a7Dat.rowI aIx 85 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 85 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 85) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 85) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 85)) a7_85_0) a7_85_8) a7_85_16) a7_85_24) a7_85_32) a7_85_40) a7_85_48) a7_85_56) a7_85_64) a7_85_72) a7_85_80) a7_85_88) a7_85_96) a7_85_104) a7_85_112) a7_85_120) a7_85_128)

theorem a7_86_0 : allFrom (a7Dat.rectI aIx 86) 0 8 = true := by
  decide +kernel

theorem a7_86_8 : allFrom (a7Dat.rectI aIx 86) 8 8 = true := by
  decide +kernel

theorem a7_86_16 : allFrom (a7Dat.rectI aIx 86) 16 8 = true := by
  decide +kernel

theorem a7_86_24 : allFrom (a7Dat.rectI aIx 86) 24 8 = true := by
  decide +kernel

theorem a7_86_32 : allFrom (a7Dat.rectI aIx 86) 32 8 = true := by
  decide +kernel

theorem a7_86_40 : allFrom (a7Dat.rectI aIx 86) 40 8 = true := by
  decide +kernel

theorem a7_86_48 : allFrom (a7Dat.rectI aIx 86) 48 8 = true := by
  decide +kernel

theorem a7_86_56 : allFrom (a7Dat.rectI aIx 86) 56 8 = true := by
  decide +kernel

theorem a7_86_64 : allFrom (a7Dat.rectI aIx 86) 64 8 = true := by
  decide +kernel

theorem a7_86_72 : allFrom (a7Dat.rectI aIx 86) 72 8 = true := by
  decide +kernel

theorem a7_86_80 : allFrom (a7Dat.rectI aIx 86) 80 8 = true := by
  decide +kernel

theorem a7_86_88 : allFrom (a7Dat.rectI aIx 86) 88 8 = true := by
  decide +kernel

theorem a7_86_96 : allFrom (a7Dat.rectI aIx 86) 96 8 = true := by
  decide +kernel

theorem a7_86_104 : allFrom (a7Dat.rectI aIx 86) 104 8 = true := by
  decide +kernel

theorem a7_86_112 : allFrom (a7Dat.rectI aIx 86) 112 8 = true := by
  decide +kernel

theorem a7_86_120 : allFrom (a7Dat.rectI aIx 86) 120 8 = true := by
  decide +kernel

theorem a7_86_128 : allFrom (a7Dat.rectI aIx 86) 128 8 = true := by
  decide +kernel

theorem a7_row_86 : a7Dat.rowI aIx 86 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 86 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 86) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 86) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 86)) a7_86_0) a7_86_8) a7_86_16) a7_86_24) a7_86_32) a7_86_40) a7_86_48) a7_86_56) a7_86_64) a7_86_72) a7_86_80) a7_86_88) a7_86_96) a7_86_104) a7_86_112) a7_86_120) a7_86_128)

theorem a7_blk_84 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 84 3 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 84) a7_row_84 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 85) a7_row_85 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 86) a7_row_86 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 87))))

end SandierSerfaty.CertData.Box
