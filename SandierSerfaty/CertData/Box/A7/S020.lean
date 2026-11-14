/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 20 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `80`–`83`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_80_0 : allFrom (a7Dat.rectI aIx 80) 0 8 = true := by
  decide +kernel

theorem a7_80_8 : allFrom (a7Dat.rectI aIx 80) 8 8 = true := by
  decide +kernel

theorem a7_80_16 : allFrom (a7Dat.rectI aIx 80) 16 8 = true := by
  decide +kernel

theorem a7_80_24 : allFrom (a7Dat.rectI aIx 80) 24 8 = true := by
  decide +kernel

theorem a7_80_32 : allFrom (a7Dat.rectI aIx 80) 32 8 = true := by
  decide +kernel

theorem a7_80_40 : allFrom (a7Dat.rectI aIx 80) 40 8 = true := by
  decide +kernel

theorem a7_80_48 : allFrom (a7Dat.rectI aIx 80) 48 8 = true := by
  decide +kernel

theorem a7_80_56 : allFrom (a7Dat.rectI aIx 80) 56 8 = true := by
  decide +kernel

theorem a7_80_64 : allFrom (a7Dat.rectI aIx 80) 64 8 = true := by
  decide +kernel

theorem a7_80_72 : allFrom (a7Dat.rectI aIx 80) 72 8 = true := by
  decide +kernel

theorem a7_80_80 : allFrom (a7Dat.rectI aIx 80) 80 8 = true := by
  decide +kernel

theorem a7_80_88 : allFrom (a7Dat.rectI aIx 80) 88 8 = true := by
  decide +kernel

theorem a7_80_96 : allFrom (a7Dat.rectI aIx 80) 96 8 = true := by
  decide +kernel

theorem a7_80_104 : allFrom (a7Dat.rectI aIx 80) 104 8 = true := by
  decide +kernel

theorem a7_80_112 : allFrom (a7Dat.rectI aIx 80) 112 8 = true := by
  decide +kernel

theorem a7_80_120 : allFrom (a7Dat.rectI aIx 80) 120 8 = true := by
  decide +kernel

theorem a7_80_128 : allFrom (a7Dat.rectI aIx 80) 128 8 = true := by
  decide +kernel

theorem a7_row_80 : a7Dat.rowI aIx 80 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 80 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 80) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 80) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 80)) a7_80_0) a7_80_8) a7_80_16) a7_80_24) a7_80_32) a7_80_40) a7_80_48) a7_80_56) a7_80_64) a7_80_72) a7_80_80) a7_80_88) a7_80_96) a7_80_104) a7_80_112) a7_80_120) a7_80_128)

theorem a7_81_0 : allFrom (a7Dat.rectI aIx 81) 0 8 = true := by
  decide +kernel

theorem a7_81_8 : allFrom (a7Dat.rectI aIx 81) 8 8 = true := by
  decide +kernel

theorem a7_81_16 : allFrom (a7Dat.rectI aIx 81) 16 8 = true := by
  decide +kernel

theorem a7_81_24 : allFrom (a7Dat.rectI aIx 81) 24 8 = true := by
  decide +kernel

theorem a7_81_32 : allFrom (a7Dat.rectI aIx 81) 32 8 = true := by
  decide +kernel

theorem a7_81_40 : allFrom (a7Dat.rectI aIx 81) 40 8 = true := by
  decide +kernel

theorem a7_81_48 : allFrom (a7Dat.rectI aIx 81) 48 8 = true := by
  decide +kernel

theorem a7_81_56 : allFrom (a7Dat.rectI aIx 81) 56 8 = true := by
  decide +kernel

theorem a7_81_64 : allFrom (a7Dat.rectI aIx 81) 64 8 = true := by
  decide +kernel

theorem a7_81_72 : allFrom (a7Dat.rectI aIx 81) 72 8 = true := by
  decide +kernel

theorem a7_81_80 : allFrom (a7Dat.rectI aIx 81) 80 8 = true := by
  decide +kernel

theorem a7_81_88 : allFrom (a7Dat.rectI aIx 81) 88 8 = true := by
  decide +kernel

theorem a7_81_96 : allFrom (a7Dat.rectI aIx 81) 96 8 = true := by
  decide +kernel

theorem a7_81_104 : allFrom (a7Dat.rectI aIx 81) 104 8 = true := by
  decide +kernel

theorem a7_81_112 : allFrom (a7Dat.rectI aIx 81) 112 8 = true := by
  decide +kernel

theorem a7_81_120 : allFrom (a7Dat.rectI aIx 81) 120 8 = true := by
  decide +kernel

theorem a7_81_128 : allFrom (a7Dat.rectI aIx 81) 128 8 = true := by
  decide +kernel

theorem a7_row_81 : a7Dat.rowI aIx 81 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 81 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 81) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 81) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 81)) a7_81_0) a7_81_8) a7_81_16) a7_81_24) a7_81_32) a7_81_40) a7_81_48) a7_81_56) a7_81_64) a7_81_72) a7_81_80) a7_81_88) a7_81_96) a7_81_104) a7_81_112) a7_81_120) a7_81_128)

theorem a7_82_0 : allFrom (a7Dat.rectI aIx 82) 0 8 = true := by
  decide +kernel

theorem a7_82_8 : allFrom (a7Dat.rectI aIx 82) 8 8 = true := by
  decide +kernel

theorem a7_82_16 : allFrom (a7Dat.rectI aIx 82) 16 8 = true := by
  decide +kernel

theorem a7_82_24 : allFrom (a7Dat.rectI aIx 82) 24 8 = true := by
  decide +kernel

theorem a7_82_32 : allFrom (a7Dat.rectI aIx 82) 32 8 = true := by
  decide +kernel

theorem a7_82_40 : allFrom (a7Dat.rectI aIx 82) 40 8 = true := by
  decide +kernel

theorem a7_82_48 : allFrom (a7Dat.rectI aIx 82) 48 8 = true := by
  decide +kernel

theorem a7_82_56 : allFrom (a7Dat.rectI aIx 82) 56 8 = true := by
  decide +kernel

theorem a7_82_64 : allFrom (a7Dat.rectI aIx 82) 64 8 = true := by
  decide +kernel

theorem a7_82_72 : allFrom (a7Dat.rectI aIx 82) 72 8 = true := by
  decide +kernel

theorem a7_82_80 : allFrom (a7Dat.rectI aIx 82) 80 8 = true := by
  decide +kernel

theorem a7_82_88 : allFrom (a7Dat.rectI aIx 82) 88 8 = true := by
  decide +kernel

theorem a7_82_96 : allFrom (a7Dat.rectI aIx 82) 96 8 = true := by
  decide +kernel

theorem a7_82_104 : allFrom (a7Dat.rectI aIx 82) 104 8 = true := by
  decide +kernel

theorem a7_82_112 : allFrom (a7Dat.rectI aIx 82) 112 8 = true := by
  decide +kernel

theorem a7_82_120 : allFrom (a7Dat.rectI aIx 82) 120 8 = true := by
  decide +kernel

theorem a7_82_128 : allFrom (a7Dat.rectI aIx 82) 128 8 = true := by
  decide +kernel

theorem a7_row_82 : a7Dat.rowI aIx 82 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 82 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 82) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 82) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 82)) a7_82_0) a7_82_8) a7_82_16) a7_82_24) a7_82_32) a7_82_40) a7_82_48) a7_82_56) a7_82_64) a7_82_72) a7_82_80) a7_82_88) a7_82_96) a7_82_104) a7_82_112) a7_82_120) a7_82_128)

theorem a7_83_0 : allFrom (a7Dat.rectI aIx 83) 0 8 = true := by
  decide +kernel

theorem a7_83_8 : allFrom (a7Dat.rectI aIx 83) 8 8 = true := by
  decide +kernel

theorem a7_83_16 : allFrom (a7Dat.rectI aIx 83) 16 8 = true := by
  decide +kernel

theorem a7_83_24 : allFrom (a7Dat.rectI aIx 83) 24 8 = true := by
  decide +kernel

theorem a7_83_32 : allFrom (a7Dat.rectI aIx 83) 32 8 = true := by
  decide +kernel

theorem a7_83_40 : allFrom (a7Dat.rectI aIx 83) 40 8 = true := by
  decide +kernel

theorem a7_83_48 : allFrom (a7Dat.rectI aIx 83) 48 8 = true := by
  decide +kernel

theorem a7_83_56 : allFrom (a7Dat.rectI aIx 83) 56 8 = true := by
  decide +kernel

theorem a7_83_64 : allFrom (a7Dat.rectI aIx 83) 64 8 = true := by
  decide +kernel

theorem a7_83_72 : allFrom (a7Dat.rectI aIx 83) 72 8 = true := by
  decide +kernel

theorem a7_83_80 : allFrom (a7Dat.rectI aIx 83) 80 8 = true := by
  decide +kernel

theorem a7_83_88 : allFrom (a7Dat.rectI aIx 83) 88 8 = true := by
  decide +kernel

theorem a7_83_96 : allFrom (a7Dat.rectI aIx 83) 96 8 = true := by
  decide +kernel

theorem a7_83_104 : allFrom (a7Dat.rectI aIx 83) 104 8 = true := by
  decide +kernel

theorem a7_83_112 : allFrom (a7Dat.rectI aIx 83) 112 8 = true := by
  decide +kernel

theorem a7_83_120 : allFrom (a7Dat.rectI aIx 83) 120 8 = true := by
  decide +kernel

theorem a7_83_128 : allFrom (a7Dat.rectI aIx 83) 128 8 = true := by
  decide +kernel

theorem a7_row_83 : a7Dat.rowI aIx 83 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 83 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 83) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 83) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 83)) a7_83_0) a7_83_8) a7_83_16) a7_83_24) a7_83_32) a7_83_40) a7_83_48) a7_83_56) a7_83_64) a7_83_72) a7_83_80) a7_83_88) a7_83_96) a7_83_104) a7_83_112) a7_83_120) a7_83_128)

theorem a7_blk_80 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 80 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 80) a7_row_80 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 81) a7_row_81 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 82) a7_row_82 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 83) a7_row_83 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 84)))))

end SandierSerfaty.CertData.Box
