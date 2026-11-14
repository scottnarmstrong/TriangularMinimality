/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 12 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `48`–`51`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_48_0 : allFrom (a7Dat.rectI aIx 48) 0 8 = true := by
  decide +kernel

theorem a7_48_8 : allFrom (a7Dat.rectI aIx 48) 8 8 = true := by
  decide +kernel

theorem a7_48_16 : allFrom (a7Dat.rectI aIx 48) 16 8 = true := by
  decide +kernel

theorem a7_48_24 : allFrom (a7Dat.rectI aIx 48) 24 8 = true := by
  decide +kernel

theorem a7_48_32 : allFrom (a7Dat.rectI aIx 48) 32 8 = true := by
  decide +kernel

theorem a7_48_40 : allFrom (a7Dat.rectI aIx 48) 40 8 = true := by
  decide +kernel

theorem a7_48_48 : allFrom (a7Dat.rectI aIx 48) 48 8 = true := by
  decide +kernel

theorem a7_48_56 : allFrom (a7Dat.rectI aIx 48) 56 8 = true := by
  decide +kernel

theorem a7_48_64 : allFrom (a7Dat.rectI aIx 48) 64 8 = true := by
  decide +kernel

theorem a7_48_72 : allFrom (a7Dat.rectI aIx 48) 72 8 = true := by
  decide +kernel

theorem a7_48_80 : allFrom (a7Dat.rectI aIx 48) 80 8 = true := by
  decide +kernel

theorem a7_48_88 : allFrom (a7Dat.rectI aIx 48) 88 8 = true := by
  decide +kernel

theorem a7_48_96 : allFrom (a7Dat.rectI aIx 48) 96 8 = true := by
  decide +kernel

theorem a7_48_104 : allFrom (a7Dat.rectI aIx 48) 104 8 = true := by
  decide +kernel

theorem a7_48_112 : allFrom (a7Dat.rectI aIx 48) 112 8 = true := by
  decide +kernel

theorem a7_48_120 : allFrom (a7Dat.rectI aIx 48) 120 8 = true := by
  decide +kernel

theorem a7_48_128 : allFrom (a7Dat.rectI aIx 48) 128 8 = true := by
  decide +kernel

theorem a7_row_48 : a7Dat.rowI aIx 48 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 48 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 48) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 48) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 48)) a7_48_0) a7_48_8) a7_48_16) a7_48_24) a7_48_32) a7_48_40) a7_48_48) a7_48_56) a7_48_64) a7_48_72) a7_48_80) a7_48_88) a7_48_96) a7_48_104) a7_48_112) a7_48_120) a7_48_128)

theorem a7_49_0 : allFrom (a7Dat.rectI aIx 49) 0 8 = true := by
  decide +kernel

theorem a7_49_8 : allFrom (a7Dat.rectI aIx 49) 8 8 = true := by
  decide +kernel

theorem a7_49_16 : allFrom (a7Dat.rectI aIx 49) 16 8 = true := by
  decide +kernel

theorem a7_49_24 : allFrom (a7Dat.rectI aIx 49) 24 8 = true := by
  decide +kernel

theorem a7_49_32 : allFrom (a7Dat.rectI aIx 49) 32 8 = true := by
  decide +kernel

theorem a7_49_40 : allFrom (a7Dat.rectI aIx 49) 40 8 = true := by
  decide +kernel

theorem a7_49_48 : allFrom (a7Dat.rectI aIx 49) 48 8 = true := by
  decide +kernel

theorem a7_49_56 : allFrom (a7Dat.rectI aIx 49) 56 8 = true := by
  decide +kernel

theorem a7_49_64 : allFrom (a7Dat.rectI aIx 49) 64 8 = true := by
  decide +kernel

theorem a7_49_72 : allFrom (a7Dat.rectI aIx 49) 72 8 = true := by
  decide +kernel

theorem a7_49_80 : allFrom (a7Dat.rectI aIx 49) 80 8 = true := by
  decide +kernel

theorem a7_49_88 : allFrom (a7Dat.rectI aIx 49) 88 8 = true := by
  decide +kernel

theorem a7_49_96 : allFrom (a7Dat.rectI aIx 49) 96 8 = true := by
  decide +kernel

theorem a7_49_104 : allFrom (a7Dat.rectI aIx 49) 104 8 = true := by
  decide +kernel

theorem a7_49_112 : allFrom (a7Dat.rectI aIx 49) 112 8 = true := by
  decide +kernel

theorem a7_49_120 : allFrom (a7Dat.rectI aIx 49) 120 8 = true := by
  decide +kernel

theorem a7_49_128 : allFrom (a7Dat.rectI aIx 49) 128 8 = true := by
  decide +kernel

theorem a7_row_49 : a7Dat.rowI aIx 49 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 49 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 49) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 49) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 49)) a7_49_0) a7_49_8) a7_49_16) a7_49_24) a7_49_32) a7_49_40) a7_49_48) a7_49_56) a7_49_64) a7_49_72) a7_49_80) a7_49_88) a7_49_96) a7_49_104) a7_49_112) a7_49_120) a7_49_128)

theorem a7_50_0 : allFrom (a7Dat.rectI aIx 50) 0 8 = true := by
  decide +kernel

theorem a7_50_8 : allFrom (a7Dat.rectI aIx 50) 8 8 = true := by
  decide +kernel

theorem a7_50_16 : allFrom (a7Dat.rectI aIx 50) 16 8 = true := by
  decide +kernel

theorem a7_50_24 : allFrom (a7Dat.rectI aIx 50) 24 8 = true := by
  decide +kernel

theorem a7_50_32 : allFrom (a7Dat.rectI aIx 50) 32 8 = true := by
  decide +kernel

theorem a7_50_40 : allFrom (a7Dat.rectI aIx 50) 40 8 = true := by
  decide +kernel

theorem a7_50_48 : allFrom (a7Dat.rectI aIx 50) 48 8 = true := by
  decide +kernel

theorem a7_50_56 : allFrom (a7Dat.rectI aIx 50) 56 8 = true := by
  decide +kernel

theorem a7_50_64 : allFrom (a7Dat.rectI aIx 50) 64 8 = true := by
  decide +kernel

theorem a7_50_72 : allFrom (a7Dat.rectI aIx 50) 72 8 = true := by
  decide +kernel

theorem a7_50_80 : allFrom (a7Dat.rectI aIx 50) 80 8 = true := by
  decide +kernel

theorem a7_50_88 : allFrom (a7Dat.rectI aIx 50) 88 8 = true := by
  decide +kernel

theorem a7_50_96 : allFrom (a7Dat.rectI aIx 50) 96 8 = true := by
  decide +kernel

theorem a7_50_104 : allFrom (a7Dat.rectI aIx 50) 104 8 = true := by
  decide +kernel

theorem a7_50_112 : allFrom (a7Dat.rectI aIx 50) 112 8 = true := by
  decide +kernel

theorem a7_50_120 : allFrom (a7Dat.rectI aIx 50) 120 8 = true := by
  decide +kernel

theorem a7_50_128 : allFrom (a7Dat.rectI aIx 50) 128 8 = true := by
  decide +kernel

theorem a7_row_50 : a7Dat.rowI aIx 50 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 50 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 50) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 50) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 50)) a7_50_0) a7_50_8) a7_50_16) a7_50_24) a7_50_32) a7_50_40) a7_50_48) a7_50_56) a7_50_64) a7_50_72) a7_50_80) a7_50_88) a7_50_96) a7_50_104) a7_50_112) a7_50_120) a7_50_128)

theorem a7_51_0 : allFrom (a7Dat.rectI aIx 51) 0 8 = true := by
  decide +kernel

theorem a7_51_8 : allFrom (a7Dat.rectI aIx 51) 8 8 = true := by
  decide +kernel

theorem a7_51_16 : allFrom (a7Dat.rectI aIx 51) 16 8 = true := by
  decide +kernel

theorem a7_51_24 : allFrom (a7Dat.rectI aIx 51) 24 8 = true := by
  decide +kernel

theorem a7_51_32 : allFrom (a7Dat.rectI aIx 51) 32 8 = true := by
  decide +kernel

theorem a7_51_40 : allFrom (a7Dat.rectI aIx 51) 40 8 = true := by
  decide +kernel

theorem a7_51_48 : allFrom (a7Dat.rectI aIx 51) 48 8 = true := by
  decide +kernel

theorem a7_51_56 : allFrom (a7Dat.rectI aIx 51) 56 8 = true := by
  decide +kernel

theorem a7_51_64 : allFrom (a7Dat.rectI aIx 51) 64 8 = true := by
  decide +kernel

theorem a7_51_72 : allFrom (a7Dat.rectI aIx 51) 72 8 = true := by
  decide +kernel

theorem a7_51_80 : allFrom (a7Dat.rectI aIx 51) 80 8 = true := by
  decide +kernel

theorem a7_51_88 : allFrom (a7Dat.rectI aIx 51) 88 8 = true := by
  decide +kernel

theorem a7_51_96 : allFrom (a7Dat.rectI aIx 51) 96 8 = true := by
  decide +kernel

theorem a7_51_104 : allFrom (a7Dat.rectI aIx 51) 104 8 = true := by
  decide +kernel

theorem a7_51_112 : allFrom (a7Dat.rectI aIx 51) 112 8 = true := by
  decide +kernel

theorem a7_51_120 : allFrom (a7Dat.rectI aIx 51) 120 8 = true := by
  decide +kernel

theorem a7_51_128 : allFrom (a7Dat.rectI aIx 51) 128 8 = true := by
  decide +kernel

theorem a7_row_51 : a7Dat.rowI aIx 51 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 51 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 51) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 51) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 51)) a7_51_0) a7_51_8) a7_51_16) a7_51_24) a7_51_32) a7_51_40) a7_51_48) a7_51_56) a7_51_64) a7_51_72) a7_51_80) a7_51_88) a7_51_96) a7_51_104) a7_51_112) a7_51_120) a7_51_128)

theorem a7_blk_48 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 48 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 48) a7_row_48 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 49) a7_row_49 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 50) a7_row_50 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 51) a7_row_51 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 52)))))

end SandierSerfaty.CertData.Box
