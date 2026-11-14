/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 11 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `44`–`47`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_44_0 : allFrom (a7Dat.rectI aIx 44) 0 8 = true := by
  decide +kernel

theorem a7_44_8 : allFrom (a7Dat.rectI aIx 44) 8 8 = true := by
  decide +kernel

theorem a7_44_16 : allFrom (a7Dat.rectI aIx 44) 16 8 = true := by
  decide +kernel

theorem a7_44_24 : allFrom (a7Dat.rectI aIx 44) 24 8 = true := by
  decide +kernel

theorem a7_44_32 : allFrom (a7Dat.rectI aIx 44) 32 8 = true := by
  decide +kernel

theorem a7_44_40 : allFrom (a7Dat.rectI aIx 44) 40 8 = true := by
  decide +kernel

theorem a7_44_48 : allFrom (a7Dat.rectI aIx 44) 48 8 = true := by
  decide +kernel

theorem a7_44_56 : allFrom (a7Dat.rectI aIx 44) 56 8 = true := by
  decide +kernel

theorem a7_44_64 : allFrom (a7Dat.rectI aIx 44) 64 8 = true := by
  decide +kernel

theorem a7_44_72 : allFrom (a7Dat.rectI aIx 44) 72 8 = true := by
  decide +kernel

theorem a7_44_80 : allFrom (a7Dat.rectI aIx 44) 80 8 = true := by
  decide +kernel

theorem a7_44_88 : allFrom (a7Dat.rectI aIx 44) 88 8 = true := by
  decide +kernel

theorem a7_44_96 : allFrom (a7Dat.rectI aIx 44) 96 8 = true := by
  decide +kernel

theorem a7_44_104 : allFrom (a7Dat.rectI aIx 44) 104 8 = true := by
  decide +kernel

theorem a7_44_112 : allFrom (a7Dat.rectI aIx 44) 112 8 = true := by
  decide +kernel

theorem a7_44_120 : allFrom (a7Dat.rectI aIx 44) 120 8 = true := by
  decide +kernel

theorem a7_44_128 : allFrom (a7Dat.rectI aIx 44) 128 8 = true := by
  decide +kernel

theorem a7_row_44 : a7Dat.rowI aIx 44 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 44 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 44) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 44) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 44)) a7_44_0) a7_44_8) a7_44_16) a7_44_24) a7_44_32) a7_44_40) a7_44_48) a7_44_56) a7_44_64) a7_44_72) a7_44_80) a7_44_88) a7_44_96) a7_44_104) a7_44_112) a7_44_120) a7_44_128)

theorem a7_45_0 : allFrom (a7Dat.rectI aIx 45) 0 8 = true := by
  decide +kernel

theorem a7_45_8 : allFrom (a7Dat.rectI aIx 45) 8 8 = true := by
  decide +kernel

theorem a7_45_16 : allFrom (a7Dat.rectI aIx 45) 16 8 = true := by
  decide +kernel

theorem a7_45_24 : allFrom (a7Dat.rectI aIx 45) 24 8 = true := by
  decide +kernel

theorem a7_45_32 : allFrom (a7Dat.rectI aIx 45) 32 8 = true := by
  decide +kernel

theorem a7_45_40 : allFrom (a7Dat.rectI aIx 45) 40 8 = true := by
  decide +kernel

theorem a7_45_48 : allFrom (a7Dat.rectI aIx 45) 48 8 = true := by
  decide +kernel

theorem a7_45_56 : allFrom (a7Dat.rectI aIx 45) 56 8 = true := by
  decide +kernel

theorem a7_45_64 : allFrom (a7Dat.rectI aIx 45) 64 8 = true := by
  decide +kernel

theorem a7_45_72 : allFrom (a7Dat.rectI aIx 45) 72 8 = true := by
  decide +kernel

theorem a7_45_80 : allFrom (a7Dat.rectI aIx 45) 80 8 = true := by
  decide +kernel

theorem a7_45_88 : allFrom (a7Dat.rectI aIx 45) 88 8 = true := by
  decide +kernel

theorem a7_45_96 : allFrom (a7Dat.rectI aIx 45) 96 8 = true := by
  decide +kernel

theorem a7_45_104 : allFrom (a7Dat.rectI aIx 45) 104 8 = true := by
  decide +kernel

theorem a7_45_112 : allFrom (a7Dat.rectI aIx 45) 112 8 = true := by
  decide +kernel

theorem a7_45_120 : allFrom (a7Dat.rectI aIx 45) 120 8 = true := by
  decide +kernel

theorem a7_45_128 : allFrom (a7Dat.rectI aIx 45) 128 8 = true := by
  decide +kernel

theorem a7_row_45 : a7Dat.rowI aIx 45 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 45 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 45) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 45) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 45)) a7_45_0) a7_45_8) a7_45_16) a7_45_24) a7_45_32) a7_45_40) a7_45_48) a7_45_56) a7_45_64) a7_45_72) a7_45_80) a7_45_88) a7_45_96) a7_45_104) a7_45_112) a7_45_120) a7_45_128)

theorem a7_46_0 : allFrom (a7Dat.rectI aIx 46) 0 8 = true := by
  decide +kernel

theorem a7_46_8 : allFrom (a7Dat.rectI aIx 46) 8 8 = true := by
  decide +kernel

theorem a7_46_16 : allFrom (a7Dat.rectI aIx 46) 16 8 = true := by
  decide +kernel

theorem a7_46_24 : allFrom (a7Dat.rectI aIx 46) 24 8 = true := by
  decide +kernel

theorem a7_46_32 : allFrom (a7Dat.rectI aIx 46) 32 8 = true := by
  decide +kernel

theorem a7_46_40 : allFrom (a7Dat.rectI aIx 46) 40 8 = true := by
  decide +kernel

theorem a7_46_48 : allFrom (a7Dat.rectI aIx 46) 48 8 = true := by
  decide +kernel

theorem a7_46_56 : allFrom (a7Dat.rectI aIx 46) 56 8 = true := by
  decide +kernel

theorem a7_46_64 : allFrom (a7Dat.rectI aIx 46) 64 8 = true := by
  decide +kernel

theorem a7_46_72 : allFrom (a7Dat.rectI aIx 46) 72 8 = true := by
  decide +kernel

theorem a7_46_80 : allFrom (a7Dat.rectI aIx 46) 80 8 = true := by
  decide +kernel

theorem a7_46_88 : allFrom (a7Dat.rectI aIx 46) 88 8 = true := by
  decide +kernel

theorem a7_46_96 : allFrom (a7Dat.rectI aIx 46) 96 8 = true := by
  decide +kernel

theorem a7_46_104 : allFrom (a7Dat.rectI aIx 46) 104 8 = true := by
  decide +kernel

theorem a7_46_112 : allFrom (a7Dat.rectI aIx 46) 112 8 = true := by
  decide +kernel

theorem a7_46_120 : allFrom (a7Dat.rectI aIx 46) 120 8 = true := by
  decide +kernel

theorem a7_46_128 : allFrom (a7Dat.rectI aIx 46) 128 8 = true := by
  decide +kernel

theorem a7_row_46 : a7Dat.rowI aIx 46 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 46 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 46) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 46) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 46)) a7_46_0) a7_46_8) a7_46_16) a7_46_24) a7_46_32) a7_46_40) a7_46_48) a7_46_56) a7_46_64) a7_46_72) a7_46_80) a7_46_88) a7_46_96) a7_46_104) a7_46_112) a7_46_120) a7_46_128)

theorem a7_47_0 : allFrom (a7Dat.rectI aIx 47) 0 8 = true := by
  decide +kernel

theorem a7_47_8 : allFrom (a7Dat.rectI aIx 47) 8 8 = true := by
  decide +kernel

theorem a7_47_16 : allFrom (a7Dat.rectI aIx 47) 16 8 = true := by
  decide +kernel

theorem a7_47_24 : allFrom (a7Dat.rectI aIx 47) 24 8 = true := by
  decide +kernel

theorem a7_47_32 : allFrom (a7Dat.rectI aIx 47) 32 8 = true := by
  decide +kernel

theorem a7_47_40 : allFrom (a7Dat.rectI aIx 47) 40 8 = true := by
  decide +kernel

theorem a7_47_48 : allFrom (a7Dat.rectI aIx 47) 48 8 = true := by
  decide +kernel

theorem a7_47_56 : allFrom (a7Dat.rectI aIx 47) 56 8 = true := by
  decide +kernel

theorem a7_47_64 : allFrom (a7Dat.rectI aIx 47) 64 8 = true := by
  decide +kernel

theorem a7_47_72 : allFrom (a7Dat.rectI aIx 47) 72 8 = true := by
  decide +kernel

theorem a7_47_80 : allFrom (a7Dat.rectI aIx 47) 80 8 = true := by
  decide +kernel

theorem a7_47_88 : allFrom (a7Dat.rectI aIx 47) 88 8 = true := by
  decide +kernel

theorem a7_47_96 : allFrom (a7Dat.rectI aIx 47) 96 8 = true := by
  decide +kernel

theorem a7_47_104 : allFrom (a7Dat.rectI aIx 47) 104 8 = true := by
  decide +kernel

theorem a7_47_112 : allFrom (a7Dat.rectI aIx 47) 112 8 = true := by
  decide +kernel

theorem a7_47_120 : allFrom (a7Dat.rectI aIx 47) 120 8 = true := by
  decide +kernel

theorem a7_47_128 : allFrom (a7Dat.rectI aIx 47) 128 8 = true := by
  decide +kernel

theorem a7_row_47 : a7Dat.rowI aIx 47 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 47 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 47) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 47) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 47)) a7_47_0) a7_47_8) a7_47_16) a7_47_24) a7_47_32) a7_47_40) a7_47_48) a7_47_56) a7_47_64) a7_47_72) a7_47_80) a7_47_88) a7_47_96) a7_47_104) a7_47_112) a7_47_120) a7_47_128)

theorem a7_blk_44 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 44 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 44) a7_row_44 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 45) a7_row_45 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 46) a7_row_46 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 47) a7_row_47 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 48)))))

end SandierSerfaty.CertData.Box
