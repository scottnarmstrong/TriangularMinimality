/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 16 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `64`–`67`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_64_0 : allFrom (a7Dat.rectI aIx 64) 0 8 = true := by
  decide +kernel

theorem a7_64_8 : allFrom (a7Dat.rectI aIx 64) 8 8 = true := by
  decide +kernel

theorem a7_64_16 : allFrom (a7Dat.rectI aIx 64) 16 8 = true := by
  decide +kernel

theorem a7_64_24 : allFrom (a7Dat.rectI aIx 64) 24 8 = true := by
  decide +kernel

theorem a7_64_32 : allFrom (a7Dat.rectI aIx 64) 32 8 = true := by
  decide +kernel

theorem a7_64_40 : allFrom (a7Dat.rectI aIx 64) 40 8 = true := by
  decide +kernel

theorem a7_64_48 : allFrom (a7Dat.rectI aIx 64) 48 8 = true := by
  decide +kernel

theorem a7_64_56 : allFrom (a7Dat.rectI aIx 64) 56 8 = true := by
  decide +kernel

theorem a7_64_64 : allFrom (a7Dat.rectI aIx 64) 64 8 = true := by
  decide +kernel

theorem a7_64_72 : allFrom (a7Dat.rectI aIx 64) 72 8 = true := by
  decide +kernel

theorem a7_64_80 : allFrom (a7Dat.rectI aIx 64) 80 8 = true := by
  decide +kernel

theorem a7_64_88 : allFrom (a7Dat.rectI aIx 64) 88 8 = true := by
  decide +kernel

theorem a7_64_96 : allFrom (a7Dat.rectI aIx 64) 96 8 = true := by
  decide +kernel

theorem a7_64_104 : allFrom (a7Dat.rectI aIx 64) 104 8 = true := by
  decide +kernel

theorem a7_64_112 : allFrom (a7Dat.rectI aIx 64) 112 8 = true := by
  decide +kernel

theorem a7_64_120 : allFrom (a7Dat.rectI aIx 64) 120 8 = true := by
  decide +kernel

theorem a7_64_128 : allFrom (a7Dat.rectI aIx 64) 128 8 = true := by
  decide +kernel

theorem a7_row_64 : a7Dat.rowI aIx 64 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 64 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 64) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 64) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 64)) a7_64_0) a7_64_8) a7_64_16) a7_64_24) a7_64_32) a7_64_40) a7_64_48) a7_64_56) a7_64_64) a7_64_72) a7_64_80) a7_64_88) a7_64_96) a7_64_104) a7_64_112) a7_64_120) a7_64_128)

theorem a7_65_0 : allFrom (a7Dat.rectI aIx 65) 0 8 = true := by
  decide +kernel

theorem a7_65_8 : allFrom (a7Dat.rectI aIx 65) 8 8 = true := by
  decide +kernel

theorem a7_65_16 : allFrom (a7Dat.rectI aIx 65) 16 8 = true := by
  decide +kernel

theorem a7_65_24 : allFrom (a7Dat.rectI aIx 65) 24 8 = true := by
  decide +kernel

theorem a7_65_32 : allFrom (a7Dat.rectI aIx 65) 32 8 = true := by
  decide +kernel

theorem a7_65_40 : allFrom (a7Dat.rectI aIx 65) 40 8 = true := by
  decide +kernel

theorem a7_65_48 : allFrom (a7Dat.rectI aIx 65) 48 8 = true := by
  decide +kernel

theorem a7_65_56 : allFrom (a7Dat.rectI aIx 65) 56 8 = true := by
  decide +kernel

theorem a7_65_64 : allFrom (a7Dat.rectI aIx 65) 64 8 = true := by
  decide +kernel

theorem a7_65_72 : allFrom (a7Dat.rectI aIx 65) 72 8 = true := by
  decide +kernel

theorem a7_65_80 : allFrom (a7Dat.rectI aIx 65) 80 8 = true := by
  decide +kernel

theorem a7_65_88 : allFrom (a7Dat.rectI aIx 65) 88 8 = true := by
  decide +kernel

theorem a7_65_96 : allFrom (a7Dat.rectI aIx 65) 96 8 = true := by
  decide +kernel

theorem a7_65_104 : allFrom (a7Dat.rectI aIx 65) 104 8 = true := by
  decide +kernel

theorem a7_65_112 : allFrom (a7Dat.rectI aIx 65) 112 8 = true := by
  decide +kernel

theorem a7_65_120 : allFrom (a7Dat.rectI aIx 65) 120 8 = true := by
  decide +kernel

theorem a7_65_128 : allFrom (a7Dat.rectI aIx 65) 128 8 = true := by
  decide +kernel

theorem a7_row_65 : a7Dat.rowI aIx 65 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 65 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 65) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 65) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 65)) a7_65_0) a7_65_8) a7_65_16) a7_65_24) a7_65_32) a7_65_40) a7_65_48) a7_65_56) a7_65_64) a7_65_72) a7_65_80) a7_65_88) a7_65_96) a7_65_104) a7_65_112) a7_65_120) a7_65_128)

theorem a7_66_0 : allFrom (a7Dat.rectI aIx 66) 0 8 = true := by
  decide +kernel

theorem a7_66_8 : allFrom (a7Dat.rectI aIx 66) 8 8 = true := by
  decide +kernel

theorem a7_66_16 : allFrom (a7Dat.rectI aIx 66) 16 8 = true := by
  decide +kernel

theorem a7_66_24 : allFrom (a7Dat.rectI aIx 66) 24 8 = true := by
  decide +kernel

theorem a7_66_32 : allFrom (a7Dat.rectI aIx 66) 32 8 = true := by
  decide +kernel

theorem a7_66_40 : allFrom (a7Dat.rectI aIx 66) 40 8 = true := by
  decide +kernel

theorem a7_66_48 : allFrom (a7Dat.rectI aIx 66) 48 8 = true := by
  decide +kernel

theorem a7_66_56 : allFrom (a7Dat.rectI aIx 66) 56 8 = true := by
  decide +kernel

theorem a7_66_64 : allFrom (a7Dat.rectI aIx 66) 64 8 = true := by
  decide +kernel

theorem a7_66_72 : allFrom (a7Dat.rectI aIx 66) 72 8 = true := by
  decide +kernel

theorem a7_66_80 : allFrom (a7Dat.rectI aIx 66) 80 8 = true := by
  decide +kernel

theorem a7_66_88 : allFrom (a7Dat.rectI aIx 66) 88 8 = true := by
  decide +kernel

theorem a7_66_96 : allFrom (a7Dat.rectI aIx 66) 96 8 = true := by
  decide +kernel

theorem a7_66_104 : allFrom (a7Dat.rectI aIx 66) 104 8 = true := by
  decide +kernel

theorem a7_66_112 : allFrom (a7Dat.rectI aIx 66) 112 8 = true := by
  decide +kernel

theorem a7_66_120 : allFrom (a7Dat.rectI aIx 66) 120 8 = true := by
  decide +kernel

theorem a7_66_128 : allFrom (a7Dat.rectI aIx 66) 128 8 = true := by
  decide +kernel

theorem a7_row_66 : a7Dat.rowI aIx 66 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 66 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 66) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 66) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 66)) a7_66_0) a7_66_8) a7_66_16) a7_66_24) a7_66_32) a7_66_40) a7_66_48) a7_66_56) a7_66_64) a7_66_72) a7_66_80) a7_66_88) a7_66_96) a7_66_104) a7_66_112) a7_66_120) a7_66_128)

theorem a7_67_0 : allFrom (a7Dat.rectI aIx 67) 0 8 = true := by
  decide +kernel

theorem a7_67_8 : allFrom (a7Dat.rectI aIx 67) 8 8 = true := by
  decide +kernel

theorem a7_67_16 : allFrom (a7Dat.rectI aIx 67) 16 8 = true := by
  decide +kernel

theorem a7_67_24 : allFrom (a7Dat.rectI aIx 67) 24 8 = true := by
  decide +kernel

theorem a7_67_32 : allFrom (a7Dat.rectI aIx 67) 32 8 = true := by
  decide +kernel

theorem a7_67_40 : allFrom (a7Dat.rectI aIx 67) 40 8 = true := by
  decide +kernel

theorem a7_67_48 : allFrom (a7Dat.rectI aIx 67) 48 8 = true := by
  decide +kernel

theorem a7_67_56 : allFrom (a7Dat.rectI aIx 67) 56 8 = true := by
  decide +kernel

theorem a7_67_64 : allFrom (a7Dat.rectI aIx 67) 64 8 = true := by
  decide +kernel

theorem a7_67_72 : allFrom (a7Dat.rectI aIx 67) 72 8 = true := by
  decide +kernel

theorem a7_67_80 : allFrom (a7Dat.rectI aIx 67) 80 8 = true := by
  decide +kernel

theorem a7_67_88 : allFrom (a7Dat.rectI aIx 67) 88 8 = true := by
  decide +kernel

theorem a7_67_96 : allFrom (a7Dat.rectI aIx 67) 96 8 = true := by
  decide +kernel

theorem a7_67_104 : allFrom (a7Dat.rectI aIx 67) 104 8 = true := by
  decide +kernel

theorem a7_67_112 : allFrom (a7Dat.rectI aIx 67) 112 8 = true := by
  decide +kernel

theorem a7_67_120 : allFrom (a7Dat.rectI aIx 67) 120 8 = true := by
  decide +kernel

theorem a7_67_128 : allFrom (a7Dat.rectI aIx 67) 128 8 = true := by
  decide +kernel

theorem a7_row_67 : a7Dat.rowI aIx 67 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 67 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 67) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 67) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 67)) a7_67_0) a7_67_8) a7_67_16) a7_67_24) a7_67_32) a7_67_40) a7_67_48) a7_67_56) a7_67_64) a7_67_72) a7_67_80) a7_67_88) a7_67_96) a7_67_104) a7_67_112) a7_67_120) a7_67_128)

theorem a7_blk_64 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 64 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 64) a7_row_64 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 65) a7_row_65 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 66) a7_row_66 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 67) a7_row_67 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 68)))))

end SandierSerfaty.CertData.Box
