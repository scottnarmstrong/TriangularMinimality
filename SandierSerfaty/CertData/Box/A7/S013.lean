/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 13 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `52`–`55`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_52_0 : allFrom (a7Dat.rectI aIx 52) 0 8 = true := by
  decide +kernel

theorem a7_52_8 : allFrom (a7Dat.rectI aIx 52) 8 8 = true := by
  decide +kernel

theorem a7_52_16 : allFrom (a7Dat.rectI aIx 52) 16 8 = true := by
  decide +kernel

theorem a7_52_24 : allFrom (a7Dat.rectI aIx 52) 24 8 = true := by
  decide +kernel

theorem a7_52_32 : allFrom (a7Dat.rectI aIx 52) 32 8 = true := by
  decide +kernel

theorem a7_52_40 : allFrom (a7Dat.rectI aIx 52) 40 8 = true := by
  decide +kernel

theorem a7_52_48 : allFrom (a7Dat.rectI aIx 52) 48 8 = true := by
  decide +kernel

theorem a7_52_56 : allFrom (a7Dat.rectI aIx 52) 56 8 = true := by
  decide +kernel

theorem a7_52_64 : allFrom (a7Dat.rectI aIx 52) 64 8 = true := by
  decide +kernel

theorem a7_52_72 : allFrom (a7Dat.rectI aIx 52) 72 8 = true := by
  decide +kernel

theorem a7_52_80 : allFrom (a7Dat.rectI aIx 52) 80 8 = true := by
  decide +kernel

theorem a7_52_88 : allFrom (a7Dat.rectI aIx 52) 88 8 = true := by
  decide +kernel

theorem a7_52_96 : allFrom (a7Dat.rectI aIx 52) 96 8 = true := by
  decide +kernel

theorem a7_52_104 : allFrom (a7Dat.rectI aIx 52) 104 8 = true := by
  decide +kernel

theorem a7_52_112 : allFrom (a7Dat.rectI aIx 52) 112 8 = true := by
  decide +kernel

theorem a7_52_120 : allFrom (a7Dat.rectI aIx 52) 120 8 = true := by
  decide +kernel

theorem a7_52_128 : allFrom (a7Dat.rectI aIx 52) 128 8 = true := by
  decide +kernel

theorem a7_row_52 : a7Dat.rowI aIx 52 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 52 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 52) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 52) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 52)) a7_52_0) a7_52_8) a7_52_16) a7_52_24) a7_52_32) a7_52_40) a7_52_48) a7_52_56) a7_52_64) a7_52_72) a7_52_80) a7_52_88) a7_52_96) a7_52_104) a7_52_112) a7_52_120) a7_52_128)

theorem a7_53_0 : allFrom (a7Dat.rectI aIx 53) 0 8 = true := by
  decide +kernel

theorem a7_53_8 : allFrom (a7Dat.rectI aIx 53) 8 8 = true := by
  decide +kernel

theorem a7_53_16 : allFrom (a7Dat.rectI aIx 53) 16 8 = true := by
  decide +kernel

theorem a7_53_24 : allFrom (a7Dat.rectI aIx 53) 24 8 = true := by
  decide +kernel

theorem a7_53_32 : allFrom (a7Dat.rectI aIx 53) 32 8 = true := by
  decide +kernel

theorem a7_53_40 : allFrom (a7Dat.rectI aIx 53) 40 8 = true := by
  decide +kernel

theorem a7_53_48 : allFrom (a7Dat.rectI aIx 53) 48 8 = true := by
  decide +kernel

theorem a7_53_56 : allFrom (a7Dat.rectI aIx 53) 56 8 = true := by
  decide +kernel

theorem a7_53_64 : allFrom (a7Dat.rectI aIx 53) 64 8 = true := by
  decide +kernel

theorem a7_53_72 : allFrom (a7Dat.rectI aIx 53) 72 8 = true := by
  decide +kernel

theorem a7_53_80 : allFrom (a7Dat.rectI aIx 53) 80 8 = true := by
  decide +kernel

theorem a7_53_88 : allFrom (a7Dat.rectI aIx 53) 88 8 = true := by
  decide +kernel

theorem a7_53_96 : allFrom (a7Dat.rectI aIx 53) 96 8 = true := by
  decide +kernel

theorem a7_53_104 : allFrom (a7Dat.rectI aIx 53) 104 8 = true := by
  decide +kernel

theorem a7_53_112 : allFrom (a7Dat.rectI aIx 53) 112 8 = true := by
  decide +kernel

theorem a7_53_120 : allFrom (a7Dat.rectI aIx 53) 120 8 = true := by
  decide +kernel

theorem a7_53_128 : allFrom (a7Dat.rectI aIx 53) 128 8 = true := by
  decide +kernel

theorem a7_row_53 : a7Dat.rowI aIx 53 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 53 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 53) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 53) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 53)) a7_53_0) a7_53_8) a7_53_16) a7_53_24) a7_53_32) a7_53_40) a7_53_48) a7_53_56) a7_53_64) a7_53_72) a7_53_80) a7_53_88) a7_53_96) a7_53_104) a7_53_112) a7_53_120) a7_53_128)

theorem a7_54_0 : allFrom (a7Dat.rectI aIx 54) 0 8 = true := by
  decide +kernel

theorem a7_54_8 : allFrom (a7Dat.rectI aIx 54) 8 8 = true := by
  decide +kernel

theorem a7_54_16 : allFrom (a7Dat.rectI aIx 54) 16 8 = true := by
  decide +kernel

theorem a7_54_24 : allFrom (a7Dat.rectI aIx 54) 24 8 = true := by
  decide +kernel

theorem a7_54_32 : allFrom (a7Dat.rectI aIx 54) 32 8 = true := by
  decide +kernel

theorem a7_54_40 : allFrom (a7Dat.rectI aIx 54) 40 8 = true := by
  decide +kernel

theorem a7_54_48 : allFrom (a7Dat.rectI aIx 54) 48 8 = true := by
  decide +kernel

theorem a7_54_56 : allFrom (a7Dat.rectI aIx 54) 56 8 = true := by
  decide +kernel

theorem a7_54_64 : allFrom (a7Dat.rectI aIx 54) 64 8 = true := by
  decide +kernel

theorem a7_54_72 : allFrom (a7Dat.rectI aIx 54) 72 8 = true := by
  decide +kernel

theorem a7_54_80 : allFrom (a7Dat.rectI aIx 54) 80 8 = true := by
  decide +kernel

theorem a7_54_88 : allFrom (a7Dat.rectI aIx 54) 88 8 = true := by
  decide +kernel

theorem a7_54_96 : allFrom (a7Dat.rectI aIx 54) 96 8 = true := by
  decide +kernel

theorem a7_54_104 : allFrom (a7Dat.rectI aIx 54) 104 8 = true := by
  decide +kernel

theorem a7_54_112 : allFrom (a7Dat.rectI aIx 54) 112 8 = true := by
  decide +kernel

theorem a7_54_120 : allFrom (a7Dat.rectI aIx 54) 120 8 = true := by
  decide +kernel

theorem a7_54_128 : allFrom (a7Dat.rectI aIx 54) 128 8 = true := by
  decide +kernel

theorem a7_row_54 : a7Dat.rowI aIx 54 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 54 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 54) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 54) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 54)) a7_54_0) a7_54_8) a7_54_16) a7_54_24) a7_54_32) a7_54_40) a7_54_48) a7_54_56) a7_54_64) a7_54_72) a7_54_80) a7_54_88) a7_54_96) a7_54_104) a7_54_112) a7_54_120) a7_54_128)

theorem a7_55_0 : allFrom (a7Dat.rectI aIx 55) 0 8 = true := by
  decide +kernel

theorem a7_55_8 : allFrom (a7Dat.rectI aIx 55) 8 8 = true := by
  decide +kernel

theorem a7_55_16 : allFrom (a7Dat.rectI aIx 55) 16 8 = true := by
  decide +kernel

theorem a7_55_24 : allFrom (a7Dat.rectI aIx 55) 24 8 = true := by
  decide +kernel

theorem a7_55_32 : allFrom (a7Dat.rectI aIx 55) 32 8 = true := by
  decide +kernel

theorem a7_55_40 : allFrom (a7Dat.rectI aIx 55) 40 8 = true := by
  decide +kernel

theorem a7_55_48 : allFrom (a7Dat.rectI aIx 55) 48 8 = true := by
  decide +kernel

theorem a7_55_56 : allFrom (a7Dat.rectI aIx 55) 56 8 = true := by
  decide +kernel

theorem a7_55_64 : allFrom (a7Dat.rectI aIx 55) 64 8 = true := by
  decide +kernel

theorem a7_55_72 : allFrom (a7Dat.rectI aIx 55) 72 8 = true := by
  decide +kernel

theorem a7_55_80 : allFrom (a7Dat.rectI aIx 55) 80 8 = true := by
  decide +kernel

theorem a7_55_88 : allFrom (a7Dat.rectI aIx 55) 88 8 = true := by
  decide +kernel

theorem a7_55_96 : allFrom (a7Dat.rectI aIx 55) 96 8 = true := by
  decide +kernel

theorem a7_55_104 : allFrom (a7Dat.rectI aIx 55) 104 8 = true := by
  decide +kernel

theorem a7_55_112 : allFrom (a7Dat.rectI aIx 55) 112 8 = true := by
  decide +kernel

theorem a7_55_120 : allFrom (a7Dat.rectI aIx 55) 120 8 = true := by
  decide +kernel

theorem a7_55_128 : allFrom (a7Dat.rectI aIx 55) 128 8 = true := by
  decide +kernel

theorem a7_row_55 : a7Dat.rowI aIx 55 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 55 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 55) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 55) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 55)) a7_55_0) a7_55_8) a7_55_16) a7_55_24) a7_55_32) a7_55_40) a7_55_48) a7_55_56) a7_55_64) a7_55_72) a7_55_80) a7_55_88) a7_55_96) a7_55_104) a7_55_112) a7_55_120) a7_55_128)

theorem a7_blk_52 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 52 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 52) a7_row_52 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 53) a7_row_53 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 54) a7_row_54 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 55) a7_row_55 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 56)))))

end SandierSerfaty.CertData.Box
