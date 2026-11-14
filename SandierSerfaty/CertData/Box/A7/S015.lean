/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 15 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `60`–`63`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_60_0 : allFrom (a7Dat.rectI aIx 60) 0 8 = true := by
  decide +kernel

theorem a7_60_8 : allFrom (a7Dat.rectI aIx 60) 8 8 = true := by
  decide +kernel

theorem a7_60_16 : allFrom (a7Dat.rectI aIx 60) 16 8 = true := by
  decide +kernel

theorem a7_60_24 : allFrom (a7Dat.rectI aIx 60) 24 8 = true := by
  decide +kernel

theorem a7_60_32 : allFrom (a7Dat.rectI aIx 60) 32 8 = true := by
  decide +kernel

theorem a7_60_40 : allFrom (a7Dat.rectI aIx 60) 40 8 = true := by
  decide +kernel

theorem a7_60_48 : allFrom (a7Dat.rectI aIx 60) 48 8 = true := by
  decide +kernel

theorem a7_60_56 : allFrom (a7Dat.rectI aIx 60) 56 8 = true := by
  decide +kernel

theorem a7_60_64 : allFrom (a7Dat.rectI aIx 60) 64 8 = true := by
  decide +kernel

theorem a7_60_72 : allFrom (a7Dat.rectI aIx 60) 72 8 = true := by
  decide +kernel

theorem a7_60_80 : allFrom (a7Dat.rectI aIx 60) 80 8 = true := by
  decide +kernel

theorem a7_60_88 : allFrom (a7Dat.rectI aIx 60) 88 8 = true := by
  decide +kernel

theorem a7_60_96 : allFrom (a7Dat.rectI aIx 60) 96 8 = true := by
  decide +kernel

theorem a7_60_104 : allFrom (a7Dat.rectI aIx 60) 104 8 = true := by
  decide +kernel

theorem a7_60_112 : allFrom (a7Dat.rectI aIx 60) 112 8 = true := by
  decide +kernel

theorem a7_60_120 : allFrom (a7Dat.rectI aIx 60) 120 8 = true := by
  decide +kernel

theorem a7_60_128 : allFrom (a7Dat.rectI aIx 60) 128 8 = true := by
  decide +kernel

theorem a7_row_60 : a7Dat.rowI aIx 60 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 60 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 60) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 60) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 60)) a7_60_0) a7_60_8) a7_60_16) a7_60_24) a7_60_32) a7_60_40) a7_60_48) a7_60_56) a7_60_64) a7_60_72) a7_60_80) a7_60_88) a7_60_96) a7_60_104) a7_60_112) a7_60_120) a7_60_128)

theorem a7_61_0 : allFrom (a7Dat.rectI aIx 61) 0 8 = true := by
  decide +kernel

theorem a7_61_8 : allFrom (a7Dat.rectI aIx 61) 8 8 = true := by
  decide +kernel

theorem a7_61_16 : allFrom (a7Dat.rectI aIx 61) 16 8 = true := by
  decide +kernel

theorem a7_61_24 : allFrom (a7Dat.rectI aIx 61) 24 8 = true := by
  decide +kernel

theorem a7_61_32 : allFrom (a7Dat.rectI aIx 61) 32 8 = true := by
  decide +kernel

theorem a7_61_40 : allFrom (a7Dat.rectI aIx 61) 40 8 = true := by
  decide +kernel

theorem a7_61_48 : allFrom (a7Dat.rectI aIx 61) 48 8 = true := by
  decide +kernel

theorem a7_61_56 : allFrom (a7Dat.rectI aIx 61) 56 8 = true := by
  decide +kernel

theorem a7_61_64 : allFrom (a7Dat.rectI aIx 61) 64 8 = true := by
  decide +kernel

theorem a7_61_72 : allFrom (a7Dat.rectI aIx 61) 72 8 = true := by
  decide +kernel

theorem a7_61_80 : allFrom (a7Dat.rectI aIx 61) 80 8 = true := by
  decide +kernel

theorem a7_61_88 : allFrom (a7Dat.rectI aIx 61) 88 8 = true := by
  decide +kernel

theorem a7_61_96 : allFrom (a7Dat.rectI aIx 61) 96 8 = true := by
  decide +kernel

theorem a7_61_104 : allFrom (a7Dat.rectI aIx 61) 104 8 = true := by
  decide +kernel

theorem a7_61_112 : allFrom (a7Dat.rectI aIx 61) 112 8 = true := by
  decide +kernel

theorem a7_61_120 : allFrom (a7Dat.rectI aIx 61) 120 8 = true := by
  decide +kernel

theorem a7_61_128 : allFrom (a7Dat.rectI aIx 61) 128 8 = true := by
  decide +kernel

theorem a7_row_61 : a7Dat.rowI aIx 61 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 61 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 61) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 61) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 61)) a7_61_0) a7_61_8) a7_61_16) a7_61_24) a7_61_32) a7_61_40) a7_61_48) a7_61_56) a7_61_64) a7_61_72) a7_61_80) a7_61_88) a7_61_96) a7_61_104) a7_61_112) a7_61_120) a7_61_128)

theorem a7_62_0 : allFrom (a7Dat.rectI aIx 62) 0 8 = true := by
  decide +kernel

theorem a7_62_8 : allFrom (a7Dat.rectI aIx 62) 8 8 = true := by
  decide +kernel

theorem a7_62_16 : allFrom (a7Dat.rectI aIx 62) 16 8 = true := by
  decide +kernel

theorem a7_62_24 : allFrom (a7Dat.rectI aIx 62) 24 8 = true := by
  decide +kernel

theorem a7_62_32 : allFrom (a7Dat.rectI aIx 62) 32 8 = true := by
  decide +kernel

theorem a7_62_40 : allFrom (a7Dat.rectI aIx 62) 40 8 = true := by
  decide +kernel

theorem a7_62_48 : allFrom (a7Dat.rectI aIx 62) 48 8 = true := by
  decide +kernel

theorem a7_62_56 : allFrom (a7Dat.rectI aIx 62) 56 8 = true := by
  decide +kernel

theorem a7_62_64 : allFrom (a7Dat.rectI aIx 62) 64 8 = true := by
  decide +kernel

theorem a7_62_72 : allFrom (a7Dat.rectI aIx 62) 72 8 = true := by
  decide +kernel

theorem a7_62_80 : allFrom (a7Dat.rectI aIx 62) 80 8 = true := by
  decide +kernel

theorem a7_62_88 : allFrom (a7Dat.rectI aIx 62) 88 8 = true := by
  decide +kernel

theorem a7_62_96 : allFrom (a7Dat.rectI aIx 62) 96 8 = true := by
  decide +kernel

theorem a7_62_104 : allFrom (a7Dat.rectI aIx 62) 104 8 = true := by
  decide +kernel

theorem a7_62_112 : allFrom (a7Dat.rectI aIx 62) 112 8 = true := by
  decide +kernel

theorem a7_62_120 : allFrom (a7Dat.rectI aIx 62) 120 8 = true := by
  decide +kernel

theorem a7_62_128 : allFrom (a7Dat.rectI aIx 62) 128 8 = true := by
  decide +kernel

theorem a7_row_62 : a7Dat.rowI aIx 62 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 62 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 62) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 62) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 62)) a7_62_0) a7_62_8) a7_62_16) a7_62_24) a7_62_32) a7_62_40) a7_62_48) a7_62_56) a7_62_64) a7_62_72) a7_62_80) a7_62_88) a7_62_96) a7_62_104) a7_62_112) a7_62_120) a7_62_128)

theorem a7_63_0 : allFrom (a7Dat.rectI aIx 63) 0 8 = true := by
  decide +kernel

theorem a7_63_8 : allFrom (a7Dat.rectI aIx 63) 8 8 = true := by
  decide +kernel

theorem a7_63_16 : allFrom (a7Dat.rectI aIx 63) 16 8 = true := by
  decide +kernel

theorem a7_63_24 : allFrom (a7Dat.rectI aIx 63) 24 8 = true := by
  decide +kernel

theorem a7_63_32 : allFrom (a7Dat.rectI aIx 63) 32 8 = true := by
  decide +kernel

theorem a7_63_40 : allFrom (a7Dat.rectI aIx 63) 40 8 = true := by
  decide +kernel

theorem a7_63_48 : allFrom (a7Dat.rectI aIx 63) 48 8 = true := by
  decide +kernel

theorem a7_63_56 : allFrom (a7Dat.rectI aIx 63) 56 8 = true := by
  decide +kernel

theorem a7_63_64 : allFrom (a7Dat.rectI aIx 63) 64 8 = true := by
  decide +kernel

theorem a7_63_72 : allFrom (a7Dat.rectI aIx 63) 72 8 = true := by
  decide +kernel

theorem a7_63_80 : allFrom (a7Dat.rectI aIx 63) 80 8 = true := by
  decide +kernel

theorem a7_63_88 : allFrom (a7Dat.rectI aIx 63) 88 8 = true := by
  decide +kernel

theorem a7_63_96 : allFrom (a7Dat.rectI aIx 63) 96 8 = true := by
  decide +kernel

theorem a7_63_104 : allFrom (a7Dat.rectI aIx 63) 104 8 = true := by
  decide +kernel

theorem a7_63_112 : allFrom (a7Dat.rectI aIx 63) 112 8 = true := by
  decide +kernel

theorem a7_63_120 : allFrom (a7Dat.rectI aIx 63) 120 8 = true := by
  decide +kernel

theorem a7_63_128 : allFrom (a7Dat.rectI aIx 63) 128 8 = true := by
  decide +kernel

theorem a7_row_63 : a7Dat.rowI aIx 63 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 63 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 63) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 63) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 63)) a7_63_0) a7_63_8) a7_63_16) a7_63_24) a7_63_32) a7_63_40) a7_63_48) a7_63_56) a7_63_64) a7_63_72) a7_63_80) a7_63_88) a7_63_96) a7_63_104) a7_63_112) a7_63_120) a7_63_128)

theorem a7_blk_60 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 60 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 60) a7_row_60 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 61) a7_row_61 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 62) a7_row_62 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 63) a7_row_63 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 64)))))

end SandierSerfaty.CertData.Box
