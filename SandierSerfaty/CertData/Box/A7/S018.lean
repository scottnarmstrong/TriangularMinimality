/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 18 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `72`–`75`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_72_0 : allFrom (a7Dat.rectI aIx 72) 0 8 = true := by
  decide +kernel

theorem a7_72_8 : allFrom (a7Dat.rectI aIx 72) 8 8 = true := by
  decide +kernel

theorem a7_72_16 : allFrom (a7Dat.rectI aIx 72) 16 8 = true := by
  decide +kernel

theorem a7_72_24 : allFrom (a7Dat.rectI aIx 72) 24 8 = true := by
  decide +kernel

theorem a7_72_32 : allFrom (a7Dat.rectI aIx 72) 32 8 = true := by
  decide +kernel

theorem a7_72_40 : allFrom (a7Dat.rectI aIx 72) 40 8 = true := by
  decide +kernel

theorem a7_72_48 : allFrom (a7Dat.rectI aIx 72) 48 8 = true := by
  decide +kernel

theorem a7_72_56 : allFrom (a7Dat.rectI aIx 72) 56 8 = true := by
  decide +kernel

theorem a7_72_64 : allFrom (a7Dat.rectI aIx 72) 64 8 = true := by
  decide +kernel

theorem a7_72_72 : allFrom (a7Dat.rectI aIx 72) 72 8 = true := by
  decide +kernel

theorem a7_72_80 : allFrom (a7Dat.rectI aIx 72) 80 8 = true := by
  decide +kernel

theorem a7_72_88 : allFrom (a7Dat.rectI aIx 72) 88 8 = true := by
  decide +kernel

theorem a7_72_96 : allFrom (a7Dat.rectI aIx 72) 96 8 = true := by
  decide +kernel

theorem a7_72_104 : allFrom (a7Dat.rectI aIx 72) 104 8 = true := by
  decide +kernel

theorem a7_72_112 : allFrom (a7Dat.rectI aIx 72) 112 8 = true := by
  decide +kernel

theorem a7_72_120 : allFrom (a7Dat.rectI aIx 72) 120 8 = true := by
  decide +kernel

theorem a7_72_128 : allFrom (a7Dat.rectI aIx 72) 128 8 = true := by
  decide +kernel

theorem a7_row_72 : a7Dat.rowI aIx 72 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 72 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 72) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 72) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 72)) a7_72_0) a7_72_8) a7_72_16) a7_72_24) a7_72_32) a7_72_40) a7_72_48) a7_72_56) a7_72_64) a7_72_72) a7_72_80) a7_72_88) a7_72_96) a7_72_104) a7_72_112) a7_72_120) a7_72_128)

theorem a7_73_0 : allFrom (a7Dat.rectI aIx 73) 0 8 = true := by
  decide +kernel

theorem a7_73_8 : allFrom (a7Dat.rectI aIx 73) 8 8 = true := by
  decide +kernel

theorem a7_73_16 : allFrom (a7Dat.rectI aIx 73) 16 8 = true := by
  decide +kernel

theorem a7_73_24 : allFrom (a7Dat.rectI aIx 73) 24 8 = true := by
  decide +kernel

theorem a7_73_32 : allFrom (a7Dat.rectI aIx 73) 32 8 = true := by
  decide +kernel

theorem a7_73_40 : allFrom (a7Dat.rectI aIx 73) 40 8 = true := by
  decide +kernel

theorem a7_73_48 : allFrom (a7Dat.rectI aIx 73) 48 8 = true := by
  decide +kernel

theorem a7_73_56 : allFrom (a7Dat.rectI aIx 73) 56 8 = true := by
  decide +kernel

theorem a7_73_64 : allFrom (a7Dat.rectI aIx 73) 64 8 = true := by
  decide +kernel

theorem a7_73_72 : allFrom (a7Dat.rectI aIx 73) 72 8 = true := by
  decide +kernel

theorem a7_73_80 : allFrom (a7Dat.rectI aIx 73) 80 8 = true := by
  decide +kernel

theorem a7_73_88 : allFrom (a7Dat.rectI aIx 73) 88 8 = true := by
  decide +kernel

theorem a7_73_96 : allFrom (a7Dat.rectI aIx 73) 96 8 = true := by
  decide +kernel

theorem a7_73_104 : allFrom (a7Dat.rectI aIx 73) 104 8 = true := by
  decide +kernel

theorem a7_73_112 : allFrom (a7Dat.rectI aIx 73) 112 8 = true := by
  decide +kernel

theorem a7_73_120 : allFrom (a7Dat.rectI aIx 73) 120 8 = true := by
  decide +kernel

theorem a7_73_128 : allFrom (a7Dat.rectI aIx 73) 128 8 = true := by
  decide +kernel

theorem a7_row_73 : a7Dat.rowI aIx 73 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 73 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 73) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 73) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 73)) a7_73_0) a7_73_8) a7_73_16) a7_73_24) a7_73_32) a7_73_40) a7_73_48) a7_73_56) a7_73_64) a7_73_72) a7_73_80) a7_73_88) a7_73_96) a7_73_104) a7_73_112) a7_73_120) a7_73_128)

theorem a7_74_0 : allFrom (a7Dat.rectI aIx 74) 0 8 = true := by
  decide +kernel

theorem a7_74_8 : allFrom (a7Dat.rectI aIx 74) 8 8 = true := by
  decide +kernel

theorem a7_74_16 : allFrom (a7Dat.rectI aIx 74) 16 8 = true := by
  decide +kernel

theorem a7_74_24 : allFrom (a7Dat.rectI aIx 74) 24 8 = true := by
  decide +kernel

theorem a7_74_32 : allFrom (a7Dat.rectI aIx 74) 32 8 = true := by
  decide +kernel

theorem a7_74_40 : allFrom (a7Dat.rectI aIx 74) 40 8 = true := by
  decide +kernel

theorem a7_74_48 : allFrom (a7Dat.rectI aIx 74) 48 8 = true := by
  decide +kernel

theorem a7_74_56 : allFrom (a7Dat.rectI aIx 74) 56 8 = true := by
  decide +kernel

theorem a7_74_64 : allFrom (a7Dat.rectI aIx 74) 64 8 = true := by
  decide +kernel

theorem a7_74_72 : allFrom (a7Dat.rectI aIx 74) 72 8 = true := by
  decide +kernel

theorem a7_74_80 : allFrom (a7Dat.rectI aIx 74) 80 8 = true := by
  decide +kernel

theorem a7_74_88 : allFrom (a7Dat.rectI aIx 74) 88 8 = true := by
  decide +kernel

theorem a7_74_96 : allFrom (a7Dat.rectI aIx 74) 96 8 = true := by
  decide +kernel

theorem a7_74_104 : allFrom (a7Dat.rectI aIx 74) 104 8 = true := by
  decide +kernel

theorem a7_74_112 : allFrom (a7Dat.rectI aIx 74) 112 8 = true := by
  decide +kernel

theorem a7_74_120 : allFrom (a7Dat.rectI aIx 74) 120 8 = true := by
  decide +kernel

theorem a7_74_128 : allFrom (a7Dat.rectI aIx 74) 128 8 = true := by
  decide +kernel

theorem a7_row_74 : a7Dat.rowI aIx 74 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 74 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 74) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 74) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 74)) a7_74_0) a7_74_8) a7_74_16) a7_74_24) a7_74_32) a7_74_40) a7_74_48) a7_74_56) a7_74_64) a7_74_72) a7_74_80) a7_74_88) a7_74_96) a7_74_104) a7_74_112) a7_74_120) a7_74_128)

theorem a7_75_0 : allFrom (a7Dat.rectI aIx 75) 0 8 = true := by
  decide +kernel

theorem a7_75_8 : allFrom (a7Dat.rectI aIx 75) 8 8 = true := by
  decide +kernel

theorem a7_75_16 : allFrom (a7Dat.rectI aIx 75) 16 8 = true := by
  decide +kernel

theorem a7_75_24 : allFrom (a7Dat.rectI aIx 75) 24 8 = true := by
  decide +kernel

theorem a7_75_32 : allFrom (a7Dat.rectI aIx 75) 32 8 = true := by
  decide +kernel

theorem a7_75_40 : allFrom (a7Dat.rectI aIx 75) 40 8 = true := by
  decide +kernel

theorem a7_75_48 : allFrom (a7Dat.rectI aIx 75) 48 8 = true := by
  decide +kernel

theorem a7_75_56 : allFrom (a7Dat.rectI aIx 75) 56 8 = true := by
  decide +kernel

theorem a7_75_64 : allFrom (a7Dat.rectI aIx 75) 64 8 = true := by
  decide +kernel

theorem a7_75_72 : allFrom (a7Dat.rectI aIx 75) 72 8 = true := by
  decide +kernel

theorem a7_75_80 : allFrom (a7Dat.rectI aIx 75) 80 8 = true := by
  decide +kernel

theorem a7_75_88 : allFrom (a7Dat.rectI aIx 75) 88 8 = true := by
  decide +kernel

theorem a7_75_96 : allFrom (a7Dat.rectI aIx 75) 96 8 = true := by
  decide +kernel

theorem a7_75_104 : allFrom (a7Dat.rectI aIx 75) 104 8 = true := by
  decide +kernel

theorem a7_75_112 : allFrom (a7Dat.rectI aIx 75) 112 8 = true := by
  decide +kernel

theorem a7_75_120 : allFrom (a7Dat.rectI aIx 75) 120 8 = true := by
  decide +kernel

theorem a7_75_128 : allFrom (a7Dat.rectI aIx 75) 128 8 = true := by
  decide +kernel

theorem a7_row_75 : a7Dat.rowI aIx 75 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 75 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 75) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 75) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 75)) a7_75_0) a7_75_8) a7_75_16) a7_75_24) a7_75_32) a7_75_40) a7_75_48) a7_75_56) a7_75_64) a7_75_72) a7_75_80) a7_75_88) a7_75_96) a7_75_104) a7_75_112) a7_75_120) a7_75_128)

theorem a7_blk_72 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 72 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 72) a7_row_72 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 73) a7_row_73 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 74) a7_row_74 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 75) a7_row_75 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 76)))))

end SandierSerfaty.CertData.Box
