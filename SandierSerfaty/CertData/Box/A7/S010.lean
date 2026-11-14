/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 10 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `40`–`43`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_40_0 : allFrom (a7Dat.rectI aIx 40) 0 8 = true := by
  decide +kernel

theorem a7_40_8 : allFrom (a7Dat.rectI aIx 40) 8 8 = true := by
  decide +kernel

theorem a7_40_16 : allFrom (a7Dat.rectI aIx 40) 16 8 = true := by
  decide +kernel

theorem a7_40_24 : allFrom (a7Dat.rectI aIx 40) 24 8 = true := by
  decide +kernel

theorem a7_40_32 : allFrom (a7Dat.rectI aIx 40) 32 8 = true := by
  decide +kernel

theorem a7_40_40 : allFrom (a7Dat.rectI aIx 40) 40 8 = true := by
  decide +kernel

theorem a7_40_48 : allFrom (a7Dat.rectI aIx 40) 48 8 = true := by
  decide +kernel

theorem a7_40_56 : allFrom (a7Dat.rectI aIx 40) 56 8 = true := by
  decide +kernel

theorem a7_40_64 : allFrom (a7Dat.rectI aIx 40) 64 8 = true := by
  decide +kernel

theorem a7_40_72 : allFrom (a7Dat.rectI aIx 40) 72 8 = true := by
  decide +kernel

theorem a7_40_80 : allFrom (a7Dat.rectI aIx 40) 80 8 = true := by
  decide +kernel

theorem a7_40_88 : allFrom (a7Dat.rectI aIx 40) 88 8 = true := by
  decide +kernel

theorem a7_40_96 : allFrom (a7Dat.rectI aIx 40) 96 8 = true := by
  decide +kernel

theorem a7_40_104 : allFrom (a7Dat.rectI aIx 40) 104 8 = true := by
  decide +kernel

theorem a7_40_112 : allFrom (a7Dat.rectI aIx 40) 112 8 = true := by
  decide +kernel

theorem a7_40_120 : allFrom (a7Dat.rectI aIx 40) 120 8 = true := by
  decide +kernel

theorem a7_40_128 : allFrom (a7Dat.rectI aIx 40) 128 8 = true := by
  decide +kernel

theorem a7_row_40 : a7Dat.rowI aIx 40 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 40 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 40) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 40) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 40)) a7_40_0) a7_40_8) a7_40_16) a7_40_24) a7_40_32) a7_40_40) a7_40_48) a7_40_56) a7_40_64) a7_40_72) a7_40_80) a7_40_88) a7_40_96) a7_40_104) a7_40_112) a7_40_120) a7_40_128)

theorem a7_41_0 : allFrom (a7Dat.rectI aIx 41) 0 8 = true := by
  decide +kernel

theorem a7_41_8 : allFrom (a7Dat.rectI aIx 41) 8 8 = true := by
  decide +kernel

theorem a7_41_16 : allFrom (a7Dat.rectI aIx 41) 16 8 = true := by
  decide +kernel

theorem a7_41_24 : allFrom (a7Dat.rectI aIx 41) 24 8 = true := by
  decide +kernel

theorem a7_41_32 : allFrom (a7Dat.rectI aIx 41) 32 8 = true := by
  decide +kernel

theorem a7_41_40 : allFrom (a7Dat.rectI aIx 41) 40 8 = true := by
  decide +kernel

theorem a7_41_48 : allFrom (a7Dat.rectI aIx 41) 48 8 = true := by
  decide +kernel

theorem a7_41_56 : allFrom (a7Dat.rectI aIx 41) 56 8 = true := by
  decide +kernel

theorem a7_41_64 : allFrom (a7Dat.rectI aIx 41) 64 8 = true := by
  decide +kernel

theorem a7_41_72 : allFrom (a7Dat.rectI aIx 41) 72 8 = true := by
  decide +kernel

theorem a7_41_80 : allFrom (a7Dat.rectI aIx 41) 80 8 = true := by
  decide +kernel

theorem a7_41_88 : allFrom (a7Dat.rectI aIx 41) 88 8 = true := by
  decide +kernel

theorem a7_41_96 : allFrom (a7Dat.rectI aIx 41) 96 8 = true := by
  decide +kernel

theorem a7_41_104 : allFrom (a7Dat.rectI aIx 41) 104 8 = true := by
  decide +kernel

theorem a7_41_112 : allFrom (a7Dat.rectI aIx 41) 112 8 = true := by
  decide +kernel

theorem a7_41_120 : allFrom (a7Dat.rectI aIx 41) 120 8 = true := by
  decide +kernel

theorem a7_41_128 : allFrom (a7Dat.rectI aIx 41) 128 8 = true := by
  decide +kernel

theorem a7_row_41 : a7Dat.rowI aIx 41 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 41 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 41) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 41) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 41)) a7_41_0) a7_41_8) a7_41_16) a7_41_24) a7_41_32) a7_41_40) a7_41_48) a7_41_56) a7_41_64) a7_41_72) a7_41_80) a7_41_88) a7_41_96) a7_41_104) a7_41_112) a7_41_120) a7_41_128)

theorem a7_42_0 : allFrom (a7Dat.rectI aIx 42) 0 8 = true := by
  decide +kernel

theorem a7_42_8 : allFrom (a7Dat.rectI aIx 42) 8 8 = true := by
  decide +kernel

theorem a7_42_16 : allFrom (a7Dat.rectI aIx 42) 16 8 = true := by
  decide +kernel

theorem a7_42_24 : allFrom (a7Dat.rectI aIx 42) 24 8 = true := by
  decide +kernel

theorem a7_42_32 : allFrom (a7Dat.rectI aIx 42) 32 8 = true := by
  decide +kernel

theorem a7_42_40 : allFrom (a7Dat.rectI aIx 42) 40 8 = true := by
  decide +kernel

theorem a7_42_48 : allFrom (a7Dat.rectI aIx 42) 48 8 = true := by
  decide +kernel

theorem a7_42_56 : allFrom (a7Dat.rectI aIx 42) 56 8 = true := by
  decide +kernel

theorem a7_42_64 : allFrom (a7Dat.rectI aIx 42) 64 8 = true := by
  decide +kernel

theorem a7_42_72 : allFrom (a7Dat.rectI aIx 42) 72 8 = true := by
  decide +kernel

theorem a7_42_80 : allFrom (a7Dat.rectI aIx 42) 80 8 = true := by
  decide +kernel

theorem a7_42_88 : allFrom (a7Dat.rectI aIx 42) 88 8 = true := by
  decide +kernel

theorem a7_42_96 : allFrom (a7Dat.rectI aIx 42) 96 8 = true := by
  decide +kernel

theorem a7_42_104 : allFrom (a7Dat.rectI aIx 42) 104 8 = true := by
  decide +kernel

theorem a7_42_112 : allFrom (a7Dat.rectI aIx 42) 112 8 = true := by
  decide +kernel

theorem a7_42_120 : allFrom (a7Dat.rectI aIx 42) 120 8 = true := by
  decide +kernel

theorem a7_42_128 : allFrom (a7Dat.rectI aIx 42) 128 8 = true := by
  decide +kernel

theorem a7_row_42 : a7Dat.rowI aIx 42 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 42 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 42) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 42) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 42)) a7_42_0) a7_42_8) a7_42_16) a7_42_24) a7_42_32) a7_42_40) a7_42_48) a7_42_56) a7_42_64) a7_42_72) a7_42_80) a7_42_88) a7_42_96) a7_42_104) a7_42_112) a7_42_120) a7_42_128)

theorem a7_43_0 : allFrom (a7Dat.rectI aIx 43) 0 8 = true := by
  decide +kernel

theorem a7_43_8 : allFrom (a7Dat.rectI aIx 43) 8 8 = true := by
  decide +kernel

theorem a7_43_16 : allFrom (a7Dat.rectI aIx 43) 16 8 = true := by
  decide +kernel

theorem a7_43_24 : allFrom (a7Dat.rectI aIx 43) 24 8 = true := by
  decide +kernel

theorem a7_43_32 : allFrom (a7Dat.rectI aIx 43) 32 8 = true := by
  decide +kernel

theorem a7_43_40 : allFrom (a7Dat.rectI aIx 43) 40 8 = true := by
  decide +kernel

theorem a7_43_48 : allFrom (a7Dat.rectI aIx 43) 48 8 = true := by
  decide +kernel

theorem a7_43_56 : allFrom (a7Dat.rectI aIx 43) 56 8 = true := by
  decide +kernel

theorem a7_43_64 : allFrom (a7Dat.rectI aIx 43) 64 8 = true := by
  decide +kernel

theorem a7_43_72 : allFrom (a7Dat.rectI aIx 43) 72 8 = true := by
  decide +kernel

theorem a7_43_80 : allFrom (a7Dat.rectI aIx 43) 80 8 = true := by
  decide +kernel

theorem a7_43_88 : allFrom (a7Dat.rectI aIx 43) 88 8 = true := by
  decide +kernel

theorem a7_43_96 : allFrom (a7Dat.rectI aIx 43) 96 8 = true := by
  decide +kernel

theorem a7_43_104 : allFrom (a7Dat.rectI aIx 43) 104 8 = true := by
  decide +kernel

theorem a7_43_112 : allFrom (a7Dat.rectI aIx 43) 112 8 = true := by
  decide +kernel

theorem a7_43_120 : allFrom (a7Dat.rectI aIx 43) 120 8 = true := by
  decide +kernel

theorem a7_43_128 : allFrom (a7Dat.rectI aIx 43) 128 8 = true := by
  decide +kernel

theorem a7_row_43 : a7Dat.rowI aIx 43 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 43 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 43) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 43) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 43)) a7_43_0) a7_43_8) a7_43_16) a7_43_24) a7_43_32) a7_43_40) a7_43_48) a7_43_56) a7_43_64) a7_43_72) a7_43_80) a7_43_88) a7_43_96) a7_43_104) a7_43_112) a7_43_120) a7_43_128)

theorem a7_blk_40 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 40 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 40) a7_row_40 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 41) a7_row_41 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 42) a7_row_42 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 43) a7_row_43 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 44)))))

end SandierSerfaty.CertData.Box
