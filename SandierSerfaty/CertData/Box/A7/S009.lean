/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 9 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `36`–`39`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_36_0 : allFrom (a7Dat.rectI aIx 36) 0 8 = true := by
  decide +kernel

theorem a7_36_8 : allFrom (a7Dat.rectI aIx 36) 8 8 = true := by
  decide +kernel

theorem a7_36_16 : allFrom (a7Dat.rectI aIx 36) 16 8 = true := by
  decide +kernel

theorem a7_36_24 : allFrom (a7Dat.rectI aIx 36) 24 8 = true := by
  decide +kernel

theorem a7_36_32 : allFrom (a7Dat.rectI aIx 36) 32 8 = true := by
  decide +kernel

theorem a7_36_40 : allFrom (a7Dat.rectI aIx 36) 40 8 = true := by
  decide +kernel

theorem a7_36_48 : allFrom (a7Dat.rectI aIx 36) 48 8 = true := by
  decide +kernel

theorem a7_36_56 : allFrom (a7Dat.rectI aIx 36) 56 8 = true := by
  decide +kernel

theorem a7_36_64 : allFrom (a7Dat.rectI aIx 36) 64 8 = true := by
  decide +kernel

theorem a7_36_72 : allFrom (a7Dat.rectI aIx 36) 72 8 = true := by
  decide +kernel

theorem a7_36_80 : allFrom (a7Dat.rectI aIx 36) 80 8 = true := by
  decide +kernel

theorem a7_36_88 : allFrom (a7Dat.rectI aIx 36) 88 8 = true := by
  decide +kernel

theorem a7_36_96 : allFrom (a7Dat.rectI aIx 36) 96 8 = true := by
  decide +kernel

theorem a7_36_104 : allFrom (a7Dat.rectI aIx 36) 104 8 = true := by
  decide +kernel

theorem a7_36_112 : allFrom (a7Dat.rectI aIx 36) 112 8 = true := by
  decide +kernel

theorem a7_36_120 : allFrom (a7Dat.rectI aIx 36) 120 8 = true := by
  decide +kernel

theorem a7_36_128 : allFrom (a7Dat.rectI aIx 36) 128 8 = true := by
  decide +kernel

theorem a7_row_36 : a7Dat.rowI aIx 36 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 36 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 36) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 36) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 36)) a7_36_0) a7_36_8) a7_36_16) a7_36_24) a7_36_32) a7_36_40) a7_36_48) a7_36_56) a7_36_64) a7_36_72) a7_36_80) a7_36_88) a7_36_96) a7_36_104) a7_36_112) a7_36_120) a7_36_128)

theorem a7_37_0 : allFrom (a7Dat.rectI aIx 37) 0 8 = true := by
  decide +kernel

theorem a7_37_8 : allFrom (a7Dat.rectI aIx 37) 8 8 = true := by
  decide +kernel

theorem a7_37_16 : allFrom (a7Dat.rectI aIx 37) 16 8 = true := by
  decide +kernel

theorem a7_37_24 : allFrom (a7Dat.rectI aIx 37) 24 8 = true := by
  decide +kernel

theorem a7_37_32 : allFrom (a7Dat.rectI aIx 37) 32 8 = true := by
  decide +kernel

theorem a7_37_40 : allFrom (a7Dat.rectI aIx 37) 40 8 = true := by
  decide +kernel

theorem a7_37_48 : allFrom (a7Dat.rectI aIx 37) 48 8 = true := by
  decide +kernel

theorem a7_37_56 : allFrom (a7Dat.rectI aIx 37) 56 8 = true := by
  decide +kernel

theorem a7_37_64 : allFrom (a7Dat.rectI aIx 37) 64 8 = true := by
  decide +kernel

theorem a7_37_72 : allFrom (a7Dat.rectI aIx 37) 72 8 = true := by
  decide +kernel

theorem a7_37_80 : allFrom (a7Dat.rectI aIx 37) 80 8 = true := by
  decide +kernel

theorem a7_37_88 : allFrom (a7Dat.rectI aIx 37) 88 8 = true := by
  decide +kernel

theorem a7_37_96 : allFrom (a7Dat.rectI aIx 37) 96 8 = true := by
  decide +kernel

theorem a7_37_104 : allFrom (a7Dat.rectI aIx 37) 104 8 = true := by
  decide +kernel

theorem a7_37_112 : allFrom (a7Dat.rectI aIx 37) 112 8 = true := by
  decide +kernel

theorem a7_37_120 : allFrom (a7Dat.rectI aIx 37) 120 8 = true := by
  decide +kernel

theorem a7_37_128 : allFrom (a7Dat.rectI aIx 37) 128 8 = true := by
  decide +kernel

theorem a7_row_37 : a7Dat.rowI aIx 37 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 37 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 37) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 37) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 37)) a7_37_0) a7_37_8) a7_37_16) a7_37_24) a7_37_32) a7_37_40) a7_37_48) a7_37_56) a7_37_64) a7_37_72) a7_37_80) a7_37_88) a7_37_96) a7_37_104) a7_37_112) a7_37_120) a7_37_128)

theorem a7_38_0 : allFrom (a7Dat.rectI aIx 38) 0 8 = true := by
  decide +kernel

theorem a7_38_8 : allFrom (a7Dat.rectI aIx 38) 8 8 = true := by
  decide +kernel

theorem a7_38_16 : allFrom (a7Dat.rectI aIx 38) 16 8 = true := by
  decide +kernel

theorem a7_38_24 : allFrom (a7Dat.rectI aIx 38) 24 8 = true := by
  decide +kernel

theorem a7_38_32 : allFrom (a7Dat.rectI aIx 38) 32 8 = true := by
  decide +kernel

theorem a7_38_40 : allFrom (a7Dat.rectI aIx 38) 40 8 = true := by
  decide +kernel

theorem a7_38_48 : allFrom (a7Dat.rectI aIx 38) 48 8 = true := by
  decide +kernel

theorem a7_38_56 : allFrom (a7Dat.rectI aIx 38) 56 8 = true := by
  decide +kernel

theorem a7_38_64 : allFrom (a7Dat.rectI aIx 38) 64 8 = true := by
  decide +kernel

theorem a7_38_72 : allFrom (a7Dat.rectI aIx 38) 72 8 = true := by
  decide +kernel

theorem a7_38_80 : allFrom (a7Dat.rectI aIx 38) 80 8 = true := by
  decide +kernel

theorem a7_38_88 : allFrom (a7Dat.rectI aIx 38) 88 8 = true := by
  decide +kernel

theorem a7_38_96 : allFrom (a7Dat.rectI aIx 38) 96 8 = true := by
  decide +kernel

theorem a7_38_104 : allFrom (a7Dat.rectI aIx 38) 104 8 = true := by
  decide +kernel

theorem a7_38_112 : allFrom (a7Dat.rectI aIx 38) 112 8 = true := by
  decide +kernel

theorem a7_38_120 : allFrom (a7Dat.rectI aIx 38) 120 8 = true := by
  decide +kernel

theorem a7_38_128 : allFrom (a7Dat.rectI aIx 38) 128 8 = true := by
  decide +kernel

theorem a7_row_38 : a7Dat.rowI aIx 38 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 38 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 38) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 38) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 38)) a7_38_0) a7_38_8) a7_38_16) a7_38_24) a7_38_32) a7_38_40) a7_38_48) a7_38_56) a7_38_64) a7_38_72) a7_38_80) a7_38_88) a7_38_96) a7_38_104) a7_38_112) a7_38_120) a7_38_128)

theorem a7_39_0 : allFrom (a7Dat.rectI aIx 39) 0 8 = true := by
  decide +kernel

theorem a7_39_8 : allFrom (a7Dat.rectI aIx 39) 8 8 = true := by
  decide +kernel

theorem a7_39_16 : allFrom (a7Dat.rectI aIx 39) 16 8 = true := by
  decide +kernel

theorem a7_39_24 : allFrom (a7Dat.rectI aIx 39) 24 8 = true := by
  decide +kernel

theorem a7_39_32 : allFrom (a7Dat.rectI aIx 39) 32 8 = true := by
  decide +kernel

theorem a7_39_40 : allFrom (a7Dat.rectI aIx 39) 40 8 = true := by
  decide +kernel

theorem a7_39_48 : allFrom (a7Dat.rectI aIx 39) 48 8 = true := by
  decide +kernel

theorem a7_39_56 : allFrom (a7Dat.rectI aIx 39) 56 8 = true := by
  decide +kernel

theorem a7_39_64 : allFrom (a7Dat.rectI aIx 39) 64 8 = true := by
  decide +kernel

theorem a7_39_72 : allFrom (a7Dat.rectI aIx 39) 72 8 = true := by
  decide +kernel

theorem a7_39_80 : allFrom (a7Dat.rectI aIx 39) 80 8 = true := by
  decide +kernel

theorem a7_39_88 : allFrom (a7Dat.rectI aIx 39) 88 8 = true := by
  decide +kernel

theorem a7_39_96 : allFrom (a7Dat.rectI aIx 39) 96 8 = true := by
  decide +kernel

theorem a7_39_104 : allFrom (a7Dat.rectI aIx 39) 104 8 = true := by
  decide +kernel

theorem a7_39_112 : allFrom (a7Dat.rectI aIx 39) 112 8 = true := by
  decide +kernel

theorem a7_39_120 : allFrom (a7Dat.rectI aIx 39) 120 8 = true := by
  decide +kernel

theorem a7_39_128 : allFrom (a7Dat.rectI aIx 39) 128 8 = true := by
  decide +kernel

theorem a7_row_39 : a7Dat.rowI aIx 39 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 39 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 39) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 39) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 39)) a7_39_0) a7_39_8) a7_39_16) a7_39_24) a7_39_32) a7_39_40) a7_39_48) a7_39_56) a7_39_64) a7_39_72) a7_39_80) a7_39_88) a7_39_96) a7_39_104) a7_39_112) a7_39_120) a7_39_128)

theorem a7_blk_36 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 36 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 36) a7_row_36 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 37) a7_row_37 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 38) a7_row_38 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 39) a7_row_39 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 40)))))

end SandierSerfaty.CertData.Box
