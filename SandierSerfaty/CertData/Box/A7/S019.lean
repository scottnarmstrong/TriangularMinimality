/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 19 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `76`–`79`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_76_0 : allFrom (a7Dat.rectI aIx 76) 0 8 = true := by
  decide +kernel

theorem a7_76_8 : allFrom (a7Dat.rectI aIx 76) 8 8 = true := by
  decide +kernel

theorem a7_76_16 : allFrom (a7Dat.rectI aIx 76) 16 8 = true := by
  decide +kernel

theorem a7_76_24 : allFrom (a7Dat.rectI aIx 76) 24 8 = true := by
  decide +kernel

theorem a7_76_32 : allFrom (a7Dat.rectI aIx 76) 32 8 = true := by
  decide +kernel

theorem a7_76_40 : allFrom (a7Dat.rectI aIx 76) 40 8 = true := by
  decide +kernel

theorem a7_76_48 : allFrom (a7Dat.rectI aIx 76) 48 8 = true := by
  decide +kernel

theorem a7_76_56 : allFrom (a7Dat.rectI aIx 76) 56 8 = true := by
  decide +kernel

theorem a7_76_64 : allFrom (a7Dat.rectI aIx 76) 64 8 = true := by
  decide +kernel

theorem a7_76_72 : allFrom (a7Dat.rectI aIx 76) 72 8 = true := by
  decide +kernel

theorem a7_76_80 : allFrom (a7Dat.rectI aIx 76) 80 8 = true := by
  decide +kernel

theorem a7_76_88 : allFrom (a7Dat.rectI aIx 76) 88 8 = true := by
  decide +kernel

theorem a7_76_96 : allFrom (a7Dat.rectI aIx 76) 96 8 = true := by
  decide +kernel

theorem a7_76_104 : allFrom (a7Dat.rectI aIx 76) 104 8 = true := by
  decide +kernel

theorem a7_76_112 : allFrom (a7Dat.rectI aIx 76) 112 8 = true := by
  decide +kernel

theorem a7_76_120 : allFrom (a7Dat.rectI aIx 76) 120 8 = true := by
  decide +kernel

theorem a7_76_128 : allFrom (a7Dat.rectI aIx 76) 128 8 = true := by
  decide +kernel

theorem a7_row_76 : a7Dat.rowI aIx 76 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 76 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 76) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 76) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 76)) a7_76_0) a7_76_8) a7_76_16) a7_76_24) a7_76_32) a7_76_40) a7_76_48) a7_76_56) a7_76_64) a7_76_72) a7_76_80) a7_76_88) a7_76_96) a7_76_104) a7_76_112) a7_76_120) a7_76_128)

theorem a7_77_0 : allFrom (a7Dat.rectI aIx 77) 0 8 = true := by
  decide +kernel

theorem a7_77_8 : allFrom (a7Dat.rectI aIx 77) 8 8 = true := by
  decide +kernel

theorem a7_77_16 : allFrom (a7Dat.rectI aIx 77) 16 8 = true := by
  decide +kernel

theorem a7_77_24 : allFrom (a7Dat.rectI aIx 77) 24 8 = true := by
  decide +kernel

theorem a7_77_32 : allFrom (a7Dat.rectI aIx 77) 32 8 = true := by
  decide +kernel

theorem a7_77_40 : allFrom (a7Dat.rectI aIx 77) 40 8 = true := by
  decide +kernel

theorem a7_77_48 : allFrom (a7Dat.rectI aIx 77) 48 8 = true := by
  decide +kernel

theorem a7_77_56 : allFrom (a7Dat.rectI aIx 77) 56 8 = true := by
  decide +kernel

theorem a7_77_64 : allFrom (a7Dat.rectI aIx 77) 64 8 = true := by
  decide +kernel

theorem a7_77_72 : allFrom (a7Dat.rectI aIx 77) 72 8 = true := by
  decide +kernel

theorem a7_77_80 : allFrom (a7Dat.rectI aIx 77) 80 8 = true := by
  decide +kernel

theorem a7_77_88 : allFrom (a7Dat.rectI aIx 77) 88 8 = true := by
  decide +kernel

theorem a7_77_96 : allFrom (a7Dat.rectI aIx 77) 96 8 = true := by
  decide +kernel

theorem a7_77_104 : allFrom (a7Dat.rectI aIx 77) 104 8 = true := by
  decide +kernel

theorem a7_77_112 : allFrom (a7Dat.rectI aIx 77) 112 8 = true := by
  decide +kernel

theorem a7_77_120 : allFrom (a7Dat.rectI aIx 77) 120 8 = true := by
  decide +kernel

theorem a7_77_128 : allFrom (a7Dat.rectI aIx 77) 128 8 = true := by
  decide +kernel

theorem a7_row_77 : a7Dat.rowI aIx 77 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 77 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 77) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 77) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 77)) a7_77_0) a7_77_8) a7_77_16) a7_77_24) a7_77_32) a7_77_40) a7_77_48) a7_77_56) a7_77_64) a7_77_72) a7_77_80) a7_77_88) a7_77_96) a7_77_104) a7_77_112) a7_77_120) a7_77_128)

theorem a7_78_0 : allFrom (a7Dat.rectI aIx 78) 0 8 = true := by
  decide +kernel

theorem a7_78_8 : allFrom (a7Dat.rectI aIx 78) 8 8 = true := by
  decide +kernel

theorem a7_78_16 : allFrom (a7Dat.rectI aIx 78) 16 8 = true := by
  decide +kernel

theorem a7_78_24 : allFrom (a7Dat.rectI aIx 78) 24 8 = true := by
  decide +kernel

theorem a7_78_32 : allFrom (a7Dat.rectI aIx 78) 32 8 = true := by
  decide +kernel

theorem a7_78_40 : allFrom (a7Dat.rectI aIx 78) 40 8 = true := by
  decide +kernel

theorem a7_78_48 : allFrom (a7Dat.rectI aIx 78) 48 8 = true := by
  decide +kernel

theorem a7_78_56 : allFrom (a7Dat.rectI aIx 78) 56 8 = true := by
  decide +kernel

theorem a7_78_64 : allFrom (a7Dat.rectI aIx 78) 64 8 = true := by
  decide +kernel

theorem a7_78_72 : allFrom (a7Dat.rectI aIx 78) 72 8 = true := by
  decide +kernel

theorem a7_78_80 : allFrom (a7Dat.rectI aIx 78) 80 8 = true := by
  decide +kernel

theorem a7_78_88 : allFrom (a7Dat.rectI aIx 78) 88 8 = true := by
  decide +kernel

theorem a7_78_96 : allFrom (a7Dat.rectI aIx 78) 96 8 = true := by
  decide +kernel

theorem a7_78_104 : allFrom (a7Dat.rectI aIx 78) 104 8 = true := by
  decide +kernel

theorem a7_78_112 : allFrom (a7Dat.rectI aIx 78) 112 8 = true := by
  decide +kernel

theorem a7_78_120 : allFrom (a7Dat.rectI aIx 78) 120 8 = true := by
  decide +kernel

theorem a7_78_128 : allFrom (a7Dat.rectI aIx 78) 128 8 = true := by
  decide +kernel

theorem a7_row_78 : a7Dat.rowI aIx 78 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 78 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 78) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 78) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 78)) a7_78_0) a7_78_8) a7_78_16) a7_78_24) a7_78_32) a7_78_40) a7_78_48) a7_78_56) a7_78_64) a7_78_72) a7_78_80) a7_78_88) a7_78_96) a7_78_104) a7_78_112) a7_78_120) a7_78_128)

theorem a7_79_0 : allFrom (a7Dat.rectI aIx 79) 0 8 = true := by
  decide +kernel

theorem a7_79_8 : allFrom (a7Dat.rectI aIx 79) 8 8 = true := by
  decide +kernel

theorem a7_79_16 : allFrom (a7Dat.rectI aIx 79) 16 8 = true := by
  decide +kernel

theorem a7_79_24 : allFrom (a7Dat.rectI aIx 79) 24 8 = true := by
  decide +kernel

theorem a7_79_32 : allFrom (a7Dat.rectI aIx 79) 32 8 = true := by
  decide +kernel

theorem a7_79_40 : allFrom (a7Dat.rectI aIx 79) 40 8 = true := by
  decide +kernel

theorem a7_79_48 : allFrom (a7Dat.rectI aIx 79) 48 8 = true := by
  decide +kernel

theorem a7_79_56 : allFrom (a7Dat.rectI aIx 79) 56 8 = true := by
  decide +kernel

theorem a7_79_64 : allFrom (a7Dat.rectI aIx 79) 64 8 = true := by
  decide +kernel

theorem a7_79_72 : allFrom (a7Dat.rectI aIx 79) 72 8 = true := by
  decide +kernel

theorem a7_79_80 : allFrom (a7Dat.rectI aIx 79) 80 8 = true := by
  decide +kernel

theorem a7_79_88 : allFrom (a7Dat.rectI aIx 79) 88 8 = true := by
  decide +kernel

theorem a7_79_96 : allFrom (a7Dat.rectI aIx 79) 96 8 = true := by
  decide +kernel

theorem a7_79_104 : allFrom (a7Dat.rectI aIx 79) 104 8 = true := by
  decide +kernel

theorem a7_79_112 : allFrom (a7Dat.rectI aIx 79) 112 8 = true := by
  decide +kernel

theorem a7_79_120 : allFrom (a7Dat.rectI aIx 79) 120 8 = true := by
  decide +kernel

theorem a7_79_128 : allFrom (a7Dat.rectI aIx 79) 128 8 = true := by
  decide +kernel

theorem a7_row_79 : a7Dat.rowI aIx 79 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 79 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 79) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 79) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 79)) a7_79_0) a7_79_8) a7_79_16) a7_79_24) a7_79_32) a7_79_40) a7_79_48) a7_79_56) a7_79_64) a7_79_72) a7_79_80) a7_79_88) a7_79_96) a7_79_104) a7_79_112) a7_79_120) a7_79_128)

theorem a7_blk_76 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 76 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 76) a7_row_76 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 77) a7_row_77 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 78) a7_row_78 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 79) a7_row_79 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 80)))))

end SandierSerfaty.CertData.Box
