/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The A7 rectangles, shard 17 (kernel)

Blocks of `aSeg` rectangles (`allFrom (a7Dat.rectI aIx j)`, checked index), the rows, the block. Rows `68`–`71`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7_68_0 : allFrom (a7Dat.rectI aIx 68) 0 8 = true := by
  decide +kernel

theorem a7_68_8 : allFrom (a7Dat.rectI aIx 68) 8 8 = true := by
  decide +kernel

theorem a7_68_16 : allFrom (a7Dat.rectI aIx 68) 16 8 = true := by
  decide +kernel

theorem a7_68_24 : allFrom (a7Dat.rectI aIx 68) 24 8 = true := by
  decide +kernel

theorem a7_68_32 : allFrom (a7Dat.rectI aIx 68) 32 8 = true := by
  decide +kernel

theorem a7_68_40 : allFrom (a7Dat.rectI aIx 68) 40 8 = true := by
  decide +kernel

theorem a7_68_48 : allFrom (a7Dat.rectI aIx 68) 48 8 = true := by
  decide +kernel

theorem a7_68_56 : allFrom (a7Dat.rectI aIx 68) 56 8 = true := by
  decide +kernel

theorem a7_68_64 : allFrom (a7Dat.rectI aIx 68) 64 8 = true := by
  decide +kernel

theorem a7_68_72 : allFrom (a7Dat.rectI aIx 68) 72 8 = true := by
  decide +kernel

theorem a7_68_80 : allFrom (a7Dat.rectI aIx 68) 80 8 = true := by
  decide +kernel

theorem a7_68_88 : allFrom (a7Dat.rectI aIx 68) 88 8 = true := by
  decide +kernel

theorem a7_68_96 : allFrom (a7Dat.rectI aIx 68) 96 8 = true := by
  decide +kernel

theorem a7_68_104 : allFrom (a7Dat.rectI aIx 68) 104 8 = true := by
  decide +kernel

theorem a7_68_112 : allFrom (a7Dat.rectI aIx 68) 112 8 = true := by
  decide +kernel

theorem a7_68_120 : allFrom (a7Dat.rectI aIx 68) 120 8 = true := by
  decide +kernel

theorem a7_68_128 : allFrom (a7Dat.rectI aIx 68) 128 8 = true := by
  decide +kernel

theorem a7_row_68 : a7Dat.rowI aIx 68 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 68 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 68) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 68) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 68)) a7_68_0) a7_68_8) a7_68_16) a7_68_24) a7_68_32) a7_68_40) a7_68_48) a7_68_56) a7_68_64) a7_68_72) a7_68_80) a7_68_88) a7_68_96) a7_68_104) a7_68_112) a7_68_120) a7_68_128)

theorem a7_69_0 : allFrom (a7Dat.rectI aIx 69) 0 8 = true := by
  decide +kernel

theorem a7_69_8 : allFrom (a7Dat.rectI aIx 69) 8 8 = true := by
  decide +kernel

theorem a7_69_16 : allFrom (a7Dat.rectI aIx 69) 16 8 = true := by
  decide +kernel

theorem a7_69_24 : allFrom (a7Dat.rectI aIx 69) 24 8 = true := by
  decide +kernel

theorem a7_69_32 : allFrom (a7Dat.rectI aIx 69) 32 8 = true := by
  decide +kernel

theorem a7_69_40 : allFrom (a7Dat.rectI aIx 69) 40 8 = true := by
  decide +kernel

theorem a7_69_48 : allFrom (a7Dat.rectI aIx 69) 48 8 = true := by
  decide +kernel

theorem a7_69_56 : allFrom (a7Dat.rectI aIx 69) 56 8 = true := by
  decide +kernel

theorem a7_69_64 : allFrom (a7Dat.rectI aIx 69) 64 8 = true := by
  decide +kernel

theorem a7_69_72 : allFrom (a7Dat.rectI aIx 69) 72 8 = true := by
  decide +kernel

theorem a7_69_80 : allFrom (a7Dat.rectI aIx 69) 80 8 = true := by
  decide +kernel

theorem a7_69_88 : allFrom (a7Dat.rectI aIx 69) 88 8 = true := by
  decide +kernel

theorem a7_69_96 : allFrom (a7Dat.rectI aIx 69) 96 8 = true := by
  decide +kernel

theorem a7_69_104 : allFrom (a7Dat.rectI aIx 69) 104 8 = true := by
  decide +kernel

theorem a7_69_112 : allFrom (a7Dat.rectI aIx 69) 112 8 = true := by
  decide +kernel

theorem a7_69_120 : allFrom (a7Dat.rectI aIx 69) 120 8 = true := by
  decide +kernel

theorem a7_69_128 : allFrom (a7Dat.rectI aIx 69) 128 8 = true := by
  decide +kernel

theorem a7_row_69 : a7Dat.rowI aIx 69 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 69 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 69) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 69) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 69)) a7_69_0) a7_69_8) a7_69_16) a7_69_24) a7_69_32) a7_69_40) a7_69_48) a7_69_56) a7_69_64) a7_69_72) a7_69_80) a7_69_88) a7_69_96) a7_69_104) a7_69_112) a7_69_120) a7_69_128)

theorem a7_70_0 : allFrom (a7Dat.rectI aIx 70) 0 8 = true := by
  decide +kernel

theorem a7_70_8 : allFrom (a7Dat.rectI aIx 70) 8 8 = true := by
  decide +kernel

theorem a7_70_16 : allFrom (a7Dat.rectI aIx 70) 16 8 = true := by
  decide +kernel

theorem a7_70_24 : allFrom (a7Dat.rectI aIx 70) 24 8 = true := by
  decide +kernel

theorem a7_70_32 : allFrom (a7Dat.rectI aIx 70) 32 8 = true := by
  decide +kernel

theorem a7_70_40 : allFrom (a7Dat.rectI aIx 70) 40 8 = true := by
  decide +kernel

theorem a7_70_48 : allFrom (a7Dat.rectI aIx 70) 48 8 = true := by
  decide +kernel

theorem a7_70_56 : allFrom (a7Dat.rectI aIx 70) 56 8 = true := by
  decide +kernel

theorem a7_70_64 : allFrom (a7Dat.rectI aIx 70) 64 8 = true := by
  decide +kernel

theorem a7_70_72 : allFrom (a7Dat.rectI aIx 70) 72 8 = true := by
  decide +kernel

theorem a7_70_80 : allFrom (a7Dat.rectI aIx 70) 80 8 = true := by
  decide +kernel

theorem a7_70_88 : allFrom (a7Dat.rectI aIx 70) 88 8 = true := by
  decide +kernel

theorem a7_70_96 : allFrom (a7Dat.rectI aIx 70) 96 8 = true := by
  decide +kernel

theorem a7_70_104 : allFrom (a7Dat.rectI aIx 70) 104 8 = true := by
  decide +kernel

theorem a7_70_112 : allFrom (a7Dat.rectI aIx 70) 112 8 = true := by
  decide +kernel

theorem a7_70_120 : allFrom (a7Dat.rectI aIx 70) 120 8 = true := by
  decide +kernel

theorem a7_70_128 : allFrom (a7Dat.rectI aIx 70) 128 8 = true := by
  decide +kernel

theorem a7_row_70 : a7Dat.rowI aIx 70 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 70 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 70) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 70) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 70)) a7_70_0) a7_70_8) a7_70_16) a7_70_24) a7_70_32) a7_70_40) a7_70_48) a7_70_56) a7_70_64) a7_70_72) a7_70_80) a7_70_88) a7_70_96) a7_70_104) a7_70_112) a7_70_120) a7_70_128)

theorem a7_71_0 : allFrom (a7Dat.rectI aIx 71) 0 8 = true := by
  decide +kernel

theorem a7_71_8 : allFrom (a7Dat.rectI aIx 71) 8 8 = true := by
  decide +kernel

theorem a7_71_16 : allFrom (a7Dat.rectI aIx 71) 16 8 = true := by
  decide +kernel

theorem a7_71_24 : allFrom (a7Dat.rectI aIx 71) 24 8 = true := by
  decide +kernel

theorem a7_71_32 : allFrom (a7Dat.rectI aIx 71) 32 8 = true := by
  decide +kernel

theorem a7_71_40 : allFrom (a7Dat.rectI aIx 71) 40 8 = true := by
  decide +kernel

theorem a7_71_48 : allFrom (a7Dat.rectI aIx 71) 48 8 = true := by
  decide +kernel

theorem a7_71_56 : allFrom (a7Dat.rectI aIx 71) 56 8 = true := by
  decide +kernel

theorem a7_71_64 : allFrom (a7Dat.rectI aIx 71) 64 8 = true := by
  decide +kernel

theorem a7_71_72 : allFrom (a7Dat.rectI aIx 71) 72 8 = true := by
  decide +kernel

theorem a7_71_80 : allFrom (a7Dat.rectI aIx 71) 80 8 = true := by
  decide +kernel

theorem a7_71_88 : allFrom (a7Dat.rectI aIx 71) 88 8 = true := by
  decide +kernel

theorem a7_71_96 : allFrom (a7Dat.rectI aIx 71) 96 8 = true := by
  decide +kernel

theorem a7_71_104 : allFrom (a7Dat.rectI aIx 71) 104 8 = true := by
  decide +kernel

theorem a7_71_112 : allFrom (a7Dat.rectI aIx 71) 112 8 = true := by
  decide +kernel

theorem a7_71_120 : allFrom (a7Dat.rectI aIx 71) 120 8 = true := by
  decide +kernel

theorem a7_71_128 : allFrom (a7Dat.rectI aIx 71) 128 8 = true := by
  decide +kernel

theorem a7_row_71 : a7Dat.rowI aIx 71 a7Dat.nk = true :=
  (a7rowI_eq_allLt a7Dat aIx 71 a7Dat.nk).trans
    (allLt_add (f := a7Dat.rectI aIx 71) (n := 128) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 120) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 112) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 104) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 96) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 88) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 80) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 72) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 64) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 56) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 48) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 40) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 32) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 24) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 16) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 8) (m := 8) (allLt_add (f := a7Dat.rectI aIx 71) (n := 0) (m := 8) (allLt_zero (a7Dat.rectI aIx 71)) a7_71_0) a7_71_8) a7_71_16) a7_71_24) a7_71_32) a7_71_40) a7_71_48) a7_71_56) a7_71_64) a7_71_72) a7_71_80) a7_71_88) a7_71_96) a7_71_104) a7_71_112) a7_71_120) a7_71_128)

theorem a7_blk_68 : allFrom (fun j => a7Dat.rowI aIx j a7Dat.nk) 68 4 = true :=
  (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 68) a7_row_68 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 69) a7_row_69 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 70) a7_row_70 (allFrom_cons (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (a := 71) a7_row_71 (allFrom_zero (fun j => a7Dat.rowI aIx j a7Dat.nk) 72)))))

end SandierSerfaty.CertData.Box
