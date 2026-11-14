/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 70 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1680`–`1681`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1680_0 : bothSeg evalE (oGrid.idx 1680) (oGrid.dm 1680) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1680) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73233908771455853805652604503006345884623572213577729067382100496046049848⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1680_400 : bothSeg evalE (oGrid.idx 1680) (oGrid.dm 1680) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1680) oGrid.kl oGrid.kr 400 400 ⟨false, 73233908771455853805652604503006345884623572213577729067382100496046049848⟩ ⟨false, 0⟩ ⟨false, 164059032560149233024884777784831597061509087625987650788135260276491941020⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1680_800 : bothSeg evalE (oGrid.idx 1680) (oGrid.dm 1680) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1680) oGrid.kl oGrid.kr 400 800 ⟨false, 164059032560149233024884777784831597061509087625987650788135260276491941020⟩ ⟨false, 0⟩ ⟨false, 286685444538387056558585695674937411258781767141141329632289793464239886638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1680_1200 : bothSeg evalE (oGrid.idx 1680) (oGrid.dm 1680) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1680) oGrid.kl oGrid.kr 400 1200 ⟨false, 286685444538387056558585695674937411258781767141141329632289793464239886638⟩ ⟨false, 0⟩ ⟨false, 450015309105297974566047692572146000017420498885226164117958612811544431020⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1680_1600 : bothSeg evalE (oGrid.idx 1680) (oGrid.dm 1680) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1680) oGrid.kl oGrid.kr 400 1600 ⟨false, 450015309105297974566047692572146000017420498885226164117958612811544431020⟩ ⟨false, 0⟩ ⟨false, 657785878449728137796870940154514958395513659475224607233654457015966556158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1680_2000 : bothSeg evalE (oGrid.idx 1680) (oGrid.dm 1680) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1680) oGrid.kl oGrid.kr 400 2000 ⟨false, 657785878449728137796870940154514958395513659475224607233654457015966556158⟩ ⟨false, 0⟩ ⟨false, 909438783584802955776250572675801581923404712117321191931414897974455935848⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1680_2400 : bothLoop evalE (oGrid.idx 1680) (oGrid.dm 1680) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1680) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 909438783584802955776250572675801581923404712117321191931414897974455935848⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1680 : oGrid.row evalE 1680 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1680_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1680_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1680_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1680_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1680_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1680_2000).1 (bothLoop_sound b_1680_2400).1))))))

theorem n_row_1680 : nGrid.row evalE 1680 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1680_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1680_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1680_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1680_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1680_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1680_2000).2 (bothLoop_sound b_1680_2400).2))))))

theorem b_1681_0 : bothSeg evalE (oGrid.idx 1681) (oGrid.dm 1681) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1681) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73620152161033891506868697913803167943955320297199369080240217021729008218⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1681_400 : bothSeg evalE (oGrid.idx 1681) (oGrid.dm 1681) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1681) oGrid.kl oGrid.kr 400 400 ⟨false, 73620152161033891506868697913803167943955320297199369080240217021729008218⟩ ⟨false, 0⟩ ⟨false, 164813464099574230089808208908985095667314657727794878140970358297342233980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1681_800 : bothSeg evalE (oGrid.idx 1681) (oGrid.dm 1681) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1681) oGrid.kl oGrid.kr 400 800 ⟨false, 164813464099574230089808208908985095667314657727794878140970358297342233980⟩ ⟨false, 0⟩ ⟨false, 287777552554584588440448349634347748895170726335142754985788933958006586150⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1681_1200 : bothSeg evalE (oGrid.idx 1681) (oGrid.dm 1681) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1681) oGrid.kl oGrid.kr 400 1200 ⟨false, 287777552554584588440448349634347748895170726335142754985788933958006586150⟩ ⟨false, 0⟩ ⟨false, 451410000540617242358052015770989556063358194870083243271681464405293762500⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1681_1600 : bothSeg evalE (oGrid.idx 1681) (oGrid.dm 1681) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1681) oGrid.kl oGrid.kr 400 1600 ⟨false, 451410000540617242358052015770989556063358194870083243271681464405293762500⟩ ⟨false, 0⟩ ⟨false, 659450262665246970096075537082383645562279519593088409249192044301516260692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1681_2000 : bothSeg evalE (oGrid.idx 1681) (oGrid.dm 1681) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1681) oGrid.kl oGrid.kr 400 2000 ⟨false, 659450262665246970096075537082383645562279519593088409249192044301516260692⟩ ⟨false, 0⟩ ⟨false, 911345470949327397260317545969516661973560111486666618431808110240661696344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1681_2400 : bothLoop evalE (oGrid.idx 1681) (oGrid.dm 1681) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1681) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 911345470949327397260317545969516661973560111486666618431808110240661696344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1681 : oGrid.row evalE 1681 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1681_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1681_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1681_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1681_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1681_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1681_2000).1 (bothLoop_sound b_1681_2400).1))))))

theorem n_row_1681 : nGrid.row evalE 1681 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1681_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1681_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1681_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1681_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1681_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1681_2000).2 (bothLoop_sound b_1681_2400).2))))))

theorem o_blk_1680 : allFrom (fun j => oGrid.row evalE j) 1680 2 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1680) o_row_1680 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1681) o_row_1681 (allFrom_zero (fun j => oGrid.row evalE j) 1682)))

theorem n_blk_1680 : allFrom (fun j => nGrid.row evalE j) 1680 2 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1680) n_row_1680 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1681) n_row_1681 (allFrom_zero (fun j => nGrid.row evalE j) 1682)))

end SandierSerfaty.CertData.Box
