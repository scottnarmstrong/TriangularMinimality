/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 59 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1416`–`1439`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1416_0 : bothSeg evalE (oGrid.idx 1416) (oGrid.dm 1416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1416) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 22227863242946822215797272226011993187816523833430340408625991423597014484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1416_400 : bothSeg evalE (oGrid.idx 1416) (oGrid.dm 1416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1416) oGrid.kl oGrid.kr 400 400 ⟨false, 22227863242946822215797272226011993187816523833430340408625991423597014484⟩ ⟨false, 0⟩ ⟨false, 67178851055249752656467623892895530529825688898031786382219711199648997890⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1416_800 : bothSeg evalE (oGrid.idx 1416) (oGrid.dm 1416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1416) oGrid.kl oGrid.kr 400 800 ⟨false, 67178851055249752656467623892895530529825688898031786382219711199648997890⟩ ⟨false, 0⟩ ⟨false, 128767274156115484910143009195867076713796397865276677444632999404016609840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1416_1200 : bothSeg evalE (oGrid.idx 1416) (oGrid.dm 1416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1416) oGrid.kl oGrid.kr 400 1200 ⟨false, 128767274156115484910143009195867076713796397865276677444632999404016609840⟩ ⟨false, 0⟩ ⟨false, 211436264237972201091279597854514472075311591567852797513688224250823649004⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1416_1600 : bothSeg evalE (oGrid.idx 1416) (oGrid.dm 1416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1416) oGrid.kl oGrid.kr 400 1600 ⟨false, 211436264237972201091279597854514472075311591567852797513688224250823649004⟩ ⟨false, 0⟩ ⟨false, 348303757550623913057926681970736226519131764811400866012811116843266228922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1416_2000 : bothSeg evalE (oGrid.idx 1416) (oGrid.dm 1416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1416) oGrid.kl oGrid.kr 400 2000 ⟨false, 348303757550623913057926681970736226519131764811400866012811116843266228922⟩ ⟨false, 0⟩ ⟨false, 536913270822004822223697306845730328513026682777080328837896734877320830310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1416_2400 : bothLoop evalE (oGrid.idx 1416) (oGrid.dm 1416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1416) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 536913270822004822223697306845730328513026682777080328837896734877320830310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1416 : oGrid.row evalE 1416 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1416_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1416_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1416_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1416_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1416_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1416_2000).1 (bothLoop_sound b_1416_2400).1))))))

theorem n_row_1416 : nGrid.row evalE 1416 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1416_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1416_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1416_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1416_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1416_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1416_2000).2 (bothLoop_sound b_1416_2400).2))))))

theorem b_1417_0 : bothSeg evalE (oGrid.idx 1417) (oGrid.dm 1417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1417) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 22645521119585090402738602708066694184161403102388742038155010307537088710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1417_400 : bothSeg evalE (oGrid.idx 1417) (oGrid.dm 1417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1417) oGrid.kl oGrid.kr 400 400 ⟨false, 22645521119585090402738602708066694184161403102388742038155010307537088710⟩ ⟨false, 0⟩ ⟨false, 68062863492592032579802276538755586203626989707601850012826158616378407492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1417_800 : bothSeg evalE (oGrid.idx 1417) (oGrid.dm 1417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1417) oGrid.kl oGrid.kr 400 800 ⟨false, 68062863492592032579802276538755586203626989707601850012826158616378407492⟩ ⟨false, 0⟩ ⟨false, 129629457355361015947525022384078022359145261821021490978921021760727246114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1417_1200 : bothSeg evalE (oGrid.idx 1417) (oGrid.dm 1417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1417) oGrid.kl oGrid.kr 400 1200 ⟨false, 129629457355361015947525022384078022359145261821021490978921021760727246114⟩ ⟨false, 0⟩ ⟨false, 212605634355254260524415667464176076587033688044964856626667639141793747044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1417_1600 : bothSeg evalE (oGrid.idx 1417) (oGrid.dm 1417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1417) oGrid.kl oGrid.kr 400 1600 ⟨false, 212605634355254260524415667464176076587033688044964856626667639141793747044⟩ ⟨false, 0⟩ ⟨false, 349739972741897986853492407189947073375450663556359066205466739785789895512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1417_2000 : bothSeg evalE (oGrid.idx 1417) (oGrid.dm 1417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1417) oGrid.kl oGrid.kr 400 2000 ⟨false, 349739972741897986853492407189947073375450663556359066205466739785789895512⟩ ⟨false, 0⟩ ⟨false, 538584156163907264562023042620663768869389235222565212517493593618696031856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1417_2400 : bothLoop evalE (oGrid.idx 1417) (oGrid.dm 1417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1417) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 538584156163907264562023042620663768869389235222565212517493593618696031856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1417 : oGrid.row evalE 1417 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1417_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1417_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1417_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1417_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1417_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1417_2000).1 (bothLoop_sound b_1417_2400).1))))))

theorem n_row_1417 : nGrid.row evalE 1417 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1417_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1417_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1417_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1417_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1417_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1417_2000).2 (bothLoop_sound b_1417_2400).2))))))

theorem b_1418_0 : bothSeg evalE (oGrid.idx 1418) (oGrid.dm 1418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1418) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 23063709416073914312607898197073007330006191377436046143054595225830109416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1418_400 : bothSeg evalE (oGrid.idx 1418) (oGrid.dm 1418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1418) oGrid.kl oGrid.kr 400 400 ⟨false, 23063709416073914312607898197073007330006191377436046143054595225830109416⟩ ⟨false, 0⟩ ⟨false, 68948452004928931692609320170621270988100654950188515740873693109182823004⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1418_800 : bothSeg evalE (oGrid.idx 1418) (oGrid.dm 1418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1418) oGrid.kl oGrid.kr 400 800 ⟨false, 68948452004928931692609320170621270988100654950188515740873693109182823004⟩ ⟨false, 0⟩ ⟨false, 130491003535566480641274057823021509902814053963378308628542224967897244620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1418_1200 : bothSeg evalE (oGrid.idx 1418) (oGrid.dm 1418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1418) oGrid.kl oGrid.kr 400 1200 ⟨false, 130491003535566480641274057823021509902814053963378308628542224967897244620⟩ ⟨false, 0⟩ ⟨false, 213774402325920690641098836224484086949358425407281938675577748482209738746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1418_1600 : bothSeg evalE (oGrid.idx 1418) (oGrid.dm 1418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1418) oGrid.kl oGrid.kr 400 1600 ⟨false, 213774402325920690641098836224484086949358425407281938675577748482209738746⟩ ⟨false, 0⟩ ⟨false, 351175604162906049338533953084331797242430425646226526880904529497370558666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1418_2000 : bothSeg evalE (oGrid.idx 1418) (oGrid.dm 1418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1418) oGrid.kl oGrid.kr 400 2000 ⟨false, 351175604162906049338533953084331797242430425646226526880904529497370558666⟩ ⟨false, 0⟩ ⟨false, 540254494531985615199160689802993651712987822364969818209368427832481948318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1418_2400 : bothLoop evalE (oGrid.idx 1418) (oGrid.dm 1418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1418) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 540254494531985615199160689802993651712987822364969818209368427832481948318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1418 : oGrid.row evalE 1418 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1418_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1418_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1418_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1418_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1418_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1418_2000).1 (bothLoop_sound b_1418_2400).1))))))

theorem n_row_1418 : nGrid.row evalE 1418 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1418_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1418_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1418_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1418_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1418_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1418_2000).2 (bothLoop_sound b_1418_2400).2))))))

theorem b_1419_0 : bothSeg evalE (oGrid.idx 1419) (oGrid.dm 1419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1419) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 23482427435618257927919294679969744342060891498641237045475331373447796976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1419_400 : bothSeg evalE (oGrid.idx 1419) (oGrid.dm 1419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1419) oGrid.kl oGrid.kr 400 400 ⟨false, 23482427435618257927919294679969744342060891498641237045475331373447796976⟩ ⟨false, 0⟩ ⟨false, 69835508764613932585617700655939278397539491939466355335368580343623863248⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1419_800 : bothSeg evalE (oGrid.idx 1419) (oGrid.dm 1419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1419) oGrid.kl oGrid.kr 400 800 ⟨false, 69835508764613932585617700655939278397539491939466355335368580343623863248⟩ ⟨false, 0⟩ ⟨false, 131351873644470997640888923416964063037895929005244064909269378333415556504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1419_1200 : bothSeg evalE (oGrid.idx 1419) (oGrid.dm 1419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1419) oGrid.kl oGrid.kr 400 1200 ⟨false, 131351873644470997640888923416964063037895929005244064909269378333415556504⟩ ⟨false, 0⟩ ⟨false, 214942533189526149449419657490226783809175653030476754807516541812263821376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1419_1600 : bothSeg evalE (oGrid.idx 1419) (oGrid.dm 1419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1419) oGrid.kl oGrid.kr 400 1600 ⟨false, 214942533189526149449419657490226783809175653030476754807516541812263821376⟩ ⟨false, 0⟩ ⟨false, 352610616785782942665036275873534495640625050043465863962527464716483352210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1419_2000 : bothSeg evalE (oGrid.idx 1419) (oGrid.dm 1419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1419) oGrid.kl oGrid.kr 400 2000 ⟨false, 352610616785782942665036275873534495640625050043465863962527464716483352210⟩ ⟨false, 0⟩ ⟨false, 541924250831383781662066231699806731718283025339059583771117568020836038542⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1419_2400 : bothLoop evalE (oGrid.idx 1419) (oGrid.dm 1419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1419) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 541924250831383781662066231699806731718283025339059583771117568020836038542⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1419 : oGrid.row evalE 1419 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1419_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1419_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1419_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1419_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1419_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1419_2000).1 (bothLoop_sound b_1419_2400).1))))))

theorem n_row_1419 : nGrid.row evalE 1419 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1419_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1419_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1419_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1419_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1419_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1419_2000).2 (bothLoop_sound b_1419_2400).2))))))

theorem b_1420_0 : bothSeg evalE (oGrid.idx 1420) (oGrid.dm 1420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1420) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 23901673683790422225808718126469374672528833755227432539789317720475377676⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1420_400 : bothSeg evalE (oGrid.idx 1420) (oGrid.dm 1420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1420) oGrid.kl oGrid.kr 400 400 ⟨false, 23901673683790422225808718126469374672528833755227432539789317720475377676⟩ ⟨false, 0⟩ ⟨false, 70723939375455477814073715130555871933900881959115014867367501689022575500⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1420_800 : bothSeg evalE (oGrid.idx 1420) (oGrid.dm 1420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1420) oGrid.kl oGrid.kr 400 800 ⟨false, 70723939375455477814073715130555871933900881959115014867367501689022575500⟩ ⟨false, 0⟩ ⟨false, 132212060946399338666194361124852775137940331337077208035111683897890570736⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1420_1200 : bothSeg evalE (oGrid.idx 1420) (oGrid.dm 1420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1420) oGrid.kl oGrid.kr 400 1200 ⟨false, 132212060946399338666194361124852775137940331337077208035111683897890570736⟩ ⟨false, 0⟩ ⟨false, 216110023380972513827447322726046254599103860965844609213769471793329570160⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1420_1600 : bothSeg evalE (oGrid.idx 1420) (oGrid.dm 1420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1420) oGrid.kl oGrid.kr 400 1600 ⟨false, 216110023380972513827447322726046254599103860965844609213769471793329570160⟩ ⟨false, 0⟩ ⟨false, 354045006978133522061468080785857941864805692584767165421417989625114050728⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1420_2000 : bothSeg evalE (oGrid.idx 1420) (oGrid.dm 1420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1420) oGrid.kl oGrid.kr 400 2000 ⟨false, 354045006978133522061468080785857941864805692584767165421417989625114050728⟩ ⟨false, 0⟩ ⟨false, 543593421362801483209243675502243298804298580006400974253706629460922515596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1420_2400 : bothLoop evalE (oGrid.idx 1420) (oGrid.dm 1420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1420) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 543593421362801483209243675502243298804298580006400974253706629460922515596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1420 : oGrid.row evalE 1420 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1420_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1420_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1420_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1420_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1420_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1420_2000).1 (bothLoop_sound b_1420_2400).1))))))

theorem n_row_1420 : nGrid.row evalE 1420 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1420_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1420_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1420_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1420_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1420_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1420_2000).2 (bothLoop_sound b_1420_2400).2))))))

theorem b_1421_0 : bothSeg evalE (oGrid.idx 1421) (oGrid.dm 1421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1421) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 24321442839135551033348355023001482044989203960593658735394892466345437602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1421_400 : bothSeg evalE (oGrid.idx 1421) (oGrid.dm 1421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1421) oGrid.kl oGrid.kr 400 400 ⟨false, 24321442839135551033348355023001482044989203960593658735394892466345437602⟩ ⟨false, 0⟩ ⟨false, 71613618156783221445590357789797266368352996434984390138274573576864237202⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1421_800 : bothSeg evalE (oGrid.idx 1421) (oGrid.dm 1421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1421) oGrid.kl oGrid.kr 400 800 ⟨false, 71613618156783221445590357789797266368352996434984390138274573576864237202⟩ ⟨false, 0⟩ ⟨false, 133071509241425662347284546341287335130982075891604433891654215949310965170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1421_1200 : bothSeg evalE (oGrid.idx 1421) (oGrid.dm 1421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1421) oGrid.kl oGrid.kr 400 1200 ⟨false, 133071509241425662347284546341287335130982075891604433891654215949310965170⟩ ⟨false, 0⟩ ⟨false, 217276818321285474675026337850161926918586596676726490233394105098046808862⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1421_1600 : bothSeg evalE (oGrid.idx 1421) (oGrid.dm 1421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1421) oGrid.kl oGrid.kr 400 1600 ⟨false, 217276818321285474675026337850161926918586596676726490233394105098046808862⟩ ⟨false, 0⟩ ⟨false, 355478720093809060047655734198650168983162482074054107166581988659279786200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1421_2000 : bothSeg evalE (oGrid.idx 1421) (oGrid.dm 1421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1421) oGrid.kl oGrid.kr 400 2000 ⟨false, 355478720093809060047655734198650168983162482074054107166581988659279786200⟩ ⟨false, 0⟩ ⟨false, 545261951413270575340449682224033532727372969598595596900678855607253294426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1421_2400 : bothLoop evalE (oGrid.idx 1421) (oGrid.dm 1421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1421) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 545261951413270575340449682224033532727372969598595596900678855607253294426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1421 : oGrid.row evalE 1421 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1421_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1421_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1421_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1421_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1421_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1421_2000).1 (bothLoop_sound b_1421_2400).1))))))

theorem n_row_1421 : nGrid.row evalE 1421 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1421_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1421_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1421_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1421_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1421_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1421_2000).2 (bothLoop_sound b_1421_2400).2))))))

theorem b_1422_0 : bothSeg evalE (oGrid.idx 1422) (oGrid.dm 1422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1422) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 24741738651859980730244320666216976043780740654447193470104426359071815154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1422_400 : bothSeg evalE (oGrid.idx 1422) (oGrid.dm 1422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1422) oGrid.kl oGrid.kr 400 400 ⟨false, 24741738651859980730244320666216976043780740654447193470104426359071815154⟩ ⟨false, 0⟩ ⟨false, 72504447123547624105212838775813085155175046611900380007775056454817347056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1422_800 : bothSeg evalE (oGrid.idx 1422) (oGrid.dm 1422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1422) oGrid.kl oGrid.kr 400 800 ⟨false, 72504447123547624105212838775813085155175046611900380007775056454817347056⟩ ⟨false, 0⟩ ⟨false, 133930219201858850839092693163582223579630046219273651009382220836620048098⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1422_1200 : bothSeg evalE (oGrid.idx 1422) (oGrid.dm 1422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1422) oGrid.kl oGrid.kr 400 1200 ⟨false, 133930219201858850839092693163582223579630046219273651009382220836620048098⟩ ⟨false, 0⟩ ⟨false, 218442921455610905456484966201061270537732136356942657809909850268680065414⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1422_1600 : bothSeg evalE (oGrid.idx 1422) (oGrid.dm 1422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1422) oGrid.kl oGrid.kr 400 1600 ⟨false, 218442921455610905456484966201061270537732136356942657809909850268680065414⟩ ⟨false, 0⟩ ⟨false, 356911759510903424275050736180698199927144520366176819182639976779367357590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1422_2000 : bothSeg evalE (oGrid.idx 1422) (oGrid.dm 1422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1422) oGrid.kl oGrid.kr 400 2000 ⟨false, 356911759510903424275050736180698199927144520366176819182639976779367357590⟩ ⟨false, 0⟩ ⟨false, 546929844294151147922277705437215499335294380438963956579503992824125833952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1422_2400 : bothLoop evalE (oGrid.idx 1422) (oGrid.dm 1422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1422) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 546929844294151147922277705437215499335294380438963956579503992824125833952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1422 : oGrid.row evalE 1422 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1422_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1422_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1422_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1422_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1422_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1422_2000).1 (bothLoop_sound b_1422_2400).1))))))

theorem n_row_1422 : nGrid.row evalE 1422 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1422_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1422_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1422_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1422_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1422_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1422_2000).2 (bothLoop_sound b_1422_2400).2))))))

theorem b_1423_0 : bothSeg evalE (oGrid.idx 1423) (oGrid.dm 1423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1423) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 25162560778337318386722847174873116299392421382115778573166730009587894284⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1423_400 : bothSeg evalE (oGrid.idx 1423) (oGrid.dm 1423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1423) oGrid.kl oGrid.kr 400 400 ⟨false, 25162560778337318386722847174873116299392421382115778573166730009587894284⟩ ⟨false, 0⟩ ⟨false, 73396295441841666487937783260253111640080169656550269878465724495628123028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1423_800 : bothSeg evalE (oGrid.idx 1423) (oGrid.dm 1423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1423) oGrid.kl oGrid.kr 400 800 ⟨false, 73396295441841666487937783260253111640080169656550269878465724495628123028⟩ ⟨false, 0⟩ ⟨false, 134788148417605312410051346279653424091363258195022640041840493269395737060⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1423_1200 : bothSeg evalE (oGrid.idx 1423) (oGrid.dm 1423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1423) oGrid.kl oGrid.kr 400 1200 ⟨false, 134788148417605312410051346279653424091363258195022640041840493269395737060⟩ ⟨false, 0⟩ ⟨false, 219608292208831305891972598025524716932065990685860447857069433814360497930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1423_1600 : bothSeg evalE (oGrid.idx 1423) (oGrid.dm 1423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1423) oGrid.kl oGrid.kr 400 1600 ⟨false, 219608292208831305891972598025524716932065990685860447857069433814360497930⟩ ⟨false, 0⟩ ⟨false, 358344084587369330750057609701565745505012860475839498667196709181671599176⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1423_2000 : bothSeg evalE (oGrid.idx 1423) (oGrid.dm 1423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1423) oGrid.kl oGrid.kr 400 2000 ⟨false, 358344084587369330750057609701565745505012860475839498667196709181671599176⟩ ⟨false, 0⟩ ⟨false, 548597059296747698687625216994473241169836473111330658837517155562551757594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1423_2400 : bothLoop evalE (oGrid.idx 1423) (oGrid.dm 1423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1423) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 548597059296747698687625216994473241169836473111330658837517155562551757594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1423 : oGrid.row evalE 1423 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1423_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1423_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1423_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1423_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1423_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1423_2000).1 (bothLoop_sound b_1423_2400).1))))))

theorem n_row_1423 : nGrid.row evalE 1423 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1423_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1423_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1423_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1423_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1423_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1423_2000).2 (bothLoop_sound b_1423_2400).2))))))

theorem b_1424_0 : bothSeg evalE (oGrid.idx 1424) (oGrid.dm 1424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1424) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 25583910514868664920675629711234239565016703763101220007715465408578707660⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1424_400 : bothSeg evalE (oGrid.idx 1424) (oGrid.dm 1424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1424) oGrid.kl oGrid.kr 400 400 ⟨false, 25583910514868664920675629711234239565016703763101220007715465408578707660⟩ ⟨false, 0⟩ ⟨false, 74289051364463989315957300939353837151791466495123733875577203668913043794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1424_800 : bothSeg evalE (oGrid.idx 1424) (oGrid.dm 1424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1424) oGrid.kl oGrid.kr 400 800 ⟨false, 74289051364463989315957300939353837151791466495123733875577203668913043794⟩ ⟨false, 0⟩ ⟨false, 135645286138946545218951615664811506125499881246988179562461615965608541620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1424_1200 : bothSeg evalE (oGrid.idx 1424) (oGrid.dm 1424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1424) oGrid.kl oGrid.kr 400 1200 ⟨false, 135645286138946545218951615664811506125499881246988179562461615965608541620⟩ ⟨false, 0⟩ ⟨false, 220772921067240104873226160241798751444971977812769679720417964445727052968⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1424_1600 : bothSeg evalE (oGrid.idx 1424) (oGrid.dm 1424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1424) oGrid.kl oGrid.kr 400 1600 ⟨false, 220772921067240104873226160241798751444971977812769679720417964445727052968⟩ ⟨false, 0⟩ ⟨false, 359775685742692456516170863799341668004579554995767025301187507198743991940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1424_2000 : bothSeg evalE (oGrid.idx 1424) (oGrid.dm 1424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1424) oGrid.kl oGrid.kr 400 2000 ⟨false, 359775685742692456516170863799341668004579554995767025301187507198743991940⟩ ⟨false, 0⟩ ⟨false, 550263586773983166185128176150408892718857715337041492817084992175839611514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1424_2400 : bothLoop evalE (oGrid.idx 1424) (oGrid.dm 1424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1424) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 550263586773983166185128176150408892718857715337041492817084992175839611514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1424 : oGrid.row evalE 1424 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1424_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1424_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1424_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1424_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1424_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1424_2000).1 (bothLoop_sound b_1424_2400).1))))))

theorem n_row_1424 : nGrid.row evalE 1424 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1424_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1424_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1424_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1424_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1424_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1424_2000).2 (bothLoop_sound b_1424_2400).2))))))

theorem b_1425_0 : bothSeg evalE (oGrid.idx 1425) (oGrid.dm 1425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1425) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 26005791859496893334623584859413441544204427809089464945765371800395543634⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1425_400 : bothSeg evalE (oGrid.idx 1425) (oGrid.dm 1425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1425) oGrid.kl oGrid.kr 400 400 ⟨false, 26005791859496893334623584859413441544204427809089464945765371800395543634⟩ ⟨false, 0⟩ ⟨false, 75182580972830748274618480121056627936795102290163857560138714269737341526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1425_800 : bothSeg evalE (oGrid.idx 1425) (oGrid.dm 1425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1425) oGrid.kl oGrid.kr 400 800 ⟨false, 75182580972830748274618480121056627936795102290163857560138714269737341526⟩ ⟨false, 0⟩ ⟨false, 136501598111211271945836857888999053416863201785063122500039190241468050910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1425_1200 : bothSeg evalE (oGrid.idx 1425) (oGrid.dm 1425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1425) oGrid.kl oGrid.kr 400 1200 ⟨false, 136501598111211271945836857888999053416863201785063122500039190241468050910⟩ ⟨false, 0⟩ ⟨false, 221936774037134261825642225212384112327901362304968098365123380435697939338⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1425_1600 : bothSeg evalE (oGrid.idx 1425) (oGrid.dm 1425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1425) oGrid.kl oGrid.kr 400 1600 ⟨false, 221936774037134261825642225212384112327901362304968098365123380435697939338⟩ ⟨false, 0⟩ ⟨false, 361206528916483851016745086146922548354652469389129626218302059029414807380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1425_2000 : bothSeg evalE (oGrid.idx 1425) (oGrid.dm 1425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1425) oGrid.kl oGrid.kr 400 2000 ⟨false, 361206528916483851016745086146922548354652469389129626218302059029414807380⟩ ⟨false, 0⟩ ⟨false, 551929392598991261400721076828893408110182388918233977226180975473029666474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1425_2400 : bothLoop evalE (oGrid.idx 1425) (oGrid.dm 1425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1425) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 551929392598991261400721076828893408110182388918233977226180975473029666474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1425 : oGrid.row evalE 1425 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1425_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1425_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1425_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1425_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1425_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1425_2000).1 (bothLoop_sound b_1425_2400).1))))))

theorem n_row_1425 : nGrid.row evalE 1425 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1425_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1425_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1425_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1425_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1425_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1425_2000).2 (bothLoop_sound b_1425_2400).2))))))

theorem b_1426_0 : bothSeg evalE (oGrid.idx 1426) (oGrid.dm 1426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1426) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 26428207788271621373183038379633061262121969018293868986193583324795087364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1426_400 : bothSeg evalE (oGrid.idx 1426) (oGrid.dm 1426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1426) oGrid.kl oGrid.kr 400 400 ⟨false, 26428207788271621373183038379633061262121969018293868986193583324795087364⟩ ⟨false, 0⟩ ⟨false, 76076755394255277559358297030395116959373171471172381902037200042871136760⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1426_800 : bothSeg evalE (oGrid.idx 1426) (oGrid.dm 1426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1426) oGrid.kl oGrid.kr 400 800 ⟨false, 76076755394255277559358297030395116959373171471172381902037200042871136760⟩ ⟨false, 0⟩ ⟨false, 137357056584527820902826560985395868201367060494417606151253564019001281178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1426_1200 : bothSeg evalE (oGrid.idx 1426) (oGrid.dm 1426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1426) oGrid.kl oGrid.kr 400 1200 ⟨false, 137357056584527820902826560985395868201367060494417606151253564019001281178⟩ ⟨false, 0⟩ ⟨false, 223099821954036804571985685454580905137188032723290388692585908252153049754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1426_1600 : bothSeg evalE (oGrid.idx 1426) (oGrid.dm 1426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1426) oGrid.kl oGrid.kr 400 1600 ⟨false, 223099821954036804571985685454580905137188032723290388692585908252153049754⟩ ⟨false, 0⟩ ⟨false, 362636584877702284193675287793865775852481876188310512194303312213634201350⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1426_2000 : bothSeg evalE (oGrid.idx 1426) (oGrid.dm 1426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1426) oGrid.kl oGrid.kr 400 2000 ⟨false, 362636584877702284193675287793865775852481876188310512194303312213634201350⟩ ⟨false, 0⟩ ⟨false, 553594447474338736106932758292439877799833059144733739448200963082402825846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1426_2400 : bothLoop evalE (oGrid.idx 1426) (oGrid.dm 1426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1426) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 553594447474338736106932758292439877799833059144733739448200963082402825846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1426 : oGrid.row evalE 1426 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1426_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1426_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1426_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1426_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1426_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1426_2000).1 (bothLoop_sound b_1426_2400).1))))))

theorem n_row_1426 : nGrid.row evalE 1426 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1426_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1426_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1426_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1426_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1426_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1426_2000).2 (bothLoop_sound b_1426_2400).2))))))

theorem b_1427_0 : bothSeg evalE (oGrid.idx 1427) (oGrid.dm 1427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1427) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 26851164727671957900803981028906900500857456209085015237898085946079379638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1427_400 : bothSeg evalE (oGrid.idx 1427) (oGrid.dm 1427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1427) oGrid.kl oGrid.kr 400 400 ⟨false, 26851164727671957900803981028906900500857456209085015237898085946079379638⟩ ⟨false, 0⟩ ⟨false, 76971437859339866653749085394816598346361573202517229403653999995566621930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1427_800 : bothSeg evalE (oGrid.idx 1427) (oGrid.dm 1427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1427) oGrid.kl oGrid.kr 400 800 ⟨false, 76971437859339866653749085394816598346361573202517229403653999995566621930⟩ ⟨false, 0⟩ ⟨false, 138211651957617224217620290187522943637357889848873458794456274213439560968⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1427_1200 : bothSeg evalE (oGrid.idx 1427) (oGrid.dm 1427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1427) oGrid.kl oGrid.kr 400 1200 ⟨false, 138211651957617224217620290187522943637357889848873458794456274213439560968⟩ ⟨false, 0⟩ ⟨false, 224262054759543352689909244153447495369942946680189634849138232875027342246⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1427_1600 : bothSeg evalE (oGrid.idx 1427) (oGrid.dm 1427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1427) oGrid.kl oGrid.kr 400 1600 ⟨false, 224262054759543352689909244153447495369942946680189634849138232875027342246⟩ ⟨false, 0⟩ ⟨false, 364065843501500580314106870894212332236414251465571255589860605543037014080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1427_2000 : bothSeg evalE (oGrid.idx 1427) (oGrid.dm 1427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1427) oGrid.kl oGrid.kr 400 2000 ⟨false, 364065843501500580314106870894212332236414251465571255589860605543037014080⟩ ⟨false, 0⟩ ⟨false, 555258741208871636932369198656379763945889198637262285276804999529578192804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1427_2400 : bothLoop evalE (oGrid.idx 1427) (oGrid.dm 1427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1427) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 555258741208871636932369198656379763945889198637262285276804999529578192804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1427 : oGrid.row evalE 1427 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1427_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1427_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1427_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1427_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1427_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1427_2000).1 (bothLoop_sound b_1427_2400).1))))))

theorem n_row_1427 : nGrid.row evalE 1427 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1427_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1427_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1427_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1427_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1427_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1427_2000).2 (bothLoop_sound b_1427_2400).2))))))

theorem b_1428_0 : bothSeg evalE (oGrid.idx 1428) (oGrid.dm 1428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1428) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 27274670733334912914851107245446697474409396196398146822242736078812008996⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1428_400 : bothSeg evalE (oGrid.idx 1428) (oGrid.dm 1428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1428) oGrid.kl oGrid.kr 400 400 ⟨false, 27274670733334912914851107245446697474409396196398146822242736078812008996⟩ ⟨false, 0⟩ ⟨false, 77866489342358861781825754465768231268621503657683130324954093355445145110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1428_800 : bothSeg evalE (oGrid.idx 1428) (oGrid.dm 1428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1428) oGrid.kl oGrid.kr 400 800 ⟨false, 77866489342358861781825754465768231268621503657683130324954093355445145110⟩ ⟨false, 0⟩ ⟨false, 139065345399983618433529130788222146499820417226710183817789943151402431946⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1428_1200 : bothSeg evalE (oGrid.idx 1428) (oGrid.dm 1428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1428) oGrid.kl oGrid.kr 400 1200 ⟨false, 139065345399983618433529130788222146499820417226710183817789943151402431946⟩ ⟨false, 0⟩ ⟨false, 225423430927823391691224425360211717158749644766621661347653047821577483788⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1428_1600 : bothSeg evalE (oGrid.idx 1428) (oGrid.dm 1428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1428) oGrid.kl oGrid.kr 400 1600 ⟨false, 225423430927823391691224425360211717158749644766621661347653047821577483788⟩ ⟨false, 0⟩ ⟨false, 365494263195726702853059915277952721814497426755363368883751661916072049228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1428_2000 : bothSeg evalE (oGrid.idx 1428) (oGrid.dm 1428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1428) oGrid.kl oGrid.kr 400 2000 ⟨false, 365494263195726702853059915277952721814497426755363368883751661916072049228⟩ ⟨false, 0⟩ ⟨false, 556922232144216310479598624868824259224707539580131737276830020323393131546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1428_2400 : bothLoop evalE (oGrid.idx 1428) (oGrid.dm 1428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1428) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 556922232144216310479598624868824259224707539580131737276830020323393131546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1428 : oGrid.row evalE 1428 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1428_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1428_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1428_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1428_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1428_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1428_2000).1 (bothLoop_sound b_1428_2400).1))))))

theorem n_row_1428 : nGrid.row evalE 1428 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1428_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1428_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1428_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1428_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1428_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1428_2000).2 (bothLoop_sound b_1428_2400).2))))))

theorem b_1429_0 : bothSeg evalE (oGrid.idx 1429) (oGrid.dm 1429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1429) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 27698734342424401479795579461535528963361048499854286495709831491402801532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1429_400 : bothSeg evalE (oGrid.idx 1429) (oGrid.dm 1429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1429) oGrid.kl oGrid.kr 400 400 ⟨false, 27698734342424401479795579461535528963361048499854286495709831491402801532⟩ ⟨false, 0⟩ ⟨false, 78761767150774561165037660118969295808788587888123189649975309167152430256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1429_800 : bothSeg evalE (oGrid.idx 1429) (oGrid.dm 1429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1429) oGrid.kl oGrid.kr 400 800 ⟨false, 78761767150774561165037660118969295808788587888123189649975309167152430256⟩ ⟨false, 0⟩ ⟨false, 139918136130643529074671040508179113104870163283488758486818032161081226232⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1429_1200 : bothSeg evalE (oGrid.idx 1429) (oGrid.dm 1429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1429) oGrid.kl oGrid.kr 400 1200 ⟨false, 139918136130643529074671040508179113104870163283488758486818032161081226232⟩ ⟨false, 0⟩ ⟨false, 226583946286747139172718697382591100930441295409574921047508286331290255666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1429_1600 : bothSeg evalE (oGrid.idx 1429) (oGrid.dm 1429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1429) oGrid.kl oGrid.kr 400 1600 ⟨false, 226583946286747139172718697382591100930441295409574921047508286331290255666⟩ ⟨false, 0⟩ ⟨false, 366921839722050431581705246286661084126766566279077344225371431530553017142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1429_2000 : bothSeg evalE (oGrid.idx 1429) (oGrid.dm 1429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1429) oGrid.kl oGrid.kr 400 2000 ⟨false, 366921839722050431581705246286661084126766566279077344225371431530553017142⟩ ⟨false, 0⟩ ⟨false, 558584915975906000641505831444484570932039783208540695646636762971509384194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1429_2400 : bothLoop evalE (oGrid.idx 1429) (oGrid.dm 1429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1429) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 558584915975906000641505831444484570932039783208540695646636762971509384194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1429 : oGrid.row evalE 1429 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1429_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1429_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1429_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1429_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1429_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1429_2000).1 (bothLoop_sound b_1429_2400).1))))))

theorem n_row_1429 : nGrid.row evalE 1429 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1429_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1429_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1429_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1429_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1429_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1429_2000).2 (bothLoop_sound b_1429_2400).2))))))

theorem b_1430_0 : bothSeg evalE (oGrid.idx 1430) (oGrid.dm 1430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1430) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 28123364286175395290747677397377970707750995722549574649536954528866575862⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1430_400 : bothSeg evalE (oGrid.idx 1430) (oGrid.dm 1430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1430) oGrid.kl oGrid.kr 400 400 ⟨false, 28123364286175395290747677397377970707750995722549574649536954528866575862⟩ ⟨false, 0⟩ ⟨false, 79657124662798063079344485573252589391486936350826052933156325768813807530⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1430_800 : bothSeg evalE (oGrid.idx 1430) (oGrid.dm 1430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1430) oGrid.kl oGrid.kr 400 800 ⟨false, 79657124662798063079344485573252589391486936350826052933156325768813807530⟩ ⟨false, 0⟩ ⟨false, 140769975437762734031045333092677425478536034866266698338032101052688966012⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1430_1200 : bothSeg evalE (oGrid.idx 1430) (oGrid.dm 1430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1430) oGrid.kl oGrid.kr 400 1200 ⟨false, 140769975437762734031045333092677425478536034866266698338032101052688966012⟩ ⟨false, 0⟩ ⟨false, 227743547969480802253647937517052210735940858656219022119937284935754345216⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1430_1600 : bothSeg evalE (oGrid.idx 1430) (oGrid.dm 1430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1430) oGrid.kl oGrid.kr 400 1600 ⟨false, 227743547969480802253647937517052210735940858656219022119937284935754345216⟩ ⟨false, 0⟩ ⟨false, 368348520147558431176363263765926437756946927205979686015411623717506747194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1430_2000 : bothSeg evalE (oGrid.idx 1430) (oGrid.dm 1430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1430) oGrid.kl oGrid.kr 400 2000 ⟨false, 368348520147558431176363263765926437756946927205979686015411623717506747194⟩ ⟨false, 0⟩ ⟨false, 560246739704975837431514912785931496370096630210346600678121931646048451616⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1430_2400 : bothLoop evalE (oGrid.idx 1430) (oGrid.dm 1430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1430) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 560246739704975837431514912785931496370096630210346600678121931646048451616⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1430 : oGrid.row evalE 1430 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1430_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1430_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1430_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1430_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1430_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1430_2000).1 (bothLoop_sound b_1430_2400).1))))))

theorem n_row_1430 : nGrid.row evalE 1430 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1430_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1430_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1430_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1430_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1430_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1430_2000).2 (bothLoop_sound b_1430_2400).2))))))

theorem b_1431_0 : bothSeg evalE (oGrid.idx 1431) (oGrid.dm 1431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1431) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 28548578092092024679858670930885173876898370066796471603914974929859021260⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1431_400 : bothSeg evalE (oGrid.idx 1431) (oGrid.dm 1431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1431) oGrid.kl oGrid.kr 400 400 ⟨false, 28548578092092024679858670930885173876898370066796471603914974929859021260⟩ ⟨false, 0⟩ ⟨false, 80552415369007674706688200903856183463039574910158700068870682219911721072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1431_800 : bothSeg evalE (oGrid.idx 1431) (oGrid.dm 1431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1431) oGrid.kl oGrid.kr 400 800 ⟨false, 80552415369007674706688200903856183463039574910158700068870682219911721072⟩ ⟨false, 0⟩ ⟨false, 141620871743147611464078267564059595357099279302248311383571759767140888144⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1431_1200 : bothSeg evalE (oGrid.idx 1431) (oGrid.dm 1431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1431) oGrid.kl oGrid.kr 400 1200 ⟨false, 141620871743147611464078267564059595357099279302248311383571759767140888144⟩ ⟨false, 0⟩ ⟨false, 228902239718089209834397037055670516416575271978546402038066435683214395566⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1431_1600 : bothSeg evalE (oGrid.idx 1431) (oGrid.dm 1431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1431) oGrid.kl oGrid.kr 400 1600 ⟨false, 228902239718089209834397037055670516416575271978546402038066435683214395566⟩ ⟨false, 0⟩ ⟨false, 369774308148356694882658971586085555707591023717613321230685104879396883658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1431_2000 : bothSeg evalE (oGrid.idx 1431) (oGrid.dm 1431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1431) oGrid.kl oGrid.kr 400 2000 ⟨false, 369774308148356694882658971586085555707591023717613321230685104879396883658⟩ ⟨false, 0⟩ ⟨false, 561907706941565200862440871443157636344422986716708944469582794781247702742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1431_2400 : bothLoop evalE (oGrid.idx 1431) (oGrid.dm 1431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1431) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 561907706941565200862440871443157636344422986716708944469582794781247702742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1431 : oGrid.row evalE 1431 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1431_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1431_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1431_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1431_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1431_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1431_2000).1 (bothLoop_sound b_1431_2400).1))))))

theorem n_row_1431 : nGrid.row evalE 1431 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1431_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1431_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1431_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1431_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1431_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1431_2000).2 (bothLoop_sound b_1431_2400).2))))))

theorem b_1432_0 : bothSeg evalE (oGrid.idx 1432) (oGrid.dm 1432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1432) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 28974389509483843736066207891995970031116886605643875847407343466733327508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1432_400 : bothSeg evalE (oGrid.idx 1432) (oGrid.dm 1432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1432) oGrid.kl oGrid.kr 400 400 ⟨false, 28974389509483843736066207891995970031116886605643875847407343466733327508⟩ ⟨false, 0⟩ ⟨false, 81447488794463897274921237804293866695489471341370643893915349162833536564⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1432_800 : bothSeg evalE (oGrid.idx 1432) (oGrid.dm 1432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1432) oGrid.kl oGrid.kr 400 800 ⟨false, 81447488794463897274921237804293866695489471341370643893915349162833536564⟩ ⟨false, 0⟩ ⟨false, 142470800292273618045099531526172226689851198185304914054034611333006550434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1432_1200 : bothSeg evalE (oGrid.idx 1432) (oGrid.dm 1432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1432) oGrid.kl oGrid.kr 400 1200 ⟨false, 142470800292273618045099531526172226689851198185304914054034611333006550434⟩ ⟨false, 0⟩ ⟨false, 230059990496660720724190357084874206652192528250081433522157283146461229536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1432_1600 : bothSeg evalE (oGrid.idx 1432) (oGrid.dm 1432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1432) oGrid.kl oGrid.kr 400 1600 ⟨false, 230059990496660720724190357084874206652192528250081433522157283146461229536⟩ ⟨false, 0⟩ ⟨false, 371199172622695264282654453190018620899017979862526861282695020773932717278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1432_2000 : bothSeg evalE (oGrid.idx 1432) (oGrid.dm 1432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1432) oGrid.kl oGrid.kr 400 2000 ⟨false, 371199172622695264282654453190018620899017979862526861282695020773932717278⟩ ⟨false, 0⟩ ⟨false, 563567786518042360922117171788808562764853109225971514512673574549821609854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1432_2400 : bothLoop evalE (oGrid.idx 1432) (oGrid.dm 1432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1432) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 563567786518042360922117171788808562764853109225971514512673574549821609854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1432 : oGrid.row evalE 1432 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1432_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1432_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1432_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1432_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1432_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1432_2000).1 (bothLoop_sound b_1432_2400).1))))))

theorem n_row_1432 : nGrid.row evalE 1432 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1432_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1432_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1432_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1432_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1432_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1432_2000).2 (bothLoop_sound b_1432_2400).2))))))

theorem b_1433_0 : bothSeg evalE (oGrid.idx 1433) (oGrid.dm 1433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1433) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 29400813529209394406088874061381157335263739930385274045358128531847128170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1433_400 : bothSeg evalE (oGrid.idx 1433) (oGrid.dm 1433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1433) oGrid.kl oGrid.kr 400 400 ⟨false, 29400813529209394406088874061381157335263739930385274045358128531847128170⟩ ⟨false, 0⟩ ⟨false, 82342187259627951457917913015272097056165118059494106606554654675647439360⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1433_800 : bothSeg evalE (oGrid.idx 1433) (oGrid.dm 1433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1433) oGrid.kl oGrid.kr 400 800 ⟨false, 82342187259627951457917913015272097056165118059494106606554654675647439360⟩ ⟨false, 0⟩ ⟨false, 143319731492439415887736944390612121398110759803661570273383824393545513734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1433_1200 : bothSeg evalE (oGrid.idx 1433) (oGrid.dm 1433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1433) oGrid.kl oGrid.kr 400 1200 ⟨false, 143319731492439415887736944390612121398110759803661570273383824393545513734⟩ ⟨false, 0⟩ ⟨false, 231216764653413966127662411205656255541859196742155054755980779058647792116⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1433_1600 : bothSeg evalE (oGrid.idx 1433) (oGrid.dm 1433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1433) oGrid.kl oGrid.kr 400 1600 ⟨false, 231216764653413966127662411205656255541859196742155054755980779058647792116⟩ ⟨false, 0⟩ ⟨false, 372623077853074783654707604646831713700582401699720730463626176971165879314⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1433_2000 : bothSeg evalE (oGrid.idx 1433) (oGrid.dm 1433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1433) oGrid.kl oGrid.kr 400 2000 ⟨false, 372623077853074783654707604646831713700582401699720730463626176971165879314⟩ ⟨false, 0⟩ ⟨false, 565226942651110952135872678522423612008718871577901389623939442705455662104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1433_2400 : bothLoop evalE (oGrid.idx 1433) (oGrid.dm 1433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1433) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 565226942651110952135872678522423612008718871577901389623939442705455662104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1433 : oGrid.row evalE 1433 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1433_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1433_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1433_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1433_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1433_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1433_2000).1 (bothLoop_sound b_1433_2400).1))))))

theorem n_row_1433 : nGrid.row evalE 1433 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1433_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1433_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1433_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1433_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1433_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1433_2000).2 (bothLoop_sound b_1433_2400).2))))))

theorem b_1434_0 : bothSeg evalE (oGrid.idx 1434) (oGrid.dm 1434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1434) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 29827870712392991738276525306354815934392995890603207265794600274182831332⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1434_400 : bothSeg evalE (oGrid.idx 1434) (oGrid.dm 1434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1434) oGrid.kl oGrid.kr 400 400 ⟨false, 29827870712392991738276525306354815934392995890603207265794600274182831332⟩ ⟨false, 0⟩ ⟨false, 83236352077234951673463648376835912134232985576236711531512654239799426326⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1434_800 : bothSeg evalE (oGrid.idx 1434) (oGrid.dm 1434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1434) oGrid.kl oGrid.kr 400 800 ⟨false, 83236352077234951673463648376835912134232985576236711531512654239799426326⟩ ⟨false, 0⟩ ⟨false, 144167674530105788533884355681434035469187717791117935160846565504265137150⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1434_1200 : bothSeg evalE (oGrid.idx 1434) (oGrid.dm 1434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1434) oGrid.kl oGrid.kr 400 1200 ⟨false, 144167674530105788533884355681434035469187717791117935160846565504265137150⟩ ⟨false, 0⟩ ⟨false, 232372564805971656721529334915420175067589111387611964521814173392286397702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1434_1600 : bothSeg evalE (oGrid.idx 1434) (oGrid.dm 1434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1434) oGrid.kl oGrid.kr 400 1600 ⟨false, 232372564805971656721529334915420175067589111387611964521814173392286397702⟩ ⟨false, 0⟩ ⟨false, 374046026391520119157235026472517464695137435492286043028274379311680825306⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1434_2000 : bothSeg evalE (oGrid.idx 1434) (oGrid.dm 1434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1434) oGrid.kl oGrid.kr 400 2000 ⟨false, 374046026391520119157235026472517464695137435492286043028274379311680825306⟩ ⟨false, 0⟩ ⟨false, 566885177827083512947359316107689234919643571418880714641185047079534939478⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1434_2400 : bothLoop evalE (oGrid.idx 1434) (oGrid.dm 1434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1434) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 566885177827083512947359316107689234919643571418880714641185047079534939478⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1434 : oGrid.row evalE 1434 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1434_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1434_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1434_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1434_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1434_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1434_2000).1 (bothLoop_sound b_1434_2400).1))))))

theorem n_row_1434 : nGrid.row evalE 1434 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1434_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1434_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1434_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1434_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1434_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1434_2000).2 (bothLoop_sound b_1434_2400).2))))))

theorem b_1435_0 : bothSeg evalE (oGrid.idx 1435) (oGrid.dm 1435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1435) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 30255582160718495528719405377530887498673047801930020988421143210840845768⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1435_400 : bothSeg evalE (oGrid.idx 1435) (oGrid.dm 1435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1435) oGrid.kl oGrid.kr 400 400 ⟨false, 30255582160718495528719405377530887498673047801930020988421143210840845768⟩ ⟨false, 0⟩ ⟨false, 84129826557978105319805632457392801808345108835841282242721401246576475774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1435_800 : bothSeg evalE (oGrid.idx 1435) (oGrid.dm 1435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1435) oGrid.kl oGrid.kr 400 800 ⟨false, 84129826557978105319805632457392801808345108835841282242721401246576475774⟩ ⟨false, 0⟩ ⟨false, 145014585945876129070632656817637790235263577812822463837017621543361553988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1435_1200 : bothSeg evalE (oGrid.idx 1435) (oGrid.dm 1435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1435) oGrid.kl oGrid.kr 400 1200 ⟨false, 145014585945876129070632656817637790235263577812822463837017621543361553988⟩ ⟨false, 0⟩ ⟨false, 233527340776898213190074117489833561030396369897047176211865754899993769454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1435_1600 : bothSeg evalE (oGrid.idx 1435) (oGrid.dm 1435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1435) oGrid.kl oGrid.kr 400 1600 ⟨false, 233527340776898213190074117489833561030396369897047176211865754899993769454⟩ ⟨false, 0⟩ ⟨false, 375467967995117801705028303531360965909564716828543189887184072797586682488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1435_2000 : bothSeg evalE (oGrid.idx 1435) (oGrid.dm 1435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1435) oGrid.kl oGrid.kr 400 2000 ⟨false, 375467967995117801705028303531360965909564716828543189887184072797586682488⟩ ⟨false, 0⟩ ⟨false, 568542441737418848786701923156072803908557732165396408717299487731775031086⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1435_2400 : bothLoop evalE (oGrid.idx 1435) (oGrid.dm 1435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1435) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 568542441737418848786701923156072803908557732165396408717299487731775031086⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1435 : oGrid.row evalE 1435 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1435_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1435_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1435_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1435_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1435_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1435_2000).1 (bothLoop_sound b_1435_2400).1))))))

theorem n_row_1435 : nGrid.row evalE 1435 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1435_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1435_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1435_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1435_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1435_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1435_2000).2 (bothLoop_sound b_1435_2400).2))))))

theorem b_1436_0 : bothSeg evalE (oGrid.idx 1436) (oGrid.dm 1436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1436) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 30683967637046032409336396495176577487084351006188617288717257207713001070⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1436_400 : bothSeg evalE (oGrid.idx 1436) (oGrid.dm 1436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1436) oGrid.kl oGrid.kr 400 400 ⟨false, 30683967637046032409336396495176577487084351006188617288717257207713001070⟩ ⟨false, 0⟩ ⟨false, 85022439542570143813406703532792312129705666283750735368799842365570706180⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1436_800 : bothSeg evalE (oGrid.idx 1436) (oGrid.dm 1436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1436) oGrid.kl oGrid.kr 400 800 ⟨false, 85022439542570143813406703532792312129705666283750735368799842365570706180⟩ ⟨false, 0⟩ ⟨false, 145860463970507699165582793898290352964894705569374280724129342991981561484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1436_1200 : bothSeg evalE (oGrid.idx 1436) (oGrid.dm 1436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1436) oGrid.kl oGrid.kr 400 1200 ⟨false, 145860463970507699165582793898290352964894705569374280724129342991981561484⟩ ⟨false, 0⟩ ⟨false, 234681083697957026137370778536279897907506759858725455577567606894220416678⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1436_1600 : bothSeg evalE (oGrid.idx 1436) (oGrid.dm 1436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1436) oGrid.kl oGrid.kr 400 1600 ⟨false, 234681083697957026137370778536279897907506759858725455577567606894220416678⟩ ⟨false, 0⟩ ⟨false, 376888893730273099455984026381238933359743697063809226260821171650099270488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1436_2000 : bothSeg evalE (oGrid.idx 1436) (oGrid.dm 1436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1436) oGrid.kl oGrid.kr 400 2000 ⟨false, 376888893730273099455984026381238933359743697063809226260821171650099270488⟩ ⟨false, 0⟩ ⟨false, 570198725382979024744151712620372184948874695185787464814931745229993438664⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1436_2400 : bothLoop evalE (oGrid.idx 1436) (oGrid.dm 1436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1436) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 570198725382979024744151712620372184948874695185787464814931745229993438664⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1436 : oGrid.row evalE 1436 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1436_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1436_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1436_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1436_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1436_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1436_2000).1 (bothLoop_sound b_1436_2400).1))))))

theorem n_row_1436 : nGrid.row evalE 1436 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1436_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1436_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1436_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1436_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1436_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1436_2000).2 (bothLoop_sound b_1436_2400).2))))))

theorem b_1437_0 : bothSeg evalE (oGrid.idx 1437) (oGrid.dm 1437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1437) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 31113055142460968915648425606303018188403544551134511669017726574449747766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1437_400 : bothSeg evalE (oGrid.idx 1437) (oGrid.dm 1437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1437) oGrid.kl oGrid.kr 400 400 ⟨false, 31113055142460968915648425606303018188403544551134511669017726574449747766⟩ ⟨false, 0⟩ ⟨false, 85914033428038571685310655076858009407659592171504300293583700567284243058⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1437_800 : bothSeg evalE (oGrid.idx 1437) (oGrid.dm 1437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1437) oGrid.kl oGrid.kr 400 800 ⟨false, 85914033428038571685310655076858009407659592171504300293583700567284243058⟩ ⟨false, 0⟩ ⟨false, 146705288311783047343191535254694778053343296284185931227170702509194919854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1437_1200 : bothSeg evalE (oGrid.idx 1437) (oGrid.dm 1437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1437) oGrid.kl oGrid.kr 400 1200 ⟨false, 146705288311783047343191535254694778053343296284185931227170702509194919854⟩ ⟨false, 0⟩ ⟨false, 235833767428799675066174956060492654397061229194472114564744459462329737932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1437_1600 : bothSeg evalE (oGrid.idx 1437) (oGrid.dm 1437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1437) oGrid.kl oGrid.kr 400 1600 ⟨false, 235833767428799675066174956060492654397061229194472114564744459462329737932⟩ ⟨false, 0⟩ ⟨false, 378308777391399049598109115552791904745043360230612408801159152179117408778⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1437_2000 : bothSeg evalE (oGrid.idx 1437) (oGrid.dm 1437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1437) oGrid.kl oGrid.kr 400 2000 ⟨false, 378308777391399049598109115552791904745043360230612408801159152179117408778⟩ ⟨false, 0⟩ ⟨false, 571854002492718317539424772529227515318544990208883447173551419172538668134⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1437_2400 : bothLoop evalE (oGrid.idx 1437) (oGrid.dm 1437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1437) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 571854002492718317539424772529227515318544990208883447173551419172538668134⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1437 : oGrid.row evalE 1437 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1437_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1437_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1437_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1437_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1437_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1437_2000).1 (bothLoop_sound b_1437_2400).1))))))

theorem n_row_1437 : nGrid.row evalE 1437 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1437_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1437_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1437_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1437_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1437_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1437_2000).2 (bothLoop_sound b_1437_2400).2))))))

theorem b_1438_0 : bothSeg evalE (oGrid.idx 1438) (oGrid.dm 1438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1438) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 31542873498862219647877298900394263063974103960728826453304646091553801440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1438_400 : bothSeg evalE (oGrid.idx 1438) (oGrid.dm 1438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1438) oGrid.kl oGrid.kr 400 400 ⟨false, 31542873498862219647877298900394263063974103960728826453304646091553801440⟩ ⟨false, 0⟩ ⟨false, 86804442022623215360569952985164713440058751813808999192950026375306589424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1438_800 : bothSeg evalE (oGrid.idx 1438) (oGrid.dm 1438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1438) oGrid.kl oGrid.kr 400 800 ⟨false, 86804442022623215360569952985164713440058751813808999192950026375306589424⟩ ⟨false, 0⟩ ⟨false, 147549045737563873032581725891871631471026126919807214495680569857431851794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1438_1200 : bothSeg evalE (oGrid.idx 1438) (oGrid.dm 1438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1438) oGrid.kl oGrid.kr 400 1200 ⟨false, 147549045737563873032581725891871631471026126919807214495680569857431851794⟩ ⟨false, 0⟩ ⟨false, 236985373074200374570733689153145760070595984045558710811494857833633597150⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1438_1600 : bothSeg evalE (oGrid.idx 1438) (oGrid.dm 1438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1438) oGrid.kl oGrid.kr 400 1600 ⟨false, 236985373074200374570733689153145760070595984045558710811494857833633597150⟩ ⟨false, 0⟩ ⟨false, 379727600018150717583987255694187053097137567359833316394044852547452407680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1438_2000 : bothSeg evalE (oGrid.idx 1438) (oGrid.dm 1438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1438) oGrid.kl oGrid.kr 400 2000 ⟨false, 379727600018150717583987255694187053097137567359833316394044852547452407680⟩ ⟨false, 0⟩ ⟨false, 573508254040917394934230106111739712197676716165413110536499967479000467360⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1438_2400 : bothLoop evalE (oGrid.idx 1438) (oGrid.dm 1438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1438) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 573508254040917394934230106111739712197676716165413110536499967479000467360⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1438 : oGrid.row evalE 1438 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1438_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1438_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1438_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1438_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1438_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1438_2000).1 (bothLoop_sound b_1438_2400).1))))))

theorem n_row_1438 : nGrid.row evalE 1438 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1438_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1438_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1438_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1438_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1438_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1438_2000).2 (bothLoop_sound b_1438_2400).2))))))

theorem b_1439_0 : bothSeg evalE (oGrid.idx 1439) (oGrid.dm 1439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1439) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 31973452265738210183016916808668312910953531542188044877990777829316577856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1439_400 : bothSeg evalE (oGrid.idx 1439) (oGrid.dm 1439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1439) oGrid.kl oGrid.kr 400 400 ⟨false, 31973452265738210183016916808668312910953531542188044877990777829316577856⟩ ⟨false, 0⟩ ⟨false, 87693501302986403189140943340462223415666437052465255001687215002865295442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1439_800 : bothSeg evalE (oGrid.idx 1439) (oGrid.dm 1439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1439) oGrid.kl oGrid.kr 400 800 ⟨false, 87693501302986403189140943340462223415666437052465255001687215002865295442⟩ ⟨false, 0⟩ ⟨false, 148391728058475591791620395956903431258507667316237702921942613732790211334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1439_1200 : bothSeg evalE (oGrid.idx 1439) (oGrid.dm 1439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1439) oGrid.kl oGrid.kr 400 1200 ⟨false, 148391728058475591791620395956903431258507667316237702921942613732790211334⟩ ⟨false, 0⟩ ⟨false, 238135888395063889647585768376341677355839936437132798244960045547326339240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1439_1600 : bothSeg evalE (oGrid.idx 1439) (oGrid.dm 1439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1439) oGrid.kl oGrid.kr 400 1600 ⟨false, 238135888395063889647585768376341677355839936437132798244960045547326339240⟩ ⟨false, 0⟩ ⟨false, 381145349306432925716709771361708881133440878791619770475083459569522653908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1439_2000 : bothSeg evalE (oGrid.idx 1439) (oGrid.dm 1439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1439) oGrid.kl oGrid.kr 400 2000 ⟨false, 381145349306432925716709771361708881133440878791619770475083459569522653908⟩ ⟨false, 0⟩ ⟨false, 575161467658190964492308056617681905155252786827983767339091734133846981338⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1439_2400 : bothLoop evalE (oGrid.idx 1439) (oGrid.dm 1439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1439) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 575161467658190964492308056617681905155252786827983767339091734133846981338⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1439 : oGrid.row evalE 1439 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1439_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1439_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1439_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1439_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1439_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1439_2000).1 (bothLoop_sound b_1439_2400).1))))))

theorem n_row_1439 : nGrid.row evalE 1439 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1439_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1439_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1439_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1439_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1439_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1439_2000).2 (bothLoop_sound b_1439_2400).2))))))

theorem o_blk_1416 : allFrom (fun j => oGrid.row evalE j) 1416 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1416) o_row_1416 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1417) o_row_1417 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1418) o_row_1418 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1419) o_row_1419 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1420) o_row_1420 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1421) o_row_1421 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1422) o_row_1422 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1423) o_row_1423 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1424) o_row_1424 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1425) o_row_1425 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1426) o_row_1426 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1427) o_row_1427 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1428) o_row_1428 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1429) o_row_1429 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1430) o_row_1430 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1431) o_row_1431 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1432) o_row_1432 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1433) o_row_1433 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1434) o_row_1434 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1435) o_row_1435 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1436) o_row_1436 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1437) o_row_1437 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1438) o_row_1438 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1439) o_row_1439 (allFrom_zero (fun j => oGrid.row evalE j) 1440)))))))))))))))))))))))))

theorem n_blk_1416 : allFrom (fun j => nGrid.row evalE j) 1416 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1416) n_row_1416 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1417) n_row_1417 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1418) n_row_1418 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1419) n_row_1419 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1420) n_row_1420 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1421) n_row_1421 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1422) n_row_1422 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1423) n_row_1423 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1424) n_row_1424 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1425) n_row_1425 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1426) n_row_1426 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1427) n_row_1427 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1428) n_row_1428 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1429) n_row_1429 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1430) n_row_1430 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1431) n_row_1431 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1432) n_row_1432 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1433) n_row_1433 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1434) n_row_1434 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1435) n_row_1435 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1436) n_row_1436 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1437) n_row_1437 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1438) n_row_1438 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1439) n_row_1439 (allFrom_zero (fun j => nGrid.row evalE j) 1440)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
