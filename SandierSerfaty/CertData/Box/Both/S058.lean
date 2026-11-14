/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 58 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1392`–`1415`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1392_0 : bothSeg evalE (oGrid.idx 1392) (oGrid.dm 1392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1392) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 12366156049527780672243581530906898715918334868270127742704306551578427398⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1392_400 : bothSeg evalE (oGrid.idx 1392) (oGrid.dm 1392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1392) oGrid.kl oGrid.kr 400 400 ⟨false, 12366156049527780672243581530906898715918334868270127742704306551578427398⟩ ⟨false, 0⟩ ⟨false, 46598047309647158357686483123428505970531930340857682391093508183671322172⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1392_800 : bothSeg evalE (oGrid.idx 1392) (oGrid.dm 1392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1392) oGrid.kl oGrid.kr 400 800 ⟨false, 46598047309647158357686483123428505970531930340857682391093508183671322172⟩ ⟨false, 0⟩ ⟨false, 107918875247579851835189773964059810104568504673401999700341279816435524022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1392_1200 : bothSeg evalE (oGrid.idx 1392) (oGrid.dm 1392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1392) oGrid.kl oGrid.kr 400 1200 ⟨false, 107918875247579851835189773964059810104568504673401999700341279816435524022⟩ ⟨false, 0⟩ ⟨false, 183231474448400289211734689258287082975465436416648737570019863991280754936⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1392_1600 : bothSeg evalE (oGrid.idx 1392) (oGrid.dm 1392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1392) oGrid.kl oGrid.kr 400 1600 ⟨false, 183231474448400289211734689258287082975465436416648737570019863991280754936⟩ ⟨false, 0⟩ ⟨false, 313700376355565365752437655897064580617901461485211627527104100469074216876⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1392_2000 : bothSeg evalE (oGrid.idx 1392) (oGrid.dm 1392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1392) oGrid.kl oGrid.kr 400 2000 ⟨false, 313700376355565365752437655897064580617901461485211627527104100469074216876⟩ ⟨false, 0⟩ ⟨false, 496689020634465943589315081400662064159839206503107418037439877260617624816⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1392_2400 : bothLoop evalE (oGrid.idx 1392) (oGrid.dm 1392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1392) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 496689020634465943589315081400662064159839206503107418037439877260617624816⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1392 : oGrid.row evalE 1392 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1392_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1392_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1392_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1392_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1392_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1392_2000).1 (bothLoop_sound b_1392_2400).1))))))

theorem n_row_1392 : nGrid.row evalE 1392 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1392_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1392_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1392_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1392_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1392_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1392_2000).2 (bothLoop_sound b_1392_2400).2))))))

theorem b_1393_0 : bothSeg evalE (oGrid.idx 1393) (oGrid.dm 1393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1393) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 12771254826517162338646793380999258864527894995035106762347924983309750368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1393_400 : bothSeg evalE (oGrid.idx 1393) (oGrid.dm 1393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1393) oGrid.kl oGrid.kr 400 400 ⟨false, 12771254826517162338646793380999258864527894995035106762347924983309750368⟩ ⟨false, 0⟩ ⟨false, 47428642852991560947531514329024499748434980299101085427032420829805933982⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1393_800 : bothSeg evalE (oGrid.idx 1393) (oGrid.dm 1393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1393) oGrid.kl oGrid.kr 400 800 ⟨false, 47428642852991560947531514329024499748434980299101085427032420829805933982⟩ ⟨false, 0⟩ ⟨false, 108793942529002041071035457440685106853522776721897437238868801773160867032⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1393_1200 : bothSeg evalE (oGrid.idx 1393) (oGrid.dm 1393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1393) oGrid.kl oGrid.kr 400 1200 ⟨false, 108793942529002041071035457440685106853522776721897437238868801773160867032⟩ ⟨false, 0⟩ ⟨false, 184411315791684829924924124945932632810081090050629865008871808826737319518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1393_1600 : bothSeg evalE (oGrid.idx 1393) (oGrid.dm 1393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1393) oGrid.kl oGrid.kr 400 1600 ⟨false, 184411315791684829924924124945932632810081090050629865008871808826737319518⟩ ⟨false, 0⟩ ⟨false, 315146601191867385575214700322600290652820842360777649285536458243607966866⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1393_2000 : bothSeg evalE (oGrid.idx 1393) (oGrid.dm 1393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1393) oGrid.kl oGrid.kr 400 2000 ⟨false, 315146601191867385575214700322600290652820842360777649285536458243607966866⟩ ⟨false, 0⟩ ⟨false, 498369012185035642437801328231045555339767924763564913478755514403914747864⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1393_2400 : bothLoop evalE (oGrid.idx 1393) (oGrid.dm 1393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1393) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 498369012185035642437801328231045555339767924763564913478755514403914747864⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1393 : oGrid.row evalE 1393 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1393_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1393_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1393_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1393_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1393_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1393_2000).1 (bothLoop_sound b_1393_2400).1))))))

theorem n_row_1393 : nGrid.row evalE 1393 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1393_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1393_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1393_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1393_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1393_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1393_2000).2 (bothLoop_sound b_1393_2400).2))))))

theorem b_1394_0 : bothSeg evalE (oGrid.idx 1394) (oGrid.dm 1394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1394) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 13176768129296916535914198344189425593507975826402696081094340999006442164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1394_400 : bothSeg evalE (oGrid.idx 1394) (oGrid.dm 1394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1394) oGrid.kl oGrid.kr 400 400 ⟨false, 13176768129296916535914198344189425593507975826402696081094340999006442164⟩ ⟨false, 0⟩ ⟨false, 48261552172422700815830863197894521865919174459277665808161220489263374938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1394_800 : bothSeg evalE (oGrid.idx 1394) (oGrid.dm 1394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1394) oGrid.kl oGrid.kr 400 800 ⟨false, 48261552172422700815830863197894521865919174459277665808161220489263374938⟩ ⟨false, 0⟩ ⟨false, 109668257481750934970364924250929839036624456895064944400523386212248101012⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1394_1200 : bothSeg evalE (oGrid.idx 1394) (oGrid.dm 1394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1394) oGrid.kl oGrid.kr 400 1200 ⟨false, 109668257481750934970364924250929839036624456895064944400523386212248101012⟩ ⟨false, 0⟩ ⟨false, 185590742182631213056403732905863563495885427571150216293553128107051322546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1394_1600 : bothSeg evalE (oGrid.idx 1394) (oGrid.dm 1394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1394) oGrid.kl oGrid.kr 400 1600 ⟨false, 185590742182631213056403732905863563495885427571150216293553128107051322546⟩ ⟨false, 0⟩ ⟨false, 316592431107595263858788976337729485731753733597419005307852978775798489454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1394_2000 : bothSeg evalE (oGrid.idx 1394) (oGrid.dm 1394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1394) oGrid.kl oGrid.kr 400 2000 ⟨false, 316592431107595263858788976337729485731753733597419005307852978775798489454⟩ ⟨false, 0⟩ ⟨false, 500048647245202179664920918761943764815828011475771034287861243646285489434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1394_2400 : bothLoop evalE (oGrid.idx 1394) (oGrid.dm 1394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1394) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 500048647245202179664920918761943764815828011475771034287861243646285489434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1394 : oGrid.row evalE 1394 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1394_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1394_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1394_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1394_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1394_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1394_2000).1 (bothLoop_sound b_1394_2400).1))))))

theorem n_row_1394 : nGrid.row evalE 1394 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1394_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1394_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1394_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1394_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1394_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1394_2000).2 (bothLoop_sound b_1394_2400).2))))))

theorem b_1395_0 : bothSeg evalE (oGrid.idx 1395) (oGrid.dm 1395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1395) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 13582714635660365475489802975771307527900200186139486454785884602669145022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1395_400 : bothSeg evalE (oGrid.idx 1395) (oGrid.dm 1395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1395) oGrid.kl oGrid.kr 400 400 ⟨false, 13582714635660365475489802975771307527900200186139486454785884602669145022⟩ ⟨false, 0⟩ ⟨false, 49096802471929741442780836595132673032730478243316444565278648339100077554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1395_800 : bothSeg evalE (oGrid.idx 1395) (oGrid.dm 1395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1395) oGrid.kl oGrid.kr 400 800 ⟨false, 49096802471929741442780836595132673032730478243316444565278648339100077554⟩ ⟨false, 0⟩ ⟨false, 110541863003919097188189797909801292059027190479027007365886149525585842228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1395_1200 : bothSeg evalE (oGrid.idx 1395) (oGrid.dm 1395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1395) oGrid.kl oGrid.kr 400 1200 ⟨false, 110541863003919097188189797909801292059027190479027007365886149525585842228⟩ ⟨false, 0⟩ ⟨false, 186769755950373222371284211528592429594624458618330901916262015580800832020⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1395_1600 : bothSeg evalE (oGrid.idx 1395) (oGrid.dm 1395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1395) oGrid.kl oGrid.kr 400 1600 ⟨false, 186769755950373222371284211528592429594624458618330901916262015580800832020⟩ ⟨false, 0⟩ ⟨false, 318037868361458016059914382981023526994620774048537771553206911950348610184⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1395_2000 : bothSeg evalE (oGrid.idx 1395) (oGrid.dm 1395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1395) oGrid.kl oGrid.kr 400 2000 ⟨false, 318037868361458016059914382981023526994620774048537771553206911950348610184⟩ ⟨false, 0⟩ ⟨false, 501727928004600587597681151161264346644965637576094220214162750519312917084⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1395_2400 : bothLoop evalE (oGrid.idx 1395) (oGrid.dm 1395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1395) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 501727928004600587597681151161264346644965637576094220214162750519312917084⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1395 : oGrid.row evalE 1395 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1395_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1395_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1395_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1395_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1395_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1395_2000).1 (bothLoop_sound b_1395_2400).1))))))

theorem n_row_1395 : nGrid.row evalE 1395 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1395_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1395_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1395_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1395_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1395_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1395_2000).2 (bothLoop_sound b_1395_2400).2))))))

theorem b_1396_0 : bothSeg evalE (oGrid.idx 1396) (oGrid.dm 1396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1396) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 13989117305688633789828531669135441971421281223070290360983469039921324462⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1396_400 : bothSeg evalE (oGrid.idx 1396) (oGrid.dm 1396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1396) oGrid.kl oGrid.kr 400 400 ⟨false, 13989117305688633789828531669135441971421281223070290360983469039921324462⟩ ⟨false, 0⟩ ⟨false, 49934425989418513434104446058264758918339980576597881578332244469319047880⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1396_800 : bothSeg evalE (oGrid.idx 1396) (oGrid.dm 1396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1396) oGrid.kl oGrid.kr 400 800 ⟨false, 49934425989418513434104446058264758918339980576597881578332244469319047880⟩ ⟨false, 0⟩ ⟨false, 111414831204800546757588019003133531922957516721810497545308780369246562562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1396_1200 : bothSeg evalE (oGrid.idx 1396) (oGrid.dm 1396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1396) oGrid.kl oGrid.kr 400 1200 ⟨false, 111414831204800546757588019003133531922957516721810497545308780369246562562⟩ ⟨false, 0⟩ ⟨false, 187948393567191613443673637078041378691134958945154975168861911931217953594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1396_1600 : bothSeg evalE (oGrid.idx 1396) (oGrid.dm 1396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1396) oGrid.kl oGrid.kr 400 1600 ⟨false, 187948393567191613443673637078041378691134958945154975168861911931217953594⟩ ⟨false, 0⟩ ⟨false, 319482949355439076591489279234154011433085749898150645556816613453550273036⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1396_2000 : bothSeg evalE (oGrid.idx 1396) (oGrid.dm 1396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1396) oGrid.kl oGrid.kr 400 2000 ⟨false, 319482949355439076591489279234154011433085749898150645556816613453550273036⟩ ⟨false, 0⟩ ⟨false, 503406890796228025346912364287063276544428510002583108442132673857032554586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1396_2400 : bothLoop evalE (oGrid.idx 1396) (oGrid.dm 1396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1396) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 503406890796228025346912364287063276544428510002583108442132673857032554586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1396 : oGrid.row evalE 1396 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1396_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1396_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1396_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1396_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1396_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1396_2000).1 (bothLoop_sound b_1396_2400).1))))))

theorem n_row_1396 : nGrid.row evalE 1396 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1396_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1396_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1396_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1396_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1396_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1396_2000).2 (bothLoop_sound b_1396_2400).2))))))

theorem b_1397_0 : bothSeg evalE (oGrid.idx 1397) (oGrid.dm 1397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1397) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 14395992946211574951213656626059735793084684823041001220237053016976366638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1397_400 : bothSeg evalE (oGrid.idx 1397) (oGrid.dm 1397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1397) oGrid.kl oGrid.kr 400 400 ⟨false, 14395992946211574951213656626059735793084684823041001220237053016976366638⟩ ⟨false, 0⟩ ⟨false, 50774442280280629995230859841796082339872472978788292773042196720834664640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1397_800 : bothSeg evalE (oGrid.idx 1397) (oGrid.dm 1397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1397) oGrid.kl oGrid.kr 400 800 ⟨false, 50774442280280629995230859841796082339872472978788292773042196720834664640⟩ ⟨false, 0⟩ ⟨false, 112287160050363563127635276010304210863325647181910004877210533956959242512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1397_1200 : bothSeg evalE (oGrid.idx 1397) (oGrid.dm 1397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1397) oGrid.kl oGrid.kr 400 1200 ⟨false, 112287160050363563127635276010304210863325647181910004877210533956959242512⟩ ⟨false, 0⟩ ⟨false, 189126619425775884189418581022842519995938307779312126317677432540406624978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1397_1600 : bothSeg evalE (oGrid.idx 1397) (oGrid.dm 1397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1397) oGrid.kl oGrid.kr 400 1600 ⟨false, 189126619425775884189418581022842519995938307779312126317677432540406624978⟩ ⟨false, 0⟩ ⟨false, 320927638412057872778825457867342151965203444701717072677868894862936780944⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1397_2000 : bothSeg evalE (oGrid.idx 1397) (oGrid.dm 1397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1397) oGrid.kl oGrid.kr 400 2000 ⟨false, 320927638412057872778825457867342151965203444701717072677868894862936780944⟩ ⟨false, 0⟩ ⟨false, 505085499873705273390953606520860958912731842307347178549670177671120190694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1397_2400 : bothLoop evalE (oGrid.idx 1397) (oGrid.dm 1397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1397) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 505085499873705273390953606520860958912731842307347178549670177671120190694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1397 : oGrid.row evalE 1397 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1397_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1397_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1397_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1397_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1397_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1397_2000).1 (bothLoop_sound b_1397_2400).1))))))

theorem n_row_1397 : nGrid.row evalE 1397 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1397_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1397_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1397_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1397_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1397_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1397_2000).2 (bothLoop_sound b_1397_2400).2))))))

theorem b_1398_0 : bothSeg evalE (oGrid.idx 1398) (oGrid.dm 1398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1398) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 14803357473236073441613555398578188065347583666470775220080753641125644072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1398_400 : bothSeg evalE (oGrid.idx 1398) (oGrid.dm 1398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1398) oGrid.kl oGrid.kr 400 400 ⟨false, 14803357473236073441613555398578188065347583666470775220080753641125644072⟩ ⟨false, 0⟩ ⟨false, 51616870849675976096261432948017510285922284105564093716942621964204643146⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1398_800 : bothSeg evalE (oGrid.idx 1398) (oGrid.dm 1398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1398) oGrid.kl oGrid.kr 400 800 ⟨false, 51616870849675976096261432948017510285922284105564093716942621964204643146⟩ ⟨false, 0⟩ ⟨false, 113158931948621344750058730652153341957245171451708267247031931639059119050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1398_1200 : bothSeg evalE (oGrid.idx 1398) (oGrid.dm 1398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1398) oGrid.kl oGrid.kr 400 1200 ⟨false, 113158931948621344750058730652153341957245171451708267247031931639059119050⟩ ⟨false, 0⟩ ⟨false, 190304484274561555743587484365130486189948520639547657842204709182872227340⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1398_1600 : bothSeg evalE (oGrid.idx 1398) (oGrid.dm 1398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1398) oGrid.kl oGrid.kr 400 1600 ⟨false, 190304484274561555743587484365130486189948520639547657842204709182872227340⟩ ⟨false, 0⟩ ⟨false, 322371986209706909395986629999458692675889716667556932621656213569575491390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1398_2000 : bothSeg evalE (oGrid.idx 1398) (oGrid.dm 1398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1398) oGrid.kl oGrid.kr 400 2000 ⟨false, 322371986209706909395986629999458692675889716667556932621656213569575491390⟩ ⟨false, 0⟩ ⟨false, 506763805846613738721437751509908629656544962063609681933624098448925337680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1398_2400 : bothLoop evalE (oGrid.idx 1398) (oGrid.dm 1398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1398) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 506763805846613738721437751509908629656544962063609681933624098448925337680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1398 : oGrid.row evalE 1398 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1398_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1398_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1398_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1398_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1398_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1398_2000).1 (bothLoop_sound b_1398_2400).1))))))

theorem n_row_1398 : nGrid.row evalE 1398 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1398_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1398_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1398_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1398_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1398_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1398_2000).2 (bothLoop_sound b_1398_2400).2))))))

theorem b_1399_0 : bothSeg evalE (oGrid.idx 1399) (oGrid.dm 1399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1399) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 15211223899484283006085209462948628630684707156200220452764121930548598842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1399_400 : bothSeg evalE (oGrid.idx 1399) (oGrid.dm 1399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1399) oGrid.kl oGrid.kr 400 400 ⟨false, 15211223899484283006085209462948628630684707156200220452764121930548598842⟩ ⟨false, 0⟩ ⟨false, 52461721073856761124437149772407105959739819247119680491236148431737952644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1399_800 : bothSeg evalE (oGrid.idx 1399) (oGrid.dm 1399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1399) oGrid.kl oGrid.kr 400 800 ⟨false, 52461721073856761124437149772407105959739819247119680491236148431737952644⟩ ⟨false, 0⟩ ⟨false, 114030139781175920851902476837665586790521191305054187267051300872008272342⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1399_1200 : bothSeg evalE (oGrid.idx 1399) (oGrid.dm 1399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1399) oGrid.kl oGrid.kr 400 1200 ⟨false, 114030139781175920851902476837665586790521191305054187267051300872008272342⟩ ⟨false, 0⟩ ⟨false, 191481953606029193793735163631545523776652896052175487622362805965868937384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1399_1600 : bothSeg evalE (oGrid.idx 1399) (oGrid.dm 1399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1399) oGrid.kl oGrid.kr 400 1600 ⟨false, 191481953606029193793735163631545523776652896052175487622362805965868937384⟩ ⟨false, 0⟩ ⟨false, 323815958170950593893214515831775163610637339500837492149293011346627070266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1399_2000 : bothSeg evalE (oGrid.idx 1399) (oGrid.dm 1399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1399) oGrid.kl oGrid.kr 400 2000 ⟨false, 323815958170950593893214515831775163610637339500837492149293011346627070266⟩ ⟨false, 0⟩ ⟨false, 508441774068794200662561132982188114694495636290167342554406140231846236574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1399_2400 : bothLoop evalE (oGrid.idx 1399) (oGrid.dm 1399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1399) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 508441774068794200662561132982188114694495636290167342554406140231846236574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1399 : oGrid.row evalE 1399 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1399_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1399_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1399_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1399_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1399_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1399_2000).1 (bothLoop_sound b_1399_2400).1))))))

theorem n_row_1399 : nGrid.row evalE 1399 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1399_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1399_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1399_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1399_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1399_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1399_2000).2 (bothLoop_sound b_1399_2400).2))))))

theorem b_1400_0 : bothSeg evalE (oGrid.idx 1400) (oGrid.dm 1400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1400) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 15619603954957616947820900489155320622354493766082157502666676307489296740⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1400_400 : bothSeg evalE (oGrid.idx 1400) (oGrid.dm 1400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1400) oGrid.kl oGrid.kr 400 400 ⟨false, 15619603954957616947820900489155320622354493766082157502666676307489296740⟩ ⟨false, 0⟩ ⟨false, 53308995475220990878579401858675222800986622444295441739067873304734778384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1400_800 : bothSeg evalE (oGrid.idx 1400) (oGrid.dm 1400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1400) oGrid.kl oGrid.kr 400 800 ⟨false, 53308995475220990878579401858675222800986622444295441739067873304734778384⟩ ⟨false, 0⟩ ⟨false, 114900832571651263307712816878265726238506478356574199057334163163532785826⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1400_1200 : bothSeg evalE (oGrid.idx 1400) (oGrid.dm 1400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1400) oGrid.kl oGrid.kr 400 1200 ⟨false, 114900832571651263307712816878265726238506478356574199057334163163532785826⟩ ⟨false, 0⟩ ⟨false, 192659050820064303186489726012833013180088084927338782156205806468904953260⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1400_1600 : bothSeg evalE (oGrid.idx 1400) (oGrid.dm 1400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1400) oGrid.kl oGrid.kr 400 1600 ⟨false, 192659050820064303186489726012833013180088084927338782156205806468904953260⟩ ⟨false, 0⟩ ⟨false, 325259577625884935132961736415825075270735510327891645845890047276980615252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1400_2000 : bothSeg evalE (oGrid.idx 1400) (oGrid.dm 1400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1400) oGrid.kl oGrid.kr 400 2000 ⟨false, 325259577625884935132961736415825075270735510327891645845890047276980615252⟩ ⟨false, 0⟩ ⟨false, 510119427801706430181722574428735596772675463526448128084539834278948925170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1400_2400 : bothLoop evalE (oGrid.idx 1400) (oGrid.dm 1400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1400) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 510119427801706430181722574428735596772675463526448128084539834278948925170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1400 : oGrid.row evalE 1400 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1400_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1400_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1400_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1400_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1400_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1400_2000).1 (bothLoop_sound b_1400_2400).1))))))

theorem n_row_1400 : nGrid.row evalE 1400 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1400_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1400_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1400_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1400_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1400_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1400_2000).2 (bothLoop_sound b_1400_2400).2))))))

theorem b_1401_0 : bothSeg evalE (oGrid.idx 1401) (oGrid.dm 1401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1401) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 16028509360186439557791812435307558562942037762028188393447875873189129666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1401_400 : bothSeg evalE (oGrid.idx 1401) (oGrid.dm 1401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1401) oGrid.kl oGrid.kr 400 400 ⟨false, 16028509360186439557791812435307558562942037762028188393447875873189129666⟩ ⟨false, 0⟩ ⟨false, 54158700928769232207001362420118778733980479513159620657856741442092279346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1401_800 : bothSeg evalE (oGrid.idx 1401) (oGrid.dm 1401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1401) oGrid.kl oGrid.kr 400 800 ⟨false, 54158700928769232207001362420118778733980479513159620657856741442092279346⟩ ⟨false, 0⟩ ⟨false, 115771032845738302016586089917970696860424499885149276009650679799314361768⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1401_1200 : bothSeg evalE (oGrid.idx 1401) (oGrid.dm 1401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1401) oGrid.kl oGrid.kr 400 1200 ⟨false, 115771032845738302016586089917970696860424499885149276009650679799314361768⟩ ⟨false, 0⟩ ⟨false, 193835777784625732014121123642541828290396810839881217672557220880839465250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1401_1600 : bothSeg evalE (oGrid.idx 1401) (oGrid.dm 1401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1401) oGrid.kl oGrid.kr 400 1600 ⟨false, 193835777784625732014121123642541828290396810839881217672557220880839465250⟩ ⟨false, 0⟩ ⟨false, 326702846372805751841167356935573026963759494280990207357662780473153846932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1401_2000 : bothSeg evalE (oGrid.idx 1401) (oGrid.dm 1401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1401) oGrid.kl oGrid.kr 400 2000 ⟨false, 326702846372805751841167356935573026963759494280990207357662780473153846932⟩ ⟨false, 0⟩ ⟨false, 511796768775097318898532052382784642169598448407157832936024963268566305766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1401_2400 : bothLoop evalE (oGrid.idx 1401) (oGrid.dm 1401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1401) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 511796768775097318898532052382784642169598448407157832936024963268566305766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1401 : oGrid.row evalE 1401 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1401_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1401_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1401_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1401_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1401_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1401_2000).1 (bothLoop_sound b_1401_2400).1))))))

theorem n_row_1401 : nGrid.row evalE 1401 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1401_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1401_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1401_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1401_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1401_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1401_2000).2 (bothLoop_sound b_1401_2400).2))))))

theorem b_1402_0 : bothSeg evalE (oGrid.idx 1402) (oGrid.dm 1402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1402) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 16437949335732980911891666469443563550229357285054881637581283558947969752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1402_400 : bothSeg evalE (oGrid.idx 1402) (oGrid.dm 1402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1402) oGrid.kl oGrid.kr 400 400 ⟨false, 16437949335732980911891666469443563550229357285054881637581283558947969752⟩ ⟨false, 0⟩ ⟨false, 55010832498608568875534655877181069173598755307342165310450713529121316980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1402_800 : bothSeg evalE (oGrid.idx 1402) (oGrid.dm 1402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1402) oGrid.kl oGrid.kr 400 800 ⟨false, 55010832498608568875534655877181069173598755307342165310450713529121316980⟩ ⟨false, 0⟩ ⟨false, 116640746340497561445846082096525174414090467010891040162905231902312765276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1402_1200 : bothSeg evalE (oGrid.idx 1402) (oGrid.dm 1402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1402) oGrid.kl oGrid.kr 400 1200 ⟨false, 116640746340497561445846082096525174414090467010891040162905231902312765276⟩ ⟨false, 0⟩ ⟨false, 195012118351648046869190907297344901817610067091372016334938294797730373752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1402_1600 : bothSeg evalE (oGrid.idx 1402) (oGrid.dm 1402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1402) oGrid.kl oGrid.kr 400 1600 ⟨false, 195012118351648046869190907297344901817610067091372016334938294797730373752⟩ ⟨false, 0⟩ ⟨false, 328145748194110852461849971904395603474325195077159118563079708773208721402⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1402_2000 : bothSeg evalE (oGrid.idx 1402) (oGrid.dm 1402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1402) oGrid.kl oGrid.kr 400 2000 ⟨false, 328145748194110852461849971904395603474325195077159118563079708773208721402⟩ ⟨false, 0⟩ ⟨false, 513473780702902979480626982342628030169279323394386808451111252600440408054⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1402_2400 : bothLoop evalE (oGrid.idx 1402) (oGrid.dm 1402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1402) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 513473780702902979480626982342628030169279323394386808451111252600440408054⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1402 : oGrid.row evalE 1402 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1402_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1402_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1402_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1402_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1402_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1402_2000).1 (bothLoop_sound b_1402_2400).1))))))

theorem n_row_1402 : nGrid.row evalE 1402 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1402_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1402_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1402_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1402_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1402_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1402_2000).2 (bothLoop_sound b_1402_2400).2))))))

theorem b_1403_0 : bothSeg evalE (oGrid.idx 1403) (oGrid.dm 1403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1403) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 16847929808408763071337362309569387574295467951928137463627956719758033654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1403_400 : bothSeg evalE (oGrid.idx 1403) (oGrid.dm 1403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1403) oGrid.kl oGrid.kr 400 400 ⟨false, 16847929808408763071337362309569387574295467951928137463627956719758033654⟩ ⟨false, 0⟩ ⟨false, 55865377593969909137079525298325340137571708060649425229157952570614457986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1403_800 : bothSeg evalE (oGrid.idx 1403) (oGrid.dm 1403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1403) oGrid.kl oGrid.kr 400 800 ⟨false, 55865377593969909137079525298325340137571708060649425229157952570614457986⟩ ⟨false, 0⟩ ⟨false, 117510006492406327844214429598685786405245727195698711460181604175162561794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1403_1200 : bothSeg evalE (oGrid.idx 1403) (oGrid.dm 1403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1403) oGrid.kl oGrid.kr 400 1200 ⟨false, 117510006492406327844214429598685786405245727195698711460181604175162561794⟩ ⟨false, 0⟩ ⟨false, 196188089654188216933965384628376839835661086250447416596794832272465173630⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1403_1600 : bothSeg evalE (oGrid.idx 1403) (oGrid.dm 1403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1403) oGrid.kl oGrid.kr 400 1600 ⟨false, 196188089654188216933965384628376839835661086250447416596794832272465173630⟩ ⟨false, 0⟩ ⟨false, 329588300153446524081674583622088770361929871501716062799375280948560839772⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1403_2000 : bothSeg evalE (oGrid.idx 1403) (oGrid.dm 1403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1403) oGrid.kl oGrid.kr 400 2000 ⟨false, 329588300153446524081674583622088770361929871501716062799375280948560839772⟩ ⟨false, 0⟩ ⟨false, 515150480580395155093314190804947062301322973833411905872947327524567416580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1403_2400 : bothLoop evalE (oGrid.idx 1403) (oGrid.dm 1403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1403) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 515150480580395155093314190804947062301322973833411905872947327524567416580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1403 : oGrid.row evalE 1403 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1403_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1403_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1403_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1403_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1403_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1403_2000).1 (bothLoop_sound b_1403_2400).1))))))

theorem n_row_1403 : nGrid.row evalE 1403 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1403_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1403_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1403_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1403_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1403_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1403_2000).2 (bothLoop_sound b_1403_2400).2))))))

theorem b_1404_0 : bothSeg evalE (oGrid.idx 1404) (oGrid.dm 1404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1404) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 17258457980001762301363962767770789065284323570026761028607886243313252926⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1404_400 : bothSeg evalE (oGrid.idx 1404) (oGrid.dm 1404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1404) oGrid.kl oGrid.kr 400 400 ⟨false, 17258457980001762301363962767770789065284323570026761028607886243313252926⟩ ⟨false, 0⟩ ⟨false, 56722323342346712800390576349289044368089526971872515070789708449431362264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1404_800 : bothSeg evalE (oGrid.idx 1404) (oGrid.dm 1404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1404) oGrid.kl oGrid.kr 400 800 ⟨false, 56722323342346712800390576349289044368089526971872515070789708449431362264⟩ ⟨false, 0⟩ ⟨false, 118378795231383128550354135770235869905781871006392009229303886426554622468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1404_1200 : bothSeg evalE (oGrid.idx 1404) (oGrid.dm 1404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1404) oGrid.kl oGrid.kr 400 1200 ⟨false, 118378795231383128550354135770235869905781871006392009229303886426554622468⟩ ⟨false, 0⟩ ⟨false, 197363659265259478118807797386243581267728964906675749812882138365254561112⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1404_1600 : bothSeg evalE (oGrid.idx 1404) (oGrid.dm 1404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1404) oGrid.kl oGrid.kr 400 1600 ⟨false, 197363659265259478118807797386243581267728964906675749812882138365254561112⟩ ⟨false, 0⟩ ⟨false, 331030469754541201638681657174725585835837474486344738071279629853158479704⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1404_2000 : bothSeg evalE (oGrid.idx 1404) (oGrid.dm 1404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1404) oGrid.kl oGrid.kr 400 2000 ⟨false, 331030469754541201638681657174725585835837474486344738071279629853158479704⟩ ⟨false, 0⟩ ⟨false, 516826835843014809117586485362240232688456303420067491903462892709271948490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1404_2400 : bothLoop evalE (oGrid.idx 1404) (oGrid.dm 1404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1404) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 516826835843014809117586485362240232688456303420067491903462892709271948490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1404 : oGrid.row evalE 1404 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1404_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1404_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1404_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1404_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1404_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1404_2000).1 (bothLoop_sound b_1404_2400).1))))))

theorem n_row_1404 : nGrid.row evalE 1404 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1404_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1404_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1404_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1404_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1404_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1404_2000).2 (bothLoop_sound b_1404_2400).2))))))

theorem b_1405_0 : bothSeg evalE (oGrid.idx 1405) (oGrid.dm 1405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1405) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 17669537645117057315880254168335288544309148707127080410077687848949451280⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1405_400 : bothSeg evalE (oGrid.idx 1405) (oGrid.dm 1405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1405) oGrid.kl oGrid.kr 400 400 ⟨false, 17669537645117057315880254168335288544309148707127080410077687848949451280⟩ ⟨false, 0⟩ ⟨false, 57581645135591161145766543256428244317545870663620250772798667679418745974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1405_800 : bothSeg evalE (oGrid.idx 1405) (oGrid.dm 1405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1405) oGrid.kl oGrid.kr 400 800 ⟨false, 57581645135591161145766543256428244317545870663620250772798667679418745974⟩ ⟨false, 0⟩ ⟨false, 119247144565950024188952010379588982232180782155818271194051840966493674716⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1405_1200 : bothSeg evalE (oGrid.idx 1405) (oGrid.dm 1405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1405) oGrid.kl oGrid.kr 400 1200 ⟨false, 119247144565950024188952010379588982232180782155818271194051840966493674716⟩ ⟨false, 0⟩ ⟨false, 198538847278446751282805255264234427920241592572983793028815848226853732144⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1405_1600 : bothSeg evalE (oGrid.idx 1405) (oGrid.dm 1405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1405) oGrid.kl oGrid.kr 400 1600 ⟨false, 198538847278446751282805255264234427920241592572983793028815848226853732144⟩ ⟨false, 0⟩ ⟨false, 332472277021820691448405587449939848376507063914231556627162300650730799530⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1405_2000 : bothSeg evalE (oGrid.idx 1405) (oGrid.dm 1405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1405) oGrid.kl oGrid.kr 400 2000 ⟨false, 332472277021820691448405587449939848376507063914231556627162300650730799530⟩ ⟨false, 0⟩ ⟨false, 518502866446987269170100306627229970143012121427533755302591242933010241388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1405_2400 : bothLoop evalE (oGrid.idx 1405) (oGrid.dm 1405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1405) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 518502866446987269170100306627229970143012121427533755302591242933010241388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1405 : oGrid.row evalE 1405 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1405_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1405_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1405_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1405_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1405_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1405_2000).1 (bothLoop_sound b_1405_2400).1))))))

theorem n_row_1405 : nGrid.row evalE 1405 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1405_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1405_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1405_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1405_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1405_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1405_2000).2 (bothLoop_sound b_1405_2400).2))))))

theorem b_1406_0 : bothSeg evalE (oGrid.idx 1406) (oGrid.dm 1406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1406) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 18081168432148784767076463007613134901607580899269347572630041537933204252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1406_400 : bothSeg evalE (oGrid.idx 1406) (oGrid.dm 1406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1406) oGrid.kl oGrid.kr 400 400 ⟨false, 18081168432148784767076463007613134901607580899269347572630041537933204252⟩ ⟨false, 0⟩ ⟨false, 58443312831592646091231304383906116773472161698016908830374766819633640804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1406_800 : bothSeg evalE (oGrid.idx 1406) (oGrid.dm 1406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1406) oGrid.kl oGrid.kr 400 800 ⟨false, 58443312831592646091231304383906116773472161698016908830374766819633640804⟩ ⟨false, 0⟩ ⟨false, 120115036321031416916194138378517096089998643176470133332575063730435129508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1406_1200 : bothSeg evalE (oGrid.idx 1406) (oGrid.dm 1406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1406) oGrid.kl oGrid.kr 400 1200 ⟨false, 120115036321031416916194138378517096089998643176470133332575063730435129508⟩ ⟨false, 0⟩ ⟨false, 199713623340373833797228403881452467066070497996301272641611350380911054946⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1406_1600 : bothSeg evalE (oGrid.idx 1406) (oGrid.dm 1406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1406) oGrid.kl oGrid.kr 400 1600 ⟨false, 199713623340373833797228403881452467066070497996301272641611350380911054946⟩ ⟨false, 0⟩ ⟨false, 333913691532875168307950788985881555982603811871806485108767438616327969210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1406_2000 : bothSeg evalE (oGrid.idx 1406) (oGrid.dm 1406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1406) oGrid.kl oGrid.kr 400 2000 ⟨false, 333913691532875168307950788985881555982603811871806485108767438616327969210⟩ ⟨false, 0⟩ ⟨false, 520178541901789144686040643778586867519593338037240697006954596326464719656⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1406_2400 : bothLoop evalE (oGrid.idx 1406) (oGrid.dm 1406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1406) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 520178541901789144686040643778586867519593338037240697006954596326464719656⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1406 : oGrid.row evalE 1406 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1406_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1406_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1406_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1406_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1406_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1406_2000).1 (bothLoop_sound b_1406_2400).1))))))

theorem n_row_1406 : nGrid.row evalE 1406 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1406_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1406_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1406_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1406_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1406_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1406_2000).2 (bothLoop_sound b_1406_2400).2))))))

theorem b_1407_0 : bothSeg evalE (oGrid.idx 1407) (oGrid.dm 1407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1407) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 18493352517231406548333399369383020300504442363779112539216591769217305642⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1407_400 : bothSeg evalE (oGrid.idx 1407) (oGrid.dm 1407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1407) oGrid.kl oGrid.kr 400 400 ⟨false, 18493352517231406548333399369383020300504442363779112539216591769217305642⟩ ⟨false, 0⟩ ⟨false, 59307288626890194419497484381494576447891296178717534869071441892917687512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1407_800 : bothSeg evalE (oGrid.idx 1407) (oGrid.dm 1407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1407) oGrid.kl oGrid.kr 400 800 ⟨false, 59307288626890194419497484381494576447891296178717534869071441892917687512⟩ ⟨false, 0⟩ ⟨false, 120982472430391580183982826688561629688081977852178021667322548814597240820⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1407_1200 : bothSeg evalE (oGrid.idx 1407) (oGrid.dm 1407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1407) oGrid.kl oGrid.kr 400 1200 ⟨false, 120982472430391580183982826688561629688081977852178021667322548814597240820⟩ ⟨false, 0⟩ ⟨false, 200887982230441532242293026551887138261345914217931299789430521086959339700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1407_1600 : bothSeg evalE (oGrid.idx 1407) (oGrid.dm 1407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1407) oGrid.kl oGrid.kr 400 1600 ⟨false, 200887982230441532242293026551887138261345914217931299789430521086959339700⟩ ⟨false, 0⟩ ⟨false, 335354707998197113968463583442633564404843419679673250624082976765298140554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1407_2000 : bothSeg evalE (oGrid.idx 1407) (oGrid.dm 1407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1407) oGrid.kl oGrid.kr 400 2000 ⟨false, 335354707998197113968463583442633564404843419679673250624082976765298140554⟩ ⟨false, 0⟩ ⟨false, 521853856849886185855668085241004144072353064263799931584491070591284782986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1407_2400 : bothLoop evalE (oGrid.idx 1407) (oGrid.dm 1407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1407) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 521853856849886185855668085241004144072353064263799931584491070591284782986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1407 : oGrid.row evalE 1407 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1407_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1407_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1407_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1407_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1407_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1407_2000).1 (bothLoop_sound b_1407_2400).1))))))

theorem n_row_1407 : nGrid.row evalE 1407 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1407_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1407_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1407_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1407_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1407_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1407_2000).2 (bothLoop_sound b_1407_2400).2))))))

theorem b_1408_0 : bothSeg evalE (oGrid.idx 1408) (oGrid.dm 1408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1408) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 18906095293518882144502384785000786678390529654647589892017052466063106260⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1408_400 : bothSeg evalE (oGrid.idx 1408) (oGrid.dm 1408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1408) oGrid.kl oGrid.kr 400 400 ⟨false, 18906095293518882144502384785000786678390529654647589892017052466063106260⟩ ⟨false, 0⟩ ⟨false, 60173542269515356698131931199018793882170736887045969977221981779859870052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1408_800 : bothSeg evalE (oGrid.idx 1408) (oGrid.dm 1408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1408) oGrid.kl oGrid.kr 400 800 ⟨false, 60173542269515356698131931199018793882170736887045969977221981779859870052⟩ ⟨false, 0⟩ ⟨false, 121849451505742855562112924594129386687787300599707507167618187480248467028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1408_1200 : bothSeg evalE (oGrid.idx 1408) (oGrid.dm 1408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1408) oGrid.kl oGrid.kr 400 1200 ⟨false, 121849451505742855562112924594129386687787300599707507167618187480248467028⟩ ⟨false, 0⟩ ⟨false, 202061916615430776151446779203935712806774880306421687134825782181152186510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1408_1600 : bothSeg evalE (oGrid.idx 1408) (oGrid.dm 1408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1408) oGrid.kl oGrid.kr 400 1600 ⟨false, 202061916615430776151446779203935712806774880306421687134825782181152186510⟩ ⟨false, 0⟩ ⟨false, 336795319015784236890190807424554454741407811626086768600992020456892625438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1408_2000 : bothSeg evalE (oGrid.idx 1408) (oGrid.dm 1408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1408) oGrid.kl oGrid.kr 400 2000 ⟨false, 336795319015784236890190807424554454741407811626086768600992020456892625438⟩ ⟨false, 0⟩ ⟨false, 523528803821336123829094352758893417087303969925240220203973297683542173484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1408_2400 : bothLoop evalE (oGrid.idx 1408) (oGrid.dm 1408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1408) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 523528803821336123829094352758893417087303969925240220203973297683542173484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1408 : oGrid.row evalE 1408 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1408_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1408_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1408_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1408_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1408_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1408_2000).1 (bothLoop_sound b_1408_2400).1))))))

theorem n_row_1408 : nGrid.row evalE 1408 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1408_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1408_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1408_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1408_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1408_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1408_2000).2 (bothLoop_sound b_1408_2400).2))))))

theorem b_1409_0 : bothSeg evalE (oGrid.idx 1409) (oGrid.dm 1409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1409) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 19319393493822186945004914526602117627882516173963979851686218902555886612⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1409_400 : bothSeg evalE (oGrid.idx 1409) (oGrid.dm 1409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1409) oGrid.kl oGrid.kr 400 400 ⟨false, 19319393493822186945004914526602117627882516173963979851686218902555886612⟩ ⟨false, 0⟩ ⟨false, 61042025792238518328810443758787531914287752657008346404634661435175980220⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1409_800 : bothSeg evalE (oGrid.idx 1409) (oGrid.dm 1409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1409) oGrid.kl oGrid.kr 400 800 ⟨false, 61042025792238518328810443758787531914287752657008346404634661435175980220⟩ ⟨false, 0⟩ ⟨false, 122715969230921850431391783961573293606901000052971780402527618623144261610⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1409_1200 : bothSeg evalE (oGrid.idx 1409) (oGrid.dm 1409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1409) oGrid.kl oGrid.kr 400 1200 ⟨false, 122715969230921850431391783961573293606901000052971780402527618623144261610⟩ ⟨false, 0⟩ ⟨false, 203235417631315195687982599074386228908973902828012063589898854801247890632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1409_1600 : bothSeg evalE (oGrid.idx 1409) (oGrid.dm 1409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1409) oGrid.kl oGrid.kr 400 1600 ⟨false, 203235417631315195687982599074386228908973902828012063589898854801247890632⟩ ⟨false, 0⟩ ⟨false, 338235515652951856164893159214935818989681180511353795918121378446161467662⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1409_2000 : bothSeg evalE (oGrid.idx 1409) (oGrid.dm 1409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1409) oGrid.kl oGrid.kr 400 2000 ⟨false, 338235515652951856164893159214935818989681180511353795918121378446161467662⟩ ⟨false, 0⟩ ⟨false, 525203373815600975074408494816914859419293703200451080841010998969263024126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1409_2400 : bothLoop evalE (oGrid.idx 1409) (oGrid.dm 1409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1409) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 525203373815600975074408494816914859419293703200451080841010998969263024126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1409 : oGrid.row evalE 1409 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1409_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1409_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1409_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1409_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1409_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1409_2000).1 (bothLoop_sound b_1409_2400).1))))))

theorem n_row_1409 : nGrid.row evalE 1409 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1409_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1409_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1409_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1409_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1409_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1409_2000).2 (bothLoop_sound b_1409_2400).2))))))

theorem b_1410_0 : bothSeg evalE (oGrid.idx 1410) (oGrid.dm 1410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1410) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 19733245316693509488376399897721923173235560527341902424228407957108395488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1410_400 : bothSeg evalE (oGrid.idx 1410) (oGrid.dm 1410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1410) oGrid.kl oGrid.kr 400 400 ⟨false, 19733245316693509488376399897721923173235560527341902424228407957108395488⟩ ⟨false, 0⟩ ⟨false, 61912688942735237112770600321056175891949047671321326348819132762327149994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1410_800 : bothSeg evalE (oGrid.idx 1410) (oGrid.dm 1410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1410) oGrid.kl oGrid.kr 400 800 ⟨false, 61912688942735237112770600321056175891949047671321326348819132762327149994⟩ ⟨false, 0⟩ ⟨false, 123582013174403868928200686200133484365360693947631800843383092762733313304⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1410_1200 : bothSeg evalE (oGrid.idx 1410) (oGrid.dm 1410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1410) oGrid.kl oGrid.kr 400 1200 ⟨false, 123582013174403868928200686200133484365360693947631800843383092762733313304⟩ ⟨false, 0⟩ ⟨false, 204408467662804763029892868468541080906631526994380622533106413938093149056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1410_1600 : bothSeg evalE (oGrid.idx 1410) (oGrid.dm 1410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1410) oGrid.kl oGrid.kr 400 1600 ⟨false, 204408467662804763029892868468541080906631526994380622533106413938093149056⟩ ⟨false, 0⟩ ⟨false, 339675280225876349381492604555001326114083529321651744768855595815904315528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1410_2000 : bothSeg evalE (oGrid.idx 1410) (oGrid.dm 1410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1410) oGrid.kl oGrid.kr 400 2000 ⟨false, 339675280225876349381492604555001326114083529321651744768855595815904315528⟩ ⟨false, 0⟩ ⟨false, 526877549081090409665385951842701837152772282591747894478124404314493055440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1410_2400 : bothLoop evalE (oGrid.idx 1410) (oGrid.dm 1410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1410) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 526877549081090409665385951842701837152772282591747894478124404314493055440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1410 : oGrid.row evalE 1410 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1410_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1410_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1410_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1410_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1410_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1410_2000).1 (bothLoop_sound b_1410_2400).1))))))

theorem n_row_1410 : nGrid.row evalE 1410 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1410_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1410_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1410_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1410_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1410_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1410_2000).2 (bothLoop_sound b_1410_2400).2))))))

theorem b_1411_0 : bothSeg evalE (oGrid.idx 1411) (oGrid.dm 1411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1411) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 20147650014179965325293577228899655518500958307401161990327744605837752506⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1411_400 : bothSeg evalE (oGrid.idx 1411) (oGrid.dm 1411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1411) oGrid.kl oGrid.kr 400 400 ⟨false, 20147650014179965325293577228899655518500958307401161990327744605837752506⟩ ⟨false, 0⟩ ⟨false, 62785473369995792452431986791521044608920855928648323470491342020894116856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1411_800 : bothSeg evalE (oGrid.idx 1411) (oGrid.dm 1411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1411) oGrid.kl oGrid.kr 400 800 ⟨false, 62785473369995792452431986791521044608920855928648323470491342020894116856⟩ ⟨false, 0⟩ ⟨false, 124447556842570496305786297889817158603858579987893184494379460855707116600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1411_1200 : bothSeg evalE (oGrid.idx 1411) (oGrid.dm 1411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1411) oGrid.kl oGrid.kr 400 1200 ⟨false, 124447556842570496305786297889817158603858579987893184494379460855707116600⟩ ⟨false, 0⟩ ⟨false, 205581040779501735107670740050467885490899211105532224227979247441045371472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1411_1600 : bothSeg evalE (oGrid.idx 1411) (oGrid.dm 1411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1411) oGrid.kl oGrid.kr 400 1600 ⟨false, 205581040779501735107670740050467885490899211105532224227979247441045371472⟩ ⟨false, 0⟩ ⟨false, 341114586735750902079624253981502418707525311499949972405375990437287167702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1411_2000 : bothSeg evalE (oGrid.idx 1411) (oGrid.dm 1411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1411) oGrid.kl oGrid.kr 400 2000 ⟨false, 341114586735750902079624253981502418707525311499949972405375990437287167702⟩ ⟨false, 0⟩ ⟨false, 528551303551317421143802535967387422308456441553269833838063126964620766530⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1411_2400 : bothLoop evalE (oGrid.idx 1411) (oGrid.dm 1411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1411) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 528551303551317421143802535967387422308456441553269833838063126964620766530⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1411 : oGrid.row evalE 1411 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1411_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1411_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1411_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1411_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1411_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1411_2000).1 (bothLoop_sound b_1411_2400).1))))))

theorem n_row_1411 : nGrid.row evalE 1411 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1411_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1411_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1411_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1411_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1411_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1411_2000).2 (bothLoop_sound b_1411_2400).2))))))

theorem b_1412_0 : bothSeg evalE (oGrid.idx 1412) (oGrid.dm 1412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1412) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 20562605407040528507922824730186223589200589430402357797816169192178464724⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1412_400 : bothSeg evalE (oGrid.idx 1412) (oGrid.dm 1412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1412) oGrid.kl oGrid.kr 400 400 ⟨false, 20562605407040528507922824730186223589200589430402357797816169192178464724⟩ ⟨false, 0⟩ ⟨false, 63660319270890114629588262823638535306267613554310806205766930076299284170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1412_800 : bothSeg evalE (oGrid.idx 1412) (oGrid.dm 1412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1412) oGrid.kl oGrid.kr 400 800 ⟨false, 63660319270890114629588262823638535306267613554310806205766930076299284170⟩ ⟨false, 0⟩ ⟨false, 125312603481358470206807952447701802358302986767682393319955542530951447118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1412_1200 : bothSeg evalE (oGrid.idx 1412) (oGrid.dm 1412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1412) oGrid.kl oGrid.kr 400 1200 ⟨false, 125312603481358470206807952447701802358302986767682393319955542530951447118⟩ ⟨false, 0⟩ ⟨false, 206753139337820806380432563461508271582996185551728681156447311358410545818⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1412_1600 : bothSeg evalE (oGrid.idx 1412) (oGrid.dm 1412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1412) oGrid.kl oGrid.kr 400 1600 ⟨false, 206753139337820806380432563461508271582996185551728681156447311358410545818⟩ ⟨false, 0⟩ ⟨false, 342553437470705467476429431065631695654346692999481282127718256261122870334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1412_2000 : bothSeg evalE (oGrid.idx 1412) (oGrid.dm 1412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1412) oGrid.kl oGrid.kr 400 2000 ⟨false, 342553437470705467476429431065631695654346692999481282127718256261122870334⟩ ⟨false, 0⟩ ⟨false, 530224639446818206642040415948550990874228636139557474903579992746150917546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1412_2400 : bothLoop evalE (oGrid.idx 1412) (oGrid.dm 1412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1412) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 530224639446818206642040415948550990874228636139557474903579992746150917546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1412 : oGrid.row evalE 1412 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1412_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1412_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1412_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1412_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1412_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1412_2000).1 (bothLoop_sound b_1412_2400).1))))))

theorem n_row_1412 : nGrid.row evalE 1412 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1412_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1412_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1412_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1412_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1412_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1412_2000).2 (bothLoop_sound b_1412_2400).2))))))

theorem b_1413_0 : bothSeg evalE (oGrid.idx 1413) (oGrid.dm 1413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1413) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 20978107556945565029967471434121136729402751471093056712193839009244782288⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1413_400 : bothSeg evalE (oGrid.idx 1413) (oGrid.dm 1413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1413) oGrid.kl oGrid.kr 400 400 ⟨false, 20978107556945565029967471434121136729402751471093056712193839009244782288⟩ ⟨false, 0⟩ ⟨false, 64537156068114566021806185190089820385353414213053828091801061500401038272⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1413_800 : bothSeg evalE (oGrid.idx 1413) (oGrid.dm 1413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1413) oGrid.kl oGrid.kr 400 800 ⟨false, 64537156068114566021806185190089820385353414213053828091801061500401038272⟩ ⟨false, 0⟩ ⟨false, 126177111404006566891580977924753707889595479075766625136794013696306572868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1413_1200 : bothSeg evalE (oGrid.idx 1413) (oGrid.dm 1413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1413) oGrid.kl oGrid.kr 400 1200 ⟨false, 126177111404006566891580977924753707889595479075766625136794013696306572868⟩ ⟨false, 0⟩ ⟨false, 207924722514577821944358126015702227612877512741836637408283166124482080900⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1413_1600 : bothSeg evalE (oGrid.idx 1413) (oGrid.dm 1413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1413) oGrid.kl oGrid.kr 400 1600 ⟨false, 207924722514577821944358126015702227612877512741836637408283166124482080900⟩ ⟨false, 0⟩ ⟨false, 343991791539395286760548203602742924816522105960434623379715305417303346290⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1413_2000 : bothSeg evalE (oGrid.idx 1413) (oGrid.dm 1413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1413) oGrid.kl oGrid.kr 400 2000 ⟨false, 343991791539395286760548203602742924816522105960434623379715305417303346290⟩ ⟨false, 0⟩ ⟨false, 531897515808740607560293494606043390507322489698408381980081383423064192840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1413_2400 : bothLoop evalE (oGrid.idx 1413) (oGrid.dm 1413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1413) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 531897515808740607560293494606043390507322489698408381980081383423064192840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1413 : oGrid.row evalE 1413 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1413_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1413_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1413_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1413_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1413_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1413_2000).1 (bothLoop_sound b_1413_2400).1))))))

theorem n_row_1413 : nGrid.row evalE 1413 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1413_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1413_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1413_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1413_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1413_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1413_2000).2 (bothLoop_sound b_1413_2400).2))))))

theorem b_1414_0 : bothSeg evalE (oGrid.idx 1414) (oGrid.dm 1414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1414) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 21394151842101938676792705607762817070011637526290417219340066605126686222⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1414_400 : bothSeg evalE (oGrid.idx 1414) (oGrid.dm 1414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1414) oGrid.kl oGrid.kr 400 400 ⟨false, 21394151842101938676792705607762817070011637526290417219340066605126686222⟩ ⟨false, 0⟩ ⟨false, 65415907952361368513376297241560702131484383555364598563242665063605399930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1414_800 : bothSeg evalE (oGrid.idx 1414) (oGrid.dm 1414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1414) oGrid.kl oGrid.kr 400 800 ⟨false, 65415907952361368513376297241560702131484383555364598563242665063605399930⟩ ⟨false, 0⟩ ⟨false, 127041074218474489423966332069549610214108209229695498575859457490850857142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1414_1200 : bothSeg evalE (oGrid.idx 1414) (oGrid.dm 1414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1414) oGrid.kl oGrid.kr 400 1200 ⟨false, 127041074218474489423966332069549610214108209229695498575859457490850857142⟩ ⟨false, 0⟩ ⟨false, 209095783823257699621132309526341647103196636311998647790767233583645220398⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1414_1600 : bothSeg evalE (oGrid.idx 1414) (oGrid.dm 1414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1414) oGrid.kl oGrid.kr 400 1600 ⟨false, 209095783823257699621132309526341647103196636311998647790767233583645220398⟩ ⟨false, 0⟩ ⟨false, 345429642387268618600955325103660754292518596208348076774482705113776621110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1414_2000 : bothSeg evalE (oGrid.idx 1414) (oGrid.dm 1414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1414) oGrid.kl oGrid.kr 400 2000 ⟨false, 345429642387268618600955325103660754292518596208348076774482705113776621110⟩ ⟨false, 0⟩ ⟨false, 533569926015111759446363988496036608077192363761124484331951279581827443396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1414_2400 : bothLoop evalE (oGrid.idx 1414) (oGrid.dm 1414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1414) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 533569926015111759446363988496036608077192363761124484331951279581827443396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1414 : oGrid.row evalE 1414 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1414_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1414_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1414_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1414_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1414_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1414_2000).1 (bothLoop_sound b_1414_2400).1))))))

theorem n_row_1414 : nGrid.row evalE 1414 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1414_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1414_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1414_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1414_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1414_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1414_2000).2 (bothLoop_sound b_1414_2400).2))))))

theorem b_1415_0 : bothSeg evalE (oGrid.idx 1415) (oGrid.dm 1415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1415) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 21810738519335565180343031486638668812156558751176221681670890943247873056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1415_400 : bothSeg evalE (oGrid.idx 1415) (oGrid.dm 1415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1415) oGrid.kl oGrid.kr 400 400 ⟨false, 21810738519335565180343031486638668812156558751176221681670890943247873056⟩ ⟨false, 0⟩ ⟨false, 66296500038303931327959207865336270198700811080663773434519557446554427432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1415_800 : bothSeg evalE (oGrid.idx 1415) (oGrid.dm 1415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1415) oGrid.kl oGrid.kr 400 800 ⟨false, 66296500038303931327959207865336270198700811080663773434519557446554427432⟩ ⟨false, 0⟩ ⟨false, 127904472053551785431003059191374018864372452910636078107776573389685331390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1415_1200 : bothSeg evalE (oGrid.idx 1415) (oGrid.dm 1415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1415) oGrid.kl oGrid.kr 400 1200 ⟨false, 127904472053551785431003059191374018864372452910636078107776573389685331390⟩ ⟨false, 0⟩ ⟨false, 210266307146807338615703551969929213150772444543464148356484273701211149348⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1415_1600 : bothSeg evalE (oGrid.idx 1415) (oGrid.dm 1415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1415) oGrid.kl oGrid.kr 400 1600 ⟨false, 210266307146807338615703551969929213150772444543464148356484273701211149348⟩ ⟨false, 0⟩ ⟨false, 346866973829359455459914112803301356556259205855327141562492769745379782118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1415_2000 : bothSeg evalE (oGrid.idx 1415) (oGrid.dm 1415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1415) oGrid.kl oGrid.kr 400 2000 ⟨false, 346866973829359455459914112803301356556259205855327141562492769745379782118⟩ ⟨false, 0⟩ ⟨false, 535241853813630728667671348517679769310354654885041207814123017119543189972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1415_2400 : bothLoop evalE (oGrid.idx 1415) (oGrid.dm 1415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1415) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 535241853813630728667671348517679769310354654885041207814123017119543189972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1415 : oGrid.row evalE 1415 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1415_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1415_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1415_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1415_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1415_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1415_2000).1 (bothLoop_sound b_1415_2400).1))))))

theorem n_row_1415 : nGrid.row evalE 1415 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1415_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1415_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1415_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1415_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1415_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1415_2000).2 (bothLoop_sound b_1415_2400).2))))))

theorem o_blk_1392 : allFrom (fun j => oGrid.row evalE j) 1392 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1392) o_row_1392 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1393) o_row_1393 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1394) o_row_1394 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1395) o_row_1395 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1396) o_row_1396 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1397) o_row_1397 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1398) o_row_1398 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1399) o_row_1399 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1400) o_row_1400 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1401) o_row_1401 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1402) o_row_1402 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1403) o_row_1403 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1404) o_row_1404 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1405) o_row_1405 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1406) o_row_1406 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1407) o_row_1407 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1408) o_row_1408 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1409) o_row_1409 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1410) o_row_1410 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1411) o_row_1411 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1412) o_row_1412 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1413) o_row_1413 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1414) o_row_1414 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1415) o_row_1415 (allFrom_zero (fun j => oGrid.row evalE j) 1416)))))))))))))))))))))))))

theorem n_blk_1392 : allFrom (fun j => nGrid.row evalE j) 1392 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1392) n_row_1392 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1393) n_row_1393 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1394) n_row_1394 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1395) n_row_1395 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1396) n_row_1396 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1397) n_row_1397 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1398) n_row_1398 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1399) n_row_1399 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1400) n_row_1400 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1401) n_row_1401 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1402) n_row_1402 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1403) n_row_1403 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1404) n_row_1404 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1405) n_row_1405 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1406) n_row_1406 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1407) n_row_1407 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1408) n_row_1408 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1409) n_row_1409 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1410) n_row_1410 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1411) n_row_1411 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1412) n_row_1412 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1413) n_row_1413 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1414) n_row_1414 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1415) n_row_1415 (allFrom_zero (fun j => nGrid.row evalE j) 1416)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
