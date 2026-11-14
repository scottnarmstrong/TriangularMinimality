/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 57 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1368`–`1391`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1368_0 : bothSeg evalE (oGrid.idx 1368) (oGrid.dm 1368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1368) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2674963201036110218437098441652550093444474970550844497614003770798676938⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ = true := by
  decide +kernel

theorem b_1368_400 : bothSeg evalE (oGrid.idx 1368) (oGrid.dm 1368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1368) oGrid.kl oGrid.kr 400 400 ⟨false, 2674963201036110218437098441652550093444474970550844497614003770798676938⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ ⟨false, 27192454961728817451473666057892225241283629692626295643441906538836141954⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ = true := by
  decide +kernel

theorem b_1368_800 : bothSeg evalE (oGrid.idx 1368) (oGrid.dm 1368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1368) oGrid.kl oGrid.kr 400 800 ⟨false, 27192454961728817451473666057892225241283629692626295643441906538836141954⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ ⟨false, 86470581387537041771418703962322883729783299525202469532024922854468882306⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ = true := by
  decide +kernel

theorem b_1368_1200 : bothSeg evalE (oGrid.idx 1368) (oGrid.dm 1368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1368) oGrid.kl oGrid.kr 400 1200 ⟨false, 86470581387537041771418703962322883729783299525202469532024922854468882306⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ ⟨false, 154722544232999110962109669016775348666388091540834713811181232137874840998⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ = true := by
  decide +kernel

theorem b_1368_1600 : bothSeg evalE (oGrid.idx 1368) (oGrid.dm 1368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1368) oGrid.kl oGrid.kr 400 1600 ⟨false, 154722544232999110962109669016775348666388091540834713811181232137874840998⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ ⟨false, 278804437197475888452617348609869853975890230591690304187299800189043665756⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ = true := by
  decide +kernel

theorem b_1368_2000 : bothSeg evalE (oGrid.idx 1368) (oGrid.dm 1368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1368) oGrid.kl oGrid.kr 400 2000 ⟨false, 278804437197475888452617348609869853975890230591690304187299800189043665756⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ ⟨false, 456194390524666102071006078680750384416192149761136973726461098985435845508⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ = true := by
  decide +kernel

theorem b_1368_2400 : bothLoop evalE (oGrid.idx 1368) (oGrid.dm 1368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1368) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 456194390524666102071006078680750384416192149761136973726461098985435845508⟩ ⟨false, 253099656785923321664892558323853330094024232057094109469812132461790010⟩ = true := by
  decide +kernel

theorem o_row_1368 : oGrid.row evalE 1368 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1368_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1368_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1368_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1368_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1368_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1368_2000).1 (bothLoop_sound b_1368_2400).1))))))

theorem n_row_1368 : nGrid.row evalE 1368 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1368_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1368_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1368_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1368_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1368_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1368_2000).2 (bothLoop_sound b_1368_2400).2))))))

theorem b_1369_0 : bothSeg evalE (oGrid.idx 1369) (oGrid.dm 1369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1369) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3081944627479827578421917029043468109972663449238026937380253648287149080⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ = true := by
  decide +kernel

theorem b_1369_400 : bothSeg evalE (oGrid.idx 1369) (oGrid.dm 1369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1369) oGrid.kl oGrid.kr 400 400 ⟨false, 3081944627479827578421917029043468109972663449238026937380253648287149080⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ ⟨false, 27988629621224089257700117229894392679442976575496011145863861727523326036⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ = true := by
  decide +kernel

theorem b_1369_800 : bothSeg evalE (oGrid.idx 1369) (oGrid.dm 1369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1369) oGrid.kl oGrid.kr 400 800 ⟨false, 27988629621224089257700117229894392679442976575496011145863861727523326036⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ ⟨false, 87391694981024155534438985001806790000549037280753217499355609799787674378⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ = true := by
  decide +kernel

theorem b_1369_1200 : bothSeg evalE (oGrid.idx 1369) (oGrid.dm 1369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1369) oGrid.kl oGrid.kr 400 1200 ⟨false, 87391694981024155534438985001806790000549037280753217499355609799787674378⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ ⟨false, 155921324571742442599460689590295509572747213043997147661409301170584607858⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ = true := by
  decide +kernel

theorem b_1369_1600 : bothSeg evalE (oGrid.idx 1369) (oGrid.dm 1369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1369) oGrid.kl oGrid.kr 400 1600 ⟨false, 155921324571742442599460689590295509572747213043997147661409301170584607858⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ ⟨false, 280269098804634186876499573982475972568965109089105715597425486033632877182⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ = true := by
  decide +kernel

theorem b_1369_2000 : bothSeg evalE (oGrid.idx 1369) (oGrid.dm 1369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1369) oGrid.kl oGrid.kr 400 2000 ⟨false, 280269098804634186876499573982475972568965109089105715597425486033632877182⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ ⟨false, 457891875570362224848763664125115383067635955026158072459232009108654636724⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ = true := by
  decide +kernel

theorem b_1369_2400 : bothLoop evalE (oGrid.idx 1369) (oGrid.dm 1369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1369) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 457891875570362224848763664125115383067635955026158072459232009108654636724⟩ ⟨false, 133244756025856691427501165840593379706178608834359056243982327613580770⟩ = true := by
  decide +kernel

theorem o_row_1369 : oGrid.row evalE 1369 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1369_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1369_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1369_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1369_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1369_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1369_2000).1 (bothLoop_sound b_1369_2400).1))))))

theorem n_row_1369 : nGrid.row evalE 1369 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1369_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1369_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1369_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1369_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1369_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1369_2000).2 (bothLoop_sound b_1369_2400).2))))))

theorem b_1370_0 : bothSeg evalE (oGrid.idx 1370) (oGrid.dm 1370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1370) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3488160616172023756024760980334673634123400188083794439891650816305656668⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ = true := by
  decide +kernel

theorem b_1370_400 : bothSeg evalE (oGrid.idx 1370) (oGrid.dm 1370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1370) oGrid.kl oGrid.kr 400 400 ⟨false, 3488160616172023756024760980334673634123400188083794439891650816305656668⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ ⟨false, 28785067861609577164118002781773786597990554562351093880080437739905694938⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ = true := by
  decide +kernel

theorem b_1370_800 : bothSeg evalE (oGrid.idx 1370) (oGrid.dm 1370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1370) oGrid.kl oGrid.kr 400 800 ⟨false, 28785067861609577164118002781773786597990554562351093880080437739905694938⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ ⟨false, 88309390389697122506133162584411793289911386491368828185038555210324171740⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ = true := by
  decide +kernel

theorem b_1370_1200 : bothSeg evalE (oGrid.idx 1370) (oGrid.dm 1370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1370) oGrid.kl oGrid.kr 400 1200 ⟨false, 88309390389697122506133162584411793289911386491368828185038555210324171740⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ ⟨false, 157118743300353205687576143600966455592199193589262597207885966397711837086⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ = true := by
  decide +kernel

theorem b_1370_1600 : bothSeg evalE (oGrid.idx 1370) (oGrid.dm 1370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1370) oGrid.kl oGrid.kr 400 1600 ⟨false, 157118743300353205687576143600966455592199193589262597207885966397711837086⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ ⟨false, 281732420562367746568756359308895956321004641349492707537953766002817658676⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ = true := by
  decide +kernel

theorem b_1370_2000 : bothSeg evalE (oGrid.idx 1370) (oGrid.dm 1370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1370) oGrid.kl oGrid.kr 400 2000 ⟨false, 281732420562367746568756359308895956321004641349492707537953766002817658676⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ ⟨false, 459588060881098548883897876656174610831667268013512197830814631905961192134⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ = true := by
  decide +kernel

theorem b_1370_2400 : bothLoop evalE (oGrid.idx 1370) (oGrid.dm 1370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1370) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 459588060881098548883897876656174610831667268013512197830814631905961192134⟩ ⟨false, 42575713115150310854798077606592859751391640947692105535776724457499350⟩ = true := by
  decide +kernel

theorem o_row_1370 : oGrid.row evalE 1370 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1370_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1370_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1370_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1370_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1370_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1370_2000).1 (bothLoop_sound b_1370_2400).1))))))

theorem n_row_1370 : nGrid.row evalE 1370 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1370_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1370_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1370_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1370_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1370_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1370_2000).2 (bothLoop_sound b_1370_2400).2))))))

theorem b_1371_0 : bothSeg evalE (oGrid.idx 1371) (oGrid.dm 1371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1371) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3893772018395530024550928588599119341454042430490312236322311149034566500⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1371_400 : bothSeg evalE (oGrid.idx 1371) (oGrid.dm 1371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1371) oGrid.kl oGrid.kr 400 400 ⟨false, 3893772018395530024550928588599119341454042430490312236322311149034566500⟩ ⟨false, 0⟩ ⟨false, 29581974159967285207668061665663109647754603419108965257740303833477083898⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1371_800 : bothSeg evalE (oGrid.idx 1371) (oGrid.dm 1371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1371) oGrid.kl oGrid.kr 400 800 ⟨false, 29581974159967285207668061665663109647754603419108965257740303833477083898⟩ ⟨false, 0⟩ ⟨false, 89223889880237477324620362716520780535840938310185362188056681383719056878⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1371_1200 : bothSeg evalE (oGrid.idx 1371) (oGrid.dm 1371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1371) oGrid.kl oGrid.kr 400 1200 ⟨false, 89223889880237477324620362716520780535840938310185362188056681383719056878⟩ ⟨false, 0⟩ ⟨false, 158314926527642735701052444353311118277195359615638474627315012433676760476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1371_1600 : bothSeg evalE (oGrid.idx 1371) (oGrid.dm 1371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1371) oGrid.kl oGrid.kr 400 1600 ⟨false, 158314926527642735701052444353311118277195359615638474627315012433676760476⟩ ⟨false, 0⟩ ⟨false, 283194528505944818138172037079557739856492400884140171915720779605974080912⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1371_2000 : bothSeg evalE (oGrid.idx 1371) (oGrid.dm 1371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1371) oGrid.kl oGrid.kr 400 2000 ⟨false, 283194528505944818138172037079557739856492400884140171915720779605974080912⟩ ⟨false, 0⟩ ⟨false, 461283072420940595307598047486307130725639676781658512621357714909763285978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1371_2400 : bothLoop evalE (oGrid.idx 1371) (oGrid.dm 1371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1371) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 461283072420940595307598047486307130725639676781658512621357714909763285978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1371 : oGrid.row evalE 1371 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1371_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1371_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1371_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1371_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1371_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1371_2000).1 (bothLoop_sound b_1371_2400).1))))))

theorem n_row_1371 : nGrid.row evalE 1371 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1371_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1371_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1371_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1371_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1371_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1371_2000).2 (bothLoop_sound b_1371_2400).2))))))

theorem b_1372_0 : bothSeg evalE (oGrid.idx 1372) (oGrid.dm 1372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1372) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4298880925209018677556784048675203069108699997172219230871781577496211312⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1372_400 : bothSeg evalE (oGrid.idx 1372) (oGrid.dm 1372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1372) oGrid.kl oGrid.kr 400 400 ⟨false, 4298880925209018677556784048675203069108699997172219230871781577496211312⟩ ⟨false, 0⟩ ⟨false, 30379500968139363051905999857000908151048413854111585652215918493768690178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1372_800 : bothSeg evalE (oGrid.idx 1372) (oGrid.dm 1372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1372) oGrid.kl oGrid.kr 400 800 ⟨false, 30379500968139363051905999857000908151048413854111585652215918493768690178⟩ ⟨false, 0⟩ ⟨false, 90135383357543395370558843092771124014543515769483313839100476611840022834⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1372_1200 : bothSeg evalE (oGrid.idx 1372) (oGrid.dm 1372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1372) oGrid.kl oGrid.kr 400 1200 ⟨false, 90135383357543395370558843092771124014543515769483313839100476611840022834⟩ ⟨false, 0⟩ ⟨false, 159509982571576353877529271697758864227437812140829196528765999087521605728⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1372_1600 : bothSeg evalE (oGrid.idx 1372) (oGrid.dm 1372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1372) oGrid.kl oGrid.kr 400 1600 ⟨false, 159509982571576353877529271697758864227437812140829196528765999087521605728⟩ ⟨false, 0⟩ ⟨false, 284655530879919873567726280488602497398438311466493922340566610826764485998⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1372_2000 : bothSeg evalE (oGrid.idx 1372) (oGrid.dm 1372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1372) oGrid.kl oGrid.kr 400 2000 ⟨false, 284655530879919873567726280488602497398438311466493922340566610826764485998⟩ ⟨false, 0⟩ ⟨false, 462977018363329713026722305630599239454651944038521130557218697408676550572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1372_2400 : bothLoop evalE (oGrid.idx 1372) (oGrid.dm 1372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1372) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 462977018363329713026722305630599239454651944038521130557218697408676550572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1372 : oGrid.row evalE 1372 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1372_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1372_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1372_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1372_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1372_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1372_2000).1 (bothLoop_sound b_1372_2400).1))))))

theorem n_row_1372 : nGrid.row evalE 1372 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1372_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1372_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1372_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1372_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1372_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1372_2000).2 (bothLoop_sound b_1372_2400).2))))))

theorem b_1373_0 : bothSeg evalE (oGrid.idx 1373) (oGrid.dm 1373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1373) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4703480651940191833531280140320745391839247563366041656099496990884479928⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1373_400 : bothSeg evalE (oGrid.idx 1373) (oGrid.dm 1373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1373) oGrid.kl oGrid.kr 400 400 ⟨false, 4703480651940191833531280140320745391839247563366041656099496990884479928⟩ ⟨false, 0⟩ ⟨false, 31177689685030548581176455847896874975540860526885175528484368195644534740⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1373_800 : bothSeg evalE (oGrid.idx 1373) (oGrid.dm 1373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1373) oGrid.kl oGrid.kr 400 800 ⟨false, 31177689685030548581176455847896874975540860526885175528484368195644534740⟩ ⟨false, 0⟩ ⟨false, 91043971711307630205041395995896026007532515128516727837455786871207280130⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1373_1200 : bothSeg evalE (oGrid.idx 1373) (oGrid.dm 1373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1373) oGrid.kl oGrid.kr 400 1200 ⟨false, 91043971711307630205041395995896026007532515128516727837455786871207280130⟩ ⟨false, 0⟩ ⟨false, 160703920787387425035969301586311646821236990353428862616051196324828105542⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1373_1600 : bothSeg evalE (oGrid.idx 1373) (oGrid.dm 1373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1373) oGrid.kl oGrid.kr 400 1600 ⟨false, 160703920787387425035969301586311646821236990353428862616051196324828105542⟩ ⟨false, 0⟩ ⟨false, 286115436966247461805819742255736787286445137910854672416657069244057775924⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1373_2000 : bothSeg evalE (oGrid.idx 1373) (oGrid.dm 1373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1373) oGrid.kl oGrid.kr 400 2000 ⟨false, 286115436966247461805819742255736787286445137910854672416657069244057775924⟩ ⟨false, 0⟩ ⟨false, 464669907919196855487237990350500689518142717427951322617670553729872504646⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1373_2400 : bothLoop evalE (oGrid.idx 1373) (oGrid.dm 1373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1373) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 464669907919196855487237990350500689518142717427951322617670553729872504646⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1373 : oGrid.row evalE 1373 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1373_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1373_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1373_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1373_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1373_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1373_2000).1 (bothLoop_sound b_1373_2400).1))))))

theorem n_row_1373 : nGrid.row evalE 1373 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1373_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1373_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1373_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1373_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1373_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1373_2000).2 (bothLoop_sound b_1373_2400).2))))))

theorem b_1374_0 : bothSeg evalE (oGrid.idx 1374) (oGrid.dm 1374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1374) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5107630939890478754357373959923664667638595916623541504913524107486066134⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1374_400 : bothSeg evalE (oGrid.idx 1374) (oGrid.dm 1374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1374) oGrid.kl oGrid.kr 400 400 ⟨false, 5107630939890478754357373959923664667638595916623541504913524107486066134⟩ ⟨false, 0⟩ ⟨false, 31976648300542305417001714479481097931441601237496049602399816229863538826⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1374_800 : bothSeg evalE (oGrid.idx 1374) (oGrid.dm 1374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1374) oGrid.kl oGrid.kr 400 800 ⟨false, 31976648300542305417001714479481097931441601237496049602399816229863538826⟩ ⟨false, 0⟩ ⟨false, 91949729323377967109601360017793759973822443635989592078226004475178949666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1374_1200 : bothSeg evalE (oGrid.idx 1374) (oGrid.dm 1374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1374) oGrid.kl oGrid.kr 400 1200 ⟨false, 91949729323377967109601360017793759973822443635989592078226004475178949666⟩ ⟨false, 0⟩ ⟨false, 161896721597713114265732875171312655334561352159482574540198641535053273128⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1374_1600 : bothSeg evalE (oGrid.idx 1374) (oGrid.dm 1374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1374) oGrid.kl oGrid.kr 400 1600 ⟨false, 161896721597713114265732875171312655334561352159482574540198641535053273128⟩ ⟨false, 0⟩ ⟨false, 287574227114417763463712155548851645329396416937579869371365619653316934988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1374_2000 : bothSeg evalE (oGrid.idx 1374) (oGrid.dm 1374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1374) oGrid.kl oGrid.kr 400 2000 ⟨false, 287574227114417763463712155548851645329396416937579869371365619653316934988⟩ ⟨false, 0⟩ ⟨false, 466361721367098056516700199660069917094833325985442615116418302421248407786⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1374_2400 : bothLoop evalE (oGrid.idx 1374) (oGrid.dm 1374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1374) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 466361721367098056516700199660069917094833325985442615116418302421248407786⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1374 : oGrid.row evalE 1374 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1374_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1374_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1374_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1374_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1374_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1374_2000).1 (bothLoop_sound b_1374_2400).1))))))

theorem n_row_1374 : nGrid.row evalE 1374 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1374_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1374_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1374_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1374_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1374_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1374_2000).2 (bothLoop_sound b_1374_2400).2))))))

theorem b_1375_0 : bothSeg evalE (oGrid.idx 1375) (oGrid.dm 1375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1375) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5511395041194728410249295799529633746872407865794507801978251357835263530⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1375_400 : bothSeg evalE (oGrid.idx 1375) (oGrid.dm 1375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1375) oGrid.kl oGrid.kr 400 400 ⟨false, 5511395041194728410249295799529633746872407865794507801978251357835263530⟩ ⟨false, 0⟩ ⟨false, 32776483611236963156235492713608555103641976046151692916461760810341297190⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1375_800 : bothSeg evalE (oGrid.idx 1375) (oGrid.dm 1375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1375) oGrid.kl oGrid.kr 400 800 ⟨false, 32776483611236963156235492713608555103641976046151692916461760810341297190⟩ ⟨false, 0⟩ ⟨false, 92852875224912660445093606585583658868167752974152346047693710225908504126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1375_1200 : bothSeg evalE (oGrid.idx 1375) (oGrid.dm 1375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1375) oGrid.kl oGrid.kr 400 1200 ⟨false, 92852875224912660445093606585583658868167752974152346047693710225908504126⟩ ⟨false, 0⟩ ⟨false, 163088523216357037197270629472775824761141526636972305811575164740459081102⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1375_1600 : bothSeg evalE (oGrid.idx 1375) (oGrid.dm 1375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1375) oGrid.kl oGrid.kr 400 1600 ⟨false, 163088523216357037197270629472775824761141526636972305811575164740459081102⟩ ⟨false, 0⟩ ⟨false, 289032039465219039330008444018287813331756154131096570793404344829588687702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1375_2000 : bothSeg evalE (oGrid.idx 1375) (oGrid.dm 1375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1375) oGrid.kl oGrid.kr 400 2000 ⟨false, 289032039465219039330008444018287813331756154131096570793404344829588687702⟩ ⟨false, 0⟩ ⟨false, 468052596776976799957003032741047856030122431628561333310681618758794783844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1375_2400 : bothLoop evalE (oGrid.idx 1375) (oGrid.dm 1375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1375) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 468052596776976799957003032741047856030122431628561333310681618758794783844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1375 : oGrid.row evalE 1375 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1375_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1375_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1375_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1375_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1375_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1375_2000).1 (bothLoop_sound b_1375_2400).1))))))

theorem n_row_1375 : nGrid.row evalE 1375 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1375_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1375_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1375_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1375_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1375_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1375_2000).2 (bothLoop_sound b_1375_2400).2))))))

theorem b_1376_0 : bothSeg evalE (oGrid.idx 1376) (oGrid.dm 1376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1376) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5914828616338159152687694674069359156648974228907824438157502326187165018⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1376_400 : bothSeg evalE (oGrid.idx 1376) (oGrid.dm 1376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1376) oGrid.kl oGrid.kr 400 400 ⟨false, 5914828616338159152687694674069359156648974228907824438157502326187165018⟩ ⟨false, 0⟩ ⟨false, 33577300242317223266408822893403518561481475293976662043329812268498596394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1376_800 : bothSeg evalE (oGrid.idx 1376) (oGrid.dm 1376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1376) oGrid.kl oGrid.kr 400 800 ⟨false, 33577300242317223266408822893403518561481475293976662043329812268498596394⟩ ⟨false, 0⟩ ⟨false, 93753487001856080641977024644877163554212654784320719397181271790105291888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1376_1200 : bothSeg evalE (oGrid.idx 1376) (oGrid.dm 1376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1376) oGrid.kl oGrid.kr 400 1200 ⟨false, 93753487001856080641977024644877163554212654784320719397181271790105291888⟩ ⟨false, 0⟩ ⟨false, 164279316023296525477807703641636724901033801520972381471380921004119214376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1376_1600 : bothSeg evalE (oGrid.idx 1376) (oGrid.dm 1376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1376) oGrid.kl oGrid.kr 400 1600 ⟨false, 164279316023296525477807703641636724901033801520972381471380921004119214376⟩ ⟨false, 0⟩ ⟨false, 290488864325744694325577512559046598959035445592397936513324027196919905534⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1376_2000 : bothSeg evalE (oGrid.idx 1376) (oGrid.dm 1376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1376) oGrid.kl oGrid.kr 400 2000 ⟨false, 290488864325744694325577512559046598959035445592397936513324027196919905534⟩ ⟨false, 0⟩ ⟨false, 469742524385171004711185837754018361500500933647070300990018801757135270672⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1376_2400 : bothLoop evalE (oGrid.idx 1376) (oGrid.dm 1376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1376) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 469742524385171004711185837754018361500500933647070300990018801757135270672⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1376 : oGrid.row evalE 1376 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1376_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1376_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1376_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1376_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1376_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1376_2000).1 (bothLoop_sound b_1376_2400).1))))))

theorem n_row_1376 : nGrid.row evalE 1376 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1376_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1376_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1376_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1376_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1376_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1376_2000).2 (bothLoop_sound b_1376_2400).2))))))

theorem b_1377_0 : bothSeg evalE (oGrid.idx 1377) (oGrid.dm 1377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1377) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 6317988222459022680217304171796609594646958499381388054381494074752626158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1377_400 : bothSeg evalE (oGrid.idx 1377) (oGrid.dm 1377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1377) oGrid.kl oGrid.kr 400 400 ⟨false, 6317988222459022680217304171796609594646958499381388054381494074752626158⟩ ⟨false, 0⟩ ⟨false, 34379197018291188806302010932540775441005727482474150344207783469389752148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1377_800 : bothSeg evalE (oGrid.idx 1377) (oGrid.dm 1377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1377) oGrid.kl oGrid.kr 400 800 ⟨false, 34379197018291188806302010932540775441005727482474150344207783469389752148⟩ ⟨false, 0⟩ ⟨false, 94651733967163273898897966643904882408172212083745510636432215191193068766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1377_1200 : bothSeg evalE (oGrid.idx 1377) (oGrid.dm 1377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1377) oGrid.kl oGrid.kr 400 1200 ⟨false, 94651733967163273898897966643904882408172212083745510636432215191193068766⟩ ⟨false, 0⟩ ⟨false, 165469180874353892476456191292486203413226810651833192261903558894034893434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1377_1600 : bothSeg evalE (oGrid.idx 1377) (oGrid.dm 1377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1377) oGrid.kl oGrid.kr 400 1600 ⟨false, 165469180874353892476456191292486203413226810651833192261903558894034893434⟩ ⟨false, 0⟩ ⟨false, 291944782479064341923349986577991737206963319460463176470987753678566791258⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1377_2000 : bothSeg evalE (oGrid.idx 1377) (oGrid.dm 1377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1377) oGrid.kl oGrid.kr 400 2000 ⟨false, 291944782479064341923349986577991737206963319460463176470987753678566791258⟩ ⟨false, 0⟩ ⟨false, 471431584904084010229137004904661642229536869608088187251455133442240170104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1377_2400 : bothLoop evalE (oGrid.idx 1377) (oGrid.dm 1377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1377) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 471431584904084010229137004904661642229536869608088187251455133442240170104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1377 : oGrid.row evalE 1377 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1377_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1377_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1377_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1377_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1377_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1377_2000).1 (bothLoop_sound b_1377_2400).1))))))

theorem n_row_1377 : nGrid.row evalE 1377 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1377_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1377_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1377_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1377_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1377_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1377_2000).2 (bothLoop_sound b_1377_2400).2))))))

theorem b_1378_0 : bothSeg evalE (oGrid.idx 1378) (oGrid.dm 1378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1378) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 6720929462490568691595883360429549978612254106260121783456009435494589938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1378_400 : bothSeg evalE (oGrid.idx 1378) (oGrid.dm 1378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1378) oGrid.kl oGrid.kr 400 400 ⟨false, 6720929462490568691595883360429549978612254106260121783456009435494589938⟩ ⟨false, 0⟩ ⟨false, 35182272995209052706056610642610418297631119034945411718633871716330834002⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1378_800 : bothSeg evalE (oGrid.idx 1378) (oGrid.dm 1378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1378) oGrid.kl oGrid.kr 400 800 ⟨false, 35182272995209052706056610642610418297631119034945411718633871716330834002⟩ ⟨false, 0⟩ ⟨false, 95547725962555683506132482278785693339681296726444484725105988456632082792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1378_1200 : bothSeg evalE (oGrid.idx 1378) (oGrid.dm 1378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1378) oGrid.kl oGrid.kr 400 1200 ⟨false, 95547725962555683506132482278785693339681296726444484725105988456632082792⟩ ⟨false, 0⟩ ⟨false, 166658145759608957921588040085565861224724382543754942259619997592197888316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1378_1600 : bothSeg evalE (oGrid.idx 1378) (oGrid.dm 1378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1378) oGrid.kl oGrid.kr 400 1600 ⟨false, 166658145759608957921588040085565861224724382543754942259619997592197888316⟩ ⟨false, 0⟩ ⟨false, 293399821842636127735835245050170933469605281793629366959718043481727513186⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1378_2000 : bothSeg evalE (oGrid.idx 1378) (oGrid.dm 1378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1378) oGrid.kl oGrid.kr 400 2000 ⟨false, 293399821842636127735835245050170933469605281793629366959718043481727513186⟩ ⟨false, 0⟩ ⟨false, 473119806180596821135430557514012578451600063972675403225451724123184146352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1378_2400 : bothLoop evalE (oGrid.idx 1378) (oGrid.dm 1378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1378) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 473119806180596821135430557514012578451600063972675403225451724123184146352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1378 : oGrid.row evalE 1378 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1378_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1378_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1378_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1378_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1378_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1378_2000).1 (bothLoop_sound b_1378_2400).1))))))

theorem n_row_1378 : nGrid.row evalE 1378 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1378_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1378_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1378_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1378_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1378_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1378_2000).2 (bothLoop_sound b_1378_2400).2))))))

theorem b_1379_0 : bothSeg evalE (oGrid.idx 1379) (oGrid.dm 1379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1379) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 7123709952553262657782109456048413120965337083078559864956285798868091972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1379_400 : bothSeg evalE (oGrid.idx 1379) (oGrid.dm 1379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1379) oGrid.kl oGrid.kr 400 400 ⟨false, 7123709952553262657782109456048413120965337083078559864956285798868091972⟩ ⟨false, 0⟩ ⟨false, 35986627153062577043670189707914844590341153101912385195888957584221725866⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1379_800 : bothSeg evalE (oGrid.idx 1379) (oGrid.dm 1379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1379) oGrid.kl oGrid.kr 400 800 ⟨false, 35986627153062577043670189707914844590341153101912385195888957584221725866⟩ ⟨false, 0⟩ ⟨false, 96441594683299937077028836102393385350143981184898786488541945761989668844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1379_1200 : bothSeg evalE (oGrid.idx 1379) (oGrid.dm 1379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1379) oGrid.kl oGrid.kr 400 1200 ⟨false, 96441594683299937077028836102393385350143981184898786488541945761989668844⟩ ⟨false, 0⟩ ⟨false, 167846263664999791143403684638042961236706942021330556063919769730813056256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1379_1600 : bothSeg evalE (oGrid.idx 1379) (oGrid.dm 1379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1379) oGrid.kl oGrid.kr 400 1600 ⟨false, 167846263664999791143403684638042961236706942021330556063919769730813056256⟩ ⟨false, 0⟩ ⟨false, 294854035329907271943299731411169114629347293016942976694002672039819744176⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1379_2000 : bothSeg evalE (oGrid.idx 1379) (oGrid.dm 1379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1379) oGrid.kl oGrid.kr 400 2000 ⟨false, 294854035329907271943299731411169114629347293016942976694002672039819744176⟩ ⟨false, 0⟩ ⟨false, 474807241057668570672631071155462503080412633029074737767677630223193722504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1379_2400 : bothLoop evalE (oGrid.idx 1379) (oGrid.dm 1379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1379) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 474807241057668570672631071155462503080412633029074737767677630223193722504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1379 : oGrid.row evalE 1379 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1379_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1379_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1379_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1379_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1379_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1379_2000).1 (bothLoop_sound b_1379_2400).1))))))

theorem n_row_1379 : nGrid.row evalE 1379 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1379_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1379_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1379_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1379_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1379_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1379_2000).2 (bothLoop_sound b_1379_2400).2))))))

theorem b_1380_0 : bothSeg evalE (oGrid.idx 1380) (oGrid.dm 1380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1380) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 7526378322630886116135474320447581928243579219861478434349156296936626992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1380_400 : bothSeg evalE (oGrid.idx 1380) (oGrid.dm 1380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1380) oGrid.kl oGrid.kr 400 400 ⟨false, 7526378322630886116135474320447581928243579219861478434349156296936626992⟩ ⟨false, 0⟩ ⟨false, 36792356044329459049249042348195493389214390892887433208246458968262522762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1380_800 : bothSeg evalE (oGrid.idx 1380) (oGrid.dm 1380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1380) oGrid.kl oGrid.kr 400 800 ⟨false, 36792356044329459049249042348195493389214390892887433208246458968262522762⟩ ⟨false, 0⟩ ⟨false, 97333477023414344046181888600688214548738980613227264640660953021085637398⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1380_1200 : bothSeg evalE (oGrid.idx 1380) (oGrid.dm 1380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1380) oGrid.kl oGrid.kr 400 1200 ⟨false, 97333477023414344046181888600688214548738980613227264640660953021085637398⟩ ⟨false, 0⟩ ⟨false, 169033587036063838753916319455402019673044643154135038522983185103206655102⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1380_1600 : bothSeg evalE (oGrid.idx 1380) (oGrid.dm 1380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1380) oGrid.kl oGrid.kr 400 1600 ⟨false, 169033587036063838753916319455402019673044643154135038522983185103206655102⟩ ⟨false, 0⟩ ⟨false, 296307475314054996394831707842872610688338747844762764576457041902621268926⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1380_2000 : bothSeg evalE (oGrid.idx 1380) (oGrid.dm 1380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1380) oGrid.kl oGrid.kr 400 2000 ⟨false, 296307475314054996394831707842872610688338747844762764576457041902621268926⟩ ⟨false, 0⟩ ⟨false, 476493941838077368792684274147362664375608936061076531731284841562456927764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1380_2400 : bothLoop evalE (oGrid.idx 1380) (oGrid.dm 1380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1380) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 476493941838077368792684274147362664375608936061076531731284841562456927764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1380 : oGrid.row evalE 1380 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1380_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1380_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1380_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1380_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1380_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1380_2000).1 (bothLoop_sound b_1380_2400).1))))))

theorem n_row_1380 : nGrid.row evalE 1380 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1380_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1380_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1380_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1380_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1380_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1380_2000).2 (bothLoop_sound b_1380_2400).2))))))

theorem b_1381_0 : bothSeg evalE (oGrid.idx 1381) (oGrid.dm 1381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1381) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 7928988380454686577691949892749748145289379162279482184750802832155398984⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1381_400 : bothSeg evalE (oGrid.idx 1381) (oGrid.dm 1381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1381) oGrid.kl oGrid.kr 400 400 ⟨false, 7928988380454686577691949892749748145289379162279482184750802832155398984⟩ ⟨false, 0⟩ ⟨false, 37599550708886399267411396194509630883187358947433184965337911181380950126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1381_800 : bothSeg evalE (oGrid.idx 1381) (oGrid.dm 1381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1381) oGrid.kl oGrid.kr 400 800 ⟨false, 37599550708886399267411396194509630883187358947433184965337911181380950126⟩ ⟨false, 0⟩ ⟨false, 98223458453608701592700851623174893746340807815175754422964867461961884028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1381_1200 : bothSeg evalE (oGrid.idx 1381) (oGrid.dm 1381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1381) oGrid.kl oGrid.kr 400 1200 ⟨false, 98223458453608701592700851623174893746340807815175754422964867461961884028⟩ ⟨false, 0⟩ ⟨false, 170220127464539733297075613939145757581990986258741745686814412280683701948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1381_1600 : bothSeg evalE (oGrid.idx 1381) (oGrid.dm 1381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1381) oGrid.kl oGrid.kr 400 1600 ⟨false, 170220127464539733297075613939145757581990986258741745686814412280683701948⟩ ⟨false, 0⟩ ⟨false, 297760153314588132915020081787617443211013776593765396479067470800822362024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1381_2000 : bothSeg evalE (oGrid.idx 1381) (oGrid.dm 1381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1381) oGrid.kl oGrid.kr 400 2000 ⟨false, 297760153314588132915020081787617443211013776593765396479067470800822362024⟩ ⟨false, 0⟩ ⟨false, 478179919971021831429511790844317446005625298781816510547174098280388204242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1381_2400 : bothLoop evalE (oGrid.idx 1381) (oGrid.dm 1381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1381) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 478179919971021831429511790844317446005625298781816510547174098280388204242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1381 : oGrid.row evalE 1381 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1381_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1381_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1381_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1381_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1381_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1381_2000).1 (bothLoop_sound b_1381_2400).1))))))

theorem n_row_1381 : nGrid.row evalE 1381 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1381_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1381_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1381_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1381_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1381_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1381_2000).2 (bothLoop_sound b_1381_2400).2))))))

theorem b_1382_0 : bothSeg evalE (oGrid.idx 1382) (oGrid.dm 1382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1382) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 8331584798413506685202805246434244192204567899053618096522796380886309210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1382_400 : bothSeg evalE (oGrid.idx 1382) (oGrid.dm 1382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1382) oGrid.kl oGrid.kr 400 400 ⟨false, 8331584798413506685202805246434244192204567899053618096522796380886309210⟩ ⟨false, 0⟩ ⟨false, 38408299063109139569464687460743917832185285008153091817816202503652137560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1382_800 : bothSeg evalE (oGrid.idx 1382) (oGrid.dm 1382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1382) oGrid.kl oGrid.kr 400 800 ⟨false, 38408299063109139569464687460743917832185285008153091817816202503652137560⟩ ⟨false, 0⟩ ⟨false, 99111698832944047780166646130049215965924775771305856263462577579013010758⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1382_1200 : bothSeg evalE (oGrid.idx 1382) (oGrid.dm 1382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1382) oGrid.kl oGrid.kr 400 1200 ⟨false, 99111698832944047780166646130049215965924775771305856263462577579013010758⟩ ⟨false, 0⟩ ⟨false, 171405965989631154236250042040222572446906693978230497334316315833832287818⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1382_1600 : bothSeg evalE (oGrid.idx 1382) (oGrid.dm 1382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1382) oGrid.kl oGrid.kr 400 1600 ⟨false, 171405965989631154236250042040222572446906693978230497334316315833832287818⟩ ⟨false, 0⟩ ⟨false, 299212150298610784183468878939301839338338685928647494404592095058031444916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1382_2000 : bothSeg evalE (oGrid.idx 1382) (oGrid.dm 1382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1382) oGrid.kl oGrid.kr 400 2000 ⟨false, 299212150298610784183468878939301839338338685928647494404592095058031444916⟩ ⟨false, 0⟩ ⟨false, 479865256353384662320421082617842710448522296032788829000115280894903626302⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1382_2400 : bothLoop evalE (oGrid.idx 1382) (oGrid.dm 1382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1382) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 479865256353384662320421082617842710448522296032788829000115280894903626302⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1382 : oGrid.row evalE 1382 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1382_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1382_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1382_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1382_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1382_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1382_2000).1 (bothLoop_sound b_1382_2400).1))))))

theorem n_row_1382 : nGrid.row evalE 1382 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1382_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1382_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1382_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1382_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1382_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1382_2000).2 (bothLoop_sound b_1382_2400).2))))))

theorem b_1383_0 : bothSeg evalE (oGrid.idx 1383) (oGrid.dm 1383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1383) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 8734215076519165670587933517365137191152561616901594457479074256670283750⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1383_400 : bothSeg evalE (oGrid.idx 1383) (oGrid.dm 1383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1383) oGrid.kl oGrid.kr 400 400 ⟨false, 8734215076519165670587933517365137191152561616901594457479074256670283750⟩ ⟨false, 0⟩ ⟨false, 39218684583391333314705550382007026220343286933746699267510146253862173906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1383_800 : bothSeg evalE (oGrid.idx 1383) (oGrid.dm 1383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1383) oGrid.kl oGrid.kr 400 800 ⟨false, 39218684583391333314705550382007026220343286933746699267510146253862173906⟩ ⟨false, 0⟩ ⟨false, 99998257161542783704306925410021108769367677789863497073256420574041681866⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1383_1200 : bothSeg evalE (oGrid.idx 1383) (oGrid.dm 1383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1383) oGrid.kl oGrid.kr 400 1200 ⟨false, 99998257161542783704306925410021108769367677789863497073256420574041681866⟩ ⟨false, 0⟩ ⟨false, 172591090091974866522110030848927599372666112252361732757846425138855482652⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1383_1600 : bothSeg evalE (oGrid.idx 1383) (oGrid.dm 1383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1383) oGrid.kl oGrid.kr 400 1600 ⟨false, 172591090091974866522110030848927599372666112252361732757846425138855482652⟩ ⟨false, 0⟩ ⟨false, 300663453674790162430190550545516960588565792922795149602422043762209273346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1383_2000 : bothSeg evalE (oGrid.idx 1383) (oGrid.dm 1383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1383) oGrid.kl oGrid.kr 400 2000 ⟨false, 300663453674790162430190550545516960588565792922795149602422043762209273346⟩ ⟨false, 0⟩ ⟨false, 481549938323700412619761906190211001319728220626644445604470343111315783420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1383_2400 : bothLoop evalE (oGrid.idx 1383) (oGrid.dm 1383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1383) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 481549938323700412619761906190211001319728220626644445604470343111315783420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1383 : oGrid.row evalE 1383 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1383_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1383_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1383_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1383_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1383_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1383_2000).1 (bothLoop_sound b_1383_2400).1))))))

theorem n_row_1383 : nGrid.row evalE 1383 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1383_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1383_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1383_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1383_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1383_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1383_2000).2 (bothLoop_sound b_1383_2400).2))))))

theorem b_1384_0 : bothSeg evalE (oGrid.idx 1384) (oGrid.dm 1384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1384) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 9136926671658704249674096454074340023839869557143105339187511745029332822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1384_400 : bothSeg evalE (oGrid.idx 1384) (oGrid.dm 1384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1384) oGrid.kl oGrid.kr 400 400 ⟨false, 9136926671658704249674096454074340023839869557143105339187511745029332822⟩ ⟨false, 0⟩ ⟨false, 40030791613768069932881724928946270476822389496050157554238714016626326518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1384_800 : bothSeg evalE (oGrid.idx 1384) (oGrid.dm 1384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1384) oGrid.kl oGrid.kr 400 800 ⟨false, 40030791613768069932881724928946270476822389496050157554238714016626326518⟩ ⟨false, 0⟩ ⟨false, 100883290873252893853616020143155752405270469753912585286696611022849208652⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1384_1200 : bothSeg evalE (oGrid.idx 1384) (oGrid.dm 1384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1384) oGrid.kl oGrid.kr 400 1200 ⟨false, 100883290873252893853616020143155752405270469753912585286696611022849208652⟩ ⟨false, 0⟩ ⟨false, 173775586785618944069446730303631711025738695378244534423583273498659713774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1384_1600 : bothSeg evalE (oGrid.idx 1384) (oGrid.dm 1384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1384) oGrid.kl oGrid.kr 400 1600 ⟨false, 173775586785618944069446730303631711025738695378244534423583273498659713774⟩ ⟨false, 0⟩ ⟨false, 302114150385334613275412489549944674142986581887595325542181224516048147720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1384_2000 : bothSeg evalE (oGrid.idx 1384) (oGrid.dm 1384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1384) oGrid.kl oGrid.kr 400 2000 ⟨false, 302114150385334613275412489549944674142986581887595325542181224516048147720⟩ ⟨false, 0⟩ ⟨false, 483234052754133425633750450018199382845907897906149732424078253975789598344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1384_2400 : bothLoop evalE (oGrid.idx 1384) (oGrid.dm 1384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1384) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 483234052754133425633750450018199382845907897906149732424078253975789598344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1384 : oGrid.row evalE 1384 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1384_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1384_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1384_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1384_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1384_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1384_2000).1 (bothLoop_sound b_1384_2400).1))))))

theorem n_row_1384 : nGrid.row evalE 1384 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1384_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1384_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1384_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1384_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1384_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1384_2000).2 (bothLoop_sound b_1384_2400).2))))))

theorem b_1385_0 : bothSeg evalE (oGrid.idx 1385) (oGrid.dm 1385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1385) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 9539755990462226625389423966020665209972343843960433277423224234376064362⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1385_400 : bothSeg evalE (oGrid.idx 1385) (oGrid.dm 1385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1385) oGrid.kl oGrid.kr 400 400 ⟨false, 9539755990462226625389423966020665209972343843960433277423224234376064362⟩ ⟨false, 0⟩ ⟨false, 40844693400830132123173104677218874198140809257781702360822521337417000936⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1385_800 : bothSeg evalE (oGrid.idx 1385) (oGrid.dm 1385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1385) oGrid.kl oGrid.kr 400 800 ⟨false, 40844693400830132123173104677218874198140809257781702360822521337417000936⟩ ⟨false, 0⟩ ⟨false, 101766860529031762694052402493840791028762027906788332031045636641916562736⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1385_1200 : bothSeg evalE (oGrid.idx 1385) (oGrid.dm 1385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1385) oGrid.kl oGrid.kr 400 1200 ⟨false, 101766860529031762694052402493840791028762027906788332031045636641916562736⟩ ⟨false, 0⟩ ⟨false, 174959445594990378459468980969153542665049746196898496142457757526195996170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1385_1600 : bothSeg evalE (oGrid.idx 1385) (oGrid.dm 1385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1385) oGrid.kl oGrid.kr 400 1600 ⟨false, 174959445594990378459468980969153542665049746196898496142457757526195996170⟩ ⟨false, 0⟩ ⟨false, 303564229882961025030337500591509636974374689882237483232292846478115097010⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1385_2000 : bothSeg evalE (oGrid.idx 1385) (oGrid.dm 1385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1385) oGrid.kl oGrid.kr 400 2000 ⟨false, 303564229882961025030337500591509636974374689882237483232292846478115097010⟩ ⟨false, 0⟩ ⟨false, 484917589027445166993387337394741566937903313184390234426675435431483348654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1385_2400 : bothLoop evalE (oGrid.idx 1385) (oGrid.dm 1385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1385) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 484917589027445166993387337394741566937903313184390234426675435431483348654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1385 : oGrid.row evalE 1385 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1385_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1385_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1385_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1385_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1385_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1385_2000).1 (bothLoop_sound b_1385_2400).1))))))

theorem n_row_1385 : nGrid.row evalE 1385 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1385_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1385_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1385_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1385_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1385_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1385_2000).2 (bothLoop_sound b_1385_2400).2))))))

theorem b_1386_0 : bothSeg evalE (oGrid.idx 1386) (oGrid.dm 1386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1386) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 9942751711530181272803416077158776272361735455447336710696479558684180154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1386_400 : bothSeg evalE (oGrid.idx 1386) (oGrid.dm 1386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1386) oGrid.kl oGrid.kr 400 400 ⟨false, 9942751711530181272803416077158776272361735455447336710696479558684180154⟩ ⟨false, 0⟩ ⟨false, 41660464037449742451111151085296530312067170479795787223249047807482507612⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1386_800 : bothSeg evalE (oGrid.idx 1386) (oGrid.dm 1386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1386) oGrid.kl oGrid.kr 400 800 ⟨false, 41660464037449742451111151085296530312067170479795787223249047807482507612⟩ ⟨false, 0⟩ ⟨false, 102649081473209087417900618465272083078086774459288572268096075807546839152⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1386_1200 : bothSeg evalE (oGrid.idx 1386) (oGrid.dm 1386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1386) oGrid.kl oGrid.kr 400 1200 ⟨false, 102649081473209087417900618465272083078086774459288572268096075807546839152⟩ ⟨false, 0⟩ ⟨false, 176142716991598187949012453568076751138749235927239764611145748994534359838⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1386_1600 : bothSeg evalE (oGrid.idx 1386) (oGrid.dm 1386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1386) oGrid.kl oGrid.kr 400 1600 ⟨false, 176142716991598187949012453568076751138749235927239764611145748994534359838⟩ ⟨false, 0⟩ ⟨false, 305013742567597738540288968219038853093085415200217618719720545724934957772⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1386_2000 : bothSeg evalE (oGrid.idx 1386) (oGrid.dm 1386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1386) oGrid.kl oGrid.kr 400 2000 ⟨false, 305013742567597738540288968219038853093085415200217618719720545724934957772⟩ ⟨false, 0⟩ ⟨false, 486600597473697055347284344905456124337301558141303475508921748642284600592⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1386_2400 : bothLoop evalE (oGrid.idx 1386) (oGrid.dm 1386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1386) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 486600597473697055347284344905456124337301558141303475508921748642284600592⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1386 : oGrid.row evalE 1386 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1386_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1386_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1386_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1386_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1386_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1386_2000).1 (bothLoop_sound b_1386_2400).1))))))

theorem n_row_1386 : nGrid.row evalE 1386 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1386_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1386_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1386_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1386_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1386_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1386_2000).2 (bothLoop_sound b_1386_2400).2))))))

theorem b_1387_0 : bothSeg evalE (oGrid.idx 1387) (oGrid.dm 1387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1387) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 10345945951087065382760328933094876059973067881045301152647072089530786822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1387_400 : bothSeg evalE (oGrid.idx 1387) (oGrid.dm 1387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1387) oGrid.kl oGrid.kr 400 400 ⟨false, 10345945951087065382760328933094876059973067881045301152647072089530786822⟩ ⟨false, 0⟩ ⟨false, 42478176890664714210216472655076798052040611675168923040742883514507960558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1387_800 : bothSeg evalE (oGrid.idx 1387) (oGrid.dm 1387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1387) oGrid.kl oGrid.kr 400 800 ⟨false, 42478176890664714210216472655076798052040611675168923040742883514507960558⟩ ⟨false, 0⟩ ⟨false, 103530054994722800481738405504956416332473382076532624552145562982704422202⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1387_1200 : bothSeg evalE (oGrid.idx 1387) (oGrid.dm 1387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1387) oGrid.kl oGrid.kr 400 1200 ⟨false, 103530054994722800481738405504956416332473382076532624552145562982704422202⟩ ⟨false, 0⟩ ⟨false, 177325441039208657919410072439733480141916163484955636031816600489657562824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1387_1600 : bothSeg evalE (oGrid.idx 1387) (oGrid.dm 1387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1387) oGrid.kl oGrid.kr 400 1600 ⟨false, 177325441039208657919410072439733480141916163484955636031816600489657562824⟩ ⟨false, 0⟩ ⟨false, 306462728431559588702985215648255673639381801322985183919948294921095145544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1387_2000 : bothSeg evalE (oGrid.idx 1387) (oGrid.dm 1387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1387) oGrid.kl oGrid.kr 400 2000 ⟨false, 306462728431559588702985215648255673639381801322985183919948294921095145544⟩ ⟨false, 0⟩ ⟨false, 488283118015425424707527096610753285771961533177411761326293829336499799868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1387_2400 : bothLoop evalE (oGrid.idx 1387) (oGrid.dm 1387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1387) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 488283118015425424707527096610753285771961533177411761326293829336499799868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1387 : oGrid.row evalE 1387 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1387_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1387_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1387_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1387_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1387_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1387_2000).1 (bothLoop_sound b_1387_2400).1))))))

theorem n_row_1387 : nGrid.row evalE 1387 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1387_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1387_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1387_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1387_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1387_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1387_2000).2 (bothLoop_sound b_1387_2400).2))))))

theorem b_1388_0 : bothSeg evalE (oGrid.idx 1388) (oGrid.dm 1388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1388) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 10749380989308906873745831210690348764946546023491026177057548508128062882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1388_400 : bothSeg evalE (oGrid.idx 1388) (oGrid.dm 1388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1388) oGrid.kl oGrid.kr 400 400 ⟨false, 10749380989308906873745831210690348764946546023491026177057548508128062882⟩ ⟨false, 0⟩ ⟨false, 43297901267069959556082951152754812096964160187671990478478115305255603610⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1388_800 : bothSeg evalE (oGrid.idx 1388) (oGrid.dm 1388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1388) oGrid.kl oGrid.kr 400 800 ⟨false, 43297901267069959556082951152754812096964160187671990478478115305255603610⟩ ⟨false, 0⟩ ⟨false, 104409838915958425297243935695487495339900544070754773314992663209947421498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1388_1200 : bothSeg evalE (oGrid.idx 1388) (oGrid.dm 1388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1388) oGrid.kl oGrid.kr 400 1200 ⟨false, 104409838915958425297243935695487495339900544070754773314992663209947421498⟩ ⟨false, 0⟩ ⟨false, 178507613006095450168238513823769657179761973748718182513848227583123553518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1388_1600 : bothSeg evalE (oGrid.idx 1388) (oGrid.dm 1388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1388) oGrid.kl oGrid.kr 400 1600 ⟨false, 178507613006095450168238513823769657179761973748718182513848227583123553518⟩ ⟨false, 0⟩ ⟨false, 307911182671797815065151841429600583964964196756146825246393964662995882646⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1388_2000 : bothSeg evalE (oGrid.idx 1388) (oGrid.dm 1388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1388) oGrid.kl oGrid.kr 400 2000 ⟨false, 307911182671797815065151841429600583964964196756146825246393964662995882646⟩ ⟨false, 0⟩ ⟨false, 489965145779891355852163956266780872107872506445677889354373239944432456638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1388_2400 : bothLoop evalE (oGrid.idx 1388) (oGrid.dm 1388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1388) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 489965145779891355852163956266780872107872506445677889354373239944432456638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1388 : oGrid.row evalE 1388 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1388_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1388_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1388_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1388_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1388_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1388_2000).1 (bothLoop_sound b_1388_2400).1))))))

theorem n_row_1388 : nGrid.row evalE 1388 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1388_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1388_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1388_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1388_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1388_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1388_2000).2 (bothLoop_sound b_1388_2400).2))))))

theorem b_1389_0 : bothSeg evalE (oGrid.idx 1389) (oGrid.dm 1389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1389) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 11153087727233298161419459557068705723418241325276135533087378538830724990⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1389_400 : bothSeg evalE (oGrid.idx 1389) (oGrid.dm 1389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1389) oGrid.kl oGrid.kr 400 400 ⟨false, 11153087727233298161419459557068705723418241325276135533087378538830724990⟩ ⟨false, 0⟩ ⟨false, 44119695166523120456340015192311346250080058238076239706650032787562529402⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1389_800 : bothSeg evalE (oGrid.idx 1389) (oGrid.dm 1389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1389) oGrid.kl oGrid.kr 400 800 ⟨false, 44119695166523120456340015192311346250080058238076239706650032787562529402⟩ ⟨false, 0⟩ ⟨false, 105288559492321050821940424435739555325518885149015363766194920758621730424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1389_1200 : bothSeg evalE (oGrid.idx 1389) (oGrid.dm 1389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1389) oGrid.kl oGrid.kr 400 1200 ⟨false, 105288559492321050821940424435739555325518885149015363766194920758621730424⟩ ⟨false, 0⟩ ⟨false, 179689301682919071911994083592787165997035516195720973081884794765745289680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1389_1600 : bothSeg evalE (oGrid.idx 1389) (oGrid.dm 1389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1389) oGrid.kl oGrid.kr 400 1600 ⟨false, 179689301682919071911994083592787165997035516195720973081884794765745289680⟩ ⟨false, 0⟩ ⟨false, 309359174007779332365517958261240494561379792924857921363850245074948988976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1389_2000 : bothSeg evalE (oGrid.idx 1389) (oGrid.dm 1389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1389) oGrid.kl oGrid.kr 400 2000 ⟨false, 309359174007779332365517958261240494561379792924857921363850245074948988976⟩ ⟨false, 0⟩ ⟨false, 491646749416959867652747146796738269852818845171457817166523606552952641364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1389_2400 : bothLoop evalE (oGrid.idx 1389) (oGrid.dm 1389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1389) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 491646749416959867652747146796738269852818845171457817166523606552952641364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1389 : oGrid.row evalE 1389 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1389_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1389_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1389_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1389_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1389_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1389_2000).1 (bothLoop_sound b_1389_2400).1))))))

theorem n_row_1389 : nGrid.row evalE 1389 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1389_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1389_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1389_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1389_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1389_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1389_2000).2 (bothLoop_sound b_1389_2400).2))))))

theorem b_1390_0 : bothSeg evalE (oGrid.idx 1390) (oGrid.dm 1390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1390) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 11557099618841913793247340305922489400099892676695790414414466829591648926⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1390_400 : bothSeg evalE (oGrid.idx 1390) (oGrid.dm 1390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1390) oGrid.kl oGrid.kr 400 400 ⟨false, 11557099618841913793247340305922489400099892676695790414414466829591648926⟩ ⟨false, 0⟩ ⟨false, 44943616240933105468768812628885301096481440929905003021567185243873676604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1390_800 : bothSeg evalE (oGrid.idx 1390) (oGrid.dm 1390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1390) oGrid.kl oGrid.kr 400 800 ⟨false, 44943616240933105468768812628885301096481440929905003021567185243873676604⟩ ⟨false, 0⟩ ⟨false, 106166237233350209031999278174844803117842045714639132773750250885585146068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1390_1200 : bothSeg evalE (oGrid.idx 1390) (oGrid.dm 1390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1390) oGrid.kl oGrid.kr 400 1200 ⟨false, 106166237233350209031999278174844803117842045714639132773750250885585146068⟩ ⟨false, 0⟩ ⟨false, 180870473351272879758505064875417506353720834733534556263741130289608198562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1390_1600 : bothSeg evalE (oGrid.idx 1390) (oGrid.dm 1390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1390) oGrid.kl oGrid.kr 400 1600 ⟨false, 180870473351272879758505064875417506353720834733534556263741130289608198562⟩ ⟨false, 0⟩ ⟨false, 310806668650032536282994673931664565695494869236425823995815247347370832522⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1390_2000 : bothSeg evalE (oGrid.idx 1390) (oGrid.dm 1390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1390) oGrid.kl oGrid.kr 400 2000 ⟨false, 310806668650032536282994673931664565695494869236425823995815247347370832522⟩ ⟨false, 0⟩ ⟨false, 493327895067645643586103215134287138531625170277589144267345708951821311138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1390_2400 : bothLoop evalE (oGrid.idx 1390) (oGrid.dm 1390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1390) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 493327895067645643586103215134287138531625170277589144267345708951821311138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1390 : oGrid.row evalE 1390 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1390_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1390_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1390_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1390_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1390_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1390_2000).1 (bothLoop_sound b_1390_2400).1))))))

theorem n_row_1390 : nGrid.row evalE 1390 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1390_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1390_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1390_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1390_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1390_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1390_2000).2 (bothLoop_sound b_1390_2400).2))))))

theorem b_1391_0 : bothSeg evalE (oGrid.idx 1391) (oGrid.dm 1391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1391) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 11961446895645326908205504034620748063465277477411064492985466331807048654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1391_400 : bothSeg evalE (oGrid.idx 1391) (oGrid.dm 1391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1391) oGrid.kl oGrid.kr 400 400 ⟨false, 11961446895645326908205504034620748063465277477411064492985466331807048654⟩ ⟨false, 0⟩ ⟨false, 45769718760651126772704520099086484738068525572349097259692136858617369178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1391_800 : bothSeg evalE (oGrid.idx 1391) (oGrid.dm 1391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1391) oGrid.kl oGrid.kr 400 800 ⟨false, 45769718760651126772704520099086484738068525572349097259692136858617369178⟩ ⟨false, 0⟩ ⟨false, 107042999159129437582773082069627739685783422385482343201373077535298568158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1391_1200 : bothSeg evalE (oGrid.idx 1391) (oGrid.dm 1391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1391) oGrid.kl oGrid.kr 400 1200 ⟨false, 107042999159129437582773082069627739685783422385482343201373077535298568158⟩ ⟨false, 0⟩ ⟨false, 182051204456764131460116961653187603796150278482049170114329196056240557948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1391_1600 : bothSeg evalE (oGrid.idx 1391) (oGrid.dm 1391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1391) oGrid.kl oGrid.kr 400 1600 ⟨false, 182051204456764131460116961653187603796150278482049170114329196056240557948⟩ ⟨false, 0⟩ ⟨false, 312253742973228157201062126722465733066273513359194747501684368538957417870⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1391_2000 : bothSeg evalE (oGrid.idx 1391) (oGrid.dm 1391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1391) oGrid.kl oGrid.kr 400 2000 ⟨false, 312253742973228157201062126722465733066273513359194747501684368538957417870⟩ ⟨false, 0⟩ ⟨false, 495008659037193806241736609191162395365353329608245136171164162235246909648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1391_2400 : bothLoop evalE (oGrid.idx 1391) (oGrid.dm 1391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1391) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 495008659037193806241736609191162395365353329608245136171164162235246909648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1391 : oGrid.row evalE 1391 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1391_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1391_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1391_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1391_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1391_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1391_2000).1 (bothLoop_sound b_1391_2400).1))))))

theorem n_row_1391 : nGrid.row evalE 1391 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1391_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1391_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1391_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1391_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1391_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1391_2000).2 (bothLoop_sound b_1391_2400).2))))))

theorem o_blk_1368 : allFrom (fun j => oGrid.row evalE j) 1368 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1368) o_row_1368 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1369) o_row_1369 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1370) o_row_1370 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1371) o_row_1371 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1372) o_row_1372 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1373) o_row_1373 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1374) o_row_1374 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1375) o_row_1375 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1376) o_row_1376 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1377) o_row_1377 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1378) o_row_1378 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1379) o_row_1379 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1380) o_row_1380 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1381) o_row_1381 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1382) o_row_1382 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1383) o_row_1383 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1384) o_row_1384 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1385) o_row_1385 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1386) o_row_1386 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1387) o_row_1387 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1388) o_row_1388 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1389) o_row_1389 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1390) o_row_1390 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1391) o_row_1391 (allFrom_zero (fun j => oGrid.row evalE j) 1392)))))))))))))))))))))))))

theorem n_blk_1368 : allFrom (fun j => nGrid.row evalE j) 1368 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1368) n_row_1368 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1369) n_row_1369 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1370) n_row_1370 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1371) n_row_1371 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1372) n_row_1372 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1373) n_row_1373 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1374) n_row_1374 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1375) n_row_1375 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1376) n_row_1376 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1377) n_row_1377 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1378) n_row_1378 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1379) n_row_1379 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1380) n_row_1380 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1381) n_row_1381 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1382) n_row_1382 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1383) n_row_1383 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1384) n_row_1384 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1385) n_row_1385 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1386) n_row_1386 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1387) n_row_1387 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1388) n_row_1388 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1389) n_row_1389 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1390) n_row_1390 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1391) n_row_1391 (allFrom_zero (fun j => nGrid.row evalE j) 1392)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
