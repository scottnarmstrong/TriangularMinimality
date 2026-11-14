/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 62 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1488`–`1511`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1488_0 : bothSeg evalE (oGrid.idx 1488) (oGrid.dm 1488) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1488) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 54831725022711848875117189110306620188726807651453305237564873121953553048⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1488_400 : bothSeg evalE (oGrid.idx 1488) (oGrid.dm 1488) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1488) oGrid.kl oGrid.kr 400 400 ⟨false, 54831725022711848875117189110306620188726807651453305237564873121953553048⟩ ⟨false, 0⟩ ⟨false, 126006892842591207150692764572770105663939700746479378546039615248626722822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1488_800 : bothSeg evalE (oGrid.idx 1488) (oGrid.dm 1488) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1488) oGrid.kl oGrid.kr 400 800 ⟨false, 126006892842591207150692764572770105663939700746479378546039615248626722822⟩ ⟨false, 0⟩ ⟨false, 187776342425672825221288222834083539269753044087780108032581948976032070584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1488_1200 : bothSeg evalE (oGrid.idx 1488) (oGrid.dm 1488) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1488) oGrid.kl oGrid.kr 400 1200 ⟨false, 187776342425672825221288222834083539269753044087780108032581948976032070584⟩ ⟨false, 0⟩ ⟨false, 292581426153173481681531851840565844384466482072801099508711092373019124240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1488_1600 : bothSeg evalE (oGrid.idx 1488) (oGrid.dm 1488) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1488) oGrid.kl oGrid.kr 400 1600 ⟨false, 292581426153173481681531851840565844384466482072801099508711092373019124240⟩ ⟨false, 0⟩ ⟨false, 448704837519553324449010835423737162235314387551958960282808772111475670878⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1488_2000 : bothSeg evalE (oGrid.idx 1488) (oGrid.dm 1488) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1488) oGrid.kl oGrid.kr 400 2000 ⟨false, 448704837519553324449010835423737162235314387551958960282808772111475670878⟩ ⟨false, 0⟩ ⟨false, 654300745154977393750638769674090711253194219420340421739122385199170468584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1488_2400 : bothLoop evalE (oGrid.idx 1488) (oGrid.dm 1488) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1488) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 654300745154977393750638769674090711253194219420340421739122385199170468584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1488 : oGrid.row evalE 1488 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1488_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1488_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1488_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1488_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1488_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1488_2000).1 (bothLoop_sound b_1488_2400).1))))))

theorem n_row_1488 : nGrid.row evalE 1488 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1488_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1488_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1488_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1488_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1488_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1488_2000).2 (bothLoop_sound b_1488_2400).2))))))

theorem b_1489_0 : bothSeg evalE (oGrid.idx 1489) (oGrid.dm 1489) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1489) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 55341391228432451327397702422067268156689388441652582466417450337959514472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1489_400 : bothSeg evalE (oGrid.idx 1489) (oGrid.dm 1489) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1489) oGrid.kl oGrid.kr 400 400 ⟨false, 55341391228432451327397702422067268156689388441652582466417450337959514472⟩ ⟨false, 0⟩ ⟨false, 126611653339025644183118873330249949597034683187441295183547013487081471046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1489_800 : bothSeg evalE (oGrid.idx 1489) (oGrid.dm 1489) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1489) oGrid.kl oGrid.kr 400 800 ⟨false, 126611653339025644183118873330249949597034683187441295183547013487081471046⟩ ⟨false, 0⟩ ⟨false, 188518817483711345656392428290590326738170221195823619519873273345641529720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1489_1200 : bothSeg evalE (oGrid.idx 1489) (oGrid.dm 1489) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1489) oGrid.kl oGrid.kr 400 1200 ⟨false, 188518817483711345656392428290590326738170221195823619519873273345641529720⟩ ⟨false, 0⟩ ⟨false, 293630784231172971707460639400777945565165626217363444572727274536370357530⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1489_1600 : bothSeg evalE (oGrid.idx 1489) (oGrid.dm 1489) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1489) oGrid.kl oGrid.kr 400 1600 ⟨false, 293630784231172971707460639400777945565165626217363444572727274536370357530⟩ ⟨false, 0⟩ ⟨false, 450022198573951750922929148517176250484409253009666787206539888034685960992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1489_2000 : bothSeg evalE (oGrid.idx 1489) (oGrid.dm 1489) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1489) oGrid.kl oGrid.kr 400 2000 ⟨false, 450022198573951750922929148517176250484409253009666787206539888034685960992⟩ ⟨false, 0⟩ ⟨false, 655855259509943132893869922800922749427880425360601884094494554165080346796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1489_2400 : bothLoop evalE (oGrid.idx 1489) (oGrid.dm 1489) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1489) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 655855259509943132893869922800922749427880425360601884094494554165080346796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1489 : oGrid.row evalE 1489 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1489_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1489_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1489_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1489_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1489_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1489_2000).1 (bothLoop_sound b_1489_2400).1))))))

theorem n_row_1489 : nGrid.row evalE 1489 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1489_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1489_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1489_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1489_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1489_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1489_2000).2 (bothLoop_sound b_1489_2400).2))))))

theorem b_1490_0 : bothSeg evalE (oGrid.idx 1490) (oGrid.dm 1490) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1490) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 55851978255425515622617048758494620008815610415935872392605558577028520652⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1490_400 : bothSeg evalE (oGrid.idx 1490) (oGrid.dm 1490) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1490) oGrid.kl oGrid.kr 400 400 ⟨false, 55851978255425515622617048758494620008815610415935872392605558577028520652⟩ ⟨false, 0⟩ ⟨false, 127206724868296698891391151218555620970047675945388516921247140187640470918⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1490_800 : bothSeg evalE (oGrid.idx 1490) (oGrid.dm 1490) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1490) oGrid.kl oGrid.kr 400 800 ⟨false, 127206724868296698891391151218555620970047675945388516921247140187640470918⟩ ⟨false, 0⟩ ⟨false, 189257183392241943714627662544813717607537677102736459411958784285091360830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1490_1200 : bothSeg evalE (oGrid.idx 1490) (oGrid.dm 1490) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1490) oGrid.kl oGrid.kr 400 1200 ⟨false, 189257183392241943714627662544813717607537677102736459411958784285091360830⟩ ⟨false, 0⟩ ⟨false, 294676013276513289278908190046099906183349315123152119032011737473864755660⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1490_1600 : bothSeg evalE (oGrid.idx 1490) (oGrid.dm 1490) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1490) oGrid.kl oGrid.kr 400 1600 ⟨false, 294676013276513289278908190046099906183349315123152119032011737473864755660⟩ ⟨false, 0⟩ ⟨false, 451335444420528752224163808149405927543381396181934884719853244245337786954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1490_2000 : bothSeg evalE (oGrid.idx 1490) (oGrid.dm 1490) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1490) oGrid.kl oGrid.kr 400 2000 ⟨false, 451335444420528752224163808149405927543381396181934884719853244245337786954⟩ ⟨false, 0⟩ ⟨false, 657405690844724556123332553531446847048532037924865555295618365154142249556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1490_2400 : bothLoop evalE (oGrid.idx 1490) (oGrid.dm 1490) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1490) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 657405690844724556123332553531446847048532037924865555295618365154142249556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1490 : oGrid.row evalE 1490 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1490_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1490_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1490_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1490_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1490_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1490_2000).1 (bothLoop_sound b_1490_2400).1))))))

theorem n_row_1490 : nGrid.row evalE 1490 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1490_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1490_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1490_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1490_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1490_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1490_2000).2 (bothLoop_sound b_1490_2400).2))))))

theorem b_1491_0 : bothSeg evalE (oGrid.idx 1491) (oGrid.dm 1491) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1491) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 56363336509424727183769189218950241107482980551488183418766586445225455524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1491_400 : bothSeg evalE (oGrid.idx 1491) (oGrid.dm 1491) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1491) oGrid.kl oGrid.kr 400 400 ⟨false, 56363336509424727183769189218950241107482980551488183418766586445225455524⟩ ⟨false, 0⟩ ⟨false, 127791985377375244550490228621048934154085598539570943651889437408768152074⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1491_800 : bothSeg evalE (oGrid.idx 1491) (oGrid.dm 1491) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1491) oGrid.kl oGrid.kr 400 800 ⟨false, 127791985377375244550490228621048934154085598539570943651889437408768152074⟩ ⟨false, 0⟩ ⟨false, 189991301120394892530913919498916231455556645430261459344387344499935269332⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1491_1200 : bothSeg evalE (oGrid.idx 1491) (oGrid.dm 1491) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1491) oGrid.kl oGrid.kr 400 1200 ⟨false, 189991301120394892530913919498916231455556645430261459344387344499935269332⟩ ⟨false, 0⟩ ⟨false, 295716974226047929098090370342539237308426096781561159067345397262797990584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1491_1600 : bothSeg evalE (oGrid.idx 1491) (oGrid.dm 1491) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1491) oGrid.kl oGrid.kr 400 1600 ⟨false, 295716974226047929098090370342539237308426096781561159067345397262797990584⟩ ⟨false, 0⟩ ⟨false, 452644435937085072810781716958694002028679279591651287287863778233074498452⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1491_2000 : bothSeg evalE (oGrid.idx 1491) (oGrid.dm 1491) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1491) oGrid.kl oGrid.kr 400 2000 ⟨false, 452644435937085072810781716958694002028679279591651287287863778233074498452⟩ ⟨false, 0⟩ ⟨false, 658951899976105012374177056508045953088293735298151427189454044480091631510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1491_2400 : bothLoop evalE (oGrid.idx 1491) (oGrid.dm 1491) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1491) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 658951899976105012374177056508045953088293735298151427189454044480091631510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1491 : oGrid.row evalE 1491 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1491_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1491_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1491_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1491_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1491_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1491_2000).1 (bothLoop_sound b_1491_2400).1))))))

theorem n_row_1491 : nGrid.row evalE 1491 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1491_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1491_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1491_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1491_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1491_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1491_2000).2 (bothLoop_sound b_1491_2400).2))))))

theorem b_1492_0 : bothSeg evalE (oGrid.idx 1492) (oGrid.dm 1492) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1492) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 56875299608009080124101972636656285755901426766772098238402074213555554390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1492_400 : bothSeg evalE (oGrid.idx 1492) (oGrid.dm 1492) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1492) oGrid.kl oGrid.kr 400 400 ⟨false, 56875299608009080124101972636656285755901426766772098238402074213555554390⟩ ⟨false, 0⟩ ⟨false, 128367287700040513525208665580368630504840445967975528344375002996566969414⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1492_800 : bothSeg evalE (oGrid.idx 1492) (oGrid.dm 1492) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1492) oGrid.kl oGrid.kr 400 800 ⟨false, 128367287700040513525208665580368630504840445967975528344375002996566969414⟩ ⟨false, 0⟩ ⟨false, 190721003754307035995951433309458106278263156432281397752619576343582574148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1492_1200 : bothSeg evalE (oGrid.idx 1492) (oGrid.dm 1492) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1492) oGrid.kl oGrid.kr 400 1200 ⟨false, 190721003754307035995951433309458106278263156432281397752619576343582574148⟩ ⟨false, 0⟩ ⟨false, 296753500133742162625888579428871483132494983765690974933030634501888306454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1492_1600 : bothSeg evalE (oGrid.idx 1492) (oGrid.dm 1492) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1492) oGrid.kl oGrid.kr 400 1600 ⟨false, 296753500133742162625888579428871483132494983765690974933030634501888306454⟩ ⟨false, 0⟩ ⟨false, 453949006118642875877524941757467364117586614130346576402780311372704705540⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1492_2000 : bothSeg evalE (oGrid.idx 1492) (oGrid.dm 1492) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1492) oGrid.kl oGrid.kr 400 2000 ⟨false, 453949006118642875877524941757467364117586614130346576402780311372704705540⟩ ⟨false, 0⟩ ⟨false, 660493719838169323748454253386992133398930279713857148000279175415822242830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1492_2400 : bothLoop evalE (oGrid.idx 1492) (oGrid.dm 1492) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1492) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 660493719838169323748454253386992133398930279713857148000279175415822242830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1492 : oGrid.row evalE 1492 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1492_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1492_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1492_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1492_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1492_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1492_2000).1 (bothLoop_sound b_1492_2400).1))))))

theorem n_row_1492 : nGrid.row evalE 1492 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1492_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1492_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1492_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1492_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1492_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1492_2000).2 (bothLoop_sound b_1492_2400).2))))))

theorem b_1493_0 : bothSeg evalE (oGrid.idx 1493) (oGrid.dm 1493) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1493) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 57387695320244783400318386279506046246669911392700530649118715638994004160⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1493_400 : bothSeg evalE (oGrid.idx 1493) (oGrid.dm 1493) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1493) oGrid.kl oGrid.kr 400 400 ⟨false, 57387695320244783400318386279506046246669911392700530649118715638994004160⟩ ⟨false, 0⟩ ⟨false, 128932473619693437177725319291850911554153336635389485515591609350755931436⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1493_800 : bothSeg evalE (oGrid.idx 1493) (oGrid.dm 1493) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1493) oGrid.kl oGrid.kr 400 800 ⟨false, 128932473619693437177725319291850911554153336635389485515591609350755931436⟩ ⟨false, 0⟩ ⟨false, 191446105788669423498939424186450872905400602327194926359472900948384999996⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1493_1200 : bothSeg evalE (oGrid.idx 1493) (oGrid.dm 1493) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1493) oGrid.kl oGrid.kr 400 1200 ⟨false, 191446105788669423498939424186450872905400602327194926359472900948384999996⟩ ⟨false, 0⟩ ⟨false, 297785405462220428548122388727851599478925923730600144656572765652789253528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1493_1600 : bothSeg evalE (oGrid.idx 1493) (oGrid.dm 1493) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1493) oGrid.kl oGrid.kr 400 1600 ⟨false, 297785405462220428548122388727851599478925923730600144656572765652789253528⟩ ⟨false, 0⟩ ⟨false, 455248969368992959576394424692535154306149431250292867244602832619398817306⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1493_2000 : bothSeg evalE (oGrid.idx 1493) (oGrid.dm 1493) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1493) oGrid.kl oGrid.kr 400 2000 ⟨false, 455248969368992959576394424692535154306149431250292867244602832619398817306⟩ ⟨false, 0⟩ ⟨false, 662030964773850922136268458533961087822656007196570372335456239431793343198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1493_2400 : bothLoop evalE (oGrid.idx 1493) (oGrid.dm 1493) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1493) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 662030964773850922136268458533961087822656007196570372335456239431793343198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1493 : oGrid.row evalE 1493 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1493_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1493_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1493_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1493_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1493_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1493_2000).1 (bothLoop_sound b_1493_2400).1))))))

theorem n_row_1493 : nGrid.row evalE 1493 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1493_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1493_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1493_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1493_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1493_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1493_2000).2 (bothLoop_sound b_1493_2400).2))))))

theorem b_1494_0 : bothSeg evalE (oGrid.idx 1494) (oGrid.dm 1494) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1494) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 57900333926696780224396865739252739358472255834344289915223184815346939702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1494_400 : bothSeg evalE (oGrid.idx 1494) (oGrid.dm 1494) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1494) oGrid.kl oGrid.kr 400 400 ⟨false, 57900333926696780224396865739252739358472255834344289915223184815346939702⟩ ⟨false, 0⟩ ⟨false, 129487418469530224456152671001869152425560144965499994192225744177172398480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1494_800 : bothSeg evalE (oGrid.idx 1494) (oGrid.dm 1494) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1494) oGrid.kl oGrid.kr 400 800 ⟨false, 129487418469530224456152671001869152425560144965499994192225744177172398480⟩ ⟨false, 0⟩ ⟨false, 192166448168782073172880508389529198368540303224779988494890530212729458688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1494_1200 : bothSeg evalE (oGrid.idx 1494) (oGrid.dm 1494) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1494) oGrid.kl oGrid.kr 400 1200 ⟨false, 192166448168782073172880508389529198368540303224779988494890530212729458688⟩ ⟨false, 0⟩ ⟨false, 298812531124820852271014418921695417484045042279859352705556010504695685942⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1494_1600 : bothSeg evalE (oGrid.idx 1494) (oGrid.dm 1494) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1494) oGrid.kl oGrid.kr 400 1600 ⟨false, 298812531124820852271014418921695417484045042279859352705556010504695685942⟩ ⟨false, 0⟩ ⟨false, 456544166542749102494675412680732117488986926243487733855573340433048629922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1494_2000 : bothSeg evalE (oGrid.idx 1494) (oGrid.dm 1494) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1494) oGrid.kl oGrid.kr 400 2000 ⟨false, 456544166542749102494675412680732117488986926243487733855573340433048629922⟩ ⟨false, 0⟩ ⟨false, 663563475576986115106150678103139483386809553148750986671338167215301354270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1494_2400 : bothLoop evalE (oGrid.idx 1494) (oGrid.dm 1494) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1494) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 663563475576986115106150678103139483386809553148750986671338167215301354270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1494 : oGrid.row evalE 1494 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1494_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1494_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1494_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1494_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1494_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1494_2000).1 (bothLoop_sound b_1494_2400).1))))))

theorem n_row_1494 : nGrid.row evalE 1494 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1494_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1494_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1494_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1494_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1494_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1494_2000).2 (bothLoop_sound b_1494_2400).2))))))

theorem b_1495_0 : bothSeg evalE (oGrid.idx 1495) (oGrid.dm 1495) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1495) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 58413025303843416118257130625948949185660001034109328094232440587793958514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1495_400 : bothSeg evalE (oGrid.idx 1495) (oGrid.dm 1495) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1495) oGrid.kl oGrid.kr 400 400 ⟨false, 58413025303843416118257130625948949185660001034109328094232440587793958514⟩ ⟨false, 0⟩ ⟨false, 130031999646810613112924837526722138021798832744644128202064377435145573700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1495_800 : bothSeg evalE (oGrid.idx 1495) (oGrid.dm 1495) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1495) oGrid.kl oGrid.kr 400 800 ⟨false, 130031999646810613112924837526722138021798832744644128202064377435145573700⟩ ⟨false, 0⟩ ⟨false, 192881876763900140040277460546881009356061888000696096905872907626150696388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1495_1200 : bothSeg evalE (oGrid.idx 1495) (oGrid.dm 1495) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1495) oGrid.kl oGrid.kr 400 1200 ⟨false, 192881876763900140040277460546881009356061888000696096905872907626150696388⟩ ⟨false, 0⟩ ⟨false, 299834722958941170842591576730885400375185435394432560377037604803361132982⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1495_1600 : bothSeg evalE (oGrid.idx 1495) (oGrid.dm 1495) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1495) oGrid.kl oGrid.kr 400 1600 ⟨false, 299834722958941170842591576730885400375185435394432560377037604803361132982⟩ ⟨false, 0⟩ ⟨false, 457834443418693814787029516151532927592439300356035173590245646995117518088⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1495_2000 : bothSeg evalE (oGrid.idx 1495) (oGrid.dm 1495) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1495) oGrid.kl oGrid.kr 400 2000 ⟨false, 457834443418693814787029516151532927592439300356035173590245646995117518088⟩ ⟨false, 0⟩ ⟨false, 665091097965659757461532922654952909157720580011420149702794176176650068378⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1495_2400 : bothLoop evalE (oGrid.idx 1495) (oGrid.dm 1495) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1495) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 665091097965659757461532922654952909157720580011420149702794176176650068378⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1495 : oGrid.row evalE 1495 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1495_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1495_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1495_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1495_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1495_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1495_2000).1 (bothLoop_sound b_1495_2400).1))))))

theorem n_row_1495 : nGrid.row evalE 1495 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1495_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1495_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1495_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1495_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1495_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1495_2000).2 (bothLoop_sound b_1495_2400).2))))))

theorem b_1496_0 : bothSeg evalE (oGrid.idx 1496) (oGrid.dm 1496) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1496) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 58925561732670911560674126807392357071623557190294567233371512961697348062⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1496_400 : bothSeg evalE (oGrid.idx 1496) (oGrid.dm 1496) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1496) oGrid.kl oGrid.kr 400 400 ⟨false, 58925561732670911560674126807392357071623557190294567233371512961697348062⟩ ⟨false, 0⟩ ⟨false, 130566061078854666152158748626354061596972595588962695730646833540679482422⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1496_800 : bothSeg evalE (oGrid.idx 1496) (oGrid.dm 1496) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1496) oGrid.kl oGrid.kr 400 800 ⟨false, 130566061078854666152158748626354061596972595588962695730646833540679482422⟩ ⟨false, 0⟩ ⟨false, 193592187999680654280415684592826184313670301153171330142199971141062134254⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1496_1200 : bothSeg evalE (oGrid.idx 1496) (oGrid.dm 1496) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1496) oGrid.kl oGrid.kr 400 1200 ⟨false, 193592187999680654280415684592826184313670301153171330142199971141062134254⟩ ⟨false, 0⟩ ⟨false, 300851777358485228520155237356798711894707298382848928152481964228442719644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1496_1600 : bothSeg evalE (oGrid.idx 1496) (oGrid.dm 1496) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1496) oGrid.kl oGrid.kr 400 1600 ⟨false, 300851777358485228520155237356798711894707298382848928152481964228442719644⟩ ⟨false, 0⟩ ⟨false, 459119596332224660181665998485125258795048286077812481266984328002737657654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1496_2000 : bothSeg evalE (oGrid.idx 1496) (oGrid.dm 1496) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1496) oGrid.kl oGrid.kr 400 2000 ⟨false, 459119596332224660181665998485125258795048286077812481266984328002737657654⟩ ⟨false, 0⟩ ⟨false, 666613628214651493683591285354681227064853540777362010199035467092904597250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1496_2400 : bothLoop evalE (oGrid.idx 1496) (oGrid.dm 1496) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1496) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 666613628214651493683591285354681227064853540777362010199035467092904597250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1496 : oGrid.row evalE 1496 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1496_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1496_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1496_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1496_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1496_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1496_2000).1 (bothLoop_sound b_1496_2400).1))))))

theorem n_row_1496 : nGrid.row evalE 1496 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1496_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1496_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1496_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1496_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1496_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1496_2000).2 (bothLoop_sound b_1496_2400).2))))))

theorem b_1497_0 : bothSeg evalE (oGrid.idx 1497) (oGrid.dm 1497) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1497) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59437726937434764052495510748494598812145269633042284240804539612111433828⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1497_400 : bothSeg evalE (oGrid.idx 1497) (oGrid.dm 1497) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1497) oGrid.kl oGrid.kr 400 400 ⟨false, 59437726937434764052495510748494598812145269633042284240804539612111433828⟩ ⟨false, 0⟩ ⟨false, 131089480553458824662795031021794697966224414634016070086690669218315218782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1497_800 : bothSeg evalE (oGrid.idx 1497) (oGrid.dm 1497) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1497) oGrid.kl oGrid.kr 400 800 ⟨false, 131089480553458824662795031021794697966224414634016070086690669218315218782⟩ ⟨false, 0⟩ ⟨false, 194297218168130173165333618329347319983131575194480491912721740360360271072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1497_1200 : bothSeg evalE (oGrid.idx 1497) (oGrid.dm 1497) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1497) oGrid.kl oGrid.kr 400 1200 ⟨false, 194297218168130173165333618329347319983131575194480491912721740360360271072⟩ ⟨false, 0⟩ ⟨false, 301863530583810386529863621193155252257923004871721227850236738445041768778⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1497_1600 : bothSeg evalE (oGrid.idx 1497) (oGrid.dm 1497) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1497) oGrid.kl oGrid.kr 400 1600 ⟨false, 301863530583810386529863621193155252257923004871721227850236738445041768778⟩ ⟨false, 0⟩ ⟨false, 460399461485301492406514791898996384736944654766597276973790005266845067148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1497_2000 : bothSeg evalE (oGrid.idx 1497) (oGrid.dm 1497) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1497) oGrid.kl oGrid.kr 400 2000 ⟨false, 460399461485301492406514791898996384736944654766597276973790005266845067148⟩ ⟨false, 0⟩ ⟨false, 668130902465382914806634316366202146942435376432710783530112965977721346710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1497_2400 : bothLoop evalE (oGrid.idx 1497) (oGrid.dm 1497) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1497) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 668130902465382914806634316366202146942435376432710783530112965977721346710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1497 : oGrid.row evalE 1497 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1497_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1497_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1497_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1497_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1497_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1497_2000).1 (bothLoop_sound b_1497_2400).1))))))

theorem n_row_1497 : nGrid.row evalE 1497 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1497_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1497_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1497_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1497_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1497_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1497_2000).2 (bothLoop_sound b_1497_2400).2))))))

theorem b_1498_0 : bothSeg evalE (oGrid.idx 1498) (oGrid.dm 1498) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1498) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59949294607237343351489167327175649529388941088416514791327312863077912916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1498_400 : bothSeg evalE (oGrid.idx 1498) (oGrid.dm 1498) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1498) oGrid.kl oGrid.kr 400 400 ⟨false, 59949294607237343351489167327175649529388941088416514791327312863077912916⟩ ⟨false, 0⟩ ⟨false, 131602114126046467185991538153131125621014698461021916435179906398920455090⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1498_800 : bothSeg evalE (oGrid.idx 1498) (oGrid.dm 1498) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1498) oGrid.kl oGrid.kr 400 800 ⟨false, 131602114126046467185991538153131125621014698461021916435179906398920455090⟩ ⟨false, 0⟩ ⟨false, 194996767575850906592083926085762789071934273483003572620120192705119225272⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1498_1200 : bothSeg evalE (oGrid.idx 1498) (oGrid.dm 1498) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1498) oGrid.kl oGrid.kr 400 1200 ⟨false, 194996767575850906592083926085762789071934273483003572620120192705119225272⟩ ⟨false, 0⟩ ⟨false, 302869782909973406944972035787705629396258180321814111237075277174334837032⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1498_1600 : bothSeg evalE (oGrid.idx 1498) (oGrid.dm 1498) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1498) oGrid.kl oGrid.kr 400 1600 ⟨false, 302869782909973406944972035787705629396258180321814111237075277174334837032⟩ ⟨false, 0⟩ ⟨false, 461673839094692165961825394099572167882897069947015578996174302996040275880⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1498_2000 : bothSeg evalE (oGrid.idx 1498) (oGrid.dm 1498) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1498) oGrid.kl oGrid.kr 400 2000 ⟨false, 461673839094692165961825394099572167882897069947015578996174302996040275880⟩ ⟨false, 0⟩ ⟨false, 669642720874163189652713869498594987631398844431806939153352322691127334504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1498_2400 : bothLoop evalE (oGrid.idx 1498) (oGrid.dm 1498) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1498) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 669642720874163189652713869498594987631398844431806939153352322691127334504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1498 : oGrid.row evalE 1498 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1498_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1498_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1498_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1498_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1498_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1498_2000).1 (bothLoop_sound b_1498_2400).1))))))

theorem n_row_1498 : nGrid.row evalE 1498 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1498_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1498_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1498_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1498_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1498_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1498_2000).2 (bothLoop_sound b_1498_2400).2))))))

theorem b_1499_0 : bothSeg evalE (oGrid.idx 1499) (oGrid.dm 1499) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1499) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60460025191108027286914435986744608424047254983777324139063892890925105572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1499_400 : bothSeg evalE (oGrid.idx 1499) (oGrid.dm 1499) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1499) oGrid.kl oGrid.kr 400 400 ⟨false, 60460025191108027286914435986744608424047254983777324139063892890925105572⟩ ⟨false, 0⟩ ⟨false, 132103828997450384962988568761102321923390733155696764203632008029866996386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1499_800 : bothSeg evalE (oGrid.idx 1499) (oGrid.dm 1499) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1499) oGrid.kl oGrid.kr 400 800 ⟨false, 132103828997450384962988568761102321923390733155696764203632008029866996386⟩ ⟨false, 0⟩ ⟨false, 195690647455342866354304916169031079982445908435309314153462330494621489304⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1499_1200 : bothSeg evalE (oGrid.idx 1499) (oGrid.dm 1499) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1499) oGrid.kl oGrid.kr 400 1200 ⟨false, 195690647455342866354304916169031079982445908435309314153462330494621489304⟩ ⟨false, 0⟩ ⟨false, 303870345538032360824695028022508490206158898575033481803730060212461587556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1499_1600 : bothSeg evalE (oGrid.idx 1499) (oGrid.dm 1499) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1499) oGrid.kl oGrid.kr 400 1600 ⟨false, 303870345538032360824695028022508490206158898575033481803730060212461587556⟩ ⟨false, 0⟩ ⟨false, 462942540303274271381033414738906290818038073679130212946928171856162369582⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1499_2000 : bothSeg evalE (oGrid.idx 1499) (oGrid.dm 1499) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1499) oGrid.kl oGrid.kr 400 2000 ⟨false, 462942540303274271381033414738906290818038073679130212946928171856162369582⟩ ⟨false, 0⟩ ⟨false, 671148894523490720567552201434894991562190754238322005028657963921441078214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1499_2400 : bothLoop evalE (oGrid.idx 1499) (oGrid.dm 1499) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1499) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 671148894523490720567552201434894991562190754238322005028657963921441078214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1499 : oGrid.row evalE 1499 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1499_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1499_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1499_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1499_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1499_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1499_2000).1 (bothLoop_sound b_1499_2400).1))))))

theorem n_row_1499 : nGrid.row evalE 1499 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1499_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1499_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1499_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1499_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1499_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1499_2000).2 (bothLoop_sound b_1499_2400).2))))))

theorem b_1500_0 : bothSeg evalE (oGrid.idx 1500) (oGrid.dm 1500) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1500) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60969673476774652794059342104051919187976086475351670557209807720470772820⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1500_400 : bothSeg evalE (oGrid.idx 1500) (oGrid.dm 1500) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1500) oGrid.kl oGrid.kr 400 400 ⟨false, 60969673476774652794059342104051919187976086475351670557209807720470772820⟩ ⟨false, 0⟩ ⟨false, 132594483851017456753293883855899365616667010683489862081090570785486374450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1500_800 : bothSeg evalE (oGrid.idx 1500) (oGrid.dm 1500) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1500) oGrid.kl oGrid.kr 400 800 ⟨false, 132594483851017456753293883855899365616667010683489862081090570785486374450⟩ ⟨false, 0⟩ ⟨false, 196378656017529942627062447242127075591435972969109644475490643543836977572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1500_1200 : bothSeg evalE (oGrid.idx 1500) (oGrid.dm 1500) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1500) oGrid.kl oGrid.kr 400 1200 ⟨false, 196378656017529942627062447242127075591435972969109644475490643543836977572⟩ ⟨false, 0⟩ ⟨false, 304865016647572464086597109544559053413677200964424132112471962259582597276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1500_1600 : bothSeg evalE (oGrid.idx 1500) (oGrid.dm 1500) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1500) oGrid.kl oGrid.kr 400 1600 ⟨false, 304865016647572464086597109544559053413677200964424132112471962259582597276⟩ ⟨false, 0⟩ ⟨false, 464205363232560798452678404048353657346169802149502302991068639179043870378⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1500_2000 : bothSeg evalE (oGrid.idx 1500) (oGrid.dm 1500) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1500) oGrid.kl oGrid.kr 400 2000 ⟨false, 464205363232560798452678404048353657346169802149502302991068639179043870378⟩ ⟨false, 0⟩ ⟨false, 672649221474578727130819959415906226999436816065960366584338677544151386844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1500_2400 : bothLoop evalE (oGrid.idx 1500) (oGrid.dm 1500) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1500) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 672649221474578727130819959415906226999436816065960366584338677544151386844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1500 : oGrid.row evalE 1500 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1500_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1500_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1500_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1500_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1500_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1500_2000).1 (bothLoop_sound b_1500_2400).1))))))

theorem n_row_1500 : nGrid.row evalE 1500 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1500_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1500_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1500_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1500_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1500_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1500_2000).2 (bothLoop_sound b_1500_2400).2))))))

theorem b_1501_0 : bothSeg evalE (oGrid.idx 1501) (oGrid.dm 1501) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1501) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61477981377240113911844658364708563948990906317683025460285203856380034432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1501_400 : bothSeg evalE (oGrid.idx 1501) (oGrid.dm 1501) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1501) oGrid.kl oGrid.kr 400 400 ⟨false, 61477981377240113911844658364708563948990906317683025460285203856380034432⟩ ⟨false, 0⟩ ⟨false, 133073953536051921019095536978401954215498697939988907155550587849313678590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1501_800 : bothSeg evalE (oGrid.idx 1501) (oGrid.dm 1501) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1501) oGrid.kl oGrid.kr 400 800 ⟨false, 133073953536051921019095536978401954215498697939988907155550587849313678590⟩ ⟨false, 0⟩ ⟨false, 197060601959700377435847795324418461045981765463596748672798541758550989322⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1501_1200 : bothSeg evalE (oGrid.idx 1501) (oGrid.dm 1501) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1501) oGrid.kl oGrid.kr 400 1200 ⟨false, 197060601959700377435847795324418461045981765463596748672798541758550989322⟩ ⟨false, 0⟩ ⟨false, 305853604904646310882345715492132652162664339508398654793710235792813374712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1501_1600 : bothSeg evalE (oGrid.idx 1501) (oGrid.dm 1501) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1501) oGrid.kl oGrid.kr 400 1600 ⟨false, 305853604904646310882345715492132652162664339508398654793710235792813374712⟩ ⟨false, 0⟩ ⟨false, 465462116490640197173082842817860913197745834816792680618305952557344815920⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1501_2000 : bothSeg evalE (oGrid.idx 1501) (oGrid.dm 1501) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1501) oGrid.kl oGrid.kr 400 2000 ⟨false, 465462116490640197173082842817860913197745834816792680618305952557344815920⟩ ⟨false, 0⟩ ⟨false, 674143510275295227610724934919431247631520971573616608422787967276214101730⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1501_2400 : bothLoop evalE (oGrid.idx 1501) (oGrid.dm 1501) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1501) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 674143510275295227610724934919431247631520971573616608422787967276214101730⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1501 : oGrid.row evalE 1501 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1501_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1501_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1501_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1501_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1501_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1501_2000).1 (bothLoop_sound b_1501_2400).1))))))

theorem n_row_1501 : nGrid.row evalE 1501 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1501_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1501_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1501_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1501_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1501_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1501_2000).2 (bothLoop_sound b_1501_2400).2))))))

theorem b_1502_0 : bothSeg evalE (oGrid.idx 1502) (oGrid.dm 1502) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1502) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61984676092099518814397333130990918037919846013078979948689099217466081356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1502_400 : bothSeg evalE (oGrid.idx 1502) (oGrid.dm 1502) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1502) oGrid.kl oGrid.kr 400 400 ⟨false, 61984676092099518814397333130990918037919846013078979948689099217466081356⟩ ⟨false, 0⟩ ⟨false, 133542109228506403044194908586947602596181155163423095860839787523616488204⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1502_800 : bothSeg evalE (oGrid.idx 1502) (oGrid.dm 1502) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1502) oGrid.kl oGrid.kr 400 800 ⟨false, 133542109228506403044194908586947602596181155163423095860839787523616488204⟩ ⟨false, 0⟩ ⟨false, 197736286231812891250363638668010106954403321585447432735730324648092279046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1502_1200 : bothSeg evalE (oGrid.idx 1502) (oGrid.dm 1502) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1502) oGrid.kl oGrid.kr 400 1200 ⟨false, 197736286231812891250363638668010106954403321585447432735730324648092279046⟩ ⟨false, 0⟩ ⟨false, 306835911228079760616408530406926647251882694045813569047278710133900778148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1502_1600 : bothSeg evalE (oGrid.idx 1502) (oGrid.dm 1502) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1502) oGrid.kl oGrid.kr 400 1600 ⟨false, 306835911228079760616408530406926647251882694045813569047278710133900778148⟩ ⟨false, 0⟩ ⟨false, 466712600938482092569249901014529118429409374695551248841256564876491155866⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1502_2000 : bothSeg evalE (oGrid.idx 1502) (oGrid.dm 1502) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1502) oGrid.kl oGrid.kr 400 2000 ⟨false, 466712600938482092569249901014529118429409374695551248841256564876491155866⟩ ⟨false, 0⟩ ⟨false, 675631561726468674302618186525603357739630425942836874584510181834281604694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1502_2400 : bothLoop evalE (oGrid.idx 1502) (oGrid.dm 1502) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1502) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 675631561726468674302618186525603357739630425942836874584510181834281604694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1502 : oGrid.row evalE 1502 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1502_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1502_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1502_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1502_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1502_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1502_2000).1 (bothLoop_sound b_1502_2400).1))))))

theorem n_row_1502 : nGrid.row evalE 1502 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1502_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1502_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1502_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1502_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1502_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1502_2000).2 (bothLoop_sound b_1502_2400).2))))))

theorem b_1503_0 : bothSeg evalE (oGrid.idx 1503) (oGrid.dm 1503) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1503) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62489487702829118580286593436647171009864564703999853087722042695062176774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1503_400 : bothSeg evalE (oGrid.idx 1503) (oGrid.dm 1503) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1503) oGrid.kl oGrid.kr 400 400 ⟨false, 62489487702829118580286593436647171009864564703999853087722042695062176774⟩ ⟨false, 0⟩ ⟨false, 133998829217018688322109602683710294682008871454130484418570454620431628192⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1503_800 : bothSeg evalE (oGrid.idx 1503) (oGrid.dm 1503) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1503) oGrid.kl oGrid.kr 400 800 ⟨false, 133998829217018688322109602683710294682008871454130484418570454620431628192⟩ ⟨false, 0⟩ ⟨false, 198405514995320719923026997359311429258008247867933169816498699389680555846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1503_1200 : bothSeg evalE (oGrid.idx 1503) (oGrid.dm 1503) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1503) oGrid.kl oGrid.kr 400 1200 ⟨false, 198405514995320719923026997359311429258008247867933169816498699389680555846⟩ ⟨false, 0⟩ ⟨false, 307811741748295735826575781918616034892438320958958072575736462270599121096⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1503_1600 : bothSeg evalE (oGrid.idx 1503) (oGrid.dm 1503) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1503) oGrid.kl oGrid.kr 400 1600 ⟨false, 307811741748295735826575781918616034892438320958958072575736462270599121096⟩ ⟨false, 0⟩ ⟨false, 467956622648760910610735297790828320490275019903336566423571575844180901606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1503_2000 : bothSeg evalE (oGrid.idx 1503) (oGrid.dm 1503) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1503) oGrid.kl oGrid.kr 400 2000 ⟨false, 467956622648760910610735297790828320490275019903336566423571575844180901606⟩ ⟨false, 0⟩ ⟨false, 677113181840711499970620860791074740599086907063320988861820215839752536142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1503_2400 : bothLoop evalE (oGrid.idx 1503) (oGrid.dm 1503) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1503) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 677113181840711499970620860791074740599086907063320988861820215839752536142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1503 : oGrid.row evalE 1503 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1503_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1503_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1503_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1503_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1503_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1503_2000).1 (bothLoop_sound b_1503_2400).1))))))

theorem n_row_1503 : nGrid.row evalE 1503 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1503_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1503_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1503_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1503_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1503_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1503_2000).2 (bothLoop_sound b_1503_2400).2))))))

theorem b_1504_0 : bothSeg evalE (oGrid.idx 1504) (oGrid.dm 1504) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1504) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62992128897442899654902045552038046082801201706064052137126597201599915154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1504_400 : bothSeg evalE (oGrid.idx 1504) (oGrid.dm 1504) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1504) oGrid.kl oGrid.kr 400 400 ⟨false, 62992128897442899654902045552038046082801201706064052137126597201599915154⟩ ⟨false, 0⟩ ⟨false, 134443978015680514593674095269172031528872639164963734658241190538921518516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1504_800 : bothSeg evalE (oGrid.idx 1504) (oGrid.dm 1504) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1504) oGrid.kl oGrid.kr 400 800 ⟨false, 134443978015680514593674095269172031528872639164963734658241190538921518516⟩ ⟨false, 0⟩ ⟨false, 199068072706411084362260138857169594841639637369555747103657625283941852546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1504_1200 : bothSeg evalE (oGrid.idx 1504) (oGrid.dm 1504) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1504) oGrid.kl oGrid.kr 400 1200 ⟨false, 199068072706411084362260138857169594841639637369555747103657625283941852546⟩ ⟨false, 0⟩ ⟨false, 308780880890553453315332063057422327382233918192104655006048081411542783932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1504_1600 : bothSeg evalE (oGrid.idx 1504) (oGrid.dm 1504) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1504) oGrid.kl oGrid.kr 400 1600 ⟨false, 308780880890553453315332063057422327382233918192104655006048081411542783932⟩ ⟨false, 0⟩ ⟨false, 469193965989094937599391819124648343544686566392232232056858636218624210272⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1504_2000 : bothSeg evalE (oGrid.idx 1504) (oGrid.dm 1504) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1504) oGrid.kl oGrid.kr 400 2000 ⟨false, 469193965989094937599391819124648343544686566392232232056858636218624210272⟩ ⟨false, 0⟩ ⟨false, 678588154925659097781417266267478416616890176829812145435770938604197929246⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1504_2400 : bothLoop evalE (oGrid.idx 1504) (oGrid.dm 1504) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1504) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 678588154925659097781417266267478416616890176829812145435770938604197929246⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1504 : oGrid.row evalE 1504 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1504_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1504_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1504_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1504_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1504_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1504_2000).1 (bothLoop_sound b_1504_2400).1))))))

theorem n_row_1504 : nGrid.row evalE 1504 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1504_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1504_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1504_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1504_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1504_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1504_2000).2 (bothLoop_sound b_1504_2400).2))))))

theorem b_1505_0 : bothSeg evalE (oGrid.idx 1505) (oGrid.dm 1505) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1505) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63492299564528493600966097122583190729765173637387423249270567246783825160⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1505_400 : bothSeg evalE (oGrid.idx 1505) (oGrid.dm 1505) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1505) oGrid.kl oGrid.kr 400 400 ⟨false, 63492299564528493600966097122583190729765173637387423249270567246783825160⟩ ⟨false, 0⟩ ⟨false, 134877432984449207370782056993233097768716639909920587023984557101816770986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1505_800 : bothSeg evalE (oGrid.idx 1505) (oGrid.dm 1505) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1505) oGrid.kl oGrid.kr 400 800 ⟨false, 134877432984449207370782056993233097768716639909920587023984557101816770986⟩ ⟨false, 0⟩ ⟨false, 199723759291612311780429731875633269172104838581807456816195952135099313858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1505_1200 : bothSeg evalE (oGrid.idx 1505) (oGrid.dm 1505) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1505) oGrid.kl oGrid.kr 400 1200 ⟨false, 199723759291612311780429731875633269172104838581807456816195952135099313858⟩ ⟨false, 0⟩ ⟨false, 309743128550555307370893299948738494504011428295420178407024388350002412726⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1505_1600 : bothSeg evalE (oGrid.idx 1505) (oGrid.dm 1505) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1505) oGrid.kl oGrid.kr 400 1600 ⟨false, 309743128550555307370893299948738494504011428295420178407024388350002412726⟩ ⟨false, 0⟩ ⟨false, 470424430797653031875675372900050991111092329588867708059711539449456135936⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1505_2000 : bothSeg evalE (oGrid.idx 1505) (oGrid.dm 1505) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1505) oGrid.kl oGrid.kr 400 2000 ⟨false, 470424430797653031875675372900050991111092329588867708059711539449456135936⟩ ⟨false, 0⟩ ⟨false, 680056280759576453569149084828118621184588580698955537171180392152087499376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1505_2400 : bothLoop evalE (oGrid.idx 1505) (oGrid.dm 1505) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1505) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 680056280759576453569149084828118621184588580698955537171180392152087499376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1505 : oGrid.row evalE 1505 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1505_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1505_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1505_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1505_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1505_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1505_2000).1 (bothLoop_sound b_1505_2400).1))))))

theorem n_row_1505 : nGrid.row evalE 1505 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1505_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1505_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1505_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1505_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1505_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1505_2000).2 (bothLoop_sound b_1505_2400).2))))))

theorem b_1506_0 : bothSeg evalE (oGrid.idx 1506) (oGrid.dm 1506) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1506) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63989701819971894087305832516460624714993735376404808108735132024551545882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1506_400 : bothSeg evalE (oGrid.idx 1506) (oGrid.dm 1506) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1506) oGrid.kl oGrid.kr 400 400 ⟨false, 63989701819971894087305832516460624714993735376404808108735132024551545882⟩ ⟨false, 0⟩ ⟨false, 135299070726343765736260591185594699085909738201276251715652184138886000490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1506_800 : bothSeg evalE (oGrid.idx 1506) (oGrid.dm 1506) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1506) oGrid.kl oGrid.kr 400 800 ⟨false, 135299070726343765736260591185594699085909738201276251715652184138886000490⟩ ⟨false, 0⟩ ⟨false, 200372363427642652320393609267859603910636427625394857940949307897653116174⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1506_1200 : bothSeg evalE (oGrid.idx 1506) (oGrid.dm 1506) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1506) oGrid.kl oGrid.kr 400 1200 ⟨false, 200372363427642652320393609267859603910636427625394857940949307897653116174⟩ ⟨false, 0⟩ ⟨false, 310698273374295448880825343378106822547814667397915127223991979847383158636⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1506_1600 : bothSeg evalE (oGrid.idx 1506) (oGrid.dm 1506) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1506) oGrid.kl oGrid.kr 400 1600 ⟨false, 310698273374295448880825343378106822547814667397915127223991979847383158636⟩ ⟨false, 0⟩ ⟨false, 471647805663003031644301595068340113276850857931331543686626861162175719516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1506_2000 : bothSeg evalE (oGrid.idx 1506) (oGrid.dm 1506) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1506) oGrid.kl oGrid.kr 400 2000 ⟨false, 471647805663003031644301595068340113276850857931331543686626861162175719516⟩ ⟨false, 0⟩ ⟨false, 681517347871206474234444746395922798095746411605102506400348575865885573126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1506_2400 : bothLoop evalE (oGrid.idx 1506) (oGrid.dm 1506) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1506) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 681517347871206474234444746395922798095746411605102506400348575865885573126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1506 : oGrid.row evalE 1506 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1506_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1506_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1506_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1506_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1506_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1506_2000).1 (bothLoop_sound b_1506_2400).1))))))

theorem n_row_1506 : nGrid.row evalE 1506 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1506_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1506_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1506_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1506_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1506_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1506_2000).2 (bothLoop_sound b_1506_2400).2))))))

theorem b_1507_0 : bothSeg evalE (oGrid.idx 1507) (oGrid.dm 1507) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1507) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64484017594070385891962076200264797252360683047352287350718162286796482412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1507_400 : bothSeg evalE (oGrid.idx 1507) (oGrid.dm 1507) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1507) oGrid.kl oGrid.kr 400 400 ⟨false, 64484017594070385891962076200264797252360683047352287350718162286796482412⟩ ⟨false, 0⟩ ⟨false, 135708750859294165925523342721534088718943468739698146446447224253538889254⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1507_800 : bothSeg evalE (oGrid.idx 1507) (oGrid.dm 1507) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1507) oGrid.kl oGrid.kr 400 800 ⟨false, 135708750859294165925523342721534088718943468739698146446447224253538889254⟩ ⟨false, 0⟩ ⟨false, 201013659422730425783792919176399672428735582423608079904687719408294614870⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1507_1200 : bothSeg evalE (oGrid.idx 1507) (oGrid.dm 1507) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1507) oGrid.kl oGrid.kr 400 1200 ⟨false, 201013659422730425783792919176399672428735582423608079904687719408294614870⟩ ⟨false, 0⟩ ⟨false, 311646089639379695060340863582805320922139482653415250663738897439199389364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1507_1600 : bothSeg evalE (oGrid.idx 1507) (oGrid.dm 1507) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1507) oGrid.kl oGrid.kr 400 1600 ⟨false, 311646089639379695060340863582805320922139482653415250663738897439199389364⟩ ⟨false, 0⟩ ⟨false, 472863864805431493641221497904675861194802778720127409572139094760456238436⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1507_2000 : bothSeg evalE (oGrid.idx 1507) (oGrid.dm 1507) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1507) oGrid.kl oGrid.kr 400 2000 ⟨false, 472863864805431493641221497904675861194802778720127409572139094760456238436⟩ ⟨false, 0⟩ ⟨false, 682971130421089646999796481271571171293141638096741767616734416407736454622⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1507_2400 : bothLoop evalE (oGrid.idx 1507) (oGrid.dm 1507) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1507) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 682971130421089646999796481271571171293141638096741767616734416407736454622⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1507 : oGrid.row evalE 1507 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1507_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1507_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1507_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1507_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1507_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1507_2000).1 (bothLoop_sound b_1507_2400).1))))))

theorem n_row_1507 : nGrid.row evalE 1507 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1507_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1507_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1507_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1507_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1507_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1507_2000).2 (bothLoop_sound b_1507_2400).2))))))

theorem b_1508_0 : bothSeg evalE (oGrid.idx 1508) (oGrid.dm 1508) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1508) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64974926208031405086358436188958696634675804025521200886235175297788330348⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1508_400 : bothSeg evalE (oGrid.idx 1508) (oGrid.dm 1508) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1508) oGrid.kl oGrid.kr 400 400 ⟨false, 64974926208031405086358436188958696634675804025521200886235175297788330348⟩ ⟨false, 0⟩ ⟨false, 136106371974444796600070182027540075881279702996221527531160824946290270406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1508_800 : bothSeg evalE (oGrid.idx 1508) (oGrid.dm 1508) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1508) oGrid.kl oGrid.kr 400 800 ⟨false, 136106371974444796600070182027540075881279702996221527531160824946290270406⟩ ⟨false, 0⟩ ⟨false, 201647454741636039004649100048700572483089611615444934953690527354292814658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1508_1200 : bothSeg evalE (oGrid.idx 1508) (oGrid.dm 1508) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1508) oGrid.kl oGrid.kr 400 1200 ⟨false, 201647454741636039004649100048700572483089611615444934953690527354292814658⟩ ⟨false, 0⟩ ⟨false, 312586384780047310337794664981998652477675736880606175409952247116597423698⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1508_1600 : bothSeg evalE (oGrid.idx 1508) (oGrid.dm 1508) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1508) oGrid.kl oGrid.kr 400 1600 ⟨false, 312586384780047310337794664981998652477675736880606175409952247116597423698⟩ ⟨false, 0⟩ ⟨false, 474072415601965303184307369632911355066279748722552247038258259691384980024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1508_2000 : bothSeg evalE (oGrid.idx 1508) (oGrid.dm 1508) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1508) oGrid.kl oGrid.kr 400 2000 ⟨false, 474072415601965303184307369632911355066279748722552247038258259691384980024⟩ ⟨false, 0⟩ ⟨false, 684417435726585570063919295875862135481583809732000029434793764460948765930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1508_2400 : bothLoop evalE (oGrid.idx 1508) (oGrid.dm 1508) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1508) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 684417435726585570063919295875862135481583809732000029434793764460948765930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1508 : oGrid.row evalE 1508 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1508_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1508_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1508_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1508_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1508_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1508_2000).1 (bothLoop_sound b_1508_2400).1))))))

theorem n_row_1508 : nGrid.row evalE 1508 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1508_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1508_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1508_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1508_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1508_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1508_2000).2 (bothLoop_sound b_1508_2400).2))))))

theorem b_1509_0 : bothSeg evalE (oGrid.idx 1509) (oGrid.dm 1509) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1509) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65462099504209380003603087640193532673336322996687110533975499215871482022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1509_400 : bothSeg evalE (oGrid.idx 1509) (oGrid.dm 1509) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1509) oGrid.kl oGrid.kr 400 400 ⟨false, 65462099504209380003603087640193532673336322996687110533975499215871482022⟩ ⟨false, 0⟩ ⟨false, 136491815794812329177557695858694119714820554343987237947367204133766832056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1509_800 : bothSeg evalE (oGrid.idx 1509) (oGrid.dm 1509) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1509) oGrid.kl oGrid.kr 400 800 ⟨false, 136491815794812329177557695858694119714820554343987237947367204133766832056⟩ ⟨false, 0⟩ ⟨false, 202273536559580441027148643774632823338572045047472297371687207005079984564⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1509_1200 : bothSeg evalE (oGrid.idx 1509) (oGrid.dm 1509) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1509) oGrid.kl oGrid.kr 400 1200 ⟨false, 202273536559580441027148643774632823338572045047472297371687207005079984564⟩ ⟨false, 0⟩ ⟨false, 313518945941099225555222845989854131755799906111875170363603156262012610832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1509_1600 : bothSeg evalE (oGrid.idx 1509) (oGrid.dm 1509) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1509) oGrid.kl oGrid.kr 400 1600 ⟨false, 313518945941099225555222845989854131755799906111875170363603156262012610832⟩ ⟨false, 0⟩ ⟨false, 475273245140299722765464728402625127349328394976317587673995557698613105550⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1509_2000 : bothSeg evalE (oGrid.idx 1509) (oGrid.dm 1509) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1509) oGrid.kl oGrid.kr 400 2000 ⟨false, 475273245140299722765464728402625127349328394976317587673995557698613105550⟩ ⟨false, 0⟩ ⟨false, 685856050815800921813049727412244663198220529969471507274746150504216197354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1509_2400 : bothLoop evalE (oGrid.idx 1509) (oGrid.dm 1509) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1509) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 685856050815800921813049727412244663198220529969471507274746150504216197354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1509 : oGrid.row evalE 1509 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1509_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1509_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1509_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1509_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1509_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1509_2000).1 (bothLoop_sound b_1509_2400).1))))))

theorem n_row_1509 : nGrid.row evalE 1509 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1509_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1509_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1509_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1509_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1509_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1509_2000).2 (bothLoop_sound b_1509_2400).2))))))

theorem b_1510_0 : bothSeg evalE (oGrid.idx 1510) (oGrid.dm 1510) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1510) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65945205183763987328994135091600299567964521414938620220283362119224867170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1510_400 : bothSeg evalE (oGrid.idx 1510) (oGrid.dm 1510) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1510) oGrid.kl oGrid.kr 400 400 ⟨false, 65945205183763987328994135091600299567964521414938620220283362119224867170⟩ ⟨false, 0⟩ ⟨false, 136864967270278463492684404611496688857922001555942745788231751130515189504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1510_800 : bothSeg evalE (oGrid.idx 1510) (oGrid.dm 1510) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1510) oGrid.kl oGrid.kr 400 800 ⟨false, 136864967270278463492684404611496688857922001555942745788231751130515189504⟩ ⟨false, 0⟩ ⟨false, 202891696373402597431183872858043382390360490639285694519262190345406916908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1510_1200 : bothSeg evalE (oGrid.idx 1510) (oGrid.dm 1510) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1510) oGrid.kl oGrid.kr 400 1200 ⟨false, 202891696373402597431183872858043382390360490639285694519262190345406916908⟩ ⟨false, 0⟩ ⟨false, 314443564589055276826458269227666239150880879819481256392370951674957736014⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1510_1600 : bothSeg evalE (oGrid.idx 1510) (oGrid.dm 1510) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1510) oGrid.kl oGrid.kr 400 1600 ⟨false, 314443564589055276826458269227666239150880879819481256392370951674957736014⟩ ⟨false, 0⟩ ⟨false, 476466144829955460526572463412965675357280197681844331299603454118649945740⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1510_2000 : bothSeg evalE (oGrid.idx 1510) (oGrid.dm 1510) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1510) oGrid.kl oGrid.kr 400 2000 ⟨false, 476466144829955460526572463412965675357280197681844331299603454118649945740⟩ ⟨false, 0⟩ ⟨false, 687286767038746449931827581365025275040327055994498615152613603797267415462⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1510_2400 : bothLoop evalE (oGrid.idx 1510) (oGrid.dm 1510) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1510) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 687286767038746449931827581365025275040327055994498615152613603797267415462⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1510 : oGrid.row evalE 1510 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1510_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1510_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1510_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1510_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1510_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1510_2000).1 (bothLoop_sound b_1510_2400).1))))))

theorem n_row_1510 : nGrid.row evalE 1510 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1510_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1510_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1510_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1510_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1510_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1510_2000).2 (bothLoop_sound b_1510_2400).2))))))

theorem b_1511_0 : bothSeg evalE (oGrid.idx 1511) (oGrid.dm 1511) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1511) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66423901446995153544543516688769674493028364244425897164609470004689220634⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1511_400 : bothSeg evalE (oGrid.idx 1511) (oGrid.dm 1511) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1511) oGrid.kl oGrid.kr 400 400 ⟨false, 66423901446995153544543516688769674493028364244425897164609470004689220634⟩ ⟨false, 0⟩ ⟨false, 137225717523884510732566887542648525569687477420298614593140437553333056356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1511_800 : bothSeg evalE (oGrid.idx 1511) (oGrid.dm 1511) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1511) oGrid.kl oGrid.kr 400 800 ⟨false, 137225717523884510732566887542648525569687477420298614593140437553333056356⟩ ⟨false, 0⟩ ⟨false, 203501724697348861611657901221618270761664221243325155995260316532722702768⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1511_1200 : bothSeg evalE (oGrid.idx 1511) (oGrid.dm 1511) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1511) oGrid.kl oGrid.kr 400 1200 ⟨false, 203501724697348861611657901221618270761664221243325155995260316532722702768⟩ ⟨false, 0⟩ ⟨false, 315360031207943341857796528386429205844172480443724248686727733086716638072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1511_1600 : bothSeg evalE (oGrid.idx 1511) (oGrid.dm 1511) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1511) oGrid.kl oGrid.kr 400 1600 ⟨false, 315360031207943341857796528386429205844172480443724248686727733086716638072⟩ ⟨false, 0⟩ ⟨false, 477650905098067636424094310895572413759675496229911140901308959812536526614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1511_2000 : bothSeg evalE (oGrid.idx 1511) (oGrid.dm 1511) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1511) oGrid.kl oGrid.kr 400 2000 ⟨false, 477650905098067636424094310895572413759675496229911140901308959812536526614⟩ ⟨false, 0⟩ ⟨false, 688709374763125858218843891879160280231824764016772478658710986401553146888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1511_2400 : bothLoop evalE (oGrid.idx 1511) (oGrid.dm 1511) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1511) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 688709374763125858218843891879160280231824764016772478658710986401553146888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1511 : oGrid.row evalE 1511 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1511_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1511_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1511_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1511_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1511_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1511_2000).1 (bothLoop_sound b_1511_2400).1))))))

theorem n_row_1511 : nGrid.row evalE 1511 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1511_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1511_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1511_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1511_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1511_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1511_2000).2 (bothLoop_sound b_1511_2400).2))))))

theorem o_blk_1488 : allFrom (fun j => oGrid.row evalE j) 1488 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1488) o_row_1488 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1489) o_row_1489 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1490) o_row_1490 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1491) o_row_1491 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1492) o_row_1492 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1493) o_row_1493 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1494) o_row_1494 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1495) o_row_1495 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1496) o_row_1496 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1497) o_row_1497 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1498) o_row_1498 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1499) o_row_1499 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1500) o_row_1500 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1501) o_row_1501 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1502) o_row_1502 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1503) o_row_1503 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1504) o_row_1504 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1505) o_row_1505 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1506) o_row_1506 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1507) o_row_1507 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1508) o_row_1508 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1509) o_row_1509 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1510) o_row_1510 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1511) o_row_1511 (allFrom_zero (fun j => oGrid.row evalE j) 1512)))))))))))))))))))))))))

theorem n_blk_1488 : allFrom (fun j => nGrid.row evalE j) 1488 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1488) n_row_1488 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1489) n_row_1489 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1490) n_row_1490 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1491) n_row_1491 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1492) n_row_1492 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1493) n_row_1493 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1494) n_row_1494 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1495) n_row_1495 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1496) n_row_1496 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1497) n_row_1497 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1498) n_row_1498 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1499) n_row_1499 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1500) n_row_1500 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1501) n_row_1501 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1502) n_row_1502 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1503) n_row_1503 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1504) n_row_1504 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1505) n_row_1505 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1506) n_row_1506 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1507) n_row_1507 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1508) n_row_1508 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1509) n_row_1509 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1510) n_row_1510 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1511) n_row_1511 (allFrom_zero (fun j => nGrid.row evalE j) 1512)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
