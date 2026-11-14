/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 61 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1464`–`1487`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1464_0 : bothSeg evalE (oGrid.idx 1464) (oGrid.dm 1464) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1464) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 43106966538378906142797964137036204228664934380633104536207212530034594752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1464_400 : bothSeg evalE (oGrid.idx 1464) (oGrid.dm 1464) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1464) oGrid.kl oGrid.kr 400 400 ⟨false, 43106966538378906142797964137036204228664934380633104536207212530034594752⟩ ⟨false, 0⟩ ⟨false, 108969660155890871333083698208207232815795225623420179747627987201451474208⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1464_800 : bothSeg evalE (oGrid.idx 1464) (oGrid.dm 1464) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1464) oGrid.kl oGrid.kr 400 800 ⟨false, 108969660155890871333083698208207232815795225623420179747627987201451474208⟩ ⟨false, 0⟩ ⟨false, 169045995141065737719141866253030269813769875413215853019143313536018108304⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1464_1200 : bothSeg evalE (oGrid.idx 1464) (oGrid.dm 1464) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1464) oGrid.kl oGrid.kr 400 1200 ⟨false, 169045995141065737719141866253030269813769875413215853019143313536018108304⟩ ⟨false, 0⟩ ⟨false, 266480007234377191523867207038285766297172672083263567854520920306020391200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1464_1600 : bothSeg evalE (oGrid.idx 1464) (oGrid.dm 1464) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1464) oGrid.kl oGrid.kr 400 1600 ⟨false, 266480007234377191523867207038285766297172672083263567854520920306020391200⟩ ⟨false, 0⟩ ⟨false, 416175650097107618774429587442295428770195487813728894606959545633906695816⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1464_2000 : bothSeg evalE (oGrid.idx 1464) (oGrid.dm 1464) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1464) oGrid.kl oGrid.kr 400 2000 ⟨false, 416175650097107618774429587442295428770195487813728894606959545633906695816⟩ ⟨false, 0⟩ ⟨false, 616089694868060669334498542573385648304118639717568059119924904763712839334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1464_2400 : bothLoop evalE (oGrid.idx 1464) (oGrid.dm 1464) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1464) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 616089694868060669334498542573385648304118639717568059119924904763712839334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1464 : oGrid.row evalE 1464 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1464_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1464_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1464_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1464_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1464_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1464_2000).1 (bothLoop_sound b_1464_2400).1))))))

theorem n_row_1464 : nGrid.row evalE 1464 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1464_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1464_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1464_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1464_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1464_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1464_2000).2 (bothLoop_sound b_1464_2400).2))))))

theorem b_1465_0 : bothSeg evalE (oGrid.idx 1465) (oGrid.dm 1465) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1465) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 43572657228800743590264848619604486810297539818590163963913259995243371046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1465_400 : bothSeg evalE (oGrid.idx 1465) (oGrid.dm 1465) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1465) oGrid.kl oGrid.kr 400 400 ⟨false, 43572657228800743590264848619604486810297539818590163963913259995243371046⟩ ⟨false, 0⟩ ⟨false, 109762255475659953174703067380902626508865244366116899562668378905723279246⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1465_800 : bothSeg evalE (oGrid.idx 1465) (oGrid.dm 1465) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1465) oGrid.kl oGrid.kr 400 800 ⟨false, 109762255475659953174703067380902626508865244366116899562668378905723279246⟩ ⟨false, 0⟩ ⟨false, 169852780234890687171298425701178740097654304046234432587648772938429995380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1465_1200 : bothSeg evalE (oGrid.idx 1465) (oGrid.dm 1465) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1465) oGrid.kl oGrid.kr 400 1200 ⟨false, 169852780234890687171298425701178740097654304046234432587648772938429995380⟩ ⟨false, 0⟩ ⟨false, 267594142582884660190432625978091836670576612340333533039409995656441293992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1465_1600 : bothSeg evalE (oGrid.idx 1465) (oGrid.dm 1465) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1465) oGrid.kl oGrid.kr 400 1600 ⟨false, 267594142582884660190432625978091836670576612340333533039409995656441293992⟩ ⟨false, 0⟩ ⟨false, 417557438621933373838836675369395370964055115023507063646040187176284422346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1465_2000 : bothSeg evalE (oGrid.idx 1465) (oGrid.dm 1465) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1465) oGrid.kl oGrid.kr 400 2000 ⟨false, 417557438621933373838836675369395370964055115023507063646040187176284422346⟩ ⟨false, 0⟩ ⟨false, 617707845675404935535755498437283196031398368871768232040945207200079482386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1465_2400 : bothLoop evalE (oGrid.idx 1465) (oGrid.dm 1465) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1465) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 617707845675404935535755498437283196031398368871768232040945207200079482386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1465 : oGrid.row evalE 1465 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1465_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1465_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1465_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1465_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1465_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1465_2000).1 (bothLoop_sound b_1465_2400).1))))))

theorem n_row_1465 : nGrid.row evalE 1465 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1465_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1465_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1465_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1465_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1465_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1465_2000).2 (bothLoop_sound b_1465_2400).2))))))

theorem b_1466_0 : bothSeg evalE (oGrid.idx 1466) (oGrid.dm 1466) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1466) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 44040317866963531053531774454148959774302607697613929261177558540908527048⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1466_400 : bothSeg evalE (oGrid.idx 1466) (oGrid.dm 1466) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1466) oGrid.kl oGrid.kr 400 400 ⟨false, 44040317866963531053531774454148959774302607697613929261177558540908527048⟩ ⟨false, 0⟩ ⟨false, 110548828511695760701362481073148289314379686575541030890334394747823682650⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1466_800 : bothSeg evalE (oGrid.idx 1466) (oGrid.dm 1466) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1466) oGrid.kl oGrid.kr 400 800 ⟨false, 110548828511695760701362481073148289314379686575541030890334394747823682650⟩ ⟨false, 0⟩ ⟨false, 170657782206659800033178578877717222638043747844641505165809515714215723298⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1466_1200 : bothSeg evalE (oGrid.idx 1466) (oGrid.dm 1466) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1466) oGrid.kl oGrid.kr 400 1200 ⟨false, 170657782206659800033178578877717222638043747844641505165809515714215723298⟩ ⟨false, 0⟩ ⟨false, 268706475733033991428687188244253044524405344853986912229753165254876400992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1466_1600 : bothSeg evalE (oGrid.idx 1466) (oGrid.dm 1466) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1466) oGrid.kl oGrid.kr 400 1600 ⟨false, 268706475733033991428687188244253044524405344853986912229753165254876400992⟩ ⟨false, 0⟩ ⟨false, 418937440223854393928260982044604191382087763108295903189572512937983762706⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1466_2000 : bothSeg evalE (oGrid.idx 1466) (oGrid.dm 1466) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1466) oGrid.kl oGrid.kr 400 2000 ⟨false, 418937440223854393928260982044604191382087763108295903189572512937983762706⟩ ⟨false, 0⟩ ⟨false, 619324243236122537213630762878869139369132158413571761691120072113423176268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1466_2400 : bothLoop evalE (oGrid.idx 1466) (oGrid.dm 1466) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1466) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 619324243236122537213630762878869139369132158413571761691120072113423176268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1466 : oGrid.row evalE 1466 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1466_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1466_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1466_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1466_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1466_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1466_2000).1 (bothLoop_sound b_1466_2400).1))))))

theorem n_row_1466 : nGrid.row evalE 1466 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1466_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1466_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1466_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1466_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1466_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1466_2000).2 (bothLoop_sound b_1466_2400).2))))))

theorem b_1467_0 : bothSeg evalE (oGrid.idx 1467) (oGrid.dm 1467) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1467) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 44509976816158850611421632705195059526695693284690485934905022386230994982⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1467_400 : bothSeg evalE (oGrid.idx 1467) (oGrid.dm 1467) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1467) oGrid.kl oGrid.kr 400 400 ⟨false, 44509976816158850611421632705195059526695693284690485934905022386230994982⟩ ⟨false, 0⟩ ⟨false, 111329198432333250968298039051551618888219959008407832570838376737112687602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1467_800 : bothSeg evalE (oGrid.idx 1467) (oGrid.dm 1467) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1467) oGrid.kl oGrid.kr 400 800 ⟨false, 111329198432333250968298039051551618888219959008407832570838376737112687602⟩ ⟨false, 0⟩ ⟨false, 171460938975393563565176627681611182632059189112159735373014888083133651298⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1467_1200 : bothSeg evalE (oGrid.idx 1467) (oGrid.dm 1467) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1467) oGrid.kl oGrid.kr 400 1200 ⟨false, 171460938975393563565176627681611182632059189112159735373014888083133651298⟩ ⟨false, 0⟩ ⟨false, 269816944568969279061192592084803039055329514775837514107508314576610947322⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1467_1600 : bothSeg evalE (oGrid.idx 1467) (oGrid.dm 1467) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1467) oGrid.kl oGrid.kr 400 1600 ⟨false, 269816944568969279061192592084803039055329514775837514107508314576610947322⟩ ⟨false, 0⟩ ⟨false, 420315592725277745979573859611649228971627569252040997333981379983093373012⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1467_2000 : bothSeg evalE (oGrid.idx 1467) (oGrid.dm 1467) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1467) oGrid.kl oGrid.kr 400 2000 ⟨false, 420315592725277745979573859611649228971627569252040997333981379983093373012⟩ ⟨false, 0⟩ ⟨false, 620938825309657933598989097604947290517842359149390092906086418228003112044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1467_2400 : bothLoop evalE (oGrid.idx 1467) (oGrid.dm 1467) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1467) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 620938825309657933598989097604947290517842359149390092906086418228003112044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1467 : oGrid.row evalE 1467 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1467_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1467_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1467_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1467_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1467_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1467_2000).1 (bothLoop_sound b_1467_2400).1))))))

theorem n_row_1467 : nGrid.row evalE 1467 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1467_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1467_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1467_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1467_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1467_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1467_2000).2 (bothLoop_sound b_1467_2400).2))))))

theorem b_1468_0 : bothSeg evalE (oGrid.idx 1468) (oGrid.dm 1468) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1468) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 44981662897400458934763799790328468851312931971116981187720640936658572290⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1468_400 : bothSeg evalE (oGrid.idx 1468) (oGrid.dm 1468) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1468) oGrid.kl oGrid.kr 400 400 ⟨false, 44981662897400458934763799790328468851312931971116981187720640936658572290⟩ ⟨false, 0⟩ ⟨false, 112103212248373103456982673684865534780157573245588444412686409046023661940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1468_800 : bothSeg evalE (oGrid.idx 1468) (oGrid.dm 1468) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1468) oGrid.kl oGrid.kr 400 800 ⟨false, 112103212248373103456982673684865534780157573245588444412686409046023661940⟩ ⟨false, 0⟩ ⟨false, 172262206986297526247148330540727764638965198884200466132657233776707704476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1468_1200 : bothSeg evalE (oGrid.idx 1468) (oGrid.dm 1468) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1468) oGrid.kl oGrid.kr 400 1200 ⟨false, 172262206986297526247148330540727764638965198884200466132657233776707704476⟩ ⟨false, 0⟩ ⟨false, 270925505501130907543815248242077106208248067340752309095091851991902181710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1468_1600 : bothSeg evalE (oGrid.idx 1468) (oGrid.dm 1468) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1468) oGrid.kl oGrid.kr 400 1600 ⟨false, 270925505501130907543815248242077106208248067340752309095091851991902181710⟩ ⟨false, 0⟩ ⟨false, 421691852475020680208264953580806349243623083045914249627671787048207217294⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1468_2000 : bothSeg evalE (oGrid.idx 1468) (oGrid.dm 1468) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1468) oGrid.kl oGrid.kr 400 2000 ⟨false, 421691852475020680208264953580806349243623083045914249627671787048207217294⟩ ⟨false, 0⟩ ⟨false, 622551548181947734867479739843621817153983758500717476145662668128111817938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1468_2400 : bothLoop evalE (oGrid.idx 1468) (oGrid.dm 1468) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1468) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 622551548181947734867479739843621817153983758500717476145662668128111817938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1468 : oGrid.row evalE 1468 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1468_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1468_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1468_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1468_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1468_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1468_2000).1 (bothLoop_sound b_1468_2400).1))))))

theorem n_row_1468 : nGrid.row evalE 1468 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1468_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1468_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1468_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1468_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1468_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1468_2000).2 (bothLoop_sound b_1468_2400).2))))))

theorem b_1469_0 : bothSeg evalE (oGrid.idx 1469) (oGrid.dm 1469) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1469) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 45455396001730384973425415391792687783805705435446731337082966662729483558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1469_400 : bothSeg evalE (oGrid.idx 1469) (oGrid.dm 1469) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1469) oGrid.kl oGrid.kr 400 400 ⟨false, 45455396001730384973425415391792687783805705435446731337082966662729483558⟩ ⟨false, 0⟩ ⟨false, 112870703527986583411271005156326020822388196010163173171840495421793520138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1469_800 : bothSeg evalE (oGrid.idx 1469) (oGrid.dm 1469) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1469) oGrid.kl oGrid.kr 400 800 ⟨false, 112870703527986583411271005156326020822388196010163173171840495421793520138⟩ ⟨false, 0⟩ ⟨false, 173061528645202811687556506769763533925404355855035465196309235069259287954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1469_1200 : bothSeg evalE (oGrid.idx 1469) (oGrid.dm 1469) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1469) oGrid.kl oGrid.kr 400 1200 ⟨false, 173061528645202811687556506769763533925404355855035465196309235069259287954⟩ ⟨false, 0⟩ ⟨false, 272032100900695808636412536081560295048129561104285936722243308108931335118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1469_1600 : bothSeg evalE (oGrid.idx 1469) (oGrid.dm 1469) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1469) oGrid.kl oGrid.kr 400 1600 ⟨false, 272032100900695808636412536081560295048129561104285936722243308108931335118⟩ ⟨false, 0⟩ ⟨false, 423066161782750707021780454081610402079080767427661040343773044921501923432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1469_2000 : bothSeg evalE (oGrid.idx 1469) (oGrid.dm 1469) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1469) oGrid.kl oGrid.kr 400 2000 ⟨false, 423066161782750707021780454081610402079080767427661040343773044921501923432⟩ ⟨false, 0⟩ ⟨false, 624162354099860699250278228371465012292924309888773821423148673418105099008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1469_2400 : bothLoop evalE (oGrid.idx 1469) (oGrid.dm 1469) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1469) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 624162354099860699250278228371465012292924309888773821423148673418105099008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1469 : oGrid.row evalE 1469 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1469_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1469_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1469_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1469_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1469_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1469_2000).1 (bothLoop_sound b_1469_2400).1))))))

theorem n_row_1469 : nGrid.row evalE 1469 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1469_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1469_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1469_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1469_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1469_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1469_2000).2 (bothLoop_sound b_1469_2400).2))))))

theorem b_1470_0 : bothSeg evalE (oGrid.idx 1470) (oGrid.dm 1470) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1470) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 45931196618497790089209303480693357131860540877622271792819009914835252446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1470_400 : bothSeg evalE (oGrid.idx 1470) (oGrid.dm 1470) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1470) oGrid.kl oGrid.kr 400 400 ⟨false, 45931196618497790089209303480693357131860540877622271792819009914835252446⟩ ⟨false, 0⟩ ⟨false, 113631521246788607228329360436813095822346592469341714581640112787690904290⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1470_800 : bothSeg evalE (oGrid.idx 1470) (oGrid.dm 1470) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1470) oGrid.kl oGrid.kr 400 800 ⟨false, 113631521246788607228329360436813095822346592469341714581640112787690904290⟩ ⟨false, 0⟩ ⟨false, 173858852997077711987611351449561982918657307814836238297080921812745243752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1470_1200 : bothSeg evalE (oGrid.idx 1470) (oGrid.dm 1470) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1470) oGrid.kl oGrid.kr 400 1200 ⟨false, 173858852997077711987611351449561982918657307814836238297080921812745243752⟩ ⟨false, 0⟩ ⟨false, 273136679778088798081163154751548873227670236025221330174630071866204053602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1470_1600 : bothSeg evalE (oGrid.idx 1470) (oGrid.dm 1470) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1470) oGrid.kl oGrid.kr 400 1600 ⟨false, 273136679778088798081163154751548873227670236025221330174630071866204053602⟩ ⟨false, 0⟩ ⟨false, 424438469597496754171371876294473382824004258182423730281254560243351118574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1470_2000 : bothSeg evalE (oGrid.idx 1470) (oGrid.dm 1470) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1470) oGrid.kl oGrid.kr 400 2000 ⟨false, 424438469597496754171371876294473382824004258182423730281254560243351118574⟩ ⟨false, 0⟩ ⟨false, 625771191949708810388658934705915117645285729327859076850528799952667550694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1470_2400 : bothLoop evalE (oGrid.idx 1470) (oGrid.dm 1470) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1470) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 625771191949708810388658934705915117645285729327859076850528799952667550694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1470 : oGrid.row evalE 1470 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1470_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1470_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1470_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1470_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1470_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1470_2000).1 (bothLoop_sound b_1470_2400).1))))))

theorem n_row_1470 : nGrid.row evalE 1470 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1470_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1470_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1470_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1470_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1470_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1470_2000).2 (bothLoop_sound b_1470_2400).2))))))

theorem b_1471_0 : bothSeg evalE (oGrid.idx 1471) (oGrid.dm 1471) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1471) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 46409074124481709747798618662048542858210884862002174518463985156618606210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1471_400 : bothSeg evalE (oGrid.idx 1471) (oGrid.dm 1471) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1471) oGrid.kl oGrid.kr 400 400 ⟨false, 46409074124481709747798618662048542858210884862002174518463985156618606210⟩ ⟨false, 0⟩ ⟨false, 114385480385600340868475224303901032130537734052662140455207567276697337668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1471_800 : bothSeg evalE (oGrid.idx 1471) (oGrid.dm 1471) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1471) oGrid.kl oGrid.kr 400 800 ⟨false, 114385480385600340868475224303901032130537734052662140455207567276697337668⟩ ⟨false, 0⟩ ⟨false, 174654091110468453004012858585492597792563228316030638372009647228647661808⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1471_1200 : bothSeg evalE (oGrid.idx 1471) (oGrid.dm 1471) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1471) oGrid.kl oGrid.kr 400 1200 ⟨false, 174654091110468453004012858585492597792563228316030638372009647228647661808⟩ ⟨false, 0⟩ ⟨false, 274239153167423084731043014457701981910242824476082469191637367089863822888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1471_1600 : bothSeg evalE (oGrid.idx 1471) (oGrid.dm 1471) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1471) oGrid.kl oGrid.kr 400 1600 ⟨false, 274239153167423084731043014457701981910242824476082469191637367089863822888⟩ ⟨false, 0⟩ ⟨false, 425808686892089496584857576808722424057968442306853858604654940110556562600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1471_2000 : bothSeg evalE (oGrid.idx 1471) (oGrid.dm 1471) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1471) oGrid.kl oGrid.kr 400 2000 ⟨false, 425808686892089496584857576808722424057968442306853858604654940110556562600⟩ ⟨false, 0⟩ ⟨false, 627377972641687527375081833398958413566756760376491421704926727514623561994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1471_2400 : bothLoop evalE (oGrid.idx 1471) (oGrid.dm 1471) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1471) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 627377972641687527375081833398958413566756760376491421704926727514623561994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1471 : oGrid.row evalE 1471 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1471_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1471_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1471_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1471_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1471_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1471_2000).1 (bothLoop_sound b_1471_2400).1))))))

theorem n_row_1471 : nGrid.row evalE 1471 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1471_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1471_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1471_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1471_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1471_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1471_2000).2 (bothLoop_sound b_1471_2400).2))))))

theorem b_1472_0 : bothSeg evalE (oGrid.idx 1472) (oGrid.dm 1472) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1472) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 46889036486751654584085063911026023287396741596834590672023382843845152172⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1472_400 : bothSeg evalE (oGrid.idx 1472) (oGrid.dm 1472) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1472) oGrid.kl oGrid.kr 400 400 ⟨false, 46889036486751654584085063911026023287396741596834590672023382843845152172⟩ ⟨false, 0⟩ ⟨false, 115132454849506718574453954191199172367204357981088732779063277140611877536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1472_800 : bothSeg evalE (oGrid.idx 1472) (oGrid.dm 1472) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1472) oGrid.kl oGrid.kr 400 800 ⟨false, 115132454849506718574453954191199172367204357981088732779063277140611877536⟩ ⟨false, 0⟩ ⟨false, 175447214623480190517507153269552115885540729600243057225942382806974472074⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1472_1200 : bothSeg evalE (oGrid.idx 1472) (oGrid.dm 1472) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1472) oGrid.kl oGrid.kr 400 1200 ⟨false, 175447214623480190517507153269552115885540729600243057225942382806974472074⟩ ⟨false, 0⟩ ⟨false, 275339492672481011134554334166689146088411035794074735100870620660280696288⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1472_1600 : bothSeg evalE (oGrid.idx 1472) (oGrid.dm 1472) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1472) oGrid.kl oGrid.kr 400 1600 ⟨false, 275339492672481011134554334166689146088411035794074735100870620660280696288⟩ ⟨false, 0⟩ ⟨false, 427176785209141917886304545476433531062671777373827656375261426414704473916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1472_2000 : bothSeg evalE (oGrid.idx 1472) (oGrid.dm 1472) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1472) oGrid.kl oGrid.kr 400 2000 ⟨false, 427176785209141917886304545476433531062671777373827656375261426414704473916⟩ ⟨false, 0⟩ ⟨false, 628982667655856266487081294126243452333760688148979544904359141001343685512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1472_2400 : bothLoop evalE (oGrid.idx 1472) (oGrid.dm 1472) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1472) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 628982667655856266487081294126243452333760688148979544904359141001343685512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1472 : oGrid.row evalE 1472 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1472_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1472_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1472_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1472_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1472_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1472_2000).1 (bothLoop_sound b_1472_2400).1))))))

theorem n_row_1472 : nGrid.row evalE 1472 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1472_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1472_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1472_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1472_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1472_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1472_2000).2 (bothLoop_sound b_1472_2400).2))))))

theorem b_1473_0 : bothSeg evalE (oGrid.idx 1473) (oGrid.dm 1473) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1473) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 47371084606775353470949213603576597516118868667282291416956192866221306498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1473_400 : bothSeg evalE (oGrid.idx 1473) (oGrid.dm 1473) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1473) oGrid.kl oGrid.kr 400 400 ⟨false, 47371084606775353470949213603576597516118868667282291416956192866221306498⟩ ⟨false, 0⟩ ⟨false, 115872252397284560458376171711091635035250601378582283852123229257924453302⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1473_800 : bothSeg evalE (oGrid.idx 1473) (oGrid.dm 1473) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1473) oGrid.kl oGrid.kr 400 800 ⟨false, 115872252397284560458376171711091635035250601378582283852123229257924453302⟩ ⟨false, 0⟩ ⟨false, 176238113071014778048535263954474342269479952889697156644926317165849753920⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1473_1200 : bothSeg evalE (oGrid.idx 1473) (oGrid.dm 1473) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1473) oGrid.kl oGrid.kr 400 1200 ⟨false, 176238113071014778048535263954474342269479952889697156644926317165849753920⟩ ⟨false, 0⟩ ⟨false, 276437587793951566316884159886602524099622474414668084492417363900261216076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1473_1600 : bothSeg evalE (oGrid.idx 1473) (oGrid.dm 1473) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1473) oGrid.kl oGrid.kr 400 1600 ⟨false, 276437587793951566316884159886602524099622474414668084492417363900261216076⟩ ⟨false, 0⟩ ⟨false, 428542653988286644342705676779345668326716495209337437019587784136336351390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1473_2000 : bothSeg evalE (oGrid.idx 1473) (oGrid.dm 1473) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1473) oGrid.kl oGrid.kr 400 2000 ⟨false, 428542653988286644342705676779345668326716495209337437019587784136336351390⟩ ⟨false, 0⟩ ⟨false, 630585166369375655354311261434180322902220683499600146441564005139931409492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1473_2400 : bothLoop evalE (oGrid.idx 1473) (oGrid.dm 1473) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1473) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 630585166369375655354311261434180322902220683499600146441564005139931409492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1473 : oGrid.row evalE 1473 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1473_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1473_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1473_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1473_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1473_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1473_2000).1 (bothLoop_sound b_1473_2400).1))))))

theorem n_row_1473 : nGrid.row evalE 1473 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1473_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1473_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1473_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1473_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1473_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1473_2000).2 (bothLoop_sound b_1473_2400).2))))))

theorem b_1474_0 : bothSeg evalE (oGrid.idx 1474) (oGrid.dm 1474) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1474) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 47855216378757211121869598295957429187915293271632296402683538350223227138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1474_400 : bothSeg evalE (oGrid.idx 1474) (oGrid.dm 1474) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1474) oGrid.kl oGrid.kr 400 400 ⟨false, 47855216378757211121869598295957429187915293271632296402683538350223227138⟩ ⟨false, 0⟩ ⟨false, 116604752068020107514967385430090073251770838944947346355059481791603770686⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1474_800 : bothSeg evalE (oGrid.idx 1474) (oGrid.dm 1474) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1474) oGrid.kl oGrid.kr 400 800 ⟨false, 116604752068020107514967385430090073251770838944947346355059481791603770686⟩ ⟨false, 0⟩ ⟨false, 177026749770113682340859511120964478151545906555533474977351034171069151280⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1474_1200 : bothSeg evalE (oGrid.idx 1474) (oGrid.dm 1474) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1474) oGrid.kl oGrid.kr 400 1200 ⟨false, 177026749770113682340859511120964478151545906555533474977351034171069151280⟩ ⟨false, 0⟩ ⟨false, 277533401814773046777276979467424553678257680973771386719471715761284593708⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1474_1600 : bothSeg evalE (oGrid.idx 1474) (oGrid.dm 1474) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1474) oGrid.kl oGrid.kr 400 1600 ⟨false, 277533401814773046777276979467424553678257680973771386719471715761284593708⟩ ⟨false, 0⟩ ⟨false, 429906256451518427257335308140029999027080042239868940170774222434560778312⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1474_2000 : bothSeg evalE (oGrid.idx 1474) (oGrid.dm 1474) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1474) oGrid.kl oGrid.kr 400 2000 ⟨false, 429906256451518427257335308140029999027080042239868940170774222434560778312⟩ ⟨false, 0⟩ ⟨false, 632185431941849935578707692921809129950607386260057100580977133596586026386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1474_2400 : bothLoop evalE (oGrid.idx 1474) (oGrid.dm 1474) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1474) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 632185431941849935578707692921809129950607386260057100580977133596586026386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1474 : oGrid.row evalE 1474 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1474_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1474_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1474_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1474_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1474_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1474_2000).1 (bothLoop_sound b_1474_2400).1))))))

theorem n_row_1474 : nGrid.row evalE 1474 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1474_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1474_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1474_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1474_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1474_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1474_2000).2 (bothLoop_sound b_1474_2400).2))))))

theorem b_1475_0 : bothSeg evalE (oGrid.idx 1475) (oGrid.dm 1475) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1475) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 48341417937332352262247899942942952236829676547381647435416125323215015278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1475_400 : bothSeg evalE (oGrid.idx 1475) (oGrid.dm 1475) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1475) oGrid.kl oGrid.kr 400 400 ⟨false, 48341417937332352262247899942942952236829676547381647435416125323215015278⟩ ⟨false, 0⟩ ⟨false, 117329777914648905107992468875833891403830348272973982203505896569709439162⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1475_800 : bothSeg evalE (oGrid.idx 1475) (oGrid.dm 1475) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1475) oGrid.kl oGrid.kr 400 800 ⟨false, 117329777914648905107992468875833891403830348272973982203505896569709439162⟩ ⟨false, 0⟩ ⟨false, 177813025973536845123393016183836600660657929896708978349026600323155611072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1475_1200 : bothSeg evalE (oGrid.idx 1475) (oGrid.dm 1475) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1475) oGrid.kl oGrid.kr 400 1200 ⟨false, 177813025973536845123393016183836600660657929896708978349026600323155611072⟩ ⟨false, 0⟩ ⟨false, 278626835953711664311748253211610127492241143875731108737882109329017437954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1475_1600 : bothSeg evalE (oGrid.idx 1475) (oGrid.dm 1475) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1475) oGrid.kl oGrid.kr 400 1600 ⟨false, 278626835953711664311748253211610127492241143875731108737882109329017437954⟩ ⟨false, 0⟩ ⟨false, 431267493756772572418807082558517167491249321538399177022920837066265811640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1475_2000 : bothSeg evalE (oGrid.idx 1475) (oGrid.dm 1475) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1475) oGrid.kl oGrid.kr 400 2000 ⟨false, 431267493756772572418807082558517167491249321538399177022920837066265811640⟩ ⟨false, 0⟩ ⟨false, 633783365468905312417069320860009880459677260032002263713336899954334438262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1475_2400 : bothLoop evalE (oGrid.idx 1475) (oGrid.dm 1475) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1475) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 633783365468905312417069320860009880459677260032002263713336899954334438262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1475 : oGrid.row evalE 1475 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1475_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1475_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1475_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1475_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1475_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1475_2000).1 (bothLoop_sound b_1475_2400).1))))))

theorem n_row_1475 : nGrid.row evalE 1475 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1475_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1475_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1475_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1475_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1475_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1475_2000).2 (bothLoop_sound b_1475_2400).2))))))

theorem b_1476_0 : bothSeg evalE (oGrid.idx 1476) (oGrid.dm 1476) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1476) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 48829673409949708126615591305348713011561258008420055757095154892727928482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1476_400 : bothSeg evalE (oGrid.idx 1476) (oGrid.dm 1476) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1476) oGrid.kl oGrid.kr 400 400 ⟨false, 48829673409949708126615591305348713011561258008420055757095154892727928482⟩ ⟨false, 0⟩ ⟨false, 118047189592790822535195807067360819148638468994457717854741077461611374576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1476_800 : bothSeg evalE (oGrid.idx 1476) (oGrid.dm 1476) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1476) oGrid.kl oGrid.kr 400 800 ⟨false, 118047189592790822535195807067360819148638468994457717854741077461611374576⟩ ⟨false, 0⟩ ⟨false, 178596870868030035527033336789122518152710483656993179278085694112099408112⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1476_1200 : bothSeg evalE (oGrid.idx 1476) (oGrid.dm 1476) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1476) oGrid.kl oGrid.kr 400 1200 ⟨false, 178596870868030035527033336789122518152710483656993179278085694112099408112⟩ ⟨false, 0⟩ ⟨false, 279717819363628645036842996819011476043298127811123129429418228936217223022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1476_1600 : bothSeg evalE (oGrid.idx 1476) (oGrid.dm 1476) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1476) oGrid.kl oGrid.kr 400 1600 ⟨false, 279717819363628645036842996819011476043298127811123129429418228936217223022⟩ ⟨false, 0⟩ ⟨false, 432626294996191860981434641759229203605338886017796515869678501733279459178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1476_2000 : bothSeg evalE (oGrid.idx 1476) (oGrid.dm 1476) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1476) oGrid.kl oGrid.kr 400 2000 ⟨false, 432626294996191860981434641759229203605338886017796515869678501733279459178⟩ ⟨false, 0⟩ ⟨false, 635378895980456795901933178101018181469263158627801525901235908836620685288⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1476_2400 : bothLoop evalE (oGrid.idx 1476) (oGrid.dm 1476) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1476) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 635378895980456795901933178101018181469263158627801525901235908836620685288⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1476 : oGrid.row evalE 1476 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1476_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1476_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1476_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1476_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1476_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1476_2000).1 (bothLoop_sound b_1476_2400).1))))))

theorem n_row_1476 : nGrid.row evalE 1476 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1476_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1476_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1476_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1476_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1476_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1476_2000).2 (bothLoop_sound b_1476_2400).2))))))

theorem b_1477_0 : bothSeg evalE (oGrid.idx 1477) (oGrid.dm 1477) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1477) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 49319957893123217031016661841469778469797362348621651433319926606162934978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1477_400 : bothSeg evalE (oGrid.idx 1477) (oGrid.dm 1477) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1477) oGrid.kl oGrid.kr 400 400 ⟨false, 49319957893123217031016661841469778469797362348621651433319926606162934978⟩ ⟨false, 0⟩ ⟨false, 118756825215443321352605958127242690474435613417844611584816513911488758616⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1477_800 : bothSeg evalE (oGrid.idx 1477) (oGrid.dm 1477) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1477) oGrid.kl oGrid.kr 400 800 ⟨false, 118756825215443321352605958127242690474435613417844611584816513911488758616⟩ ⟨false, 0⟩ ⟨false, 179378192596063005438695280216448694040867939757403757133928351125337875122⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1477_1200 : bothSeg evalE (oGrid.idx 1477) (oGrid.dm 1477) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1477) oGrid.kl oGrid.kr 400 1200 ⟨false, 179378192596063005438695280216448694040867939757403757133928351125337875122⟩ ⟨false, 0⟩ ⟨false, 280806260153218131895539412812816301474533549993830214721918522074353646616⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1477_1600 : bothSeg evalE (oGrid.idx 1477) (oGrid.dm 1477) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1477) oGrid.kl oGrid.kr 400 1600 ⟨false, 280806260153218131895539412812816301474533549993830214721918522074353646616⟩ ⟨false, 0⟩ ⟨false, 433982568217864274057890652172474055837656271986390317761102743158649734742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1477_2000 : bothSeg evalE (oGrid.idx 1477) (oGrid.dm 1477) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1477) oGrid.kl oGrid.kr 400 2000 ⟨false, 433982568217864274057890652172474055837656271986390317761102743158649734742⟩ ⟨false, 0⟩ ⟨false, 636971931462445845682015255083925336424934640260891310074707910013813667352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1477_2400 : bothLoop evalE (oGrid.idx 1477) (oGrid.dm 1477) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1477) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 636971931462445845682015255083925336424934640260891310074707910013813667352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1477 : oGrid.row evalE 1477 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1477_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1477_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1477_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1477_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1477_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1477_2000).1 (bothLoop_sound b_1477_2400).1))))))

theorem n_row_1477 : nGrid.row evalE 1477 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1477_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1477_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1477_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1477_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1477_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1477_2000).2 (bothLoop_sound b_1477_2400).2))))))

theorem b_1478_0 : bothSeg evalE (oGrid.idx 1478) (oGrid.dm 1478) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1478) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 49812238158936665284539580116070727684050487773791868529415932485370917486⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1478_400 : bothSeg evalE (oGrid.idx 1478) (oGrid.dm 1478) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1478) oGrid.kl oGrid.kr 400 400 ⟨false, 49812238158936665284539580116070727684050487773791868529415932485370917486⟩ ⟨false, 0⟩ ⟨false, 119458536301796767604252750835306441971029216280077873517959840401144689424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1478_800 : bothSeg evalE (oGrid.idx 1478) (oGrid.dm 1478) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1478) oGrid.kl oGrid.kr 400 800 ⟨false, 119458536301796767604252750835306441971029216280077873517959840401144689424⟩ ⟨false, 0⟩ ⟨false, 180156895878175739272695518293205572180792063233793781774550615412090956608⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1478_1200 : bothSeg evalE (oGrid.idx 1478) (oGrid.dm 1478) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1478) oGrid.kl oGrid.kr 400 1200 ⟨false, 180156895878175739272695518293205572180792063233793781774550615412090956608⟩ ⟨false, 0⟩ ⟨false, 281892063009353182124356951464606558590631117960567455137127085954610830312⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1478_1600 : bothSeg evalE (oGrid.idx 1478) (oGrid.dm 1478) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1478) oGrid.kl oGrid.kr 400 1600 ⟨false, 281892063009353182124356951464606558590631117960567455137127085954610830312⟩ ⟨false, 0⟩ ⟨false, 435336218048168812503118192391995868443668184482895188281796540568436596316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1478_2000 : bothSeg evalE (oGrid.idx 1478) (oGrid.dm 1478) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1478) oGrid.kl oGrid.kr 400 2000 ⟨false, 435336218048168812503118192391995868443668184482895188281796540568436596316⟩ ⟨false, 0⟩ ⟨false, 638562376479186111061444113634495052145708123848535686230843324175269990840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1478_2400 : bothLoop evalE (oGrid.idx 1478) (oGrid.dm 1478) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1478) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 638562376479186111061444113634495052145708123848535686230843324175269990840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1478 : oGrid.row evalE 1478 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1478_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1478_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1478_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1478_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1478_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1478_2000).1 (bothLoop_sound b_1478_2400).1))))))

theorem n_row_1478 : nGrid.row evalE 1478 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1478_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1478_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1478_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1478_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1478_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1478_2000).2 (bothLoop_sound b_1478_2400).2))))))

theorem b_1479_0 : bothSeg evalE (oGrid.idx 1479) (oGrid.dm 1479) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1479) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 50306470612672812837029984006998814533381875182116004744384280490399020084⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1479_400 : bothSeg evalE (oGrid.idx 1479) (oGrid.dm 1479) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1479) oGrid.kl oGrid.kr 400 400 ⟨false, 50306470612672812837029984006998814533381875182116004744384280490399020084⟩ ⟨false, 0⟩ ⟨false, 120152154169666934876344612373310664018194575600357879511958353610517871508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1479_800 : bothSeg evalE (oGrid.idx 1479) (oGrid.dm 1479) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1479) oGrid.kl oGrid.kr 400 800 ⟨false, 120152154169666934876344612373310664018194575600357879511958353610517871508⟩ ⟨false, 0⟩ ⟨false, 180932873105787243361289353900658409785945781274556828487302901908581732774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1479_1200 : bothSeg evalE (oGrid.idx 1479) (oGrid.dm 1479) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1479) oGrid.kl oGrid.kr 400 1200 ⟨false, 180932873105787243361289353900658409785945781274556828487302901908581732774⟩ ⟨false, 0⟩ ⟨false, 282975120289894304882377721195235079028783265903145112068376808946271985536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1479_1600 : bothSeg evalE (oGrid.idx 1479) (oGrid.dm 1479) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1479) oGrid.kl oGrid.kr 400 1600 ⟨false, 282975120289894304882377721195235079028783265903145112068376808946271985536⟩ ⟨false, 0⟩ ⟨false, 436687136784583857090097216064681456742084694231737879447154125480148035908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1479_2000 : bothSeg evalE (oGrid.idx 1479) (oGrid.dm 1479) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1479) oGrid.kl oGrid.kr 400 2000 ⟨false, 436687136784583857090097216064681456742084694231737879447154125480148035908⟩ ⟨false, 0⟩ ⟨false, 640150123266171711438662903905328100883839181941166232624711765203148105516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1479_2400 : bothLoop evalE (oGrid.idx 1479) (oGrid.dm 1479) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1479) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 640150123266171711438662903905328100883839181941166232624711765203148105516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1479 : oGrid.row evalE 1479 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1479_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1479_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1479_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1479_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1479_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1479_2000).1 (bothLoop_sound b_1479_2400).1))))))

theorem n_row_1479 : nGrid.row evalE 1479 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1479_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1479_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1479_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1479_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1479_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1479_2000).2 (bothLoop_sound b_1479_2400).2))))))

theorem b_1480_0 : bothSeg evalE (oGrid.idx 1480) (oGrid.dm 1480) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1480) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 50802612326296249463377134547750022689872412821451670857432508716707031750⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1480_400 : bothSeg evalE (oGrid.idx 1480) (oGrid.dm 1480) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1480) oGrid.kl oGrid.kr 400 400 ⟨false, 50802612326296249463377134547750022689872412821451670857432508716707031750⟩ ⟨false, 0⟩ ⟨false, 120837552245970059323806043335145367170268275497996873904096239303078356658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1480_800 : bothSeg evalE (oGrid.idx 1480) (oGrid.dm 1480) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1480) oGrid.kl oGrid.kr 400 800 ⟨false, 120837552245970059323806043335145367170268275497996873904096239303078356658⟩ ⟨false, 0⟩ ⟨false, 181706040869838355827604658641663793282425599379293079140309387949823534510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1480_1200 : bothSeg evalE (oGrid.idx 1480) (oGrid.dm 1480) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1480) oGrid.kl oGrid.kr 400 1200 ⟨false, 181706040869838355827604658641663793282425599379293079140309387949823534510⟩ ⟨false, 0⟩ ⟨false, 284055348552332019904336649295312738109656712768109944727806414399082965624⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1480_1600 : bothSeg evalE (oGrid.idx 1480) (oGrid.dm 1480) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1480) oGrid.kl oGrid.kr 400 1600 ⟨false, 284055348552332019904336649295312738109656712768109944727806414399082965624⟩ ⟨false, 0⟩ ⟨false, 438035240924329549939514436283301048703501191088967117061258431752942269126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1480_2000 : bothSeg evalE (oGrid.idx 1480) (oGrid.dm 1480) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1480) oGrid.kl oGrid.kr 400 2000 ⟨false, 438035240924329549939514436283301048703501191088967117061258431752942269126⟩ ⟨false, 0⟩ ⟨false, 641735088258719538007319801003502550310358437938871237001666736035227350804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1480_2400 : bothLoop evalE (oGrid.idx 1480) (oGrid.dm 1480) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1480) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 641735088258719538007319801003502550310358437938871237001666736035227350804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1480 : oGrid.row evalE 1480 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1480_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1480_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1480_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1480_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1480_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1480_2000).1 (bothLoop_sound b_1480_2400).1))))))

theorem n_row_1480 : nGrid.row evalE 1480 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1480_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1480_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1480_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1480_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1480_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1480_2000).2 (bothLoop_sound b_1480_2400).2))))))

theorem b_1481_0 : bothSeg evalE (oGrid.idx 1481) (oGrid.dm 1481) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1481) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 51300605737551304461968002996089247226657779610955701268365834649227989282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1481_400 : bothSeg evalE (oGrid.idx 1481) (oGrid.dm 1481) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1481) oGrid.kl oGrid.kr 400 400 ⟨false, 51300605737551304461968002996089247226657779610955701268365834649227989282⟩ ⟨false, 0⟩ ⟨false, 121514581053518176465452719767966388147992051083389885706177826246702022948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1481_800 : bothSeg evalE (oGrid.idx 1481) (oGrid.dm 1481) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1481) oGrid.kl oGrid.kr 400 800 ⟨false, 121514581053518176465452719767966388147992051083389885706177826246702022948⟩ ⟨false, 0⟩ ⟨false, 182476297044558422430328031483742170206325669940653370699093782210582481130⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1481_1200 : bothSeg evalE (oGrid.idx 1481) (oGrid.dm 1481) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1481) oGrid.kl oGrid.kr 400 1200 ⟨false, 182476297044558422430328031483742170206325669940653370699093782210582481130⟩ ⟨false, 0⟩ ⟨false, 285132645637553282666047634510339003208911001018776909533542722337469759702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1481_1600 : bothSeg evalE (oGrid.idx 1481) (oGrid.dm 1481) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1481) oGrid.kl oGrid.kr 400 1600 ⟨false, 285132645637553282666047634510339003208911001018776909533542722337469759702⟩ ⟨false, 0⟩ ⟨false, 439380428248134042691495974375248543318609893350355883009183265105659364596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1481_2000 : bothSeg evalE (oGrid.idx 1481) (oGrid.dm 1481) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1481) oGrid.kl oGrid.kr 400 2000 ⟨false, 439380428248134042691495974375248543318609893350355883009183265105659364596⟩ ⟨false, 0⟩ ⟨false, 643317169175735422207576815509999571088228036886740876972350207382241449042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1481_2400 : bothLoop evalE (oGrid.idx 1481) (oGrid.dm 1481) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1481) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 643317169175735422207576815509999571088228036886740876972350207382241449042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1481 : oGrid.row evalE 1481 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1481_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1481_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1481_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1481_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1481_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1481_2000).1 (bothLoop_sound b_1481_2400).1))))))

theorem n_row_1481 : nGrid.row evalE 1481 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1481_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1481_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1481_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1481_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1481_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1481_2000).2 (bothLoop_sound b_1481_2400).2))))))

theorem b_1482_0 : bothSeg evalE (oGrid.idx 1482) (oGrid.dm 1482) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1482) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 51800382891358480422500185703447833778734030298799080169219919222879591016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1482_400 : bothSeg evalE (oGrid.idx 1482) (oGrid.dm 1482) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1482) oGrid.kl oGrid.kr 400 400 ⟨false, 51800382891358480422500185703447833778734030298799080169219919222879591016⟩ ⟨false, 0⟩ ⟨false, 122183080507095270239912723584134764628637502846457312462911526731998475948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1482_800 : bothSeg evalE (oGrid.idx 1482) (oGrid.dm 1482) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1482) oGrid.kl oGrid.kr 400 800 ⟨false, 122183080507095270239912723584134764628637502846457312462911526731998475948⟩ ⟨false, 0⟩ ⟨false, 183243516192434187478338606316125937383809684791030951759476572782541847200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1482_1200 : bothSeg evalE (oGrid.idx 1482) (oGrid.dm 1482) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1482) oGrid.kl oGrid.kr 400 1200 ⟨false, 183243516192434187478338606316125937383809684791030951759476572782541847200⟩ ⟨false, 0⟩ ⟨false, 286206886074810125159275120684161651128807424687241842763884244930082059032⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1482_1600 : bothSeg evalE (oGrid.idx 1482) (oGrid.dm 1482) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1482) oGrid.kl oGrid.kr 400 1600 ⟨false, 286206886074810125159275120684161651128807424687241842763884244930082059032⟩ ⟨false, 0⟩ ⟨false, 440722573225201960516403464604466821256137296228924070407186039462938295972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1482_2000 : bothSeg evalE (oGrid.idx 1482) (oGrid.dm 1482) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1482) oGrid.kl oGrid.kr 400 2000 ⟨false, 440722573225201960516403464604466821256137296228924070407186039462938295972⟩ ⟨false, 0⟩ ⟨false, 644896240424682520025107224298862819075585438167838255067046928284985350244⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1482_2400 : bothLoop evalE (oGrid.idx 1482) (oGrid.dm 1482) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1482) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 644896240424682520025107224298862819075585438167838255067046928284985350244⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1482 : oGrid.row evalE 1482 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1482_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1482_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1482_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1482_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1482_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1482_2000).1 (bothLoop_sound b_1482_2400).1))))))

theorem n_row_1482 : nGrid.row evalE 1482 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1482_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1482_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1482_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1482_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1482_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1482_2000).2 (bothLoop_sound b_1482_2400).2))))))

theorem b_1483_0 : bothSeg evalE (oGrid.idx 1483) (oGrid.dm 1483) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1483) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 52301872234387090311363751086609229085177948197809346301465626427050255238⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1483_400 : bothSeg evalE (oGrid.idx 1483) (oGrid.dm 1483) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1483) oGrid.kl oGrid.kr 400 400 ⟨false, 52301872234387090311363751086609229085177948197809346301465626427050255238⟩ ⟨false, 0⟩ ⟨false, 122842915029611026074716744534982368971536756838880692603451592840314232056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1483_800 : bothSeg evalE (oGrid.idx 1483) (oGrid.dm 1483) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1483) oGrid.kl oGrid.kr 400 800 ⟨false, 122842915029611026074716744534982368971536756838880692603451592840314232056⟩ ⟨false, 0⟩ ⟨false, 184007596883686482178560466051706786141543417059668178779955514706062170366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1483_1200 : bothSeg evalE (oGrid.idx 1483) (oGrid.dm 1483) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1483) oGrid.kl oGrid.kr 400 1200 ⟨false, 184007596883686482178560466051706786141543417059668178779955514706062170366⟩ ⟨false, 0⟩ ⟨false, 287277968401196094638237858924322826967733573201695644304974023779272674100⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1483_1600 : bothSeg evalE (oGrid.idx 1483) (oGrid.dm 1483) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1483) oGrid.kl oGrid.kr 400 1600 ⟨false, 287277968401196094638237858924322826967733573201695644304974023779272674100⟩ ⟨false, 0⟩ ⟨false, 442061574332690664326770810385512871234349339339205733021965761230894624708⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1483_2000 : bothSeg evalE (oGrid.idx 1483) (oGrid.dm 1483) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1483) oGrid.kl oGrid.kr 400 2000 ⟨false, 442061574332690664326770810385512871234349339339205733021965761230894624708⟩ ⟨false, 0⟩ ⟨false, 646472200421057494500127318465090997204717164132064555757329675857244105438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1483_2400 : bothLoop evalE (oGrid.idx 1483) (oGrid.dm 1483) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1483) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 646472200421057494500127318465090997204717164132064555757329675857244105438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1483 : oGrid.row evalE 1483 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1483_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1483_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1483_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1483_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1483_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1483_2000).1 (bothLoop_sound b_1483_2400).1))))))

theorem n_row_1483 : nGrid.row evalE 1483 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1483_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1483_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1483_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1483_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1483_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1483_2000).2 (bothLoop_sound b_1483_2400).2))))))

theorem b_1484_0 : bothSeg evalE (oGrid.idx 1484) (oGrid.dm 1484) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1484) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 52804986857039474879573313869275848770264860517103535664353653244334701746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1484_400 : bothSeg evalE (oGrid.idx 1484) (oGrid.dm 1484) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1484) oGrid.kl oGrid.kr 400 400 ⟨false, 52804986857039474879573313869275848770264860517103535664353653244334701746⟩ ⟨false, 0⟩ ⟨false, 123493926559634531464226775321042962993076280545215916035668998983914304292⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1484_800 : bothSeg evalE (oGrid.idx 1484) (oGrid.dm 1484) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1484) oGrid.kl oGrid.kr 400 800 ⟨false, 123493926559634531464226775321042962993076280545215916035668998983914304292⟩ ⟨false, 0⟩ ⟨false, 184768403933967574996603825176961996182329918482175057406006877055468980948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1484_1200 : bothSeg evalE (oGrid.idx 1484) (oGrid.dm 1484) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1484) oGrid.kl oGrid.kr 400 1200 ⟨false, 184768403933967574996603825176961996182329918482175057406006877055468980948⟩ ⟨false, 0⟩ ⟨false, 288345757399343354916232637643606068756216074496652285519806674501815508180⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1484_1600 : bothSeg evalE (oGrid.idx 1484) (oGrid.dm 1484) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1484) oGrid.kl oGrid.kr 400 1600 ⟨false, 288345757399343354916232637643606068756216074496652285519806674501815508180⟩ ⟨false, 0⟩ ⟨false, 443397296293407175768758970129368284915002322785857734455894167372161354104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1484_2000 : bothSeg evalE (oGrid.idx 1484) (oGrid.dm 1484) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1484) oGrid.kl oGrid.kr 400 2000 ⟨false, 443397296293407175768758970129368284915002322785857734455894167372161354104⟩ ⟨false, 0⟩ ⟨false, 648044913826087361025107296745599605022884944912027257603668294973956986404⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1484_2400 : bothLoop evalE (oGrid.idx 1484) (oGrid.dm 1484) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1484) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 648044913826087361025107296745599605022884944912027257603668294973956986404⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1484 : oGrid.row evalE 1484 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1484_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1484_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1484_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1484_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1484_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1484_2000).1 (bothLoop_sound b_1484_2400).1))))))

theorem n_row_1484 : nGrid.row evalE 1484 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1484_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1484_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1484_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1484_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1484_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1484_2000).2 (bothLoop_sound b_1484_2400).2))))))

theorem b_1485_0 : bothSeg evalE (oGrid.idx 1485) (oGrid.dm 1485) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1485) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 53309639130962716239869838908780576340347046598426170351924991158082654324⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1485_400 : bothSeg evalE (oGrid.idx 1485) (oGrid.dm 1485) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1485) oGrid.kl oGrid.kr 400 400 ⟨false, 53309639130962716239869838908780576340347046598426170351924991158082654324⟩ ⟨false, 0⟩ ⟨false, 124135979665068299643579837683946695129073963860192766271825560598866607980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1485_800 : bothSeg evalE (oGrid.idx 1485) (oGrid.dm 1485) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1485) oGrid.kl oGrid.kr 400 800 ⟨false, 124135979665068299643579837683946695129073963860192766271825560598866607980⟩ ⟨false, 0⟩ ⟨false, 185525818093532733805243153397344115250600042171817618381786715695794545254⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1485_1200 : bothSeg evalE (oGrid.idx 1485) (oGrid.dm 1485) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1485) oGrid.kl oGrid.kr 400 1200 ⟨false, 185525818093532733805243153397344115250600042171817618381786715695794545254⟩ ⟨false, 0⟩ ⟨false, 289410133786593999986345577223486615166041153501116920670024197707307540310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1485_1600 : bothSeg evalE (oGrid.idx 1485) (oGrid.dm 1485) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1485) oGrid.kl oGrid.kr 400 1600 ⟨false, 289410133786593999986345577223486615166041153501116920670024197707307540310⟩ ⟨false, 0⟩ ⟨false, 444729619764979314766985143661596831536643170066080746547905991643232669524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1485_2000 : bothSeg evalE (oGrid.idx 1485) (oGrid.dm 1485) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1485) oGrid.kl oGrid.kr 400 2000 ⟨false, 444729619764979314766985143661596831536643170066080746547905991643232669524⟩ ⟨false, 0⟩ ⟨false, 649614261235900545205284077424207861582578077044485181603354678909729967972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1485_2400 : bothLoop evalE (oGrid.idx 1485) (oGrid.dm 1485) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1485) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 649614261235900545205284077424207861582578077044485181603354678909729967972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1485 : oGrid.row evalE 1485 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1485_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1485_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1485_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1485_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1485_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1485_2000).1 (bothLoop_sound b_1485_2400).1))))))

theorem n_row_1485 : nGrid.row evalE 1485 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1485_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1485_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1485_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1485_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1485_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1485_2000).2 (bothLoop_sound b_1485_2400).2))))))

theorem b_1486_0 : bothSeg evalE (oGrid.idx 1486) (oGrid.dm 1486) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1486) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 53815721176553759073361850873088336005214007632023018910159131121660927042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1486_400 : bothSeg evalE (oGrid.idx 1486) (oGrid.dm 1486) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1486) oGrid.kl oGrid.kr 400 400 ⟨false, 53815721176553759073361850873088336005214007632023018910159131121660927042⟩ ⟨false, 0⟩ ⟨false, 124768914500477919924099866363009363639410692121632646036978041593134571394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1486_800 : bothSeg evalE (oGrid.idx 1486) (oGrid.dm 1486) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1486) oGrid.kl oGrid.kr 400 800 ⟨false, 124768914500477919924099866363009363639410692121632646036978041593134571394⟩ ⟨false, 0⟩ ⟨false, 186279701206139586101930143078578719189846703889597585417939070262044974456⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1486_1200 : bothSeg evalE (oGrid.idx 1486) (oGrid.dm 1486) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1486) oGrid.kl oGrid.kr 400 1200 ⟨false, 186279701206139586101930143078578719189846703889597585417939070262044974456⟩ ⟨false, 0⟩ ⟨false, 290470959373899166246370121760955265961875184076494329588474321341367356002⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1486_1600 : bothSeg evalE (oGrid.idx 1486) (oGrid.dm 1486) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1486) oGrid.kl oGrid.kr 400 1600 ⟨false, 290470959373899166246370121760955265961875184076494329588474321341367356002⟩ ⟨false, 0⟩ ⟨false, 446058406498754635902733446080316561314360527183356037803988437245874317550⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1486_2000 : bothSeg evalE (oGrid.idx 1486) (oGrid.dm 1486) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1486) oGrid.kl oGrid.kr 400 2000 ⟨false, 446058406498754635902733446080316561314360527183356037803988437245874317550⟩ ⟨false, 0⟩ ⟨false, 651180104340425739562248472150566034478796618445905584091544325499953772528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1486_2400 : bothLoop evalE (oGrid.idx 1486) (oGrid.dm 1486) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1486) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 651180104340425739562248472150566034478796618445905584091544325499953772528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1486 : oGrid.row evalE 1486 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1486_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1486_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1486_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1486_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1486_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1486_2000).1 (bothLoop_sound b_1486_2400).1))))))

theorem n_row_1486 : nGrid.row evalE 1486 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1486_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1486_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1486_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1486_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1486_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1486_2000).2 (bothLoop_sound b_1486_2400).2))))))

theorem b_1487_0 : bothSeg evalE (oGrid.idx 1487) (oGrid.dm 1487) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1487) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 54323123295500748640479141005597809310229616834613983614769811320093856854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1487_400 : bothSeg evalE (oGrid.idx 1487) (oGrid.dm 1487) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1487) oGrid.kl oGrid.kr 400 400 ⟨false, 54323123295500748640479141005597809310229616834613983614769811320093856854⟩ ⟨false, 0⟩ ⟨false, 125392600415812385697667885860148895788498877420566178029561943832691075242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1487_800 : bothSeg evalE (oGrid.idx 1487) (oGrid.dm 1487) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1487) oGrid.kl oGrid.kr 400 800 ⟨false, 125392600415812385697667885860148895788498877420566178029561943832691075242⟩ ⟨false, 0⟩ ⟨false, 187029920067695848056749298597307805506481409846691787852369864947752647770⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1487_1200 : bothSeg evalE (oGrid.idx 1487) (oGrid.dm 1487) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1487) oGrid.kl oGrid.kr 400 1200 ⟨false, 187029920067695848056749298597307805506481409846691787852369864947752647770⟩ ⟨false, 0⟩ ⟨false, 291528100924466514088262540439350092727053357290067046211031380098665850770⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1487_1600 : bothSeg evalE (oGrid.idx 1487) (oGrid.dm 1487) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1487) oGrid.kl oGrid.kr 400 1600 ⟨false, 291528100924466514088262540439350092727053357290067046211031380098665850770⟩ ⟨false, 0⟩ ⟨false, 447383523198447734385765020975033627306321569064236925954108433809111883248⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1487_2000 : bothSeg evalE (oGrid.idx 1487) (oGrid.dm 1487) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1487) oGrid.kl oGrid.kr 400 2000 ⟨false, 447383523198447734385765020975033627306321569064236925954108433809111883248⟩ ⟨false, 0⟩ ⟨false, 652742309782039129841088987390609381333309013730288111501554408812937678368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1487_2400 : bothLoop evalE (oGrid.idx 1487) (oGrid.dm 1487) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1487) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 652742309782039129841088987390609381333309013730288111501554408812937678368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1487 : oGrid.row evalE 1487 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1487_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1487_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1487_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1487_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1487_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1487_2000).1 (bothLoop_sound b_1487_2400).1))))))

theorem n_row_1487 : nGrid.row evalE 1487 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1487_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1487_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1487_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1487_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1487_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1487_2000).2 (bothLoop_sound b_1487_2400).2))))))

theorem o_blk_1464 : allFrom (fun j => oGrid.row evalE j) 1464 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1464) o_row_1464 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1465) o_row_1465 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1466) o_row_1466 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1467) o_row_1467 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1468) o_row_1468 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1469) o_row_1469 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1470) o_row_1470 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1471) o_row_1471 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1472) o_row_1472 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1473) o_row_1473 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1474) o_row_1474 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1475) o_row_1475 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1476) o_row_1476 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1477) o_row_1477 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1478) o_row_1478 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1479) o_row_1479 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1480) o_row_1480 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1481) o_row_1481 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1482) o_row_1482 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1483) o_row_1483 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1484) o_row_1484 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1485) o_row_1485 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1486) o_row_1486 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1487) o_row_1487 (allFrom_zero (fun j => oGrid.row evalE j) 1488)))))))))))))))))))))))))

theorem n_blk_1464 : allFrom (fun j => nGrid.row evalE j) 1464 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1464) n_row_1464 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1465) n_row_1465 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1466) n_row_1466 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1467) n_row_1467 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1468) n_row_1468 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1469) n_row_1469 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1470) n_row_1470 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1471) n_row_1471 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1472) n_row_1472 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1473) n_row_1473 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1474) n_row_1474 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1475) n_row_1475 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1476) n_row_1476 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1477) n_row_1477 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1478) n_row_1478 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1479) n_row_1479 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1480) n_row_1480 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1481) n_row_1481 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1482) n_row_1482 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1483) n_row_1483 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1484) n_row_1484 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1485) n_row_1485 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1486) n_row_1486 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1487) n_row_1487 (allFrom_zero (fun j => nGrid.row evalE j) 1488)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
