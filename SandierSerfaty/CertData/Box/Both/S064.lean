/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 64 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1536`–`1559`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1536_0 : bothSeg evalE (oGrid.idx 1536) (oGrid.dm 1536) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1536) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75890242406523093476435905903360495030017369000371928624340041477810462474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1536_400 : bothSeg evalE (oGrid.idx 1536) (oGrid.dm 1536) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1536) oGrid.kl oGrid.kr 400 400 ⟨false, 75890242406523093476435905903360495030017369000371928624340041477810462474⟩ ⟨false, 0⟩ ⟨false, 141972497265555537045430795740382253749627026567730660874968703277866419198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1536_800 : bothSeg evalE (oGrid.idx 1536) (oGrid.dm 1536) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1536) oGrid.kl oGrid.kr 400 800 ⟨false, 141972497265555537045430795740382253749627026567730660874968703277866419198⟩ ⟨false, 0⟩ ⟨false, 215562378889862247876253566924026034013885127860551347942599794992840360830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1536_1200 : bothSeg evalE (oGrid.idx 1536) (oGrid.dm 1536) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1536) oGrid.kl oGrid.kr 400 1200 ⟨false, 215562378889862247876253566924026034013885127860551347942599794992840360830⟩ ⟨false, 0⟩ ⟨false, 335074881180812789362196233730785738401013294318037488609380809286882836812⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1536_1600 : bothSeg evalE (oGrid.idx 1536) (oGrid.dm 1536) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1536) oGrid.kl oGrid.kr 400 1600 ⟨false, 335074881180812789362196233730785738401013294318037488609380809286882836812⟩ ⟨false, 0⟩ ⟨false, 504077029493518688389571992265602302516740362436821106784033488968579895940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1536_2000 : bothSeg evalE (oGrid.idx 1536) (oGrid.dm 1536) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1536) oGrid.kl oGrid.kr 400 2000 ⟨false, 504077029493518688389571992265602302516740362436821106784033488968579895940⟩ ⟨false, 0⟩ ⟨false, 721091563294815668486278044865205405097040630547448331198746742141270357430⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1536_2400 : bothLoop evalE (oGrid.idx 1536) (oGrid.dm 1536) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1536) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 721091563294815668486278044865205405097040630547448331198746742141270357430⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1536 : oGrid.row evalE 1536 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1536_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1536_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1536_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1536_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1536_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1536_2000).1 (bothLoop_sound b_1536_2400).1))))))

theorem n_row_1536 : nGrid.row evalE 1536 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1536_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1536_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1536_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1536_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1536_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1536_2000).2 (bothLoop_sound b_1536_2400).2))))))

theorem b_1537_0 : bothSeg evalE (oGrid.idx 1537) (oGrid.dm 1537) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1537) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76126878427194019030881096885396851007633033248414328770696061633100747642⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1537_400 : bothSeg evalE (oGrid.idx 1537) (oGrid.dm 1537) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1537) oGrid.kl oGrid.kr 400 400 ⟨false, 76126878427194019030881096885396851007633033248414328770696061633100747642⟩ ⟨false, 0⟩ ⟨false, 141986964602162281103164278051354274318416695149740516731207862655373922038⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1537_800 : bothSeg evalE (oGrid.idx 1537) (oGrid.dm 1537) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1537) oGrid.kl oGrid.kr 400 800 ⟨false, 141986964602162281103164278051354274318416695149740516731207862655373922038⟩ ⟨false, 0⟩ ⟨false, 215900630987000866820662199472283912202222857329181635182577902220671879114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1537_1200 : bothSeg evalE (oGrid.idx 1537) (oGrid.dm 1537) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1537) oGrid.kl oGrid.kr 400 1200 ⟨false, 215900630987000866820662199472283912202222857329181635182577902220671879114⟩ ⟨false, 0⟩ ⟨false, 335719027271446820093158589105707490155220567259555012259037613891750356756⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1537_1600 : bothSeg evalE (oGrid.idx 1537) (oGrid.dm 1537) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1537) oGrid.kl oGrid.kr 400 1600 ⟨false, 335719027271446820093158589105707490155220567259555012259037613891750356756⟩ ⟨false, 0⟩ ⟨false, 504989777404113489579722715075637844883060092262109913258098564971944780662⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1537_2000 : bothSeg evalE (oGrid.idx 1537) (oGrid.dm 1537) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1537) oGrid.kl oGrid.kr 400 2000 ⟨false, 504989777404113489579722715075637844883060092262109913258098564971944780662⟩ ⟨false, 0⟩ ⟨false, 722242942054093081481276606477906057149354825289338345318071234870834441222⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1537_2400 : bothLoop evalE (oGrid.idx 1537) (oGrid.dm 1537) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1537) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 722242942054093081481276606477906057149354825289338345318071234870834441222⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1537 : oGrid.row evalE 1537 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1537_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1537_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1537_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1537_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1537_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1537_2000).1 (bothLoop_sound b_1537_2400).1))))))

theorem n_row_1537 : nGrid.row evalE 1537 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1537_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1537_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1537_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1537_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1537_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1537_2000).2 (bothLoop_sound b_1537_2400).2))))))

theorem b_1538_0 : bothSeg evalE (oGrid.idx 1538) (oGrid.dm 1538) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1538) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76349694460839518417890198676789040779318619997013787364524942453296457344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1538_400 : bothSeg evalE (oGrid.idx 1538) (oGrid.dm 1538) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1538) oGrid.kl oGrid.kr 400 400 ⟨false, 76349694460839518417890198676789040779318619997013787364524942453296457344⟩ ⟨false, 0⟩ ⟨false, 141988113836479115781411574838682022086670499135544085327706187613496710114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1538_800 : bothSeg evalE (oGrid.idx 1538) (oGrid.dm 1538) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1538) oGrid.kl oGrid.kr 400 800 ⟨false, 141988113836479115781411574838682022086670499135544085327706187613496710114⟩ ⟨false, 0⟩ ⟨false, 216227119575809158059049531048775659949862305409689965311852053742013788018⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1538_1200 : bothSeg evalE (oGrid.idx 1538) (oGrid.dm 1538) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1538) oGrid.kl oGrid.kr 400 1200 ⟨false, 216227119575809158059049531048775659949862305409689965311852053742013788018⟩ ⟨false, 0⟩ ⟨false, 336351388535861943728001713834049695936971064203052987342564508960553680840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1538_1600 : bothSeg evalE (oGrid.idx 1538) (oGrid.dm 1538) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1538) oGrid.kl oGrid.kr 400 1600 ⟨false, 336351388535861943728001713834049695936971064203052987342564508960553680840⟩ ⟨false, 0⟩ ⟨false, 505890751599501716498801145992814287611217110348886023279995348553718117750⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1538_2000 : bothSeg evalE (oGrid.idx 1538) (oGrid.dm 1538) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1538) oGrid.kl oGrid.kr 400 2000 ⟨false, 505890751599501716498801145992814287611217110348886023279995348553718117750⟩ ⟨false, 0⟩ ⟨false, 723382576445893407915220037899578991182763195313863824162402596004728926214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1538_2400 : bothLoop evalE (oGrid.idx 1538) (oGrid.dm 1538) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1538) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 723382576445893407915220037899578991182763195313863824162402596004728926214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1538 : oGrid.row evalE 1538 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1538_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1538_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1538_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1538_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1538_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1538_2000).1 (bothLoop_sound b_1538_2400).1))))))

theorem n_row_1538 : nGrid.row evalE 1538 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1538_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1538_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1538_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1538_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1538_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1538_2000).2 (bothLoop_sound b_1538_2400).2))))))

theorem b_1539_0 : bothSeg evalE (oGrid.idx 1539) (oGrid.dm 1539) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1539) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76558449740280246079961049609050365457242363953799657928883715734389968882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1539_400 : bothSeg evalE (oGrid.idx 1539) (oGrid.dm 1539) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1539) oGrid.kl oGrid.kr 400 400 ⟨false, 76558449740280246079961049609050365457242363953799657928883715734389968882⟩ ⟨false, 0⟩ ⟨false, 141976036148012193925149485336288925749969872593345316326685295982387151286⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1539_800 : bothSeg evalE (oGrid.idx 1539) (oGrid.dm 1539) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1539) oGrid.kl oGrid.kr 400 800 ⟨false, 141976036148012193925149485336288925749969872593345316326685295982387151286⟩ ⟨false, 0⟩ ⟨false, 216541856045436722297587600181424002765509771648820472037725116263933792048⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1539_1200 : bothSeg evalE (oGrid.idx 1539) (oGrid.dm 1539) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1539) oGrid.kl oGrid.kr 400 1200 ⟨false, 216541856045436722297587600181424002765509771648820472037725116263933792048⟩ ⟨false, 0⟩ ⟨false, 336971976335714231340094489563910989906663348384280595501567998124526546628⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1539_1600 : bothSeg evalE (oGrid.idx 1539) (oGrid.dm 1539) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1539) oGrid.kl oGrid.kr 400 1600 ⟨false, 336971976335714231340094489563910989906663348384280595501567998124526546628⟩ ⟨false, 0⟩ ⟨false, 506779963387356879121661473210857500606005806338227254943913671877824669758⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1539_2000 : bothSeg evalE (oGrid.idx 1539) (oGrid.dm 1539) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1539) oGrid.kl oGrid.kr 400 2000 ⟨false, 506779963387356879121661473210857500606005806338227254943913671877824669758⟩ ⟨false, 0⟩ ⟨false, 724510477720625838567078123983984799629020832787423122291476620796457138296⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1539_2400 : bothLoop evalE (oGrid.idx 1539) (oGrid.dm 1539) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1539) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 724510477720625838567078123983984799629020832787423122291476620796457138296⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1539 : oGrid.row evalE 1539 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1539_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1539_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1539_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1539_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1539_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1539_2000).1 (bothLoop_sound b_1539_2400).1))))))

theorem n_row_1539 : nGrid.row evalE 1539 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1539_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1539_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1539_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1539_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1539_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1539_2000).2 (bothLoop_sound b_1539_2400).2))))))

theorem b_1540_0 : bothSeg evalE (oGrid.idx 1540) (oGrid.dm 1540) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1540) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76752892890014269552660514667245314634506051956705901411312399731119748392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1540_400 : bothSeg evalE (oGrid.idx 1540) (oGrid.dm 1540) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1540) oGrid.kl oGrid.kr 400 400 ⟨false, 76752892890014269552660514667245314634506051956705901411312399731119748392⟩ ⟨false, 0⟩ ⟨false, 141950831379909708805040753598999396505608263236237462180236304364990789270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1540_800 : bothSeg evalE (oGrid.idx 1540) (oGrid.dm 1540) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1540) oGrid.kl oGrid.kr 400 800 ⟨false, 141950831379909708805040753598999396505608263236237462180236304364990789270⟩ ⟨false, 0⟩ ⟨false, 216844862610676571008014247277720638206024161112578956905068904861380366426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1540_1200 : bothSeg evalE (oGrid.idx 1540) (oGrid.dm 1540) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1540) oGrid.kl oGrid.kr 400 1200 ⟨false, 216844862610676571008014247277720638206024161112578956905068904861380366426⟩ ⟨false, 0⟩ ⟨false, 337580812858397221483179226228136121123881244029887069658959827964014536304⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1540_1600 : bothSeg evalE (oGrid.idx 1540) (oGrid.dm 1540) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1540) oGrid.kl oGrid.kr 400 1600 ⟨false, 337580812858397221483179226228136121123881244029887069658959827964014536304⟩ ⟨false, 0⟩ ⟨false, 507657434901191488349239611822679211966727705673295369221875219581199793572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1540_2000 : bothSeg evalE (oGrid.idx 1540) (oGrid.dm 1540) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1540) oGrid.kl oGrid.kr 400 2000 ⟨false, 507657434901191488349239611822679211966727705673295369221875219581199793572⟩ ⟨false, 0⟩ ⟨false, 725626667954614816320835192039929500416349248873872873158218782130902534212⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1540_2400 : bothLoop evalE (oGrid.idx 1540) (oGrid.dm 1540) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1540) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 725626667954614816320835192039929500416349248873872873158218782130902534212⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1540 : oGrid.row evalE 1540 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1540_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1540_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1540_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1540_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1540_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1540_2000).1 (bothLoop_sound b_1540_2400).1))))))

theorem n_row_1540 : nGrid.row evalE 1540 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1540_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1540_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1540_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1540_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1540_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1540_2000).2 (bothLoop_sound b_1540_2400).2))))))

theorem b_1541_0 : bothSeg evalE (oGrid.idx 1541) (oGrid.dm 1541) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1541) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76932821111559835904969548701638889968423806114362107291616512436326348424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1541_400 : bothSeg evalE (oGrid.idx 1541) (oGrid.dm 1541) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1541) oGrid.kl oGrid.kr 400 400 ⟨false, 76932821111559835904969548701638889968423806114362107291616512436326348424⟩ ⟨false, 0⟩ ⟨false, 141912629814210692133669107736887235404240186246893183290700873127151933408⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1541_800 : bothSeg evalE (oGrid.idx 1541) (oGrid.dm 1541) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1541) oGrid.kl oGrid.kr 400 800 ⟨false, 141912629814210692133669107736887235404240186246893183290700873127151933408⟩ ⟨false, 0⟩ ⟨false, 217136194200764208957349367038808855723229712646909268543135756886716219168⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1541_1200 : bothSeg evalE (oGrid.idx 1541) (oGrid.dm 1541) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1541) oGrid.kl oGrid.kr 400 1200 ⟨false, 217136194200764208957349367038808855723229712646909268543135756886716219168⟩ ⟨false, 0⟩ ⟨false, 338177953005840782553996566674110984477433682296678435791038234894888107940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1541_1600 : bothSeg evalE (oGrid.idx 1541) (oGrid.dm 1541) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1541) oGrid.kl oGrid.kr 400 1600 ⟨false, 338177953005840782553996566674110984477433682296678435791038234894888107940⟩ ⟨false, 0⟩ ⟨false, 508523220989155754934487102220791072914388026259990553322097390330436123132⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1541_2000 : bothSeg evalE (oGrid.idx 1541) (oGrid.dm 1541) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1541) oGrid.kl oGrid.kr 400 2000 ⟨false, 508523220989155754934487102220791072914388026259990553322097390330436123132⟩ ⟨false, 0⟩ ⟨false, 726731201938898656329100979324406808013318483346054360860527490992811863354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1541_2400 : bothLoop evalE (oGrid.idx 1541) (oGrid.dm 1541) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1541) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 726731201938898656329100979324406808013318483346054360860527490992811863354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1541 : oGrid.row evalE 1541 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1541_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1541_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1541_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1541_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1541_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1541_2000).1 (bothLoop_sound b_1541_2400).1))))))

theorem n_row_1541 : nGrid.row evalE 1541 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1541_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1541_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1541_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1541_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1541_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1541_2000).2 (bothLoop_sound b_1541_2400).2))))))

theorem b_1542_0 : bothSeg evalE (oGrid.idx 1542) (oGrid.dm 1542) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1542) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77098022673047297548488468329103403534614310074633066321273845421096784724⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1542_400 : bothSeg evalE (oGrid.idx 1542) (oGrid.dm 1542) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1542) oGrid.kl oGrid.kr 400 400 ⟨false, 77098022673047297548488468329103403534614310074633066321273845421096784724⟩ ⟨false, 0⟩ ⟨false, 141861556013295413101793764005767034425753070943278526526978834120878397240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1542_800 : bothSeg evalE (oGrid.idx 1542) (oGrid.dm 1542) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1542) oGrid.kl oGrid.kr 400 800 ⟨false, 141861556013295413101793764005767034425753070943278526526978834120878397240⟩ ⟨false, 0⟩ ⟨false, 217415902739141004453200300484667502875717582583587506876856242909698663320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1542_1200 : bothSeg evalE (oGrid.idx 1542) (oGrid.dm 1542) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1542) oGrid.kl oGrid.kr 400 1200 ⟨false, 217415902739141004453200300484667502875717582583587506876856242909698663320⟩ ⟨false, 0⟩ ⟨false, 338763448674274263348106503141236924163043104953642606015416155023495052990⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1542_1600 : bothSeg evalE (oGrid.idx 1542) (oGrid.dm 1542) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1542) oGrid.kl oGrid.kr 400 1600 ⟨false, 338763448674274263348106503141236924163043104953642606015416155023495052990⟩ ⟨false, 0⟩ ⟨false, 509377373493800576823232508772339549169359924575955709549891269731347399570⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1542_2000 : bothSeg evalE (oGrid.idx 1542) (oGrid.dm 1542) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1542) oGrid.kl oGrid.kr 400 2000 ⟨false, 509377373493800576823232508772339549169359924575955709549891269731347399570⟩ ⟨false, 0⟩ ⟨false, 727824131458992454614615322986150758726797381045442228645520915921410839892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1542_2400 : bothLoop evalE (oGrid.idx 1542) (oGrid.dm 1542) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1542) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 727824131458992454614615322986150758726797381045442228645520915921410839892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1542 : oGrid.row evalE 1542 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1542_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1542_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1542_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1542_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1542_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1542_2000).1 (bothLoop_sound b_1542_2400).1))))))

theorem n_row_1542 : nGrid.row evalE 1542 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1542_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1542_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1542_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1542_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1542_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1542_2000).2 (bothLoop_sound b_1542_2400).2))))))

theorem b_1543_0 : bothSeg evalE (oGrid.idx 1543) (oGrid.dm 1543) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1543) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77248301414100175742401705663392064863064446282568057060090327429026950758⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1543_400 : bothSeg evalE (oGrid.idx 1543) (oGrid.dm 1543) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1543) oGrid.kl oGrid.kr 400 400 ⟨false, 77248301414100175742401705663392064863064446282568057060090327429026950758⟩ ⟨false, 0⟩ ⟨false, 141797736120536328228642481887794978820940105054851998283924319282280964840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1543_800 : bothSeg evalE (oGrid.idx 1543) (oGrid.dm 1543) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1543) oGrid.kl oGrid.kr 400 800 ⟨false, 141797736120536328228642481887794978820940105054851998283924319282280964840⟩ ⟨false, 0⟩ ⟨false, 217684043746748334176001335606368788123677970510842104901683925127580657916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1543_1200 : bothSeg evalE (oGrid.idx 1543) (oGrid.dm 1543) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1543) oGrid.kl oGrid.kr 400 1200 ⟨false, 217684043746748334176001335606368788123677970510842104901683925127580657916⟩ ⟨false, 0⟩ ⟨false, 339337355357520418679272636012172144684571183793459778569199271317582179154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1543_1600 : bothSeg evalE (oGrid.idx 1543) (oGrid.dm 1543) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1543) oGrid.kl oGrid.kr 400 1600 ⟨false, 339337355357520418679272636012172144684571183793459778569199271317582179154⟩ ⟨false, 0⟩ ⟨false, 510219947855371301780186012879632479372617042771785778798316382516512967316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1543_2000 : bothSeg evalE (oGrid.idx 1543) (oGrid.dm 1543) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1543) oGrid.kl oGrid.kr 400 2000 ⟨false, 510219947855371301780186012879632479372617042771785778798316382516512967316⟩ ⟨false, 0⟩ ⟨false, 728905511898181771980072490607947779180437125235541882584487391892965424618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1543_2400 : bothLoop evalE (oGrid.idx 1543) (oGrid.dm 1543) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1543) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 728905511898181771980072490607947779180437125235541882584487391892965424618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1543 : oGrid.row evalE 1543 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1543_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1543_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1543_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1543_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1543_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1543_2000).1 (bothLoop_sound b_1543_2400).1))))))

theorem n_row_1543 : nGrid.row evalE 1543 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1543_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1543_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1543_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1543_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1543_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1543_2000).2 (bothLoop_sound b_1543_2400).2))))))

theorem b_1544_0 : bothSeg evalE (oGrid.idx 1544) (oGrid.dm 1544) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1544) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77383496317466042032541858562844983706378413020443477327384478905758323388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1544_400 : bothSeg evalE (oGrid.idx 1544) (oGrid.dm 1544) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1544) oGrid.kl oGrid.kr 400 400 ⟨false, 77383496317466042032541858562844983706378413020443477327384478905758323388⟩ ⟨false, 0⟩ ⟨false, 141721350219725623851872585149549902884136691969924114961551285918333513076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1544_800 : bothSeg evalE (oGrid.idx 1544) (oGrid.dm 1544) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1544) oGrid.kl oGrid.kr 400 800 ⟨false, 141721350219725623851872585149549902884136691969924114961551285918333513076⟩ ⟨false, 0⟩ ⟨false, 217940729171961939636574289996551944449614280078943891529376084785133622586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1544_1200 : bothSeg evalE (oGrid.idx 1544) (oGrid.dm 1544) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1544) oGrid.kl oGrid.kr 400 1200 ⟨false, 217940729171961939636574289996551944449614280078943891529376084785133622586⟩ ⟨false, 0⟩ ⟨false, 339899784976929547099820539728679978020601601848011044294296119256436749178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1544_1600 : bothSeg evalE (oGrid.idx 1544) (oGrid.dm 1544) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1544) oGrid.kl oGrid.kr 400 1600 ⟨false, 339899784976929547099820539728679978020601601848011044294296119256436749178⟩ ⟨false, 0⟩ ⟨false, 511051055941741702337346057164280986643570436474504891516049131566202757556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1544_2000 : bothSeg evalE (oGrid.idx 1544) (oGrid.dm 1544) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1544) oGrid.kl oGrid.kr 400 2000 ⟨false, 511051055941741702337346057164280986643570436474504891516049131566202757556⟩ ⟨false, 0⟩ ⟨false, 729975455067456530263733237040398860863064349265037428909065488395061693264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1544_2400 : bothLoop evalE (oGrid.idx 1544) (oGrid.dm 1544) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1544) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 729975455067456530263733237040398860863064349265037428909065488395061693264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1544 : oGrid.row evalE 1544 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1544_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1544_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1544_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1544_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1544_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1544_2000).1 (bothLoop_sound b_1544_2400).1))))))

theorem n_row_1544 : nGrid.row evalE 1544 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1544_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1544_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1544_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1544_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1544_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1544_2000).2 (bothLoop_sound b_1544_2400).2))))))

theorem b_1545_0 : bothSeg evalE (oGrid.idx 1545) (oGrid.dm 1545) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1545) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77503448864122163431652450335666877556364240430760542035187053067081539384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1545_400 : bothSeg evalE (oGrid.idx 1545) (oGrid.dm 1545) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1545) oGrid.kl oGrid.kr 400 400 ⟨false, 77503448864122163431652450335666877556364240430760542035187053067081539384⟩ ⟨false, 0⟩ ⟨false, 141632559594541874220305745261676447793925549293406711376291721869304064344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1545_800 : bothSeg evalE (oGrid.idx 1545) (oGrid.dm 1545) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1545) oGrid.kl oGrid.kr 400 800 ⟨false, 141632559594541874220305745261676447793925549293406711376291721869304064344⟩ ⟨false, 0⟩ ⟨false, 218186055157629767060989580428916376126114820354577591980908056325925941044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1545_1200 : bothSeg evalE (oGrid.idx 1545) (oGrid.dm 1545) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1545) oGrid.kl oGrid.kr 400 1200 ⟨false, 218186055157629767060989580428916376126114820354577591980908056325925941044⟩ ⟨false, 0⟩ ⟨false, 340450833648417112522975260939953174569142088015046834160879680227938772806⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1545_1600 : bothSeg evalE (oGrid.idx 1545) (oGrid.dm 1545) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1545) oGrid.kl oGrid.kr 400 1600 ⟨false, 340450833648417112522975260939953174569142088015046834160879680227938772806⟩ ⟨false, 0⟩ ⟨false, 511870793815451434865660489651375498350229117044980617288599098415995547048⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1545_2000 : bothSeg evalE (oGrid.idx 1545) (oGrid.dm 1545) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1545) oGrid.kl oGrid.kr 400 2000 ⟨false, 511870793815451434865660489651375498350229117044980617288599098415995547048⟩ ⟨false, 0⟩ ⟨false, 731034056972548392741885372734223770317187616841237478071773095101373989472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1545_2400 : bothLoop evalE (oGrid.idx 1545) (oGrid.dm 1545) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1545) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 731034056972548392741885372734223770317187616841237478071773095101373989472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1545 : oGrid.row evalE 1545 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1545_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1545_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1545_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1545_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1545_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1545_2000).1 (bothLoop_sound b_1545_2400).1))))))

theorem n_row_1545 : nGrid.row evalE 1545 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1545_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1545_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1545_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1545_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1545_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1545_2000).2 (bothLoop_sound b_1545_2400).2))))))

theorem b_1546_0 : bothSeg evalE (oGrid.idx 1546) (oGrid.dm 1546) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1546) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77608031875366615696396396257130984643675774782592720423584255089884559126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1546_400 : bothSeg evalE (oGrid.idx 1546) (oGrid.dm 1546) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1546) oGrid.kl oGrid.kr 400 400 ⟨false, 77608031875366615696396396257130984643675774782592720423584255089884559126⟩ ⟨false, 0⟩ ⟨false, 141531565896812630048215268107670140963372495380215806518482312453309184352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1546_800 : bothSeg evalE (oGrid.idx 1546) (oGrid.dm 1546) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1546) oGrid.kl oGrid.kr 400 800 ⟨false, 141531565896812630048215268107670140963372495380215806518482312453309184352⟩ ⟨false, 0⟩ ⟨false, 218420159806729020045685496927185432151638135161800510942565999129276314288⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1546_1200 : bothSeg evalE (oGrid.idx 1546) (oGrid.dm 1546) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1546) oGrid.kl oGrid.kr 400 1200 ⟨false, 218420159806729020045685496927185432151638135161800510942565999129276314288⟩ ⟨false, 0⟩ ⟨false, 340990639448120579089163013498437266838889444456458901795530872254362363992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1546_1600 : bothSeg evalE (oGrid.idx 1546) (oGrid.dm 1546) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1546) oGrid.kl oGrid.kr 400 1600 ⟨false, 340990639448120579089163013498437266838889444456458901795530872254362363992⟩ ⟨false, 0⟩ ⟨false, 512679299499362712111774132122144741314834055939475772429385044342109481024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1546_2000 : bothSeg evalE (oGrid.idx 1546) (oGrid.dm 1546) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1546) oGrid.kl oGrid.kr 400 2000 ⟨false, 512679299499362712111774132122144741314834055939475772429385044342109481024⟩ ⟨false, 0⟩ ⟨false, 732081455579587358020192213900792454967783594916756810250546413979919223796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1546_2400 : bothLoop evalE (oGrid.idx 1546) (oGrid.dm 1546) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1546) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 732081455579587358020192213900792454967783594916756810250546413979919223796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1546 : oGrid.row evalE 1546 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1546_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1546_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1546_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1546_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1546_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1546_2000).1 (bothLoop_sound b_1546_2400).1))))))

theorem n_row_1546 : nGrid.row evalE 1546 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1546_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1546_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1546_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1546_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1546_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1546_2000).2 (bothLoop_sound b_1546_2400).2))))))

theorem b_1547_0 : bothSeg evalE (oGrid.idx 1547) (oGrid.dm 1547) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1547) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77697134555084407901573784053915492850311855093172872738155320873596301118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1547_400 : bothSeg evalE (oGrid.idx 1547) (oGrid.dm 1547) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1547) oGrid.kl oGrid.kr 400 400 ⟨false, 77697134555084407901573784053915492850311855093172872738155320873596301118⟩ ⟨false, 0⟩ ⟨false, 141418566896188985869001572734089143682751183575786880672993760956827338060⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1547_800 : bothSeg evalE (oGrid.idx 1547) (oGrid.dm 1547) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1547) oGrid.kl oGrid.kr 400 800 ⟨false, 141418566896188985869001572734089143682751183575786880672993760956827338060⟩ ⟨false, 0⟩ ⟨false, 218643180401890738944952679273295407548004188044444452722060114264872193700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1547_1200 : bothSeg evalE (oGrid.idx 1547) (oGrid.dm 1547) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1547) oGrid.kl oGrid.kr 400 1200 ⟨false, 218643180401890738944952679273295407548004188044444452722060114264872193700⟩ ⟨false, 0⟩ ⟨false, 341519339631923773237413140717546440711866487044767303363668596287662279516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1547_1600 : bothSeg evalE (oGrid.idx 1547) (oGrid.dm 1547) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1547) oGrid.kl oGrid.kr 400 1600 ⟨false, 341519339631923773237413140717546440711866487044767303363668596287662279516⟩ ⟨false, 0⟩ ⟨false, 513476710196184503160845142116297446832510348366242364052856036227081632720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1547_2000 : bothSeg evalE (oGrid.idx 1547) (oGrid.dm 1547) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1547) oGrid.kl oGrid.kr 400 2000 ⟨false, 513476710196184503160845142116297446832510348366242364052856036227081632720⟩ ⟨false, 0⟩ ⟨false, 733117788034625881375117842423779354778623532232571863056634461829326461066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1547_2400 : bothLoop evalE (oGrid.idx 1547) (oGrid.dm 1547) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1547) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 733117788034625881375117842423779354778623532232571863056634461829326461066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1547 : oGrid.row evalE 1547 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1547_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1547_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1547_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1547_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1547_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1547_2000).1 (bothLoop_sound b_1547_2400).1))))))

theorem n_row_1547 : nGrid.row evalE 1547 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1547_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1547_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1547_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1547_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1547_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1547_2000).2 (bothLoop_sound b_1547_2400).2))))))

theorem b_1548_0 : bothSeg evalE (oGrid.idx 1548) (oGrid.dm 1548) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1548) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77770651816934048388730885430652245764187453263866501996744135367138293994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1548_400 : bothSeg evalE (oGrid.idx 1548) (oGrid.dm 1548) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1548) oGrid.kl oGrid.kr 400 400 ⟨false, 77770651816934048388730885430652245764187453263866501996744135367138293994⟩ ⟨false, 0⟩ ⟨false, 141293768297271624095813949099008525485823325783992040637869146246230351712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1548_800 : bothSeg evalE (oGrid.idx 1548) (oGrid.dm 1548) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1548) oGrid.kl oGrid.kr 400 800 ⟨false, 141293768297271624095813949099008525485823325783992040637869146246230351712⟩ ⟨false, 0⟩ ⟨false, 218855263479308081850359713418023993075838974365527448400625433551683015374⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1548_1200 : bothSeg evalE (oGrid.idx 1548) (oGrid.dm 1548) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1548) oGrid.kl oGrid.kr 400 1200 ⟨false, 218855263479308081850359713418023993075838974365527448400625433551683015374⟩ ⟨false, 0⟩ ⟨false, 342037080709364947840467058614243070512176019079295062929049126717600135194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1548_1600 : bothSeg evalE (oGrid.idx 1548) (oGrid.dm 1548) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1548) oGrid.kl oGrid.kr 400 1600 ⟨false, 342037080709364947840467058614243070512176019079295062929049126717600135194⟩ ⟨false, 0⟩ ⟨false, 514263172362380435683882624640650349618188265994455124297095256574588616400⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1548_2000 : bothSeg evalE (oGrid.idx 1548) (oGrid.dm 1548) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1548) oGrid.kl oGrid.kr 400 2000 ⟨false, 514263172362380435683882624640650349618188265994455124297095256574588616400⟩ ⟨false, 0⟩ ⟨false, 734143200737546698404087304746036345879606551706810288626872862058035718712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1548_2400 : bothLoop evalE (oGrid.idx 1548) (oGrid.dm 1548) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1548) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 734143200737546698404087304746036345879606551706810288626872862058035718712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1548 : oGrid.row evalE 1548 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1548_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1548_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1548_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1548_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1548_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1548_2000).1 (bothLoop_sound b_1548_2400).1))))))

theorem n_row_1548 : nGrid.row evalE 1548 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1548_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1548_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1548_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1548_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1548_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1548_2000).2 (bothLoop_sound b_1548_2400).2))))))

theorem b_1549_0 : bothSeg evalE (oGrid.idx 1549) (oGrid.dm 1549) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1549) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77828517420838581330345263342140783621163192592246124312321193376148396040⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1549_400 : bothSeg evalE (oGrid.idx 1549) (oGrid.dm 1549) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1549) oGrid.kl oGrid.kr 400 400 ⟨false, 77828517420838581330345263342140783621163192592246124312321193376148396040⟩ ⟨false, 0⟩ ⟨false, 141157412035014324359539606091844880346405099256020579503576052918361389678⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1549_800 : bothSeg evalE (oGrid.idx 1549) (oGrid.dm 1549) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1549) oGrid.kl oGrid.kr 400 800 ⟨false, 141157412035014324359539606091844880346405099256020579503576052918361389678⟩ ⟨false, 0⟩ ⟨false, 219056594792799512553824301581270884806637523095489425538527240123138697248⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1549_1200 : bothSeg evalE (oGrid.idx 1549) (oGrid.dm 1549) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1549) oGrid.kl oGrid.kr 400 1200 ⟨false, 219056594792799512553824301581270884806637523095489425538527240123138697248⟩ ⟨false, 0⟩ ⟨false, 342544048407699753794331152376178636101681509967246720476638587965700867300⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1549_1600 : bothSeg evalE (oGrid.idx 1549) (oGrid.dm 1549) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1549) oGrid.kl oGrid.kr 400 1600 ⟨false, 342544048407699753794331152376178636101681509967246720476638587965700867300⟩ ⟨false, 0⟩ ⟨false, 515038871672231605860187655162633405412482755273678755988182652480407040482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1549_2000 : bothSeg evalE (oGrid.idx 1549) (oGrid.dm 1549) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1549) oGrid.kl oGrid.kr 400 2000 ⟨false, 515038871672231605860187655162633405412482755273678755988182652480407040482⟩ ⟨false, 0⟩ ⟨false, 735157879306125556375168701644340261663475801452941552016106613399227541824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1549_2400 : bothLoop evalE (oGrid.idx 1549) (oGrid.dm 1549) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1549) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 735157879306125556375168701644340261663475801452941552016106613399227541824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1549 : oGrid.row evalE 1549 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1549_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1549_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1549_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1549_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1549_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1549_2000).1 (bothLoop_sound b_1549_2400).1))))))

theorem n_row_1549 : nGrid.row evalE 1549 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1549_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1549_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1549_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1549_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1549_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1549_2000).2 (bothLoop_sound b_1549_2400).2))))))

theorem b_1550_0 : bothSeg evalE (oGrid.idx 1550) (oGrid.dm 1550) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1550) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77870678943283512374118391042857230001826502749118180072545013064291964720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1550_400 : bothSeg evalE (oGrid.idx 1550) (oGrid.dm 1550) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1550) oGrid.kl oGrid.kr 400 400 ⟨false, 77870678943283512374118391042857230001826502749118180072545013064291964720⟩ ⟨false, 0⟩ ⟨false, 141009735245970358911474784356130022572821543300890228701179928537866457146⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1550_800 : bothSeg evalE (oGrid.idx 1550) (oGrid.dm 1550) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1550) oGrid.kl oGrid.kr 400 800 ⟨false, 141009735245970358911474784356130022572821543300890228701179928537866457146⟩ ⟨false, 0⟩ ⟨false, 219247357067665576465685353444383608419631873436350503672991548814691003258⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1550_1200 : bothSeg evalE (oGrid.idx 1550) (oGrid.dm 1550) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1550) oGrid.kl oGrid.kr 400 1200 ⟨false, 219247357067665576465685353444383608419631873436350503672991548814691003258⟩ ⟨false, 0⟩ ⟨false, 343040425425757800032663212491238721357223507076279879602480745361402079238⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1550_1600 : bothSeg evalE (oGrid.idx 1550) (oGrid.dm 1550) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1550) oGrid.kl oGrid.kr 400 1600 ⟨false, 343040425425757800032663212491238721357223507076279879602480745361402079238⟩ ⟨false, 0⟩ ⟨false, 515803990771692976945131940394140058517928309049487324121568092648875658232⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1550_2000 : bothSeg evalE (oGrid.idx 1550) (oGrid.dm 1550) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1550) oGrid.kl oGrid.kr 400 2000 ⟨false, 515803990771692976945131940394140058517928309049487324121568092648875658232⟩ ⟨false, 0⟩ ⟨false, 736162006329887534246715305334338026326211931588938214867038710765171494814⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1550_2400 : bothLoop evalE (oGrid.idx 1550) (oGrid.dm 1550) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1550) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 736162006329887534246715305334338026326211931588938214867038710765171494814⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1550 : oGrid.row evalE 1550 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1550_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1550_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1550_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1550_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1550_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1550_2000).1 (bothLoop_sound b_1550_2400).1))))))

theorem n_row_1550 : nGrid.row evalE 1550 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1550_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1550_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1550_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1550_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1550_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1550_2000).2 (bothLoop_sound b_1550_2400).2))))))

theorem b_1551_0 : bothSeg evalE (oGrid.idx 1551) (oGrid.dm 1551) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1551) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77897103204485447065945717664204232201058885356020000762152665154550421732⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1551_400 : bothSeg evalE (oGrid.idx 1551) (oGrid.dm 1551) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1551) oGrid.kl oGrid.kr 400 400 ⟨false, 77897103204485447065945717664204232201058885356020000762152665154550421732⟩ ⟨false, 0⟩ ⟨false, 140851008594852034007872395718076408326574757015064203533971488335488921306⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1551_800 : bothSeg evalE (oGrid.idx 1551) (oGrid.dm 1551) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1551) oGrid.kl oGrid.kr 400 800 ⟨false, 140851008594852034007872395718076408326574757015064203533971488335488921306⟩ ⟨false, 0⟩ ⟨false, 219427768324188882499654210019583646101213775613769031759927046469653712974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1551_1200 : bothSeg evalE (oGrid.idx 1551) (oGrid.dm 1551) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1551) oGrid.kl oGrid.kr 400 1200 ⟨false, 219427768324188882499654210019583646101213775613769031759927046469653712974⟩ ⟨false, 0⟩ ⟨false, 343526429757442419976906580125892060978202480065421025817010221326145904824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1551_1600 : bothSeg evalE (oGrid.idx 1551) (oGrid.dm 1551) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1551) oGrid.kl oGrid.kr 400 1600 ⟨false, 343526429757442419976906580125892060978202480065421025817010221326145904824⟩ ⟨false, 0⟩ ⟨false, 516558747601892984494032380957034613201482675686173914439397126522483576028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1551_2000 : bothSeg evalE (oGrid.idx 1551) (oGrid.dm 1551) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1551) oGrid.kl oGrid.kr 400 2000 ⟨false, 516558747601892984494032380957034613201482675686173914439397126522483576028⟩ ⟨false, 0⟩ ⟨false, 737155799693606569367928999968305148089290283630367877790846388332698459242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1551_2400 : bothLoop evalE (oGrid.idx 1551) (oGrid.dm 1551) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1551) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 737155799693606569367928999968305148089290283630367877790846388332698459242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1551 : oGrid.row evalE 1551 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1551_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1551_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1551_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1551_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1551_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1551_2000).1 (bothLoop_sound b_1551_2400).1))))))

theorem n_row_1551 : nGrid.row evalE 1551 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1551_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1551_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1551_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1551_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1551_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1551_2000).2 (bothLoop_sound b_1551_2400).2))))))

theorem b_1552_0 : bothSeg evalE (oGrid.idx 1552) (oGrid.dm 1552) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1552) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77907769917309257945440996176854361535879132955464551275622062850072192264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1552_400 : bothSeg evalE (oGrid.idx 1552) (oGrid.dm 1552) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1552) oGrid.kl oGrid.kr 400 400 ⟨false, 77907769917309257945440996176854361535879132955464551275622062850072192264⟩ ⟨false, 0⟩ ⟨false, 140681497135142386049766967256255602223908275561723235269029232442661065656⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1552_800 : bothSeg evalE (oGrid.idx 1552) (oGrid.dm 1552) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1552) oGrid.kl oGrid.kr 400 800 ⟨false, 140681497135142386049766967256255602223908275561723235269029232442661065656⟩ ⟨false, 0⟩ ⟨false, 219598043010000029572259169040728717374039650765794772498139815541243421082⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1552_1200 : bothSeg evalE (oGrid.idx 1552) (oGrid.dm 1552) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1552) oGrid.kl oGrid.kr 400 1200 ⟨false, 219598043010000029572259169040728717374039650765794772498139815541243421082⟩ ⟨false, 0⟩ ⟨false, 344002275824096383068823845939511290542748435628171977896578081869250399948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1552_1600 : bothSeg evalE (oGrid.idx 1552) (oGrid.dm 1552) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1552) oGrid.kl oGrid.kr 400 1600 ⟨false, 344002275824096383068823845939511290542748435628171977896578081869250399948⟩ ⟨false, 0⟩ ⟨false, 517303356531499086888616932753369603127858532700573465979266012931016472822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1552_2000 : bothSeg evalE (oGrid.idx 1552) (oGrid.dm 1552) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1552) oGrid.kl oGrid.kr 400 2000 ⟨false, 517303356531499086888616932753369603127858532700573465979266012931016472822⟩ ⟨false, 0⟩ ⟨false, 738139473709670929507042598781622429133062479367886885113272901927033662552⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1552_2400 : bothLoop evalE (oGrid.idx 1552) (oGrid.dm 1552) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1552) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 738139473709670929507042598781622429133062479367886885113272901927033662552⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1552 : oGrid.row evalE 1552 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1552_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1552_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1552_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1552_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1552_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1552_2000).1 (bothLoop_sound b_1552_2400).1))))))

theorem n_row_1552 : nGrid.row evalE 1552 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1552_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1552_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1552_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1552_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1552_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1552_2000).2 (bothLoop_sound b_1552_2400).2))))))

theorem b_1553_0 : bothSeg evalE (oGrid.idx 1553) (oGrid.dm 1553) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1553) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77902710771947761547215101951129847913544243687192844288626925981849671484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1553_400 : bothSeg evalE (oGrid.idx 1553) (oGrid.dm 1553) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1553) oGrid.kl oGrid.kr 400 400 ⟨false, 77902710771947761547215101951129847913544243687192844288626925981849671484⟩ ⟨false, 0⟩ ⟨false, 140501513414351738516090082135052121269910614918075026603658099383341478636⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1553_800 : bothSeg evalE (oGrid.idx 1553) (oGrid.dm 1553) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1553) oGrid.kl oGrid.kr 400 800 ⟨false, 140501513414351738516090082135052121269910614918075026603658099383341478636⟩ ⟨false, 0⟩ ⟨false, 219758445709087831430160099381950932752880424663981835042063567127263007372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1553_1200 : bothSeg evalE (oGrid.idx 1553) (oGrid.dm 1553) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1553) oGrid.kl oGrid.kr 400 1200 ⟨false, 219758445709087831430160099381950932752880424663981835042063567127263007372⟩ ⟨false, 0⟩ ⟨false, 344468228183511905097846280894243296418961663478487689856742402736723160146⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1553_1600 : bothSeg evalE (oGrid.idx 1553) (oGrid.dm 1553) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1553) oGrid.kl oGrid.kr 400 1600 ⟨false, 344468228183511905097846280894243296418961663478487689856742402736723160146⟩ ⟨false, 0⟩ ⟨false, 518038082065727614878340960045613963642580101363780813890047800308043464992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1553_2000 : bothSeg evalE (oGrid.idx 1553) (oGrid.dm 1553) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1553) oGrid.kl oGrid.kr 400 2000 ⟨false, 518038082065727614878340960045613963642580101363780813890047800308043464992⟩ ⟨false, 0⟩ ⟨false, 739113292827092983919581514210213679786860116956174259848583705672378062346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1553_2400 : bothLoop evalE (oGrid.idx 1553) (oGrid.dm 1553) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1553) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 739113292827092983919581514210213679786860116956174259848583705672378062346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1553 : oGrid.row evalE 1553 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1553_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1553_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1553_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1553_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1553_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1553_2000).1 (bothLoop_sound b_1553_2400).1))))))

theorem n_row_1553 : nGrid.row evalE 1553 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1553_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1553_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1553_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1553_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1553_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1553_2000).2 (bothLoop_sound b_1553_2400).2))))))

theorem b_1554_0 : bothSeg evalE (oGrid.idx 1554) (oGrid.dm 1554) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1554) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77881959293149058795240139207771557735016716645560086308230917173979970446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1554_400 : bothSeg evalE (oGrid.idx 1554) (oGrid.dm 1554) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1554) oGrid.kl oGrid.kr 400 400 ⟨false, 77881959293149058795240139207771557735016716645560086308230917173979970446⟩ ⟨false, 0⟩ ⟨false, 140311362948114379794655117289528667031209016803524911205850681179824737090⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1554_800 : bothSeg evalE (oGrid.idx 1554) (oGrid.dm 1554) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1554) oGrid.kl oGrid.kr 400 800 ⟨false, 140311362948114379794655117289528667031209016803524911205850681179824737090⟩ ⟨false, 0⟩ ⟨false, 219909234555678678601674365969000379300006318595184309180786021861534404896⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1554_1200 : bothSeg evalE (oGrid.idx 1554) (oGrid.dm 1554) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1554) oGrid.kl oGrid.kr 400 1200 ⟨false, 219909234555678678601674365969000379300006318595184309180786021861534404896⟩ ⟨false, 0⟩ ⟨false, 344924544943809796118621325649816807597017873106911082967229247738175407726⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1554_1600 : bothSeg evalE (oGrid.idx 1554) (oGrid.dm 1554) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1554) oGrid.kl oGrid.kr 400 1600 ⟨false, 344924544943809796118621325649816807597017873106911082967229247738175407726⟩ ⟨false, 0⟩ ⟨false, 518763182260222758931778886755930130545669491883454028996646902740000081880⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1554_2000 : bothSeg evalE (oGrid.idx 1554) (oGrid.dm 1554) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1554) oGrid.kl oGrid.kr 400 2000 ⟨false, 518763182260222758931778886755930130545669491883454028996646902740000081880⟩ ⟨false, 0⟩ ⟨false, 740077515045388112252130000106998854033186675129330791174434763187066633856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1554_2400 : bothLoop evalE (oGrid.idx 1554) (oGrid.dm 1554) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1554) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 740077515045388112252130000106998854033186675129330791174434763187066633856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1554 : oGrid.row evalE 1554 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1554_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1554_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1554_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1554_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1554_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1554_2000).1 (bothLoop_sound b_1554_2400).1))))))

theorem n_row_1554 : nGrid.row evalE 1554 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1554_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1554_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1554_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1554_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1554_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1554_2000).2 (bothLoop_sound b_1554_2400).2))))))

theorem b_1555_0 : bothSeg evalE (oGrid.idx 1555) (oGrid.dm 1555) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1555) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77845557950445571711451484658001853452423901822690925102900269680538171174⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1555_400 : bothSeg evalE (oGrid.idx 1555) (oGrid.dm 1555) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1555) oGrid.kl oGrid.kr 400 400 ⟨false, 77845557950445571711451484658001853452423901822690925102900269680538171174⟩ ⟨false, 0⟩ ⟨false, 140111359558834706623603989162800884767069029862388621576183630142054422188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1555_800 : bothSeg evalE (oGrid.idx 1555) (oGrid.dm 1555) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1555) oGrid.kl oGrid.kr 400 800 ⟨false, 140111359558834706623603989162800884767069029862388621576183630142054422188⟩ ⟨false, 0⟩ ⟨false, 220050678808235289664458767366278358785748811729071968429649876157890682512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1555_1200 : bothSeg evalE (oGrid.idx 1555) (oGrid.dm 1555) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1555) oGrid.kl oGrid.kr 400 1200 ⟨false, 220050678808235289664458767366278358785748811729071968429649876157890682512⟩ ⟨false, 0⟩ ⟨false, 345371495337437998149745658276722991324250491526593319466007644485110589498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1555_1600 : bothSeg evalE (oGrid.idx 1555) (oGrid.dm 1555) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1555) oGrid.kl oGrid.kr 400 1600 ⟨false, 345371495337437998149745658276722991324250491526593319466007644485110589498⟩ ⟨false, 0⟩ ⟨false, 519478926295054946588920614760876121482392310792596988234547184581160299740⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1555_2000 : bothSeg evalE (oGrid.idx 1555) (oGrid.dm 1555) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1555) oGrid.kl oGrid.kr 400 2000 ⟨false, 519478926295054946588920614760876121482392310792596988234547184581160299740⟩ ⟨false, 0⟩ ⟨false, 741032409488573003472630979168256707378767533570672906297610560148024568120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1555_2400 : bothLoop evalE (oGrid.idx 1555) (oGrid.dm 1555) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1555) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 741032409488573003472630979168256707378767533570672906297610560148024568120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1555 : oGrid.row evalE 1555 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1555_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1555_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1555_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1555_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1555_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1555_2000).1 (bothLoop_sound b_1555_2400).1))))))

theorem n_row_1555 : nGrid.row evalE 1555 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1555_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1555_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1555_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1555_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1555_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1555_2000).2 (bothLoop_sound b_1555_2400).2))))))

theorem b_1556_0 : bothSeg evalE (oGrid.idx 1556) (oGrid.dm 1556) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1556) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77793597600634131522405938831608505834477080381013387006873352334530504812⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1556_400 : bothSeg evalE (oGrid.idx 1556) (oGrid.dm 1556) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1556) oGrid.kl oGrid.kr 400 400 ⟨false, 77793597600634131522405938831608505834477080381013387006873352334530504812⟩ ⟨false, 0⟩ ⟨false, 139901844164505449413375082698941316235012436319825684306542881938536126414⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1556_800 : bothSeg evalE (oGrid.idx 1556) (oGrid.dm 1556) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1556) oGrid.kl oGrid.kr 400 800 ⟨false, 139901844164505449413375082698941316235012436319825684306542881938536126414⟩ ⟨false, 0⟩ ⟨false, 220183075197916454228681607412325388344744500929777397370937668991752392716⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1556_1200 : bothSeg evalE (oGrid.idx 1556) (oGrid.dm 1556) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1556) oGrid.kl oGrid.kr 400 1200 ⟨false, 220183075197916454228681607412325388344744500929777397370937668991752392716⟩ ⟨false, 0⟩ ⟨false, 345809376069631115052062489984278289218091413184365861284397875277715006632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1556_1600 : bothSeg evalE (oGrid.idx 1556) (oGrid.dm 1556) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1556) oGrid.kl oGrid.kr 400 1600 ⟨false, 345809376069631115052062489984278289218091413184365861284397875277715006632⟩ ⟨false, 0⟩ ⟨false, 520185610823180212212592780678953338221050062821486729858798363625734411584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1556_2000 : bothSeg evalE (oGrid.idx 1556) (oGrid.dm 1556) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1556) oGrid.kl oGrid.kr 400 2000 ⟨false, 520185610823180212212592780678953338221050062821486729858798363625734411584⟩ ⟨false, 0⟩ ⟨false, 741978272753624947225638205526208742419395946520562992963480803369972971086⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1556_2400 : bothLoop evalE (oGrid.idx 1556) (oGrid.dm 1556) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1556) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 741978272753624947225638205526208742419395946520562992963480803369972971086⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1556 : oGrid.row evalE 1556 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1556_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1556_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1556_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1556_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1556_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1556_2000).1 (bothLoop_sound b_1556_2400).1))))))

theorem n_row_1556 : nGrid.row evalE 1556 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1556_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1556_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1556_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1556_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1556_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1556_2000).2 (bothLoop_sound b_1556_2400).2))))))

theorem b_1557_0 : bothSeg evalE (oGrid.idx 1557) (oGrid.dm 1557) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1557) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77726188213802268390689230347547110968762134865310669045918538614074447792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1557_400 : bothSeg evalE (oGrid.idx 1557) (oGrid.dm 1557) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1557) oGrid.kl oGrid.kr 400 400 ⟨false, 77726188213802268390689230347547110968762134865310669045918538614074447792⟩ ⟨false, 0⟩ ⟨false, 139683183165651912994700565544657080099146864004176732414979831867747688632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1557_800 : bothSeg evalE (oGrid.idx 1557) (oGrid.dm 1557) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1557) oGrid.kl oGrid.kr 400 800 ⟨false, 139683183165651912994700565544657080099146864004176732414979831867747688632⟩ ⟨false, 0⟩ ⟨false, 220306749041346443873601839323163050911148972160973746144660132138495248558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1557_1200 : bothSeg evalE (oGrid.idx 1557) (oGrid.dm 1557) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1557) oGrid.kl oGrid.kr 400 1200 ⟨false, 220306749041346443873601839323163050911148972160973746144660132138495248558⟩ ⟨false, 0⟩ ⟨false, 346238512431179610823486264720495225288320143241438835329860185820486776658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1557_1600 : bothSeg evalE (oGrid.idx 1557) (oGrid.dm 1557) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1557) oGrid.kl oGrid.kr 400 1600 ⟨false, 346238512431179610823486264720495225288320143241438835329860185820486776658⟩ ⟨false, 0⟩ ⟨false, 520883561083209235375808925186855830934296434926743132330944841421347294564⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1557_2000 : bothSeg evalE (oGrid.idx 1557) (oGrid.dm 1557) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1557) oGrid.kl oGrid.kr 400 2000 ⟨false, 520883561083209235375808925186855830934296434926743132330944841421347294564⟩ ⟨false, 0⟩ ⟨false, 742915430023250793849522651531259939844718087999368245700490901143752723252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1557_2400 : bothLoop evalE (oGrid.idx 1557) (oGrid.dm 1557) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1557) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 742915430023250793849522651531259939844718087999368245700490901143752723252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1557 : oGrid.row evalE 1557 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1557_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1557_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1557_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1557_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1557_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1557_2000).1 (bothLoop_sound b_1557_2400).1))))))

theorem n_row_1557 : nGrid.row evalE 1557 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1557_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1557_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1557_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1557_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1557_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1557_2000).2 (bothLoop_sound b_1557_2400).2))))))

theorem b_1558_0 : bothSeg evalE (oGrid.idx 1558) (oGrid.dm 1558) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1558) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77643449091705107013040484729623275525558288550085534614944392736269775614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1558_400 : bothSeg evalE (oGrid.idx 1558) (oGrid.dm 1558) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1558) oGrid.kl oGrid.kr 400 400 ⟨false, 77643449091705107013040484729623275525558288550085534614944392736269775614⟩ ⟨false, 0⟩ ⟨false, 139455739793719120056459321268582248546325863147991571518427080773276276590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1558_800 : bothSeg evalE (oGrid.idx 1558) (oGrid.dm 1558) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1558) oGrid.kl oGrid.kr 400 800 ⟨false, 139455739793719120056459321268582248546325863147991571518427080773276276590⟩ ⟨false, 0⟩ ⟨false, 220422022118602476645122072383722948500742183984603244391058329432727665152⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1558_1200 : bothSeg evalE (oGrid.idx 1558) (oGrid.dm 1558) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1558) oGrid.kl oGrid.kr 400 1200 ⟨false, 220422022118602476645122072383722948500742183984603244391058329432727665152⟩ ⟨false, 0⟩ ⟨false, 346659226176417061916969497648949153205898576558263084500832491025508963706⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1558_1600 : bothSeg evalE (oGrid.idx 1558) (oGrid.dm 1558) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1558) oGrid.kl oGrid.kr 400 1600 ⟨false, 346659226176417061916969497648949153205898576558263084500832491025508963706⟩ ⟨false, 0⟩ ⟨false, 521573098777394433491503688032017312535283561228329560541999282811853116668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1558_2000 : bothSeg evalE (oGrid.idx 1558) (oGrid.dm 1558) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1558) oGrid.kl oGrid.kr 400 2000 ⟨false, 521573098777394433491503688032017312535283561228329560541999282811853116668⟩ ⟨false, 0⟩ ⟨false, 743844202943873968662285185807522043949355929133289290951186425579191861832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1558_2400 : bothLoop evalE (oGrid.idx 1558) (oGrid.dm 1558) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1558) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 743844202943873968662285185807522043949355929133289290951186425579191861832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1558 : oGrid.row evalE 1558 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1558_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1558_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1558_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1558_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1558_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1558_2000).1 (bothLoop_sound b_1558_2400).1))))))

theorem n_row_1558 : nGrid.row evalE 1558 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1558_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1558_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1558_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1558_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1558_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1558_2000).2 (bothLoop_sound b_1558_2400).2))))))

theorem b_1559_0 : bothSeg evalE (oGrid.idx 1559) (oGrid.dm 1559) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1559) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77545527030250801143932914866753370588374500586314299011766811752078517688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1559_400 : bothSeg evalE (oGrid.idx 1559) (oGrid.dm 1559) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1559) oGrid.kl oGrid.kr 400 400 ⟨false, 77545527030250801143932914866753370588374500586314299011766811752078517688⟩ ⟨false, 0⟩ ⟨false, 139219896710113914837145380565695089112310794265569989274476197572785664820⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1559_800 : bothSeg evalE (oGrid.idx 1559) (oGrid.dm 1559) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1559) oGrid.kl oGrid.kr 400 800 ⟨false, 139219896710113914837145380565695089112310794265569989274476197572785664820⟩ ⟨false, 0⟩ ⟨false, 220529238954182375695375696476550478520462027005955178403374326792527867474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1559_1200 : bothSeg evalE (oGrid.idx 1559) (oGrid.dm 1559) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1559) oGrid.kl oGrid.kr 400 1200 ⟨false, 220529238954182375695375696476550478520462027005955178403374326792527867474⟩ ⟨false, 0⟩ ⟨false, 347071861804187604161721658411077105879172513497030319799943460424553723118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1559_1600 : bothSeg evalE (oGrid.idx 1559) (oGrid.dm 1559) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1559) oGrid.kl oGrid.kr 400 1600 ⟨false, 347071861804187604161721658411077105879172513497030319799943460424553723118⟩ ⟨false, 0⟩ ⟨false, 522254568352597249264600796386697540403503703274673001665695409267757192396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1559_2000 : bothSeg evalE (oGrid.idx 1559) (oGrid.dm 1559) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1559) oGrid.kl oGrid.kr 400 2000 ⟨false, 522254568352597249264600796386697540403503703274673001665695409267757192396⟩ ⟨false, 0⟩ ⟨false, 744764935906601681096121405466547276663363684990707327794284189005040213466⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1559_2400 : bothLoop evalE (oGrid.idx 1559) (oGrid.dm 1559) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1559) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 744764935906601681096121405466547276663363684990707327794284189005040213466⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1559 : oGrid.row evalE 1559 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1559_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1559_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1559_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1559_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1559_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1559_2000).1 (bothLoop_sound b_1559_2400).1))))))

theorem n_row_1559 : nGrid.row evalE 1559 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1559_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1559_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1559_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1559_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1559_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1559_2000).2 (bothLoop_sound b_1559_2400).2))))))

theorem o_blk_1536 : allFrom (fun j => oGrid.row evalE j) 1536 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1536) o_row_1536 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1537) o_row_1537 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1538) o_row_1538 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1539) o_row_1539 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1540) o_row_1540 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1541) o_row_1541 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1542) o_row_1542 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1543) o_row_1543 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1544) o_row_1544 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1545) o_row_1545 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1546) o_row_1546 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1547) o_row_1547 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1548) o_row_1548 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1549) o_row_1549 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1550) o_row_1550 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1551) o_row_1551 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1552) o_row_1552 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1553) o_row_1553 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1554) o_row_1554 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1555) o_row_1555 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1556) o_row_1556 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1557) o_row_1557 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1558) o_row_1558 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1559) o_row_1559 (allFrom_zero (fun j => oGrid.row evalE j) 1560)))))))))))))))))))))))))

theorem n_blk_1536 : allFrom (fun j => nGrid.row evalE j) 1536 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1536) n_row_1536 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1537) n_row_1537 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1538) n_row_1538 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1539) n_row_1539 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1540) n_row_1540 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1541) n_row_1541 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1542) n_row_1542 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1543) n_row_1543 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1544) n_row_1544 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1545) n_row_1545 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1546) n_row_1546 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1547) n_row_1547 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1548) n_row_1548 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1549) n_row_1549 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1550) n_row_1550 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1551) n_row_1551 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1552) n_row_1552 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1553) n_row_1553 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1554) n_row_1554 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1555) n_row_1555 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1556) n_row_1556 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1557) n_row_1557 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1558) n_row_1558 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1559) n_row_1559 (allFrom_zero (fun j => nGrid.row evalE j) 1560)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
