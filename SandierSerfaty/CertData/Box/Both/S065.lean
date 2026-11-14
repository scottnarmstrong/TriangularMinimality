/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 65 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1560`–`1583`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1560_0 : bothSeg evalE (oGrid.idx 1560) (oGrid.dm 1560) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1560) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77432603029188990700935753317707378380583599536645993447868143366350863528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1560_400 : bothSeg evalE (oGrid.idx 1560) (oGrid.dm 1560) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1560) oGrid.kl oGrid.kr 400 400 ⟨false, 77432603029188990700935753317707378380583599536645993447868143366350863528⟩ ⟨false, 0⟩ ⟨false, 138976061731293684920018844250905188239656219387366415965672551416136309932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1560_800 : bothSeg evalE (oGrid.idx 1560) (oGrid.dm 1560) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1560) oGrid.kl oGrid.kr 400 800 ⟨false, 138976061731293684920018844250905188239656219387366415965672551416136309932⟩ ⟨false, 0⟩ ⟨false, 220628768834760675933152215854553039322270424348671927030668013884206687472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1560_1200 : bothSeg evalE (oGrid.idx 1560) (oGrid.dm 1560) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1560) oGrid.kl oGrid.kr 400 1200 ⟨false, 220628768834760675933152215854553039322270424348671927030668013884206687472⟩ ⟨false, 0⟩ ⟨false, 347476788575601828155535545334370404625043951491752912427370884885264165386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1560_1600 : bothSeg evalE (oGrid.idx 1560) (oGrid.dm 1560) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1560) oGrid.kl oGrid.kr 400 1600 ⟨false, 347476788575601828155535545334370404625043951491752912427370884885264165386⟩ ⟨false, 0⟩ ⟨false, 522928339018043886834109641591696549586318215903367633803837589875875833030⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1560_2000 : bothSeg evalE (oGrid.idx 1560) (oGrid.dm 1560) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1560) oGrid.kl oGrid.kr 400 2000 ⟨false, 522928339018043886834109641591696549586318215903367633803837589875875833030⟩ ⟨false, 0⟩ ⟨false, 745677998064980582548628656481357947033863560286505420882809051060787042224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1560_2400 : bothLoop evalE (oGrid.idx 1560) (oGrid.dm 1560) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1560) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 745677998064980582548628656481357947033863560286505420882809051060787042224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1560 : oGrid.row evalE 1560 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1560_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1560_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1560_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1560_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1560_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1560_2000).1 (bothLoop_sound b_1560_2400).1))))))

theorem n_row_1560 : nGrid.row evalE 1560 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1560_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1560_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1560_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1560_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1560_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1560_2000).2 (bothLoop_sound b_1560_2400).2))))))

theorem b_1561_0 : bothSeg evalE (oGrid.idx 1561) (oGrid.dm 1561) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1561) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77304875797040924994259395147132311769923065220119261630112341403787231148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1561_400 : bothSeg evalE (oGrid.idx 1561) (oGrid.dm 1561) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1561) oGrid.kl oGrid.kr 400 400 ⟨false, 77304875797040924994259395147132311769923065220119261630112341403787231148⟩ ⟨false, 0⟩ ⟨false, 138724649482485933321804632663459494147858165830817503483833478511322476922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1561_800 : bothSeg evalE (oGrid.idx 1561) (oGrid.dm 1561) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1561) oGrid.kl oGrid.kr 400 800 ⟨false, 138724649482485933321804632663459494147858165830817503483833478511322476922⟩ ⟨false, 0⟩ ⟨false, 220720990861837660823194713689488795051644163101217776346426369523193809956⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1561_1200 : bothSeg evalE (oGrid.idx 1561) (oGrid.dm 1561) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1561) oGrid.kl oGrid.kr 400 1200 ⟨false, 220720990861837660823194713689488795051644163101217776346426369523193809956⟩ ⟨false, 0⟩ ⟨false, 347874385566685605265308129279790664751392995976806716826515548115018248032⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1561_1600 : bothSeg evalE (oGrid.idx 1561) (oGrid.dm 1561) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1561) oGrid.kl oGrid.kr 400 1600 ⟨false, 347874385566685605265308129279790664751392995976806716826515548115018248032⟩ ⟨false, 0⟩ ⟨false, 523594789797973978742176262583450513456327288393747026847982356407337180104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1561_2000 : bothSeg evalE (oGrid.idx 1561) (oGrid.dm 1561) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1561) oGrid.kl oGrid.kr 400 2000 ⟨false, 523594789797973978742176262583450513456327288393747026847982356407337180104⟩ ⟨false, 0⟩ ⟨false, 746583768387645355087775445568935180968167605172640449211427740754641476328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1561_2400 : bothLoop evalE (oGrid.idx 1561) (oGrid.dm 1561) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1561) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 746583768387645355087775445568935180968167605172640449211427740754641476328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1561 : oGrid.row evalE 1561 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1561_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1561_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1561_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1561_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1561_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1561_2000).1 (bothLoop_sound b_1561_2400).1))))))

theorem n_row_1561 : nGrid.row evalE 1561 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1561_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1561_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1561_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1561_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1561_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1561_2000).2 (bothLoop_sound b_1561_2400).2))))))

theorem b_1562_0 : bothSeg evalE (oGrid.idx 1562) (oGrid.dm 1562) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1562) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77162558028024731083866357097851049345420955295702015943030951341189339132⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1562_400 : bothSeg evalE (oGrid.idx 1562) (oGrid.dm 1562) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1562) oGrid.kl oGrid.kr 400 400 ⟨false, 77162558028024731083866357097851049345420955295702015943030951341189339132⟩ ⟨false, 0⟩ ⟨false, 138466081882030423611132049761669260063919962852313555004577991329622743070⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1562_800 : bothSeg evalE (oGrid.idx 1562) (oGrid.dm 1562) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1562) oGrid.kl oGrid.kr 400 800 ⟨false, 138466081882030423611132049761669260063919962852313555004577991329622743070⟩ ⟨false, 0⟩ ⟨false, 220806290795086316553725410835497266804512164577225641372964307512938714766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1562_1200 : bothSeg evalE (oGrid.idx 1562) (oGrid.dm 1562) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1562) oGrid.kl oGrid.kr 400 1200 ⟨false, 220806290795086316553725410835497266804512164577225641372964307512938714766⟩ ⟨false, 0⟩ ⟨false, 348265038511726831454166588444194640394227888130207221039683510662081324944⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1562_1600 : bothSeg evalE (oGrid.idx 1562) (oGrid.dm 1562) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1562) oGrid.kl oGrid.kr 400 1600 ⟨false, 348265038511726831454166588444194640394227888130207221039683510662081324944⟩ ⟨false, 0⟩ ⟨false, 524254306374987170948337791181089944824507750202914441803672032601929738036⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1562_2000 : bothSeg evalE (oGrid.idx 1562) (oGrid.dm 1562) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1562) oGrid.kl oGrid.kr 400 2000 ⟨false, 524254306374987170948337791181089944824507750202914441803672032601929738036⟩ ⟨false, 0⟩ ⟨false, 747482632501665218229075832294119864158018474462780208844104263663090786632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1562_2400 : bothLoop evalE (oGrid.idx 1562) (oGrid.dm 1562) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1562) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 747482632501665218229075832294119864158018474462780208844104263663090786632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1562 : oGrid.row evalE 1562 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1562_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1562_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1562_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1562_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1562_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1562_2000).1 (bothLoop_sound b_1562_2400).1))))))

theorem n_row_1562 : nGrid.row evalE 1562 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1562_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1562_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1562_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1562_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1562_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1562_2000).2 (bothLoop_sound b_1562_2400).2))))))

theorem b_1563_0 : bothSeg evalE (oGrid.idx 1563) (oGrid.dm 1563) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1563) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 77005902059042472233522128258313590571893845667194021250926587490514024718⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1563_400 : bothSeg evalE (oGrid.idx 1563) (oGrid.dm 1563) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1563) oGrid.kl oGrid.kr 400 400 ⟨false, 77005902059042472233522128258313590571893845667194021250926587490514024718⟩ ⟨false, 0⟩ ⟨false, 138200811889092402627877253312154457315164385480797485904221899667427231252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1563_800 : bothSeg evalE (oGrid.idx 1563) (oGrid.dm 1563) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1563) oGrid.kl oGrid.kr 400 800 ⟨false, 138200811889092402627877253312154457315164385480797485904221899667427231252⟩ ⟨false, 0⟩ ⟨false, 220885089135874055626779193979779953057690971698641315042356789103777724442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1563_1200 : bothSeg evalE (oGrid.idx 1563) (oGrid.dm 1563) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1563) oGrid.kl oGrid.kr 400 1200 ⟨false, 220885089135874055626779193979779953057690971698641315042356789103777724442⟩ ⟨false, 0⟩ ⟨false, 348649167886796940988835866181594581272675066239032764261742774903844399814⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1563_1600 : bothSeg evalE (oGrid.idx 1563) (oGrid.dm 1563) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1563) oGrid.kl oGrid.kr 400 1600 ⟨false, 348649167886796940988835866181594581272675066239032764261742774903844399814⟩ ⟨false, 0⟩ ⟨false, 524907309173564477942454522951671085976403713531944947457105748108684136368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1563_2000 : bothSeg evalE (oGrid.idx 1563) (oGrid.dm 1563) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1563) oGrid.kl oGrid.kr 400 2000 ⟨false, 524907309173564477942454522951671085976403713531944947457105748108684136368⟩ ⟨false, 0⟩ ⟨false, 748375010776065205838635649508472140658054857050681648806772437900214793902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1563_2400 : bothLoop evalE (oGrid.idx 1563) (oGrid.dm 1563) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1563) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 748375010776065205838635649508472140658054857050681648806772437900214793902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1563 : oGrid.row evalE 1563 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1563_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1563_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1563_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1563_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1563_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1563_2000).1 (bothLoop_sound b_1563_2400).1))))))

theorem n_row_1563 : nGrid.row evalE 1563 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1563_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1563_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1563_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1563_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1563_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1563_2000).2 (bothLoop_sound b_1563_2400).2))))))

theorem b_1564_0 : bothSeg evalE (oGrid.idx 1564) (oGrid.dm 1564) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1564) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76835182740964760766157019578018090699906467887909584210980455383407866538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1564_400 : bothSeg evalE (oGrid.idx 1564) (oGrid.dm 1564) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1564) oGrid.kl oGrid.kr 400 400 ⟨false, 76835182740964760766157019578018090699906467887909584210980455383407866538⟩ ⟨false, 0⟩ ⟨false, 137929304109548493529323709301592657798491056243362852129332516153066988762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1564_800 : bothSeg evalE (oGrid.idx 1564) (oGrid.dm 1564) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1564) oGrid.kl oGrid.kr 400 800 ⟨false, 137929304109548493529323709301592657798491056243362852129332516153066988762⟩ ⟨false, 0⟩ ⟨false, 220957817087638981238588944591792050561821816539767463158109132578174711278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1564_1200 : bothSeg evalE (oGrid.idx 1564) (oGrid.dm 1564) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1564) oGrid.kl oGrid.kr 400 1200 ⟨false, 220957817087638981238588944591792050561821816539767463158109132578174711278⟩ ⟨false, 0⟩ ⟨false, 349027204870126961393549737455488640397868461385490909635151451991091068150⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1564_1600 : bothSeg evalE (oGrid.idx 1564) (oGrid.dm 1564) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1564) oGrid.kl oGrid.kr 400 1600 ⟨false, 349027204870126961393549737455488640397868461385490909635151451991091068150⟩ ⟨false, 0⟩ ⟨false, 525554229320444179322458932232695782314086817574695025252348980925919950010⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1564_2000 : bothSeg evalE (oGrid.idx 1564) (oGrid.dm 1564) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1564) oGrid.kl oGrid.kr 400 2000 ⟨false, 525554229320444179322458932232695782314086817574695025252348980925919950010⟩ ⟨false, 0⟩ ⟨false, 749261334282201984528401708329954285273026674908817788543119084527427771696⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1564_2400 : bothLoop evalE (oGrid.idx 1564) (oGrid.dm 1564) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1564) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 749261334282201984528401708329954285273026674908817788543119084527427771696⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1564 : oGrid.row evalE 1564 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1564_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1564_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1564_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1564_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1564_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1564_2000).1 (bothLoop_sound b_1564_2400).1))))))

theorem n_row_1564 : nGrid.row evalE 1564 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1564_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1564_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1564_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1564_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1564_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1564_2000).2 (bothLoop_sound b_1564_2400).2))))))

theorem b_1565_0 : bothSeg evalE (oGrid.idx 1565) (oGrid.dm 1565) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1565) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76650679836872189131875887014095630241027270725161901324533432979430668928⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1565_400 : bothSeg evalE (oGrid.idx 1565) (oGrid.dm 1565) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1565) oGrid.kl oGrid.kr 400 400 ⟨false, 76650679836872189131875887014095630241027270725161901324533432979430668928⟩ ⟨false, 0⟩ ⟨false, 137652016307440771848000773535359634244429402152024854935840539527789330806⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1565_800 : bothSeg evalE (oGrid.idx 1565) (oGrid.dm 1565) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1565) oGrid.kl oGrid.kr 400 800 ⟨false, 137652016307440771848000773535359634244429402152024854935840539527789330806⟩ ⟨false, 0⟩ ⟨false, 221024901673325608465788690280654620123232439068053972067616358357917218870⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1565_1200 : bothSeg evalE (oGrid.idx 1565) (oGrid.dm 1565) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1565) oGrid.kl oGrid.kr 400 1200 ⟨false, 221024901673325608465788690280654620123232439068053972067616358357917218870⟩ ⟨false, 0⟩ ⟨false, 349399576459543025665331255329519272096043798829126410776768863445390528562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1565_1600 : bothSeg evalE (oGrid.idx 1565) (oGrid.dm 1565) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1565) oGrid.kl oGrid.kr 400 1600 ⟨false, 349399576459543025665331255329519272096043798829126410776768863445390528562⟩ ⟨false, 0⟩ ⟨false, 526195493762057173851584340503198551800662196820078361796261425892740786696⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1565_2000 : bothSeg evalE (oGrid.idx 1565) (oGrid.dm 1565) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1565) oGrid.kl oGrid.kr 400 2000 ⟨false, 526195493762057173851584340503198551800662196820078361796261425892740786696⟩ ⟨false, 0⟩ ⟨false, 750142029911199129558467690080781949713537596791264134621544898633995790084⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1565_2400 : bothLoop evalE (oGrid.idx 1565) (oGrid.dm 1565) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1565) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 750142029911199129558467690080781949713537596791264134621544898633995790084⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1565 : oGrid.row evalE 1565 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1565_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1565_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1565_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1565_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1565_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1565_2000).1 (bothLoop_sound b_1565_2400).1))))))

theorem n_row_1565 : nGrid.row evalE 1565 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1565_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1565_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1565_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1565_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1565_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1565_2000).2 (bothLoop_sound b_1565_2400).2))))))

theorem b_1566_0 : bothSeg evalE (oGrid.idx 1566) (oGrid.dm 1566) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1566) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76452702273443097594981423690421700718142706490154736984055859263915893574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1566_400 : bothSeg evalE (oGrid.idx 1566) (oGrid.dm 1566) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1566) oGrid.kl oGrid.kr 400 400 ⟨false, 76452702273443097594981423690421700718142706490154736984055859263915893574⟩ ⟨false, 0⟩ ⟨false, 137369431306644822511340876075948131415174699428669226099012696991165140016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1566_800 : bothSeg evalE (oGrid.idx 1566) (oGrid.dm 1566) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1566) oGrid.kl oGrid.kr 400 800 ⟨false, 137369431306644822511340876075948131415174699428669226099012696991165140016⟩ ⟨false, 0⟩ ⟨false, 221086796101765627535961439417170700903649342386300651871920036715400229250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1566_1200 : bothSeg evalE (oGrid.idx 1566) (oGrid.dm 1566) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1566) oGrid.kl oGrid.kr 400 1200 ⟨false, 221086796101765627535961439417170700903649342386300651871920036715400229250⟩ ⟨false, 0⟩ ⟨false, 349766735838846927028230982028248376234670135840778698025156170487021787436⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1566_1600 : bothSeg evalE (oGrid.idx 1566) (oGrid.dm 1566) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1566) oGrid.kl oGrid.kr 400 1600 ⟨false, 349766735838846927028230982028248376234670135840778698025156170487021787436⟩ ⟨false, 0⟩ ⟨false, 526831555630907376272497988726775335125468386547050813112565069562119807122⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1566_2000 : bothSeg evalE (oGrid.idx 1566) (oGrid.dm 1566) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1566) oGrid.kl oGrid.kr 400 2000 ⟨false, 526831555630907376272497988726775335125468386547050813112565069562119807122⟩ ⟨false, 0⟩ ⟨false, 751017550740327443524051626995556992637794923523339063869439677923379162052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1566_2400 : bothLoop evalE (oGrid.idx 1566) (oGrid.dm 1566) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1566) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 751017550740327443524051626995556992637794923523339063869439677923379162052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1566 : oGrid.row evalE 1566 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1566_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1566_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1566_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1566_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1566_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1566_2000).1 (bothLoop_sound b_1566_2400).1))))))

theorem n_row_1566 : nGrid.row evalE 1566 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1566_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1566_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1566_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1566_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1566_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1566_2000).2 (bothLoop_sound b_1566_2400).2))))))

theorem b_1567_0 : bothSeg evalE (oGrid.idx 1567) (oGrid.dm 1567) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1567) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76241591258577168404131605087697169037546136130494998620419063621805609574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1567_400 : bothSeg evalE (oGrid.idx 1567) (oGrid.dm 1567) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1567) oGrid.kl oGrid.kr 400 400 ⟨false, 76241591258577168404131605087697169037546136130494998620419063621805609574⟩ ⟨false, 0⟩ ⟨false, 137082044872519751357324233945673488398907238591412739778801083644016749678⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1567_800 : bothSeg evalE (oGrid.idx 1567) (oGrid.dm 1567) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1567) oGrid.kl oGrid.kr 400 800 ⟨false, 137082044872519751357324233945673488398907238591412739778801083644016749678⟩ ⟨false, 0⟩ ⟨false, 221143968169079613914823565147272363114217785732088906728235267908884435024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1567_1200 : bothSeg evalE (oGrid.idx 1567) (oGrid.dm 1567) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1567) oGrid.kl oGrid.kr 400 1200 ⟨false, 221143968169079613914823565147272363114217785732088906728235267908884435024⟩ ⟨false, 0⟩ ⟨false, 350129150779217620957878106523042634234289762898615894823740385188934351656⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1567_1600 : bothSeg evalE (oGrid.idx 1567) (oGrid.dm 1567) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1567) oGrid.kl oGrid.kr 400 1600 ⟨false, 350129150779217620957878106523042634234289762898615894823740385188934351656⟩ ⟨false, 0⟩ ⟨false, 527462882646973061609529473496950115696433085491108271214717920254415804044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1567_2000 : bothSeg evalE (oGrid.idx 1567) (oGrid.dm 1567) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1567) oGrid.kl oGrid.kr 400 2000 ⟨false, 527462882646973061609529473496950115696433085491108271214717920254415804044⟩ ⟨false, 0⟩ ⟨false, 751888364434406222558525243040299007617983003717792691494569538232726595306⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1567_2400 : bothLoop evalE (oGrid.idx 1567) (oGrid.dm 1567) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1567) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 751888364434406222558525243040299007617983003717792691494569538232726595306⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1567 : oGrid.row evalE 1567 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1567_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1567_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1567_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1567_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1567_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1567_2000).1 (bothLoop_sound b_1567_2400).1))))))

theorem n_row_1567 : nGrid.row evalE 1567 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1567_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1567_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1567_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1567_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1567_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1567_2000).2 (bothLoop_sound b_1567_2400).2))))))

theorem b_1568_0 : bothSeg evalE (oGrid.idx 1568) (oGrid.dm 1568) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1568) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 76017708198894808526673769674093123800162503503855915035113247747123926278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1568_400 : bothSeg evalE (oGrid.idx 1568) (oGrid.dm 1568) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1568) oGrid.kl oGrid.kr 400 400 ⟨false, 76017708198894808526673769674093123800162503503855915035113247747123926278⟩ ⟨false, 0⟩ ⟨false, 136790370916765566118539256623340585200679341965849216533420575134636180832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1568_800 : bothSeg evalE (oGrid.idx 1568) (oGrid.dm 1568) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1568) oGrid.kl oGrid.kr 400 800 ⟨false, 136790370916765566118539256623340585200679341965849216533420575134636180832⟩ ⟨false, 0⟩ ⟨false, 221196905398804464727354753037161267118177974842272191428316285493669852182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1568_1200 : bothSeg evalE (oGrid.idx 1568) (oGrid.dm 1568) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1568) oGrid.kl oGrid.kr 400 1200 ⟨false, 221196905398804464727354753037161267118177974842272191428316285493669852182⟩ ⟨false, 0⟩ ⟨false, 350487308779338453992718389132948130771680407510047236002232101515278889030⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1568_1600 : bothSeg evalE (oGrid.idx 1568) (oGrid.dm 1568) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1568) oGrid.kl oGrid.kr 400 1600 ⟨false, 350487308779338453992718389132948130771680407510047236002232101515278889030⟩ ⟨false, 0⟩ ⟨false, 528089962257833936475203860596102982998777967178120055418719306689647464416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1568_2000 : bothSeg evalE (oGrid.idx 1568) (oGrid.dm 1568) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1568) oGrid.kl oGrid.kr 400 2000 ⟨false, 528089962257833936475203860596102982998777967178120055418719306689647464416⟩ ⟨false, 0⟩ ⟨false, 752754958385930249568892942639567329488602026994021208106330323258457511694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1568_2400 : bothLoop evalE (oGrid.idx 1568) (oGrid.dm 1568) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1568) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 752754958385930249568892942639567329488602026994021208106330323258457511694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1568 : oGrid.row evalE 1568 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1568_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1568_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1568_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1568_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1568_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1568_2000).1 (bothLoop_sound b_1568_2400).1))))))

theorem n_row_1568 : nGrid.row evalE 1568 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1568_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1568_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1568_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1568_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1568_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1568_2000).2 (bothLoop_sound b_1568_2400).2))))))

theorem b_1569_0 : bothSeg evalE (oGrid.idx 1569) (oGrid.dm 1569) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1569) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75781426008032741889308546265462024677421445051747124579730566408121489822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1569_400 : bothSeg evalE (oGrid.idx 1569) (oGrid.dm 1569) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1569) oGrid.kl oGrid.kr 400 400 ⟨false, 75781426008032741889308546265462024677421445051747124579730566408121489822⟩ ⟨false, 0⟩ ⟨false, 136494916811715479729429027380312318315398099251280867888939417702534290250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1569_800 : bothSeg evalE (oGrid.idx 1569) (oGrid.dm 1569) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1569) oGrid.kl oGrid.kr 400 800 ⟨false, 136494916811715479729429027380312318315398099251280867888939417702534290250⟩ ⟨false, 0⟩ ⟨false, 221246090816076681682169582949766329314220839118809955598430467269878253428⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1569_1200 : bothSeg evalE (oGrid.idx 1569) (oGrid.dm 1569) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1569) oGrid.kl oGrid.kr 400 1200 ⟨false, 221246090816076681682169582949766329314220839118809955598430467269878253428⟩ ⟨false, 0⟩ ⟨false, 350841692839580239500301618673778557173985644432265553453553237764389907242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1569_1600 : bothSeg evalE (oGrid.idx 1569) (oGrid.dm 1569) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1569) oGrid.kl oGrid.kr 400 1600 ⟨false, 350841692839580239500301618673778557173985644432265553453553237764389907242⟩ ⟨false, 0⟩ ⟨false, 528713277412854057549277053316512928469033455631602148240499147508513573336⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1569_2000 : bothSeg evalE (oGrid.idx 1569) (oGrid.dm 1569) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1569) oGrid.kl oGrid.kr 400 2000 ⟨false, 528713277412854057549277053316512928469033455631602148240499147508513573336⟩ ⟨false, 0⟩ ⟨false, 753617815489252634672105663871663932119775900858785404839522105261643833554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1569_2400 : bothLoop evalE (oGrid.idx 1569) (oGrid.dm 1569) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1569) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 753617815489252634672105663871663932119775900858785404839522105261643833554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1569 : oGrid.row evalE 1569 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1569_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1569_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1569_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1569_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1569_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1569_2000).1 (bothLoop_sound b_1569_2400).1))))))

theorem n_row_1569 : nGrid.row evalE 1569 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1569_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1569_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1569_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1569_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1569_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1569_2000).2 (bothLoop_sound b_1569_2400).2))))))

theorem b_1570_0 : bothSeg evalE (oGrid.idx 1570) (oGrid.dm 1570) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1570) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75533146996504164390050688711502253283269683762209292794825489775280500278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1570_400 : bothSeg evalE (oGrid.idx 1570) (oGrid.dm 1570) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1570) oGrid.kl oGrid.kr 400 400 ⟨false, 75533146996504164390050688711502253283269683762209292794825489775280500278⟩ ⟨false, 0⟩ ⟨false, 136196213297148299802564174460281235164033037930380898313791610514914485738⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1570_800 : bothSeg evalE (oGrid.idx 1570) (oGrid.dm 1570) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1570) oGrid.kl oGrid.kr 400 800 ⟨false, 136196213297148299802564174460281235164033037930380898313791610514914485738⟩ ⟨false, 0⟩ ⟨false, 221292032502211360763521448843119316959829710995621314806922617380048431000⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1570_1200 : bothSeg evalE (oGrid.idx 1570) (oGrid.dm 1570) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1570) oGrid.kl oGrid.kr 400 1200 ⟨false, 221292032502211360763521448843119316959829710995621314806922617380048431000⟩ ⟨false, 0⟩ ⟨false, 351192811016580040662077587720042619319362682452938652046132171532864770480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1570_1600 : bothSeg evalE (oGrid.idx 1570) (oGrid.dm 1570) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1570) oGrid.kl oGrid.kr 400 1600 ⟨false, 351192811016580040662077587720042619319362682452938652046132171532864770480⟩ ⟨false, 0⟩ ⟨false, 529333336117760457493566835051460653015070607310510053928140966598582398648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1570_2000 : bothSeg evalE (oGrid.idx 1570) (oGrid.dm 1570) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1570) oGrid.kl oGrid.kr 400 2000 ⟨false, 529333336117760457493566835051460653015070607310510053928140966598582398648⟩ ⟨false, 0⟩ ⟨false, 754477443695163363095689822221948036324396678440422756177713520404645097222⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1570_2400 : bothLoop evalE (oGrid.idx 1570) (oGrid.dm 1570) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1570) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 754477443695163363095689822221948036324396678440422756177713520404645097222⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1570 : oGrid.row evalE 1570 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1570_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1570_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1570_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1570_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1570_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1570_2000).1 (bothLoop_sound b_1570_2400).1))))))

theorem n_row_1570 : nGrid.row evalE 1570 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1570_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1570_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1570_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1570_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1570_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1570_2000).2 (bothLoop_sound b_1570_2400).2))))))

theorem b_1571_0 : bothSeg evalE (oGrid.idx 1571) (oGrid.dm 1571) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1571) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75273292232499348903938791233881004762681775278828634398704147846665451266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1571_400 : bothSeg evalE (oGrid.idx 1571) (oGrid.dm 1571) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1571) oGrid.kl oGrid.kr 400 400 ⟨false, 75273292232499348903938791233881004762681775278828634398704147846665451266⟩ ⟨false, 0⟩ ⟨false, 135894792505843311728157460895775071700959478421393557650765234128990135098⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1571_800 : bothSeg evalE (oGrid.idx 1571) (oGrid.dm 1571) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1571) oGrid.kl oGrid.kr 400 800 ⟨false, 135894792505843311728157460895775071700959478421393557650765234128990135098⟩ ⟨false, 0⟩ ⟨false, 221335242830366346452216959956301873157125254720650668632658916703698970660⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1571_1200 : bothSeg evalE (oGrid.idx 1571) (oGrid.dm 1571) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1571) oGrid.kl oGrid.kr 400 1200 ⟨false, 221335242830366346452216959956301873157125254720650668632658916703698970660⟩ ⟨false, 0⟩ ⟨false, 351541175658905118437048716510219064468893693890593175644038679988223221210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1571_1600 : bothSeg evalE (oGrid.idx 1571) (oGrid.dm 1571) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1571) oGrid.kl oGrid.kr 400 1600 ⟨false, 351541175658905118437048716510219064468893693890593175644038679988223221210⟩ ⟨false, 0⟩ ⟨false, 529950650670306936062761656178224827707167423794519145582714290185974433198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1571_2000 : bothSeg evalE (oGrid.idx 1571) (oGrid.dm 1571) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1571) oGrid.kl oGrid.kr 400 2000 ⟨false, 529950650670306936062761656178224827707167423794519145582714290185974433198⟩ ⟨false, 0⟩ ⟨false, 755334355246553008303059391209468517405583869481394921643750982548727970956⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1571_2400 : bothLoop evalE (oGrid.idx 1571) (oGrid.dm 1571) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1571) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 755334355246553008303059391209468517405583869481394921643750982548727970956⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1571 : oGrid.row evalE 1571 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1571_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1571_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1571_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1571_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1571_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1571_2000).1 (bothLoop_sound b_1571_2400).1))))))

theorem n_row_1571 : nGrid.row evalE 1571 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1571_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1571_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1571_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1571_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1571_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1571_2000).2 (bothLoop_sound b_1571_2400).2))))))

theorem b_1572_0 : bothSeg evalE (oGrid.idx 1572) (oGrid.dm 1572) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1572) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75002298391434130984614180354452774320314726911269611017165726624030500608⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1572_400 : bothSeg evalE (oGrid.idx 1572) (oGrid.dm 1572) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1572) oGrid.kl oGrid.kr 400 400 ⟨false, 75002298391434130984614180354452774320314726911269611017165726624030500608⟩ ⟨false, 0⟩ ⟨false, 135591197565921737782897535268322816223031736303416512021890453145830010662⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1572_800 : bothSeg evalE (oGrid.idx 1572) (oGrid.dm 1572) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1572) oGrid.kl oGrid.kr 400 800 ⟨false, 135591197565921737782897535268322816223031736303416512021890453145830010662⟩ ⟨false, 0⟩ ⟨false, 221376248154290303548295346919642602985641778037365260966720048933422132154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1572_1200 : bothSeg evalE (oGrid.idx 1572) (oGrid.dm 1572) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1572) oGrid.kl oGrid.kr 400 1200 ⟨false, 221376248154290303548295346919642602985641778037365260966720048933422132154⟩ ⟨false, 0⟩ ⟨false, 351887313095800797576205519532174982095130922555506661063462877869770398362⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1572_1600 : bothSeg evalE (oGrid.idx 1572) (oGrid.dm 1572) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1572) oGrid.kl oGrid.kr 400 1600 ⟨false, 351887313095800797576205519532174982095130922555506661063462877869770398362⟩ ⟨false, 0⟩ ⟨false, 530565747349021769482966827715166225382169891942745829728965460435398408314⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1572_2000 : bothSeg evalE (oGrid.idx 1572) (oGrid.dm 1572) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1572) oGrid.kl oGrid.kr 400 2000 ⟨false, 530565747349021769482966827715166225382169891942745829728965460435398408314⟩ ⟨false, 0⟩ ⟨false, 756189076367160363415455930709867571580858479216025262424806199939720031188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1572_2400 : bothLoop evalE (oGrid.idx 1572) (oGrid.dm 1572) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1572) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 756189076367160363415455930709867571580858479216025262424806199939720031188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1572 : oGrid.row evalE 1572 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1572_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1572_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1572_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1572_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1572_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1572_2000).1 (bothLoop_sound b_1572_2400).1))))))

theorem n_row_1572 : nGrid.row evalE 1572 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1572_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1572_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1572_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1572_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1572_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1572_2000).2 (bothLoop_sound b_1572_2400).2))))))

theorem b_1573_0 : bothSeg evalE (oGrid.idx 1573) (oGrid.dm 1573) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1573) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 74720623024969313666412972793975542889774615690799848262380216858672198148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1573_400 : bothSeg evalE (oGrid.idx 1573) (oGrid.dm 1573) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1573) oGrid.kl oGrid.kr 400 400 ⟨false, 74720623024969313666412972793975542889774615690799848262380216858672198148⟩ ⟨false, 0⟩ ⟨false, 135285968499126332166408726143662152634924690270113377556048342182967953370⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1573_800 : bothSeg evalE (oGrid.idx 1573) (oGrid.dm 1573) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1573) oGrid.kl oGrid.kr 400 800 ⟨false, 135285968499126332166408726143662152634924690270113377556048342182967953370⟩ ⟨false, 0⟩ ⟨false, 221415572890342142386689216865567031112791916199631241917063792755825992644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1573_1200 : bothSeg evalE (oGrid.idx 1573) (oGrid.dm 1573) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1573) oGrid.kl oGrid.kr 400 1200 ⟨false, 221415572890342142386689216865567031112791916199631241917063792755825992644⟩ ⟨false, 0⟩ ⟨false, 352231747719209686478034611039026851771437772808455315179733839905122162704⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1573_1600 : bothSeg evalE (oGrid.idx 1573) (oGrid.dm 1573) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1573) oGrid.kl oGrid.kr 400 1600 ⟨false, 352231747719209686478034611039026851771437772808455315179733839905122162704⟩ ⟨false, 0⟩ ⟨false, 531179150495226773888110818794838669465667330826351431357941803916637181328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1573_2000 : bothSeg evalE (oGrid.idx 1573) (oGrid.dm 1573) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1573) oGrid.kl oGrid.kr 400 2000 ⟨false, 531179150495226773888110818794838669465667330826351431357941803916637181328⟩ ⟨false, 0⟩ ⟨false, 757042131343591426720823582736201304403042632314210409814763657485689774164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1573_2400 : bothLoop evalE (oGrid.idx 1573) (oGrid.dm 1573) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1573) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 757042131343591426720823582736201304403042632314210409814763657485689774164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1573 : oGrid.row evalE 1573 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1573_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1573_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1573_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1573_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1573_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1573_2000).1 (bothLoop_sound b_1573_2400).1))))))

theorem n_row_1573 : nGrid.row evalE 1573 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1573_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1573_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1573_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1573_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1573_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1573_2000).2 (bothLoop_sound b_1573_2400).2))))))

theorem b_1574_0 : bothSeg evalE (oGrid.idx 1574) (oGrid.dm 1574) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1574) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 74428744434537191425799889286301896222287920037694653897387333460775444870⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1574_400 : bothSeg evalE (oGrid.idx 1574) (oGrid.dm 1574) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1574) oGrid.kl oGrid.kr 400 400 ⟨false, 74428744434537191425799889286301896222287920037694653897387333460775444870⟩ ⟨false, 0⟩ ⟨false, 134979661138939438635532370292177030174318011779406206495880645400111938972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1574_800 : bothSeg evalE (oGrid.idx 1574) (oGrid.dm 1574) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1574) oGrid.kl oGrid.kr 400 800 ⟨false, 134979661138939438635532370292177030174318011779406206495880645400111938972⟩ ⟨false, 0⟩ ⟨false, 221453763575843170691621492503112858003438229442683007727926314788552674162⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1574_1200 : bothSeg evalE (oGrid.idx 1574) (oGrid.dm 1574) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1574) oGrid.kl oGrid.kr 400 1200 ⟨false, 221453763575843170691621492503112858003438229442683007727926314788552674162⟩ ⟨false, 0⟩ ⟨false, 352575026042123624129929116538795384136248439666225050402745230255677853478⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1574_1600 : bothSeg evalE (oGrid.idx 1574) (oGrid.dm 1574) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1574) oGrid.kl oGrid.kr 400 1600 ⟨false, 352575026042123624129929116538795384136248439666225050402745230255677853478⟩ ⟨false, 0⟩ ⟨false, 531791406571389096058874061512668515289624871549469795649745914774511419000⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1574_2000 : bothSeg evalE (oGrid.idx 1574) (oGrid.dm 1574) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1574) oGrid.kl oGrid.kr 400 2000 ⟨false, 531791406571389096058874061512668515289624871549469795649745914774511419000⟩ ⟨false, 0⟩ ⟨false, 757894066583671114514464937662898126699420194620263632866044130669001243412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1574_2400 : bothLoop evalE (oGrid.idx 1574) (oGrid.dm 1574) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1574) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 757894066583671114514464937662898126699420194620263632866044130669001243412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1574 : oGrid.row evalE 1574 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1574_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1574_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1574_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1574_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1574_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1574_2000).1 (bothLoop_sound b_1574_2400).1))))))

theorem n_row_1574 : nGrid.row evalE 1574 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1574_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1574_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1574_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1574_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1574_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1574_2000).2 (bothLoop_sound b_1574_2400).2))))))

theorem b_1575_0 : bothSeg evalE (oGrid.idx 1575) (oGrid.dm 1575) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1575) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 74127165426200854568531010403187323614227847120834661872801872844506334572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1575_400 : bothSeg evalE (oGrid.idx 1575) (oGrid.dm 1575) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1575) oGrid.kl oGrid.kr 400 400 ⟨false, 74127165426200854568531010403187323614227847120834661872801872844506334572⟩ ⟨false, 0⟩ ⟨false, 134672838322857418657879101820767750857705514724565426439871423430739109422⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1575_800 : bothSeg evalE (oGrid.idx 1575) (oGrid.dm 1575) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1575) oGrid.kl oGrid.kr 400 800 ⟨false, 134672838322857418657879101820767750857705514724565426439871423430739109422⟩ ⟨false, 0⟩ ⟨false, 221491376047629423314243590530034154654725658422621138002230912175374014758⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1575_1200 : bothSeg evalE (oGrid.idx 1575) (oGrid.dm 1575) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1575) oGrid.kl oGrid.kr 400 1200 ⟨false, 221491376047629423314243590530034154654725658422621138002230912175374014758⟩ ⟨false, 0⟩ ⟨false, 352917703877135805379083255845424331355618326726038861204185102313259509978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1575_1600 : bothSeg evalE (oGrid.idx 1575) (oGrid.dm 1575) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1575) oGrid.kl oGrid.kr 400 1600 ⟨false, 352917703877135805379083255845424331355618326726038861204185102313259509978⟩ ⟨false, 0⟩ ⟨false, 532403071339673182707554104344013428646381317151047303780525569190355210680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1575_2000 : bothSeg evalE (oGrid.idx 1575) (oGrid.dm 1575) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1575) oGrid.kl oGrid.kr 400 2000 ⟨false, 532403071339673182707554104344013428646381317151047303780525569190355210680⟩ ⟨false, 0⟩ ⟨false, 758745437794995152515074290539807104353014929682538045218434764520393481214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1575_2400 : bothLoop evalE (oGrid.idx 1575) (oGrid.dm 1575) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1575) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 758745437794995152515074290539807104353014929682538045218434764520393481214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1575 : oGrid.row evalE 1575 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1575_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1575_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1575_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1575_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1575_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1575_2000).1 (bothLoop_sound b_1575_2400).1))))))

theorem n_row_1575 : nGrid.row evalE 1575 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1575_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1575_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1575_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1575_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1575_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1575_2000).2 (bothLoop_sound b_1575_2400).2))))))

theorem b_1576_0 : bothSeg evalE (oGrid.idx 1576) (oGrid.dm 1576) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1576) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73816390164822964509642327010191657755356821497989477977881151539503429672⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1576_400 : bothSeg evalE (oGrid.idx 1576) (oGrid.dm 1576) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1576) oGrid.kl oGrid.kr 400 400 ⟨false, 73816390164822964509642327010191657755356821497989477977881151539503429672⟩ ⟨false, 0⟩ ⟨false, 134366050429777979274968616694050228000853074679241068523347555729473050124⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1576_800 : bothSeg evalE (oGrid.idx 1576) (oGrid.dm 1576) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1576) oGrid.kl oGrid.kr 400 800 ⟨false, 134366050429777979274968616694050228000853074679241068523347555729473050124⟩ ⟨false, 0⟩ ⟨false, 221528958365497462044797244971520463286470862437955181862296889621432005386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1576_1200 : bothSeg evalE (oGrid.idx 1576) (oGrid.dm 1576) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1576) oGrid.kl oGrid.kr 400 1200 ⟨false, 221528958365497462044797244971520463286470862437955181862296889621432005386⟩ ⟨false, 0⟩ ⟨false, 353260329259886376723231889848271871009546961281607119722058707527517668038⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1576_1600 : bothSeg evalE (oGrid.idx 1576) (oGrid.dm 1576) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1576) oGrid.kl oGrid.kr 400 1600 ⟨false, 353260329259886376723231889848271871009546961281607119722058707527517668038⟩ ⟨false, 0⟩ ⟨false, 533014692785386220499059524331731205692615705647037861875021767308987571154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1576_2000 : bothSeg evalE (oGrid.idx 1576) (oGrid.dm 1576) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1576) oGrid.kl oGrid.kr 400 2000 ⟨false, 533014692785386220499059524331731205692615705647037861875021767308987571154⟩ ⟨false, 0⟩ ⟨false, 759596792908375438046522557499026910455070321621097507756236872331342612558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1576_2400 : bothLoop evalE (oGrid.idx 1576) (oGrid.dm 1576) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1576) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 759596792908375438046522557499026910455070321621097507756236872331342612558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1576 : oGrid.row evalE 1576 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1576_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1576_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1576_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1576_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1576_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1576_2000).1 (bothLoop_sound b_1576_2400).1))))))

theorem n_row_1576 : nGrid.row evalE 1576 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1576_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1576_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1576_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1576_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1576_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1576_2000).2 (bothLoop_sound b_1576_2400).2))))))

theorem b_1577_0 : bothSeg evalE (oGrid.idx 1577) (oGrid.dm 1577) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1577) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73496953704726510496854112791234465052371422128701307415253931344684976450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1577_400 : bothSeg evalE (oGrid.idx 1577) (oGrid.dm 1577) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1577) oGrid.kl oGrid.kr 400 400 ⟨false, 73496953704726510496854112791234465052371422128701307415253931344684976450⟩ ⟨false, 0⟩ ⟨false, 134059869260027228721229599524525480068484435048235622140892416347233796378⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1577_800 : bothSeg evalE (oGrid.idx 1577) (oGrid.dm 1577) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1577) oGrid.kl oGrid.kr 400 800 ⟨false, 134059869260027228721229599524525480068484435048235622140892416347233796378⟩ ⟨false, 0⟩ ⟨false, 221567082090827163237865603435330041033968275165228856491841573833747257994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1577_1200 : bothSeg evalE (oGrid.idx 1577) (oGrid.dm 1577) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1577) oGrid.kl oGrid.kr 400 1200 ⟨false, 221567082090827163237865603435330041033968275165228856491841573833747257994⟩ ⟨false, 0⟩ ⟨false, 353603473727685020358880720127841156032554172947204725911701884794869880418⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1577_1600 : bothSeg evalE (oGrid.idx 1577) (oGrid.dm 1577) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1577) oGrid.kl oGrid.kr 400 1600 ⟨false, 353603473727685020358880720127841156032554172947204725911701884794869880418⟩ ⟨false, 0⟩ ⟨false, 533626842395600564545509450993838000065421258348394212375043704485699220472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1577_2000 : bothSeg evalE (oGrid.idx 1577) (oGrid.dm 1577) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1577) oGrid.kl oGrid.kr 400 2000 ⟨false, 533626842395600564545509450993838000065421258348394212375043704485699220472⟩ ⟨false, 0⟩ ⟨false, 760448703356462390723051748664497632018545613748453415732835518517830603158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1577_2400 : bothLoop evalE (oGrid.idx 1577) (oGrid.dm 1577) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1577) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 760448703356462390723051748664497632018545613748453415732835518517830603158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1577 : oGrid.row evalE 1577 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1577_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1577_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1577_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1577_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1577_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1577_2000).1 (bothLoop_sound b_1577_2400).1))))))

theorem n_row_1577 : nGrid.row evalE 1577 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1577_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1577_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1577_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1577_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1577_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1577_2000).2 (bothLoop_sound b_1577_2400).2))))))

theorem b_1578_0 : bothSeg evalE (oGrid.idx 1578) (oGrid.dm 1578) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1578) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73169396241414747193929367993766778757462497116647650112153599747544224706⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1578_400 : bothSeg evalE (oGrid.idx 1578) (oGrid.dm 1578) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1578) oGrid.kl oGrid.kr 400 400 ⟨false, 73169396241414747193929367993766778757462497116647650112153599747544224706⟩ ⟨false, 0⟩ ⟨false, 133754858106127596410271114722312069204317862974641452324863365316253407446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1578_800 : bothSeg evalE (oGrid.idx 1578) (oGrid.dm 1578) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1578) oGrid.kl oGrid.kr 400 800 ⟨false, 133754858106127596410271114722312069204317862974641452324863365316253407446⟩ ⟨false, 0⟩ ⟨false, 221606310545810562700196370404710935721588027923539182554389139842134684460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1578_1200 : bothSeg evalE (oGrid.idx 1578) (oGrid.dm 1578) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1578) oGrid.kl oGrid.kr 400 1200 ⟨false, 221606310545810562700196370404710935721588027923539182554389139842134684460⟩ ⟨false, 0⟩ ⟨false, 353947700578739595935591649456802723913721030976846986356229440068378404374⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1578_1600 : bothSeg evalE (oGrid.idx 1578) (oGrid.dm 1578) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1578) oGrid.kl oGrid.kr 400 1600 ⟨false, 353947700578739595935591649456802723913721030976846986356229440068378404374⟩ ⟨false, 0⟩ ⟨false, 534240083418382224822833922912243006126566965038424182738578036020526408812⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1578_2000 : bothSeg evalE (oGrid.idx 1578) (oGrid.dm 1578) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1578) oGrid.kl oGrid.kr 400 2000 ⟨false, 534240083418382224822833922912243006126566965038424182738578036020526408812⟩ ⟨false, 0⟩ ⟨false, 761301732332973361086454447954482580430728861255654879487002126622236593702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1578_2400 : bothLoop evalE (oGrid.idx 1578) (oGrid.dm 1578) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1578) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 761301732332973361086454447954482580430728861255654879487002126622236593702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1578 : oGrid.row evalE 1578 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1578_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1578_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1578_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1578_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1578_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1578_2000).1 (bothLoop_sound b_1578_2400).1))))))

theorem n_row_1578 : nGrid.row evalE 1578 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1578_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1578_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1578_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1578_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1578_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1578_2000).2 (bothLoop_sound b_1578_2400).2))))))

theorem b_1579_0 : bothSeg evalE (oGrid.idx 1579) (oGrid.dm 1579) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1579) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72834275910724954077231547549561588403667690175759500212004819352475070690⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1579_400 : bothSeg evalE (oGrid.idx 1579) (oGrid.dm 1579) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1579) oGrid.kl oGrid.kr 400 400 ⟨false, 72834275910724954077231547549561588403667690175759500212004819352475070690⟩ ⟨false, 0⟩ ⟨false, 133451594640607317965667946974011273110044714592397672803726236722773911822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1579_800 : bothSeg evalE (oGrid.idx 1579) (oGrid.dm 1579) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1579) oGrid.kl oGrid.kr 400 800 ⟨false, 133451594640607317965667946974011273110044714592397672803726236722773911822⟩ ⟨false, 0⟩ ⟨false, 221647221432661406807206380805636639596428670214491874151799890062048161464⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1579_1200 : bothSeg evalE (oGrid.idx 1579) (oGrid.dm 1579) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1579) oGrid.kl oGrid.kr 400 1200 ⟨false, 221647221432661406807206380805636639596428670214491874151799890062048161464⟩ ⟨false, 0⟩ ⟨false, 354293587491365488981516091324488984106107647958871657018252619984505240238⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1579_1600 : bothSeg evalE (oGrid.idx 1579) (oGrid.dm 1579) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1579) oGrid.kl oGrid.kr 400 1600 ⟨false, 354293587491365488981516091324488984106107647958871657018252619984505240238⟩ ⟨false, 0⟩ ⟨false, 534854993482000059474398130472492920499978963506492299419286450775956065910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1579_2000 : bothSeg evalE (oGrid.idx 1579) (oGrid.dm 1579) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1579) oGrid.kl oGrid.kr 400 2000 ⟨false, 534854993482000059474398130472492920499978963506492299419286450775956065910⟩ ⟨false, 0⟩ ⟨false, 762156457411901746160440770949116447677266852936826366584980794586291549508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1579_2400 : bothLoop evalE (oGrid.idx 1579) (oGrid.dm 1579) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1579) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 762156457411901746160440770949116447677266852936826366584980794586291549508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1579 : oGrid.row evalE 1579 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1579_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1579_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1579_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1579_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1579_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1579_2000).1 (bothLoop_sound b_1579_2400).1))))))

theorem n_row_1579 : nGrid.row evalE 1579 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1579_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1579_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1579_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1579_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1579_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1579_2000).2 (bothLoop_sound b_1579_2400).2))))))

theorem b_1580_0 : bothSeg evalE (oGrid.idx 1580) (oGrid.dm 1580) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1580) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72492170862756421531403606320469987772341388633613218480721512547869618380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1580_400 : bothSeg evalE (oGrid.idx 1580) (oGrid.dm 1580) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1580) oGrid.kl oGrid.kr 400 400 ⟨false, 72492170862756421531403606320469987772341388633613218480721512547869618380⟩ ⟨false, 0⟩ ⟨false, 133150653620936015066608783697009995401211885134409098879758299862998262046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1580_800 : bothSeg evalE (oGrid.idx 1580) (oGrid.dm 1580) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1580) oGrid.kl oGrid.kr 400 800 ⟨false, 133150653620936015066608783697009995401211885134409098879758299862998262046⟩ ⟨false, 0⟩ ⟨false, 221690389538550610133153420332046152931571383173435390776727401808516821822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1580_1200 : bothSeg evalE (oGrid.idx 1580) (oGrid.dm 1580) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1580) oGrid.kl oGrid.kr 400 1200 ⟨false, 221690389538550610133153420332046152931571383173435390776727401808516821822⟩ ⟨false, 0⟩ ⟨false, 354641709228920866284247119052934477806869451654385840683604961603621730344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1580_1600 : bothSeg evalE (oGrid.idx 1580) (oGrid.dm 1580) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1580) oGrid.kl oGrid.kr 400 1600 ⟨false, 354641709228920866284247119052934477806869451654385840683604961603621730344⟩ ⟨false, 0⟩ ⟨false, 535472147299860875285551256360279305023280176962664705584696567777000438374⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1580_2000 : bothSeg evalE (oGrid.idx 1580) (oGrid.dm 1580) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1580) oGrid.kl oGrid.kr 400 2000 ⟨false, 535472147299860875285551256360279305023280176962664705584696567777000438374⟩ ⟨false, 0⟩ ⟨false, 763013453252452012206272120703957752340425828421638784522725446721881575600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1580_2400 : bothLoop evalE (oGrid.idx 1580) (oGrid.dm 1580) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1580) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 763013453252452012206272120703957752340425828421638784522725446721881575600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1580 : oGrid.row evalE 1580 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1580_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1580_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1580_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1580_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1580_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1580_2000).1 (bothLoop_sound b_1580_2400).1))))))

theorem n_row_1580 : nGrid.row evalE 1580 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1580_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1580_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1580_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1580_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1580_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1580_2000).2 (bothLoop_sound b_1580_2400).2))))))

theorem b_1581_0 : bothSeg evalE (oGrid.idx 1581) (oGrid.dm 1581) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1581) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72143652091876828904848289847548191314555353190400233466920937165131260796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1581_400 : bothSeg evalE (oGrid.idx 1581) (oGrid.dm 1581) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1581) oGrid.kl oGrid.kr 400 400 ⟨false, 72143652091876828904848289847548191314555353190400233466920937165131260796⟩ ⟨false, 0⟩ ⟨false, 132852602991423588695957139831268969500102262852399508310219373072403935000⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1581_800 : bothSeg evalE (oGrid.idx 1581) (oGrid.dm 1581) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1581) oGrid.kl oGrid.kr 400 800 ⟨false, 132852602991423588695957139831268969500102262852399508310219373072403935000⟩ ⟨false, 0⟩ ⟨false, 221736382837505026904342948203243873827252201633571333312304946511931756766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1581_1200 : bothSeg evalE (oGrid.idx 1581) (oGrid.dm 1581) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1581) oGrid.kl oGrid.kr 400 1200 ⟨false, 221736382837505026904342948203243873827252201633571333312304946511931756766⟩ ⟨false, 0⟩ ⟨false, 354992633741705245535444851639037509775475753443907920676293704562533287176⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1581_1600 : bothSeg evalE (oGrid.idx 1581) (oGrid.dm 1581) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1581) oGrid.kl oGrid.kr 400 1600 ⟨false, 354992633741705245535444851639037509775475753443907920676293704562533287176⟩ ⟨false, 0⟩ ⟨false, 536092112772407842637383690975452316951349338675648755458601110038042572580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1581_2000 : bothSeg evalE (oGrid.idx 1581) (oGrid.dm 1581) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1581) oGrid.kl oGrid.kr 400 2000 ⟨false, 536092112772407842637383690975452316951349338675648755458601110038042572580⟩ ⟨false, 0⟩ ⟨false, 763873287700938031988123319813729494288504628805097010225566183073674231576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1581_2400 : bothLoop evalE (oGrid.idx 1581) (oGrid.dm 1581) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1581) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 763873287700938031988123319813729494288504628805097010225566183073674231576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1581 : oGrid.row evalE 1581 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1581_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1581_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1581_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1581_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1581_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1581_2000).1 (bothLoop_sound b_1581_2400).1))))))

theorem n_row_1581 : nGrid.row evalE 1581 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1581_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1581_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1581_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1581_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1581_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1581_2000).2 (bothLoop_sound b_1581_2400).2))))))

theorem b_1582_0 : bothSeg evalE (oGrid.idx 1582) (oGrid.dm 1582) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1582) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 71789329157957254926962626481306797806869509953044273327416610024237873566⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1582_400 : bothSeg evalE (oGrid.idx 1582) (oGrid.dm 1582) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1582) oGrid.kl oGrid.kr 400 400 ⟨false, 71789329157957254926962626481306797806869509953044273327416610024237873566⟩ ⟨false, 0⟩ ⟨false, 132558036261323616974945971384068173764374737969516037342512812010955157050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1582_800 : bothSeg evalE (oGrid.idx 1582) (oGrid.dm 1582) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1582) oGrid.kl oGrid.kr 400 800 ⟨false, 132558036261323616974945971384068173764374737969516037342512812010955157050⟩ ⟨false, 0⟩ ⟨false, 221785794868510727458282808773005810910761891398942144933876092682640679026⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1582_1200 : bothSeg evalE (oGrid.idx 1582) (oGrid.dm 1582) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1582) oGrid.kl oGrid.kr 400 1200 ⟨false, 221785794868510727458282808773005810910761891398942144933876092682640679026⟩ ⟨false, 0⟩ ⟨false, 355346954545062570421236569766758666218437811983661410426886952234570408120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1582_1600 : bothSeg evalE (oGrid.idx 1582) (oGrid.dm 1582) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1582) oGrid.kl oGrid.kr 400 1600 ⟨false, 355346954545062570421236569766758666218437811983661410426886952234570408120⟩ ⟨false, 0⟩ ⟨false, 536715483365223416121523058491173261604779251916080975850753362099401044086⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1582_2000 : bothSeg evalE (oGrid.idx 1582) (oGrid.dm 1582) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1582) oGrid.kl oGrid.kr 400 2000 ⟨false, 536715483365223416121523058491173261604779251916080975850753362099401044086⟩ ⟨false, 0⟩ ⟨false, 764736554168885927730180550756367132922423804302093252444271227526914736402⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1582_2400 : bothLoop evalE (oGrid.idx 1582) (oGrid.dm 1582) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1582) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 764736554168885927730180550756367132922423804302093252444271227526914736402⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1582 : oGrid.row evalE 1582 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1582_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1582_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1582_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1582_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1582_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1582_2000).1 (bothLoop_sound b_1582_2400).1))))))

theorem n_row_1582 : nGrid.row evalE 1582 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1582_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1582_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1582_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1582_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1582_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1582_2000).2 (bothLoop_sound b_1582_2400).2))))))

theorem b_1583_0 : bothSeg evalE (oGrid.idx 1583) (oGrid.dm 1583) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1583) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 71429798941523671118058127190595643277043209128828690567412459630521933398⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1583_400 : bothSeg evalE (oGrid.idx 1583) (oGrid.dm 1583) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1583) oGrid.kl oGrid.kr 400 400 ⟨false, 71429798941523671118058127190595643277043209128828690567412459630521933398⟩ ⟨false, 0⟩ ⟨false, 132267525560332514802806969238266883173771609753760670781891068324738281718⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1583_800 : bothSeg evalE (oGrid.idx 1583) (oGrid.dm 1583) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1583) oGrid.kl oGrid.kr 400 800 ⟨false, 132267525560332514802806969238266883173771609753760670781891068324738281718⟩ ⟨false, 0⟩ ⟨false, 221839197791012036925783084647906438075301515752425181864190188800087635486⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1583_1200 : bothSeg evalE (oGrid.idx 1583) (oGrid.dm 1583) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1583) oGrid.kl oGrid.kr 400 1200 ⟨false, 221839197791012036925783084647906438075301515752425181864190188800087635486⟩ ⟨false, 0⟩ ⟨false, 355705243774880048374478785417763746138553441917025634176612130070888890056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1583_1600 : bothSeg evalE (oGrid.idx 1583) (oGrid.dm 1583) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1583) oGrid.kl oGrid.kr 400 1600 ⟨false, 355705243774880048374478785417763746138553441917025634176612130070888890056⟩ ⟨false, 0⟩ ⟨false, 537342831164528018031884784783482580002271340150381157887600878992589085338⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1583_2000 : bothSeg evalE (oGrid.idx 1583) (oGrid.dm 1583) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1583) oGrid.kl oGrid.kr 400 2000 ⟨false, 537342831164528018031884784783482580002271340150381157887600878992589085338⟩ ⟨false, 0⟩ ⟨false, 765603824688532676981567029490452541630751961585937452548542991860719051772⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1583_2400 : bothLoop evalE (oGrid.idx 1583) (oGrid.dm 1583) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1583) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 765603824688532676981567029490452541630751961585937452548542991860719051772⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1583 : oGrid.row evalE 1583 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1583_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1583_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1583_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1583_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1583_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1583_2000).1 (bothLoop_sound b_1583_2400).1))))))

theorem n_row_1583 : nGrid.row evalE 1583 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1583_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1583_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1583_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1583_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1583_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1583_2000).2 (bothLoop_sound b_1583_2400).2))))))

theorem o_blk_1560 : allFrom (fun j => oGrid.row evalE j) 1560 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1560) o_row_1560 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1561) o_row_1561 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1562) o_row_1562 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1563) o_row_1563 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1564) o_row_1564 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1565) o_row_1565 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1566) o_row_1566 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1567) o_row_1567 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1568) o_row_1568 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1569) o_row_1569 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1570) o_row_1570 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1571) o_row_1571 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1572) o_row_1572 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1573) o_row_1573 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1574) o_row_1574 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1575) o_row_1575 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1576) o_row_1576 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1577) o_row_1577 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1578) o_row_1578 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1579) o_row_1579 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1580) o_row_1580 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1581) o_row_1581 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1582) o_row_1582 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1583) o_row_1583 (allFrom_zero (fun j => oGrid.row evalE j) 1584)))))))))))))))))))))))))

theorem n_blk_1560 : allFrom (fun j => nGrid.row evalE j) 1560 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1560) n_row_1560 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1561) n_row_1561 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1562) n_row_1562 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1563) n_row_1563 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1564) n_row_1564 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1565) n_row_1565 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1566) n_row_1566 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1567) n_row_1567 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1568) n_row_1568 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1569) n_row_1569 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1570) n_row_1570 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1571) n_row_1571 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1572) n_row_1572 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1573) n_row_1573 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1574) n_row_1574 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1575) n_row_1575 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1576) n_row_1576 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1577) n_row_1577 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1578) n_row_1578 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1579) n_row_1579 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1580) n_row_1580 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1581) n_row_1581 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1582) n_row_1582 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1583) n_row_1583 (allFrom_zero (fun j => nGrid.row evalE j) 1584)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
