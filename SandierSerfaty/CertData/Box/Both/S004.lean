/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 4 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `96`–`119`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_96_0 : bothSeg evalE (oGrid.idx 96) (oGrid.dm 96) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 96) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3675079270275636792641321870479287099994993858552391224576767073496038170470⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_96_400 : bothSeg evalE (oGrid.idx 96) (oGrid.dm 96) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 96) oGrid.kl oGrid.kr 400 400 ⟨false, 3675079270275636792641321870479287099994993858552391224576767073496038170470⟩ ⟨false, 0⟩ ⟨false, 5931203528458140884692653934192592672999106646230377313285597217315109271802⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_96_800 : bothSeg evalE (oGrid.idx 96) (oGrid.dm 96) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 96) oGrid.kl oGrid.kr 400 800 ⟨false, 5931203528458140884692653934192592672999106646230377313285597217315109271802⟩ ⟨false, 0⟩ ⟨false, 6778197815513688598433752727110211192312998037414119370296816389107058697644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_96_1200 : bothSeg evalE (oGrid.idx 96) (oGrid.dm 96) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 96) oGrid.kl oGrid.kr 400 1200 ⟨false, 6778197815513688598433752727110211192312998037414119370296816389107058697644⟩ ⟨false, 0⟩ ⟨false, 6925186798576233765446718649371572503711400179751583959033918928251291991744⟩ ⟨false, 79958219954343744221014931135792283689039808433893165119777023990251522⟩ = true := by
  decide +kernel

theorem b_96_1600 : bothSeg evalE (oGrid.idx 96) (oGrid.dm 96) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 96) oGrid.kl oGrid.kr 400 1600 ⟨false, 6925186798576233765446718649371572503711400179751583959033918928251291991744⟩ ⟨false, 79958219954343744221014931135792283689039808433893165119777023990251522⟩ ⟨false, 6744481027767884367214359768798945742418916987598988327352070258405842268936⟩ ⟨false, 181038666364203946362781998549836199601100737324658174468671141196736025574⟩ = true := by
  decide +kernel

theorem b_96_2000 : bothSeg evalE (oGrid.idx 96) (oGrid.dm 96) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 96) oGrid.kl oGrid.kr 400 2000 ⟨false, 6744481027767884367214359768798945742418916987598988327352070258405842268936⟩ ⟨false, 181038666364203946362781998549836199601100737324658174468671141196736025574⟩ ⟨false, 6682810122249970172373824002297341521039579196168440671664307327520396897486⟩ ⟨false, 243404634132045680032501287203173718644387070374901612155837331134232862570⟩ = true := by
  decide +kernel

theorem b_96_2400 : bothLoop evalE (oGrid.idx 96) (oGrid.dm 96) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 96) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6682810122249970172373824002297341521039579196168440671664307327520396897486⟩ ⟨false, 243404634132045680032501287203173718644387070374901612155837331134232862570⟩ = true := by
  decide +kernel

theorem o_row_96 : oGrid.row evalE 96 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_96_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_96_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_96_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_96_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_96_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_96_2000).1 (bothLoop_sound b_96_2400).1))))))

theorem n_row_96 : nGrid.row evalE 96 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_96_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_96_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_96_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_96_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_96_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_96_2000).2 (bothLoop_sound b_96_2400).2))))))

theorem b_97_0 : bothSeg evalE (oGrid.idx 97) (oGrid.dm 97) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 97) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3661657474609464641178783006073734520373378576751961275624640896167150746458⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_97_400 : bothSeg evalE (oGrid.idx 97) (oGrid.dm 97) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 97) oGrid.kl oGrid.kr 400 400 ⟨false, 3661657474609464641178783006073734520373378576751961275624640896167150746458⟩ ⟨false, 0⟩ ⟨false, 5909777334374115377302535412339411598760195949157931702755722902792444243296⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_97_800 : bothSeg evalE (oGrid.idx 97) (oGrid.dm 97) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 97) oGrid.kl oGrid.kr 400 800 ⟨false, 5909777334374115377302535412339411598760195949157931702755722902792444243296⟩ ⟨false, 0⟩ ⟨false, 6753625149388024341330750316353394277901166285340415747891801907052207926454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_97_1200 : bothSeg evalE (oGrid.idx 97) (oGrid.dm 97) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 97) oGrid.kl oGrid.kr 400 1200 ⟨false, 6753625149388024341330750316353394277901166285340415747891801907052207926454⟩ ⟨false, 0⟩ ⟨false, 6899739431720768328828875541113202867834748085723093447356655855939537081296⟩ ⟨false, 101959106463270538168943856422870528729150576274105198696457106605831276⟩ = true := by
  decide +kernel

theorem b_97_1600 : bothSeg evalE (oGrid.idx 97) (oGrid.dm 97) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 97) oGrid.kl oGrid.kr 400 1600 ⟨false, 6899739431720768328828875541113202867834748085723093447356655855939537081296⟩ ⟨false, 101959106463270538168943856422870528729150576274105198696457106605831276⟩ ⟨false, 6718892459705190052616000867664845665576796018844398185648265279301647233418⟩ ⟨false, 181202678778398353354798661880496796125113174750649399343854064840916421328⟩ = true := by
  decide +kernel

theorem b_97_2000 : bothSeg evalE (oGrid.idx 97) (oGrid.dm 97) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 97) oGrid.kl oGrid.kr 400 2000 ⟨false, 6718892459705190052616000867664845665576796018844398185648265279301647233418⟩ ⟨false, 181202678778398353354798661880496796125113174750649399343854064840916421328⟩ ⟨false, 6657589758580085170464480347475848468309127484435104755772125594802173095224⟩ ⟨false, 243202037879252176668019018402987990005870005803278112519696468814363132830⟩ = true := by
  decide +kernel

theorem b_97_2400 : bothLoop evalE (oGrid.idx 97) (oGrid.dm 97) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 97) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6657589758580085170464480347475848468309127484435104755772125594802173095224⟩ ⟨false, 243202037879252176668019018402987990005870005803278112519696468814363132830⟩ = true := by
  decide +kernel

theorem o_row_97 : oGrid.row evalE 97 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_97_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_97_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_97_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_97_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_97_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_97_2000).1 (bothLoop_sound b_97_2400).1))))))

theorem n_row_97 : nGrid.row evalE 97 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_97_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_97_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_97_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_97_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_97_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_97_2000).2 (bothLoop_sound b_97_2400).2))))))

theorem b_98_0 : bothSeg evalE (oGrid.idx 98) (oGrid.dm 98) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 98) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3648275458417715931952781965827226061304351397732665133101689506674967934226⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_98_400 : bothSeg evalE (oGrid.idx 98) (oGrid.dm 98) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 98) oGrid.kl oGrid.kr 400 400 ⟨false, 3648275458417715931952781965827226061304351397732665133101689506674967934226⟩ ⟨false, 0⟩ ⟨false, 5888411090731987946348370277948538795301805109865172653180704519215338632868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_98_800 : bothSeg evalE (oGrid.idx 98) (oGrid.dm 98) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 98) oGrid.kl oGrid.kr 400 800 ⟨false, 5888411090731987946348370277948538795301805109865172653180704519215338632868⟩ ⟨false, 0⟩ ⟨false, 6729118818277862719145495682695052830623644385517852785742452741727392546326⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_98_1200 : bothSeg evalE (oGrid.idx 98) (oGrid.dm 98) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 98) oGrid.kl oGrid.kr 400 1200 ⟨false, 6729118818277862719145495682695052830623644385517852785742452741727392546326⟩ ⟨false, 0⟩ ⟨false, 6874357844945769209684212485575552790814452060116364875005984900019783634150⟩ ⟨false, 126909638733984094040380254367470086741790026353303480255530681534753382⟩ = true := by
  decide +kernel

theorem b_98_1600 : bothSeg evalE (oGrid.idx 98) (oGrid.dm 98) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 98) oGrid.kl oGrid.kr 400 1600 ⟨false, 6874357844945769209684212485575552790814452060116364875005984900019783634150⟩ ⟨false, 126909638733984094040380254367470086741790026353303480255530681534753382⟩ ⟨false, 6693374254969854083170226845871174071954390214152926845309705974255079709414⟩ ⟨false, 181364879435415436403014474998477764485684453661680961115483310097816274482⟩ = true := by
  decide +kernel

theorem b_98_2000 : bothSeg evalE (oGrid.idx 98) (oGrid.dm 98) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 98) oGrid.kl oGrid.kr 400 2000 ⟨false, 6693374254969854083170226845871174071954390214152926845309705974255079709414⟩ ⟨false, 181364879435415436403014474998477764485684453661680961115483310097816274482⟩ ⟨false, 6632437461369037555796777401109748886361919047821663437226945247241467776554⟩ ⟨false, 242999696451988688506828367311572544702413713258054058758666590285707605386⟩ = true := by
  decide +kernel

theorem b_98_2400 : bothLoop evalE (oGrid.idx 98) (oGrid.dm 98) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 98) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6632437461369037555796777401109748886361919047821663437226945247241467776554⟩ ⟨false, 242999696451988688506828367311572544702413713258054058758666590285707605386⟩ = true := by
  decide +kernel

theorem o_row_98 : oGrid.row evalE 98 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_98_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_98_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_98_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_98_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_98_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_98_2000).1 (bothLoop_sound b_98_2400).1))))))

theorem n_row_98 : nGrid.row evalE 98 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_98_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_98_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_98_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_98_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_98_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_98_2000).2 (bothLoop_sound b_98_2400).2))))))

theorem b_99_0 : bothSeg evalE (oGrid.idx 99) (oGrid.dm 99) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 99) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3634933129476895360274082780765830288770885240041591611171229228305450635682⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_99_400 : bothSeg evalE (oGrid.idx 99) (oGrid.dm 99) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 99) oGrid.kl oGrid.kr 400 400 ⟨false, 3634933129476895360274082780765830288770885240041591611171229228305450635682⟩ ⟨false, 0⟩ ⟨false, 5867104629347428646545168951038231526272133560496777169428141139610631135388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_99_800 : bothSeg evalE (oGrid.idx 99) (oGrid.dm 99) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 99) oGrid.kl oGrid.kr 400 800 ⟨false, 5867104629347428646545168951038231526272133560496777169428141139610631135388⟩ ⟨false, 0⟩ ⟨false, 6704678670386705156386841054610637313189462071938084778064089564019407496076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_99_1200 : bothSeg evalE (oGrid.idx 99) (oGrid.dm 99) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 99) oGrid.kl oGrid.kr 400 1200 ⟨false, 6704678670386705156386841054610637313189462071938084778064089564019407496076⟩ ⟨false, 0⟩ ⟨false, 6849041719424962849100770581149603648011097153838801475808368724275806072774⟩ ⟨false, 155002025101997778094613173941814285980090342392207779811024339717621856⟩ = true := by
  decide +kernel

theorem b_99_1600 : bothSeg evalE (oGrid.idx 99) (oGrid.dm 99) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 99) oGrid.kl oGrid.kr 400 1600 ⟨false, 6849041719424962849100770581149603648011097153838801475808368724275806072774⟩ ⟨false, 155002025101997778094613173941814285980090342392207779811024339717621856⟩ ⟨false, 6667926027277403347394373001423109696241204209307704679869293635080854393080⟩ ⟨false, 181525682740807545635130702020547684375524879321928187870482444248172000964⟩ = true := by
  decide +kernel

theorem b_99_2000 : bothSeg evalE (oGrid.idx 99) (oGrid.dm 99) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 99) oGrid.kl oGrid.kr 400 2000 ⟨false, 6667926027277403347394373001423109696241204209307704679869293635080854393080⟩ ⟨false, 181525682740807545635130702020547684375524879321928187870482444248172000964⟩ ⟨false, 6607352860988642703555999261730571741588651562878869089455393815695525119454⟩ ⟨false, 242798499037644507537938952379667150647434252822011275643311757899468233628⟩ = true := by
  decide +kernel

theorem b_99_2400 : bothLoop evalE (oGrid.idx 99) (oGrid.dm 99) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 99) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6607352860988642703555999261730571741588651562878869089455393815695525119454⟩ ⟨false, 242798499037644507537938952379667150647434252822011275643311757899468233628⟩ = true := by
  decide +kernel

theorem o_row_99 : oGrid.row evalE 99 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_99_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_99_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_99_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_99_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_99_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_99_2000).1 (bothLoop_sound b_99_2400).1))))))

theorem n_row_99 : nGrid.row evalE 99 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_99_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_99_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_99_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_99_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_99_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_99_2000).2 (bothLoop_sound b_99_2400).2))))))

theorem b_100_0 : bothSeg evalE (oGrid.idx 100) (oGrid.dm 100) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 100) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3621630428098647450513590830338908457002396195229446692635795412349227999580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_100_400 : bothSeg evalE (oGrid.idx 100) (oGrid.dm 100) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 100) oGrid.kl oGrid.kr 400 400 ⟨false, 3621630428098647450513590830338908457002396195229446692635795412349227999580⟩ ⟨false, 0⟩ ⟨false, 5845857861954942761395111523674211811282814357030101882676332734890304216416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_100_800 : bothSeg evalE (oGrid.idx 100) (oGrid.dm 100) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 100) oGrid.kl oGrid.kr 400 800 ⟨false, 5845857861954942761395111523674211811282814357030101882676332734890304216416⟩ ⟨false, 0⟩ ⟨false, 6680304685620912477432897047221176688486791196385558596168574932098017502440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_100_1200 : bothSeg evalE (oGrid.idx 100) (oGrid.dm 100) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 100) oGrid.kl oGrid.kr 400 1200 ⟨false, 6680304685620912477432897047221176688486791196385558596168574932098017502440⟩ ⟨false, 0⟩ ⟨false, 6823790966844931218374386350294424027966771269458426367725541365487288833860⟩ ⟨false, 186406579622777328166326106318896104763793365303329660192404464643800806⟩ = true := by
  decide +kernel

theorem b_100_1600 : bothSeg evalE (oGrid.idx 100) (oGrid.dm 100) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 100) oGrid.kl oGrid.kr 400 1600 ⟨false, 6823790966844931218374386350294424027966771269458426367725541365487288833860⟩ ⟨false, 186406579622777328166326106318896104763793365303329660192404464643800806⟩ ⟨false, 6642547848140040752849357459397414839076005212882655222948642677695839376926⟩ ⟨false, 181685205064342366723614157225435170466212742258739341606045872228194212530⟩ = true := by
  decide +kernel

theorem b_100_2000 : bothSeg evalE (oGrid.idx 100) (oGrid.dm 100) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 100) oGrid.kl oGrid.kr 400 2000 ⟨false, 6642547848140040752849357459397414839076005212882655222948642677695839376926⟩ ⟨false, 181685205064342366723614157225435170466212742258739341606045872228194212530⟩ ⟨false, 6582336028432856940422113119643311201221038113149376441297232087752636279606⟩ ⟨false, 242598039690397906300568301423244333356690809394242374382097500596462082364⟩ = true := by
  decide +kernel

theorem b_100_2400 : bothLoop evalE (oGrid.idx 100) (oGrid.dm 100) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 100) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6582336028432856940422113119643311201221038113149376441297232087752636279606⟩ ⟨false, 242598039690397906300568301423244333356690809394242374382097500596462082364⟩ = true := by
  decide +kernel

theorem o_row_100 : oGrid.row evalE 100 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_100_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_100_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_100_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_100_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_100_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_100_2000).1 (bothLoop_sound b_100_2400).1))))))

theorem n_row_100 : nGrid.row evalE 100 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_100_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_100_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_100_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_100_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_100_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_100_2000).2 (bothLoop_sound b_100_2400).2))))))

theorem b_101_0 : bothSeg evalE (oGrid.idx 101) (oGrid.dm 101) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 101) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3608367222650977707031448279696330353036870866789205879712705025192532624826⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_101_400 : bothSeg evalE (oGrid.idx 101) (oGrid.dm 101) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 101) oGrid.kl oGrid.kr 400 400 ⟨false, 3608367222650977707031448279696330353036870866789205879712705025192532624826⟩ ⟨false, 0⟩ ⟨false, 5824670627223133690740162469655912092523834847131786436262933980568773654008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_101_800 : bothSeg evalE (oGrid.idx 101) (oGrid.dm 101) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 101) oGrid.kl oGrid.kr 400 800 ⟨false, 5824670627223133690740162469655912092523834847131786436262933980568773654008⟩ ⟨false, 0⟩ ⟨false, 6655996605070329709551690092409518560658885753312355641458349787874652645456⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_101_1200 : bothSeg evalE (oGrid.idx 101) (oGrid.dm 101) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 101) oGrid.kl oGrid.kr 400 1200 ⟨false, 6655996605070329709551690092409518560658885753312355641458349787874652645456⟩ ⟨false, 0⟩ ⟨false, 6798605160103012371296669237421646031817191658379691354126534691807282362932⟩ ⟨false, 221513463555598531731095764172276547774595171671283019119930837739787546⟩ = true := by
  decide +kernel

theorem b_101_1600 : bothSeg evalE (oGrid.idx 101) (oGrid.dm 101) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 101) oGrid.kl oGrid.kr 400 1600 ⟨false, 6798605160103012371296669237421646031817191658379691354126534691807282362932⟩ ⟨false, 221513463555598531731095764172276547774595171671283019119930837739787546⟩ ⟨false, 6617239407554171149788448382740720704639993553276431733318377872074640383110⟩ ⟨false, 181843589417889150282979464430070877725919400288701487761517487294299936396⟩ = true := by
  decide +kernel

theorem b_101_2000 : bothSeg evalE (oGrid.idx 101) (oGrid.dm 101) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 101) oGrid.kl oGrid.kr 400 2000 ⟨false, 6617239407554171149788448382740720704639993553276431733318377872074640383110⟩ ⟨false, 181843589417889150282979464430070877725919400288701487761517487294299936396⟩ ⟨false, 6557386656293466944181998549136953077017005451492642189262870466051835366386⟩ ⟨false, 242398971618871104004620327437204949109597781174799797955285715934639313544⟩ = true := by
  decide +kernel

theorem b_101_2400 : bothLoop evalE (oGrid.idx 101) (oGrid.dm 101) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 101) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6557386656293466944181998549136953077017005451492642189262870466051835366386⟩ ⟨false, 242398971618871104004620327437204949109597781174799797955285715934639313544⟩ = true := by
  decide +kernel

theorem o_row_101 : oGrid.row evalE 101 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_101_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_101_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_101_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_101_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_101_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_101_2000).1 (bothLoop_sound b_101_2400).1))))))

theorem n_row_101 : nGrid.row evalE 101 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_101_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_101_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_101_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_101_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_101_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_101_2000).2 (bothLoop_sound b_101_2400).2))))))

theorem b_102_0 : bothSeg evalE (oGrid.idx 102) (oGrid.dm 102) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 102) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3595143430452926692615880204637797367541994165153350485662912017299266522252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_102_400 : bothSeg evalE (oGrid.idx 102) (oGrid.dm 102) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 102) oGrid.kl oGrid.kr 400 400 ⟨false, 3595143430452926692615880204637797367541994165153350485662912017299266522252⟩ ⟨false, 0⟩ ⟨false, 5803542859627959490611620535167229961718435483020676231923918826790743335110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_102_800 : bothSeg evalE (oGrid.idx 102) (oGrid.dm 102) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 102) oGrid.kl oGrid.kr 400 800 ⟨false, 5803542859627959490611620535167229961718435483020676231923918826790743335110⟩ ⟨false, 0⟩ ⟨false, 6631754400973059452800258833518858856940457146328934797789830717315846952556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_102_1200 : bothSeg evalE (oGrid.idx 102) (oGrid.dm 102) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 102) oGrid.kl oGrid.kr 400 1200 ⟨false, 6631754400973059452800258833518858856940457146328934797789830717315846952556⟩ ⟨false, 0⟩ ⟨false, 6773484170104382898924407356309435323324886382834513315999106444794211498836⟩ ⟨false, 260051586182255107903022441080280576715919243280582777890210735608048296⟩ = true := by
  decide +kernel

theorem b_102_1600 : bothSeg evalE (oGrid.idx 102) (oGrid.dm 102) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 102) oGrid.kl oGrid.kr 400 1600 ⟨false, 6773484170104382898924407356309435323324886382834513315999106444794211498836⟩ ⟨false, 260051586182255107903022441080280576715919243280582777890210735608048296⟩ ⟨false, 6592000635553710979568190683391867915380557637530341586081046321616327011934⟩ ⟨false, 182000811984933277809007459968694146759028147363563311999813654821136901650⟩ = true := by
  decide +kernel

theorem b_102_2000 : bothSeg evalE (oGrid.idx 102) (oGrid.dm 102) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 102) oGrid.kl oGrid.kr 400 2000 ⟨false, 6592000635553710979568190683391867915380557637530341586081046321616327011934⟩ ⟨false, 182000811984933277809007459968694146759028147363563311999813654821136901650⟩ ⟨false, 6532504694403115987579527074037862267412541338170948693227270922733236993504⟩ ⟨false, 242200793578981094632353445595455133542261463545354337213791480003744557472⟩ = true := by
  decide +kernel

theorem b_102_2400 : bothLoop evalE (oGrid.idx 102) (oGrid.dm 102) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 102) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6532504694403115987579527074037862267412541338170948693227270922733236993504⟩ ⟨false, 242200793578981094632353445595455133542261463545354337213791480003744557472⟩ = true := by
  decide +kernel

theorem o_row_102 : oGrid.row evalE 102 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_102_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_102_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_102_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_102_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_102_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_102_2000).1 (bothLoop_sound b_102_2400).1))))))

theorem n_row_102 : nGrid.row evalE 102 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_102_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_102_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_102_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_102_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_102_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_102_2000).2 (bothLoop_sound b_102_2400).2))))))

theorem b_103_0 : bothSeg evalE (oGrid.idx 103) (oGrid.dm 103) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 103) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3581958940235624973101152875171766180549982620967843983369271527200949745606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_103_400 : bothSeg evalE (oGrid.idx 103) (oGrid.dm 103) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 103) oGrid.kl oGrid.kr 400 400 ⟨false, 3581958940235624973101152875171766180549982620967843983369271527200949745606⟩ ⟨false, 0⟩ ⟨false, 5782474348076934158312547926728951623065323447451878077055576578807935062146⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_103_800 : bothSeg evalE (oGrid.idx 103) (oGrid.dm 103) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 103) oGrid.kl oGrid.kr 400 800 ⟨false, 5782474348076934158312547926728951623065323447451878077055576578807935062146⟩ ⟨false, 0⟩ ⟨false, 6607577911805819486414070600260713704795411326559135547252325960654968837680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_103_1200 : bothSeg evalE (oGrid.idx 103) (oGrid.dm 103) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 103) oGrid.kl oGrid.kr 400 1200 ⟨false, 6607577911805819486414070600260713704795411326559135547252325960654968837680⟩ ⟨false, 0⟩ ⟨false, 6748427714385119758902706193647614178127406684994242184017807489495385232542⟩ ⟨false, 302194603646781119508238188277941767907852196517738879673865008283788898⟩ = true := by
  decide +kernel

theorem b_103_1600 : bothSeg evalE (oGrid.idx 103) (oGrid.dm 103) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 103) oGrid.kl oGrid.kr 400 1600 ⟨false, 6748427714385119758902706193647614178127406684994242184017807489495385232542⟩ ⟨false, 302194603646781119508238188277941767907852196517738879673865008283788898⟩ ⟨false, 6566831454796978268077643039324710155130630349283095006169697009846644289014⟩ ⟨false, 182156258080746229964943156898017033498376452928783230938060698060177303110⟩ = true := by
  decide +kernel

theorem b_103_2000 : bothSeg evalE (oGrid.idx 103) (oGrid.dm 103) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 103) oGrid.kl oGrid.kr 400 2000 ⟨false, 6566831454796978268077643039324710155130630349283095006169697009846644289014⟩ ⟨false, 182156258080746229964943156898017033498376452928783230938060698060177303110⟩ ⟨false, 6507690064096638884803531605997356075473562323808698843040122442980136720322⟩ ⟨false, 242003250193395842891203846006615536735383455950656971689983789067829555680⟩ = true := by
  decide +kernel

theorem b_103_2400 : bothLoop evalE (oGrid.idx 103) (oGrid.dm 103) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 103) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6507690064096638884803531605997356075473562323808698843040122442980136720322⟩ ⟨false, 242003250193395842891203846006615536735383455950656971689983789067829555680⟩ = true := by
  decide +kernel

theorem o_row_103 : oGrid.row evalE 103 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_103_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_103_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_103_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_103_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_103_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_103_2000).1 (bothLoop_sound b_103_2400).1))))))

theorem n_row_103 : nGrid.row evalE 103 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_103_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_103_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_103_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_103_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_103_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_103_2000).2 (bothLoop_sound b_103_2400).2))))))

theorem b_104_0 : bothSeg evalE (oGrid.idx 104) (oGrid.dm 104) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 104) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3568813587624648304725314697448193845878844386902472540916122520155659630356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_104_400 : bothSeg evalE (oGrid.idx 104) (oGrid.dm 104) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 104) oGrid.kl oGrid.kr 400 400 ⟨false, 3568813587624648304725314697448193845878844386902472540916122520155659630356⟩ ⟨false, 0⟩ ⟨false, 5761464956788918808145295191833945724957480980897828968602937569216520196046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_104_800 : bothSeg evalE (oGrid.idx 104) (oGrid.dm 104) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 104) oGrid.kl oGrid.kr 400 800 ⟨false, 5761464956788918808145295191833945724957480980897828968602937569216520196046⟩ ⟨false, 0⟩ ⟨false, 6583466929700582167065991303031717162104142138710867892637899707775580679510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_104_1200 : bothSeg evalE (oGrid.idx 104) (oGrid.dm 104) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 104) oGrid.kl oGrid.kr 400 1200 ⟨false, 6583466929700582167065991303031717162104142138710867892637899707775580679510⟩ ⟨false, 0⟩ ⟨false, 6723435464668090017385733843975211895915426972356728578599910431059015033952⟩ ⟨false, 348085987959851031661568218627509814734482843547432642762701194391725774⟩ = true := by
  decide +kernel

theorem b_104_1600 : bothSeg evalE (oGrid.idx 104) (oGrid.dm 104) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 104) oGrid.kl oGrid.kr 400 1600 ⟨false, 6723435464668090017385733843975211895915426972356728578599910431059015033952⟩ ⟨false, 348085987959851031661568218627509814734482843547432642762701194391725774⟩ ⟨false, 6541731637932575775064264623253538894084906203909095070928005106964688391674⟩ ⟨false, 182310155582623260198325157661705036812933107971040628585347797392894145742⟩ = true := by
  decide +kernel

theorem b_104_2000 : bothSeg evalE (oGrid.idx 104) (oGrid.dm 104) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 104) oGrid.kl oGrid.kr 400 2000 ⟨false, 6541731637932575775064264623253538894084906203909095070928005106964688391674⟩ ⟨false, 182310155582623260198325157661705036812933107971040628585347797392894145742⟩ ⟨false, 6482942553066325162556762793182909780909394673781327560529781053691152301712⟩ ⟨false, 241806338199229798137859645827602971781584563117923232861402832636338965212⟩ = true := by
  decide +kernel

theorem b_104_2400 : bothLoop evalE (oGrid.idx 104) (oGrid.dm 104) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 104) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6482942553066325162556762793182909780909394673781327560529781053691152301712⟩ ⟨false, 241806338199229798137859645827602971781584563117923232861402832636338965212⟩ = true := by
  decide +kernel

theorem o_row_104 : oGrid.row evalE 104 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_104_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_104_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_104_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_104_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_104_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_104_2000).1 (bothLoop_sound b_104_2400).1))))))

theorem n_row_104 : nGrid.row evalE 104 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_104_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_104_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_104_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_104_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_104_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_104_2000).2 (bothLoop_sound b_104_2400).2))))))

theorem b_105_0 : bothSeg evalE (oGrid.idx 105) (oGrid.dm 105) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 105) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3555707306792094696499866769596395902960624555451207239761307379477237446962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_105_400 : bothSeg evalE (oGrid.idx 105) (oGrid.dm 105) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 105) oGrid.kl oGrid.kr 400 400 ⟨false, 3555707306792094696499866769596395902960624555451207239761307379477237446962⟩ ⟨false, 0⟩ ⟨false, 5740514536972995850085414345282300088247107519957111029935712790499006257840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_105_800 : bothSeg evalE (oGrid.idx 105) (oGrid.dm 105) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 105) oGrid.kl oGrid.kr 400 800 ⟨false, 5740514536972995850085414345282300088247107519957111029935712790499006257840⟩ ⟨false, 0⟩ ⟨false, 6559421326972229208483122538721670624826391075865507605204647000759591612322⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_105_1200 : bothSeg evalE (oGrid.idx 105) (oGrid.dm 105) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 105) oGrid.kl oGrid.kr 400 1200 ⟨false, 6559421326972229208483122538721670624826391075865507605204647000759591612322⟩ ⟨false, 0⟩ ⟨false, 6698507203747531439529811420307701861590306507158074397302482438124115332316⟩ ⟨false, 397792003239117846278525436661095132046606056077289508749097456860867240⟩ = true := by
  decide +kernel

theorem b_105_1600 : bothSeg evalE (oGrid.idx 105) (oGrid.dm 105) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 105) oGrid.kl oGrid.kr 400 1600 ⟨false, 6698507203747531439529811420307701861590306507158074397302482438124115332316⟩ ⟨false, 397792003239117846278525436661095132046606056077289508749097456860867240⟩ ⟨false, 6516700955907019937375179122465186729758288923518459226461126823111108265534⟩ ⟨false, 182462866830705848021622169951192267247724742160520154241479578706306108610⟩ = true := by
  decide +kernel

theorem b_105_2000 : bothSeg evalE (oGrid.idx 105) (oGrid.dm 105) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 105) oGrid.kl oGrid.kr 400 2000 ⟨false, 6516700955907019937375179122465186729758288923518459226461126823111108265534⟩ ⟨false, 182462866830705848021622169951192267247724742160520154241479578706306108610⟩ ⟨false, 6458261936108710424042004739773599116189259193063293990574249988800181097170⟩ ⟨false, 241610445735988294038447273523531753861184820062025713794721685507449578434⟩ = true := by
  decide +kernel

theorem b_105_2400 : bothLoop evalE (oGrid.idx 105) (oGrid.dm 105) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 105) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6458261936108710424042004739773599116189259193063293990574249988800181097170⟩ ⟨false, 241610445735988294038447273523531753861184820062025713794721685507449578434⟩ = true := by
  decide +kernel

theorem o_row_105 : oGrid.row evalE 105 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_105_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_105_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_105_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_105_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_105_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_105_2000).1 (bothLoop_sound b_105_2400).1))))))

theorem n_row_105 : nGrid.row evalE 105 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_105_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_105_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_105_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_105_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_105_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_105_2000).2 (bothLoop_sound b_105_2400).2))))))

theorem b_106_0 : bothSeg evalE (oGrid.idx 106) (oGrid.dm 106) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 106) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3542639982431569591725272581031837630461681755200925612820476836807408050394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_106_400 : bothSeg evalE (oGrid.idx 106) (oGrid.dm 106) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 106) oGrid.kl oGrid.kr 400 400 ⟨false, 3542639982431569591725272581031837630461681755200925612820476836807408050394⟩ ⟨false, 0⟩ ⟨false, 5719622933028204878509263959788851912244605804199113204951019687453941760230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_106_800 : bothSeg evalE (oGrid.idx 106) (oGrid.dm 106) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 106) oGrid.kl oGrid.kr 400 800 ⟨false, 5719622933028204878509263959788851912244605804199113204951019687453941760230⟩ ⟨false, 0⟩ ⟨false, 6535441001246576882711492233198076786548145469314404317431537017330656955380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_106_1200 : bothSeg evalE (oGrid.idx 106) (oGrid.dm 106) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 106) oGrid.kl oGrid.kr 400 1200 ⟨false, 6535441001246576882711492233198076786548145469314404317431537017330656955380⟩ ⟨false, 0⟩ ⟨false, 6673642674135691031629948226590298244882767679144310345079061574131758251194⟩ ⟨false, 451465579122157791744712507990499999878363726990872057357342622805960902⟩ = true := by
  decide +kernel

theorem b_106_1600 : bothSeg evalE (oGrid.idx 106) (oGrid.dm 106) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 106) oGrid.kl oGrid.kr 400 1600 ⟨false, 6673642674135691031629948226590298244882767679144310345079061574131758251194⟩ ⟨false, 451465579122157791744712507990499999878363726990872057357342622805960902⟩ ⟨false, 6491739440453412685581736620958626069895005304289119627483824406174692713986⟩ ⟨false, 182614591097925180860974173015074451610243046904064945330931406264629427206⟩ = true := by
  decide +kernel

theorem b_106_2000 : bothSeg evalE (oGrid.idx 106) (oGrid.dm 106) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 106) oGrid.kl oGrid.kr 400 2000 ⟨false, 6491739440453412685581736620958626069895005304289119627483824406174692713986⟩ ⟨false, 182614591097925180860974173015074451610243046904064945330931406264629427206⟩ ⟨false, 6433648261679372943571764587151252298448163294373151524730928957180367067158⟩ ⟨false, 241415913799746001478718723935034919592330861708650887754873150624842205976⟩ = true := by
  decide +kernel

theorem b_106_2400 : bothLoop evalE (oGrid.idx 106) (oGrid.dm 106) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 106) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6433648261679372943571764587151252298448163294373151524730928957180367067158⟩ ⟨false, 241415913799746001478718723935034919592330861708650887754873150624842205976⟩ = true := by
  decide +kernel

theorem o_row_106 : oGrid.row evalE 106 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_106_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_106_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_106_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_106_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_106_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_106_2000).1 (bothLoop_sound b_106_2400).1))))))

theorem n_row_106 : nGrid.row evalE 106 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_106_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_106_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_106_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_106_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_106_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_106_2000).2 (bothLoop_sound b_106_2400).2))))))

theorem b_107_0 : bothSeg evalE (oGrid.idx 107) (oGrid.dm 107) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 107) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3529611503586332120365140631971458904354759487994666256575076896105227425088⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_107_400 : bothSeg evalE (oGrid.idx 107) (oGrid.dm 107) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 107) oGrid.kl oGrid.kr 400 400 ⟨false, 3529611503586332120365140631971458904354759487994666256575076896105227425088⟩ ⟨false, 0⟩ ⟨false, 5698790103533500863989446880191816284107608843156560865730014591307093033298⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_107_800 : bothSeg evalE (oGrid.idx 107) (oGrid.dm 107) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 107) oGrid.kl oGrid.kr 400 800 ⟨false, 5698790103533500863989446880191816284107608843156560865730014591307093033298⟩ ⟨false, 0⟩ ⟨false, 6511525834956868745947779608603113166724672757696736665636165100969676988620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_107_1200 : bothSeg evalE (oGrid.idx 107) (oGrid.dm 107) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 107) oGrid.kl oGrid.kr 400 1200 ⟨false, 6511525834956868745947779608603113166724672757696736665636165100969676988620⟩ ⟨false, 0⟩ ⟨false, 6648841700787842629812912087364439135496646077534101740655465440517911301096⟩ ⟨false, 509250359973758811508377744984182765132139623457771111785558107895112692⟩ = true := by
  decide +kernel

theorem b_107_1600 : bothSeg evalE (oGrid.idx 107) (oGrid.dm 107) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 107) oGrid.kl oGrid.kr 400 1600 ⟨false, 6648841700787842629812912087364439135496646077534101740655465440517911301096⟩ ⟨false, 509250359973758811508377744984182765132139623457771111785558107895112692⟩ ⟨false, 6466846913053414530330517600189795503495227133493593044705495406742865601012⟩ ⟨false, 182764775402706361120452038966476768573731671959632383787938079345282901906⟩ = true := by
  decide +kernel

theorem b_107_2000 : bothSeg evalE (oGrid.idx 107) (oGrid.dm 107) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 107) oGrid.kl oGrid.kr 400 2000 ⟨false, 6466846913053414530330517600189795503495227133493593044705495406742865601012⟩ ⟨false, 182764775402706361120452038966476768573731671959632383787938079345282901906⟩ ⟨false, 6409101348220104685916435724060785441402704920856545789541307648041623896838⟩ ⟨false, 241221895905420395241574375633769562601466011902913870021242241233193625746⟩ = true := by
  decide +kernel

theorem b_107_2400 : bothLoop evalE (oGrid.idx 107) (oGrid.dm 107) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 107) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6409101348220104685916435724060785441402704920856545789541307648041623896838⟩ ⟨false, 241221895905420395241574375633769562601466011902913870021242241233193625746⟩ = true := by
  decide +kernel

theorem o_row_107 : oGrid.row evalE 107 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_107_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_107_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_107_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_107_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_107_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_107_2000).1 (bothLoop_sound b_107_2400).1))))))

theorem n_row_107 : nGrid.row evalE 107 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_107_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_107_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_107_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_107_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_107_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_107_2000).2 (bothLoop_sound b_107_2400).2))))))

theorem b_108_0 : bothSeg evalE (oGrid.idx 108) (oGrid.dm 108) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 108) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3516621787146907046942900131159004675720821979976567906552588256108441478124⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_108_400 : bothSeg evalE (oGrid.idx 108) (oGrid.dm 108) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 108) oGrid.kl oGrid.kr 400 400 ⟨false, 3516621787146907046942900131159004675720821979976567906552588256108441478124⟩ ⟨false, 0⟩ ⟨false, 5678015809640932311893156304241649266004743096284808808641901531545973863184⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_108_800 : bothSeg evalE (oGrid.idx 108) (oGrid.dm 108) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 108) oGrid.kl oGrid.kr 400 800 ⟨false, 5678015809640932311893156304241649266004743096284808808641901531545973863184⟩ ⟨false, 0⟩ ⟨false, 6487675614302484177043182401950323296161792245907273511564743074083966038018⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_108_1200 : bothSeg evalE (oGrid.idx 108) (oGrid.dm 108) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 108) oGrid.kl oGrid.kr 400 1200 ⟨false, 6487675614302484177043182401950323296161792245907273511564743074083966038018⟩ ⟨false, 0⟩ ⟨false, 6624103911914479808439911198112285499896894258632718563892556183621969323914⟩ ⟨false, 571564160562888961408506182319502944299141453995183946431573766506266120⟩ = true := by
  decide +kernel

theorem b_108_1600 : bothSeg evalE (oGrid.idx 108) (oGrid.dm 108) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 108) oGrid.kl oGrid.kr 400 1600 ⟨false, 6624103911914479808439911198112285499896894258632718563892556183621969323914⟩ ⟨false, 571564160562888961408506182319502944299141453995183946431573766506266120⟩ ⟨false, 6442023213487325755225358694851110543183023470836149742991880728226098862812⟩ ⟨false, 182913531538496242100078396233927756369796304868187947198167619009341643958⟩ = true := by
  decide +kernel

theorem b_108_2000 : bothSeg evalE (oGrid.idx 108) (oGrid.dm 108) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 108) oGrid.kl oGrid.kr 400 2000 ⟨false, 6442023213487325755225358694851110543183023470836149742991880728226098862812⟩ ⟨false, 182913531538496242100078396233927756369796304868187947198167619009341643958⟩ ⟨false, 6384621057504893889963695800945947109400098433662631945815259054556569533000⟩ ⟨false, 241028864768549748478751541255194728247785780650365015936914960527075525860⟩ = true := by
  decide +kernel

theorem b_108_2400 : bothLoop evalE (oGrid.idx 108) (oGrid.dm 108) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 108) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6384621057504893889963695800945947109400098433662631945815259054556569533000⟩ ⟨false, 241028864768549748478751541255194728247785780650365015936914960527075525860⟩ = true := by
  decide +kernel

theorem o_row_108 : oGrid.row evalE 108 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_108_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_108_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_108_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_108_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_108_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_108_2000).1 (bothLoop_sound b_108_2400).1))))))

theorem n_row_108 : nGrid.row evalE 108 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_108_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_108_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_108_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_108_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_108_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_108_2000).2 (bothLoop_sound b_108_2400).2))))))

theorem b_109_0 : bothSeg evalE (oGrid.idx 109) (oGrid.dm 109) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 109) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3503670813501594079716333816152268074707602651344132145964247158828886673020⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_109_400 : bothSeg evalE (oGrid.idx 109) (oGrid.dm 109) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 109) oGrid.kl oGrid.kr 400 400 ⟨false, 3503670813501594079716333816152268074707602651344132145964247158828886673020⟩ ⟨false, 0⟩ ⟨false, 5657300051692436754805610067981314207216058351317723215094351020233964477214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_109_800 : bothSeg evalE (oGrid.idx 109) (oGrid.dm 109) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 109) oGrid.kl oGrid.kr 400 800 ⟨false, 5657300051692436754805610067981314207216058351317723215094351020233964477214⟩ ⟨false, 0⟩ ⟨false, 6463890383559719177819091621939081094641539033356393426704932374566028405628⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_109_1200 : bothSeg evalE (oGrid.idx 109) (oGrid.dm 109) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 109) oGrid.kl oGrid.kr 400 1200 ⟨false, 6463890383559719177819091621939081094641539033356393426704932374566028405628⟩ ⟨false, 0⟩ ⟨false, 6599429297937772590491105500699950192730815930200898214254767430412002647492⟩ ⟨false, 638124691623689748217842087851797554109116959711921681202644765246350882⟩ = true := by
  decide +kernel

theorem b_109_1600 : bothSeg evalE (oGrid.idx 109) (oGrid.dm 109) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 109) oGrid.kl oGrid.kr 400 1600 ⟨false, 6599429297937772590491105500699950192730815930200898214254767430412002647492⟩ ⟨false, 638124691623689748217842087851797554109116959711921681202644765246350882⟩ ⟨false, 6417268258235014755115442419601238252618754853978235780255219285551346636472⟩ ⟨false, 183060688470314712463435048419424044706537128016193507446591902935370943758⟩ = true := by
  decide +kernel

theorem b_109_2000 : bothSeg evalE (oGrid.idx 109) (oGrid.dm 109) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 109) oGrid.kl oGrid.kr 400 2000 ⟨false, 6417268258235014755115442419601238252618754853978235780255219285551346636472⟩ ⟨false, 183060688470314712463435048419424044706537128016193507446591902935370943758⟩ ⟨false, 6360207304576944888932861478732996048569981142399354845662640096129138111896⟩ ⟨false, 240836216005650347526036990578457955859039620779053845297332849302063231312⟩ = true := by
  decide +kernel

theorem b_109_2400 : bothLoop evalE (oGrid.idx 109) (oGrid.dm 109) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 109) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6360207304576944888932861478732996048569981142399354845662640096129138111896⟩ ⟨false, 240836216005650347526036990578457955859039620779053845297332849302063231312⟩ = true := by
  decide +kernel

theorem o_row_109 : oGrid.row evalE 109 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_109_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_109_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_109_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_109_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_109_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_109_2000).1 (bothLoop_sound b_109_2400).1))))))

theorem n_row_109 : nGrid.row evalE 109 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_109_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_109_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_109_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_109_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_109_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_109_2000).2 (bothLoop_sound b_109_2400).2))))))

theorem b_110_0 : bothSeg evalE (oGrid.idx 110) (oGrid.dm 110) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 110) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3490758338360394029710875869386436006316985239891018609613149634310445448906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_110_400 : bothSeg evalE (oGrid.idx 110) (oGrid.dm 110) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 110) oGrid.kl oGrid.kr 400 400 ⟨false, 3490758338360394029710875869386436006316985239891018609613149634310445448906⟩ ⟨false, 0⟩ ⟨false, 5636642529064348699273274870413939757362961592106770176182858323624972929404⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_110_800 : bothSeg evalE (oGrid.idx 110) (oGrid.dm 110) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 110) oGrid.kl oGrid.kr 400 800 ⟨false, 5636642529064348699273274870413939757362961592106770176182858323624972929404⟩ ⟨false, 0⟩ ⟨false, 6440169792547737746828477626101495470003749772252071606508366289129865502248⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_110_1200 : bothSeg evalE (oGrid.idx 110) (oGrid.dm 110) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 110) oGrid.kl oGrid.kr 400 1200 ⟨false, 6440169792547737746828477626101495470003749772252071606508366289129865502248⟩ ⟨false, 0⟩ ⟨false, 6574817329123299727604611202232415359518053002676178878187394354469849072064⟩ ⟨false, 709120891582511751114030295172551880371199012062484054631767472585277876⟩ = true := by
  decide +kernel

theorem b_110_1600 : bothSeg evalE (oGrid.idx 110) (oGrid.dm 110) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 110) oGrid.kl oGrid.kr 400 1600 ⟨false, 6574817329123299727604611202232415359518053002676178878187394354469849072064⟩ ⟨false, 709120891582511751114030295172551880371199012062484054631767472585277876⟩ ⟨false, 6392581757945015991221258287201242071425439817942118944095009445740009265806⟩ ⟨false, 183206972454594977121815417138584952132751882030787853640617257169179432696⟩ = true := by
  decide +kernel

theorem b_110_2000 : bothSeg evalE (oGrid.idx 110) (oGrid.dm 110) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 110) oGrid.kl oGrid.kr 400 2000 ⟨false, 6392581757945015991221258287201242071425439817942118944095009445740009265806⟩ ⟨false, 183206972454594977121815417138584952132751882030787853640617257169179432696⟩ ⟨false, 6335859836140560412322835485970227430506465516317536707446980239132363000224⟩ ⟨false, 240645090749545128590375502375197496486139236682233743745787444033564303010⟩ = true := by
  decide +kernel

theorem b_110_2400 : bothLoop evalE (oGrid.idx 110) (oGrid.dm 110) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 110) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6335859836140560412322835485970227430506465516317536707446980239132363000224⟩ ⟨false, 240645090749545128590375502375197496486139236682233743745787444033564303010⟩ = true := by
  decide +kernel

theorem o_row_110 : oGrid.row evalE 110 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_110_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_110_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_110_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_110_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_110_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_110_2000).1 (bothLoop_sound b_110_2400).1))))))

theorem n_row_110 : nGrid.row evalE 110 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_110_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_110_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_110_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_110_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_110_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_110_2000).2 (bothLoop_sound b_110_2400).2))))))

theorem b_111_0 : bothSeg evalE (oGrid.idx 111) (oGrid.dm 111) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 111) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3477884270927252960661542212235874056569219471780832640001921891107804356780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_111_400 : bothSeg evalE (oGrid.idx 111) (oGrid.dm 111) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 111) oGrid.kl oGrid.kr 400 400 ⟨false, 3477884270927252960661542212235874056569219471780832640001921891107804356780⟩ ⟨false, 0⟩ ⟨false, 5616043146227815709323266366613492989415064572799622804735464102905494135474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_111_800 : bothSeg evalE (oGrid.idx 111) (oGrid.dm 111) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 111) oGrid.kl oGrid.kr 400 800 ⟨false, 5616043146227815709323266366613492989415064572799622804735464102905494135474⟩ ⟨false, 0⟩ ⟨false, 6416513740791178557077304909462853513068175514411579826749003166911062137556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_111_1200 : bothSeg evalE (oGrid.idx 111) (oGrid.dm 111) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 111) oGrid.kl oGrid.kr 400 1200 ⟨false, 6416513740791178557077304909462853513068175514411579826749003166911062137556⟩ ⟨false, 0⟩ ⟨false, 6550267869038942281260282137672335562822808435999854468099161388032659581540⟩ ⟨false, 784597785963336579762676895718260019667562485016707217440953538015787176⟩ = true := by
  decide +kernel

theorem b_111_1600 : bothSeg evalE (oGrid.idx 111) (oGrid.dm 111) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 111) oGrid.kl oGrid.kr 400 1600 ⟨false, 6550267869038942281260282137672335562822808435999854468099161388032659581540⟩ ⟨false, 784597785963336579762676895718260019667562485016707217440953538015787176⟩ ⟨false, 6367963552217989648988719603319345952443514265450694532258118015295865752060⟩ ⟨false, 183352322297840495725290724834336882196610396931046342617532377575393477852⟩ = true := by
  decide +kernel

theorem b_111_2000 : bothSeg evalE (oGrid.idx 111) (oGrid.dm 111) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 111) oGrid.kl oGrid.kr 400 2000 ⟨false, 6367963552217989648988719603319345952443514265450694532258118015295865752060⟩ ⟨false, 183352322297840495725290724834336882196610396931046342617532377575393477852⟩ ⟨false, 6311578487691413255573488089813380678911544881957682366375386451628549890234⟩ ⟨false, 240455005852774338812124905114033543569151465992619631462821467589946507368⟩ = true := by
  decide +kernel

theorem b_111_2400 : bothLoop evalE (oGrid.idx 111) (oGrid.dm 111) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 111) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6311578487691413255573488089813380678911544881957682366375386451628549890234⟩ ⟨false, 240455005852774338812124905114033543569151465992619631462821467589946507368⟩ = true := by
  decide +kernel

theorem o_row_111 : oGrid.row evalE 111 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_111_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_111_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_111_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_111_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_111_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_111_2000).1 (bothLoop_sound b_111_2400).1))))))

theorem n_row_111 : nGrid.row evalE 111 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_111_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_111_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_111_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_111_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_111_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_111_2000).2 (bothLoop_sound b_111_2400).2))))))

theorem b_112_0 : bothSeg evalE (oGrid.idx 112) (oGrid.dm 112) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 112) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3465048541908582332140834374649507793952872879523875622721166052215170883690⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_112_400 : bothSeg evalE (oGrid.idx 112) (oGrid.dm 112) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 112) oGrid.kl oGrid.kr 400 400 ⟨false, 3465048541908582332140834374649507793952872879523875622721166052215170883690⟩ ⟨false, 0⟩ ⟨false, 5595501849535268406685716034538818573305218427544502020904467174342113050510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_112_800 : bothSeg evalE (oGrid.idx 112) (oGrid.dm 112) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 112) oGrid.kl oGrid.kr 400 800 ⟨false, 5595501849535268406685716034538818573305218427544502020904467174342113050510⟩ ⟨false, 0⟩ ⟨false, 6392922227264370271551760557638511876522303783428331488329047077507047783776⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_112_1200 : bothSeg evalE (oGrid.idx 112) (oGrid.dm 112) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 112) oGrid.kl oGrid.kr 400 1200 ⟨false, 6392922227264370271551760557638511876522303783428331488329047077507047783776⟩ ⟨false, 0⟩ ⟨false, 6525780767643923111989878798838852003177311846396393180127056772859768312278⟩ ⟨false, 864717370325040552396697359190030279321512125787847301295342449278197514⟩ = true := by
  decide +kernel

theorem b_112_1600 : bothSeg evalE (oGrid.idx 112) (oGrid.dm 112) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 112) oGrid.kl oGrid.kr 400 1600 ⟨false, 6525780767643923111989878798838852003177311846396393180127056772859768312278⟩ ⟨false, 864717370325040552396697359190030279321512125787847301295342449278197514⟩ ⟨false, 6343413819703860613548459525386830468370449870449276510660950523598985055282⟩ ⟨false, 183495895033823695743585858589708771308489770525608370986506684307834156952⟩ = true := by
  decide +kernel

theorem b_112_2000 : bothSeg evalE (oGrid.idx 112) (oGrid.dm 112) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 112) oGrid.kl oGrid.kr 400 2000 ⟨false, 6343413819703860613548459525386830468370449870449276510660950523598985055282⟩ ⟨false, 183495895033823695743585858589708771308489770525608370986506684307834156952⟩ ⟨false, 6287363440814543440159846617766627128326532738419958138846463210815159652784⟩ ⟨false, 240265538898909351856688715419530043686521932604183435488576169833057035380⟩ = true := by
  decide +kernel

theorem b_112_2400 : bothLoop evalE (oGrid.idx 112) (oGrid.dm 112) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 112) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6287363440814543440159846617766627128326532738419958138846463210815159652784⟩ ⟨false, 240265538898909351856688715419530043686521932604183435488576169833057035380⟩ = true := by
  decide +kernel

theorem o_row_112 : oGrid.row evalE 112 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_112_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_112_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_112_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_112_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_112_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_112_2000).1 (bothLoop_sound b_112_2400).1))))))

theorem n_row_112 : nGrid.row evalE 112 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_112_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_112_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_112_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_112_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_112_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_112_2000).2 (bothLoop_sound b_112_2400).2))))))

theorem b_113_0 : bothSeg evalE (oGrid.idx 113) (oGrid.dm 113) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 113) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3452251052535886921244897487290456031539361049277787443965461641058097163842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_113_400 : bothSeg evalE (oGrid.idx 113) (oGrid.dm 113) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 113) oGrid.kl oGrid.kr 400 400 ⟨false, 3452251052535886921244897487290456031539361049277787443965461641058097163842⟩ ⟨false, 0⟩ ⟨false, 5575018410747997106741315459247223880687672840044400943963360794670269055752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_113_800 : bothSeg evalE (oGrid.idx 113) (oGrid.dm 113) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 113) oGrid.kl oGrid.kr 400 800 ⟨false, 5575018410747997106741315459247223880687672840044400943963360794670269055752⟩ ⟨false, 0⟩ ⟨false, 6369394984213523811579254043858310122036298660455078097376664609192786892544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_113_1200 : bothSeg evalE (oGrid.idx 113) (oGrid.dm 113) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 113) oGrid.kl oGrid.kr 400 1200 ⟨false, 6369394984213523811579254043858310122036298660455078097376664609192786892544⟩ ⟨false, 0⟩ ⟨false, 6501355671123198300990356550142931925285301707067637520205561357733746312416⟩ ⟨false, 949549510330637810169878220933860301376937417104693289720075441916934986⟩ = true := by
  decide +kernel

theorem b_113_1600 : bothSeg evalE (oGrid.idx 113) (oGrid.dm 113) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 113) oGrid.kl oGrid.kr 400 1600 ⟨false, 6501355671123198300990356550142931925285301707067637520205561357733746312416⟩ ⟨false, 949549510330637810169878220933860301376937417104693289720075441916934986⟩ ⟨false, 6318932176476413927820807632797460210551339731551311313520064957809031138708⟩ ⟨false, 183637800729266590634515787275259525275142267135117276192788726474527324292⟩ = true := by
  decide +kernel

theorem b_113_2000 : bothSeg evalE (oGrid.idx 113) (oGrid.dm 113) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 113) oGrid.kl oGrid.kr 400 2000 ⟨false, 6318932176476413927820807632797460210551339731551311313520064957809031138708⟩ ⟨false, 183637800729266590634515787275259525275142267135117276192788726474527324292⟩ ⟨false, 6263214343254028993806885356945916671305299269581760610327413073769466438768⟩ ⟨false, 240076348664688933051176905815171498463192943534094283645979101781082956988⟩ = true := by
  decide +kernel

theorem b_113_2400 : bothLoop evalE (oGrid.idx 113) (oGrid.dm 113) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 113) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6263214343254028993806885356945916671305299269581760610327413073769466438768⟩ ⟨false, 240076348664688933051176905815171498463192943534094283645979101781082956988⟩ = true := by
  decide +kernel

theorem o_row_113 : oGrid.row evalE 113 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_113_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_113_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_113_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_113_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_113_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_113_2000).1 (bothLoop_sound b_113_2400).1))))))

theorem n_row_113 : nGrid.row evalE 113 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_113_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_113_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_113_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_113_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_113_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_113_2000).2 (bothLoop_sound b_113_2400).2))))))

theorem b_114_0 : bothSeg evalE (oGrid.idx 114) (oGrid.dm 114) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 114) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3439491726792956858505008017518031415984494803011763197723640781415634213370⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_114_400 : bothSeg evalE (oGrid.idx 114) (oGrid.dm 114) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 114) oGrid.kl oGrid.kr 400 400 ⟨false, 3439491726792956858505008017518031415984494803011763197723640781415634213370⟩ ⟨false, 0⟩ ⟨false, 5554592744980669987021571552023027398182507817495702949098073828914572340468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_114_800 : bothSeg evalE (oGrid.idx 114) (oGrid.dm 114) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 114) oGrid.kl oGrid.kr 400 800 ⟨false, 5554592744980669987021571552023027398182507817495702949098073828914572340468⟩ ⟨false, 0⟩ ⟨false, 6345931911788741697772237634663873277190941314009101092884844630466363299118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_114_1200 : bothSeg evalE (oGrid.idx 114) (oGrid.dm 114) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 114) oGrid.kl oGrid.kr 400 1200 ⟨false, 6345931911788741697772237634663873277190941314009101092884844630466363299118⟩ ⟨false, 0⟩ ⟨false, 6476992377864516558323376267359848021929460129467123206296048474004548660898⟩ ⟨false, 1039191905388634777427139797429490230202442130539446141529143901006505636⟩ = true := by
  decide +kernel

theorem b_114_1600 : bothSeg evalE (oGrid.idx 114) (oGrid.dm 114) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 114) oGrid.kl oGrid.kr 400 1600 ⟨false, 6476992377864516558323376267359848021929460129467123206296048474004548660898⟩ ⟨false, 1039191905388634777427139797429490230202442130539446141529143901006505636⟩ ⟨false, 6294518369720578133077037996876736654959417302510117926403171287321868930156⟩ ⟨false, 183778225812065622167787904753584714366520544673100408842072313332271940084⟩ = true := by
  decide +kernel

theorem b_114_2000 : bothSeg evalE (oGrid.idx 114) (oGrid.dm 114) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 114) oGrid.kl oGrid.kr 400 2000 ⟨false, 6294518369720578133077037996876736654959417302510117926403171287321868930156⟩ ⟨false, 183778225812065622167787904753584714366520544673100408842072313332271940084⟩ ⟨false, 6239130928206862676855336276541769233560687159944685143967895449880570516984⟩ ⟨false, 239888009452649940944192839486635853585914391295398182892204893334477318898⟩ = true := by
  decide +kernel

theorem b_114_2400 : bothLoop evalE (oGrid.idx 114) (oGrid.dm 114) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 114) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6239130928206862676855336276541769233560687159944685143967895449880570516984⟩ ⟨false, 239888009452649940944192839486635853585914391295398182892204893334477318898⟩ = true := by
  decide +kernel

theorem o_row_114 : oGrid.row evalE 114 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_114_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_114_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_114_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_114_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_114_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_114_2000).1 (bothLoop_sound b_114_2400).1))))))

theorem n_row_114 : nGrid.row evalE 114 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_114_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_114_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_114_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_114_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_114_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_114_2000).2 (bothLoop_sound b_114_2400).2))))))

theorem b_115_0 : bothSeg evalE (oGrid.idx 115) (oGrid.dm 115) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 115) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3426770423529014699620801721028194946006968592546183205506039611197196967762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_115_400 : bothSeg evalE (oGrid.idx 115) (oGrid.dm 115) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 115) oGrid.kl oGrid.kr 400 400 ⟨false, 3426770423529014699620801721028194946006968592546183205506039611197196967762⟩ ⟨false, 0⟩ ⟨false, 5534224720247329343845507819725181717099557995171226758567819162407570399170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_115_800 : bothSeg evalE (oGrid.idx 115) (oGrid.dm 115) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 115) oGrid.kl oGrid.kr 400 800 ⟨false, 5534224720247329343845507819725181717099557995171226758567819162407570399170⟩ ⟨false, 0⟩ ⟨false, 6322532922814729585577466019804413487646986160790979863686107921627684073316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_115_1200 : bothSeg evalE (oGrid.idx 115) (oGrid.dm 115) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 115) oGrid.kl oGrid.kr 400 1200 ⟨false, 6322532922814729585577466019804413487646986160790979863686107921627684073316⟩ ⟨false, 0⟩ ⟨false, 6452690734638038652950234449494963245090465597721219421604339443233515184306⟩ ⟨false, 1133937048775988131010803390845330428970568976292936281368520732762400192⟩ = true := by
  decide +kernel

theorem b_115_1600 : bothSeg evalE (oGrid.idx 115) (oGrid.dm 115) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 115) oGrid.kl oGrid.kr 400 1600 ⟨false, 6452690734638038652950234449494963245090465597721219421604339443233515184306⟩ ⟨false, 1133937048775988131010803390845330428970568976292936281368520732762400192⟩ ⟨false, 6270172500037110535352245169866089474577470479751209995422136285771660145512⟩ ⟨false, 183917885901828035268380336707587300836535990652484553267845139860200603042⟩ = true := by
  decide +kernel

theorem b_115_2000 : bothSeg evalE (oGrid.idx 115) (oGrid.dm 115) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 115) oGrid.kl oGrid.kr 400 2000 ⟨false, 6270172500037110535352245169866089474577470479751209995422136285771660145512⟩ ⟨false, 183917885901828035268380336707587300836535990652484553267845139860200603042⟩ ⟨false, 6215113321675897426778148367001347570031560293503836120756606951245265011920⟩ ⟨false, 239700858955194111468240776030179352264377105563854563333878748785801566216⟩ = true := by
  decide +kernel

theorem b_115_2400 : bothLoop evalE (oGrid.idx 115) (oGrid.dm 115) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 115) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6215113321675897426778148367001347570031560293503836120756606951245265011920⟩ ⟨false, 239700858955194111468240776030179352264377105563854563333878748785801566216⟩ = true := by
  decide +kernel

theorem o_row_115 : oGrid.row evalE 115 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_115_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_115_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_115_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_115_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_115_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_115_2000).1 (bothLoop_sound b_115_2400).1))))))

theorem n_row_115 : nGrid.row evalE 115 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_115_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_115_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_115_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_115_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_115_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_115_2000).2 (bothLoop_sound b_115_2400).2))))))

theorem b_116_0 : bothSeg evalE (oGrid.idx 116) (oGrid.dm 116) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 116) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3414087074444276842763212198874732097092445410350695911319103822057167121328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_116_400 : bothSeg evalE (oGrid.idx 116) (oGrid.dm 116) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 116) oGrid.kl oGrid.kr 400 400 ⟨false, 3414087074444276842763212198874732097092445410350695911319103822057167121328⟩ ⟨false, 0⟩ ⟨false, 5513914220943956415636251771214016991239048336321969504526160464537917549754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_116_800 : bothSeg evalE (oGrid.idx 116) (oGrid.dm 116) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 116) oGrid.kl oGrid.kr 400 800 ⟨false, 5513914220943956415636251771214016991239048336321969504526160464537917549754⟩ ⟨false, 0⟩ ⟨false, 6299197877165119262116917167120767224409012251152173751608942666711811583966⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_116_1200 : bothSeg evalE (oGrid.idx 116) (oGrid.dm 116) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 116) oGrid.kl oGrid.kr 400 1200 ⟨false, 6299197877165119262116917167120767224409012251152173751608942666711811583966⟩ ⟨false, 0⟩ ⟨false, 6428450473830083325418519490839512851539306050799687334086883331314620737612⟩ ⟨false, 1233844206508382462976243038726096061130949160817702815010476492849899364⟩ = true := by
  decide +kernel

theorem b_116_1600 : bothSeg evalE (oGrid.idx 116) (oGrid.dm 116) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 116) oGrid.kl oGrid.kr 400 1600 ⟨false, 6428450473830083325418519490839512851539306050799687334086883331314620737612⟩ ⟨false, 1233844206508382462976243038726096061130949160817702815010476492849899364⟩ ⟨false, 6245894430470702090143981799200906154859446790811243049423302429864903882300⟩ ⟨false, 184056722951054555316010170253942205165050591830677607875285958284196411718⟩ = true := by
  decide +kernel

theorem b_116_2000 : bothSeg evalE (oGrid.idx 116) (oGrid.dm 116) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 116) oGrid.kl oGrid.kr 400 2000 ⟨false, 6245894430470702090143981799200906154859446790811243049423302429864903882300⟩ ⟨false, 184056722951054555316010170253942205165050591830677607875285958284196411718⟩ ⟨false, 6191161422565348526683209413633232416559559918918738636472155589054328536382⟩ ⟨false, 239515133993308109180575215060751359816646334919059787486412190162817853180⟩ = true := by
  decide +kernel

theorem b_116_2400 : bothLoop evalE (oGrid.idx 116) (oGrid.dm 116) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 116) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6191161422565348526683209413633232416559559918918738636472155589054328536382⟩ ⟨false, 239515133993308109180575215060751359816646334919059787486412190162817853180⟩ = true := by
  decide +kernel

theorem o_row_116 : oGrid.row evalE 116 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_116_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_116_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_116_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_116_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_116_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_116_2000).1 (bothLoop_sound b_116_2400).1))))))

theorem n_row_116 : nGrid.row evalE 116 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_116_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_116_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_116_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_116_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_116_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_116_2000).2 (bothLoop_sound b_116_2400).2))))))

theorem b_117_0 : bothSeg evalE (oGrid.idx 117) (oGrid.dm 117) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 117) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3401441532348133588421008932236225946024019847771619235399924545126053792612⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_117_400 : bothSeg evalE (oGrid.idx 117) (oGrid.dm 117) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 117) oGrid.kl oGrid.kr 400 400 ⟨false, 3401441532348133588421008932236225946024019847771619235399924545126053792612⟩ ⟨false, 0⟩ ⟨false, 5493661074453821099035040305710638990847755613642925449887330024072996489796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_117_800 : bothSeg evalE (oGrid.idx 117) (oGrid.dm 117) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 117) oGrid.kl oGrid.kr 400 800 ⟨false, 5493661074453821099035040305710638990847755613642925449887330024072996489796⟩ ⟨false, 0⟩ ⟨false, 6275926591645260981199634419217973931026012236351416084520231191206719579262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_117_1200 : bothSeg evalE (oGrid.idx 117) (oGrid.dm 117) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 117) oGrid.kl oGrid.kr 400 1200 ⟨false, 6275926591645260981199634419217973931026012236351416084520231191206719579262⟩ ⟨false, 0⟩ ⟨false, 6404271394846190365296658872621334416162689340499459966476561335838282445032⟩ ⟨false, 1338807991309127893153297283622703517246546879023951022320748314176725496⟩ = true := by
  decide +kernel

theorem b_117_1600 : bothSeg evalE (oGrid.idx 117) (oGrid.dm 117) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 117) oGrid.kl oGrid.kr 400 1600 ⟨false, 6404271394846190365296658872621334416162689340499459966476561335838282445032⟩ ⟨false, 1338807991309127893153297283622703517246546879023951022320748314176725496⟩ ⟨false, 6221683903466921940349110546445338460166950853499138162532693570337215457708⟩ ⟨false, 184193970751049937582968258617280417548457651082068878741270133608729717890⟩ = true := by
  decide +kernel

theorem b_117_2000 : bothSeg evalE (oGrid.idx 117) (oGrid.dm 117) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 117) oGrid.kl oGrid.kr 400 2000 ⟨false, 6221683903466921940349110546445338460166950853499138162532693570337215457708⟩ ⟨false, 184193970751049937582968258617280417548457651082068878741270133608729717890⟩ ⟨false, 6167274961970772198853943130106795804873798700524816233813235156285945884180⟩ ⟨false, 239329857532543662001900816926565645557428202049895235239115246811433598470⟩ = true := by
  decide +kernel

theorem b_117_2400 : bothLoop evalE (oGrid.idx 117) (oGrid.dm 117) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 117) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6167274961970772198853943130106795804873798700524816233813235156285945884180⟩ ⟨false, 239329857532543662001900816926565645557428202049895235239115246811433598470⟩ = true := by
  decide +kernel

theorem o_row_117 : oGrid.row evalE 117 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_117_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_117_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_117_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_117_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_117_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_117_2000).1 (bothLoop_sound b_117_2400).1))))))

theorem n_row_117 : nGrid.row evalE 117 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_117_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_117_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_117_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_117_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_117_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_117_2000).2 (bothLoop_sound b_117_2400).2))))))

theorem b_118_0 : bothSeg evalE (oGrid.idx 118) (oGrid.dm 118) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 118) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3388833707573362382795729397311972417209949573829750070650228655235308108302⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_118_400 : bothSeg evalE (oGrid.idx 118) (oGrid.dm 118) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 118) oGrid.kl oGrid.kr 400 400 ⟨false, 3388833707573362382795729397311972417209949573829750070650228655235308108302⟩ ⟨false, 0⟩ ⟨false, 5473465103886922999333571823951187822004921474995681367451600771803785460470⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_118_800 : bothSeg evalE (oGrid.idx 118) (oGrid.dm 118) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 118) oGrid.kl oGrid.kr 400 800 ⟨false, 5473465103886922999333571823951187822004921474995681367451600771803785460470⟩ ⟨false, 0⟩ ⟨false, 6252718915028167180307850962391724814042310547071906067015661863858288560314⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_118_1200 : bothSeg evalE (oGrid.idx 118) (oGrid.dm 118) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 118) oGrid.kl oGrid.kr 400 1200 ⟨false, 6252718915028167180307850962391724814042310547071906067015661863858288560314⟩ ⟨false, 0⟩ ⟨false, 6380153192903482406198620176458403316214433232299359569687799797570812349306⟩ ⟨false, 1448970970456428502302949987279302365884799830012826155952679889922397842⟩ = true := by
  decide +kernel

theorem b_118_1600 : bothSeg evalE (oGrid.idx 118) (oGrid.dm 118) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 118) oGrid.kl oGrid.kr 400 1600 ⟨false, 6380153192903482406198620176458403316214433232299359569687799797570812349306⟩ ⟨false, 1448970970456428502302949987279302365884799830012826155952679889922397842⟩ ⟨false, 6197540772398118049200715878500607300933501879815023359542729106195290965402⟩ ⟨false, 184329655151819506434952625783005987603934946329211605387303046674468467068⟩ = true := by
  decide +kernel

theorem b_118_2000 : bothSeg evalE (oGrid.idx 118) (oGrid.dm 118) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 118) oGrid.kl oGrid.kr 400 2000 ⟨false, 6197540772398118049200715878500607300933501879815023359542729106195290965402⟩ ⟨false, 184329655151819506434952625783005987603934946329211605387303046674468467068⟩ ⟨false, 6143453810240155418799187651823411794333024637999567482510226097485251686650⟩ ⟨false, 239145062913888396062936585491024900586537751816251021651328301630723108968⟩ = true := by
  decide +kernel

theorem b_118_2400 : bothLoop evalE (oGrid.idx 118) (oGrid.dm 118) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 118) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6143453810240155418799187651823411794333024637999567482510226097485251686650⟩ ⟨false, 239145062913888396062936585491024900586537751816251021651328301630723108968⟩ = true := by
  decide +kernel

theorem o_row_118 : oGrid.row evalE 118 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_118_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_118_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_118_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_118_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_118_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_118_2000).1 (bothLoop_sound b_118_2400).1))))))

theorem n_row_118 : nGrid.row evalE 118 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_118_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_118_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_118_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_118_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_118_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_118_2000).2 (bothLoop_sound b_118_2400).2))))))

theorem b_119_0 : bothSeg evalE (oGrid.idx 119) (oGrid.dm 119) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 119) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3376263493891856895221831447014925932906629853567912394048533596241915513536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_119_400 : bothSeg evalE (oGrid.idx 119) (oGrid.dm 119) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 119) oGrid.kl oGrid.kr 400 400 ⟨false, 3376263493891856895221831447014925932906629853567912394048533596241915513536⟩ ⟨false, 0⟩ ⟨false, 5453326220935351890296993661425990755139009164665415870161290160064500186278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_119_800 : bothSeg evalE (oGrid.idx 119) (oGrid.dm 119) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 119) oGrid.kl oGrid.kr 400 800 ⟨false, 5453326220935351890296993661425990755139009164665415870161290160064500186278⟩ ⟨false, 0⟩ ⟨false, 6229574750412019752990076374896041664478947059300162507196656248012063263388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_119_1200 : bothSeg evalE (oGrid.idx 119) (oGrid.dm 119) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 119) oGrid.kl oGrid.kr 400 1200 ⟨false, 6229574750412019752990076374896041664478947059300162507196656248012063263388⟩ ⟨false, 0⟩ ⟨false, 6356095748627515494632673561123278088943939020105600939677294874460671644084⟩ ⟨false, 1564359073811616337941257024561189204533623743273375722417753768469952450⟩ = true := by
  decide +kernel

theorem b_119_1600 : bothSeg evalE (oGrid.idx 119) (oGrid.dm 119) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 119) oGrid.kl oGrid.kr 400 1600 ⟨false, 6356095748627515494632673561123278088943939020105600939677294874460671644084⟩ ⟨false, 1564359073811616337941257024561189204533623743273375722417753768469952450⟩ ⟨false, 6173464970708676161548239045491174099730136322741687324408876504969355807604⟩ ⟨false, 184463754023904798165730595716786824287436283124182228124115907905625834368⟩ = true := by
  decide +kernel

theorem b_119_2000 : bothSeg evalE (oGrid.idx 119) (oGrid.dm 119) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 119) oGrid.kl oGrid.kr 400 2000 ⟨false, 6173464970708676161548239045491174099730136322741687324408876504969355807604⟩ ⟨false, 184463754023904798165730595716786824287436283124182228124115907905625834368⟩ ⟨false, 6119697932835361093544917243747062574361780789594161873218115795593966424676⟩ ⟨false, 238960877217793338151769805666348042533734071351552324876680720666248187782⟩ = true := by
  decide +kernel

theorem b_119_2400 : bothLoop evalE (oGrid.idx 119) (oGrid.dm 119) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 119) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6119697932835361093544917243747062574361780789594161873218115795593966424676⟩ ⟨false, 238960877217793338151769805666348042533734071351552324876680720666248187782⟩ = true := by
  decide +kernel

theorem o_row_119 : oGrid.row evalE 119 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_119_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_119_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_119_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_119_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_119_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_119_2000).1 (bothLoop_sound b_119_2400).1))))))

theorem n_row_119 : nGrid.row evalE 119 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_119_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_119_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_119_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_119_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_119_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_119_2000).2 (bothLoop_sound b_119_2400).2))))))

theorem o_blk_96 : allFrom (fun j => oGrid.row evalE j) 96 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 96) o_row_96 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 97) o_row_97 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 98) o_row_98 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 99) o_row_99 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 100) o_row_100 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 101) o_row_101 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 102) o_row_102 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 103) o_row_103 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 104) o_row_104 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 105) o_row_105 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 106) o_row_106 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 107) o_row_107 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 108) o_row_108 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 109) o_row_109 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 110) o_row_110 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 111) o_row_111 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 112) o_row_112 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 113) o_row_113 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 114) o_row_114 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 115) o_row_115 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 116) o_row_116 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 117) o_row_117 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 118) o_row_118 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 119) o_row_119 (allFrom_zero (fun j => oGrid.row evalE j) 120)))))))))))))))))))))))))

theorem n_blk_96 : allFrom (fun j => nGrid.row evalE j) 96 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 96) n_row_96 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 97) n_row_97 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 98) n_row_98 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 99) n_row_99 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 100) n_row_100 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 101) n_row_101 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 102) n_row_102 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 103) n_row_103 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 104) n_row_104 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 105) n_row_105 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 106) n_row_106 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 107) n_row_107 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 108) n_row_108 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 109) n_row_109 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 110) n_row_110 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 111) n_row_111 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 112) n_row_112 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 113) n_row_113 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 114) n_row_114 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 115) n_row_115 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 116) n_row_116 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 117) n_row_117 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 118) n_row_118 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 119) n_row_119 (allFrom_zero (fun j => nGrid.row evalE j) 120)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
