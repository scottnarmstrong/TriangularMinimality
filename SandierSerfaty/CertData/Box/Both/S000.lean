/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 0 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `0`–`23`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_0_0 : bothSeg evalE (oGrid.idx 0) (oGrid.dm 0) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 0) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5166672124925407542137365806751774355434277138302963309652216485304600977872⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_0_400 : bothSeg evalE (oGrid.idx 0) (oGrid.dm 0) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 0) oGrid.kl oGrid.kr 400 400 ⟨false, 5166672124925407542137365806751774355434277138302963309652216485304600977872⟩ ⟨false, 0⟩ ⟨false, 8289966313714565803220728766613301468051288494192291952102046702612615175780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_0_800 : bothSeg evalE (oGrid.idx 0) (oGrid.dm 0) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 0) oGrid.kl oGrid.kr 400 800 ⟨false, 8289966313714565803220728766613301468051288494192291952102046702612615175780⟩ ⟨false, 0⟩ ⟨false, 9468521332661022518879043296037608349134567008744155509773757132909151675862⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_0_1200 : bothSeg evalE (oGrid.idx 0) (oGrid.dm 0) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 0) oGrid.kl oGrid.kr 400 1200 ⟨false, 9468521332661022518879043296037608349134567008744155509773757132909151675862⟩ ⟨false, 0⟩ ⟨false, 9704990149245256542566017578340330634456023077618510434491620938570962991966⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_0_1600 : bothSeg evalE (oGrid.idx 0) (oGrid.dm 0) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 0) oGrid.kl oGrid.kr 400 1600 ⟨false, 9704990149245256542566017578340330634456023077618510434491620938570962991966⟩ ⟨false, 0⟩ ⟨false, 9550592835067294563075070099746275331652405756820164644481628617451049127366⟩ ⟨false, 158054820816995875322415033254708475649919405855648810576120519037800775782⟩ = true := by
  decide +kernel

theorem b_0_2000 : bothSeg evalE (oGrid.idx 0) (oGrid.dm 0) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 0) oGrid.kl oGrid.kr 400 2000 ⟨false, 9550592835067294563075070099746275331652405756820164644481628617451049127366⟩ ⟨false, 158054820816995875322415033254708475649919405855648810576120519037800775782⟩ ⟨false, 9442755155887732529674921372729469873712067482905869106711953286500410904962⟩ ⟨false, 266159521362403781498654975717037004139118608240268059577417703986704274866⟩ = true := by
  decide +kernel

theorem b_0_2400 : bothLoop evalE (oGrid.idx 0) (oGrid.dm 0) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 0) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9442755155887732529674921372729469873712067482905869106711953286500410904962⟩ ⟨false, 266159521362403781498654975717037004139118608240268059577417703986704274866⟩ = true := by
  decide +kernel

theorem o_row_0 : oGrid.row evalE 0 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_0_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_0_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_0_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_0_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_0_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_0_2000).1 (bothLoop_sound b_0_2400).1))))))

theorem n_row_0 : nGrid.row evalE 0 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_0_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_0_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_0_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_0_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_0_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_0_2000).2 (bothLoop_sound b_0_2400).2))))))

theorem b_1_0 : bothSeg evalE (oGrid.idx 1) (oGrid.dm 1) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5148871775945089286863679395217577172718651445736835489605677270713850690060⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1_400 : bothSeg evalE (oGrid.idx 1) (oGrid.dm 1) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1) oGrid.kl oGrid.kr 400 400 ⟨false, 5148871775945089286863679395217577172718651445736835489605677270713850690060⟩ ⟨false, 0⟩ ⟨false, 8262076137798608257740300886727440371134598310447541676990569259557557887782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1_800 : bothSeg evalE (oGrid.idx 1) (oGrid.dm 1) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1) oGrid.kl oGrid.kr 400 800 ⟨false, 8262076137798608257740300886727440371134598310447541676990569259557557887782⟩ ⟨false, 0⟩ ⟨false, 9436882466183431230589496527731883022089233933625106308573880225240631792630⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1_1200 : bothSeg evalE (oGrid.idx 1) (oGrid.dm 1) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1) oGrid.kl oGrid.kr 400 1200 ⟨false, 9436882466183431230589496527731883022089233933625106308573880225240631792630⟩ ⟨false, 0⟩ ⟨false, 9672346341526236242191079803734650209780387493138663049509241292714982159706⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1_1600 : bothSeg evalE (oGrid.idx 1) (oGrid.dm 1) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1) oGrid.kl oGrid.kr 400 1600 ⟨false, 9672346341526236242191079803734650209780387493138663049509241292714982159706⟩ ⟨false, 0⟩ ⟨false, 9517558688002344951913297714554229074988160281216117302632836488286601053290⟩ ⟨false, 158377450281843775830738772122803221744225284281451966822895609912909143126⟩ = true := by
  decide +kernel

theorem b_1_2000 : bothSeg evalE (oGrid.idx 1) (oGrid.dm 1) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1) oGrid.kl oGrid.kr 400 2000 ⟨false, 9517558688002344951913297714554229074988160281216117302632836488286601053290⟩ ⟨false, 158377450281843775830738772122803221744225284281451966822895609912909143126⟩ ⟨false, 9410310891125538901188457359763991291174136369028394821679072453778545305126⟩ ⟨false, 265899906684834721263341630614962622375004736693665436982941041722617688320⟩ = true := by
  decide +kernel

theorem b_1_2400 : bothLoop evalE (oGrid.idx 1) (oGrid.dm 1) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9410310891125538901188457359763991291174136369028394821679072453778545305126⟩ ⟨false, 265899906684834721263341630614962622375004736693665436982941041722617688320⟩ = true := by
  decide +kernel

theorem o_row_1 : oGrid.row evalE 1 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1_2000).1 (bothLoop_sound b_1_2400).1))))))

theorem n_row_1 : nGrid.row evalE 1 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1_2000).2 (bothLoop_sound b_1_2400).2))))))

theorem b_2_0 : bothSeg evalE (oGrid.idx 2) (oGrid.dm 2) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 2) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5131123261968978199255492034800709355516469483116006832543870252310308331534⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_2_400 : bothSeg evalE (oGrid.idx 2) (oGrid.dm 2) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 2) oGrid.kl oGrid.kr 400 400 ⟨false, 5131123261968978199255492034800709355516469483116006832543870252310308331534⟩ ⟨false, 0⟩ ⟨false, 8234261170394224204230965160561644048897346987941745002663242005071971901496⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_2_800 : bothSeg evalE (oGrid.idx 2) (oGrid.dm 2) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 2) oGrid.kl oGrid.kr 400 800 ⟨false, 8234261170394224204230965160561644048897346987941745002663242005071971901496⟩ ⟨false, 0⟩ ⟨false, 9405324846031036853331739022043840201851649026517910236163819026497120804858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_2_1200 : bothSeg evalE (oGrid.idx 2) (oGrid.dm 2) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 2) oGrid.kl oGrid.kr 400 1200 ⟨false, 9405324846031036853331739022043840201851649026517910236163819026497120804858⟩ ⟨false, 0⟩ ⟨false, 9639785219701560654278983483880660732676878722281663914577054537105575549584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_2_1600 : bothSeg evalE (oGrid.idx 2) (oGrid.dm 2) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 2) oGrid.kl oGrid.kr 400 1600 ⟨false, 9639785219701560654278983483880660732676878722281663914577054537105575549584⟩ ⟨false, 0⟩ ⟨false, 9484609809730166624736684761653932338364655985952183287429637800102731784964⟩ ⟨false, 158697771222213425311523816542979000021486478228106119580173455152659529880⟩ = true := by
  decide +kernel

theorem b_2_2000 : bothSeg evalE (oGrid.idx 2) (oGrid.dm 2) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 2) oGrid.kl oGrid.kr 400 2000 ⟨false, 9484609809730166624736684761653932338364655985952183287429637800102731784964⟩ ⟨false, 158697771222213425311523816542979000021486478228106119580173455152659529880⟩ ⟨false, 9377949582693830687466573703238491598927627055087039032717409062049707822236⟩ ⟨false, 265640285097072498389249851530843662579353911910680651911242446141746375086⟩ = true := by
  decide +kernel

theorem b_2_2400 : bothLoop evalE (oGrid.idx 2) (oGrid.dm 2) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 2) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9377949582693830687466573703238491598927627055087039032717409062049707822236⟩ ⟨false, 265640285097072498389249851530843662579353911910680651911242446141746375086⟩ = true := by
  decide +kernel

theorem o_row_2 : oGrid.row evalE 2 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_2_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_2_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_2_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_2_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_2_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_2_2000).1 (bothLoop_sound b_2_2400).1))))))

theorem n_row_2 : nGrid.row evalE 2 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_2_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_2_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_2_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_2_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_2_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_2_2000).2 (bothLoop_sound b_2_2400).2))))))

theorem b_3_0 : bothSeg evalE (oGrid.idx 3) (oGrid.dm 3) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 3) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5113426408100330414966757509483132460441916475002451928155972404229908355294⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_3_400 : bothSeg evalE (oGrid.idx 3) (oGrid.dm 3) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 3) oGrid.kl oGrid.kr 400 400 ⟨false, 5113426408100330414966757509483132460441916475002451928155972404229908355294⟩ ⟨false, 0⟩ ⟨false, 8206521044333332592430046273065760922322009599551703273735754587450481500860⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_3_800 : bothSeg evalE (oGrid.idx 3) (oGrid.dm 3) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 3) oGrid.kl oGrid.kr 400 800 ⟨false, 8206521044333332592430046273065760922322009599551703273735754587450481500860⟩ ⟨false, 0⟩ ⟨false, 9373848114211070813654658302738138949050687759150386789600940829041855880988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_3_1200 : bothSeg evalE (oGrid.idx 3) (oGrid.dm 3) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 3) oGrid.kl oGrid.kr 400 1200 ⟨false, 9373848114211070813654658302738138949050687759150386789600940829041855880988⟩ ⟨false, 0⟩ ⟨false, 9607306448752768275722643250981833046119626520165548637805361775369027053778⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_3_1600 : bothSeg evalE (oGrid.idx 3) (oGrid.dm 3) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 3) oGrid.kl oGrid.kr 400 1600 ⟨false, 9607306448752768275722643250981833046119626520165548637805361775369027053778⟩ ⟨false, 0⟩ ⟨false, 9451745853947442197961588345410838710739323590751051028233470757466010666386⟩ ⟨false, 159016047052117671223201429103755252114550260481132322147414170624991559830⟩ = true := by
  decide +kernel

theorem b_3_2000 : bothSeg evalE (oGrid.idx 3) (oGrid.dm 3) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 3) oGrid.kl oGrid.kr 400 2000 ⟨false, 9451745853947442197961588345410838710739323590751051028233470757466010666386⟩ ⟨false, 159016047052117671223201429103755252114550260481132322147414170624991559830⟩ ⟨false, 9345670903032778979289626868666685438978803699378358570848764079584841767342⟩ ⟨false, 265381051930318824527535266062848954565494431332996039775336849219257345552⟩ = true := by
  decide +kernel

theorem b_3_2400 : bothLoop evalE (oGrid.idx 3) (oGrid.dm 3) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 3) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9345670903032778979289626868666685438978803699378358570848764079584841767342⟩ ⟨false, 265381051930318824527535266062848954565494431332996039775336849219257345552⟩ = true := by
  decide +kernel

theorem o_row_3 : oGrid.row evalE 3 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_3_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_3_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_3_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_3_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_3_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_3_2000).1 (bothLoop_sound b_3_2400).1))))))

theorem n_row_3 : nGrid.row evalE 3 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_3_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_3_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_3_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_3_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_3_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_3_2000).2 (bothLoop_sound b_3_2400).2))))))

theorem b_4_0 : bothSeg evalE (oGrid.idx 4) (oGrid.dm 4) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 4) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5095781180603939608812312398840726761531856100969079350172719015302674997066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_4_400 : bothSeg evalE (oGrid.idx 4) (oGrid.dm 4) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 4) oGrid.kl oGrid.kr 400 400 ⟨false, 5095781180603939608812312398840726761531856100969079350172719015302674997066⟩ ⟨false, 0⟩ ⟨false, 8178855733513400634395426632982930777797016534777553603067945896135618745224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_4_800 : bothSeg evalE (oGrid.idx 4) (oGrid.dm 4) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 4) oGrid.kl oGrid.kr 400 800 ⟨false, 8178855733513400634395426632982930777797016534777553603067945896135618745224⟩ ⟨false, 0⟩ ⟨false, 9342452245376011704011137344208006537311334754330331688406239753399719744364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_4_1200 : bothSeg evalE (oGrid.idx 4) (oGrid.dm 4) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 4) oGrid.kl oGrid.kr 400 1200 ⟨false, 9342452245376011704011137344208006537311334754330331688406239753399719744364⟩ ⟨false, 0⟩ ⟨false, 9574909987590050372713373812380669142023383046187660728522360063031852187866⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_4_1600 : bothSeg evalE (oGrid.idx 4) (oGrid.dm 4) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 4) oGrid.kl oGrid.kr 400 1600 ⟨false, 9574909987590050372713373812380669142023383046187660728522360063031852187866⟩ ⟨false, 0⟩ ⟨false, 9418966675963848556718514169183769379788324293677143155784219962066014824756⟩ ⟨false, 159332865237969652772174517672937945323789088360700496114478672445467717040⟩ = true := by
  decide +kernel

theorem b_4_2000 : bothSeg evalE (oGrid.idx 4) (oGrid.dm 4) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 4) oGrid.kl oGrid.kr 400 2000 ⟨false, 9418966675963848556718514169183769379788324293677143155784219962066014824756⟩ ⟨false, 159332865237969652772174517672937945323789088360700496114478672445467717040⟩ ⟨false, 9313474727022800175035733649493189747958986516717436148294017801779180883798⟩ ⟨false, 265122642972247521524786623388943255884905421269377492757767451328478702718⟩ = true := by
  decide +kernel

theorem b_4_2400 : bothLoop evalE (oGrid.idx 4) (oGrid.dm 4) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 4) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9313474727022800175035733649493189747958986516717436148294017801779180883798⟩ ⟨false, 265122642972247521524786623388943255884905421269377492757767451328478702718⟩ = true := by
  decide +kernel

theorem o_row_4 : oGrid.row evalE 4 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_4_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_4_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_4_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_4_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_4_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_4_2000).1 (bothLoop_sound b_4_2400).1))))))

theorem n_row_4 : nGrid.row evalE 4 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_4_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_4_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_4_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_4_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_4_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_4_2000).2 (bothLoop_sound b_4_2400).2))))))

theorem b_5_0 : bothSeg evalE (oGrid.idx 5) (oGrid.dm 5) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 5) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5078187444889728238299576770754418816413263040625071810402646367372526298754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_5_400 : bothSeg evalE (oGrid.idx 5) (oGrid.dm 5) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 5) oGrid.kl oGrid.kr 400 400 ⟨false, 5078187444889728238299576770754418816413263040625071810402646367372526298754⟩ ⟨false, 0⟩ ⟨false, 8151265001694005879462640893731454084349171607185000163901196806295501270682⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_5_800 : bothSeg evalE (oGrid.idx 5) (oGrid.dm 5) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 5) oGrid.kl oGrid.kr 400 800 ⟨false, 8151265001694005879462640893731454084349171607185000163901196806295501270682⟩ ⟨false, 0⟩ ⟨false, 9311136994579700727831645237885614354880523431436243663175690023006161636070⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_5_1200 : bothSeg evalE (oGrid.idx 5) (oGrid.dm 5) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 5) oGrid.kl oGrid.kr 400 1200 ⟨false, 9311136994579700727831645237885614354880523431436243663175690023006161636070⟩ ⟨false, 0⟩ ⟨false, 9542595616065027335854058242438029608176602979232120208509254610011456207618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_5_1600 : bothSeg evalE (oGrid.idx 5) (oGrid.dm 5) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 5) oGrid.kl oGrid.kr 400 1600 ⟨false, 9542595616065027335854058242438029608176602979232120208509254610011456207618⟩ ⟨false, 0⟩ ⟨false, 9386272140217066053041079318075167415163777409591707607533543129973257244862⟩ ⟨false, 159647674112778310492512924006402900850781671971362823939061353160580896938⟩ = true := by
  decide +kernel

theorem b_5_2000 : bothSeg evalE (oGrid.idx 5) (oGrid.dm 5) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 5) oGrid.kl oGrid.kr 400 2000 ⟨false, 9386272140217066053041079318075167415163777409591707607533543129973257244862⟩ ⟨false, 159647674112778310492512924006402900850781671971362823939061353160580896938⟩ ⟨false, 9281360829584266975514451308890083534717969892217664245717065272109874329378⟩ ⟨false, 264864693009487668005152779662485246946491403459170499555128491356697494112⟩ = true := by
  decide +kernel

theorem b_5_2400 : bothLoop evalE (oGrid.idx 5) (oGrid.dm 5) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 5) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9281360829584266975514451308890083534717969892217664245717065272109874329378⟩ ⟨false, 264864693009487668005152779662485246946491403459170499555128491356697494112⟩ = true := by
  decide +kernel

theorem o_row_5 : oGrid.row evalE 5 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_5_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_5_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_5_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_5_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_5_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_5_2000).1 (bothLoop_sound b_5_2400).1))))))

theorem n_row_5 : nGrid.row evalE 5 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_5_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_5_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_5_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_5_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_5_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_5_2000).2 (bothLoop_sound b_5_2400).2))))))

theorem b_6_0 : bothSeg evalE (oGrid.idx 6) (oGrid.dm 6) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 6) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5060644965597995644288935236301287943321422115269900767670275419256298070520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_6_400 : bothSeg evalE (oGrid.idx 6) (oGrid.dm 6) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 6) oGrid.kl oGrid.kr 400 400 ⟨false, 5060644965597995644288935236301287943321422115269900767670275419256298070520⟩ ⟨false, 0⟩ ⟨false, 8123748762757352211559035844111036115852096531936058301418300212090973660580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_6_800 : bothSeg evalE (oGrid.idx 6) (oGrid.dm 6) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 6) oGrid.kl oGrid.kr 400 800 ⟨false, 8123748762757352211559035844111036115852096531936058301418300212090973660580⟩ ⟨false, 0⟩ ⟨false, 9279902317371248524730257325080019376091597927010808396958006939620888384496⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_6_1200 : bothSeg evalE (oGrid.idx 6) (oGrid.dm 6) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 6) oGrid.kl oGrid.kr 400 1200 ⟨false, 9279902317371248524730257325080019376091597927010808396958006939620888384496⟩ ⟨false, 0⟩ ⟨false, 9510363287569401803963615126365245487903126387327528164611630722559984276320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_6_1600 : bothSeg evalE (oGrid.idx 6) (oGrid.dm 6) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 6) oGrid.kl oGrid.kr 400 1600 ⟨false, 9510363287569401803963615126365245487903126387327528164611630722559984276320⟩ ⟨false, 0⟩ ⟨false, 9353662091089857427390846765916436690908189302375226010613958755853356074082⟩ ⟨false, 159960820033684944420505819689499533664598136822051728798338347900838713610⟩ = true := by
  decide +kernel

theorem b_6_2000 : bothSeg evalE (oGrid.idx 6) (oGrid.dm 6) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 6) oGrid.kl oGrid.kr 400 2000 ⟨false, 9353662091089857427390846765916436690908189302375226010613958755853356074082⟩ ⟨false, 159960820033684944420505819689499533664598136822051728798338347900838713610⟩ ⟨false, 9249329148163829185790896122978143378659017392287555090913791623570392541734⟩ ⟨false, 264607377778473698753976208163101371289171947876059778424719836312005859310⟩ = true := by
  decide +kernel

theorem b_6_2400 : bothLoop evalE (oGrid.idx 6) (oGrid.dm 6) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 6) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9249329148163829185790896122978143378659017392287555090913791623570392541734⟩ ⟨false, 264607377778473698753976208163101371289171947876059778424719836312005859310⟩ = true := by
  decide +kernel

theorem o_row_6 : oGrid.row evalE 6 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_6_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_6_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_6_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_6_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_6_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_6_2000).1 (bothLoop_sound b_6_2400).1))))))

theorem n_row_6 : nGrid.row evalE 6 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_6_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_6_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_6_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_6_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_6_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_6_2000).2 (bothLoop_sound b_6_2400).2))))))

theorem b_7_0 : bothSeg evalE (oGrid.idx 7) (oGrid.dm 7) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 7) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5043153695041950907014032688165054818581005235617000717235392720828050350840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_7_400 : bothSeg evalE (oGrid.idx 7) (oGrid.dm 7) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 7) oGrid.kl oGrid.kr 400 400 ⟨false, 5043153695041950907014032688165054818581005235617000717235392720828050350840⟩ ⟨false, 0⟩ ⟨false, 8096306799948425552654449787861679269944828270527201435393549697782465778546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_7_800 : bothSeg evalE (oGrid.idx 7) (oGrid.dm 7) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 7) oGrid.kl oGrid.kr 400 800 ⟨false, 8096306799948425552654449787861679269944828270527201435393549697782465778546⟩ ⟨false, 0⟩ ⟨false, 9248747972451425746367624989211086522568110801044500639897453955556385090850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_7_1200 : bothSeg evalE (oGrid.idx 7) (oGrid.dm 7) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 7) oGrid.kl oGrid.kr 400 1200 ⟨false, 9248747972451425746367624989211086522568110801044500639897453955556385090850⟩ ⟨false, 0⟩ ⟨false, 9478212759297934297939254239008170605192909203535085247651829818329386823190⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_7_1600 : bothSeg evalE (oGrid.idx 7) (oGrid.dm 7) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 7) oGrid.kl oGrid.kr 400 1600 ⟨false, 9478212759297934297939254239008170605192909203535085247651829818329386823190⟩ ⟨false, 0⟩ ⟨false, 9321136593678282051659572838528119968109204545130835455335170659081561276104⟩ ⟨false, 160271354645645524802376941750901044861654905412800403648871966470357509518⟩ = true := by
  decide +kernel

theorem b_7_2000 : bothSeg evalE (oGrid.idx 7) (oGrid.dm 7) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 7) oGrid.kl oGrid.kr 400 2000 ⟨false, 9321136593678282051659572838528119968109204545130835455335170659081561276104⟩ ⟨false, 160271354645645524802376941750901044861654905412800403648871966470357509518⟩ ⟨false, 9217379738483317221717005326496743721033612817735447479212652658359775073368⟩ ⟨false, 264349791870972585773945804987544063550981702804353081883104532703850180480⟩ = true := by
  decide +kernel

theorem b_7_2400 : bothLoop evalE (oGrid.idx 7) (oGrid.dm 7) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 7) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9217379738483317221717005326496743721033612817735447479212652658359775073368⟩ ⟨false, 264349791870972585773945804987544063550981702804353081883104532703850180480⟩ = true := by
  decide +kernel

theorem o_row_7 : oGrid.row evalE 7 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_7_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_7_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_7_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_7_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_7_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_7_2000).1 (bothLoop_sound b_7_2400).1))))))

theorem n_row_7 : nGrid.row evalE 7 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_7_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_7_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_7_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_7_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_7_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_7_2000).2 (bothLoop_sound b_7_2400).2))))))

theorem b_8_0 : bothSeg evalE (oGrid.idx 8) (oGrid.dm 8) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 8) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5025713409069440705249075620598056268176571992643126694186701840299136357438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_8_400 : bothSeg evalE (oGrid.idx 8) (oGrid.dm 8) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 8) oGrid.kl oGrid.kr 400 400 ⟨false, 5025713409069440705249075620598056268176571992643126694186701840299136357438⟩ ⟨false, 0⟩ ⟨false, 8068938860793957931543163121768969174602267938608817415256800847725565936734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_8_800 : bothSeg evalE (oGrid.idx 8) (oGrid.dm 8) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 8) oGrid.kl oGrid.kr 400 800 ⟨false, 8068938860793957931543163121768969174602267938608817415256800847725565936734⟩ ⟨false, 0⟩ ⟨false, 9217673737301784364587078910791675786396779645643179721460682697275367994748⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_8_1200 : bothSeg evalE (oGrid.idx 8) (oGrid.dm 8) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 8) oGrid.kl oGrid.kr 400 1200 ⟨false, 9217673737301784364587078910791675786396779645643179721460682697275367994748⟩ ⟨false, 0⟩ ⟨false, 9446143819162270011963903515554174194358152916645490894690363404949002600580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_8_1600 : bothSeg evalE (oGrid.idx 8) (oGrid.dm 8) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 8) oGrid.kl oGrid.kr 400 1600 ⟨false, 9446143819162270011963903515554174194358152916645490894690363404949002600580⟩ ⟨false, 0⟩ ⟨false, 9288695229392283712127362949167669965897147527429527964055807871310360267516⟩ ⟨false, 160580038169933047920168791804655624174828430178538742463167601037334311218⟩ = true := by
  decide +kernel

theorem b_8_2000 : bothSeg evalE (oGrid.idx 8) (oGrid.dm 8) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 8) oGrid.kl oGrid.kr 400 2000 ⟨false, 9288695229392283712127362949167669965897147527429527964055807871310360267516⟩ ⟨false, 160580038169933047920168791804655624174828430178538742463167601037334311218⟩ ⟨false, 9185512187505221535654078268101530690304685938892657033190920757649062949790⟩ ⟨false, 264092687464907073272287445267973179332034222831010357048865273538979245054⟩ = true := by
  decide +kernel

theorem b_8_2400 : bothLoop evalE (oGrid.idx 8) (oGrid.dm 8) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 8) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9185512187505221535654078268101530690304685938892657033190920757649062949790⟩ ⟨false, 264092687464907073272287445267973179332034222831010357048865273538979245054⟩ = true := by
  decide +kernel

theorem o_row_8 : oGrid.row evalE 8 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_8_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_8_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_8_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_8_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_8_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_8_2000).1 (bothLoop_sound b_8_2400).1))))))

theorem n_row_8 : nGrid.row evalE 8 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_8_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_8_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_8_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_8_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_8_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_8_2000).2 (bothLoop_sound b_8_2400).2))))))

theorem b_9_0 : bothSeg evalE (oGrid.idx 9) (oGrid.dm 9) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 9) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 5008324047382450914539641802155229179371896000315411642015514513414135819638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_9_400 : bothSeg evalE (oGrid.idx 9) (oGrid.dm 9) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 9) oGrid.kl oGrid.kr 400 400 ⟨false, 5008324047382450914539641802155229179371896000315411642015514513414135819638⟩ ⟨false, 0⟩ ⟨false, 8041644899948489476891992887180472799348903237106869826648128746738490417604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_9_800 : bothSeg evalE (oGrid.idx 9) (oGrid.dm 9) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 9) oGrid.kl oGrid.kr 400 800 ⟨false, 8041644899948489476891992887180472799348903237106869826648128746738490417604⟩ ⟨false, 0⟩ ⟨false, 9186679559054201806930653976170300312974714871027632768203618323201222806316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_9_1200 : bothSeg evalE (oGrid.idx 9) (oGrid.dm 9) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 9) oGrid.kl oGrid.kr 400 1200 ⟨false, 9186679559054201806930653976170300312974714871027632768203618323201222806316⟩ ⟨false, 0⟩ ⟨false, 9414156419180084129145649255370180407432063167589574661660553199222908609664⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_9_1600 : bothSeg evalE (oGrid.idx 9) (oGrid.dm 9) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 9) oGrid.kl oGrid.kr 400 1600 ⟨false, 9414156419180084129145649255370180407432063167589574661660553199222908609664⟩ ⟨false, 0⟩ ⟨false, 9256337911542212916981175668415857667400042528630932815258163923823942125076⟩ ⟨false, 160887693888168154807147857639013475535491773377477922600857096069201632384⟩ = true := by
  decide +kernel

theorem b_9_2000 : bothSeg evalE (oGrid.idx 9) (oGrid.dm 9) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 9) oGrid.kl oGrid.kr 400 2000 ⟨false, 9256337911542212916981175668415857667400042528630932815258163923823942125076⟩ ⟨false, 160887693888168154807147857639013475535491773377477922600857096069201632384⟩ ⟨false, 9153726394107351147208650425658037202870813826372264333901294834818181132596⟩ ⟨false, 263836856400439806579712036708110069714266567469710124747494088566877463410⟩ = true := by
  decide +kernel

theorem b_9_2400 : bothLoop evalE (oGrid.idx 9) (oGrid.dm 9) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 9) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9153726394107351147208650425658037202870813826372264333901294834818181132596⟩ ⟨false, 263836856400439806579712036708110069714266567469710124747494088566877463410⟩ = true := by
  decide +kernel

theorem o_row_9 : oGrid.row evalE 9 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_9_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_9_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_9_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_9_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_9_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_9_2000).1 (bothLoop_sound b_9_2400).1))))))

theorem n_row_9 : nGrid.row evalE 9 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_9_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_9_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_9_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_9_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_9_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_9_2000).2 (bothLoop_sound b_9_2400).2))))))

theorem b_10_0 : bothSeg evalE (oGrid.idx 10) (oGrid.dm 10) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 10) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4990985337897809120212749268421554094132928037095676461045140281746869847596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_10_400 : bothSeg evalE (oGrid.idx 10) (oGrid.dm 10) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 10) oGrid.kl oGrid.kr 400 400 ⟨false, 4990985337897809120212749268421554094132928037095676461045140281746869847596⟩ ⟨false, 0⟩ ⟨false, 8014424591504530146153175928910472451739513909936011862125737233382896840968⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_10_800 : bothSeg evalE (oGrid.idx 10) (oGrid.dm 10) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 10) oGrid.kl oGrid.kr 400 800 ⟨false, 8014424591504530146153175928910472451739513909936011862125737233382896840968⟩ ⟨false, 0⟩ ⟨false, 9155765121900039777942358587711768762389856493469372768098631902945810610214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_10_1200 : bothSeg evalE (oGrid.idx 10) (oGrid.dm 10) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 10) oGrid.kl oGrid.kr 400 1200 ⟨false, 9155765121900039777942358587711768762389856493469372768098631902945810610214⟩ ⟨false, 0⟩ ⟨false, 9382250242521295746133634408850655664622799239060296982906485043848639920244⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_10_1600 : bothSeg evalE (oGrid.idx 10) (oGrid.dm 10) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 10) oGrid.kl oGrid.kr 400 1600 ⟨false, 9382250242521295746133634408850655664622799239060296982906485043848639920244⟩ ⟨false, 0⟩ ⟨false, 9224064404286257853218328446768622361073271614660489168599430062603122635048⟩ ⟨false, 161192485951009291927092365129247320964612592720171723529730613696618732858⟩ = true := by
  decide +kernel

theorem b_10_2000 : bothSeg evalE (oGrid.idx 10) (oGrid.dm 10) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 10) oGrid.kl oGrid.kr 400 2000 ⟨false, 9224064404286257853218328446768622361073271614660489168599430062603122635048⟩ ⟨false, 161192485951009291927092365129247320964612592720171723529730613696618732858⟩ ⟨false, 9122022137723878766925646656783034322416733413786181978339058653779835686560⟩ ⟨false, 263580514578403664552903484691611124453292689737753160917335027094088405308⟩ = true := by
  decide +kernel

theorem b_10_2400 : bothLoop evalE (oGrid.idx 10) (oGrid.dm 10) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 10) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9122022137723878766925646656783034322416733413786181978339058653779835686560⟩ ⟨false, 263580514578403664552903484691611124453292689737753160917335027094088405308⟩ = true := by
  decide +kernel

theorem o_row_10 : oGrid.row evalE 10 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_10_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_10_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_10_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_10_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_10_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_10_2000).1 (bothLoop_sound b_10_2400).1))))))

theorem n_row_10 : nGrid.row evalE 10 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_10_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_10_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_10_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_10_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_10_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_10_2000).2 (bothLoop_sound b_10_2400).2))))))

theorem b_11_0 : bothSeg evalE (oGrid.idx 11) (oGrid.dm 11) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 11) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4973697257197534113040520856485103978898749445939567180177766570825081883808⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_11_400 : bothSeg evalE (oGrid.idx 11) (oGrid.dm 11) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 11) oGrid.kl oGrid.kr 400 400 ⟨false, 4973697257197534113040520856485103978898749445939567180177766570825081883808⟩ ⟨false, 0⟩ ⟨false, 7987277876670038413268149687463810540547454360199418175166940149710732244396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_11_800 : bothSeg evalE (oGrid.idx 11) (oGrid.dm 11) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 11) oGrid.kl oGrid.kr 400 800 ⟨false, 7987277876670038413268149687463810540547454360199418175166940149710732244396⟩ ⟨false, 0⟩ ⟨false, 9124930373913222495739752022128991285478523132415258157620663538707088074796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_11_1200 : bothSeg evalE (oGrid.idx 11) (oGrid.dm 11) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 11) oGrid.kl oGrid.kr 400 1200 ⟨false, 9124930373913222495739752022128991285478523132415258157620663538707088074796⟩ ⟨false, 0⟩ ⟨false, 9350425257210690221716990826487426822379733690812105503369535775558263042730⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_11_1600 : bothSeg evalE (oGrid.idx 11) (oGrid.dm 11) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 11) oGrid.kl oGrid.kr 400 1600 ⟨false, 9350425257210690221716990826487426822379733690812105503369535775558263042730⟩ ⟨false, 0⟩ ⟨false, 9191874600625739298410594143292416021638045859053418704321662788332589221694⟩ ⟨false, 161495625996800987230715183615009984786311541121570006890798176020099459900⟩ = true := by
  decide +kernel

theorem b_11_2000 : bothSeg evalE (oGrid.idx 11) (oGrid.dm 11) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 11) oGrid.kl oGrid.kr 400 2000 ⟨false, 9191874600625739298410594143292416021638045859053418704321662788332589221694⟩ ⟨false, 161495625996800987230715183615009984786311541121570006890798176020099459900⟩ ⟨false, 9090399261955753094417445639877670826216122043557725540810237634303287728912⟩ ⟨false, 263324817991536385897127386068752941908409566619774239094657814340089233032⟩ = true := by
  decide +kernel

theorem b_11_2400 : bothLoop evalE (oGrid.idx 11) (oGrid.dm 11) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 11) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9090399261955753094417445639877670826216122043557725540810237634303287728912⟩ ⟨false, 263324817991536385897127386068752941908409566619774239094657814340089233032⟩ = true := by
  decide +kernel

theorem o_row_11 : oGrid.row evalE 11 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_11_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_11_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_11_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_11_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_11_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_11_2000).1 (bothLoop_sound b_11_2400).1))))))

theorem n_row_11 : nGrid.row evalE 11 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_11_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_11_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_11_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_11_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_11_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_11_2000).2 (bothLoop_sound b_11_2400).2))))))

theorem b_12_0 : bothSeg evalE (oGrid.idx 12) (oGrid.dm 12) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 12) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4956459690842413044637502015961002737275685716487156973816154557179812126886⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_12_400 : bothSeg evalE (oGrid.idx 12) (oGrid.dm 12) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 12) oGrid.kl oGrid.kr 400 400 ⟨false, 4956459690842413044637502015961002737275685716487156973816154557179812126886⟩ ⟨false, 0⟩ ⟨false, 7960204619494389897095069712440599917627318681619679021281204317448395279786⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_12_800 : bothSeg evalE (oGrid.idx 12) (oGrid.dm 12) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 12) oGrid.kl oGrid.kr 400 800 ⟨false, 7960204619494389897095069712440599917627318681619679021281204317448395279786⟩ ⟨false, 0⟩ ⟨false, 9094175196476733775948253586056997249183951785040619314184789742232379817106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_12_1200 : bothSeg evalE (oGrid.idx 12) (oGrid.dm 12) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 12) oGrid.kl oGrid.kr 400 1200 ⟨false, 9094175196476733775948253586056997249183951785040619314184789742232379817106⟩ ⟨false, 0⟩ ⟨false, 9318681332739230907697380869977083297201200441129787424835651556302505537686⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_12_1600 : bothSeg evalE (oGrid.idx 12) (oGrid.dm 12) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 12) oGrid.kl oGrid.kr 400 1600 ⟨false, 9318681332739230907697380869977083297201200441129787424835651556302505537686⟩ ⟨false, 0⟩ ⟨false, 9159768311910409891851021688648141998705021664428798309157009742443264651948⟩ ⟨false, 161797233321952215139447458592454686320207608161389785693236122716357590228⟩ = true := by
  decide +kernel

theorem b_12_2000 : bothSeg evalE (oGrid.idx 12) (oGrid.dm 12) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 12) oGrid.kl oGrid.kr 400 2000 ⟨false, 9159768311910409891851021688648141998705021664428798309157009742443264651948⟩ ⟨false, 161797233321952215139447458592454686320207608161389785693236122716357590228⟩ ⟨false, 9058857638103909798677465152120944065935206222299444097882973130870823438834⟩ ⟨false, 263069953289025357046740964991676276186982630126273696571805267018991380354⟩ = true := by
  decide +kernel

theorem b_12_2400 : bothLoop evalE (oGrid.idx 12) (oGrid.dm 12) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 12) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9058857638103909798677465152120944065935206222299444097882973130870823438834⟩ ⟨false, 263069953289025357046740964991676276186982630126273696571805267018991380354⟩ = true := by
  decide +kernel

theorem o_row_12 : oGrid.row evalE 12 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_12_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_12_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_12_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_12_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_12_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_12_2000).1 (bothLoop_sound b_12_2400).1))))))

theorem n_row_12 : nGrid.row evalE 12 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_12_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_12_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_12_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_12_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_12_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_12_2000).2 (bothLoop_sound b_12_2400).2))))))

theorem b_13_0 : bothSeg evalE (oGrid.idx 13) (oGrid.dm 13) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 13) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4939272367928683533382239328886714503371951925607125677726149264365485667328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_13_400 : bothSeg evalE (oGrid.idx 13) (oGrid.dm 13) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 13) oGrid.kl oGrid.kr 400 400 ⟨false, 4939272367928683533382239328886714503371951925607125677726149264365485667328⟩ ⟨false, 0⟩ ⟨false, 7933204516071081462140267695934119086372460339079309824622059515411458648290⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_13_800 : bothSeg evalE (oGrid.idx 13) (oGrid.dm 13) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 13) oGrid.kl oGrid.kr 400 800 ⟨false, 7933204516071081462140267695934119086372460339079309824622059515411458648290⟩ ⟨false, 0⟩ ⟨false, 9063499269090737379421304631735938828163871882291335189541538827430493050648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_13_1200 : bothSeg evalE (oGrid.idx 13) (oGrid.dm 13) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 13) oGrid.kl oGrid.kr 400 1200 ⟨false, 9063499269090737379421304631735938828163871882291335189541538827430493050648⟩ ⟨false, 0⟩ ⟨false, 9287018167279248524495052982874543407597542903516472684103647459026638750614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_13_1600 : bothSeg evalE (oGrid.idx 13) (oGrid.dm 13) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 13) oGrid.kl oGrid.kr 400 1600 ⟨false, 9287018167279248524495052982874543407597542903516472684103647459026638750614⟩ ⟨false, 0⟩ ⟨false, 9127745169862246904398126357651128934363402378799325447443844346682480632930⟩ ⟨false, 162097117474617105755747739768854980882218458605022833714739549666567804534⟩ = true := by
  decide +kernel

theorem b_13_2000 : bothSeg evalE (oGrid.idx 13) (oGrid.dm 13) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 13) oGrid.kl oGrid.kr 400 2000 ⟨false, 9127745169862246904398126357651128934363402378799325447443844346682480632930⟩ ⟨false, 162097117474617105755747739768854980882218458605022833714739549666567804534⟩ ⟨false, 9027396892337815079259269886464676449837169235333440316773347776949303842020⟩ ⟨false, 262815570094901355273258578119246241032445633941722574227075388190543890528⟩ = true := by
  decide +kernel

theorem b_13_2400 : bothLoop evalE (oGrid.idx 13) (oGrid.dm 13) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 13) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 9027396892337815079259269886464676449837169235333440316773347776949303842020⟩ ⟨false, 262815570094901355273258578119246241032445633941722574227075388190543890528⟩ = true := by
  decide +kernel

theorem o_row_13 : oGrid.row evalE 13 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_13_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_13_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_13_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_13_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_13_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_13_2000).1 (bothLoop_sound b_13_2400).1))))))

theorem n_row_13 : nGrid.row evalE 13 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_13_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_13_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_13_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_13_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_13_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_13_2000).2 (bothLoop_sound b_13_2400).2))))))

theorem b_14_0 : bothSeg evalE (oGrid.idx 14) (oGrid.dm 14) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 14) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4922135219763956670851765065012202302942194948655568700056912439384419257604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_14_400 : bothSeg evalE (oGrid.idx 14) (oGrid.dm 14) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 14) oGrid.kl oGrid.kr 400 400 ⟨false, 4922135219763956670851765065012202302942194948655568700056912439384419257604⟩ ⟨false, 0⟩ ⟨false, 7906277441592915398113450687517961184285204445513871753273097241950733692932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_14_800 : bothSeg evalE (oGrid.idx 14) (oGrid.dm 14) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 14) oGrid.kl oGrid.kr 400 800 ⟨false, 7906277441592915398113450687517961184285204445513871753273097241950733692932⟩ ⟨false, 0⟩ ⟨false, 9032902492709398231873072289929204329346756346156383296110622977199346625202⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_14_1200 : bothSeg evalE (oGrid.idx 14) (oGrid.dm 14) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 14) oGrid.kl oGrid.kr 400 1200 ⟨false, 9032902492709398231873072289929204329346756346156383296110622977199346625202⟩ ⟨false, 0⟩ ⟨false, 9255435640271479118930398437098794161244912259779162545375079338835050614596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_14_1600 : bothSeg evalE (oGrid.idx 14) (oGrid.dm 14) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 14) oGrid.kl oGrid.kr 400 1600 ⟨false, 9255435640271479118930398437098794161244912259779162545375079338835050614596⟩ ⟨false, 0⟩ ⟨false, 9095805220151593500912547708561097035918809575581324273284020147323891593582⟩ ⟨false, 162394566414551594393368799818982665239061730717879713595379548616734637598⟩ = true := by
  decide +kernel

theorem b_14_2000 : bothSeg evalE (oGrid.idx 14) (oGrid.dm 14) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 14) oGrid.kl oGrid.kr 400 2000 ⟨false, 9095805220151593500912547708561097035918809575581324273284020147323891593582⟩ ⟨false, 162394566414551594393368799818982665239061730717879713595379548616734637598⟩ ⟨false, 8996017081734203992199630715923070962010391882169706642950690048341131134924⟩ ⟨false, 262561112461748416594045620654956725566316990250213327319147229613096430542⟩ = true := by
  decide +kernel

theorem b_14_2400 : bothLoop evalE (oGrid.idx 14) (oGrid.dm 14) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 14) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8996017081734203992199630715923070962010391882169706642950690048341131134924⟩ ⟨false, 262561112461748416594045620654956725566316990250213327319147229613096430542⟩ = true := by
  decide +kernel

theorem o_row_14 : oGrid.row evalE 14 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_14_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_14_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_14_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_14_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_14_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_14_2000).1 (bothLoop_sound b_14_2400).1))))))

theorem n_row_14 : nGrid.row evalE 14 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_14_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_14_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_14_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_14_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_14_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_14_2000).2 (bothLoop_sound b_14_2400).2))))))

theorem b_15_0 : bothSeg evalE (oGrid.idx 15) (oGrid.dm 15) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 15) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4905048114945473735927273161429846686572195055752834011922102641523571541962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_15_400 : bothSeg evalE (oGrid.idx 15) (oGrid.dm 15) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 15) oGrid.kl oGrid.kr 400 400 ⟨false, 4905048114945473735927273161429846686572195055752834011922102641523571541962⟩ ⟨false, 0⟩ ⟨false, 7879423210179949558520341793635597791516663638741088221854718632829922625242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_15_800 : bothSeg evalE (oGrid.idx 15) (oGrid.dm 15) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 15) oGrid.kl oGrid.kr 400 800 ⟨false, 7879423210179949558520341793635597791516663638741088221854718632829922625242⟩ ⟨false, 0⟩ ⟨false, 9002384685022012300627427042839498783168411672094571424194002205559998994076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_15_1200 : bothSeg evalE (oGrid.idx 15) (oGrid.dm 15) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 15) oGrid.kl oGrid.kr 400 1200 ⟨false, 9002384685022012300627427042839498783168411672094571424194002205559998994076⟩ ⟨false, 0⟩ ⟨false, 9223933623022461536740115572420645909207240422425411753146954235495266858974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_15_1600 : bothSeg evalE (oGrid.idx 15) (oGrid.dm 15) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 15) oGrid.kl oGrid.kr 400 1600 ⟨false, 9223933623022461536740115572420645909207240422425411753146954235495266858974⟩ ⟨false, 0⟩ ⟨false, 9063948404836294713377558742782461158764657905626128814517730340651700158540⟩ ⟨false, 162690600561305752909114480181823720618192334931668483209946819729505865322⟩ = true := by
  decide +kernel

theorem b_15_2000 : bothSeg evalE (oGrid.idx 15) (oGrid.dm 15) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 15) oGrid.kl oGrid.kr 400 2000 ⟨false, 9063948404836294713377558742782461158764657905626128814517730340651700158540⟩ ⟨false, 162690600561305752909114480181823720618192334931668483209946819729505865322⟩ ⟨false, 8964718140998780246398813292020057992338318654576089618660785389389899895326⟩ ⟨false, 262307446874208138042011840051827665050526569002470298581381277356610431318⟩ = true := by
  decide +kernel

theorem b_15_2400 : bothLoop evalE (oGrid.idx 15) (oGrid.dm 15) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 15) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8964718140998780246398813292020057992338318654576089618660785389389899895326⟩ ⟨false, 262307446874208138042011840051827665050526569002470298581381277356610431318⟩ = true := by
  decide +kernel

theorem o_row_15 : oGrid.row evalE 15 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_15_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_15_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_15_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_15_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_15_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_15_2000).1 (bothLoop_sound b_15_2400).1))))))

theorem n_row_15 : nGrid.row evalE 15 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_15_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_15_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_15_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_15_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_15_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_15_2000).2 (bothLoop_sound b_15_2400).2))))))

theorem b_16_0 : bothSeg evalE (oGrid.idx 16) (oGrid.dm 16) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 16) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4888010866871844503992452880006616528594942164549481547355649616448771335494⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_16_400 : bothSeg evalE (oGrid.idx 16) (oGrid.dm 16) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 16) oGrid.kl oGrid.kr 400 400 ⟨false, 4888010866871844503992452880006616528594942164549481547355649616448771335494⟩ ⟨false, 0⟩ ⟨false, 7852641791385439587619041107187627095739369473924284992971650504206665592780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_16_800 : bothSeg evalE (oGrid.idx 16) (oGrid.dm 16) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 16) oGrid.kl oGrid.kr 400 800 ⟨false, 7852641791385439587619041107187627095739369473924284992971650504206665592780⟩ ⟨false, 0⟩ ⟨false, 8971945803714247472055486794414262376995035034436981975920775102032682851786⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_16_1200 : bothSeg evalE (oGrid.idx 16) (oGrid.dm 16) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 16) oGrid.kl oGrid.kr 400 1200 ⟨false, 8971945803714247472055486794414262376995035034436981975920775102032682851786⟩ ⟨false, 0⟩ ⟨false, 9192512022106226426046519809083936729394733911835773820914202546316245412964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_16_1600 : bothSeg evalE (oGrid.idx 16) (oGrid.dm 16) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 16) oGrid.kl oGrid.kr 400 1600 ⟨false, 9192512022106226426046519809083936729394733911835773820914202546316245412964⟩ ⟨false, 0⟩ ⟨false, 9032174541878469899404215711853522474515024673934610773469854388369305755916⟩ ⟨false, 162984488253957771295243685457621850462546747227366829583751197721717867348⟩ = true := by
  decide +kernel

theorem b_16_2000 : bothSeg evalE (oGrid.idx 16) (oGrid.dm 16) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 16) oGrid.kl oGrid.kr 400 2000 ⟨false, 9032174541878469899404215711853522474515024673934610773469854388369305755916⟩ ⟨false, 162984488253957771295243685457621850462546747227366829583751197721717867348⟩ ⟨false, 8933499881346483380008821225111885093739470036179763650794413342219321994406⟩ ⟨false, 262053947326765993823959898890555574113008110711336508715450836939396549302⟩ = true := by
  decide +kernel

theorem b_16_2400 : bothLoop evalE (oGrid.idx 16) (oGrid.dm 16) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 16) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8933499881346483380008821225111885093739470036179763650794413342219321994406⟩ ⟨false, 262053947326765993823959898890555574113008110711336508715450836939396549302⟩ = true := by
  decide +kernel

theorem o_row_16 : oGrid.row evalE 16 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_16_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_16_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_16_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_16_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_16_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_16_2000).1 (bothLoop_sound b_16_2400).1))))))

theorem n_row_16 : nGrid.row evalE 16 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_16_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_16_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_16_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_16_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_16_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_16_2000).2 (bothLoop_sound b_16_2400).2))))))

theorem b_17_0 : bothSeg evalE (oGrid.idx 17) (oGrid.dm 17) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 17) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4871023387557672356090206516294434185026688726319475641244899645932491310108⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_17_400 : bothSeg evalE (oGrid.idx 17) (oGrid.dm 17) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 17) oGrid.kl oGrid.kr 400 400 ⟨false, 4871023387557672356090206516294434185026688726319475641244899645932491310108⟩ ⟨false, 0⟩ ⟨false, 7825932797943826121533296588764458906588725425995510695203806943609076813072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_17_800 : bothSeg evalE (oGrid.idx 17) (oGrid.dm 17) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 17) oGrid.kl oGrid.kr 400 800 ⟨false, 7825932797943826121533296588764458906588725425995510695203806943609076813072⟩ ⟨false, 0⟩ ⟨false, 8941585495453305799307688192680576608936780627910630133385489283316865793374⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_17_1200 : bothSeg evalE (oGrid.idx 17) (oGrid.dm 17) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 17) oGrid.kl oGrid.kr 400 1200 ⟨false, 8941585495453305799307688192680576608936780627910630133385489283316865793374⟩ ⟨false, 0⟩ ⟨false, 9161170524960161870211579220258022405285159500007680852658762313400869329504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_17_1600 : bothSeg evalE (oGrid.idx 17) (oGrid.dm 17) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 17) oGrid.kl oGrid.kr 400 1600 ⟨false, 9161170524960161870211579220258022405285159500007680852658762313400869329504⟩ ⟨false, 0⟩ ⟨false, 9000483203223562088256590208452438469359048382990886606804526598539164454220⟩ ⟨false, 163276348642795826837800076473867021322325957514368505467134860317312913302⟩ = true := by
  decide +kernel

theorem b_17_2000 : bothSeg evalE (oGrid.idx 17) (oGrid.dm 17) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 17) oGrid.kl oGrid.kr 400 2000 ⟨false, 9000483203223562088256590208452438469359048382990886606804526598539164454220⟩ ⟨false, 163276348642795826837800076473867021322325957514368505467134860317312913302⟩ ⟨false, 8902361822408178899783126312822406567252168571634784076273674968939476087646⟩ ⟨false, 261800721702303228480029537109063855287696204662255518370561038359083492990⟩ = true := by
  decide +kernel

theorem b_17_2400 : bothLoop evalE (oGrid.idx 17) (oGrid.dm 17) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 17) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8902361822408178899783126312822406567252168571634784076273674968939476087646⟩ ⟨false, 261800721702303228480029537109063855287696204662255518370561038359083492990⟩ = true := by
  decide +kernel

theorem o_row_17 : oGrid.row evalE 17 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_17_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_17_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_17_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_17_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_17_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_17_2000).1 (bothLoop_sound b_17_2400).1))))))

theorem n_row_17 : nGrid.row evalE 17 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_17_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_17_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_17_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_17_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_17_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_17_2000).2 (bothLoop_sound b_17_2400).2))))))

theorem b_18_0 : bothSeg evalE (oGrid.idx 18) (oGrid.dm 18) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 18) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4854085557943940841172424062506884236027088173252408231033548757415852194946⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_18_400 : bothSeg evalE (oGrid.idx 18) (oGrid.dm 18) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 18) oGrid.kl oGrid.kr 400 400 ⟨false, 4854085557943940841172424062506884236027088173252408231033548757415852194946⟩ ⟨false, 0⟩ ⟨false, 7799296184135212739751570173157390810965631698089834166780410949215850512068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_18_800 : bothSeg evalE (oGrid.idx 18) (oGrid.dm 18) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 18) oGrid.kl oGrid.kr 400 800 ⟨false, 7799296184135212739751570173157390810965631698089834166780410949215850512068⟩ ⟨false, 0⟩ ⟨false, 8911303712072554392682158295416742760487150114219859066550186745949960659114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_18_1200 : bothSeg evalE (oGrid.idx 18) (oGrid.dm 18) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 18) oGrid.kl oGrid.kr 400 1200 ⟨false, 8911303712072554392682158295416742760487150114219859066550186745949960659114⟩ ⟨false, 0⟩ ⟨false, 9129909066188284928911619817899824377808994346051671577931131795051143295832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_18_1600 : bothSeg evalE (oGrid.idx 18) (oGrid.dm 18) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 18) oGrid.kl oGrid.kr 400 1600 ⟨false, 9129909066188284928911619817899824377808994346051671577931131795051143295832⟩ ⟨false, 0⟩ ⟨false, 8968874471877913208947089131864651051132701256768847236194025632809632625042⟩ ⟨false, 163566688138681403298181354527506210379792714586351457637158057523577084102⟩ = true := by
  decide +kernel

theorem b_18_2000 : bothSeg evalE (oGrid.idx 18) (oGrid.dm 18) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 18) oGrid.kl oGrid.kr 400 2000 ⟨false, 8968874471877913208947089131864651051132701256768847236194025632809632625042⟩ ⟨false, 163566688138681403298181354527506210379792714586351457637158057523577084102⟩ ⟨false, 8871304132893222668091417212011082854224278477011872027863292760317027241298⟩ ⟨false, 261548209617251115679204367699138747889035539373002573536648586026469732670⟩ = true := by
  decide +kernel

theorem b_18_2400 : bothLoop evalE (oGrid.idx 18) (oGrid.dm 18) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 18) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8871304132893222668091417212011082854224278477011872027863292760317027241298⟩ ⟨false, 261548209617251115679204367699138747889035539373002573536648586026469732670⟩ = true := by
  decide +kernel

theorem o_row_18 : oGrid.row evalE 18 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_18_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_18_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_18_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_18_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_18_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_18_2000).1 (bothLoop_sound b_18_2400).1))))))

theorem n_row_18 : nGrid.row evalE 18 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_18_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_18_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_18_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_18_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_18_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_18_2000).2 (bothLoop_sound b_18_2400).2))))))

theorem b_19_0 : bothSeg evalE (oGrid.idx 19) (oGrid.dm 19) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 19) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4837197150308207915440765781335140311496275138551523480836157593722388938494⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_19_400 : bothSeg evalE (oGrid.idx 19) (oGrid.dm 19) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 19) oGrid.kl oGrid.kr 400 400 ⟨false, 4837197150308207915440765781335140311496275138551523480836157593722388938494⟩ ⟨false, 0⟩ ⟨false, 7772731782356789137518208021322854829405235403645006798830258420692816514744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_19_800 : bothSeg evalE (oGrid.idx 19) (oGrid.dm 19) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 19) oGrid.kl oGrid.kr 400 800 ⟨false, 7772731782356789137518208021322854829405235403645006798830258420692816514744⟩ ⟨false, 0⟩ ⟨false, 8881100278306081358968749373060033267822289945890017639743154867514537850318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_19_1200 : bothSeg evalE (oGrid.idx 19) (oGrid.dm 19) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 19) oGrid.kl oGrid.kr 400 1200 ⟨false, 8881100278306081358968749373060033267822289945890017639743154867514537850318⟩ ⟨false, 0⟩ ⟨false, 9098727493357866048036495148611838340310758149450584575764193483943877031104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_19_1600 : bothSeg evalE (oGrid.idx 19) (oGrid.dm 19) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 19) oGrid.kl oGrid.kr 400 1600 ⟨false, 9098727493357866048036495148611838340310758149450584575764193483943877031104⟩ ⟨false, 0⟩ ⟨false, 8937348049530729105756413356225996666417460311181342792535907075517898500526⟩ ⟨false, 163855504773235444091587499332774379469825622477960564501482468076584217618⟩ = true := by
  decide +kernel

theorem b_19_2000 : bothSeg evalE (oGrid.idx 19) (oGrid.dm 19) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 19) oGrid.kl oGrid.kr 400 2000 ⟨false, 8937348049530729105756413356225996666417460311181342792535907075517898500526⟩ ⟨false, 163855504773235444091587499332774379469825622477960564501482468076584217618⟩ ⟨false, 8840326497850595231338428205130681418853356215881234310056607211766644130154⟩ ⟨false, 261296417786351775089967350271673110295054804988472421396753507103352629506⟩ = true := by
  decide +kernel

theorem b_19_2400 : bothLoop evalE (oGrid.idx 19) (oGrid.dm 19) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 19) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8840326497850595231338428205130681418853356215881234310056607211766644130154⟩ ⟨false, 261296417786351775089967350271673110295054804988472421396753507103352629506⟩ = true := by
  decide +kernel

theorem o_row_19 : oGrid.row evalE 19 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_19_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_19_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_19_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_19_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_19_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_19_2000).1 (bothLoop_sound b_19_2400).1))))))

theorem n_row_19 : nGrid.row evalE 19 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_19_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_19_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_19_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_19_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_19_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_19_2000).2 (bothLoop_sound b_19_2400).2))))))

theorem b_20_0 : bothSeg evalE (oGrid.idx 20) (oGrid.dm 20) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 20) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4820358081202691096356012057846763043288773283886995008678536598359416616110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_20_400 : bothSeg evalE (oGrid.idx 20) (oGrid.dm 20) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 20) oGrid.kl oGrid.kr 400 400 ⟨false, 4820358081202691096356012057846763043288773283886995008678536598359416616110⟩ ⟨false, 0⟩ ⟨false, 7746239367284303990839977316602276011781810073731561506741637237993280658724⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_20_800 : bothSeg evalE (oGrid.idx 20) (oGrid.dm 20) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 20) oGrid.kl oGrid.kr 400 800 ⟨false, 7746239367284303990839977316602276011781810073731561506741637237993280658724⟩ ⟨false, 0⟩ ⟨false, 8850974994846642294326607863514773560959574045579883984218003337458348983336⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_20_1200 : bothSeg evalE (oGrid.idx 20) (oGrid.dm 20) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 20) oGrid.kl oGrid.kr 400 1200 ⟨false, 8850974994846642294326607863514773560959574045579883984218003337458348983336⟩ ⟨false, 0⟩ ⟨false, 9067625592151342311551629024808510282787865227141710957532802971495636246620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_20_1600 : bothSeg evalE (oGrid.idx 20) (oGrid.dm 20) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 20) oGrid.kl oGrid.kr 400 1600 ⟨false, 9067625592151342311551629024808510282787865227141710957532802971495636246620⟩ ⟨false, 0⟩ ⟨false, 8905903672540016835096860493736754072481126919202734873716344753090082882094⟩ ⟨false, 164141880250283599039578968400664718227889257064168619805621719611846625338⟩ = true := by
  decide +kernel

theorem b_20_2000 : bothSeg evalE (oGrid.idx 20) (oGrid.dm 20) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 20) oGrid.kl oGrid.kr 400 2000 ⟨false, 8905903672540016835096860493736754072481126919202734873716344753090082882094⟩ ⟨false, 164141880250283599039578968400664718227889257064168619805621719611846625338⟩ ⟨false, 8809428625267930182865525621256625968259306342549684038068611029771099447262⟩ ⟨false, 261044413048843470126443277692241034223064770020452902434567041932558808012⟩ = true := by
  decide +kernel

theorem b_20_2400 : bothLoop evalE (oGrid.idx 20) (oGrid.dm 20) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 20) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8809428625267930182865525621256625968259306342549684038068611029771099447262⟩ ⟨false, 261044413048843470126443277692241034223064770020452902434567041932558808012⟩ = true := by
  decide +kernel

theorem o_row_20 : oGrid.row evalE 20 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_20_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_20_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_20_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_20_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_20_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_20_2000).1 (bothLoop_sound b_20_2400).1))))))

theorem n_row_20 : nGrid.row evalE 20 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_20_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_20_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_20_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_20_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_20_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_20_2000).2 (bothLoop_sound b_20_2400).2))))))

theorem b_21_0 : bothSeg evalE (oGrid.idx 21) (oGrid.dm 21) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 21) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4803568165072789367819460427542336225555298634877790997767993879323128875856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_21_400 : bothSeg evalE (oGrid.idx 21) (oGrid.dm 21) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 21) oGrid.kl oGrid.kr 400 400 ⟨false, 4803568165072789367819460427542336225555298634877790997767993879323128875856⟩ ⟨false, 0⟩ ⟨false, 7719818746485556297964179814886362820144658962881107889753105772020794541402⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_21_800 : bothSeg evalE (oGrid.idx 21) (oGrid.dm 21) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 21) oGrid.kl oGrid.kr 400 800 ⟨false, 7719818746485556297964179814886362820144658962881107889753105772020794541402⟩ ⟨false, 0⟩ ⟨false, 8820927655147851675858767648760933986361692625362125704122298396598012808892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_21_1200 : bothSeg evalE (oGrid.idx 21) (oGrid.dm 21) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 21) oGrid.kl oGrid.kr 400 1200 ⟨false, 8820927655147851675858767648760933986361692625362125704122298396598012808892⟩ ⟨false, 0⟩ ⟨false, 9036603191176043926005867180593674239901104689314128111104638623211738055050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_21_1600 : bothSeg evalE (oGrid.idx 21) (oGrid.dm 21) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 21) oGrid.kl oGrid.kr 400 1600 ⟨false, 9036603191176043926005867180593674239901104689314128111104638623211738055050⟩ ⟨false, 0⟩ ⟨false, 8874541362801191554379874843721741025948986706713834558364653201371118944370⟩ ⟨false, 164425995726718823959956588701855220935350916872355755001328432037953972022⟩ = true := by
  decide +kernel

theorem b_21_2000 : bothSeg evalE (oGrid.idx 21) (oGrid.dm 21) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 21) oGrid.kl oGrid.kr 400 2000 ⟨false, 8874541362801191554379874843721741025948986706713834558364653201371118944370⟩ ⟨false, 164425995726718823959956588701855220935350916872355755001328432037953972022⟩ ⟨false, 8778610587691228398548506833840099072852071590448322800125605754714153238228⟩ ⟨false, 260792409059678147792737259687467778159756524096229631876016981891080173652⟩ = true := by
  decide +kernel

theorem b_21_2400 : bothLoop evalE (oGrid.idx 21) (oGrid.dm 21) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 21) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8778610587691228398548506833840099072852071590448322800125605754714153238228⟩ ⟨false, 260792409059678147792737259687467778159756524096229631876016981891080173652⟩ = true := by
  decide +kernel

theorem o_row_21 : oGrid.row evalE 21 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_21_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_21_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_21_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_21_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_21_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_21_2000).1 (bothLoop_sound b_21_2400).1))))))

theorem n_row_21 : nGrid.row evalE 21 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_21_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_21_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_21_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_21_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_21_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_21_2000).2 (bothLoop_sound b_21_2400).2))))))

theorem b_22_0 : bothSeg evalE (oGrid.idx 22) (oGrid.dm 22) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 22) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4786827416715174810435611060634289872196707626944375006893154845113717329560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_22_400 : bothSeg evalE (oGrid.idx 22) (oGrid.dm 22) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 22) oGrid.kl oGrid.kr 400 400 ⟨false, 4786827416715174810435611060634289872196707626944375006893154845113717329560⟩ ⟨false, 0⟩ ⟨false, 7693469954016837638818614070756432589710273526003605946139933545942634256924⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_22_800 : bothSeg evalE (oGrid.idx 22) (oGrid.dm 22) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 22) oGrid.kl oGrid.kr 400 800 ⟨false, 7693469954016837638818614070756432589710273526003605946139933545942634256924⟩ ⟨false, 0⟩ ⟨false, 8790958305183455778997946609662949703754534605862951946535732223526433244738⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_22_1200 : bothSeg evalE (oGrid.idx 22) (oGrid.dm 22) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 22) oGrid.kl oGrid.kr 400 1200 ⟨false, 8790958305183455778997946609662949703754534605862951946535732223526433244738⟩ ⟨false, 0⟩ ⟨false, 9005660306268676222391143101181248630605066830832166225685023615219918865704⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_22_1600 : bothSeg evalE (oGrid.idx 22) (oGrid.dm 22) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 22) oGrid.kl oGrid.kr 400 1600 ⟨false, 9005660306268676222391143101181248630605066830832166225685023615219918865704⟩ ⟨false, 0⟩ ⟨false, 8843260959882750105888113243687119452365671294869098392285396143810238800754⟩ ⟨false, 164709926907042947749359904385120782342936507720128881543174032244026187016⟩ = true := by
  decide +kernel

theorem b_22_2000 : bothSeg evalE (oGrid.idx 22) (oGrid.dm 22) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 22) oGrid.kl oGrid.kr 400 2000 ⟨false, 8843260959882750105888113243687119452365671294869098392285396143810238800754⟩ ⟨false, 164709926907042947749359904385120782342936507720128881543174032244026187016⟩ ⟨false, 8747872186802800684074561754471506281053403315393424902438050696077412633882⟩ ⟨false, 260542376146792535674364625665588476051989705197160177661154891300016304586⟩ = true := by
  decide +kernel

theorem b_22_2400 : bothLoop evalE (oGrid.idx 22) (oGrid.dm 22) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 22) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8747872186802800684074561754471506281053403315393424902438050696077412633882⟩ ⟨false, 260542376146792535674364625665588476051989705197160177661154891300016304586⟩ = true := by
  decide +kernel

theorem o_row_22 : oGrid.row evalE 22 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_22_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_22_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_22_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_22_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_22_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_22_2000).1 (bothLoop_sound b_22_2400).1))))))

theorem n_row_22 : nGrid.row evalE 22 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_22_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_22_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_22_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_22_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_22_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_22_2000).2 (bothLoop_sound b_22_2400).2))))))

theorem b_23_0 : bothSeg evalE (oGrid.idx 23) (oGrid.dm 23) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 23) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4770135522224077586365547860723232471071131068813939881797073516395648697842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_23_400 : bothSeg evalE (oGrid.idx 23) (oGrid.dm 23) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 23) oGrid.kl oGrid.kr 400 400 ⟨false, 4770135522224077586365547860723232471071131068813939881797073516395648697842⟩ ⟨false, 0⟩ ⟨false, 7667192527936375451346848353225127348583577867315198444550930693348554017454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_23_800 : bothSeg evalE (oGrid.idx 23) (oGrid.dm 23) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 23) oGrid.kl oGrid.kr 400 800 ⟨false, 7667192527936375451346848353225127348583577867315198444550930693348554017454⟩ ⟨false, 0⟩ ⟨false, 8761066508023495952581980251274909938942130269347929414557865499434433588620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_23_1200 : bothSeg evalE (oGrid.idx 23) (oGrid.dm 23) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 23) oGrid.kl oGrid.kr 400 1200 ⟨false, 8761066508023495952581980251274909938942130269347929414557865499434433588620⟩ ⟨false, 0⟩ ⟨false, 8974796530485204442601340621458283768254293965694835315458464469290887432432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_23_1600 : bothSeg evalE (oGrid.idx 23) (oGrid.dm 23) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 23) oGrid.kl oGrid.kr 400 1600 ⟨false, 8974796530485204442601340621458283768254293965694835315458464469290887432432⟩ ⟨false, 0⟩ ⟨false, 8812062181558388013141245313206985075559082415726409706764152865527063787384⟩ ⟨false, 164991257548583512877201223997111195374344564542437510207717133428553663186⟩ = true := by
  decide +kernel

theorem b_23_2000 : bothSeg evalE (oGrid.idx 23) (oGrid.dm 23) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 23) oGrid.kl oGrid.kr 400 2000 ⟨false, 8812062181558388013141245313206985075559082415726409706764152865527063787384⟩ ⟨false, 164991257548583512877201223997111195374344564542437510207717133428553663186⟩ ⟨false, 8717213091221445487269368090204621435416726587954367974958966904164152613658⟩ ⟨false, 260292100197719310750608436747514059858401469556860415141613715055679435826⟩ = true := by
  decide +kernel

theorem b_23_2400 : bothLoop evalE (oGrid.idx 23) (oGrid.dm 23) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 23) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8717213091221445487269368090204621435416726587954367974958966904164152613658⟩ ⟨false, 260292100197719310750608436747514059858401469556860415141613715055679435826⟩ = true := by
  decide +kernel

theorem o_row_23 : oGrid.row evalE 23 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_23_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_23_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_23_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_23_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_23_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_23_2000).1 (bothLoop_sound b_23_2400).1))))))

theorem n_row_23 : nGrid.row evalE 23 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_23_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_23_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_23_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_23_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_23_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_23_2000).2 (bothLoop_sound b_23_2400).2))))))

theorem o_blk_0 : allFrom (fun j => oGrid.row evalE j) 0 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 0) o_row_0 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1) o_row_1 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 2) o_row_2 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 3) o_row_3 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 4) o_row_4 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 5) o_row_5 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 6) o_row_6 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 7) o_row_7 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 8) o_row_8 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 9) o_row_9 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 10) o_row_10 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 11) o_row_11 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 12) o_row_12 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 13) o_row_13 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 14) o_row_14 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 15) o_row_15 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 16) o_row_16 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 17) o_row_17 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 18) o_row_18 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 19) o_row_19 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 20) o_row_20 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 21) o_row_21 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 22) o_row_22 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 23) o_row_23 (allFrom_zero (fun j => oGrid.row evalE j) 24)))))))))))))))))))))))))

theorem n_blk_0 : allFrom (fun j => nGrid.row evalE j) 0 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 0) n_row_0 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1) n_row_1 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 2) n_row_2 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 3) n_row_3 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 4) n_row_4 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 5) n_row_5 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 6) n_row_6 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 7) n_row_7 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 8) n_row_8 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 9) n_row_9 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 10) n_row_10 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 11) n_row_11 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 12) n_row_12 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 13) n_row_13 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 14) n_row_14 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 15) n_row_15 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 16) n_row_16 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 17) n_row_17 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 18) n_row_18 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 19) n_row_19 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 20) n_row_20 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 21) n_row_21 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 22) n_row_22 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 23) n_row_23 (allFrom_zero (fun j => nGrid.row evalE j) 24)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
