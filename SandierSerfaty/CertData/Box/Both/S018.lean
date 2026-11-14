/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 18 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `432`–`455`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_432_0 : bothSeg evalE (oGrid.idx 432) (oGrid.dm 432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 432) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 868102181705038662563929743866346123956884079555126913093328788429753597266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_432_400 : bothSeg evalE (oGrid.idx 432) (oGrid.dm 432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 432) oGrid.kl oGrid.kr 400 400 ⟨false, 868102181705038662563929743866346123956884079555126913093328788429753597266⟩ ⟨false, 0⟩ ⟨false, 1375351907454193383320855260468197201701325721389184123238687674881987895948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_432_800 : bothSeg evalE (oGrid.idx 432) (oGrid.dm 432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 432) oGrid.kl oGrid.kr 400 800 ⟨false, 1375351907454193383320855260468197201701325721389184123238687674881987895948⟩ ⟨false, 0⟩ ⟨false, 1509211482518015351494559125008975256848977203519554350523757573414414689278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_432_1200 : bothSeg evalE (oGrid.idx 432) (oGrid.dm 432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 432) oGrid.kl oGrid.kr 400 1200 ⟨false, 1509211482518015351494559125008975256848977203519554350523757573414414689278⟩ ⟨false, 0⟩ ⟨false, 1436438307696079178219832572154720743302705654217184533707048120025209346714⟩ ⟨false, 73937311780337540606319445450518466358975779135145916543058129990424499886⟩ = true := by
  decide +kernel

theorem b_432_1600 : bothSeg evalE (oGrid.idx 432) (oGrid.dm 432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 432) oGrid.kl oGrid.kr 400 1600 ⟨false, 1436438307696079178219832572154720743302705654217184533707048120025209346714⟩ ⟨false, 73937311780337540606319445450518466358975779135145916543058129990424499886⟩ ⟨false, 1327847907387584058536078110657979862101726417247309606259347508227654175554⟩ ⟨false, 182527712088832660290073906947259347559955016105020843990758741787979671046⟩ = true := by
  decide +kernel

theorem b_432_2000 : bothSeg evalE (oGrid.idx 432) (oGrid.dm 432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 432) oGrid.kl oGrid.kr 400 2000 ⟨false, 1327847907387584058536078110657979862101726417247309606259347508227654175554⟩ ⟨false, 182527712088832660290073906947259347559955016105020843990758741787979671046⟩ ⟨false, 1329598001723416047899943240270500487166194507172491237078681702319380760950⟩ ⟨false, 189202014523623029299028959840615236270522846361160806486071453660895800464⟩ = true := by
  decide +kernel

theorem b_432_2400 : bothLoop evalE (oGrid.idx 432) (oGrid.dm 432) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 432) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1329598001723416047899943240270500487166194507172491237078681702319380760950⟩ ⟨false, 189202014523623029299028959840615236270522846361160806486071453660895800464⟩ = true := by
  decide +kernel

theorem o_row_432 : oGrid.row evalE 432 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_432_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_432_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_432_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_432_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_432_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_432_2000).1 (bothLoop_sound b_432_2400).1))))))

theorem n_row_432 : nGrid.row evalE 432 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_432_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_432_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_432_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_432_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_432_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_432_2000).2 (bothLoop_sound b_432_2400).2))))))

theorem b_433_0 : bothSeg evalE (oGrid.idx 433) (oGrid.dm 433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 433) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 863553147225317347242578773048936389068671433603239484937643240982331442940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_433_400 : bothSeg evalE (oGrid.idx 433) (oGrid.dm 433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 433) oGrid.kl oGrid.kr 400 400 ⟨false, 863553147225317347242578773048936389068671433603239484937643240982331442940⟩ ⟨false, 0⟩ ⟨false, 1367872259311625313344659096859007271260990532909835580725128860472563495464⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_433_800 : bothSeg evalE (oGrid.idx 433) (oGrid.dm 433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 433) oGrid.kl oGrid.kr 400 800 ⟨false, 1367872259311625313344659096859007271260990532909835580725128860472563495464⟩ ⟨false, 0⟩ ⟨false, 1500538193249015529409278375703048381242729132305984149474372561705931424386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_433_1200 : bothSeg evalE (oGrid.idx 433) (oGrid.dm 433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 433) oGrid.kl oGrid.kr 400 1200 ⟨false, 1500538193249015529409278375703048381242729132305984149474372561705931424386⟩ ⟨false, 0⟩ ⟨false, 1427260851732296844950726809533910837692243580781089767560420366607790668882⟩ ⟨false, 74395986321781591388229021573558210017562371199059783961494427445616035988⟩ = true := by
  decide +kernel

theorem b_433_1600 : bothSeg evalE (oGrid.idx 433) (oGrid.dm 433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 433) oGrid.kl oGrid.kr 400 1600 ⟨false, 1427260851732296844950726809533910837692243580781089767560420366607790668882⟩ ⟨false, 74395986321781591388229021573558210017562371199059783961494427445616035988⟩ ⟨false, 1319230129064433121533788470970118479237954724076220098847245732375365468582⟩ ⟨false, 182426708989645314805167360137350568471851227903929452674669061678041236288⟩ = true := by
  decide +kernel

theorem b_433_2000 : bothSeg evalE (oGrid.idx 433) (oGrid.dm 433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 433) oGrid.kl oGrid.kr 400 2000 ⟨false, 1319230129064433121533788470970118479237954724076220098847245732375365468582⟩ ⟨false, 182426708989645314805167360137350568471851227903929452674669061678041236288⟩ ⟨false, 1321022680587314361753192691321499679118722218587671409114964138961151218710⟩ ⟨false, 189076452823526883759301344737831143520862536321197906973926837768716849436⟩ = true := by
  decide +kernel

theorem b_433_2400 : bothLoop evalE (oGrid.idx 433) (oGrid.dm 433) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 433) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1321022680587314361753192691321499679118722218587671409114964138961151218710⟩ ⟨false, 189076452823526883759301344737831143520862536321197906973926837768716849436⟩ = true := by
  decide +kernel

theorem o_row_433 : oGrid.row evalE 433 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_433_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_433_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_433_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_433_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_433_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_433_2000).1 (bothLoop_sound b_433_2400).1))))))

theorem n_row_433 : nGrid.row evalE 433 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_433_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_433_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_433_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_433_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_433_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_433_2000).2 (bothLoop_sound b_433_2400).2))))))

theorem b_434_0 : bothSeg evalE (oGrid.idx 434) (oGrid.dm 434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 434) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 859020536485273149100425134636030253839022386856860783767475974496331755312⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_434_400 : bothSeg evalE (oGrid.idx 434) (oGrid.dm 434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 434) oGrid.kl oGrid.kr 400 400 ⟨false, 859020536485273149100425134636030253839022386856860783767475974496331755312⟩ ⟨false, 0⟩ ⟨false, 1360419555730617735533935526776268073188905762282448688548514452383349098058⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_434_800 : bothSeg evalE (oGrid.idx 434) (oGrid.dm 434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 434) oGrid.kl oGrid.kr 400 800 ⟨false, 1360419555730617735533935526776268073188905762282448688548514452383349098058⟩ ⟨false, 0⟩ ⟨false, 1491896525561003518989688246656628365591523231390690232187533583280977533582⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_434_1200 : bothSeg evalE (oGrid.idx 434) (oGrid.dm 434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 434) oGrid.kl oGrid.kr 400 1200 ⟨false, 1491896525561003518989688246656628365591523231390690232187533583280977533582⟩ ⟨false, 0⟩ ⟨false, 1418119300200628714483137877875600431618180004470335805649750231740961850356⟩ ⟨false, 74852453155560611407606123693924568113371184228811465890833046940073633446⟩ = true := by
  decide +kernel

theorem b_434_1600 : bothSeg evalE (oGrid.idx 434) (oGrid.dm 434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 434) oGrid.kl oGrid.kr 400 1600 ⟨false, 1418119300200628714483137877875600431618180004470335805649750231740961850356⟩ ⟨false, 74852453155560611407606123693924568113371184228811465890833046940073633446⟩ ⟨false, 1310646514294973623551861043548371550509465167395949390852230076503931192596⟩ ⟨false, 182325239061215702338882958021153449222086021303197880688353202177104291206⟩ = true := by
  decide +kernel

theorem b_434_2000 : bothSeg evalE (oGrid.idx 434) (oGrid.dm 434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 434) oGrid.kl oGrid.kr 400 2000 ⟨false, 1310646514294973623551861043548371550509465167395949390852230076503931192596⟩ ⟨false, 182325239061215702338882958021153449222086021303197880688353202177104291206⟩ ⟨false, 1312482970031411983912157102920785806894999878978075355714820846483601590140⟩ ⟨false, 188948612154919082085375918069900409019441641503565736312388306488061727902⟩ = true := by
  decide +kernel

theorem b_434_2400 : bothLoop evalE (oGrid.idx 434) (oGrid.dm 434) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 434) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1312482970031411983912157102920785806894999878978075355714820846483601590140⟩ ⟨false, 188948612154919082085375918069900409019441641503565736312388306488061727902⟩ = true := by
  decide +kernel

theorem o_row_434 : oGrid.row evalE 434 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_434_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_434_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_434_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_434_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_434_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_434_2000).1 (bothLoop_sound b_434_2400).1))))))

theorem n_row_434 : nGrid.row evalE 434 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_434_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_434_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_434_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_434_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_434_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_434_2000).2 (bothLoop_sound b_434_2400).2))))))

theorem b_435_0 : bothSeg evalE (oGrid.idx 435) (oGrid.dm 435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 435) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 854504307216316879573326951544913374322800289863118599518119575848176504486⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_435_400 : bothSeg evalE (oGrid.idx 435) (oGrid.dm 435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 435) oGrid.kl oGrid.kr 400 400 ⟨false, 854504307216316879573326951544913374322800289863118599518119575848176504486⟩ ⟨false, 0⟩ ⟨false, 1352993761821363589633842956198685240965354705308390806370145545058163407726⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_435_800 : bothSeg evalE (oGrid.idx 435) (oGrid.dm 435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 435) oGrid.kl oGrid.kr 400 800 ⟨false, 1352993761821363589633842956198685240965354705308390806370145545058163407726⟩ ⟨false, 0⟩ ⟨false, 1483286340562102335886278017931783563120026325074736081736117609629622113752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_435_1200 : bothSeg evalE (oGrid.idx 435) (oGrid.dm 435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 435) oGrid.kl oGrid.kr 400 1200 ⟨false, 1483286340562102335886278017931783563120026325074736081736117609629622113752⟩ ⟨false, 0⟩ ⟨false, 1409013364694934733891084389403728517928304379554573282357658633659379202796⟩ ⟨false, 75306666002947338869151320588831386150456353103184257317111317968365832428⟩ = true := by
  decide +kernel

theorem b_435_1600 : bothSeg evalE (oGrid.idx 435) (oGrid.dm 435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 435) oGrid.kl oGrid.kr 400 1600 ⟨false, 1409013364694934733891084389403728517928304379554573282357658633659379202796⟩ ⟨false, 75306666002947338869151320588831386150456353103184257317111317968365832428⟩ ⟨false, 1302096606064284750979638622827177753363411906881085568631769704766641157832⟩ ⟨false, 182223424633597321780597087165382150715348825776671971043000246861103877392⟩ = true := by
  decide +kernel

theorem b_435_2000 : bothSeg evalE (oGrid.idx 435) (oGrid.dm 435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 435) oGrid.kl oGrid.kr 400 2000 ⟨false, 1302096606064284750979638622827177753363411906881085568631769704766641157832⟩ ⟨false, 182223424633597321780597087165382150715348825776671971043000246861103877392⟩ ⟨false, 1303978426807929879118469490956045978182392566363751328004087462066051254020⟩ ⟨false, 188819689103042044214734619347085309222738544007334545532897688299116939686⟩ = true := by
  decide +kernel

theorem b_435_2400 : bothLoop evalE (oGrid.idx 435) (oGrid.dm 435) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 435) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1303978426807929879118469490956045978182392566363751328004087462066051254020⟩ ⟨false, 188819689103042044214734619347085309222738544007334545532897688299116939686⟩ = true := by
  decide +kernel

theorem o_row_435 : oGrid.row evalE 435 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_435_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_435_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_435_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_435_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_435_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_435_2000).1 (bothLoop_sound b_435_2400).1))))))

theorem n_row_435 : nGrid.row evalE 435 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_435_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_435_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_435_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_435_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_435_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_435_2000).2 (bothLoop_sound b_435_2400).2))))))

theorem b_436_0 : bothSeg evalE (oGrid.idx 436) (oGrid.dm 436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 436) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 850004415439311275333656060896680543084561360766138609872061309555273967358⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_436_400 : bothSeg evalE (oGrid.idx 436) (oGrid.dm 436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 436) oGrid.kl oGrid.kr 400 400 ⟨false, 850004415439311275333656060896680543084561360766138609872061309555273967358⟩ ⟨false, 0⟩ ⟨false, 1345594779131234220314278373145421524452048081722871346979761353697982818854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_436_800 : bothSeg evalE (oGrid.idx 436) (oGrid.dm 436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 436) oGrid.kl oGrid.kr 400 800 ⟨false, 1345594779131234220314278373145421524452048081722871346979761353697982818854⟩ ⟨false, 0⟩ ⟨false, 1474707404505251929377796043923420591565147819194712500656602441363075940082⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_436_1200 : bothSeg evalE (oGrid.idx 436) (oGrid.dm 436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 436) oGrid.kl oGrid.kr 400 1200 ⟨false, 1474707404505251929377796043923420591565147819194712500656602441363075940082⟩ ⟨false, 0⟩ ⟨false, 1399943031488636301624365170048130387980541699473092803141844481936737764692⟩ ⟨false, 75759011378333681200464453403721592971895987138102708376375146901115598330⟩ = true := by
  decide +kernel

theorem b_436_1600 : bothSeg evalE (oGrid.idx 436) (oGrid.dm 436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 436) oGrid.kl oGrid.kr 400 1600 ⟨false, 1399943031488636301624365170048130387980541699473092803141844481936737764692⟩ ⟨false, 75759011378333681200464453403721592971895987138102708376375146901115598330⟩ ⟨false, 1293580551801711806034005100555529625378859950003522082821996855946040027998⟩ ⟨false, 182121491065258176790824522896322355573577736607673428696222772891813335024⟩ = true := by
  decide +kernel

theorem b_436_2000 : bothSeg evalE (oGrid.idx 436) (oGrid.dm 436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 436) oGrid.kl oGrid.kr 400 2000 ⟨false, 1293580551801711806034005100555529625378859950003522082821996855946040027998⟩ ⟨false, 182121491065258176790824522896322355573577736607673428696222772891813335024⟩ ⟨false, 1295509232897897993039389728298527209132356289485764233068051844449534176462⟩ ⟨false, 188689033129894253569080667481210904776245781406708123546808691917950995916⟩ = true := by
  decide +kernel

theorem b_436_2400 : bothLoop evalE (oGrid.idx 436) (oGrid.dm 436) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 436) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1295509232897897993039389728298527209132356289485764233068051844449534176462⟩ ⟨false, 188689033129894253569080667481210904776245781406708123546808691917950995916⟩ = true := by
  decide +kernel

theorem o_row_436 : oGrid.row evalE 436 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_436_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_436_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_436_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_436_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_436_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_436_2000).1 (bothLoop_sound b_436_2400).1))))))

theorem n_row_436 : nGrid.row evalE 436 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_436_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_436_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_436_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_436_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_436_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_436_2000).2 (bothLoop_sound b_436_2400).2))))))

theorem b_437_0 : bothSeg evalE (oGrid.idx 437) (oGrid.dm 437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 437) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 845520819252590899794110574726070504382081249894013929866909553312136359492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_437_400 : bothSeg evalE (oGrid.idx 437) (oGrid.dm 437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 437) oGrid.kl oGrid.kr 400 400 ⟨false, 845520819252590899794110574726070504382081249894013929866909553312136359492⟩ ⟨false, 0⟩ ⟨false, 1338222555656600610600983184297165836023338800691021241055495359206718034468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_437_800 : bothSeg evalE (oGrid.idx 437) (oGrid.dm 437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 437) oGrid.kl oGrid.kr 400 800 ⟨false, 1338222555656600610600983184297165836023338800691021241055495359206718034468⟩ ⟨false, 0⟩ ⟨false, 1466159707499397691973819268325451312329928725249181897378552088462481778528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_437_1200 : bothSeg evalE (oGrid.idx 437) (oGrid.dm 437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 437) oGrid.kl oGrid.kr 400 1200 ⟨false, 1466159707499397691973819268325451312329928725249181897378552088462481778528⟩ ⟨false, 0⟩ ⟨false, 1390908387524613814508594558751081939674736142770616650988324753771511273692⟩ ⟨false, 76209109191050666307009652551687592259005465105326528445009169861539078560⟩ = true := by
  decide +kernel

theorem b_437_1600 : bothSeg evalE (oGrid.idx 437) (oGrid.dm 437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 437) oGrid.kl oGrid.kr 400 1600 ⟨false, 1390908387524613814508594558751081939674736142770616650988324753771511273692⟩ ⟨false, 76209109191050666307009652551687592259005465105326528445009169861539078560⟩ ⟨false, 1285098430862448982802007403780608320736914239630040847662889351663936454440⟩ ⟨false, 182019065853215498013596807522161211196827368245902331770444571969113897812⟩ = true := by
  decide +kernel

theorem b_437_2000 : bothSeg evalE (oGrid.idx 437) (oGrid.dm 437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 437) oGrid.kl oGrid.kr 400 2000 ⟨false, 1285098430862448982802007403780608320736914239630040847662889351663936454440⟩ ⟨false, 182019065853215498013596807522161211196827368245902331770444571969113897812⟩ ⟨false, 1287075477616914343894832042187490335989411200358295649960769107175351742166⟩ ⟨false, 188555959919541007998435922774160184741393303268602524337117511567283850734⟩ = true := by
  decide +kernel

theorem b_437_2400 : bothLoop evalE (oGrid.idx 437) (oGrid.dm 437) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 437) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1287075477616914343894832042187490335989411200358295649960769107175351742166⟩ ⟨false, 188555959919541007998435922774160184741393303268602524337117511567283850734⟩ = true := by
  decide +kernel

theorem o_row_437 : oGrid.row evalE 437 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_437_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_437_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_437_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_437_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_437_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_437_2000).1 (bothLoop_sound b_437_2400).1))))))

theorem n_row_437 : nGrid.row evalE 437 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_437_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_437_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_437_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_437_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_437_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_437_2000).2 (bothLoop_sound b_437_2400).2))))))

theorem b_438_0 : bothSeg evalE (oGrid.idx 438) (oGrid.dm 438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 438) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 841053474649797867400310703510216588351508303095128597631064171890812368862⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_438_400 : bothSeg evalE (oGrid.idx 438) (oGrid.dm 438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 438) oGrid.kl oGrid.kr 400 400 ⟨false, 841053474649797867400310703510216588351508303095128597631064171890812368862⟩ ⟨false, 0⟩ ⟨false, 1330877017845099687679418969868078514424719038781696416968749803793929019308⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_438_800 : bothSeg evalE (oGrid.idx 438) (oGrid.dm 438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 438) oGrid.kl oGrid.kr 400 800 ⟨false, 1330877017845099687679418969868078514424719038781696416968749803793929019308⟩ ⟨false, 0⟩ ⟨false, 1457643101676147397807846707189181788792397544159502019546846301739795488714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_438_1200 : bothSeg evalE (oGrid.idx 438) (oGrid.dm 438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 438) oGrid.kl oGrid.kr 400 1200 ⟨false, 1457643101676147397807846707189181788792397544159502019546846301739795488714⟩ ⟨false, 0⟩ ⟨false, 1381909087425924820351151226557774166148015973429889795251312988859797743136⟩ ⟨false, 76657072491013004614062298759987090523002256278691797682569164107259600432⟩ = true := by
  decide +kernel

theorem b_438_1600 : bothSeg evalE (oGrid.idx 438) (oGrid.dm 438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 438) oGrid.kl oGrid.kr 400 1600 ⟨false, 1381909087425924820351151226557774166148015973429889795251312988859797743136⟩ ⟨false, 76657072491013004614062298759987090523002256278691797682569164107259600432⟩ ⟨false, 1276649904542155221606001363709993844952507278299043216047187008515118007572⟩ ⟨false, 181916255374782603359212161607767411718510951409538376886695144451939335996⟩ = true := by
  decide +kernel

theorem b_438_2000 : bothSeg evalE (oGrid.idx 438) (oGrid.dm 438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 438) oGrid.kl oGrid.kr 400 2000 ⟨false, 1276649904542155221606001363709993844952507278299043216047187008515118007572⟩ ⟨false, 181916255374782603359212161607767411718510951409538376886695144451939335996⟩ ⟨false, 1278676830707464695438827748884042901671892913832167903872294870957528577390⟩ ⟨false, 188421318631330429870202317672585759428902921211800903496248328171931758182⟩ = true := by
  decide +kernel

theorem b_438_2400 : bothLoop evalE (oGrid.idx 438) (oGrid.dm 438) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 438) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1278676830707464695438827748884042901671892913832167903872294870957528577390⟩ ⟨false, 188421318631330429870202317672585759428902921211800903496248328171931758182⟩ = true := by
  decide +kernel

theorem o_row_438 : oGrid.row evalE 438 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_438_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_438_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_438_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_438_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_438_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_438_2000).1 (bothLoop_sound b_438_2400).1))))))

theorem n_row_438 : nGrid.row evalE 438 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_438_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_438_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_438_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_438_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_438_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_438_2000).2 (bothLoop_sound b_438_2400).2))))))

theorem b_439_0 : bothSeg evalE (oGrid.idx 439) (oGrid.dm 439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 439) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 836602339909909496132508430486333289483641456735405228060646155833291046002⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_439_400 : bothSeg evalE (oGrid.idx 439) (oGrid.dm 439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 439) oGrid.kl oGrid.kr 400 400 ⟨false, 836602339909909496132508430486333289483641456735405228060646155833291046002⟩ ⟨false, 0⟩ ⟨false, 1323558130102573129751989926220062345452702106542352356543369516441840508444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_439_800 : bothSeg evalE (oGrid.idx 439) (oGrid.dm 439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 439) oGrid.kl oGrid.kr 400 800 ⟨false, 1323558130102573129751989926220062345452702106542352356543369516441840508444⟩ ⟨false, 0⟩ ⟨false, 1449157397066897951165990326726886414246260686038609443333575276439053650772⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_439_1200 : bothSeg evalE (oGrid.idx 439) (oGrid.dm 439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 439) oGrid.kl oGrid.kr 400 1200 ⟨false, 1449157397066897951165990326726886414246260686038609443333575276439053650772⟩ ⟨false, 0⟩ ⟨false, 1372945130024509105894801858817348523407569011497098496131990100653460077572⟩ ⟨false, 77102488739737295678296362690974452347715773768359085588576990220362044316⟩ = true := by
  decide +kernel

theorem b_439_1600 : bothSeg evalE (oGrid.idx 439) (oGrid.dm 439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 439) oGrid.kl oGrid.kr 400 1600 ⟨false, 1372945130024509105894801858817348523407569011497098496131990100653460077572⟩ ⟨false, 77102488739737295678296362690974452347715773768359085588576990220362044316⟩ ⟨false, 1268234970423919641273470618349455463467674391968934642476319666076639517460⟩ ⟨false, 181812648340326760299627603158867512287610393296522939244247424797182604428⟩ = true := by
  decide +kernel

theorem b_439_2000 : bothSeg evalE (oGrid.idx 439) (oGrid.dm 439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 439) oGrid.kl oGrid.kr 400 2000 ⟨false, 1268234970423919641273470618349455463467674391968934642476319666076639517460⟩ ⟨false, 181812648340326760299627603158867512287610393296522939244247424797182604428⟩ ⟨false, 1270313330915798192721452643993636555661219663149827161484802287885078106692⟩ ⟨false, 188284797948021523294239771203820441019248830330877290359105418679916571848⟩ = true := by
  decide +kernel

theorem b_439_2400 : bothLoop evalE (oGrid.idx 439) (oGrid.dm 439) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 439) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1270313330915798192721452643993636555661219663149827161484802287885078106692⟩ ⟨false, 188284797948021523294239771203820441019248830330877290359105418679916571848⟩ = true := by
  decide +kernel

theorem o_row_439 : oGrid.row evalE 439 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_439_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_439_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_439_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_439_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_439_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_439_2000).1 (bothLoop_sound b_439_2400).1))))))

theorem n_row_439 : nGrid.row evalE 439 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_439_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_439_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_439_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_439_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_439_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_439_2000).2 (bothLoop_sound b_439_2400).2))))))

theorem b_440_0 : bothSeg evalE (oGrid.idx 440) (oGrid.dm 440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 440) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 832167369835229111360779578430819610986700992715500421402001912033056636594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_440_400 : bothSeg evalE (oGrid.idx 440) (oGrid.dm 440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 440) oGrid.kl oGrid.kr 400 400 ⟨false, 832167369835229111360779578430819610986700992715500421402001912033056636594⟩ ⟨false, 0⟩ ⟨false, 1316265781488182291926344381421775322778490957595037461068642629720072296244⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_440_800 : bothSeg evalE (oGrid.idx 440) (oGrid.dm 440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 440) oGrid.kl oGrid.kr 400 800 ⟨false, 1316265781488182291926344381421775322778490957595037461068642629720072296244⟩ ⟨false, 0⟩ ⟨false, 1440702495428653572950457509343649495288766242739747403384048023594916338478⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_440_1200 : bothSeg evalE (oGrid.idx 440) (oGrid.dm 440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 440) oGrid.kl oGrid.kr 400 1200 ⟨false, 1440702495428653572950457509343649495288766242739747403384048023594916338478⟩ ⟨false, 0⟩ ⟨false, 1364016410449860092471718703565837649333801816164116015748874332694471152358⟩ ⟨false, 77546419864017199334791374565933518829627649793327963261242536128603160834⟩ = true := by
  decide +kernel

theorem b_440_1600 : bothSeg evalE (oGrid.idx 440) (oGrid.dm 440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 440) oGrid.kl oGrid.kr 400 1600 ⟨false, 1364016410449860092471718703565837649333801816164116015748874332694471152358⟩ ⟨false, 77546419864017199334791374565933518829627649793327963261242536128603160834⟩ ⟨false, 1259853555136390325831811770396506246918279760422905083699517228183538990114⟩ ⟨false, 181709275177486965974698307735264921245149705534538895310599640639535323078⟩ = true := by
  decide +kernel

theorem b_440_2000 : bothSeg evalE (oGrid.idx 440) (oGrid.dm 440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 440) oGrid.kl oGrid.kr 400 2000 ⟨false, 1259853555136390325831811770396506246918279760422905083699517228183538990114⟩ ⟨false, 181709275177486965974698307735264921245149705534538895310599640639535323078⟩ ⟨false, 1261984902764920122586445272889209649838429968247729680480790330887900093768⟩ ⟨false, 188146551230804211982112959652500577866414923992196696502792307969429654444⟩ = true := by
  decide +kernel

theorem b_440_2400 : bothLoop evalE (oGrid.idx 440) (oGrid.dm 440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 440) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1261984902764920122586445272889209649838429968247729680480790330887900093768⟩ ⟨false, 188146551230804211982112959652500577866414923992196696502792307969429654444⟩ = true := by
  decide +kernel

theorem o_row_440 : oGrid.row evalE 440 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_440_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_440_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_440_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_440_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_440_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_440_2000).1 (bothLoop_sound b_440_2400).1))))))

theorem n_row_440 : nGrid.row evalE 440 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_440_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_440_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_440_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_440_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_440_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_440_2000).2 (bothLoop_sound b_440_2400).2))))))

theorem b_441_0 : bothSeg evalE (oGrid.idx 441) (oGrid.dm 441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 441) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 827748520098012174298812773222116573654932150151696034760461908167286225356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_441_400 : bothSeg evalE (oGrid.idx 441) (oGrid.dm 441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 441) oGrid.kl oGrid.kr 400 400 ⟨false, 827748520098012174298812773222116573654932150151696034760461908167286225356⟩ ⟨false, 0⟩ ⟨false, 1308999921476403998155236313736944287114999562905189394943081836706450230704⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_441_800 : bothSeg evalE (oGrid.idx 441) (oGrid.dm 441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 441) oGrid.kl oGrid.kr 400 800 ⟨false, 1308999921476403998155236313736944287114999562905189394943081836706450230704⟩ ⟨false, 0⟩ ⟨false, 1432278270080201399291250821511899805188290278395847381749795309864985012300⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_441_1200 : bothSeg evalE (oGrid.idx 441) (oGrid.dm 441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 441) oGrid.kl oGrid.kr 400 1200 ⟨false, 1432278270080201399291250821511899805188290278395847381749795309864985012300⟩ ⟨false, 0⟩ ⟨false, 1355123054227678576832702274672938127779547981748730562653449201830641741850⟩ ⟨false, 77988259357895083281676526272495582792900153727870343898099327309287220410⟩ = true := by
  decide +kernel

theorem b_441_1600 : bothSeg evalE (oGrid.idx 441) (oGrid.dm 441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 441) oGrid.kl oGrid.kr 400 1600 ⟨false, 1355123054227678576832702274672938127779547981748730562653449201830641741850⟩ ⟨false, 77988259357895083281676526272495582792900153727870343898099327309287220410⟩ ⟨false, 1251505781964784834881602419905387239694467249936692473985967360173865999582⟩ ⟨false, 181605531620788825232776381040046470877980885539908432565581168966062962678⟩ = true := by
  decide +kernel

theorem b_441_2000 : bothSeg evalE (oGrid.idx 441) (oGrid.dm 441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 441) oGrid.kl oGrid.kr 400 2000 ⟨false, 1251505781964784834881602419905387239694467249936692473985967360173865999582⟩ ⟨false, 181605531620788825232776381040046470877980885539908432565581168966062962678⟩ ⟨false, 1253691722987720627794511900666276537520796709839087810227032634223071908098⟩ ⟨false, 188006158748388557752601754046789009170046244554482508511541094592087001628⟩ = true := by
  decide +kernel

theorem b_441_2400 : bothLoop evalE (oGrid.idx 441) (oGrid.dm 441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 441) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1253691722987720627794511900666276537520796709839087810227032634223071908098⟩ ⟨false, 188006158748388557752601754046789009170046244554482508511541094592087001628⟩ = true := by
  decide +kernel

theorem o_row_441 : oGrid.row evalE 441 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_441_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_441_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_441_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_441_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_441_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_441_2000).1 (bothLoop_sound b_441_2400).1))))))

theorem n_row_441 : nGrid.row evalE 441 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_441_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_441_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_441_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_441_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_441_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_441_2000).2 (bothLoop_sound b_441_2400).2))))))

theorem b_442_0 : bothSeg evalE (oGrid.idx 442) (oGrid.dm 442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 442) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 823345748617943765731193614863614216978829009688083063786216717476996999416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_442_400 : bothSeg evalE (oGrid.idx 442) (oGrid.dm 442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 442) oGrid.kl oGrid.kr 400 400 ⟨false, 823345748617943765731193614863614216978829009688083063786216717476996999416⟩ ⟨false, 0⟩ ⟨false, 1301760484629573384821881167988765665165204422188371281208764008323011332112⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_442_800 : bothSeg evalE (oGrid.idx 442) (oGrid.dm 442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 442) oGrid.kl oGrid.kr 400 800 ⟨false, 1301760484629573384821881167988765665165204422188371281208764008323011332112⟩ ⟨false, 0⟩ ⟨false, 1423884509789258974770766485697771120862575785714386051368388591177085007398⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_442_1200 : bothSeg evalE (oGrid.idx 442) (oGrid.dm 442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 442) oGrid.kl oGrid.kr 400 1200 ⟨false, 1423884509789258974770766485697771120862575785714386051368388591177085007398⟩ ⟨false, 0⟩ ⟨false, 1346264554663469525987199915399369678918409096945172382091899173502255117300⟩ ⟨false, 78427534557166929808417117131327922577321563603642761395324980054195933598⟩ = true := by
  decide +kernel

theorem b_442_1600 : bothSeg evalE (oGrid.idx 442) (oGrid.dm 442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 442) oGrid.kl oGrid.kr 400 1600 ⟨false, 1346264554663469525987199915399369678918409096945172382091899173502255117300⟩ ⟨false, 78427534557166929808417117131327922577321563603642761395324980054195933598⟩ ⟨false, 1243191132709953090102415753351018001124956111031676641252214181971087596742⟩ ⟨false, 181500956510683365693201279179679600370774549517138502235009971585363454156⟩ = true := by
  decide +kernel

theorem b_442_2000 : bothSeg evalE (oGrid.idx 442) (oGrid.dm 442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 442) oGrid.kl oGrid.kr 400 2000 ⟨false, 1243191132709953090102415753351018001124956111031676641252214181971087596742⟩ ⟨false, 181500956510683365693201279179679600370774549517138502235009971585363454156⟩ ⟨false, 1245433245662903071446766051700961457092330315630924518766386216567423411552⟩ ⟨false, 187864156890516519988678181202035595504601122239593029953188550144196907702⟩ = true := by
  decide +kernel

theorem b_442_2400 : bothLoop evalE (oGrid.idx 442) (oGrid.dm 442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 442) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1245433245662903071446766051700961457092330315630924518766386216567423411552⟩ ⟨false, 187864156890516519988678181202035595504601122239593029953188550144196907702⟩ = true := by
  decide +kernel

theorem o_row_442 : oGrid.row evalE 442 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_442_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_442_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_442_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_442_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_442_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_442_2000).1 (bothLoop_sound b_442_2400).1))))))

theorem n_row_442 : nGrid.row evalE 442 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_442_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_442_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_442_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_442_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_442_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_442_2000).2 (bothLoop_sound b_442_2400).2))))))

theorem b_443_0 : bothSeg evalE (oGrid.idx 443) (oGrid.dm 443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 443) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 818959014507248145474139735742316112981850555023958043500882835362800023742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_443_400 : bothSeg evalE (oGrid.idx 443) (oGrid.dm 443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 443) oGrid.kl oGrid.kr 400 400 ⟨false, 818959014507248145474139735742316112981850555023958043500882835362800023742⟩ ⟨false, 0⟩ ⟨false, 1294547424551814699878037706645557072053751125232092700852942040339144055654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_443_800 : bothSeg evalE (oGrid.idx 443) (oGrid.dm 443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 443) oGrid.kl oGrid.kr 400 800 ⟨false, 1294547424551814699878037706645557072053751125232092700852942040339144055654⟩ ⟨false, 0⟩ ⟨false, 1415521098871461204102860762192194045839583362923145286385090616944602289516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_443_1200 : bothSeg evalE (oGrid.idx 443) (oGrid.dm 443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 443) oGrid.kl oGrid.kr 400 1200 ⟨false, 1415521098871461204102860762192194045839583362923145286385090616944602289516⟩ ⟨false, 0⟩ ⟨false, 1337441135767878573954850364168724105683856993292794608062536648639251564182⟩ ⟨false, 78865179885756068257962952857928345611073985178793408702752345949652556420⟩ = true := by
  decide +kernel

theorem b_443_1600 : bothSeg evalE (oGrid.idx 443) (oGrid.dm 443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 443) oGrid.kl oGrid.kr 400 1600 ⟨false, 1337441135767878573954850364168724105683856993292794608062536648639251564182⟩ ⟨false, 78865179885756068257962952857928345611073985178793408702752345949652556420⟩ ⟨false, 1234909866763440536145004801086241503413555731586162328399358772140384965170⟩ ⟨false, 181396448890194106067808515940410947881375246885425688365930222448519155432⟩ = true := by
  decide +kernel

theorem b_443_2000 : bothSeg evalE (oGrid.idx 443) (oGrid.dm 443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 443) oGrid.kl oGrid.kr 400 2000 ⟨false, 1234909866763440536145004801086241503413555731586162328399358772140384965170⟩ ⟨false, 181396448890194106067808515940410947881375246885425688365930222448519155432⟩ ⟨false, 1237209758611818096871422975990300868257748575686974440350050729261366132666⟩ ⟨false, 187720246016389085388388420243752177803607269939300258091322629260475515270⟩ = true := by
  decide +kernel

theorem b_443_2400 : bothLoop evalE (oGrid.idx 443) (oGrid.dm 443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 443) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1237209758611818096871422975990300868257748575686974440350050729261366132666⟩ ⟨false, 187720246016389085388388420243752177803607269939300258091322629260475515270⟩ = true := by
  decide +kernel

theorem o_row_443 : oGrid.row evalE 443 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_443_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_443_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_443_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_443_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_443_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_443_2000).1 (bothLoop_sound b_443_2400).1))))))

theorem n_row_443 : nGrid.row evalE 443 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_443_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_443_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_443_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_443_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_443_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_443_2000).2 (bothLoop_sound b_443_2400).2))))))

theorem b_444_0 : bothSeg evalE (oGrid.idx 444) (oGrid.dm 444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 444) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 814588274238702403342938659789857684065764156913828516936302502953549374600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_444_400 : bothSeg evalE (oGrid.idx 444) (oGrid.dm 444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 444) oGrid.kl oGrid.kr 400 400 ⟨false, 814588274238702403342938659789857684065764156913828516936302502953549374600⟩ ⟨false, 0⟩ ⟨false, 1287360636711691083530784729454865237868712454254472710490424532832951554914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_444_800 : bothSeg evalE (oGrid.idx 444) (oGrid.dm 444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 444) oGrid.kl oGrid.kr 400 800 ⟨false, 1287360636711691083530784729454865237868712454254472710490424532832951554914⟩ ⟨false, 0⟩ ⟨false, 1407187872462079554810329334759935047532994317687241875384622911369259160424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_444_1200 : bothSeg evalE (oGrid.idx 444) (oGrid.dm 444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 444) oGrid.kl oGrid.kr 400 1200 ⟨false, 1407187872462079554810329334759935047532994317687241875384622911369259160424⟩ ⟨false, 0⟩ ⟨false, 1328652705511886491581850589817459841267126581400891110384521471827123580194⟩ ⟨false, 79300389324698519217550557768821613953551437224600951278948023473542352136⟩ = true := by
  decide +kernel

theorem b_444_1600 : bothSeg evalE (oGrid.idx 444) (oGrid.dm 444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 444) oGrid.kl oGrid.kr 400 1600 ⟨false, 1328652705511886491581850589817459841267126581400891110384521471827123580194⟩ ⟨false, 79300389324698519217550557768821613953551437224600951278948023473542352136⟩ ⟨false, 1226661882142564486593814123878774286703626396763959177748487990918928075632⟩ ⟨false, 181291212694020524205587023707507168517051621861532883914981504381737856698⟩ = true := by
  decide +kernel

theorem b_444_2000 : bothSeg evalE (oGrid.idx 444) (oGrid.dm 444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 444) oGrid.kl oGrid.kr 400 2000 ⟨false, 1226661882142564486593814123878774286703626396763959177748487990918928075632⟩ ⟨false, 181291212694020524205587023707507168517051621861532883914981504381737856698⟩ ⟨false, 1229021146806176481245499327622504659387718965380630904382604692167329292688⟩ ⟨false, 187573611295349207192402717160889958238967733255048020120856665724521626752⟩ = true := by
  decide +kernel

theorem b_444_2400 : bothLoop evalE (oGrid.idx 444) (oGrid.dm 444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 444) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1229021146806176481245499327622504659387718965380630904382604692167329292688⟩ ⟨false, 187573611295349207192402717160889958238967733255048020120856665724521626752⟩ = true := by
  decide +kernel

theorem o_row_444 : oGrid.row evalE 444 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_444_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_444_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_444_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_444_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_444_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_444_2000).1 (bothLoop_sound b_444_2400).1))))))

theorem n_row_444 : nGrid.row evalE 444 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_444_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_444_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_444_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_444_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_444_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_444_2000).2 (bothLoop_sound b_444_2400).2))))))

theorem b_445_0 : bothSeg evalE (oGrid.idx 445) (oGrid.dm 445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 445) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 810233486239963346211022294380311106324020689034425656514151891537771442504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_445_400 : bothSeg evalE (oGrid.idx 445) (oGrid.dm 445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 445) oGrid.kl oGrid.kr 400 400 ⟨false, 810233486239963346211022294380311106324020689034425656514151891537771442504⟩ ⟨false, 0⟩ ⟨false, 1280200083703153540782860671373397689804613902208722684379522183411622768586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_445_800 : bothSeg evalE (oGrid.idx 445) (oGrid.dm 445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 445) oGrid.kl oGrid.kr 400 800 ⟨false, 1280200083703153540782860671373397689804613902208722684379522183411622768586⟩ ⟨false, 0⟩ ⟨false, 1398884633072545153849657295469591284356267804295544128895333374240147374114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_445_1200 : bothSeg evalE (oGrid.idx 445) (oGrid.dm 445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 445) oGrid.kl oGrid.kr 400 1200 ⟨false, 1398884633072545153849657295469591284356267804295544128895333374240147374114⟩ ⟨false, 0⟩ ⟨false, 1319899078065489228515538362915964125898200251966841417161071416491095401418⟩ ⟨false, 79733707212751723996206614237397283074717131402365434056468813370841296312⟩ = true := by
  decide +kernel

theorem b_445_1600 : bothSeg evalE (oGrid.idx 445) (oGrid.dm 445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 445) oGrid.kl oGrid.kr 400 1600 ⟨false, 1319899078065489228515538362915964125898200251966841417161071416491095401418⟩ ⟨false, 79733707212751723996206614237397283074717131402365434056468813370841296312⟩ ⟨false, 1218446988376879634489280999401326039424219632098671112184355146871197578420⟩ ⟨false, 181185796901361318022463977752035369548697751270535739033185082990739119310⟩ = true := by
  decide +kernel

theorem b_445_2000 : bothSeg evalE (oGrid.idx 445) (oGrid.dm 445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 445) oGrid.kl oGrid.kr 400 2000 ⟨false, 1218446988376879634489280999401326039424219632098671112184355146871197578420⟩ ⟨false, 181185796901361318022463977752035369548697751270535739033185082990739119310⟩ ⟨false, 1220867235011326805787441891218728883709940025219387822427697830648220768202⟩ ⟨false, 187425812476986997029966847410622985947509327131075593789658286440456051990⟩ = true := by
  decide +kernel

theorem b_445_2400 : bothLoop evalE (oGrid.idx 445) (oGrid.dm 445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 445) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1220867235011326805787441891218728883709940025219387822427697830648220768202⟩ ⟨false, 187425812476986997029966847410622985947509327131075593789658286440456051990⟩ = true := by
  decide +kernel

theorem o_row_445 : oGrid.row evalE 445 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_445_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_445_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_445_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_445_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_445_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_445_2000).1 (bothLoop_sound b_445_2400).1))))))

theorem n_row_445 : nGrid.row evalE 445 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_445_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_445_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_445_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_445_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_445_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_445_2000).2 (bothLoop_sound b_445_2400).2))))))

theorem b_446_0 : bothSeg evalE (oGrid.idx 446) (oGrid.dm 446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 446) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 805894606708640696471054515294344922689150335944754366632792791583539576498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_446_400 : bothSeg evalE (oGrid.idx 446) (oGrid.dm 446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 446) oGrid.kl oGrid.kr 400 400 ⟨false, 805894606708640696471054515294344922689150335944754366632792791583539576498⟩ ⟨false, 0⟩ ⟨false, 1273065684502400326479616660482898216865044265498274520529284171305067369826⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_446_800 : bothSeg evalE (oGrid.idx 446) (oGrid.dm 446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 446) oGrid.kl oGrid.kr 400 800 ⟨false, 1273065684502400326479616660482898216865044265498274520529284171305067369826⟩ ⟨false, 0⟩ ⟨false, 1390611218431530242262769624945287927405132669388198872420675847698215486092⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_446_1200 : bothSeg evalE (oGrid.idx 446) (oGrid.dm 446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 446) oGrid.kl oGrid.kr 400 1200 ⟨false, 1390611218431530242262769624945287927405132669388198872420675847698215486092⟩ ⟨false, 0⟩ ⟨false, 1311180179158326764929390116379090801763643632890057789181666137479805097970⟩ ⟨false, 80165139407933831246936599717099790285539559326911175489674441065263695038⟩ = true := by
  decide +kernel

theorem b_446_1600 : bothSeg evalE (oGrid.idx 446) (oGrid.dm 446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 446) oGrid.kl oGrid.kr 400 1600 ⟨false, 1311180179158326764929390116379090801763643632890057789181666137479805097970⟩ ⟨false, 80165139407933831246936599717099790285539559326911175489674441065263695038⟩ ⟨false, 1210265124775734097789164223210784407092024249625125432144396226170493254180⟩ ⟨false, 181080193790526498387162492885406184957158942591843532526944352374575538828⟩ = true := by
  decide +kernel

theorem b_446_2000 : bothSeg evalE (oGrid.idx 446) (oGrid.dm 446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 446) oGrid.kl oGrid.kr 400 2000 ⟨false, 1210265124775734097789164223210784407092024249625125432144396226170493254180⟩ ⟨false, 181080193790526498387162492885406184957158942591843532526944352374575538828⟩ ⟨false, 1212747995410045400652218062878954406289229997179833291042638334515750090612⟩ ⟨false, 187276174026707825385084268965161765665954015549658348193607987429317858906⟩ = true := by
  decide +kernel

theorem b_446_2400 : bothLoop evalE (oGrid.idx 446) (oGrid.dm 446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 446) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1212747995410045400652218062878954406289229997179833291042638334515750090612⟩ ⟨false, 187276174026707825385084268965161765665954015549658348193607987429317858906⟩ = true := by
  decide +kernel

theorem o_row_446 : oGrid.row evalE 446 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_446_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_446_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_446_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_446_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_446_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_446_2000).1 (bothLoop_sound b_446_2400).1))))))

theorem n_row_446 : nGrid.row evalE 446 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_446_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_446_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_446_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_446_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_446_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_446_2000).2 (bothLoop_sound b_446_2400).2))))))

theorem b_447_0 : bothSeg evalE (oGrid.idx 447) (oGrid.dm 447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 447) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 801571595180278582703197206278760164651659353134238580813187159044687213818⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_447_400 : bothSeg evalE (oGrid.idx 447) (oGrid.dm 447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 447) oGrid.kl oGrid.kr 400 400 ⟨false, 801571595180278582703197206278760164651659353134238580813187159044687213818⟩ ⟨false, 0⟩ ⟨false, 1265957393099205217547659208570758781997332951213694752135319826350943930476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_447_800 : bothSeg evalE (oGrid.idx 447) (oGrid.dm 447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 447) oGrid.kl oGrid.kr 400 800 ⟨false, 1265957393099205217547659208570758781997332951213694752135319826350943930476⟩ ⟨false, 0⟩ ⟨false, 1382367524050805238195069045228789328458612564603096594609694062874408978356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_447_1200 : bothSeg evalE (oGrid.idx 447) (oGrid.dm 447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 447) oGrid.kl oGrid.kr 400 1200 ⟨false, 1382367524050805238195069045228789328458612564603096594609694062874408978356⟩ ⟨false, 0⟩ ⟨false, 1302495917100269179984286222299918021721460397785560740068983639743104063070⟩ ⟨false, 80594425884289167051256917468256472932635312857251872711598081063027903178⟩ = true := by
  decide +kernel

theorem b_447_1600 : bothSeg evalE (oGrid.idx 447) (oGrid.dm 447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 447) oGrid.kl oGrid.kr 400 1600 ⟨false, 1302495917100269179984286222299918021721460397785560740068983639743104063070⟩ ⟨false, 80594425884289167051256917468256472932635312857251872711598081063027903178⟩ ⟨false, 1202116245687581068129211230520344667504575849097320376989757316690485227064⟩ ⟨false, 180974097296977278906331909247829827149519861545492235790824404115646739184⟩ = true := by
  decide +kernel

theorem b_447_2000 : bothSeg evalE (oGrid.idx 447) (oGrid.dm 447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 447) oGrid.kl oGrid.kr 400 2000 ⟨false, 1202116245687581068129211230520344667504575849097320376989757316690485227064⟩ ⟨false, 180974097296977278906331909247829827149519861545492235790824404115646739184⟩ ⟨false, 1204663375893072822141158583517552864952999811310796277827541763989557564406⟩ ⟨false, 187124102874876324456541606067260835969733850793789575829122660380655910618⟩ = true := by
  decide +kernel

theorem b_447_2400 : bothLoop evalE (oGrid.idx 447) (oGrid.dm 447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 447) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1204663375893072822141158583517552864952999811310796277827541763989557564406⟩ ⟨false, 187124102874876324456541606067260835969733850793789575829122660380655910618⟩ = true := by
  decide +kernel

theorem o_row_447 : oGrid.row evalE 447 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_447_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_447_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_447_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_447_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_447_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_447_2000).1 (bothLoop_sound b_447_2400).1))))))

theorem n_row_447 : nGrid.row evalE 447 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_447_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_447_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_447_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_447_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_447_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_447_2000).2 (bothLoop_sound b_447_2400).2))))))

theorem b_448_0 : bothSeg evalE (oGrid.idx 448) (oGrid.dm 448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 448) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 797264400873530576122309037321086928067325425468305920044997089934896011356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_448_400 : bothSeg evalE (oGrid.idx 448) (oGrid.dm 448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 448) oGrid.kl oGrid.kr 400 400 ⟨false, 797264400873530576122309037321086928067325425468305920044997089934896011356⟩ ⟨false, 0⟩ ⟨false, 1258875111226157491611197419957611575932673500943106517438098095014988758148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_448_800 : bothSeg evalE (oGrid.idx 448) (oGrid.dm 448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 448) oGrid.kl oGrid.kr 400 800 ⟨false, 1258875111226157491611197419957611575932673500943106517438098095014988758148⟩ ⟨false, 0⟩ ⟨false, 1374153267356410493750511453126139130411066211423704030196955165598304345358⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_448_1200 : bothSeg evalE (oGrid.idx 448) (oGrid.dm 448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 448) oGrid.kl oGrid.kr 400 1200 ⟨false, 1374153267356410493750511453126139130411066211423704030196955165598304345358⟩ ⟨false, 0⟩ ⟨false, 1293846378661245961087014904280904920134532948792736614508088451826963115650⟩ ⟨false, 81021391554624130889289678124948052584779752457628430417290256538207456068⟩ = true := by
  decide +kernel

theorem b_448_1600 : bothSeg evalE (oGrid.idx 448) (oGrid.dm 448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 448) oGrid.kl oGrid.kr 400 1600 ⟨false, 1293846378661245961087014904280904920134532948792736614508088451826963115650⟩ ⟨false, 81021391554624130889289678124948052584779752457628430417290256538207456068⟩ ⟨false, 1194000384850594650222780131983110290024475307921440893329437511530665174068⟩ ⟨false, 180867385365275441753524450422742682694837393328924151595941196834505397650⟩ = true := by
  decide +kernel

theorem b_448_2000 : bothSeg evalE (oGrid.idx 448) (oGrid.dm 448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 448) oGrid.kl oGrid.kr 400 2000 ⟨false, 1194000384850594650222780131983110290024475307921440893329437511530665174068⟩ ⟨false, 180867385365275441753524450422742682694837393328924151595941196834505397650⟩ ⟨false, 1196613399213766534726012810437690257888485896112963555937389486581182579918⟩ ⟨false, 186970053056063630417606513179868732017123008843118963586548160497455494138⟩ = true := by
  decide +kernel

theorem b_448_2400 : bothLoop evalE (oGrid.idx 448) (oGrid.dm 448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 448) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1196613399213766534726012810437690257888485896112963555937389486581182579918⟩ ⟨false, 186970053056063630417606513179868732017123008843118963586548160497455494138⟩ = true := by
  decide +kernel

theorem o_row_448 : oGrid.row evalE 448 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_448_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_448_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_448_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_448_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_448_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_448_2000).1 (bothLoop_sound b_448_2400).1))))))

theorem n_row_448 : nGrid.row evalE 448 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_448_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_448_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_448_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_448_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_448_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_448_2000).2 (bothLoop_sound b_448_2400).2))))))

theorem b_449_0 : bothSeg evalE (oGrid.idx 449) (oGrid.dm 449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 449) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 792972991955099467319617796349226233302762633046013828331402794914704363952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_449_400 : bothSeg evalE (oGrid.idx 449) (oGrid.dm 449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 449) oGrid.kl oGrid.kr 400 400 ⟨false, 792972991955099467319617796349226233302762633046013828331402794914704363952⟩ ⟨false, 0⟩ ⟨false, 1251818807574876214303535854873249323792237254641291779916507594954168276326⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_449_800 : bothSeg evalE (oGrid.idx 449) (oGrid.dm 449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 449) oGrid.kl oGrid.kr 400 800 ⟨false, 1251818807574876214303535854873249323792237254641291779916507594954168276326⟩ ⟨false, 0⟩ ⟨false, 1365968299528780671118295693785948071761888426055303173065029419029557488726⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_449_1200 : bothSeg evalE (oGrid.idx 449) (oGrid.dm 449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 449) oGrid.kl oGrid.kr 400 1200 ⟨false, 1365968299528780671118295693785948071761888426055303173065029419029557488726⟩ ⟨false, 0⟩ ⟨false, 1285231101458586426267901210781145558243760235863723220007579252382074073504⟩ ⟨false, 81446357319563982808324088182760387270886202350503854951883609577689607556⟩ = true := by
  decide +kernel

theorem b_449_1600 : bothSeg evalE (oGrid.idx 449) (oGrid.dm 449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 449) oGrid.kl oGrid.kr 400 1600 ⟨false, 1285231101458586426267901210781145558243760235863723220007579252382074073504⟩ ⟨false, 81446357319563982808324088182760387270886202350503854951883609577689607556⟩ ⟨false, 1185917122409815185861161394867131274847182263897853222164091580068388396512⟩ ⟨false, 180760336368335223215063904096774670667464174316373852795371281891375284548⟩ = true := by
  decide +kernel

theorem b_449_2000 : bothSeg evalE (oGrid.idx 449) (oGrid.dm 449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 449) oGrid.kl oGrid.kr 400 2000 ⟨false, 1185917122409815185861161394867131274847182263897853222164091580068388396512⟩ ⟨false, 180760336368335223215063904096774670667464174316373852795371281891375284548⟩ ⟨false, 1188597637512653431033934587862650754961046829048350300110795491794704615762⟩ ⟨false, 186814524038188646335045268020037868563873024327796867229722477403457262904⟩ = true := by
  decide +kernel

theorem b_449_2400 : bothLoop evalE (oGrid.idx 449) (oGrid.dm 449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 449) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1188597637512653431033934587862650754961046829048350300110795491794704615762⟩ ⟨false, 186814524038188646335045268020037868563873024327796867229722477403457262904⟩ = true := by
  decide +kernel

theorem o_row_449 : oGrid.row evalE 449 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_449_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_449_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_449_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_449_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_449_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_449_2000).1 (bothLoop_sound b_449_2400).1))))))

theorem n_row_449 : nGrid.row evalE 449 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_449_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_449_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_449_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_449_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_449_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_449_2000).2 (bothLoop_sound b_449_2400).2))))))

theorem b_450_0 : bothSeg evalE (oGrid.idx 450) (oGrid.dm 450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 450) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 788697321626124117266844108049019619132666597252045455422647338904002297268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_450_400 : bothSeg evalE (oGrid.idx 450) (oGrid.dm 450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 450) oGrid.kl oGrid.kr 400 400 ⟨false, 788697321626124117266844108049019619132666597252045455422647338904002297268⟩ ⟨false, 0⟩ ⟨false, 1244788377219606478929566765549584639878661712732732091269560504935849941458⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_450_800 : bothSeg evalE (oGrid.idx 450) (oGrid.dm 450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 450) oGrid.kl oGrid.kr 400 800 ⟨false, 1244788377219606478929566765549584639878661712732732091269560504935849941458⟩ ⟨false, 0⟩ ⟨false, 1357812473076799458188713273257603253816739499265112229285436059121262372948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_450_1200 : bothSeg evalE (oGrid.idx 450) (oGrid.dm 450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 450) oGrid.kl oGrid.kr 400 1200 ⟨false, 1357812473076799458188713273257603253816739499265112229285436059121262372948⟩ ⟨false, 0⟩ ⟨false, 1276650338601897554633496274425079153715847077556470151843412767563195870384⟩ ⟨false, 81869946983157996131594380834596249495615858253660481032358408871723081596⟩ = true := by
  decide +kernel

theorem b_450_1600 : bothSeg evalE (oGrid.idx 450) (oGrid.dm 450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 450) oGrid.kl oGrid.kr 400 1600 ⟨false, 1276650338601897554633496274425079153715847077556470151843412767563195870384⟩ ⟨false, 81869946983157996131594380834596249495615858253660481032358408871723081596⟩ ⟨false, 1177866772647843487640779638880018141823738972882452448277797650204342888030⟩ ⟨false, 180653512937212063124311016379657261387723962927678184597973526230576063950⟩ = true := by
  decide +kernel

theorem b_450_2000 : bothSeg evalE (oGrid.idx 450) (oGrid.dm 450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 450) oGrid.kl oGrid.kr 400 2000 ⟨false, 1177866772647843487640779638880018141823738972882452448277797650204342888030⟩ ⟨false, 180653512937212063124311016379657261387723962927678184597973526230576063950⟩ ⟨false, 1180616446854944955586734999729018463489690310806206491127080215926370279180⟩ ⟨false, 186657213693221422352549610231036242530757201778944267735796929695601758230⟩ = true := by
  decide +kernel

theorem b_450_2400 : bothLoop evalE (oGrid.idx 450) (oGrid.dm 450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 450) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1180616446854944955586734999729018463489690310806206491127080215926370279180⟩ ⟨false, 186657213693221422352549610231036242530757201778944267735796929695601758230⟩ = true := by
  decide +kernel

theorem o_row_450 : oGrid.row evalE 450 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_450_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_450_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_450_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_450_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_450_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_450_2000).1 (bothLoop_sound b_450_2400).1))))))

theorem n_row_450 : nGrid.row evalE 450 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_450_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_450_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_450_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_450_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_450_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_450_2000).2 (bothLoop_sound b_450_2400).2))))))

theorem b_451_0 : bothSeg evalE (oGrid.idx 451) (oGrid.dm 451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 451) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 784437348877586253926877798175537348889298920632544445332814163559986166804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_451_400 : bothSeg evalE (oGrid.idx 451) (oGrid.dm 451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 451) oGrid.kl oGrid.kr 400 400 ⟨false, 784437348877586253926877798175537348889298920632544445332814163559986166804⟩ ⟨false, 0⟩ ⟨false, 1237783796050912383407308402760477161921220750294371947313792937380904478284⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_451_800 : bothSeg evalE (oGrid.idx 451) (oGrid.dm 451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 451) oGrid.kl oGrid.kr 400 800 ⟨false, 1237783796050912383407308402760477161921220750294371947313792937380904478284⟩ ⟨false, 0⟩ ⟨false, 1349685627500552458468395763835845320630141162165391740023396243863303883766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_451_1200 : bothSeg evalE (oGrid.idx 451) (oGrid.dm 451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 451) oGrid.kl oGrid.kr 400 1200 ⟨false, 1349685627500552458468395763835845320630141162165391740023396243863303883766⟩ ⟨false, 0⟩ ⟨false, 1268103933829847253601083741575417628268876113751764751959087299976383496192⟩ ⟨false, 82290920541529062915571980688728356058765432741379153730253533463074452094⟩ = true := by
  decide +kernel

theorem b_451_1600 : bothSeg evalE (oGrid.idx 451) (oGrid.dm 451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 451) oGrid.kl oGrid.kr 400 1600 ⟨false, 1268103933829847253601083741575417628268876113751764751959087299976383496192⟩ ⟨false, 82290920541529062915571980688728356058765432741379153730253533463074452094⟩ ⟨false, 1169848968314640282074110284234232674379129649809012128372179772578016244080⟩ ⟨false, 180545886056736034442545438029913309948511896684131777317161060861441704206⟩ = true := by
  decide +kernel

theorem b_451_2000 : bothSeg evalE (oGrid.idx 451) (oGrid.dm 451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 451) oGrid.kl oGrid.kr 400 2000 ⟨false, 1169848968314640282074110284234232674379129649809012128372179772578016244080⟩ ⟨false, 180545886056736034442545438029913309948511896684131777317161060861441704206⟩ ⟨false, 1172669406554601178763458307654876412976450060156095420034480751540757100704⟩ ⟨false, 186497159194251943808017056612473150565236277883674255679362538144368059946⟩ = true := by
  decide +kernel

theorem b_451_2400 : bothLoop evalE (oGrid.idx 451) (oGrid.dm 451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 451) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1172669406554601178763458307654876412976450060156095420034480751540757100704⟩ ⟨false, 186497159194251943808017056612473150565236277883674255679362538144368059946⟩ = true := by
  decide +kernel

theorem o_row_451 : oGrid.row evalE 451 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_451_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_451_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_451_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_451_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_451_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_451_2000).1 (bothLoop_sound b_451_2400).1))))))

theorem n_row_451 : nGrid.row evalE 451 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_451_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_451_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_451_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_451_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_451_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_451_2000).2 (bothLoop_sound b_451_2400).2))))))

theorem b_452_0 : bothSeg evalE (oGrid.idx 452) (oGrid.dm 452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 452) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 780193033137139357967955233106683385889222490055607293022912086345223602790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_452_400 : bothSeg evalE (oGrid.idx 452) (oGrid.dm 452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 452) oGrid.kl oGrid.kr 400 400 ⟨false, 780193033137139357967955233106683385889222490055607293022912086345223602790⟩ ⟨false, 0⟩ ⟨false, 1230804985087147023643709109401243091148046647405059354249226155196264449208⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_452_800 : bothSeg evalE (oGrid.idx 452) (oGrid.dm 452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 452) oGrid.kl oGrid.kr 400 800 ⟨false, 1230804985087147023643709109401243091148046647405059354249226155196264449208⟩ ⟨false, 0⟩ ⟨false, 1341587441668122450582189064197090338681520905629349035789641065419371422804⟩ ⟨false, 2661441860824209500404999442685421269202353964149351889055865336105614⟩ = true := by
  decide +kernel

theorem b_452_1200 : bothSeg evalE (oGrid.idx 452) (oGrid.dm 452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 452) oGrid.kl oGrid.kr 400 1200 ⟨false, 1341587441668122450582189064197090338681520905629349035789641065419371422804⟩ ⟨false, 2661441860824209500404999442685421269202353964149351889055865336105614⟩ ⟨false, 1259591694006237457149903930876844081007666643497318080754050068809650534412⟩ ⟨false, 82710017990267022889401367347936266332171980350894264975288629340452292890⟩ = true := by
  decide +kernel

theorem b_452_1600 : bothSeg evalE (oGrid.idx 452) (oGrid.dm 452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 452) oGrid.kl oGrid.kr 400 1600 ⟨false, 1259591694006237457149903930876844081007666643497318080754050068809650534412⟩ ⟨false, 82710017990267022889401367347936266332171980350894264975288629340452292890⟩ ⟨false, 1161863690980888418423306829441716919215944451293432902818468300345437702086⟩ ⟨false, 180438021015616061615998468783063428123894172554779442910870397804665125216⟩ = true := by
  decide +kernel

theorem b_452_2000 : bothSeg evalE (oGrid.idx 452) (oGrid.dm 452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 452) oGrid.kl oGrid.kr 400 2000 ⟨false, 1161863690980888418423306829441716919215944451293432902818468300345437702086⟩ ⟨false, 180438021015616061615998468783063428123894172554779442910870397804665125216⟩ ⟨false, 1164756533107131194636273794187133829044910605813839567463098713428003525702⟩ ⟨false, 186336012231040022316967981461329637083917553080962784166944463100503704552⟩ = true := by
  decide +kernel

theorem b_452_2400 : bothLoop evalE (oGrid.idx 452) (oGrid.dm 452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 452) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1164756533107131194636273794187133829044910605813839567463098713428003525702⟩ ⟨false, 186336012231040022316967981461329637083917553080962784166944463100503704552⟩ = true := by
  decide +kernel

theorem o_row_452 : oGrid.row evalE 452 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_452_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_452_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_452_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_452_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_452_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_452_2000).1 (bothLoop_sound b_452_2400).1))))))

theorem n_row_452 : nGrid.row evalE 452 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_452_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_452_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_452_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_452_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_452_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_452_2000).2 (bothLoop_sound b_452_2400).2))))))

theorem b_453_0 : bothSeg evalE (oGrid.idx 453) (oGrid.dm 453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 453) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 775964332659355183579411195359288812861775369298757751450659449135992158806⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_453_400 : bothSeg evalE (oGrid.idx 453) (oGrid.dm 453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 453) oGrid.kl oGrid.kr 400 400 ⟨false, 775964332659355183579411195359288812861775369298757751450659449135992158806⟩ ⟨false, 0⟩ ⟨false, 1223851877816585971984278314880090835203005105144284920269995364018183222240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_453_800 : bothSeg evalE (oGrid.idx 453) (oGrid.dm 453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 453) oGrid.kl oGrid.kr 400 800 ⟨false, 1223851877816585971984278314880090835203005105144284920269995364018183222240⟩ ⟨false, 0⟩ ⟨false, 1333517898649553593003847203596826322628381714648115142444146596723331710910⟩ ⟨false, 8803150935590936934676123900844216441197149528422720970420806141108344⟩ = true := by
  decide +kernel

theorem b_453_1200 : bothSeg evalE (oGrid.idx 453) (oGrid.dm 453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 453) oGrid.kl oGrid.kr 400 1200 ⟨false, 1333517898649553593003847203596826322628381714648115142444146596723331710910⟩ ⟨false, 8803150935590936934676123900844216441197149528422720970420806141108344⟩ ⟨false, 1251113620669468392539509302089213543319797239543223671788022583606834401448⟩ ⟨false, 83127044627886463116402144808331907309739047224718958871872927840782727648⟩ = true := by
  decide +kernel

theorem b_453_1600 : bothSeg evalE (oGrid.idx 453) (oGrid.dm 453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 453) oGrid.kl oGrid.kr 400 1600 ⟨false, 1251113620669468392539509302089213543319797239543223671788022583606834401448⟩ ⟨false, 83127044627886463116402144808331907309739047224718958871872927840782727648⟩ ⟨false, 1153910927992643446427434911425158266118012211961649698366238522850738808924⟩ ⟨false, 180329737304711409228476535472387184511524074806292932293656988596878320172⟩ = true := by
  decide +kernel

theorem b_453_2000 : bothSeg evalE (oGrid.idx 453) (oGrid.dm 453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 453) oGrid.kl oGrid.kr 400 2000 ⟨false, 1153910927992643446427434911425158266118012211961649698366238522850738808924⟩ ⟨false, 180329737304711409228476535472387184511524074806292932293656988596878320172⟩ ⟨false, 1156877778625228307468649031152814306770619251486691033765488526330953625418⟩ ⟨false, 186175118564272964941034132664311400945881975490502367123765596682769427362⟩ = true := by
  decide +kernel

theorem b_453_2400 : bothLoop evalE (oGrid.idx 453) (oGrid.dm 453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 453) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1156877778625228307468649031152814306770619251486691033765488526330953625418⟩ ⟨false, 186175118564272964941034132664311400945881975490502367123765596682769427362⟩ = true := by
  decide +kernel

theorem o_row_453 : oGrid.row evalE 453 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_453_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_453_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_453_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_453_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_453_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_453_2000).1 (bothLoop_sound b_453_2400).1))))))

theorem n_row_453 : nGrid.row evalE 453 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_453_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_453_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_453_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_453_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_453_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_453_2000).2 (bothLoop_sound b_453_2400).2))))))

theorem b_454_0 : bothSeg evalE (oGrid.idx 454) (oGrid.dm 454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 454) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 771751203694237715819143520309640391646054455154462748480952751802482957554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_454_400 : bothSeg evalE (oGrid.idx 454) (oGrid.dm 454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 454) oGrid.kl oGrid.kr 400 400 ⟨false, 771751203694237715819143520309640391646054455154462748480952751802482957554⟩ ⟨false, 0⟩ ⟨false, 1216924412969538663809240600818077194345995025540162657867802799651200138192⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_454_800 : bothSeg evalE (oGrid.idx 454) (oGrid.dm 454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 454) oGrid.kl oGrid.kr 400 800 ⟨false, 1216924412969538663809240600818077194345995025540162657867802799651200138192⟩ ⟨false, 0⟩ ⟨false, 1325476778894460371046200109664882059418512544164448892298150833946810399966⟩ ⟨false, 18619638540848725558098193992729663622542102278203994485994476263754752⟩ = true := by
  decide +kernel

theorem b_454_1200 : bothSeg evalE (oGrid.idx 454) (oGrid.dm 454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 454) oGrid.kl oGrid.kr 400 1200 ⟨false, 1325476778894460371046200109664882059418512544164448892298150833946810399966⟩ ⟨false, 18619638540848725558098193992729663622542102278203994485994476263754752⟩ ⟨false, 1242669611139902624624894792996371978129342714230247674765399984046469473068⟩ ⟨false, 83542209862313751450842835459931615227089124727930582541486588330990201400⟩ = true := by
  decide +kernel

theorem b_454_1600 : bothSeg evalE (oGrid.idx 454) (oGrid.dm 454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 454) oGrid.kl oGrid.kr 400 1600 ⟨false, 1242669611139902624624894792996371978129342714230247674765399984046469473068⟩ ⟨false, 83542209862313751450842835459931615227089124727930582541486588330990201400⟩ ⟨false, 1145990591976554281227032173978205087234822536983589461549059969100336015022⟩ ⟨false, 180221229025662094848705454478098506121609301974588795757826603277123659446⟩ = true := by
  decide +kernel

theorem b_454_2000 : bothSeg evalE (oGrid.idx 454) (oGrid.dm 454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 454) oGrid.kl oGrid.kr 400 2000 ⟨false, 1145990591976554281227032173978205087234822536983589461549059969100336015022⟩ ⟨false, 180221229025662094848705454478098506121609301974588795757826603277123659446⟩ ⟨false, 1149033047805396864015207014691709886259397494954569930171637745130425710728⟩ ⟨false, 186014008135376489321835531644358127254842510408084681513289448200935020416⟩ = true := by
  decide +kernel

theorem b_454_2400 : bothLoop evalE (oGrid.idx 454) (oGrid.dm 454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 454) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1149033047805396864015207014691709886259397494954569930171637745130425710728⟩ ⟨false, 186014008135376489321835531644358127254842510408084681513289448200935020416⟩ = true := by
  decide +kernel

theorem o_row_454 : oGrid.row evalE 454 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_454_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_454_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_454_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_454_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_454_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_454_2000).1 (bothLoop_sound b_454_2400).1))))))

theorem n_row_454 : nGrid.row evalE 454 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_454_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_454_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_454_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_454_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_454_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_454_2000).2 (bothLoop_sound b_454_2400).2))))))

theorem b_455_0 : bothSeg evalE (oGrid.idx 455) (oGrid.dm 455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 455) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 767553598959071820258230285524294842344531231031863495155513356042114650028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_455_400 : bothSeg evalE (oGrid.idx 455) (oGrid.dm 455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 455) oGrid.kl oGrid.kr 400 400 ⟨false, 767553598959071820258230285524294842344531231031863495155513356042114650028⟩ ⟨false, 0⟩ ⟨false, 1210022484050033907623358501409776701774731157868119441513731922848616154178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_455_800 : bothSeg evalE (oGrid.idx 455) (oGrid.dm 455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 455) oGrid.kl oGrid.kr 400 800 ⟨false, 1210022484050033907623358501409776701774731157868119441513731922848616154178⟩ ⟨false, 0⟩ ⟨false, 1317463682746625923208445352629734975223387788933123506852901035704258657506⟩ ⟨false, 32307529319806534600765944944331066134565795733723158627600773785949786⟩ = true := by
  decide +kernel

theorem b_455_1200 : bothSeg evalE (oGrid.idx 455) (oGrid.dm 455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 455) oGrid.kl oGrid.kr 400 1200 ⟨false, 1317463682746625923208445352629734975223387788933123506852901035704258657506⟩ ⟨false, 32307529319806534600765944944331066134565795733723158627600773785949786⟩ ⟨false, 1234259524466632924549050984958271542963274804048622533677641683773562119352⟩ ⟨false, 83955575518543257138873148297114016162373320311775122926525752555509887646⟩ = true := by
  decide +kernel

theorem b_455_1600 : bothSeg evalE (oGrid.idx 455) (oGrid.dm 455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 455) oGrid.kl oGrid.kr 400 1600 ⟨false, 1234259524466632924549050984958271542963274804048622533677641683773562119352⟩ ⟨false, 83955575518543257138873148297114016162373320311775122926525752555509887646⟩ ⟨false, 1138102549866566504705564517271027466970280362577290671154973275344091835444⟩ ⟨false, 180112550118609676982359615984358092155367761783106985449194160984980171554⟩ = true := by
  decide +kernel

theorem b_455_2000 : bothSeg evalE (oGrid.idx 455) (oGrid.dm 455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 455) oGrid.kl oGrid.kr 400 2000 ⟨false, 1138102549866566504705564517271027466970280362577290671154973275344091835444⟩ ⟨false, 180112550118609676982359615984358092155367761783106985449194160984980171554⟩ ⟨false, 1141222234529809568492988954506080521672714233421446651236997394803407632054⟩ ⟨false, 185853440519176622397030514976858778863229249190585039063882242287744625988⟩ = true := by
  decide +kernel

theorem b_455_2400 : bothLoop evalE (oGrid.idx 455) (oGrid.dm 455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 455) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1141222234529809568492988954506080521672714233421446651236997394803407632054⟩ ⟨false, 185853440519176622397030514976858778863229249190585039063882242287744625988⟩ = true := by
  decide +kernel

theorem o_row_455 : oGrid.row evalE 455 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_455_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_455_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_455_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_455_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_455_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_455_2000).1 (bothLoop_sound b_455_2400).1))))))

theorem n_row_455 : nGrid.row evalE 455 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_455_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_455_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_455_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_455_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_455_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_455_2000).2 (bothLoop_sound b_455_2400).2))))))

theorem o_blk_432 : allFrom (fun j => oGrid.row evalE j) 432 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 432) o_row_432 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 433) o_row_433 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 434) o_row_434 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 435) o_row_435 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 436) o_row_436 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 437) o_row_437 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 438) o_row_438 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 439) o_row_439 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 440) o_row_440 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 441) o_row_441 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 442) o_row_442 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 443) o_row_443 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 444) o_row_444 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 445) o_row_445 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 446) o_row_446 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 447) o_row_447 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 448) o_row_448 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 449) o_row_449 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 450) o_row_450 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 451) o_row_451 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 452) o_row_452 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 453) o_row_453 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 454) o_row_454 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 455) o_row_455 (allFrom_zero (fun j => oGrid.row evalE j) 456)))))))))))))))))))))))))

theorem n_blk_432 : allFrom (fun j => nGrid.row evalE j) 432 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 432) n_row_432 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 433) n_row_433 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 434) n_row_434 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 435) n_row_435 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 436) n_row_436 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 437) n_row_437 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 438) n_row_438 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 439) n_row_439 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 440) n_row_440 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 441) n_row_441 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 442) n_row_442 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 443) n_row_443 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 444) n_row_444 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 445) n_row_445 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 446) n_row_446 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 447) n_row_447 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 448) n_row_448 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 449) n_row_449 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 450) n_row_450 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 451) n_row_451 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 452) n_row_452 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 453) n_row_453 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 454) n_row_454 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 455) n_row_455 (allFrom_zero (fun j => nGrid.row evalE j) 456)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
