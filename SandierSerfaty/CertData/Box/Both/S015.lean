/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 15 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `360`–`383`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_360_0 : bothSeg evalE (oGrid.idx 360) (oGrid.dm 360) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 360) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1241756988020517785629999441790837719646720962780979924657354776298649406368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_360_400 : bothSeg evalE (oGrid.idx 360) (oGrid.dm 360) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 360) oGrid.kl oGrid.kr 400 400 ⟨false, 1241756988020517785629999441790837719646720962780979924657354776298649406368⟩ ⟨false, 0⟩ ⟨false, 1989274860550815686113196670143379485180177278148531537225465327921940460972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_360_800 : bothSeg evalE (oGrid.idx 360) (oGrid.dm 360) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 360) oGrid.kl oGrid.kr 400 800 ⟨false, 1989274860550815686113196670143379485180177278148531537225465327921940460972⟩ ⟨false, 0⟩ ⟨false, 2221938456366044877241841865415360812938889993247516352777817155296527884758⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_360_1200 : bothSeg evalE (oGrid.idx 360) (oGrid.dm 360) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 360) oGrid.kl oGrid.kr 400 1200 ⟨false, 2221938456366044877241841865415360812938889993247516352777817155296527884758⟩ ⟨false, 0⟩ ⟨false, 2191625327500324573712051606928598263793458386812648124260314360889581207272⟩ ⟨false, 40214359224652784008628523277211181917533423018979587251852414535211906530⟩ = true := by
  decide +kernel

theorem b_360_1600 : bothSeg evalE (oGrid.idx 360) (oGrid.dm 360) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 360) oGrid.kl oGrid.kr 400 1600 ⟨false, 2191625327500324573712051606928598263793458386812648124260314360889581207272⟩ ⟨false, 40214359224652784008628523277211181917533423018979587251852414535211906530⟩ ⟨false, 2043152505734079989772123521396265829030908165901212071877461420953805591806⟩ ⟨false, 188687180990897367948556608809543616680083643930415639634705354470987521996⟩ = true := by
  decide +kernel

theorem b_360_2000 : bothSeg evalE (oGrid.idx 360) (oGrid.dm 360) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 360) oGrid.kl oGrid.kr 400 2000 ⟨false, 2043152505734079989772123521396265829030908165901212071877461420953805591806⟩ ⟨false, 188687180990897367948556608809543616680083643930415639634705354470987521996⟩ ⟨false, 2042645797161972143613016927255429158142440538278226494749081608052057489960⟩ ⟨false, 196438328932246781073574900138913010041140048441267909890099940965915795674⟩ = true := by
  decide +kernel

theorem b_360_2400 : bothLoop evalE (oGrid.idx 360) (oGrid.dm 360) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 360) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2042645797161972143613016927255429158142440538278226494749081608052057489960⟩ ⟨false, 196438328932246781073574900138913010041140048441267909890099940965915795674⟩ = true := by
  decide +kernel

theorem o_row_360 : oGrid.row evalE 360 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_360_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_360_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_360_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_360_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_360_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_360_2000).1 (bothLoop_sound b_360_2400).1))))))

theorem n_row_360 : nGrid.row evalE 360 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_360_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_360_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_360_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_360_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_360_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_360_2000).2 (bothLoop_sound b_360_2400).2))))))

theorem b_361_0 : bothSeg evalE (oGrid.idx 361) (oGrid.dm 361) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 361) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1235903636773326286875903968684178826336571170803395630229858952987204688170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_361_400 : bothSeg evalE (oGrid.idx 361) (oGrid.dm 361) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 361) oGrid.kl oGrid.kr 400 400 ⟨false, 1235903636773326286875903968684178826336571170803395630229858952987204688170⟩ ⟨false, 0⟩ ⟨false, 1979667954702586627033047180022365936577951522788682102401895551933344276584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_361_800 : bothSeg evalE (oGrid.idx 361) (oGrid.dm 361) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 361) oGrid.kl oGrid.kr 400 800 ⟨false, 1979667954702586627033047180022365936577951522788682102401895551933344276584⟩ ⟨false, 0⟩ ⟨false, 2210778392295789291854830895079419863122811133246241834898117080271397613394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_361_1200 : bothSeg evalE (oGrid.idx 361) (oGrid.dm 361) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 361) oGrid.kl oGrid.kr 400 1200 ⟨false, 2210778392295789291854830895079419863122811133246241834898117080271397613394⟩ ⟨false, 0⟩ ⟨false, 2179913393051677534100611868359237923860386404069904139286554279403358685556⟩ ⟨false, 40568407101425325913283190481321168237373667707824030118457601755416684572⟩ = true := by
  decide +kernel

theorem b_361_1600 : bothSeg evalE (oGrid.idx 361) (oGrid.dm 361) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 361) oGrid.kl oGrid.kr 400 1600 ⟨false, 2179913393051677534100611868359237923860386404069904139286554279403358685556⟩ ⟨false, 40568407101425325913283190481321168237373667707824030118457601755416684572⟩ ⟨false, 2031863503013261956613480685256339348262710746254451011123613709568458585138⟩ ⟨false, 188618297139840903400414373584219743835049325523277158281398171590316784990⟩ = true := by
  decide +kernel

theorem b_361_2000 : bothSeg evalE (oGrid.idx 361) (oGrid.dm 361) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 361) oGrid.kl oGrid.kr 400 2000 ⟨false, 2031863503013261956613480685256339348262710746254451011123613709568458585138⟩ ⟨false, 188618297139840903400414373584219743835049325523277158281398171590316784990⟩ ⟨false, 2031423395839350765376884750362837597467791468185951045905510829317850436046⟩ ⟨false, 196317873553004142099348656866798160555608262812059768569686618323839328358⟩ = true := by
  decide +kernel

theorem b_361_2400 : bothLoop evalE (oGrid.idx 361) (oGrid.dm 361) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 361) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2031423395839350765376884750362837597467791468185951045905510829317850436046⟩ ⟨false, 196317873553004142099348656866798160555608262812059768569686618323839328358⟩ = true := by
  decide +kernel

theorem o_row_361 : oGrid.row evalE 361 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_361_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_361_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_361_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_361_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_361_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_361_2000).1 (bothLoop_sound b_361_2400).1))))))

theorem n_row_361 : nGrid.row evalE 361 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_361_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_361_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_361_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_361_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_361_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_361_2000).2 (bothLoop_sound b_361_2400).2))))))

theorem b_362_0 : bothSeg evalE (oGrid.idx 362) (oGrid.dm 362) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 362) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1230070141321517214084154366315731656817321337389613217592095655752506797254⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_362_400 : bothSeg evalE (oGrid.idx 362) (oGrid.dm 362) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 362) oGrid.kl oGrid.kr 400 400 ⟨false, 1230070141321517214084154366315731656817321337389613217592095655752506797254⟩ ⟨false, 0⟩ ⟨false, 1970093224162526039745085239723701088911457522120494429036563895091682440264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_362_800 : bothSeg evalE (oGrid.idx 362) (oGrid.dm 362) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 362) oGrid.kl oGrid.kr 400 800 ⟨false, 1970093224162526039745085239723701088911457522120494429036563895091682440264⟩ ⟨false, 0⟩ ⟨false, 2199655784543132208349051106770349037326590644598574052954226264437472048300⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_362_1200 : bothSeg evalE (oGrid.idx 362) (oGrid.dm 362) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 362) oGrid.kl oGrid.kr 400 1200 ⟨false, 2199655784543132208349051106770349037326590644598574052954226264437472048300⟩ ⟨false, 0⟩ ⟨false, 2168234451852824756034919982496876568197677457239577642475345117176933753690⟩ ⟨false, 40929281970598419443533480241827023507012072595534185221797459230808429784⟩ = true := by
  decide +kernel

theorem b_362_1600 : bothSeg evalE (oGrid.idx 362) (oGrid.dm 362) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 362) oGrid.kl oGrid.kr 400 1600 ⟨false, 2168234451852824756034919982496876568197677457239577642475345117176933753690⟩ ⟨false, 40929281970598419443533480241827023507012072595534185221797459230808429784⟩ ⟨false, 2020614672083135477655113756414840341226569125991617561689006189377500647102⟩ ⟨false, 188549061740287697823339706323863250478120403843494266008136387030241536372⟩ = true := by
  decide +kernel

theorem b_362_2000 : bothSeg evalE (oGrid.idx 362) (oGrid.dm 362) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 362) oGrid.kl oGrid.kr 400 2000 ⟨false, 2020614672083135477655113756414840341226569125991617561689006189377500647102⟩ ⟨false, 188549061740287697823339706323863250478120403843494266008136387030241536372⟩ ⟨false, 2020238999824232162982348720017809974906213490487589137645179419331011510174⟩ ⟨false, 196199219705996974448316078824058842338002294513526226867434036804491543632⟩ = true := by
  decide +kernel

theorem b_362_2400 : bothLoop evalE (oGrid.idx 362) (oGrid.dm 362) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 362) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2020238999824232162982348720017809974906213490487589137645179419331011510174⟩ ⟨false, 196199219705996974448316078824058842338002294513526226867434036804491543632⟩ = true := by
  decide +kernel

theorem o_row_362 : oGrid.row evalE 362 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_362_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_362_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_362_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_362_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_362_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_362_2000).1 (bothLoop_sound b_362_2400).1))))))

theorem n_row_362 : nGrid.row evalE 362 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_362_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_362_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_362_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_362_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_362_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_362_2000).2 (bothLoop_sound b_362_2400).2))))))

theorem b_363_0 : bothSeg evalE (oGrid.idx 363) (oGrid.dm 363) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 363) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1224256452053686612308237554790969216526655149063901794825534334722674060952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_363_400 : bothSeg evalE (oGrid.idx 363) (oGrid.dm 363) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 363) oGrid.kl oGrid.kr 400 400 ⟨false, 1224256452053686612308237554790969216526655149063901794825534334722674060952⟩ ⟨false, 0⟩ ⟨false, 1960550605027435711140784302923119075296224660764431665861903359666884128788⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_363_800 : bothSeg evalE (oGrid.idx 363) (oGrid.dm 363) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 363) oGrid.kl oGrid.kr 400 800 ⟨false, 1960550605027435711140784302923119075296224660764431665861903359666884128788⟩ ⟨false, 0⟩ ⟨false, 2188570613477332822644982255901103060424807200975656138835076884510816726212⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_363_1200 : bothSeg evalE (oGrid.idx 363) (oGrid.dm 363) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 363) oGrid.kl oGrid.kr 400 1200 ⟨false, 2188570613477332822644982255901103060424807200975656138835076884510816726212⟩ ⟨false, 0⟩ ⟨false, 2156588434582286174973534511004244221957191121680856132236507245872555769466⟩ ⟨false, 41296799637924504138324102387928513587374897802023219678039472972528923588⟩ = true := by
  decide +kernel

theorem b_363_1600 : bothSeg evalE (oGrid.idx 363) (oGrid.dm 363) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 363) oGrid.kl oGrid.kr 400 1600 ⟨false, 2156588434582286174973534511004244221957191121680856132236507245872555769466⟩ ⟨false, 41296799637924504138324102387928513587374897802023219678039472972528923588⟩ ⟨false, 2009405962745382923547046372235045534446015861451605416033922928759974869194⟩ ⟨false, 188479271474827755564812241157127201098550158031273935880623790085109823860⟩ = true := by
  decide +kernel

theorem b_363_2000 : bothSeg evalE (oGrid.idx 363) (oGrid.dm 363) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 363) oGrid.kl oGrid.kr 400 2000 ⟨false, 2009405962745382923547046372235045534446015861451605416033922928759974869194⟩ ⟨false, 188479271474827755564812241157127201098550158031273935880623790085109823860⟩ ⟨false, 2009092616180364599023719707345691665127823009556045078305840490994876633622⟩ ⟨false, 196082167715541739268817530438535704278427411570958548141506893305321151678⟩ = true := by
  decide +kernel

theorem b_363_2400 : bothLoop evalE (oGrid.idx 363) (oGrid.dm 363) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 363) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2009092616180364599023719707345691665127823009556045078305840490994876633622⟩ ⟨false, 196082167715541739268817530438535704278427411570958548141506893305321151678⟩ = true := by
  decide +kernel

theorem o_row_363 : oGrid.row evalE 363 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_363_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_363_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_363_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_363_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_363_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_363_2000).1 (bothLoop_sound b_363_2400).1))))))

theorem n_row_363 : nGrid.row evalE 363 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_363_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_363_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_363_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_363_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_363_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_363_2000).2 (bothLoop_sound b_363_2400).2))))))

theorem b_364_0 : bothSeg evalE (oGrid.idx 364) (oGrid.dm 364) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 364) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1218462519118570742745348570571078926414983821129978625653934093141159443782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_364_400 : bothSeg evalE (oGrid.idx 364) (oGrid.dm 364) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 364) oGrid.kl oGrid.kr 400 400 ⟨false, 1218462519118570742745348570571078926414983821129978625653934093141159443782⟩ ⟨false, 0⟩ ⟨false, 1951040007178054120849453327542992200417659157899596297854536244337551542318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_364_800 : bothSeg evalE (oGrid.idx 364) (oGrid.dm 364) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 364) oGrid.kl oGrid.kr 400 800 ⟨false, 1951040007178054120849453327542992200417659157899596297854536244337551542318⟩ ⟨false, 0⟩ ⟨false, 2177522683248799762375600166684158450196112395467800463004248303693514358528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_364_1200 : bothSeg evalE (oGrid.idx 364) (oGrid.dm 364) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 364) oGrid.kl oGrid.kr 400 1200 ⟨false, 2177522683248799762375600166684158450196112395467800463004248303693514358528⟩ ⟨false, 0⟩ ⟨false, 2144975428547680706902920075523294405949992374649885081083147224310053719490⟩ ⟨false, 41670558287502171615095945693694082473964459920283039805830105452450713576⟩ = true := by
  decide +kernel

theorem b_364_1600 : bothSeg evalE (oGrid.idx 364) (oGrid.dm 364) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 364) oGrid.kl oGrid.kr 400 1600 ⟨false, 2144975428547680706902920075523294405949992374649885081083147224310053719490⟩ ⟨false, 41670558287502171615095945693694082473964459920283039805830105452450713576⟩ ⟨false, 1998237216925582466645469759226177967068555337076568960485181460715703552482⟩ ⟨false, 188408769909600411872546261990810521355401497493599160403795869046800880584⟩ = true := by
  decide +kernel

theorem b_364_2000 : bothSeg evalE (oGrid.idx 364) (oGrid.dm 364) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 364) oGrid.kl oGrid.kr 400 2000 ⟨false, 1998237216925582466645469759226177967068555337076568960485181460715703552482⟩ ⟨false, 188408769909600411872546261990810521355401497493599160403795869046800880584⟩ ⟨false, 1997984113942094651915949365297386743175054866129066046095263246535218753628⟩ ⟨false, 195966885400692935523150945442987120574058001819371959290893726387317999468⟩ = true := by
  decide +kernel

theorem b_364_2400 : bothLoop evalE (oGrid.idx 364) (oGrid.dm 364) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 364) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1997984113942094651915949365297386743175054866129066046095263246535218753628⟩ ⟨false, 195966885400692935523150945442987120574058001819371959290893726387317999468⟩ = true := by
  decide +kernel

theorem o_row_364 : oGrid.row evalE 364 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_364_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_364_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_364_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_364_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_364_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_364_2000).1 (bothLoop_sound b_364_2400).1))))))

theorem n_row_364 : nGrid.row evalE 364 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_364_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_364_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_364_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_364_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_364_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_364_2000).2 (bothLoop_sound b_364_2400).2))))))

theorem b_365_0 : bothSeg evalE (oGrid.idx 365) (oGrid.dm 365) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 365) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1212688290140903809877087359333843537528285042216805821391849245072202455400⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_365_400 : bothSeg evalE (oGrid.idx 365) (oGrid.dm 365) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 365) oGrid.kl oGrid.kr 400 400 ⟨false, 1212688290140903809877087359333843537528285042216805821391849245072202455400⟩ ⟨false, 0⟩ ⟨false, 1941561370876170350887197485760357795559202010174444884457234772723730362080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_365_800 : bothSeg evalE (oGrid.idx 365) (oGrid.dm 365) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 365) oGrid.kl oGrid.kr 400 800 ⟨false, 1941561370876170350887197485760357795559202010174444884457234772723730362080⟩ ⟨false, 0⟩ ⟨false, 2166511955958607139914447620531483683968731139712713153386366355772316633586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_365_1200 : bothSeg evalE (oGrid.idx 365) (oGrid.dm 365) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 365) oGrid.kl oGrid.kr 400 1200 ⟨false, 2166511955958607139914447620531483683968731139712713153386366355772316633586⟩ ⟨false, 0⟩ ⟨false, 2133395446610542389962912135295895215120141138296876243375251574752958227598⟩ ⟨false, 42050891172589770918592482085928961723585038253623897606062363032164737158⟩ = true := by
  decide +kernel

theorem b_365_1600 : bothSeg evalE (oGrid.idx 365) (oGrid.dm 365) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 365) oGrid.kl oGrid.kr 400 1600 ⟨false, 2133395446610542389962912135295895215120141138296876243375251574752958227598⟩ ⟨false, 42050891172589770918592482085928961723585038253623897606062363032164737158⟩ ⟨false, 1987108434572032320980552855158910531354027845159566612784293604734159633050⟩ ⟨false, 188337903211099839900951762222913645489698331390933528197020333050963331706⟩ = true := by
  decide +kernel

theorem b_365_2000 : bothSeg evalE (oGrid.idx 365) (oGrid.dm 365) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 365) oGrid.kl oGrid.kr 400 2000 ⟨false, 1987108434572032320980552855158910531354027845159566612784293604734159633050⟩ ⟨false, 188337903211099839900951762222913645489698331390933528197020333050963331706⟩ ⟨false, 1986913529317332355172966705383294710895159411972921078612507279700862019140⟩ ⟨false, 195853064965613742820935792158027235148100672099456058672891778039499402496⟩ = true := by
  decide +kernel

theorem b_365_2400 : bothLoop evalE (oGrid.idx 365) (oGrid.dm 365) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 365) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1986913529317332355172966705383294710895159411972921078612507279700862019140⟩ ⟨false, 195853064965613742820935792158027235148100672099456058672891778039499402496⟩ = true := by
  decide +kernel

theorem o_row_365 : oGrid.row evalE 365 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_365_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_365_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_365_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_365_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_365_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_365_2000).1 (bothLoop_sound b_365_2400).1))))))

theorem n_row_365 : nGrid.row evalE 365 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_365_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_365_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_365_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_365_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_365_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_365_2000).2 (bothLoop_sound b_365_2400).2))))))

theorem b_366_0 : bothSeg evalE (oGrid.idx 366) (oGrid.dm 366) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 366) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1206933709556589373211440441882138262091065896018940495758989789064700305106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_366_400 : bothSeg evalE (oGrid.idx 366) (oGrid.dm 366) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 366) oGrid.kl oGrid.kr 400 400 ⟨false, 1206933709556589373211440441882138262091065896018940495758989789064700305106⟩ ⟨false, 0⟩ ⟨false, 1932114600090445168520460499812800642596175186177872817828658173664480060826⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_366_800 : bothSeg evalE (oGrid.idx 366) (oGrid.dm 366) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 366) oGrid.kl oGrid.kr 400 800 ⟨false, 1932114600090445168520460499812800642596175186177872817828658173664480060826⟩ ⟨false, 0⟩ ⟨false, 2155538387883647588866917024189001660910191062660067331327686297188664809028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_366_1200 : bothSeg evalE (oGrid.idx 366) (oGrid.dm 366) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 366) oGrid.kl oGrid.kr 400 1200 ⟨false, 2155538387883647588866917024189001660910191062660067331327686297188664809028⟩ ⟨false, 0⟩ ⟨false, 2121848658599473887445755819408781978935422353601295391702044217520818294880⟩ ⟨false, 42437231381762647224914268443373875197216446141377006305812965512541878824⟩ = true := by
  decide +kernel

theorem b_366_1600 : bothSeg evalE (oGrid.idx 366) (oGrid.dm 366) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 366) oGrid.kl oGrid.kr 400 1600 ⟨false, 2121848658599473887445755819408781978935422353601295391702044217520818294880⟩ ⟨false, 42437231381762647224914268443373875197216446141377006305812965512541878824⟩ ⟨false, 1976019608062051997422803716708667007947657550140361688268337692345399546490⟩ ⟨false, 188266281919184537247866371143488846184981249602310709739519490687960627214⟩ = true := by
  decide +kernel

theorem b_366_2000 : bothSeg evalE (oGrid.idx 366) (oGrid.dm 366) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 366) oGrid.kl oGrid.kr 400 2000 ⟨false, 1976019608062051997422803716708667007947657550140361688268337692345399546490⟩ ⟨false, 188266281919184537247866371143488846184981249602310709739519490687960627214⟩ ⟨false, 1975880892225268686845402850411170468942447305864171842788235951418878252978⟩ ⟨false, 195740050614593431319566008103285205485778054422175879944540172737690765172⟩ = true := by
  decide +kernel

theorem b_366_2400 : bothLoop evalE (oGrid.idx 366) (oGrid.dm 366) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 366) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1975880892225268686845402850411170468942447305864171842788235951418878252978⟩ ⟨false, 195740050614593431319566008103285205485778054422175879944540172737690765172⟩ = true := by
  decide +kernel

theorem o_row_366 : oGrid.row evalE 366 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_366_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_366_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_366_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_366_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_366_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_366_2000).1 (bothLoop_sound b_366_2400).1))))))

theorem n_row_366 : nGrid.row evalE 366 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_366_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_366_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_366_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_366_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_366_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_366_2000).2 (bothLoop_sound b_366_2400).2))))))

theorem b_367_0 : bothSeg evalE (oGrid.idx 367) (oGrid.dm 367) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 367) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1201198726438461595261467451135097591768019935840105927456990586406394764912⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_367_400 : bothSeg evalE (oGrid.idx 367) (oGrid.dm 367) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 367) oGrid.kl oGrid.kr 400 400 ⟨false, 1201198726438461595261467451135097591768019935840105927456990586406394764912⟩ ⟨false, 0⟩ ⟨false, 1922699625841903423926856215941587705491011398579070341506105276177940238346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_367_800 : bothSeg evalE (oGrid.idx 367) (oGrid.dm 367) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 367) oGrid.kl oGrid.kr 400 800 ⟨false, 1922699625841903423926856215941587705491011398579070341506105276177940238346⟩ ⟨false, 0⟩ ⟨false, 2144601843658157144424634905229222911602542479893436381695323214614027104984⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_367_1200 : bothSeg evalE (oGrid.idx 367) (oGrid.dm 367) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 367) oGrid.kl oGrid.kr 400 1200 ⟨false, 2144601843658157144424634905229222911602542479893436381695323214614027104984⟩ ⟨false, 0⟩ ⟨false, 2110334899155198467300939290103254174077261782760349688977477458784762406368⟩ ⟨false, 42829814520460947094785235081752784709617110080036404952609297675469116030⟩ = true := by
  decide +kernel

theorem b_367_1600 : bothSeg evalE (oGrid.idx 367) (oGrid.dm 367) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 367) oGrid.kl oGrid.kr 400 1600 ⟨false, 2110334899155198467300939290103254174077261782760349688977477458784762406368⟩ ⟨false, 42829814520460947094785235081752784709617110080036404952609297675469116030⟩ ⟨false, 1964970421795498709746441958150876804976471987250227133587202083852181305280⟩ ⟨false, 188194291880160704649282567034130153810406905590158960342884672608050217118⟩ = true := by
  decide +kernel

theorem b_367_2000 : bothSeg evalE (oGrid.idx 367) (oGrid.dm 367) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 367) oGrid.kl oGrid.kr 400 2000 ⟨false, 1964970421795498709746441958150876804976471987250227133587202083852181305280⟩ ⟨false, 188194291880160704649282567034130153810406905590158960342884672608050217118⟩ ⟨false, 1964885939119156779682171135467310938523869595750722319050019045199272426348⟩ ⟨false, 195629260616856822901067571469900245633746828893741780851523357419268582170⟩ = true := by
  decide +kernel

theorem b_367_2400 : bothLoop evalE (oGrid.idx 367) (oGrid.dm 367) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 367) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1964885939119156779682171135467310938523869595750722319050019045199272426348⟩ ⟨false, 195629260616856822901067571469900245633746828893741780851523357419268582170⟩ = true := by
  decide +kernel

theorem o_row_367 : oGrid.row evalE 367 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_367_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_367_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_367_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_367_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_367_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_367_2000).1 (bothLoop_sound b_367_2400).1))))))

theorem n_row_367 : nGrid.row evalE 367 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_367_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_367_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_367_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_367_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_367_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_367_2000).2 (bothLoop_sound b_367_2400).2))))))

theorem b_368_0 : bothSeg evalE (oGrid.idx 368) (oGrid.dm 368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 368) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1195483289002925585539256446863562443809954665150528771872854507877301007954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_368_400 : bothSeg evalE (oGrid.idx 368) (oGrid.dm 368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 368) oGrid.kl oGrid.kr 400 400 ⟨false, 1195483289002925585539256446863562443809954665150528771872854507877301007954⟩ ⟨false, 0⟩ ⟨false, 1913316357208896734041398909961491400055845489832474622136006795850120082282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_368_800 : bothSeg evalE (oGrid.idx 368) (oGrid.dm 368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 368) oGrid.kl oGrid.kr 400 800 ⟨false, 1913316357208896734041398909961491400055845489832474622136006795850120082282⟩ ⟨false, 0⟩ ⟨false, 2133702212121457329875792253421339423465949836917954000400352841910573293268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_368_1200 : bothSeg evalE (oGrid.idx 368) (oGrid.dm 368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 368) oGrid.kl oGrid.kr 400 1200 ⟨false, 2133702212121457329875792253421339423465949836917954000400352841910573293268⟩ ⟨false, 0⟩ ⟨false, 2098854344177803016120554597929696311841775326054976416940763457706048783426⟩ ⟨false, 43228438080644828643579120165011901011693951994699950848390251059047591022⟩ = true := by
  decide +kernel

theorem b_368_1600 : bothSeg evalE (oGrid.idx 368) (oGrid.dm 368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 368) oGrid.kl oGrid.kr 400 1600 ⟨false, 2098854344177803016120554597929696311841775326054976416940763457706048783426⟩ ⟨false, 43228438080644828643579120165011901011693951994699950848390251059047591022⟩ ⟨false, 1953960970470420148982163917094889010125051706918716144241445526045974108882⟩ ⟨false, 188121811788027695781969800999819202728417571130960223547708182719122265566⟩ = true := by
  decide +kernel

theorem b_368_2000 : bothSeg evalE (oGrid.idx 368) (oGrid.dm 368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 368) oGrid.kl oGrid.kr 400 2000 ⟨false, 1953960970470420148982163917094889010125051706918716144241445526045974108882⟩ ⟨false, 188121811788027695781969800999819202728417571130960223547708182719122265566⟩ ⟨false, 1953928803185193236821534857075663809424648457037432666386989792541577379506⟩ ⟨false, 195519924213083135285667480218165202018293582606213986690873930221224810198⟩ = true := by
  decide +kernel

theorem b_368_2400 : bothLoop evalE (oGrid.idx 368) (oGrid.dm 368) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 368) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1953928803185193236821534857075663809424648457037432666386989792541577379506⟩ ⟨false, 195519924213083135285667480218165202018293582606213986690873930221224810198⟩ = true := by
  decide +kernel

theorem o_row_368 : oGrid.row evalE 368 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_368_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_368_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_368_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_368_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_368_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_368_2000).1 (bothLoop_sound b_368_2400).1))))))

theorem n_row_368 : nGrid.row evalE 368 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_368_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_368_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_368_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_368_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_368_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_368_2000).2 (bothLoop_sound b_368_2400).2))))))

theorem b_369_0 : bothSeg evalE (oGrid.idx 369) (oGrid.dm 369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 369) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1189787351086102117094307046463058957172145086777694471333678853457324981720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_369_400 : bothSeg evalE (oGrid.idx 369) (oGrid.dm 369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 369) oGrid.kl oGrid.kr 400 400 ⟨false, 1189787351086102117094307046463058957172145086777694471333678853457324981720⟩ ⟨false, 0⟩ ⟨false, 1903964746663157921531886391112091696915333540539426419781495193282341787840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_369_800 : bothSeg evalE (oGrid.idx 369) (oGrid.dm 369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 369) oGrid.kl oGrid.kr 400 800 ⟨false, 1903964746663157921531886391112091696915333540539426419781495193282341787840⟩ ⟨false, 0⟩ ⟨false, 2122839504447194254836810446315151478020845231761726524784727184739347826576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_369_1200 : bothSeg evalE (oGrid.idx 369) (oGrid.dm 369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 369) oGrid.kl oGrid.kr 400 1200 ⟨false, 2122839504447194254836810446315151478020845231761726524784727184739347826576⟩ ⟨false, 0⟩ ⟨false, 2087406952990532132321100298871413306983845895640860785645756532935671561460⟩ ⟨false, 43633178183947196133990046374407556268066536903067427260903829051690297934⟩ = true := by
  decide +kernel

theorem b_369_1600 : bothSeg evalE (oGrid.idx 369) (oGrid.dm 369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 369) oGrid.kl oGrid.kr 400 1600 ⟨false, 2087406952990532132321100298871413306983845895640860785645756532935671561460⟩ ⟨false, 43633178183947196133990046374407556268066536903067427260903829051690297934⟩ ⟨false, 1942991020980620194387191091767926274538778569619190319509020014708215278030⟩ ⟨false, 188049110193859134067899253477894588713133862924737893397640347279146581364⟩ = true := by
  decide +kernel

theorem b_369_2000 : bothSeg evalE (oGrid.idx 369) (oGrid.dm 369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 369) oGrid.kl oGrid.kr 400 2000 ⟨false, 1942991020980620194387191091767926274538778569619190319509020014708215278030⟩ ⟨false, 188049110193859134067899253477894588713133862924737893397640347279146581364⟩ ⟨false, 1943009271442623704137798556038122533945703782626811308340557612748706946226⟩ ⟨false, 195411854680282324876670260753218891183566338288765816156151075447611612454⟩ = true := by
  decide +kernel

theorem b_369_2400 : bothLoop evalE (oGrid.idx 369) (oGrid.dm 369) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 369) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1943009271442623704137798556038122533945703782626811308340557612748706946226⟩ ⟨false, 195411854680282324876670260753218891183566338288765816156151075447611612454⟩ = true := by
  decide +kernel

theorem o_row_369 : oGrid.row evalE 369 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_369_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_369_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_369_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_369_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_369_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_369_2000).1 (bothLoop_sound b_369_2400).1))))))

theorem n_row_369 : nGrid.row evalE 369 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_369_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_369_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_369_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_369_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_369_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_369_2000).2 (bothLoop_sound b_369_2400).2))))))

theorem b_370_0 : bothSeg evalE (oGrid.idx 370) (oGrid.dm 370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 370) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1184110860231934255317445014880123765535707751851764546313753341603690393624⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_370_400 : bothSeg evalE (oGrid.idx 370) (oGrid.dm 370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 370) oGrid.kl oGrid.kr 400 400 ⟨false, 1184110860231934255317445014880123765535707751851764546313753341603690393624⟩ ⟨false, 0⟩ ⟨false, 1894644691623556021082314335023463775639471037857922509419906411429475958488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_370_800 : bothSeg evalE (oGrid.idx 370) (oGrid.dm 370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 370) oGrid.kl oGrid.kr 400 800 ⟨false, 1894644691623556021082314335023463775639471037857922509419906411429475958488⟩ ⟨false, 0⟩ ⟨false, 2112013589220239968983752216109943939156126731315164443029407639200952515820⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_370_1200 : bothSeg evalE (oGrid.idx 370) (oGrid.dm 370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 370) oGrid.kl oGrid.kr 400 1200 ⟨false, 2112013589220239968983752216109943939156126731315164443029407639200952515820⟩ ⟨false, 0⟩ ⟨false, 2075992618056514532763024781486109415540551682051267584688283323274530888976⟩ ⟨false, 44043589801945774287990001916073824001723036671820900835168733492404990940⟩ = true := by
  decide +kernel

theorem b_370_1600 : bothSeg evalE (oGrid.idx 370) (oGrid.dm 370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 370) oGrid.kl oGrid.kr 400 1600 ⟨false, 2075992618056514532763024781486109415540551682051267584688283323274530888976⟩ ⟨false, 44043589801945774287990001916073824001723036671820900835168733492404990940⟩ ⟨false, 1932060517223024238122111596329998207831708488818655690248724287170471728848⟩ ⟨false, 187975690635436068928903187072185031710566229904432795274727769596464151068⟩ = true := by
  decide +kernel

theorem b_370_2000 : bothSeg evalE (oGrid.idx 370) (oGrid.dm 370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 370) oGrid.kl oGrid.kr 400 2000 ⟨false, 1932060517223024238122111596329998207831708488818655690248724287170471728848⟩ ⟨false, 187975690635436068928903187072185031710566229904432795274727769596464151068⟩ ⟨false, 1932127357216982586560523132969447330815060221294717219019660874549298539700⟩ ⟨false, 195305614383069495322962232122695246694365249109355283485605975369517147288⟩ = true := by
  decide +kernel

theorem b_370_2400 : bothLoop evalE (oGrid.idx 370) (oGrid.dm 370) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 370) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1932127357216982586560523132969447330815060221294717219019660874549298539700⟩ ⟨false, 195305614383069495322962232122695246694365249109355283485605975369517147288⟩ = true := by
  decide +kernel

theorem o_row_370 : oGrid.row evalE 370 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_370_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_370_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_370_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_370_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_370_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_370_2000).1 (bothLoop_sound b_370_2400).1))))))

theorem n_row_370 : nGrid.row evalE 370 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_370_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_370_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_370_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_370_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_370_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_370_2000).2 (bothLoop_sound b_370_2400).2))))))

theorem b_371_0 : bothSeg evalE (oGrid.idx 371) (oGrid.dm 371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 371) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1178453765138974707134935764069905739587127968932271288045929337314321446678⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_371_400 : bothSeg evalE (oGrid.idx 371) (oGrid.dm 371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 371) oGrid.kl oGrid.kr 400 400 ⟨false, 1178453765138974707134935764069905739587127968932271288045929337314321446678⟩ ⟨false, 0⟩ ⟨false, 1885356133800492707049471738904574207208808759419316006570796984107877761992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_371_800 : bothSeg evalE (oGrid.idx 371) (oGrid.dm 371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 371) oGrid.kl oGrid.kr 400 800 ⟨false, 1885356133800492707049471738904574207208808759419316006570796984107877761992⟩ ⟨false, 0⟩ ⟨false, 2101224291154232998302823501610383715011112856854895609957543374715106597502⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_371_1200 : bothSeg evalE (oGrid.idx 371) (oGrid.dm 371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 371) oGrid.kl oGrid.kr 400 1200 ⟨false, 2101224291154232998302823501610383715011112856854895609957543374715106597502⟩ ⟨false, 0⟩ ⟨false, 2064611740300539628396782240682526879376762066431109763038551985000470421244⟩ ⟨false, 44459197274123837481608981833636994472298291666056246571725947016565914376⟩ = true := by
  decide +kernel

theorem b_371_1600 : bothSeg evalE (oGrid.idx 371) (oGrid.dm 371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 371) oGrid.kl oGrid.kr 400 1600 ⟨false, 2064611740300539628396782240682526879376762066431109763038551985000470421244⟩ ⟨false, 44459197274123837481608981833636994472298291666056246571725947016565914376⟩ ⟨false, 1921169538912093881807332335933977811375393743407196355373999063889477386036⟩ ⟨false, 187901398662569584071058886582186062473666614689969654236278868127558949584⟩ = true := by
  decide +kernel

theorem b_371_2000 : bothSeg evalE (oGrid.idx 371) (oGrid.dm 371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 371) oGrid.kl oGrid.kr 400 2000 ⟨false, 1921169538912093881807332335933977811375393743407196355373999063889477386036⟩ ⟨false, 187901398662569584071058886582186062473666614689969654236278868127558949584⟩ ⟨false, 1921283191932904403379276364481887399896268798688163789148124346457130973608⟩ ⟨false, 195199823760905195739249464099887578461214424681139582802885926988324299072⟩ = true := by
  decide +kernel

theorem b_371_2400 : bothLoop evalE (oGrid.idx 371) (oGrid.dm 371) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 371) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1921283191932904403379276364481887399896268798688163789148124346457130973608⟩ ⟨false, 195199823760905195739249464099887578461214424681139582802885926988324299072⟩ = true := by
  decide +kernel

theorem o_row_371 : oGrid.row evalE 371 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_371_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_371_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_371_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_371_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_371_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_371_2000).1 (bothLoop_sound b_371_2400).1))))))

theorem n_row_371 : nGrid.row evalE 371 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_371_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_371_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_371_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_371_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_371_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_371_2000).2 (bothLoop_sound b_371_2400).2))))))

theorem b_372_0 : bothSeg evalE (oGrid.idx 372) (oGrid.dm 372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 372) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1172816012442539723634265039087271806934075879707546227224139439804393670170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_372_400 : bothSeg evalE (oGrid.idx 372) (oGrid.dm 372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 372) oGrid.kl oGrid.kr 400 400 ⟨false, 1172816012442539723634265039087271806934075879707546227224139439804393670170⟩ ⟨false, 0⟩ ⟨false, 1876098975126320626411245667086229127300710132153419794293850962584081950938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_372_800 : bothSeg evalE (oGrid.idx 372) (oGrid.dm 372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 372) oGrid.kl oGrid.kr 400 800 ⟨false, 1876098975126320626411245667086229127300710132153419794293850962584081950938⟩ ⟨false, 0⟩ ⟨false, 2090471652559906029760749716243935036296669510743649082916988886015940913510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_372_1200 : bothSeg evalE (oGrid.idx 372) (oGrid.dm 372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 372) oGrid.kl oGrid.kr 400 1200 ⟨false, 2090471652559906029760749716243935036296669510743649082916988886015940913510⟩ ⟨false, 0⟩ ⟨false, 2053264249234595236649497455265628086752192206790242567627063989602216823020⟩ ⟨false, 44880195141924889150693101088092128229840210788658023181465089910842758292⟩ = true := by
  decide +kernel

theorem b_372_1600 : bothSeg evalE (oGrid.idx 372) (oGrid.dm 372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 372) oGrid.kl oGrid.kr 400 1600 ⟨false, 2053264249234595236649497455265628086752192206790242567627063989602216823020⟩ ⟨false, 44880195141924889150693101088092128229840210788658023181465089910842758292⟩ ⟨false, 1910317887114245269034358125765947837855297133300296694397604643423131480780⟩ ⟨false, 187826557262274856765832430587772377126735284278603896410924436089928100532⟩ = true := by
  decide +kernel

theorem b_372_2000 : bothSeg evalE (oGrid.idx 372) (oGrid.dm 372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 372) oGrid.kl oGrid.kr 400 2000 ⟨false, 1910317887114245269034358125765947837855297133300296694397604643423131480780⟩ ⟨false, 187826557262274856765832430587772377126735284278603896410924436089928100532⟩ ⟨false, 1910476575878538741465388109370492327173937927326844242401040204198678722390⟩ ⟨false, 195094835745482191899836725066250074464781019919127758578403984474835895440⟩ = true := by
  decide +kernel

theorem b_372_2400 : bothLoop evalE (oGrid.idx 372) (oGrid.dm 372) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 372) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1910476575878538741465388109370492327173937927326844242401040204198678722390⟩ ⟨false, 195094835745482191899836725066250074464781019919127758578403984474835895440⟩ = true := by
  decide +kernel

theorem o_row_372 : oGrid.row evalE 372 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_372_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_372_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_372_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_372_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_372_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_372_2000).1 (bothLoop_sound b_372_2400).1))))))

theorem n_row_372 : nGrid.row evalE 372 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_372_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_372_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_372_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_372_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_372_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_372_2000).2 (bothLoop_sound b_372_2400).2))))))

theorem b_373_0 : bothSeg evalE (oGrid.idx 373) (oGrid.dm 373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 373) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1167197554171787442548416051836139468107828575050758543783935782494539640360⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_373_400 : bothSeg evalE (oGrid.idx 373) (oGrid.dm 373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 373) oGrid.kl oGrid.kr 400 400 ⟨false, 1167197554171787442548416051836139468107828575050758543783935782494539640360⟩ ⟨false, 0⟩ ⟨false, 1866873161060682632539788492288738069233435187428738194518280773158912200954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_373_800 : bothSeg evalE (oGrid.idx 373) (oGrid.dm 373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 373) oGrid.kl oGrid.kr 400 800 ⟨false, 1866873161060682632539788492288738069233435187428738194518280773158912200954⟩ ⟨false, 0⟩ ⟨false, 2079755600455464984336292649696291268180533947843826659825604065738613313800⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_373_1200 : bothSeg evalE (oGrid.idx 373) (oGrid.dm 373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 373) oGrid.kl oGrid.kr 400 1200 ⟨false, 2079755600455464984336292649696291268180533947843826659825604065738613313800⟩ ⟨false, 0⟩ ⟨false, 2041950302761046936936151486418130523257343663712733290467371789983750111606⟩ ⟨false, 45306938504253185913696159609467281742233952850608464581483548338046095894⟩ = true := by
  decide +kernel

theorem b_373_1600 : bothSeg evalE (oGrid.idx 373) (oGrid.dm 373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 373) oGrid.kl oGrid.kr 400 1600 ⟨false, 2041950302761046936936151486418130523257343663712733290467371789983750111606⟩ ⟨false, 45306938504253185913696159609467281742233952850608464581483548338046095894⟩ ⟨false, 1899505547632583610978797232712204197503667275799672549374374552019103468470⟩ ⟨false, 187751693632716511871050413315393607495910340763669205674480786302692739030⟩ = true := by
  decide +kernel

theorem b_373_2000 : bothSeg evalE (oGrid.idx 373) (oGrid.dm 373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 373) oGrid.kl oGrid.kr 400 2000 ⟨false, 1899505547632583610978797232712204197503667275799672549374374552019103468470⟩ ⟨false, 187751693632716511871050413315393607495910340763669205674480786302692739030⟩ ⟨false, 1899707582922350758405377731132349679167738071370015283624078426074979093972⟩ ⟨false, 194992616047650267796435524049827311926432060408022000853661620611803990034⟩ = true := by
  decide +kernel

theorem b_373_2400 : bothLoop evalE (oGrid.idx 373) (oGrid.dm 373) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 373) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1899707582922350758405377731132349679167738071370015283624078426074979093972⟩ ⟨false, 194992616047650267796435524049827311926432060408022000853661620611803990034⟩ = true := by
  decide +kernel

theorem o_row_373 : oGrid.row evalE 373 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_373_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_373_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_373_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_373_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_373_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_373_2000).1 (bothLoop_sound b_373_2400).1))))))

theorem n_row_373 : nGrid.row evalE 373 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_373_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_373_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_373_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_373_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_373_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_373_2000).2 (bothLoop_sound b_373_2400).2))))))

theorem b_374_0 : bothSeg evalE (oGrid.idx 374) (oGrid.dm 374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 374) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1161598340661282070688515545724376954657987781756737385041486929484170261980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_374_400 : bothSeg evalE (oGrid.idx 374) (oGrid.dm 374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 374) oGrid.kl oGrid.kr 400 400 ⟨false, 1161598340661282070688515545724376954657987781756737385041486929484170261980⟩ ⟨false, 0⟩ ⟨false, 1857678602246941248741976820673493248762625765824479477269626860907832629510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_374_800 : bothSeg evalE (oGrid.idx 374) (oGrid.dm 374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 374) oGrid.kl oGrid.kr 400 800 ⟨false, 1857678602246941248741976820673493248762625765824479477269626860907832629510⟩ ⟨false, 0⟩ ⟨false, 2069075891799732880039000452780456909127569537560512494652310953527353720418⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_374_1200 : bothSeg evalE (oGrid.idx 374) (oGrid.dm 374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 374) oGrid.kl oGrid.kr 400 1200 ⟨false, 2069075891799732880039000452780456909127569537560512494652310953527353720418⟩ ⟨false, 0⟩ ⟨false, 2030669679761139533736295727582175212811191316742434473554278083197665244796⟩ ⟨false, 45738968640343959999381981521317365147766809369525957955824323184422762962⟩ = true := by
  decide +kernel

theorem b_374_1600 : bothSeg evalE (oGrid.idx 374) (oGrid.dm 374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 374) oGrid.kl oGrid.kr 400 1600 ⟨false, 2030669679761139533736295727582175212811191316742434473554278083197665244796⟩ ⟨false, 45738968640343959999381981521317365147766809369525957955824323184422762962⟩ ⟨false, 1888732162562668543242661685662100367895446942107387230086351437221838561652⟩ ⟨false, 187676485838814950493016023441392210063511184004573201423750969160249446106⟩ = true := by
  decide +kernel

theorem b_374_2000 : bothSeg evalE (oGrid.idx 374) (oGrid.dm 374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 374) oGrid.kl oGrid.kr 400 2000 ⟨false, 1888732162562668543242661685662100367895446942107387230086351437221838561652⟩ ⟨false, 187676485838814950493016023441392210063511184004573201423750969160249446106⟩ ⟨false, 1888975914742353391621834184378836007854857539214548780403903635831721709138⟩ ⟨false, 194891315441905686675096002165467053964310827519503560316296206642759783632⟩ = true := by
  decide +kernel

theorem b_374_2400 : bothLoop evalE (oGrid.idx 374) (oGrid.dm 374) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 374) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1888975914742353391621834184378836007854857539214548780403903635831721709138⟩ ⟨false, 194891315441905686675096002165467053964310827519503560316296206642759783632⟩ = true := by
  decide +kernel

theorem o_row_374 : oGrid.row evalE 374 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_374_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_374_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_374_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_374_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_374_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_374_2000).1 (bothLoop_sound b_374_2400).1))))))

theorem n_row_374 : nGrid.row evalE 374 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_374_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_374_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_374_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_374_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_374_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_374_2000).2 (bothLoop_sound b_374_2400).2))))))

theorem b_375_0 : bothSeg evalE (oGrid.idx 375) (oGrid.dm 375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 375) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1156018312427289466981487465872364264321579302855055783433058845722312859432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_375_400 : bothSeg evalE (oGrid.idx 375) (oGrid.dm 375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 375) oGrid.kl oGrid.kr 400 400 ⟨false, 1156018312427289466981487465872364264321579302855055783433058845722312859432⟩ ⟨false, 0⟩ ⟨false, 1848515228075059632424183283876741434987310136043081519695803089706572723158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_375_800 : bothSeg evalE (oGrid.idx 375) (oGrid.dm 375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 375) oGrid.kl oGrid.kr 400 800 ⟨false, 1848515228075059632424183283876741434987310136043081519695803089706572723158⟩ ⟨false, 0⟩ ⟨false, 2058432598354098603153313412544237479686756809084269334501584763381615644390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_375_1200 : bothSeg evalE (oGrid.idx 375) (oGrid.dm 375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 375) oGrid.kl oGrid.kr 400 1200 ⟨false, 2058432598354098603153313412544237479686756809084269334501584763381615644390⟩ ⟨false, 0⟩ ⟨false, 2019422692987742879199416350124477198463945583625807380515520770491418762140⟩ ⟨false, 46175694069468067501210712931639001379745062315012139635529376805727127144⟩ = true := by
  decide +kernel

theorem b_375_1600 : bothSeg evalE (oGrid.idx 375) (oGrid.dm 375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 375) oGrid.kl oGrid.kr 400 1600 ⟨false, 2019422692987742879199416350124477198463945583625807380515520770491418762140⟩ ⟨false, 46175694069468067501210712931639001379745062315012139635529376805727127144⟩ ⟨false, 1877997906864513528125296672286335701918840700055423897168245736727228200128⟩ ⟨false, 187600480192697418575330390769780497924849945885395622982804410569917689156⟩ = true := by
  decide +kernel

theorem b_375_2000 : bothSeg evalE (oGrid.idx 375) (oGrid.dm 375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 375) oGrid.kl oGrid.kr 400 2000 ⟨false, 1877997906864513528125296672286335701918840700055423897168245736727228200128⟩ ⟨false, 187600480192697418575330390769780497924849945885395622982804410569917689156⟩ ⟨false, 1878281743079507537386293529475812780637829554690711625141535225891273286840⟩ ⟨false, 194790292312009254071732611532543843694353421665561328360397003244987009542⟩ = true := by
  decide +kernel

theorem b_375_2400 : bothLoop evalE (oGrid.idx 375) (oGrid.dm 375) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 375) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1878281743079507537386293529475812780637829554690711625141535225891273286840⟩ ⟨false, 194790292312009254071732611532543843694353421665561328360397003244987009542⟩ = true := by
  decide +kernel

theorem o_row_375 : oGrid.row evalE 375 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_375_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_375_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_375_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_375_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_375_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_375_2000).1 (bothLoop_sound b_375_2400).1))))))

theorem n_row_375 : nGrid.row evalE 375 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_375_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_375_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_375_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_375_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_375_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_375_2000).2 (bothLoop_sound b_375_2400).2))))))

theorem b_376_0 : bothSeg evalE (oGrid.idx 376) (oGrid.dm 376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 376) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1150457433340567171581674986818985120160325627524127314634635645776514802712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_376_400 : bothSeg evalE (oGrid.idx 376) (oGrid.dm 376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 376) oGrid.kl oGrid.kr 400 400 ⟨false, 1150457433340567171581674986818985120160325627524127314634635645776514802712⟩ ⟨false, 0⟩ ⟨false, 1839382959824248280255929717249523751802208010359896921798449325710261406778⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_376_800 : bothSeg evalE (oGrid.idx 376) (oGrid.dm 376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 376) oGrid.kl oGrid.kr 400 800 ⟨false, 1839382959824248280255929717249523751802208010359896921798449325710261406778⟩ ⟨false, 0⟩ ⟨false, 2047825610387800929710764283064025523978659216451235900097855299519053662122⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_376_1200 : bothSeg evalE (oGrid.idx 376) (oGrid.dm 376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 376) oGrid.kl oGrid.kr 400 1200 ⟨false, 2047825610387800929710764283064025523978659216451235900097855299519053662122⟩ ⟨false, 0⟩ ⟨false, 2008209334296669949435051393459957332266487314688650012968789675588769621124⟩ ⟨false, 46617398837607304470365490845536991992350951321760479800697064422236931626⟩ = true := by
  decide +kernel

theorem b_376_1600 : bothSeg evalE (oGrid.idx 376) (oGrid.dm 376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 376) oGrid.kl oGrid.kr 400 1600 ⟨false, 2008209334296669949435051393459957332266487314688650012968789675588769621124⟩ ⟨false, 46617398837607304470365490845536991992350951321760479800697064422236931626⟩ ⟨false, 1867302594970922765253132819108640257990518315956539868646600202988303670926⟩ ⟨false, 187524138163354488652284065196854066268319950053870624122886537022702881824⟩ = true := by
  decide +kernel

theorem b_376_2000 : bothSeg evalE (oGrid.idx 376) (oGrid.dm 376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 376) oGrid.kl oGrid.kr 400 2000 ⟨false, 1867302594970922765253132819108640257990518315956539868646600202988303670926⟩ ⟨false, 187524138163354488652284065196854066268319950053870624122886537022702881824⟩ ⟨false, 1867624977214970592623902552718340839498314554425114287128714359364529338088⟩ ⟨false, 194691453836575129110198435392480554713677125725330036956599241888807068448⟩ = true := by
  decide +kernel

theorem b_376_2400 : bothLoop evalE (oGrid.idx 376) (oGrid.dm 376) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 376) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1867624977214970592623902552718340839498314554425114287128714359364529338088⟩ ⟨false, 194691453836575129110198435392480554713677125725330036956599241888807068448⟩ = true := by
  decide +kernel

theorem o_row_376 : oGrid.row evalE 376 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_376_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_376_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_376_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_376_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_376_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_376_2000).1 (bothLoop_sound b_376_2400).1))))))

theorem n_row_376 : nGrid.row evalE 376 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_376_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_376_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_376_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_376_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_376_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_376_2000).2 (bothLoop_sound b_376_2400).2))))))

theorem b_377_0 : bothSeg evalE (oGrid.idx 377) (oGrid.dm 377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 377) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1144915646564394474651650361137818811986029603986178681084372004965895867620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_377_400 : bothSeg evalE (oGrid.idx 377) (oGrid.dm 377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 377) oGrid.kl oGrid.kr 400 400 ⟨false, 1144915646564394474651650361137818811986029603986178681084372004965895867620⟩ ⟨false, 0⟩ ⟨false, 1830281725758988070871089282976342417504822116759492493353687050745920248972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_377_800 : bothSeg evalE (oGrid.idx 377) (oGrid.dm 377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 377) oGrid.kl oGrid.kr 400 800 ⟨false, 1830281725758988070871089282976342417504822116759492493353687050745920248972⟩ ⟨false, 0⟩ ⟨false, 2037254751355745426590079184985899337548984619406868006329229959498184482306⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_377_1200 : bothSeg evalE (oGrid.idx 377) (oGrid.dm 377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 377) oGrid.kl oGrid.kr 400 1200 ⟨false, 2037254751355745426590079184985899337548984619406868006329229959498184482306⟩ ⟨false, 0⟩ ⟨false, 1997029497422251736513365204029739020652318308430549996268839372181567835960⟩ ⟨false, 47063824400720187937144222482754913914479864639571673693673061122383738632⟩ = true := by
  decide +kernel

theorem b_377_1600 : bothSeg evalE (oGrid.idx 377) (oGrid.dm 377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 377) oGrid.kl oGrid.kr 400 1600 ⟨false, 1997029497422251736513365204029739020652318308430549996268839372181567835960⟩ ⟨false, 47063824400720187937144222482754913914479864639571673693673061122383738632⟩ ⟨false, 1856645886813014244044967179908386529956625649856322579074710348457668503138⟩ ⟨false, 187447435009957680405542246604107404610172523213799090887802084846283071454⟩ = true := by
  decide +kernel

theorem b_377_2000 : bothSeg evalE (oGrid.idx 377) (oGrid.dm 377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 377) oGrid.kl oGrid.kr 400 2000 ⟨false, 1856645886813014244044967179908386529956625649856322579074710348457668503138⟩ ⟨false, 187447435009957680405542246604107404610172523213799090887802084846283071454⟩ ⟨false, 1857005323891461121948981185195940004825350331421145422137623698653454006920⟩ ⟨false, 194593238090800185091757909396260917280867561451807913610604833242758991170⟩ = true := by
  decide +kernel

theorem b_377_2400 : bothLoop evalE (oGrid.idx 377) (oGrid.dm 377) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 377) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1857005323891461121948981185195940004825350331421145422137623698653454006920⟩ ⟨false, 194593238090800185091757909396260917280867561451807913610604833242758991170⟩ = true := by
  decide +kernel

theorem o_row_377 : oGrid.row evalE 377 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_377_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_377_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_377_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_377_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_377_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_377_2000).1 (bothLoop_sound b_377_2400).1))))))

theorem n_row_377 : nGrid.row evalE 377 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_377_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_377_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_377_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_377_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_377_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_377_2000).2 (bothLoop_sound b_377_2400).2))))))

theorem b_378_0 : bothSeg evalE (oGrid.idx 378) (oGrid.dm 378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 378) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1139392899092037558732800569408272739104727558207006160357726180655659643406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_378_400 : bothSeg evalE (oGrid.idx 378) (oGrid.dm 378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 378) oGrid.kl oGrid.kr 400 400 ⟨false, 1139392899092037558732800569408272739104727558207006160357726180655659643406⟩ ⟨false, 0⟩ ⟨false, 1821211442659639113059467780635330485847731693108316825013872369960905916250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_378_800 : bothSeg evalE (oGrid.idx 378) (oGrid.dm 378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 378) oGrid.kl oGrid.kr 400 800 ⟨false, 1821211442659639113059467780635330485847731693108316825013872369960905916250⟩ ⟨false, 0⟩ ⟨false, 2026720054349326612075616060734380104060484279427539896153122606923250474390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_378_1200 : bothSeg evalE (oGrid.idx 378) (oGrid.dm 378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 378) oGrid.kl oGrid.kr 400 1200 ⟨false, 2026720054349326612075616060734380104060484279427539896153122606923250474390⟩ ⟨false, 0⟩ ⟨false, 1985883329919584314381790928422841630634980180019016034281184078580194496288⟩ ⟨false, 47514755778271494951662703120736000019682732920985557304574038659111022112⟩ = true := by
  decide +kernel

theorem b_378_1600 : bothSeg evalE (oGrid.idx 378) (oGrid.dm 378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 378) oGrid.kl oGrid.kr 400 1600 ⟨false, 1985883329919584314381790928422841630634980180019016034281184078580194496288⟩ ⟨false, 47514755778271494951662703120736000019682732920985557304574038659111022112⟩ ⟨false, 1846027958479284208151234791638907820268704013339637616750572312256453201590⟩ ⟨false, 187370127218571601182218839904669810385958899600363974835185804982852316810⟩ = true := by
  decide +kernel

theorem b_378_2000 : bothSeg evalE (oGrid.idx 378) (oGrid.dm 378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 378) oGrid.kl oGrid.kr 400 2000 ⟨false, 1846027958479284208151234791638907820268704013339637616750572312256453201590⟩ ⟨false, 187370127218571601182218839904669810385958899600363974835185804982852316810⟩ ⟨false, 1846422991573340684282100540252905002908192243980867179590068257783545387174⟩ ⟨false, 194495355023385448813018207901552861269424643790335221480089169050023351080⟩ = true := by
  decide +kernel

theorem b_378_2400 : bothLoop evalE (oGrid.idx 378) (oGrid.dm 378) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 378) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1846422991573340684282100540252905002908192243980867179590068257783545387174⟩ ⟨false, 194495355023385448813018207901552861269424643790335221480089169050023351080⟩ = true := by
  decide +kernel

theorem o_row_378 : oGrid.row evalE 378 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_378_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_378_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_378_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_378_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_378_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_378_2000).1 (bothLoop_sound b_378_2400).1))))))

theorem n_row_378 : nGrid.row evalE 378 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_378_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_378_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_378_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_378_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_378_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_378_2000).2 (bothLoop_sound b_378_2400).2))))))

theorem b_379_0 : bothSeg evalE (oGrid.idx 379) (oGrid.dm 379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 379) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1133889145252961210806704805088935742788367592483246780146669648323869097520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_379_400 : bothSeg evalE (oGrid.idx 379) (oGrid.dm 379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 379) oGrid.kl oGrid.kr 400 400 ⟨false, 1133889145252961210806704805088935742788367592483246780146669648323869097520⟩ ⟨false, 0⟩ ⟨false, 1812172045216664671887624347166793789366322081373028778855148852797625543030⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_379_800 : bothSeg evalE (oGrid.idx 379) (oGrid.dm 379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 379) oGrid.kl oGrid.kr 400 800 ⟨false, 1812172045216664671887624347166793789366322081373028778855148852797625543030⟩ ⟨false, 0⟩ ⟨false, 2016221399814048696174414122163607663318398712138368100782184986220192582034⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_379_1200 : bothSeg evalE (oGrid.idx 379) (oGrid.dm 379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 379) oGrid.kl oGrid.kr 400 1200 ⟨false, 2016221399814048696174414122163607663318398712138368100782184986220192582034⟩ ⟨false, 0⟩ ⟨false, 1974771338448790789004462769735091981074566535830029988150252077323439404304⟩ ⟨false, 47969811498833411829503677522271880732739090185887540540574260361575141056⟩ = true := by
  decide +kernel

theorem b_379_1600 : bothSeg evalE (oGrid.idx 379) (oGrid.dm 379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 379) oGrid.kl oGrid.kr 400 1600 ⟨false, 1974771338448790789004462769735091981074566535830029988150252077323439404304⟩ ⟨false, 47969811498833411829503677522271880732739090185887540540574260361575141056⟩ ⟨false, 1835449147051661547966413744162250816385901116798285618807533854847828009814⟩ ⟨false, 187292002895962652867552703095113045421404509217631909883292482837186535546⟩ = true := by
  decide +kernel

theorem b_379_2000 : bothSeg evalE (oGrid.idx 379) (oGrid.dm 379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 379) oGrid.kl oGrid.kr 400 2000 ⟨false, 1835449147051661547966413744162250816385901116798285618807533854847828009814⟩ ⟨false, 187292002895962652867552703095113045421404509217631909883292482837186535546⟩ ⟨false, 1835878382906235759619083120116881161453132933518824826573797892432092374200⟩ ⟨false, 194399436467223309056607088408545144712454595733782155930231004359254455140⟩ = true := by
  decide +kernel

theorem b_379_2400 : bothLoop evalE (oGrid.idx 379) (oGrid.dm 379) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 379) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1835878382906235759619083120116881161453132933518824826573797892432092374200⟩ ⟨false, 194399436467223309056607088408545144712454595733782155930231004359254455140⟩ = true := by
  decide +kernel

theorem o_row_379 : oGrid.row evalE 379 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_379_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_379_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_379_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_379_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_379_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_379_2000).1 (bothLoop_sound b_379_2400).1))))))

theorem n_row_379 : nGrid.row evalE 379 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_379_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_379_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_379_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_379_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_379_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_379_2000).2 (bothLoop_sound b_379_2400).2))))))

theorem b_380_0 : bothSeg evalE (oGrid.idx 380) (oGrid.dm 380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 380) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1128404333918151022220071238666974018819981549949174543045832130411188103550⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_380_400 : bothSeg evalE (oGrid.idx 380) (oGrid.dm 380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 380) oGrid.kl oGrid.kr 400 400 ⟨false, 1128404333918151022220071238666974018819981549949174543045832130411188103550⟩ ⟨false, 0⟩ ⟨false, 1803163454652538028748337575983360967929681903471342044595370158769007606484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_380_800 : bothSeg evalE (oGrid.idx 380) (oGrid.dm 380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 380) oGrid.kl oGrid.kr 400 800 ⟨false, 1803163454652538028748337575983360967929681903471342044595370158769007606484⟩ ⟨false, 0⟩ ⟨false, 2005758634662351272308034461820991988934944351457452248419591584969559100240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_380_1200 : bothSeg evalE (oGrid.idx 380) (oGrid.dm 380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 380) oGrid.kl oGrid.kr 400 1200 ⟨false, 2005758634662351272308034461820991988934944351457452248419591584969559100240⟩ ⟨false, 0⟩ ⟨false, 1963693248668450202267222269003655891991318365685627227674174364613886666834⟩ ⟨false, 48429310396124815728710095527036489581261207302410479083464464550130724314⟩ = true := by
  decide +kernel

theorem b_380_1600 : bothSeg evalE (oGrid.idx 380) (oGrid.dm 380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 380) oGrid.kl oGrid.kr 400 1600 ⟨false, 1963693248668450202267222269003655891991318365685627227674174364613886666834⟩ ⟨false, 48429310396124815728710095527036489581261207302410479083464464550130724314⟩ ⟨false, 1824908899606305326316710217170108840544997435986748249968988925442381232808⟩ ⟨false, 187213659458269691679222147360583541027582137001289456788649903721636158340⟩ = true := by
  decide +kernel

theorem b_380_2000 : bothSeg evalE (oGrid.idx 380) (oGrid.dm 380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 380) oGrid.kl oGrid.kr 400 2000 ⟨false, 1824908899606305326316710217170108840544997435986748249968988925442381232808⟩ ⟨false, 187213659458269691679222147360583541027582137001289456788649903721636158340⟩ ⟨false, 1825370982579720045162704763199428495897509732884130551772120772939833156654⟩ ⟨false, 194304028952743705951371891273685699923163682817040709882913538936408748532⟩ = true := by
  decide +kernel

theorem b_380_2400 : bothLoop evalE (oGrid.idx 380) (oGrid.dm 380) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 380) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1825370982579720045162704763199428495897509732884130551772120772939833156654⟩ ⟨false, 194304028952743705951371891273685699923163682817040709882913538936408748532⟩ = true := by
  decide +kernel

theorem o_row_380 : oGrid.row evalE 380 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_380_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_380_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_380_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_380_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_380_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_380_2000).1 (bothLoop_sound b_380_2400).1))))))

theorem n_row_380 : nGrid.row evalE 380 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_380_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_380_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_380_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_380_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_380_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_380_2000).2 (bothLoop_sound b_380_2400).2))))))

theorem b_381_0 : bothSeg evalE (oGrid.idx 381) (oGrid.dm 381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 381) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1122938415512038084847616568095879705723426209003583947642669743145883267280⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_381_400 : bothSeg evalE (oGrid.idx 381) (oGrid.dm 381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 381) oGrid.kl oGrid.kr 400 400 ⟨false, 1122938415512038084847616568095879705723426209003583947642669743145883267280⟩ ⟨false, 0⟩ ⟨false, 1794185597139188468227509087791713052678882380103313453306152067331931655648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_381_800 : bothSeg evalE (oGrid.idx 381) (oGrid.dm 381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 381) oGrid.kl oGrid.kr 400 800 ⟨false, 1794185597139188468227509087791713052678882380103313453306152067331931655648⟩ ⟨false, 0⟩ ⟨false, 1995331754194678825918700492102477804226811550684297971705079680589689315900⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_381_1200 : bothSeg evalE (oGrid.idx 381) (oGrid.dm 381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 381) oGrid.kl oGrid.kr 400 1200 ⟨false, 1995331754194678825918700492102477804226811550684297971705079680589689315900⟩ ⟨false, 0⟩ ⟨false, 1952649086513826227604703341283186440570204201425227901397737158369114524296⟩ ⟨false, 48892681819718384985483829516169498777112927313084404416847058731046908240⟩ = true := by
  decide +kernel

theorem b_381_1600 : bothSeg evalE (oGrid.idx 381) (oGrid.dm 381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 381) oGrid.kl oGrid.kr 400 1600 ⟨false, 1952649086513826227604703341283186440570204201425227901397737158369114524296⟩ ⟨false, 48892681819718384985483829516169498777112927313084404416847058731046908240⟩ ⟨false, 1814407057247384025924498959037982795688739480546715235189100769780314473184⟩ ⟨false, 187134711086160586665688211761373143658577648191597070625483447319846959352⟩ = true := by
  decide +kernel

theorem b_381_2000 : bothSeg evalE (oGrid.idx 381) (oGrid.dm 381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 381) oGrid.kl oGrid.kr 400 2000 ⟨false, 1814407057247384025924498959037982795688739480546715235189100769780314473184⟩ ⟨false, 187134711086160586665688211761373143658577648191597070625483447319846959352⟩ ⟨false, 1814900712223361944585941945731680250577051966094349104847898307373578168446⟩ ⟨false, 194208704063129415318500814883666909835970056205589981480845601004117579050⟩ = true := by
  decide +kernel

theorem b_381_2400 : bothLoop evalE (oGrid.idx 381) (oGrid.dm 381) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 381) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1814900712223361944585941945731680250577051966094349104847898307373578168446⟩ ⟨false, 194208704063129415318500814883666909835970056205589981480845601004117579050⟩ = true := by
  decide +kernel

theorem o_row_381 : oGrid.row evalE 381 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_381_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_381_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_381_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_381_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_381_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_381_2000).1 (bothLoop_sound b_381_2400).1))))))

theorem n_row_381 : nGrid.row evalE 381 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_381_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_381_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_381_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_381_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_381_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_381_2000).2 (bothLoop_sound b_381_2400).2))))))

theorem b_382_0 : bothSeg evalE (oGrid.idx 382) (oGrid.dm 382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 382) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1117491339404773961691140741693997815739213537599763665012792816608579579880⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_382_400 : bothSeg evalE (oGrid.idx 382) (oGrid.dm 382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 382) oGrid.kl oGrid.kr 400 400 ⟨false, 1117491339404773961691140741693997815739213537599763665012792816608579579880⟩ ⟨false, 0⟩ ⟨false, 1785238385003496831290828336170540675982113043503726480169426819966769909096⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_382_800 : bothSeg evalE (oGrid.idx 382) (oGrid.dm 382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 382) oGrid.kl oGrid.kr 400 800 ⟨false, 1785238385003496831290828336170540675982113043503726480169426819966769909096⟩ ⟨false, 0⟩ ⟨false, 1984940675391706931839202901415842739289782775082122888588416941813469371734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_382_1200 : bothSeg evalE (oGrid.idx 382) (oGrid.dm 382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 382) oGrid.kl oGrid.kr 400 1200 ⟨false, 1984940675391706931839202901415842739289782775082122888588416941813469371734⟩ ⟨false, 0⟩ ⟨false, 1941639074194484449622179457564906613733329070456949398782076358848700620956⟩ ⟨false, 49359656607523796437393119208305012265222426411981419138320329008677237628⟩ = true := by
  decide +kernel

theorem b_382_1600 : bothSeg evalE (oGrid.idx 382) (oGrid.dm 382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 382) oGrid.kl oGrid.kr 400 1600 ⟨false, 1941639074194484449622179457564906613733329070456949398782076358848700620956⟩ ⟨false, 49359656607523796437393119208305012265222426411981419138320329008677237628⟩ ⟨false, 1803943638656559773858304078636865956420150452163236804692959344844131452532⟩ ⟨false, 187055092145448472201268498136345669578401044705694013227437343013246406052⟩ = true := by
  decide +kernel

theorem b_382_2000 : bothSeg evalE (oGrid.idx 382) (oGrid.dm 382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 382) oGrid.kl oGrid.kr 400 2000 ⟨false, 1803943638656559773858304078636865956420150452163236804692959344844131452532⟩ ⟨false, 187055092145448472201268498136345669578401044705694013227437343013246406052⟩ ⟨false, 1804467620926569479618824555685758937256161159046555223065771122645713791636⟩ ⟨false, 194115066960715678226161062207413021802579625742272765795516929236885719602⟩ = true := by
  decide +kernel

theorem b_382_2400 : bothLoop evalE (oGrid.idx 382) (oGrid.dm 382) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 382) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1804467620926569479618824555685758937256161159046555223065771122645713791636⟩ ⟨false, 194115066960715678226161062207413021802579625742272765795516929236885719602⟩ = true := by
  decide +kernel

theorem o_row_382 : oGrid.row evalE 382 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_382_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_382_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_382_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_382_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_382_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_382_2000).1 (bothLoop_sound b_382_2400).1))))))

theorem n_row_382 : nGrid.row evalE 382 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_382_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_382_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_382_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_382_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_382_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_382_2000).2 (bothLoop_sound b_382_2400).2))))))

theorem b_383_0 : bothSeg evalE (oGrid.idx 383) (oGrid.dm 383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 383) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1112063056210044036584928947889609927472675869969672794551504198489665907500⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_383_400 : bothSeg evalE (oGrid.idx 383) (oGrid.dm 383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 383) oGrid.kl oGrid.kr 400 400 ⟨false, 1112063056210044036584928947889609927472675869969672794551504198489665907500⟩ ⟨false, 0⟩ ⟨false, 1776321757022263176260641048601015425782279963857263810681160526665006390910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_383_800 : bothSeg evalE (oGrid.idx 383) (oGrid.dm 383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 383) oGrid.kl oGrid.kr 400 800 ⟨false, 1776321757022263176260641048601015425782279963857263810681160526665006390910⟩ ⟨false, 0⟩ ⟨false, 1974585260204013450759127065546329093475916576653290856106705360019402823310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_383_1200 : bothSeg evalE (oGrid.idx 383) (oGrid.dm 383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 383) oGrid.kl oGrid.kr 400 1200 ⟨false, 1974585260204013450759127065546329093475916576653290856106705360019402823310⟩ ⟨false, 0⟩ ⟨false, 1930663156408951562461934943759782862851180898745476548132674608675205367150⟩ ⟨false, 49830464968442752061461595760898606189487248383018407335924116204729613964⟩ = true := by
  decide +kernel

theorem b_383_1600 : bothSeg evalE (oGrid.idx 383) (oGrid.dm 383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 383) oGrid.kl oGrid.kr 400 1600 ⟨false, 1930663156408951562461934943759782862851180898745476548132674608675205367150⟩ ⟨false, 49830464968442752061461595760898606189487248383018407335924116204729613964⟩ ⟨false, 1793518438558451772015981685016256755305351064630659969933962303637703451746⟩ ⟨false, 186975182818942542507414854504424713735317082497834985534636421242231529368⟩ = true := by
  decide +kernel

theorem b_383_2000 : bothSeg evalE (oGrid.idx 383) (oGrid.dm 383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 383) oGrid.kl oGrid.kr 400 2000 ⟨false, 1793518438558451772015981685016256755305351064630659969933962303637703451746⟩ ⟨false, 186975182818942542507414854504424713735317082497834985534636421242231529368⟩ ⟨false, 1794071573692932852188521740644293996080551704776974323471993753116036731028⟩ ⟨false, 194021748549360384015216331595147911521003196333142855299667974057224771692⟩ = true := by
  decide +kernel

theorem b_383_2400 : bothLoop evalE (oGrid.idx 383) (oGrid.dm 383) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 383) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1794071573692932852188521740644293996080551704776974323471993753116036731028⟩ ⟨false, 194021748549360384015216331595147911521003196333142855299667974057224771692⟩ = true := by
  decide +kernel

theorem o_row_383 : oGrid.row evalE 383 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_383_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_383_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_383_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_383_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_383_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_383_2000).1 (bothLoop_sound b_383_2400).1))))))

theorem n_row_383 : nGrid.row evalE 383 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_383_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_383_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_383_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_383_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_383_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_383_2000).2 (bothLoop_sound b_383_2400).2))))))

theorem o_blk_360 : allFrom (fun j => oGrid.row evalE j) 360 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 360) o_row_360 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 361) o_row_361 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 362) o_row_362 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 363) o_row_363 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 364) o_row_364 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 365) o_row_365 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 366) o_row_366 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 367) o_row_367 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 368) o_row_368 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 369) o_row_369 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 370) o_row_370 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 371) o_row_371 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 372) o_row_372 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 373) o_row_373 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 374) o_row_374 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 375) o_row_375 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 376) o_row_376 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 377) o_row_377 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 378) o_row_378 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 379) o_row_379 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 380) o_row_380 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 381) o_row_381 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 382) o_row_382 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 383) o_row_383 (allFrom_zero (fun j => oGrid.row evalE j) 384)))))))))))))))))))))))))

theorem n_blk_360 : allFrom (fun j => nGrid.row evalE j) 360 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 360) n_row_360 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 361) n_row_361 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 362) n_row_362 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 363) n_row_363 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 364) n_row_364 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 365) n_row_365 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 366) n_row_366 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 367) n_row_367 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 368) n_row_368 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 369) n_row_369 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 370) n_row_370 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 371) n_row_371 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 372) n_row_372 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 373) n_row_373 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 374) n_row_374 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 375) n_row_375 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 376) n_row_376 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 377) n_row_377 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 378) n_row_378 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 379) n_row_379 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 380) n_row_380 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 381) n_row_381 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 382) n_row_382 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 383) n_row_383 (allFrom_zero (fun j => nGrid.row evalE j) 384)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
