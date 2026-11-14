/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 7 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `168`–`191`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_168_0 : bothSeg evalE (oGrid.idx 168) (oGrid.dm 168) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 168) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2804384398625818704660146428716730473509203166129397396448234310435869206952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_168_400 : bothSeg evalE (oGrid.idx 168) (oGrid.dm 168) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 168) oGrid.kl oGrid.kr 400 400 ⟨false, 2804384398625818704660146428716730473509203166129397396448234310435869206952⟩ ⟨false, 0⟩ ⟨false, 4533763203508221648395823010071835128785451066253407142073854139799474089858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_168_800 : bothSeg evalE (oGrid.idx 168) (oGrid.dm 168) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 168) oGrid.kl oGrid.kr 400 800 ⟨false, 4533763203508221648395823010071835128785451066253407142073854139799474089858⟩ ⟨false, 0⟩ ⟨false, 5170599592192255822317941212143384116703931260775129726578693398200164113106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_168_1200 : bothSeg evalE (oGrid.idx 168) (oGrid.dm 168) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 168) oGrid.kl oGrid.kr 400 1200 ⟨false, 5170599592192255822317941212143384116703931260775129726578693398200164113106⟩ ⟨false, 0⟩ ⟨false, 5248827813507730343860967236358835627325572762530259781136878223595465236596⟩ ⟨false, 13866155330099560088595073674660661204432077521021973975753874156090966378⟩ = true := by
  decide +kernel

theorem b_168_1600 : bothSeg evalE (oGrid.idx 168) (oGrid.dm 168) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 168) oGrid.kl oGrid.kr 400 1600 ⟨false, 5248827813507730343860967236358835627325572762530259781136878223595465236596⟩ ⟨false, 13866155330099560088595073674660661204432077521021973975753874156090966378⟩ ⟨false, 5073420381526197275061412277969147919147607677898870621637070483023775546016⟩ ⟨false, 189579681518554880406544562869119381470554693913080256810238983346443711020⟩ = true := by
  decide +kernel

theorem b_168_2000 : bothSeg evalE (oGrid.idx 168) (oGrid.dm 168) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 168) oGrid.kl oGrid.kr 400 2000 ⟨false, 5073420381526197275061412277969147919147607677898870621637070483023775546016⟩ ⟨false, 189579681518554880406544562869119381470554693913080256810238983346443711020⟩ ⟨false, 5033230685433614785255346689365996832781905585949567504253636723360027659008⟩ ⟨false, 230579897107035600077708402932594772927716341529220975246770366472268012646⟩ = true := by
  decide +kernel

theorem b_168_2400 : bothLoop evalE (oGrid.idx 168) (oGrid.dm 168) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 168) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5033230685433614785255346689365996832781905585949567504253636723360027659008⟩ ⟨false, 230579897107035600077708402932594772927716341529220975246770366472268012646⟩ = true := by
  decide +kernel

theorem o_row_168 : oGrid.row evalE 168 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_168_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_168_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_168_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_168_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_168_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_168_2000).1 (bothLoop_sound b_168_2400).1))))))

theorem n_row_168 : nGrid.row evalE 168 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_168_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_168_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_168_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_168_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_168_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_168_2000).2 (bothLoop_sound b_168_2400).2))))))

theorem b_169_0 : bothSeg evalE (oGrid.idx 169) (oGrid.dm 169) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 169) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2793572678690072592447153779987238995311798829291813233999333162026814413718⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_169_400 : bothSeg evalE (oGrid.idx 169) (oGrid.dm 169) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 169) oGrid.kl oGrid.kr 400 400 ⟨false, 2793572678690072592447153779987238995311798829291813233999333162026814413718⟩ ⟨false, 0⟩ ⟨false, 4516315437264189253677335175000009663381482918678531140622516395609960738082⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_169_800 : bothSeg evalE (oGrid.idx 169) (oGrid.dm 169) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 169) oGrid.kl oGrid.kr 400 800 ⟨false, 4516315437264189253677335175000009663381482918678531140622516395609960738082⟩ ⟨false, 0⟩ ⟨false, 5150466206439120295359658084560814589377865481106266541068791124665582647822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_169_1200 : bothSeg evalE (oGrid.idx 169) (oGrid.dm 169) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 169) oGrid.kl oGrid.kr 400 1200 ⟨false, 5150466206439120295359658084560814589377865481106266541068791124665582647822⟩ ⟨false, 0⟩ ⟨false, 5227664850374856565302682197625371364769663385195621824154941629489281585402⟩ ⟨false, 14225102372587453322155069763923503764511485066873385683125503143371076448⟩ = true := by
  decide +kernel

theorem b_169_1600 : bothSeg evalE (oGrid.idx 169) (oGrid.dm 169) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 169) oGrid.kl oGrid.kr 400 1600 ⟨false, 5227664850374856565302682197625371364769663385195621824154941629489281585402⟩ ⟨false, 14225102372587453322155069763923503764511485066873385683125503143371076448⟩ ⟨false, 5052541003802762058285472995422971248908328896935587240570910761204378013602⟩ ⟨false, 189655945458074454478761376621621538746570310124937491564681699653262213556⟩ = true := by
  decide +kernel

theorem b_169_2000 : bothSeg evalE (oGrid.idx 169) (oGrid.dm 169) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 169) oGrid.kl oGrid.kr 400 2000 ⟨false, 5052541003802762058285472995422971248908328896935587240570910761204378013602⟩ ⟨false, 189655945458074454478761376621621538746570310124937491564681699653262213556⟩ ⟨false, 5012596333308690570581844892109407577714971111601163832445968116423038519926⟩ ⟨false, 230412893960322219814401784727429072195912727838775660679696954387858338234⟩ = true := by
  decide +kernel

theorem b_169_2400 : bothLoop evalE (oGrid.idx 169) (oGrid.dm 169) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 169) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5012596333308690570581844892109407577714971111601163832445968116423038519926⟩ ⟨false, 230412893960322219814401784727429072195912727838775660679696954387858338234⟩ = true := by
  decide +kernel

theorem o_row_169 : oGrid.row evalE 169 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_169_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_169_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_169_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_169_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_169_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_169_2000).1 (bothLoop_sound b_169_2400).1))))))

theorem n_row_169 : nGrid.row evalE 169 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_169_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_169_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_169_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_169_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_169_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_169_2000).2 (bothLoop_sound b_169_2400).2))))))

theorem b_170_0 : bothSeg evalE (oGrid.idx 170) (oGrid.dm 170) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 170) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2782793804816771060162966330215666925532859198792762753564230778719593542780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_170_400 : bothSeg evalE (oGrid.idx 170) (oGrid.dm 170) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 170) oGrid.kl oGrid.kr 400 400 ⟨false, 2782793804816771060162966330215666925532859198792762753564230778719593542780⟩ ⟨false, 0⟩ ⟨false, 4498918363312843854535488850249558339936846323277785429384557751678975928318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_170_800 : bothSeg evalE (oGrid.idx 170) (oGrid.dm 170) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 170) oGrid.kl oGrid.kr 400 800 ⟨false, 4498918363312843854535488850249558339936846323277785429384557751678975928318⟩ ⟨false, 0⟩ ⟨false, 5130389858435613305846857618643902027191215950092296131226866886293663286482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_170_1200 : bothSeg evalE (oGrid.idx 170) (oGrid.dm 170) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 170) oGrid.kl oGrid.kr 400 1200 ⟨false, 5130389858435613305846857618643902027191215950092296131226866886293663286482⟩ ⟨false, 0⟩ ⟨false, 5206559394514119519763827257879634954608801087519519051619228350318403019200⟩ ⟨false, 14586125889599355687228529316450349535659026481492012230309551390544346768⟩ = true := by
  decide +kernel

theorem b_170_1600 : bothSeg evalE (oGrid.idx 170) (oGrid.dm 170) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 170) oGrid.kl oGrid.kr 400 1600 ⟨false, 5206559394514119519763827257879634954608801087519519051619228350318403019200⟩ ⟨false, 14586125889599355687228529316450349535659026481492012230309551390544346768⟩ ⟨false, 5031722194327662455756724258602821424695073032704827800451819181788079485422⟩ ⟨false, 189731214317116430359584176103883275623298431953496194984079547568161850268⟩ = true := by
  decide +kernel

theorem b_170_2000 : bothSeg evalE (oGrid.idx 170) (oGrid.dm 170) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 170) oGrid.kl oGrid.kr 400 2000 ⟨false, 5031722194327662455756724258602821424695073032704827800451819181788079485422⟩ ⟨false, 189731214317116430359584176103883275623298431953496194984079547568161850268⟩ ⟨false, 4992021759917419425882219517051392779697697506051379254109677948492018802866⟩ ⟨false, 230245593907148737923776991661765790303526332480847882881274263139611413436⟩ = true := by
  decide +kernel

theorem b_170_2400 : bothLoop evalE (oGrid.idx 170) (oGrid.dm 170) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 170) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4992021759917419425882219517051392779697697506051379254109677948492018802866⟩ ⟨false, 230245593907148737923776991661765790303526332480847882881274263139611413436⟩ = true := by
  decide +kernel

theorem o_row_170 : oGrid.row evalE 170 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_170_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_170_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_170_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_170_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_170_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_170_2000).1 (bothLoop_sound b_170_2400).1))))))

theorem n_row_170 : nGrid.row evalE 170 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_170_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_170_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_170_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_170_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_170_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_170_2000).2 (bothLoop_sound b_170_2400).2))))))

theorem b_171_0 : bothSeg evalE (oGrid.idx 171) (oGrid.dm 171) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 171) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2772047709579076705571762704450222805424031764979438071877609621388550564356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_171_400 : bothSeg evalE (oGrid.idx 171) (oGrid.dm 171) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 171) oGrid.kl oGrid.kr 400 400 ⟨false, 2772047709579076705571762704450222805424031764979438071877609621388550564356⟩ ⟨false, 0⟩ ⟨false, 4481571897536753139635631519706542965429382543929338889704229562972556750908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_171_800 : bothSeg evalE (oGrid.idx 171) (oGrid.dm 171) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 171) oGrid.kl oGrid.kr 400 800 ⟨false, 4481571897536753139635631519706542965429382543929338889704229562972556750908⟩ ⟨false, 0⟩ ⟨false, 5110370470875598035263187800493268392265844670569341644107952679998497323188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_171_1200 : bothSeg evalE (oGrid.idx 171) (oGrid.dm 171) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 171) oGrid.kl oGrid.kr 400 1200 ⟨false, 5110370470875598035263187800493268392265844670569341644107952679998497323188⟩ ⟨false, 0⟩ ⟨false, 5185511611646606972436893957094986207435764059345544603338687900926933703356⟩ ⟨false, 14948994184530612062334919895189046982555898540887330729757822675849796994⟩ = true := by
  decide +kernel

theorem b_171_1600 : bothSeg evalE (oGrid.idx 171) (oGrid.dm 171) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 171) oGrid.kl oGrid.kr 400 1600 ⟨false, 5185511611646606972436893957094986207435764059345544603338687900926933703356⟩ ⟨false, 14948994184530612062334919895189046982555898540887330729757822675849796994⟩ ⟨false, 5010964051270886866311699066479208473253157203801219986722524442241875976182⟩ ⟨false, 189805529264228034952221188545434077688868759630880551244133718377160791614⟩ = true := by
  decide +kernel

theorem b_171_2000 : bothSeg evalE (oGrid.idx 171) (oGrid.dm 171) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 171) oGrid.kl oGrid.kr 400 2000 ⟨false, 5010964051270886866311699066479208473253157203801219986722524442241875976182⟩ ⟨false, 189805529264228034952221188545434077688868759630880551244133718377160791614⟩ ⟨false, 4971507082453349978039166862948137568830131658187358204993683298680270425362⟩ ⟨false, 230078284006132945355973166082829745303363271704823816788691986303766424946⟩ = true := by
  decide +kernel

theorem b_171_2400 : bothLoop evalE (oGrid.idx 171) (oGrid.dm 171) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 171) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4971507082453349978039166862948137568830131658187358204993683298680270425362⟩ ⟨false, 230078284006132945355973166082829745303363271704823816788691986303766424946⟩ = true := by
  decide +kernel

theorem o_row_171 : oGrid.row evalE 171 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_171_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_171_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_171_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_171_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_171_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_171_2000).1 (bothLoop_sound b_171_2400).1))))))

theorem n_row_171 : nGrid.row evalE 171 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_171_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_171_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_171_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_171_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_171_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_171_2000).2 (bothLoop_sound b_171_2400).2))))))

theorem b_172_0 : bothSeg evalE (oGrid.idx 172) (oGrid.dm 172) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 172) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2761334258895375359778288359058511657428925451411174065484664728417359612352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_172_400 : bothSeg evalE (oGrid.idx 172) (oGrid.dm 172) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 172) oGrid.kl oGrid.kr 400 400 ⟨false, 2761334258895375359778288359058511657428925451411174065484664728417359612352⟩ ⟨false, 0⟩ ⟨false, 4464275862334753356479758883856961381007659927309965703118688286095777542480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_172_800 : bothSeg evalE (oGrid.idx 172) (oGrid.dm 172) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 172) oGrid.kl oGrid.kr 400 800 ⟨false, 4464275862334753356479758883856961381007659927309965703118688286095777542480⟩ ⟨false, 0⟩ ⟨false, 5090407858350762514270958757167352882963194876821862759663170721373351847600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_172_1200 : bothSeg evalE (oGrid.idx 172) (oGrid.dm 172) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 172) oGrid.kl oGrid.kr 400 1200 ⟨false, 5090407858350762514270958757167352882963194876821862759663170721373351847600⟩ ⟨false, 0⟩ ⟨false, 5164521489731438676949922267241486791218225774436554519559263576356839982156⟩ ⟨false, 15313541125476831647224481428863638013572552360029122765367689577079175604⟩ = true := by
  decide +kernel

theorem b_172_1600 : bothSeg evalE (oGrid.idx 172) (oGrid.dm 172) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 172) oGrid.kl oGrid.kr 400 1600 ⟨false, 5164521489731438676949922267241486791218225774436554519559263576356839982156⟩ ⟨false, 15313541125476831647224481428863638013572552360029122765367689577079175604⟩ ⟨false, 4990266060703099055927821199626223485564350125945095184835906664335009333240⟩ ⟨false, 189878735839823773140346467667279003038054024806372043785145613053249798684⟩ = true := by
  decide +kernel

theorem b_172_2000 : bothSeg evalE (oGrid.idx 172) (oGrid.dm 172) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 172) oGrid.kl oGrid.kr 400 2000 ⟨false, 4990266060703099055927821199626223485564350125945095184835906664335009333240⟩ ⟨false, 189878735839823773140346467667279003038054024806372043785145613053249798684⟩ ⟨false, 4951051847451117774550853429296052084460190148991956411921471660783657688332⟩ ⟨false, 229910365958437441358291538610329659295845367932862936096968574923461891416⟩ = true := by
  decide +kernel

theorem b_172_2400 : bothLoop evalE (oGrid.idx 172) (oGrid.dm 172) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 172) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4951051847451117774550853429296052084460190148991956411921471660783657688332⟩ ⟨false, 229910365958437441358291538610329659295845367932862936096968574923461891416⟩ = true := by
  decide +kernel

theorem o_row_172 : oGrid.row evalE 172 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_172_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_172_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_172_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_172_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_172_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_172_2000).1 (bothLoop_sound b_172_2400).1))))))

theorem n_row_172 : nGrid.row evalE 172 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_172_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_172_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_172_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_172_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_172_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_172_2000).2 (bothLoop_sound b_172_2400).2))))))

theorem b_173_0 : bothSeg evalE (oGrid.idx 173) (oGrid.dm 173) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 173) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2750653374138980427267281493697629268542023827928014182936060859493680467264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_173_400 : bothSeg evalE (oGrid.idx 173) (oGrid.dm 173) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 173) oGrid.kl oGrid.kr 400 400 ⟨false, 2750653374138980427267281493697629268542023827928014182936060859493680467264⟩ ⟨false, 0⟩ ⟨false, 4447030146424515675425959056322131549766640147035041063454158259997028008008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_173_800 : bothSeg evalE (oGrid.idx 173) (oGrid.dm 173) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 173) oGrid.kl oGrid.kr 400 800 ⟨false, 4447030146424515675425959056322131549766640147035041063454158259997028008008⟩ ⟨false, 0⟩ ⟨false, 5070501897108460076857588098077286454392704629928474427351135301464019139182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_173_1200 : bothSeg evalE (oGrid.idx 173) (oGrid.dm 173) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 173) oGrid.kl oGrid.kr 400 1200 ⟨false, 5070501897108460076857588098077286454392704629928474427351135301464019139182⟩ ⟨false, 0⟩ ⟨false, 5143589129125438796814727226337666355754203230799909874931214488871083292606⟩ ⟨false, 15679524660289717343042145743555450432372478133035214679847255663240457638⟩ = true := by
  decide +kernel

theorem b_173_1600 : bothSeg evalE (oGrid.idx 173) (oGrid.dm 173) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 173) oGrid.kl oGrid.kr 400 1600 ⟨false, 5143589129125438796814727226337666355754203230799909874931214488871083292606⟩ ⟨false, 15679524660289717343042145743555450432372478133035214679847255663240457638⟩ ⟨false, 4969628738344662343096795693402602060611532528187279791544510470495225108474⟩ ⟨false, 189950539391815573092685975792099299560998108873724260182302717507810885760⟩ = true := by
  decide +kernel

theorem b_173_2000 : bothSeg evalE (oGrid.idx 173) (oGrid.dm 173) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 173) oGrid.kl oGrid.kr 400 2000 ⟨false, 4969628738344662343096795693402602060611532528187279791544510470495225108474⟩ ⟨false, 189950539391815573092685975792099299560998108873724260182302717507810885760⟩ ⟨false, 4930656560964679684518825441614831240542561327814707060112997670052496801180⟩ ⟨false, 229742012743030391130857708815492141546149828173078829531642846003657474308⟩ = true := by
  decide +kernel

theorem b_173_2400 : bothLoop evalE (oGrid.idx 173) (oGrid.dm 173) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 173) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4930656560964679684518825441614831240542561327814707060112997670052496801180⟩ ⟨false, 229742012743030391130857708815492141546149828173078829531642846003657474308⟩ = true := by
  decide +kernel

theorem o_row_173 : oGrid.row evalE 173 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_173_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_173_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_173_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_173_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_173_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_173_2000).1 (bothLoop_sound b_173_2400).1))))))

theorem n_row_173 : nGrid.row evalE 173 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_173_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_173_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_173_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_173_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_173_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_173_2000).2 (bothLoop_sound b_173_2400).2))))))

theorem b_174_0 : bothSeg evalE (oGrid.idx 174) (oGrid.dm 174) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 174) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2740004993406637229179855667777885574433174633652953213023783035165824283912⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_174_400 : bothSeg evalE (oGrid.idx 174) (oGrid.dm 174) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 174) oGrid.kl oGrid.kr 400 400 ⟨false, 2740004993406637229179855667777885574433174633652953213023783035165824283912⟩ ⟨false, 0⟩ ⟨false, 4429834632263290595396804249772871930845249328524925161789811060601184164108⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_174_800 : bothSeg evalE (oGrid.idx 174) (oGrid.dm 174) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 174) oGrid.kl oGrid.kr 400 800 ⟨false, 4429834632263290595396804249772871930845249328524925161789811060601184164108⟩ ⟨false, 0⟩ ⟨false, 5050652472330712094234240453207544956976708921983456128738797882440896939104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_174_1200 : bothSeg evalE (oGrid.idx 174) (oGrid.dm 174) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 174) oGrid.kl oGrid.kr 400 1200 ⟨false, 5050652472330712094234240453207544956976708921983456128738797882440896939104⟩ ⟨false, 0⟩ ⟨false, 5122714565759927082378885046998772130502779610171518114975156980381608199964⟩ ⟨false, 16046813317329527891367619568147872990142173360748988689119406705471145726⟩ = true := by
  decide +kernel

theorem b_174_1600 : bothSeg evalE (oGrid.idx 174) (oGrid.dm 174) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 174) oGrid.kl oGrid.kr 400 1600 ⟨false, 5122714565759927082378885046998772130502779610171518114975156980381608199964⟩ ⟨false, 16046813317329527891367619568147872990142173360748988689119406705471145726⟩ ⟨false, 4949051319686518054737758403436992935549086915988941935934699048506325382228⟩ ⟨false, 190021274425067369851197051456033737528630612959494780366212140191761187378⟩ = true := by
  decide +kernel

theorem b_174_2000 : bothSeg evalE (oGrid.idx 174) (oGrid.dm 174) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 174) oGrid.kl oGrid.kr 400 2000 ⟨false, 4949051319686518054737758403436992935549086915988941935934699048506325382228⟩ ⟨false, 190021274425067369851197051456033737528630612959494780366212140191761187378⟩ ⟨false, 4910320499844133698067956481171592050585603031264901159108424573235811926580⟩ ⟨false, 229573079885432768263019125393831598918883319697632813181774474752866783704⟩ = true := by
  decide +kernel

theorem b_174_2400 : bothLoop evalE (oGrid.idx 174) (oGrid.dm 174) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 174) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4910320499844133698067956481171592050585603031264901159108424573235811926580⟩ ⟨false, 229573079885432768263019125393831598918883319697632813181774474752866783704⟩ = true := by
  decide +kernel

theorem o_row_174 : oGrid.row evalE 174 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_174_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_174_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_174_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_174_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_174_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_174_2000).1 (bothLoop_sound b_174_2400).1))))))

theorem n_row_174 : nGrid.row evalE 174 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_174_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_174_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_174_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_174_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_174_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_174_2000).2 (bothLoop_sound b_174_2400).2))))))

theorem b_175_0 : bothSeg evalE (oGrid.idx 175) (oGrid.dm 175) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 175) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2729389000426622470419345079842764061673523008285303746193035215737425528318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_175_400 : bothSeg evalE (oGrid.idx 175) (oGrid.dm 175) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 175) oGrid.kl oGrid.kr 400 400 ⟨false, 2729389000426622470419345079842764061673523008285303746193035215737425528318⟩ ⟨false, 0⟩ ⟨false, 4412689199912927838765902945847271036886144569789869185993060609630082536978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_175_800 : bothSeg evalE (oGrid.idx 175) (oGrid.dm 175) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 175) oGrid.kl oGrid.kr 400 800 ⟨false, 4412689199912927838765902945847271036886144569789869185993060609630082536978⟩ ⟨false, 0⟩ ⟨false, 5030859467774446173271206422296393366664663990004478997138093681752917136108⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_175_1200 : bothSeg evalE (oGrid.idx 175) (oGrid.dm 175) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 175) oGrid.kl oGrid.kr 400 1200 ⟨false, 5030859467774446173271206422296393366664663990004478997138093681752917136108⟩ ⟨false, 0⟩ ⟨false, 5101897872352220366926487116477513962023207404565794679671859389826134218690⟩ ⟨false, 16415204000594013373939682929872539770312003187182455176979503309146281884⟩ = true := by
  decide +kernel

theorem b_175_1600 : bothSeg evalE (oGrid.idx 175) (oGrid.dm 175) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 175) oGrid.kl oGrid.kr 400 1600 ⟨false, 5101897872352220366926487116477513962023207404565794679671859389826134218690⟩ ⟨false, 16415204000594013373939682929872539770312003187182455176979503309146281884⟩ ⟨false, 4928533828055042246779571932194367581625687410516309290486018039176283771580⟩ ⟨false, 190091420718622954840538212888656149603368324799169566364811675033468779668⟩ = true := by
  decide +kernel

theorem b_175_2000 : bothSeg evalE (oGrid.idx 175) (oGrid.dm 175) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 175) oGrid.kl oGrid.kr 400 2000 ⟨false, 4928533828055042246779571932194367581625687410516309290486018039176283771580⟩ ⟨false, 190091420718622954840538212888656149603368324799169566364811675033468779668⟩ ⟨false, 4890043725392030408800420259847948836541886329924771616276670193253061717676⟩ ⟨false, 229404276743113628109952972127093983135771503534679454168303876860995324212⟩ = true := by
  decide +kernel

theorem b_175_2400 : bothLoop evalE (oGrid.idx 175) (oGrid.dm 175) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 175) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4890043725392030408800420259847948836541886329924771616276670193253061717676⟩ ⟨false, 229404276743113628109952972127093983135771503534679454168303876860995324212⟩ = true := by
  decide +kernel

theorem o_row_175 : oGrid.row evalE 175 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_175_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_175_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_175_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_175_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_175_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_175_2000).1 (bothLoop_sound b_175_2400).1))))))

theorem n_row_175 : nGrid.row evalE 175 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_175_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_175_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_175_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_175_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_175_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_175_2000).2 (bothLoop_sound b_175_2400).2))))))

theorem b_176_0 : bothSeg evalE (oGrid.idx 176) (oGrid.dm 176) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 176) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2718805344175927131474145025165134997567482555982967276399766543720765231590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_176_400 : bothSeg evalE (oGrid.idx 176) (oGrid.dm 176) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 176) oGrid.kl oGrid.kr 400 400 ⟨false, 2718805344175927131474145025165134997567482555982967276399766543720765231590⟩ ⟨false, 0⟩ ⟨false, 4395593773183613004065705399515745000683407503816990506750828699170368950696⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_176_800 : bothSeg evalE (oGrid.idx 176) (oGrid.dm 176) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 176) oGrid.kl oGrid.kr 400 800 ⟨false, 4395593773183613004065705399515745000683407503816990506750828699170368950696⟩ ⟨false, 0⟩ ⟨false, 5011122796297915792965323690662313952036403198258257937281587588166521691358⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_176_1200 : bothSeg evalE (oGrid.idx 176) (oGrid.dm 176) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 176) oGrid.kl oGrid.kr 400 1200 ⟨false, 5011122796297915792965323690662313952036403198258257937281587588166521691358⟩ ⟨false, 0⟩ ⟨false, 5081139185668616195974187036357637161136548154524248552618952242418928345724⟩ ⟨false, 16784497771048297102450123738474357488353303474325638235139311866923850368⟩ = true := by
  decide +kernel

theorem b_176_1600 : bothSeg evalE (oGrid.idx 176) (oGrid.dm 176) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 176) oGrid.kl oGrid.kr 400 1600 ⟨false, 5081139185668616195974187036357637161136548154524248552618952242418928345724⟩ ⟨false, 16784497771048297102450123738474357488353303474325638235139311866923850368⟩ ⟨false, 4908076420880682250657485897011091602699382650500601314269709293586985696822⟩ ⟨false, 190160369773389129603548935652319188362443356822001139062343725398129053468⟩ = true := by
  decide +kernel

theorem b_176_2000 : bothSeg evalE (oGrid.idx 176) (oGrid.dm 176) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 176) oGrid.kl oGrid.kr 400 2000 ⟨false, 4908076420880682250657485897011091602699382650500601314269709293586985696822⟩ ⟨false, 190160369773389129603548935652319188362443356822001139062343725398129053468⟩ ⟨false, 4869826424246595343051574680475927640445642675186759264837746680500277759130⟩ ⟨false, 229234948810846446245229337597380792067999576526413366533600199316009140262⟩ = true := by
  decide +kernel

theorem b_176_2400 : bothLoop evalE (oGrid.idx 176) (oGrid.dm 176) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 176) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4869826424246595343051574680475927640445642675186759264837746680500277759130⟩ ⟨false, 229234948810846446245229337597380792067999576526413366533600199316009140262⟩ = true := by
  decide +kernel

theorem o_row_176 : oGrid.row evalE 176 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_176_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_176_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_176_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_176_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_176_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_176_2000).1 (bothLoop_sound b_176_2400).1))))))

theorem n_row_176 : nGrid.row evalE 176 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_176_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_176_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_176_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_176_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_176_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_176_2000).2 (bothLoop_sound b_176_2400).2))))))

theorem b_177_0 : bothSeg evalE (oGrid.idx 177) (oGrid.dm 177) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 177) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2708253916556198668780345102484599056798919176930193947398204620714542026010⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_177_400 : bothSeg evalE (oGrid.idx 177) (oGrid.dm 177) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 177) oGrid.kl oGrid.kr 400 400 ⟨false, 2708253916556198668780345102484599056798919176930193947398204620714542026010⟩ ⟨false, 0⟩ ⟨false, 4378548219440105485729772332331733003655739332198043561813601290718081847854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_177_800 : bothSeg evalE (oGrid.idx 177) (oGrid.dm 177) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 177) oGrid.kl oGrid.kr 400 800 ⟨false, 4378548219440105485729772332331733003655739332198043561813601290718081847854⟩ ⟨false, 0⟩ ⟨false, 4991442322747775988176086930399540395804141726589107843387117173276980033164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_177_1200 : bothSeg evalE (oGrid.idx 177) (oGrid.dm 177) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 177) oGrid.kl oGrid.kr 400 1200 ⟨false, 4991442322747775988176086930399540395804141726589107843387117173276980033164⟩ ⟨false, 0⟩ ⟨false, 5060438556424924451390840130164976083920403727600314582778815370028464101792⟩ ⟨false, 17154445024049825436382292086833093317379952897240243845204108728573452790⟩ = true := by
  decide +kernel

theorem b_177_1600 : bothSeg evalE (oGrid.idx 177) (oGrid.dm 177) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 177) oGrid.kl oGrid.kr 400 1600 ⟨false, 5060438556424924451390840130164976083920403727600314582778815370028464101792⟩ ⟨false, 17154445024049825436382292086833093317379952897240243845204108728573452790⟩ ⟨false, 4887678872190941225258860222867891246327702377153159648639790514471361393716⟩ ⟨false, 190228095061935404177204367850056747287357171182594674426408199294239974690⟩ = true := by
  decide +kernel

theorem b_177_2000 : bothSeg evalE (oGrid.idx 177) (oGrid.dm 177) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 177) oGrid.kl oGrid.kr 400 2000 ⟨false, 4887678872190941225258860222867891246327702377153159648639790514471361393716⟩ ⟨false, 190228095061935404177204367850056747287357171182594674426408199294239974690⟩ ⟨false, 4849668393882443530957042423385260891705932693043236603708005690906551704302⟩ ⟨false, 229064759720057084836437249397904042351274577120823469719912345848302741160⟩ = true := by
  decide +kernel

theorem b_177_2400 : bothLoop evalE (oGrid.idx 177) (oGrid.dm 177) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 177) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4849668393882443530957042423385260891705932693043236603708005690906551704302⟩ ⟨false, 229064759720057084836437249397904042351274577120823469719912345848302741160⟩ = true := by
  decide +kernel

theorem o_row_177 : oGrid.row evalE 177 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_177_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_177_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_177_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_177_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_177_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_177_2000).1 (bothLoop_sound b_177_2400).1))))))

theorem n_row_177 : nGrid.row evalE 177 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_177_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_177_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_177_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_177_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_177_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_177_2000).2 (bothLoop_sound b_177_2400).2))))))

theorem b_178_0 : bothSeg evalE (oGrid.idx 178) (oGrid.dm 178) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 178) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2697734643706337146049351760986916966963028610045206590979681590595642616192⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_178_400 : bothSeg evalE (oGrid.idx 178) (oGrid.dm 178) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 178) oGrid.kl oGrid.kr 400 400 ⟨false, 2697734643706337146049351760986916966963028610045206590979681590595642616192⟩ ⟨false, 0⟩ ⟨false, 4361552394402052395008377436647461781732189663113615112291858908406406187682⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_178_800 : bothSeg evalE (oGrid.idx 178) (oGrid.dm 178) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 178) oGrid.kl oGrid.kr 400 800 ⟨false, 4361552394402052395008377436647461781732189663113615112291858908406406187682⟩ ⟨false, 0⟩ ⟨false, 4971817918085106697337677629567865377536074181720849101557175993706408513990⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_178_1200 : bothSeg evalE (oGrid.idx 178) (oGrid.dm 178) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 178) oGrid.kl oGrid.kr 400 1200 ⟨false, 4971817918085106697337677629567865377536074181720849101557175993706408513990⟩ ⟨false, 0⟩ ⟨false, 5039796030474307512780215471568109027409522798301780517016446571711705320108⟩ ⟨false, 17524933764155951471608093091490883974011195170508203138449179021539059858⟩ = true := by
  decide +kernel

theorem b_178_1600 : bothSeg evalE (oGrid.idx 178) (oGrid.dm 178) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 178) oGrid.kl oGrid.kr 400 1600 ⟨false, 5039796030474307512780215471568109027409522798301780517016446571711705320108⟩ ⟨false, 17524933764155951471608093091490883974011195170508203138449179021539059858⟩ ⟨false, 4867340863593897682858468447830964471930562704729162180009334015959509395570⟩ ⟨false, 190294756137692465773710972560623749735288423367108066599250949892730051216⟩ = true := by
  decide +kernel

theorem b_178_2000 : bothSeg evalE (oGrid.idx 178) (oGrid.dm 178) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 178) oGrid.kl oGrid.kr 400 2000 ⟨false, 4867340863593897682858468447830964471930562704729162180009334015959509395570⟩ ⟨false, 190294756137692465773710972560623749735288423367108066599250949892730051216⟩ ⟨false, 4829569359698121617870503011025093449413200673436290278917606275650196824006⟩ ⟨false, 228894382980116055998767812023552154001468249534682747665103073689215642298⟩ = true := by
  decide +kernel

theorem b_178_2400 : bothLoop evalE (oGrid.idx 178) (oGrid.dm 178) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 178) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4829569359698121617870503011025093449413200673436290278917606275650196824006⟩ ⟨false, 228894382980116055998767812023552154001468249534682747665103073689215642298⟩ = true := by
  decide +kernel

theorem o_row_178 : oGrid.row evalE 178 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_178_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_178_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_178_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_178_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_178_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_178_2000).1 (bothLoop_sound b_178_2400).1))))))

theorem n_row_178 : nGrid.row evalE 178 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_178_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_178_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_178_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_178_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_178_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_178_2000).2 (bothLoop_sound b_178_2400).2))))))

theorem b_179_0 : bothSeg evalE (oGrid.idx 179) (oGrid.dm 179) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 179) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2687247433685594904122984311792220520659395837376224003620820801774926581404⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_179_400 : bothSeg evalE (oGrid.idx 179) (oGrid.dm 179) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 179) oGrid.kl oGrid.kr 400 400 ⟨false, 2687247433685594904122984311792220520659395837376224003620820801774926581404⟩ ⟨false, 0⟩ ⟨false, 4344606192712606805093345109155352106162538429876122477367611656962780425296⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_179_800 : bothSeg evalE (oGrid.idx 179) (oGrid.dm 179) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 179) oGrid.kl oGrid.kr 400 800 ⟨false, 4344606192712606805093345109155352106162538429876122477367611656962780425296⟩ ⟨false, 0⟩ ⟨false, 4952249446350790719627184124828827944439569354408572107608865813694346947818⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_179_1200 : bothSeg evalE (oGrid.idx 179) (oGrid.dm 179) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 179) oGrid.kl oGrid.kr 400 1200 ⟨false, 4952249446350790719627184124828827944439569354408572107608865813694346947818⟩ ⟨false, 0⟩ ⟨false, 5019211728105189311057747224946322618651494773545675980887874117745275496334⟩ ⟨false, 17895683051834234657223442585872189990114700532502452258414368105633421524⟩ = true := by
  decide +kernel

theorem b_179_1600 : bothSeg evalE (oGrid.idx 179) (oGrid.dm 179) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 179) oGrid.kl oGrid.kr 400 1600 ⟨false, 5019211728105189311057747224946322618651494773545675980887874117745275496334⟩ ⟨false, 17895683051834234657223442585872189990114700532502452258414368105633421524⟩ ⟨false, 4847062415696360366461785160065338484954159717364139418824989023483059803568⟩ ⟨false, 190360371882643093911882199325348869173130505522163931949291581167629154168⟩ = true := by
  decide +kernel

theorem b_179_2000 : bothSeg evalE (oGrid.idx 179) (oGrid.dm 179) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 179) oGrid.kl oGrid.kr 400 2000 ⟨false, 4847062415696360366461785160065338484954159717364139418824989023483059803568⟩ ⟨false, 190360371882643093911882199325348869173130505522163931949291581167629154168⟩ ⟨false, 4809529350800973719994306870872979506451027915369584838755845198649312892824⟩ ⟨false, 228723246635651430058143709665625605450847279860758681100018792530233457268⟩ = true := by
  decide +kernel

theorem b_179_2400 : bothLoop evalE (oGrid.idx 179) (oGrid.dm 179) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 179) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4809529350800973719994306870872979506451027915369584838755845198649312892824⟩ ⟨false, 228723246635651430058143709665625605450847279860758681100018792530233457268⟩ = true := by
  decide +kernel

theorem o_row_179 : oGrid.row evalE 179 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_179_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_179_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_179_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_179_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_179_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_179_2000).1 (bothLoop_sound b_179_2400).1))))))

theorem n_row_179 : nGrid.row evalE 179 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_179_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_179_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_179_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_179_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_179_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_179_2000).2 (bothLoop_sound b_179_2400).2))))))

theorem b_180_0 : bothSeg evalE (oGrid.idx 180) (oGrid.dm 180) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 180) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2676792177578746505022865315680572461603399228438732584579123438481970439044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_180_400 : bothSeg evalE (oGrid.idx 180) (oGrid.dm 180) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 180) oGrid.kl oGrid.kr 400 400 ⟨false, 2676792177578746505022865315680572461603399228438732584579123438481970439044⟩ ⟨false, 0⟩ ⟨false, 4327709489760052883356998328019696550539387210757393540319270997965090302892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_180_800 : bothSeg evalE (oGrid.idx 180) (oGrid.dm 180) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 180) oGrid.kl oGrid.kr 400 800 ⟨false, 4327709489760052883356998328019696550539387210757393540319270997965090302892⟩ ⟨false, 0⟩ ⟨false, 4932736786635324815603537808935949922777037710546167502931081266513538099160⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_180_1200 : bothSeg evalE (oGrid.idx 180) (oGrid.dm 180) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 180) oGrid.kl oGrid.kr 400 1200 ⟨false, 4932736786635324815603537808935949922777037710546167502931081266513538099160⟩ ⟨false, 0⟩ ⟨false, 4998685680854364650773614054189548216680429127693756511473221798835684405638⟩ ⟨false, 18266557904704713582400317309426117120503373782843773827079138684245081480⟩ = true := by
  decide +kernel

theorem b_180_1600 : bothSeg evalE (oGrid.idx 180) (oGrid.dm 180) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 180) oGrid.kl oGrid.kr 400 1600 ⟨false, 4998685680854364650773614054189548216680429127693756511473221798835684405638⟩ ⟨false, 18266557904704713582400317309426117120503373782843773827079138684245081480⟩ ⟨false, 4826843427343494389441997149633984444870533678133680329367459989540734008104⟩ ⟨false, 190425038307156035224763726984678391166176421058689387311276930847728707850⟩ = true := by
  decide +kernel

theorem b_180_2000 : bothSeg evalE (oGrid.idx 180) (oGrid.dm 180) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 180) oGrid.kl oGrid.kr 400 2000 ⟨false, 4826843427343494389441997149633984444870533678133680329367459989540734008104⟩ ⟨false, 190425038307156035224763726984678391166176421058689387311276930847728707850⟩ ⟨false, 4789548299060121421758969602723485387438208849765693390378298387972590401392⟩ ⟨false, 228551785970853345547922889251335022413063868615088889788005662573842445770⟩ = true := by
  decide +kernel

theorem b_180_2400 : bothLoop evalE (oGrid.idx 180) (oGrid.dm 180) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 180) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4789548299060121421758969602723485387438208849765693390378298387972590401392⟩ ⟨false, 228551785970853345547922889251335022413063868615088889788005662573842445770⟩ = true := by
  decide +kernel

theorem o_row_180 : oGrid.row evalE 180 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_180_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_180_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_180_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_180_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_180_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_180_2000).1 (bothLoop_sound b_180_2400).1))))))

theorem n_row_180 : nGrid.row evalE 180 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_180_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_180_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_180_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_180_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_180_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_180_2000).2 (bothLoop_sound b_180_2400).2))))))

theorem b_181_0 : bothSeg evalE (oGrid.idx 181) (oGrid.dm 181) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 181) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2666368813528135697370571568200701471789155038030037249920409410864080526156⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_181_400 : bothSeg evalE (oGrid.idx 181) (oGrid.dm 181) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 181) oGrid.kl oGrid.kr 400 400 ⟨false, 2666368813528135697370571568200701471789155038030037249920409410864080526156⟩ ⟨false, 0⟩ ⟨false, 4310862184438058687083803486183524836520240541648297179171943702499821985368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_181_800 : bothSeg evalE (oGrid.idx 181) (oGrid.dm 181) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 181) oGrid.kl oGrid.kr 400 800 ⟨false, 4310862184438058687083803486183524836520240541648297179171943702499821985368⟩ ⟨false, 0⟩ ⟨false, 4913279851036199859373213244861882552342024812641452943664127256207031967232⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_181_1200 : bothSeg evalE (oGrid.idx 181) (oGrid.dm 181) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 181) oGrid.kl oGrid.kr 400 1200 ⟨false, 4913279851036199859373213244861882552342024812641452943664127256207031967232⟩ ⟨false, 0⟩ ⟨false, 4978217994597356983913221021036160308249135424226051712245206906676730081410⟩ ⟨false, 18637348692735695517554902741645212016744619002363382057492598885759546474⟩ = true := by
  decide +kernel

theorem b_181_1600 : bothSeg evalE (oGrid.idx 181) (oGrid.dm 181) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 181) oGrid.kl oGrid.kr 400 1600 ⟨false, 4978217994597356983913221021036160308249135424226051712245206906676730081410⟩ ⟨false, 18637348692735695517554902741645212016744619002363382057492598885759546474⟩ ⟨false, 4806683624508989774678528430120748620917684202962498690098272859652167778436⟩ ⟨false, 190488741772512041555378552862228217916990302811259407868697267006275315422⟩ = true := by
  decide +kernel

theorem b_181_2000 : bothSeg evalE (oGrid.idx 181) (oGrid.dm 181) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 181) oGrid.kl oGrid.kr 400 2000 ⟨false, 4806683624508989774678528430120748620917684202962498690098272859652167778436⟩ ⟨false, 190488741772512041555378552862228217916990302811259407868697267006275315422⟩ ⟨false, 4769625993396635562779061297862060775247412968190947615091995653559075990612⟩ ⟨false, 228379810286200010034864615100589508497745393486257332412131355237747480154⟩ = true := by
  decide +kernel

theorem b_181_2400 : bothLoop evalE (oGrid.idx 181) (oGrid.dm 181) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 181) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4769625993396635562779061297862060775247412968190947615091995653559075990612⟩ ⟨false, 228379810286200010034864615100589508497745393486257332412131355237747480154⟩ = true := by
  decide +kernel

theorem o_row_181 : oGrid.row evalE 181 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_181_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_181_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_181_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_181_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_181_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_181_2000).1 (bothLoop_sound b_181_2400).1))))))

theorem n_row_181 : nGrid.row evalE 181 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_181_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_181_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_181_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_181_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_181_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_181_2000).2 (bothLoop_sound b_181_2400).2))))))

theorem b_182_0 : bothSeg evalE (oGrid.idx 182) (oGrid.dm 182) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 182) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2655977295308594887440175769716626851857931773446199407792375124110782896212⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_182_400 : bothSeg evalE (oGrid.idx 182) (oGrid.dm 182) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 182) oGrid.kl oGrid.kr 400 400 ⟨false, 2655977295308594887440175769716626851857931773446199407792375124110782896212⟩ ⟨false, 0⟩ ⟨false, 4294064188795862333688070776999011577404291569280453450731288604481228554418⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_182_800 : bothSeg evalE (oGrid.idx 182) (oGrid.dm 182) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 182) oGrid.kl oGrid.kr 400 800 ⟨false, 4294064188795862333688070776999011577404291569280453450731288604481228554418⟩ ⟨false, 0⟩ ⟨false, 4893878534715378131104244209785763963869893526704220964063504433643015559262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_182_1200 : bothSeg evalE (oGrid.idx 182) (oGrid.dm 182) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 182) oGrid.kl oGrid.kr 400 1200 ⟨false, 4893878534715378131104244209785763963869893526704220964063504433643015559262⟩ ⟨false, 0⟩ ⟨false, 4957808816871269816070532336801576857954178052831228418415320445124812802126⟩ ⟨false, 19007827113171648505975193243396576659810325916317787724261979126983003642⟩ = true := by
  decide +kernel

theorem b_182_1600 : bothSeg evalE (oGrid.idx 182) (oGrid.dm 182) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 182) oGrid.kl oGrid.kr 400 1600 ⟨false, 4957808816871269816070532336801576857954178052831228418415320445124812802126⟩ ⟨false, 19007827113171648505975193243396576659810325916317787724261979126983003642⟩ ⟨false, 4786583087879144940990588845189868121214359162631034875581079267942778403858⟩ ⟨false, 190551741034453451146813853728800069570333902169336811793870228378070466050⟩ = true := by
  decide +kernel

theorem b_182_2000 : bothSeg evalE (oGrid.idx 182) (oGrid.dm 182) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 182) oGrid.kl oGrid.kr 400 2000 ⟨false, 4786583087879144940990588845189868121214359162631034875581079267942778403858⟩ ⟨false, 190551741034453451146813853728800069570333902169336811793870228378070466050⟩ ⟨false, 4749762493943352510227058274894718406807863690100709462854138888035142283428⟩ ⟨false, 228207518249391399858365516729797881476487838893185845892378812788167183114⟩ = true := by
  decide +kernel

theorem b_182_2400 : bothLoop evalE (oGrid.idx 182) (oGrid.dm 182) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 182) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4749762493943352510227058274894718406807863690100709462854138888035142283428⟩ ⟨false, 228207518249391399858365516729797881476487838893185845892378812788167183114⟩ = true := by
  decide +kernel

theorem o_row_182 : oGrid.row evalE 182 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_182_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_182_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_182_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_182_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_182_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_182_2000).1 (bothLoop_sound b_182_2400).1))))))

theorem n_row_182 : nGrid.row evalE 182 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_182_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_182_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_182_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_182_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_182_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_182_2000).2 (bothLoop_sound b_182_2400).2))))))

theorem b_183_0 : bothSeg evalE (oGrid.idx 183) (oGrid.dm 183) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 183) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2645617504481887759719395311000713140258722014562062159382150578182015747988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_183_400 : bothSeg evalE (oGrid.idx 183) (oGrid.dm 183) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 183) oGrid.kl oGrid.kr 400 400 ⟨false, 2645617504481887759719395311000713140258722014562062159382150578182015747988⟩ ⟨false, 0⟩ ⟨false, 4277315353711491374247381134898222577926145458875841919199001220121768778492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_183_800 : bothSeg evalE (oGrid.idx 183) (oGrid.dm 183) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 183) oGrid.kl oGrid.kr 400 800 ⟨false, 4277315353711491374247381134898222577926145458875841919199001220121768778492⟩ ⟨false, 0⟩ ⟨false, 4874532686333428691976200221106696198755018940122068138316831253061617799338⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_183_1200 : bothSeg evalE (oGrid.idx 183) (oGrid.dm 183) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 183) oGrid.kl oGrid.kr 400 1200 ⟨false, 4874532686333428691976200221106696198755018940122068138316831253061617799338⟩ ⟨false, 0⟩ ⟨false, 4937458180131195158777614798477726828703587320598203109574727784182052430946⟩ ⟨false, 19377797508010428007996700215629256625539363544093668609519863147304992938⟩ = true := by
  decide +kernel

theorem b_183_1600 : bothSeg evalE (oGrid.idx 183) (oGrid.dm 183) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 183) oGrid.kl oGrid.kr 400 1600 ⟨false, 4937458180131195158777614798477726828703587320598203109574727784182052430946⟩ ⟨false, 19377797508010428007996700215629256625539363544093668609519863147304992938⟩ ⟨false, 4766541612761641272072139922764454362370365715956681679255083414331987313512⟩ ⟨false, 190613508115807691842102350334721136048906908640310237564447513646741791484⟩ = true := by
  decide +kernel

theorem b_183_2000 : bothSeg evalE (oGrid.idx 183) (oGrid.dm 183) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 183) oGrid.kl oGrid.kr 400 2000 ⟨false, 4766541612761641272072139922764454362370365715956681679255083414331987313512⟩ ⟨false, 190613508115807691842102350334721136048906908640310237564447513646741791484⟩ ⟨false, 4729957644660315521198929394409530233674556736098545333605128927332097787820⟩ ⟨false, 228034481100414087617665748355508126135733565750547619308178528885297276386⟩ = true := by
  decide +kernel

theorem b_183_2400 : bothLoop evalE (oGrid.idx 183) (oGrid.dm 183) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 183) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4729957644660315521198929394409530233674556736098545333605128927332097787820⟩ ⟨false, 228034481100414087617665748355508126135733565750547619308178528885297276386⟩ = true := by
  decide +kernel

theorem o_row_183 : oGrid.row evalE 183 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_183_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_183_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_183_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_183_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_183_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_183_2000).1 (bothLoop_sound b_183_2400).1))))))

theorem n_row_183 : nGrid.row evalE 183 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_183_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_183_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_183_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_183_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_183_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_183_2000).2 (bothLoop_sound b_183_2400).2))))))

theorem b_184_0 : bothSeg evalE (oGrid.idx 184) (oGrid.dm 184) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 184) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2635289315063939279086043513038490755679176662321603100301440070959390379772⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_184_400 : bothSeg evalE (oGrid.idx 184) (oGrid.dm 184) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 184) oGrid.kl oGrid.kr 400 400 ⟨false, 2635289315063939279086043513038490755679176662321603100301440070959390379772⟩ ⟨false, 0⟩ ⟨false, 4260615512553461399279330785508820051735972214936749568882912787584569219344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_184_800 : bothSeg evalE (oGrid.idx 184) (oGrid.dm 184) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 184) oGrid.kl oGrid.kr 400 800 ⟨false, 4260615512553461399279330785508820051735972214936749568882912787584569219344⟩ ⟨false, 0⟩ ⟨false, 4855242152475374185133244100919598710279389815447992108507415860477606307952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_184_1200 : bothSeg evalE (oGrid.idx 184) (oGrid.dm 184) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 184) oGrid.kl oGrid.kr 400 1200 ⟨false, 4855242152475374185133244100919598710279389815447992108507415860477606307952⟩ ⟨false, 0⟩ ⟨false, 4917166117614454670697136760765691698651506154624385950274216395862480039534⟩ ⟨false, 19747077446681642006670553034986867347939090989519225302274191198673263626⟩ = true := by
  decide +kernel

theorem b_184_1600 : bothSeg evalE (oGrid.idx 184) (oGrid.dm 184) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 184) oGrid.kl oGrid.kr 400 1600 ⟨false, 4917166117614454670697136760765691698651506154624385950274216395862480039534⟩ ⟨false, 19747077446681642006670553034986867347939090989519225302274191198673263626⟩ ⟨false, 4746559099097690800416306432850833401953749511414140379828483104725720110834⟩ ⟨false, 190674203525033935155705214945363504460973157915140542320931438254612566776⟩ = true := by
  decide +kernel

theorem b_184_2000 : bothSeg evalE (oGrid.idx 184) (oGrid.dm 184) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 184) oGrid.kl oGrid.kr 400 2000 ⟨false, 4746559099097690800416306432850833401953749511414140379828483104725720110834⟩ ⟨false, 190674203525033935155705214945363504460973157915140542320931438254612566776⟩ ⟨false, 4710211387923942416872832545145478977437824927651615016615398621054849938588⟩ ⟨false, 227860612681610313344975343996887913623630920147521740117913862731761872416⟩ = true := by
  decide +kernel

theorem b_184_2400 : bothLoop evalE (oGrid.idx 184) (oGrid.dm 184) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 184) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4710211387923942416872832545145478977437824927651615016615398621054849938588⟩ ⟨false, 227860612681610313344975343996887913623630920147521740117913862731761872416⟩ = true := by
  decide +kernel

theorem o_row_184 : oGrid.row evalE 184 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_184_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_184_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_184_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_184_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_184_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_184_2000).1 (bothLoop_sound b_184_2400).1))))))

theorem n_row_184 : nGrid.row evalE 184 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_184_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_184_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_184_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_184_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_184_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_184_2000).2 (bothLoop_sound b_184_2400).2))))))

theorem b_185_0 : bothSeg evalE (oGrid.idx 185) (oGrid.dm 185) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 185) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2624992723789210241988724573829659095406548520209225379157114521366242752796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_185_400 : bothSeg evalE (oGrid.idx 185) (oGrid.dm 185) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 185) oGrid.kl oGrid.kr 400 400 ⟨false, 2624992723789210241988724573829659095406548520209225379157114521366242752796⟩ ⟨false, 0⟩ ⟨false, 4243964724499853585924588825755759424529918716291383753483282263717656327214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_185_800 : bothSeg evalE (oGrid.idx 185) (oGrid.dm 185) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 185) oGrid.kl oGrid.kr 400 800 ⟨false, 4243964724499853585924588825755759424529918716291383753483282263717656327214⟩ ⟨false, 0⟩ ⟨false, 4836006958220040822150278119408167345096406195312151177860115432525933030460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_185_1200 : bothSeg evalE (oGrid.idx 185) (oGrid.dm 185) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 185) oGrid.kl oGrid.kr 400 1200 ⟨false, 4836006958220040822150278119408167345096406195312151177860115432525933030460⟩ ⟨false, 0⟩ ⟨false, 4896932868460614694469708688490853156581165660595522922633593817433026120156⟩ ⟨false, 20115432611151971117571466311507607789331010250708250792255216811824761832⟩ = true := by
  decide +kernel

theorem b_185_1600 : bothSeg evalE (oGrid.idx 185) (oGrid.dm 185) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 185) oGrid.kl oGrid.kr 400 1600 ⟨false, 4896932868460614694469708688490853156581165660595522922633593817433026120156⟩ ⟨false, 20115432611151971117571466311507607789331010250708250792255216811824761832⟩ ⟨false, 4726635308502165388780511942323759470555399869955030551902378060617090661300⟩ ⟨false, 190733948897158610456567762734866514501054402466052529671126074980202854112⟩ = true := by
  decide +kernel

theorem b_185_2000 : bothSeg evalE (oGrid.idx 185) (oGrid.dm 185) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 185) oGrid.kl oGrid.kr 400 2000 ⟨false, 4726635308502165388780511942323759470555399869955030551902378060617090661300⟩ ⟨false, 190733948897158610456567762734866514501054402466052529671126074980202854112⟩ ⟨false, 4690523496165149012715964019676053544412811722136927695377283028941104845700⟩ ⟨false, 227686408238075694287983585994856206309023821664009387286099028308804634142⟩ = true := by
  decide +kernel

theorem b_185_2400 : bothLoop evalE (oGrid.idx 185) (oGrid.dm 185) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 185) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4690523496165149012715964019676053544412811722136927695377283028941104845700⟩ ⟨false, 227686408238075694287983585994856206309023821664009387286099028308804634142⟩ = true := by
  decide +kernel

theorem o_row_185 : oGrid.row evalE 185 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_185_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_185_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_185_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_185_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_185_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_185_2000).1 (bothLoop_sound b_185_2400).1))))))

theorem n_row_185 : nGrid.row evalE 185 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_185_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_185_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_185_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_185_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_185_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_185_2000).2 (bothLoop_sound b_185_2400).2))))))

theorem b_186_0 : bothSeg evalE (oGrid.idx 186) (oGrid.dm 186) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 186) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2614727583694461927550678055016700292275158340150556560650345911517218624604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_186_400 : bothSeg evalE (oGrid.idx 186) (oGrid.dm 186) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 186) oGrid.kl oGrid.kr 400 400 ⟨false, 2614727583694461927550678055016700292275158340150556560650345911517218624604⟩ ⟨false, 0⟩ ⟨false, 4227362667827595212688786179166864626113240184143689011257171385468691305286⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_186_800 : bothSeg evalE (oGrid.idx 186) (oGrid.dm 186) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 186) oGrid.kl oGrid.kr 400 800 ⟨false, 4227362667827595212688786179166864626113240184143689011257171385468691305286⟩ ⟨false, 0⟩ ⟨false, 4816826800325244027056450534914892675007586326368434531278045026444830636970⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_186_1200 : bothSeg evalE (oGrid.idx 186) (oGrid.dm 186) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 186) oGrid.kl oGrid.kr 400 1200 ⟨false, 4816826800325244027056450534914892675007586326368434531278045026444830636970⟩ ⟨false, 0⟩ ⟨false, 4876758338939497933519376899941815814449527436395261162069324916166125419628⟩ ⟨false, 20482794026888236098699424017507260257455728089444998812913822496608466816⟩ = true := by
  decide +kernel

theorem b_186_1600 : bothSeg evalE (oGrid.idx 186) (oGrid.dm 186) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 186) oGrid.kl oGrid.kr 400 1600 ⟨false, 4876758338939497933519376899941815814449527436395261162069324916166125419628⟩ ⟨false, 20482794026888236098699424017507260257455728089444998812913822496608466816⟩ ⟨false, 4706770362113536416871884270667082072131575808576252309030092378890823212214⟩ ⟨false, 190792449936472111822236659935276752663698491946028422868961070793609416888⟩ = true := by
  decide +kernel

theorem b_186_2000 : bothSeg evalE (oGrid.idx 186) (oGrid.dm 186) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 186) oGrid.kl oGrid.kr 400 2000 ⟨false, 4706770362113536416871884270667082072131575808576252309030092378890823212214⟩ ⟨false, 190792449936472111822236659935276752663698491946028422868961070793609416888⟩ ⟨false, 4670894128476825136727825941276254399115158454557673490589391895735196924110⟩ ⟨false, 227511035548375036193670422639477904954236650294634515063775196184716763500⟩ = true := by
  decide +kernel

theorem b_186_2400 : bothLoop evalE (oGrid.idx 186) (oGrid.dm 186) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 186) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4670894128476825136727825941276254399115158454557673490589391895735196924110⟩ ⟨false, 227511035548375036193670422639477904954236650294634515063775196184716763500⟩ = true := by
  decide +kernel

theorem o_row_186 : oGrid.row evalE 186 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_186_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_186_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_186_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_186_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_186_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_186_2000).1 (bothLoop_sound b_186_2400).1))))))

theorem n_row_186 : nGrid.row evalE 186 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_186_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_186_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_186_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_186_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_186_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_186_2000).2 (bothLoop_sound b_186_2400).2))))))

theorem b_187_0 : bothSeg evalE (oGrid.idx 187) (oGrid.dm 187) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 187) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2604493825263266916823343041841118399282701202594700061001377857052842439068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_187_400 : bothSeg evalE (oGrid.idx 187) (oGrid.dm 187) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 187) oGrid.kl oGrid.kr 400 400 ⟨false, 2604493825263266916823343041841118399282701202594700061001377857052842439068⟩ ⟨false, 0⟩ ⟨false, 4210809332844997084862691749564807405422235873654044361823776731390790263372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_187_800 : bothSeg evalE (oGrid.idx 187) (oGrid.dm 187) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 187) oGrid.kl oGrid.kr 400 800 ⟨false, 4210809332844997084862691749564807405422235873654044361823776731390790263372⟩ ⟨false, 0⟩ ⟨false, 4797701668189963628024563597421810419957938414787853835528793555596615156900⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_187_1200 : bothSeg evalE (oGrid.idx 187) (oGrid.dm 187) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 187) oGrid.kl oGrid.kr 400 1200 ⟨false, 4797701668189963628024563597421810419957938414787853835528793555596615156900⟩ ⟨false, 0⟩ ⟨false, 4856642672636466657480014908387278981753890226209198629511307725957448469380⟩ ⟨false, 20848845203848005796436383782634313090486558986118183619519572508511673370⟩ = true := by
  decide +kernel

theorem b_187_1600 : bothSeg evalE (oGrid.idx 187) (oGrid.dm 187) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 187) oGrid.kl oGrid.kr 400 1600 ⟨false, 4856642672636466657480014908387278981753890226209198629511307725957448469380⟩ ⟨false, 20848845203848005796436383782634313090486558986118183619519572508511673370⟩ ⟨false, 4686963755493186958873969290612345555350004410591589415497026423857863876448⟩ ⟨false, 190850060811441481314599560172694928129516658635193331879700256062395849298⟩ = true := by
  decide +kernel

theorem b_187_2000 : bothSeg evalE (oGrid.idx 187) (oGrid.dm 187) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 187) oGrid.kl oGrid.kr 400 2000 ⟨false, 4686963755493186958873969290612345555350004410591589415497026423857863876448⟩ ⟨false, 190850060811441481314599560172694928129516658635193331879700256062395849298⟩ ⟨false, 4651322800441101924483119442915945268802706505504353906601129465270708178038⟩ ⟨false, 227335248048375025472207632980914496719543147907963331521046167772567837640⟩ = true := by
  decide +kernel

theorem b_187_2400 : bothLoop evalE (oGrid.idx 187) (oGrid.dm 187) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 187) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4651322800441101924483119442915945268802706505504353906601129465270708178038⟩ ⟨false, 227335248048375025472207632980914496719543147907963331521046167772567837640⟩ = true := by
  decide +kernel

theorem o_row_187 : oGrid.row evalE 187 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_187_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_187_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_187_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_187_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_187_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_187_2000).1 (bothLoop_sound b_187_2400).1))))))

theorem n_row_187 : nGrid.row evalE 187 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_187_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_187_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_187_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_187_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_187_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_187_2000).2 (bothLoop_sound b_187_2400).2))))))

theorem b_188_0 : bothSeg evalE (oGrid.idx 188) (oGrid.dm 188) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 188) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2594291397568333858085676891013130794527494183949404948951444750211128608528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_188_400 : bothSeg evalE (oGrid.idx 188) (oGrid.dm 188) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 188) oGrid.kl oGrid.kr 400 400 ⟨false, 2594291397568333858085676891013130794527494183949404948951444750211128608528⟩ ⟨false, 0⟩ ⟨false, 4194304581618282942353736187019310446571397530091056927648568096805177364948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_188_800 : bothSeg evalE (oGrid.idx 188) (oGrid.dm 188) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 188) oGrid.kl oGrid.kr 400 800 ⟨false, 4194304581618282942353736187019310446571397530091056927648568096805177364948⟩ ⟨false, 0⟩ ⟨false, 4778631408587426508773298824951276999623010665291363812021424769980569730614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_188_1200 : bothSeg evalE (oGrid.idx 188) (oGrid.dm 188) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 188) oGrid.kl oGrid.kr 400 1200 ⟨false, 4778631408587426508773298824951276999623010665291363812021424769980569730614⟩ ⟨false, 0⟩ ⟨false, 4836585955623881212925070213461476093410494700804303903637235540830448138388⟩ ⟨false, 21213379808858199601205523250295703495386217710602140791867883563448825458⟩ = true := by
  decide +kernel

theorem b_188_1600 : bothSeg evalE (oGrid.idx 188) (oGrid.dm 188) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 188) oGrid.kl oGrid.kr 400 1600 ⟨false, 4836585955623881212925070213461476093410494700804303903637235540830448138388⟩ ⟨false, 21213379808858199601205523250295703495386217710602140791867883563448825458⟩ ⟨false, 4667215677554798749329357941710043422429701195130644647855707794915827791776⟩ ⟨false, 190906555486101886495741288771941267650832824848908605728126345106155753618⟩ = true := by
  decide +kernel

theorem b_188_2000 : bothSeg evalE (oGrid.idx 188) (oGrid.dm 188) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 188) oGrid.kl oGrid.kr 400 2000 ⟨false, 4667215677554798749329357941710043422429701195130644647855707794915827791776⟩ ⟨false, 190906555486101886495741288771941267650832824848908605728126345106155753618⟩ ⟨false, 4631809735602180283000259410166505567066214163259661687941920884414997957138⟩ ⟨false, 227158560469255374951851395573223085673943277630729317155669689622967941862⟩ = true := by
  decide +kernel

theorem b_188_2400 : bothLoop evalE (oGrid.idx 188) (oGrid.dm 188) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 188) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4631809735602180283000259410166505567066214163259661687941920884414997957138⟩ ⟨false, 227158560469255374951851395573223085673943277630729317155669689622967941862⟩ = true := by
  decide +kernel

theorem o_row_188 : oGrid.row evalE 188 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_188_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_188_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_188_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_188_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_188_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_188_2000).1 (bothLoop_sound b_188_2400).1))))))

theorem n_row_188 : nGrid.row evalE 188 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_188_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_188_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_188_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_188_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_188_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_188_2000).2 (bothLoop_sound b_188_2400).2))))))

theorem b_189_0 : bothSeg evalE (oGrid.idx 189) (oGrid.dm 189) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 189) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2584120207259002704237190827317050671548381645124570562793701768397070060452⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_189_400 : bothSeg evalE (oGrid.idx 189) (oGrid.dm 189) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 189) oGrid.kl oGrid.kr 400 400 ⟨false, 2584120207259002704237190827317050671548381645124570562793701768397070060452⟩ ⟨false, 0⟩ ⟨false, 4177848364941892965006998167672748295000093437503573430147576833463613523066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_189_800 : bothSeg evalE (oGrid.idx 189) (oGrid.dm 189) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 189) oGrid.kl oGrid.kr 400 800 ⟨false, 4177848364941892965006998167672748295000093437503573430147576833463613523066⟩ ⟨false, 0⟩ ⟨false, 4759615975146630529036783503076355296356046263575338469956257316589925653834⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_189_1200 : bothSeg evalE (oGrid.idx 189) (oGrid.dm 189) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 189) oGrid.kl oGrid.kr 400 1200 ⟨false, 4759615975146630529036783503076355296356046263575338469956257316589925653834⟩ ⟨false, 0⟩ ⟨false, 4816588297854889785376176522795725621857830554122062641456025851071665506520⟩ ⟨false, 21576250921738275069885942242076818226002951513866663039475665778335912574⟩ = true := by
  decide +kernel

theorem b_189_1600 : bothSeg evalE (oGrid.idx 189) (oGrid.dm 189) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 189) oGrid.kl oGrid.kr 400 1600 ⟨false, 4816588297854889785376176522795725621857830554122062641456025851071665506520⟩ ⟨false, 21576250921738275069885942242076818226002951513866663039475665778335912574⟩ ⟨false, 4647525987122199121389487857954619859217511321158381374691998839402921322538⟩ ⟨false, 190962456088086478238854261172077495918824004577364431788877426598236899184⟩ = true := by
  decide +kernel

theorem b_189_2000 : bothSeg evalE (oGrid.idx 189) (oGrid.dm 189) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 189) oGrid.kl oGrid.kr 400 2000 ⟨false, 4647525987122199121389487857954619859217511321158381374691998839402921322538⟩ ⟨false, 190962456088086478238854261172077495918824004577364431788877426598236899184⟩ ⟨false, 4612354807456055287847067619723913020320856094465921294240894228426597066730⟩ ⟨false, 226981390302458918137491901594821932408099368531663339126977461752977988776⟩ = true := by
  decide +kernel

theorem b_189_2400 : bothLoop evalE (oGrid.idx 189) (oGrid.dm 189) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 189) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4612354807456055287847067619723913020320856094465921294240894228426597066730⟩ ⟨false, 226981390302458918137491901594821932408099368531663339126977461752977988776⟩ = true := by
  decide +kernel

theorem o_row_189 : oGrid.row evalE 189 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_189_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_189_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_189_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_189_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_189_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_189_2000).1 (bothLoop_sound b_189_2400).1))))))

theorem n_row_189 : nGrid.row evalE 189 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_189_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_189_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_189_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_189_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_189_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_189_2000).2 (bothLoop_sound b_189_2400).2))))))

theorem b_190_0 : bothSeg evalE (oGrid.idx 190) (oGrid.dm 190) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 190) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2573980141209471181709968709250840878033433449190106612841137134218217167246⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_190_400 : bothSeg evalE (oGrid.idx 190) (oGrid.dm 190) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 190) oGrid.kl oGrid.kr 400 400 ⟨false, 2573980141209471181709968709250840878033433449190106612841137134218217167246⟩ ⟨false, 0⟩ ⟨false, 4161440493270670069807988208314336776667670372878801331180785385339202955328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_190_800 : bothSeg evalE (oGrid.idx 190) (oGrid.dm 190) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 190) oGrid.kl oGrid.kr 400 800 ⟨false, 4161440493270670069807988208314336776667670372878801331180785385339202955328⟩ ⟨false, 0⟩ ⟨false, 4740655179906377847058335159725385542194848978302672947740872383448629525068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_190_1200 : bothSeg evalE (oGrid.idx 190) (oGrid.dm 190) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 190) oGrid.kl oGrid.kr 400 1200 ⟨false, 4740655179906377847058335159725385542194848978302672947740872383448629525068⟩ ⟨false, 0⟩ ⟨false, 4796649769837025672344819171544716141076388853493857549343471310759178675418⟩ ⟨false, 21937176975843613260018753862061740450379625227707754510091337960026229548⟩ = true := by
  decide +kernel

theorem b_190_1600 : bothSeg evalE (oGrid.idx 190) (oGrid.dm 190) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 190) oGrid.kl oGrid.kr 400 1600 ⟨false, 4796649769837025672344819171544716141076388853493857549343471310759178675418⟩ ⟨false, 21937176975843613260018753862061740450379625227707754510091337960026229548⟩ ⟨false, 4627894454457963284818466707065702399942368354684252907382213351808338253516⟩ ⟨false, 191017540845509261026329453822773029165936232327401725293242806443677371470⟩ = true := by
  decide +kernel

theorem b_190_2000 : bothSeg evalE (oGrid.idx 190) (oGrid.dm 190) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 190) oGrid.kl oGrid.kr 400 2000 ⟨false, 4627894454457963284818466707065702399942368354684252907382213351808338253516⟩ ⟨false, 191017540845509261026329453822773029165936232327401725293242806443677371470⟩ ⟨false, 4592957836551279373848941099156126132811906483381953013131944634831549773124⟩ ⟨false, 226803890095022602252474901565055293949511872557949393433971170250713740062⟩ = true := by
  decide +kernel

theorem b_190_2400 : bothLoop evalE (oGrid.idx 190) (oGrid.dm 190) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 190) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4592957836551279373848941099156126132811906483381953013131944634831549773124⟩ ⟨false, 226803890095022602252474901565055293949511872557949393433971170250713740062⟩ = true := by
  decide +kernel

theorem o_row_190 : oGrid.row evalE 190 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_190_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_190_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_190_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_190_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_190_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_190_2000).1 (bothLoop_sound b_190_2400).1))))))

theorem n_row_190 : nGrid.row evalE 190 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_190_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_190_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_190_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_190_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_190_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_190_2000).2 (bothLoop_sound b_190_2400).2))))))

theorem b_191_0 : bothSeg evalE (oGrid.idx 191) (oGrid.dm 191) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 191) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2563871134761799231268884131741410354716556156384726395019942946378128512464⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_191_400 : bothSeg evalE (oGrid.idx 191) (oGrid.dm 191) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 191) oGrid.kl oGrid.kr 400 400 ⟨false, 2563871134761799231268884131741410354716556156384726395019942946378128512464⟩ ⟨false, 0⟩ ⟨false, 4145080856920327427891193091885639706186248699435394125987418749823110582298⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_191_800 : bothSeg evalE (oGrid.idx 191) (oGrid.dm 191) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 191) oGrid.kl oGrid.kr 400 800 ⟨false, 4145080856920327427891193091885639706186248699435394125987418749823110582298⟩ ⟨false, 0⟩ ⟨false, 4721748891289223642541065654738850539978128877552077172699745744028578303268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_191_1200 : bothSeg evalE (oGrid.idx 191) (oGrid.dm 191) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 191) oGrid.kl oGrid.kr 400 1200 ⟨false, 4721748891289223642541065654738850539978128877552077172699745744028578303268⟩ ⟨false, 0⟩ ⟨false, 4776770375420578187756372293959342001630708031758409594529243209706761741812⟩ ⟨false, 22296049123013096392959546105967663855735083055559724205600610479206190798⟩ = true := by
  decide +kernel

theorem b_191_1600 : bothSeg evalE (oGrid.idx 191) (oGrid.dm 191) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 191) oGrid.kl oGrid.kr 400 1600 ⟨false, 4776770375420578187756372293959342001630708031758409594529243209706761741812⟩ ⟨false, 22296049123013096392959546105967663855735083055559724205600610479206190798⟩ ⟨false, 4608320982535980570388932920131238865128959091041902165660224061382351991796⟩ ⟨false, 191071486140257234167378455115471713764244501398507247599602808074235753148⟩ = true := by
  decide +kernel

theorem b_191_2000 : bothSeg evalE (oGrid.idx 191) (oGrid.dm 191) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 191) oGrid.kl oGrid.kr 400 2000 ⟨false, 4608320982535980570388932920131238865128959091041902165660224061382351991796⟩ ⟨false, 191071486140257234167378455115471713764244501398507247599602808074235753148⟩ ⟨false, 4573618712497106959571381697328633021510756388577662497949994014858907973692⟩ ⟨false, 226625193994131959778786613391618315014917121572948843028568485662744497496⟩ = true := by
  decide +kernel

theorem b_191_2400 : bothLoop evalE (oGrid.idx 191) (oGrid.dm 191) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 191) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4573618712497106959571381697328633021510756388577662497949994014858907973692⟩ ⟨false, 226625193994131959778786613391618315014917121572948843028568485662744497496⟩ = true := by
  decide +kernel

theorem o_row_191 : oGrid.row evalE 191 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_191_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_191_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_191_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_191_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_191_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_191_2000).1 (bothLoop_sound b_191_2400).1))))))

theorem n_row_191 : nGrid.row evalE 191 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_191_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_191_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_191_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_191_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_191_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_191_2000).2 (bothLoop_sound b_191_2400).2))))))

theorem o_blk_168 : allFrom (fun j => oGrid.row evalE j) 168 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 168) o_row_168 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 169) o_row_169 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 170) o_row_170 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 171) o_row_171 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 172) o_row_172 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 173) o_row_173 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 174) o_row_174 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 175) o_row_175 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 176) o_row_176 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 177) o_row_177 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 178) o_row_178 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 179) o_row_179 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 180) o_row_180 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 181) o_row_181 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 182) o_row_182 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 183) o_row_183 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 184) o_row_184 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 185) o_row_185 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 186) o_row_186 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 187) o_row_187 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 188) o_row_188 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 189) o_row_189 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 190) o_row_190 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 191) o_row_191 (allFrom_zero (fun j => oGrid.row evalE j) 192)))))))))))))))))))))))))

theorem n_blk_168 : allFrom (fun j => nGrid.row evalE j) 168 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 168) n_row_168 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 169) n_row_169 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 170) n_row_170 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 171) n_row_171 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 172) n_row_172 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 173) n_row_173 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 174) n_row_174 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 175) n_row_175 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 176) n_row_176 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 177) n_row_177 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 178) n_row_178 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 179) n_row_179 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 180) n_row_180 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 181) n_row_181 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 182) n_row_182 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 183) n_row_183 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 184) n_row_184 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 185) n_row_185 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 186) n_row_186 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 187) n_row_187 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 188) n_row_188 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 189) n_row_189 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 190) n_row_190 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 191) n_row_191 (allFrom_zero (fun j => nGrid.row evalE j) 192)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
