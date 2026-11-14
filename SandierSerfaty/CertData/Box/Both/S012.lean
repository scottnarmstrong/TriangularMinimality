/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 12 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `288`–`311`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_288_0 : bothSeg evalE (oGrid.idx 288) (oGrid.dm 288) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 288) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1718916008532099401633908428279595286167470891886245575608743539870021209406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_288_400 : bothSeg evalE (oGrid.idx 288) (oGrid.dm 288) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 288) oGrid.kl oGrid.kr 400 400 ⟨false, 1718916008532099401633908428279595286167470891886245575608743539870021209406⟩ ⟨false, 0⟩ ⟨false, 2770798467318230536845130519316950299747966477977360735026369401312343193734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_288_800 : bothSeg evalE (oGrid.idx 288) (oGrid.dm 288) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 288) oGrid.kl oGrid.kr 400 800 ⟨false, 2770798467318230536845130519316950299747966477977360735026369401312343193734⟩ ⟨false, 0⟩ ⟨false, 3129647346499489389193704870843144818483584123047283168106522223096299225850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_288_1200 : bothSeg evalE (oGrid.idx 288) (oGrid.dm 288) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 288) oGrid.kl oGrid.kr 400 1200 ⟨false, 3129647346499489389193704870843144818483584123047283168106522223096299225850⟩ ⟨false, 0⟩ ⟨false, 3126689990294532569710264911613550598257843720218700949641027569418431596860⟩ ⟨false, 33069462716349245092994858975062869763427383103155004888016968677007745000⟩ = true := by
  decide +kernel

theorem b_288_1600 : bothSeg evalE (oGrid.idx 288) (oGrid.dm 288) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 288) oGrid.kl oGrid.kr 400 1600 ⟨false, 3126689990294532569710264911613550598257843720218700949641027569418431596860⟩ ⟨false, 33069462716349245092994858975062869763427383103155004888016968677007745000⟩ ⟨false, 2967704592945874637400149895601771931737405460365733192726032053573362969718⟩ ⟨false, 192164239502045562016376580044889753114734646151991558937400114180981384182⟩ = true := by
  decide +kernel

theorem b_288_2000 : bothSeg evalE (oGrid.idx 288) (oGrid.dm 288) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 288) oGrid.kl oGrid.kr 400 2000 ⟨false, 2967704592945874637400149895601771931737405460365733192726032053573362969718⟩ ⟨false, 192164239502045562016376580044889753114734646151991558937400114180981384182⟩ ⟨false, 2956188527497748793783799801949033148476010114089858752806315352183963670942⟩ ⟨false, 208238031303797029891785814516061722539262577100453657293378923322755863440⟩ = true := by
  decide +kernel

theorem b_288_2400 : bothLoop evalE (oGrid.idx 288) (oGrid.dm 288) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 288) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2956188527497748793783799801949033148476010114089858752806315352183963670942⟩ ⟨false, 208238031303797029891785814516061722539262577100453657293378923322755863440⟩ = true := by
  decide +kernel

theorem o_row_288 : oGrid.row evalE 288 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_288_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_288_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_288_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_288_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_288_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_288_2000).1 (bothLoop_sound b_288_2400).1))))))

theorem n_row_288 : nGrid.row evalE 288 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_288_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_288_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_288_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_288_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_288_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_288_2000).2 (bothLoop_sound b_288_2400).2))))))

theorem b_289_0 : bothSeg evalE (oGrid.idx 289) (oGrid.dm 289) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 289) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1711487515554748133359448016027728282026189203928356452822477474439041237522⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_289_400 : bothSeg evalE (oGrid.idx 289) (oGrid.dm 289) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 289) oGrid.kl oGrid.kr 400 400 ⟨false, 1711487515554748133359448016027728282026189203928356452822477474439041237522⟩ ⟨false, 0⟩ ⟨false, 2758658888554204283384236854876161414732299694490106544581054208158414584610⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_289_800 : bothSeg evalE (oGrid.idx 289) (oGrid.dm 289) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 289) oGrid.kl oGrid.kr 400 800 ⟨false, 2758658888554204283384236854876161414732299694490106544581054208158414584610⟩ ⟨false, 0⟩ ⟨false, 3115555208367317445618725882624199552648823353985262817179244377676561647314⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_289_1200 : bothSeg evalE (oGrid.idx 289) (oGrid.dm 289) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 289) oGrid.kl oGrid.kr 400 1200 ⟨false, 3115555208367317445618725882624199552648823353985262817179244377676561647314⟩ ⟨false, 0⟩ ⟨false, 3112310597288762525904800791523351879150003489446650952121725477242499303504⟩ ⟨false, 33008961244024391230004454717531676363963047377175282737993096880875622960⟩ = true := by
  decide +kernel

theorem b_289_1600 : bothSeg evalE (oGrid.idx 289) (oGrid.dm 289) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 289) oGrid.kl oGrid.kr 400 1600 ⟨false, 3112310597288762525904800791523351879150003489446650952121725477242499303504⟩ ⟨false, 33008961244024391230004454717531676363963047377175282737993096880875622960⟩ ⟨false, 2953272065519676174376332163184808677271378056277622253169508042651566068194⟩ ⟨false, 192138163373243352808550243995288003597204626870262943247639652127079912866⟩ = true := by
  decide +kernel

theorem b_289_2000 : bothSeg evalE (oGrid.idx 289) (oGrid.dm 289) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 289) oGrid.kl oGrid.kr 400 2000 ⟨false, 2953272065519676174376332163184808677271378056277622253169508042651566068194⟩ ⟨false, 192138163373243352808550243995288003597204626870262943247639652127079912866⟩ ⟨false, 2941980666451990859614081214987113642694468027534429676737037014675905831456⟩ ⟨false, 208058498241037805429657852090922763238724767288131654849344493899684919798⟩ = true := by
  decide +kernel

theorem b_289_2400 : bothLoop evalE (oGrid.idx 289) (oGrid.dm 289) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 289) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2941980666451990859614081214987113642694468027534429676737037014675905831456⟩ ⟨false, 208058498241037805429657852090922763238724767288131654849344493899684919798⟩ = true := by
  decide +kernel

theorem o_row_289 : oGrid.row evalE 289 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_289_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_289_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_289_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_289_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_289_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_289_2000).1 (bothLoop_sound b_289_2400).1))))))

theorem n_row_289 : nGrid.row evalE 289 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_289_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_289_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_289_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_289_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_289_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_289_2000).2 (bothLoop_sound b_289_2400).2))))))

theorem b_290_0 : bothSeg evalE (oGrid.idx 290) (oGrid.dm 290) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 290) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1704082987763921930194944451493919744377431159622819901697500397968936590302⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_290_400 : bothSeg evalE (oGrid.idx 290) (oGrid.dm 290) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 290) oGrid.kl oGrid.kr 400 400 ⟨false, 1704082987763921930194944451493919744377431159622819901697500397968936590302⟩ ⟨false, 0⟩ ⟨false, 2746557567820390207306741650896929561706399298686072626355765617845701980180⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_290_800 : bothSeg evalE (oGrid.idx 290) (oGrid.dm 290) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 290) oGrid.kl oGrid.kr 400 800 ⟨false, 2746557567820390207306741650896929561706399298686072626355765617845701980180⟩ ⟨false, 0⟩ ⟨false, 3101507085905521108974562951350644937145026793449323239639296879010806475742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_290_1200 : bothSeg evalE (oGrid.idx 290) (oGrid.dm 290) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 290) oGrid.kl oGrid.kr 400 1200 ⟨false, 3101507085905521108974562951350644937145026793449323239639296879010806475742⟩ ⟨false, 0⟩ ⟨false, 3097976155314245898220184121896926406802251028004375713122248682174481347720⟩ ⟨false, 32948695653110139244898212393140360508164000346400589533702087457739349990⟩ = true := by
  decide +kernel

theorem b_290_1600 : bothSeg evalE (oGrid.idx 290) (oGrid.dm 290) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 290) oGrid.kl oGrid.kr 400 1600 ⟨false, 3097976155314245898220184121896926406802251028004375713122248682174481347720⟩ ⟨false, 32948695653110139244898212393140360508164000346400589533702087457739349990⟩ ⟨false, 2938886384375774790466652103869850554302066042974040286500455334456784817074⟩ ⟨false, 192111593138470087013056120263787048044633990221299160975291874523502903022⟩ = true := by
  decide +kernel

theorem b_290_2000 : bothSeg evalE (oGrid.idx 290) (oGrid.dm 290) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 290) oGrid.kl oGrid.kr 400 2000 ⟨false, 2938886384375774790466652103869850554302066042974040286500455334456784817074⟩ ⟨false, 192111593138470087013056120263787048044633990221299160975291874523502903022⟩ ⟨false, 2927818349632998058029468275001243222564369359490436282288139304274905379286⟩ ⟨false, 207879782276856044390353080605693655741186714167235168838922282888031510134⟩ = true := by
  decide +kernel

theorem b_290_2400 : bothLoop evalE (oGrid.idx 290) (oGrid.dm 290) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 290) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2927818349632998058029468275001243222564369359490436282288139304274905379286⟩ ⟨false, 207879782276856044390353080605693655741186714167235168838922282888031510134⟩ = true := by
  decide +kernel

theorem o_row_290 : oGrid.row evalE 290 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_290_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_290_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_290_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_290_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_290_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_290_2000).1 (bothLoop_sound b_290_2400).1))))))

theorem n_row_290 : nGrid.row evalE 290 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_290_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_290_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_290_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_290_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_290_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_290_2000).2 (bothLoop_sound b_290_2400).2))))))

theorem b_291_0 : bothSeg evalE (oGrid.idx 291) (oGrid.dm 291) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 291) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1696702377075331450955708996363629509095884808430305197297139592166448283138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_291_400 : bothSeg evalE (oGrid.idx 291) (oGrid.dm 291) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 291) oGrid.kl oGrid.kr 400 400 ⟨false, 1696702377075331450955708996363629509095884808430305197297139592166448283138⟩ ⟨false, 0⟩ ⟨false, 2734494396254137722560189221407932820259869873126953881127587710155624880094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_291_800 : bothSeg evalE (oGrid.idx 291) (oGrid.dm 291) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 291) oGrid.kl oGrid.kr 400 800 ⟨false, 2734494396254137722560189221407932820259869873126953881127587710155624880094⟩ ⟨false, 0⟩ ⟨false, 3087502921094244744759053568273314474159904723124459420128274614694671322224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_291_1200 : bothSeg evalE (oGrid.idx 291) (oGrid.dm 291) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 291) oGrid.kl oGrid.kr 400 1200 ⟨false, 3087502921094244744759053568273314474159904723124459420128274614694671322224⟩ ⟨false, 0⟩ ⟨false, 3083687089064410230100993726770399138874628850559253242753686129551926928594⟩ ⟨false, 32888075687553320388015310877137928225152558080036393293862817405299258432⟩ = true := by
  decide +kernel

theorem b_291_1600 : bothSeg evalE (oGrid.idx 291) (oGrid.dm 291) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 291) oGrid.kl oGrid.kr 400 1600 ⟨false, 3083687089064410230100993726770399138874628850559253242753686129551926928594⟩ ⟨false, 32888075687553320388015310877137928225152558080036393293862817405299258432⟩ ⟨false, 2924548173999076529451402379420396168590451255700555680168344717242175528252⟩ ⟨false, 192083951231249099947046008769185913831390216446277594502213385255466329412⟩ = true := by
  decide +kernel

theorem b_291_2000 : bothSeg evalE (oGrid.idx 291) (oGrid.dm 291) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 291) oGrid.kl oGrid.kr 400 2000 ⟨false, 2924548173999076529451402379420396168590451255700555680168344717242175528252⟩ ⟨false, 192083951231249099947046008769185913831390216446277594502213385255466329412⟩ ⟨false, 2913702161172357391281216013345188165463694500381297719232480617701799302990⟩ ⟨false, 207700655098261337222203432404814625975874122171783977340459676189955046346⟩ = true := by
  decide +kernel

theorem b_291_2400 : bothLoop evalE (oGrid.idx 291) (oGrid.dm 291) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 291) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2913702161172357391281216013345188165463694500381297719232480617701799302990⟩ ⟨false, 207700655098261337222203432404814625975874122171783977340459676189955046346⟩ = true := by
  decide +kernel

theorem o_row_291 : oGrid.row evalE 291 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_291_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_291_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_291_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_291_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_291_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_291_2000).1 (bothLoop_sound b_291_2400).1))))))

theorem n_row_291 : nGrid.row evalE 291 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_291_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_291_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_291_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_291_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_291_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_291_2000).2 (bothLoop_sound b_291_2400).2))))))

theorem b_292_0 : bothSeg evalE (oGrid.idx 292) (oGrid.dm 292) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 292) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1689345584455222603372657410597717493960793487605958190937479481056905150746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_292_400 : bothSeg evalE (oGrid.idx 292) (oGrid.dm 292) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 292) oGrid.kl oGrid.kr 400 400 ⟨false, 1689345584455222603372657410597717493960793487605958190937479481056905150746⟩ ⟨false, 0⟩ ⟨false, 2722469248365741996279249205542219447700520269966326837345619542174693105822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_292_800 : bothSeg evalE (oGrid.idx 292) (oGrid.dm 292) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 292) oGrid.kl oGrid.kr 400 800 ⟨false, 2722469248365741996279249205542219447700520269966326837345619542174693105822⟩ ⟨false, 0⟩ ⟨false, 3073542576345830347843810339050382454128430827348061424134016679320727833358⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_292_1200 : bothSeg evalE (oGrid.idx 292) (oGrid.dm 292) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 292) oGrid.kl oGrid.kr 400 1200 ⟨false, 3073542576345830347843810339050382454128430827348061424134016679320727833358⟩ ⟨false, 0⟩ ⟨false, 3069442884840323273613204300439367951256572661066957497912729439415396966302⟩ ⟨false, 32827236809299892770664688136189180358648201122659798604823626200284334932⟩ = true := by
  decide +kernel

theorem b_292_1600 : bothSeg evalE (oGrid.idx 292) (oGrid.dm 292) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 292) oGrid.kl oGrid.kr 400 1600 ⟨false, 3069442884840323273613204300439367951256572661066957497912729439415396966302⟩ ⟨false, 32827236809299892770664688136189180358648201122659798604823626200284334932⟩ ⟨false, 2910257076249880455636733634780784457084974861895579938315937329224517735362⟩ ⟨false, 192055429184592158797725618121363233297457999888302381772840840313280305756⟩ = true := by
  decide +kernel

theorem b_292_2000 : bothSeg evalE (oGrid.idx 292) (oGrid.dm 292) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 292) oGrid.kl oGrid.kr 400 2000 ⟨false, 2910257076249880455636733634780784457084974861895579938315937329224517735362⟩ ⟨false, 192055429184592158797725618121363233297457999888302381772840840313280305756⟩ ⟨false, 2899631734383140193801819066524175865273809277374572452476802523423400747118⟩ ⟨false, 207521292395423481905195506095301928615353519217646941436909747471236086736⟩ = true := by
  decide +kernel

theorem b_292_2400 : bothLoop evalE (oGrid.idx 292) (oGrid.dm 292) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 292) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2899631734383140193801819066524175865273809277374572452476802523423400747118⟩ ⟨false, 207521292395423481905195506095301928615353519217646941436909747471236086736⟩ = true := by
  decide +kernel

theorem o_row_292 : oGrid.row evalE 292 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_292_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_292_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_292_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_292_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_292_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_292_2000).1 (bothLoop_sound b_292_2400).1))))))

theorem n_row_292 : nGrid.row evalE 292 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_292_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_292_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_292_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_292_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_292_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_292_2000).2 (bothLoop_sound b_292_2400).2))))))

theorem b_293_0 : bothSeg evalE (oGrid.idx 293) (oGrid.dm 293) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 293) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1682012571347521816852491091834244868235790221821190426303906787318358964792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_293_400 : bothSeg evalE (oGrid.idx 293) (oGrid.dm 293) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 293) oGrid.kl oGrid.kr 400 400 ⟨false, 1682012571347521816852491091834244868235790221821190426303906787318358964792⟩ ⟨false, 0⟩ ⟨false, 2710482071338746342006551685207729116078858732688873377132331539151147923932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_293_800 : bothSeg evalE (oGrid.idx 293) (oGrid.dm 293) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 293) oGrid.kl oGrid.kr 400 800 ⟨false, 2710482071338746342006551685207729116078858732688873377132331539151147923932⟩ ⟨false, 0⟩ ⟨false, 3059625927229224125121136688536294579643842138386831358539416651964435825658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_293_1200 : bothSeg evalE (oGrid.idx 293) (oGrid.dm 293) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 293) oGrid.kl oGrid.kr 400 1200 ⟨false, 3059625927229224125121136688536294579643842138386831358539416651964435825658⟩ ⟨false, 0⟩ ⟨false, 3055242870192510016280940970095441482691030452735729088756633613783684296988⟩ ⟨false, 32766448901713854839084491310896028791754939069206742328840728454281116758⟩ = true := by
  decide +kernel

theorem b_293_1600 : bothSeg evalE (oGrid.idx 293) (oGrid.dm 293) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 293) oGrid.kl oGrid.kr 400 1600 ⟨false, 3055242870192510016280940970095441482691030452735729088756633613783684296988⟩ ⟨false, 32766448901713854839084491310896028791754939069206742328840728454281116758⟩ ⟨false, 2896012738484409020140620496015335118583877305640339594329845839943647059090⟩ ⟨false, 192026187677606011993179075591356024377170355548131096906564423005031620876⟩ = true := by
  decide +kernel

theorem b_293_2000 : bothSeg evalE (oGrid.idx 293) (oGrid.dm 293) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 293) oGrid.kl oGrid.kr 400 2000 ⟨false, 2896012738484409020140620496015335118583877305640339594329845839943647059090⟩ ⟨false, 192026187677606011993179075591356024377170355548131096906564423005031620876⟩ ⟨false, 2885606648122101722227881873436681848183734713095025855751526118913591036164⟩ ⟨false, 207342609145542725212614423898136533987184213336272901971635207501959279388⟩ = true := by
  decide +kernel

theorem b_293_2400 : bothLoop evalE (oGrid.idx 293) (oGrid.dm 293) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 293) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2885606648122101722227881873436681848183734713095025855751526118913591036164⟩ ⟨false, 207342609145542725212614423898136533987184213336272901971635207501959279388⟩ = true := by
  decide +kernel

theorem o_row_293 : oGrid.row evalE 293 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_293_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_293_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_293_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_293_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_293_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_293_2000).1 (bothLoop_sound b_293_2400).1))))))

theorem n_row_293 : nGrid.row evalE 293 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_293_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_293_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_293_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_293_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_293_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_293_2000).2 (bothLoop_sound b_293_2400).2))))))

theorem b_294_0 : bothSeg evalE (oGrid.idx 294) (oGrid.dm 294) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 294) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1674703287778557156981841823731978838134321031966667633928277963204196665118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_294_400 : bothSeg evalE (oGrid.idx 294) (oGrid.dm 294) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 294) oGrid.kl oGrid.kr 400 400 ⟨false, 1674703287778557156981841823731978838134321031966667633928277963204196665118⟩ ⟨false, 0⟩ ⟨false, 2698532784606186740339694493861563395053426007150658690857290551969667924650⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_294_800 : bothSeg evalE (oGrid.idx 294) (oGrid.dm 294) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 294) oGrid.kl oGrid.kr 400 800 ⟨false, 2698532784606186740339694493861563395053426007150658690857290551969667924650⟩ ⟨false, 0⟩ ⟨false, 3045752964429899901252018791942343276680960247574868934887091009245213272268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_294_1200 : bothSeg evalE (oGrid.idx 294) (oGrid.dm 294) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 294) oGrid.kl oGrid.kr 400 1200 ⟨false, 3045752964429899901252018791942343276680960247574868934887091009245213272268⟩ ⟨false, 0⟩ ⟨false, 3041086910317281007049706386738678019865618481174083592289494847525358729372⟩ ⟨false, 32705919664387188404276356695934494509129180429768869912146663763114161606⟩ = true := by
  decide +kernel

theorem b_294_1600 : bothSeg evalE (oGrid.idx 294) (oGrid.dm 294) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 294) oGrid.kl oGrid.kr 400 1600 ⟨false, 3041086910317281007049706386738678019865618481174083592289494847525358729372⟩ ⟨false, 32705919664387188404276356695934494509129180429768869912146663763114161606⟩ ⟨false, 2881815101340353919183581671532800342110807823681435578850102570426257943742⟩ ⟨false, 191996568364235564707581384819120907615392580623373805978989009416113273116⟩ = true := by
  decide +kernel

theorem b_294_2000 : bothSeg evalE (oGrid.idx 294) (oGrid.dm 294) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 294) oGrid.kl oGrid.kr 400 2000 ⟨false, 2881815101340353919183581671532800342110807823681435578850102570426257943742⟩ ⟨false, 191996568364235564707581384819120907615392580623373805978989009416113273116⟩ ⟨false, 2871626820705324259124727529601619772085093178427209153133352714350319724044⟩ ⟨false, 207164314760226162746073028913785117529942493188099768357255458216804893468⟩ = true := by
  decide +kernel

theorem b_294_2400 : bothLoop evalE (oGrid.idx 294) (oGrid.dm 294) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 294) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2871626820705324259124727529601619772085093178427209153133352714350319724044⟩ ⟨false, 207164314760226162746073028913785117529942493188099768357255458216804893468⟩ = true := by
  decide +kernel

theorem o_row_294 : oGrid.row evalE 294 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_294_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_294_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_294_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_294_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_294_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_294_2000).1 (bothLoop_sound b_294_2400).1))))))

theorem n_row_294 : nGrid.row evalE 294 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_294_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_294_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_294_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_294_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_294_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_294_2000).2 (bothLoop_sound b_294_2400).2))))))

theorem b_295_0 : bothSeg evalE (oGrid.idx 295) (oGrid.dm 295) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 295) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1667417653640197222125056822553603540460226849005831144624223646129268595984⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_295_400 : bothSeg evalE (oGrid.idx 295) (oGrid.dm 295) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 295) oGrid.kl oGrid.kr 400 400 ⟨false, 1667417653640197222125056822553603540460226849005831144624223646129268595984⟩ ⟨false, 0⟩ ⟨false, 2686621285244924646534694640728410748561231199416165022175781632659270869950⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_295_800 : bothSeg evalE (oGrid.idx 295) (oGrid.dm 295) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 295) oGrid.kl oGrid.kr 400 800 ⟨false, 2686621285244924646534694640728410748561231199416165022175781632659270869950⟩ ⟨false, 0⟩ ⟨false, 3031923557284684958350813533625278003107891378362121549832435388498605194504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_295_1200 : bothSeg evalE (oGrid.idx 295) (oGrid.dm 295) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 295) oGrid.kl oGrid.kr 400 1200 ⟨false, 3031923557284684958350813533625278003107891378362121549832435388498605194504⟩ ⟨false, 0⟩ ⟨false, 3026974639951353218959193417955105453228850872107550161323475507397945076682⟩ ⟨false, 32645449876612228567121168787170647457940797716267661038515192259383386848⟩ = true := by
  decide +kernel

theorem b_295_1600 : bothSeg evalE (oGrid.idx 295) (oGrid.dm 295) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 295) oGrid.kl oGrid.kr 400 1600 ⟨false, 3026974639951353218959193417955105453228850872107550161323475507397945076682⟩ ⟨false, 32645449876612228567121168787170647457940797716267661038515192259383386848⟩ ⟨false, 2867664041001107148746721942578945706144323985253728078648246409580133111270⟩ ⟨false, 191966338591679577071772039320833282021659306819778940485452172969857463790⟩ = true := by
  decide +kernel

theorem b_295_2000 : bothSeg evalE (oGrid.idx 295) (oGrid.dm 295) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 295) oGrid.kl oGrid.kr 400 2000 ⟨false, 2867664041001107148746721942578945706144323985253728078648246409580133111270⟩ ⟨false, 191966338591679577071772039320833282021659306819778940485452172969857463790⟩ ⟨false, 2857692066770899305250506199365048669208263816125437720968959134486615517732⟩ ⟨false, 206986193795275559933811505496605453786420286083091667467495590831530531274⟩ = true := by
  decide +kernel

theorem b_295_2400 : bothLoop evalE (oGrid.idx 295) (oGrid.dm 295) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 295) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2857692066770899305250506199365048669208263816125437720968959134486615517732⟩ ⟨false, 206986193795275559933811505496605453786420286083091667467495590831530531274⟩ = true := by
  decide +kernel

theorem o_row_295 : oGrid.row evalE 295 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_295_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_295_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_295_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_295_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_295_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_295_2000).1 (bothLoop_sound b_295_2400).1))))))

theorem n_row_295 : nGrid.row evalE 295 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_295_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_295_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_295_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_295_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_295_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_295_2000).2 (bothLoop_sound b_295_2400).2))))))

theorem b_296_0 : bothSeg evalE (oGrid.idx 296) (oGrid.dm 296) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 296) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1660155607029930543719240250597986954701509654963599498831840813667084194868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_296_400 : bothSeg evalE (oGrid.idx 296) (oGrid.dm 296) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 296) oGrid.kl oGrid.kr 400 400 ⟨false, 1660155607029930543719240250597986954701509654963599498831840813667084194868⟩ ⟨false, 0⟩ ⟨false, 2674747476908203510359361267088375524393284513294505397300498472174803961764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_296_800 : bothSeg evalE (oGrid.idx 296) (oGrid.dm 296) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 296) oGrid.kl oGrid.kr 400 800 ⟨false, 2674747476908203510359361267088375524393284513294505397300498472174803961764⟩ ⟨false, 0⟩ ⟨false, 3018137564352406125468781580020489326646223937582407223570263238368462222178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_296_1200 : bothSeg evalE (oGrid.idx 296) (oGrid.dm 296) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 296) oGrid.kl oGrid.kr 400 1200 ⟨false, 3018137564352406125468781580020489326646223937582407223570263238368462222178⟩ ⟨false, 0⟩ ⟨false, 3012905694983123522027458835715989848805728098446521403045762132642990217598⟩ ⟨false, 32585046714745218801318422268793224918082918170328643551958761612384634076⟩ = true := by
  decide +kernel

theorem b_296_1600 : bothSeg evalE (oGrid.idx 296) (oGrid.dm 296) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 296) oGrid.kl oGrid.kr 400 1600 ⟨false, 3012905694983123522027458835715989848805728098446521403045762132642990217598⟩ ⟨false, 32585046714745218801318422268793224918082918170328643551958761612384634076⟩ ⟨false, 2853559460726317830854880669101207391647908970687310933627674746221924425028⟩ ⟨false, 191935444624578502261684141344389178849636033688756971621030629683235491006⟩ = true := by
  decide +kernel

theorem b_296_2000 : bothSeg evalE (oGrid.idx 296) (oGrid.dm 296) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 296) oGrid.kl oGrid.kr 400 2000 ⟨false, 2853559460726317830854880669101207391647908970687310933627674746221924425028⟩ ⟨false, 191935444624578502261684141344389178849636033688756971621030629683235491006⟩ ⟨false, 2843802255399948514533033822612669087546507901986636535649329276539768379044⟩ ⟨false, 206808288425736288168158541079435149790631227961513285154594961036255245912⟩ = true := by
  decide +kernel

theorem b_296_2400 : bothLoop evalE (oGrid.idx 296) (oGrid.dm 296) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 296) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2843802255399948514533033822612669087546507901986636535649329276539768379044⟩ ⟨false, 206808288425736288168158541079435149790631227961513285154594961036255245912⟩ = true := by
  decide +kernel

theorem o_row_296 : oGrid.row evalE 296 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_296_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_296_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_296_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_296_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_296_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_296_2000).1 (bothLoop_sound b_296_2400).1))))))

theorem n_row_296 : nGrid.row evalE 296 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_296_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_296_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_296_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_296_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_296_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_296_2000).2 (bothLoop_sound b_296_2400).2))))))

theorem b_297_0 : bothSeg evalE (oGrid.idx 297) (oGrid.dm 297) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 297) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1652917098290790647604883374320898806452858043451098189153024353250939201720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_297_400 : bothSeg evalE (oGrid.idx 297) (oGrid.dm 297) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 297) oGrid.kl oGrid.kr 400 400 ⟨false, 1652917098290790647604883374320898806452858043451098189153024353250939201720⟩ ⟨false, 0⟩ ⟨false, 2662911272249666971235718792764171340977603869977465124467513580703500702438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_297_800 : bothSeg evalE (oGrid.idx 297) (oGrid.dm 297) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 297) oGrid.kl oGrid.kr 400 800 ⟨false, 2662911272249666971235718792764171340977603869977465124467513580703500702438⟩ ⟨false, 0⟩ ⟨false, 3004394935004998379441692275796065362721881727201834929447671491265246446420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_297_1200 : bothSeg evalE (oGrid.idx 297) (oGrid.dm 297) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 297) oGrid.kl oGrid.kr 400 1200 ⟨false, 3004394935004998379441692275796065362721881727201834929447671491265246446420⟩ ⟨false, 0⟩ ⟨false, 2998879796576257529359877829910181211419360009954230385185398703339776385654⟩ ⟨false, 32524668323688557344797764485652056059829512183827488628675959923920263656⟩ = true := by
  decide +kernel

theorem b_297_1600 : bothSeg evalE (oGrid.idx 297) (oGrid.dm 297) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 297) oGrid.kl oGrid.kr 400 1600 ⟨false, 2998879796576257529359877829910181211419360009954230385185398703339776385654⟩ ⟨false, 32524668323688557344797764485652056059829512183827488628675959923920263656⟩ ⟨false, 2839501234002738970440284963838792522680934945550154005867375143284746600630⟩ ⟨false, 191903897017050212148620678411598092742436646527151785369149856962927377172⟩ = true := by
  decide +kernel

theorem b_297_2000 : bothSeg evalE (oGrid.idx 297) (oGrid.dm 297) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 297) oGrid.kl oGrid.kr 400 2000 ⟨false, 2839501234002738970440284963838792522680934945550154005867375143284746600630⟩ ⟨false, 191903897017050212148620678411598092742436646527151785369149856962927377172⟩ ⟨false, 2829957229481835220457045424838149843735034380246816453147683422395756677646⟩ ⟨false, 206630806216736982530253692545128298451601940078589522498647860221940371048⟩ = true := by
  decide +kernel

theorem b_297_2400 : bothLoop evalE (oGrid.idx 297) (oGrid.dm 297) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 297) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2829957229481835220457045424838149843735034380246816453147683422395756677646⟩ ⟨false, 206630806216736982530253692545128298451601940078589522498647860221940371048⟩ = true := by
  decide +kernel

theorem o_row_297 : oGrid.row evalE 297 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_297_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_297_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_297_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_297_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_297_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_297_2000).1 (bothLoop_sound b_297_2400).1))))))

theorem n_row_297 : nGrid.row evalE 297 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_297_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_297_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_297_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_297_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_297_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_297_2000).2 (bothLoop_sound b_297_2400).2))))))

theorem b_298_0 : bothSeg evalE (oGrid.idx 298) (oGrid.dm 298) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 298) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1645702066786704921984657859215147899294049865902974075558947937140024027556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_298_400 : bothSeg evalE (oGrid.idx 298) (oGrid.dm 298) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 298) oGrid.kl oGrid.kr 400 400 ⟨false, 1645702066786704921984657859215147899294049865902974075558947937140024027556⟩ ⟨false, 0⟩ ⟨false, 2651112591736409810429045128787460954480847370358065315301990690585322842246⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_298_800 : bothSeg evalE (oGrid.idx 298) (oGrid.dm 298) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 298) oGrid.kl oGrid.kr 400 800 ⟨false, 2651112591736409810429045128787460954480847370358065315301990690585322842246⟩ ⟨false, 0⟩ ⟨false, 2990695582050621854377594739961794094541805560580853635077628923045727331838⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_298_1200 : bothSeg evalE (oGrid.idx 298) (oGrid.dm 298) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 298) oGrid.kl oGrid.kr 400 1200 ⟨false, 2990695582050621854377594739961794094541805560580853635077628923045727331838⟩ ⟨false, 0⟩ ⟨false, 2984896493175510564469823266786834602908665297371204930720456438534615085690⟩ ⟨false, 32464506611867925046615341413115617289247331439588229400328173065145429600⟩ = true := by
  decide +kernel

theorem b_298_1600 : bothSeg evalE (oGrid.idx 298) (oGrid.dm 298) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 298) oGrid.kl oGrid.kr 400 1600 ⟨false, 2984896493175510564469823266786834602908665297371204930720456438534615085690⟩ ⟨false, 32464506611867925046615341413115617289247331439588229400328173065145429600⟩ ⟨false, 2825489096416047452796498472103905069769913945260088426744999386771639941138⟩ ⟨false, 191871903371331036719940136096045150427998683550704733375785224828120574152⟩ = true := by
  decide +kernel

theorem b_298_2000 : bothSeg evalE (oGrid.idx 298) (oGrid.dm 298) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 298) oGrid.kl oGrid.kr 400 2000 ⟨false, 2825489096416047452796498472103905069769913945260088426744999386771639941138⟩ ⟨false, 191871903371331036719940136096045150427998683550704733375785224828120574152⟩ ⟨false, 2816156668732182993202085004041848460663813751552978384979016515339352748916⟩ ⟨false, 206453796822497507515678870419149738092933539943329952377012444296977380890⟩ = true := by
  decide +kernel

theorem b_298_2400 : bothLoop evalE (oGrid.idx 298) (oGrid.dm 298) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 298) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2816156668732182993202085004041848460663813751552978384979016515339352748916⟩ ⟨false, 206453796822497507515678870419149738092933539943329952377012444296977380890⟩ = true := by
  decide +kernel

theorem o_row_298 : oGrid.row evalE 298 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_298_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_298_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_298_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_298_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_298_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_298_2000).1 (bothLoop_sound b_298_2400).1))))))

theorem n_row_298 : nGrid.row evalE 298 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_298_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_298_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_298_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_298_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_298_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_298_2000).2 (bothLoop_sound b_298_2400).2))))))

theorem b_299_0 : bothSeg evalE (oGrid.idx 299) (oGrid.dm 299) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 299) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1638510435698460644672118152244858387141004483890870454378861505193904421636⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_299_400 : bothSeg evalE (oGrid.idx 299) (oGrid.dm 299) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 299) oGrid.kl oGrid.kr 400 400 ⟨false, 1638510435698460644672118152244858387141004483890870454378861505193904421636⟩ ⟨false, 0⟩ ⟨false, 2639351337361901144532289179747404379479530076879763416922734596450392394776⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_299_800 : bothSeg evalE (oGrid.idx 299) (oGrid.dm 299) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 299) oGrid.kl oGrid.kr 400 800 ⟨false, 2639351337361901144532289179747404379479530076879763416922734596450392394776⟩ ⟨false, 0⟩ ⟨false, 2977039356314282565770222380064940053139412044568578071337665979647988375536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_299_1200 : bothSeg evalE (oGrid.idx 299) (oGrid.dm 299) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 299) oGrid.kl oGrid.kr 400 1200 ⟨false, 2977039356314282565770222380064940053139412044568578071337665979647988375536⟩ ⟨false, 0⟩ ⟨false, 2970956079048196195299566115479286843967252904587730439207472236992714588440⟩ ⟨false, 32406322042928313910281111361855911938571656518701146744894179622779898860⟩ = true := by
  decide +kernel

theorem b_299_1600 : bothSeg evalE (oGrid.idx 299) (oGrid.dm 299) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 299) oGrid.kl oGrid.kr 400 1600 ⟨false, 2970956079048196195299566115479286843967252904587730439207472236992714588440⟩ ⟨false, 32406322042928313910281111361855911938571656518701146744894179622779898860⟩ ⟨false, 2811523563894066464242484126238204842657665284355932124126389222321687116000⟩ ⟨false, 191838837197058044967363100602937913248159276750499461825977194293807371300⟩ = true := by
  decide +kernel

theorem b_299_2000 : bothSeg evalE (oGrid.idx 299) (oGrid.dm 299) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 299) oGrid.kl oGrid.kr 400 2000 ⟨false, 2811523563894066464242484126238204842657665284355932124126389222321687116000⟩ ⟨false, 191838837197058044967363100602937913248159276750499461825977194293807371300⟩ ⟨false, 2802401074086428780260806910777620222529261577662856338040894824268180816798⟩ ⟨false, 206276547491460003766503968358935595320540093312680816721572791115785651224⟩ = true := by
  decide +kernel

theorem b_299_2400 : bothLoop evalE (oGrid.idx 299) (oGrid.dm 299) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 299) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2802401074086428780260806910777620222529261577662856338040894824268180816798⟩ ⟨false, 206276547491460003766503968358935595320540093312680816721572791115785651224⟩ = true := by
  decide +kernel

theorem o_row_299 : oGrid.row evalE 299 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_299_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_299_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_299_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_299_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_299_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_299_2000).1 (bothLoop_sound b_299_2400).1))))))

theorem n_row_299 : nGrid.row evalE 299 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_299_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_299_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_299_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_299_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_299_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_299_2000).2 (bothLoop_sound b_299_2400).2))))))

theorem b_300_0 : bothSeg evalE (oGrid.idx 300) (oGrid.dm 300) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 300) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1631342153329702591820772717968595366538988457368136237488543991037567541608⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_300_400 : bothSeg evalE (oGrid.idx 300) (oGrid.dm 300) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 300) oGrid.kl oGrid.kr 400 400 ⟨false, 1631342153329702591820772717968595366538988457368136237488543991037567541608⟩ ⟨false, 0⟩ ⟨false, 2627627418791146374081211783902636284178763769003339719015307637758767014292⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_300_800 : bothSeg evalE (oGrid.idx 300) (oGrid.dm 300) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 300) oGrid.kl oGrid.kr 400 800 ⟨false, 2627627418791146374081211783902636284178763769003339719015307637758767014292⟩ ⟨false, 0⟩ ⟨false, 2963426212735826136990264250873559464877237372477713077463749982424063813246⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_300_1200 : bothSeg evalE (oGrid.idx 300) (oGrid.dm 300) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 300) oGrid.kl oGrid.kr 400 1200 ⟨false, 2963426212735826136990264250873559464877237372477713077463749982424063813246⟩ ⟨false, 0⟩ ⟨false, 2957057966749247438668432478171112877679234811242144475315611308608183563420⟩ ⟨false, 32351246461340804503233323423840335096979023258404028911185416693949350038⟩ = true := by
  decide +kernel

theorem b_300_1600 : bothSeg evalE (oGrid.idx 300) (oGrid.dm 300) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 300) oGrid.kl oGrid.kr 400 1600 ⟨false, 2957057966749247438668432478171112877679234811242144475315611308608183563420⟩ ⟨false, 32351246461340804503233323423840335096979023258404028911185416693949350038⟩ ⟨false, 2797604257065183723917300599336306359972510590432762496137634217990200951712⟩ ⟨false, 191804956145404519254365202258646852803703244067786008089162507311931961746⟩ = true := by
  decide +kernel

theorem b_300_2000 : bothSeg evalE (oGrid.idx 300) (oGrid.dm 300) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 300) oGrid.kl oGrid.kr 400 2000 ⟨false, 2797604257065183723917300599336306359972510590432762496137634217990200951712⟩ ⟨false, 191804956145404519254365202258646852803703244067786008089162507311931961746⟩ ⟨false, 2788689998193046169697178962274469011292871419551655699220587986459611127694⟩ ⟨false, 206099067271774094116012381427640274899941756332007544810795177007258208066⟩ = true := by
  decide +kernel

theorem b_300_2400 : bothLoop evalE (oGrid.idx 300) (oGrid.dm 300) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 300) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2788689998193046169697178962274469011292871419551655699220587986459611127694⟩ ⟨false, 206099067271774094116012381427640274899941756332007544810795177007258208066⟩ = true := by
  decide +kernel

theorem o_row_300 : oGrid.row evalE 300 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_300_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_300_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_300_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_300_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_300_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_300_2000).1 (bothLoop_sound b_300_2400).1))))))

theorem n_row_300 : nGrid.row evalE 300 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_300_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_300_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_300_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_300_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_300_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_300_2000).2 (bothLoop_sound b_300_2400).2))))))

theorem b_301_0 : bothSeg evalE (oGrid.idx 301) (oGrid.dm 301) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 301) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1624197155540209516934326869245032333123260152620885014384547285743460892912⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_301_400 : bothSeg evalE (oGrid.idx 301) (oGrid.dm 301) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 301) oGrid.kl oGrid.kr 400 400 ⟨false, 1624197155540209516934326869245032333123260152620885014384547285743460892912⟩ ⟨false, 0⟩ ⟨false, 2615940760921818104373741429273527280601207400158926772951098365823361777666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_301_800 : bothSeg evalE (oGrid.idx 301) (oGrid.dm 301) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 301) oGrid.kl oGrid.kr 400 800 ⟨false, 2615940760921818104373741429273527280601207400158926772951098365823361777666⟩ ⟨false, 0⟩ ⟨false, 2949856061756325482343036337446784992724618559672567354576508135725582036416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_301_1200 : bothSeg evalE (oGrid.idx 301) (oGrid.dm 301) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 301) oGrid.kl oGrid.kr 400 1200 ⟨false, 2949856061756325482343036337446784992724618559672567354576508135725582036416⟩ ⟨false, 0⟩ ⟨false, 2943201776356014975015184971903820036821969887457990910530535705599113672326⟩ ⟨false, 32299637019008228403755439991126812281336300537636571800802484701762623472⟩ = true := by
  decide +kernel

theorem b_301_1600 : bothSeg evalE (oGrid.idx 301) (oGrid.dm 301) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 301) oGrid.kl oGrid.kr 400 1600 ⟨false, 2943201776356014975015184971903820036821969887457990910530535705599113672326⟩ ⟨false, 32299637019008228403755439991126812281336300537636571800802484701762623472⟩ ⟨false, 2783730942378869271294700848811876327960246235670338684761302792449036922348⟩ ⟨false, 191770470996153932124239563083070521143059952325288797570035397851839373450⟩ = true := by
  decide +kernel

theorem b_301_2000 : bothSeg evalE (oGrid.idx 301) (oGrid.dm 301) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 301) oGrid.kl oGrid.kr 400 2000 ⟨false, 2783730942378869271294700848811876327960246235670338684761302792449036922348⟩ ⟨false, 191770470996153932124239563083070521143059952325288797570035397851839373450⟩ ⟨false, 2775023202929222226630154821633264965812081582756511659332061338424151183098⟩ ⟨false, 205922395150431875464002977606912881229306751908949524494882504199434322440⟩ = true := by
  decide +kernel

theorem b_301_2400 : bothLoop evalE (oGrid.idx 301) (oGrid.dm 301) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 301) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2775023202929222226630154821633264965812081582756511659332061338424151183098⟩ ⟨false, 205922395150431875464002977606912881229306751908949524494882504199434322440⟩ = true := by
  decide +kernel

theorem o_row_301 : oGrid.row evalE 301 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_301_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_301_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_301_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_301_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_301_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_301_2000).1 (bothLoop_sound b_301_2400).1))))))

theorem n_row_301 : nGrid.row evalE 301 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_301_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_301_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_301_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_301_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_301_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_301_2000).2 (bothLoop_sound b_301_2400).2))))))

theorem b_302_0 : bothSeg evalE (oGrid.idx 302) (oGrid.dm 302) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 302) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1617075383311142492807989733253980397054645493266020763229255696599891318028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_302_400 : bothSeg evalE (oGrid.idx 302) (oGrid.dm 302) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 302) oGrid.kl oGrid.kr 400 400 ⟨false, 1617075383311142492807989733253980397054645493266020763229255696599891318028⟩ ⟨false, 0⟩ ⟨false, 2604291253070405649896532436719759407842366922182526974420095725626524881562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_302_800 : bothSeg evalE (oGrid.idx 302) (oGrid.dm 302) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 302) oGrid.kl oGrid.kr 400 800 ⟨false, 2604291253070405649896532436719759407842366922182526974420095725626524881562⟩ ⟨false, 0⟩ ⟨false, 2936328754943035607396609516708406249693904382499492430969918064347294111600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_302_1200 : bothSeg evalE (oGrid.idx 302) (oGrid.dm 302) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 302) oGrid.kl oGrid.kr 400 1200 ⟨false, 2936328754943035607396609516708406249693904382499492430969918064347294111600⟩ ⟨false, 0⟩ ⟨false, 2929387106921599061149632005240638043816075395240802466203279188536858792198⟩ ⟨false, 32251990369749911636834694704535438645789853602174005464426063706081578832⟩ = true := by
  decide +kernel

theorem b_302_1600 : bothSeg evalE (oGrid.idx 302) (oGrid.dm 302) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 302) oGrid.kl oGrid.kr 400 1600 ⟨false, 2929387106921599061149632005240638043816075395240802466203279188536858792198⟩ ⟨false, 32251990369749911636834694704535438645789853602174005464426063706081578832⟩ ⟨false, 2769903417686213156133643740342413514282479757616260374130357792139396580266⟩ ⟨false, 191735679605135816652822959602759968179385491226716097537347460103543790764⟩ = true := by
  decide +kernel

theorem b_302_2000 : bothSeg evalE (oGrid.idx 302) (oGrid.dm 302) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 302) oGrid.kl oGrid.kr 400 2000 ⟨false, 2769903417686213156133643740342413514282479757616260374130357792139396580266⟩ ⟨false, 191735679605135816652822959602759968179385491226716097537347460103543790764⟩ ⟨false, 2761400432727210004980975216551748875079857961103622132955163280371158571424⟩ ⟨false, 205746165332053145934789344697993452520310626121333482983461776724646063964⟩ = true := by
  decide +kernel

theorem b_302_2400 : bothLoop evalE (oGrid.idx 302) (oGrid.dm 302) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 302) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2761400432727210004980975216551748875079857961103622132955163280371158571424⟩ ⟨false, 205746165332053145934789344697993452520310626121333482983461776724646063964⟩ = true := by
  decide +kernel

theorem o_row_302 : oGrid.row evalE 302 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_302_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_302_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_302_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_302_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_302_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_302_2000).1 (bothLoop_sound b_302_2400).1))))))

theorem n_row_302 : nGrid.row evalE 302 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_302_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_302_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_302_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_302_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_302_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_302_2000).2 (bothLoop_sound b_302_2400).2))))))

theorem b_303_0 : bothSeg evalE (oGrid.idx 303) (oGrid.dm 303) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 303) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1609976782405924069472613651357023223565475552088786163116516591882894789412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_303_400 : bothSeg evalE (oGrid.idx 303) (oGrid.dm 303) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 303) oGrid.kl oGrid.kr 400 400 ⟨false, 1609976782405924069472613651357023223565475552088786163116516591882894789412⟩ ⟨false, 0⟩ ⟨false, 2592678828449564956673409849212542197540283220837565273173424810518760874414⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_303_800 : bothSeg evalE (oGrid.idx 303) (oGrid.dm 303) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 303) oGrid.kl oGrid.kr 400 800 ⟨false, 2592678828449564956673409849212542197540283220837565273173424810518760874414⟩ ⟨false, 0⟩ ⟨false, 2922844234898840103123842553929257092079966108442286108395494556961676301514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_303_1200 : bothSeg evalE (oGrid.idx 303) (oGrid.dm 303) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 303) oGrid.kl oGrid.kr 400 1200 ⟨false, 2922844234898840103123842553929257092079966108442286108395494556961676301514⟩ ⟨false, 0⟩ ⟨false, 2915613802825567647670378119245688035064775519374899981591621744505088425354⟩ ⟨false, 32208124802710898786475302193983084888908166229199564313675427695640264798⟩ = true := by
  decide +kernel

theorem b_303_1600 : bothSeg evalE (oGrid.idx 303) (oGrid.dm 303) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 303) oGrid.kl oGrid.kr 400 1600 ⟨false, 2915613802825567647670378119245688035064775519374899981591621744505088425354⟩ ⟨false, 32208124802710898786475302193983084888908166229199564313675427695640264798⟩ ⟨false, 2756121784935123671281136714241131163018935474454015593621584380806673709530⟩ ⟨false, 191700142693154875175716707198539956934748211150083952283712791394054980622⟩ = true := by
  decide +kernel

theorem b_303_2000 : bothSeg evalE (oGrid.idx 303) (oGrid.dm 303) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 303) oGrid.kl oGrid.kr 400 2000 ⟨false, 2756121784935123671281136714241131163018935474454015593621584380806673709530⟩ ⟨false, 191700142693154875175716707198539956934748211150083952283712791394054980622⟩ ⟨false, 2747821756562735393272644183994679111360247427312019868456899359832132899024⟩ ⟨false, 205569843825745512699865686909057709493956284022824876882227606716398295540⟩ = true := by
  decide +kernel

theorem b_303_2400 : bothLoop evalE (oGrid.idx 303) (oGrid.dm 303) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 303) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2747821756562735393272644183994679111360247427312019868456899359832132899024⟩ ⟨false, 205569843825745512699865686909057709493956284022824876882227606716398295540⟩ = true := by
  decide +kernel

theorem o_row_303 : oGrid.row evalE 303 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_303_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_303_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_303_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_303_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_303_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_303_2000).1 (bothLoop_sound b_303_2400).1))))))

theorem n_row_303 : nGrid.row evalE 303 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_303_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_303_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_303_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_303_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_303_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_303_2000).2 (bothLoop_sound b_303_2400).2))))))

theorem b_304_0 : bothSeg evalE (oGrid.idx 304) (oGrid.dm 304) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 304) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1602901286035526301918955364595009029017641440129903012750047545841855219830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_304_400 : bothSeg evalE (oGrid.idx 304) (oGrid.dm 304) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 304) oGrid.kl oGrid.kr 400 400 ⟨false, 1602901286035526301918955364595009029017641440129903012750047545841855219830⟩ ⟨false, 0⟩ ⟨false, 2581103392046591736252991981196265744862056567452912768996507675015995475052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_304_800 : bothSeg evalE (oGrid.idx 304) (oGrid.dm 304) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 304) oGrid.kl oGrid.kr 400 800 ⟨false, 2581103392046591736252991981196265744862056567452912768996507675015995475052⟩ ⟨false, 0⟩ ⟨false, 2909402424833601746830293486422706921267800401255227813140658826020831212562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_304_1200 : bothSeg evalE (oGrid.idx 304) (oGrid.dm 304) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 304) oGrid.kl oGrid.kr 400 1200 ⟨false, 2909402424833601746830293486422706921267800401255227813140658826020831212562⟩ ⟨false, 0⟩ ⟨false, 2901881507859646401773356787562736573991561343061517862012664784928375015358⟩ ⟨false, 32168278346697282925637970877373534217306626709955582486557657990194059686⟩ = true := by
  decide +kernel

theorem b_304_1600 : bothSeg evalE (oGrid.idx 304) (oGrid.dm 304) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 304) oGrid.kl oGrid.kr 400 1600 ⟨false, 2901881507859646401773356787562736573991561343061517862012664784928375015358⟩ ⟨false, 32168278346697282925637970877373534217306626709955582486557657990194059686⟩ ⟨false, 2742385833740864211342548791373864247967559102079297094794766170823013412632⟩ ⟨false, 191663952465479473356445967066245860241308867692176349704456272095555662412⟩ = true := by
  decide +kernel

theorem b_304_2000 : bothSeg evalE (oGrid.idx 304) (oGrid.dm 304) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 304) oGrid.kl oGrid.kr 400 2000 ⟨false, 2742385833740864211342548791373864247967559102079297094794766170823013412632⟩ ⟨false, 191663952465479473356445967066245860241308867692176349704456272095555662412⟩ ⟨false, 2734286895189410668610305225216406565824771244994985218518385681699244710744⟩ ⟨false, 205393812359138904112222505984159044721393553550795451905811275523738256984⟩ = true := by
  decide +kernel

theorem b_304_2400 : bothLoop evalE (oGrid.idx 304) (oGrid.dm 304) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 304) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2734286895189410668610305225216406565824771244994985218518385681699244710744⟩ ⟨false, 205393812359138904112222505984159044721393553550795451905811275523738256984⟩ = true := by
  decide +kernel

theorem o_row_304 : oGrid.row evalE 304 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_304_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_304_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_304_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_304_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_304_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_304_2000).1 (bothLoop_sound b_304_2400).1))))))

theorem n_row_304 : nGrid.row evalE 304 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_304_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_304_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_304_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_304_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_304_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_304_2000).2 (bothLoop_sound b_304_2400).2))))))

theorem b_305_0 : bothSeg evalE (oGrid.idx 305) (oGrid.dm 305) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 305) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1595848836299620386803620918368577386992341676731362136703820762690309689814⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_305_400 : bothSeg evalE (oGrid.idx 305) (oGrid.dm 305) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 305) oGrid.kl oGrid.kr 400 400 ⟨false, 1595848836299620386803620918368577386992341676731362136703820762690309689814⟩ ⟨false, 0⟩ ⟨false, 2569564847924410508331067550606528394506733009768543143165782073462205364184⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_305_800 : bothSeg evalE (oGrid.idx 305) (oGrid.dm 305) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 305) oGrid.kl oGrid.kr 400 800 ⟨false, 2569564847924410508331067550606528394506733009768543143165782073462205364184⟩ ⟨false, 0⟩ ⟨false, 2896003173957028951615579703605088812318354624031905850287517054951992660658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_305_1200 : bothSeg evalE (oGrid.idx 305) (oGrid.dm 305) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 305) oGrid.kl oGrid.kr 400 1200 ⟨false, 2896003173957028951615579703605088812318354624031905850287517054951992660658⟩ ⟨false, 0⟩ ⟨false, 2888190017265419917816897673755310290997908053134575817305545112612169527944⟩ ⟨false, 32132592094299825909776566160234864700529843019394033915721052154194273972⟩ = true := by
  decide +kernel

theorem b_305_1600 : bothSeg evalE (oGrid.idx 305) (oGrid.dm 305) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 305) oGrid.kl oGrid.kr 400 1600 ⟨false, 2888190017265419917816897673755310290997908053134575817305545112612169527944⟩ ⟨false, 32132592094299825909776566160234864700529843019394033915721052154194273972⟩ ⟨false, 2728695469713292988823151087072001398977318515789576746355867765683042306112⟩ ⟨false, 191627139646426754903523152843543756721119380364393104865398399083321495804⟩ = true := by
  decide +kernel

theorem b_305_2000 : bothSeg evalE (oGrid.idx 305) (oGrid.dm 305) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 305) oGrid.kl oGrid.kr 400 2000 ⟨false, 2728695469713292988823151087072001398977318515789576746355867765683042306112⟩ ⟨false, 191627139646426754903523152843543756721119380364393104865398399083321495804⟩ ⟨false, 2720795748809539752644161187114425663769025512112950778816330901757258271828⟩ ⟨false, 205218306634572228754811458808632807536240052980422014191565528118948581484⟩ = true := by
  decide +kernel

theorem b_305_2400 : bothLoop evalE (oGrid.idx 305) (oGrid.dm 305) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 305) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2720795748809539752644161187114425663769025512112950778816330901757258271828⟩ ⟨false, 205218306634572228754811458808632807536240052980422014191565528118948581484⟩ = true := by
  decide +kernel

theorem o_row_305 : oGrid.row evalE 305 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_305_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_305_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_305_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_305_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_305_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_305_2000).1 (bothLoop_sound b_305_2400).1))))))

theorem n_row_305 : nGrid.row evalE 305 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_305_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_305_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_305_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_305_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_305_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_305_2000).2 (bothLoop_sound b_305_2400).2))))))

theorem b_306_0 : bothSeg evalE (oGrid.idx 306) (oGrid.dm 306) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 306) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1588819366207088168171836063409313320750717761249747858524048804450936792356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_306_400 : bothSeg evalE (oGrid.idx 306) (oGrid.dm 306) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 306) oGrid.kl oGrid.kr 400 400 ⟨false, 1588819366207088168171836063409313320750717761249747858524048804450936792356⟩ ⟨false, 0⟩ ⟨false, 2558063111689381200050713894401896848430199271728960115608903159801158767692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_306_800 : bothSeg evalE (oGrid.idx 306) (oGrid.dm 306) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 306) oGrid.kl oGrid.kr 400 800 ⟨false, 2558063111689381200050713894401896848430199271728960115608903159801158767692⟩ ⟨false, 0⟩ ⟨false, 2882646417972640045793341931594531352039113598136984773501551003169258323560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_306_1200 : bothSeg evalE (oGrid.idx 306) (oGrid.dm 306) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 306) oGrid.kl oGrid.kr 400 1200 ⟨false, 2882646417972640045793341931594531352039113598136984773501551003169258323560⟩ ⟨false, 0⟩ ⟨false, 2874538884078179530905223033428362695003703711342885614846506689700798119612⟩ ⟨false, 32101515725316479705563382721079686297172910008822857495036399970816240978⟩ = true := by
  decide +kernel

theorem b_306_1600 : bothSeg evalE (oGrid.idx 306) (oGrid.dm 306) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 306) oGrid.kl oGrid.kr 400 1600 ⟨false, 2874538884078179530905223033428362695003703711342885614846506689700798119612⟩ ⟨false, 32101515725316479705563382721079686297172910008822857495036399970816240978⟩ ⟨false, 2715050524287563226864097733873543707514451892551974082919314584977415869472⟩ ⟨false, 191589875515932783746688682275898673786424728799734389422228504694198491118⟩ = true := by
  decide +kernel

theorem b_306_2000 : bothSeg evalE (oGrid.idx 306) (oGrid.dm 306) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 306) oGrid.kl oGrid.kr 400 2000 ⟨false, 2715050524287563226864097733873543707514451892551974082919314584977415869472⟩ ⟨false, 191589875515932783746688682275898673786424728799734389422228504694198491118⟩ ⟨false, 2707348114604866348517938822012828016906820886091720610692292218829960536928⟩ ⟨false, 205043011270068907305766880034778568778309165505342652131211154574308758806⟩ = true := by
  decide +kernel

theorem b_306_2400 : bothLoop evalE (oGrid.idx 306) (oGrid.dm 306) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 306) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2707348114604866348517938822012828016906820886091720610692292218829960536928⟩ ⟨false, 205043011270068907305766880034778568778309165505342652131211154574308758806⟩ = true := by
  decide +kernel

theorem o_row_306 : oGrid.row evalE 306 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_306_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_306_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_306_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_306_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_306_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_306_2000).1 (bothLoop_sound b_306_2400).1))))))

theorem n_row_306 : nGrid.row evalE 306 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_306_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_306_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_306_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_306_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_306_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_306_2000).2 (bothLoop_sound b_306_2400).2))))))

theorem b_307_0 : bothSeg evalE (oGrid.idx 307) (oGrid.dm 307) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 307) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1581812831122083385060572038475414536692418596940937321650748839167892264574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_307_400 : bothSeg evalE (oGrid.idx 307) (oGrid.dm 307) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 307) oGrid.kl oGrid.kr 400 400 ⟨false, 1581812831122083385060572038475414536692418596940937321650748839167892264574⟩ ⟨false, 0⟩ ⟨false, 2546598112557811127012670021710342860714179133454207139663146856212051517000⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_307_800 : bothSeg evalE (oGrid.idx 307) (oGrid.dm 307) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 307) oGrid.kl oGrid.kr 400 800 ⟨false, 2546598112557811127012670021710342860714179133454207139663146856212051517000⟩ ⟨false, 0⟩ ⟨false, 2869332111742089208482899450912312462714022710512210040919822780115235056576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_307_1200 : bothSeg evalE (oGrid.idx 307) (oGrid.dm 307) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 307) oGrid.kl oGrid.kr 400 1200 ⟨false, 2869332111742089208482899450912312462714022710512210040919822780115235056576⟩ ⟨false, 0⟩ ⟨false, 2860928252431830240109680869770400613129436455692976214094590905873848512046⟩ ⟨false, 32074746621430844782554816209589540932415563027489588088615888645035694346⟩ = true := by
  decide +kernel

theorem b_307_1600 : bothSeg evalE (oGrid.idx 307) (oGrid.dm 307) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 307) oGrid.kl oGrid.kr 400 1600 ⟨false, 2860928252431830240109680869770400613129436455692976214094590905873848512046⟩ ⟨false, 32074746621430844782554816209589540932415563027489588088615888645035694346⟩ ⟨false, 2701451263712260371260538926964365349101244026115666903220542369708069949206⟩ ⟨false, 191551735341000713631696759015624804960607992604798898962664424810814257186⟩ = true := by
  decide +kernel

theorem b_307_2000 : bothSeg evalE (oGrid.idx 307) (oGrid.dm 307) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 307) oGrid.kl oGrid.kr 400 2000 ⟨false, 2701451263712260371260538926964365349101244026115666903220542369708069949206⟩ ⟨false, 191551735341000713631696759015624804960607992604798898962664424810814257186⟩ ⟨false, 2693944233879277943052836877097758126530082449700370389101416059919695049774⟩ ⟨false, 204867855971523350923691867090322551001184149981639430062642134748715808452⟩ = true := by
  decide +kernel

theorem b_307_2400 : bothLoop evalE (oGrid.idx 307) (oGrid.dm 307) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 307) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2693944233879277943052836877097758126530082449700370389101416059919695049774⟩ ⟨false, 204867855971523350923691867090322551001184149981639430062642134748715808452⟩ = true := by
  decide +kernel

theorem o_row_307 : oGrid.row evalE 307 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_307_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_307_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_307_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_307_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_307_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_307_2000).1 (bothLoop_sound b_307_2400).1))))))

theorem n_row_307 : nGrid.row evalE 307 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_307_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_307_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_307_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_307_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_307_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_307_2000).2 (bothLoop_sound b_307_2400).2))))))

theorem b_308_0 : bothSeg evalE (oGrid.idx 308) (oGrid.dm 308) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 308) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1574829156468650661533278010233689768157720685925797312797275742593271186844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_308_400 : bothSeg evalE (oGrid.idx 308) (oGrid.dm 308) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 308) oGrid.kl oGrid.kr 400 400 ⟨false, 1574829156468650661533278010233689768157720685925797312797275742593271186844⟩ ⟨false, 0⟩ ⟨false, 2535169744174417540367055688804991874630100726872434676691533616115104398252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_308_800 : bothSeg evalE (oGrid.idx 308) (oGrid.dm 308) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 308) oGrid.kl oGrid.kr 400 800 ⟨false, 2535169744174417540367055688804991874630100726872434676691533616115104398252⟩ ⟨false, 0⟩ ⟨false, 2856060078300251302093041787187860281986802520743247578729622405925874315308⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_308_1200 : bothSeg evalE (oGrid.idx 308) (oGrid.dm 308) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 308) oGrid.kl oGrid.kr 400 1200 ⟨false, 2856060078300251302093041787187860281986802520743247578729622405925874315308⟩ ⟨false, 0⟩ ⟨false, 2847357538149132248068471205929021632598250043055140002187871517488281233758⟩ ⟨false, 32052670401605801523237861889392128526925459678876616179474080696730445258⟩ = true := by
  decide +kernel

theorem b_308_1600 : bothSeg evalE (oGrid.idx 308) (oGrid.dm 308) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 308) oGrid.kl oGrid.kr 400 1600 ⟨false, 2847357538149132248068471205929021632598250043055140002187871517488281233758⟩ ⟨false, 32052670401605801523237861889392128526925459678876616179474080696730445258⟩ ⟨false, 2687897269192406268494895205779716356634629738991437431149367500332737833542⟩ ⟨false, 191512939358331781096813862038697404490545763742579187217978097852273845474⟩ = true := by
  decide +kernel

theorem b_308_2000 : bothSeg evalE (oGrid.idx 308) (oGrid.dm 308) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 308) oGrid.kl oGrid.kr 400 2000 ⟨false, 2687897269192406268494895205779716356634629738991437431149367500332737833542⟩ ⟨false, 191512939358331781096813862038697404490545763742579187217978097852273845474⟩ ⟨false, 2680583630402613203660066981250710937266107293678221763515957989174111748410⟩ ⟨false, 204692591602491416479552069005289690174765352844858912040083687162719575392⟩ = true := by
  decide +kernel

theorem b_308_2400 : bothLoop evalE (oGrid.idx 308) (oGrid.dm 308) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 308) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2680583630402613203660066981250710937266107293678221763515957989174111748410⟩ ⟨false, 204692591602491416479552069005289690174765352844858912040083687162719575392⟩ = true := by
  decide +kernel

theorem o_row_308 : oGrid.row evalE 308 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_308_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_308_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_308_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_308_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_308_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_308_2000).1 (bothLoop_sound b_308_2400).1))))))

theorem n_row_308 : nGrid.row evalE 308 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_308_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_308_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_308_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_308_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_308_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_308_2000).2 (bothLoop_sound b_308_2400).2))))))

theorem b_309_0 : bothSeg evalE (oGrid.idx 309) (oGrid.dm 309) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 309) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1567868286077524015251855976875908605355336380445701997727924119451014237882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_309_400 : bothSeg evalE (oGrid.idx 309) (oGrid.dm 309) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 309) oGrid.kl oGrid.kr 400 400 ⟨false, 1567868286077524015251855976875908605355336380445701997727924119451014237882⟩ ⟨false, 0⟩ ⟨false, 2523777920690026657011869892866170122699114925815774092706403158033189002552⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_309_800 : bothSeg evalE (oGrid.idx 309) (oGrid.dm 309) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 309) oGrid.kl oGrid.kr 400 800 ⟨false, 2523777920690026657011869892866170122699114925815774092706403158033189002552⟩ ⟨false, 0⟩ ⟨false, 2842830249899840746977303267130322228767758149010430836858984853215665124462⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_309_1200 : bothSeg evalE (oGrid.idx 309) (oGrid.dm 309) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 309) oGrid.kl oGrid.kr 400 1200 ⟨false, 2842830249899840746977303267130322228767758149010430836858984853215665124462⟩ ⟨false, 0⟩ ⟨false, 2833826455057674910028543868379696863223747914041222574031006943652281077212⟩ ⟨false, 32035776229647647883519971989683158161011986883649337838360468228131533712⟩ = true := by
  decide +kernel

theorem b_309_1600 : bothSeg evalE (oGrid.idx 309) (oGrid.dm 309) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 309) oGrid.kl oGrid.kr 400 1600 ⟨false, 2833826455057674910028543868379696863223747914041222574031006943652281077212⟩ ⟨false, 32035776229647647883519971989683158161011986883649337838360468228131533712⟩ ⟨false, 2674388464120524015221264821030004862658189509595043298955956213764006334880⟩ ⟨false, 191473767166798542690799019339375158726570391329828612913411198116406276044⟩ = true := by
  decide +kernel

theorem b_309_2000 : bothSeg evalE (oGrid.idx 309) (oGrid.dm 309) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 309) oGrid.kl oGrid.kr 400 2000 ⟨false, 2674388464120524015221264821030004862658189509595043298955956213764006334880⟩ ⟨false, 191473767166798542690799019339375158726570391329828612913411198116406276044⟩ ⟨false, 2667266182790484893222612022813163657458775477400204314683647186337127293822⟩ ⟨false, 204518152576491194168533600796174896983201598417688854746909986610755943848⟩ = true := by
  decide +kernel

theorem b_309_2400 : bothLoop evalE (oGrid.idx 309) (oGrid.dm 309) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 309) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2667266182790484893222612022813163657458775477400204314683647186337127293822⟩ ⟨false, 204518152576491194168533600796174896983201598417688854746909986610755943848⟩ = true := by
  decide +kernel

theorem o_row_309 : oGrid.row evalE 309 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_309_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_309_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_309_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_309_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_309_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_309_2000).1 (bothLoop_sound b_309_2400).1))))))

theorem n_row_309 : nGrid.row evalE 309 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_309_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_309_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_309_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_309_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_309_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_309_2000).2 (bothLoop_sound b_309_2400).2))))))

theorem b_310_0 : bothSeg evalE (oGrid.idx 310) (oGrid.dm 310) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 310) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1560930165271783578759352991952543883984164615670084741701628728951964119876⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_310_400 : bothSeg evalE (oGrid.idx 310) (oGrid.dm 310) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 310) oGrid.kl oGrid.kr 400 400 ⟨false, 1560930165271783578759352991952543883984164615670084741701628728951964119876⟩ ⟨false, 0⟩ ⟨false, 2512422560220709697772122791440065996759061621252344459550285890864952710962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_310_800 : bothSeg evalE (oGrid.idx 310) (oGrid.dm 310) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 310) oGrid.kl oGrid.kr 400 800 ⟨false, 2512422560220709697772122791440065996759061621252344459550285890864952710962⟩ ⟨false, 0⟩ ⟨false, 2829642565689834649701606627991853461234594981521489167178662917384498099960⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_310_1200 : bothSeg evalE (oGrid.idx 310) (oGrid.dm 310) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 310) oGrid.kl oGrid.kr 400 1200 ⟨false, 2829642565689834649701606627991853461234594981521489167178662917384498099960⟩ ⟨false, 0⟩ ⟨false, 2820334720088593269636844249081177610758625173366226242396871347030368516146⟩ ⟨false, 32024010680896840151074191267889498986900330637410509264918785517014068330⟩ = true := by
  decide +kernel

theorem b_310_1600 : bothSeg evalE (oGrid.idx 310) (oGrid.dm 310) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 310) oGrid.kl oGrid.kr 400 1600 ⟨false, 2820334720088593269636844249081177610758625173366226242396871347030368516146⟩ ⟨false, 32024010680896840151074191267889498986900330637410509264918785517014068330⟩ ⟨false, 2660924763313635702002097626444879785222544976543254433532106123582180881700⟩ ⟨false, 191433967455854407785820813904187324522980527460382318129684008965201702776⟩ = true := by
  decide +kernel

theorem b_310_2000 : bothSeg evalE (oGrid.idx 310) (oGrid.dm 310) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 310) oGrid.kl oGrid.kr 400 2000 ⟨false, 2660924763313635702002097626444879785222544976543254433532106123582180881700⟩ ⟨false, 191433967455854407785820813904187324522980527460382318129684008965201702776⟩ ⟨false, 2653991795506793743175477000342190903675708925203804330493754024425432409232⟩ ⟨false, 204344036433529831751186232459229860722435457233779690922556895886129887216⟩ = true := by
  decide +kernel

theorem b_310_2400 : bothLoop evalE (oGrid.idx 310) (oGrid.dm 310) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 310) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2653991795506793743175477000342190903675708925203804330493754024425432409232⟩ ⟨false, 204344036433529831751186232459229860722435457233779690922556895886129887216⟩ = true := by
  decide +kernel

theorem o_row_310 : oGrid.row evalE 310 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_310_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_310_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_310_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_310_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_310_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_310_2000).1 (bothLoop_sound b_310_2400).1))))))

theorem n_row_310 : nGrid.row evalE 310 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_310_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_310_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_310_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_310_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_310_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_310_2000).2 (bothLoop_sound b_310_2400).2))))))

theorem b_311_0 : bothSeg evalE (oGrid.idx 311) (oGrid.dm 311) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 311) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1554014726299092325002461945537474195325506730403482704630364565273425422396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_311_400 : bothSeg evalE (oGrid.idx 311) (oGrid.dm 311) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 311) oGrid.kl oGrid.kr 400 400 ⟨false, 1554014726299092325002461945537474195325506730403482704630364565273425422396⟩ ⟨false, 0⟩ ⟨false, 2501103570585736046872236733543980256715302663530209632412637783361198055976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_311_800 : bothSeg evalE (oGrid.idx 311) (oGrid.dm 311) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 311) oGrid.kl oGrid.kr 400 800 ⟨false, 2501103570585736046872236733543980256715302663530209632412637783361198055976⟩ ⟨false, 0⟩ ⟨false, 2816496902378727896781730294770951567602214216118757427390316692623282840842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_311_1200 : bothSeg evalE (oGrid.idx 311) (oGrid.dm 311) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 311) oGrid.kl oGrid.kr 400 1200 ⟨false, 2816496902378727896781730294770951567602214216118757427390316692623282840842⟩ ⟨false, 0⟩ ⟨false, 2806882232423128861993391958543809599382011873115166365111442429268215180272⟩ ⟨false, 32017401766900558105373481127723170833033530800469088554354400402240859900⟩ = true := by
  decide +kernel

theorem b_311_1600 : bothSeg evalE (oGrid.idx 311) (oGrid.dm 311) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 311) oGrid.kl oGrid.kr 400 1600 ⟨false, 2806882232423128861993391958543809599382011873115166365111442429268215180272⟩ ⟨false, 32017401766900558105373481127723170833033530800469088554354400402240859900⟩ ⟨false, 2647506175886710246214026702321319615373112094192565286953980580176750434132⟩ ⟨false, 191393458303319173884738737350213154841933309723070166711816249493705606040⟩ = true := by
  decide +kernel

theorem b_311_2000 : bothSeg evalE (oGrid.idx 311) (oGrid.dm 311) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 311) oGrid.kl oGrid.kr 400 2000 ⟨false, 2647506175886710246214026702321319615373112094192565286953980580176750434132⟩ ⟨false, 191393458303319173884738737350213154841933309723070166711816249493705606040⟩ ⟨false, 2640760448600228245684992221177563339252697728270579839589078110850167912806⟩ ⟨false, 204169837502594830521486276478149742620107421859428356945708105178774308218⟩ = true := by
  decide +kernel

theorem b_311_2400 : bothLoop evalE (oGrid.idx 311) (oGrid.dm 311) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 311) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2640760448600228245684992221177563339252697728270579839589078110850167912806⟩ ⟨false, 204169837502594830521486276478149742620107421859428356945708105178774308218⟩ = true := by
  decide +kernel

theorem o_row_311 : oGrid.row evalE 311 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_311_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_311_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_311_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_311_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_311_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_311_2000).1 (bothLoop_sound b_311_2400).1))))))

theorem n_row_311 : nGrid.row evalE 311 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_311_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_311_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_311_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_311_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_311_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_311_2000).2 (bothLoop_sound b_311_2400).2))))))

theorem o_blk_288 : allFrom (fun j => oGrid.row evalE j) 288 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 288) o_row_288 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 289) o_row_289 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 290) o_row_290 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 291) o_row_291 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 292) o_row_292 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 293) o_row_293 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 294) o_row_294 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 295) o_row_295 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 296) o_row_296 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 297) o_row_297 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 298) o_row_298 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 299) o_row_299 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 300) o_row_300 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 301) o_row_301 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 302) o_row_302 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 303) o_row_303 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 304) o_row_304 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 305) o_row_305 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 306) o_row_306 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 307) o_row_307 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 308) o_row_308 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 309) o_row_309 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 310) o_row_310 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 311) o_row_311 (allFrom_zero (fun j => oGrid.row evalE j) 312)))))))))))))))))))))))))

theorem n_blk_288 : allFrom (fun j => nGrid.row evalE j) 288 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 288) n_row_288 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 289) n_row_289 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 290) n_row_290 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 291) n_row_291 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 292) n_row_292 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 293) n_row_293 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 294) n_row_294 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 295) n_row_295 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 296) n_row_296 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 297) n_row_297 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 298) n_row_298 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 299) n_row_299 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 300) n_row_300 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 301) n_row_301 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 302) n_row_302 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 303) n_row_303 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 304) n_row_304 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 305) n_row_305 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 306) n_row_306 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 307) n_row_307 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 308) n_row_308 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 309) n_row_309 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 310) n_row_310 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 311) n_row_311 (allFrom_zero (fun j => nGrid.row evalE j) 312)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
