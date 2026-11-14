/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 13 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `312`–`335`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_312_0 : bothSeg evalE (oGrid.idx 312) (oGrid.dm 312) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 312) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1547121925905304106173118805635875618409821359934239124752014829494304233488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_312_400 : bothSeg evalE (oGrid.idx 312) (oGrid.dm 312) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 312) oGrid.kl oGrid.kr 400 400 ⟨false, 1547121925905304106173118805635875618409821359934239124752014829494304233488⟩ ⟨false, 0⟩ ⟨false, 2489820878128897208726625414895559385779379024015911041095250711669818558940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_312_800 : bothSeg evalE (oGrid.idx 312) (oGrid.dm 312) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 312) oGrid.kl oGrid.kr 400 800 ⟨false, 2489820878128897208726625414895559385779379024015911041095250711669818558940⟩ ⟨false, 0⟩ ⟨false, 2803393173292710364505665536850148772256803791748386218243885004969005885692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_312_1200 : bothSeg evalE (oGrid.idx 312) (oGrid.dm 312) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 312) oGrid.kl oGrid.kr 400 1200 ⟨false, 2803393173292710364505665536850148772256803791748386218243885004969005885692⟩ ⟨false, 0⟩ ⟨false, 2793468608945812448927074826688051235158997051637515038045424660884597286604⟩ ⟨false, 32016106243807248988058614585359438766669767316557404373756861820403944882⟩ = true := by
  decide +kernel

theorem b_312_1600 : bothSeg evalE (oGrid.idx 312) (oGrid.dm 312) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 312) oGrid.kl oGrid.kr 400 1600 ⟨false, 2793468608945812448927074826688051235158997051637515038045424660884597286604⟩ ⟨false, 32016106243807248988058614585359438766669767316557404373756861820403944882⟩ ⟨false, 2634132429096694524070728233652670897483633431260683400926237017341922115190⟩ ⟨false, 191352286092925173844405207620739776442033387693389041492944505363079116296⟩ = true := by
  decide +kernel

theorem b_312_2000 : bothSeg evalE (oGrid.idx 312) (oGrid.dm 312) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 312) oGrid.kl oGrid.kr 400 2000 ⟨false, 2634132429096694524070728233652670897483633431260683400926237017341922115190⟩ ⟨false, 191352286092925173844405207620739776442033387693389041492944505363079116296⟩ ⟨false, 2627571814879523420783426043541141414172075684562072004591641732672363113118⟩ ⟨false, 203995686304627879777428554028823913530625708086560659515441829554343545274⟩ = true := by
  decide +kernel

theorem b_312_2400 : bothLoop evalE (oGrid.idx 312) (oGrid.dm 312) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 312) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2627571814879523420783426043541141414172075684562072004591641732672363113118⟩ ⟨false, 203995686304627879777428554028823913530625708086560659515441829554343545274⟩ = true := by
  decide +kernel

theorem o_row_312 : oGrid.row evalE 312 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_312_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_312_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_312_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_312_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_312_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_312_2000).1 (bothLoop_sound b_312_2400).1))))))

theorem n_row_312 : nGrid.row evalE 312 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_312_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_312_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_312_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_312_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_312_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_312_2000).2 (bothLoop_sound b_312_2400).2))))))

theorem b_313_0 : bothSeg evalE (oGrid.idx 313) (oGrid.dm 313) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 313) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1540251698260111508796642472909806263554195734637012843681284096393302373216⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_313_400 : bothSeg evalE (oGrid.idx 313) (oGrid.dm 313) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 313) oGrid.kl oGrid.kr 400 400 ⟨false, 1540251698260111508796642472909806263554195734637012843681284096393302373216⟩ ⟨false, 0⟩ ⟨false, 2478574399539808522794560568852270141852825453700194728031220387562893742290⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_313_800 : bothSeg evalE (oGrid.idx 313) (oGrid.dm 313) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 313) oGrid.kl oGrid.kr 400 800 ⟨false, 2478574399539808522794560568852270141852825453700194728031220387562893742290⟩ ⟨false, 0⟩ ⟨false, 2790331307956822888136322620168579686647153793831992735049265423885770319954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_313_1200 : bothSeg evalE (oGrid.idx 313) (oGrid.dm 313) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 313) oGrid.kl oGrid.kr 400 1200 ⟨false, 2790331307956822888136322620168579686647153793831992735049265423885770319954⟩ ⟨false, 0⟩ ⟨false, 2780093716669350530445881159551209611269024701073905580302082864170334671086⟩ ⟨false, 32020215628607793044734577656847706910225645193904105423786193452772109306⟩ = true := by
  decide +kernel

theorem b_313_1600 : bothSeg evalE (oGrid.idx 313) (oGrid.dm 313) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 313) oGrid.kl oGrid.kr 400 1600 ⟨false, 2780093716669350530445881159551209611269024701073905580302082864170334671086⟩ ⟨false, 32020215628607793044734577656847706910225645193904105423786193452772109306⟩ ⟨false, 2620803673845568912672898828288825404788318974543799369173397991183008358174⟩ ⟨false, 191310258452389410817716908919231913390931371724010316552471066440098422218⟩ = true := by
  decide +kernel

theorem b_313_2000 : bothSeg evalE (oGrid.idx 313) (oGrid.dm 313) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 313) oGrid.kl oGrid.kr 400 2000 ⟨false, 2620803673845568912672898828288825404788318974543799369173397991183008358174⟩ ⟨false, 191310258452389410817716908919231913390931371724010316552471066440098422218⟩ ⟨false, 2614426053269545002849994363604371045026408953493129781882689051422009888110⟩ ⟨false, 203821935960390677324386324333324064233036526330437756208993443313983944286⟩ = true := by
  decide +kernel

theorem b_313_2400 : bothLoop evalE (oGrid.idx 313) (oGrid.dm 313) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 313) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2614426053269545002849994363604371045026408953493129781882689051422009888110⟩ ⟨false, 203821935960390677324386324333324064233036526330437756208993443313983944286⟩ = true := by
  decide +kernel

theorem o_row_313 : oGrid.row evalE 313 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_313_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_313_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_313_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_313_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_313_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_313_2000).1 (bothLoop_sound b_313_2400).1))))))

theorem n_row_313 : nGrid.row evalE 313 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_313_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_313_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_313_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_313_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_313_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_313_2000).2 (bothLoop_sound b_313_2400).2))))))

theorem b_314_0 : bothSeg evalE (oGrid.idx 314) (oGrid.dm 314) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 314) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1533403969587525058131770460297481588464139928272883399253551529977348641024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_314_400 : bothSeg evalE (oGrid.idx 314) (oGrid.dm 314) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 314) oGrid.kl oGrid.kr 400 400 ⟨false, 1533403969587525058131770460297481588464139928272883399253551529977348641024⟩ ⟨false, 0⟩ ⟨false, 2467364019822097032544538186876983843979424039431137411735539100263718712044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_314_800 : bothSeg evalE (oGrid.idx 314) (oGrid.dm 314) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 314) oGrid.kl oGrid.kr 400 800 ⟨false, 2467364019822097032544538186876983843979424039431137411735539100263718712044⟩ ⟨false, 0⟩ ⟨false, 2777311168440510120150876626376062520892717208435346068959934665245865067220⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_314_1200 : bothSeg evalE (oGrid.idx 314) (oGrid.dm 314) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 314) oGrid.kl oGrid.kr 400 1200 ⟨false, 2777311168440510120150876626376062520892717208435346068959934665245865067220⟩ ⟨false, 0⟩ ⟨false, 2766757366248508584588992828935901517560965944163686025556200305036702931998⟩ ⟨false, 32029877566342306905096555264724353278225814025637385137053266396841322152⟩ = true := by
  decide +kernel

theorem b_314_1600 : bothSeg evalE (oGrid.idx 314) (oGrid.dm 314) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 314) oGrid.kl oGrid.kr 400 1600 ⟨false, 2766757366248508584588992828935901517560965944163686025556200305036702931998⟩ ⟨false, 32029877566342306905096555264724353278225814025637385137053266396841322152⟩ ⟨false, 2607519719079029018919532719157908540416807496985303633097566027719780156060⟩ ⟨false, 191267524735821872574556665042717330422384261204019777595687543713764098090⟩ = true := by
  decide +kernel

theorem b_314_2000 : bothSeg evalE (oGrid.idx 314) (oGrid.dm 314) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 314) oGrid.kl oGrid.kr 400 2000 ⟨false, 2607519719079029018919532719157908540416807496985303633097566027719780156060⟩ ⟨false, 191267524735821872574556665042717330422384261204019777595687543713764098090⟩ ⟨false, 2601322896299982909626064840429316971510810602522572317889070395180954004948⟩ ⟨false, 203648195677746893170811265667656051132820331363717476345291894762647314996⟩ = true := by
  decide +kernel

theorem b_314_2400 : bothLoop evalE (oGrid.idx 314) (oGrid.dm 314) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 314) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2601322896299982909626064840429316971510810602522572317889070395180954004948⟩ ⟨false, 203648195677746893170811265667656051132820331363717476345291894762647314996⟩ = true := by
  decide +kernel

theorem o_row_314 : oGrid.row evalE 314 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_314_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_314_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_314_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_314_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_314_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_314_2000).1 (bothLoop_sound b_314_2400).1))))))

theorem n_row_314 : nGrid.row evalE 314 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_314_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_314_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_314_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_314_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_314_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_314_2000).2 (bothLoop_sound b_314_2400).2))))))

theorem b_315_0 : bothSeg evalE (oGrid.idx 315) (oGrid.dm 315) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 315) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1526578690923753687104294137503002998297105000390751273218103742010140711740⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_315_400 : bothSeg evalE (oGrid.idx 315) (oGrid.dm 315) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 315) oGrid.kl oGrid.kr 400 400 ⟨false, 1526578690923753687104294137503002998297105000390751273218103742010140711740⟩ ⟨false, 0⟩ ⟨false, 2456189666271349029560046892116698994314833414371540389315231509042874554546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_315_800 : bothSeg evalE (oGrid.idx 315) (oGrid.dm 315) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 315) oGrid.kl oGrid.kr 400 800 ⟨false, 2456189666271349029560046892116698994314833414371540389315231509042874554546⟩ ⟨false, 0⟩ ⟨false, 2764332671790307253744623777484669231050905412841420852762119489700753650480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_315_1200 : bothSeg evalE (oGrid.idx 315) (oGrid.dm 315) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 315) oGrid.kl oGrid.kr 400 1200 ⟨false, 2764332671790307253744623777484669231050905412841420852762119489700753650480⟩ ⟨false, 0⟩ ⟨false, 2753458894460407522590817243596724841127953521092433569008192273578567926858⟩ ⟨false, 32045693155564034229793281039167582602242151485911397245717232083835523170⟩ = true := by
  decide +kernel

theorem b_315_1600 : bothSeg evalE (oGrid.idx 315) (oGrid.dm 315) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 315) oGrid.kl oGrid.kr 400 1600 ⟨false, 2753458894460407522590817243596724841127953521092433569008192273578567926858⟩ ⟨false, 32045693155564034229793281039167582602242151485911397245717232083835523170⟩ ⟨false, 2594280194245269656415871674593132031193636492397673848155791074400820784942⟩ ⟨false, 191224393370701900404738850042760392536559180180671118098118431261582665086⟩ = true := by
  decide +kernel

theorem b_315_2000 : bothSeg evalE (oGrid.idx 315) (oGrid.dm 315) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 315) oGrid.kl oGrid.kr 400 2000 ⟨false, 2594280194245269656415871674593132031193636492397673848155791074400820784942⟩ ⟨false, 191224393370701900404738850042760392536559180180671118098118431261582665086⟩ ⟨false, 2588261976857900424020506135490369511890850164292837222982874828648095908960⟩ ⟨false, 203474885297434040208121269672309972574678096574015981396376445569639001654⟩ = true := by
  decide +kernel

theorem b_315_2400 : bothLoop evalE (oGrid.idx 315) (oGrid.dm 315) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 315) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2588261976857900424020506135490369511890850164292837222982874828648095908960⟩ ⟨false, 203474885297434040208121269672309972574678096574015981396376445569639001654⟩ = true := by
  decide +kernel

theorem o_row_315 : oGrid.row evalE 315 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_315_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_315_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_315_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_315_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_315_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_315_2000).1 (bothLoop_sound b_315_2400).1))))))

theorem n_row_315 : nGrid.row evalE 315 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_315_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_315_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_315_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_315_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_315_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_315_2000).2 (bothLoop_sound b_315_2400).2))))))

theorem b_316_0 : bothSeg evalE (oGrid.idx 316) (oGrid.dm 316) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 316) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1519775816694596714845750164317016571646948479982979285761351963028377200332⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_316_400 : bothSeg evalE (oGrid.idx 316) (oGrid.dm 316) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 316) oGrid.kl oGrid.kr 400 400 ⟨false, 1519775816694596714845750164317016571646948479982979285761351963028377200332⟩ ⟨false, 0⟩ ⟨false, 2445051266270073917534671002615127816293114433358079708543908628236437177474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_316_800 : bothSeg evalE (oGrid.idx 316) (oGrid.dm 316) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 316) oGrid.kl oGrid.kr 400 800 ⟨false, 2445051266270073917534671002615127816293114433358079708543908628236437177474⟩ ⟨false, 0⟩ ⟨false, 2751395753876470865578219384056929177399531133411120254211889863387674853508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_316_1200 : bothSeg evalE (oGrid.idx 316) (oGrid.dm 316) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 316) oGrid.kl oGrid.kr 400 1200 ⟨false, 2751395753876470865578219384056929177399531133411120254211889863387674853508⟩ ⟨false, 0⟩ ⟨false, 2740198366564501370914412869117558182090462592965009511344832146585981219418⟩ ⟨false, 32067691706624683230246903851846450982771491800094232513299755669885748910⟩ = true := by
  decide +kernel

theorem b_316_1600 : bothSeg evalE (oGrid.idx 316) (oGrid.dm 316) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 316) oGrid.kl oGrid.kr 400 1600 ⟨false, 2740198366564501370914412869117558182090462592965009511344832146585981219418⟩ ⟨false, 32067691706624683230246903851846450982771491800094232513299755669885748910⟩ ⟨false, 2581085192220748012234607702161797782465325550928513388427540388261907336442⟩ ⟨false, 191180866050378041910052070807606850607908533836590355430591513993959631886⟩ = true := by
  decide +kernel

theorem b_316_2000 : bothSeg evalE (oGrid.idx 316) (oGrid.dm 316) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 316) oGrid.kl oGrid.kr 400 2000 ⟨false, 2581085192220748012234607702161797782465325550928513388427540388261907336442⟩ ⟨false, 191180866050378041910052070807606850607908533836590355430591513993959631886⟩ ⟨false, 2575243346552065323011328350364439946370557709775636051027717141980229255286⟩ ⟨false, 203301921111678179638581024789081493827177772407844726022104031489347772806⟩ = true := by
  decide +kernel

theorem b_316_2400 : bothLoop evalE (oGrid.idx 316) (oGrid.dm 316) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 316) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2575243346552065323011328350364439946370557709775636051027717141980229255286⟩ ⟨false, 203301921111678179638581024789081493827177772407844726022104031489347772806⟩ = true := by
  decide +kernel

theorem o_row_316 : oGrid.row evalE 316 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_316_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_316_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_316_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_316_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_316_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_316_2000).1 (bothLoop_sound b_316_2400).1))))))

theorem n_row_316 : nGrid.row evalE 316 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_316_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_316_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_316_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_316_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_316_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_316_2000).2 (bothLoop_sound b_316_2400).2))))))

theorem b_317_0 : bothSeg evalE (oGrid.idx 317) (oGrid.dm 317) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 317) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1512995271305460039074386242629758464831347987989964490493701781905902682582⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_317_400 : bothSeg evalE (oGrid.idx 317) (oGrid.dm 317) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 317) oGrid.kl oGrid.kr 400 400 ⟨false, 1512995271305460039074386242629758464831347987989964490493701781905902682582⟩ ⟨false, 0⟩ ⟨false, 2433948717780390126509106736690360091091268487823043138536619222054872990330⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_317_800 : bothSeg evalE (oGrid.idx 317) (oGrid.dm 317) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 317) oGrid.kl oGrid.kr 400 800 ⟨false, 2433948717780390126509106736690360091091268487823043138536619222054872990330⟩ ⟨false, 0⟩ ⟨false, 2738500329771995122913157154463476114437769501744136983658703460592951780022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_317_1200 : bothSeg evalE (oGrid.idx 317) (oGrid.dm 317) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 317) oGrid.kl oGrid.kr 400 1200 ⟨false, 2738500329771995122913157154463476114437769501744136983658703460592951780022⟩ ⟨false, 0⟩ ⟨false, 2726975547101338541109631170307931826922078322409506662613559949460606571448⟩ ⟨false, 32095775547915142780664783168120654361858811471043284549052599233095229022⟩ = true := by
  decide +kernel

theorem b_317_1600 : bothSeg evalE (oGrid.idx 317) (oGrid.dm 317) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 317) oGrid.kl oGrid.kr 400 1600 ⟨false, 2726975547101338541109631170307931826922078322409506662613559949460606571448⟩ ⟨false, 32095775547915142780664783168120654361858811471043284549052599233095229022⟩ ⟨false, 2567934666498481778365047385237182890769877319794016513426333977509367062712⟩ ⟨false, 191136656150771905525248568238869590514059814086533433736278571184334737758⟩ = true := by
  decide +kernel

theorem b_317_2000 : bothSeg evalE (oGrid.idx 317) (oGrid.dm 317) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 317) oGrid.kl oGrid.kr 400 2000 ⟨false, 2567934666498481778365047385237182890769877319794016513426333977509367062712⟩ ⟨false, 191136656150771905525248568238869590514059814086533433736278571184334737758⟩ ⟨false, 2562266957124568236016718866750203485070483018901322853678425594933658959196⟩ ⟨false, 203129170044348449593910744212005733440530275034011810591722354885421736848⟩ = true := by
  decide +kernel

theorem b_317_2400 : bothLoop evalE (oGrid.idx 317) (oGrid.dm 317) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 317) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2562266957124568236016718866750203485070483018901322853678425594933658959196⟩ ⟨false, 203129170044348449593910744212005733440530275034011810591722354885421736848⟩ = true := by
  decide +kernel

theorem o_row_317 : oGrid.row evalE 317 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_317_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_317_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_317_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_317_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_317_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_317_2000).1 (bothLoop_sound b_317_2400).1))))))

theorem n_row_317 : nGrid.row evalE 317 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_317_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_317_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_317_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_317_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_317_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_317_2000).2 (bothLoop_sound b_317_2400).2))))))

theorem b_318_0 : bothSeg evalE (oGrid.idx 318) (oGrid.dm 318) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 318) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1506237003850181231717529035843536684116989915659118134443613303469772598532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_318_400 : bothSeg evalE (oGrid.idx 318) (oGrid.dm 318) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 318) oGrid.kl oGrid.kr 400 400 ⟨false, 1506237003850181231717529035843536684116989915659118134443613303469772598532⟩ ⟨false, 0⟩ ⟨false, 2422881953514454384810045381125417293959858398743271874384868716344343492106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_318_800 : bothSeg evalE (oGrid.idx 318) (oGrid.dm 318) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 318) oGrid.kl oGrid.kr 400 800 ⟨false, 2422881953514454384810045381125417293959858398743271874384868716344343492106⟩ ⟨false, 0⟩ ⟨false, 2725646218511109865041052275862092512906320760233783779977581032774359404888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_318_1200 : bothSeg evalE (oGrid.idx 318) (oGrid.dm 318) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 318) oGrid.kl oGrid.kr 400 1200 ⟨false, 2725646218511109865041052275862092512906320760233783779977581032774359404888⟩ ⟨false, 0⟩ ⟨false, 2713790211422065360024550825387597560059226391168499908202273893038739189560⟩ ⟨false, 32129992068655092315322987505637793138147067954310309656721204525091086842⟩ = true := by
  decide +kernel

theorem b_318_1600 : bothSeg evalE (oGrid.idx 318) (oGrid.dm 318) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 318) oGrid.kl oGrid.kr 400 1600 ⟨false, 2713790211422065360024550825387597560059226391168499908202273893038739189560⟩ ⟨false, 32129992068655092315322987505637793138147067954310309656721204525091086842⟩ ⟨false, 2554828492758988725199065448062774691738455527790156480523539577175112265810⟩ ⟨false, 191091710731731727140808364830460661458917931332653737335455520388718010592⟩ = true := by
  decide +kernel

theorem b_318_2000 : bothSeg evalE (oGrid.idx 318) (oGrid.dm 318) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 318) oGrid.kl oGrid.kr 400 2000 ⟨false, 2554828492758988725199065448062774691738455527790156480523539577175112265810⟩ ⟨false, 191091710731731727140808364830460661458917931332653737335455520388718010592⟩ ⟨false, 2549332608177705257154657720216402801783802918818429602759905313700333029564⟩ ⟨false, 202956742655140171179312418272793121779952737220823186741281944439094001458⟩ = true := by
  decide +kernel

theorem b_318_2400 : bothLoop evalE (oGrid.idx 318) (oGrid.dm 318) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 318) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2549332608177705257154657720216402801783802918818429602759905313700333029564⟩ ⟨false, 202956742655140171179312418272793121779952737220823186741281944439094001458⟩ = true := by
  decide +kernel

theorem o_row_318 : oGrid.row evalE 318 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_318_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_318_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_318_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_318_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_318_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_318_2000).1 (bothLoop_sound b_318_2400).1))))))

theorem n_row_318 : nGrid.row evalE 318 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_318_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_318_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_318_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_318_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_318_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_318_2000).2 (bothLoop_sound b_318_2400).2))))))

theorem b_319_0 : bothSeg evalE (oGrid.idx 319) (oGrid.dm 319) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 319) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1499500956865447936323094403299855731411617156050625434515055584480469850038⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_319_400 : bothSeg evalE (oGrid.idx 319) (oGrid.dm 319) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 319) oGrid.kl oGrid.kr 400 400 ⟨false, 1499500956865447936323094403299855731411617156050625434515055584480469850038⟩ ⟨false, 0⟩ ⟨false, 2411850874129971870675685733961605731165168198945607557190887579948724806928⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_319_800 : bothSeg evalE (oGrid.idx 319) (oGrid.dm 319) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 319) oGrid.kl oGrid.kr 400 800 ⟨false, 2411850874129971870675685733961605731165168198945607557190887579948724806928⟩ ⟨false, 0⟩ ⟨false, 2712833444984496122599915800708869958873350714645717006379370303974335068116⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_319_1200 : bothSeg evalE (oGrid.idx 319) (oGrid.dm 319) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 319) oGrid.kl oGrid.kr 400 1200 ⟨false, 2712833444984496122599915800708869958873350714645717006379370303974335068116⟩ ⟨false, 0⟩ ⟨false, 2700642169133995401673039491788296817343800970314851590824851276148647089202⟩ ⟨false, 32170714025246131502854289278335021058660910326009502033980959029659033712⟩ = true := by
  decide +kernel

theorem b_319_1600 : bothSeg evalE (oGrid.idx 319) (oGrid.dm 319) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 319) oGrid.kl oGrid.kr 400 1600 ⟨false, 2700642169133995401673039491788296817343800970314851590824851276148647089202⟩ ⟨false, 32170714025246131502854289278335021058660910326009502033980959029659033712⟩ ⟨false, 2541766567894742584994151642767127863321251264013800364695805858806000164702⟩ ⟨false, 191046315264498948181742138299503975081210616627060728163026376372305958212⟩ = true := by
  decide +kernel

theorem b_319_2000 : bothSeg evalE (oGrid.idx 319) (oGrid.dm 319) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 319) oGrid.kl oGrid.kr 400 2000 ⟨false, 2541766567894742584994151642767127863321251264013800364695805858806000164702⟩ ⟨false, 191046315264498948181742138299503975081210616627060728163026376372305958212⟩ ⟨false, 2536440202516859548580459116994215969137217034837764128371574988244712102680⟩ ⟨false, 202784634119770423250746689576192037181665333107418791356079107410721094414⟩ = true := by
  decide +kernel

theorem b_319_2400 : bothLoop evalE (oGrid.idx 319) (oGrid.dm 319) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 319) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2536440202516859548580459116994215969137217034837764128371574988244712102680⟩ ⟨false, 202784634119770423250746689576192037181665333107418791356079107410721094414⟩ = true := by
  decide +kernel

theorem o_row_319 : oGrid.row evalE 319 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_319_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_319_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_319_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_319_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_319_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_319_2000).1 (bothLoop_sound b_319_2400).1))))))

theorem n_row_319 : nGrid.row evalE 319 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_319_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_319_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_319_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_319_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_319_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_319_2000).2 (bothLoop_sound b_319_2400).2))))))

theorem b_320_0 : bothSeg evalE (oGrid.idx 320) (oGrid.dm 320) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 320) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1492787081048939448774491960105002714802655112735347903439888444731208798516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_320_400 : bothSeg evalE (oGrid.idx 320) (oGrid.dm 320) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 320) oGrid.kl oGrid.kr 400 400 ⟨false, 1492787081048939448774491960105002714802655112735347903439888444731208798516⟩ ⟨false, 0⟩ ⟨false, 2400855402170630788594603151253730984678676173582933303046509583821895225710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_320_800 : bothSeg evalE (oGrid.idx 320) (oGrid.dm 320) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 320) oGrid.kl oGrid.kr 400 800 ⟨false, 2400855402170630788594603151253730984678676173582933303046509583821895225710⟩ ⟨false, 0⟩ ⟨false, 2700061874063766440089219095142276903210622860809482717807072433973138206796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_320_1200 : bothSeg evalE (oGrid.idx 320) (oGrid.dm 320) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 320) oGrid.kl oGrid.kr 400 1200 ⟨false, 2700061874063766440089219095142276903210622860809482717807072433973138206796⟩ ⟨false, 0⟩ ⟨false, 2687531191310737892011681285645373164492403663738187264415435664311824862702⟩ ⟨false, 32217939854914505611080660894456864812344192385865752329904964675029377776⟩ = true := by
  decide +kernel

theorem b_320_1600 : bothSeg evalE (oGrid.idx 320) (oGrid.dm 320) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 320) oGrid.kl oGrid.kr 400 1600 ⟨false, 2687531191310737892011681285645373164492403663738187264415435664311824862702⟩ ⟨false, 32217939854914505611080660894456864812344192385865752329904964675029377776⟩ ⟨false, 2528748915622158024602578863686177740482689429434822365392498333848425111924⟩ ⟨false, 191000215543494373020183082853652288822058426689230651352842295138429128554⟩ = true := by
  decide +kernel

theorem b_320_2000 : bothSeg evalE (oGrid.idx 320) (oGrid.dm 320) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 320) oGrid.kl oGrid.kr 400 2000 ⟨false, 2528748915622158024602578863686177740482689429434822365392498333848425111924⟩ ⟨false, 191000215543494373020183082853652288822058426689230651352842295138429128554⟩ ⟨false, 2523589760754931863492406485907216624926013381804492590967000290993852913158⟩ ⟨false, 202612346353475890801249617966438200999676217687980802448655405359437651006⟩ = true := by
  decide +kernel

theorem b_320_2400 : bothLoop evalE (oGrid.idx 320) (oGrid.dm 320) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 320) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2523589760754931863492406485907216624926013381804492590967000290993852913158⟩ ⟨false, 202612346353475890801249617966438200999676217687980802448655405359437651006⟩ = true := by
  decide +kernel

theorem o_row_320 : oGrid.row evalE 320 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_320_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_320_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_320_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_320_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_320_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_320_2000).1 (bothLoop_sound b_320_2400).1))))))

theorem n_row_320 : nGrid.row evalE 320 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_320_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_320_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_320_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_320_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_320_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_320_2000).2 (bothLoop_sound b_320_2400).2))))))

theorem b_321_0 : bothSeg evalE (oGrid.idx 321) (oGrid.dm 321) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 321) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1486095289701086537073903478697579110503714015024584547399209636940584694292⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_321_400 : bothSeg evalE (oGrid.idx 321) (oGrid.dm 321) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 321) oGrid.kl oGrid.kr 400 400 ⟨false, 1486095289701086537073903478697579110503714015024584547399209636940584694292⟩ ⟨false, 0⟩ ⟨false, 2389895431539563763285674450635744796702581809304862754444517476130745995994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_321_800 : bothSeg evalE (oGrid.idx 321) (oGrid.dm 321) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 321) oGrid.kl oGrid.kr 400 800 ⟨false, 2389895431539563763285674450635744796702581809304862754444517476130745995994⟩ ⟨false, 0⟩ ⟨false, 2687331351301775036873390522408518225276437796894395617451580056796400583982⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_321_1200 : bothSeg evalE (oGrid.idx 321) (oGrid.dm 321) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 321) oGrid.kl oGrid.kr 400 1200 ⟨false, 2687331351301775036873390522408518225276437796894395617451580056796400583982⟩ ⟨false, 0⟩ ⟨false, 2674457051066347955953552200229462345463491958077598291710352946203237432354⟩ ⟨false, 32271737854164388187237697855326694180229321431568089879225982299205741618⟩ = true := by
  decide +kernel

theorem b_321_1600 : bothSeg evalE (oGrid.idx 321) (oGrid.dm 321) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 321) oGrid.kl oGrid.kr 400 1600 ⟨false, 2674457051066347955953552200229462345463491958077598291710352946203237432354⟩ ⟨false, 32271737854164388187237697855326694180229321431568089879225982299205741618⟩ ⟨false, 2515775325204161556756789299448107274442180948248393926452625960296259314498⟩ ⟨false, 190953463716350787384000598636681765201540331260772455136952968206183859474⟩ = true := by
  decide +kernel

theorem b_321_2000 : bothSeg evalE (oGrid.idx 321) (oGrid.dm 321) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 321) oGrid.kl oGrid.kr 400 2000 ⟨false, 2515775325204161556756789299448107274442180948248393926452625960296259314498⟩ ⟨false, 190953463716350787384000598636681765201540331260772455136952968206183859474⟩ ⟨false, 2510781005640821978046587784921677787824060578911708882219984198025683072352⟩ ⟨false, 202440502439973089381179350662837411665542591171527708111192220257962421626⟩ = true := by
  decide +kernel

theorem b_321_2400 : bothLoop evalE (oGrid.idx 321) (oGrid.dm 321) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 321) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2510781005640821978046587784921677787824060578911708882219984198025683072352⟩ ⟨false, 202440502439973089381179350662837411665542591171527708111192220257962421626⟩ = true := by
  decide +kernel

theorem o_row_321 : oGrid.row evalE 321 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_321_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_321_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_321_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_321_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_321_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_321_2000).1 (bothLoop_sound b_321_2400).1))))))

theorem n_row_321 : nGrid.row evalE 321 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_321_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_321_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_321_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_321_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_321_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_321_2000).2 (bothLoop_sound b_321_2400).2))))))

theorem b_322_0 : bothSeg evalE (oGrid.idx 322) (oGrid.dm 322) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 322) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1479425555859368060919018194444480807135054790559887415861298109249784584682⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_322_400 : bothSeg evalE (oGrid.idx 322) (oGrid.dm 322) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 322) oGrid.kl oGrid.kr 400 400 ⟨false, 1479425555859368060919018194444480807135054790559887415861298109249784584682⟩ ⟨false, 0⟩ ⟨false, 2378970906642572618309986362876448242031921123965628391218088029977664592400⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_322_800 : bothSeg evalE (oGrid.idx 322) (oGrid.dm 322) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 322) oGrid.kl oGrid.kr 400 800 ⟨false, 2378970906642572618309986362876448242031921123965628391218088029977664592400⟩ ⟨false, 0⟩ ⟨false, 2674641871360494016881764496172027645953230597635099882427125928391005441754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_322_1200 : bothSeg evalE (oGrid.idx 322) (oGrid.dm 322) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 322) oGrid.kl oGrid.kr 400 1200 ⟨false, 2674641871360494016881764496172027645953230597635099882427125928391005441754⟩ ⟨false, 0⟩ ⟨false, 2661419868652396276685994714655661061664380313636698885635916345686197372126⟩ ⟨false, 32332187356079595262921410394251179427327158895376977646408741561499004294⟩ = true := by
  decide +kernel

theorem b_322_1600 : bothSeg evalE (oGrid.idx 322) (oGrid.dm 322) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 322) oGrid.kl oGrid.kr 400 1600 ⟨false, 2661419868652396276685994714655661061664380313636698885635916345686197372126⟩ ⟨false, 32332187356079595262921410394251179427327158895376977646408741561499004294⟩ ⟨false, 2502846053378800431499269542008287220090860502055082149406051063043854714396⟩ ⟨false, 190906002629675440449646583041625021000846970476993713876274024203841662024⟩ = true := by
  decide +kernel

theorem b_322_2000 : bothSeg evalE (oGrid.idx 322) (oGrid.dm 322) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 322) oGrid.kl oGrid.kr 400 2000 ⟨false, 2502846053378800431499269542008287220090860502055082149406051063043854714396⟩ ⟨false, 190906002629675440449646583041625021000846970476993713876274024203841662024⟩ ⟨false, 2498014197751435390268421855221639600377178224826448498300225961672170407924⟩ ⟨false, 202268928578297625692675958891096481071890368076740337927340549134740130990⟩ = true := by
  decide +kernel

theorem b_322_2400 : bothLoop evalE (oGrid.idx 322) (oGrid.dm 322) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 322) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2498014197751435390268421855221639600377178224826448498300225961672170407924⟩ ⟨false, 202268928578297625692675958891096481071890368076740337927340549134740130990⟩ = true := by
  decide +kernel

theorem o_row_322 : oGrid.row evalE 322 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_322_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_322_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_322_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_322_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_322_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_322_2000).1 (bothLoop_sound b_322_2400).1))))))

theorem n_row_322 : nGrid.row evalE 322 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_322_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_322_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_322_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_322_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_322_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_322_2000).2 (bothLoop_sound b_322_2400).2))))))

theorem b_323_0 : bothSeg evalE (oGrid.idx 323) (oGrid.dm 323) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 323) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1472777809050646165770223948698541246789161361722668547393613012679348452836⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_323_400 : bothSeg evalE (oGrid.idx 323) (oGrid.dm 323) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 323) oGrid.kl oGrid.kr 400 400 ⟨false, 1472777809050646165770223948698541246789161361722668547393613012679348452836⟩ ⟨false, 0⟩ ⟨false, 2368081724347017986948863555136690305314012772876532236794768849322310405622⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_323_800 : bothSeg evalE (oGrid.idx 323) (oGrid.dm 323) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 323) oGrid.kl oGrid.kr 400 800 ⟨false, 2368081724347017986948863555136690305314012772876532236794768849322310405622⟩ ⟨false, 0⟩ ⟨false, 2661993326318475870809022843961595384801997089548427696440249879066456166910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_323_1200 : bothSeg evalE (oGrid.idx 323) (oGrid.dm 323) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 323) oGrid.kl oGrid.kr 400 1200 ⟨false, 2661993326318475870809022843961595384801997089548427696440249879066456166910⟩ ⟨false, 0⟩ ⟨false, 2648418494271463929313789638152802762907783354591690570710103968625858697050⟩ ⟨false, 32399837671483650905586122385636466445307441218948514057476168954433104266⟩ = true := by
  decide +kernel

theorem b_323_1600 : bothSeg evalE (oGrid.idx 323) (oGrid.dm 323) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 323) oGrid.kl oGrid.kr 400 1600 ⟨false, 2648418494271463929313789638152802762907783354591690570710103968625858697050⟩ ⟨false, 32399837671483650905586122385636466445307441218948514057476168954433104266⟩ ⟨false, 2489960087251674575783858990373359230058541881224500197087055039178938433950⟩ ⟨false, 190858244691273004435516770165079999294548914586138887680525098401353367366⟩ = true := by
  decide +kernel

theorem b_323_2000 : bothSeg evalE (oGrid.idx 323) (oGrid.dm 323) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 323) oGrid.kl oGrid.kr 400 2000 ⟨false, 2489960087251674575783858990373359230058541881224500197087055039178938433950⟩ ⟨false, 190858244691273004435516770165079999294548914586138887680525098401353367366⟩ ⟨false, 2485288300731597859673095775399656419554698324836717163736056803006623091374⟩ ⟨false, 202097691019675078857580786201802347161521238429506361106972608560067632122⟩ = true := by
  decide +kernel

theorem b_323_2400 : bothLoop evalE (oGrid.idx 323) (oGrid.dm 323) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 323) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2485288300731597859673095775399656419554698324836717163736056803006623091374⟩ ⟨false, 202097691019675078857580786201802347161521238429506361106972608560067632122⟩ = true := by
  decide +kernel

theorem o_row_323 : oGrid.row evalE 323 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_323_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_323_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_323_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_323_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_323_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_323_2000).1 (bothLoop_sound b_323_2400).1))))))

theorem n_row_323 : nGrid.row evalE 323 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_323_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_323_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_323_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_323_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_323_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_323_2000).2 (bothLoop_sound b_323_2400).2))))))

theorem b_324_0 : bothSeg evalE (oGrid.idx 324) (oGrid.dm 324) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 324) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1466151991266392746009239777748711768923894432121104237391956310805391176882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_324_400 : bothSeg evalE (oGrid.idx 324) (oGrid.dm 324) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 324) oGrid.kl oGrid.kr 400 400 ⟨false, 1466151991266392746009239777748711768923894432121104237391956310805391176882⟩ ⟨false, 0⟩ ⟨false, 2357227816036402931717977491711145200903419441851492513417602921137422477650⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_324_800 : bothSeg evalE (oGrid.idx 324) (oGrid.dm 324) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 324) oGrid.kl oGrid.kr 400 800 ⟨false, 2357227816036402931717977491711145200903419441851492513417602921137422477650⟩ ⟨false, 0⟩ ⟨false, 2649385560515198506498186646131874579431825560661446835425776132932397676564⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_324_1200 : bothSeg evalE (oGrid.idx 324) (oGrid.dm 324) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 324) oGrid.kl oGrid.kr 400 1200 ⟨false, 2649385560515198506498186646131874579431825560661446835425776132932397676564⟩ ⟨false, 0⟩ ⟨false, 2635453320230654079209028435263094829166292259374680596201113054654173832300⟩ ⟨false, 32474409657722535269799510833324107779613086153207325792266926322605784688⟩ = true := by
  decide +kernel

theorem b_324_1600 : bothSeg evalE (oGrid.idx 324) (oGrid.dm 324) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 324) oGrid.kl oGrid.kr 400 1600 ⟨false, 2635453320230654079209028435263094829166292259374680596201113054654173832300⟩ ⟨false, 32474409657722535269799510833324107779613086153207325792266926322605784688⟩ ⟨false, 2477117876556794097734388283917072755956408822302567472816446500333680369738⟩ ⟨false, 190809853331582516744439662179346180989496523225320449176933480643099247250⟩ = true := by
  decide +kernel

theorem b_324_2000 : bothSeg evalE (oGrid.idx 324) (oGrid.dm 324) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 324) oGrid.kl oGrid.kr 400 2000 ⟨false, 2477117876556794097734388283917072755956408822302567472816446500333680369738⟩ ⟨false, 190809853331582516744439662179346180989496523225320449176933480643099247250⟩ ⟨false, 2472603741830169186364269268156550545210966379634227861335435208173356469784⟩ ⟨false, 201926683617012001522014964506417323702193765863246602127608992751607277812⟩ = true := by
  decide +kernel

theorem b_324_2400 : bothLoop evalE (oGrid.idx 324) (oGrid.dm 324) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 324) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2472603741830169186364269268156550545210966379634227861335435208173356469784⟩ ⟨false, 201926683617012001522014964506417323702193765863246602127608992751607277812⟩ = true := by
  decide +kernel

theorem o_row_324 : oGrid.row evalE 324 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_324_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_324_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_324_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_324_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_324_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_324_2000).1 (bothLoop_sound b_324_2400).1))))))

theorem n_row_324 : nGrid.row evalE 324 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_324_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_324_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_324_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_324_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_324_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_324_2000).2 (bothLoop_sound b_324_2400).2))))))

theorem b_325_0 : bothSeg evalE (oGrid.idx 325) (oGrid.dm 325) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 325) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1459548043087839923940331451013856413916724386592026056991042475648774345554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_325_400 : bothSeg evalE (oGrid.idx 325) (oGrid.dm 325) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 325) oGrid.kl oGrid.kr 400 400 ⟨false, 1459548043087839923940331451013856413916724386592026056991042475648774345554⟩ ⟨false, 0⟩ ⟨false, 2346409070345342727154694075492042121944329199175802320452633539973427892022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_325_800 : bothSeg evalE (oGrid.idx 325) (oGrid.dm 325) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 325) oGrid.kl oGrid.kr 400 800 ⟨false, 2346409070345342727154694075492042121944329199175802320452633539973427892022⟩ ⟨false, 0⟩ ⟨false, 2636818559972956773808863053948756604454634574922212315411406463243653981326⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_325_1200 : bothSeg evalE (oGrid.idx 325) (oGrid.dm 325) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 325) oGrid.kl oGrid.kr 400 1200 ⟨false, 2636818559972956773808863053948756604454634574922212315411406463243653981326⟩ ⟨false, 0⟩ ⟨false, 2622524156795966211142560605419431081124210291336019712252742682919516421952⟩ ⟨false, 32556021074315544467515007816666507390515044822072008500857428538044573164⟩ = true := by
  decide +kernel

theorem b_325_1600 : bothSeg evalE (oGrid.idx 325) (oGrid.dm 325) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 325) oGrid.kl oGrid.kr 400 1600 ⟨false, 2622524156795966211142560605419431081124210291336019712252742682919516421952⟩ ⟨false, 32556021074315544467515007816666507390515044822072008500857428538044573164⟩ ⟨false, 2464319350273595969506375515298819250502926019884786867652629786150931277988⟩ ⟨false, 190760827596685786103700097937278338011799316273304853100970325306629717128⟩ = true := by
  decide +kernel

theorem b_325_2000 : bothSeg evalE (oGrid.idx 325) (oGrid.dm 325) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 325) oGrid.kl oGrid.kr 400 2000 ⟨false, 2464319350273595969506375515298819250502926019884786867652629786150931277988⟩ ⟨false, 190760827596685786103700097937278338011799316273304853100970325306629717128⟩ ⟨false, 2459960414474807415056868791369562677865152096515354983505986532095900883210⟩ ⟨false, 201755746395049473553296625297548194465593364616374042732089805653346803456⟩ = true := by
  decide +kernel

theorem b_325_2400 : bothLoop evalE (oGrid.idx 325) (oGrid.dm 325) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 325) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2459960414474807415056868791369562677865152096515354983505986532095900883210⟩ ⟨false, 201755746395049473553296625297548194465593364616374042732089805653346803456⟩ = true := by
  decide +kernel

theorem o_row_325 : oGrid.row evalE 325 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_325_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_325_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_325_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_325_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_325_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_325_2000).1 (bothLoop_sound b_325_2400).1))))))

theorem n_row_325 : nGrid.row evalE 325 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_325_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_325_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_325_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_325_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_325_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_325_2000).2 (bothLoop_sound b_325_2400).2))))))

theorem b_326_0 : bothSeg evalE (oGrid.idx 326) (oGrid.dm 326) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 326) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1452965918212244528114485025266077485310475741489919413475058819358682095158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_326_400 : bothSeg evalE (oGrid.idx 326) (oGrid.dm 326) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 326) oGrid.kl oGrid.kr 400 400 ⟨false, 1452965918212244528114485025266077485310475741489919413475058819358682095158⟩ ⟨false, 0⟩ ⟨false, 2335625434768742753166418023740162023746682030415922008199645786807866867164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_326_800 : bothSeg evalE (oGrid.idx 326) (oGrid.dm 326) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 326) oGrid.kl oGrid.kr 400 800 ⟨false, 2335625434768742753166418023740162023746682030415922008199645786807866867164⟩ ⟨false, 0⟩ ⟨false, 2624292219083922524529871491894874962604140401021740413926338248037296631804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_326_1200 : bothSeg evalE (oGrid.idx 326) (oGrid.dm 326) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 326) oGrid.kl oGrid.kr 400 1200 ⟨false, 2624292219083922524529871491894874962604140401021740413926338248037296631804⟩ ⟨false, 0⟩ ⟨false, 2609630897306758251915714888196861628058744380180089440622705374621820060158⟩ ⟨false, 32644636630178388441161344757710135291061218179474500745520459038131976942⟩ = true := by
  decide +kernel

theorem b_326_1600 : bothSeg evalE (oGrid.idx 326) (oGrid.dm 326) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 326) oGrid.kl oGrid.kr 400 1600 ⟨false, 2609630897306758251915714888196861628058744380180089440622705374621820060158⟩ ⟨false, 32644636630178388441161344757710135291061218179474500745520459038131976942⟩ ⟨false, 2451564505058291355604287370134363045199296580554072907042036800242438911162⟩ ⟨false, 190711028878645284752588862820208718150509017805491034326189033417513125938⟩ = true := by
  decide +kernel

theorem b_326_2000 : bothSeg evalE (oGrid.idx 326) (oGrid.dm 326) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 326) oGrid.kl oGrid.kr 400 2000 ⟨false, 2451564505058291355604287370134363045199296580554072907042036800242438911162⟩ ⟨false, 190711028878645284752588862820208718150509017805491034326189033417513125938⟩ ⟨false, 2447358324964748375822954355792945977525539037404316904935763827172524032456⟩ ⟨false, 201585041049554827245426277249705663356254546434761172710002389406466596506⟩ = true := by
  decide +kernel

theorem b_326_2400 : bothLoop evalE (oGrid.idx 326) (oGrid.dm 326) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 326) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2447358324964748375822954355792945977525539037404316904935763827172524032456⟩ ⟨false, 201585041049554827245426277249705663356254546434761172710002389406466596506⟩ = true := by
  decide +kernel

theorem o_row_326 : oGrid.row evalE 326 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_326_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_326_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_326_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_326_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_326_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_326_2000).1 (bothLoop_sound b_326_2400).1))))))

theorem n_row_326 : nGrid.row evalE 326 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_326_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_326_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_326_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_326_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_326_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_326_2000).2 (bothLoop_sound b_326_2400).2))))))

theorem b_327_0 : bothSeg evalE (oGrid.idx 327) (oGrid.dm 327) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 327) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1446405559171110146481772365313742270685582778570225124948016954361480383446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_327_400 : bothSeg evalE (oGrid.idx 327) (oGrid.dm 327) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 327) oGrid.kl oGrid.kr 400 400 ⟨false, 1446405559171110146481772365313742270685582778570225124948016954361480383446⟩ ⟨false, 0⟩ ⟨false, 2324876813695642182744720718563673418304346396820928117387281524749215510638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_327_800 : bothSeg evalE (oGrid.idx 327) (oGrid.dm 327) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 327) oGrid.kl oGrid.kr 400 800 ⟨false, 2324876813695642182744720718563673418304346396820928117387281524749215510638⟩ ⟨false, 0⟩ ⟨false, 2611806404188659930585425212603293299494341917915774321111302953636344442760⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_327_1200 : bothSeg evalE (oGrid.idx 327) (oGrid.dm 327) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 327) oGrid.kl oGrid.kr 400 1200 ⟨false, 2611806404188659930585425212603293299494341917915774321111302953636344442760⟩ ⟨false, 0⟩ ⟨false, 2596773273037131844517612038213006776595618120581522890221897064946945721664⟩ ⟨false, 32740615739513867806013418652856198592073152584172201366445819153917208196⟩ = true := by
  decide +kernel

theorem b_327_1600 : bothSeg evalE (oGrid.idx 327) (oGrid.dm 327) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 327) oGrid.kl oGrid.kr 400 1600 ⟨false, 2596773273037131844517612038213006776595618120581522890221897064946945721664⟩ ⟨false, 32740615739513867806013418652856198592073152584172201366445819153917208196⟩ ⟨false, 2438853090767428083691145953706943352536365152439602290956294355206166353450⟩ ⟨false, 190660798009217628632479503158919622651326120726092800632048528894696576410⟩ = true := by
  decide +kernel

theorem b_327_2000 : bothSeg evalE (oGrid.idx 327) (oGrid.dm 327) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 327) oGrid.kl oGrid.kr 400 2000 ⟨false, 2438853090767428083691145953706943352536365152439602290956294355206166353450⟩ ⟨false, 190660798009217628632479503158919622651326120726092800632048528894696576410⟩ ⟨false, 2434797236242266121492928938259351468281781178747866441974723580115358582108⟩ ⟨false, 201414862947091837365124101640226594809850345557080227776144162493927329824⟩ = true := by
  decide +kernel

theorem b_327_2400 : bothLoop evalE (oGrid.idx 327) (oGrid.dm 327) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 327) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2434797236242266121492928938259351468281781178747866441974723580115358582108⟩ ⟨false, 201414862947091837365124101640226594809850345557080227776144162493927329824⟩ = true := by
  decide +kernel

theorem o_row_327 : oGrid.row evalE 327 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_327_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_327_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_327_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_327_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_327_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_327_2000).1 (bothLoop_sound b_327_2400).1))))))

theorem n_row_327 : nGrid.row evalE 327 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_327_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_327_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_327_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_327_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_327_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_327_2000).2 (bothLoop_sound b_327_2400).2))))))

theorem b_328_0 : bothSeg evalE (oGrid.idx 328) (oGrid.dm 328) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 328) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1439866888955411365963481815526842978732918348525208569971846909095927231420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_328_400 : bothSeg evalE (oGrid.idx 328) (oGrid.dm 328) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 328) oGrid.kl oGrid.kr 400 400 ⟨false, 1439866888955411365963481815526842978732918348525208569971846909095927231420⟩ ⟨false, 0⟩ ⟨false, 2314163103184262565241565108387200194317324045512552485758948525452628579072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_328_800 : bothSeg evalE (oGrid.idx 328) (oGrid.dm 328) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 328) oGrid.kl oGrid.kr 400 800 ⟨false, 2314163103184262565241565108387200194317324045512552485758948525452628579072⟩ ⟨false, 0⟩ ⟨false, 2599361047923017037214473583362062439540129543745366243346160022040287770716⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_328_1200 : bothSeg evalE (oGrid.idx 328) (oGrid.dm 328) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 328) oGrid.kl oGrid.kr 400 1200 ⟨false, 2599361047923017037214473583362062439540129543745366243346160022040287770716⟩ ⟨false, 0⟩ ⟨false, 2583951213421694921456152539259523793868903763144889080462753953363335750016⟩ ⟨false, 32843934978807911846659855140368582044461396579924169038060480162321111546⟩ = true := by
  decide +kernel

theorem b_328_1600 : bothSeg evalE (oGrid.idx 328) (oGrid.dm 328) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 328) oGrid.kl oGrid.kr 400 1600 ⟨false, 2583951213421694921456152539259523793868903763144889080462753953363335750016⟩ ⟨false, 32843934978807911846659855140368582044461396579924169038060480162321111546⟩ ⟨false, 2426185211457594951396700111507174215241965330115843586905070296353138984746⟩ ⟨false, 190609936942907881906112282892718160671399829608969662595744137172517876816⟩ = true := by
  decide +kernel

theorem b_328_2000 : bothSeg evalE (oGrid.idx 328) (oGrid.dm 328) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 328) oGrid.kl oGrid.kr 400 2000 ⟨false, 2426185211457594951396700111507174215241965330115843586905070296353138984746⟩ ⟨false, 190609936942907881906112282892718160671399829608969662595744137172517876816⟩ ⟨false, 2422277149312656146703892476413547606862328916340086649516063440827278157500⟩ ⟨false, 201244675068118340111263955992457495105907094378160907877267101097873878084⟩ = true := by
  decide +kernel

theorem b_328_2400 : bothLoop evalE (oGrid.idx 328) (oGrid.dm 328) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 328) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2422277149312656146703892476413547606862328916340086649516063440827278157500⟩ ⟨false, 201244675068118340111263955992457495105907094378160907877267101097873878084⟩ = true := by
  decide +kernel

theorem o_row_328 : oGrid.row evalE 328 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_328_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_328_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_328_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_328_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_328_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_328_2000).1 (bothLoop_sound b_328_2400).1))))))

theorem n_row_328 : nGrid.row evalE 328 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_328_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_328_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_328_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_328_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_328_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_328_2000).2 (bothLoop_sound b_328_2400).2))))))

theorem b_329_0 : bothSeg evalE (oGrid.idx 329) (oGrid.dm 329) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 329) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1433349868890682453922904861780082926044732261354220147220342118084008229538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_329_400 : bothSeg evalE (oGrid.idx 329) (oGrid.dm 329) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 329) oGrid.kl oGrid.kr 400 400 ⟨false, 1433349868890682453922904861780082926044732261354220147220342118084008229538⟩ ⟨false, 0⟩ ⟨false, 2303484247065144165094087575085021998665154944270537104987766045263506697772⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_329_800 : bothSeg evalE (oGrid.idx 329) (oGrid.dm 329) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 329) oGrid.kl oGrid.kr 400 800 ⟨false, 2303484247065144165094087575085021998665154944270537104987766045263506697772⟩ ⟨false, 0⟩ ⟨false, 2586956095086348170211296042901097092703743232631835510150426178020660476138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_329_1200 : bothSeg evalE (oGrid.idx 329) (oGrid.dm 329) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 329) oGrid.kl oGrid.kr 400 1200 ⟨false, 2586956095086348170211296042901097092703743232631835510150426178020660476138⟩ ⟨false, 0⟩ ⟨false, 2571164603610977373692446018231060835999752031356091255953273203910792310214⟩ ⟨false, 32954583065039381213814286931524447581760088695208308219360225763495432588⟩ = true := by
  decide +kernel

theorem b_329_1600 : bothSeg evalE (oGrid.idx 329) (oGrid.dm 329) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 329) oGrid.kl oGrid.kr 400 1600 ⟨false, 2571164603610977373692446018231060835999752031356091255953273203910792310214⟩ ⟨false, 32954583065039381213814286931524447581760088695208308219360225763495432588⟩ ⟨false, 2413560749774234760707043070075006978891594865882579607539030809395321960356⟩ ⟨false, 190558436901781994199217235087578304689917254168719956633602620278965782446⟩ = true := by
  decide +kernel

theorem b_329_2000 : bothSeg evalE (oGrid.idx 329) (oGrid.dm 329) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 329) oGrid.kl oGrid.kr 400 2000 ⟨false, 2413560749774234760707043070075006978891594865882579607539030809395321960356⟩ ⟨false, 190558436901781994199217235087578304689917254168719956633602620278965782446⟩ ⟨false, 2409797993168898865763472755362461332134329958289051230273024458632253255230⟩ ⟨false, 201074372767280015513055978635106362446615699420395090292708991516729850536⟩ = true := by
  decide +kernel

theorem b_329_2400 : bothLoop evalE (oGrid.idx 329) (oGrid.dm 329) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 329) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2409797993168898865763472755362461332134329958289051230273024458632253255230⟩ ⟨false, 201074372767280015513055978635106362446615699420395090292708991516729850536⟩ = true := by
  decide +kernel

theorem o_row_329 : oGrid.row evalE 329 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_329_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_329_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_329_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_329_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_329_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_329_2000).1 (bothLoop_sound b_329_2400).1))))))

theorem n_row_329 : nGrid.row evalE 329 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_329_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_329_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_329_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_329_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_329_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_329_2000).2 (bothLoop_sound b_329_2400).2))))))

theorem b_330_0 : bothSeg evalE (oGrid.idx 330) (oGrid.dm 330) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 330) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1426854449632784949085251516348730398094692046336157686674905562820889788540⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_330_400 : bothSeg evalE (oGrid.idx 330) (oGrid.dm 330) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 330) oGrid.kl oGrid.kr 400 400 ⟨false, 1426854449632784949085251516348730398094692046336157686674905562820889788540⟩ ⟨false, 0⟩ ⟨false, 2292840163664230661020017245749619221087438829517599928863889519705821337050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_330_800 : bothSeg evalE (oGrid.idx 330) (oGrid.dm 330) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 330) oGrid.kl oGrid.kr 400 800 ⟨false, 2292840163664230661020017245749619221087438829517599928863889519705821337050⟩ ⟨false, 0⟩ ⟨false, 2574591387384568302400309162523002665967546814604273107070334129204115901970⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_330_1200 : bothSeg evalE (oGrid.idx 330) (oGrid.dm 330) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 330) oGrid.kl oGrid.kr 400 1200 ⟨false, 2574591387384568302400309162523002665967546814604273107070334129204115901970⟩ ⟨false, 0⟩ ⟨false, 2558413463461426557256573973286543073272013707826613452841567167053660798828⟩ ⟨false, 33072889664226307344462690085370450815405440100700575564500934468076562942⟩ = true := by
  decide +kernel

theorem b_330_1600 : bothSeg evalE (oGrid.idx 330) (oGrid.dm 330) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 330) oGrid.kl oGrid.kr 400 1600 ⟨false, 2558413463461426557256573973286543073272013707826613452841567167053660798828⟩ ⟨false, 33072889664226307344462690085370450815405440100700575564500934468076562942⟩ ⟨false, 2400979820307522920000613011083098275221392465770167383075460686108544554874⟩ ⟨false, 190506532818129944600423652288815248866026682157146645330607415413192806896⟩ = true := by
  decide +kernel

theorem b_330_2000 : bothSeg evalE (oGrid.idx 330) (oGrid.dm 330) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 330) oGrid.kl oGrid.kr 400 2000 ⟨false, 2400979820307522920000613011083098275221392465770167383075460686108544554874⟩ ⟨false, 190506532818129944600423652288815248866026682157146645330607415413192806896⟩ ⟨false, 2397359859565117918328436265903918267995885093480113670186509710762418479108⟩ ⟨false, 200905022073520625000277443208171273880701494196267389949608570977669316758⟩ = true := by
  decide +kernel

theorem b_330_2400 : bothLoop evalE (oGrid.idx 330) (oGrid.dm 330) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 330) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2397359859565117918328436265903918267995885093480113670186509710762418479108⟩ ⟨false, 200905022073520625000277443208171273880701494196267389949608570977669316758⟩ = true := by
  decide +kernel

theorem o_row_330 : oGrid.row evalE 330 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_330_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_330_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_330_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_330_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_330_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_330_2000).1 (bothLoop_sound b_330_2400).1))))))

theorem n_row_330 : nGrid.row evalE 330 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_330_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_330_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_330_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_330_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_330_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_330_2000).2 (bothLoop_sound b_330_2400).2))))))

theorem b_331_0 : bothSeg evalE (oGrid.idx 331) (oGrid.dm 331) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 331) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1420380552568083127838929342160957363219986675694866465463611787526656291452⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_331_400 : bothSeg evalE (oGrid.idx 331) (oGrid.dm 331) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 331) oGrid.kl oGrid.kr 400 400 ⟨false, 1420380552568083127838929342160957363219986675694866465463611787526656291452⟩ ⟨false, 0⟩ ⟨false, 2282230739805337383369309725833454447606358914196310282620060930498807736476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_331_800 : bothSeg evalE (oGrid.idx 331) (oGrid.dm 331) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 331) oGrid.kl oGrid.kr 400 800 ⟨false, 2282230739805337383369309725833454447606358914196310282620060930498807736476⟩ ⟨false, 0⟩ ⟨false, 2562266875251547764011688103389395484283468952522252798042427060982655199432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_331_1200 : bothSeg evalE (oGrid.idx 331) (oGrid.dm 331) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 331) oGrid.kl oGrid.kr 400 1200 ⟨false, 2562266875251547764011688103389395484283468952522252798042427060982655199432⟩ ⟨false, 0⟩ ⟨false, 2545696497992436247333714025593648472456431860858279100118714210037235419178⟩ ⟨false, 33198791502480579045512876316486965499791133193051126306822418230831418708⟩ = true := by
  decide +kernel

theorem b_331_1600 : bothSeg evalE (oGrid.idx 331) (oGrid.dm 331) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 331) oGrid.kl oGrid.kr 400 1600 ⟨false, 2545696497992436247333714025593648472456431860858279100118714210037235419178⟩ ⟨false, 33198791502480579045512876316486965499791133193051126306822418230831418708⟩ ⟨false, 2388441202621889542246566003776427393183713174306160585436727712044062340836⟩ ⟨false, 190454086873027284132660898133708044772509819745169640988808916224004497050⟩ = true := by
  decide +kernel

theorem b_331_2000 : bothSeg evalE (oGrid.idx 331) (oGrid.dm 331) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 331) oGrid.kl oGrid.kr 400 2000 ⟨false, 2388441202621889542246566003776427393183713174306160585436727712044062340836⟩ ⟨false, 190454086873027284132660898133708044772509819745169640988808916224004497050⟩ ⟨false, 2384961535064621045008031094302659362435063215137698794366484409621351514192⟩ ⟨false, 200735848734040330779687501133414476761842231968465407280347282841561300104⟩ = true := by
  decide +kernel

theorem b_331_2400 : bothLoop evalE (oGrid.idx 331) (oGrid.dm 331) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 331) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2384961535064621045008031094302659362435063215137698794366484409621351514192⟩ ⟨false, 200735848734040330779687501133414476761842231968465407280347282841561300104⟩ = true := by
  decide +kernel

theorem o_row_331 : oGrid.row evalE 331 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_331_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_331_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_331_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_331_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_331_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_331_2000).1 (bothLoop_sound b_331_2400).1))))))

theorem n_row_331 : nGrid.row evalE 331 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_331_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_331_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_331_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_331_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_331_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_331_2000).2 (bothLoop_sound b_331_2400).2))))))

theorem b_332_0 : bothSeg evalE (oGrid.idx 332) (oGrid.dm 332) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 332) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1413928138619375515807381852554798504582367415300462484452066415202536761754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_332_400 : bothSeg evalE (oGrid.idx 332) (oGrid.dm 332) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 332) oGrid.kl oGrid.kr 400 400 ⟨false, 1413928138619375515807381852554798504582367415300462484452066415202536761754⟩ ⟨false, 0⟩ ⟨false, 2271655918948749710245339937431313100065102696768618152298896985764892597468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_332_800 : bothSeg evalE (oGrid.idx 332) (oGrid.dm 332) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 332) oGrid.kl oGrid.kr 400 800 ⟨false, 2271655918948749710245339937431313100065102696768618152298896985764892597468⟩ ⟨false, 0⟩ ⟨false, 2549982486251624045698879846834464914900393845666794835627604482596418759854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_332_1200 : bothSeg evalE (oGrid.idx 332) (oGrid.dm 332) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 332) oGrid.kl oGrid.kr 400 1200 ⟨false, 2549982486251624045698879846834464914900393845666794835627604482596418759854⟩ ⟨false, 0⟩ ⟨false, 2533014410696805867670312358793630709086793587964507265513100463598897947910⟩ ⟨false, 33332214715726756069932538298848457482472969109834986801118897150536151770⟩ = true := by
  decide +kernel

theorem b_332_1600 : bothSeg evalE (oGrid.idx 332) (oGrid.dm 332) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 332) oGrid.kl oGrid.kr 400 1600 ⟨false, 2533014410696805867670312358793630709086793587964507265513100463598897947910⟩ ⟨false, 33332214715726756069932538298848457482472969109834986801118897150536151770⟩ ⟨false, 2375945594255878526311823308493394423760950959242704221586222075411712521192⟩ ⟨false, 190401031156654097428421588599084742808315597831638030727997285337721578488⟩ = true := by
  decide +kernel

theorem b_332_2000 : bothSeg evalE (oGrid.idx 332) (oGrid.dm 332) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 332) oGrid.kl oGrid.kr 400 2000 ⟨false, 2375945594255878526311823308493394423760950959242704221586222075411712521192⟩ ⟨false, 190401031156654097428421588599084742808315597831638030727997285337721578488⟩ ⟨false, 2372603684697323420051623374731160145995970213801243195132510453410326569666⟩ ⟨false, 200566627064276671682113898551705577707755316635034076142469857341537826426⟩ = true := by
  decide +kernel

theorem b_332_2400 : bothLoop evalE (oGrid.idx 332) (oGrid.dm 332) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 332) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2372603684697323420051623374731160145995970213801243195132510453410326569666⟩ ⟨false, 200566627064276671682113898551705577707755316635034076142469857341537826426⟩ = true := by
  decide +kernel

theorem o_row_332 : oGrid.row evalE 332 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_332_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_332_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_332_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_332_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_332_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_332_2000).1 (bothLoop_sound b_332_2400).1))))))

theorem n_row_332 : nGrid.row evalE 332 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_332_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_332_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_332_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_332_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_332_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_332_2000).2 (bothLoop_sound b_332_2400).2))))))

theorem b_333_0 : bothSeg evalE (oGrid.idx 333) (oGrid.dm 333) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 333) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1407497142095427604077028282964281017525657623401029136023265014716739212964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_333_400 : bothSeg evalE (oGrid.idx 333) (oGrid.dm 333) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 333) oGrid.kl oGrid.kr 400 400 ⟨false, 1407497142095427604077028282964281017525657623401029136023265014716739212964⟩ ⟨false, 0⟩ ⟨false, 2261115604773148342354617261864254186923027680926765597327958120480331697550⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_333_800 : bothSeg evalE (oGrid.idx 333) (oGrid.dm 333) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 333) oGrid.kl oGrid.kr 400 800 ⟨false, 2261115604773148342354617261864254186923027680926765597327958120480331697550⟩ ⟨false, 0⟩ ⟨false, 2537738081899534450478075842962996931332078435881729720062526288303782805850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_333_1200 : bothSeg evalE (oGrid.idx 333) (oGrid.dm 333) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 333) oGrid.kl oGrid.kr 400 1200 ⟨false, 2537738081899534450478075842962996931332078435881729720062526288303782805850⟩ ⟨false, 0⟩ ⟨false, 2520367047158068647462103023521892529310455925620554370044549219644697643860⟩ ⟨false, 33473499371112025659898568622012173771303041662093551372217870557732608630⟩ = true := by
  decide +kernel

theorem b_333_1600 : bothSeg evalE (oGrid.idx 333) (oGrid.dm 333) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 333) oGrid.kl oGrid.kr 400 1600 ⟨false, 2520367047158068647462103023521892529310455925620554370044549219644697643860⟩ ⟨false, 33473499371112025659898568622012173771303041662093551372217870557732608630⟩ ⟨false, 2363493008979029179056733419984262346494117602414002376128826180771422456840⟩ ⟨false, 190347537550151494065268172159642356587641364868645545287940909431007795650⟩ = true := by
  decide +kernel

theorem b_333_2000 : bothSeg evalE (oGrid.idx 333) (oGrid.dm 333) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 333) oGrid.kl oGrid.kr 400 2000 ⟨false, 2363493008979029179056733419984262346494117602414002376128826180771422456840⟩ ⟨false, 190347537550151494065268172159642356587641364868645545287940909431007795650⟩ ⟨false, 2360286304628615204380075566356386550794914089313369229683532365163707153726⟩ ⟨false, 200397895208523711959702922167492231679594066409548655108637970908676604526⟩ = true := by
  decide +kernel

theorem b_333_2400 : bothLoop evalE (oGrid.idx 333) (oGrid.dm 333) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 333) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2360286304628615204380075566356386550794914089313369229683532365163707153726⟩ ⟨false, 200397895208523711959702922167492231679594066409548655108637970908676604526⟩ = true := by
  decide +kernel

theorem o_row_333 : oGrid.row evalE 333 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_333_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_333_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_333_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_333_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_333_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_333_2000).1 (bothLoop_sound b_333_2400).1))))))

theorem n_row_333 : nGrid.row evalE 333 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_333_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_333_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_333_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_333_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_333_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_333_2000).2 (bothLoop_sound b_333_2400).2))))))

theorem b_334_0 : bothSeg evalE (oGrid.idx 334) (oGrid.dm 334) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 334) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1401087521880550854825632857806844793883172825874641609622876227803636344992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_334_400 : bothSeg evalE (oGrid.idx 334) (oGrid.dm 334) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 334) oGrid.kl oGrid.kr 400 400 ⟨false, 1401087521880550854825632857806844793883172825874641609622876227803636344992⟩ ⟨false, 0⟩ ⟨false, 2250609734071148165600809592257075015905715387703772101288117585082127523242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_334_800 : bothSeg evalE (oGrid.idx 334) (oGrid.dm 334) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 334) oGrid.kl oGrid.kr 400 800 ⟨false, 2250609734071148165600809592257075015905715387703772101288117585082127523242⟩ ⟨false, 0⟩ ⟨false, 2525533605064189545500180442060726455183726751412277116947290038840083160578⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_334_1200 : bothSeg evalE (oGrid.idx 334) (oGrid.dm 334) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 334) oGrid.kl oGrid.kr 400 1200 ⟨false, 2525533605064189545500180442060726455183726751412277116947290038840083160578⟩ ⟨false, 0⟩ ⟨false, 2507754265371505388963130380203640514200645539042348986207613381943369643250⟩ ⟨false, 33622363795430470632620008155708306665824110508273185679054672595990487258⟩ = true := by
  decide +kernel

theorem b_334_1600 : bothSeg evalE (oGrid.idx 334) (oGrid.dm 334) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 334) oGrid.kl oGrid.kr 400 1600 ⟨false, 2507754265371505388963130380203640514200645539042348986207613381943369643250⟩ ⟨false, 33622363795430470632620008155708306665824110508273185679054672595990487258⟩ ⟨false, 2351083256014015224274125974688356390095147858869224627811532528403003206112⟩ ⟨false, 190293373152920635321624413670992430771321790681397544075135526136356924396⟩ = true := by
  decide +kernel

theorem b_334_2000 : bothSeg evalE (oGrid.idx 334) (oGrid.dm 334) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 334) oGrid.kl oGrid.kr 400 2000 ⟨false, 2351083256014015224274125974688356390095147858869224627811532528403003206112⟩ ⟨false, 190293373152920635321624413670992430771321790681397544075135526136356924396⟩ ⟨false, 2348009209871401560610971826554464427363055076757415006274327348944950285314⟩ ⟨false, 200229228373408569806775870595986014754438281907810267232701238477158406236⟩ = true := by
  decide +kernel

theorem b_334_2400 : bothLoop evalE (oGrid.idx 334) (oGrid.dm 334) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 334) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2348009209871401560610971826554464427363055076757415006274327348944950285314⟩ ⟨false, 200229228373408569806775870595986014754438281907810267232701238477158406236⟩ = true := by
  decide +kernel

theorem o_row_334 : oGrid.row evalE 334 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_334_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_334_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_334_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_334_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_334_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_334_2000).1 (bothLoop_sound b_334_2400).1))))))

theorem n_row_334 : nGrid.row evalE 334 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_334_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_334_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_334_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_334_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_334_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_334_2000).2 (bothLoop_sound b_334_2400).2))))))

theorem b_335_0 : bothSeg evalE (oGrid.idx 335) (oGrid.dm 335) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 335) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1394699202037574001692077057872434230896082326447626131597925107523590825212⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_335_400 : bothSeg evalE (oGrid.idx 335) (oGrid.dm 335) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 335) oGrid.kl oGrid.kr 400 400 ⟨false, 1394699202037574001692077057872434230896082326447626131597925107523590825212⟩ ⟨false, 0⟩ ⟨false, 2240138199576373914136526391757380653116894696246374185244313778322684943940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_335_800 : bothSeg evalE (oGrid.idx 335) (oGrid.dm 335) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 335) oGrid.kl oGrid.kr 400 800 ⟨false, 2240138199576373914136526391757380653116894696246374185244313778322684943940⟩ ⟨false, 0⟩ ⟨false, 2513368982154621976956023235737040758931906256346190993437509708957694707352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_335_1200 : bothSeg evalE (oGrid.idx 335) (oGrid.dm 335) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 335) oGrid.kl oGrid.kr 400 1200 ⟨false, 2513368982154621976956023235737040758931906256346190993437509708957694707352⟩ ⟨false, 0⟩ ⟨false, 2495175969196435428599180345365490990105049389172496486949939209665336903382⟩ ⟨false, 33778813748220515117322074146371743418670197575463265763992026373163818052⟩ = true := by
  decide +kernel

theorem b_335_1600 : bothSeg evalE (oGrid.idx 335) (oGrid.dm 335) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 335) oGrid.kl oGrid.kr 400 1600 ⟨false, 2495175969196435428599180345365490990105049389172496486949939209665336903382⟩ ⟨false, 33778813748220515117322074146371743418670197575463265763992026373163818052⟩ ⟨false, 2338716337207093716496592655636922101095170183987730378669464308689181105394⟩ ⟨false, 190238445737562227219909763874940632428549402760229374044466927349319616040⟩ = true := by
  decide +kernel

theorem b_335_2000 : bothSeg evalE (oGrid.idx 335) (oGrid.dm 335) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 335) oGrid.kl oGrid.kr 400 2000 ⟨false, 2338716337207093716496592655636922101095170183987730378669464308689181105394⟩ ⟨false, 190238445737562227219909763874940632428549402760229374044466927349319616040⟩ ⟨false, 2335772408933194961284119792823093834554950793608817778708027928634341310172⟩ ⟨false, 200060729723766509195189391533055811823225874377409478864290873787532187084⟩ = true := by
  decide +kernel

theorem b_335_2400 : bothLoop evalE (oGrid.idx 335) (oGrid.dm 335) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 335) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2335772408933194961284119792823093834554950793608817778708027928634341310172⟩ ⟨false, 200060729723766509195189391533055811823225874377409478864290873787532187084⟩ = true := by
  decide +kernel

theorem o_row_335 : oGrid.row evalE 335 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_335_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_335_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_335_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_335_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_335_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_335_2000).1 (bothLoop_sound b_335_2400).1))))))

theorem n_row_335 : nGrid.row evalE 335 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_335_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_335_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_335_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_335_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_335_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_335_2000).2 (bothLoop_sound b_335_2400).2))))))

theorem o_blk_312 : allFrom (fun j => oGrid.row evalE j) 312 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 312) o_row_312 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 313) o_row_313 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 314) o_row_314 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 315) o_row_315 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 316) o_row_316 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 317) o_row_317 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 318) o_row_318 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 319) o_row_319 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 320) o_row_320 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 321) o_row_321 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 322) o_row_322 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 323) o_row_323 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 324) o_row_324 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 325) o_row_325 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 326) o_row_326 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 327) o_row_327 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 328) o_row_328 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 329) o_row_329 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 330) o_row_330 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 331) o_row_331 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 332) o_row_332 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 333) o_row_333 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 334) o_row_334 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 335) o_row_335 (allFrom_zero (fun j => oGrid.row evalE j) 336)))))))))))))))))))))))))

theorem n_blk_312 : allFrom (fun j => nGrid.row evalE j) 312 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 312) n_row_312 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 313) n_row_313 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 314) n_row_314 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 315) n_row_315 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 316) n_row_316 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 317) n_row_317 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 318) n_row_318 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 319) n_row_319 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 320) n_row_320 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 321) n_row_321 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 322) n_row_322 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 323) n_row_323 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 324) n_row_324 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 325) n_row_325 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 326) n_row_326 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 327) n_row_327 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 328) n_row_328 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 329) n_row_329 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 330) n_row_330 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 331) n_row_331 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 332) n_row_332 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 333) n_row_333 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 334) n_row_334 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 335) n_row_335 (allFrom_zero (fun j => nGrid.row evalE j) 336)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
