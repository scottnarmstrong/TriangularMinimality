/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 11 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `264`–`287`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_264_0 : bothSeg evalE (oGrid.idx 264) (oGrid.dm 264) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 264) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1904554674390319797977926505346351498723062794202927104152314730614532268310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_264_400 : bothSeg evalE (oGrid.idx 264) (oGrid.dm 264) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 264) oGrid.kl oGrid.kr 400 400 ⟨false, 1904554674390319797977926505346351498723062794202927104152314730614532268310⟩ ⟨false, 0⟩ ⟨false, 3073858020718047875042085570332616488267957674591368912365829233406219744350⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_264_800 : bothSeg evalE (oGrid.idx 264) (oGrid.dm 264) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 264) oGrid.kl oGrid.kr 400 800 ⟨false, 3073858020718047875042085570332616488267957674591368912365829233406219744350⟩ ⟨false, 0⟩ ⟨false, 3481321930795788126471539368070480816443469344147065703494957439189830745088⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_264_1200 : bothSeg evalE (oGrid.idx 264) (oGrid.dm 264) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 264) oGrid.kl oGrid.kr 400 1200 ⟨false, 3481321930795788126471539368070480816443469344147065703494957439189830745088⟩ ⟨false, 0⟩ ⟨false, 3486183387159001663948975920985446863468758025318427309145104202495277044328⟩ ⟨false, 34495249379166229238298642677415177344487288938304369927652677026652822634⟩ = true := by
  decide +kernel

theorem b_264_1600 : bothSeg evalE (oGrid.idx 264) (oGrid.dm 264) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 264) oGrid.kl oGrid.kr 400 1600 ⟨false, 3486183387159001663948975920985446863468758025318427309145104202495277044328⟩ ⟨false, 34495249379166229238298642677415177344487288938304369927652677026652822634⟩ ⟨false, 3328490861217649892786027185581081459958830485811311072476254838295288098618⟩ ⟨false, 192586692419138868135322556117916787196439515148565520745327726627449411950⟩ = true := by
  decide +kernel

theorem b_264_2000 : bothSeg evalE (oGrid.idx 264) (oGrid.dm 264) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 264) oGrid.kl oGrid.kr 400 2000 ⟨false, 3328490861217649892786027185581081459958830485811311072476254838295288098618⟩ ⟨false, 192586692419138868135322556117916787196439515148565520745327726627449411950⟩ ⟨false, 3311300532505284003117608983758349352505054426403270865842437503109791678786⟩ ⟨false, 212625947279565612715460143471570115695790892520869342726524343831772214800⟩ = true := by
  decide +kernel

theorem b_264_2400 : bothLoop evalE (oGrid.idx 264) (oGrid.dm 264) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 264) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3311300532505284003117608983758349352505054426403270865842437503109791678786⟩ ⟨false, 212625947279565612715460143471570115695790892520869342726524343831772214800⟩ = true := by
  decide +kernel

theorem o_row_264 : oGrid.row evalE 264 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_264_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_264_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_264_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_264_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_264_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_264_2000).1 (bothLoop_sound b_264_2400).1))))))

theorem n_row_264 : nGrid.row evalE 264 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_264_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_264_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_264_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_264_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_264_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_264_2000).2 (bothLoop_sound b_264_2400).2))))))

theorem b_265_0 : bothSeg evalE (oGrid.idx 265) (oGrid.dm 265) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 265) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1896531846004008232125306867006804783716240150216022948507684735096542290170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_265_400 : bothSeg evalE (oGrid.idx 265) (oGrid.dm 265) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 265) oGrid.kl oGrid.kr 400 400 ⟨false, 1896531846004008232125306867006804783716240150216022948507684735096542290170⟩ ⟨false, 0⟩ ⟨false, 3060773096006838539325241077911831200036637841105780010217161692394794451372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_265_800 : bothSeg evalE (oGrid.idx 265) (oGrid.dm 265) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 265) oGrid.kl oGrid.kr 400 800 ⟨false, 3060773096006838539325241077911831200036637841105780010217161692394794451372⟩ ⟨false, 0⟩ ⟨false, 3466143590335735872678451986641148916908459333115186421009148085648863349268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_265_1200 : bothSeg evalE (oGrid.idx 265) (oGrid.dm 265) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 265) oGrid.kl oGrid.kr 400 1200 ⟨false, 3466143590335735872678451986641148916908459333115186421009148085648863349268⟩ ⟨false, 0⟩ ⟨false, 3470624811613667367539721656227134538591448495681383774100294583940646233560⟩ ⟨false, 34448747673349857118027459118845948654603199119698412141341504645556630030⟩ = true := by
  decide +kernel

theorem b_265_1600 : bothSeg evalE (oGrid.idx 265) (oGrid.dm 265) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 265) oGrid.kl oGrid.kr 400 1600 ⟨false, 3470624811613667367539721656227134538591448495681383774100294583940646233560⟩ ⟨false, 34448747673349857118027459118845948654603199119698412141341504645556630030⟩ ⟨false, 3312896163398156336452032522932545539695433414784152110365268224975928842128⟩ ⟨false, 192577469750933223080250651433857376191991998531492169216633197080023557542⟩ = true := by
  decide +kernel

theorem b_265_2000 : bothSeg evalE (oGrid.idx 265) (oGrid.dm 265) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 265) oGrid.kl oGrid.kr 400 2000 ⟨false, 3312896163398156336452032522932545539695433414784152110365268224975928842128⟩ ⟨false, 192577469750933223080250651433857376191991998531492169216633197080023557542⟩ ⟨false, 3295949522557150482500857429817571304795408254963330377678451512386076370320⟩ ⟨false, 212440230097724872366547339987667065131227111691029190195396151434476724672⟩ = true := by
  decide +kernel

theorem b_265_2400 : bothLoop evalE (oGrid.idx 265) (oGrid.dm 265) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 265) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3295949522557150482500857429817571304795408254963330377678451512386076370320⟩ ⟨false, 212440230097724872366547339987667065131227111691029190195396151434476724672⟩ = true := by
  decide +kernel

theorem o_row_265 : oGrid.row evalE 265 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_265_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_265_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_265_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_265_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_265_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_265_2000).1 (bothLoop_sound b_265_2400).1))))))

theorem n_row_265 : nGrid.row evalE 265 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_265_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_265_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_265_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_265_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_265_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_265_2000).2 (bothLoop_sound b_265_2400).2))))))

theorem b_266_0 : bothSeg evalE (oGrid.idx 266) (oGrid.dm 266) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 266) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1888534525991718559207340942235542335960117997952840414557410380280575699742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_266_400 : bothSeg evalE (oGrid.idx 266) (oGrid.dm 266) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 266) oGrid.kl oGrid.kr 400 400 ⟨false, 1888534525991718559207340942235542335960117997952840414557410380280575699742⟩ ⟨false, 0⟩ ⟨false, 3047728619245193622717021510428863422503040307127126247002657969257014771350⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_266_800 : bothSeg evalE (oGrid.idx 266) (oGrid.dm 266) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 266) oGrid.kl oGrid.kr 400 800 ⟨false, 3047728619245193622717021510428863422503040307127126247002657969257014771350⟩ ⟨false, 0⟩ ⟨false, 3451011663336892505456384967075106092241637632928667117244286941435554156964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_266_1200 : bothSeg evalE (oGrid.idx 266) (oGrid.dm 266) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 266) oGrid.kl oGrid.kr 400 1200 ⟨false, 3451011663336892505456384967075106092241637632928667117244286941435554156964⟩ ⟨false, 0⟩ ⟨false, 3455118758043436099654198602514790092143605657857563052966638085439739178294⟩ ⟨false, 34398603360812123948424222735819352852935372624353792454335344681941230260⟩ = true := by
  decide +kernel

theorem b_266_1600 : bothSeg evalE (oGrid.idx 266) (oGrid.dm 266) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 266) oGrid.kl oGrid.kr 400 1600 ⟨false, 3455118758043436099654198602514790092143605657857563052966638085439739178294⟩ ⟨false, 34398603360812123948424222735819352852935372624353792454335344681941230260⟩ ⟨false, 3297351112237140665667746075383145059584777858486926797209612342338274509430⟩ ⟨false, 192567474537889926217808109447345813684992176713101322198833122779089639408⟩ = true := by
  decide +kernel

theorem b_266_2000 : bothSeg evalE (oGrid.idx 266) (oGrid.dm 266) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 266) oGrid.kl oGrid.kr 400 2000 ⟨false, 3297351112237140665667746075383145059584777858486926797209612342338274509430⟩ ⟨false, 192567474537889926217808109447345813684992176713101322198833122779089639408⟩ ⟨false, 3280647781925278510667674617074938417296844398814261682970429452738335718136⟩ ⟨false, 212254719687879453757202145281448988772701811055477106249987515257356823036⟩ = true := by
  decide +kernel

theorem b_266_2400 : bothLoop evalE (oGrid.idx 266) (oGrid.dm 266) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 266) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3280647781925278510667674617074938417296844398814261682970429452738335718136⟩ ⟨false, 212254719687879453757202145281448988772701811055477106249987515257356823036⟩ = true := by
  decide +kernel

theorem o_row_266 : oGrid.row evalE 266 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_266_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_266_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_266_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_266_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_266_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_266_2000).1 (bothLoop_sound b_266_2400).1))))))

theorem n_row_266 : nGrid.row evalE 266 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_266_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_266_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_266_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_266_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_266_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_266_2000).2 (bothLoop_sound b_266_2400).2))))))

theorem b_267_0 : bothSeg evalE (oGrid.idx 267) (oGrid.dm 267) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 267) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1880562654562448364300660130588169246383670736216739077838320260390781627024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_267_400 : bothSeg evalE (oGrid.idx 267) (oGrid.dm 267) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 267) oGrid.kl oGrid.kr 400 400 ⟨false, 1880562654562448364300660130588169246383670736216739077838320260390781627024⟩ ⟨false, 0⟩ ⟨false, 3034724547739799429462606828913820697543481039591862231154265642285621351030⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_267_800 : bothSeg evalE (oGrid.idx 267) (oGrid.dm 267) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 267) oGrid.kl oGrid.kr 400 800 ⟨false, 3034724547739799429462606828913820697543481039591862231154265642285621351030⟩ ⟨false, 0⟩ ⟨false, 3435926074316847149623612108776858435772515229726238252382350124638832637582⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_267_1200 : bothSeg evalE (oGrid.idx 267) (oGrid.dm 267) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 267) oGrid.kl oGrid.kr 400 1200 ⟨false, 3435926074316847149623612108776858435772515229726238252382350124638832637582⟩ ⟨false, 0⟩ ⟨false, 3439664995989225577254976586233150709688085114607249001944781318814298772256⟩ ⟨false, 34344978337114078630323049666624954223677496740534593317875657663003161708⟩ = true := by
  decide +kernel

theorem b_267_1600 : bothSeg evalE (oGrid.idx 267) (oGrid.dm 267) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 267) oGrid.kl oGrid.kr 400 1600 ⟨false, 3439664995989225577254976586233150709688085114607249001944781318814298772256⟩ ⟨false, 34344978337114078630323049666624954223677496740534593317875657663003161708⟩ ⟨false, 3281855592779428158451074336470723805727144716518693847865756074726968826480⟩ ⟨false, 192556804314722322348991613177888162484013999141923836768737872118005459916⟩ = true := by
  decide +kernel

theorem b_267_2000 : bothSeg evalE (oGrid.idx 267) (oGrid.dm 267) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 267) oGrid.kl oGrid.kr 400 2000 ⟨false, 3281855592779428158451074336470723805727144716518693847865756074726968826480⟩ ⟨false, 192556804314722322348991613177888162484013999141923836768737872118005459916⟩ ⟨false, 3265395179337757935083667325109208542455516667473777251361495717029160038608⟩ ⟨false, 212069561522788408850313335777028329821799724974511557600101598492081231924⟩ = true := by
  decide +kernel

theorem b_267_2400 : bothLoop evalE (oGrid.idx 267) (oGrid.dm 267) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 267) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3265395179337757935083667325109208542455516667473777251361495717029160038608⟩ ⟨false, 212069561522788408850313335777028329821799724974511557600101598492081231924⟩ = true := by
  decide +kernel

theorem o_row_267 : oGrid.row evalE 267 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_267_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_267_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_267_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_267_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_267_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_267_2000).1 (bothLoop_sound b_267_2400).1))))))

theorem n_row_267 : nGrid.row evalE 267 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_267_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_267_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_267_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_267_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_267_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_267_2000).2 (bothLoop_sound b_267_2400).2))))))

theorem b_268_0 : bothSeg evalE (oGrid.idx 268) (oGrid.dm 268) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 268) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1872616181711765045441167110881976601782575439577661317653521634162299761652⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_268_400 : bothSeg evalE (oGrid.idx 268) (oGrid.dm 268) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 268) oGrid.kl oGrid.kr 400 400 ⟨false, 1872616181711765045441167110881976601782575439577661317653521634162299761652⟩ ⟨false, 0⟩ ⟨false, 3021760753641483278119517155268478545800369035157189512063709803948049440490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_268_800 : bothSeg evalE (oGrid.idx 268) (oGrid.dm 268) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 268) oGrid.kl oGrid.kr 400 800 ⟨false, 3021760753641483278119517155268478545800369035157189512063709803948049440490⟩ ⟨false, 0⟩ ⟨false, 3420886664665665885406521208912983584548028000795221275924068471575262727546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_268_1200 : bothSeg evalE (oGrid.idx 268) (oGrid.dm 268) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 268) oGrid.kl oGrid.kr 400 1200 ⟨false, 3420886664665665885406521208912983584548028000795221275924068471575262727546⟩ ⟨false, 0⟩ ⟨false, 3424263334214910023726807101318665425927957474453890152236748788400621605388⟩ ⟨false, 34287879757275129100304913312522918618793585973062548628280533144928927886⟩ = true := by
  decide +kernel

theorem b_268_1600 : bothSeg evalE (oGrid.idx 268) (oGrid.dm 268) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 268) oGrid.kl oGrid.kr 400 1600 ⟨false, 3424263334214910023726807101318665425927957474453890152236748788400621605388⟩ ⟨false, 34287879757275129100304913312522918618793585973062548628280533144928927886⟩ ⟨false, 3266409531676667761418624690762911851209866305972532734467471827567671568500⟩ ⟨false, 192545244184049939849434376622171562660754655663060886183708285972173093920⟩ = true := by
  decide +kernel

theorem b_268_2000 : bothSeg evalE (oGrid.idx 268) (oGrid.dm 268) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 268) oGrid.kl oGrid.kr 400 2000 ⟨false, 3266409531676667761418624690762911851209866305972532734467471827567671568500⟩ ⟨false, 192545244184049939849434376622171562660754655663060886183708285972173093920⟩ ⟨false, 3250191610339656508902276438394941154491564480618546121809705011798128847622⟩ ⟨false, 211884733162931234305778952408810724947028176801486091364641941604298859052⟩ = true := by
  decide +kernel

theorem b_268_2400 : bothLoop evalE (oGrid.idx 268) (oGrid.dm 268) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 268) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3250191610339656508902276438394941154491564480618546121809705011798128847622⟩ ⟨false, 211884733162931234305778952408810724947028176801486091364641941604298859052⟩ = true := by
  decide +kernel

theorem o_row_268 : oGrid.row evalE 268 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_268_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_268_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_268_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_268_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_268_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_268_2000).1 (bothLoop_sound b_268_2400).1))))))

theorem n_row_268 : nGrid.row evalE 268 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_268_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_268_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_268_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_268_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_268_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_268_2000).2 (bothLoop_sound b_268_2400).2))))))

theorem b_269_0 : bothSeg evalE (oGrid.idx 269) (oGrid.dm 269) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 269) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1864695027336802625335586836295940196974193130113905361283482860084327990498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_269_400 : bothSeg evalE (oGrid.idx 269) (oGrid.dm 269) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 269) oGrid.kl oGrid.kr 400 400 ⟨false, 1864695027336802625335586836295940196974193130113905361283482860084327990498⟩ ⟨false, 0⟩ ⟨false, 3008837144334857275855439778483657453862038777565811284699368356209953219666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_269_800 : bothSeg evalE (oGrid.idx 269) (oGrid.dm 269) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 269) oGrid.kl oGrid.kr 400 800 ⟨false, 3008837144334857275855439778483657453862038777565811284699368356209953219666⟩ ⟨false, 0⟩ ⟨false, 3405893365655402647326084851213694922512080168356834930967809640840586224784⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_269_1200 : bothSeg evalE (oGrid.idx 269) (oGrid.dm 269) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 269) oGrid.kl oGrid.kr 400 1200 ⟨false, 3405893365655402647326084851213694922512080168356834930967809640840586224784⟩ ⟨false, 0⟩ ⟨false, 3408913383630844903447751611839237110706853028660229335537687962483294398216⟩ ⟨false, 34227630935716134356225303734363828874768258665552225266883282946624572296⟩ = true := by
  decide +kernel

theorem b_269_1600 : bothSeg evalE (oGrid.idx 269) (oGrid.dm 269) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 269) oGrid.kl oGrid.kr 400 1600 ⟨false, 3408913383630844903447751611839237110706853028660229335537687962483294398216⟩ ⟨false, 34227630935716134356225303734363828874768258665552225266883282946624572296⟩ ⟨false, 3251012831121175070880129550367615330661880110517161442643361843519958668124⟩ ⟨false, 192532905889390428264785659763293717123097687104592108200903143218209294558⟩ = true := by
  decide +kernel

theorem b_269_2000 : bothSeg evalE (oGrid.idx 269) (oGrid.dm 269) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 269) oGrid.kl oGrid.kr 400 2000 ⟨false, 3251012831121175070880129550367615330661880110517161442643361843519958668124⟩ ⟨false, 192532905889390428264785659763293717123097687104592108200903143218209294558⟩ ⟨false, 3235036941431704538064240542335004351189390404921443153738899484393601909516⟩ ⟨false, 211699863743543707648288714728938668841334751192491826260262672204624173516⟩ = true := by
  decide +kernel

theorem b_269_2400 : bothLoop evalE (oGrid.idx 269) (oGrid.dm 269) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 269) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3235036941431704538064240542335004351189390404921443153738899484393601909516⟩ ⟨false, 211699863743543707648288714728938668841334751192491826260262672204624173516⟩ = true := by
  decide +kernel

theorem o_row_269 : oGrid.row evalE 269 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_269_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_269_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_269_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_269_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_269_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_269_2000).1 (bothLoop_sound b_269_2400).1))))))

theorem n_row_269 : nGrid.row evalE 269 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_269_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_269_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_269_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_269_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_269_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_269_2000).2 (bothLoop_sound b_269_2400).2))))))

theorem b_270_0 : bothSeg evalE (oGrid.idx 270) (oGrid.dm 270) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 270) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1856799109561341424630385567478582571102089341532326609693918241436912775444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_270_400 : bothSeg evalE (oGrid.idx 270) (oGrid.dm 270) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 270) oGrid.kl oGrid.kr 400 400 ⟨false, 1856799109561341424630385567478582571102089341532326609693918241436912775444⟩ ⟨false, 0⟩ ⟨false, 2995953608853119627101422697596627001811174562906036483749845193109975203806⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_270_800 : bothSeg evalE (oGrid.idx 270) (oGrid.dm 270) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 270) oGrid.kl oGrid.kr 400 800 ⟨false, 2995953608853119627101422697596627001811174562906036483749845193109975203806⟩ ⟨false, 0⟩ ⟨false, 3390946084745020140955229204322204485432240267748699430729259523594029931456⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_270_1200 : bothSeg evalE (oGrid.idx 270) (oGrid.dm 270) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 270) oGrid.kl oGrid.kr 400 1200 ⟨false, 3390946084745020140955229204322204485432240267748699430729259523594029931456⟩ ⟨false, 0⟩ ⟨false, 3393614896048621481386865529352320837476578891173170973806562732927170189962⟩ ⟨false, 34166343638127158497020219403907411036185547966691736902972069132722111070⟩ = true := by
  decide +kernel

theorem b_270_1600 : bothSeg evalE (oGrid.idx 270) (oGrid.dm 270) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 270) oGrid.kl oGrid.kr 400 1600 ⟨false, 3393614896048621481386865529352320837476578891173170973806562732927170189962⟩ ⟨false, 34166343638127158497020219403907411036185547966691736902972069132722111070⟩ ⟨false, 3235665348115319984393259992609092308959674424194054450739748006044276217918⟩ ⟨false, 192519809637289555855147179652340658282863989852439618499918018495589468408⟩ = true := by
  decide +kernel

theorem b_270_2000 : bothSeg evalE (oGrid.idx 270) (oGrid.dm 270) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 270) oGrid.kl oGrid.kr 400 2000 ⟨false, 3235665348115319984393259992609092308959674424194054450739748006044276217918⟩ ⟨false, 192519809637289555855147179652340658282863989852439618499918018495589468408⟩ ⟨false, 3219930983835803873475488176548159692544391304747428816641335615081723692728⟩ ⟨false, 211514906117606635859799378388729758537187923873831590418020538312572499246⟩ = true := by
  decide +kernel

theorem b_270_2400 : bothLoop evalE (oGrid.idx 270) (oGrid.dm 270) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 270) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3219930983835803873475488176548159692544391304747428816641335615081723692728⟩ ⟨false, 211514906117606635859799378388729758537187923873831590418020538312572499246⟩ = true := by
  decide +kernel

theorem o_row_270 : oGrid.row evalE 270 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_270_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_270_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_270_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_270_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_270_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_270_2000).1 (bothLoop_sound b_270_2400).1))))))

theorem n_row_270 : nGrid.row evalE 270 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_270_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_270_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_270_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_270_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_270_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_270_2000).2 (bothLoop_sound b_270_2400).2))))))

theorem b_271_0 : bothSeg evalE (oGrid.idx 271) (oGrid.dm 271) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 271) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1848928372709508399589410537743926505740336458958453914909839344872558648524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_271_400 : bothSeg evalE (oGrid.idx 271) (oGrid.dm 271) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 271) oGrid.kl oGrid.kr 400 400 ⟨false, 1848928372709508399589410537743926505740336458958453914909839344872558648524⟩ ⟨false, 0⟩ ⟨false, 2983110059205264209904475828457490473043225692479511089716184002266615538996⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_271_800 : bothSeg evalE (oGrid.idx 271) (oGrid.dm 271) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 271) oGrid.kl oGrid.kr 400 800 ⟨false, 2983110059205264209904475828457490473043225692479511089716184002266615538996⟩ ⟨false, 0⟩ ⟨false, 3376044658887684022160024928413197304445618359285513194961593584827070626998⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_271_1200 : bothSeg evalE (oGrid.idx 271) (oGrid.dm 271) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 271) oGrid.kl oGrid.kr 400 1200 ⟨false, 3376044658887684022160024928413197304445618359285513194961593584827070626998⟩ ⟨false, 0⟩ ⟨false, 3378367418302486248048281997689113421963657399451786281592083002638338167562⟩ ⟨false, 34105152970396378808320265984425296987769231243097427170707597899304873892⟩ = true := by
  decide +kernel

theorem b_271_1600 : bothSeg evalE (oGrid.idx 271) (oGrid.dm 271) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 271) oGrid.kl oGrid.kr 400 1600 ⟨false, 3378367418302486248048281997689113421963657399451786281592083002638338167562⟩ ⟨false, 34105152970396378808320265984425296987769231243097427170707597899304873892⟩ ⟨false, 3220366823602698658433094286887308422228691127111164891842174030847962023946⟩ ⟨false, 192506096817110027956829226075837838659813330991945003907389966003513946310⟩ = true := by
  decide +kernel

theorem b_271_2000 : bothSeg evalE (oGrid.idx 271) (oGrid.dm 271) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 271) oGrid.kl oGrid.kr 400 2000 ⟨false, 3220366823602698658433094286887308422228691127111164891842174030847962023946⟩ ⟨false, 192506096817110027956829226075837838659813330991945003907389966003513946310⟩ ⟨false, 3204873457217844191410808130029269583081383480500825481680413587474103798778⟩ ⟨false, 211331083905144019874485709423351881270186501497028189312244213113213528988⟩ = true := by
  decide +kernel

theorem b_271_2400 : bothLoop evalE (oGrid.idx 271) (oGrid.dm 271) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 271) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3204873457217844191410808130029269583081383480500825481680413587474103798778⟩ ⟨false, 211331083905144019874485709423351881270186501497028189312244213113213528988⟩ = true := by
  decide +kernel

theorem o_row_271 : oGrid.row evalE 271 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_271_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_271_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_271_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_271_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_271_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_271_2000).1 (bothLoop_sound b_271_2400).1))))))

theorem n_row_271 : nGrid.row evalE 271 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_271_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_271_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_271_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_271_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_271_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_271_2000).2 (bothLoop_sound b_271_2400).2))))))

theorem b_272_0 : bothSeg evalE (oGrid.idx 272) (oGrid.dm 272) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 272) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1841082749488335691392738465272571337012949540637456612470931467029661573008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_272_400 : bothSeg evalE (oGrid.idx 272) (oGrid.dm 272) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 272) oGrid.kl oGrid.kr 400 400 ⟨false, 1841082749488335691392738465272571337012949540637456612470931467029661573008⟩ ⟨false, 0⟩ ⟨false, 2970306420800311838410309202483259470818060805585018491740289360041599932744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_272_800 : bothSeg evalE (oGrid.idx 272) (oGrid.dm 272) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 272) oGrid.kl oGrid.kr 400 800 ⟨false, 2970306420800311838410309202483259470818060805585018491740289360041599932744⟩ ⟨false, 0⟩ ⟨false, 3361189059183554837104671416400151603559661651344737057380856910890239051634⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_272_1200 : bothSeg evalE (oGrid.idx 272) (oGrid.dm 272) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 272) oGrid.kl oGrid.kr 400 1200 ⟨false, 3361189059183554837104671416400151603559661651344737057380856910890239051634⟩ ⟨false, 0⟩ ⟨false, 3363170834981110828702125370884620560587132100524883889531575133730277459460⟩ ⟨false, 34043940412679803971265269078047193196430127076841322863635599971543799768⟩ = true := by
  decide +kernel

theorem b_272_1600 : bothSeg evalE (oGrid.idx 272) (oGrid.dm 272) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 272) oGrid.kl oGrid.kr 400 1600 ⟨false, 3363170834981110828702125370884620560587132100524883889531575133730277459460⟩ ⟨false, 34043940412679803971265269078047193196430127076841322863635599971543799768⟩ ⟨false, 3205117367774628636788897603889893569432154779086322434357323088104505158266⟩ ⟨false, 192491590761667248059834014869440210157850928064789940919015097954400065764⟩ = true := by
  decide +kernel

theorem b_272_2000 : bothSeg evalE (oGrid.idx 272) (oGrid.dm 272) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 272) oGrid.kl oGrid.kr 400 2000 ⟨false, 3205117367774628636788897603889893569432154779086322434357323088104505158266⟩ ⟨false, 192491590761667248059834014869440210157850928064789940919015097954400065764⟩ ⟨false, 3189864402703290543207612256165583860229668735388827759859498135654419200578⟩ ⟨false, 211147082128883898349444942399765225459404748712368639215201598817831804498⟩ = true := by
  decide +kernel

theorem b_272_2400 : bothLoop evalE (oGrid.idx 272) (oGrid.dm 272) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 272) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3189864402703290543207612256165583860229668735388827759859498135654419200578⟩ ⟨false, 211147082128883898349444942399765225459404748712368639215201598817831804498⟩ = true := by
  decide +kernel

theorem o_row_272 : oGrid.row evalE 272 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_272_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_272_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_272_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_272_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_272_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_272_2000).1 (bothLoop_sound b_272_2400).1))))))

theorem n_row_272 : nGrid.row evalE 272 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_272_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_272_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_272_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_272_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_272_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_272_2000).2 (bothLoop_sound b_272_2400).2))))))

theorem b_273_0 : bothSeg evalE (oGrid.idx 273) (oGrid.dm 273) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 273) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1833262185864145719609769818616232461470135133625404693003649763070480689660⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_273_400 : bothSeg evalE (oGrid.idx 273) (oGrid.dm 273) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 273) oGrid.kl oGrid.kr 400 400 ⟨false, 1833262185864145719609769818616232461470135133625404693003649763070480689660⟩ ⟨false, 0⟩ ⟨false, 2957542602518931220583601693807840231284512105512154724968185441903425234824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_273_800 : bothSeg evalE (oGrid.idx 273) (oGrid.dm 273) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 273) oGrid.kl oGrid.kr 400 800 ⟨false, 2957542602518931220583601693807840231284512105512154724968185441903425234824⟩ ⟨false, 0⟩ ⟨false, 3346379174194669459338175832050041251771938640160136736980994780599312468036⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_273_1200 : bothSeg evalE (oGrid.idx 273) (oGrid.dm 273) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 273) oGrid.kl oGrid.kr 400 1200 ⟨false, 3346379174194669459338175832050041251771938640160136736980994780599312468036⟩ ⟨false, 0⟩ ⟨false, 3348024706248226414340958104076706812518754570670184078291181376314781466296⟩ ⟨false, 33982792566160555782631063037639284658184562686183361794042794693357714542⟩ = true := by
  decide +kernel

theorem b_273_1600 : bothSeg evalE (oGrid.idx 273) (oGrid.dm 273) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 273) oGrid.kl oGrid.kr 400 1600 ⟨false, 3348024706248226414340958104076706812518754570670184078291181376314781466296⟩ ⟨false, 33982792566160555782631063037639284658184562686183361794042794693357714542⟩ ⟨false, 3189916681839560744156811420417583473903357032240060632227031009004006317954⟩ ⟨false, 192476409641513882811183753021078079097159892315215369571053024783510761942⟩ = true := by
  decide +kernel

theorem b_273_2000 : bothSeg evalE (oGrid.idx 273) (oGrid.dm 273) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 273) oGrid.kl oGrid.kr 400 2000 ⟨false, 3189916681839560744156811420417583473903357032240060632227031009004006317954⟩ ⟨false, 192476409641513882811183753021078079097159892315215369571053024783510761942⟩ ⟨false, 3174903524915793975361944529492300774592063143465535055844665218564955294540⟩ ⟨false, 210963164754746331596602389459810227566937549996400769489211885935921964192⟩ = true := by
  decide +kernel

theorem b_273_2400 : bothLoop evalE (oGrid.idx 273) (oGrid.dm 273) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 273) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3174903524915793975361944529492300774592063143465535055844665218564955294540⟩ ⟨false, 210963164754746331596602389459810227566937549996400769489211885935921964192⟩ = true := by
  decide +kernel

theorem o_row_273 : oGrid.row evalE 273 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_273_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_273_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_273_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_273_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_273_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_273_2000).1 (bothLoop_sound b_273_2400).1))))))

theorem n_row_273 : nGrid.row evalE 273 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_273_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_273_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_273_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_273_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_273_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_273_2000).2 (bothLoop_sound b_273_2400).2))))))

theorem b_274_0 : bothSeg evalE (oGrid.idx 274) (oGrid.dm 274) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 274) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1825466596748292964192376977661911887279818881582690566489203809996804503358⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_274_400 : bothSeg evalE (oGrid.idx 274) (oGrid.dm 274) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 274) oGrid.kl oGrid.kr 400 400 ⟨false, 1825466596748292964192376977661911887279818881582690566489203809996804503358⟩ ⟨false, 0⟩ ⟨false, 2944818466715698661669126903211056675305070043667006267357302355758103993734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_274_800 : bothSeg evalE (oGrid.idx 274) (oGrid.dm 274) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 274) oGrid.kl oGrid.kr 400 800 ⟨false, 2944818466715698661669126903211056675305070043667006267357302355758103993734⟩ ⟨false, 0⟩ ⟨false, 3331614855094635688758451518022698067938638490953456137259042244604051615654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_274_1200 : bothSeg evalE (oGrid.idx 274) (oGrid.dm 274) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 274) oGrid.kl oGrid.kr 400 1200 ⟨false, 3331614855094635688758451518022698067938638490953456137259042244604051615654⟩ ⟨false, 0⟩ ⟨false, 3332928658693174744292898127460934490389452789637865425492741226212216508120⟩ ⟨false, 33921811666204470470800802280564525739806533973576202425428022651414840184⟩ = true := by
  decide +kernel

theorem b_274_1600 : bothSeg evalE (oGrid.idx 274) (oGrid.dm 274) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 274) oGrid.kl oGrid.kr 400 1600 ⟨false, 3332928658693174744292898127460934490389452789637865425492741226212216508120⟩ ⟨false, 33921811666204470470800802280564525739806533973576202425428022651414840184⟩ ⟨false, 3174764729923511716694491290902131656151002338683662960210965425527916905898⟩ ⟨false, 192460593499520775796187573486529542619861468800864871045831156163132946634⟩ = true := by
  decide +kernel

theorem b_274_2000 : bothSeg evalE (oGrid.idx 274) (oGrid.dm 274) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 274) oGrid.kl oGrid.kr 400 2000 ⟨false, 3174764729923511716694491290902131656151002338683662960210965425527916905898⟩ ⟨false, 192460593499520775796187573486529542619861468800864871045831156163132946634⟩ ⟨false, 3159990734440001270246926172261951986279738137160156428883220851463216339720⟩ ⟨false, 210779802435866965930743655529257586644867986662474834158585445235934101178⟩ = true := by
  decide +kernel

theorem b_274_2400 : bothLoop evalE (oGrid.idx 274) (oGrid.dm 274) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 274) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3159990734440001270246926172261951986279738137160156428883220851463216339720⟩ ⟨false, 210779802435866965930743655529257586644867986662474834158585445235934101178⟩ = true := by
  decide +kernel

theorem o_row_274 : oGrid.row evalE 274 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_274_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_274_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_274_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_274_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_274_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_274_2000).1 (bothLoop_sound b_274_2400).1))))))

theorem n_row_274 : nGrid.row evalE 274 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_274_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_274_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_274_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_274_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_274_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_274_2000).2 (bothLoop_sound b_274_2400).2))))))

theorem b_275_0 : bothSeg evalE (oGrid.idx 275) (oGrid.dm 275) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 275) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1817695953831457045464839999947385034057983389207490717760979679237227338830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_275_400 : bothSeg evalE (oGrid.idx 275) (oGrid.dm 275) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 275) oGrid.kl oGrid.kr 400 400 ⟨false, 1817695953831457045464839999947385034057983389207490717760979679237227338830⟩ ⟨false, 0⟩ ⟨false, 2932133972020490038912677337397482112853517757853800252492670417428492568744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_275_800 : bothSeg evalE (oGrid.idx 275) (oGrid.dm 275) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 275) oGrid.kl oGrid.kr 400 800 ⟨false, 2932133972020490038912677337397482112853517757853800252492670417428492568744⟩ ⟨false, 0⟩ ⟨false, 3316896063148532317593986886200963819384825364453964957958508969694981011280⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_275_1200 : bothSeg evalE (oGrid.idx 275) (oGrid.dm 275) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 275) oGrid.kl oGrid.kr 400 1200 ⟨false, 3316896063148532317593986886200963819384825364453964957958508969694981011280⟩ ⟨false, 0⟩ ⟨false, 3317882674977818204890908525314377751399611916722158589914028717126299099716⟩ ⟨false, 33860926882540987348481608573136671693242842258158727859763547733381179178⟩ = true := by
  decide +kernel

theorem b_275_1600 : bothSeg evalE (oGrid.idx 275) (oGrid.dm 275) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 275) oGrid.kl oGrid.kr 400 1600 ⟨false, 3317882674977818204890908525314377751399611916722158589914028717126299099716⟩ ⟨false, 33860926882540987348481608573136671693242842258158727859763547733381179178⟩ ⟨false, 3159661553147384324760073231250662462383830981759754543434253927560840709886⟩ ⟨false, 192444112006202566083751407867028886859955508249210714247806467322704061270⟩ = true := by
  decide +kernel

theorem b_275_2000 : bothSeg evalE (oGrid.idx 275) (oGrid.dm 275) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 275) oGrid.kl oGrid.kr 400 2000 ⟨false, 3159661553147384324760073231250662462383830981759754543434253927560840709886⟩ ⟨false, 192444112006202566083751407867028886859955508249210714247806467322704061270⟩ ⟨false, 3145126014866419643555538293599822501798037442008375629547752769904369721052⟩ ⟨false, 210596840589669592640665292641810878941001251374360830079170425920975439050⟩ = true := by
  decide +kernel

theorem b_275_2400 : bothLoop evalE (oGrid.idx 275) (oGrid.dm 275) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 275) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3145126014866419643555538293599822501798037442008375629547752769904369721052⟩ ⟨false, 210596840589669592640665292641810878941001251374360830079170425920975439050⟩ = true := by
  decide +kernel

theorem o_row_275 : oGrid.row evalE 275 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_275_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_275_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_275_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_275_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_275_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_275_2000).1 (bothLoop_sound b_275_2400).1))))))

theorem n_row_275 : nGrid.row evalE 275 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_275_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_275_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_275_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_275_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_275_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_275_2000).2 (bothLoop_sound b_275_2400).2))))))

theorem b_276_0 : bothSeg evalE (oGrid.idx 276) (oGrid.dm 276) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 276) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1809950171424721014272064278224180291920358911152601971139546432830874308512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_276_400 : bothSeg evalE (oGrid.idx 276) (oGrid.dm 276) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 276) oGrid.kl oGrid.kr 400 400 ⟨false, 1809950171424721014272064278224180291920358911152601971139546432830874308512⟩ ⟨false, 0⟩ ⟨false, 2919489012313253816563517615890974046792392247216827924237486143525283816626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_276_800 : bothSeg evalE (oGrid.idx 276) (oGrid.dm 276) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 276) oGrid.kl oGrid.kr 400 800 ⟨false, 2919489012313253816563517615890974046792392247216827924237486143525283816626⟩ ⟨false, 0⟩ ⟨false, 3302222704449410388335111660792584781187005332656017467393257684346450159748⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_276_1200 : bothSeg evalE (oGrid.idx 276) (oGrid.dm 276) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 276) oGrid.kl oGrid.kr 400 1200 ⟨false, 3302222704449410388335111660792584781187005332656017467393257684346450159748⟩ ⟨false, 0⟩ ⟨false, 3302886587987742319087689227400244939649193222336830562521158073773749364572⟩ ⟨false, 33799827333345813677337463817409631797565865351265847454213214052158808020⟩ = true := by
  decide +kernel

theorem b_276_1600 : bothSeg evalE (oGrid.idx 276) (oGrid.dm 276) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 276) oGrid.kl oGrid.kr 400 1600 ⟨false, 3302886587987742319087689227400244939649193222336830562521158073773749364572⟩ ⟨false, 33799827333345813677337463817409631797565865351265847454213214052158808020⟩ ⟨false, 3144607242192625256129005462800949122954659178273401998127238225696704236258⟩ ⟨false, 192426703577360554664989097716628244562181410908091969170023614487428865856⟩ = true := by
  decide +kernel

theorem b_276_2000 : bothSeg evalE (oGrid.idx 276) (oGrid.dm 276) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 276) oGrid.kl oGrid.kr 400 2000 ⟨false, 3144607242192625256129005462800949122954659178273401998127238225696704236258⟩ ⟨false, 192426703577360554664989097716628244562181410908091969170023614487428865856⟩ ⟨false, 3130309420951132457877200965796916860068261489638389098548147345508047673770⟩ ⟨false, 210413796456935238733939004454337119518058058039018069396547931208929125842⟩ = true := by
  decide +kernel

theorem b_276_2400 : bothLoop evalE (oGrid.idx 276) (oGrid.dm 276) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 276) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3130309420951132457877200965796916860068261489638389098548147345508047673770⟩ ⟨false, 210413796456935238733939004454337119518058058039018069396547931208929125842⟩ = true := by
  decide +kernel

theorem o_row_276 : oGrid.row evalE 276 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_276_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_276_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_276_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_276_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_276_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_276_2000).1 (bothLoop_sound b_276_2400).1))))))

theorem n_row_276 : nGrid.row evalE 276 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_276_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_276_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_276_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_276_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_276_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_276_2000).2 (bothLoop_sound b_276_2400).2))))))

theorem b_277_0 : bothSeg evalE (oGrid.idx 277) (oGrid.dm 277) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 277) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1802229165987707545920008219635323010483847385015029220932131216145919959342⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_277_400 : bothSeg evalE (oGrid.idx 277) (oGrid.dm 277) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 277) oGrid.kl oGrid.kr 400 400 ⟨false, 1802229165987707545920008219635323010483847385015029220932131216145919959342⟩ ⟨false, 0⟩ ⟨false, 2906883467358899437401370266167085323705589602682666201503392145778749587366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_277_800 : bothSeg evalE (oGrid.idx 277) (oGrid.dm 277) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 277) oGrid.kl oGrid.kr 400 800 ⟨false, 2906883467358899437401370266167085323705589602682666201503392145778749587366⟩ ⟨false, 0⟩ ⟨false, 3287594601183809971233406306521442482354426004558305800163056753313366867966⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_277_1200 : bothSeg evalE (oGrid.idx 277) (oGrid.dm 277) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 277) oGrid.kl oGrid.kr 400 1200 ⟨false, 3287594601183809971233406306521442482354426004558305800163056753313366867966⟩ ⟨false, 0⟩ ⟨false, 3287939715914671077771184132048948801304657206081601109187490534674625680056⟩ ⟨false, 33738755129035750432223008236827384328500435805011608127710956851349428504⟩ = true := by
  decide +kernel

theorem b_277_1600 : bothSeg evalE (oGrid.idx 277) (oGrid.dm 277) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 277) oGrid.kl oGrid.kr 400 1600 ⟨false, 3287939715914671077771184132048948801304657206081601109187490534674625680056⟩ ⟨false, 33738755129035750432223008236827384328500435805011608127710956851349428504⟩ ⟨false, 3129601205272239682459631881870185665082157042109136920064657076408932929622⟩ ⟨false, 192408621410931845236722857211523972006696655222801592334957289278444180300⟩ = true := by
  decide +kernel

theorem b_277_2000 : bothSeg evalE (oGrid.idx 277) (oGrid.dm 277) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 277) oGrid.kl oGrid.kr 400 2000 ⟨false, 3129601205272239682459631881870185665082157042109136920064657076408932929622⟩ ⟨false, 192408621410931845236722857211523972006696655222801592334957289278444180300⟩ ⟨false, 3115540361115388082194479075673364697975004533880616951281553285654197961934⟩ ⟨false, 210230922675159210072383702678599829768342165801485584915339189215432200546⟩ = true := by
  decide +kernel

theorem b_277_2400 : bothLoop evalE (oGrid.idx 277) (oGrid.dm 277) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 277) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3115540361115388082194479075673364697975004533880616951281553285654197961934⟩ ⟨false, 210230922675159210072383702678599829768342165801485584915339189215432200546⟩ = true := by
  decide +kernel

theorem o_row_277 : oGrid.row evalE 277 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_277_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_277_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_277_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_277_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_277_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_277_2000).1 (bothLoop_sound b_277_2400).1))))))

theorem n_row_277 : nGrid.row evalE 277 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_277_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_277_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_277_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_277_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_277_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_277_2000).2 (bothLoop_sound b_277_2400).2))))))

theorem b_278_0 : bothSeg evalE (oGrid.idx 278) (oGrid.dm 278) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 278) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1794532880215828185746399423792305513331547493579145907908829464931016785052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_278_400 : bothSeg evalE (oGrid.idx 278) (oGrid.dm 278) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 278) oGrid.kl oGrid.kr 400 400 ⟨false, 1794532880215828185746399423792305513331547493579145907908829464931016785052⟩ ⟨false, 0⟩ ⟨false, 2894317257725739727634058607304570294620968680232770372507723914649015585672⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_278_800 : bothSeg evalE (oGrid.idx 278) (oGrid.dm 278) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 278) oGrid.kl oGrid.kr 400 800 ⟨false, 2894317257725739727634058607304570294620968680232770372507723914649015585672⟩ ⟨false, 0⟩ ⟨false, 3273011707036439259440899891130128546230536376696258101935418359001354849318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_278_1200 : bothSeg evalE (oGrid.idx 278) (oGrid.dm 278) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 278) oGrid.kl oGrid.kr 400 1200 ⟨false, 3273011707036439259440899891130128546230536376696258101935418359001354849318⟩ ⟨false, 0⟩ ⟨false, 3273041882139642537685201906480469986687488315391057837200225789634072377818⟩ ⟨false, 33677681436628365369373887351851909386655549031699200661237546697784596896⟩ = true := by
  decide +kernel

theorem b_278_1600 : bothSeg evalE (oGrid.idx 278) (oGrid.dm 278) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 278) oGrid.kl oGrid.kr 400 1600 ⟨false, 3273041882139642537685201906480469986687488315391057837200225789634072377818⟩ ⟨false, 33677681436628365369373887351851909386655549031699200661237546697784596896⟩ ⟨false, 3114643694409771484963004213619704231157042047258853460049836648296804672908⟩ ⟨false, 192389719698374249088099162490121574061495218901391867487001022933923205148⟩ = true := by
  decide +kernel

theorem b_278_2000 : bothSeg evalE (oGrid.idx 278) (oGrid.dm 278) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 278) oGrid.kl oGrid.kr 400 2000 ⟨false, 3114643694409771484963004213619704231157042047258853460049836648296804672908⟩ ⟨false, 192389719698374249088099162490121574061495218901391867487001022933923205148⟩ ⟨false, 3100819006521982481547818499060005887613978832120070721836538968631243303252⟩ ⟨false, 210048316147879928976776469177252260911991108812171216019488326957448451098⟩ = true := by
  decide +kernel

theorem b_278_2400 : bothLoop evalE (oGrid.idx 278) (oGrid.dm 278) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 278) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3100819006521982481547818499060005887613978832120070721836538968631243303252⟩ ⟨false, 210048316147879928976776469177252260911991108812171216019488326957448451098⟩ = true := by
  decide +kernel

theorem o_row_278 : oGrid.row evalE 278 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_278_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_278_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_278_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_278_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_278_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_278_2000).1 (bothLoop_sound b_278_2400).1))))))

theorem n_row_278 : nGrid.row evalE 278 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_278_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_278_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_278_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_278_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_278_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_278_2000).2 (bothLoop_sound b_278_2400).2))))))

theorem b_279_0 : bothSeg evalE (oGrid.idx 279) (oGrid.dm 279) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 279) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1786861259763035681595560706295632931151143248819059968203533241279554944908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_279_400 : bothSeg evalE (oGrid.idx 279) (oGrid.dm 279) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 279) oGrid.kl oGrid.kr 400 400 ⟨false, 1786861259763035681595560706295632931151143248819059968203533241279554944908⟩ ⟨false, 0⟩ ⟨false, 2881790292384280451891288271523910248258505144224245371192575725000671026116⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_279_800 : bothSeg evalE (oGrid.idx 279) (oGrid.dm 279) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 279) oGrid.kl oGrid.kr 400 800 ⟨false, 2881790292384280451891288271523910248258505144224245371192575725000671026116⟩ ⟨false, 0⟩ ⟨false, 3258473929209683237140357734318306905544998764063756959605140032326822317640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_279_1200 : bothSeg evalE (oGrid.idx 279) (oGrid.dm 279) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 279) oGrid.kl oGrid.kr 400 1200 ⟨false, 3258473929209683237140357734318306905544998764063756959605140032326822317640⟩ ⟨false, 0⟩ ⟨false, 3258192706059898994699580097569803942407509644341830826900052800238877296170⟩ ⟨false, 33616679041142247306747787334012853639744834586982931632867754319122922716⟩ = true := by
  decide +kernel

theorem b_279_1600 : bothSeg evalE (oGrid.idx 279) (oGrid.dm 279) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 279) oGrid.kl oGrid.kr 400 1600 ⟨false, 3258192706059898994699580097569803942407509644341830826900052800238877296170⟩ ⟨false, 33616679041142247306747787334012853639744834586982931632867754319122922716⟩ ⟨false, 3099734325327562160856574441531429383714195460654903736167024747265067038934⟩ ⟨false, 192370232946851618231185025664758438498106539028188879324041830484855933368⟩ = true := by
  decide +kernel

theorem b_279_2000 : bothSeg evalE (oGrid.idx 279) (oGrid.dm 279) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 279) oGrid.kl oGrid.kr 400 2000 ⟨false, 3099734325327562160856574441531429383714195460654903736167024747265067038934⟩ ⟨false, 192370232946851618231185025664758438498106539028188879324041830484855933368⟩ ⟨false, 3086144966445312274922918372913021444377447723934317621743976288502075617476⟩ ⟨false, 209866280398591615257079310912213026012227538122772962781182985331597566192⟩ = true := by
  decide +kernel

theorem b_279_2400 : bothLoop evalE (oGrid.idx 279) (oGrid.dm 279) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 279) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3086144966445312274922918372913021444377447723934317621743976288502075617476⟩ ⟨false, 209866280398591615257079310912213026012227538122772962781182985331597566192⟩ = true := by
  decide +kernel

theorem o_row_279 : oGrid.row evalE 279 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_279_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_279_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_279_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_279_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_279_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_279_2000).1 (bothLoop_sound b_279_2400).1))))))

theorem n_row_279 : nGrid.row evalE 279 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_279_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_279_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_279_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_279_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_279_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_279_2000).2 (bothLoop_sound b_279_2400).2))))))

theorem b_280_0 : bothSeg evalE (oGrid.idx 280) (oGrid.dm 280) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 280) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1779214243782433697314445588876970591326586810685380836982218939404865714974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_280_400 : bothSeg evalE (oGrid.idx 280) (oGrid.dm 280) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 280) oGrid.kl oGrid.kr 400 400 ⟨false, 1779214243782433697314445588876970591326586810685380836982218939404865714974⟩ ⟨false, 0⟩ ⟨false, 2869302485667336644135230599176296331678161951276874577205322206831290546416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_280_800 : bothSeg evalE (oGrid.idx 280) (oGrid.dm 280) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 280) oGrid.kl oGrid.kr 400 800 ⟨false, 2869302485667336644135230599176296331678161951276874577205322206831290546416⟩ ⟨false, 0⟩ ⟨false, 3243981146809631760266821248475806706916012306991346461453943103846218894968⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_280_1200 : bothSeg evalE (oGrid.idx 280) (oGrid.dm 280) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 280) oGrid.kl oGrid.kr 400 1200 ⟨false, 3243981146809631760266821248475806706916012306991346461453943103846218894968⟩ ⟨false, 0⟩ ⟨false, 3243391862439120245643448638252625840969239247127612898531673362703110056752⟩ ⟨false, 33555756018209410829590225002831930037040628078459503346168340688340687360⟩ = true := by
  decide +kernel

theorem b_280_1600 : bothSeg evalE (oGrid.idx 280) (oGrid.dm 280) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 280) oGrid.kl oGrid.kr 400 1600 ⟨false, 3243391862439120245643448638252625840969239247127612898531673362703110056752⟩ ⟨false, 33555756018209410829590225002831930037040628078459503346168340688340687360⟩ ⟨false, 3084873031438693134299189643824344145942754042084125465784926429151888217420⟩ ⟨false, 192350092885444859498660010814991930977336649142634000803857991195741258284⟩ = true := by
  decide +kernel

theorem b_280_2000 : bothSeg evalE (oGrid.idx 280) (oGrid.dm 280) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 280) oGrid.kl oGrid.kr 400 2000 ⟨false, 3084873031438693134299189643824344145942754042084125465784926429151888217420⟩ ⟨false, 192350092885444859498660010814991930977336649142634000803857991195741258284⟩ ⟨false, 3071518123210597119378720005151191700035752162824494379815815384741266163280⟩ ⟨false, 209684265720238867112345845912407191507248017868676920955363967893115091956⟩ = true := by
  decide +kernel

theorem b_280_2400 : bothLoop evalE (oGrid.idx 280) (oGrid.dm 280) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 280) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3071518123210597119378720005151191700035752162824494379815815384741266163280⟩ ⟨false, 209684265720238867112345845912407191507248017868676920955363967893115091956⟩ = true := by
  decide +kernel

theorem o_row_280 : oGrid.row evalE 280 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_280_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_280_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_280_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_280_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_280_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_280_2000).1 (bothLoop_sound b_280_2400).1))))))

theorem n_row_280 : nGrid.row evalE 280 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_280_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_280_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_280_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_280_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_280_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_280_2000).2 (bothLoop_sound b_280_2400).2))))))

theorem b_281_0 : bothSeg evalE (oGrid.idx 281) (oGrid.dm 281) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 281) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1771591759886263114778180046842682866496727252067068676275228568580352575878⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_281_400 : bothSeg evalE (oGrid.idx 281) (oGrid.dm 281) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 281) oGrid.kl oGrid.kr 400 400 ⟨false, 1771591759886263114778180046842682866496727252067068676275228568580352575878⟩ ⟨false, 0⟩ ⟨false, 2856853742986081716974449399623652185238262803028817823307263087328964492512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_281_800 : bothSeg evalE (oGrid.idx 281) (oGrid.dm 281) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 281) oGrid.kl oGrid.kr 400 800 ⟨false, 2856853742986081716974449399623652185238262803028817823307263087328964492512⟩ ⟨false, 0⟩ ⟨false, 3229533269385266329478204973232406827740291550369844379462059842316302770398⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_281_1200 : bothSeg evalE (oGrid.idx 281) (oGrid.dm 281) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 281) oGrid.kl oGrid.kr 400 1200 ⟨false, 3229533269385266329478204973232406827740291550369844379462059842316302770398⟩ ⟨false, 0⟩ ⟨false, 3228639017419933082665067743381598453602987559455959267099673329532807359660⟩ ⟨false, 33494934980039454336377216610937843859242579371023737803177816824032163692⟩ = true := by
  decide +kernel

theorem b_281_1600 : bothSeg evalE (oGrid.idx 281) (oGrid.dm 281) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 281) oGrid.kl oGrid.kr 400 1600 ⟨false, 3228639017419933082665067743381598453602987559455959267099673329532807359660⟩ ⟨false, 33494934980039454336377216610937843859242579371023737803177816824032163692⟩ ⟨false, 3070059768895376009480446289516216534827480414988305499155455314556024498912⟩ ⟨false, 192329296038126404868391708876089224952534253987511604866064090770166279034⟩ = true := by
  decide +kernel

theorem b_281_2000 : bothSeg evalE (oGrid.idx 281) (oGrid.dm 281) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 281) oGrid.kl oGrid.kr 400 2000 ⟨false, 3070059768895376009480446289516216534827480414988305499155455314556024498912⟩ ⟨false, 192329296038126404868391708876089224952534253987511604866064090770166279034⟩ ⟨false, 3056938382643488855596110656209428888648392197535783889232038338444692489206⟩ ⟨false, 209502281316337605475826063388655607462229630890333946660895754619551585582⟩ = true := by
  decide +kernel

theorem b_281_2400 : bothLoop evalE (oGrid.idx 281) (oGrid.dm 281) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 281) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3056938382643488855596110656209428888648392197535783889232038338444692489206⟩ ⟨false, 209502281316337605475826063388655607462229630890333946660895754619551585582⟩ = true := by
  decide +kernel

theorem o_row_281 : oGrid.row evalE 281 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_281_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_281_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_281_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_281_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_281_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_281_2000).1 (bothLoop_sound b_281_2400).1))))))

theorem n_row_281 : nGrid.row evalE 281 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_281_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_281_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_281_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_281_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_281_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_281_2000).2 (bothLoop_sound b_281_2400).2))))))

theorem b_282_0 : bothSeg evalE (oGrid.idx 282) (oGrid.dm 282) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 282) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1763993748653372166470632596623010802494135974594725622315865570120276639156⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_282_400 : bothSeg evalE (oGrid.idx 282) (oGrid.dm 282) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 282) oGrid.kl oGrid.kr 400 400 ⟨false, 1763993748653372166470632596623010802494135974594725622315865570120276639156⟩ ⟨false, 0⟩ ⟨false, 2844443955231602244713671173063310850887685206123759367117548167747860322588⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_282_800 : bothSeg evalE (oGrid.idx 282) (oGrid.dm 282) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 282) oGrid.kl oGrid.kr 400 800 ⟨false, 2844443955231602244713671173063310850887685206123759367117548167747860322588⟩ ⟨false, 0⟩ ⟨false, 3215130217701869638215122929114647633514900238226591825980434125210770734448⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_282_1200 : bothSeg evalE (oGrid.idx 282) (oGrid.dm 282) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 282) oGrid.kl oGrid.kr 400 1200 ⟨false, 3215130217701869638215122929114647633514900238226591825980434125210770734448⟩ ⟨false, 0⟩ ⟨false, 3213933706330011306729290235213367722140220499693043489885783691809374007220⟩ ⟨false, 33434309497206777127982910078538591440470027114485194478937155712921088334⟩ = true := by
  decide +kernel

theorem b_282_1600 : bothSeg evalE (oGrid.idx 282) (oGrid.dm 282) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 282) oGrid.kl oGrid.kr 400 1600 ⟨false, 3213933706330011306729290235213367722140220499693043489885783691809374007220⟩ ⟨false, 33434309497206777127982910078538591440470027114485194478937155712921088334⟩ ⟨false, 3055294182588141326613231123372891603041996816894232617805458384520368361902⟩ ⟨false, 192308012253397009861701422655118908065614272369286148906707489639977816684⟩ = true := by
  decide +kernel

theorem b_282_2000 : bothSeg evalE (oGrid.idx 282) (oGrid.dm 282) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 282) oGrid.kl oGrid.kr 400 2000 ⟨false, 3055294182588141326613231123372891603041996816894232617805458384520368361902⟩ ⟨false, 192308012253397009861701422655118908065614272369286148906707489639977816684⟩ ⟨false, 3042405334903001423403915056103898609684146885315217035845980933088568761280⟩ ⟨false, 209321497945446051064400657817896046859728496297354637069460166095001939554⟩ = true := by
  decide +kernel

theorem b_282_2400 : bothLoop evalE (oGrid.idx 282) (oGrid.dm 282) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 282) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3042405334903001423403915056103898609684146885315217035845980933088568761280⟩ ⟨false, 209321497945446051064400657817896046859728496297354637069460166095001939554⟩ = true := by
  decide +kernel

theorem o_row_282 : oGrid.row evalE 282 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_282_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_282_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_282_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_282_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_282_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_282_2000).1 (bothLoop_sound b_282_2400).1))))))

theorem n_row_282 : nGrid.row evalE 282 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_282_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_282_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_282_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_282_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_282_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_282_2000).2 (bothLoop_sound b_282_2400).2))))))

theorem b_283_0 : bothSeg evalE (oGrid.idx 283) (oGrid.dm 283) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 283) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1756420152450437431445715448103686735197237066175830948320168330029299159976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_283_400 : bothSeg evalE (oGrid.idx 283) (oGrid.dm 283) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 283) oGrid.kl oGrid.kr 400 400 ⟨false, 1756420152450437431445715448103686735197237066175830948320168330029299159976⟩ ⟨false, 0⟩ ⟨false, 2832073059245904089370414602382716671549882320766990662867763732005830047946⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_283_800 : bothSeg evalE (oGrid.idx 283) (oGrid.dm 283) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 283) oGrid.kl oGrid.kr 400 800 ⟨false, 2832073059245904089370414602382716671549882320766990662867763732005830047946⟩ ⟨false, 0⟩ ⟨false, 3200771865717902714520562682310749094134952933532759780157525375332101390272⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_283_1200 : bothSeg evalE (oGrid.idx 283) (oGrid.dm 283) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 283) oGrid.kl oGrid.kr 400 1200 ⟨false, 3200771865717902714520562682310749094134952933532759780157525375332101390272⟩ ⟨false, 0⟩ ⟨false, 3199276116378214137939844602091122203124219304162296072011985735359155575772⟩ ⟨false, 33373429716605179250919697690310824634057135860657415956406019852447949464⟩ = true := by
  decide +kernel

theorem b_283_1600 : bothSeg evalE (oGrid.idx 283) (oGrid.dm 283) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 283) oGrid.kl oGrid.kr 400 1600 ⟨false, 3199276116378214137939844602091122203124219304162296072011985735359155575772⟩ ⟨false, 33373429716605179250919697690310824634057135860657415956406019852447949464⟩ ⟨false, 3040576726729986355389932837946436414188422301924049903213785303144308943278⟩ ⟨false, 192285710093427870191485981582847988036143753958853739861199250337284981002⟩ = true := by
  decide +kernel

theorem b_283_2000 : bothSeg evalE (oGrid.idx 283) (oGrid.dm 283) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 283) oGrid.kl oGrid.kr 400 2000 ⟨false, 3040576726729986355389932837946436414188422301924049903213785303144308943278⟩ ⟨false, 192285710093427870191485981582847988036143753958853739861199250337284981002⟩ ⟨false, 3027919426382664111441815856698463585431220777286358782176641967254799114920⟩ ⟨false, 209140234049728416005418950960971359846439840345556759218341581556640908154⟩ = true := by
  decide +kernel

theorem b_283_2400 : bothLoop evalE (oGrid.idx 283) (oGrid.dm 283) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 283) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3027919426382664111441815856698463585431220777286358782176641967254799114920⟩ ⟨false, 209140234049728416005418950960971359846439840345556759218341581556640908154⟩ = true := by
  decide +kernel

theorem o_row_283 : oGrid.row evalE 283 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_283_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_283_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_283_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_283_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_283_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_283_2000).1 (bothLoop_sound b_283_2400).1))))))

theorem n_row_283 : nGrid.row evalE 283 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_283_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_283_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_283_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_283_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_283_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_283_2000).2 (bothLoop_sound b_283_2400).2))))))

theorem b_284_0 : bothSeg evalE (oGrid.idx 284) (oGrid.dm 284) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 284) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1748870894298199768062128476655760876468960137966077443951670573424168700650⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_284_400 : bothSeg evalE (oGrid.idx 284) (oGrid.dm 284) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 284) oGrid.kl oGrid.kr 400 400 ⟨false, 1748870894298199768062128476655760876468960137966077443951670573424168700650⟩ ⟨false, 0⟩ ⟨false, 2819740943237381553141703997694777285178705243948493137548302053219501095588⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_284_800 : bothSeg evalE (oGrid.idx 284) (oGrid.dm 284) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 284) oGrid.kl oGrid.kr 400 800 ⟨false, 2819740943237381553141703997694777285178705243948493137548302053219501095588⟩ ⟨false, 0⟩ ⟨false, 3186458130448740015081430637115335424897752665374866854699287540610268273868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_284_1200 : bothSeg evalE (oGrid.idx 284) (oGrid.dm 284) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 284) oGrid.kl oGrid.kr 400 1200 ⟨false, 3186458130448740015081430637115335424897752665374866854699287540610268273868⟩ ⟨false, 0⟩ ⟨false, 3184665966000731021262090031212930655601123676911154422247214259205879864540⟩ ⟨false, 33312279302455608754529519490387188048066253554898994443698919321502366136⟩ = true := by
  decide +kernel

theorem b_284_1600 : bothSeg evalE (oGrid.idx 284) (oGrid.dm 284) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 284) oGrid.kl oGrid.kr 400 1600 ⟨false, 3184665966000731021262090031212930655601123676911154422247214259205879864540⟩ ⟨false, 33312279302455608754529519490387188048066253554898994443698919321502366136⟩ ⟨false, 3025907344038488674901738985342183571047787935381124336167048289100103345746⟩ ⟨false, 192262415169416190752206936496148131724964627437599175657039757727530584356⟩ = true := by
  decide +kernel

theorem b_284_2000 : bothSeg evalE (oGrid.idx 284) (oGrid.dm 284) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 284) oGrid.kl oGrid.kr 400 2000 ⟨false, 3025907344038488674901738985342183571047787935381124336167048289100103345746⟩ ⟨false, 192262415169416190752206936496148131724964627437599175657039757727530584356⟩ ⟨false, 3013480552840266123795290522055550321462657727464343643012794459192745302582⟩ ⟨false, 208958807669124488515497545282189562676486217329336827182271803311988562716⟩ = true := by
  decide +kernel

theorem b_284_2400 : bothLoop evalE (oGrid.idx 284) (oGrid.dm 284) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 284) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3013480552840266123795290522055550321462657727464343643012794459192745302582⟩ ⟨false, 208958807669124488515497545282189562676486217329336827182271803311988562716⟩ = true := by
  decide +kernel

theorem o_row_284 : oGrid.row evalE 284 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_284_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_284_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_284_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_284_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_284_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_284_2000).1 (bothLoop_sound b_284_2400).1))))))

theorem n_row_284 : nGrid.row evalE 284 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_284_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_284_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_284_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_284_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_284_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_284_2000).2 (bothLoop_sound b_284_2400).2))))))

theorem b_285_0 : bothSeg evalE (oGrid.idx 285) (oGrid.dm 285) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 285) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1741345910645921433242635475914265345497061055938629323531266578325236559916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_285_400 : bothSeg evalE (oGrid.idx 285) (oGrid.dm 285) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 285) oGrid.kl oGrid.kr 400 400 ⟨false, 1741345910645921433242635475914265345497061055938629323531266578325236559916⟩ ⟨false, 0⟩ ⟨false, 2807447520037906514253537456972350836253465733530154409328562941329723351546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_285_800 : bothSeg evalE (oGrid.idx 285) (oGrid.dm 285) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 285) oGrid.kl oGrid.kr 400 800 ⟨false, 2807447520037906514253537456972350836253465733530154409328562941329723351546⟩ ⟨false, 0⟩ ⟨false, 3172188915403815294050215375116808012114740104342493986049631163069215416254⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_285_1200 : bothSeg evalE (oGrid.idx 285) (oGrid.dm 285) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 285) oGrid.kl oGrid.kr 400 1200 ⟨false, 3172188915403815294050215375116808012114740104342493986049631163069215416254⟩ ⟨false, 0⟩ ⟨false, 3170102595976627317024126006549946309327849488052907272082751321273628815156⟩ ⟨false, 33251455786924813709466390797992821203554892435923449531635652137626763394⟩ = true := by
  decide +kernel

theorem b_285_1600 : bothSeg evalE (oGrid.idx 285) (oGrid.dm 285) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 285) oGrid.kl oGrid.kr 400 1600 ⟨false, 3170102595976627317024126006549946309327849488052907272082751321273628815156⟩ ⟨false, 33251455786924813709466390797992821203554892435923449531635652137626763394⟩ ⟨false, 3011285529499345310599516062935192799143278455896712095294509661078070988426⟩ ⟨false, 192238825870596869280630889266452231923720431753284813540998200920701399846⟩ = true := by
  decide +kernel

theorem b_285_2000 : bothSeg evalE (oGrid.idx 285) (oGrid.dm 285) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 285) oGrid.kl oGrid.kr 400 2000 ⟨false, 3011285529499345310599516062935192799143278455896712095294509661078070988426⟩ ⟨false, 192238825870596869280630889266452231923720431753284813540998200920701399846⟩ ⟨false, 2999088143920008454817868779486101617418611660714411351113519128453865359046⟩ ⟨false, 208778137683015386604701733264249541828769307675453925097151654038806165596⟩ = true := by
  decide +kernel

theorem b_285_2400 : bothLoop evalE (oGrid.idx 285) (oGrid.dm 285) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 285) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2999088143920008454817868779486101617418611660714411351113519128453865359046⟩ ⟨false, 208778137683015386604701733264249541828769307675453925097151654038806165596⟩ = true := by
  decide +kernel

theorem o_row_285 : oGrid.row evalE 285 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_285_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_285_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_285_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_285_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_285_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_285_2000).1 (bothLoop_sound b_285_2400).1))))))

theorem n_row_285 : nGrid.row evalE 285 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_285_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_285_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_285_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_285_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_285_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_285_2000).2 (bothLoop_sound b_285_2400).2))))))

theorem b_286_0 : bothSeg evalE (oGrid.idx 286) (oGrid.dm 286) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 286) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1733845136637757145657347921948782637564772951659807304033406920097097597096⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_286_400 : bothSeg evalE (oGrid.idx 286) (oGrid.dm 286) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 286) oGrid.kl oGrid.kr 400 400 ⟨false, 1733845136637757145657347921948782637564772951659807304033406920097097597096⟩ ⟨false, 0⟩ ⟨false, 2795192684109912976412970279375244382645376878875451448924269027245676246258⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_286_800 : bothSeg evalE (oGrid.idx 286) (oGrid.dm 286) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 286) oGrid.kl oGrid.kr 400 800 ⟨false, 2795192684109912976412970279375244382645376878875451448924269027245676246258⟩ ⟨false, 0⟩ ⟨false, 3157964107645372490459724436850208939700518094281888000264708341866267610460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_286_1200 : bothSeg evalE (oGrid.idx 286) (oGrid.dm 286) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 286) oGrid.kl oGrid.kr 400 1200 ⟨false, 3157964107645372490459724436850208939700518094281888000264708341866267610460⟩ ⟨false, 0⟩ ⟨false, 3155585695976700113644996064351402092148099045010773317767995422043564923656⟩ ⟨false, 33190708461726132337931275559179496305202654448060825672917066665638827082⟩ = true := by
  decide +kernel

theorem b_286_1600 : bothSeg evalE (oGrid.idx 286) (oGrid.dm 286) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 286) oGrid.kl oGrid.kr 400 1600 ⟨false, 3155585695976700113644996064351402092148099045010773317767995422043564923656⟩ ⟨false, 33190708461726132337931275559179496305202654448060825672917066665638827082⟩ ⟨false, 2996711209690830157658222659155002740072963814379579186302829353606379976308⟩ ⟨false, 192214605707618755988697539234394220179855337814141099728572213940410136946⟩ = true := by
  decide +kernel

theorem b_286_2000 : bothSeg evalE (oGrid.idx 286) (oGrid.dm 286) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 286) oGrid.kl oGrid.kr 400 2000 ⟨false, 2996711209690830157658222659155002740072963814379579186302829353606379976308⟩ ⟨false, 192214605707618755988697539234394220179855337814141099728572213940410136946⟩ ⟨false, 2984742115936089590297658017589465743043852197287207989096283875940490858468⟩ ⟨false, 208597905057163829264991804500647954910733653739766487277447814640420366872⟩ = true := by
  decide +kernel

theorem b_286_2400 : bothLoop evalE (oGrid.idx 286) (oGrid.dm 286) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 286) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2984742115936089590297658017589465743043852197287207989096283875940490858468⟩ ⟨false, 208597905057163829264991804500647954910733653739766487277447814640420366872⟩ = true := by
  decide +kernel

theorem o_row_286 : oGrid.row evalE 286 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_286_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_286_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_286_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_286_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_286_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_286_2000).1 (bothLoop_sound b_286_2400).1))))))

theorem n_row_286 : nGrid.row evalE 286 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_286_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_286_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_286_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_286_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_286_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_286_2000).2 (bothLoop_sound b_286_2400).2))))))

theorem b_287_0 : bothSeg evalE (oGrid.idx 287) (oGrid.dm 287) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 287) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1726368534369770996283279072801587145090759046780267352942620620490167570238⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_287_400 : bothSeg evalE (oGrid.idx 287) (oGrid.dm 287) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 287) oGrid.kl oGrid.kr 400 400 ⟨false, 1726368534369770996283279072801587145090759046780267352942620620490167570238⟩ ⟨false, 0⟩ ⟨false, 2782976370077475254971652113748787907677418082472783783362874725501428734774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_287_800 : bothSeg evalE (oGrid.idx 287) (oGrid.dm 287) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 287) oGrid.kl oGrid.kr 400 800 ⟨false, 2782976370077475254971652113748787907677418082472783783362874725501428734774⟩ ⟨false, 0⟩ ⟨false, 3143783602212425379004209691444377453480046590606331002608916855970886355764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_287_1200 : bothSeg evalE (oGrid.idx 287) (oGrid.dm 287) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 287) oGrid.kl oGrid.kr 400 1200 ⟨false, 3143783602212425379004209691444377453480046590606331002608916855970886355764⟩ ⟨false, 0⟩ ⟨false, 3141114925664918622775030085273847531694922825858562566220437277862081716814⟩ ⟨false, 33130056004049202629158828376527646098001020782393334765186729048554348960⟩ = true := by
  decide +kernel

theorem b_287_1600 : bothSeg evalE (oGrid.idx 287) (oGrid.dm 287) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 287) oGrid.kl oGrid.kr 400 1600 ⟨false, 3141114925664918622775030085273847531694922825858562566220437277862081716814⟩ ⟨false, 33130056004049202629158828376527646098001020782393334765186729048554348960⟩ ⟨false, 2982184234593405757251019674503981544105611170855209735310664266031858203494⟩ ⟨false, 192189761257165210436799567672077676124814765300047466255868190144907238490⟩ = true := by
  decide +kernel

theorem b_287_2000 : bothSeg evalE (oGrid.idx 287) (oGrid.dm 287) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 287) oGrid.kl oGrid.kr 400 2000 ⟨false, 2982184234593405757251019674503981544105611170855209735310664266031858203494⟩ ⟨false, 192189761257165210436799567672077676124814765300047466255868190144907238490⟩ ⟨false, 2970442242567486195697234038348462272287096896369338602010192483735702348554⟩ ⟨false, 208417919284723993346149736521875137411240142229635300843115692944571151874⟩ = true := by
  decide +kernel

theorem b_287_2400 : bothLoop evalE (oGrid.idx 287) (oGrid.dm 287) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 287) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2970442242567486195697234038348462272287096896369338602010192483735702348554⟩ ⟨false, 208417919284723993346149736521875137411240142229635300843115692944571151874⟩ = true := by
  decide +kernel

theorem o_row_287 : oGrid.row evalE 287 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_287_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_287_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_287_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_287_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_287_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_287_2000).1 (bothLoop_sound b_287_2400).1))))))

theorem n_row_287 : nGrid.row evalE 287 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_287_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_287_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_287_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_287_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_287_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_287_2000).2 (bothLoop_sound b_287_2400).2))))))

theorem o_blk_264 : allFrom (fun j => oGrid.row evalE j) 264 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 264) o_row_264 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 265) o_row_265 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 266) o_row_266 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 267) o_row_267 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 268) o_row_268 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 269) o_row_269 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 270) o_row_270 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 271) o_row_271 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 272) o_row_272 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 273) o_row_273 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 274) o_row_274 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 275) o_row_275 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 276) o_row_276 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 277) o_row_277 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 278) o_row_278 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 279) o_row_279 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 280) o_row_280 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 281) o_row_281 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 282) o_row_282 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 283) o_row_283 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 284) o_row_284 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 285) o_row_285 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 286) o_row_286 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 287) o_row_287 (allFrom_zero (fun j => oGrid.row evalE j) 288)))))))))))))))))))))))))

theorem n_blk_264 : allFrom (fun j => nGrid.row evalE j) 264 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 264) n_row_264 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 265) n_row_265 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 266) n_row_266 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 267) n_row_267 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 268) n_row_268 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 269) n_row_269 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 270) n_row_270 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 271) n_row_271 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 272) n_row_272 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 273) n_row_273 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 274) n_row_274 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 275) n_row_275 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 276) n_row_276 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 277) n_row_277 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 278) n_row_278 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 279) n_row_279 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 280) n_row_280 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 281) n_row_281 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 282) n_row_282 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 283) n_row_283 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 284) n_row_284 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 285) n_row_285 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 286) n_row_286 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 287) n_row_287 (allFrom_zero (fun j => nGrid.row evalE j) 288)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
