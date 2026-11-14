/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 67 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1608`–`1631`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1608_0 : bothSeg evalE (oGrid.idx 1608) (oGrid.dm 1608) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1608) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62601236440512512502053949138475564493949631216101998511840545390316368846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1608_400 : bothSeg evalE (oGrid.idx 1608) (oGrid.dm 1608) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1608) oGrid.kl oGrid.kr 400 400 ⟨false, 62601236440512512502053949138475564493949631216101998511840545390316368846⟩ ⟨false, 0⟩ ⟨false, 127925825238621081329347649264973195191895609581675493830155624725108868288⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1608_800 : bothSeg evalE (oGrid.idx 1608) (oGrid.dm 1608) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1608) oGrid.kl oGrid.kr 400 800 ⟨false, 127925825238621081329347649264973195191895609581675493830155624725108868288⟩ ⟨false, 0⟩ ⟨false, 226074255646502984703857605119625269549338690498089419436090911455427166420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1608_1200 : bothSeg evalE (oGrid.idx 1608) (oGrid.dm 1608) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1608) oGrid.kl oGrid.kr 400 1200 ⟨false, 226074255646502984703857605119625269549338690498089419436090911455427166420⟩ ⟨false, 0⟩ ⟨false, 367555090989137932859847717019155544197730259415332185612007536939676419476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1608_1600 : bothSeg evalE (oGrid.idx 1608) (oGrid.dm 1608) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1608) oGrid.kl oGrid.kr 400 1600 ⟨false, 367555090989137932859847717019155544197730259415332185612007536939676419476⟩ ⟨false, 0⟩ ⟨false, 555921852770873505865507250372701818427335003310876717571678104749890612322⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1608_2000 : bothSeg evalE (oGrid.idx 1608) (oGrid.dm 1608) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1608) oGrid.kl oGrid.kr 400 2000 ⟨false, 555921852770873505865507250372701818427335003310876717571678104749890612322⟩ ⟨false, 0⟩ ⟨false, 790189482578223408675987031218172650071843103405640893158922132911551419230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1608_2400 : bothLoop evalE (oGrid.idx 1608) (oGrid.dm 1608) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1608) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 790189482578223408675987031218172650071843103405640893158922132911551419230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1608 : oGrid.row evalE 1608 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1608_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1608_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1608_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1608_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1608_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1608_2000).1 (bothLoop_sound b_1608_2400).1))))))

theorem n_row_1608 : nGrid.row evalE 1608 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1608_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1608_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1608_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1608_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1608_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1608_2000).2 (bothLoop_sound b_1608_2400).2))))))

theorem b_1609_0 : bothSeg evalE (oGrid.idx 1609) (oGrid.dm 1609) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1609) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62325827445945941420171312599182188337822757387361710421583606668385196782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1609_400 : bothSeg evalE (oGrid.idx 1609) (oGrid.dm 1609) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1609) oGrid.kl oGrid.kr 400 400 ⟨false, 62325827445945941420171312599182188337822757387361710421583606668385196782⟩ ⟨false, 0⟩ ⟨false, 127924593631425430566223781439295727984412898114729330390420494570005684726⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1609_800 : bothSeg evalE (oGrid.idx 1609) (oGrid.dm 1609) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1609) oGrid.kl oGrid.kr 400 800 ⟨false, 127924593631425430566223781439295727984412898114729330390420494570005684726⟩ ⟨false, 0⟩ ⟨false, 226415254574066638569403415545106807186218998709092456813190545902726388046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1609_1200 : bothSeg evalE (oGrid.idx 1609) (oGrid.dm 1609) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1609) oGrid.kl oGrid.kr 400 1200 ⟨false, 226415254574066638569403415545106807186218998709092456813190545902726388046⟩ ⟨false, 0⟩ ⟨false, 368200384138326521970256297828181427308539042961060297744472885807621171008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1609_1600 : bothSeg evalE (oGrid.idx 1609) (oGrid.dm 1609) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1609) oGrid.kl oGrid.kr 400 1600 ⟨false, 368200384138326521970256297828181427308539042961060297744472885807621171008⟩ ⟨false, 0⟩ ⟨false, 556836415643875235793999466710688914336642131565708223864272922466938237072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1609_2000 : bothSeg evalE (oGrid.idx 1609) (oGrid.dm 1609) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1609) oGrid.kl oGrid.kr 400 2000 ⟨false, 556836415643875235793999466710688914336642131565708223864272922466938237072⟩ ⟨false, 0⟩ ⟨false, 791344647435774296438378127493846894651809315186275713884444751001882552728⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1609_2400 : bothLoop evalE (oGrid.idx 1609) (oGrid.dm 1609) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1609) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 791344647435774296438378127493846894651809315186275713884444751001882552728⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1609 : oGrid.row evalE 1609 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1609_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1609_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1609_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1609_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1609_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1609_2000).1 (bothLoop_sound b_1609_2400).1))))))

theorem n_row_1609 : nGrid.row evalE 1609 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1609_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1609_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1609_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1609_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1609_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1609_2000).2 (bothLoop_sound b_1609_2400).2))))))

theorem b_1610_0 : bothSeg evalE (oGrid.idx 1610) (oGrid.dm 1610) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1610) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62061252808914440416934935357046444777670396198774174172807258484581934626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1610_400 : bothSeg evalE (oGrid.idx 1610) (oGrid.dm 1610) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1610) oGrid.kl oGrid.kr 400 400 ⟨false, 62061252808914440416934935357046444777670396198774174172807258484581934626⟩ ⟨false, 0⟩ ⟨false, 127939944264833741562055121591397764070535237664738425140566182720775590382⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1610_800 : bothSeg evalE (oGrid.idx 1610) (oGrid.dm 1610) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1610) oGrid.kl oGrid.kr 400 800 ⟨false, 127939944264833741562055121591397764070535237664738425140566182720775590382⟩ ⟨false, 0⟩ ⟨false, 226772771413211838414867843527253179409409962944882792631757843630730460426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1610_1200 : bothSeg evalE (oGrid.idx 1610) (oGrid.dm 1610) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1610) oGrid.kl oGrid.kr 400 1200 ⟨false, 226772771413211838414867843527253179409409962944882792631757843630730460426⟩ ⟨false, 0⟩ ⟨false, 368862172129430085545936316774297681652047980237527894866626311994775242352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1610_1600 : bothSeg evalE (oGrid.idx 1610) (oGrid.dm 1610) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1610) oGrid.kl oGrid.kr 400 1600 ⟨false, 368862172129430085545936316774297681652047980237527894866626311994775242352⟩ ⟨false, 0⟩ ⟨false, 557767480833057909181146315426631375008904362753355605866583291216353450900⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1610_2000 : bothSeg evalE (oGrid.idx 1610) (oGrid.dm 1610) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1610) oGrid.kl oGrid.kr 400 2000 ⟨false, 557767480833057909181146315426631375008904362753355605866583291216353450900⟩ ⟨false, 0⟩ ⟨false, 792516340024431692875868998235791806641297511529827628004888264107015797990⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1610_2400 : bothLoop evalE (oGrid.idx 1610) (oGrid.dm 1610) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1610) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 792516340024431692875868998235791806641297511529827628004888264107015797990⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1610 : oGrid.row evalE 1610 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1610_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1610_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1610_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1610_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1610_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1610_2000).1 (bothLoop_sound b_1610_2400).1))))))

theorem n_row_1610 : nGrid.row evalE 1610 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1610_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1610_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1610_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1610_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1610_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1610_2000).2 (bothLoop_sound b_1610_2400).2))))))

theorem b_1611_0 : bothSeg evalE (oGrid.idx 1611) (oGrid.dm 1611) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1611) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61807937836092662479657694286512579113163043971006928394931208299935811560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1611_400 : bothSeg evalE (oGrid.idx 1611) (oGrid.dm 1611) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1611) oGrid.kl oGrid.kr 400 400 ⟨false, 61807937836092662479657694286512579113163043971006928394931208299935811560⟩ ⟨false, 0⟩ ⟨false, 127972110421648698553962439777657356764161631028697088835478084692797846922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1611_800 : bothSeg evalE (oGrid.idx 1611) (oGrid.dm 1611) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1611) oGrid.kl oGrid.kr 400 800 ⟨false, 127972110421648698553962439777657356764161631028697088835478084692797846922⟩ ⟨false, 0⟩ ⟨false, 227147039476873431273842738389813993231411470957011560160943032658305839228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1611_1200 : bothSeg evalE (oGrid.idx 1611) (oGrid.dm 1611) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1611) oGrid.kl oGrid.kr 400 1200 ⟨false, 227147039476873431273842738389813993231411470957011560160943032658305839228⟩ ⟨false, 0⟩ ⟨false, 369540688254126779808673922804756228084229620984381927570806316856268966760⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1611_1600 : bothSeg evalE (oGrid.idx 1611) (oGrid.dm 1611) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1611) oGrid.kl oGrid.kr 400 1600 ⟨false, 369540688254126779808673922804756228084229620984381927570806316856268966760⟩ ⟨false, 0⟩ ⟨false, 558715281583022845893708565482144769074341637424869021271862851467777264130⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1611_2000 : bothSeg evalE (oGrid.idx 1611) (oGrid.dm 1611) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1611) oGrid.kl oGrid.kr 400 2000 ⟨false, 558715281583022845893708565482144769074341637424869021271862851467777264130⟩ ⟨false, 0⟩ ⟨false, 793704793536822940783685552899845773819908498571960734888025587169233072256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1611_2400 : bothLoop evalE (oGrid.idx 1611) (oGrid.dm 1611) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1611) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 793704793536822940783685552899845773819908498571960734888025587169233072256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1611 : oGrid.row evalE 1611 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1611_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1611_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1611_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1611_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1611_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1611_2000).1 (bothLoop_sound b_1611_2400).1))))))

theorem n_row_1611 : nGrid.row evalE 1611 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1611_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1611_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1611_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1611_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1611_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1611_2000).2 (bothLoop_sound b_1611_2400).2))))))

theorem b_1612_0 : bothSeg evalE (oGrid.idx 1612) (oGrid.dm 1612) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1612) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61566286735463244702317417162786513807605001830443226126847891071317307536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1612_400 : bothSeg evalE (oGrid.idx 1612) (oGrid.dm 1612) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1612) oGrid.kl oGrid.kr 400 400 ⟨false, 61566286735463244702317417162786513807605001830443226126847891071317307536⟩ ⟨false, 0⟩ ⟨false, 128021302308411983788216245321346938692543034223908408845131287495903417876⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1612_800 : bothSeg evalE (oGrid.idx 1612) (oGrid.dm 1612) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1612) oGrid.kl oGrid.kr 400 800 ⟨false, 128021302308411983788216245321346938692543034223908408845131287495903417876⟩ ⟨false, 0⟩ ⟨false, 227538269001737348551508184051532758595481095555173350630420974294948170920⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1612_1200 : bothSeg evalE (oGrid.idx 1612) (oGrid.dm 1612) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1612) oGrid.kl oGrid.kr 400 1200 ⟨false, 227538269001737348551508184051532758595481095555173350630420974294948170920⟩ ⟨false, 0⟩ ⟨false, 370236142727925214238046320143233253816915240906966932525538310769109229474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1612_1600 : bothSeg evalE (oGrid.idx 1612) (oGrid.dm 1612) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1612) oGrid.kl oGrid.kr 400 1600 ⟨false, 370236142727925214238046320143233253816915240906966932525538310769109229474⟩ ⟨false, 0⟩ ⟨false, 559680028062292142236512225510146798020340019272175247242922052303331496886⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1612_2000 : bothSeg evalE (oGrid.idx 1612) (oGrid.dm 1612) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1612) oGrid.kl oGrid.kr 400 2000 ⟨false, 559680028062292142236512225510146798020340019272175247242922052303331496886⟩ ⟨false, 0⟩ ⟨false, 794910218089566810033352064959422088703274473288472747986026418073525115322⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1612_2400 : bothLoop evalE (oGrid.idx 1612) (oGrid.dm 1612) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1612) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 794910218089566810033352064959422088703274473288472747986026418073525115322⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1612 : oGrid.row evalE 1612 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1612_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1612_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1612_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1612_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1612_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1612_2000).1 (bothLoop_sound b_1612_2400).1))))))

theorem n_row_1612 : nGrid.row evalE 1612 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1612_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1612_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1612_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1612_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1612_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1612_2000).2 (bothLoop_sound b_1612_2400).2))))))

theorem b_1613_0 : bothSeg evalE (oGrid.idx 1613) (oGrid.dm 1613) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1613) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61336681950123986062583149829366283935252883482990705734269566734993141886⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1613_400 : bothSeg evalE (oGrid.idx 1613) (oGrid.dm 1613) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1613) oGrid.kl oGrid.kr 400 400 ⟨false, 61336681950123986062583149829366283935252883482990705734269566734993141886⟩ ⟨false, 0⟩ ⟨false, 128087709508531696559318788754896013907795203250218356625753601513916609092⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1613_800 : bothSeg evalE (oGrid.idx 1613) (oGrid.dm 1613) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1613) oGrid.kl oGrid.kr 400 800 ⟨false, 128087709508531696559318788754896013907795203250218356625753601513916609092⟩ ⟨false, 0⟩ ⟨false, 227946649601367916059659302683315238361584742037024860144491318838483986032⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1613_1200 : bothSeg evalE (oGrid.idx 1613) (oGrid.dm 1613) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1613) oGrid.kl oGrid.kr 400 1200 ⟨false, 227946649601367916059659302683315238361584742037024860144491318838483986032⟩ ⟨false, 0⟩ ⟨false, 370948725143291573429174476884104793149445341555717224549606418533413713648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1613_1600 : bothSeg evalE (oGrid.idx 1613) (oGrid.dm 1613) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1613) oGrid.kl oGrid.kr 400 1600 ⟨false, 370948725143291573429174476884104793149445341555717224549606418533413713648⟩ ⟨false, 0⟩ ⟨false, 560661909816435644920698014637567290864226315427850162165234657370348997142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1613_2000 : bothSeg evalE (oGrid.idx 1613) (oGrid.dm 1613) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1613) oGrid.kl oGrid.kr 400 2000 ⟨false, 560661909816435644920698014637567290864226315427850162165234657370348997142⟩ ⟨false, 0⟩ ⟨false, 796132803176400394918353210720105358952532737275726041785283060149851532138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1613_2400 : bothLoop evalE (oGrid.idx 1613) (oGrid.dm 1613) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1613) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 796132803176400394918353210720105358952532737275726041785283060149851532138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1613 : oGrid.row evalE 1613 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1613_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1613_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1613_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1613_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1613_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1613_2000).1 (bothLoop_sound b_1613_2400).1))))))

theorem n_row_1613 : nGrid.row evalE 1613 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1613_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1613_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1613_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1613_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1613_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1613_2000).2 (bothLoop_sound b_1613_2400).2))))))

theorem b_1614_0 : bothSeg evalE (oGrid.idx 1614) (oGrid.dm 1614) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1614) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61119479067727360192880430253659506090974163434548424922140179391835460468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1614_400 : bothSeg evalE (oGrid.idx 1614) (oGrid.dm 1614) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1614) oGrid.kl oGrid.kr 400 400 ⟨false, 61119479067727360192880430253659506090974163434548424922140179391835460468⟩ ⟨false, 0⟩ ⟨false, 128171494149956730725693575176451433580178946743029392864506318886413687698⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1614_800 : bothSeg evalE (oGrid.idx 1614) (oGrid.dm 1614) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1614) oGrid.kl oGrid.kr 400 800 ⟨false, 128171494149956730725693575176451433580178946743029392864506318886413687698⟩ ⟨false, 0⟩ ⟨false, 228372343433882122907860271047005884665241570902944106079051236800230393694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1614_1200 : bothSeg evalE (oGrid.idx 1614) (oGrid.dm 1614) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1614) oGrid.kl oGrid.kr 400 1200 ⟨false, 228372343433882122907860271047005884665241570902944106079051236800230393694⟩ ⟨false, 0⟩ ⟨false, 371678597637323698218127124791191871158123136111838047113628740377816582940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1614_1600 : bothSeg evalE (oGrid.idx 1614) (oGrid.dm 1614) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1614) oGrid.kl oGrid.kr 400 1600 ⟨false, 371678597637323698218127124791191871158123136111838047113628740377816582940⟩ ⟨false, 0⟩ ⟨false, 561661088935744884509200101511967323790195065504418520617749965275472919420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1614_2000 : bothSeg evalE (oGrid.idx 1614) (oGrid.dm 1614) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1614) oGrid.kl oGrid.kr 400 2000 ⟨false, 561661088935744884509200101511967323790195065504418520617749965275472919420⟩ ⟨false, 0⟩ ⟨false, 797372710835852971012974771653190421270963562472903235620763800608863480848⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1614_2400 : bothLoop evalE (oGrid.idx 1614) (oGrid.dm 1614) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1614) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 797372710835852971012974771653190421270963562472903235620763800608863480848⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1614 : oGrid.row evalE 1614 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1614_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1614_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1614_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1614_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1614_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1614_2000).1 (bothLoop_sound b_1614_2400).1))))))

theorem n_row_1614 : nGrid.row evalE 1614 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1614_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1614_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1614_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1614_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1614_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1614_2000).2 (bothLoop_sound b_1614_2400).2))))))

theorem b_1615_0 : bothSeg evalE (oGrid.idx 1615) (oGrid.dm 1615) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1615) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60915017424165208593457770839136357259735405869413024111670504369826847620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1615_400 : bothSeg evalE (oGrid.idx 1615) (oGrid.dm 1615) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1615) oGrid.kl oGrid.kr 400 400 ⟨false, 60915017424165208593457770839136357259735405869413024111670504369826847620⟩ ⟨false, 0⟩ ⟨false, 128272801666874846909361728095825906943950637345072077902501714087277898694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1615_800 : bothSeg evalE (oGrid.idx 1615) (oGrid.dm 1615) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1615) oGrid.kl oGrid.kr 400 800 ⟨false, 128272801666874846909361728095825906943950637345072077902501714087277898694⟩ ⟨false, 0⟩ ⟨false, 228815495963647585456923370837396528430596703488810270787462746928841642754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1615_1200 : bothSeg evalE (oGrid.idx 1615) (oGrid.dm 1615) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1615) oGrid.kl oGrid.kr 400 1200 ⟨false, 228815495963647585456923370837396528430596703488810270787462746928841642754⟩ ⟨false, 0⟩ ⟨false, 372425905653448862280316193571088187622460437840079519771444582048687627830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1615_1600 : bothSeg evalE (oGrid.idx 1615) (oGrid.dm 1615) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1615) oGrid.kl oGrid.kr 400 1600 ⟨false, 372425905653448862280316193571088187622460437840079519771444582048687627830⟩ ⟨false, 0⟩ ⟨false, 562677710816930704544610499705878439348384756466840244351284291014494497808⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1615_2000 : bothSeg evalE (oGrid.idx 1615) (oGrid.dm 1615) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1615) oGrid.kl oGrid.kr 400 2000 ⟨false, 562677710816930704544610499705878439348384756466840244351284291014494497808⟩ ⟨false, 0⟩ ⟨false, 798630086412943547749631080624958247702054425068438323577496710489014983046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1615_2400 : bothLoop evalE (oGrid.idx 1615) (oGrid.dm 1615) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1615) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 798630086412943547749631080624958247702054425068438323577496710489014983046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1615 : oGrid.row evalE 1615 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1615_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1615_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1615_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1615_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1615_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1615_2000).1 (bothLoop_sound b_1615_2400).1))))))

theorem n_row_1615 : nGrid.row evalE 1615 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1615_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1615_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1615_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1615_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1615_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1615_2000).2 (bothLoop_sound b_1615_2400).2))))))

theorem b_1616_0 : bothSeg evalE (oGrid.idx 1616) (oGrid.dm 1616) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1616) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60723610365184509668981309568258116110434918493384793759224658860911499482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1616_400 : bothSeg evalE (oGrid.idx 1616) (oGrid.dm 1616) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1616) oGrid.kl oGrid.kr 400 400 ⟨false, 60723610365184509668981309568258116110434918493384793759224658860911499482⟩ ⟨false, 0⟩ ⟨false, 128391751069590935628393696088582808733574537860148301766042696611255098590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1616_800 : bothSeg evalE (oGrid.idx 1616) (oGrid.dm 1616) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1616) oGrid.kl oGrid.kr 400 800 ⟨false, 128391751069590935628393696088582808733574537860148301766042696611255098590⟩ ⟨false, 0⟩ ⟨false, 229276226231160702582323678333280375749203276124504463662005257847437559378⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1616_1200 : bothSeg evalE (oGrid.idx 1616) (oGrid.dm 1616) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1616) oGrid.kl oGrid.kr 400 1200 ⟨false, 229276226231160702582323678333280375749203276124504463662005257847437559378⟩ ⟨false, 0⟩ ⟨false, 373190768211301740448638208002461227395670732710791160919022253170617018980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1616_1600 : bothSeg evalE (oGrid.idx 1616) (oGrid.dm 1616) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1616) oGrid.kl oGrid.kr 400 1600 ⟨false, 373190768211301740448638208002461227395670732710791160919022253170617018980⟩ ⟨false, 0⟩ ⟨false, 563711894433001082605999558463254740529707747209292259569602707317647478644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1616_2000 : bothSeg evalE (oGrid.idx 1616) (oGrid.dm 1616) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1616) oGrid.kl oGrid.kr 400 2000 ⟨false, 563711894433001082605999558463254740529707747209292259569602707317647478644⟩ ⟨false, 0⟩ ⟨false, 799905048829058612961400613559075110071865768649383701769613773780087625332⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1616_2400 : bothLoop evalE (oGrid.idx 1616) (oGrid.dm 1616) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1616) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 799905048829058612961400613559075110071865768649383701769613773780087625332⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1616 : oGrid.row evalE 1616 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1616_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1616_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1616_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1616_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1616_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1616_2000).1 (bothLoop_sound b_1616_2400).1))))))

theorem n_row_1616 : nGrid.row evalE 1616 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1616_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1616_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1616_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1616_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1616_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1616_2000).2 (bothLoop_sound b_1616_2400).2))))))

theorem b_1617_0 : bothSeg evalE (oGrid.idx 1617) (oGrid.dm 1617) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1617) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60545541628088889114758947134217364213805725912175205531262255139222529284⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1617_400 : bothSeg evalE (oGrid.idx 1617) (oGrid.dm 1617) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1617) oGrid.kl oGrid.kr 400 400 ⟨false, 60545541628088889114758947134217364213805725912175205531262255139222529284⟩ ⟨false, 0⟩ ⟨false, 128528434521115725612234644130993915836581449902212816585923083681072645686⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1617_800 : bothSeg evalE (oGrid.idx 1617) (oGrid.dm 1617) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1617) oGrid.kl oGrid.kr 400 800 ⟨false, 128528434521115725612234644130993915836581449902212816585923083681072645686⟩ ⟨false, 0⟩ ⟨false, 229754626429635256496473467736425557057779380288457009975131377145711091838⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1617_1200 : bothSeg evalE (oGrid.idx 1617) (oGrid.dm 1617) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1617) oGrid.kl oGrid.kr 400 1200 ⟨false, 229754626429635256496473467736425557057779380288457009975131377145711091838⟩ ⟨false, 0⟩ ⟨false, 373973277483312822999431244535233840548287988088827186351915279693649113074⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1617_1600 : bothSeg evalE (oGrid.idx 1617) (oGrid.dm 1617) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1617) oGrid.kl oGrid.kr 400 1600 ⟨false, 373973277483312822999431244535233840548287988088827186351915279693649113074⟩ ⟨false, 0⟩ ⟨false, 564763731909849397542577724487646836870106038245735102140862852898450215040⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1617_2000 : bothSeg evalE (oGrid.idx 1617) (oGrid.dm 1617) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1617) oGrid.kl oGrid.kr 400 2000 ⟨false, 564763731909849397542577724487646836870106038245735102140862852898450215040⟩ ⟨false, 0⟩ ⟨false, 801197690158540323637805137308635923590133772746169586419158932057118676714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1617_2400 : bothLoop evalE (oGrid.idx 1617) (oGrid.dm 1617) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1617) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 801197690158540323637805137308635923590133772746169586419158932057118676714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1617 : oGrid.row evalE 1617 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1617_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1617_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1617_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1617_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1617_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1617_2000).1 (bothLoop_sound b_1617_2400).1))))))

theorem n_row_1617 : nGrid.row evalE 1617 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1617_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1617_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1617_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1617_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1617_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1617_2000).2 (bothLoop_sound b_1617_2400).2))))))

theorem b_1618_0 : bothSeg evalE (oGrid.idx 1618) (oGrid.dm 1618) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1618) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60381075782460039863111823696751351648555931683291725641183803084899435492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1618_400 : bothSeg evalE (oGrid.idx 1618) (oGrid.dm 1618) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1618) oGrid.kl oGrid.kr 400 400 ⟨false, 60381075782460039863111823696751351648555931683291725641183803084899435492⟩ ⟨false, 0⟩ ⟨false, 128682923996943530653856990136252611685438919598037489391960048366392764770⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1618_800 : bothSeg evalE (oGrid.idx 1618) (oGrid.dm 1618) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1618) oGrid.kl oGrid.kr 400 800 ⟨false, 128682923996943530653856990136252611685438919598037489391960048366392764770⟩ ⟨false, 0⟩ ⟨false, 230250768564780052482639129557190844874213970993463235381234715839439637804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1618_1200 : bothSeg evalE (oGrid.idx 1618) (oGrid.dm 1618) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1618) oGrid.kl oGrid.kr 400 1200 ⟨false, 230250768564780052482639129557190844874213970993463235381234715839439637804⟩ ⟨false, 0⟩ ⟨false, 374773505454485869258177368141661619253844262592824001348155416856733178172⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1618_1600 : bothSeg evalE (oGrid.idx 1618) (oGrid.dm 1618) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1618) oGrid.kl oGrid.kr 400 1600 ⟨false, 374773505454485869258177368141661619253844262592824001348155416856733178172⟩ ⟨false, 0⟩ ⟨false, 565833295186031736235943745953922444719463283029590190043475410147635664932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1618_2000 : bothSeg evalE (oGrid.idx 1618) (oGrid.dm 1618) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1618) oGrid.kl oGrid.kr 400 2000 ⟨false, 565833295186031736235943745953922444719463283029590190043475410147635664932⟩ ⟨false, 0⟩ ⟨false, 802508082288463736245727094629981944940470422810165414653919490188352106164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1618_2400 : bothLoop evalE (oGrid.idx 1618) (oGrid.dm 1618) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1618) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 802508082288463736245727094629981944940470422810165414653919490188352106164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1618 : oGrid.row evalE 1618 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1618_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1618_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1618_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1618_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1618_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1618_2000).1 (bothLoop_sound b_1618_2400).1))))))

theorem n_row_1618 : nGrid.row evalE 1618 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1618_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1618_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1618_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1618_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1618_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1618_2000).2 (bothLoop_sound b_1618_2400).2))))))

theorem b_1619_0 : bothSeg evalE (oGrid.idx 1619) (oGrid.dm 1619) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1619) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60230450032322280566246867668381872768161214514346678853986554553260202602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1619_400 : bothSeg evalE (oGrid.idx 1619) (oGrid.dm 1619) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1619) oGrid.kl oGrid.kr 400 400 ⟨false, 60230450032322280566246867668381872768161214514346678853986554553260202602⟩ ⟨false, 0⟩ ⟨false, 128855267707143991073654179402351673472250265508911395731191978256443236360⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1619_800 : bothSeg evalE (oGrid.idx 1619) (oGrid.dm 1619) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1619) oGrid.kl oGrid.kr 400 800 ⟨false, 128855267707143991073654179402351673472250265508911395731191978256443236360⟩ ⟨false, 0⟩ ⟨false, 230764700876890553614247634775350771415465852314825415670376431997846934590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1619_1200 : bothSeg evalE (oGrid.idx 1619) (oGrid.dm 1619) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1619) oGrid.kl oGrid.kr 400 1200 ⟨false, 230764700876890553614247634775350771415465852314825415670376431997846934590⟩ ⟨false, 0⟩ ⟨false, 375591500344489356597846294784715426640523590816717491370059152056289623204⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1619_1600 : bothSeg evalE (oGrid.idx 1619) (oGrid.dm 1619) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1619) oGrid.kl oGrid.kr 400 1600 ⟨false, 375591500344489356597846294784715426640523590816717491370059152056289623204⟩ ⟨false, 0⟩ ⟨false, 566920632434858195963629988622318907506740776062809372286821249523315574052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1619_2000 : bothSeg evalE (oGrid.idx 1619) (oGrid.dm 1619) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1619) oGrid.kl oGrid.kr 400 2000 ⟨false, 566920632434858195963629988622318907506740776062809372286821249523315574052⟩ ⟨false, 0⟩ ⟨false, 803836273340728032688324682605821479615727742787060089550394816257367422856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1619_2400 : bothLoop evalE (oGrid.idx 1619) (oGrid.dm 1619) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1619) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 803836273340728032688324682605821479615727742787060089550394816257367422856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1619 : oGrid.row evalE 1619 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1619_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1619_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1619_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1619_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1619_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1619_2000).1 (bothLoop_sound b_1619_2400).1))))))

theorem n_row_1619 : nGrid.row evalE 1619 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1619_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1619_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1619_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1619_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1619_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1619_2000).2 (bothLoop_sound b_1619_2400).2))))))

theorem b_1620_0 : bothSeg evalE (oGrid.idx 1620) (oGrid.dm 1620) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1620) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60093875038323670177273624687461796202035008911125628966927643429858689022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1620_400 : bothSeg evalE (oGrid.idx 1620) (oGrid.dm 1620) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1620) oGrid.kl oGrid.kr 400 400 ⟨false, 60093875038323670177273624687461796202035008911125628966927643429858689022⟩ ⟨false, 0⟩ ⟨false, 129045488874205015340790036461634774848472877965416140217431071502897084610⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1620_800 : bothSeg evalE (oGrid.idx 1620) (oGrid.dm 1620) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1620) oGrid.kl oGrid.kr 400 800 ⟨false, 129045488874205015340790036461634774848472877965416140217431071502897084610⟩ ⟨false, 0⟩ ⟨false, 231296446618691716004133408346114072977258344925661544458266403436638106896⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1620_1200 : bothSeg evalE (oGrid.idx 1620) (oGrid.dm 1620) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1620) oGrid.kl oGrid.kr 400 1200 ⟨false, 231296446618691716004133408346114072977258344925661544458266403436638106896⟩ ⟨false, 0⟩ ⟨false, 376427285385499130373581450945963888266690923697540101503934344694440205388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1620_1600 : bothSeg evalE (oGrid.idx 1620) (oGrid.dm 1620) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1620) oGrid.kl oGrid.kr 400 1600 ⟨false, 376427285385499130373581450945963888266690923697540101503934344694440205388⟩ ⟨false, 0⟩ ⟨false, 568025766842235387907460636911515054115438571704383115383763576033270716278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1620_2000 : bothSeg evalE (oGrid.idx 1620) (oGrid.dm 1620) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1620) oGrid.kl oGrid.kr 400 2000 ⟨false, 568025766842235387907460636911515054115438571704383115383763576033270716278⟩ ⟨false, 0⟩ ⟨false, 805182286449898947445608462722139777227178249267910515952893659868427981482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1620_2400 : bothLoop evalE (oGrid.idx 1620) (oGrid.dm 1620) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1620) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 805182286449898947445608462722139777227178249267910515952893659868427981482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1620 : oGrid.row evalE 1620 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1620_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1620_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1620_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1620_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1620_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1620_2000).1 (bothLoop_sound b_1620_2400).1))))))

theorem n_row_1620 : nGrid.row evalE 1620 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1620_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1620_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1620_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1620_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1620_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1620_2000).2 (bothLoop_sound b_1620_2400).2))))))

theorem b_1621_0 : bothSeg evalE (oGrid.idx 1621) (oGrid.dm 1621) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1621) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59971546962050922633544658134510102043593875726074501038658100141723047362⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1621_400 : bothSeg evalE (oGrid.idx 1621) (oGrid.dm 1621) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1621) oGrid.kl oGrid.kr 400 400 ⟨false, 59971546962050922633544658134510102043593875726074501038658100141723047362⟩ ⟨false, 0⟩ ⟨false, 129253595833320258184004279164076132228268511588435943062031693705910608958⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1621_800 : bothSeg evalE (oGrid.idx 1621) (oGrid.dm 1621) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1621) oGrid.kl oGrid.kr 400 800 ⟨false, 129253595833320258184004279164076132228268511588435943062031693705910608958⟩ ⟨false, 0⟩ ⟨false, 231846014155625360914566295941460665574215396349620317128429303263130111460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1621_1200 : bothSeg evalE (oGrid.idx 1621) (oGrid.dm 1621) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1621) oGrid.kl oGrid.kr 400 1200 ⟨false, 231846014155625360914566295941460665574215396349620317128429303263130111460⟩ ⟨false, 0⟩ ⟨false, 377280868922485591123721013229054918886921553785258172482658338269275017748⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1621_1600 : bothSeg evalE (oGrid.idx 1621) (oGrid.dm 1621) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1621) oGrid.kl oGrid.kr 400 1600 ⟨false, 377280868922485591123721013229054918886921553785258172482658338269275017748⟩ ⟨false, 0⟩ ⟨false, 569148706706953478136529644038112270910352493949207605006234504665282632510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1621_2000 : bothSeg evalE (oGrid.idx 1621) (oGrid.dm 1621) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1621) oGrid.kl oGrid.kr 400 2000 ⟨false, 569148706706953478136529644038112270910352493949207605006234504665282632510⟩ ⟨false, 0⟩ ⟨false, 806546129863495732226633713049335444464055934233751596671342336617387546720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1621_2400 : bothLoop evalE (oGrid.idx 1621) (oGrid.dm 1621) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1621) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 806546129863495732226633713049335444464055934233751596671342336617387546720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1621 : oGrid.row evalE 1621 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1621_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1621_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1621_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1621_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1621_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1621_2000).1 (bothLoop_sound b_1621_2400).1))))))

theorem n_row_1621 : nGrid.row evalE 1621 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1621_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1621_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1621_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1621_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1621_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1621_2000).2 (bothLoop_sound b_1621_2400).2))))))

theorem b_1622_0 : bothSeg evalE (oGrid.idx 1622) (oGrid.dm 1622) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1622) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59863618728072974125021689211368734096910881982192610204439430555326757524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1622_400 : bothSeg evalE (oGrid.idx 1622) (oGrid.dm 1622) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1622) oGrid.kl oGrid.kr 400 400 ⟨false, 59863618728072974125021689211368734096910881982192610204439430555326757524⟩ ⟨false, 0⟩ ⟨false, 129479558949554749001526955833645117502640511777008900049553891640545338222⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1622_800 : bothSeg evalE (oGrid.idx 1622) (oGrid.dm 1622) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1622) oGrid.kl oGrid.kr 400 800 ⟨false, 129479558949554749001526955833645117502640511777008900049553891640545338222⟩ ⟨false, 0⟩ ⟨false, 232413373883015697536557047752778546077884263391053009844579143809269208102⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1622_1200 : bothSeg evalE (oGrid.idx 1622) (oGrid.dm 1622) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1622) oGrid.kl oGrid.kr 400 1200 ⟨false, 232413373883015697536557047752778546077884263391053009844579143809269208102⟩ ⟨false, 0⟩ ⟨false, 378152221330379032844803840259528365494631315391785876888662332947150099788⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1622_1600 : bothSeg evalE (oGrid.idx 1622) (oGrid.dm 1622) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1622) oGrid.kl oGrid.kr 400 1600 ⟨false, 378152221330379032844803840259528365494631315391785876888662332947150099788⟩ ⟨false, 0⟩ ⟨false, 570289422357851379872262306975198338990075712441713894721835921330519198662⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1622_2000 : bothSeg evalE (oGrid.idx 1622) (oGrid.dm 1622) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1622) oGrid.kl oGrid.kr 400 2000 ⟨false, 570289422357851379872262306975198338990075712441713894721835921330519198662⟩ ⟨false, 0⟩ ⟨false, 807927773859156271940919027730325560519431543572762507815998100625365454826⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1622_2400 : bothLoop evalE (oGrid.idx 1622) (oGrid.dm 1622) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1622) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 807927773859156271940919027730325560519431543572762507815998100625365454826⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1622 : oGrid.row evalE 1622 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1622_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1622_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1622_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1622_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1622_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1622_2000).1 (bothLoop_sound b_1622_2400).1))))))

theorem n_row_1622 : nGrid.row evalE 1622 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1622_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1622_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1622_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1622_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1622_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1622_2000).2 (bothLoop_sound b_1622_2400).2))))))

theorem b_1623_0 : bothSeg evalE (oGrid.idx 1623) (oGrid.dm 1623) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1623) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59770228024679347790641311863395211550232380329599189229735850195557528010⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1623_400 : bothSeg evalE (oGrid.idx 1623) (oGrid.dm 1623) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1623) oGrid.kl oGrid.kr 400 400 ⟨false, 59770228024679347790641311863395211550232380329599189229735850195557528010⟩ ⟨false, 0⟩ ⟨false, 129723333036478452609390091327389221723759246069022070068893814387924142964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1623_800 : bothSeg evalE (oGrid.idx 1623) (oGrid.dm 1623) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1623) oGrid.kl oGrid.kr 400 800 ⟨false, 129723333036478452609390091327389221723759246069022070068893814387924142964⟩ ⟨false, 0⟩ ⟨false, 232998480644702778476575821084146853216041657803782827203714287773698702460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1623_1200 : bothSeg evalE (oGrid.idx 1623) (oGrid.dm 1623) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1623) oGrid.kl oGrid.kr 400 1200 ⟨false, 232998480644702778476575821084146853216041657803782827203714287773698702460⟩ ⟨false, 0⟩ ⟨false, 379041297432702914377850874285511462023258104762316896300932124809202576958⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1623_1600 : bothSeg evalE (oGrid.idx 1623) (oGrid.dm 1623) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1623) oGrid.kl oGrid.kr 400 1600 ⟨false, 379041297432702914377850874285511462023258104762316896300932124809202576958⟩ ⟨false, 0⟩ ⟨false, 571447868572449879072664692359200995395546982126897076960512275386162089568⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1623_2000 : bothSeg evalE (oGrid.idx 1623) (oGrid.dm 1623) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1623) oGrid.kl oGrid.kr 400 2000 ⟨false, 571447868572449879072664692359200995395546982126897076960512275386162089568⟩ ⟨false, 0⟩ ⟨false, 809327173163270134026341304569271187455888443689681809683509381222174888614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1623_2400 : bothLoop evalE (oGrid.idx 1623) (oGrid.dm 1623) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1623) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 809327173163270134026341304569271187455888443689681809683509381222174888614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1623 : oGrid.row evalE 1623 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1623_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1623_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1623_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1623_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1623_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1623_2000).1 (bothLoop_sound b_1623_2400).1))))))

theorem n_row_1623 : nGrid.row evalE 1623 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1623_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1623_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1623_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1623_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1623_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1623_2000).2 (bothLoop_sound b_1623_2400).2))))))

theorem b_1624_0 : bothSeg evalE (oGrid.idx 1624) (oGrid.dm 1624) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1624) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59691493503124262835635116664639774109579826725719122189355471392036300674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1624_400 : bothSeg evalE (oGrid.idx 1624) (oGrid.dm 1624) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1624) oGrid.kl oGrid.kr 400 400 ⟨false, 59691493503124262835635116664639774109579826725719122189355471392036300674⟩ ⟨false, 0⟩ ⟨false, 129984859484626009639230338033215843266319900655575012822093630121377577502⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1624_800 : bothSeg evalE (oGrid.idx 1624) (oGrid.dm 1624) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1624) oGrid.kl oGrid.kr 400 800 ⟨false, 129984859484626009639230338033215843266319900655575012822093630121377577502⟩ ⟨false, 0⟩ ⟨false, 233601275861502135260628255603556226213256808299143124415276629924398453796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1624_1200 : bothSeg evalE (oGrid.idx 1624) (oGrid.dm 1624) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1624) oGrid.kl oGrid.kr 400 1200 ⟨false, 233601275861502135260628255603556226213256808299143124415276629924398453796⟩ ⟨false, 0⟩ ⟨false, 379948038630033311215023227310634745142621578445411469022001545433615672392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1624_1600 : bothSeg evalE (oGrid.idx 1624) (oGrid.dm 1624) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1624) oGrid.kl oGrid.kr 400 1600 ⟨false, 379948038630033311215023227310634745142621578445411469022001545433615672392⟩ ⟨false, 0⟩ ⟨false, 572623986705410940644675464834051230442845371610082301264376099681158864844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1624_2000 : bothSeg evalE (oGrid.idx 1624) (oGrid.dm 1624) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1624) oGrid.kl oGrid.kr 400 2000 ⟨false, 572623986705410940644675464834051230442845371610082301264376099681158864844⟩ ⟨false, 0⟩ ⟨false, 810744269079437798442566874191704737791937029462690769125333455552577899450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1624_2400 : bothLoop evalE (oGrid.idx 1624) (oGrid.dm 1624) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1624) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 810744269079437798442566874191704737791937029462690769125333455552577899450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1624 : oGrid.row evalE 1624 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1624_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1624_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1624_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1624_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1624_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1624_2000).1 (bothLoop_sound b_1624_2400).1))))))

theorem n_row_1624 : nGrid.row evalE 1624 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1624_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1624_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1624_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1624_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1624_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1624_2000).2 (bothLoop_sound b_1624_2400).2))))))

theorem b_1625_0 : bothSeg evalE (oGrid.idx 1625) (oGrid.dm 1625) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1625) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59627493888001650615306714214913394575918619478245889328050770017156764336⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1625_400 : bothSeg evalE (oGrid.idx 1625) (oGrid.dm 1625) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1625) oGrid.kl oGrid.kr 400 400 ⟨false, 59627493888001650615306714214913394575918619478245889328050770017156764336⟩ ⟨false, 0⟩ ⟨false, 130264039932661977310781420709503180810597625829489160017952249766771964550⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1625_800 : bothSeg evalE (oGrid.idx 1625) (oGrid.dm 1625) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1625) oGrid.kl oGrid.kr 400 800 ⟨false, 130264039932661977310781420709503180810597625829489160017952249766771964550⟩ ⟨false, 0⟩ ⟨false, 234221661202369914579742198970488492268591214857150361415299340041594267362⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1625_1200 : bothSeg evalE (oGrid.idx 1625) (oGrid.dm 1625) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1625) oGrid.kl oGrid.kr 400 1200 ⟨false, 234221661202369914579742198970488492268591214857150361415299340041594267362⟩ ⟨false, 0⟩ ⟨false, 380872346571163868449868273735616587264930823366307519657335227341768240724⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1625_1600 : bothSeg evalE (oGrid.idx 1625) (oGrid.dm 1625) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1625) oGrid.kl oGrid.kr 400 1600 ⟨false, 380872346571163868449868273735616587264930823366307519657335227341768240724⟩ ⟨false, 0⟩ ⟨false, 573817678359702516007644467128416885222818049464601830277701091364633431628⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1625_2000 : bothSeg evalE (oGrid.idx 1625) (oGrid.dm 1625) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1625) oGrid.kl oGrid.kr 400 2000 ⟨false, 573817678359702516007644467128416885222818049464601830277701091364633431628⟩ ⟨false, 0⟩ ⟨false, 812178963159635389053187611469427559383403845954358039715317431782304756630⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1625_2400 : bothLoop evalE (oGrid.idx 1625) (oGrid.dm 1625) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1625) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 812178963159635389053187611469427559383403845954358039715317431782304756630⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1625 : oGrid.row evalE 1625 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1625_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1625_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1625_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1625_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1625_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1625_2000).1 (bothLoop_sound b_1625_2400).1))))))

theorem n_row_1625 : nGrid.row evalE 1625 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1625_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1625_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1625_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1625_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1625_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1625_2000).2 (bothLoop_sound b_1625_2400).2))))))

theorem b_1626_0 : bothSeg evalE (oGrid.idx 1626) (oGrid.dm 1626) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1626) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59578291887390459066146704554014993088031596221435367667791124935575652780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1626_400 : bothSeg evalE (oGrid.idx 1626) (oGrid.dm 1626) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1626) oGrid.kl oGrid.kr 400 400 ⟨false, 59578291887390459066146704554014993088031596221435367667791124935575652780⟩ ⟨false, 0⟩ ⟨false, 130560766131526796366417749456039724296760532200152532908014738403504636986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1626_800 : bothSeg evalE (oGrid.idx 1626) (oGrid.dm 1626) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1626) oGrid.kl oGrid.kr 400 800 ⟨false, 130560766131526796366417749456039724296760532200152532908014738403504636986⟩ ⟨false, 0⟩ ⟨false, 234859528448548741063084266014783962728881728835171322783039823737209629998⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1626_1200 : bothSeg evalE (oGrid.idx 1626) (oGrid.dm 1626) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1626) oGrid.kl oGrid.kr 400 1200 ⟨false, 234859528448548741063084266014783962728881728835171322783039823737209629998⟩ ⟨false, 0⟩ ⟨false, 381814113017251480656532758237384904746052938330195230896491193695229548494⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1626_1600 : bothSeg evalE (oGrid.idx 1626) (oGrid.dm 1626) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1626) oGrid.kl oGrid.kr 400 1600 ⟨false, 381814113017251480656532758237384904746052938330195230896491193695229548494⟩ ⟨false, 0⟩ ⟨false, 575028835250744077793129781292749485722613711366985773587258053487950396644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1626_2000 : bothSeg evalE (oGrid.idx 1626) (oGrid.dm 1626) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1626) oGrid.kl oGrid.kr 400 2000 ⟨false, 575028835250744077793129781292749485722613711366985773587258053487950396644⟩ ⟨false, 0⟩ ⟨false, 813631147068360132181897541544496794281713496325331169683907870346396410126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1626_2400 : bothLoop evalE (oGrid.idx 1626) (oGrid.dm 1626) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1626) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 813631147068360132181897541544496794281713496325331169683907870346396410126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1626 : oGrid.row evalE 1626 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1626_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1626_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1626_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1626_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1626_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1626_2000).1 (bothLoop_sound b_1626_2400).1))))))

theorem n_row_1626 : nGrid.row evalE 1626 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1626_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1626_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1626_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1626_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1626_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1626_2000).2 (bothLoop_sound b_1626_2400).2))))))

theorem b_1627_0 : bothSeg evalE (oGrid.idx 1627) (oGrid.dm 1627) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1627) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59543924958970312583338400094846775639315372287824848887584323885707797654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1627_400 : bothSeg evalE (oGrid.idx 1627) (oGrid.dm 1627) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1627) oGrid.kl oGrid.kr 400 400 ⟨false, 59543924958970312583338400094846775639315372287824848887584323885707797654⟩ ⟨false, 0⟩ ⟨false, 130874905482094092272970719272381518034077916194396531965428787985917160856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1627_800 : bothSeg evalE (oGrid.idx 1627) (oGrid.dm 1627) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1627) oGrid.kl oGrid.kr 400 800 ⟨false, 130874905482094092272970719272381518034077916194396531965428787985917160856⟩ ⟨false, 0⟩ ⟨false, 235514745031224914682789067998279169739897912569707181138870947676917170556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1627_1200 : bothSeg evalE (oGrid.idx 1627) (oGrid.dm 1627) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1627) oGrid.kl oGrid.kr 400 1200 ⟨false, 235514745031224914682789067998279169739897912569707181138870947676917170556⟩ ⟨false, 0⟩ ⟨false, 382773205379473306801187160265847250986902034087840281780767558638126048654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1627_1600 : bothSeg evalE (oGrid.idx 1627) (oGrid.dm 1627) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1627) oGrid.kl oGrid.kr 400 1600 ⟨false, 382773205379473306801187160265847250986902034087840281780767558638126048654⟩ ⟨false, 0⟩ ⟨false, 576257324744063489784069929257992016807121435752318364228699386057821735016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1627_2000 : bothSeg evalE (oGrid.idx 1627) (oGrid.dm 1627) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1627) oGrid.kl oGrid.kr 400 2000 ⟨false, 576257324744063489784069929257992016807121435752318364228699386057821735016⟩ ⟨false, 0⟩ ⟨false, 815100688120287150445909675121411353916324815741369433497131106318941300596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1627_2400 : bothLoop evalE (oGrid.idx 1627) (oGrid.dm 1627) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1627) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 815100688120287150445909675121411353916324815741369433497131106318941300596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1627 : oGrid.row evalE 1627 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1627_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1627_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1627_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1627_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1627_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1627_2000).1 (bothLoop_sound b_1627_2400).1))))))

theorem n_row_1627 : nGrid.row evalE 1627 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1627_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1627_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1627_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1627_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1627_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1627_2000).2 (bothLoop_sound b_1627_2400).2))))))

theorem b_1628_0 : bothSeg evalE (oGrid.idx 1628) (oGrid.dm 1628) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1628) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59524402731913383594955864004974841835532786466793153875481733592683863028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1628_400 : bothSeg evalE (oGrid.idx 1628) (oGrid.dm 1628) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1628) oGrid.kl oGrid.kr 400 400 ⟨false, 59524402731913383594955864004974841835532786466793153875481733592683863028⟩ ⟨false, 0⟩ ⟨false, 131206301579603490047590334115033008919958324376441837426348253156300736560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1628_800 : bothSeg evalE (oGrid.idx 1628) (oGrid.dm 1628) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1628) oGrid.kl oGrid.kr 400 800 ⟨false, 131206301579603490047590334115033008919958324376441837426348253156300736560⟩ ⟨false, 0⟩ ⟨false, 236187154575961122146138566289378583052754966883747423709992545922485284342⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1628_1200 : bothSeg evalE (oGrid.idx 1628) (oGrid.dm 1628) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1628) oGrid.kl oGrid.kr 400 1200 ⟨false, 236187154575961122146138566289378583052754966883747423709992545922485284342⟩ ⟨false, 0⟩ ⟨false, 383749467263459299540461751627445834946741205908099768228799525125604807702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1628_1600 : bothSeg evalE (oGrid.idx 1628) (oGrid.dm 1628) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1628) oGrid.kl oGrid.kr 400 1600 ⟨false, 383749467263459299540461751627445834946741205908099768228799525125604807702⟩ ⟨false, 0⟩ ⟨false, 577502990399729391447943764744390285936385578084477534421350527285006763736⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1628_2000 : bothSeg evalE (oGrid.idx 1628) (oGrid.dm 1628) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1628) oGrid.kl oGrid.kr 400 2000 ⟨false, 577502990399729391447943764744390285936385578084477534421350527285006763736⟩ ⟨false, 0⟩ ⟨false, 816587429824701771221367997248204627694577650468880051668803658936681084094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1628_2400 : bothLoop evalE (oGrid.idx 1628) (oGrid.dm 1628) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1628) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 816587429824701771221367997248204627694577650468880051668803658936681084094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1628 : oGrid.row evalE 1628 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1628_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1628_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1628_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1628_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1628_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1628_2000).1 (bothLoop_sound b_1628_2400).1))))))

theorem n_row_1628 : nGrid.row evalE 1628 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1628_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1628_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1628_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1628_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1628_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1628_2000).2 (bothLoop_sound b_1628_2400).2))))))

theorem b_1629_0 : bothSeg evalE (oGrid.idx 1629) (oGrid.dm 1629) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1629) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59519710211550662297489814499027736995501068708763490474373303226524165384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1629_400 : bothSeg evalE (oGrid.idx 1629) (oGrid.dm 1629) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1629) oGrid.kl oGrid.kr 400 400 ⟨false, 59519710211550662297489814499027736995501068708763490474373303226524165384⟩ ⟨false, 0⟩ ⟨false, 131554776527694118428886274470747623349349666997968567605561782332719680050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1629_800 : bothSeg evalE (oGrid.idx 1629) (oGrid.dm 1629) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1629) oGrid.kl oGrid.kr 400 800 ⟨false, 131554776527694118428886274470747623349349666997968567605561782332719680050⟩ ⟨false, 0⟩ ⟨false, 236876579216729837995193973416848551478507044353437437304505599823225309558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1629_1200 : bothSeg evalE (oGrid.idx 1629) (oGrid.dm 1629) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1629) oGrid.kl oGrid.kr 400 1200 ⟨false, 236876579216729837995193973416848551478507044353437437304505599823225309558⟩ ⟨false, 0⟩ ⟨false, 384742720783325424626161327543685341075953769730854933497004732585184642080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1629_1600 : bothSeg evalE (oGrid.idx 1629) (oGrid.dm 1629) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1629) oGrid.kl oGrid.kr 400 1600 ⟨false, 384742720783325424626161327543685341075953769730854933497004732585184642080⟩ ⟨false, 0⟩ ⟨false, 578765654286384272782996853927625366063541774569045181269081019987302354506⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1629_2000 : bothSeg evalE (oGrid.idx 1629) (oGrid.dm 1629) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1629) oGrid.kl oGrid.kr 400 2000 ⟨false, 578765654286384272782996853927625366063541774569045181269081019987302354506⟩ ⟨false, 0⟩ ⟨false, 818091194199532525459975076951848555737847664251583504106569364059995960526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1629_2400 : bothLoop evalE (oGrid.idx 1629) (oGrid.dm 1629) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1629) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 818091194199532525459975076951848555737847664251583504106569364059995960526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1629 : oGrid.row evalE 1629 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1629_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1629_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1629_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1629_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1629_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1629_2000).1 (bothLoop_sound b_1629_2400).1))))))

theorem n_row_1629 : nGrid.row evalE 1629 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1629_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1629_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1629_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1629_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1629_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1629_2000).2 (bothLoop_sound b_1629_2400).2))))))

theorem b_1630_0 : bothSeg evalE (oGrid.idx 1630) (oGrid.dm 1630) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1630) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59529809894273748442440231800955593233330564439790762057119593741234434896⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1630_400 : bothSeg evalE (oGrid.idx 1630) (oGrid.dm 1630) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1630) oGrid.kl oGrid.kr 400 400 ⟨false, 59529809894273748442440231800955593233330564439790762057119593741234434896⟩ ⟨false, 0⟩ ⟨false, 131920136555040111437438806314659872183071037288386095500214805604140568864⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1630_800 : bothSeg evalE (oGrid.idx 1630) (oGrid.dm 1630) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1630) oGrid.kl oGrid.kr 400 800 ⟨false, 131920136555040111437438806314659872183071037288386095500214805604140568864⟩ ⟨false, 0⟩ ⟨false, 237582825212548723456842380071013178268923827540885195997767344769756743586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1630_1200 : bothSeg evalE (oGrid.idx 1630) (oGrid.dm 1630) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1630) oGrid.kl oGrid.kr 400 1200 ⟨false, 237582825212548723456842380071013178268923827540885195997767344769756743586⟩ ⟨false, 0⟩ ⟨false, 385752772178308878458386920447189678000946312176340541233794932222108936546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1630_1600 : bothSeg evalE (oGrid.idx 1630) (oGrid.dm 1630) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1630) oGrid.kl oGrid.kr 400 1600 ⟨false, 385752772178308878458386920447189678000946312176340541233794932222108936546⟩ ⟨false, 0⟩ ⟨false, 580045122597879547519474175274215580162788421117249665477694566573247050366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1630_2000 : bothSeg evalE (oGrid.idx 1630) (oGrid.dm 1630) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1630) oGrid.kl oGrid.kr 400 2000 ⟨false, 580045122597879547519474175274215580162788421117249665477694566573247050366⟩ ⟨false, 0⟩ ⟨false, 819611787387986144898916097940552193062074303359933045786417303211464752586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1630_2400 : bothLoop evalE (oGrid.idx 1630) (oGrid.dm 1630) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1630) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 819611787387986144898916097940552193062074303359933045786417303211464752586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1630 : oGrid.row evalE 1630 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1630_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1630_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1630_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1630_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1630_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1630_2000).1 (bothLoop_sound b_1630_2400).1))))))

theorem n_row_1630 : nGrid.row evalE 1630 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1630_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1630_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1630_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1630_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1630_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1630_2000).2 (bothLoop_sound b_1630_2400).2))))))

theorem b_1631_0 : bothSeg evalE (oGrid.idx 1631) (oGrid.dm 1631) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1631) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59554646755086592699008200963273644862325414507914969992708969232444786168⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1631_400 : bothSeg evalE (oGrid.idx 1631) (oGrid.dm 1631) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1631) oGrid.kl oGrid.kr 400 400 ⟨false, 59554646755086592699008200963273644862325414507914969992708969232444786168⟩ ⟨false, 0⟩ ⟨false, 132302173855092761837323381255173263655608055494661071896916041919870333100⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1631_800 : bothSeg evalE (oGrid.idx 1631) (oGrid.dm 1631) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1631) oGrid.kl oGrid.kr 400 800 ⟨false, 132302173855092761837323381255173263655608055494661071896916041919870333100⟩ ⟨false, 0⟩ ⟨false, 238305684787222677553777204557732946755974941343861371951762978771563240932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1631_1200 : bothSeg evalE (oGrid.idx 1631) (oGrid.dm 1631) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1631) oGrid.kl oGrid.kr 400 1200 ⟨false, 238305684787222677553777204557732946755974941343861371951762978771563240932⟩ ⟨false, 0⟩ ⟨false, 386779413652509958296751294974082352209510569738318656504769021234790345914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1631_1600 : bothSeg evalE (oGrid.idx 1631) (oGrid.dm 1631) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1631) oGrid.kl oGrid.kr 400 1600 ⟨false, 386779413652509958296751294974082352209510569738318656504769021234790345914⟩ ⟨false, 0⟩ ⟨false, 581341187493017279185357164943901133211081422455042350699114545986580794992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1631_2000 : bothSeg evalE (oGrid.idx 1631) (oGrid.dm 1631) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1631) oGrid.kl oGrid.kr 400 2000 ⟨false, 581341187493017279185357164943901133211081422455042350699114545986580794992⟩ ⟨false, 0⟩ ⟨false, 821149001498289212173717608485884874385884721139399467123596762586749136052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1631_2400 : bothLoop evalE (oGrid.idx 1631) (oGrid.dm 1631) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1631) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 821149001498289212173717608485884874385884721139399467123596762586749136052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1631 : oGrid.row evalE 1631 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1631_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1631_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1631_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1631_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1631_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1631_2000).1 (bothLoop_sound b_1631_2400).1))))))

theorem n_row_1631 : nGrid.row evalE 1631 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1631_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1631_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1631_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1631_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1631_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1631_2000).2 (bothLoop_sound b_1631_2400).2))))))

theorem o_blk_1608 : allFrom (fun j => oGrid.row evalE j) 1608 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1608) o_row_1608 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1609) o_row_1609 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1610) o_row_1610 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1611) o_row_1611 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1612) o_row_1612 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1613) o_row_1613 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1614) o_row_1614 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1615) o_row_1615 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1616) o_row_1616 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1617) o_row_1617 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1618) o_row_1618 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1619) o_row_1619 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1620) o_row_1620 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1621) o_row_1621 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1622) o_row_1622 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1623) o_row_1623 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1624) o_row_1624 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1625) o_row_1625 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1626) o_row_1626 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1627) o_row_1627 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1628) o_row_1628 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1629) o_row_1629 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1630) o_row_1630 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1631) o_row_1631 (allFrom_zero (fun j => oGrid.row evalE j) 1632)))))))))))))))))))))))))

theorem n_blk_1608 : allFrom (fun j => nGrid.row evalE j) 1608 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1608) n_row_1608 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1609) n_row_1609 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1610) n_row_1610 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1611) n_row_1611 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1612) n_row_1612 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1613) n_row_1613 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1614) n_row_1614 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1615) n_row_1615 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1616) n_row_1616 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1617) n_row_1617 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1618) n_row_1618 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1619) n_row_1619 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1620) n_row_1620 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1621) n_row_1621 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1622) n_row_1622 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1623) n_row_1623 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1624) n_row_1624 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1625) n_row_1625 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1626) n_row_1626 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1627) n_row_1627 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1628) n_row_1628 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1629) n_row_1629 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1630) n_row_1630 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1631) n_row_1631 (allFrom_zero (fun j => nGrid.row evalE j) 1632)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
