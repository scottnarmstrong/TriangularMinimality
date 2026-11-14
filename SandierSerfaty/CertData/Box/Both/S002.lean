/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 2 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `48`–`71`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_48_0 : bothSeg evalE (oGrid.idx 48) (oGrid.dm 48) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 48) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4368347896985498196723503063098250882736239593711284282638213144522307621936⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_48_400 : bothSeg evalE (oGrid.idx 48) (oGrid.dm 48) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 48) oGrid.kl oGrid.kr 400 400 ⟨false, 4368347896985498196723503063098250882736239593711284282638213144522307621936⟩ ⟨false, 0⟩ ⟨false, 7033012643908298141134886223025498549172741290155643819908276941889889087422⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_48_800 : bothSeg evalE (oGrid.idx 48) (oGrid.dm 48) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 48) oGrid.kl oGrid.kr 400 800 ⟨false, 7033012643908298141134886223025498549172741290155643819908276941889889087422⟩ ⟨false, 0⟩ ⟨false, 8038548293314624480482703197961293731049447854401077645468726290263878723486⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_48_1200 : bothSeg evalE (oGrid.idx 48) (oGrid.dm 48) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 48) oGrid.kl oGrid.kr 400 1200 ⟨false, 8038548293314624480482703197961293731049447854401077645468726290263878723486⟩ ⟨false, 0⟩ ⟨false, 8228493476398091294216689706385433016695740942872966803122298426524397997270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_48_1600 : bothSeg evalE (oGrid.idx 48) (oGrid.dm 48) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 48) oGrid.kl oGrid.kr 400 1600 ⟨false, 8228493476398091294216689706385433016695740942872966803122298426524397997270⟩ ⟨false, 0⟩ ⟨false, 8058166051573991520322725589741652719037354235458374413371749471260524005006⟩ ⟨false, 171450390254068401426424269840779599049722938469498359267739174938068361446⟩ = true := by
  decide +kernel

theorem b_48_2000 : bothSeg evalE (oGrid.idx 48) (oGrid.dm 48) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 48) oGrid.kl oGrid.kr 400 2000 ⟨false, 8058166051573991520322725589741652719037354235458374413371749471260524005006⟩ ⟨false, 171450390254068401426424269840779599049722938469498359267739174938068361446⟩ ⟨false, 7976071036407285953226746326357541125302360564286653996382375782722221237102⟩ ⟨false, 254160194802315020985588751254815240586491594639943029897575233236183667704⟩ = true := by
  decide +kernel

theorem b_48_2400 : bothLoop evalE (oGrid.idx 48) (oGrid.dm 48) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 48) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7976071036407285953226746326357541125302360564286653996382375782722221237102⟩ ⟨false, 254160194802315020985588751254815240586491594639943029897575233236183667704⟩ = true := by
  decide +kernel

theorem o_row_48 : oGrid.row evalE 48 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_48_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_48_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_48_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_48_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_48_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_48_2000).1 (bothLoop_sound b_48_2400).1))))))

theorem n_row_48 : nGrid.row evalE 48 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_48_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_48_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_48_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_48_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_48_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_48_2000).2 (bothLoop_sound b_48_2400).2))))))

theorem b_49_0 : bothSeg evalE (oGrid.idx 49) (oGrid.dm 49) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 49) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4352881474550893375061199732055197458619027549081751393141277598581428577678⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_49_400 : bothSeg evalE (oGrid.idx 49) (oGrid.dm 49) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 49) oGrid.kl oGrid.kr 400 400 ⟨false, 4352881474550893375061199732055197458619027549081751393141277598581428577678⟩ ⟨false, 0⟩ ⟨false, 7008536535972687523769125803725817217285240428924677977051408619359497720658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_49_800 : bothSeg evalE (oGrid.idx 49) (oGrid.dm 49) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 49) oGrid.kl oGrid.kr 400 800 ⟨false, 7008536535972687523769125803725817217285240428924677977051408619359497720658⟩ ⟨false, 0⟩ ⟨false, 8010620053268611370708203504573314019960209430993991942736079677899946779860⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_49_1200 : bothSeg evalE (oGrid.idx 49) (oGrid.dm 49) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 49) oGrid.kl oGrid.kr 400 1200 ⟨false, 8010620053268611370708203504573314019960209430993991942736079677899946779860⟩ ⟨false, 0⟩ ⟨false, 8199634893510895471578076128638650404134563279457519762519093545464025065648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_49_1600 : bothSeg evalE (oGrid.idx 49) (oGrid.dm 49) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 49) oGrid.kl oGrid.kr 400 1600 ⟨false, 8199634893510895471578076128638650404134563279457519762519093545464025065648⟩ ⟨false, 0⟩ ⟨false, 8029034254925872446662320978529387619356790865289556966317115885351791523132⟩ ⟨false, 171686871056323516519546128937980532550628086828336804076562454357713287252⟩ = true := by
  decide +kernel

theorem b_49_2000 : bothSeg evalE (oGrid.idx 49) (oGrid.dm 49) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 49) oGrid.kl oGrid.kr 400 2000 ⟨false, 8029034254925872446662320978529387619356790865289556966317115885351791523132⟩ ⟨false, 171686871056323516519546128937980532550628086828336804076562454357713287252⟩ ⟨false, 7947419674954082030851253977896068415260629012059292926031698360408604857462⟩ ⟨false, 253920198953938156633985294076590744062689074580140183070445513052502755412⟩ = true := by
  decide +kernel

theorem b_49_2400 : bothLoop evalE (oGrid.idx 49) (oGrid.dm 49) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 49) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7947419674954082030851253977896068415260629012059292926031698360408604857462⟩ ⟨false, 253920198953938156633985294076590744062689074580140183070445513052502755412⟩ = true := by
  decide +kernel

theorem o_row_49 : oGrid.row evalE 49 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_49_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_49_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_49_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_49_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_49_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_49_2000).1 (bothLoop_sound b_49_2400).1))))))

theorem n_row_49 : nGrid.row evalE 49 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_49_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_49_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_49_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_49_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_49_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_49_2000).2 (bothLoop_sound b_49_2400).2))))))

theorem b_50_0 : bothSeg evalE (oGrid.idx 50) (oGrid.dm 50) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 50) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4337460444818041074077108890246429446296448793688832925310142264329058123792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_50_400 : bothSeg evalE (oGrid.idx 50) (oGrid.dm 50) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 50) oGrid.kl oGrid.kr 400 400 ⟨false, 4337460444818041074077108890246429446296448793688832925310142264329058123792⟩ ⟨false, 0⟩ ⟨false, 6984127553532703020936455622140628851446273285493757042921262150703845426232⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_50_800 : bothSeg evalE (oGrid.idx 50) (oGrid.dm 50) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 50) oGrid.kl oGrid.kr 400 800 ⟨false, 6984127553532703020936455622140628851446273285493757042921262150703845426232⟩ ⟨false, 0⟩ ⟨false, 7982765250170712525963092333142986186560905800737275511812056205554509264746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_50_1200 : bothSeg evalE (oGrid.idx 50) (oGrid.dm 50) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 50) oGrid.kl oGrid.kr 400 1200 ⟨false, 7982765250170712525963092333142986186560905800737275511812056205554509264746⟩ ⟨false, 0⟩ ⟨false, 8170851396207179110126787498732611141604324989934060516181633078880572651684⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_50_1600 : bothSeg evalE (oGrid.idx 50) (oGrid.dm 50) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 50) oGrid.kl oGrid.kr 400 1600 ⟨false, 8170851396207179110126787498732611141604324989934060516181633078880572651684⟩ ⟨false, 0⟩ ⟨false, 7999979880849562155522468818586582950369304188774804839632544826333810631868⟩ ⟨false, 171922235345171510813211913067131984644358458604952626945648000814809856230⟩ = true := by
  decide +kernel

theorem b_50_2000 : bothSeg evalE (oGrid.idx 50) (oGrid.dm 50) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 50) oGrid.kl oGrid.kr 400 2000 ⟨false, 7999979880849562155522468818586582950369304188774804839632544826333810631868⟩ ⟨false, 171922235345171510813211913067131984644358458604952626945648000814809856230⟩ ⟨false, 7918843422212837749320117291305431319196054729825703719624295240519425418706⟩ ⟨false, 253681172080808791627400089924664498217596235197335629130842199033997005080⟩ = true := by
  decide +kernel

theorem b_50_2400 : bothLoop evalE (oGrid.idx 50) (oGrid.dm 50) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 50) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7918843422212837749320117291305431319196054729825703719624295240519425418706⟩ ⟨false, 253681172080808791627400089924664498217596235197335629130842199033997005080⟩ = true := by
  decide +kernel

theorem o_row_50 : oGrid.row evalE 50 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_50_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_50_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_50_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_50_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_50_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_50_2000).1 (bothLoop_sound b_50_2400).1))))))

theorem n_row_50 : nGrid.row evalE 50 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_50_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_50_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_50_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_50_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_50_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_50_2000).2 (bothLoop_sound b_50_2400).2))))))

theorem b_51_0 : bothSeg evalE (oGrid.idx 51) (oGrid.dm 51) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 51) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4322084680316188198477693563964854203178852982113232919740771690468152515638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_51_400 : bothSeg evalE (oGrid.idx 51) (oGrid.dm 51) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 51) oGrid.kl oGrid.kr 400 400 ⟨false, 4322084680316188198477693563964854203178852982113232919740771690468152515638⟩ ⟨false, 0⟩ ⟨false, 6959785478907156643799830274224667396632458459930066694199483765087287506186⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_51_800 : bothSeg evalE (oGrid.idx 51) (oGrid.dm 51) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 51) oGrid.kl oGrid.kr 400 800 ⟨false, 6959785478907156643799830274224667396632458459930066694199483765087287506186⟩ ⟨false, 0⟩ ⟨false, 7954983657132934845218185020404056790193684169088036752302330593539507493508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_51_1200 : bothSeg evalE (oGrid.idx 51) (oGrid.dm 51) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 51) oGrid.kl oGrid.kr 400 1200 ⟨false, 7954983657132934845218185020404056790193684169088036752302330593539507493508⟩ ⟨false, 0⟩ ⟨false, 8142142767644742180522173127544670263134982001733012402802448639533331546520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_51_1600 : bothSeg evalE (oGrid.idx 51) (oGrid.dm 51) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 51) oGrid.kl oGrid.kr 400 1600 ⟨false, 8142142767644742180522173127544670263134982001733012402802448639533331546520⟩ ⟨false, 0⟩ ⟨false, 7971002717081116327858781640967402903217294367632496701575831383343793273230⟩ ⟨false, 172155306821359959934624609551863936825928477622054791637714602711212674118⟩ = true := by
  decide +kernel

theorem b_51_2000 : bothSeg evalE (oGrid.idx 51) (oGrid.dm 51) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 51) oGrid.kl oGrid.kr 400 2000 ⟨false, 7971002717081116327858781640967402903217294367632496701575831383343793273230⟩ ⟨false, 172155306821359959934624609551863936825928477622054791637714602711212674118⟩ ⟨false, 7890342037863480985114932291120391446967243959842719346860132749806309358634⟩ ⟨false, 253441861046927782214573450834507351620771741388799598588145814637328526404⟩ = true := by
  decide +kernel

theorem b_51_2400 : bothLoop evalE (oGrid.idx 51) (oGrid.dm 51) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 51) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7890342037863480985114932291120391446967243959842719346860132749806309358634⟩ ⟨false, 253441861046927782214573450834507351620771741388799598588145814637328526404⟩ = true := by
  decide +kernel

theorem o_row_51 : oGrid.row evalE 51 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_51_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_51_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_51_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_51_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_51_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_51_2000).1 (bothLoop_sound b_51_2400).1))))))

theorem n_row_51 : nGrid.row evalE 51 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_51_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_51_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_51_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_51_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_51_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_51_2000).2 (bothLoop_sound b_51_2400).2))))))

theorem b_52_0 : bothSeg evalE (oGrid.idx 52) (oGrid.dm 52) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 52) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4306754082873378387732359524592778979396474795750565049086223143506557338324⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_52_400 : bothSeg evalE (oGrid.idx 52) (oGrid.dm 52) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 52) oGrid.kl oGrid.kr 400 400 ⟨false, 4306754082873378387732359524592778979396474795750565049086223143506557338324⟩ ⟨false, 0⟩ ⟨false, 6935510210324317931210317401133703227965918337807296909906485049245116330076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_52_800 : bothSeg evalE (oGrid.idx 52) (oGrid.dm 52) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 52) oGrid.kl oGrid.kr 400 800 ⟨false, 6935510210324317931210317401133703227965918337807296909906485049245116330076⟩ ⟨false, 0⟩ ⟨false, 7927275163843633914643656927768873983829327738973937209449864512432787373814⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_52_1200 : bothSeg evalE (oGrid.idx 52) (oGrid.dm 52) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 52) oGrid.kl oGrid.kr 400 1200 ⟨false, 7927275163843633914643656927768873983829327738973937209449864512432787373814⟩ ⟨false, 0⟩ ⟨false, 8113508901561678305852446083360554616074957083051009997467962929507736337588⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_52_1600 : bothSeg evalE (oGrid.idx 52) (oGrid.dm 52) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 52) oGrid.kl oGrid.kr 400 1600 ⟨false, 8113508901561678305852446083360554616074957083051009997467962929507736337588⟩ ⟨false, 0⟩ ⟨false, 7942102611720800337313716510856741360009533275801960725438054156125699495920⟩ ⟨false, 172386159263899494958024687528639611007312448070363277179805742980275131252⟩ = true := by
  decide +kernel

theorem b_52_2000 : bothSeg evalE (oGrid.idx 52) (oGrid.dm 52) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 52) oGrid.kl oGrid.kr 400 2000 ⟨false, 7942102611720800337313716510856741360009533275801960725438054156125699495920⟩ ⟨false, 172386159263899494958024687528639611007312448070363277179805742980275131252⟩ ⟨false, 7861915428395469201172247932909027269804260690563914816876617136326272931862⟩ ⟨false, 253202329162546004714533961536514861752409360033070703337587809045621191158⟩ = true := by
  decide +kernel

theorem b_52_2400 : bothLoop evalE (oGrid.idx 52) (oGrid.dm 52) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 52) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7861915428395469201172247932909027269804260690563914816876617136326272931862⟩ ⟨false, 253202329162546004714533961536514861752409360033070703337587809045621191158⟩ = true := by
  decide +kernel

theorem o_row_52 : oGrid.row evalE 52 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_52_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_52_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_52_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_52_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_52_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_52_2000).1 (bothLoop_sound b_52_2400).1))))))

theorem n_row_52 : nGrid.row evalE 52 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_52_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_52_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_52_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_52_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_52_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_52_2000).2 (bothLoop_sound b_52_2400).2))))))

theorem b_53_0 : bothSeg evalE (oGrid.idx 53) (oGrid.dm 53) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 53) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4291468501910314371857889063313506808318857586675057925727720976512445057490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_53_400 : bothSeg evalE (oGrid.idx 53) (oGrid.dm 53) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 53) oGrid.kl oGrid.kr 400 400 ⟨false, 4291468501910314371857889063313506808318857586675057925727720976512445057490⟩ ⟨false, 0⟩ ⟨false, 6911301647649094274022053905245268293824166230619330354917482911842547052378⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_53_800 : bothSeg evalE (oGrid.idx 53) (oGrid.dm 53) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 53) oGrid.kl oGrid.kr 400 800 ⟨false, 6911301647649094274022053905245268293824166230619330354917482911842547052378⟩ ⟨false, 0⟩ ⟨false, 7899639707668244126919522784634576535624089993405103193787892407011911654362⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_53_1200 : bothSeg evalE (oGrid.idx 53) (oGrid.dm 53) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 53) oGrid.kl oGrid.kr 400 1200 ⟨false, 7899639707668244126919522784634576535624089993405103193787892407011911654362⟩ ⟨false, 0⟩ ⟨false, 8084949741837850844840075313949219311972706714075339222813696074586520687372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_53_1600 : bothSeg evalE (oGrid.idx 53) (oGrid.dm 53) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 53) oGrid.kl oGrid.kr 400 1600 ⟨false, 8084949741837850844840075313949219311972706714075339222813696074586520687372⟩ ⟨false, 0⟩ ⟨false, 7913279479428946798805874636439050864941030099761943719493153244848142667840⟩ ⟨false, 172615858562603471416115432047307178661585928927070067826153826306876828982⟩ = true := by
  decide +kernel

theorem b_53_2000 : bothSeg evalE (oGrid.idx 53) (oGrid.dm 53) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 53) oGrid.kl oGrid.kr 400 2000 ⟨false, 7913279479428946798805874636439050864941030099761943719493153244848142667840⟩ ⟨false, 172615858562603471416115432047307178661585928927070067826153826306876828982⟩ ⟨false, 7833563464368320771057373142926567132855636253036413375188516943469267156532⟩ ⟨false, 252963695364022987992353708527153755549671279747366719276220086603959529804⟩ = true := by
  decide +kernel

theorem b_53_2400 : bothLoop evalE (oGrid.idx 53) (oGrid.dm 53) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 53) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7833563464368320771057373142926567132855636253036413375188516943469267156532⟩ ⟨false, 252963695364022987992353708527153755549671279747366719276220086603959529804⟩ = true := by
  decide +kernel

theorem o_row_53 : oGrid.row evalE 53 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_53_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_53_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_53_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_53_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_53_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_53_2000).1 (bothLoop_sound b_53_2400).1))))))

theorem n_row_53 : nGrid.row evalE 53 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_53_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_53_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_53_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_53_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_53_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_53_2000).2 (bothLoop_sound b_53_2400).2))))))

theorem b_54_0 : bothSeg evalE (oGrid.idx 54) (oGrid.dm 54) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 54) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4276227820942122502177112779374427738116017997320360164110968663578943052320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_54_400 : bothSeg evalE (oGrid.idx 54) (oGrid.dm 54) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 54) oGrid.kl oGrid.kr 400 400 ⟨false, 4276227820942122502177112779374427738116017997320360164110968663578943052320⟩ ⟨false, 0⟩ ⟨false, 6887159504187220772085067574759083660822817516414252612607203055788989442770⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_54_800 : bothSeg evalE (oGrid.idx 54) (oGrid.dm 54) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 54) oGrid.kl oGrid.kr 400 800 ⟨false, 6887159504187220772085067574759083660822817516414252612607203055788989442770⟩ ⟨false, 0⟩ ⟨false, 7872076983772628791397735984534530681623751010247291813532230243446200348406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_54_1200 : bothSeg evalE (oGrid.idx 54) (oGrid.dm 54) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 54) oGrid.kl oGrid.kr 400 1200 ⟨false, 7872076983772628791397735984534530681623751010247291813532230243446200348406⟩ ⟨false, 0⟩ ⟨false, 8056464972906742593844710022803862866994405339014351316408426877943486702114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_54_1600 : bothSeg evalE (oGrid.idx 54) (oGrid.dm 54) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 54) oGrid.kl oGrid.kr 400 1600 ⟨false, 8056464972906742593844710022803862866994405339014351316408426877943486702114⟩ ⟨false, 0⟩ ⟨false, 7884533169278384672134090245732971279822718642774775842343436970549594903308⟩ ⟨false, 172844628342776719350530984852971040249929716355639390060232412202585013104⟩ = true := by
  decide +kernel

theorem b_54_2000 : bothSeg evalE (oGrid.idx 54) (oGrid.dm 54) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 54) oGrid.kl oGrid.kr 400 2000 ⟨false, 7884533169278384672134090245732971279822718642774775842343436970549594903308⟩ ⟨false, 172844628342776719350530984852971040249929716355639390060232412202585013104⟩ ⟨false, 7805286007513522287420416730618862050067723909990279722295103855384024861762⟩ ⟨false, 252726079300741251372404413160593649096361036012253110318833232565138040866⟩ = true := by
  decide +kernel

theorem b_54_2400 : bothLoop evalE (oGrid.idx 54) (oGrid.dm 54) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 54) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7805286007513522287420416730618862050067723909990279722295103855384024861762⟩ ⟨false, 252726079300741251372404413160593649096361036012253110318833232565138040866⟩ = true := by
  decide +kernel

theorem o_row_54 : oGrid.row evalE 54 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_54_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_54_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_54_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_54_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_54_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_54_2000).1 (bothLoop_sound b_54_2400).1))))))

theorem n_row_54 : nGrid.row evalE 54 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_54_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_54_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_54_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_54_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_54_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_54_2000).2 (bothLoop_sound b_54_2400).2))))))

theorem b_55_0 : bothSeg evalE (oGrid.idx 55) (oGrid.dm 55) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 55) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4261031906028693348775387441015481723481314718918305360416849256702385074520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_55_400 : bothSeg evalE (oGrid.idx 55) (oGrid.dm 55) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 55) oGrid.kl oGrid.kr 400 400 ⟨false, 4261031906028693348775387441015481723481314718918305360416849256702385074520⟩ ⟨false, 0⟩ ⟨false, 6863083659703308161503205260785058595590550610991720232711398649290362257624⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_55_800 : bothSeg evalE (oGrid.idx 55) (oGrid.dm 55) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 55) oGrid.kl oGrid.kr 400 800 ⟨false, 6863083659703308161503205260785058595590550610991720232711398649290362257624⟩ ⟨false, 0⟩ ⟨false, 7844586863494861667698041997200254395196869132128621469204501271078136043824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_55_1200 : bothSeg evalE (oGrid.idx 55) (oGrid.dm 55) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 55) oGrid.kl oGrid.kr 400 1200 ⟨false, 7844586863494861667698041997200254395196869132128621469204501271078136043824⟩ ⟨false, 0⟩ ⟨false, 8028054496371561248909675072375939374788821441210969660477336481099290581556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_55_1600 : bothSeg evalE (oGrid.idx 55) (oGrid.dm 55) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 55) oGrid.kl oGrid.kr 400 1600 ⟨false, 8028054496371561248909675072375939374788821441210969660477336481099290581556⟩ ⟨false, 0⟩ ⟨false, 7855863234341103241903361293572761495960818818285810694437399808315367048146⟩ ⟨false, 173071403592296585333546883375734476355166604291170697559082892516809665832⟩ = true := by
  decide +kernel

theorem b_55_2000 : bothSeg evalE (oGrid.idx 55) (oGrid.dm 55) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 55) oGrid.kl oGrid.kr 400 2000 ⟨false, 7855863234341103241903361293572761495960818818285810694437399808315367048146⟩ ⟨false, 173071403592296585333546883375734476355166604291170697559082892516809665832⟩ ⟨false, 7777082586610084566916866540321439545384239595233345343164567250645353492942⟩ ⟨false, 252488543614444094798416994850034096084090152595861245563699056076412846372⟩ = true := by
  decide +kernel

theorem b_55_2400 : bothLoop evalE (oGrid.idx 55) (oGrid.dm 55) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 55) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7777082586610084566916866540321439545384239595233345343164567250645353492942⟩ ⟨false, 252488543614444094798416994850034096084090152595861245563699056076412846372⟩ = true := by
  decide +kernel

theorem o_row_55 : oGrid.row evalE 55 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_55_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_55_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_55_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_55_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_55_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_55_2000).1 (bothLoop_sound b_55_2400).1))))))

theorem n_row_55 : nGrid.row evalE 55 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_55_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_55_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_55_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_55_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_55_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_55_2000).2 (bothLoop_sound b_55_2400).2))))))

theorem b_56_0 : bothSeg evalE (oGrid.idx 56) (oGrid.dm 56) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 56) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4245880659745859634658155309624179396217691945726712104268628669723237575590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_56_400 : bothSeg evalE (oGrid.idx 56) (oGrid.dm 56) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 56) oGrid.kl oGrid.kr 400 400 ⟨false, 4245880659745859634658155309624179396217691945726712104268628669723237575590⟩ ⟨false, 0⟩ ⟨false, 6839073998480030001168392093079287602488769923893962842597455636141459727344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_56_800 : bothSeg evalE (oGrid.idx 56) (oGrid.dm 56) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 56) oGrid.kl oGrid.kr 400 800 ⟨false, 6839073998480030001168392093079287602488769923893962842597455636141459727344⟩ ⟨false, 0⟩ ⟨false, 7817169263335024523037046004714866685631208704151007018078106821997379119644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_56_1200 : bothSeg evalE (oGrid.idx 56) (oGrid.dm 56) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 56) oGrid.kl oGrid.kr 400 1200 ⟨false, 7817169263335024523037046004714866685631208704151007018078106821997379119644⟩ ⟨false, 0⟩ ⟨false, 7999718200095952071858991145682228173259894194377977386913060145374125653480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_56_1600 : bothSeg evalE (oGrid.idx 56) (oGrid.dm 56) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 56) oGrid.kl oGrid.kr 400 1600 ⟨false, 7999718200095952071858991145682228173259894194377977386913060145374125653480⟩ ⟨false, 0⟩ ⟨false, 7827269979329300536859909982984510052790047725298321453381627610927958159862⟩ ⟨false, 173295730334545409335272430789977958164106070190481807779996964220016625554⟩ = true := by
  decide +kernel

theorem b_56_2000 : bothSeg evalE (oGrid.idx 56) (oGrid.dm 56) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 56) oGrid.kl oGrid.kr 400 2000 ⟨false, 7827269979329300536859909982984510052790047725298321453381627610927958159862⟩ ⟨false, 173295730334545409335272430789977958164106070190481807779996964220016625554⟩ ⟨false, 7748953534685493993793572938517299366451472161897323639696579938033727742488⟩ ⟨false, 252250468831771119047975732446879246187582650393383066286802584155681172384⟩ = true := by
  decide +kernel

theorem b_56_2400 : bothLoop evalE (oGrid.idx 56) (oGrid.dm 56) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 56) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7748953534685493993793572938517299366451472161897323639696579938033727742488⟩ ⟨false, 252250468831771119047975732446879246187582650393383066286802584155681172384⟩ = true := by
  decide +kernel

theorem o_row_56 : oGrid.row evalE 56 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_56_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_56_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_56_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_56_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_56_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_56_2000).1 (bothLoop_sound b_56_2400).1))))))

theorem n_row_56 : nGrid.row evalE 56 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_56_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_56_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_56_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_56_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_56_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_56_2000).2 (bothLoop_sound b_56_2400).2))))))

theorem b_57_0 : bothSeg evalE (oGrid.idx 57) (oGrid.dm 57) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 57) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4230773910108201229207522126779215427176298344706495956090692952982195469472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_57_400 : bothSeg evalE (oGrid.idx 57) (oGrid.dm 57) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 57) oGrid.kl oGrid.kr 400 400 ⟨false, 4230773910108201229207522126779215427176298344706495956090692952982195469472⟩ ⟨false, 0⟩ ⟨false, 6815130371120068172702598936415072704659505000962045123366838788441035418426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_57_800 : bothSeg evalE (oGrid.idx 57) (oGrid.dm 57) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 57) oGrid.kl oGrid.kr 400 800 ⟨false, 6815130371120068172702598936415072704659505000962045123366838788441035418426⟩ ⟨false, 0⟩ ⟨false, 7789824022009376154470129616517342982378619329705483936643282085427255998852⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_57_1200 : bothSeg evalE (oGrid.idx 57) (oGrid.dm 57) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 57) oGrid.kl oGrid.kr 400 1200 ⟨false, 7789824022009376154470129616517342982378619329705483936643282085427255998852⟩ ⟨false, 0⟩ ⟨false, 7971455948076271052066653030627220466018700752330719808946149729089490280824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_57_1600 : bothSeg evalE (oGrid.idx 57) (oGrid.dm 57) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 57) oGrid.kl oGrid.kr 400 1600 ⟨false, 7971455948076271052066653030627220466018700752330719808946149729089490280824⟩ ⟨false, 0⟩ ⟨false, 7798753009231249722180142483020182321098065316397813387471805069645904552244⟩ ⟨false, 173518937881072854423848662499983616115940679437413821941522446012136113572⟩ = true := by
  decide +kernel

theorem b_57_2000 : bothSeg evalE (oGrid.idx 57) (oGrid.dm 57) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 57) oGrid.kl oGrid.kr 400 2000 ⟨false, 7798753009231249722180142483020182321098065316397813387471805069645904552244⟩ ⟨false, 173518937881072854423848662499983616115940679437413821941522446012136113572⟩ ⟨false, 7720898446569188049139207567642543959028314117767688645237743924890171986286⟩ ⟨false, 252013317480176050403405065495276092790974769971634216867577044392489993894⟩ = true := by
  decide +kernel

theorem b_57_2400 : bothLoop evalE (oGrid.idx 57) (oGrid.dm 57) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 57) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7720898446569188049139207567642543959028314117767688645237743924890171986286⟩ ⟨false, 252013317480176050403405065495276092790974769971634216867577044392489993894⟩ = true := by
  decide +kernel

theorem o_row_57 : oGrid.row evalE 57 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_57_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_57_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_57_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_57_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_57_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_57_2000).1 (bothLoop_sound b_57_2400).1))))))

theorem n_row_57 : nGrid.row evalE 57 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_57_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_57_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_57_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_57_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_57_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_57_2000).2 (bothLoop_sound b_57_2400).2))))))

theorem b_58_0 : bothSeg evalE (oGrid.idx 58) (oGrid.dm 58) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 58) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4215711580320726637362556119485387265086839385913217215801699058462997025558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_58_400 : bothSeg evalE (oGrid.idx 58) (oGrid.dm 58) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 58) oGrid.kl oGrid.kr 400 400 ⟨false, 4215711580320726637362556119485387265086839385913217215801699058462997025558⟩ ⟨false, 0⟩ ⟨false, 6791252559320926332078291139205509957103037432020753727150972701985222532194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_58_800 : bothSeg evalE (oGrid.idx 58) (oGrid.dm 58) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 58) oGrid.kl oGrid.kr 400 800 ⟨false, 6791252559320926332078291139205509957103037432020753727150972701985222532194⟩ ⟨false, 0⟩ ⟨false, 7762550911937045610844504582414357297529351549539621517492390912345436016338⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_58_1200 : bothSeg evalE (oGrid.idx 58) (oGrid.dm 58) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 58) oGrid.kl oGrid.kr 400 1200 ⟨false, 7762550911937045610844504582414357297529351549539621517492390912345436016338⟩ ⟨false, 0⟩ ⟨false, 7943267521392387146842592645888248338891135721111839708162861346016774976896⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_58_1600 : bothSeg evalE (oGrid.idx 58) (oGrid.dm 58) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 58) oGrid.kl oGrid.kr 400 1600 ⟨false, 7943267521392387146842592645888248338891135721111839708162861346016774976896⟩ ⟨false, 0⟩ ⟨false, 7770311984269185689800440055725092103083672015415440396930208310508060897050⟩ ⟨false, 173740969981658674845162666464259264378069195670363761059236996988551601646⟩ = true := by
  decide +kernel

theorem b_58_2000 : bothSeg evalE (oGrid.idx 58) (oGrid.dm 58) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 58) oGrid.kl oGrid.kr 400 2000 ⟨false, 7770311984269185689800440055725092103083672015415440396930208310508060897050⟩ ⟨false, 173740969981658674845162666464259264378069195670363761059236996988551601646⟩ ⟨false, 7692916971692387045945339691288923554671896821922018165074388663717896633962⟩ ⟨false, 251777044003532021806523260831241945476488345654463603436104346767815545768⟩ = true := by
  decide +kernel

theorem b_58_2400 : bothLoop evalE (oGrid.idx 58) (oGrid.dm 58) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 58) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7692916971692387045945339691288923554671896821922018165074388663717896633962⟩ ⟨false, 251777044003532021806523260831241945476488345654463603436104346767815545768⟩ = true := by
  decide +kernel

theorem o_row_58 : oGrid.row evalE 58 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_58_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_58_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_58_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_58_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_58_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_58_2000).1 (bothLoop_sound b_58_2400).1))))))

theorem n_row_58 : nGrid.row evalE 58 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_58_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_58_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_58_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_58_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_58_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_58_2000).2 (bothLoop_sound b_58_2400).2))))))

theorem b_59_0 : bothSeg evalE (oGrid.idx 59) (oGrid.dm 59) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 59) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4200693555208590403263774316455701640040441774692354489051281589810197437010⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_59_400 : bothSeg evalE (oGrid.idx 59) (oGrid.dm 59) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 59) oGrid.kl oGrid.kr 400 400 ⟨false, 4200693555208590403263774316455701640040441774692354489051281589810197437010⟩ ⟨false, 0⟩ ⟨false, 6767440477724437037483342050949685685154908302306170825482204650202743484042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_59_800 : bothSeg evalE (oGrid.idx 59) (oGrid.dm 59) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 59) oGrid.kl oGrid.kr 400 800 ⟨false, 6767440477724437037483342050949685685154908302306170825482204650202743484042⟩ ⟨false, 0⟩ ⟨false, 7735349879809696031926514157338440767395432819913812900132621266922862652450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_59_1200 : bothSeg evalE (oGrid.idx 59) (oGrid.dm 59) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 59) oGrid.kl oGrid.kr 400 1200 ⟨false, 7735349879809696031926514157338440767395432819913812900132621266922862652450⟩ ⟨false, 0⟩ ⟨false, 7915152840790492405784486363407570037520747075449097758103459621720049195248⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_59_1600 : bothSeg evalE (oGrid.idx 59) (oGrid.dm 59) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 59) oGrid.kl oGrid.kr 400 1600 ⟨false, 7915152840790492405784486363407570037520747075449097758103459621720049195248⟩ ⟨false, 0⟩ ⟨false, 7741946917271492870708375350978461032093534562332853323931250774365931785086⟩ ⟨false, 173961330322823482776507729157705801211278782727392283807713329232362466008⟩ = true := by
  decide +kernel

theorem b_59_2000 : bothSeg evalE (oGrid.idx 59) (oGrid.dm 59) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 59) oGrid.kl oGrid.kr 400 2000 ⟨false, 7741946917271492870708375350978461032093534562332853323931250774365931785086⟩ ⟨false, 173961330322823482776507729157705801211278782727392283807713329232362466008⟩ ⟨false, 7665009120623402414237602059934032527355431498472489198278150635235666952216⟩ ⟨false, 251541663640445214588869605287691615115592375661206079972075412365970301262⟩ = true := by
  decide +kernel

theorem b_59_2400 : bothLoop evalE (oGrid.idx 59) (oGrid.dm 59) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 59) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7665009120623402414237602059934032527355431498472489198278150635235666952216⟩ ⟨false, 251541663640445214588869605287691615115592375661206079972075412365970301262⟩ = true := by
  decide +kernel

theorem o_row_59 : oGrid.row evalE 59 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_59_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_59_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_59_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_59_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_59_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_59_2000).1 (bothLoop_sound b_59_2400).1))))))

theorem n_row_59 : nGrid.row evalE 59 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_59_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_59_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_59_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_59_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_59_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_59_2000).2 (bothLoop_sound b_59_2400).2))))))

theorem b_60_0 : bothSeg evalE (oGrid.idx 60) (oGrid.dm 60) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 60) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4185719687428826335163354560499728116120946183985542168529249334840511133438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_60_400 : bothSeg evalE (oGrid.idx 60) (oGrid.dm 60) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 60) oGrid.kl oGrid.kr 400 400 ⟨false, 4185719687428826335163354560499728116120946183985542168529249334840511133438⟩ ⟨false, 0⟩ ⟨false, 6743693936324074716681916500562532899837330641131705071991293367947897543408⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_60_800 : bothSeg evalE (oGrid.idx 60) (oGrid.dm 60) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 60) oGrid.kl oGrid.kr 400 800 ⟨false, 6743693936324074716681916500562532899837330641131705071991293367947897543408⟩ ⟨false, 0⟩ ⟨false, 7708220724780407296145910147349726115194167115395292814637604343459892771380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_60_1200 : bothSeg evalE (oGrid.idx 60) (oGrid.dm 60) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 60) oGrid.kl oGrid.kr 400 1200 ⟨false, 7708220724780407296145910147349726115194167115395292814637604343459892771380⟩ ⟨false, 0⟩ ⟨false, 7887111726789354503204167150826431965146010981285779549697616596494710755714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_60_1600 : bothSeg evalE (oGrid.idx 60) (oGrid.dm 60) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 60) oGrid.kl oGrid.kr 400 1600 ⟨false, 7887111726789354503204167150826431965146010981285779549697616596494710755714⟩ ⟨false, 0⟩ ⟨false, 7713657745201666960010506663766681349108746915202657787048854068286168405996⟩ ⟨false, 174179551688535960046748927825056978140651635009698083060163463025178465606⟩ = true := by
  decide +kernel

theorem b_60_2000 : bothSeg evalE (oGrid.idx 60) (oGrid.dm 60) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 60) oGrid.kl oGrid.kr 400 2000 ⟨false, 7713657745201666960010506663766681349108746915202657787048854068286168405996⟩ ⟨false, 174179551688535960046748927825056978140651635009698083060163463025178465606⟩ ⟨false, 7637174830232293199921745163680010407018815588684606413369065887267820422718⟩ ⟨false, 251306286493281099179876073506950121946224806855118352900177343366439803728⟩ = true := by
  decide +kernel

theorem b_60_2400 : bothLoop evalE (oGrid.idx 60) (oGrid.dm 60) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 60) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7637174830232293199921745163680010407018815588684606413369065887267820422718⟩ ⟨false, 251306286493281099179876073506950121946224806855118352900177343366439803728⟩ = true := by
  decide +kernel

theorem o_row_60 : oGrid.row evalE 60 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_60_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_60_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_60_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_60_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_60_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_60_2000).1 (bothLoop_sound b_60_2400).1))))))

theorem n_row_60 : nGrid.row evalE 60 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_60_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_60_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_60_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_60_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_60_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_60_2000).2 (bothLoop_sound b_60_2400).2))))))

theorem b_61_0 : bothSeg evalE (oGrid.idx 61) (oGrid.dm 61) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 61) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4170789852181739390210896340098028420402847026963945263238757080186197486552⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_61_400 : bothSeg evalE (oGrid.idx 61) (oGrid.dm 61) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 61) oGrid.kl oGrid.kr 400 400 ⟨false, 4170789852181739390210896340098028420402847026963945263238757080186197486552⟩ ⟨false, 0⟩ ⟨false, 6720012778248640091786671304964748922729343230334802991257567984757137278434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_61_800 : bothSeg evalE (oGrid.idx 61) (oGrid.dm 61) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 61) oGrid.kl oGrid.kr 400 800 ⟨false, 6720012778248640091786671304964748922729343230334802991257567984757137278434⟩ ⟨false, 0⟩ ⟨false, 7681163278738486449046681999014000482192589857279193645498541543461143609124⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_61_1200 : bothSeg evalE (oGrid.idx 61) (oGrid.dm 61) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 61) oGrid.kl oGrid.kr 400 1200 ⟨false, 7681163278738486449046681999014000482192589857279193645498541543461143609124⟩ ⟨false, 0⟩ ⟨false, 7859144003499682564327888140511184562108289732549511323537035282210858834666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_61_1600 : bothSeg evalE (oGrid.idx 61) (oGrid.dm 61) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 61) oGrid.kl oGrid.kr 400 1600 ⟨false, 7859144003499682564327888140511184562108289732549511323537035282210858834666⟩ ⟨false, 0⟩ ⟨false, 7685444317735417159770397269600635702262928562122269210584916353609459817922⟩ ⟨false, 174396589952652870414062802227409271637538976997988835004485104280061643614⟩ = true := by
  decide +kernel

theorem b_61_2000 : bothSeg evalE (oGrid.idx 61) (oGrid.dm 61) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 61) oGrid.kl oGrid.kr 400 2000 ⟨false, 7685444317735417159770397269600635702262928562122269210584916353609459817922⟩ ⟨false, 174396589952652870414062802227409271637538976997988835004485104280061643614⟩ ⟨false, 7609413935704549197645872885703747382349058793051586411464316682982322047490⟩ ⟨false, 251072215143992477550593084532294593253902291361411849252227747941583153172⟩ = true := by
  decide +kernel

theorem b_61_2400 : bothLoop evalE (oGrid.idx 61) (oGrid.dm 61) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 61) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7609413935704549197645872885703747382349058793051586411464316682982322047490⟩ ⟨false, 251072215143992477550593084532294593253902291361411849252227747941583153172⟩ = true := by
  decide +kernel

theorem o_row_61 : oGrid.row evalE 61 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_61_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_61_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_61_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_61_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_61_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_61_2000).1 (bothLoop_sound b_61_2400).1))))))

theorem n_row_61 : nGrid.row evalE 61 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_61_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_61_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_61_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_61_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_61_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_61_2000).2 (bothLoop_sound b_61_2400).2))))))

theorem b_62_0 : bothSeg evalE (oGrid.idx 62) (oGrid.dm 62) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 62) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4155903929416396575697584600063772942496030762597412926246895486329219688794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_62_400 : bothSeg evalE (oGrid.idx 62) (oGrid.dm 62) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 62) oGrid.kl oGrid.kr 400 400 ⟨false, 4155903929416396575697584600063772942496030762597412926246895486329219688794⟩ ⟨false, 0⟩ ⟨false, 6696396867851780520778824742955986050199624698727909367801006592245055828900⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_62_800 : bothSeg evalE (oGrid.idx 62) (oGrid.dm 62) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 62) oGrid.kl oGrid.kr 400 800 ⟨false, 6696396867851780520778824742955986050199624698727909367801006592245055828900⟩ ⟨false, 0⟩ ⟨false, 7654177431938821429982069773006395900710561199567646510040277172556093462914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_62_1200 : bothSeg evalE (oGrid.idx 62) (oGrid.dm 62) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 62) oGrid.kl oGrid.kr 400 1200 ⟨false, 7654177431938821429982069773006395900710561199567646510040277172556093462914⟩ ⟨false, 0⟩ ⟨false, 7831249588080611270077197687040023611312974251705470075000307882413547022800⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_62_1600 : bothSeg evalE (oGrid.idx 62) (oGrid.dm 62) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 62) oGrid.kl oGrid.kr 400 1600 ⟨false, 7831249588080611270077197687040023611312974251705470075000307882413547022800⟩ ⟨false, 0⟩ ⟨false, 7657306281508027496847116330314692374893303691396725225906736027428842139930⟩ ⟨false, 174612404400305644751033847653551332189470776303410376595863509141641874308⟩ = true := by
  decide +kernel

theorem b_62_2000 : bothSeg evalE (oGrid.idx 62) (oGrid.dm 62) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 62) oGrid.kl oGrid.kr 400 2000 ⟨false, 7657306281508027496847116330314692374893303691396725225906736027428842139930⟩ ⟨false, 174612404400305644751033847653551332189470776303410376595863509141641874308⟩ ⟨false, 7581726115136860594430969372826063799165905092952732313546469002372595656420⟩ ⟨false, 250839154940271771584925530584072558033265405710718459406663914213685045814⟩ = true := by
  decide +kernel

theorem b_62_2400 : bothLoop evalE (oGrid.idx 62) (oGrid.dm 62) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 62) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7581726115136860594430969372826063799165905092952732313546469002372595656420⟩ ⟨false, 250839154940271771584925530584072558033265405710718459406663914213685045814⟩ = true := by
  decide +kernel

theorem o_row_62 : oGrid.row evalE 62 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_62_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_62_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_62_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_62_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_62_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_62_2000).1 (bothLoop_sound b_62_2400).1))))))

theorem n_row_62 : nGrid.row evalE 62 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_62_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_62_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_62_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_62_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_62_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_62_2000).2 (bothLoop_sound b_62_2400).2))))))

theorem b_63_0 : bothSeg evalE (oGrid.idx 63) (oGrid.dm 63) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 63) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4141061848794211499235390069692061414771286826681757676684717630371070086206⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_63_400 : bothSeg evalE (oGrid.idx 63) (oGrid.dm 63) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 63) oGrid.kl oGrid.kr 400 400 ⟨false, 4141061848794211499235390069692061414771286826681757676684717630371070086206⟩ ⟨false, 0⟩ ⟨false, 6672846048935266909589736349693032537204959232387996358552299701201980589894⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_63_800 : bothSeg evalE (oGrid.idx 63) (oGrid.dm 63) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 63) oGrid.kl oGrid.kr 400 800 ⟨false, 6672846048935266909589736349693032537204959232387996358552299701201980589894⟩ ⟨false, 0⟩ ⟨false, 7627263026339676606595546500586073700966938707049462716527085562070042341484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_63_1200 : bothSeg evalE (oGrid.idx 63) (oGrid.dm 63) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 63) oGrid.kl oGrid.kr 400 1200 ⟨false, 7627263026339676606595546500586073700966938707049462716527085562070042341484⟩ ⟨false, 0⟩ ⟨false, 7803428294312550287077097787367946954765203240918272488786277122916356632562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_63_1600 : bothSeg evalE (oGrid.idx 63) (oGrid.dm 63) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 63) oGrid.kl oGrid.kr 400 1600 ⟨false, 7803428294312550287077097787367946954765203240918272488786277122916356632562⟩ ⟨false, 0⟩ ⟨false, 7629243721213714022881104302482614456727880346203642900415077525120222083386⟩ ⟨false, 174826009815823759397680067685728053878526101789817587105628951394448103438⟩ = true := by
  decide +kernel

theorem b_63_2000 : bothSeg evalE (oGrid.idx 63) (oGrid.dm 63) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 63) oGrid.kl oGrid.kr 400 2000 ⟨false, 7629243721213714022881104302482614456727880346203642900415077525120222083386⟩ ⟨false, 174826009815823759397680067685728053878526101789817587105628951394448103438⟩ ⟨false, 7554111425377108340328150795743952916180789758972141752929977635276856434038⟩ ⟨false, 250606319812711014994581711185012104298106190042415761434457777952937292030⟩ = true := by
  decide +kernel

theorem b_63_2400 : bothLoop evalE (oGrid.idx 63) (oGrid.dm 63) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 63) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7554111425377108340328150795743952916180789758972141752929977635276856434038⟩ ⟨false, 250606319812711014994581711185012104298106190042415761434457777952937292030⟩ = true := by
  decide +kernel

theorem o_row_63 : oGrid.row evalE 63 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_63_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_63_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_63_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_63_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_63_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_63_2000).1 (bothLoop_sound b_63_2400).1))))))

theorem n_row_63 : nGrid.row evalE 63 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_63_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_63_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_63_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_63_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_63_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_63_2000).2 (bothLoop_sound b_63_2400).2))))))

theorem b_64_0 : bothSeg evalE (oGrid.idx 64) (oGrid.dm 64) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 64) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4126263416744891881192709651820098781502695100263702970521639923608227813186⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_64_400 : bothSeg evalE (oGrid.idx 64) (oGrid.dm 64) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 64) oGrid.kl oGrid.kr 400 400 ⟨false, 4126263416744891881192709651820098781502695100263702970521639923608227813186⟩ ⟨false, 0⟩ ⟨false, 6649360141775288934709816445064126587708758370272259423151863625783519086964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_64_800 : bothSeg evalE (oGrid.idx 64) (oGrid.dm 64) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 64) oGrid.kl oGrid.kr 400 800 ⟨false, 6649360141775288934709816445064126587708758370272259423151863625783519086964⟩ ⟨false, 0⟩ ⟨false, 7600419863679632694125024123531490255281912343220537031726293807973877243140⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_64_1200 : bothSeg evalE (oGrid.idx 64) (oGrid.dm 64) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 64) oGrid.kl oGrid.kr 400 1200 ⟨false, 7600419863679632694125024123531490255281912343220537031726293807973877243140⟩ ⟨false, 0⟩ ⟨false, 7775679958688961218988033098595474732567245039958603681187011680121580250022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_64_1600 : bothSeg evalE (oGrid.idx 64) (oGrid.dm 64) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 64) oGrid.kl oGrid.kr 400 1600 ⟨false, 7775679958688961218988033098595474732567245039958603681187011680121580250022⟩ ⟨false, 0⟩ ⟨false, 7601256308630434423376640642761882527646245606885780526913465328659734532926⟩ ⟨false, 175038001044607677337849373159985201923210252286615565374899853333861893912⟩ = true := by
  decide +kernel

theorem b_64_2000 : bothSeg evalE (oGrid.idx 64) (oGrid.dm 64) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 64) oGrid.kl oGrid.kr 400 2000 ⟨false, 7601256308630434423376640642761882527646245606885780526913465328659734532926⟩ ⟨false, 175038001044607677337849373159985201923210252286615565374899853333861893912⟩ ⟨false, 7526569535939519737497902499464808888657461917342339190127055061943603268108⟩ ⟨false, 250374129969559165006094821068220553265105942827167930581446223107027569404⟩ = true := by
  decide +kernel

theorem b_64_2400 : bothLoop evalE (oGrid.idx 64) (oGrid.dm 64) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 64) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7526569535939519737497902499464808888657461917342339190127055061943603268108⟩ ⟨false, 250374129969559165006094821068220553265105942827167930581446223107027569404⟩ = true := by
  decide +kernel

theorem o_row_64 : oGrid.row evalE 64 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_64_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_64_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_64_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_64_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_64_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_64_2000).1 (bothLoop_sound b_64_2400).1))))))

theorem n_row_64 : nGrid.row evalE 64 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_64_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_64_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_64_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_64_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_64_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_64_2000).2 (bothLoop_sound b_64_2400).2))))))

theorem b_65_0 : bothSeg evalE (oGrid.idx 65) (oGrid.dm 65) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 65) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4111508533387145892509384697392470762436794191055353828293694694809889011776⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_65_400 : bothSeg evalE (oGrid.idx 65) (oGrid.dm 65) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 65) oGrid.kl oGrid.kr 400 400 ⟨false, 4111508533387145892509384697392470762436794191055353828293694694809889011776⟩ ⟨false, 0⟩ ⟨false, 6625938981126280601412787014829316763034583822891247013575054381614842647510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_65_800 : bothSeg evalE (oGrid.idx 65) (oGrid.dm 65) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 65) oGrid.kl oGrid.kr 400 800 ⟨false, 6625938981126280601412787014829316763034583822891247013575054381614842647510⟩ ⟨false, 0⟩ ⟨false, 7573647818156141392026071940401129975061288348781923446619538435793522730910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_65_1200 : bothSeg evalE (oGrid.idx 65) (oGrid.dm 65) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 65) oGrid.kl oGrid.kr 400 1200 ⟨false, 7573647818156141392026071940401129975061288348781923446619538435793522730910⟩ ⟨false, 0⟩ ⟨false, 7748004416069584585062187563786427198764302813807089274999886672969147715354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_65_1600 : bothSeg evalE (oGrid.idx 65) (oGrid.dm 65) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 65) oGrid.kl oGrid.kr 400 1600 ⟨false, 7748004416069584585062187563786427198764302813807089274999886672969147715354⟩ ⟨false, 0⟩ ⟨false, 7573343872394283738274035095046491772071766642530610029733423525539261067816⟩ ⟨false, 175248978199396887139604999010751261850956260473131174995793081643413801928⟩ = true := by
  decide +kernel

theorem b_65_2000 : bothSeg evalE (oGrid.idx 65) (oGrid.dm 65) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 65) oGrid.kl oGrid.kr 400 2000 ⟨false, 7573343872394283738274035095046491772071766642530610029733423525539261067816⟩ ⟨false, 175248978199396887139604999010751261850956260473131174995793081643413801928⟩ ⟨false, 7499100266097961728703018587728884916269018861660936091662661086225185267188⟩ ⟨false, 250143371449305567045961668466804950310785309293840972444441494655039797570⟩ = true := by
  decide +kernel

theorem b_65_2400 : bothLoop evalE (oGrid.idx 65) (oGrid.dm 65) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 65) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7499100266097961728703018587728884916269018861660936091662661086225185267188⟩ ⟨false, 250143371449305567045961668466804950310785309293840972444441494655039797570⟩ = true := by
  decide +kernel

theorem o_row_65 : oGrid.row evalE 65 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_65_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_65_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_65_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_65_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_65_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_65_2000).1 (bothLoop_sound b_65_2400).1))))))

theorem n_row_65 : nGrid.row evalE 65 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_65_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_65_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_65_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_65_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_65_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_65_2000).2 (bothLoop_sound b_65_2400).2))))))

theorem b_66_0 : bothSeg evalE (oGrid.idx 66) (oGrid.dm 66) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 66) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4096797108468268415898590721265548054615089192633585920889352845288163647016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_66_400 : bothSeg evalE (oGrid.idx 66) (oGrid.dm 66) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 66) oGrid.kl oGrid.kr 400 400 ⟨false, 4096797108468268415898590721265548054615089192633585920889352845288163647016⟩ ⟨false, 0⟩ ⟨false, 6602582558445573623197865016982858077297289308541927324114853998922735600454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_66_800 : bothSeg evalE (oGrid.idx 66) (oGrid.dm 66) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 66) oGrid.kl oGrid.kr 400 800 ⟨false, 6602582558445573623197865016982858077297289308541927324114853998922735600454⟩ ⟨false, 0⟩ ⟨false, 7546946859665462504528797973365133066658954107396617375200119890488184815424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_66_1200 : bothSeg evalE (oGrid.idx 66) (oGrid.dm 66) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 66) oGrid.kl oGrid.kr 400 1200 ⟨false, 7546946859665462504528797973365133066658954107396617375200119890488184815424⟩ ⟨false, 0⟩ ⟨false, 7720401662098749143730503392384889040896324692273074773885195147567115653938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_66_1600 : bothSeg evalE (oGrid.idx 66) (oGrid.dm 66) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 66) oGrid.kl oGrid.kr 400 1600 ⟨false, 7720401662098749143730503392384889040896324692273074773885195147567115653938⟩ ⟨false, 0⟩ ⟨false, 7545506562862454366018416870821638191876994129052175256163493860227476430516⟩ ⟨false, 175458397342488699895244149253305347004328814561017752318763257979254775642⟩ = true := by
  decide +kernel

theorem b_66_2000 : bothSeg evalE (oGrid.idx 66) (oGrid.dm 66) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 66) oGrid.kl oGrid.kr 400 2000 ⟨false, 7545506562862454366018416870821638191876994129052175256163493860227476430516⟩ ⟨false, 175458397342488699895244149253305347004328814561017752318763257979254775642⟩ ⟨false, 7471703799578270987525080314241150273199650931156778954176599542426000969066⟩ ⟨false, 249913279186327088315264997921505728367885656548258978566667999890623232830⟩ = true := by
  decide +kernel

theorem b_66_2400 : bothLoop evalE (oGrid.idx 66) (oGrid.dm 66) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 66) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7471703799578270987525080314241150273199650931156778954176599542426000969066⟩ ⟨false, 249913279186327088315264997921505728367885656548258978566667999890623232830⟩ = true := by
  decide +kernel

theorem o_row_66 : oGrid.row evalE 66 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_66_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_66_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_66_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_66_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_66_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_66_2000).1 (bothLoop_sound b_66_2400).1))))))

theorem n_row_66 : nGrid.row evalE 66 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_66_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_66_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_66_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_66_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_66_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_66_2000).2 (bothLoop_sound b_66_2400).2))))))

theorem b_67_0 : bothSeg evalE (oGrid.idx 67) (oGrid.dm 67) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 67) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4082129017508282425583778513106450846683722121927108160009075132248926675042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_67_400 : bothSeg evalE (oGrid.idx 67) (oGrid.dm 67) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 67) oGrid.kl oGrid.kr 400 400 ⟨false, 4082129017508282425583778513106450846683722121927108160009075132248926675042⟩ ⟨false, 0⟩ ⟨false, 6579290535822808756049073778694473147423582507589482439806732667133184269332⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_67_800 : bothSeg evalE (oGrid.idx 67) (oGrid.dm 67) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 67) oGrid.kl oGrid.kr 400 800 ⟨false, 6579290535822808756049073778694473147423582507589482439806732667133184269332⟩ ⟨false, 0⟩ ⟨false, 7520316644822574930292463651774450657906044911193336392315570208439236833346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_67_1200 : bothSeg evalE (oGrid.idx 67) (oGrid.dm 67) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 67) oGrid.kl oGrid.kr 400 1200 ⟨false, 7520316644822574930292463651774450657906044911193336392315570208439236833346⟩ ⟨false, 0⟩ ⟨false, 7692871305768467534232182612500153206153875027506674327587419093790354365034⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_67_1600 : bothSeg evalE (oGrid.idx 67) (oGrid.dm 67) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 67) oGrid.kl oGrid.kr 400 1600 ⟨false, 7692871305768467534232182612500153206153875027506674327587419093790354365034⟩ ⟨false, 0⟩ ⟨false, 7517743878335192743593188581258307673844286844640379095419382443435337004414⟩ ⟨false, 175665972292950564978450776033358121690038486665608187301474070289456804784⟩ = true := by
  decide +kernel

theorem b_67_2000 : bothSeg evalE (oGrid.idx 67) (oGrid.dm 67) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 67) oGrid.kl oGrid.kr 400 2000 ⟨false, 7517743878335192743593188581258307673844286844640379095419382443435337004414⟩ ⟨false, 175665972292950564978450776033358121690038486665608187301474070289456804784⟩ ⟨false, 7444379594961632090620080723213342420239835093659898245638066751205864025530⟩ ⟨false, 249683818298125362297270114260245964043710544069033086539642704601265861858⟩ = true := by
  decide +kernel

theorem b_67_2400 : bothLoop evalE (oGrid.idx 67) (oGrid.dm 67) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 67) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7444379594961632090620080723213342420239835093659898245638066751205864025530⟩ ⟨false, 249683818298125362297270114260245964043710544069033086539642704601265861858⟩ = true := by
  decide +kernel

theorem o_row_67 : oGrid.row evalE 67 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_67_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_67_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_67_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_67_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_67_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_67_2000).1 (bothLoop_sound b_67_2400).1))))))

theorem n_row_67 : nGrid.row evalE 67 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_67_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_67_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_67_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_67_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_67_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_67_2000).2 (bothLoop_sound b_67_2400).2))))))

theorem b_68_0 : bothSeg evalE (oGrid.idx 68) (oGrid.dm 68) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 68) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4067504098759973185917211858124770882537810007702726214995941730869367234216⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_68_400 : bothSeg evalE (oGrid.idx 68) (oGrid.dm 68) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 68) oGrid.kl oGrid.kr 400 400 ⟨false, 4067504098759973185917211858124770882537810007702726214995941730869367234216⟩ ⟨false, 0⟩ ⟨false, 6556062848951699174207726308149033778024451655384355276914510112724251711602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_68_800 : bothSeg evalE (oGrid.idx 68) (oGrid.dm 68) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 68) oGrid.kl oGrid.kr 400 800 ⟨false, 6556062848951699174207726308149033778024451655384355276914510112724251711602⟩ ⟨false, 0⟩ ⟨false, 7493757134615376394115946852582859331361611792936594176288406270971500119184⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_68_1200 : bothSeg evalE (oGrid.idx 68) (oGrid.dm 68) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 68) oGrid.kl oGrid.kr 400 1200 ⟨false, 7493757134615376394115946852582859331361611792936594176288406270971500119184⟩ ⟨false, 0⟩ ⟨false, 7665413340044382800983480661301097366151333371643372786258392643581494588228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_68_1600 : bothSeg evalE (oGrid.idx 68) (oGrid.dm 68) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 68) oGrid.kl oGrid.kr 400 1600 ⟨false, 7665413340044382800983480661301097366151333371643372786258392643581494588228⟩ ⟨false, 0⟩ ⟨false, 7490055878306028251582296285107101409364346091008052934052933289563926033400⟩ ⟨false, 175871758862032556919945768927696479643928973225727769385817746688575746806⟩ = true := by
  decide +kernel

theorem b_68_2000 : bothSeg evalE (oGrid.idx 68) (oGrid.dm 68) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 68) oGrid.kl oGrid.kr 400 2000 ⟨false, 7490055878306028251582296285107101409364346091008052934052933289563926033400⟩ ⟨false, 175871758862032556919945768927696479643928973225727769385817746688575746806⟩ ⟨false, 7417127742958077700132981500239523315614915913083255799817165412476835168030⟩ ⟨false, 249454789647236021175244083230113317188387093108978062736305171896162565822⟩ = true := by
  decide +kernel

theorem b_68_2400 : bothLoop evalE (oGrid.idx 68) (oGrid.dm 68) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 68) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7417127742958077700132981500239523315614915913083255799817165412476835168030⟩ ⟨false, 249454789647236021175244083230113317188387093108978062736305171896162565822⟩ = true := by
  decide +kernel

theorem o_row_68 : oGrid.row evalE 68 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_68_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_68_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_68_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_68_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_68_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_68_2000).1 (bothLoop_sound b_68_2400).1))))))

theorem n_row_68 : nGrid.row evalE 68 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_68_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_68_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_68_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_68_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_68_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_68_2000).2 (bothLoop_sound b_68_2400).2))))))

theorem b_69_0 : bothSeg evalE (oGrid.idx 69) (oGrid.dm 69) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 69) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4052922374404324569108016721284321623372195217919983475335792716224239349094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_69_400 : bothSeg evalE (oGrid.idx 69) (oGrid.dm 69) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 69) oGrid.kl oGrid.kr 400 400 ⟨false, 4052922374404324569108016721284321623372195217919983475335792716224239349094⟩ ⟨false, 0⟩ ⟨false, 6532899415051800122215459192563935154967053947847371598239992374942604961578⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_69_800 : bothSeg evalE (oGrid.idx 69) (oGrid.dm 69) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 69) oGrid.kl oGrid.kr 400 800 ⟨false, 6532899415051800122215459192563935154967053947847371598239992374942604961578⟩ ⟨false, 0⟩ ⟨false, 7467268247618929091533865146331201954848415086731974411793198246323037240482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_69_1200 : bothSeg evalE (oGrid.idx 69) (oGrid.dm 69) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 69) oGrid.kl oGrid.kr 400 1200 ⟨false, 7467268247618929091533865146331201954848415086731974411793198246323037240482⟩ ⟨false, 0⟩ ⟨false, 7638027637241045574913898198998058376034794708327682363279578585679639653868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_69_1600 : bothSeg evalE (oGrid.idx 69) (oGrid.dm 69) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 69) oGrid.kl oGrid.kr 400 1600 ⟨false, 7638027637241045574913898198998058376034794708327682363279578585679639653868⟩ ⟨false, 0⟩ ⟨false, 7462442360530616959160868385991741769784686176529790577008527169653362935576⟩ ⟨false, 176076232284548144214738450688716514879275733646313144727186089326427274854⟩ = true := by
  decide +kernel

theorem b_69_2000 : bothSeg evalE (oGrid.idx 69) (oGrid.dm 69) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 69) oGrid.kl oGrid.kr 400 2000 ⟨false, 7462442360530616959160868385991741769784686176529790577008527169653362935576⟩ ⟨false, 176076232284548144214738450688716514879275733646313144727186089326427274854⟩ ⟨false, 7389948006691827865015982918086817395606279322174261277896024485790483809426⟩ ⟨false, 249226929809852892203912100895178464759556019626866734202767899823492376902⟩ = true := by
  decide +kernel

theorem b_69_2400 : bothLoop evalE (oGrid.idx 69) (oGrid.dm 69) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 69) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7389948006691827865015982918086817395606279322174261277896024485790483809426⟩ ⟨false, 249226929809852892203912100895178464759556019626866734202767899823492376902⟩ = true := by
  decide +kernel

theorem o_row_69 : oGrid.row evalE 69 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_69_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_69_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_69_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_69_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_69_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_69_2000).1 (bothLoop_sound b_69_2400).1))))))

theorem n_row_69 : nGrid.row evalE 69 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_69_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_69_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_69_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_69_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_69_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_69_2000).2 (bothLoop_sound b_69_2400).2))))))

theorem b_70_0 : bothSeg evalE (oGrid.idx 70) (oGrid.dm 70) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 70) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4038383522770034655158029370190372895303887349901159969829979718098219025352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_70_400 : bothSeg evalE (oGrid.idx 70) (oGrid.dm 70) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 70) oGrid.kl oGrid.kr 400 400 ⟨false, 4038383522770034655158029370190372895303887349901159969829979718098219025352⟩ ⟨false, 0⟩ ⟨false, 6509799907830361569918391988784418583377973802381394659513290078661829249436⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_70_800 : bothSeg evalE (oGrid.idx 70) (oGrid.dm 70) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 70) oGrid.kl oGrid.kr 400 800 ⟨false, 6509799907830361569918391988784418583377973802381394659513290078661829249436⟩ ⟨false, 0⟩ ⟨false, 7440849636505986844388976468568077605942784708234262540466589065407660524282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_70_1200 : bothSeg evalE (oGrid.idx 70) (oGrid.dm 70) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 70) oGrid.kl oGrid.kr 400 1200 ⟨false, 7440849636505986844388976468568077605942784708234262540466589065407660524282⟩ ⟨false, 0⟩ ⟨false, 7610713839143375038504985626681494158579808335570135094054861097897759656364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_70_1600 : bothSeg evalE (oGrid.idx 70) (oGrid.dm 70) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 70) oGrid.kl oGrid.kr 400 1600 ⟨false, 7610713839143375038504985626681494158579808335570135094054861097897759656364⟩ ⟨false, 0⟩ ⟨false, 7434903038461743500511365810785177266198756017782590417840986195333094049092⟩ ⟨false, 176279364653807044324852701494309603603728473265614900169675747681307565998⟩ = true := by
  decide +kernel

theorem b_70_2000 : bothSeg evalE (oGrid.idx 70) (oGrid.dm 70) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 70) oGrid.kl oGrid.kr 400 2000 ⟨false, 7434903038461743500511365810785177266198756017782590417840986195333094049092⟩ ⟨false, 176279364653807044324852701494309603603728473265614900169675747681307565998⟩ ⟨false, 7362840105613156911881555630861785550778167451841778370295390666565879312684⟩ ⟨false, 249000026627763261591338130463166241121362210667408748249659297396606353528⟩ = true := by
  decide +kernel

theorem b_70_2400 : bothLoop evalE (oGrid.idx 70) (oGrid.dm 70) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 70) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7362840105613156911881555630861785550778167451841778370295390666565879312684⟩ ⟨false, 249000026627763261591338130463166241121362210667408748249659297396606353528⟩ = true := by
  decide +kernel

theorem o_row_70 : oGrid.row evalE 70 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_70_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_70_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_70_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_70_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_70_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_70_2000).1 (bothLoop_sound b_70_2400).1))))))

theorem n_row_70 : nGrid.row evalE 70 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_70_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_70_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_70_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_70_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_70_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_70_2000).2 (bothLoop_sound b_70_2400).2))))))

theorem b_71_0 : bothSeg evalE (oGrid.idx 71) (oGrid.dm 71) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 71) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4023887503197125015418999855559285640629038768824602621155812022214645115882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_71_400 : bothSeg evalE (oGrid.idx 71) (oGrid.dm 71) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 71) oGrid.kl oGrid.kr 400 400 ⟨false, 4023887503197125015418999855559285640629038768824602621155812022214645115882⟩ ⟨false, 0⟩ ⟨false, 6486764311840706819019262996168667832091640542762080246644165905783056944256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_71_800 : bothSeg evalE (oGrid.idx 71) (oGrid.dm 71) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 71) oGrid.kl oGrid.kr 400 800 ⟨false, 6486764311840706819019262996168667832091640542762080246644165905783056944256⟩ ⟨false, 0⟩ ⟨false, 7414501306304780090868191961924142710041640505321477178588839443085272114738⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_71_1200 : bothSeg evalE (oGrid.idx 71) (oGrid.dm 71) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 71) oGrid.kl oGrid.kr 400 1200 ⟨false, 7414501306304780090868191961924142710041640505321477178588839443085272114738⟩ ⟨false, 0⟩ ⟨false, 7583471904642164973479627819954043880732745311755410167848167763148199592956⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_71_1600 : bothSeg evalE (oGrid.idx 71) (oGrid.dm 71) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 71) oGrid.kl oGrid.kr 400 1600 ⟨false, 7583471904642164973479627819954043880732745311755410167848167763148199592956⟩ ⟨false, 0⟩ ⟨false, 7407437921401163032124871530011157525144830482549532010711340736458985762510⟩ ⟨false, 176481004519226634179286982990490264544327238995149036520201976701483764912⟩ = true := by
  decide +kernel

theorem b_71_2000 : bothSeg evalE (oGrid.idx 71) (oGrid.dm 71) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 71) oGrid.kl oGrid.kr 400 2000 ⟨false, 7407437921401163032124871530011157525144830482549532010711340736458985762510⟩ ⟨false, 176481004519226634179286982990490264544327238995149036520201976701483764912⟩ ⟨false, 7335804062556042182671991061876960797891996629376841165200009414081610826140⟩ ⟨false, 248773974737189967023036298667088207300581631820578695767129025869346703698⟩ = true := by
  decide +kernel

theorem b_71_2400 : bothLoop evalE (oGrid.idx 71) (oGrid.dm 71) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 71) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7335804062556042182671991061876960797891996629376841165200009414081610826140⟩ ⟨false, 248773974737189967023036298667088207300581631820578695767129025869346703698⟩ = true := by
  decide +kernel

theorem o_row_71 : oGrid.row evalE 71 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_71_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_71_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_71_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_71_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_71_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_71_2000).1 (bothLoop_sound b_71_2400).1))))))

theorem n_row_71 : nGrid.row evalE 71 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_71_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_71_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_71_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_71_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_71_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_71_2000).2 (bothLoop_sound b_71_2400).2))))))

theorem o_blk_48 : allFrom (fun j => oGrid.row evalE j) 48 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 48) o_row_48 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 49) o_row_49 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 50) o_row_50 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 51) o_row_51 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 52) o_row_52 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 53) o_row_53 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 54) o_row_54 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 55) o_row_55 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 56) o_row_56 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 57) o_row_57 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 58) o_row_58 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 59) o_row_59 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 60) o_row_60 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 61) o_row_61 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 62) o_row_62 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 63) o_row_63 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 64) o_row_64 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 65) o_row_65 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 66) o_row_66 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 67) o_row_67 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 68) o_row_68 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 69) o_row_69 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 70) o_row_70 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 71) o_row_71 (allFrom_zero (fun j => oGrid.row evalE j) 72)))))))))))))))))))))))))

theorem n_blk_48 : allFrom (fun j => nGrid.row evalE j) 48 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 48) n_row_48 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 49) n_row_49 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 50) n_row_50 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 51) n_row_51 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 52) n_row_52 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 53) n_row_53 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 54) n_row_54 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 55) n_row_55 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 56) n_row_56 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 57) n_row_57 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 58) n_row_58 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 59) n_row_59 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 60) n_row_60 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 61) n_row_61 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 62) n_row_62 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 63) n_row_63 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 64) n_row_64 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 65) n_row_65 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 66) n_row_66 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 67) n_row_67 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 68) n_row_68 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 69) n_row_69 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 70) n_row_70 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 71) n_row_71 (allFrom_zero (fun j => nGrid.row evalE j) 72)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
