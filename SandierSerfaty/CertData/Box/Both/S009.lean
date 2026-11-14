/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 9 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `216`–`239`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_216_0 : bothSeg evalE (oGrid.idx 216) (oGrid.dm 216) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 216) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2321006009404725931554766217596233187613384247036878104588070938659241033384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_216_400 : bothSeg evalE (oGrid.idx 216) (oGrid.dm 216) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 216) oGrid.kl oGrid.kr 400 400 ⟨false, 2321006009404725931554766217596233187613384247036878104588070938659241033384⟩ ⟨false, 0⟩ ⟨false, 3751448236004982418980595623318217575160382799747089043399393627461084441578⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_216_800 : bothSeg evalE (oGrid.idx 216) (oGrid.dm 216) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 216) oGrid.kl oGrid.kr 400 800 ⟨false, 3751448236004982418980595623318217575160382799747089043399393627461084441578⟩ ⟨false, 0⟩ ⟨false, 4266481893693453115856552174462977263175257319171966358548157766219798303106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_216_1200 : bothSeg evalE (oGrid.idx 216) (oGrid.dm 216) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 216) oGrid.kl oGrid.kr 400 1200 ⟨false, 4266481893693453115856552174462977263175257319171966358548157766219798303106⟩ ⟨false, 0⟩ ⟨false, 4299210252056711682487034573893810688700434910922035214340849003616046109702⟩ ⟨false, 30064998439655741235610890596883163584607708951395044677828236134432669046⟩ = true := by
  decide +kernel

theorem b_216_1600 : bothSeg evalE (oGrid.idx 216) (oGrid.dm 216) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 216) oGrid.kl oGrid.kr 400 1600 ⟨false, 4299210252056711682487034573893810688700434910922035214340849003616046109702⟩ ⟨false, 30064998439655741235610890596883163584607708951395044677828236134432669046⟩ ⟨false, 4137515483708415641939022910508686409963037954572155652246107175114820310830⟩ ⟨false, 192108699125374053598298119939172497678581859753971146350623353045413161326⟩ = true := by
  decide +kernel

theorem b_216_2000 : bothSeg evalE (oGrid.idx 216) (oGrid.dm 216) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 216) oGrid.kl oGrid.kr 400 2000 ⟨false, 4137515483708415641939022910508686409963037954572155652246107175114820310830⟩ ⟨false, 192108699125374053598298119939172497678581859753971146350623353045413161326⟩ ⟨false, 4108675356292945213487912659093779505653284543764728700406268261038806541910⟩ ⟨false, 221858209129220431303702867385898106039468780799989113459369586187067496472⟩ = true := by
  decide +kernel

theorem b_216_2400 : bothLoop evalE (oGrid.idx 216) (oGrid.dm 216) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 216) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4108675356292945213487912659093779505653284543764728700406268261038806541910⟩ ⟨false, 221858209129220431303702867385898106039468780799989113459369586187067496472⟩ = true := by
  decide +kernel

theorem o_row_216 : oGrid.row evalE 216 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_216_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_216_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_216_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_216_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_216_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_216_2000).1 (bothLoop_sound b_216_2400).1))))))

theorem n_row_216 : nGrid.row evalE 216 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_216_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_216_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_216_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_216_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_216_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_216_2000).2 (bothLoop_sound b_216_2400).2))))))

theorem b_217_0 : bothSeg evalE (oGrid.idx 217) (oGrid.dm 217) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 217) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2311676567042447497094895511769647723161889981189897323470165811383960368424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_217_400 : bothSeg evalE (oGrid.idx 217) (oGrid.dm 217) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 217) oGrid.kl oGrid.kr 400 400 ⟨false, 2311676567042447497094895511769647723161889981189897323470165811383960368424⟩ ⟨false, 0⟩ ⟨false, 3736304468692886001415261865039063769144680243317412028083654725690520179590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_217_800 : bothSeg evalE (oGrid.idx 217) (oGrid.dm 217) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 217) oGrid.kl oGrid.kr 400 800 ⟨false, 3736304468692886001415261865039063769144680243317412028083654725690520179590⟩ ⟨false, 0⟩ ⟨false, 4248953571277111226877010053860415941650999282568448364251786719064400028474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_217_1200 : bothSeg evalE (oGrid.idx 217) (oGrid.dm 217) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 217) oGrid.kl oGrid.kr 400 1200 ⟨false, 4248953571277111226877010053860415941650999282568448364251786719064400028474⟩ ⟨false, 0⟩ ⟨false, 4280889489345917477996101319537063416256313146897165072101449265504953732838⟩ ⟨false, 30309704823019800152736401335539185535557517502014954060934221662044958520⟩ = true := by
  decide +kernel

theorem b_217_1600 : bothSeg evalE (oGrid.idx 217) (oGrid.dm 217) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 217) oGrid.kl oGrid.kr 400 1600 ⟨false, 4280889489345917477996101319537063416256313146897165072101449265504953732838⟩ ⟨false, 30309704823019800152736401335539185535557517502014954060934221662044958520⟩ ⟨false, 4119410890573255953373555709310838950472556675359355096264556068480544430588⟩ ⟨false, 192138238541650152355366606458931661038024581276577904748883590691965557152⟩ = true := by
  decide +kernel

theorem b_217_2000 : bothSeg evalE (oGrid.idx 217) (oGrid.dm 217) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 217) oGrid.kl oGrid.kr 400 2000 ⟨false, 4119410890573255953373555709310838950472556675359355096264556068480544430588⟩ ⟨false, 192138238541650152355366606458931661038024581276577904748883590691965557152⟩ ⟨false, 4090807514925512813147433164614159004630655655293733610989606454864042776798⟩ ⟨false, 221659445277843870699629970992974409640240007809724281775739190273268283870⟩ = true := by
  decide +kernel

theorem b_217_2400 : bothLoop evalE (oGrid.idx 217) (oGrid.dm 217) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 217) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4090807514925512813147433164614159004630655655293733610989606454864042776798⟩ ⟨false, 221659445277843870699629970992974409640240007809724281775739190273268283870⟩ = true := by
  decide +kernel

theorem o_row_217 : oGrid.row evalE 217 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_217_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_217_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_217_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_217_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_217_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_217_2000).1 (bothLoop_sound b_217_2400).1))))))

theorem n_row_217 : nGrid.row evalE 217 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_217_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_217_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_217_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_217_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_217_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_217_2000).2 (bothLoop_sound b_217_2400).2))))))

theorem b_218_0 : bothSeg evalE (oGrid.idx 218) (oGrid.dm 218) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 218) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2302376073966201200498107478187811458663559389407011581893853055141960539224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_218_400 : bothSeg evalE (oGrid.idx 218) (oGrid.dm 218) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 218) oGrid.kl oGrid.kr 400 400 ⟨false, 2302376073966201200498107478187811458663559389407011581893853055141960539224⟩ ⟨false, 0⟩ ⟨false, 3721206011914371777278437848945181355325100867970999336457590283883563111028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_218_800 : bothSeg evalE (oGrid.idx 218) (oGrid.dm 218) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 218) oGrid.kl oGrid.kr 400 800 ⟨false, 3721206011914371777278437848945181355325100867970999336457590283883563111028⟩ ⟨false, 0⟩ ⟨false, 4231476720555251504511114416721704854974337922417688977733857789098974063358⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_218_1200 : bothSeg evalE (oGrid.idx 218) (oGrid.dm 218) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 218) oGrid.kl oGrid.kr 400 1200 ⟨false, 4231476720555251504511114416721704854974337922417688977733857789098974063358⟩ ⟨false, 0⟩ ⟨false, 4262628892337516279073716405438417233978047793886038958957699020326264727498⟩ ⟨false, 30548232898455186765889188554653104707912641102016024857789404632723864044⟩ = true := by
  decide +kernel

theorem b_218_1600 : bothSeg evalE (oGrid.idx 218) (oGrid.dm 218) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 218) oGrid.kl oGrid.kr 400 1600 ⟨false, 4262628892337516279073716405438417233978047793886038958957699020326264727498⟩ ⟨false, 30548232898455186765889188554653104707912641102016024857789404632723864044⟩ ⟨false, 4101361013146666117345579830901679173908459214007258878355305970462042834238⟩ ⟨false, 192167022208042375194092197446464647949351679698288862136007451659249627638⟩ = true := by
  decide +kernel

theorem b_218_2000 : bothSeg evalE (oGrid.idx 218) (oGrid.dm 218) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 218) oGrid.kl oGrid.kr 400 2000 ⟨false, 4101361013146666117345579830901679173908459214007258878355305970462042834238⟩ ⟨false, 192167022208042375194092197446464647949351679698288862136007451659249627638⟩ ⟨false, 4072994670998502116004990948980800017541578999328831478763312377306506376154⟩ ⟨false, 221461043325491272108384632616918033788299170194658607617830653691218059136⟩ = true := by
  decide +kernel

theorem b_218_2400 : bothLoop evalE (oGrid.idx 218) (oGrid.dm 218) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 218) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4072994670998502116004990948980800017541578999328831478763312377306506376154⟩ ⟨false, 221461043325491272108384632616918033788299170194658607617830653691218059136⟩ = true := by
  decide +kernel

theorem o_row_218 : oGrid.row evalE 218 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_218_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_218_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_218_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_218_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_218_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_218_2000).1 (bothLoop_sound b_218_2400).1))))))

theorem n_row_218 : nGrid.row evalE 218 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_218_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_218_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_218_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_218_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_218_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_218_2000).2 (bothLoop_sound b_218_2400).2))))))

theorem b_219_0 : bothSeg evalE (oGrid.idx 219) (oGrid.dm 219) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 219) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2293104416345911198965240747709636459117830761086336673013211098333286920208⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_219_400 : bothSeg evalE (oGrid.idx 219) (oGrid.dm 219) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 219) oGrid.kl oGrid.kr 400 400 ⟨false, 2293104416345911198965240747709636459117830761086336673013211098333286920208⟩ ⟨false, 0⟩ ⟨false, 3706152710310607801129611943912529285877633156340828050948105897881553444416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_219_800 : bothSeg evalE (oGrid.idx 219) (oGrid.dm 219) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 219) oGrid.kl oGrid.kr 400 800 ⟨false, 3706152710310607801129611943912529285877633156340828050948105897881553444416⟩ ⟨false, 0⟩ ⟨false, 4214051220046419595666734989384204737370537204196112521467390810948321954534⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_219_1200 : bothSeg evalE (oGrid.idx 219) (oGrid.dm 219) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 219) oGrid.kl oGrid.kr 400 1200 ⟨false, 4214051220046419595666734989384204737370537204196112521467390810948321954534⟩ ⟨false, 0⟩ ⟨false, 4244428501409258492612997287212518061131491772032002956444085317783621848016⟩ ⟨false, 30780455716371885648259053945768149955847603780434928152000915437984819292⟩ = true := by
  decide +kernel

theorem b_219_1600 : bothSeg evalE (oGrid.idx 219) (oGrid.dm 219) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 219) oGrid.kl oGrid.kr 400 1600 ⟨false, 4244428501409258492612997287212518061131491772032002956444085317783621848016⟩ ⟨false, 30780455716371885648259053945768149955847603780434928152000915437984819292⟩ ⟨false, 4083366019148370615083457145823049191349502861465936058414499167614932809440⟩ ⟨false, 192194807427930480013020485381037174382615067676804944599934818259295778868⟩ = true := by
  decide +kernel

theorem b_219_2000 : bothSeg evalE (oGrid.idx 219) (oGrid.dm 219) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 219) oGrid.kl oGrid.kr 400 2000 ⟨false, 4083366019148370615083457145823049191349502861465936058414499167614932809440⟩ ⟨false, 192194807427930480013020485381037174382615067676804944599934818259295778868⟩ ⟨false, 4055236988536739902483522200903194006401398049004222682367778441804894331994⟩ ⟨false, 221262671227627267968697432945569984227407022173280800647673930029691090250⟩ = true := by
  decide +kernel

theorem b_219_2400 : bothLoop evalE (oGrid.idx 219) (oGrid.dm 219) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 219) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4055236988536739902483522200903194006401398049004222682367778441804894331994⟩ ⟨false, 221262671227627267968697432945569984227407022173280800647673930029691090250⟩ = true := by
  decide +kernel

theorem o_row_219 : oGrid.row evalE 219 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_219_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_219_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_219_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_219_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_219_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_219_2000).1 (bothLoop_sound b_219_2400).1))))))

theorem n_row_219 : nGrid.row evalE 219 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_219_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_219_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_219_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_219_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_219_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_219_2000).2 (bothLoop_sound b_219_2400).2))))))

theorem b_220_0 : bothSeg evalE (oGrid.idx 220) (oGrid.dm 220) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 220) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2283861531297398830523475251311161120497653756944695076436839653886336819324⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_220_400 : bothSeg evalE (oGrid.idx 220) (oGrid.dm 220) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 220) oGrid.kl oGrid.kr 400 400 ⟨false, 2283861531297398830523475251311161120497653756944695076436839653886336819324⟩ ⟨false, 0⟩ ⟨false, 3691144496192669869016797005228896414001506655046516989178706717647150416190⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_220_800 : bothSeg evalE (oGrid.idx 220) (oGrid.dm 220) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 220) oGrid.kl oGrid.kr 400 800 ⟨false, 3691144496192669869016797005228896414001506655046516989178706717647150416190⟩ ⟨false, 0⟩ ⟨false, 4196676975961326578562247357569852144001398183634415210129505878662029599580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_220_1200 : bothSeg evalE (oGrid.idx 220) (oGrid.dm 220) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 220) oGrid.kl oGrid.kr 400 1200 ⟨false, 4196676975961326578562247357569852144001398183634415210129505878662029599580⟩ ⟨false, 0⟩ ⟨false, 4226288295099246648912247902338589548238578725431449631955749371559216166240⟩ ⟨false, 31006315946492998456138413157914241641417409142344569433942182219319604516⟩ = true := by
  decide +kernel

theorem b_220_1600 : bothSeg evalE (oGrid.idx 220) (oGrid.dm 220) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 220) oGrid.kl oGrid.kr 400 1600 ⟨false, 4226288295099246648912247902338589548238578725431449631955749371559216166240⟩ ⟨false, 31006315946492998456138413157914241641417409142344569433942182219319604516⟩ ⟨false, 4065425773322085315571916265659766273625236651817303431010972359525452011704⟩ ⟨false, 192221661847588107089274530360594410510519395607263131471967437428158747984⟩ = true := by
  decide +kernel

theorem b_220_2000 : bothSeg evalE (oGrid.idx 220) (oGrid.dm 220) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 220) oGrid.kl oGrid.kr 400 2000 ⟨false, 4065425773322085315571916265659766273625236651817303431010972359525452011704⟩ ⟨false, 192221661847588107089274530360594410510519395607263131471967437428158747984⟩ ⟨false, 4037534385893077181394637334778058761700178654693387509555273920126168715564⟩ ⟨false, 221064519948045044932261487792455406933882918081824940119856336976270368850⟩ = true := by
  decide +kernel

theorem b_220_2400 : bothLoop evalE (oGrid.idx 220) (oGrid.dm 220) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 220) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4037534385893077181394637334778058761700178654693387509555273920126168715564⟩ ⟨false, 221064519948045044932261487792455406933882918081824940119856336976270368850⟩ = true := by
  decide +kernel

theorem o_row_220 : oGrid.row evalE 220 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_220_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_220_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_220_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_220_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_220_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_220_2000).1 (bothLoop_sound b_220_2400).1))))))

theorem n_row_220 : nGrid.row evalE 220 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_220_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_220_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_220_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_220_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_220_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_220_2000).2 (bothLoop_sound b_220_2400).2))))))

theorem b_221_0 : bothSeg evalE (oGrid.idx 221) (oGrid.dm 221) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 221) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2274647357459518827547104795275727719321233231523715361854930943133435218930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_221_400 : bothSeg evalE (oGrid.idx 221) (oGrid.dm 221) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 221) oGrid.kl oGrid.kr 400 400 ⟨false, 2274647357459518827547104795275727719321233231523715361854930943133435218930⟩ ⟨false, 0⟩ ⟨false, 3676181283487921541033026013032616871057820795238483981888488081640423958224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_221_800 : bothSeg evalE (oGrid.idx 221) (oGrid.dm 221) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 221) oGrid.kl oGrid.kr 400 800 ⟨false, 3676181283487921541033026013032616871057820795238483981888488081640423958224⟩ ⟨false, 0⟩ ⟨false, 4179353901493286702444290900013158669377438126702972363573963460435456214396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_221_1200 : bothSeg evalE (oGrid.idx 221) (oGrid.dm 221) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 221) oGrid.kl oGrid.kr 400 1200 ⟨false, 4179353901493286702444290900013158669377438126702972363573963460435456214396⟩ ⟨false, 0⟩ ⟨false, 4208208212231071495902345375257800207276225972240801436506872573075246097240⟩ ⟨false, 31225788142335164044911704441006274898485323787433772507432029931568741574⟩ = true := by
  decide +kernel

theorem b_221_1600 : bothSeg evalE (oGrid.idx 221) (oGrid.dm 221) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 221) oGrid.kl oGrid.kr 400 1600 ⟨false, 4208208212231071495902345375257800207276225972240801436506872573075246097240⟩ ⟨false, 31225788142335164044911704441006274898485323787433772507432029931568741574⟩ ⟨false, 4047540005737647602845326979614182434635146750225440812602958819218380930524⟩ ⟨false, 192247681176898924546046500519295446063795526976453809930073180069853023424⟩ = true := by
  decide +kernel

theorem b_221_2000 : bothSeg evalE (oGrid.idx 221) (oGrid.dm 221) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 221) oGrid.kl oGrid.kr 400 2000 ⟨false, 4047540005737647602845326979614182434635146750225440812602958819218380930524⟩ ⟨false, 192247681176898924546046500519295446063795526976453809930073180069853023424⟩ ⟨false, 4019886569638925593618077161408584576534519078074441841776198981662908213334⟩ ⟨false, 220866934525965009267194598882326922132159861180196872628960692184298879986⟩ = true := by
  decide +kernel

theorem b_221_2400 : bothLoop evalE (oGrid.idx 221) (oGrid.dm 221) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 221) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4019886569638925593618077161408584576534519078074441841776198981662908213334⟩ ⟨false, 220866934525965009267194598882326922132159861180196872628960692184298879986⟩ = true := by
  decide +kernel

theorem o_row_221 : oGrid.row evalE 221 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_221_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_221_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_221_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_221_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_221_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_221_2000).1 (bothLoop_sound b_221_2400).1))))))

theorem n_row_221 : nGrid.row evalE 221 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_221_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_221_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_221_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_221_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_221_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_221_2000).2 (bothLoop_sound b_221_2400).2))))))

theorem b_222_0 : bothSeg evalE (oGrid.idx 222) (oGrid.dm 222) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 222) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2265461802576853173074064479873245121622580893648747534843071305963398710836⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_222_400 : bothSeg evalE (oGrid.idx 222) (oGrid.dm 222) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 222) oGrid.kl oGrid.kr 400 400 ⟨false, 2265461802576853173074064479873245121622580893648747534843071305963398710836⟩ ⟨false, 0⟩ ⟨false, 3661262941157058025928275692591232412548289988322786741270847428591609853632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_222_800 : bothSeg evalE (oGrid.idx 222) (oGrid.dm 222) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 222) oGrid.kl oGrid.kr 400 800 ⟨false, 3661262941157058025928275692591232412548289988322786741270847428591609853632⟩ ⟨false, 0⟩ ⟨false, 4162081848057104681355028994661376610032716599595820221581391549889733259618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_222_1200 : bothSeg evalE (oGrid.idx 222) (oGrid.dm 222) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 222) oGrid.kl oGrid.kr 400 1200 ⟨false, 4162081848057104681355028994661376610032716599595820221581391549889733259618⟩ ⟨false, 0⟩ ⟨false, 4190188221628051168310456907537607963487943169748254342434198659296978405786⟩ ⟨false, 31438733200042777349688702311208537970974347615635870344086511374286912984⟩ = true := by
  decide +kernel

theorem b_222_1600 : bothSeg evalE (oGrid.idx 222) (oGrid.dm 222) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 222) oGrid.kl oGrid.kr 400 1600 ⟨false, 4190188221628051168310456907537607963487943169748254342434198659296978405786⟩ ⟨false, 31438733200042777349688702311208537970974347615635870344086511374286912984⟩ ⟨false, 4029708670220506286344526939281521122753006780219866922639104575632093829884⟩ ⟨false, 192272948646151028635770665869031077092379284926385935236212829973217072996⟩ = true := by
  decide +kernel

theorem b_222_2000 : bothSeg evalE (oGrid.idx 222) (oGrid.dm 222) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 222) oGrid.kl oGrid.kr 400 2000 ⟨false, 4029708670220506286344526939281521122753006780219866922639104575632093829884⟩ ⟨false, 192272948646151028635770665869031077092379284926385935236212829973217072996⟩ ⟨false, 4002293505890018136605703305403623317042224566134423590333115755905045452010⟩ ⟨false, 220669554538192320503960507126064401926152283227349345212505967738155383064⟩ = true := by
  decide +kernel

theorem b_222_2400 : bothLoop evalE (oGrid.idx 222) (oGrid.dm 222) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 222) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4002293505890018136605703305403623317042224566134423590333115755905045452010⟩ ⟨false, 220669554538192320503960507126064401926152283227349345212505967738155383064⟩ = true := by
  decide +kernel

theorem o_row_222 : oGrid.row evalE 222 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_222_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_222_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_222_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_222_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_222_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_222_2000).1 (bothLoop_sound b_222_2400).1))))))

theorem n_row_222 : nGrid.row evalE 222 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_222_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_222_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_222_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_222_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_222_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_222_2000).2 (bothLoop_sound b_222_2400).2))))))

theorem b_223_0 : bothSeg evalE (oGrid.idx 223) (oGrid.dm 223) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 223) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2256304819070089395501871221319347057003104726209627590860418290653675409954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_223_400 : bothSeg evalE (oGrid.idx 223) (oGrid.dm 223) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 223) oGrid.kl oGrid.kr 400 400 ⟨false, 2256304819070089395501871221319347057003104726209627590860418290653675409954⟩ ⟨false, 0⟩ ⟨false, 3646389390044265201069756193796008380542574962338325901045606030114984051264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_223_800 : bothSeg evalE (oGrid.idx 223) (oGrid.dm 223) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 223) oGrid.kl oGrid.kr 400 800 ⟨false, 3646389390044265201069756193796008380542574962338325901045606030114984051264⟩ ⟨false, 0⟩ ⟨false, 4144860746156079222056797245988678593304766753881788109805721404007558143864⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_223_1200 : bothSeg evalE (oGrid.idx 223) (oGrid.dm 223) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 223) oGrid.kl oGrid.kr 400 1200 ⟨false, 4144860746156079222056797245988678593304766753881788109805721404007558143864⟩ ⟨false, 0⟩ ⟨false, 4172228300930367516941857989307341624091250091183268971354766446009136402880⟩ ⟨false, 31645104810842762681308011406172385467932729063681936135209673744843528744⟩ = true := by
  decide +kernel

theorem b_223_1600 : bothSeg evalE (oGrid.idx 223) (oGrid.dm 223) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 223) oGrid.kl oGrid.kr 400 1600 ⟨false, 4172228300930367516941857989307341624091250091183268971354766446009136402880⟩ ⟨false, 31645104810842762681308011406172385467932729063681936135209673744843528744⟩ ⟨false, 4011931760873271867981306349306542984677924311271373476435702782738298183014⟩ ⟨false, 192297441770586210023065708659969771389316369237829058841926364524086948102⟩ = true := by
  decide +kernel

theorem b_223_2000 : bothSeg evalE (oGrid.idx 223) (oGrid.dm 223) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 223) oGrid.kl oGrid.kr 400 2000 ⟨false, 4011931760873271867981306349306542984677924311271373476435702782738298183014⟩ ⟨false, 192297441770586210023065708659969771389316369237829058841926364524086948102⟩ ⟨false, 3984755191553218915329311957227703668221780380964407509437081421774858852120⟩ ⟨false, 220472280741664261000083836756264412645531778406560765356989561914164524552⟩ = true := by
  decide +kernel

theorem b_223_2400 : bothLoop evalE (oGrid.idx 223) (oGrid.dm 223) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 223) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3984755191553218915329311957227703668221780380964407509437081421774858852120⟩ ⟨false, 220472280741664261000083836756264412645531778406560765356989561914164524552⟩ = true := by
  decide +kernel

theorem o_row_223 : oGrid.row evalE 223 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_223_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_223_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_223_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_223_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_223_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_223_2000).1 (bothLoop_sound b_223_2400).1))))))

theorem n_row_223 : nGrid.row evalE 223 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_223_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_223_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_223_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_223_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_223_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_223_2000).2 (bothLoop_sound b_223_2400).2))))))

theorem b_224_0 : bothSeg evalE (oGrid.idx 224) (oGrid.dm 224) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 224) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2247176299171737325418485774841370702921662901003464658296928677527111722796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_224_400 : bothSeg evalE (oGrid.idx 224) (oGrid.dm 224) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 224) oGrid.kl oGrid.kr 400 400 ⟨false, 2247176299171737325418485774841370702921662901003464658296928677527111722796⟩ ⟨false, 0⟩ ⟨false, 3631560482972955092319248696326143671451232607989728421256838224674319340326⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_224_800 : bothSeg evalE (oGrid.idx 224) (oGrid.dm 224) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 224) oGrid.kl oGrid.kr 400 800 ⟨false, 3631560482972955092319248696326143671451232607989728421256838224674319340326⟩ ⟨false, 0⟩ ⟨false, 4127690444760369983143047783263406987710214352044495478305046949752227431014⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_224_1200 : bothSeg evalE (oGrid.idx 224) (oGrid.dm 224) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 224) oGrid.kl oGrid.kr 400 1200 ⟨false, 4127690444760369983143047783263406987710214352044495478305046949752227431014⟩ ⟨false, 0⟩ ⟨false, 4154328282647347605889880286199605280561281411113628104303458299622751458394⟩ ⟨false, 31844907500722062862472012866872534614491561831489614123479515589075866646⟩ = true := by
  decide +kernel

theorem b_224_1600 : bothSeg evalE (oGrid.idx 224) (oGrid.dm 224) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 224) oGrid.kl oGrid.kr 400 1600 ⟨false, 4154328282647347605889880286199605280561281411113628104303458299622751458394⟩ ⟨false, 31844907500722062862472012866872534614491561831489614123479515589075866646⟩ ⟨false, 3994209031569810583892987022988046875404020497386876181728323462386602523954⟩ ⟨false, 192321044504618648082110693485350580786065248047305307857537196906811077782⟩ = true := by
  decide +kernel

theorem b_224_2000 : bothSeg evalE (oGrid.idx 224) (oGrid.dm 224) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 224) oGrid.kl oGrid.kr 400 2000 ⟨false, 3994209031569810583892987022988046875404020497386876181728323462386602523954⟩ ⟨false, 192321044504618648082110693485350580786065248047305307857537196906811077782⟩ ⟨false, 3967271385016153940625058090902385118993267273374314247928072567822180837326⟩ ⟨false, 220275927330964275497267818127504106640752610429693620178324987210682666292⟩ = true := by
  decide +kernel

theorem b_224_2400 : bothLoop evalE (oGrid.idx 224) (oGrid.dm 224) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 224) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3967271385016153940625058090902385118993267273374314247928072567822180837326⟩ ⟨false, 220275927330964275497267818127504106640752610429693620178324987210682666292⟩ = true := by
  decide +kernel

theorem o_row_224 : oGrid.row evalE 224 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_224_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_224_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_224_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_224_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_224_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_224_2000).1 (bothLoop_sound b_224_2400).1))))))

theorem n_row_224 : nGrid.row evalE 224 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_224_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_224_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_224_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_224_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_224_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_224_2000).2 (bothLoop_sound b_224_2400).2))))))

theorem b_225_0 : bothSeg evalE (oGrid.idx 225) (oGrid.dm 225) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 225) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2238076202040550736338263112089686723856888250397808001715409290168132567482⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_225_400 : bothSeg evalE (oGrid.idx 225) (oGrid.dm 225) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 225) oGrid.kl oGrid.kr 400 400 ⟨false, 2238076202040550736338263112089686723856888250397808001715409290168132567482⟩ ⟨false, 0⟩ ⟨false, 3616776147004851783863181249350334932224947434606368608209343008061355840916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_225_800 : bothSeg evalE (oGrid.idx 225) (oGrid.dm 225) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 225) oGrid.kl oGrid.kr 400 800 ⟨false, 3616776147004851783863181249350334932224947434606368608209343008061355840916⟩ ⟨false, 0⟩ ⟨false, 4110570859415019456981941136024145149234297731981527124154612714101392354392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_225_1200 : bothSeg evalE (oGrid.idx 225) (oGrid.dm 225) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 225) oGrid.kl oGrid.kr 400 1200 ⟨false, 4110570859415019456981941136024145149234297731981527124154612714101392354392⟩ ⟨false, 0⟩ ⟨false, 4136488267966457913839118594660020367207469532572929892645405821500191073380⟩ ⟨false, 32037972042554291105362659353523557649119203383454270877946444809112055244⟩ = true := by
  decide +kernel

theorem b_225_1600 : bothSeg evalE (oGrid.idx 225) (oGrid.dm 225) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 225) oGrid.kl oGrid.kr 400 1600 ⟨false, 4136488267966457913839118594660020367207469532572929892645405821500191073380⟩ ⟨false, 32037972042554291105362659353523557649119203383454270877946444809112055244⟩ ⟨false, 3976540443780935555509122644829979218011638179967475530899808831340645237360⟩ ⟨false, 192343734603764437767700302196725111997389923044825023268289641368387446666⟩ = true := by
  decide +kernel

theorem b_225_2000 : bothSeg evalE (oGrid.idx 225) (oGrid.dm 225) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 225) oGrid.kl oGrid.kr 400 2000 ⟨false, 3976540443780935555509122644829979218011638179967475530899808831340645237360⟩ ⟨false, 192343734603764437767700302196725111997389923044825023268289641368387446666⟩ ⟨false, 3949842040888160523255356779560474812753940874997375797153214483300730231500⟩ ⟨false, 220079372195933620168564384318488617245649158766018653779179677700708872834⟩ = true := by
  decide +kernel

theorem b_225_2400 : bothLoop evalE (oGrid.idx 225) (oGrid.dm 225) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 225) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3949842040888160523255356779560474812753940874997375797153214483300730231500⟩ ⟨false, 220079372195933620168564384318488617245649158766018653779179677700708872834⟩ = true := by
  decide +kernel

theorem o_row_225 : oGrid.row evalE 225 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_225_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_225_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_225_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_225_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_225_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_225_2000).1 (bothLoop_sound b_225_2400).1))))))

theorem n_row_225 : nGrid.row evalE 225 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_225_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_225_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_225_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_225_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_225_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_225_2000).2 (bothLoop_sound b_225_2400).2))))))

theorem b_226_0 : bothSeg evalE (oGrid.idx 226) (oGrid.dm 226) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 226) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2229004422403013452235952114492946986169116091347677116521496300449029943396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_226_400 : bothSeg evalE (oGrid.idx 226) (oGrid.dm 226) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 226) oGrid.kl oGrid.kr 400 400 ⟨false, 2229004422403013452235952114492946986169116091347677116521496300449029943396⟩ ⟨false, 0⟩ ⟨false, 3602036289035284854936848744112848835749369355204479496161742642335669308612⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_226_800 : bothSeg evalE (oGrid.idx 226) (oGrid.dm 226) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 226) oGrid.kl oGrid.kr 400 800 ⟨false, 3602036289035284854936848744112848835749369355204479496161742642335669308612⟩ ⟨false, 0⟩ ⟨false, 4093501902384192246348352885913033439131216199296138063431566152036752083518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_226_1200 : bothSeg evalE (oGrid.idx 226) (oGrid.dm 226) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 226) oGrid.kl oGrid.kr 400 1200 ⟨false, 4093501902384192246348352885913033439131216199296138063431566152036752083518⟩ ⟨false, 0⟩ ⟨false, 4118708135387541330886147874430731914970536580842240810112767617603973928858⟩ ⟨false, 32224318402093654358252447040079237961860807732846155639063826397607550420⟩ = true := by
  decide +kernel

theorem b_226_1600 : bothSeg evalE (oGrid.idx 226) (oGrid.dm 226) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 226) oGrid.kl oGrid.kr 400 1600 ⟨false, 4118708135387541330886147874430731914970536580842240810112767617603973928858⟩ ⟨false, 32224318402093654358252447040079237961860807732846155639063826397607550420⟩ ⟨false, 3958925923326005543166212040443105437527066954932998234066960682479451263050⟩ ⟨false, 192365488643464894510282481653954882017872333606357788261683154766153380548⟩ = true := by
  decide +kernel

theorem b_226_2000 : bothSeg evalE (oGrid.idx 226) (oGrid.dm 226) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 226) oGrid.kl oGrid.kr 400 2000 ⟨false, 3958925923326005543166212040443105437527066954932998234066960682479451263050⟩ ⟨false, 192365488643464894510282481653954882017872333606357788261683154766153380548⟩ ⟨false, 3932467114883000846425883481662639159209458029234093613915989554571414312150⟩ ⟨false, 219882680253092589620565421683934587465367538308897566679929717648868902892⟩ = true := by
  decide +kernel

theorem b_226_2400 : bothLoop evalE (oGrid.idx 226) (oGrid.dm 226) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 226) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3932467114883000846425883481662639159209458029234093613915989554571414312150⟩ ⟨false, 219882680253092589620565421683934587465367538308897566679929717648868902892⟩ = true := by
  decide +kernel

theorem o_row_226 : oGrid.row evalE 226 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_226_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_226_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_226_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_226_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_226_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_226_2000).1 (bothLoop_sound b_226_2400).1))))))

theorem n_row_226 : nGrid.row evalE 226 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_226_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_226_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_226_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_226_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_226_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_226_2000).2 (bothLoop_sound b_226_2400).2))))))

theorem b_227_0 : bothSeg evalE (oGrid.idx 227) (oGrid.dm 227) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 227) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2219960912791752031254378185273066146276312792257753008257045380767107604580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_227_400 : bothSeg evalE (oGrid.idx 227) (oGrid.dm 227) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 227) oGrid.kl oGrid.kr 400 400 ⟨false, 2219960912791752031254378185273066146276312792257753008257045380767107604580⟩ ⟨false, 0⟩ ⟨false, 3587340777863443080410381530383613871120936974734101383553621872872893742568⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_227_800 : bothSeg evalE (oGrid.idx 227) (oGrid.dm 227) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 227) oGrid.kl oGrid.kr 400 800 ⟨false, 3587340777863443080410381530383613871120936974734101383553621872872893742568⟩ ⟨false, 0⟩ ⟨false, 4076483432875810494553761608449861173041486376314273096532913607508205759210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_227_1200 : bothSeg evalE (oGrid.idx 227) (oGrid.dm 227) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 227) oGrid.kl oGrid.kr 400 1200 ⟨false, 4076483432875810494553761608449861173041486376314273096532913607508205759210⟩ ⟨false, 0⟩ ⟨false, 4100987792776547046651602130291653779914449651387151351378672783948679135294⟩ ⟨false, 32403867286857629325629232765398734644749044645691993287925127784214768402⟩ = true := by
  decide +kernel

theorem b_227_1600 : bothSeg evalE (oGrid.idx 227) (oGrid.dm 227) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 227) oGrid.kl oGrid.kr 400 1600 ⟨false, 4100987792776547046651602130291653779914449651387151351378672783948679135294⟩ ⟨false, 32403867286857629325629232765398734644749044645691993287925127784214768402⟩ ⟨false, 3941365199707709249219849886747526870960967188396306287901390771435168663968⟩ ⟨false, 192386380937425762794855715595108680684576919038563787926871888248605027976⟩ = true := by
  decide +kernel

theorem b_227_2000 : bothSeg evalE (oGrid.idx 227) (oGrid.dm 227) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 227) oGrid.kl oGrid.kr 400 2000 ⟨false, 3941365199707709249219849886747526870960967188396306287901390771435168663968⟩ ⟨false, 192386380937425762794855715595108680684576919038563787926871888248605027976⟩ ⟨false, 3915146311908385215715785681504470422324501812068668387028506896998291568054⟩ ⟨false, 219687082931979918874768465536580468989782608888107035776239465583972848830⟩ = true := by
  decide +kernel

theorem b_227_2400 : bothLoop evalE (oGrid.idx 227) (oGrid.dm 227) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 227) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3915146311908385215715785681504470422324501812068668387028506896998291568054⟩ ⟨false, 219687082931979918874768465536580468989782608888107035776239465583972848830⟩ = true := by
  decide +kernel

theorem o_row_227 : oGrid.row evalE 227 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_227_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_227_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_227_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_227_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_227_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_227_2000).1 (bothLoop_sound b_227_2400).1))))))

theorem n_row_227 : nGrid.row evalE 227 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_227_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_227_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_227_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_227_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_227_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_227_2000).2 (bothLoop_sound b_227_2400).2))))))

theorem b_228_0 : bothSeg evalE (oGrid.idx 228) (oGrid.dm 228) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 228) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2210945578865157558031701922480632731863413030516028373378385529363885174960⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_228_400 : bothSeg evalE (oGrid.idx 228) (oGrid.dm 228) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 228) oGrid.kl oGrid.kr 400 400 ⟨false, 2210945578865157558031701922480632731863413030516028373378385529363885174960⟩ ⟨false, 0⟩ ⟨false, 3572689529811781478672460196860910584979476421340949600615990946121549088134⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_228_800 : bothSeg evalE (oGrid.idx 228) (oGrid.dm 228) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 228) oGrid.kl oGrid.kr 400 800 ⟨false, 3572689529811781478672460196860910584979476421340949600615990946121549088134⟩ ⟨false, 0⟩ ⟨false, 4059515348135939778884547429672644888887768039073095192710419959584209537224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_228_1200 : bothSeg evalE (oGrid.idx 228) (oGrid.dm 228) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 228) oGrid.kl oGrid.kr 400 1200 ⟨false, 4059515348135939778884547429672644888887768039073095192710419959584209537224⟩ ⟨false, 0⟩ ⟨false, 4083327104853311228189430252913170395658801221394004132565763609354365725144⟩ ⟨false, 32576670661228448875850945222964639212060914476287527335202361316829006338⟩ = true := by
  decide +kernel

theorem b_228_1600 : bothSeg evalE (oGrid.idx 228) (oGrid.dm 228) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 228) oGrid.kl oGrid.kr 400 1600 ⟨false, 4083327104853311228189430252913170395658801221394004132565763609354365725144⟩ ⟨false, 32576670661228448875850945222964639212060914476287527335202361316829006338⟩ ⟨false, 3923858321175184836518373663471862120919111430153205451428751765196697968220⟩ ⟨false, 192406327879221561580264798381574209051405358015951969325986333230186712500⟩ = true := by
  decide +kernel

theorem b_228_2000 : bothSeg evalE (oGrid.idx 228) (oGrid.dm 228) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 228) oGrid.kl oGrid.kr 400 2000 ⟨false, 3923858321175184836518373663471862120919111430153205451428751765196697968220⟩ ⟨false, 192406327879221561580264798381574209051405358015951969325986333230186712500⟩ ⟨false, 3897879650884920761229187324841423707246889047488582822084508742193585267826⟩ ⟨false, 219491181096097473721221927240506845620307603181871459099553650556777326280⟩ = true := by
  decide +kernel

theorem b_228_2400 : bothLoop evalE (oGrid.idx 228) (oGrid.dm 228) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 228) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3897879650884920761229187324841423707246889047488582822084508742193585267826⟩ ⟨false, 219491181096097473721221927240506845620307603181871459099553650556777326280⟩ = true := by
  decide +kernel

theorem o_row_228 : oGrid.row evalE 228 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_228_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_228_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_228_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_228_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_228_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_228_2000).1 (bothLoop_sound b_228_2400).1))))))

theorem n_row_228 : nGrid.row evalE 228 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_228_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_228_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_228_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_228_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_228_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_228_2000).2 (bothLoop_sound b_228_2400).2))))))

theorem b_229_0 : bothSeg evalE (oGrid.idx 229) (oGrid.dm 229) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 229) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2201958331009522618858767039549481621878367157039916423033315461808903874202⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_229_400 : bothSeg evalE (oGrid.idx 229) (oGrid.dm 229) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 229) oGrid.kl oGrid.kr 400 400 ⟨false, 2201958331009522618858767039549481621878367157039916423033315461808903874202⟩ ⟨false, 0⟩ ⟨false, 3558082383284180180128643338988511642511788745840732965880378886848741291918⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_229_800 : bothSeg evalE (oGrid.idx 229) (oGrid.dm 229) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 229) oGrid.kl oGrid.kr 400 800 ⟨false, 3558082383284180180128643338988511642511788745840732965880378886848741291918⟩ ⟨false, 0⟩ ⟨false, 4042597505077701392621124394860962786615387967484441162421488629752000994618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_229_1200 : bothSeg evalE (oGrid.idx 229) (oGrid.dm 229) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 229) oGrid.kl oGrid.kr 400 1200 ⟨false, 4042597505077701392621124394860962786615387967484441162421488629752000994618⟩ ⟨false, 0⟩ ⟨false, 4065726063580510171313602120676932000178017812339984445786627386752922300884⟩ ⟨false, 32742614749005583947894954512348634565118058446725055222728540736692757810⟩ = true := by
  decide +kernel

theorem b_229_1600 : bothSeg evalE (oGrid.idx 229) (oGrid.dm 229) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 229) oGrid.kl oGrid.kr 400 1600 ⟨false, 4065726063580510171313602120676932000178017812339984445786627386752922300884⟩ ⟨false, 32742614749005583947894954512348634565118058446725055222728540736692757810⟩ ⟨false, 3906405002320067935545371541819800092410592444821254011159666614113491314392⟩ ⟨false, 192425439140049341917994806997202734912971477800167373839210501775491528296⟩ = true := by
  decide +kernel

theorem b_229_2000 : bothSeg evalE (oGrid.idx 229) (oGrid.dm 229) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 229) oGrid.kl oGrid.kr 400 2000 ⟨false, 3906405002320067935545371541819800092410592444821254011159666614113491314392⟩ ⟨false, 192425439140049341917994806997202734912971477800167373839210501775491528296⟩ ⟨false, 3880666895093857679309762284694321258684972375150147979136906587238702348206⟩ ⟨false, 219295446841932014205488957598976624092991555400350935831356430332885040018⟩ = true := by
  decide +kernel

theorem b_229_2400 : bothLoop evalE (oGrid.idx 229) (oGrid.dm 229) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 229) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3880666895093857679309762284694321258684972375150147979136906587238702348206⟩ ⟨false, 219295446841932014205488957598976624092991555400350935831356430332885040018⟩ = true := by
  decide +kernel

theorem o_row_229 : oGrid.row evalE 229 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_229_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_229_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_229_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_229_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_229_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_229_2000).1 (bothLoop_sound b_229_2400).1))))))

theorem n_row_229 : nGrid.row evalE 229 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_229_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_229_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_229_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_229_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_229_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_229_2000).2 (bothLoop_sound b_229_2400).2))))))

theorem b_230_0 : bothSeg evalE (oGrid.idx 230) (oGrid.dm 230) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 230) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2192999137571393113249890942261390726919842213380391829248829423070903762442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_230_400 : bothSeg evalE (oGrid.idx 230) (oGrid.dm 230) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 230) oGrid.kl oGrid.kr 400 400 ⟨false, 2192999137571393113249890942261390726919842213380391829248829423070903762442⟩ ⟨false, 0⟩ ⟨false, 3543519320654459946612185433022421699454726799690934189098797692371021940860⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_230_800 : bothSeg evalE (oGrid.idx 230) (oGrid.dm 230) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 230) oGrid.kl oGrid.kr 400 800 ⟨false, 3543519320654459946612185433022421699454726799690934189098797692371021940860⟩ ⟨false, 0⟩ ⟨false, 4025729863633302159462802091628529097058619280440251451812196784313060892824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_230_1200 : bothSeg evalE (oGrid.idx 230) (oGrid.dm 230) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 230) oGrid.kl oGrid.kr 400 1200 ⟨false, 4025729863633302159462802091628529097058619280440251451812196784313060892824⟩ ⟨false, 0⟩ ⟨false, 4048184613653353866157587020377483290663139867783162070276854925413061549496⟩ ⟨false, 32901720763172730884150596674495856835696720432692564745792932842775279204⟩ = true := by
  decide +kernel

theorem b_230_1600 : bothSeg evalE (oGrid.idx 230) (oGrid.dm 230) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 230) oGrid.kl oGrid.kr 400 1600 ⟨false, 4048184613653353866157587020377483290663139867783162070276854925413061549496⟩ ⟨false, 32901720763172730884150596674495856835696720432692564745792932842775279204⟩ ⟨false, 3889005264784341528534279106868749902586966179754330112403928794383372318310⟩ ⟨false, 192443688367755428887178035693136289923527039763838845005827107366740194874⟩ = true := by
  decide +kernel

theorem b_230_2000 : bothSeg evalE (oGrid.idx 230) (oGrid.dm 230) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 230) oGrid.kl oGrid.kr 400 2000 ⟨false, 3889005264784341528534279106868749902586966179754330112403928794383372318310⟩ ⟨false, 192443688367755428887178035693136289923527039763838845005827107366740194874⟩ ⟨false, 3863508053608057991615675575464730771835258994464402394369821369892986165444⟩ ⟨false, 219100370723612846903728446124256605383310775062105143287405085654557763854⟩ = true := by
  decide +kernel

theorem b_230_2400 : bothLoop evalE (oGrid.idx 230) (oGrid.dm 230) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 230) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3863508053608057991615675575464730771835258994464402394369821369892986165444⟩ ⟨false, 219100370723612846903728446124256605383310775062105143287405085654557763854⟩ = true := by
  decide +kernel

theorem o_row_230 : oGrid.row evalE 230 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_230_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_230_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_230_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_230_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_230_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_230_2000).1 (bothLoop_sound b_230_2400).1))))))

theorem n_row_230 : nGrid.row evalE 230 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_230_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_230_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_230_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_230_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_230_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_230_2000).2 (bothLoop_sound b_230_2400).2))))))

theorem b_231_0 : bothSeg evalE (oGrid.idx 231) (oGrid.dm 231) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 231) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2184067890384937119700520334950184991851495844948448225852712787548626074654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_231_400 : bothSeg evalE (oGrid.idx 231) (oGrid.dm 231) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 231) oGrid.kl oGrid.kr 400 400 ⟨false, 2184067890384937119700520334950184991851495844948448225852712787548626074654⟩ ⟨false, 0⟩ ⟨false, 3529000184749362584984337885521974887970248955015404242607826864030329038382⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_231_800 : bothSeg evalE (oGrid.idx 231) (oGrid.dm 231) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 231) oGrid.kl oGrid.kr 400 800 ⟨false, 3529000184749362584984337885521974887970248955015404242607826864030329038382⟩ ⟨false, 0⟩ ⟨false, 4008912276718102385286139569026856376062709807970802767189733774099653792016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_231_1200 : bothSeg evalE (oGrid.idx 231) (oGrid.dm 231) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 231) oGrid.kl oGrid.kr 400 1200 ⟨false, 4008912276718102385286139569026856376062709807970802767189733774099653792016⟩ ⟨false, 0⟩ ⟨false, 4030702643107057857561338625889698234410486350397546995368468758989065013896⟩ ⟨false, 33053935190256115395813585958042494102308036867286687984714269275544840384⟩ = true := by
  decide +kernel

theorem b_231_1600 : bothSeg evalE (oGrid.idx 231) (oGrid.dm 231) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 231) oGrid.kl oGrid.kr 400 1600 ⟨false, 4030702643107057857561338625889698234410486350397546995368468758989065013896⟩ ⟨false, 33053935190256115395813585958042494102308036867286687984714269275544840384⟩ ⟨false, 3871659093904194791410565361508719416630407111183880578564474205710207743990⟩ ⟨false, 192460989466998401053953615728313956644840311085323781579056359860862923952⟩ = true := by
  decide +kernel

theorem b_231_2000 : bothSeg evalE (oGrid.idx 231) (oGrid.dm 231) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 231) oGrid.kl oGrid.kr 400 2000 ⟨false, 3871659093904194791410565361508719416630407111183880578564474205710207743990⟩ ⟨false, 192460989466998401053953615728313956644840311085323781579056359860862923952⟩ ⟨false, 3846403102138742175302289957262528365429306713110843196855024961791550219584⟩ ⟨false, 218905246526161311663554609254346232461249911025969166707185070471122121476⟩ = true := by
  decide +kernel

theorem b_231_2400 : bothLoop evalE (oGrid.idx 231) (oGrid.dm 231) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 231) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3846403102138742175302289957262528365429306713110843196855024961791550219584⟩ ⟨false, 218905246526161311663554609254346232461249911025969166707185070471122121476⟩ = true := by
  decide +kernel

theorem o_row_231 : oGrid.row evalE 231 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_231_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_231_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_231_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_231_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_231_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_231_2000).1 (bothLoop_sound b_231_2400).1))))))

theorem n_row_231 : nGrid.row evalE 231 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_231_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_231_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_231_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_231_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_231_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_231_2000).2 (bothLoop_sound b_231_2400).2))))))

theorem b_232_0 : bothSeg evalE (oGrid.idx 232) (oGrid.dm 232) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 232) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2175164541230044662522261200021566821962146394298907189870100292270890074996⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_232_400 : bothSeg evalE (oGrid.idx 232) (oGrid.dm 232) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 232) oGrid.kl oGrid.kr 400 400 ⟨false, 2175164541230044662522261200021566821962146394298907189870100292270890074996⟩ ⟨false, 0⟩ ⟨false, 3514524891795774087577572420701307784611467249219052589486217922910550339044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_232_800 : bothSeg evalE (oGrid.idx 232) (oGrid.dm 232) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 232) oGrid.kl oGrid.kr 400 800 ⟨false, 3514524891795774087577572420701307784611467249219052589486217922910550339044⟩ ⟨false, 0⟩ ⟨false, 3992144642546272725328570937970975060703331851352887869034011452561807559576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_232_1200 : bothSeg evalE (oGrid.idx 232) (oGrid.dm 232) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 232) oGrid.kl oGrid.kr 400 1200 ⟨false, 3992144642546272725328570937970975060703331851352887869034011452561807559576⟩ ⟨false, 0⟩ ⟨false, 4013279991970236137095793471042715226564322298976015458380845072560059734372⟩ ⟨false, 33199320560685219793635018035643570525589381841906866043937527911458449180⟩ = true := by
  decide +kernel

theorem b_232_1600 : bothSeg evalE (oGrid.idx 232) (oGrid.dm 232) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 232) oGrid.kl oGrid.kr 400 1600 ⟨false, 4013279991970236137095793471042715226564322298976015458380845072560059734372⟩ ⟨false, 33199320560685219793635018035643570525589381841906866043937527911458449180⟩ ⟨false, 3854366185548128416056633075478577624890510614229193100697229979384684891006⟩ ⟨false, 192477519300669256946489563483284254422757522303691099224595307303700006600⟩ = true := by
  decide +kernel

theorem b_232_2000 : bothSeg evalE (oGrid.idx 232) (oGrid.dm 232) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 232) oGrid.kl oGrid.kr 400 2000 ⟨false, 3854366185548128416056633075478577624890510614229193100697229979384684891006⟩ ⟨false, 192477519300669256946489563483284254422757522303691099224595307303700006600⟩ ⟨false, 3829351728607747302816559380027749545439619006893794706424015592360273067372⟩ ⟨false, 218710379208522164041248939925247913889762880857746927178559095355250125394⟩ = true := by
  decide +kernel

theorem b_232_2400 : bothLoop evalE (oGrid.idx 232) (oGrid.dm 232) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 232) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3829351728607747302816559380027749545439619006893794706424015592360273067372⟩ ⟨false, 218710379208522164041248939925247913889762880857746927178559095355250125394⟩ = true := by
  decide +kernel

theorem o_row_232 : oGrid.row evalE 232 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_232_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_232_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_232_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_232_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_232_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_232_2000).1 (bothLoop_sound b_232_2400).1))))))

theorem n_row_232 : nGrid.row evalE 232 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_232_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_232_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_232_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_232_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_232_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_232_2000).2 (bothLoop_sound b_232_2400).2))))))

theorem b_233_0 : bothSeg evalE (oGrid.idx 233) (oGrid.dm 233) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 233) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2166289028964755939697143011848704968264975651545761928168703393118694009172⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_233_400 : bothSeg evalE (oGrid.idx 233) (oGrid.dm 233) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 233) oGrid.kl oGrid.kr 400 400 ⟨false, 2166289028964755939697143011848704968264975651545761928168703393118694009172⟩ ⟨false, 0⟩ ⟨false, 3500093364925234492661790322529064651067630510470729804953915307504787945868⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_233_800 : bothSeg evalE (oGrid.idx 233) (oGrid.dm 233) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 233) oGrid.kl oGrid.kr 400 800 ⟨false, 3500093364925234492661790322529064651067630510470729804953915307504787945868⟩ ⟨false, 0⟩ ⟨false, 3975426901834549963620609327388401646517753716254481478451864172160742211176⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_233_1200 : bothSeg evalE (oGrid.idx 233) (oGrid.dm 233) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 233) oGrid.kl oGrid.kr 400 1200 ⟨false, 3975426901834549963620609327388401646517753716254481478451864172160742211176⟩ ⟨false, 0⟩ ⟨false, 3995916674419676212634385718899612064981028594843856425326688013327495821314⟩ ⟨false, 33337804100594373918497890294828975456324232867823419254497316795070794772⟩ = true := by
  decide +kernel

theorem b_233_1600 : bothSeg evalE (oGrid.idx 233) (oGrid.dm 233) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 233) oGrid.kl oGrid.kr 400 1600 ⟨false, 3995916674419676212634385718899612064981028594843856425326688013327495821314⟩ ⟨false, 33337804100594373918497890294828975456324232867823419254497316795070794772⟩ ⟨false, 3837126487348023631390529479970470023562312043421285423403827968407108934342⟩ ⟨false, 192493486790310782524637115997080186822997772393208276296370937285355656120⟩ = true := by
  decide +kernel

theorem b_233_2000 : bothSeg evalE (oGrid.idx 233) (oGrid.dm 233) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 233) oGrid.kl oGrid.kr 400 2000 ⟨false, 3837126487348023631390529479970470023562312043421285423403827968407108934342⟩ ⟨false, 192493486790310782524637115997080186822997772393208276296370937285355656120⟩ ⟨false, 3812353881109084040953909735384480883053081199328300987124729360078451449682⟩ ⟨false, 218516137082049159075801779712693663659744173781780549879165448153492109234⟩ = true := by
  decide +kernel

theorem b_233_2400 : bothLoop evalE (oGrid.idx 233) (oGrid.dm 233) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 233) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3812353881109084040953909735384480883053081199328300987124729360078451449682⟩ ⟨false, 218516137082049159075801779712693663659744173781780549879165448153492109234⟩ = true := by
  decide +kernel

theorem o_row_233 : oGrid.row evalE 233 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_233_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_233_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_233_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_233_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_233_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_233_2000).1 (bothLoop_sound b_233_2400).1))))))

theorem n_row_233 : nGrid.row evalE 233 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_233_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_233_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_233_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_233_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_233_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_233_2000).2 (bothLoop_sound b_233_2400).2))))))

theorem b_234_0 : bothSeg evalE (oGrid.idx 234) (oGrid.dm 234) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 234) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2157441234955677863075122983481639607520526903020903959747013238288495013942⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_234_400 : bothSeg evalE (oGrid.idx 234) (oGrid.dm 234) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 234) oGrid.kl oGrid.kr 400 400 ⟨false, 2157441234955677863075122983481639607520526903020903959747013238288495013942⟩ ⟨false, 0⟩ ⟨false, 3485705427603543558158352010764493401421153329986640257044474255666023047546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_234_800 : bothSeg evalE (oGrid.idx 234) (oGrid.dm 234) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 234) oGrid.kl oGrid.kr 400 800 ⟨false, 3485705427603543558158352010764493401421153329986640257044474255666023047546⟩ ⟨false, 0⟩ ⟨false, 3958758831807064375262793804152812152066895186956861918998795083375869956916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_234_1200 : bothSeg evalE (oGrid.idx 234) (oGrid.dm 234) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 234) oGrid.kl oGrid.kr 400 1200 ⟨false, 3958758831807064375262793804152812152066895186956861918998795083375869956916⟩ ⟨false, 0⟩ ⟨false, 3978612479650757510536867969753439756199104765598582458656882276985505036168⟩ ⟨false, 33469445646236898359248908301395424368215267979498505558999211718882157148⟩ = true := by
  decide +kernel

theorem b_234_1600 : bothSeg evalE (oGrid.idx 234) (oGrid.dm 234) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 234) oGrid.kl oGrid.kr 400 1600 ⟨false, 3978612479650757510536867969753439756199104765598582458656882276985505036168⟩ ⟨false, 33469445646236898359248908301395424368215267979498505558999211718882157148⟩ ⟨false, 3819939979136346105830085604304156594507807368175448769017798554000621172484⟩ ⟨false, 192508521318819922646137247663489997577777752234855691347979221214881299398⟩ = true := by
  decide +kernel

theorem b_234_2000 : bothSeg evalE (oGrid.idx 234) (oGrid.dm 234) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 234) oGrid.kl oGrid.kr 400 2000 ⟨false, 3819939979136346105830085604304156594507807368175448769017798554000621172484⟩ ⟨false, 192508521318819922646137247663489997577777752234855691347979221214881299398⟩ ⟨false, 3795409538728279604936676230134888335912542201091401931545845817487390803112⟩ ⟨false, 218322294481661276349465227882748280283127519815782474133960054845972672870⟩ = true := by
  decide +kernel

theorem b_234_2400 : bothLoop evalE (oGrid.idx 234) (oGrid.dm 234) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 234) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3795409538728279604936676230134888335912542201091401931545845817487390803112⟩ ⟨false, 218322294481661276349465227882748280283127519815782474133960054845972672870⟩ = true := by
  decide +kernel

theorem o_row_234 : oGrid.row evalE 234 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_234_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_234_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_234_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_234_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_234_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_234_2000).1 (bothLoop_sound b_234_2400).1))))))

theorem n_row_234 : nGrid.row evalE 234 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_234_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_234_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_234_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_234_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_234_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_234_2000).2 (bothLoop_sound b_234_2400).2))))))

theorem b_235_0 : bothSeg evalE (oGrid.idx 235) (oGrid.dm 235) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 235) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2148621114786428497606528788954336947679491319229642345563038661979565361038⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_235_400 : bothSeg evalE (oGrid.idx 235) (oGrid.dm 235) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 235) oGrid.kl oGrid.kr 400 400 ⟨false, 2148621114786428497606528788954336947679491319229642345563038661979565361038⟩ ⟨false, 0⟩ ⟨false, 3471361049156128657259431673307736303397414990731827177340652770800188096444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_235_800 : bothSeg evalE (oGrid.idx 235) (oGrid.dm 235) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 235) oGrid.kl oGrid.kr 400 800 ⟨false, 3471361049156128657259431673307736303397414990731827177340652770800188096444⟩ ⟨false, 0⟩ ⟨false, 3942140439599710473883868173535387379886093758606936529996916944183322947564⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_235_1200 : bothSeg evalE (oGrid.idx 235) (oGrid.dm 235) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 235) oGrid.kl oGrid.kr 400 1200 ⟨false, 3942140439599710473883868173535387379886093758606936529996916944183322947564⟩ ⟨false, 0⟩ ⟨false, 3961367254033394836310849621356051561497045219689317550924594530399913393320⟩ ⟨false, 33594297938217134329683963496900266426360090668896038546115248102787511618⟩ = true := by
  decide +kernel

theorem b_235_1600 : bothSeg evalE (oGrid.idx 235) (oGrid.dm 235) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 235) oGrid.kl oGrid.kr 400 1600 ⟨false, 3961367254033394836310849621356051561497045219689317550924594530399913393320⟩ ⟨false, 33594297938217134329683963496900266426360090668896038546115248102787511618⟩ ⟨false, 3802806350361960356443637356644631143419645856725799888229889234850272442972⟩ ⟨false, 192522797270477831707419007359135195593114510534361784908314207611955266016⟩ = true := by
  decide +kernel

theorem b_235_2000 : bothSeg evalE (oGrid.idx 235) (oGrid.dm 235) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 235) oGrid.kl oGrid.kr 400 2000 ⟨false, 3802806350361960356443637356644631143419645856725799888229889234850272442972⟩ ⟨false, 192522797270477831707419007359135195593114510534361784908314207611955266016⟩ ⟨false, 3778518376509849396876498663148423565111532446769251871909477377097666237558⟩ ⟨false, 218128457336169342121467110634261921742302344442340807655203396000878286928⟩ = true := by
  decide +kernel

theorem b_235_2400 : bothLoop evalE (oGrid.idx 235) (oGrid.dm 235) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 235) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3778518376509849396876498663148423565111532446769251871909477377097666237558⟩ ⟨false, 218128457336169342121467110634261921742302344442340807655203396000878286928⟩ = true := by
  decide +kernel

theorem o_row_235 : oGrid.row evalE 235 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_235_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_235_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_235_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_235_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_235_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_235_2000).1 (bothLoop_sound b_235_2400).1))))))

theorem n_row_235 : nGrid.row evalE 235 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_235_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_235_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_235_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_235_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_235_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_235_2000).2 (bothLoop_sound b_235_2400).2))))))

theorem b_236_0 : bothSeg evalE (oGrid.idx 236) (oGrid.dm 236) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 236) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2139828586319789804533174716994796082501140038942942475756191429437858763136⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_236_400 : bothSeg evalE (oGrid.idx 236) (oGrid.dm 236) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 236) oGrid.kl oGrid.kr 400 400 ⟨false, 2139828586319789804533174716994796082501140038942942475756191429437858763136⟩ ⟨false, 0⟩ ⟨false, 3457060088914254440992738272478368679328618755958055523457921502341277775178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_236_800 : bothSeg evalE (oGrid.idx 236) (oGrid.dm 236) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 236) oGrid.kl oGrid.kr 400 800 ⟨false, 3457060088914254440992738272478368679328618755958055523457921502341277775178⟩ ⟨false, 0⟩ ⟨false, 3925571562224556331268560319029181936176603523990359619642623205819640155802⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_236_1200 : bothSeg evalE (oGrid.idx 236) (oGrid.dm 236) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 236) oGrid.kl oGrid.kr 400 1200 ⟨false, 3925571562224556331268560319029181936176603523990359619642623205819640155802⟩ ⟨false, 0⟩ ⟨false, 3944180882100257796616066889183462938824816270115391975562378226182805883762⟩ ⟨false, 33712248009732507746899651698440379742881298131610261387862074732689306130⟩ = true := by
  decide +kernel

theorem b_236_1600 : bothSeg evalE (oGrid.idx 236) (oGrid.dm 236) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 236) oGrid.kl oGrid.kr 400 1600 ⟨false, 3944180882100257796616066889183462938824816270115391975562378226182805883762⟩ ⟨false, 33712248009732507746899651698440379742881298131610261387862074732689306130⟩ ⟨false, 3785725680048859844662019418849022566473549288500181002476554954774640936306⟩ ⟨false, 192536063079220842208932431511190620120457927767661626128178080566933363450⟩ = true := by
  decide +kernel

theorem b_236_2000 : bothSeg evalE (oGrid.idx 236) (oGrid.dm 236) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 236) oGrid.kl oGrid.kr 400 2000 ⟨false, 3785725680048859844662019418849022566473549288500181002476554954774640936306⟩ ⟨false, 192536063079220842208932431511190620120457927767661626128178080566933363450⟩ ⟨false, 3761680464541913933875918821347314009445741369059187123747391246583122787414⟩ ⟨false, 217934623311018839341585503702557326022795054408214528787954619535897652122⟩ = true := by
  decide +kernel

theorem b_236_2400 : bothLoop evalE (oGrid.idx 236) (oGrid.dm 236) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 236) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3761680464541913933875918821347314009445741369059187123747391246583122787414⟩ ⟨false, 217934623311018839341585503702557326022795054408214528787954619535897652122⟩ = true := by
  decide +kernel

theorem o_row_236 : oGrid.row evalE 236 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_236_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_236_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_236_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_236_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_236_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_236_2000).1 (bothLoop_sound b_236_2400).1))))))

theorem n_row_236 : nGrid.row evalE 236 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_236_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_236_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_236_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_236_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_236_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_236_2000).2 (bothLoop_sound b_236_2400).2))))))

theorem b_237_0 : bothSeg evalE (oGrid.idx 237) (oGrid.dm 237) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 237) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2131063582987818952496869372625324844729437171644680764560170558187481514922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_237_400 : bothSeg evalE (oGrid.idx 237) (oGrid.dm 237) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 237) oGrid.kl oGrid.kr 400 400 ⟨false, 2131063582987818952496869372625324844729437171644680764560170558187481514922⟩ ⟨false, 0⟩ ⟨false, 3442802441050891350968875150816387924194476462914730727439171258389876670734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_237_800 : bothSeg evalE (oGrid.idx 237) (oGrid.dm 237) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 237) oGrid.kl oGrid.kr 400 800 ⟨false, 3442802441050891350968875150816387924194476462914730727439171258389876670734⟩ ⟨false, 0⟩ ⟨false, 3909052074006603727294672893777286617199840129067571468499720911991166868502⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_237_1200 : bothSeg evalE (oGrid.idx 237) (oGrid.dm 237) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 237) oGrid.kl oGrid.kr 400 1200 ⟨false, 3909052074006603727294672893777286617199840129067571468499720911991166868502⟩ ⟨false, 0⟩ ⟨false, 3927053252392727599354577799314850960305099234461595880793583050544171315698⟩ ⟨false, 33823370346824245135032486202231186751079153313155973532004589006365263614⟩ = true := by
  decide +kernel

theorem b_237_1600 : bothSeg evalE (oGrid.idx 237) (oGrid.dm 237) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 237) oGrid.kl oGrid.kr 400 1600 ⟨false, 3927053252392727599354577799314850960305099234461595880793583050544171315698⟩ ⟨false, 33823370346824245135032486202231186751079153313155973532004589006365263614⟩ ⟨false, 3768697682415408040556634678585403109083886106589352130697329156758461457274⟩ ⟨false, 192548621780833230401470251700510330755876515538300418012796515590227107210⟩ = true := by
  decide +kernel

theorem b_237_2000 : bothSeg evalE (oGrid.idx 237) (oGrid.dm 237) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 237) oGrid.kl oGrid.kr 400 2000 ⟨false, 3768697682415408040556634678585403109083886106589352130697329156758461457274⟩ ⟨false, 192548621780833230401470251700510330755876515538300418012796515590227107210⟩ ⟨false, 3744895503725867938212453390201771883805849278433228042983586995432744298124⟩ ⟨false, 217741787003523259022517751518644739061363844980966569132833819812727665390⟩ = true := by
  decide +kernel

theorem b_237_2400 : bothLoop evalE (oGrid.idx 237) (oGrid.dm 237) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 237) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3744895503725867938212453390201771883805849278433228042983586995432744298124⟩ ⟨false, 217741787003523259022517751518644739061363844980966569132833819812727665390⟩ = true := by
  decide +kernel

theorem o_row_237 : oGrid.row evalE 237 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_237_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_237_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_237_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_237_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_237_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_237_2000).1 (bothLoop_sound b_237_2400).1))))))

theorem n_row_237 : nGrid.row evalE 237 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_237_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_237_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_237_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_237_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_237_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_237_2000).2 (bothLoop_sound b_237_2400).2))))))

theorem b_238_0 : bothSeg evalE (oGrid.idx 238) (oGrid.dm 238) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 238) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2122326027085764960815770783204696798647091268090926003383015443614125923580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_238_400 : bothSeg evalE (oGrid.idx 238) (oGrid.dm 238) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 238) oGrid.kl oGrid.kr 400 400 ⟨false, 2122326027085764960815770783204696798647091268090926003383015443614125923580⟩ ⟨false, 0⟩ ⟨false, 3428588012711298593242598698410832951723508367062106393402908470521808244464⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_238_800 : bothSeg evalE (oGrid.idx 238) (oGrid.dm 238) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 238) oGrid.kl oGrid.kr 400 800 ⟨false, 3428588012711298593242598698410832951723508367062106393402908470521808244464⟩ ⟨false, 0⟩ ⟨false, 3892581898108452764612036369040753683175344807728872257991706030808543334526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_238_1200 : bothSeg evalE (oGrid.idx 238) (oGrid.dm 238) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 238) oGrid.kl oGrid.kr 400 1200 ⟨false, 3892581898108452764612036369040753683175344807728872257991706030808543334526⟩ ⟨false, 0⟩ ⟨false, 3909984267173099598832299645644853787816606711264466324368310356770568150542⟩ ⟨false, 33927691261662422046520710574303635274404276714817798218864725429096319892⟩ = true := by
  decide +kernel

theorem b_238_1600 : bothSeg evalE (oGrid.idx 238) (oGrid.dm 238) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 238) oGrid.kl oGrid.kr 400 1600 ⟨false, 3909984267173099598832299645644853787816606711264466324368310356770568150542⟩ ⟨false, 33927691261662422046520710574303635274404276714817798218864725429096319892⟩ ⟨false, 3751722320322937905015056291390932162350399227476573633604693027464790713700⟩ ⟨false, 192560411911651630425688200130084833873014179754999160827497508603440473534⟩ = true := by
  decide +kernel

theorem b_238_2000 : bothSeg evalE (oGrid.idx 238) (oGrid.dm 238) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 238) oGrid.kl oGrid.kr 400 2000 ⟨false, 3751722320322937905015056291390932162350399227476573633604693027464790713700⟩ ⟨false, 192560411911651630425688200130084833873014179754999160827497508603440473534⟩ ⟨false, 3728163445760073667656390023865687601831856315989255061904168888207074602072⟩ ⟨false, 217548778268057126313495702553744860092988489190067614021872353336685105894⟩ = true := by
  decide +kernel

theorem b_238_2400 : bothLoop evalE (oGrid.idx 238) (oGrid.dm 238) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 238) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3728163445760073667656390023865687601831856315989255061904168888207074602072⟩ ⟨false, 217548778268057126313495702553744860092988489190067614021872353336685105894⟩ = true := by
  decide +kernel

theorem o_row_238 : oGrid.row evalE 238 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_238_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_238_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_238_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_238_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_238_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_238_2000).1 (bothLoop_sound b_238_2400).1))))))

theorem n_row_238 : nGrid.row evalE 238 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_238_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_238_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_238_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_238_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_238_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_238_2000).2 (bothLoop_sound b_238_2400).2))))))

theorem b_239_0 : bothSeg evalE (oGrid.idx 239) (oGrid.dm 239) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 239) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2113615870603038076618529569864504994690248912266512683983626670722870993058⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_239_400 : bothSeg evalE (oGrid.idx 239) (oGrid.dm 239) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 239) oGrid.kl oGrid.kr 400 400 ⟨false, 2113615870603038076618529569864504994690248912266512683983626670722870993058⟩ ⟨false, 0⟩ ⟨false, 3414416739810423397608724470192997503000936975738669478932707241519638531630⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_239_800 : bothSeg evalE (oGrid.idx 239) (oGrid.dm 239) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 239) oGrid.kl oGrid.kr 400 800 ⟨false, 3414416739810423397608724470192997503000936975738669478932707241519638531630⟩ ⟨false, 0⟩ ⟨false, 3876160971448302327751442639216381303537329904327185502735219926726360339432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_239_1200 : bothSeg evalE (oGrid.idx 239) (oGrid.dm 239) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 239) oGrid.kl oGrid.kr 400 1200 ⟨false, 3876160971448302327751442639216381303537329904327185502735219926726360339432⟩ ⟨false, 0⟩ ⟨false, 3892973786699954633977602382667328377126074254866638885733977602796731824096⟩ ⟨false, 34025279506611556318554798916522572768310445569123207883431016791654682006⟩ = true := by
  decide +kernel

theorem b_239_1600 : bothSeg evalE (oGrid.idx 239) (oGrid.dm 239) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 239) oGrid.kl oGrid.kr 400 1600 ⟨false, 3892973786699954633977602382667328377126074254866638885733977602796731824096⟩ ⟨false, 34025279506611556318554798916522572768310445569123207883431016791654682006⟩ ⟨false, 3734799563950053520567827845692445101677409470133383806891306537692602231972⟩ ⟨false, 192571288960679269190676774396450619369820119751635827496692108168800127608⟩ = true := by
  decide +kernel

theorem b_239_2000 : bothSeg evalE (oGrid.idx 239) (oGrid.dm 239) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 239) oGrid.kl oGrid.kr 400 2000 ⟨false, 3734799563950053520567827845692445101677409470133383806891306537692602231972⟩ ⟨false, 192571288960679269190676774396450619369820119751635827496692108168800127608⟩ ⟨false, 3711484272996528304942555638244123564243151818540868369882933656818873725080⟩ ⟨false, 217355784498718335708647588674057356799852442636013565164809299453665253458⟩ = true := by
  decide +kernel

theorem b_239_2400 : bothLoop evalE (oGrid.idx 239) (oGrid.dm 239) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 239) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3711484272996528304942555638244123564243151818540868369882933656818873725080⟩ ⟨false, 217355784498718335708647588674057356799852442636013565164809299453665253458⟩ = true := by
  decide +kernel

theorem o_row_239 : oGrid.row evalE 239 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_239_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_239_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_239_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_239_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_239_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_239_2000).1 (bothLoop_sound b_239_2400).1))))))

theorem n_row_239 : nGrid.row evalE 239 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_239_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_239_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_239_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_239_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_239_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_239_2000).2 (bothLoop_sound b_239_2400).2))))))

theorem o_blk_216 : allFrom (fun j => oGrid.row evalE j) 216 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 216) o_row_216 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 217) o_row_217 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 218) o_row_218 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 219) o_row_219 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 220) o_row_220 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 221) o_row_221 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 222) o_row_222 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 223) o_row_223 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 224) o_row_224 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 225) o_row_225 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 226) o_row_226 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 227) o_row_227 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 228) o_row_228 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 229) o_row_229 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 230) o_row_230 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 231) o_row_231 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 232) o_row_232 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 233) o_row_233 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 234) o_row_234 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 235) o_row_235 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 236) o_row_236 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 237) o_row_237 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 238) o_row_238 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 239) o_row_239 (allFrom_zero (fun j => oGrid.row evalE j) 240)))))))))))))))))))))))))

theorem n_blk_216 : allFrom (fun j => nGrid.row evalE j) 216 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 216) n_row_216 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 217) n_row_217 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 218) n_row_218 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 219) n_row_219 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 220) n_row_220 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 221) n_row_221 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 222) n_row_222 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 223) n_row_223 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 224) n_row_224 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 225) n_row_225 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 226) n_row_226 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 227) n_row_227 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 228) n_row_228 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 229) n_row_229 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 230) n_row_230 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 231) n_row_231 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 232) n_row_232 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 233) n_row_233 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 234) n_row_234 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 235) n_row_235 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 236) n_row_236 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 237) n_row_237 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 238) n_row_238 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 239) n_row_239 (allFrom_zero (fun j => nGrid.row evalE j) 240)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
