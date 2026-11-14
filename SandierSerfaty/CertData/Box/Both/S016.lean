/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 16 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `384`–`407`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_384_0 : bothSeg evalE (oGrid.idx 384) (oGrid.dm 384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 384) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1106653518655820955335470961150435576070760442957817408752977699822077584954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_384_400 : bothSeg evalE (oGrid.idx 384) (oGrid.dm 384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 384) oGrid.kl oGrid.kr 400 400 ⟨false, 1106653518655820955335470961150435576070760442957817408752977699822077584954⟩ ⟨false, 0⟩ ⟨false, 1767435636508300544507123243471729717406378745275466398426327249395949745606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_384_800 : bothSeg evalE (oGrid.idx 384) (oGrid.dm 384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 384) oGrid.kl oGrid.kr 400 800 ⟨false, 1767435636508300544507123243471729717406378745275466398426327249395949745606⟩ ⟨false, 0⟩ ⟨false, 1964265460837267401757801110472881588420646801529949315697484167489196920784⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_384_1200 : bothSeg evalE (oGrid.idx 384) (oGrid.dm 384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 384) oGrid.kl oGrid.kr 400 1200 ⟨false, 1964265460837267401757801110472881588420646801529949315697484167489196920784⟩ ⟨false, 0⟩ ⟨false, 1919721471701526434441189970257225478293551733717197189841534618996762480188⟩ ⟨false, 50305352628348251477955877219217906372038989120786753159367384849750099624⟩ = true := by
  decide +kernel

theorem b_384_1600 : bothSeg evalE (oGrid.idx 384) (oGrid.dm 384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 384) oGrid.kl oGrid.kr 400 1600 ⟨false, 1919721471701526434441189970257225478293551733717197189841534618996762480188⟩ ⟨false, 50305352628348251477955877219217906372038989120786753159367384849750099624⟩ ⟨false, 1783131434045195646627842412360112728433001078374851702636660188388901973994⟩ ⟨false, 186895390284679039291303435116330656232589644463132240364241815457610605818⟩ = true := by
  decide +kernel

theorem b_384_2000 : bothSeg evalE (oGrid.idx 384) (oGrid.dm 384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 384) oGrid.kl oGrid.kr 400 2000 ⟨false, 1783131434045195646627842412360112728433001078374851702636660188388901973994⟩ ⟨false, 186895390284679039291303435116330656232589644463132240364241815457610605818⟩ ⟨false, 1783712609626008856382584030588703940088563139625192847299536997604728718580⟩ ⟨false, 193929318302727078992807312994263207539270705519214181520319962922370543102⟩ = true := by
  decide +kernel

theorem b_384_2400 : bothLoop evalE (oGrid.idx 384) (oGrid.dm 384) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 384) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1783712609626008856382584030588703940088563139625192847299536997604728718580⟩ ⟨false, 193929318302727078992807312994263207539270705519214181520319962922370543102⟩ = true := by
  decide +kernel

theorem o_row_384 : oGrid.row evalE 384 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_384_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_384_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_384_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_384_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_384_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_384_2000).1 (bothLoop_sound b_384_2400).1))))))

theorem n_row_384 : nGrid.row evalE 384 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_384_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_384_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_384_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_384_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_384_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_384_2000).2 (bothLoop_sound b_384_2400).2))))))

theorem b_385_0 : bothSeg evalE (oGrid.idx 385) (oGrid.dm 385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 385) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1101262677769142085817975532326023866119359578806094108273852790524767941916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_385_400 : bothSeg evalE (oGrid.idx 385) (oGrid.dm 385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 385) oGrid.kl oGrid.kr 400 400 ⟨false, 1101262677769142085817975532326023866119359578806094108273852790524767941916⟩ ⟨false, 0⟩ ⟨false, 1758579956348482128479978733688826972674994880799819406119186141236385641974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_385_800 : bothSeg evalE (oGrid.idx 385) (oGrid.dm 385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 385) oGrid.kl oGrid.kr 400 800 ⟨false, 1758579956348482128479978733688826972674994880799819406119186141236385641974⟩ ⟨false, 0⟩ ⟨false, 1953981244856575796129908626924395483034048986196425547262803567789005142550⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_385_1200 : bothSeg evalE (oGrid.idx 385) (oGrid.dm 385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 385) oGrid.kl oGrid.kr 400 1200 ⟨false, 1953981244856575796129908626924395483034048986196425547262803567789005142550⟩ ⟨false, 0⟩ ⟨false, 1908814131462336907982079884286746971266073008258897894980449201438980523864⟩ ⟨false, 50783470084983306883649753838824278723486200537659802804795562142744409286⟩ = true := by
  decide +kernel

theorem b_385_1600 : bothSeg evalE (oGrid.idx 385) (oGrid.dm 385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 385) oGrid.kl oGrid.kr 400 1600 ⟨false, 1908814131462336907982079884286746971266073008258897894980449201438980523864⟩ ⟨false, 50783470084983306883649753838824278723486200537659802804795562142744409286⟩ ⟨false, 1772782512546721821904075334544240955858364342696373896309992829951454842224⟩ ⟨false, 186815089000598392961654303581330294131194866100183801475251933630270090926⟩ = true := by
  decide +kernel

theorem b_385_2000 : bothSeg evalE (oGrid.idx 385) (oGrid.dm 385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 385) oGrid.kl oGrid.kr 400 2000 ⟨false, 1772782512546721821904075334544240955858364342696373896309992829951454842224⟩ ⟨false, 186815089000598392961654303581330294131194866100183801475251933630270090926⟩ ⟨false, 1773390654112703172009325029111766841566856349058103869384018779887306729456⟩ ⟨false, 193838551601027125412920684992569229608205733930234669060850137328846863342⟩ = true := by
  decide +kernel

theorem b_385_2400 : bothLoop evalE (oGrid.idx 385) (oGrid.dm 385) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 385) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1773390654112703172009325029111766841566856349058103869384018779887306729456⟩ ⟨false, 193838551601027125412920684992569229608205733930234669060850137328846863342⟩ = true := by
  decide +kernel

theorem o_row_385 : oGrid.row evalE 385 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_385_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_385_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_385_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_385_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_385_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_385_2000).1 (bothLoop_sound b_385_2400).1))))))

theorem n_row_385 : nGrid.row evalE 385 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_385_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_385_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_385_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_385_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_385_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_385_2000).2 (bothLoop_sound b_385_2400).2))))))

theorem b_386_0 : bothSeg evalE (oGrid.idx 386) (oGrid.dm 386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 386) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1095890483122244569056404498535853175470524794849731604876190823821858623742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_386_400 : bothSeg evalE (oGrid.idx 386) (oGrid.dm 386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 386) oGrid.kl oGrid.kr 400 400 ⟨false, 1095890483122244569056404498535853175470524794849731604876190823821858623742⟩ ⟨false, 0⟩ ⟨false, 1749754621703668735615884305273661259541451108858977429875922527422715520672⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_386_800 : bothSeg evalE (oGrid.idx 386) (oGrid.dm 386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 386) oGrid.kl oGrid.kr 400 800 ⟨false, 1749754621703668735615884305273661259541451108858977429875922527422715520672⟩ ⟨false, 0⟩ ⟨false, 1943732415041621530685528625500286584461418204449288383746551869769354195230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_386_1200 : bothSeg evalE (oGrid.idx 386) (oGrid.dm 386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 386) oGrid.kl oGrid.kr 400 1200 ⟨false, 1943732415041621530685528625500286584461418204449288383746551869769354195230⟩ ⟨false, 0⟩ ⟨false, 1897941171897554677870756861816284426460664667132584037550239358682049395348⟩ ⟨false, 51264419662756514677743304879472045120196920514587580547799327669513095100⟩ = true := by
  decide +kernel

theorem b_386_1600 : bothSeg evalE (oGrid.idx 386) (oGrid.dm 386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 386) oGrid.kl oGrid.kr 400 1600 ⟨false, 1897941171897554677870756861816284426460664667132584037550239358682049395348⟩ ⟨false, 51264419662756514677743304879472045120196920514587580547799327669513095100⟩ ⟨false, 1762471577960451271264501525456786523309651534582278617695699793027035353306⟩ ⟨false, 186734013599859921283998641238969948271210053064893000402338893324527137142⟩ = true := by
  decide +kernel

theorem b_386_2000 : bothSeg evalE (oGrid.idx 386) (oGrid.dm 386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 386) oGrid.kl oGrid.kr 400 2000 ⟨false, 1762471577960451271264501525456786523309651534582278617695699793027035353306⟩ ⟨false, 186734013599859921283998641238969948271210053064893000402338893324527137142⟩ ⟨false, 1763105663479779747563029702633112354066393349790669747715305270195301099010⟩ ⟨false, 193747523147740605929617039455747303531173884353703898615510578277127082740⟩ = true := by
  decide +kernel

theorem b_386_2400 : bothLoop evalE (oGrid.idx 386) (oGrid.dm 386) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 386) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1763105663479779747563029702633112354066393349790669747715305270195301099010⟩ ⟨false, 193747523147740605929617039455747303531173884353703898615510578277127082740⟩ = true := by
  decide +kernel

theorem o_row_386 : oGrid.row evalE 386 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_386_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_386_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_386_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_386_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_386_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_386_2000).1 (bothLoop_sound b_386_2400).1))))))

theorem n_row_386 : nGrid.row evalE 386 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_386_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_386_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_386_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_386_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_386_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_386_2000).2 (bothLoop_sound b_386_2400).2))))))

theorem b_387_0 : bothSeg evalE (oGrid.idx 387) (oGrid.dm 387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 387) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1090536884138111730024310900643678173090508668833950029917544240982576812272⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_387_400 : bothSeg evalE (oGrid.idx 387) (oGrid.dm 387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 387) oGrid.kl oGrid.kr 400 400 ⟨false, 1090536884138111730024310900643678173090508668833950029917544240982576812272⟩ ⟨false, 0⟩ ⟨false, 1740959574815738341870626308514953020041610301279326457525553243187365013310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_387_800 : bothSeg evalE (oGrid.idx 387) (oGrid.dm 387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 387) oGrid.kl oGrid.kr 400 800 ⟨false, 1740959574815738341870626308514953020041610301279326457525553243187365013310⟩ ⟨false, 0⟩ ⟨false, 1933518963074231177123228009319402811449356662587998978042662107960481031622⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_387_1200 : bothSeg evalE (oGrid.idx 387) (oGrid.dm 387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 387) oGrid.kl oGrid.kr 400 1200 ⟨false, 1933518963074231177123228009319402811449356662587998978042662107960481031622⟩ ⟨false, 0⟩ ⟨false, 1887102901424147951465576505907772139402917005164182204360246767517815216636⟩ ⟨false, 51748412183190612894652375026412357306780996070821037875325846394951396416⟩ = true := by
  decide +kernel

theorem b_387_1600 : bothSeg evalE (oGrid.idx 387) (oGrid.dm 387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 387) oGrid.kl oGrid.kr 400 1600 ⟨false, 1887102901424147951465576505907772139402917005164182204360246767517815216636⟩ ⟨false, 51748412183190612894652375026412357306780996070821037875325846394951396416⟩ ⟨false, 1752199018023280069797100518706130054727166090218100826273321538725571053800⟩ ⟨false, 186652295584058494563128362228054441982531911016902415962251075187195559252⟩ = true := by
  decide +kernel

theorem b_387_2000 : bothSeg evalE (oGrid.idx 387) (oGrid.dm 387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 387) oGrid.kl oGrid.kr 400 2000 ⟨false, 1752199018023280069797100518706130054727166090218100826273321538725571053800⟩ ⟨false, 186652295584058494563128362228054441982531911016902415962251075187195559252⟩ ⟨false, 1752858127453625555711136930097583096084206075925992574914334696965055503274⟩ ⟨false, 193656275544509982607974518198023219336864357884303025497261284358987069982⟩ = true := by
  decide +kernel

theorem b_387_2400 : bothLoop evalE (oGrid.idx 387) (oGrid.dm 387) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 387) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1752858127453625555711136930097583096084206075925992574914334696965055503274⟩ ⟨false, 193656275544509982607974518198023219336864357884303025497261284358987069982⟩ = true := by
  decide +kernel

theorem o_row_387 : oGrid.row evalE 387 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_387_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_387_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_387_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_387_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_387_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_387_2000).1 (bothLoop_sound b_387_2400).1))))))

theorem n_row_387 : nGrid.row evalE 387 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_387_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_387_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_387_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_387_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_387_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_387_2000).2 (bothLoop_sound b_387_2400).2))))))

theorem b_388_0 : bothSeg evalE (oGrid.idx 388) (oGrid.dm 388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 388) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1085201836927144736408385625374478338746717113629782352805696157305848194986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_388_400 : bothSeg evalE (oGrid.idx 388) (oGrid.dm 388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 388) oGrid.kl oGrid.kr 400 400 ⟨false, 1085201836927144736408385625374478338746717113629782352805696157305848194986⟩ ⟨false, 0⟩ ⟨false, 1732194743852935214245391416139730562761577444719286170114869975788540822948⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_388_800 : bothSeg evalE (oGrid.idx 388) (oGrid.dm 388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 388) oGrid.kl oGrid.kr 400 800 ⟨false, 1732194743852935214245391416139730562761577444719286170114869975788540822948⟩ ⟨false, 0⟩ ⟨false, 1923340839822315738328757936462887352086178521718749497851237785477316871540⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_388_1200 : bothSeg evalE (oGrid.idx 388) (oGrid.dm 388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 388) oGrid.kl oGrid.kr 400 1200 ⟨false, 1923340839822315738328757936462887352086178521718749497851237785477316871540⟩ ⟨false, 0⟩ ⟨false, 1876299333240474705800521356640749424101293932178444550658695390302418789540⟩ ⟨false, 52234955831285494394902366386769086906184983829007393827453640989312321024⟩ = true := by
  decide +kernel

theorem b_388_1600 : bothSeg evalE (oGrid.idx 388) (oGrid.dm 388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 388) oGrid.kl oGrid.kr 400 1600 ⟨false, 1876299333240474705800521356640749424101293932178444550658695390302418789540⟩ ⟨false, 52234955831285494394902366386769086906184983829007393827453640989312321024⟩ ⟨false, 1741964442745820675013297673370807173415202056491473389032524465811411529840⟩ ⟨false, 186569846325939525182126049656711337592276859515978555453624565480319580724⟩ = true := by
  decide +kernel

theorem b_388_2000 : bothSeg evalE (oGrid.idx 388) (oGrid.dm 388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 388) oGrid.kl oGrid.kr 400 2000 ⟨false, 1741964442745820675013297673370807173415202056491473389032524465811411529840⟩ ⟨false, 186569846325939525182126049656711337592276859515978555453624565480319580724⟩ ⟨false, 1742647678463469819423337065766157227489591012945565578874103318534168633612⟩ ⟨false, 193566124128448863714988366211147871249971471892390192233445728248103783088⟩ = true := by
  decide +kernel

theorem b_388_2400 : bothLoop evalE (oGrid.idx 388) (oGrid.dm 388) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 388) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1742647678463469819423337065766157227489591012945565578874103318534168633612⟩ ⟨false, 193566124128448863714988366211147871249971471892390192233445728248103783088⟩ = true := by
  decide +kernel

theorem o_row_388 : oGrid.row evalE 388 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_388_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_388_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_388_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_388_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_388_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_388_2000).1 (bothLoop_sound b_388_2400).1))))))

theorem n_row_388 : nGrid.row evalE 388 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_388_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_388_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_388_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_388_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_388_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_388_2000).2 (bothLoop_sound b_388_2400).2))))))

theorem b_389_0 : bothSeg evalE (oGrid.idx 389) (oGrid.dm 389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 389) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1079885284880498419946724899277631293921381852650516436495666845782995489684⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_389_400 : bothSeg evalE (oGrid.idx 389) (oGrid.dm 389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 389) oGrid.kl oGrid.kr 400 400 ⟨false, 1079885284880498419946724899277631293921381852650516436495666845782995489684⟩ ⟨false, 0⟩ ⟨false, 1723460041311109531952354022742447835466995888443067169456312925037709695376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_389_800 : bothSeg evalE (oGrid.idx 389) (oGrid.dm 389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 389) oGrid.kl oGrid.kr 400 800 ⟨false, 1723460041311109531952354022742447835466995888443067169456312925037709695376⟩ ⟨false, 0⟩ ⟨false, 1913197866178224045473795054322350720300180199474980766733063857400373383774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_389_1200 : bothSeg evalE (oGrid.idx 389) (oGrid.dm 389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 389) oGrid.kl oGrid.kr 400 1200 ⟨false, 1913197866178224045473795054322350720300180199474980766733063857400373383774⟩ ⟨false, 0⟩ ⟨false, 1865530357054801227819267594660420583455618923446122022199506206420171646298⟩ ⟨false, 52724274090447256507970762368667182703782652513321574243513176748240834412⟩ = true := by
  decide +kernel

theorem b_389_1600 : bothSeg evalE (oGrid.idx 389) (oGrid.dm 389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 389) oGrid.kl oGrid.kr 400 1600 ⟨false, 1865530357054801227819267594660420583455618923446122022199506206420171646298⟩ ⟨false, 52724274090447256507970762368667182703782652513321574243513176748240834412⟩ ⟨false, 1731767499257806195236733141017945281076245844387806445436523179512463475020⟩ ⟨false, 186487131887442289090505216011142485083155731571637151006496203655949005690⟩ = true := by
  decide +kernel

theorem b_389_2000 : bothSeg evalE (oGrid.idx 389) (oGrid.dm 389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 389) oGrid.kl oGrid.kr 400 2000 ⟨false, 1731767499257806195236733141017945281076245844387806445436523179512463475020⟩ ⟨false, 186487131887442289090505216011142485083155731571637151006496203655949005690⟩ ⟨false, 1732474018188898907314757484583503051245448899229315129208285766177997601184⟩ ⟨false, 193476119541914874617477729720664114066284232781402444777358368528289952838⟩ = true := by
  decide +kernel

theorem b_389_2400 : bothLoop evalE (oGrid.idx 389) (oGrid.dm 389) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 389) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1732474018188898907314757484583503051245448899229315129208285766177997601184⟩ ⟨false, 193476119541914874617477729720664114066284232781402444777358368528289952838⟩ = true := by
  decide +kernel

theorem o_row_389 : oGrid.row evalE 389 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_389_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_389_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_389_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_389_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_389_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_389_2000).1 (bothLoop_sound b_389_2400).1))))))

theorem n_row_389 : nGrid.row evalE 389 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_389_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_389_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_389_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_389_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_389_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_389_2000).2 (bothLoop_sound b_389_2400).2))))))

theorem b_390_0 : bothSeg evalE (oGrid.idx 390) (oGrid.dm 390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 390) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1074587185569403285512841110743214113856302762505959561405234586177553819442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_390_400 : bothSeg evalE (oGrid.idx 390) (oGrid.dm 390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 390) oGrid.kl oGrid.kr 400 400 ⟨false, 1074587185569403285512841110743214113856302762505959561405234586177553819442⟩ ⟨false, 0⟩ ⟨false, 1714755406250811339547293688538434412334265413037132766931892089541626201432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_390_800 : bothSeg evalE (oGrid.idx 390) (oGrid.dm 390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 390) oGrid.kl oGrid.kr 400 800 ⟨false, 1714755406250811339547293688538434412334265413037132766931892089541626201432⟩ ⟨false, 0⟩ ⟨false, 1903090031105442702497310922287975928325738833013712845319978864412280977388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_390_1200 : bothSeg evalE (oGrid.idx 390) (oGrid.dm 390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 390) oGrid.kl oGrid.kr 400 1200 ⟨false, 1903090031105442702497310922287975928325738833013712845319978864412280977388⟩ ⟨false, 0⟩ ⟨false, 1854796208857967248459424824607277758217309290542826076329924961471511155766⟩ ⟨false, 53216190208417425900324486453560172496993042066784470586095494862844031554⟩ = true := by
  decide +kernel

theorem b_390_1600 : bothSeg evalE (oGrid.idx 390) (oGrid.dm 390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 390) oGrid.kl oGrid.kr 400 1600 ⟨false, 1854796208857967248459424824607277758217309290542826076329924961471511155766⟩ ⟨false, 53216190208417425900324486453560172496993042066784470586095494862844031554⟩ ⟨false, 1721608312704368438923437399805965458516882797869304728042800370225234848582⟩ ⟨false, 186404086362016235436311911254872472197419534740305818873220086109120338738⟩ = true := by
  decide +kernel

theorem b_390_2000 : bothSeg evalE (oGrid.idx 390) (oGrid.dm 390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 390) oGrid.kl oGrid.kr 400 2000 ⟨false, 1721608312704368438923437399805965458516882797869304728042800370225234848582⟩ ⟨false, 186404086362016235436311911254872472197419534740305818873220086109120338738⟩ ⟨false, 1722337350718384528283988835669417122873739756810384456990628479009411745208⟩ ⟨false, 193386262510778732761440302497479792469029953384822337266200987349802928384⟩ = true := by
  decide +kernel

theorem b_390_2400 : bothLoop evalE (oGrid.idx 390) (oGrid.dm 390) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 390) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1722337350718384528283988835669417122873739756810384456990628479009411745208⟩ ⟨false, 193386262510778732761440302497479792469029953384822337266200987349802928384⟩ = true := by
  decide +kernel

theorem o_row_390 : oGrid.row evalE 390 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_390_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_390_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_390_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_390_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_390_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_390_2000).1 (bothLoop_sound b_390_2400).1))))))

theorem n_row_390 : nGrid.row evalE 390 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_390_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_390_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_390_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_390_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_390_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_390_2000).2 (bothLoop_sound b_390_2400).2))))))

theorem b_391_0 : bothSeg evalE (oGrid.idx 391) (oGrid.dm 391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 391) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1069307487523075323197794411400496075039865199338324205194833499884916379460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_391_400 : bothSeg evalE (oGrid.idx 391) (oGrid.dm 391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 391) oGrid.kl oGrid.kr 400 400 ⟨false, 1069307487523075323197794411400496075039865199338324205194833499884916379460⟩ ⟨false, 0⟩ ⟨false, 1706080744902162302657127187193285607263790713131213696521176222916523510742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_391_800 : bothSeg evalE (oGrid.idx 391) (oGrid.dm 391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 391) oGrid.kl oGrid.kr 400 800 ⟨false, 1706080744902162302657127187193285607263790713131213696521176222916523510742⟩ ⟨false, 0⟩ ⟨false, 1893017252704574699549864070820903170098393342539112314921943445727770266276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_391_1200 : bothSeg evalE (oGrid.idx 391) (oGrid.dm 391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 391) oGrid.kl oGrid.kr 400 1200 ⟨false, 1893017252704574699549864070820903170098393342539112314921943445727770266276⟩ ⟨false, 0⟩ ⟨false, 1844096919110720334442512590037226934335473718538522337127822803429676372210⟩ ⟨false, 53710430852933404876414104099724114916613970205512141071878499812324467674⟩ = true := by
  decide +kernel

theorem b_391_1600 : bothSeg evalE (oGrid.idx 391) (oGrid.dm 391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 391) oGrid.kl oGrid.kr 400 1600 ⟨false, 1844096919110720334442512590037226934335473718538522337127822803429676372210⟩ ⟨false, 53710430852933404876414104099724114916613970205512141071878499812324467674⟩ ⟨false, 1711486693960213873816956802471224012978015564377145428673004105597170221792⟩ ⟨false, 186320656003439865501969891665727036274072124366889049526697197644830618092⟩ = true := by
  decide +kernel

theorem b_391_2000 : bothSeg evalE (oGrid.idx 391) (oGrid.dm 391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 391) oGrid.kl oGrid.kr 400 2000 ⟨false, 1711486693960213873816956802471224012978015564377145428673004105597170221792⟩ ⟨false, 186320656003439865501969891665727036274072124366889049526697197644830618092⟩ ⟨false, 1712237533406584439957557880852777745501034295345711476538667515213313056598⟩ ⟨false, 193297631160651936059507726039671766732230644930930130781927855721228839842⟩ = true := by
  decide +kernel

theorem b_391_2400 : bothLoop evalE (oGrid.idx 391) (oGrid.dm 391) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 391) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1712237533406584439957557880852777745501034295345711476538667515213313056598⟩ ⟨false, 193297631160651936059507726039671766732230644930930130781927855721228839842⟩ = true := by
  decide +kernel

theorem o_row_391 : oGrid.row evalE 391 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_391_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_391_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_391_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_391_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_391_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_391_2000).1 (bothLoop_sound b_391_2400).1))))))

theorem n_row_391 : nGrid.row evalE 391 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_391_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_391_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_391_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_391_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_391_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_391_2000).2 (bothLoop_sound b_391_2400).2))))))

theorem b_392_0 : bothSeg evalE (oGrid.idx 392) (oGrid.dm 392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 392) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1064046148953226519222115760583236805350067463530091669436675196293511131052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_392_400 : bothSeg evalE (oGrid.idx 392) (oGrid.dm 392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 392) oGrid.kl oGrid.kr 400 400 ⟨false, 1064046148953226519222115760583236805350067463530091669436675196293511131052⟩ ⟨false, 0⟩ ⟨false, 1697436013314751511374704698334951719712821225828494413626186385218534955316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_392_800 : bothSeg evalE (oGrid.idx 392) (oGrid.dm 392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 392) oGrid.kl oGrid.kr 400 800 ⟨false, 1697436013314751511374704698334951719712821225828494413626186385218534955316⟩ ⟨false, 0⟩ ⟨false, 1882979415057293522949670550627976509856723878048337075995039782216592852462⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_392_1200 : bothSeg evalE (oGrid.idx 392) (oGrid.dm 392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 392) oGrid.kl oGrid.kr 400 1200 ⟨false, 1882979415057293522949670550627976509856723878048337075995039782216592852462⟩ ⟨false, 0⟩ ⟨false, 1833432546189646311041472124589363043565008825234456645420649350002908174520⟩ ⟨false, 54206705394495554448294432710000381204979152967479656880554471712581570776⟩ = true := by
  decide +kernel

theorem b_392_1600 : bothSeg evalE (oGrid.idx 392) (oGrid.dm 392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 392) oGrid.kl oGrid.kr 400 1600 ⟨false, 1833432546189646311041472124589363043565008825234456645420649350002908174520⟩ ⟨false, 54206705394495554448294432710000381204979152967479656880554471712581570776⟩ ⟨false, 1701402539433484407788925484631365005681307307592250345452977606928907947852⟩ ⟨false, 186236712150657457700841072667998419088680670609685956848226214786581797444⟩ = true := by
  decide +kernel

theorem b_392_2000 : bothSeg evalE (oGrid.idx 392) (oGrid.dm 392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 392) oGrid.kl oGrid.kr 400 2000 ⟨false, 1701402539433484407788925484631365005681307307592250345452977606928907947852⟩ ⟨false, 186236712150657457700841072667998419088680670609685956848226214786581797444⟩ ⟨false, 1702174543282946689402428996988229330021223538433111712768817409018052165562⟩ ⟨false, 193208830227928801660329433110337520658675832633377627493491513608131988802⟩ = true := by
  decide +kernel

theorem b_392_2400 : bothLoop evalE (oGrid.idx 392) (oGrid.dm 392) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 392) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1702174543282946689402428996988229330021223538433111712768817409018052165562⟩ ⟨false, 193208830227928801660329433110337520658675832633377627493491513608131988802⟩ = true := by
  decide +kernel

theorem o_row_392 : oGrid.row evalE 392 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_392_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_392_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_392_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_392_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_392_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_392_2000).1 (bothLoop_sound b_392_2400).1))))))

theorem n_row_392 : nGrid.row evalE 392 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_392_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_392_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_392_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_392_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_392_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_392_2000).2 (bothLoop_sound b_392_2400).2))))))

theorem b_393_0 : bothSeg evalE (oGrid.idx 393) (oGrid.dm 393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 393) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1058803114326800201196871541160787782542178530094173782375118540870380894546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_393_400 : bothSeg evalE (oGrid.idx 393) (oGrid.dm 393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 393) oGrid.kl oGrid.kr 400 400 ⟨false, 1058803114326800201196871541160787782542178530094173782375118540870380894546⟩ ⟨false, 0⟩ ⟨false, 1688821119977463750491017910152112263045137158097343886311073393788341748008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_393_800 : bothSeg evalE (oGrid.idx 393) (oGrid.dm 393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 393) oGrid.kl oGrid.kr 400 800 ⟨false, 1688821119977463750491017910152112263045137158097343886311073393788341748008⟩ ⟨false, 0⟩ ⟨false, 1872976444088024210564759794248319019132525480510683295198939321595640837450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_393_1200 : bothSeg evalE (oGrid.idx 393) (oGrid.dm 393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 393) oGrid.kl oGrid.kr 400 1200 ⟨false, 1872976444088024210564759794248319019132525480510683295198939321595640837450⟩ ⟨false, 0⟩ ⟨false, 1822803308887655513853422122993719446448291367719087365843292819430654492294⟩ ⟨false, 54704832716844164339421793542020236478552445258176615604304141158292199144⟩ = true := by
  decide +kernel

theorem b_393_1600 : bothSeg evalE (oGrid.idx 393) (oGrid.dm 393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 393) oGrid.kl oGrid.kr 400 1600 ⟨false, 1822803308887655513853422122993719446448291367719087365843292819430654492294⟩ ⟨false, 54704832716844164339421793542020236478552445258176615604304141158292199144⟩ ⟨false, 1691355815077229202085518124278765304529668389218013422477377181903863685338⟩ ⟨false, 186152326527270476107325792256974378397175423759250558970219778685083006100⟩ = true := by
  decide +kernel

theorem b_393_2000 : bothSeg evalE (oGrid.idx 393) (oGrid.dm 393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 393) oGrid.kl oGrid.kr 400 2000 ⟨false, 1691355815077229202085518124278765304529668389218013422477377181903863685338⟩ ⟨false, 186152326527270476107325792256974378397175423759250558970219778685083006100⟩ ⟨false, 1692148377916539878985475360445979282306433053929582195756165009768452374712⟩ ⟨false, 193119663452456100821237847355775970509815345839520263746653784295530535356⟩ = true := by
  decide +kernel

theorem b_393_2400 : bothLoop evalE (oGrid.idx 393) (oGrid.dm 393) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 393) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1692148377916539878985475360445979282306433053929582195756165009768452374712⟩ ⟨false, 193119663452456100821237847355775970509815345839520263746653784295530535356⟩ = true := by
  decide +kernel

theorem o_row_393 : oGrid.row evalE 393 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_393_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_393_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_393_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_393_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_393_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_393_2000).1 (bothLoop_sound b_393_2400).1))))))

theorem n_row_393 : nGrid.row evalE 393 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_393_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_393_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_393_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_393_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_393_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_393_2000).2 (bothLoop_sound b_393_2400).2))))))

theorem b_394_0 : bothSeg evalE (oGrid.idx 394) (oGrid.dm 394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 394) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1053578336529416288338601733247456952059963209269602113974747710704705204286⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_394_400 : bothSeg evalE (oGrid.idx 394) (oGrid.dm 394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 394) oGrid.kl oGrid.kr 400 400 ⟨false, 1053578336529416288338601733247456952059963209269602113974747710704705204286⟩ ⟨false, 0⟩ ⟨false, 1680236001524771428809630576484203545212201313594997708761575929090328584026⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_394_800 : bothSeg evalE (oGrid.idx 394) (oGrid.dm 394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 394) oGrid.kl oGrid.kr 400 800 ⟨false, 1680236001524771428809630576484203545212201313594997708761575929090328584026⟩ ⟨false, 0⟩ ⟨false, 1863008308305867469894533904092384623271155119948927850430705504874459356438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_394_1200 : bothSeg evalE (oGrid.idx 394) (oGrid.dm 394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 394) oGrid.kl oGrid.kr 400 1200 ⟨false, 1863008308305867469894533904092384623271155119948927850430705504874459356438⟩ ⟨false, 0⟩ ⟨false, 1812209292548850246357850073648255818734111764418168377260700120478832771162⟩ ⟨false, 55205147490993656560114351126716545832156324207226980957964920891482998054⟩ = true := by
  decide +kernel

theorem b_394_1600 : bothSeg evalE (oGrid.idx 394) (oGrid.dm 394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 394) oGrid.kl oGrid.kr 400 1600 ⟨false, 1812209292548850246357850073648255818734111764418168377260700120478832771162⟩ ⟨false, 55205147490993656560114351126716545832156324207226980957964920891482998054⟩ ⟨false, 1681346261842511074627653521316144528170816945409010161107998239942886385970⟩ ⟨false, 186068178197332828290310903458827836395451143216385197110666801427429383246⟩ = true := by
  decide +kernel

theorem b_394_2000 : bothSeg evalE (oGrid.idx 394) (oGrid.dm 394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 394) oGrid.kl oGrid.kr 400 2000 ⟨false, 1681346261842511074627653521316144528170816945409010161107998239942886385970⟩ ⟨false, 186068178197332828290310903458827836395451143216385197110666801427429383246⟩ ⟨false, 1682158864523755759214434939664660174509709848567300372517189920872462008836⟩ ⟨false, 193031972607684343011310674935819911982585052178168829726889178154625743228⟩ = true := by
  decide +kernel

theorem b_394_2400 : bothLoop evalE (oGrid.idx 394) (oGrid.dm 394) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 394) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1682158864523755759214434939664660174509709848567300372517189920872462008836⟩ ⟨false, 193031972607684343011310674935819911982585052178168829726889178154625743228⟩ = true := by
  decide +kernel

theorem o_row_394 : oGrid.row evalE 394 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_394_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_394_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_394_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_394_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_394_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_394_2000).1 (bothLoop_sound b_394_2400).1))))))

theorem n_row_394 : nGrid.row evalE 394 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_394_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_394_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_394_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_394_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_394_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_394_2000).2 (bothLoop_sound b_394_2400).2))))))

theorem b_395_0 : bothSeg evalE (oGrid.idx 395) (oGrid.dm 395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 395) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1048371769691218052582440356447391566384169021025078558368395737077761284384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_395_400 : bothSeg evalE (oGrid.idx 395) (oGrid.dm 395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 395) oGrid.kl oGrid.kr 400 400 ⟨false, 1048371769691218052582440356447391566384169021025078558368395737077761284384⟩ ⟨false, 0⟩ ⟨false, 1671680562078651347784125990180159503187662529214579450267444263438375358030⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_395_800 : bothSeg evalE (oGrid.idx 395) (oGrid.dm 395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 395) oGrid.kl oGrid.kr 400 800 ⟨false, 1671680562078651347784125990180159503187662529214579450267444263438375358030⟩ ⟨false, 0⟩ ⟨false, 1853074857546608766712617031923624111832582252357475396779303629333878898384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_395_1200 : bothSeg evalE (oGrid.idx 395) (oGrid.dm 395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 395) oGrid.kl oGrid.kr 400 1200 ⟨false, 1853074857546608766712617031923624111832582252357475396779303629333878898384⟩ ⟨false, 0⟩ ⟨false, 1801650635398450160922563896690846598722920988666631382638531880925401084354⟩ ⟨false, 55706576499670424461585300198501503529027692045763877311302573316670576086⟩ = true := by
  decide +kernel

theorem b_395_1600 : bothSeg evalE (oGrid.idx 395) (oGrid.dm 395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 395) oGrid.kl oGrid.kr 400 1600 ⟨false, 1801650635398450160922563896690846598722920988666631382638531880925401084354⟩ ⟨false, 55706576499670424461585300198501503529027692045763877311302573316670576086⟩ ⟨false, 1671374488807119851107861059518074276486183074914201204048278039568834720794⟩ ⟨false, 185982723091000734276288137371273825765765605798194055901556414673236939646⟩ = true := by
  decide +kernel

theorem b_395_2000 : bothSeg evalE (oGrid.idx 395) (oGrid.dm 395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 395) oGrid.kl oGrid.kr 400 2000 ⟨false, 1671374488807119851107861059518074276486183074914201204048278039568834720794⟩ ⟨false, 185982723091000734276288137371273825765765605798194055901556414673236939646⟩ ⟨false, 1672206653494873572395224485804117265349193397797979913175102622518449969772⟩ ⟨false, 192943254826712233712160319523790070482668124921642483392407013591536884604⟩ = true := by
  decide +kernel

theorem b_395_2400 : bothLoop evalE (oGrid.idx 395) (oGrid.dm 395) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 395) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1672206653494873572395224485804117265349193397797979913175102622518449969772⟩ ⟨false, 192943254826712233712160319523790070482668124921642483392407013591536884604⟩ = true := by
  decide +kernel

theorem o_row_395 : oGrid.row evalE 395 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_395_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_395_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_395_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_395_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_395_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_395_2000).1 (bothLoop_sound b_395_2400).1))))))

theorem n_row_395 : nGrid.row evalE 395 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_395_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_395_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_395_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_395_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_395_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_395_2000).2 (bothLoop_sound b_395_2400).2))))))

theorem b_396_0 : bothSeg evalE (oGrid.idx 396) (oGrid.dm 396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 396) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1043183363053690329107083853009537655353611688786720389649972220799126103320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_396_400 : bothSeg evalE (oGrid.idx 396) (oGrid.dm 396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 396) oGrid.kl oGrid.kr 400 400 ⟨false, 1043183363053690329107083853009537655353611688786720389649972220799126103320⟩ ⟨false, 0⟩ ⟨false, 1663154759479164763436007355200995202736694980155349469320996090206446682098⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_396_800 : bothSeg evalE (oGrid.idx 396) (oGrid.dm 396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 396) oGrid.kl oGrid.kr 400 800 ⟨false, 1663154759479164763436007355200995202736694980155349469320996090206446682098⟩ ⟨false, 0⟩ ⟨false, 1843176010940329952685007111787701401190926815053371163379497430118031065358⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_396_1200 : bothSeg evalE (oGrid.idx 396) (oGrid.dm 396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 396) oGrid.kl oGrid.kr 400 1200 ⟨false, 1843176010940329952685007111787701401190926815053371163379497430118031065358⟩ ⟨false, 0⟩ ⟨false, 1791127300558307558956196363833718422631387166566870298957000530025979819628⟩ ⟨false, 56209234827839800402476027039055928883043750918804117882844953500845337110⟩ = true := by
  decide +kernel

theorem b_396_1600 : bothSeg evalE (oGrid.idx 396) (oGrid.dm 396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 396) oGrid.kl oGrid.kr 400 1600 ⟨false, 1791127300558307558956196363833718422631387166566870298957000530025979819628⟩ ⟨false, 56209234827839800402476027039055928883043750918804117882844953500845337110⟩ ⟨false, 1661439839483216480261539120862285006164766188762149907052458439607955585430⟩ ⟨false, 185896695902930879097133270010489345349664728723524509787387043918869571308⟩ = true := by
  decide +kernel

theorem b_396_2000 : bothSeg evalE (oGrid.idx 396) (oGrid.dm 396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 396) oGrid.kl oGrid.kr 400 2000 ⟨false, 1661439839483216480261539120862285006164766188762149907052458439607955585430⟩ ⟨false, 185896695902930879097133270010489345349664728723524509787387043918869571308⟩ ⟨false, 1662291149941365293744586340928166478279274326661950762501301578538948313972⟩ ⟨false, 192854115213031534024038265495592457843984779401775306898952436380940132462⟩ = true := by
  decide +kernel

theorem b_396_2400 : bothLoop evalE (oGrid.idx 396) (oGrid.dm 396) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 396) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1662291149941365293744586340928166478279274326661950762501301578538948313972⟩ ⟨false, 192854115213031534024038265495592457843984779401775306898952436380940132462⟩ = true := by
  decide +kernel

theorem o_row_396 : oGrid.row evalE 396 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_396_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_396_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_396_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_396_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_396_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_396_2000).1 (bothLoop_sound b_396_2400).1))))))

theorem n_row_396 : nGrid.row evalE 396 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_396_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_396_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_396_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_396_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_396_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_396_2000).2 (bothLoop_sound b_396_2400).2))))))

theorem b_397_0 : bothSeg evalE (oGrid.idx 397) (oGrid.dm 397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 397) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1038013072683902806042715466738645783215656026011651995284363527242648457030⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_397_400 : bothSeg evalE (oGrid.idx 397) (oGrid.dm 397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 397) oGrid.kl oGrid.kr 400 400 ⟨false, 1038013072683902806042715466738645783215656026011651995284363527242648457030⟩ ⟨false, 0⟩ ⟨false, 1654658496643825691188894356402895516433564928238425966328207992715816956068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_397_800 : bothSeg evalE (oGrid.idx 397) (oGrid.dm 397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 397) oGrid.kl oGrid.kr 400 800 ⟨false, 1654658496643825691188894356402895516433564928238425966328207992715816956068⟩ ⟨false, 0⟩ ⟨false, 1833311753423483007160162159063192294088678602846740531499890622413756150112⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_397_1200 : bothSeg evalE (oGrid.idx 397) (oGrid.dm 397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 397) oGrid.kl oGrid.kr 400 1200 ⟨false, 1833311753423483007160162159063192294088678602846740531499890622413756150112⟩ ⟨false, 0⟩ ⟨false, 1780639397860049749580514738682878764649418650917695813096202316268549934724⟩ ⟨false, 56713256366541826312437530928062095882151016066697466021986486970262633124⟩ = true := by
  decide +kernel

theorem b_397_1600 : bothSeg evalE (oGrid.idx 397) (oGrid.dm 397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 397) oGrid.kl oGrid.kr 400 1600 ⟨false, 1780639397860049749580514738682878764649418650917695813096202316268549934724⟩ ⟨false, 56713256366541826312437530928062095882151016066697466021986486970262633124⟩ ⟨false, 1651542279858456983044091574827373160070792942871219926677387385296831686820⟩ ⟨false, 185810374368134592848860694783567700460776724113173352440801417941980881028⟩ = true := by
  decide +kernel

theorem b_397_2000 : bothSeg evalE (oGrid.idx 397) (oGrid.dm 397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 397) oGrid.kl oGrid.kr 400 2000 ⟨false, 1651542279858456983044091574827373160070792942871219926677387385296831686820⟩ ⟨false, 185810374368134592848860694783567700460776724113173352440801417941980881028⟩ ⟨false, 1652412381177707407246666814556252938526043025609698367486967902827257413910⟩ ⟨false, 192765689425372138005526531341918798072414075154184306923344066675796646348⟩ = true := by
  decide +kernel

theorem b_397_2400 : bothLoop evalE (oGrid.idx 397) (oGrid.dm 397) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 397) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1652412381177707407246666814556252938526043025609698367486967902827257413910⟩ ⟨false, 192765689425372138005526531341918798072414075154184306923344066675796646348⟩ = true := by
  decide +kernel

theorem o_row_397 : oGrid.row evalE 397 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_397_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_397_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_397_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_397_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_397_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_397_2000).1 (bothLoop_sound b_397_2400).1))))))

theorem n_row_397 : nGrid.row evalE 397 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_397_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_397_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_397_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_397_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_397_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_397_2000).2 (bothLoop_sound b_397_2400).2))))))

theorem b_398_0 : bothSeg evalE (oGrid.idx 398) (oGrid.dm 398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 398) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1032860848089733342422027945835019445998587231893541023405673900244265633386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_398_400 : bothSeg evalE (oGrid.idx 398) (oGrid.dm 398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 398) oGrid.kl oGrid.kr 400 400 ⟨false, 1032860848089733342422027945835019445998587231893541023405673900244265633386⟩ ⟨false, 0⟩ ⟨false, 1646191725436394633915280482136846543636941122004364184499645139802052120130⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_398_800 : bothSeg evalE (oGrid.idx 398) (oGrid.dm 398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 398) oGrid.kl oGrid.kr 400 800 ⟨false, 1646191725436394633915280482136846543636941122004364184499645139802052120130⟩ ⟨false, 0⟩ ⟨false, 1823482009919426387847608887567002007575889994311692820186346087830479429872⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_398_1200 : bothSeg evalE (oGrid.idx 398) (oGrid.dm 398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 398) oGrid.kl oGrid.kr 400 1200 ⟨false, 1823482009919426387847608887567002007575889994311692820186346087830479429872⟩ ⟨false, 0⟩ ⟨false, 1770187097228362152029964010159466323913730116633396987259696701715085357590⟩ ⟨false, 57218172246244012327489517484479544785850900530975881132630807387558771818⟩ = true := by
  decide +kernel

theorem b_398_1600 : bothSeg evalE (oGrid.idx 398) (oGrid.dm 398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 398) oGrid.kl oGrid.kr 400 1600 ⟨false, 1770187097228362152029964010159466323913730116633396987259696701715085357590⟩ ⟨false, 57218172246244012327489517484479544785850900530975881132630807387558771818⟩ ⟨false, 1641681783377376695507738141540349160102709882991646449550340869036894407864⟩ ⟨false, 185723486097229468849715386103596708596871134172726418841986640065749721544⟩ = true := by
  decide +kernel

theorem b_398_2000 : bothSeg evalE (oGrid.idx 398) (oGrid.dm 398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 398) oGrid.kl oGrid.kr 400 2000 ⟨false, 1641681783377376695507738141540349160102709882991646449550340869036894407864⟩ ⟨false, 185723486097229468849715386103596708596871134172726418841986640065749721544⟩ ⟨false, 1642570405773109163142983641405596715473606592563301816507742345632819426948⟩ ⟨false, 192676876284779594347036494470365513818273538626396716972303671339472988880⟩ = true := by
  decide +kernel

theorem b_398_2400 : bothLoop evalE (oGrid.idx 398) (oGrid.dm 398) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 398) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1642570405773109163142983641405596715473606592563301816507742345632819426948⟩ ⟨false, 192676876284779594347036494470365513818273538626396716972303671339472988880⟩ = true := by
  decide +kernel

theorem o_row_398 : oGrid.row evalE 398 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_398_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_398_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_398_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_398_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_398_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_398_2000).1 (bothLoop_sound b_398_2400).1))))))

theorem n_row_398 : nGrid.row evalE 398 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_398_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_398_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_398_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_398_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_398_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_398_2000).2 (bothLoop_sound b_398_2400).2))))))

theorem b_399_0 : bothSeg evalE (oGrid.idx 399) (oGrid.dm 399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 399) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1027726645078354722655614342638537161925731796732358698272894039440101233910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_399_400 : bothSeg evalE (oGrid.idx 399) (oGrid.dm 399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 399) oGrid.kl oGrid.kr 400 400 ⟨false, 1027726645078354722655614342638537161925731796732358698272894039440101233910⟩ ⟨false, 0⟩ ⟨false, 1637754352849131303748842918311863174049968243164243749444338710868223496496⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_399_800 : bothSeg evalE (oGrid.idx 399) (oGrid.dm 399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 399) oGrid.kl oGrid.kr 400 800 ⟨false, 1637754352849131303748842918311863174049968243164243749444338710868223496496⟩ ⟨false, 0⟩ ⟨false, 1813686551561591148688559766908373167294965135012809205706864632770845909890⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_399_1200 : bothSeg evalE (oGrid.idx 399) (oGrid.dm 399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 399) oGrid.kl oGrid.kr 400 1200 ⟨false, 1813686551561591148688559766908373167294965135012809205706864632770845909890⟩ ⟨false, 0⟩ ⟨false, 1759770251301003349471860313319413510551614165592777886396784659902988788654⟩ ⟨false, 57724278581848478049433526093328551297048621805905995296387811850751424436⟩ = true := by
  decide +kernel

theorem b_399_1600 : bothSeg evalE (oGrid.idx 399) (oGrid.dm 399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 399) oGrid.kl oGrid.kr 400 1600 ⟨false, 1759770251301003349471860313319413510551614165592777886396784659902988788654⟩ ⟨false, 57724278581848478049433526093328551297048621805905995296387811850751424436⟩ ⟨false, 1631858040722699236801941090588943258206289808178182875296931764745452558612⟩ ⟨false, 185636489160152590719352748823798803642372979220501006396240707008287654478⟩ = true := by
  decide +kernel

theorem b_399_2000 : bothSeg evalE (oGrid.idx 399) (oGrid.dm 399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 399) oGrid.kl oGrid.kr 400 2000 ⟨false, 1631858040722699236801941090588943258206289808178182875296931764745452558612⟩ ⟨false, 185636489160152590719352748823798803642372979220501006396240707008287654478⟩ ⟨false, 1632764958187329735615991347830201772124117132885276861198240653165876089224⟩ ⟨false, 192587718030786160472864139582054465382088861918250162936874842909785083582⟩ = true := by
  decide +kernel

theorem b_399_2400 : bothLoop evalE (oGrid.idx 399) (oGrid.dm 399) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 399) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1632764958187329735615991347830201772124117132885276861198240653165876089224⟩ ⟨false, 192587718030786160472864139582054465382088861918250162936874842909785083582⟩ = true := by
  decide +kernel

theorem o_row_399 : oGrid.row evalE 399 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_399_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_399_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_399_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_399_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_399_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_399_2000).1 (bothLoop_sound b_399_2400).1))))))

theorem n_row_399 : nGrid.row evalE 399 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_399_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_399_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_399_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_399_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_399_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_399_2000).2 (bothLoop_sound b_399_2400).2))))))

theorem b_400_0 : bothSeg evalE (oGrid.idx 400) (oGrid.dm 400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 400) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1022610411308719091977553848724595745679560098986225275509003212480903701082⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_400_400 : bothSeg evalE (oGrid.idx 400) (oGrid.dm 400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 400) oGrid.kl oGrid.kr 400 400 ⟨false, 1022610411308719091977553848724595745679560098986225275509003212480903701082⟩ ⟨false, 0⟩ ⟨false, 1629346305420376283996675320742074445309774619504294773747629135478213403426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_400_800 : bothSeg evalE (oGrid.idx 400) (oGrid.dm 400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 400) oGrid.kl oGrid.kr 400 800 ⟨false, 1629346305420376283996675320742074445309774619504294773747629135478213403426⟩ ⟨false, 0⟩ ⟨false, 1803925455753432721830678602322648535348171452243691823290870775222217972940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_400_1200 : bothSeg evalE (oGrid.idx 400) (oGrid.dm 400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 400) oGrid.kl oGrid.kr 400 1200 ⟨false, 1803925455753432721830678602322648535348171452243691823290870775222217972940⟩ ⟨false, 0⟩ ⟨false, 1749389244868548403253985130958049483111034451476602270928510171972616036110⟩ ⟨false, 58231369849404914071259615870319892357580555239915130890157349295095410530⟩ = true := by
  decide +kernel

theorem b_400_1600 : bothSeg evalE (oGrid.idx 400) (oGrid.dm 400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 400) oGrid.kl oGrid.kr 400 1600 ⟨false, 1749389244868548403253985130958049483111034451476602270928510171972616036110⟩ ⟨false, 58231369849404914071259615870319892357580555239915130890157349295095410530⟩ ⟨false, 1622071241864060102230513025137501989143791829422316624350529026456419381344⟩ ⟨false, 185549372853893215094731721690867386324823177294200777468138494811292065296⟩ = true := by
  decide +kernel

theorem b_400_2000 : bothSeg evalE (oGrid.idx 400) (oGrid.dm 400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 400) oGrid.kl oGrid.kr 400 2000 ⟨false, 1622071241864060102230513025137501989143791829422316624350529026456419381344⟩ ⟨false, 185549372853893215094731721690867386324823177294200777468138494811292065296⟩ ⟨false, 1622996279063464417878765714975833215894491851140934768043169249478858176570⟩ ⟨false, 192499135039798332534977432365599100056089287117755012326517457732556879400⟩ = true := by
  decide +kernel

theorem b_400_2400 : bothLoop evalE (oGrid.idx 400) (oGrid.dm 400) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 400) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1622996279063464417878765714975833215894491851140934768043169249478858176570⟩ ⟨false, 192499135039798332534977432365599100056089287117755012326517457732556879400⟩ = true := by
  decide +kernel

theorem o_row_400 : oGrid.row evalE 400 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_400_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_400_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_400_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_400_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_400_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_400_2000).1 (bothLoop_sound b_400_2400).1))))))

theorem n_row_400 : nGrid.row evalE 400 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_400_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_400_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_400_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_400_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_400_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_400_2000).2 (bothLoop_sound b_400_2400).2))))))

theorem b_401_0 : bothSeg evalE (oGrid.idx 401) (oGrid.dm 401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 401) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1017512102226780014997309022820042850973708047795968523398055097405980247368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_401_400 : bothSeg evalE (oGrid.idx 401) (oGrid.dm 401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 401) oGrid.kl oGrid.kr 400 400 ⟨false, 1017512102226780014997309022820042850973708047795968523398055097405980247368⟩ ⟨false, 0⟩ ⟨false, 1620967520400791615519772603491594922103854124925093482087806498971257552200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_401_800 : bothSeg evalE (oGrid.idx 401) (oGrid.dm 401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 401) oGrid.kl oGrid.kr 400 800 ⟨false, 1620967520400791615519772603491594922103854124925093482087806498971257552200⟩ ⟨false, 0⟩ ⟨false, 1794198623699962105560137437061613355940685469147867660336358249678555262396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_401_1200 : bothSeg evalE (oGrid.idx 401) (oGrid.dm 401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 401) oGrid.kl oGrid.kr 400 1200 ⟨false, 1794198623699962105560137437061613355940685469147867660336358249678555262396⟩ ⟨false, 0⟩ ⟨false, 1739044002729504387747654902742195473554386791962732925135064623051604504698⟩ ⟨false, 58738592019349552512956278862348540470538892434756242206502112058112651942⟩ = true := by
  decide +kernel

theorem b_401_1600 : bothSeg evalE (oGrid.idx 401) (oGrid.dm 401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 401) oGrid.kl oGrid.kr 400 1600 ⟨false, 1739044002729504387747654902742195473554386791962732925135064623051604504698⟩ ⟨false, 58738592019349552512956278862348540470538892434756242206502112058112651942⟩ ⟨false, 1612321099455214047329229037588061097147165573024562279849475152689923012788⟩ ⟨false, 185461495293639892931382144016482916877760111372926887492091582419794143852⟩ = true := by
  decide +kernel

theorem b_401_2000 : bothSeg evalE (oGrid.idx 401) (oGrid.dm 401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 401) oGrid.kl oGrid.kr 400 2000 ⟨false, 1612321099455214047329229037588061097147165573024562279849475152689923012788⟩ ⟨false, 185461495293639892931382144016482916877760111372926887492091582419794143852⟩ ⟨false, 1613264139829731587568367869544526045276738646910581757852582559283735225378⟩ ⟨false, 192409746055884299180201890122926620522558299485271600359955951730937802970⟩ = true := by
  decide +kernel

theorem b_401_2400 : bothLoop evalE (oGrid.idx 401) (oGrid.dm 401) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 401) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1613264139829731587568367869544526045276738646910581757852582559283735225378⟩ ⟨false, 192409746055884299180201890122926620522558299485271600359955951730937802970⟩ = true := by
  decide +kernel

theorem o_row_401 : oGrid.row evalE 401 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_401_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_401_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_401_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_401_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_401_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_401_2000).1 (bothLoop_sound b_401_2400).1))))))

theorem n_row_401 : nGrid.row evalE 401 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_401_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_401_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_401_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_401_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_401_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_401_2000).2 (bothLoop_sound b_401_2400).2))))))

theorem b_402_0 : bothSeg evalE (oGrid.idx 402) (oGrid.dm 402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 402) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1012431673177755861213706827968823837934344365412119566352938780222536949638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_402_400 : bothSeg evalE (oGrid.idx 402) (oGrid.dm 402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 402) oGrid.kl oGrid.kr 400 400 ⟨false, 1012431673177755861213706827968823837934344365412119566352938780222536949638⟩ ⟨false, 0⟩ ⟨false, 1612617936771623671720973699407790330900477615231246236617285749129148860324⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_402_800 : bothSeg evalE (oGrid.idx 402) (oGrid.dm 402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 402) oGrid.kl oGrid.kr 400 800 ⟨false, 1612617936771623671720973699407790330900477615231246236617285749129148860324⟩ ⟨false, 0⟩ ⟨false, 1784505870986550478533714626633741691161610268932756763847616349046239348618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_402_1200 : bothSeg evalE (oGrid.idx 402) (oGrid.dm 402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 402) oGrid.kl oGrid.kr 400 1200 ⟨false, 1784505870986550478533714626633741691161610268932756763847616349046239348618⟩ ⟨false, 0⟩ ⟨false, 1728734748607091126213594203996287121304492482869723532739125507965495652258⟩ ⟨false, 59245715761279924683245354122667180369983434877598681466641115365130573908⟩ = true := by
  decide +kernel

theorem b_402_1600 : bothSeg evalE (oGrid.idx 402) (oGrid.dm 402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 402) oGrid.kl oGrid.kr 400 1600 ⟨false, 1728734748607091126213594203996287121304492482869723532739125507965495652258⟩ ⟨false, 59245715761279924683245354122667180369983434877598681466641115365130573908⟩ ⟨false, 1602607708608257271447346192529688720149774309354678431824261611285166323864⟩ ⟨false, 185372755760113779449493365589265581524701608392643782381505012045459902302⟩ = true := by
  decide +kernel

theorem b_402_2000 : bothSeg evalE (oGrid.idx 402) (oGrid.dm 402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 402) oGrid.kl oGrid.kr 400 2000 ⟨false, 1602607708608257271447346192529688720149774309354678431824261611285166323864⟩ ⟨false, 185372755760113779449493365589265581524701608392643782381505012045459902302⟩ ⟨false, 1603568693685677337615769461687559751457461468605594710732812342981527883806⟩ ⟨false, 192319391692010833802038398764219945666111938616877222594180083203720054730⟩ = true := by
  decide +kernel

theorem b_402_2400 : bothLoop evalE (oGrid.idx 402) (oGrid.dm 402) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 402) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1603568693685677337615769461687559751457461468605594710732812342981527883806⟩ ⟨false, 192319391692010833802038398764219945666111938616877222594180083203720054730⟩ = true := by
  decide +kernel

theorem o_row_402 : oGrid.row evalE 402 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_402_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_402_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_402_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_402_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_402_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_402_2000).1 (bothLoop_sound b_402_2400).1))))))

theorem n_row_402 : nGrid.row evalE 402 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_402_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_402_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_402_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_402_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_402_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_402_2000).2 (bothLoop_sound b_402_2400).2))))))

theorem b_403_0 : bothSeg evalE (oGrid.idx 403) (oGrid.dm 403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 403) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1007369071249775503038298465613923155939538555081372317378056023639751011820⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_403_400 : bothSeg evalE (oGrid.idx 403) (oGrid.dm 403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 403) oGrid.kl oGrid.kr 400 400 ⟨false, 1007369071249775503038298465613923155939538555081372317378056023639751011820⟩ ⟨false, 0⟩ ⟨false, 1604297460325599417977860083374751523207757912348935153454432922796822777640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_403_800 : bothSeg evalE (oGrid.idx 403) (oGrid.dm 403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 403) oGrid.kl oGrid.kr 400 800 ⟨false, 1604297460325599417977860083374751523207757912348935153454432922796822777640⟩ ⟨false, 0⟩ ⟨false, 1774847236037573852251052342882588221053065381106107815631351046337275918536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_403_1200 : bothSeg evalE (oGrid.idx 403) (oGrid.dm 403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 403) oGrid.kl oGrid.kr 400 1200 ⟨false, 1774847236037573852251052342882588221053065381106107815631351046337275918536⟩ ⟨false, 0⟩ ⟨false, 1718461424136863044186376774294567974546907428943488101552544427441091622926⟩ ⟨false, 59753848026160828703943232479365493460237206912193471965049889902164150878⟩ = true := by
  decide +kernel

theorem b_403_1600 : bothSeg evalE (oGrid.idx 403) (oGrid.dm 403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 403) oGrid.kl oGrid.kr 400 1600 ⟨false, 1718461424136863044186376774294567974546907428943488101552544427441091622926⟩ ⟨false, 59753848026160828703943232479365493460237206912193471965049889902164150878⟩ ⟨false, 1592930994602217586284832301737126462095739369844323407181831742786820768850⟩ ⟨false, 185284277560806286605487705036807005911405266011358166335762574556435004954⟩ = true := by
  decide +kernel

theorem b_403_2000 : bothSeg evalE (oGrid.idx 403) (oGrid.dm 403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 403) oGrid.kl oGrid.kr 400 2000 ⟨false, 1592930994602217586284832301737126462095739369844323407181831742786820768850⟩ ⟨false, 185284277560806286605487705036807005911405266011358166335762574556435004954⟩ ⟨false, 1593909967656823149968961094373485372451062002388707538267178813223112709700⟩ ⟨false, 192229791780435777659324761683416235242800607659721503022288484410314683938⟩ = true := by
  decide +kernel

theorem b_403_2400 : bothLoop evalE (oGrid.idx 403) (oGrid.dm 403) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 403) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1593909967656823149968961094373485372451062002388707538267178813223112709700⟩ ⟨false, 192229791780435777659324761683416235242800607659721503022288484410314683938⟩ = true := by
  decide +kernel

theorem o_row_403 : oGrid.row evalE 403 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_403_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_403_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_403_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_403_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_403_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_403_2000).1 (bothLoop_sound b_403_2400).1))))))

theorem n_row_403 : nGrid.row evalE 403 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_403_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_403_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_403_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_403_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_403_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_403_2000).2 (bothLoop_sound b_403_2400).2))))))

theorem b_404_0 : bothSeg evalE (oGrid.idx 404) (oGrid.dm 404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 404) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1002324251993145014279500848793031614414797715226402606443312738434312919146⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_404_400 : bothSeg evalE (oGrid.idx 404) (oGrid.dm 404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 404) oGrid.kl oGrid.kr 400 400 ⟨false, 1002324251993145014279500848793031614414797715226402606443312738434312919146⟩ ⟨false, 0⟩ ⟨false, 1596006029923042576901146649193804909938874931230337188608211084383527047722⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_404_800 : bothSeg evalE (oGrid.idx 404) (oGrid.dm 404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 404) oGrid.kl oGrid.kr 400 800 ⟨false, 1596006029923042576901146649193804909938874931230337188608211084383527047722⟩ ⟨false, 0⟩ ⟨false, 1765222612596625845781742864163502319292131953267382222605818503850896443192⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_404_1200 : bothSeg evalE (oGrid.idx 404) (oGrid.dm 404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 404) oGrid.kl oGrid.kr 400 1200 ⟨false, 1765222612596625845781742864163502319292131953267382222605818503850896443192⟩ ⟨false, 0⟩ ⟨false, 1708224279127629488409481604010319448922694488642331092491931938399519651890⟩ ⟨false, 60261552288087498446128479234272390553797323225101853031417669349340263260⟩ = true := by
  decide +kernel

theorem b_404_1600 : bothSeg evalE (oGrid.idx 404) (oGrid.dm 404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 404) oGrid.kl oGrid.kr 400 1600 ⟨false, 1708224279127629488409481604010319448922694488642331092491931938399519651890⟩ ⟨false, 60261552288087498446128479234272390553797323225101853031417669349340263260⟩ ⟨false, 1583290881896115481040422365825589693541488835757761320804277209578561687784⟩ ⟨false, 185194949519601505815187717419002145935002976109671624719072398170298227366⟩ = true := by
  decide +kernel

theorem b_404_2000 : bothSeg evalE (oGrid.idx 404) (oGrid.dm 404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 404) oGrid.kl oGrid.kr 400 2000 ⟨false, 1583290881896115481040422365825589693541488835757761320804277209578561687784⟩ ⟨false, 185194949519601505815187717419002145935002976109671624719072398170298227366⟩ ⟨false, 1584287893153868387393835529198438721714803976360306650526900386169385344570⟩ ⟨false, 192139222385180554697486197327080558811473095577410721160164015667141371962⟩ = true := by
  decide +kernel

theorem b_404_2400 : bothLoop evalE (oGrid.idx 404) (oGrid.dm 404) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 404) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1584287893153868387393835529198438721714803976360306650526900386169385344570⟩ ⟨false, 192139222385180554697486197327080558811473095577410721160164015667141371962⟩ = true := by
  decide +kernel

theorem o_row_404 : oGrid.row evalE 404 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_404_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_404_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_404_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_404_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_404_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_404_2000).1 (bothLoop_sound b_404_2400).1))))))

theorem n_row_404 : nGrid.row evalE 404 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_404_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_404_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_404_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_404_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_404_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_404_2000).2 (bothLoop_sound b_404_2400).2))))))

theorem b_405_0 : bothSeg evalE (oGrid.idx 405) (oGrid.dm 405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 405) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 997297171294963145717535258686638801653328759653668129021154339598633265644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_405_400 : bothSeg evalE (oGrid.idx 405) (oGrid.dm 405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 405) oGrid.kl oGrid.kr 400 400 ⟨false, 997297171294963145717535258686638801653328759653668129021154339598633265644⟩ ⟨false, 0⟩ ⟨false, 1587743565882708844858480238778632123363295655665866369794291715856822176012⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_405_800 : bothSeg evalE (oGrid.idx 405) (oGrid.dm 405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 405) oGrid.kl oGrid.kr 400 800 ⟨false, 1587743565882708844858480238778632123363295655665866369794291715856822176012⟩ ⟨false, 0⟩ ⟨false, 1755631805829316009724515654237730053350423621550274852343001953318610461790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_405_1200 : bothSeg evalE (oGrid.idx 405) (oGrid.dm 405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 405) oGrid.kl oGrid.kr 400 1200 ⟨false, 1755631805829316009724515654237730053350423621550274852343001953318610461790⟩ ⟨false, 0⟩ ⟨false, 1698023096723375445327978864946460822850922962773766432856013353522435219132⟩ ⟨false, 60768779728717136618654602987056264464798468962889063567572968203747948000⟩ = true := by
  decide +kernel

theorem b_405_1600 : bothSeg evalE (oGrid.idx 405) (oGrid.dm 405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 405) oGrid.kl oGrid.kr 400 1600 ⟨false, 1698023096723375445327978864946460822850922962773766432856013353522435219132⟩ ⟨false, 60768779728717136618654602987056264464798468962889063567572968203747948000⟩ ⟨false, 1573687009648156181978444361472141426695738428580452520633359132957052696648⟩ ⟨false, 185104866803936399968189106461375660619983003156202975790227188769130470484⟩ = true := by
  decide +kernel

theorem b_405_2000 : bothSeg evalE (oGrid.idx 405) (oGrid.dm 405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 405) oGrid.kl oGrid.kr 400 2000 ⟨false, 1573687009648156181978444361472141426695738428580452520633359132957052696648⟩ ⟨false, 185104866803936399968189106461375660619983003156202975790227188769130470484⟩ ⟨false, 1574702190463499263546669299702004403836162888050995438327824698781788291070⟩ ⟨false, 192047491541284037736673775936893410423149647736608297879244216098799814618⟩ = true := by
  decide +kernel

theorem b_405_2400 : bothLoop evalE (oGrid.idx 405) (oGrid.dm 405) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 405) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1574702190463499263546669299702004403836162888050995438327824698781788291070⟩ ⟨false, 192047491541284037736673775936893410423149647736608297879244216098799814618⟩ = true := by
  decide +kernel

theorem o_row_405 : oGrid.row evalE 405 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_405_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_405_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_405_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_405_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_405_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_405_2000).1 (bothLoop_sound b_405_2400).1))))))

theorem n_row_405 : nGrid.row evalE 405 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_405_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_405_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_405_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_405_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_405_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_405_2000).2 (bothLoop_sound b_405_2400).2))))))

theorem b_406_0 : bothSeg evalE (oGrid.idx 406) (oGrid.dm 406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 406) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 992287780637592455580537464215133694628864583615291029764502079207220325980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_406_400 : bothSeg evalE (oGrid.idx 406) (oGrid.dm 406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 406) oGrid.kl oGrid.kr 400 400 ⟨false, 992287780637592455580537464215133694628864583615291029764502079207220325980⟩ ⟨false, 0⟩ ⟨false, 1579510021813514471152368710848199910825457423014139280395149179789716824836⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_406_800 : bothSeg evalE (oGrid.idx 406) (oGrid.dm 406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 406) oGrid.kl oGrid.kr 400 800 ⟨false, 1579510021813514471152368710848199910825457423014139280395149179789716824836⟩ ⟨false, 0⟩ ⟨false, 1746074893817164698638140987605861766645192366719015796651451888710582340674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_406_1200 : bothSeg evalE (oGrid.idx 406) (oGrid.dm 406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 406) oGrid.kl oGrid.kr 400 1200 ⟨false, 1746074893817164698638140987605861766645192366719015796651451888710582340674⟩ ⟨false, 0⟩ ⟨false, 1687858224595717990456534856077514446852555930441590778568606897718283821372⟩ ⟨false, 61276191178836113016854982918659061839715871454143285046321661008746214008⟩ = true := by
  decide +kernel

theorem b_406_1600 : bothSeg evalE (oGrid.idx 406) (oGrid.dm 406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 406) oGrid.kl oGrid.kr 400 1600 ⟨false, 1687858224595717990456534856077514446852555930441590778568606897718283821372⟩ ⟨false, 61276191178836113016854982918659061839715871454143285046321661008746214008⟩ ⟨false, 1564119563168502209170306667035615835327229377563719154865415140516353683076⟩ ⟨false, 185014852606051894303083171960557673365042424332014908749513418210676352304⟩ = true := by
  decide +kernel

theorem b_406_2000 : bothSeg evalE (oGrid.idx 406) (oGrid.dm 406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 406) oGrid.kl oGrid.kr 400 2000 ⟨false, 1564119563168502209170306667035615835327229377563719154865415140516353683076⟩ ⟨false, 185014852606051894303083171960557673365042424332014908749513418210676352304⟩ ⟨false, 1565153102269826748356490576457961762962189206400796690882846424545738959278⟩ ⟨false, 191955894647255211619513959148152951564258648512586342963633850734596808918⟩ = true := by
  decide +kernel

theorem b_406_2400 : bothLoop evalE (oGrid.idx 406) (oGrid.dm 406) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 406) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1565153102269826748356490576457961762962189206400796690882846424545738959278⟩ ⟨false, 191955894647255211619513959148152951564258648512586342963633850734596808918⟩ = true := by
  decide +kernel

theorem o_row_406 : oGrid.row evalE 406 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_406_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_406_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_406_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_406_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_406_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_406_2000).1 (bothLoop_sound b_406_2400).1))))))

theorem n_row_406 : nGrid.row evalE 406 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_406_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_406_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_406_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_406_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_406_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_406_2000).2 (bothLoop_sound b_406_2400).2))))))

theorem b_407_0 : bothSeg evalE (oGrid.idx 407) (oGrid.dm 407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 407) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 987296031410783927257035975430307077011535773024888650494913492325260122196⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_407_400 : bothSeg evalE (oGrid.idx 407) (oGrid.dm 407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 407) oGrid.kl oGrid.kr 400 400 ⟨false, 987296031410783927257035975430307077011535773024888650494913492325260122196⟩ ⟨false, 0⟩ ⟨false, 1571305298787697866038144164190333002975482766282844972698746649418604961836⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_407_800 : bothSeg evalE (oGrid.idx 407) (oGrid.dm 407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 407) oGrid.kl oGrid.kr 400 800 ⟨false, 1571305298787697866038144164190333002975482766282844972698746649418604961836⟩ ⟨false, 0⟩ ⟨false, 1736551764361398501537116251772496401823907896247307673967092912685355105132⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_407_1200 : bothSeg evalE (oGrid.idx 407) (oGrid.dm 407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 407) oGrid.kl oGrid.kr 400 1200 ⟨false, 1736551764361398501537116251772496401823907896247307673967092912685355105132⟩ ⟨false, 0⟩ ⟨false, 1677729703612454766645184677069139487662504790689931697286226789603693613012⟩ ⟨false, 61783306084644352765458264441565571037024468218721210116680129501214047898⟩ = true := by
  decide +kernel

theorem b_407_1600 : bothSeg evalE (oGrid.idx 407) (oGrid.dm 407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 407) oGrid.kl oGrid.kr 400 1600 ⟨false, 1677729703612454766645184677069139487662504790689931697286226789603693613012⟩ ⟨false, 61783306084644352765458264441565571037024468218721210116680129501214047898⟩ ⟨false, 1554588420048082944611467355256592078078049944905908264456702045096935460316⟩ ⟨false, 184924589649016174799175586254112980621479314002744642946204874007972200594⟩ = true := by
  decide +kernel

theorem b_407_2000 : bothSeg evalE (oGrid.idx 407) (oGrid.dm 407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 407) oGrid.kl oGrid.kr 400 2000 ⟨false, 1554588420048082944611467355256592078078049944905908264456702045096935460316⟩ ⟨false, 184924589649016174799175586254112980621479314002744642946204874007972200594⟩ ⟨false, 1555640553512865862645257070783807940388289572670511247761724859315585883914⟩ ⟨false, 191863787002802103147886938375107991888106440421894291302986972148256532502⟩ = true := by
  decide +kernel

theorem b_407_2400 : bothLoop evalE (oGrid.idx 407) (oGrid.dm 407) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 407) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1555640553512865862645257070783807940388289572670511247761724859315585883914⟩ ⟨false, 191863787002802103147886938375107991888106440421894291302986972148256532502⟩ = true := by
  decide +kernel

theorem o_row_407 : oGrid.row evalE 407 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_407_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_407_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_407_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_407_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_407_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_407_2000).1 (bothLoop_sound b_407_2400).1))))))

theorem n_row_407 : nGrid.row evalE 407 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_407_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_407_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_407_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_407_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_407_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_407_2000).2 (bothLoop_sound b_407_2400).2))))))

theorem o_blk_384 : allFrom (fun j => oGrid.row evalE j) 384 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 384) o_row_384 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 385) o_row_385 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 386) o_row_386 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 387) o_row_387 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 388) o_row_388 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 389) o_row_389 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 390) o_row_390 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 391) o_row_391 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 392) o_row_392 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 393) o_row_393 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 394) o_row_394 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 395) o_row_395 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 396) o_row_396 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 397) o_row_397 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 398) o_row_398 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 399) o_row_399 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 400) o_row_400 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 401) o_row_401 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 402) o_row_402 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 403) o_row_403 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 404) o_row_404 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 405) o_row_405 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 406) o_row_406 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 407) o_row_407 (allFrom_zero (fun j => oGrid.row evalE j) 408)))))))))))))))))))))))))

theorem n_blk_384 : allFrom (fun j => nGrid.row evalE j) 384 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 384) n_row_384 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 385) n_row_385 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 386) n_row_386 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 387) n_row_387 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 388) n_row_388 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 389) n_row_389 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 390) n_row_390 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 391) n_row_391 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 392) n_row_392 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 393) n_row_393 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 394) n_row_394 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 395) n_row_395 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 396) n_row_396 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 397) n_row_397 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 398) n_row_398 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 399) n_row_399 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 400) n_row_400 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 401) n_row_401 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 402) n_row_402 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 403) n_row_403 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 404) n_row_404 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 405) n_row_405 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 406) n_row_406 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 407) n_row_407 (allFrom_zero (fun j => nGrid.row evalE j) 408)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
