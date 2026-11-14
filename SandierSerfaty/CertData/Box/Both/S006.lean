/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 6 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `144`–`167`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_144_0 : bothSeg evalE (oGrid.idx 144) (oGrid.dm 144) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 144) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3073946733229534242816905181389312491238280987953095329548248652060313330764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_144_400 : bothSeg evalE (oGrid.idx 144) (oGrid.dm 144) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 144) oGrid.kl oGrid.kr 400 400 ⟨false, 3073946733229534242816905181389312491238280987953095329548248652060313330764⟩ ⟨false, 0⟩ ⟨false, 4968025844283500371698977981147778010351235175451733006085440278525648785646⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_144_800 : bothSeg evalE (oGrid.idx 144) (oGrid.dm 144) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 144) oGrid.kl oGrid.kr 400 800 ⟨false, 4968025844283500371698977981147778010351235175451733006085440278525648785646⟩ ⟨false, 0⟩ ⟨false, 5671227004896356968049112246132074588987356259815160515705473794219576329922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_144_1200 : bothSeg evalE (oGrid.idx 144) (oGrid.dm 144) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 144) oGrid.kl oGrid.kr 400 1200 ⟨false, 5671227004896356968049112246132074588987356259815160515705473794219576329922⟩ ⟨false, 0⟩ ⟨false, 5773894159963402406194437682500882436515580326293280579524324299181351793188⟩ ⟨false, 6291755764714848513351356458524091302088943090397073460770515114225986864⟩ = true := by
  decide +kernel

theorem b_144_1600 : bothSeg evalE (oGrid.idx 144) (oGrid.dm 144) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 144) oGrid.kl oGrid.kr 400 1600 ⟨false, 5773894159963402406194437682500882436515580326293280579524324299181351793188⟩ ⟨false, 6291755764714848513351356458524091302088943090397073460770515114225986864⟩ ⟨false, 5593049774700290882266057493212626207466142184945286871127841989994519006514⟩ ⟨false, 187423350183925136822356602066887234053335913546467484592007268788007533218⟩ = true := by
  decide +kernel

theorem b_144_2000 : bothSeg evalE (oGrid.idx 144) (oGrid.dm 144) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 144) oGrid.kl oGrid.kr 400 2000 ⟨false, 5593049774700290882266057493212626207466142184945286871127841989994519006514⟩ ⟨false, 187423350183925136822356602066887234053335913546467484592007268788007533218⟩ ⟨false, 5546663132890334412917856155903436718943045088679488576809080689083438233272⟩ ⟨false, 234579951096167960916787444777994845146427236054173728558362380288003110462⟩ = true := by
  decide +kernel

theorem b_144_2400 : bothLoop evalE (oGrid.idx 144) (oGrid.dm 144) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 144) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5546663132890334412917856155903436718943045088679488576809080689083438233272⟩ ⟨false, 234579951096167960916787444777994845146427236054173728558362380288003110462⟩ = true := by
  decide +kernel

theorem o_row_144 : oGrid.row evalE 144 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_144_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_144_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_144_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_144_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_144_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_144_2000).1 (bothLoop_sound b_144_2400).1))))))

theorem n_row_144 : nGrid.row evalE 144 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_144_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_144_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_144_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_144_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_144_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_144_2000).2 (bothLoop_sound b_144_2400).2))))))

theorem b_145_0 : bothSeg evalE (oGrid.idx 145) (oGrid.dm 145) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 145) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3062320192518740292843718351363337346212628998747605381263709886973467197604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_145_400 : bothSeg evalE (oGrid.idx 145) (oGrid.dm 145) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 145) oGrid.kl oGrid.kr 400 400 ⟨false, 3062320192518740292843718351363337346212628998747605381263709886973467197604⟩ ⟨false, 0⟩ ⟨false, 4949325517105481728361931674165819319288690725610605420208929268670343360110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_145_800 : bothSeg evalE (oGrid.idx 145) (oGrid.dm 145) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 145) oGrid.kl oGrid.kr 400 800 ⟨false, 4949325517105481728361931674165819319288690725610605420208929268670343360110⟩ ⟨false, 0⟩ ⟨false, 5649688067966957937635217541013144088438947192354054169653253775049525240644⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_145_1200 : bothSeg evalE (oGrid.idx 145) (oGrid.dm 145) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 145) oGrid.kl oGrid.kr 400 1200 ⟨false, 5649688067966957937635217541013144088438947192354054169653253775049525240644⟩ ⟨false, 0⟩ ⟨false, 5751359939832809175688829449188756692658059202355780549027789055797523849920⟩ ⟨false, 6555028381525507515896078765374440231457733985007267817687738902870472018⟩ = true := by
  decide +kernel

theorem b_145_1600 : bothSeg evalE (oGrid.idx 145) (oGrid.dm 145) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 145) oGrid.kl oGrid.kr 400 1600 ⟨false, 5751359939832809175688829449188756692658059202355780549027789055797523849920⟩ ⟨false, 6555028381525507515896078765374440231457733985007267817687738902870472018⟩ ⟨false, 5570676630981423836961899911501260513753402702410041561621908795186086922406⟩ ⟨false, 187526222684674591200939599069257244739602581939498026041383281765310499484⟩ = true := by
  decide +kernel

theorem b_145_2000 : bothSeg evalE (oGrid.idx 145) (oGrid.dm 145) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 145) oGrid.kl oGrid.kr 400 2000 ⟨false, 5570676630981423836961899911501260513753402702410041561621908795186086922406⟩ ⟨false, 187526222684674591200939599069257244739602581939498026041383281765310499484⟩ ⟨false, 5524563005464476828099064056450358587337070217623234460566163165930150331828⟩ ⟨false, 234411510893655788397519179566045866434429555493131328310266142379070203726⟩ = true := by
  decide +kernel

theorem b_145_2400 : bothLoop evalE (oGrid.idx 145) (oGrid.dm 145) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 145) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5524563005464476828099064056450358587337070217623234460566163165930150331828⟩ ⟨false, 234411510893655788397519179566045866434429555493131328310266142379070203726⟩ = true := by
  decide +kernel

theorem o_row_145 : oGrid.row evalE 145 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_145_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_145_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_145_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_145_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_145_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_145_2000).1 (bothLoop_sound b_145_2400).1))))))

theorem n_row_145 : nGrid.row evalE 145 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_145_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_145_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_145_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_145_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_145_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_145_2000).2 (bothLoop_sound b_145_2400).2))))))

theorem b_146_0 : bothSeg evalE (oGrid.idx 146) (oGrid.dm 146) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 146) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3050728703878293171624393189443730790040860972229648350745489746931700685586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_146_400 : bothSeg evalE (oGrid.idx 146) (oGrid.dm 146) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 146) oGrid.kl oGrid.kr 400 400 ⟨false, 3050728703878293171624393189443730790040860972229648350745489746931700685586⟩ ⟨false, 0⟩ ⟨false, 4930678869764482464770355782907152639279323251304588276881947505625703297764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_146_800 : bothSeg evalE (oGrid.idx 146) (oGrid.dm 146) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 146) oGrid.kl oGrid.kr 400 800 ⟨false, 4930678869764482464770355782907152639279323251304588276881947505625703297764⟩ ⟨false, 0⟩ ⟨false, 5628209216316887642785987387279830735684529622180605471333778531427489276556⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_146_1200 : bothSeg evalE (oGrid.idx 146) (oGrid.dm 146) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 146) oGrid.kl oGrid.kr 400 1200 ⟨false, 5628209216316887642785987387279830735684529622180605471333778531427489276556⟩ ⟨false, 0⟩ ⟨false, 5728883040403135335977297355674927545249547561092492031856397673020545985948⟩ ⟨false, 6823593275805733361998284282908128526422944153461436929449903515018297676⟩ = true := by
  decide +kernel

theorem b_146_1600 : bothSeg evalE (oGrid.idx 146) (oGrid.dm 146) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 146) oGrid.kl oGrid.kr 400 1600 ⟨false, 5728883040403135335977297355674927545249547561092492031856397673020545985948⟩ ⟨false, 6823593275805733361998284282908128526422944153461436929449903515018297676⟩ ⟨false, 5548367508060668428304973930433701892048025776018517742145526017779932046726⟩ ⟨false, 187627806360979656649767407864450058169972451190373156395815866366972125866⟩ = true := by
  decide +kernel

theorem b_146_2000 : bothSeg evalE (oGrid.idx 146) (oGrid.dm 146) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 146) oGrid.kl oGrid.kr 400 2000 ⟨false, 5548367508060668428304973930433701892048025776018517742145526017779932046726⟩ ⟨false, 187627806360979656649767407864450058169972451190373156395815866366972125866⟩ ⟨false, 5502525376234587447670940973668737166155101672032004601603034988867587039618⟩ ⟨false, 234243254354380810359450820431625986657196939608581030394531626205341598540⟩ = true := by
  decide +kernel

theorem b_146_2400 : bothLoop evalE (oGrid.idx 146) (oGrid.dm 146) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 146) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5502525376234587447670940973668737166155101672032004601603034988867587039618⟩ ⟨false, 234243254354380810359450820431625986657196939608581030394531626205341598540⟩ = true := by
  decide +kernel

theorem o_row_146 : oGrid.row evalE 146 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_146_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_146_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_146_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_146_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_146_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_146_2000).1 (bothLoop_sound b_146_2400).1))))))

theorem n_row_146 : nGrid.row evalE 146 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_146_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_146_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_146_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_146_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_146_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_146_2000).2 (bothLoop_sound b_146_2400).2))))))

theorem b_147_0 : bothSeg evalE (oGrid.idx 147) (oGrid.dm 147) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 147) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3039172074791285704206406447830831079853024055295697935434076852991394429794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_147_400 : bothSeg evalE (oGrid.idx 147) (oGrid.dm 147) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 147) oGrid.kl oGrid.kr 400 400 ⟨false, 3039172074791285704206406447830831079853024055295697935434076852991394429794⟩ ⟨false, 0⟩ ⟨false, 4912085601920500612992765645405658564784471385147735897053528623878117725164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_147_800 : bothSeg evalE (oGrid.idx 147) (oGrid.dm 147) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 147) oGrid.kl oGrid.kr 400 800 ⟨false, 4912085601920500612992765645405658564784471385147735897053528623878117725164⟩ ⟨false, 0⟩ ⟨false, 5606790138402017534921553652335629990567901277841468879403763973843965725944⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_147_1200 : bothSeg evalE (oGrid.idx 147) (oGrid.dm 147) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 147) oGrid.kl oGrid.kr 400 1200 ⟨false, 5606790138402017534921553652335629990567901277841468879403763973843965725944⟩ ⟨false, 0⟩ ⟨false, 5706463208727873856583545124762937552910542528334647528143505005006375141452⟩ ⟨false, 7097386233757527480788536713788668432825760417832008019531610241762597418⟩ = true := by
  decide +kernel

theorem b_147_1600 : bothSeg evalE (oGrid.idx 147) (oGrid.dm 147) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 147) oGrid.kl oGrid.kr 400 1600 ⟨false, 5706463208727873856583545124762937552910542528334647528143505005006375141452⟩ ⟨false, 7097386233757527480788536713788668432825760417832008019531610241762597418⟩ ⟨false, 5526121620218683451615628717973761627533639140860797377752721519589037859708⟩ ⟨false, 187728581831364405343982069310167490408091974514326570000701651993281261752⟩ = true := by
  decide +kernel

theorem b_147_2000 : bothSeg evalE (oGrid.idx 147) (oGrid.dm 147) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 147) oGrid.kl oGrid.kr 400 2000 ⟨false, 5526121620218683451615628717973761627533639140860797377752721519589037859708⟩ ⟨false, 187728581831364405343982069310167490408091974514326570000701651993281261752⟩ ⟨false, 5480549536820121620349414106906083156683298238387778792027508983765570483554⟩ ⟨false, 234075556305370702966568413750626207492279400824304286925994768169730860922⟩ = true := by
  decide +kernel

theorem b_147_2400 : bothLoop evalE (oGrid.idx 147) (oGrid.dm 147) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 147) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5480549536820121620349414106906083156683298238387778792027508983765570483554⟩ ⟨false, 234075556305370702966568413750626207492279400824304286925994768169730860922⟩ = true := by
  decide +kernel

theorem o_row_147 : oGrid.row evalE 147 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_147_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_147_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_147_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_147_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_147_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_147_2000).1 (bothLoop_sound b_147_2400).1))))))

theorem n_row_147 : nGrid.row evalE 147 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_147_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_147_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_147_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_147_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_147_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_147_2000).2 (bothLoop_sound b_147_2400).2))))))

theorem b_148_0 : bothSeg evalE (oGrid.idx 148) (oGrid.dm 148) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 148) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3027650271235118897005153145676494869426011839731660133908116301318368927950⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_148_400 : bothSeg evalE (oGrid.idx 148) (oGrid.dm 148) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 148) oGrid.kl oGrid.kr 400 400 ⟨false, 3027650271235118897005153145676494869426011839731660133908116301318368927950⟩ ⟨false, 0⟩ ⟨false, 4893545765836848976727516963431129069166023975333470974756250336847992766178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_148_800 : bothSeg evalE (oGrid.idx 148) (oGrid.dm 148) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 148) oGrid.kl oGrid.kr 400 800 ⟨false, 4893545765836848976727516963431129069166023975333470974756250336847992766178⟩ ⟨false, 0⟩ ⟨false, 5585430877351334278876863923418217290335316937536576501880239643546670053018⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_148_1200 : bothSeg evalE (oGrid.idx 148) (oGrid.dm 148) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 148) oGrid.kl oGrid.kr 400 1200 ⟨false, 5585430877351334278876863923418217290335316937536576501880239643546670053018⟩ ⟨false, 0⟩ ⟨false, 5684100533513680752435004982745757399240374552245574284649076557738166856112⟩ ⟨false, 7376349054159482549880598697317501379592359972737901536532365079588501116⟩ = true := by
  decide +kernel

theorem b_148_1600 : bothSeg evalE (oGrid.idx 148) (oGrid.dm 148) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 148) oGrid.kl oGrid.kr 400 1600 ⟨false, 5684100533513680752435004982745757399240374552245574284649076557738166856112⟩ ⟨false, 7376349054159482549880598697317501379592359972737901536532365079588501116⟩ ⟨false, 5503939347425146214500265349699217959934635268567107025851332086909257629864⟩ ⟨false, 187828035649651396545154976515420561961431559094584161684532475466075011046⟩ = true := by
  decide +kernel

theorem b_148_2000 : bothSeg evalE (oGrid.idx 148) (oGrid.dm 148) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 148) oGrid.kl oGrid.kr 400 2000 ⟨false, 5503939347425146214500265349699217959934635268567107025851332086909257629864⟩ ⟨false, 187828035649651396545154976515420561961431559094584161684532475466075011046⟩ ⟨false, 5458635873611670998329646649015723364831224593151469694243151111598077139814⟩ ⟨false, 233908173549449241529092037859006783402929420444359796949036120613730746580⟩ = true := by
  decide +kernel

theorem b_148_2400 : bothLoop evalE (oGrid.idx 148) (oGrid.dm 148) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 148) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5458635873611670998329646649015723364831224593151469694243151111598077139814⟩ ⟨false, 233908173549449241529092037859006783402929420444359796949036120613730746580⟩ = true := by
  decide +kernel

theorem o_row_148 : oGrid.row evalE 148 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_148_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_148_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_148_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_148_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_148_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_148_2000).1 (bothLoop_sound b_148_2400).1))))))

theorem n_row_148 : nGrid.row evalE 148 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_148_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_148_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_148_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_148_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_148_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_148_2000).2 (bothLoop_sound b_148_2400).2))))))

theorem b_149_0 : bothSeg evalE (oGrid.idx 149) (oGrid.dm 149) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 149) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3016163182019335530235064396665452675812441545397261254967654901281982096790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_149_400 : bothSeg evalE (oGrid.idx 149) (oGrid.dm 149) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 149) oGrid.kl oGrid.kr 400 400 ⟨false, 3016163182019335530235064396665452675812441545397261254967654901281982096790⟩ ⟨false, 0⟩ ⟨false, 4875059129980282952016886495483895964234981458571542301049538710071372046612⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_149_800 : bothSeg evalE (oGrid.idx 149) (oGrid.dm 149) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 149) oGrid.kl oGrid.kr 400 800 ⟨false, 4875059129980282952016886495483895964234981458571542301049538710071372046612⟩ ⟨false, 0⟩ ⟨false, 5564131211958132442513821615833368866562396887040728353694154527379612040394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_149_1200 : bothSeg evalE (oGrid.idx 149) (oGrid.dm 149) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 149) oGrid.kl oGrid.kr 400 1200 ⟨false, 5564131211958132442513821615833368866562396887040728353694154527379612040394⟩ ⟨false, 0⟩ ⟨false, 5661794867338562926353636672131670558677440725114901583794117331566553750422⟩ ⟨false, 7660432700778002931634017770354899966715839596166858282312310772285313388⟩ = true := by
  decide +kernel

theorem b_149_1600 : bothSeg evalE (oGrid.idx 149) (oGrid.dm 149) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 149) oGrid.kl oGrid.kr 400 1600 ⟨false, 5661794867338562926353636672131670558677440725114901583794117331566553750422⟩ ⟨false, 7660432700778002931634017770354899966715839596166858282312310772285313388⟩ ⟨false, 5481820421826440529499616855984774029408064630368536670713199146007353875780⟩ ⟨false, 187926092734853007186953086020044908449523451423870474194013970191060756362⟩ = true := by
  decide +kernel

theorem b_149_2000 : bothSeg evalE (oGrid.idx 149) (oGrid.dm 149) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 149) oGrid.kl oGrid.kr 400 2000 ⟨false, 5481820421826440529499616855984774029408064630368536670713199146007353875780⟩ ⟨false, 187926092734853007186953086020044908449523451423870474194013970191060756362⟩ ⟨false, 5436784145933444907483252336309278779906408109841296691883517816752009421544⟩ ⟨false, 233740498559800192234009724918466027579493826749884570666670215325839082950⟩ = true := by
  decide +kernel

theorem b_149_2400 : bothLoop evalE (oGrid.idx 149) (oGrid.dm 149) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 149) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5436784145933444907483252336309278779906408109841296691883517816752009421544⟩ ⟨false, 233740498559800192234009724918466027579493826749884570666670215325839082950⟩ = true := by
  decide +kernel

theorem o_row_149 : oGrid.row evalE 149 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_149_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_149_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_149_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_149_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_149_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_149_2000).1 (bothLoop_sound b_149_2400).1))))))

theorem n_row_149 : nGrid.row evalE 149 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_149_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_149_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_149_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_149_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_149_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_149_2000).2 (bothLoop_sound b_149_2400).2))))))

theorem b_150_0 : bothSeg evalE (oGrid.idx 150) (oGrid.dm 150) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 150) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3004710714197445667670911135569815150079183921994240201992614910662485825712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_150_400 : bothSeg evalE (oGrid.idx 150) (oGrid.dm 150) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 150) oGrid.kl oGrid.kr 400 400 ⟨false, 3004710714197445667670911135569815150079183921994240201992614910662485825712⟩ ⟨false, 0⟩ ⟨false, 4856625578775515066210463699905429449806264917418898382157010102293021286066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_150_800 : bothSeg evalE (oGrid.idx 150) (oGrid.dm 150) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 150) oGrid.kl oGrid.kr 400 800 ⟨false, 4856625578775515066210463699905429449806264917418898382157010102293021286066⟩ ⟨false, 0⟩ ⟨false, 5542891028461732991604951097609581262944319712349162894409204238952949968692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_150_1200 : bothSeg evalE (oGrid.idx 150) (oGrid.dm 150) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 150) oGrid.kl oGrid.kr 400 1200 ⟨false, 5542891028461732991604951097609581262944319712349162894409204238952949968692⟩ ⟨false, 0⟩ ⟨false, 5639546295173172873125446697279464620186903595150370820714906428031628494980⟩ ⟨false, 7949461487788922440505723271532292388117764397763066239619173908264258258⟩ = true := by
  decide +kernel

theorem b_150_1600 : bothSeg evalE (oGrid.idx 150) (oGrid.dm 150) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 150) oGrid.kl oGrid.kr 400 1600 ⟨false, 5639546295173172873125446697279464620186903595150370820714906428031628494980⟩ ⟨false, 7949461487788922440505723271532292388117764397763066239619173908264258258⟩ ⟨false, 5459764649242371128520821303698550950115448435596377144837280699266854357358⟩ ⟨false, 188022898332631272026216988853926447593425993160960926547349037225102724294⟩ = true := by
  decide +kernel

theorem b_150_2000 : bothSeg evalE (oGrid.idx 150) (oGrid.dm 150) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 150) oGrid.kl oGrid.kr 400 2000 ⟨false, 5459764649242371128520821303698550950115448435596377144837280699266854357358⟩ ⟨false, 188022898332631272026216988853926447593425993160960926547349037225102724294⟩ ⟨false, 5414994203974309798494667405372096440079386374425363914332982619807679040458⟩ ⟨false, 233573319265715965930494953147709382315964360025099780992067935523877455550⟩ = true := by
  decide +kernel

theorem b_150_2400 : bothLoop evalE (oGrid.idx 150) (oGrid.dm 150) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 150) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5414994203974309798494667405372096440079386374425363914332982619807679040458⟩ ⟨false, 233573319265715965930494953147709382315964360025099780992067935523877455550⟩ = true := by
  decide +kernel

theorem o_row_150 : oGrid.row evalE 150 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_150_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_150_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_150_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_150_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_150_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_150_2000).1 (bothLoop_sound b_150_2400).1))))))

theorem n_row_150 : nGrid.row evalE 150 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_150_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_150_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_150_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_150_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_150_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_150_2000).2 (bothLoop_sound b_150_2400).2))))))

theorem b_151_0 : bothSeg evalE (oGrid.idx 151) (oGrid.dm 151) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 151) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2993292791717570561444187050733760215069815172532112440806985101559715035306⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_151_400 : bothSeg evalE (oGrid.idx 151) (oGrid.dm 151) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 151) oGrid.kl oGrid.kr 400 400 ⟨false, 2993292791717570561444187050733760215069815172532112440806985101559715035306⟩ ⟨false, 0⟩ ⟨false, 4838245004041936800373518605938726750649157946777971956740597517776182333360⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_151_800 : bothSeg evalE (oGrid.idx 151) (oGrid.dm 151) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 151) oGrid.kl oGrid.kr 400 800 ⟨false, 4838245004041936800373518605938726750649157946777971956740597517776182333360⟩ ⟨false, 0⟩ ⟨false, 5521710201568161044147235952903506330724483486600223911622113945708325840688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_151_1200 : bothSeg evalE (oGrid.idx 151) (oGrid.dm 151) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 151) oGrid.kl oGrid.kr 400 1200 ⟨false, 5521710201568161044147235952903506330724483486600223911622113945708325840688⟩ ⟨false, 0⟩ ⟨false, 5617354719359022157157346900766623787214182086917533548908777832331845835660⟩ ⟨false, 8243388155003881957398680498136470668758513026555391708049312172698265360⟩ = true := by
  decide +kernel

theorem b_151_1600 : bothSeg evalE (oGrid.idx 151) (oGrid.dm 151) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 151) oGrid.kl oGrid.kr 400 1600 ⟨false, 5617354719359022157157346900766623787214182086917533548908777832331845835660⟩ ⟨false, 8243388155003881957398680498136470668758513026555391708049312172698265360⟩ ⟨false, 5437771941366377739456539670736470372844293038534721506883765818410642456032⟩ ⟨false, 188118959644277319052174030178395222322142510694982230607096898052227562254⟩ = true := by
  decide +kernel

theorem b_151_2000 : bothSeg evalE (oGrid.idx 151) (oGrid.dm 151) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 151) oGrid.kl oGrid.kr 400 2000 ⟨false, 5437771941366377739456539670736470372844293038534721506883765818410642456032⟩ ⟨false, 188118959644277319052174030178395222322142510694982230607096898052227562254⟩ ⟨false, 5393265949623257048112262961110780357037430430056166126779815211597804205142⟩ ⟨false, 233406513083394980754191979579417832645789689095721508365050033407160198538⟩ = true := by
  decide +kernel

theorem b_151_2400 : bothLoop evalE (oGrid.idx 151) (oGrid.dm 151) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 151) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5393265949623257048112262961110780357037430430056166126779815211597804205142⟩ ⟨false, 233406513083394980754191979579417832645789689095721508365050033407160198538⟩ = true := by
  decide +kernel

theorem o_row_151 : oGrid.row evalE 151 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_151_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_151_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_151_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_151_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_151_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_151_2000).1 (bothLoop_sound b_151_2400).1))))))

theorem n_row_151 : nGrid.row evalE 151 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_151_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_151_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_151_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_151_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_151_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_151_2000).2 (bothLoop_sound b_151_2400).2))))))

theorem b_152_0 : bothSeg evalE (oGrid.idx 152) (oGrid.dm 152) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 152) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2981909319818265823957830089856750861026039263715300977979145408480066620842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_152_400 : bothSeg evalE (oGrid.idx 152) (oGrid.dm 152) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 152) oGrid.kl oGrid.kr 400 400 ⟨false, 2981909319818265823957830089856750861026039263715300977979145408480066620842⟩ ⟨false, 0⟩ ⟨false, 4819917305583768503467812827727158459737275502558447443289237272911217467692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_152_800 : bothSeg evalE (oGrid.idx 152) (oGrid.dm 152) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 152) oGrid.kl oGrid.kr 400 800 ⟨false, 4819917305583768503467812827727158459737275502558447443289237272911217467692⟩ ⟨false, 0⟩ ⟨false, 5500588635554660142058919798532753843098889031017479357740312950615776258066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_152_1200 : bothSeg evalE (oGrid.idx 152) (oGrid.dm 152) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 152) oGrid.kl oGrid.kr 400 1200 ⟨false, 5500588635554660142058919798532753843098889031017479357740312950615776258066⟩ ⟨false, 0⟩ ⟨false, 5595220172911916347311351126212137019093080373566361403298451037894795501240⟩ ⟨false, 8542071371599515635027161305653366739701581101069116871260067433582527208⟩ = true := by
  decide +kernel

theorem b_152_1600 : bothSeg evalE (oGrid.idx 152) (oGrid.dm 152) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 152) oGrid.kl oGrid.kr 400 1600 ⟨false, 5595220172911916347311351126212137019093080373566361403298451037894795501240⟩ ⟨false, 8542071371599515635027161305653366739701581101069116871260067433582527208⟩ ⟨false, 5415842155802039156250525745332937785361170797508230976218234959046987724302⟩ ⟨false, 188213680159101815899768169345814749141026916574413640465975913105347834772⟩ = true := by
  decide +kernel

theorem b_152_2000 : bothSeg evalE (oGrid.idx 152) (oGrid.dm 152) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 152) oGrid.kl oGrid.kr 400 2000 ⟨false, 5415842155802039156250525745332937785361170797508230976218234959046987724302⟩ ⟨false, 188213680159101815899768169345814749141026916574413640465975913105347834772⟩ ⟨false, 5371599281583815326645499678672069999062298974704401613488114910591232620772⟩ ⟨false, 233239805073600763485690536880458062939919637646980858958161373465612309884⟩ = true := by
  decide +kernel

theorem b_152_2400 : bothLoop evalE (oGrid.idx 152) (oGrid.dm 152) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 152) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5371599281583815326645499678672069999062298974704401613488114910591232620772⟩ ⟨false, 233239805073600763485690536880458062939919637646980858958161373465612309884⟩ = true := by
  decide +kernel

theorem o_row_152 : oGrid.row evalE 152 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_152_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_152_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_152_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_152_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_152_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_152_2000).1 (bothLoop_sound b_152_2400).1))))))

theorem n_row_152 : nGrid.row evalE 152 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_152_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_152_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_152_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_152_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_152_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_152_2000).2 (bothLoop_sound b_152_2400).2))))))

theorem b_153_0 : bothSeg evalE (oGrid.idx 153) (oGrid.dm 153) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 153) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2970560202920564198075041972785336500745361168965006770254097417685888586946⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_153_400 : bothSeg evalE (oGrid.idx 153) (oGrid.dm 153) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 153) oGrid.kl oGrid.kr 400 400 ⟨false, 2970560202920564198075041972785336500745361168965006770254097417685888586946⟩ ⟨false, 0⟩ ⟨false, 4801642371194749041046713977402521190220214188921895641711931909174827306466⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_153_800 : bothSeg evalE (oGrid.idx 153) (oGrid.dm 153) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 153) oGrid.kl oGrid.kr 400 800 ⟨false, 4801642371194749041046713977402521190220214188921895641711931909174827306466⟩ ⟨false, 0⟩ ⟨false, 5479526220969863397091927472315590734120103913320481119628881726197227095986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_153_1200 : bothSeg evalE (oGrid.idx 153) (oGrid.dm 153) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 153) oGrid.kl oGrid.kr 400 1200 ⟨false, 5479526220969863397091927472315590734120103913320481119628881726197227095986⟩ ⟨false, 0⟩ ⟨false, 5573142651465347304602839363537589645289589892467475870732239617324128284974⟩ ⟨false, 8845557225335515174811616379092459149408708919557394986680029839420151070⟩ = true := by
  decide +kernel

theorem b_153_1600 : bothSeg evalE (oGrid.idx 153) (oGrid.dm 153) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 153) oGrid.kl oGrid.kr 400 1600 ⟨false, 5573142651465347304602839363537589645289589892467475870732239617324128284974⟩ ⟨false, 8845557225335515174811616379092459149408708919557394986680029839420151070⟩ ⟨false, 5393975153671829325585189912763966296734873077440168705887425363790149054782⟩ ⟨false, 188307272870677880434026236286643445698782579117255735321334126306921583512⟩ = true := by
  decide +kernel

theorem b_153_2000 : bothSeg evalE (oGrid.idx 153) (oGrid.dm 153) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 153) oGrid.kl oGrid.kr 400 2000 ⟨false, 5393975153671829325585189912763966296734873077440168705887425363790149054782⟩ ⟨false, 188307272870677880434026236286643445698782579117255735321334126306921583512⟩ ⟨false, 5349994108085613330811831662815636981057194132750936757062064782950660984864⟩ ⟨false, 233073279717874738850630060304303643130392620518465897096078916616653452352⟩ = true := by
  decide +kernel

theorem b_153_2400 : bothLoop evalE (oGrid.idx 153) (oGrid.dm 153) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 153) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5349994108085613330811831662815636981057194132750936757062064782950660984864⟩ ⟨false, 233073279717874738850630060304303643130392620518465897096078916616653452352⟩ = true := by
  decide +kernel

theorem o_row_153 : oGrid.row evalE 153 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_153_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_153_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_153_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_153_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_153_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_153_2000).1 (bothLoop_sound b_153_2400).1))))))

theorem n_row_153 : nGrid.row evalE 153 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_153_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_153_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_153_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_153_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_153_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_153_2000).2 (bothLoop_sound b_153_2400).2))))))

theorem b_154_0 : bothSeg evalE (oGrid.idx 154) (oGrid.dm 154) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 154) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2959245364069902344012320401520499296850988129395010628602561994522260923982⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_154_400 : bothSeg evalE (oGrid.idx 154) (oGrid.dm 154) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 154) oGrid.kl oGrid.kr 400 400 ⟨false, 2959245364069902344012320401520499296850988129395010628602561994522260923982⟩ ⟨false, 0⟩ ⟨false, 4783420038219734146266957253032845367391224463143760672163078721833714218832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_154_800 : bothSeg evalE (oGrid.idx 154) (oGrid.dm 154) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 154) oGrid.kl oGrid.kr 400 800 ⟨false, 4783420038219734146266957253032845367391224463143760672163078721833714218832⟩ ⟨false, 0⟩ ⟨false, 5458522789844705521803178802908348257228496049044215157596486219936705917364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_154_1200 : bothSeg evalE (oGrid.idx 154) (oGrid.dm 154) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 154) oGrid.kl oGrid.kr 400 1200 ⟨false, 5458522789844705521803178802908348257228496049044215157596486219936705917364⟩ ⟨false, 0⟩ ⟨false, 5551122131952555658257918530767736754740681319323953375156323455767123778640⟩ ⟨false, 9153663842320647129196885273729053580984333925641746305336352772154676470⟩ = true := by
  decide +kernel

theorem b_154_1600 : bothSeg evalE (oGrid.idx 154) (oGrid.dm 154) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 154) oGrid.kl oGrid.kr 400 1600 ⟨false, 5551122131952555658257918530767736754740681319323953375156323455767123778640⟩ ⟨false, 9153663842320647129196885273729053580984333925641746305336352772154676470⟩ ⟨false, 5372170992433294612794515529839569378064193938403987543667075616626011074164⟩ ⟨false, 188399774661284640953867629351461737605963245783434897807296558375361173964⟩ = true := by
  decide +kernel

theorem b_154_2000 : bothSeg evalE (oGrid.idx 154) (oGrid.dm 154) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 154) oGrid.kl oGrid.kr 400 2000 ⟨false, 5372170992433294612794515529839569378064193938403987543667075616626011074164⟩ ⟨false, 188399774661284640953867629351461737605963245783434897807296558375361173964⟩ ⟨false, 5328450506694391417818468439705090029039913906047044035701392333063586040200⟩ ⟨false, 232906865102203982055192041529649950747431952568087930832227486408386445650⟩ = true := by
  decide +kernel

theorem b_154_2400 : bothLoop evalE (oGrid.idx 154) (oGrid.dm 154) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 154) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5328450506694391417818468439705090029039913906047044035701392333063586040200⟩ ⟨false, 232906865102203982055192041529649950747431952568087930832227486408386445650⟩ = true := by
  decide +kernel

theorem o_row_154 : oGrid.row evalE 154 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_154_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_154_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_154_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_154_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_154_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_154_2000).1 (bothLoop_sound b_154_2400).1))))))

theorem n_row_154 : nGrid.row evalE 154 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_154_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_154_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_154_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_154_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_154_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_154_2000).2 (bothLoop_sound b_154_2400).2))))))

theorem b_155_0 : bothSeg evalE (oGrid.idx 155) (oGrid.dm 155) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 155) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2947964667240849972182434457256714985245794075334615073165360514818037754680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_155_400 : bothSeg evalE (oGrid.idx 155) (oGrid.dm 155) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 155) oGrid.kl oGrid.kr 400 400 ⟨false, 2947964667240849972182434457256714985245794075334615073165360514818037754680⟩ ⟨false, 0⟩ ⟨false, 4765250157752354711328368883498379459352836169270788477947521343781666646744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_155_800 : bothSeg evalE (oGrid.idx 155) (oGrid.dm 155) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 155) oGrid.kl oGrid.kr 400 800 ⟨false, 4765250157752354711328368883498379459352836169270788477947521343781666646744⟩ ⟨false, 0⟩ ⟨false, 5437578180361052034525983860288307135750103856947378224019280550216495525930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_155_1200 : bothSeg evalE (oGrid.idx 155) (oGrid.dm 155) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 155) oGrid.kl oGrid.kr 400 1200 ⟨false, 5437578180361052034525983860288307135750103856947378224019280550216495525930⟩ ⟨false, 0⟩ ⟨false, 5529158551502147425652769178341368920459172711643821773964408688566689171244⟩ ⟨false, 9466172360281610605478424808940074338481437469765365806896903666866478666⟩ = true := by
  decide +kernel

theorem b_155_1600 : bothSeg evalE (oGrid.idx 155) (oGrid.dm 155) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 155) oGrid.kl oGrid.kr 400 1600 ⟨false, 5529158551502147425652769178341368920459172711643821773964408688566689171244⟩ ⟨false, 9466172360281610605478424808940074338481437469765365806896903666866478666⟩ ⟨false, 5350429185703921254937964831735547736733465637021348054456224928984120626132⟩ ⟨false, 188491277363734343638685199384703701697326518041331337122657030499878220822⟩ = true := by
  decide +kernel

theorem b_155_2000 : bothSeg evalE (oGrid.idx 155) (oGrid.dm 155) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 155) oGrid.kl oGrid.kr 400 2000 ⟨false, 5350429185703921254937964831735547736733465637021348054456224928984120626132⟩ ⟨false, 188491277363734343638685199384703701697326518041331337122657030499878220822⟩ ⟨false, 5306968007790591704258906793549779648997732816667547187708033036401706610176⟩ ⟨false, 232740774814062366808018489147771476148246414756086995458256315219879412944⟩ = true := by
  decide +kernel

theorem b_155_2400 : bothLoop evalE (oGrid.idx 155) (oGrid.dm 155) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 155) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5306968007790591704258906793549779648997732816667547187708033036401706610176⟩ ⟨false, 232740774814062366808018489147771476148246414756086995458256315219879412944⟩ = true := by
  decide +kernel

theorem o_row_155 : oGrid.row evalE 155 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_155_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_155_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_155_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_155_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_155_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_155_2000).1 (bothLoop_sound b_155_2400).1))))))

theorem n_row_155 : nGrid.row evalE 155 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_155_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_155_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_155_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_155_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_155_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_155_2000).2 (bothLoop_sound b_155_2400).2))))))

theorem b_156_0 : bothSeg evalE (oGrid.idx 156) (oGrid.dm 156) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 156) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2936718070050867055190418463099103379739434422476918399679138854842291732890⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_156_400 : bothSeg evalE (oGrid.idx 156) (oGrid.dm 156) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 156) oGrid.kl oGrid.kr 400 400 ⟨false, 2936718070050867055190418463099103379739434422476918399679138854842291732890⟩ ⟨false, 0⟩ ⟨false, 4747132678426400220325248021270558139997940816052700198755831584983577920918⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_156_800 : bothSeg evalE (oGrid.idx 156) (oGrid.dm 156) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 156) oGrid.kl oGrid.kr 400 800 ⟨false, 4747132678426400220325248021270558139997940816052700198755831584983577920918⟩ ⟨false, 0⟩ ⟨false, 5416692376533292820673749847579530613237676296639763533902736071467749563002⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_156_1200 : bothSeg evalE (oGrid.idx 156) (oGrid.dm 156) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 156) oGrid.kl oGrid.kr 400 1200 ⟨false, 5416692376533292820673749847579530613237676296639763533902736071467749563002⟩ ⟨false, 0⟩ ⟨false, 5507252032236499512245925773271083531967653425874474132341904284946824880530⟩ ⟨false, 9782949910607547965749474474951079611634362143793257132098933065649250990⟩ = true := by
  decide +kernel

theorem b_156_1600 : bothSeg evalE (oGrid.idx 156) (oGrid.dm 156) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 156) oGrid.kl oGrid.kr 400 1600 ⟨false, 5507252032236499512245925773271083531967653425874474132341904284946824880530⟩ ⟨false, 9782949910607547965749474474951079611634362143793257132098933065649250990⟩ ⟨false, 5328749881553295594903579114260461899504375531988048450729161310826333879054⟩ ⟨false, 188581616274873649816027603174384978810904444692466413311455519372985382120⟩ = true := by
  decide +kernel

theorem b_156_2000 : bothSeg evalE (oGrid.idx 156) (oGrid.dm 156) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 156) oGrid.kl oGrid.kr 400 2000 ⟨false, 5328749881553295594903579114260461899504375531988048450729161310826333879054⟩ ⟨false, 188581616274873649816027603174384978810904444692466413311455519372985382120⟩ ⟨false, 5285546810412715459845953900270742353781053204804207993354190986268235100086⟩ ⟨false, 232574604253376797722531795172637859717013373273159355120666484366077843898⟩ = true := by
  decide +kernel

theorem b_156_2400 : bothLoop evalE (oGrid.idx 156) (oGrid.dm 156) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 156) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5285546810412715459845953900270742353781053204804207993354190986268235100086⟩ ⟨false, 232574604253376797722531795172637859717013373273159355120666484366077843898⟩ = true := by
  decide +kernel

theorem o_row_156 : oGrid.row evalE 156 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_156_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_156_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_156_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_156_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_156_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_156_2000).1 (bothLoop_sound b_156_2400).1))))))

theorem n_row_156 : nGrid.row evalE 156 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_156_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_156_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_156_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_156_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_156_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_156_2000).2 (bothLoop_sound b_156_2400).2))))))

theorem b_157_0 : bothSeg evalE (oGrid.idx 157) (oGrid.dm 157) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 157) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2925505433738808957863264952442986653728336194911219761560165881699806698908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_157_400 : bothSeg evalE (oGrid.idx 157) (oGrid.dm 157) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 157) oGrid.kl oGrid.kr 400 400 ⟨false, 2925505433738808957863264952442986653728336194911219761560165881699806698908⟩ ⟨false, 0⟩ ⟨false, 4729067406204810224606029091307976445434482993079657098673300063403300400154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_157_800 : bothSeg evalE (oGrid.idx 157) (oGrid.dm 157) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 157) oGrid.kl oGrid.kr 400 800 ⟨false, 4729067406204810224606029091307976445434482993079657098673300063403300400154⟩ ⟨false, 0⟩ ⟨false, 5395865139675824888923218305671136195386084941599831590317822640262596616834⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_157_1200 : bothSeg evalE (oGrid.idx 157) (oGrid.dm 157) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 157) oGrid.kl oGrid.kr 400 1200 ⟨false, 5395865139675824888923218305671136195386084941599831590317822640262596616834⟩ ⟨false, 0⟩ ⟨false, 5485402431260105314216102368768215561339314249173438557970747011450189847310⟩ ⟨false, 10103920685723443659945832734418903912856931613637521192988649292016471272⟩ = true := by
  decide +kernel

theorem b_157_1600 : bothSeg evalE (oGrid.idx 157) (oGrid.dm 157) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 157) oGrid.kl oGrid.kr 400 1600 ⟨false, 5485402431260105314216102368768215561339314249173438557970747011450189847310⟩ ⟨false, 10103920685723443659945832734418903912856931613637521192988649292016471272⟩ ⟨false, 5307132742177048003175669904478656514947400350947048537532174406581618847446⟩ ⟨false, 188671183092468434432425223377993583459726039052774706397296657531085530734⟩ = true := by
  decide +kernel

theorem b_157_2000 : bothSeg evalE (oGrid.idx 157) (oGrid.dm 157) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 157) oGrid.kl oGrid.kr 400 2000 ⟨false, 5307132742177048003175669904478656514947400350947048537532174406581618847446⟩ ⟨false, 188671183092468434432425223377993583459726039052774706397296657531085530734⟩ ⟨false, 5264186593572858647107580706928621189340246768525180688222727144861410831506⟩ ⟨false, 232409048711051563495898831337846781414520633935071077722820824860913494498⟩ = true := by
  decide +kernel

theorem b_157_2400 : bothLoop evalE (oGrid.idx 157) (oGrid.dm 157) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 157) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5264186593572858647107580706928621189340246768525180688222727144861410831506⟩ ⟨false, 232409048711051563495898831337846781414520633935071077722820824860913494498⟩ = true := by
  decide +kernel

theorem o_row_157 : oGrid.row evalE 157 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_157_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_157_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_157_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_157_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_157_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_157_2000).1 (bothLoop_sound b_157_2400).1))))))

theorem n_row_157 : nGrid.row evalE 157 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_157_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_157_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_157_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_157_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_157_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_157_2000).2 (bothLoop_sound b_157_2400).2))))))

theorem b_158_0 : bothSeg evalE (oGrid.idx 158) (oGrid.dm 158) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 158) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2914326708377151151426183995547171410210234705906754802563263226874898079282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_158_400 : bothSeg evalE (oGrid.idx 158) (oGrid.dm 158) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 158) oGrid.kl oGrid.kr 400 400 ⟨false, 2914326708377151151426183995547171410210234705906754802563263226874898079282⟩ ⟨false, 0⟩ ⟨false, 4711054281213485782327582883620329174906395703395708853684084568728548893100⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_158_800 : bothSeg evalE (oGrid.idx 158) (oGrid.dm 158) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 158) oGrid.kl oGrid.kr 400 800 ⟨false, 4711054281213485782327582883620329174906395703395708853684084568728548893100⟩ ⟨false, 0⟩ ⟨false, 5375096415173086312931916950878232325288039949935190251733760950753673097538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_158_1200 : bothSeg evalE (oGrid.idx 158) (oGrid.dm 158) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 158) oGrid.kl oGrid.kr 400 1200 ⟨false, 5375096415173086312931916950878232325288039949935190251733760950753673097538⟩ ⟨false, 0⟩ ⟨false, 5463609885207755392339097616326259621299106660743185633406690426430633092186⟩ ⟨false, 10428880946075230779953318830304183945102006812964975518260765159187395740⟩ = true := by
  decide +kernel

theorem b_158_1600 : bothSeg evalE (oGrid.idx 158) (oGrid.dm 158) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 158) oGrid.kl oGrid.kr 400 1600 ⟨false, 5463609885207755392339097616326259621299106660743185633406690426430633092186⟩ ⟨false, 10428880946075230779953318830304183945102006812964975518260765159187395740⟩ ⟨false, 5285577872057050926327908900948814533696882376222942165783738512738199476040⟩ ⟨false, 188759397647710056128270928633358575769635664685871966669586977396612626570⟩ = true := by
  decide +kernel

theorem b_158_2000 : bothSeg evalE (oGrid.idx 158) (oGrid.dm 158) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 158) oGrid.kl oGrid.kr 400 2000 ⟨false, 5285577872057050926327908900948814533696882376222942165783738512738199476040⟩ ⟨false, 188759397647710056128270928633358575769635664685871966669586977396612626570⟩ ⟨false, 5242887492491043930656391684281461171922332679096063649045883644439861198292⟩ ⟨false, 232243076326889258388838737421411968792937055740457813581910660138519917458⟩ = true := by
  decide +kernel

theorem b_158_2400 : bothLoop evalE (oGrid.idx 158) (oGrid.dm 158) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 158) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5242887492491043930656391684281461171922332679096063649045883644439861198292⟩ ⟨false, 232243076326889258388838737421411968792937055740457813581910660138519917458⟩ = true := by
  decide +kernel

theorem o_row_158 : oGrid.row evalE 158 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_158_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_158_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_158_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_158_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_158_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_158_2000).1 (bothLoop_sound b_158_2400).1))))))

theorem n_row_158 : nGrid.row evalE 158 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_158_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_158_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_158_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_158_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_158_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_158_2000).2 (bothLoop_sound b_158_2400).2))))))

theorem b_159_0 : bothSeg evalE (oGrid.idx 159) (oGrid.dm 159) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 159) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2903181808672710905305440638954106570794463395175006670120413333325396802896⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_159_400 : bothSeg evalE (oGrid.idx 159) (oGrid.dm 159) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 159) oGrid.kl oGrid.kr 400 400 ⟨false, 2903181808672710905305440638954106570794463395175006670120413333325396802896⟩ ⟨false, 0⟩ ⟨false, 4693093161402669085997499215745632414216263356819370304077484375439420576542⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_159_800 : bothSeg evalE (oGrid.idx 159) (oGrid.dm 159) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 159) oGrid.kl oGrid.kr 400 800 ⟨false, 4693093161402669085997499215745632414216263356819370304077484375439420576542⟩ ⟨false, 0⟩ ⟨false, 5354386090198494507932451772004665162109394775570688745489490847886449499440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_159_1200 : bothSeg evalE (oGrid.idx 159) (oGrid.dm 159) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 159) oGrid.kl oGrid.kr 400 1200 ⟨false, 5354386090198494507932451772004665162109394775570688745489490847886449499440⟩ ⟨false, 0⟩ ⟨false, 5441874440928873683239730789940816421025080701987509378838450091032743599102⟩ ⟨false, 10757704235700994470198019804533079456508550844918990089983901511869359308⟩ = true := by
  decide +kernel

theorem b_159_1600 : bothSeg evalE (oGrid.idx 159) (oGrid.dm 159) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 159) oGrid.kl oGrid.kr 400 1600 ⟨false, 5441874440928873683239730789940816421025080701987509378838450091032743599102⟩ ⟨false, 10757704235700994470198019804533079456508550844918990089983901511869359308⟩ ⟨false, 5264085038079995454182391536382775318624360391852132676293160351508706004144⟩ ⟨false, 188846347534965998670781084105138644306696440507452752157520846297995066080⟩ = true := by
  decide +kernel

theorem b_159_2000 : bothSeg evalE (oGrid.idx 159) (oGrid.dm 159) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 159) oGrid.kl oGrid.kr 400 2000 ⟨false, 5264085038079995454182391536382775318624360391852132676293160351508706004144⟩ ⟨false, 188846347534965998670781084105138644306696440507452752157520846297995066080⟩ ⟨false, 5221649316667223501097833316763421245555771434387496464957583072713370717110⟩ ⟨false, 232077186563716032294018858252478654405572417636839181195851142870399888254⟩ = true := by
  decide +kernel

theorem b_159_2400 : bothLoop evalE (oGrid.idx 159) (oGrid.dm 159) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 159) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5221649316667223501097833316763421245555771434387496464957583072713370717110⟩ ⟨false, 232077186563716032294018858252478654405572417636839181195851142870399888254⟩ = true := by
  decide +kernel

theorem o_row_159 : oGrid.row evalE 159 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_159_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_159_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_159_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_159_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_159_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_159_2000).1 (bothLoop_sound b_159_2400).1))))))

theorem n_row_159 : nGrid.row evalE 159 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_159_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_159_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_159_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_159_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_159_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_159_2000).2 (bothLoop_sound b_159_2400).2))))))

theorem b_160_0 : bothSeg evalE (oGrid.idx 160) (oGrid.dm 160) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 160) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2892070658578243034621222018525076654469088883274572967399156344501901829320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_160_400 : bothSeg evalE (oGrid.idx 160) (oGrid.dm 160) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 160) oGrid.kl oGrid.kr 400 400 ⟨false, 2892070658578243034621222018525076654469088883274572967399156344501901829320⟩ ⟨false, 0⟩ ⟨false, 4675183947380551512262566524516770575241837075125204294581331664772952454910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_160_800 : bothSeg evalE (oGrid.idx 160) (oGrid.dm 160) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 160) oGrid.kl oGrid.kr 400 800 ⟨false, 4675183947380551512262566524516770575241837075125204294581331664772952454910⟩ ⟨false, 0⟩ ⟨false, 5333734031784345813810148393522300608982331185765078768630227062440351541294⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_160_1200 : bothSeg evalE (oGrid.idx 160) (oGrid.dm 160) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 160) oGrid.kl oGrid.kr 400 1200 ⟨false, 5333734031784345813810148393522300608982331185765078768630227062440351541294⟩ ⟨false, 0⟩ ⟨false, 5420196050604313740944801417217596934485930638585296958215908836656713028334⟩ ⟨false, 11090283946728172854854068081532709309079653529926789824972902764248608824⟩ = true := by
  decide +kernel

theorem b_160_1600 : bothSeg evalE (oGrid.idx 160) (oGrid.dm 160) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 160) oGrid.kl oGrid.kr 400 1600 ⟨false, 5420196050604313740944801417217596934485930638585296958215908836656713028334⟩ ⟨false, 11090283946728172854854068081532709309079653529926789824972902764248608824⟩ ⟨false, 5242654189514938462794197675025272787122337048589456944200098948621254249726⟩ ⟨false, 188931975887769899213761709448518416745603109612797441271532055910704478598⟩ = true := by
  decide +kernel

theorem b_160_2000 : bothSeg evalE (oGrid.idx 160) (oGrid.dm 160) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 160) oGrid.kl oGrid.kr 400 2000 ⟨false, 5242654189514938462794197675025272787122337048589456944200098948621254249726⟩ ⟨false, 188931975887769899213761709448518416745603109612797441271532055910704478598⟩ ⟨false, 5200471988187063051917767369672350931604535099148110833332932840071886151610⟩ ⟨false, 231910923192780169852492775299607512796628693241092964804990812743634280730⟩ = true := by
  decide +kernel

theorem b_160_2400 : bothLoop evalE (oGrid.idx 160) (oGrid.dm 160) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 160) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5200471988187063051917767369672350931604535099148110833332932840071886151610⟩ ⟨false, 231910923192780169852492775299607512796628693241092964804990812743634280730⟩ = true := by
  decide +kernel

theorem o_row_160 : oGrid.row evalE 160 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_160_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_160_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_160_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_160_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_160_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_160_2000).1 (bothLoop_sound b_160_2400).1))))))

theorem n_row_160 : nGrid.row evalE 160 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_160_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_160_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_160_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_160_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_160_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_160_2000).2 (bothLoop_sound b_160_2400).2))))))

theorem b_161_0 : bothSeg evalE (oGrid.idx 161) (oGrid.dm 161) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 161) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2880993118376984379239575702838779259438786418399110813280629999307703266976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_161_400 : bothSeg evalE (oGrid.idx 161) (oGrid.dm 161) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 161) oGrid.kl oGrid.kr 400 400 ⟨false, 2880993118376984379239575702838779259438786418399110813280629999307703266976⟩ ⟨false, 0⟩ ⟨false, 4657326465694590076922414415815375111714119833753837785103377933832840680432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_161_800 : bothSeg evalE (oGrid.idx 161) (oGrid.dm 161) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 161) oGrid.kl oGrid.kr 400 800 ⟨false, 4657326465694590076922414415815375111714119833753837785103377933832840680432⟩ ⟨false, 0⟩ ⟨false, 5313140063579258924867028583897981096446839534404187115271281511895913588748⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_161_1200 : bothSeg evalE (oGrid.idx 161) (oGrid.dm 161) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 161) oGrid.kl oGrid.kr 400 1200 ⟨false, 5313140063579258924867028583897981096446839534404187115271281511895913588748⟩ ⟨false, 0⟩ ⟨false, 5398574764571792847234283632062819044761899158252255652706327049389424542876⟩ ⟨false, 11426402733999821801244687190197616665828408427606159631063661506798109810⟩ = true := by
  decide +kernel

theorem b_161_1600 : bothSeg evalE (oGrid.idx 161) (oGrid.dm 161) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 161) oGrid.kl oGrid.kr 400 1600 ⟨false, 5398574764571792847234283632062819044761899158252255652706327049389424542876⟩ ⟨false, 11426402733999821801244687190197616665828408427606159631063661506798109810⟩ ⟨false, 5221284962503114133512308299993317962820642244475653417887919746447776178864⟩ ⟨false, 189016449951938601140556598502127002627077085038924166192724924529622341922⟩ = true := by
  decide +kernel

theorem b_161_2000 : bothSeg evalE (oGrid.idx 161) (oGrid.dm 161) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 161) oGrid.kl oGrid.kr 400 2000 ⟨false, 5221284962503114133512308299993317962820642244475653417887919746447776178864⟩ ⟨false, 189016449951938601140556598502127002627077085038924166192724924529622341922⟩ ⟨false, 5179355243936140512225013186040282801275324900729844566973074126038798789084⟩ ⟨false, 231744642109860045601879724009786553172465530605321357822662501740196596562⟩ = true := by
  decide +kernel

theorem b_161_2400 : bothLoop evalE (oGrid.idx 161) (oGrid.dm 161) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 161) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5179355243936140512225013186040282801275324900729844566973074126038798789084⟩ ⟨false, 231744642109860045601879724009786553172465530605321357822662501740196596562⟩ = true := by
  decide +kernel

theorem o_row_161 : oGrid.row evalE 161 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_161_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_161_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_161_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_161_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_161_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_161_2000).1 (bothLoop_sound b_161_2400).1))))))

theorem n_row_161 : nGrid.row evalE 161 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_161_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_161_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_161_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_161_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_161_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_161_2000).2 (bothLoop_sound b_161_2400).2))))))

theorem b_162_0 : bothSeg evalE (oGrid.idx 162) (oGrid.dm 162) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 162) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2869949072402851453567113792997726936542742545363951253486212470523456644646⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_162_400 : bothSeg evalE (oGrid.idx 162) (oGrid.dm 162) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 162) oGrid.kl oGrid.kr 400 400 ⟨false, 2869949072402851453567113792997726936542742545363951253486212470523456644646⟩ ⟨false, 0⟩ ⟨false, 4639520604736684854647592293631875744432939624227244118322111665935206165198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_162_800 : bothSeg evalE (oGrid.idx 162) (oGrid.dm 162) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 162) oGrid.kl oGrid.kr 400 800 ⟨false, 4639520604736684854647592293631875744432939624227244118322111665935206165198⟩ ⟨false, 0⟩ ⟨false, 5292604103073787411280759098499423305148489348885218030124514165435225185118⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_162_1200 : bothSeg evalE (oGrid.idx 162) (oGrid.dm 162) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 162) oGrid.kl oGrid.kr 400 1200 ⟨false, 5292604103073787411280759098499423305148489348885218030124514165435225185118⟩ ⟨false, 0⟩ ⟨false, 5377010615028839321635325213119315601136843398300123615401798359584863388006⟩ ⟨false, 11765944218063164192785597634393735563044009268232226247287523602844092496⟩ = true := by
  decide +kernel

theorem b_162_1600 : bothSeg evalE (oGrid.idx 162) (oGrid.dm 162) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 162) oGrid.kl oGrid.kr 400 1600 ⟨false, 5377010615028839321635325213119315601136843398300123615401798359584863388006⟩ ⟨false, 11765944218063164192785597634393735563044009268232226247287523602844092496⟩ ⟨false, 5199977518197114505979032414706430282710041292506925294047609204647284135464⟩ ⟨false, 189100195975326019660995028429504543908255083536789194939791495024092685738⟩ = true := by
  decide +kernel

theorem b_162_2000 : bothSeg evalE (oGrid.idx 162) (oGrid.dm 162) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 162) oGrid.kl oGrid.kr 400 2000 ⟨false, 5199977518197114505979032414706430282710041292506925294047609204647284135464⟩ ⟨false, 189100195975326019660995028429504543908255083536789194939791495024092685738⟩ ⟨false, 5158299239526738269358678122509060415162340389181915460722525574494787538836⟩ ⟨false, 231578704796244587062708711089971741854689329579873500218202756014674932322⟩ = true := by
  decide +kernel

theorem b_162_2400 : bothLoop evalE (oGrid.idx 162) (oGrid.dm 162) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 162) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5158299239526738269358678122509060415162340389181915460722525574494787538836⟩ ⟨false, 231578704796244587062708711089971741854689329579873500218202756014674932322⟩ = true := by
  decide +kernel

theorem o_row_162 : oGrid.row evalE 162 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_162_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_162_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_162_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_162_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_162_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_162_2000).1 (bothLoop_sound b_162_2400).1))))))

theorem n_row_162 : nGrid.row evalE 162 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_162_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_162_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_162_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_162_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_162_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_162_2000).2 (bothLoop_sound b_162_2400).2))))))

theorem b_163_0 : bothSeg evalE (oGrid.idx 163) (oGrid.dm 163) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 163) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2858938502754507365269706113824521449091307536624136374013021752675729619034⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_163_400 : bothSeg evalE (oGrid.idx 163) (oGrid.dm 163) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 163) oGrid.kl oGrid.kr 400 400 ⟨false, 2858938502754507365269706113824521449091307536624136374013021752675729619034⟩ ⟨false, 0⟩ ⟨false, 4621766266380980614016803384600497071131707682380285574440897273502935862412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_163_800 : bothSeg evalE (oGrid.idx 163) (oGrid.dm 163) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 163) oGrid.kl oGrid.kr 400 800 ⟨false, 4621766266380980614016803384600497071131707682380285574440897273502935862412⟩ ⟨false, 0⟩ ⟨false, 5272126014804413542528494444423538447512087697177890887038272318296996250668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_163_1200 : bothSeg evalE (oGrid.idx 163) (oGrid.dm 163) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 163) oGrid.kl oGrid.kr 400 1200 ⟨false, 5272126014804413542528494444423538447512087697177890887038272318296996250668⟩ ⟨false, 0⟩ ⟨false, 5355503598170651781799312248169234164659396449907254266469284132293922005952⟩ ⟨false, 12108758478008246083493710189700791880188878341087345605658064812848325688⟩ = true := by
  decide +kernel

theorem b_163_1600 : bothSeg evalE (oGrid.idx 163) (oGrid.dm 163) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 163) oGrid.kl oGrid.kr 400 1600 ⟨false, 5355503598170651781799312248169234164659396449907254266469284132293922005952⟩ ⟨false, 12108758478008246083493710189700791880188878341087345605658064812848325688⟩ ⟨false, 5178731524045470167693055410869311390731195116424222731313137005927545930008⟩ ⟨false, 189183124998383044022120374055372445651899411122700843071501461019260334142⟩ = true := by
  decide +kernel

theorem b_163_2000 : bothSeg evalE (oGrid.idx 163) (oGrid.dm 163) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 163) oGrid.kl oGrid.kr 400 2000 ⟨false, 5178731524045470167693055410869311390731195116424222731313137005927545930008⟩ ⟨false, 189183124998383044022120374055372445651899411122700843071501461019260334142⟩ ⟨false, 5137303680655382774642157123833613951366878374689205594724632964599210393918⟩ ⟨false, 231412760510927208156695464826696048885884545006562087133084757927485917268⟩ = true := by
  decide +kernel

theorem b_163_2400 : bothLoop evalE (oGrid.idx 163) (oGrid.dm 163) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 163) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5137303680655382774642157123833613951366878374689205594724632964599210393918⟩ ⟨false, 231412760510927208156695464826696048885884545006562087133084757927485917268⟩ = true := by
  decide +kernel

theorem o_row_163 : oGrid.row evalE 163 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_163_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_163_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_163_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_163_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_163_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_163_2000).1 (bothLoop_sound b_163_2400).1))))))

theorem n_row_163 : nGrid.row evalE 163 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_163_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_163_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_163_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_163_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_163_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_163_2000).2 (bothLoop_sound b_163_2400).2))))))

theorem b_164_0 : bothSeg evalE (oGrid.idx 164) (oGrid.dm 164) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 164) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2847961289609121031238204927912529758276971730388799693868199035871902742620⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_164_400 : bothSeg evalE (oGrid.idx 164) (oGrid.dm 164) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 164) oGrid.kl oGrid.kr 400 400 ⟨false, 2847961289609121031238204927912529758276971730388799693868199035871902742620⟩ ⟨false, 0⟩ ⟨false, 4604063319349713102400229153713586370162021092563306280230862744063129970120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_164_800 : bothSeg evalE (oGrid.idx 164) (oGrid.dm 164) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 164) oGrid.kl oGrid.kr 400 800 ⟨false, 4604063319349713102400229153713586370162021092563306280230862744063129970120⟩ ⟨false, 0⟩ ⟨false, 5251705674544471720496667854279492125621741953583606729904335307703279425612⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_164_1200 : bothSeg evalE (oGrid.idx 164) (oGrid.dm 164) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 164) oGrid.kl oGrid.kr 400 1200 ⟨false, 5251705674544471720496667854279492125621741953583606729904335307703279425612⟩ ⟨false, 0⟩ ⟨false, 5334053793775869439901141564708468937608897467365162207034740235085274317518⟩ ⟨false, 12454668874210832257384735542125961990812313008087573203225052671658244860⟩ = true := by
  decide +kernel

theorem b_164_1600 : bothSeg evalE (oGrid.idx 164) (oGrid.dm 164) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 164) oGrid.kl oGrid.kr 400 1600 ⟨false, 5334053793775869439901141564708468937608897467365162207034740235085274317518⟩ ⟨false, 12454668874210832257384735542125961990812313008087573203225052671658244860⟩ ⟨false, 5157547065270729310369361903387305345902988472043241405783988122665210863510⟩ ⟨false, 189264691101872300404236655636437959787464956304240400076228152266464158568⟩ = true := by
  decide +kernel

theorem b_164_2000 : bothSeg evalE (oGrid.idx 164) (oGrid.dm 164) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 164) oGrid.kl oGrid.kr 400 2000 ⟨false, 5157547065270729310369361903387305345902988472043241405783988122665210863510⟩ ⟨false, 189264691101872300404236655636437959787464956304240400076228152266464158568⟩ ⟨false, 5116368690855480489396828330404310453172824398264230090614144417814755604942⟩ ⟨false, 231246740547335264893077624520943902386611572685286641649767533272166989112⟩ = true := by
  decide +kernel

theorem b_164_2400 : bothLoop evalE (oGrid.idx 164) (oGrid.dm 164) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 164) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5116368690855480489396828330404310453172824398264230090614144417814755604942⟩ ⟨false, 231246740547335264893077624520943902386611572685286641649767533272166989112⟩ = true := by
  decide +kernel

theorem o_row_164 : oGrid.row evalE 164 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_164_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_164_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_164_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_164_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_164_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_164_2000).1 (bothLoop_sound b_164_2400).1))))))

theorem n_row_164 : nGrid.row evalE 164 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_164_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_164_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_164_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_164_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_164_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_164_2000).2 (bothLoop_sound b_164_2400).2))))))

theorem b_165_0 : bothSeg evalE (oGrid.idx 165) (oGrid.dm 165) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 165) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2837017394333199740608464876621025766218519566853237632743313238398849344742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_165_400 : bothSeg evalE (oGrid.idx 165) (oGrid.dm 165) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 165) oGrid.kl oGrid.kr 400 400 ⟨false, 2837017394333199740608464876621025766218519566853237632743313238398849344742⟩ ⟨false, 0⟩ ⟨false, 4586411675107842000936950044507144564329862069462046209689551970451094886930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_165_800 : bothSeg evalE (oGrid.idx 165) (oGrid.dm 165) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 165) oGrid.kl oGrid.kr 400 800 ⟨false, 4586411675107842000936950044507144564329862069462046209689551970451094886930⟩ ⟨false, 0⟩ ⟨false, 5231343007170150726220496510815425596474800516545482788048293868239252136092⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_165_1200 : bothSeg evalE (oGrid.idx 165) (oGrid.dm 165) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 165) oGrid.kl oGrid.kr 400 1200 ⟨false, 5231343007170150726220496510815425596474800516545482788048293868239252136092⟩ ⟨false, 0⟩ ⟨false, 5312661319338984435504603367398468051479783019265950790075291023380704352340⟩ ⟨false, 12803477159524695392049670230544922414916635631607678710870808701960445032⟩ = true := by
  decide +kernel

theorem b_165_1600 : bothSeg evalE (oGrid.idx 165) (oGrid.dm 165) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 165) oGrid.kl oGrid.kr 400 1600 ⟨false, 5312661319338984435504603367398468051479783019265950790075291023380704352340⟩ ⟨false, 12803477159524695392049670230544922414916635631607678710870808701960445032⟩ ⟨false, 5136423775541325298232153311581485825644613487114451316283574616602694450982⟩ ⟨false, 189345162682379621123941556728444396726255741328488713674855101250145876644⟩ = true := by
  decide +kernel

theorem b_165_2000 : bothSeg evalE (oGrid.idx 165) (oGrid.dm 165) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 165) oGrid.kl oGrid.kr 400 2000 ⟨false, 5136423775541325298232153311581485825644613487114451316283574616602694450982⟩ ⟨false, 189345162682379621123941556728444396726255741328488713674855101250145876644⟩ ⟨false, 5095493900601239109860614501299841521481233172809841316510228885275512506610⟩ ⟨false, 231080306218396780647872301125763521494670652442074010885769150818076054658⟩ = true := by
  decide +kernel

theorem b_165_2400 : bothLoop evalE (oGrid.idx 165) (oGrid.dm 165) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 165) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5095493900601239109860614501299841521481233172809841316510228885275512506610⟩ ⟨false, 231080306218396780647872301125763521494670652442074010885769150818076054658⟩ = true := by
  decide +kernel

theorem o_row_165 : oGrid.row evalE 165 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_165_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_165_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_165_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_165_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_165_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_165_2000).1 (bothLoop_sound b_165_2400).1))))))

theorem n_row_165 : nGrid.row evalE 165 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_165_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_165_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_165_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_165_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_165_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_165_2000).2 (bothLoop_sound b_165_2400).2))))))

theorem b_166_0 : bothSeg evalE (oGrid.idx 166) (oGrid.dm 166) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 166) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2826106659831949472444531286265917768915752572908806728219100496408253482992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_166_400 : bothSeg evalE (oGrid.idx 166) (oGrid.dm 166) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 166) oGrid.kl oGrid.kr 400 400 ⟨false, 2826106659831949472444531286265917768915752572908806728219100496408253482992⟩ ⟨false, 0⟩ ⟨false, 4568811177277676708410887463770774396980118827790159341138104720079271074876⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_166_800 : bothSeg evalE (oGrid.idx 166) (oGrid.dm 166) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 166) oGrid.kl oGrid.kr 400 800 ⟨false, 4568811177277676708410887463770774396980118827790159341138104720079271074876⟩ ⟨false, 0⟩ ⟨false, 5211037841298311049405269125726485151582955471048141905784284487051833233582⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_166_1200 : bothSeg evalE (oGrid.idx 166) (oGrid.dm 166) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 166) oGrid.kl oGrid.kr 400 1200 ⟨false, 5211037841298311049405269125726485151582955471048141905784284487051833233582⟩ ⟨false, 0⟩ ⟨false, 5291326117311378045975608628061321354248610982116514595939151453221870157990⟩ ⟨false, 13155046347718000026921252043591803080658285754622577538885942086000172592⟩ = true := by
  decide +kernel

theorem b_166_1600 : bothSeg evalE (oGrid.idx 166) (oGrid.dm 166) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 166) oGrid.kl oGrid.kr 400 1600 ⟨false, 5291326117311378045975608628061321354248610982116514595939151453221870157990⟩ ⟨false, 13155046347718000026921252043591803080658285754622577538885942086000172592⟩ ⟨false, 5115361584280389570305439006061696081424456564413006879870368560421733444490⟩ ⟨false, 189424462348926838531646480315859603795612588609939652673383285900789588042⟩ = true := by
  decide +kernel

theorem b_166_2000 : bothSeg evalE (oGrid.idx 166) (oGrid.dm 166) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 166) oGrid.kl oGrid.kr 400 2000 ⟨false, 5115361584280389570305439006061696081424456564413006879870368560421733444490⟩ ⟨false, 189424462348926838531646480315859603795612588609939652673383285900789588042⟩ ⟨false, 5074679303416010896202576679419131636622053300959989394967395806876662831992⟩ ⟨false, 230913814044499869477677239726184928059319271910853994334554013191983211870⟩ = true := by
  decide +kernel

theorem b_166_2400 : bothLoop evalE (oGrid.idx 166) (oGrid.dm 166) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 166) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5074679303416010896202576679419131636622053300959989394967395806876662831992⟩ ⟨false, 230913814044499869477677239726184928059319271910853994334554013191983211870⟩ = true := by
  decide +kernel

theorem o_row_166 : oGrid.row evalE 166 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_166_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_166_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_166_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_166_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_166_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_166_2000).1 (bothLoop_sound b_166_2400).1))))))

theorem n_row_166 : nGrid.row evalE 166 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_166_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_166_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_166_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_166_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_166_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_166_2000).2 (bothLoop_sound b_166_2400).2))))))

theorem b_167_0 : bothSeg evalE (oGrid.idx 167) (oGrid.dm 167) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 167) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2815229030651657587867253972974327295952489692684507472464476549479879006300⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_167_400 : bothSeg evalE (oGrid.idx 167) (oGrid.dm 167) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 167) oGrid.kl oGrid.kr 400 400 ⟨false, 2815229030651657587867253972974327295952489692684507472464476549479879006300⟩ ⟨false, 0⟩ ⟨false, 4551261755434376883738373247378981947137417861168795188884854026519215217114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_167_800 : bothSeg evalE (oGrid.idx 167) (oGrid.dm 167) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 167) oGrid.kl oGrid.kr 400 800 ⟨false, 4551261755434376883738373247378981947137417861168795188884854026519215217114⟩ ⟨false, 0⟩ ⟨false, 5190790099805378130375174978762620709057888998977187570150261207702286481562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_167_1200 : bothSeg evalE (oGrid.idx 167) (oGrid.dm 167) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 167) oGrid.kl oGrid.kr 400 1200 ⟨false, 5190790099805378130375174978762620709057888998977187570150261207702286481562⟩ ⟨false, 0⟩ ⟨false, 5270048265590871980681204586368042727848695739237810982549111724117341830906⟩ ⟨false, 13509410625960947055026362893940437172971392868610110140067961745413294286⟩ = true := by
  decide +kernel

theorem b_167_1600 : bothSeg evalE (oGrid.idx 167) (oGrid.dm 167) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 167) oGrid.kl oGrid.kr 400 1600 ⟨false, 5270048265590871980681204586368042727848695739237810982549111724117341830906⟩ ⟨false, 13509410625960947055026362893940437172971392868610110140067961745413294286⟩ ⟨false, 5094360645446098693630105826310366873271318363586364129460001931678952641104⟩ ⟨false, 189502528158741048184160273657935322345403811412173292906843675340664503690⟩ = true := by
  decide +kernel

theorem b_167_2000 : bothSeg evalE (oGrid.idx 167) (oGrid.dm 167) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 167) oGrid.kl oGrid.kr 400 2000 ⟨false, 5094360645446098693630105826310366873271318363586364129460001931678952641104⟩ ⟨false, 189502528158741048184160273657935322345403811412173292906843675340664503690⟩ ⟨false, 5053925073906029689878069431411331195130071958000571796867364597911038587576⟩ ⟨false, 230746894681460784090999801190250302883470657787279369546448373470590268748⟩ = true := by
  decide +kernel

theorem b_167_2400 : bothLoop evalE (oGrid.idx 167) (oGrid.dm 167) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 167) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5053925073906029689878069431411331195130071958000571796867364597911038587576⟩ ⟨false, 230746894681460784090999801190250302883470657787279369546448373470590268748⟩ = true := by
  decide +kernel

theorem o_row_167 : oGrid.row evalE 167 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_167_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_167_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_167_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_167_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_167_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_167_2000).1 (bothLoop_sound b_167_2400).1))))))

theorem n_row_167 : nGrid.row evalE 167 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_167_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_167_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_167_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_167_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_167_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_167_2000).2 (bothLoop_sound b_167_2400).2))))))

theorem o_blk_144 : allFrom (fun j => oGrid.row evalE j) 144 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 144) o_row_144 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 145) o_row_145 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 146) o_row_146 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 147) o_row_147 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 148) o_row_148 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 149) o_row_149 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 150) o_row_150 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 151) o_row_151 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 152) o_row_152 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 153) o_row_153 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 154) o_row_154 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 155) o_row_155 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 156) o_row_156 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 157) o_row_157 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 158) o_row_158 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 159) o_row_159 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 160) o_row_160 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 161) o_row_161 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 162) o_row_162 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 163) o_row_163 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 164) o_row_164 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 165) o_row_165 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 166) o_row_166 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 167) o_row_167 (allFrom_zero (fun j => oGrid.row evalE j) 168)))))))))))))))))))))))))

theorem n_blk_144 : allFrom (fun j => nGrid.row evalE j) 144 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 144) n_row_144 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 145) n_row_145 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 146) n_row_146 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 147) n_row_147 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 148) n_row_148 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 149) n_row_149 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 150) n_row_150 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 151) n_row_151 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 152) n_row_152 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 153) n_row_153 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 154) n_row_154 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 155) n_row_155 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 156) n_row_156 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 157) n_row_157 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 158) n_row_158 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 159) n_row_159 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 160) n_row_160 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 161) n_row_161 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 162) n_row_162 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 163) n_row_163 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 164) n_row_164 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 165) n_row_165 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 166) n_row_166 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 167) n_row_167 (allFrom_zero (fun j => nGrid.row evalE j) 168)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
