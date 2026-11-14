/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 10 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `240`–`263`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_240_0 : bothSeg evalE (oGrid.idx 240) (oGrid.dm 240) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 240) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2104933052890813865102310548742757078831017536310128277856180777685798875154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_240_400 : bothSeg evalE (oGrid.idx 240) (oGrid.dm 240) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 240) oGrid.kl oGrid.kr 400 400 ⟨false, 2104933052890813865102310548742757078831017536310128277856180777685798875154⟩ ⟨false, 0⟩ ⟨false, 3400288527136513032047612861490295186817122350414420709111599413564685950354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_240_800 : bothSeg evalE (oGrid.idx 240) (oGrid.dm 240) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 240) oGrid.kl oGrid.kr 400 800 ⟨false, 3400288527136513032047612861490295186817122350414420709111599413564685950354⟩ ⟨false, 0⟩ ⟨false, 3859789153986408793337972703310516480051160197914834382938927080168892556266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_240_1200 : bothSeg evalE (oGrid.idx 240) (oGrid.dm 240) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 240) oGrid.kl oGrid.kr 400 1200 ⟨false, 3859789153986408793337972703310516480051160197914834382938927080168892556266⟩ ⟨false, 0⟩ ⟨false, 3876021704124079308462274684816906137223035418086831178249650491167397888690⟩ ⟨false, 34116109318430988978994202548989312178286520323335341942151900200241320676⟩ = true := by
  decide +kernel

theorem b_240_1600 : bothSeg evalE (oGrid.idx 240) (oGrid.dm 240) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 240) oGrid.kl oGrid.kr 400 1600 ⟨false, 3876021704124079308462274684816906137223035418086831178249650491167397888690⟩ ⟨false, 34116109318430988978994202548989312178286520323335341942151900200241320676⟩ ⟨false, 3717929365054748609907792651379716737921120912281466516787179907447207581254⟩ ⟨false, 192581281563110198482897910715001016616192491587374679346996025910239945916⟩ = true := by
  decide +kernel

theorem b_240_2000 : bothSeg evalE (oGrid.idx 240) (oGrid.dm 240) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 240) oGrid.kl oGrid.kr 400 2000 ⟨false, 3717929365054748609907792651379716737921120912281466516787179907447207581254⟩ ⟨false, 192581281563110198482897910715001016616192491587374679346996025910239945916⟩ ⟨false, 3694857921305173594564910699077126321630102897228043957731952413791867233038⟩ ⟨false, 217163618621344171268521778390717074581451579286747468951982489630922292096⟩ = true := by
  decide +kernel

theorem b_240_2400 : bothLoop evalE (oGrid.idx 240) (oGrid.dm 240) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 240) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3694857921305173594564910699077126321630102897228043957731952413791867233038⟩ ⟨false, 217163618621344171268521778390717074581451579286747468951982489630922292096⟩ = true := by
  decide +kernel

theorem o_row_240 : oGrid.row evalE 240 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_240_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_240_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_240_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_240_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_240_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_240_2000).1 (bothLoop_sound b_240_2400).1))))))

theorem n_row_240 : nGrid.row evalE 240 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_240_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_240_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_240_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_240_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_240_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_240_2000).2 (bothLoop_sound b_240_2400).2))))))

theorem b_241_0 : bothSeg evalE (oGrid.idx 241) (oGrid.dm 241) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 241) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2096277429635742846816503357231259971152933544489002967289331134900259403712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_241_400 : bothSeg evalE (oGrid.idx 241) (oGrid.dm 241) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 241) oGrid.kl oGrid.kr 400 400 ⟨false, 2096277429635742846816503357231259971152933544489002967289331134900259403712⟩ ⟨false, 0⟩ ⟨false, 3386203188576965313129838489151075407284900654746450126547032167023393473962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_241_800 : bothSeg evalE (oGrid.idx 241) (oGrid.dm 241) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 241) oGrid.kl oGrid.kr 400 800 ⟨false, 3386203188576965313129838489151075407284900654746450126547032167023393473962⟩ ⟨false, 0⟩ ⟨false, 3843466303195372538819820472066464278232460239959238708083295497234538863828⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_241_1200 : bothSeg evalE (oGrid.idx 241) (oGrid.dm 241) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 241) oGrid.kl oGrid.kr 400 1200 ⟨false, 3843466303195372538819820472066464278232460239959238708083295497234538863828⟩ ⟨false, 0⟩ ⟨false, 3859127809216314228687161855801961409003071558224765554588701262533865036600⟩ ⟨false, 34200232408177555102366354464108172706008715175451476627174812742127012086⟩ = true := by
  decide +kernel

theorem b_241_1600 : bothSeg evalE (oGrid.idx 241) (oGrid.dm 241) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 241) oGrid.kl oGrid.kr 400 1600 ⟨false, 3859127809216314228687161855801961409003071558224765554588701262533865036600⟩ ⟨false, 34200232408177555102366354464108172706008715175451476627174812742127012086⟩ ⟨false, 3701111471976576057335965235501672880597343334229510785897158382273660858590⟩ ⟨false, 192590428301238015331463285466195858637055132477098870956740634280281145004⟩ = true := by
  decide +kernel

theorem b_241_2000 : bothSeg evalE (oGrid.idx 241) (oGrid.dm 241) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 241) oGrid.kl oGrid.kr 400 2000 ⟨false, 3701111471976576057335965235501672880597343334229510785897158382273660858590⟩ ⟨false, 192590428301238015331463285466195858637055132477098870956740634280281145004⟩ ⟨false, 3678284088986655099238765240595613848099386552175114799218544135405604197702⟩ ⟨false, 216971242507688472181601911794554576805068950974872232026257269057336060492⟩ = true := by
  decide +kernel

theorem b_241_2400 : bothLoop evalE (oGrid.idx 241) (oGrid.dm 241) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 241) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3678284088986655099238765240595613848099386552175114799218544135405604197702⟩ ⟨false, 216971242507688472181601911794554576805068950974872232026257269057336060492⟩ = true := by
  decide +kernel

theorem o_row_241 : oGrid.row evalE 241 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_241_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_241_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_241_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_241_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_241_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_241_2000).1 (bothLoop_sound b_241_2400).1))))))

theorem n_row_241 : nGrid.row evalE 241 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_241_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_241_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_241_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_241_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_241_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_241_2000).2 (bothLoop_sound b_241_2400).2))))))

theorem b_242_0 : bothSeg evalE (oGrid.idx 242) (oGrid.dm 242) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 242) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2087648984942159255442159592819113833989345646861290440357804461107137674606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_242_400 : bothSeg evalE (oGrid.idx 242) (oGrid.dm 242) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 242) oGrid.kl oGrid.kr 400 400 ⟨false, 2087648984942159255442159592819113833989345646861290440357804461107137674606⟩ ⟨false, 0⟩ ⟨false, 3372160664887353518642914123463693280608332503647146863665184812937839648218⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_242_800 : bothSeg evalE (oGrid.idx 242) (oGrid.dm 242) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 242) oGrid.kl oGrid.kr 400 800 ⟨false, 3372160664887353518642914123463693280608332503647146863665184812937839648218⟩ ⟨false, 0⟩ ⟨false, 3827192339678384320522363929082166080361097622098197009753679618639445086206⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_242_1200 : bothSeg evalE (oGrid.idx 242) (oGrid.dm 242) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 242) oGrid.kl oGrid.kr 400 1200 ⟨false, 3827192339678384320522363929082166080361097622098197009753679618639445086206⟩ ⟨false, 0⟩ ⟨false, 3842291968783334501234031076816814413162970796029830953018764992095611560868⟩ ⟨false, 34277740938643412489282151244151465962653416220693138529045604819102174714⟩ = true := by
  decide +kernel

theorem b_242_1600 : bothSeg evalE (oGrid.idx 242) (oGrid.dm 242) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 242) oGrid.kl oGrid.kr 400 1600 ⟨false, 3842291968783334501234031076816814413162970796029830953018764992095611560868⟩ ⟨false, 34277740938643412489282151244151465962653416220693138529045604819102174714⟩ ⟨false, 3684345847780417340993705202212102135980276407946812561566368854364255899456⟩ ⟨false, 192598725832660672944068795148681099067092878963672464360327233207497550308⟩ = true := by
  decide +kernel

theorem b_242_2000 : bothSeg evalE (oGrid.idx 242) (oGrid.dm 242) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 242) oGrid.kl oGrid.kr 400 2000 ⟨false, 3684345847780417340993705202212102135980276407946812561566368854364255899456⟩ ⟨false, 192598725832660672944068795148681099067092878963672464360327233207497550308⟩ ⟨false, 3661762760786789126533749778205635684820623968219990846392123209683202426144⟩ ⟨false, 216779113783742279439798716622694964683367218398005800111819676938587879238⟩ = true := by
  decide +kernel

theorem b_242_2400 : bothLoop evalE (oGrid.idx 242) (oGrid.dm 242) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 242) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3661762760786789126533749778205635684820623968219990846392123209683202426144⟩ ⟨false, 216779113783742279439798716622694964683367218398005800111819676938587879238⟩ = true := by
  decide +kernel

theorem o_row_242 : oGrid.row evalE 242 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_242_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_242_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_242_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_242_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_242_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_242_2000).1 (bothLoop_sound b_242_2400).1))))))

theorem n_row_242 : nGrid.row evalE 242 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_242_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_242_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_242_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_242_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_242_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_242_2000).2 (bothLoop_sound b_242_2400).2))))))

theorem b_243_0 : bothSeg evalE (oGrid.idx 243) (oGrid.dm 243) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 243) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2079047646902999679682926365350813528911098286474547447684757446073971026070⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_243_400 : bothSeg evalE (oGrid.idx 243) (oGrid.dm 243) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 243) oGrid.kl oGrid.kr 400 400 ⟨false, 2079047646902999679682926365350813528911098286474547447684757446073971026070⟩ ⟨false, 0⟩ ⟨false, 3358160869859107825700454259986053427536028359808233252223879405676141928026⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_243_800 : bothSeg evalE (oGrid.idx 243) (oGrid.dm 243) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 243) oGrid.kl oGrid.kr 400 800 ⟨false, 3358160869859107825700454259986053427536028359808233252223879405676141928026⟩ ⟨false, 0⟩ ⟨false, 3810967144224900458207736950726276693842571725130294951779860078754007054120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_243_1200 : bothSeg evalE (oGrid.idx 243) (oGrid.dm 243) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 243) oGrid.kl oGrid.kr 400 1200 ⟨false, 3810967144224900458207736950726276693842571725130294951779860078754007054120⟩ ⟨false, 0⟩ ⟨false, 3825514089435064235426657331594797732426170022607190957440040654276269940558⟩ ⟨false, 34348691331499675334759614487296041945431622045430525004525114353494487612⟩ = true := by
  decide +kernel

theorem b_243_1600 : bothSeg evalE (oGrid.idx 243) (oGrid.dm 243) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 243) oGrid.kl oGrid.kr 400 1600 ⟨false, 3825514089435064235426657331594797732426170022607190957440040654276269940558⟩ ⟨false, 34348691331499675334759614487296041945431622045430525004525114353494487612⟩ ⟨false, 3667632405132314218780260082932437663368406805807586737009191281954222278856⟩ ⟨false, 192606200126051436960853436962160486486079584778194799529052538556341263024⟩ = true := by
  decide +kernel

theorem b_243_2000 : bothSeg evalE (oGrid.idx 243) (oGrid.dm 243) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 243) oGrid.kl oGrid.kr 400 2000 ⟨false, 3667632405132314218780260082932437663368406805807586737009191281954222278856⟩ ⟨false, 192606200126051436960853436962160486486079584778194799529052538556341263024⟩ ⟨false, 3645293827060153842982660897988945018114363481671976166550402028309009138256⟩ ⟨false, 216587411214910094520740086010277527411922796434798034060509873862930818416⟩ = true := by
  decide +kernel

theorem b_243_2400 : bothLoop evalE (oGrid.idx 243) (oGrid.dm 243) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 243) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3645293827060153842982660897988945018114363481671976166550402028309009138256⟩ ⟨false, 216587411214910094520740086010277527411922796434798034060509873862930818416⟩ = true := by
  decide +kernel

theorem o_row_243 : oGrid.row evalE 243 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_243_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_243_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_243_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_243_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_243_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_243_2000).1 (bothLoop_sound b_243_2400).1))))))

theorem n_row_243 : nGrid.row evalE 243 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_243_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_243_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_243_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_243_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_243_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_243_2000).2 (bothLoop_sound b_243_2400).2))))))

theorem b_244_0 : bothSeg evalE (oGrid.idx 244) (oGrid.dm 244) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 244) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2070473308631001926433737983417221758984413597263765042868002003719828708986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_244_400 : bothSeg evalE (oGrid.idx 244) (oGrid.dm 244) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 244) oGrid.kl oGrid.kr 400 400 ⟨false, 2070473308631001926433737983417221758984413597263765042868002003719828708986⟩ ⟨false, 0⟩ ⟨false, 3344203699857515019976722950919971099766750114606223111993306926060850793082⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_244_800 : bothSeg evalE (oGrid.idx 244) (oGrid.dm 244) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 244) oGrid.kl oGrid.kr 400 800 ⟨false, 3344203699857515019976722950919971099766750114606223111993306926060850793082⟩ ⟨false, 0⟩ ⟨false, 3794790639487230161254311743023285864210151077163409452503432970442237447514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_244_1200 : bothSeg evalE (oGrid.idx 244) (oGrid.dm 244) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 244) oGrid.kl oGrid.kr 400 1200 ⟨false, 3794790639487230161254311743023285864210151077163409452503432970442237447514⟩ ⟨false, 0⟩ ⟨false, 3808793569950422238975765649694176803754607496012063856330290113935688077074⟩ ⟨false, 34413390725590012345583420833718510129359518886864398526392446534784562642⟩ = true := by
  decide +kernel

theorem b_244_1600 : bothSeg evalE (oGrid.idx 244) (oGrid.dm 244) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 244) oGrid.kl oGrid.kr 400 1600 ⟨false, 3808793569950422238975765649694176803754607496012063856330290113935688077074⟩ ⟨false, 34413390725590012345583420833718510129359518886864398526392446534784562642⟩ ⟨false, 3650970700218610806842203178986561110616488094650601051353464624861018911230⟩ ⟨false, 192613052935430571743631595249415323895611571554097061223956713817505708476⟩ = true := by
  decide +kernel

theorem b_244_2000 : bothSeg evalE (oGrid.idx 244) (oGrid.dm 244) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 244) oGrid.kl oGrid.kr 400 2000 ⟨false, 3650970700218610806842203178986561110616488094650601051353464624861018911230⟩ ⟨false, 192613052935430571743631595249415323895611571554097061223956713817505708476⟩ ⟨false, 3628876832736634530127856956857253315860968759348926254716663411746760273472⟩ ⟨false, 216396149465802336382420671731283812213562105708878130726597075197051814620⟩ = true := by
  decide +kernel

theorem b_244_2400 : bothLoop evalE (oGrid.idx 244) (oGrid.dm 244) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 244) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3628876832736634530127856956857253315860968759348926254716663411746760273472⟩ ⟨false, 216396149465802336382420671731283812213562105708878130726597075197051814620⟩ = true := by
  decide +kernel

theorem o_row_244 : oGrid.row evalE 244 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_244_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_244_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_244_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_244_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_244_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_244_2000).1 (bothLoop_sound b_244_2400).1))))))

theorem n_row_244 : nGrid.row evalE 244 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_244_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_244_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_244_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_244_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_244_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_244_2000).2 (bothLoop_sound b_244_2400).2))))))

theorem b_245_0 : bothSeg evalE (oGrid.idx 245) (oGrid.dm 245) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 245) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2061925934736734335835335222027147456223742518623433270992251037156913056426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_245_400 : bothSeg evalE (oGrid.idx 245) (oGrid.dm 245) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 245) oGrid.kl oGrid.kr 400 400 ⟨false, 2061925934736734335835335222027147456223742518623433270992251037156913056426⟩ ⟨false, 0⟩ ⟨false, 3330289045474705782436120561811726907332932086257789827240059876292979249626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_245_800 : bothSeg evalE (oGrid.idx 245) (oGrid.dm 245) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 245) oGrid.kl oGrid.kr 400 800 ⟨false, 3330289045474705782436120561811726907332932086257789827240059876292979249626⟩ ⟨false, 0⟩ ⟨false, 3778662716310330432441013544944385282732475652173723081149169638952446726554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_245_1200 : bothSeg evalE (oGrid.idx 245) (oGrid.dm 245) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 245) oGrid.kl oGrid.kr 400 1200 ⟨false, 3778662716310330432441013544944385282732475652173723081149169638952446726554⟩ ⟨false, 0⟩ ⟨false, 3792130589423962270353249890923872219350081200219600718323993138989170197610⟩ ⟨false, 34471665462525294003651008190333333539734889361099708461182276877787029068⟩ = true := by
  decide +kernel

theorem b_245_1600 : bothSeg evalE (oGrid.idx 245) (oGrid.dm 245) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 245) oGrid.kl oGrid.kr 400 1600 ⟨false, 3792130589423962270353249890923872219350081200219600718323993138989170197610⟩ ⟨false, 34471665462525294003651008190333333539734889361099708461182276877787029068⟩ ⟨false, 3634360866499157901565801236241796998198023589256972979633640567930216403612⟩ ⟨false, 192619321760097872560468598504031688596601303127371105121147759490063567176⟩ = true := by
  decide +kernel

theorem b_245_2000 : bothSeg evalE (oGrid.idx 245) (oGrid.dm 245) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 245) oGrid.kl oGrid.kr 400 2000 ⟨false, 3634360866499157901565801236241796998198023589256972979633640567930216403612⟩ ⟨false, 192619321760097872560468598504031688596601303127371105121147759490063567176⟩ ⟨false, 3612511892942623126550627221015616265696619149503120904516409098053260707224⟩ ⟨false, 216205211387236461724286768080341920757097513918849810120477068568719616984⟩ = true := by
  decide +kernel

theorem b_245_2400 : bothLoop evalE (oGrid.idx 245) (oGrid.dm 245) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 245) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3612511892942623126550627221015616265696619149503120904516409098053260707224⟩ ⟨false, 216205211387236461724286768080341920757097513918849810120477068568719616984⟩ = true := by
  decide +kernel

theorem o_row_245 : oGrid.row evalE 245 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_245_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_245_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_245_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_245_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_245_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_245_2000).1 (bothLoop_sound b_245_2400).1))))))

theorem n_row_245 : nGrid.row evalE 245 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_245_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_245_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_245_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_245_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_245_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_245_2000).2 (bothLoop_sound b_245_2400).2))))))

theorem b_246_0 : bothSeg evalE (oGrid.idx 246) (oGrid.dm 246) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 246) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2053405452774292422398417836628437950865017724846303195372253021495748053918⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_246_400 : bothSeg evalE (oGrid.idx 246) (oGrid.dm 246) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 246) oGrid.kl oGrid.kr 400 400 ⟨false, 2053405452774292422398417836628437950865017724846303195372253021495748053918⟩ ⟨false, 0⟩ ⟨false, 3316416819938351720907765889291744018319560908852186477463318302731666268060⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_246_800 : bothSeg evalE (oGrid.idx 246) (oGrid.dm 246) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 246) oGrid.kl oGrid.kr 400 800 ⟨false, 3316416819938351720907765889291744018319560908852186477463318302731666268060⟩ ⟨false, 0⟩ ⟨false, 3762583245806183175066846569685410273863765762227996292659930796305926242532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_246_1200 : bothSeg evalE (oGrid.idx 246) (oGrid.dm 246) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 246) oGrid.kl oGrid.kr 400 1200 ⟨false, 3762583245806183175066846569685410273863765762227996292659930796305926242532⟩ ⟨false, 0⟩ ⟨false, 3775524941176351322700763320223821791154183709992016806371792757215758801418⟩ ⟨false, 34523578542610255460710974947097107474863270297397568602399563097318193286⟩ = true := by
  decide +kernel

theorem b_246_1600 : bothSeg evalE (oGrid.idx 246) (oGrid.dm 246) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 246) oGrid.kl oGrid.kr 400 1600 ⟨false, 3775524941176351322700763320223821791154183709992016806371792757215758801418⟩ ⟨false, 34523578542610255460710974947097107474863270297397568602399563097318193286⟩ ⟨false, 3617802905783560232577148564960301848026709782444310975946627571693887242008⟩ ⟨false, 192624743733027869582753387803148033917579308593906549923947244752006514478⟩ = true := by
  decide +kernel

theorem b_246_2000 : bothSeg evalE (oGrid.idx 246) (oGrid.dm 246) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 246) oGrid.kl oGrid.kr 400 2000 ⟨false, 3617802905783560232577148564960301848026709782444310975946627571693887242008⟩ ⟨false, 192624743733027869582753387803148033917579308593906549923947244752006514478⟩ ⟨false, 3596198980057953470346951409122607444915789179072086185995752786076655338862⟩ ⟨false, 216014391002031957482905581893446600213642995080978263953965638860725501688⟩ = true := by
  decide +kernel

theorem b_246_2400 : bothLoop evalE (oGrid.idx 246) (oGrid.dm 246) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 246) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3596198980057953470346951409122607444915789179072086185995752786076655338862⟩ ⟨false, 216014391002031957482905581893446600213642995080978263953965638860725501688⟩ = true := by
  decide +kernel

theorem o_row_246 : oGrid.row evalE 246 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_246_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_246_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_246_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_246_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_246_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_246_2000).1 (bothLoop_sound b_246_2400).1))))))

theorem n_row_246 : nGrid.row evalE 246 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_246_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_246_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_246_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_246_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_246_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_246_2000).2 (bothLoop_sound b_246_2400).2))))))

theorem b_247_0 : bothSeg evalE (oGrid.idx 247) (oGrid.dm 247) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 247) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2044911796054123387779407764677782566489136734318466970566200519970919675368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_247_400 : bothSeg evalE (oGrid.idx 247) (oGrid.dm 247) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 247) oGrid.kl oGrid.kr 400 400 ⟨false, 2044911796054123387779407764677782566489136734318466970566200519970919675368⟩ ⟨false, 0⟩ ⟨false, 3302586919851156651183834256977513148321524442145749770409743688700709635458⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_247_800 : bothSeg evalE (oGrid.idx 247) (oGrid.dm 247) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 247) oGrid.kl oGrid.kr 400 800 ⟨false, 3302586919851156651183834256977513148321524442145749770409743688700709635458⟩ ⟨false, 0⟩ ⟨false, 3746552146836004919249047471676512685729637660069243681589352771007958265760⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_247_1200 : bothSeg evalE (oGrid.idx 247) (oGrid.dm 247) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 247) oGrid.kl oGrid.kr 400 1200 ⟨false, 3746552146836004919249047471676512685729637660069243681589352771007958265760⟩ ⟨false, 0⟩ ⟨false, 3758976450575915770412426164733909785476709185523297203177589265517451624122⟩ ⟨false, 34569236457466055137563020431686920202012843755869353706504381516678065638⟩ = true := by
  decide +kernel

theorem b_247_1600 : bothSeg evalE (oGrid.idx 247) (oGrid.dm 247) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 247) oGrid.kl oGrid.kr 400 1600 ⟨false, 3758976450575915770412426164733909785476709185523297203177589265517451624122⟩ ⟨false, 34569236457466055137563020431686920202012843755869353706504381516678065638⟩ ⟨false, 3601296577813640011293936815966039398105905583357908605450332915854972914608⟩ ⟨false, 192629391350375412430410349307819883983782174857732267900091472827303595546⟩ = true := by
  decide +kernel

theorem b_247_2000 : bothSeg evalE (oGrid.idx 247) (oGrid.dm 247) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 247) oGrid.kl oGrid.kr 400 2000 ⟨false, 3601296577813640011293936815966039398105905583357908605450332915854972914608⟩ ⟨false, 192629391350375412430410349307819883983782174857732267900091472827303595546⟩ ⟨false, 3579937836768935255641203569129106685913920560801918839051746386855283196976⟩ ⟨false, 215824359843265949684118453686629809829425682910196864401749480684317141518⟩ = true := by
  decide +kernel

theorem b_247_2400 : bothLoop evalE (oGrid.idx 247) (oGrid.dm 247) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 247) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3579937836768935255641203569129106685913920560801918839051746386855283196976⟩ ⟨false, 215824359843265949684118453686629809829425682910196864401749480684317141518⟩ = true := by
  decide +kernel

theorem o_row_247 : oGrid.row evalE 247 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_247_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_247_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_247_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_247_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_247_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_247_2000).1 (bothLoop_sound b_247_2400).1))))))

theorem n_row_247 : nGrid.row evalE 247 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_247_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_247_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_247_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_247_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_247_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_247_2000).2 (bothLoop_sound b_247_2400).2))))))

theorem b_248_0 : bothSeg evalE (oGrid.idx 248) (oGrid.dm 248) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 248) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2036444854526479115764473064386395347215984021285117595521660389841495177430⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_248_400 : bothSeg evalE (oGrid.idx 248) (oGrid.dm 248) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 248) oGrid.kl oGrid.kr 400 400 ⟨false, 2036444854526479115764473064386395347215984021285117595521660389841495177430⟩ ⟨false, 0⟩ ⟨false, 3288799203757276493572747543291528462269614345277193502127582453382590196506⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_248_800 : bothSeg evalE (oGrid.idx 248) (oGrid.dm 248) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 248) oGrid.kl oGrid.kr 400 800 ⟨false, 3288799203757276493572747543291528462269614345277193502127582453382590196506⟩ ⟨false, 0⟩ ⟨false, 3730569272550499328275411752231719078371746001621857479912038257851368222998⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_248_1200 : bothSeg evalE (oGrid.idx 248) (oGrid.dm 248) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 248) oGrid.kl oGrid.kr 400 1200 ⟨false, 3730569272550499328275411752231719078371746001621857479912038257851368222998⟩ ⟨false, 0⟩ ⟨false, 3742484878939266058837264062474873842188277792567147701204730595136243634472⟩ ⟨false, 34608723098632844090706641277981013690054828670262362720426631303205472462⟩ = true := by
  decide +kernel

theorem b_248_1600 : bothSeg evalE (oGrid.idx 248) (oGrid.dm 248) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 248) oGrid.kl oGrid.kr 400 1600 ⟨false, 3742484878939266058837264062474873842188277792567147701204730595136243634472⟩ ⟨false, 34608723098632844090706641277981013690054828670262362720426631303205472462⟩ ⟨false, 3584841745646780576774666979805408304347864536466106290949034280937617426160⟩ ⟨false, 192633272868698464021037490048605792596712078142598530734794347963227061518⟩ = true := by
  decide +kernel

theorem b_248_2000 : bothSeg evalE (oGrid.idx 248) (oGrid.dm 248) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 248) oGrid.kl oGrid.kr 400 2000 ⟨false, 3584841745646780576774666979805408304347864536466106290949034280937617426160⟩ ⟨false, 192633272868698464021037490048605792596712078142598530734794347963227061518⟩ ⟨false, 3563728315699526757391136953865033989354535285760935443913184313978641332546⟩ ⟨false, 215634248184967116397042956324056019725437929566120375050603218753291769970⟩ = true := by
  decide +kernel

theorem b_248_2400 : bothLoop evalE (oGrid.idx 248) (oGrid.dm 248) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 248) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3563728315699526757391136953865033989354535285760935443913184313978641332546⟩ ⟨false, 215634248184967116397042956324056019725437929566120375050603218753291769970⟩ = true := by
  decide +kernel

theorem o_row_248 : oGrid.row evalE 248 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_248_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_248_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_248_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_248_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_248_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_248_2000).1 (bothLoop_sound b_248_2400).1))))))

theorem n_row_248 : nGrid.row evalE 248 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_248_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_248_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_248_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_248_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_248_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_248_2000).2 (bothLoop_sound b_248_2400).2))))))

theorem b_249_0 : bothSeg evalE (oGrid.idx 249) (oGrid.dm 249) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 249) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2028004612353265609408716654309884894004520924446001222473272496275912062654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_249_400 : bothSeg evalE (oGrid.idx 249) (oGrid.dm 249) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 249) oGrid.kl oGrid.kr 400 400 ⟨false, 2028004612353265609408716654309884894004520924446001222473272496275912062654⟩ ⟨false, 0⟩ ⟨false, 3275053660296641551974108097806195798095684347325978113210829037994577309144⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_249_800 : bothSeg evalE (oGrid.idx 249) (oGrid.dm 249) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 249) oGrid.kl oGrid.kr 400 800 ⟨false, 3275053660296641551974108097806195798095684347325978113210829037994577309144⟩ ⟨false, 0⟩ ⟨false, 3714634593813637062386067380724851882669315643051108780466291814101553962794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_249_1200 : bothSeg evalE (oGrid.idx 249) (oGrid.dm 249) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 249) oGrid.kl oGrid.kr 400 1200 ⟨false, 3714634593813637062386067380724851882669315643051108780466291814101553962794⟩ ⟨false, 0⟩ ⟨false, 3726050162934858012127601386212274971860231312873657364212506879161556041906⟩ ⟨false, 34642085488973812087592900730058897146385151523754550575428625159122264428⟩ = true := by
  decide +kernel

theorem b_249_1600 : bothSeg evalE (oGrid.idx 249) (oGrid.dm 249) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 249) oGrid.kl oGrid.kr 400 1600 ⟨false, 3726050162934858012127601386212274971860231312873657364212506879161556041906⟩ ⟨false, 34642085488973812087592900730058897146385151523754550575428625159122264428⟩ ⟨false, 3568438630227311085369170925950224973176847368639470707323868399914551298562⟩ ⟨false, 192636151738784198110260022562091099000884809172855816145268112072667165616⟩ = true := by
  decide +kernel

theorem b_249_2000 : bothSeg evalE (oGrid.idx 249) (oGrid.dm 249) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 249) oGrid.kl oGrid.kr 400 2000 ⟨false, 3568438630227311085369170925950224973176847368639470707323868399914551298562⟩ ⟨false, 192636151738784198110260022562091099000884809172855816145268112072667165616⟩ ⟨false, 3547570626943202690672176229936310559195329310266512570295743474287014946472⟩ ⟨false, 215443893587148740855938220469511561035131352316267650842346073359852194618⟩ = true := by
  decide +kernel

theorem b_249_2400 : bothLoop evalE (oGrid.idx 249) (oGrid.dm 249) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 249) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3547570626943202690672176229936310559195329310266512570295743474287014946472⟩ ⟨false, 215443893587148740855938220469511561035131352316267650842346073359852194618⟩ = true := by
  decide +kernel

theorem o_row_249 : oGrid.row evalE 249 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_249_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_249_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_249_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_249_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_249_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_249_2000).1 (bothLoop_sound b_249_2400).1))))))

theorem n_row_249 : nGrid.row evalE 249 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_249_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_249_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_249_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_249_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_249_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_249_2000).2 (bothLoop_sound b_249_2400).2))))))

theorem b_250_0 : bothSeg evalE (oGrid.idx 250) (oGrid.dm 250) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 250) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2019590954687659335330380028989534263069958678583627872273143715106795048610⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_250_400 : bothSeg evalE (oGrid.idx 250) (oGrid.dm 250) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 250) oGrid.kl oGrid.kr 400 400 ⟨false, 2019590954687659335330380028989534263069958678583627872273143715106795048610⟩ ⟨false, 0⟩ ⟨false, 3261350112780584974250972852425838257635562767331571971106163410081566309210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_250_800 : bothSeg evalE (oGrid.idx 250) (oGrid.dm 250) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 250) oGrid.kl oGrid.kr 400 800 ⟨false, 3261350112780584974250972852425838257635562767331571971106163410081566309210⟩ ⟨false, 0⟩ ⟨false, 3698747939924588766378711192052335040652764132593621680616785149948509904810⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_250_1200 : bothSeg evalE (oGrid.idx 250) (oGrid.dm 250) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 250) oGrid.kl oGrid.kr 400 1200 ⟨false, 3698747939924588766378711192052335040652764132593621680616785149948509904810⟩ ⟨false, 0⟩ ⟨false, 3709672033870097086618773895567240520723512372479762828643681658935700991120⟩ ⟨false, 34669437632387484882480656963426017330308226591154290271548508506242293208⟩ = true := by
  decide +kernel

theorem b_250_1600 : bothSeg evalE (oGrid.idx 250) (oGrid.dm 250) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 250) oGrid.kl oGrid.kr 400 1600 ⟨false, 3709672033870097086618773895567240520723512372479762828643681658935700991120⟩ ⟨false, 34669437632387484882480656963426017330308226591154290271548508506242293208⟩ ⟨false, 3552086877821299392008195800495786593374009631127304960247482036289695556286⟩ ⟨false, 192638227722370113809141771934806939543974487620049750822836352132496119678⟩ = true := by
  decide +kernel

theorem b_250_2000 : bothSeg evalE (oGrid.idx 250) (oGrid.dm 250) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 250) oGrid.kl oGrid.kr 400 2000 ⟨false, 3552086877821299392008195800495786593374009631127304960247482036289695556286⟩ ⟨false, 192638227722370113809141771934806939543974487620049750822836352132496119678⟩ ⟨false, 3531464375422290947602474760452282503422172962697181953810254213456049684696⟩ ⟨false, 215254531862955067656736362619172091580590892044680404524490363276237968734⟩ = true := by
  decide +kernel

theorem b_250_2400 : bothLoop evalE (oGrid.idx 250) (oGrid.dm 250) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 250) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3531464375422290947602474760452282503422172962697181953810254213456049684696⟩ ⟨false, 215254531862955067656736362619172091580590892044680404524490363276237968734⟩ = true := by
  decide +kernel

theorem o_row_250 : oGrid.row evalE 250 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_250_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_250_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_250_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_250_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_250_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_250_2000).1 (bothLoop_sound b_250_2400).1))))))

theorem n_row_250 : nGrid.row evalE 250 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_250_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_250_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_250_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_250_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_250_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_250_2000).2 (bothLoop_sound b_250_2400).2))))))

theorem b_251_0 : bothSeg evalE (oGrid.idx 251) (oGrid.dm 251) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 251) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2011203824490783423809169064449970103231430945764423687111846827444966876434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_251_400 : bothSeg evalE (oGrid.idx 251) (oGrid.dm 251) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 251) oGrid.kl oGrid.kr 400 400 ⟨false, 2011203824490783423809169064449970103231430945764423687111846827444966876434⟩ ⟨false, 0⟩ ⟨false, 3247688481199548762081272451748625414802659509663480030965676687340282962324⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_251_800 : bothSeg evalE (oGrid.idx 251) (oGrid.dm 251) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 251) oGrid.kl oGrid.kr 400 800 ⟨false, 3247688481199548762081272451748625414802659509663480030965676687340282962324⟩ ⟨false, 0⟩ ⟨false, 3682909233547087896924008852538178513362404113474023601114462653336215320234⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_251_1200 : bothSeg evalE (oGrid.idx 251) (oGrid.dm 251) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 251) oGrid.kl oGrid.kr 400 1200 ⟨false, 3682909233547087896924008852538178513362404113474023601114462653336215320234⟩ ⟨false, 0⟩ ⟨false, 3693350249141882262025222044269799818103044843155498958204702622846729918822⟩ ⟨false, 34690765788582268278003335651318106361469372249323655928383736652665099880⟩ = true := by
  decide +kernel

theorem b_251_1600 : bothSeg evalE (oGrid.idx 251) (oGrid.dm 251) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 251) oGrid.kl oGrid.kr 400 1600 ⟨false, 3693350249141882262025222044269799818103044843155498958204702622846729918822⟩ ⟨false, 34690765788582268278003335651318106361469372249323655928383736652665099880⟩ ⟨false, 3535786345587660463246380930197859868900270074997062713244432024569580043568⟩ ⟨false, 192639388044655144805634054999151397239338555165207574419855975195035143456⟩ = true := by
  decide +kernel

theorem b_251_2000 : bothSeg evalE (oGrid.idx 251) (oGrid.dm 251) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 251) oGrid.kl oGrid.kr 400 2000 ⟨false, 3535786345587660463246380930197859868900270074997062713244432024569580043568⟩ ⟨false, 192639388044655144805634054999151397239338555165207574419855975195035143456⟩ ⟨false, 3515409418217857465761738666398898010154705716007705509581532442966737577924⟩ ⟨false, 215064882379862360615352453519149864833870654167744244178990997941057240458⟩ = true := by
  decide +kernel

theorem b_251_2400 : bothLoop evalE (oGrid.idx 251) (oGrid.dm 251) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 251) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3515409418217857465761738666398898010154705716007705509581532442966737577924⟩ ⟨false, 215064882379862360615352453519149864833870654167744244178990997941057240458⟩ = true := by
  decide +kernel

theorem o_row_251 : oGrid.row evalE 251 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_251_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_251_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_251_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_251_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_251_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_251_2000).1 (bothLoop_sound b_251_2400).1))))))

theorem n_row_251 : nGrid.row evalE 251 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_251_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_251_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_251_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_251_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_251_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_251_2000).2 (bothLoop_sound b_251_2400).2))))))

theorem b_252_0 : bothSeg evalE (oGrid.idx 252) (oGrid.dm 252) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 252) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2002843177922191863070474714652293934991062439740006349658508962911081859516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_252_400 : bothSeg evalE (oGrid.idx 252) (oGrid.dm 252) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 252) oGrid.kl oGrid.kr 400 400 ⟨false, 2002843177922191863070474714652293934991062439740006349658508962911081859516⟩ ⟨false, 0⟩ ⟨false, 3234068685042042411380045775415121231019802066691307110857624269300441577774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_252_800 : bothSeg evalE (oGrid.idx 252) (oGrid.dm 252) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 252) oGrid.kl oGrid.kr 400 800 ⟨false, 3234068685042042411380045775415121231019802066691307110857624269300441577774⟩ ⟨false, 0⟩ ⟨false, 3667118351037368256599769542256005229132796890912053289051291960354956276850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_252_1200 : bothSeg evalE (oGrid.idx 252) (oGrid.dm 252) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 252) oGrid.kl oGrid.kr 400 1200 ⟨false, 3667118351037368256599769542256005229132796890912053289051291960354956276850⟩ ⟨false, 0⟩ ⟨false, 3677084254624625984758472664546935094952179441046109909576871920624028191898⟩ ⟨false, 34706636093783342530305279506749294511558075788675165719295793920948805676⟩ = true := by
  decide +kernel

theorem b_252_1600 : bothSeg evalE (oGrid.idx 252) (oGrid.dm 252) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 252) oGrid.kl oGrid.kr 400 1600 ⟨false, 3677084254624625984758472664546935094952179441046109909576871920624028191898⟩ ⟨false, 34706636093783342530305279506749294511558075788675165719295793920948805676⟩ ⟨false, 3519536717828093825680499761448538894216457182625271860007154245549035557398⟩ ⟨false, 192639961151398020551291636731879859762925473653928797780863897507082013008⟩ = true := by
  decide +kernel

theorem b_252_2000 : bothSeg evalE (oGrid.idx 252) (oGrid.dm 252) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 252) oGrid.kl oGrid.kr 400 2000 ⟨false, 3519536717828093825680499761448538894216457182625271860007154245549035557398⟩ ⟨false, 192639961151398020551291636731879859762925473653928797780863897507082013008⟩ ⟨false, 3499405392218016166872306595749268644450257221966469128551492145244765028542⟩ ⟨false, 214875563529955254718751287690201740778959658600194443061002361178860885088⟩ = true := by
  decide +kernel

theorem b_252_2400 : bothLoop evalE (oGrid.idx 252) (oGrid.dm 252) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 252) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3499405392218016166872306595749268644450257221966469128551492145244765028542⟩ ⟨false, 214875563529955254718751287690201740778959658600194443061002361178860885088⟩ = true := by
  decide +kernel

theorem o_row_252 : oGrid.row evalE 252 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_252_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_252_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_252_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_252_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_252_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_252_2000).1 (bothLoop_sound b_252_2400).1))))))

theorem n_row_252 : nGrid.row evalE 252 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_252_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_252_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_252_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_252_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_252_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_252_2000).2 (bothLoop_sound b_252_2400).2))))))

theorem b_253_0 : bothSeg evalE (oGrid.idx 253) (oGrid.dm 253) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 253) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1994508910831639464097075521758482527820634292710929311862278242915458406940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_253_400 : bothSeg evalE (oGrid.idx 253) (oGrid.dm 253) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 253) oGrid.kl oGrid.kr 400 400 ⟨false, 1994508910831639464097075521758482527820634292710929311862278242915458406940⟩ ⟨false, 0⟩ ⟨false, 3220490609047331958466221618551023167974083712521701010512966450559485721858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_253_800 : bothSeg evalE (oGrid.idx 253) (oGrid.dm 253) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 253) oGrid.kl oGrid.kr 400 800 ⟨false, 3220490609047331958466221618551023167974083712521701010512966450559485721858⟩ ⟨false, 0⟩ ⟨false, 3651375208148998629397529002734836788202911554858525418190808878661623299962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_253_1200 : bothSeg evalE (oGrid.idx 253) (oGrid.dm 253) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 253) oGrid.kl oGrid.kr 400 1200 ⟨false, 3651375208148998629397529002734836788202911554858525418190808878661623299962⟩ ⟨false, 0⟩ ⟨false, 3660874117418635624400310933429182504258335612181612648819327226468125751614⟩ ⟨false, 34716894029745002180720910007320815472480358697828981798779907112956243170⟩ = true := by
  decide +kernel

theorem b_253_1600 : bothSeg evalE (oGrid.idx 253) (oGrid.dm 253) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 253) oGrid.kl oGrid.kr 400 1600 ⟨false, 3660874117418635624400310933429182504258335612181612648819327226468125751614⟩ ⟨false, 34716894029745002180720910007320815472480358697828981798779907112956243170⟩ ⟨false, 3503338007848733874468272712078138193078228019461619250669376252913524746778⟩ ⟨false, 192639878464046507867623587384044746320017292751019178514982157533776802380⟩ = true := by
  decide +kernel

theorem b_253_2000 : bothSeg evalE (oGrid.idx 253) (oGrid.dm 253) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 253) oGrid.kl oGrid.kr 400 2000 ⟨false, 3503338007848733874468272712078138193078228019461619250669376252913524746778⟩ ⟨false, 192639878464046507867623587384044746320017292751019178514982157533776802380⟩ ⟨false, 3483452317789586088688364624156858533168054605724640096684495620023121344044⟩ ⟨false, 214686855674179455190264224280172317335074708110513207200483224403655339626⟩ = true := by
  decide +kernel

theorem b_253_2400 : bothLoop evalE (oGrid.idx 253) (oGrid.dm 253) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 253) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3483452317789586088688364624156858533168054605724640096684495620023121344044⟩ ⟨false, 214686855674179455190264224280172317335074708110513207200483224403655339626⟩ = true := by
  decide +kernel

theorem o_row_253 : oGrid.row evalE 253 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_253_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_253_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_253_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_253_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_253_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_253_2000).1 (bothLoop_sound b_253_2400).1))))))

theorem n_row_253 : nGrid.row evalE 253 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_253_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_253_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_253_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_253_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_253_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_253_2000).2 (bothLoop_sound b_253_2400).2))))))

theorem b_254_0 : bothSeg evalE (oGrid.idx 254) (oGrid.dm 254) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 254) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1986200988061145349017697647515200249170308301592391336970572567222086204356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_254_400 : bothSeg evalE (oGrid.idx 254) (oGrid.dm 254) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 254) oGrid.kl oGrid.kr 400 400 ⟨false, 1986200988061145349017697647515200249170308301592391336970572567222086204356⟩ ⟨false, 0⟩ ⟨false, 3206954182635768867287313234661907341741991018194327483017167167646261347880⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_254_800 : bothSeg evalE (oGrid.idx 254) (oGrid.dm 254) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 254) oGrid.kl oGrid.kr 400 800 ⟨false, 3206954182635768867287313234661907341741991018194327483017167167646261347880⟩ ⟨false, 0⟩ ⟨false, 3635679733840769380649869897346994236724366456154520373429922266663868800976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_254_1200 : bothSeg evalE (oGrid.idx 254) (oGrid.dm 254) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 254) oGrid.kl oGrid.kr 400 1200 ⟨false, 3635679733840769380649869897346994236724366456154520373429922266663868800976⟩ ⟨false, 0⟩ ⟨false, 3644719740641291525975833671762371826959297988673780134996498612218279327170⟩ ⟨false, 34721591070633399798491139085234148900323431626884333569199668229877262192⟩ = true := by
  decide +kernel

theorem b_254_1600 : bothSeg evalE (oGrid.idx 254) (oGrid.dm 254) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 254) oGrid.kl oGrid.kr 400 1600 ⟨false, 3644719740641291525975833671762371826959297988673780134996498612218279327170⟩ ⟨false, 34721591070633399798491139085234148900323431626884333569199668229877262192⟩ ⟨false, 3487190400337294719402188456671351023605827019777312208948149879782226054066⟩ ⟨false, 192638859560488771189837886766771956414805076275072804277958405895185050412⟩ = true := by
  decide +kernel

theorem b_254_2000 : bothSeg evalE (oGrid.idx 254) (oGrid.dm 254) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 254) oGrid.kl oGrid.kr 400 2000 ⟨false, 3487190400337294719402188456671351023605827019777312208948149879782226054066⟩ ⟨false, 192638859560488771189837886766771956414805076275072804277958405895185050412⟩ ⟨false, 3467550325382548180427041564656704380044675065423938527693062911767126502994⟩ ⟨false, 214498212320061244267563206074614792997464787466722243442178229753971318764⟩ = true := by
  decide +kernel

theorem b_254_2400 : bothLoop evalE (oGrid.idx 254) (oGrid.dm 254) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 254) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3467550325382548180427041564656704380044675065423938527693062911767126502994⟩ ⟨false, 214498212320061244267563206074614792997464787466722243442178229753971318764⟩ = true := by
  decide +kernel

theorem o_row_254 : oGrid.row evalE 254 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_254_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_254_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_254_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_254_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_254_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_254_2000).1 (bothLoop_sound b_254_2400).1))))))

theorem n_row_254 : nGrid.row evalE 254 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_254_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_254_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_254_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_254_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_254_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_254_2000).2 (bothLoop_sound b_254_2400).2))))))

theorem b_255_0 : bothSeg evalE (oGrid.idx 255) (oGrid.dm 255) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 255) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1977919329705685866887076759611651547870101382418312679008805216226988638864⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_255_400 : bothSeg evalE (oGrid.idx 255) (oGrid.dm 255) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 255) oGrid.kl oGrid.kr 400 400 ⟨false, 1977919329705685866887076759611651547870101382418312679008805216226988638864⟩ ⟨false, 0⟩ ⟨false, 3193459283764309293249532066879713801519903298955565985080206167056792649188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_255_800 : bothSeg evalE (oGrid.idx 255) (oGrid.dm 255) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 255) oGrid.kl oGrid.kr 400 800 ⟨false, 3193459283764309293249532066879713801519903298955565985080206167056792649188⟩ ⟨false, 0⟩ ⟨false, 3620031761656307701209128561858652782108577351358217298409312846236309519120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_255_1200 : bothSeg evalE (oGrid.idx 255) (oGrid.dm 255) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 255) oGrid.kl oGrid.kr 400 1200 ⟨false, 3620031761656307701209128561858652782108577351358217298409312846236309519120⟩ ⟨false, 0⟩ ⟨false, 3628620751020065403829801693962757840620291402093217836567762103526501598718⟩ ⟨false, 34720902074559993175058200505557260760666341504701501323696517351942170510⟩ = true := by
  decide +kernel

theorem b_255_1600 : bothSeg evalE (oGrid.idx 255) (oGrid.dm 255) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 255) oGrid.kl oGrid.kr 400 1600 ⟨false, 3628620751020065403829801693962757840620291402093217836567762103526501598718⟩ ⟨false, 34720902074559993175058200505557260760666341504701501323696517351942170510⟩ ⟨false, 3471093549107653845905293184350676976361408581366642410162322032760516290008⟩ ⟨false, 192637074911870635858335099240952864717009334053205460751303962526266422060⟩ = true := by
  decide +kernel

theorem b_255_2000 : bothSeg evalE (oGrid.idx 255) (oGrid.dm 255) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 255) oGrid.kl oGrid.kr 400 2000 ⟨false, 3471093549107653845905293184350676976361408581366642410162322032760516290008⟩ ⟨false, 192637074911870635858335099240952864717009334053205460751303962526266422060⟩ ⟨false, 3451699071209786937469003620966477992366487479709468810711410464024839718118⟩ ⟨false, 214309809109100791458056503913652987307204978017140523841944584004635668544⟩ = true := by
  decide +kernel

theorem b_255_2400 : bothLoop evalE (oGrid.idx 255) (oGrid.dm 255) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 255) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3451699071209786937469003620966477992366487479709468810711410464024839718118⟩ ⟨false, 214309809109100791458056503913652987307204978017140523841944584004635668544⟩ = true := by
  decide +kernel

theorem o_row_255 : oGrid.row evalE 255 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_255_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_255_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_255_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_255_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_255_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_255_2000).1 (bothLoop_sound b_255_2400).1))))))

theorem n_row_255 : nGrid.row evalE 255 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_255_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_255_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_255_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_255_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_255_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_255_2000).2 (bothLoop_sound b_255_2400).2))))))

theorem b_256_0 : bothSeg evalE (oGrid.idx 256) (oGrid.dm 256) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 256) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1969663851081441823111113160674182090718016160725701195301741977242033888098⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_256_400 : bothSeg evalE (oGrid.idx 256) (oGrid.dm 256) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 256) oGrid.kl oGrid.kr 400 400 ⟨false, 1969663851081441823111113160674182090718016160725701195301741977242033888098⟩ ⟨false, 0⟩ ⟨false, 3180005816834709866965402196642770456230083569031825866883208591667274521392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_256_800 : bothSeg evalE (oGrid.idx 256) (oGrid.dm 256) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 256) oGrid.kl oGrid.kr 400 800 ⟨false, 3180005816834709866965402196642770456230083569031825866883208591667274521392⟩ ⟨false, 0⟩ ⟨false, 3604431223215774082240369639359423100885016743624391751506719407168611160950⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_256_1200 : bothSeg evalE (oGrid.idx 256) (oGrid.dm 256) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 256) oGrid.kl oGrid.kr 400 1200 ⟨false, 3604431223215774082240369639359423100885016743624391751506719407168611160950⟩ ⟨false, 0⟩ ⟨false, 3612576997552544771110612797294264801604004565098553826290086899476607592988⟩ ⟨false, 34714937758242225196080433269119836019663765525513494113926341646530424570⟩ = true := by
  decide +kernel

theorem b_256_1600 : bothSeg evalE (oGrid.idx 256) (oGrid.dm 256) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 256) oGrid.kl oGrid.kr 400 1600 ⟨false, 3612576997552544771110612797294264801604004565098553826290086899476607592988⟩ ⟨false, 34714937758242225196080433269119836019663765525513494113926341646530424570⟩ ⟨false, 3455047393344666622342889604582123794388408536336556162874390365238271064876⟩ ⟨false, 192634569659743408885426127826230543349959591650824727596138356707399690996⟩ = true := by
  decide +kernel

theorem b_256_2000 : bothSeg evalE (oGrid.idx 256) (oGrid.dm 256) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 256) oGrid.kl oGrid.kr 400 2000 ⟨false, 3455047393344666622342889604582123794388408536336556162874390365238271064876⟩ ⟨false, 192634569659743408885426127826230543349959591650824727596138356707399690996⟩ ⟨false, 3435898430892235242093112686876739690615230246872627963310444446065080605460⟩ ⟨false, 214121491869747821374268357307189723880232119771220640868405396113201831470⟩ = true := by
  decide +kernel

theorem b_256_2400 : bothLoop evalE (oGrid.idx 256) (oGrid.dm 256) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 256) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3435898430892235242093112686876739690615230246872627963310444446065080605460⟩ ⟨false, 214121491869747821374268357307189723880232119771220640868405396113201831470⟩ = true := by
  decide +kernel

theorem o_row_256 : oGrid.row evalE 256 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_256_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_256_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_256_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_256_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_256_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_256_2000).1 (bothLoop_sound b_256_2400).1))))))

theorem n_row_256 : nGrid.row evalE 256 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_256_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_256_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_256_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_256_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_256_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_256_2000).2 (bothLoop_sound b_256_2400).2))))))

theorem b_257_0 : bothSeg evalE (oGrid.idx 257) (oGrid.dm 257) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 257) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1961434487128066101849574927277175840798075917551167748952903290622461842844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_257_400 : bothSeg evalE (oGrid.idx 257) (oGrid.dm 257) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 257) oGrid.kl oGrid.kr 400 400 ⟨false, 1961434487128066101849574927277175840798075917551167748952903290622461842844⟩ ⟨false, 0⟩ ⟨false, 3166593677453794041995784393555914652589022217992267524328197696465485984514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_257_800 : bothSeg evalE (oGrid.idx 257) (oGrid.dm 257) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 257) oGrid.kl oGrid.kr 400 800 ⟨false, 3166593677453794041995784393555914652589022217992267524328197696465485984514⟩ ⟨false, 0⟩ ⟨false, 3588878001079647991088924311953607597240927037457962191367217878462807292054⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_257_1200 : bothSeg evalE (oGrid.idx 257) (oGrid.dm 257) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 257) oGrid.kl oGrid.kr 400 1200 ⟨false, 3588878001079647991088924311953607597240927037457962191367217878462807292054⟩ ⟨false, 0⟩ ⟨false, 3596588219438308589620902365556107226723313443243291899455905525793662566162⟩ ⟨false, 34703757279908126259615584750442392929823555760931520388988357392974314228⟩ = true := by
  decide +kernel

theorem b_257_1600 : bothSeg evalE (oGrid.idx 257) (oGrid.dm 257) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 257) oGrid.kl oGrid.kr 400 1600 ⟨false, 3596588219438308589620902365556107226723313443243291899455905525793662566162⟩ ⟨false, 34703757279908126259615584750442392929823555760931520388988357392974314228⟩ ⟨false, 3439052002814049665501486999038698996888282576755659311755781951340133882756⟩ ⟨false, 192631050934465306054364137591971038451511897029961334718449776040633060276⟩ = true := by
  decide +kernel

theorem b_257_2000 : bothSeg evalE (oGrid.idx 257) (oGrid.dm 257) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 257) oGrid.kl oGrid.kr 400 2000 ⟨false, 3439052002814049665501486999038698996888282576755659311755781951340133882756⟩ ⟨false, 192631050934465306054364137591971038451511897029961334718449776040633060276⟩ ⟨false, 3420148461772809587054054824367976200333089436669992449487545225154644902306⟩ ⟨false, 213933655654532716629080993086523812634205231199961428104920904974706021390⟩ = true := by
  decide +kernel

theorem b_257_2400 : bothLoop evalE (oGrid.idx 257) (oGrid.dm 257) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 257) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3420148461772809587054054824367976200333089436669992449487545225154644902306⟩ ⟨false, 213933655654532716629080993086523812634205231199961428104920904974706021390⟩ = true := by
  decide +kernel

theorem o_row_257 : oGrid.row evalE 257 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_257_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_257_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_257_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_257_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_257_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_257_2000).1 (bothLoop_sound b_257_2400).1))))))

theorem n_row_257 : nGrid.row evalE 257 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_257_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_257_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_257_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_257_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_257_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_257_2000).2 (bothLoop_sound b_257_2400).2))))))

theorem b_258_0 : bothSeg evalE (oGrid.idx 258) (oGrid.dm 258) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 258) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1953231176582001653216768634634597722916287676549059012852822586487869858372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_258_400 : bothSeg evalE (oGrid.idx 258) (oGrid.dm 258) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 258) oGrid.kl oGrid.kr 400 400 ⟨false, 1953231176582001653216768634634597722916287676549059012852822586487869858372⟩ ⟨false, 0⟩ ⟨false, 3153222781655985482504675685792146439166800465063987317085521493331646814192⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_258_800 : bothSeg evalE (oGrid.idx 258) (oGrid.dm 258) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 258) oGrid.kl oGrid.kr 400 800 ⟨false, 3153222781655985482504675685792146439166800465063987317085521493331646814192⟩ ⟨false, 0⟩ ⟨false, 3573372007513177785334541391733061808460570357054753437866283068318225165438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_258_1200 : bothSeg evalE (oGrid.idx 258) (oGrid.dm 258) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 258) oGrid.kl oGrid.kr 400 1200 ⟨false, 3573372007513177785334541391733061808460570357054753437866283068318225165438⟩ ⟨false, 0⟩ ⟨false, 3580654179442771399584006460113877048130593623440187867743426130955416446594⟩ ⟨false, 34687518118013947362030800185385766266080165432091614122977772654594961728⟩ = true := by
  decide +kernel

theorem b_258_1600 : bothSeg evalE (oGrid.idx 258) (oGrid.dm 258) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 258) oGrid.kl oGrid.kr 400 1600 ⟨false, 3580654179442771399584006460113877048130593623440187867743426130955416446594⟩ ⟨false, 34687518118013947362030800185385766266080165432091614122977772654594961728⟩ ⟨false, 3423107017099641479917931161091496184696021325580373074068685990373405687256⟩ ⟨false, 192626770728747549248014905565986892130846917262197066675959178912090203020⟩ = true := by
  decide +kernel

theorem b_258_2000 : bothSeg evalE (oGrid.idx 258) (oGrid.dm 258) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 258) oGrid.kl oGrid.kr 400 2000 ⟨false, 3423107017099641479917931161091496184696021325580373074068685990373405687256⟩ ⟨false, 192626770728747549248014905565986892130846917262197066675959178912090203020⟩ ⟨false, 3404448789563268886239132339945621407022819010827887171920872377581115907942⟩ ⟨false, 213745945629289183914362239038058304174581965073569819117504550832554423538⟩ = true := by
  decide +kernel

theorem b_258_2400 : bothLoop evalE (oGrid.idx 258) (oGrid.dm 258) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 258) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3404448789563268886239132339945621407022819010827887171920872377581115907942⟩ ⟨false, 213745945629289183914362239038058304174581965073569819117504550832554423538⟩ = true := by
  decide +kernel

theorem o_row_258 : oGrid.row evalE 258 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_258_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_258_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_258_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_258_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_258_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_258_2000).1 (bothLoop_sound b_258_2400).1))))))

theorem n_row_258 : nGrid.row evalE 258 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_258_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_258_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_258_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_258_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_258_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_258_2000).2 (bothLoop_sound b_258_2400).2))))))

theorem b_259_0 : bothSeg evalE (oGrid.idx 259) (oGrid.dm 259) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 259) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1945053860939303875136448503333380151783215796990690038381130769137981143392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_259_400 : bothSeg evalE (oGrid.idx 259) (oGrid.dm 259) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 259) oGrid.kl oGrid.kr 400 400 ⟨false, 1945053860939303875136448503333380151783215796990690038381130769137981143392⟩ ⟨false, 0⟩ ⟨false, 3139893035186513946816237368384315847362276906320818969541460703583451477658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_259_800 : bothSeg evalE (oGrid.idx 259) (oGrid.dm 259) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 259) oGrid.kl oGrid.kr 400 800 ⟨false, 3139893035186513946816237368384315847362276906320818969541460703583451477658⟩ ⟨false, 0⟩ ⟨false, 3557913119543403615736467531552591935236423242861910266119926761954343059766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_259_1200 : bothSeg evalE (oGrid.idx 259) (oGrid.dm 259) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 259) oGrid.kl oGrid.kr 400 1200 ⟨false, 3557913119543403615736467531552591935236423242861910266119926761954343059766⟩ ⟨false, 0⟩ ⟨false, 3564774559722442552819570353015595483117639484255255877674370325239862485220⟩ ⟨false, 34666471136710516877666334135057759508528563741871764132749079678769106118⟩ = true := by
  decide +kernel

theorem b_259_1600 : bothSeg evalE (oGrid.idx 259) (oGrid.dm 259) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 259) oGrid.kl oGrid.kr 400 1600 ⟨false, 3564774559722442552819570353015595483117639484255255877674370325239862485220⟩ ⟨false, 34666471136710516877666334135057759508528563741871764132749079678769106118⟩ ⟨false, 3407212446280104043022844228489044354920150744193526935574954471982561978646⟩ ⟨false, 192621679973901245623676984218305003636967340600301170180468606478718529954⟩ = true := by
  decide +kernel

theorem b_259_2000 : bothSeg evalE (oGrid.idx 259) (oGrid.dm 259) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 259) oGrid.kl oGrid.kr 400 2000 ⟨false, 3407212446280104043022844228489044354920150744193526935574954471982561978646⟩ ⟨false, 192621679973901245623676984218305003636967340600301170180468606478718529954⟩ ⟨false, 3388799401305046254920517159305382929582904470591655482626549774534888189338⟩ ⟨false, 213558074456291710758813291003187546420966281030007294500348002625108597444⟩ = true := by
  decide +kernel

theorem b_259_2400 : bothLoop evalE (oGrid.idx 259) (oGrid.dm 259) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 259) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3388799401305046254920517159305382929582904470591655482626549774534888189338⟩ ⟨false, 213558074456291710758813291003187546420966281030007294500348002625108597444⟩ = true := by
  decide +kernel

theorem o_row_259 : oGrid.row evalE 259 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_259_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_259_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_259_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_259_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_259_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_259_2000).1 (bothLoop_sound b_259_2400).1))))))

theorem n_row_259 : nGrid.row evalE 259 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_259_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_259_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_259_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_259_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_259_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_259_2000).2 (bothLoop_sound b_259_2400).2))))))

theorem b_260_0 : bothSeg evalE (oGrid.idx 260) (oGrid.dm 260) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 260) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1936902444020009731634019419487983568101881236085287027049409392121652811968⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_260_400 : bothSeg evalE (oGrid.idx 260) (oGrid.dm 260) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 260) oGrid.kl oGrid.kr 400 400 ⟨false, 1936902444020009731634019419487983568101881236085287027049409392121652811968⟩ ⟨false, 0⟩ ⟨false, 3126604304493580528515604106270233774895196722486320956462581470240106571090⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_260_800 : bothSeg evalE (oGrid.idx 260) (oGrid.dm 260) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 260) oGrid.kl oGrid.kr 400 800 ⟨false, 3126604304493580528515604106270233774895196722486320956462581470240106571090⟩ ⟨false, 0⟩ ⟨false, 3542501239516005212087917082282362529543883250588917164959818898437917630484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_260_1200 : bothSeg evalE (oGrid.idx 260) (oGrid.dm 260) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 260) oGrid.kl oGrid.kr 400 1200 ⟨false, 3542501239516005212087917082282362529543883250588917164959818898437917630484⟩ ⟨false, 0⟩ ⟨false, 3548948955285971949706882854653726717356072488826213989083858567024380196126⟩ ⟨false, 34640914859150225527129838418056838681750917279615678106751804142855334122⟩ = true := by
  decide +kernel

theorem b_260_1600 : bothSeg evalE (oGrid.idx 260) (oGrid.dm 260) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 260) oGrid.kl oGrid.kr 400 1600 ⟨false, 3548948955285971949706882854653726717356072488826213989083858567024380196126⟩ ⟨false, 34640914859150225527129838418056838681750917279615678106751804142855334122⟩ ⟨false, 3391367985559503848342525052954755062434083162873999479309364092894063792288⟩ ⟨false, 192616095860352774887816928221281876794553449245922468911275302136247640838⟩ = true := by
  decide +kernel

theorem b_260_2000 : bothSeg evalE (oGrid.idx 260) (oGrid.dm 260) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 260) oGrid.kl oGrid.kr 400 2000 ⟨false, 3391367985559503848342525052954755062434083162873999479309364092894063792288⟩ ⟨false, 192616095860352774887816928221281876794553449245922468911275302136247640838⟩ ⟨false, 3373199960875313267759081911718358892916977699690449339203250419004434933636⟩ ⟨false, 213371108684415266926232889600243405002445677912322100834040827006337085432⟩ = true := by
  decide +kernel

theorem b_260_2400 : bothLoop evalE (oGrid.idx 260) (oGrid.dm 260) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 260) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3373199960875313267759081911718358892916977699690449339203250419004434933636⟩ ⟨false, 213371108684415266926232889600243405002445677912322100834040827006337085432⟩ = true := by
  decide +kernel

theorem o_row_260 : oGrid.row evalE 260 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_260_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_260_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_260_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_260_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_260_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_260_2000).1 (bothLoop_sound b_260_2400).1))))))

theorem n_row_260 : nGrid.row evalE 260 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_260_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_260_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_260_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_260_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_260_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_260_2000).2 (bothLoop_sound b_260_2400).2))))))

theorem b_261_0 : bothSeg evalE (oGrid.idx 261) (oGrid.dm 261) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 261) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1928776893212084061987310791053808069576001049727931516600861460583427557504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_261_400 : bothSeg evalE (oGrid.idx 261) (oGrid.dm 261) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 261) oGrid.kl oGrid.kr 400 400 ⟨false, 1928776893212084061987310791053808069576001049727931516600861460583427557504⟩ ⟨false, 0⟩ ⟨false, 3113356548829196641945365682551180396669435467857924999130306404099531627666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_261_800 : bothSeg evalE (oGrid.idx 261) (oGrid.dm 261) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 261) oGrid.kl oGrid.kr 400 800 ⟨false, 3113356548829196641945365682551180396669435467857924999130306404099531627666⟩ ⟨false, 0⟩ ⟨false, 3527136301783830508337565747345540880227909392743284359080791930834673294354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_261_1200 : bothSeg evalE (oGrid.idx 261) (oGrid.dm 261) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 261) oGrid.kl oGrid.kr 400 1200 ⟨false, 3527136301783830508337565747345540880227909392743284359080791930834673294354⟩ ⟨false, 0⟩ ⟨false, 3533177340310026002440372053292655424425823215523081535072148075519160187804⟩ ⟨false, 34610802068049586355598230401215701993447922687591310166787166905122262398⟩ = true := by
  decide +kernel

theorem b_261_1600 : bothSeg evalE (oGrid.idx 261) (oGrid.dm 261) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 261) oGrid.kl oGrid.kr 400 1600 ⟨false, 3533177340310026002440372053292655424425823215523081535072148075519160187804⟩ ⟨false, 34610802068049586355598230401215701993447922687591310166787166905122262398⟩ ⟨false, 3375573649584404089667276556285785618728107900059724515256472587161794653024⟩ ⟨false, 192609869807334469152530660003841678121308318097545774009946411697053253742⟩ = true := by
  decide +kernel

theorem b_261_2000 : bothSeg evalE (oGrid.idx 261) (oGrid.dm 261) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 261) oGrid.kl oGrid.kr 400 2000 ⟨false, 3375573649584404089667276556285785618728107900059724515256472587161794653024⟩ ⟨false, 192609869807334469152530660003841678121308318097545774009946411697053253742⟩ ⟨false, 3357650422144575389788875345256737541911073947419521771183365385183773145648⟩ ⟨false, 213184572974098845431665013904855229134171889910192356586079795776277276854⟩ = true := by
  decide +kernel

theorem b_261_2400 : bothLoop evalE (oGrid.idx 261) (oGrid.dm 261) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 261) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3357650422144575389788875345256737541911073947419521771183365385183773145648⟩ ⟨false, 213184572974098845431665013904855229134171889910192356586079795776277276854⟩ = true := by
  decide +kernel

theorem o_row_261 : oGrid.row evalE 261 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_261_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_261_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_261_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_261_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_261_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_261_2000).1 (bothLoop_sound b_261_2400).1))))))

theorem n_row_261 : nGrid.row evalE 261 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_261_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_261_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_261_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_261_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_261_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_261_2000).2 (bothLoop_sound b_261_2400).2))))))

theorem b_262_0 : bothSeg evalE (oGrid.idx 262) (oGrid.dm 262) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 262) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1920677134396467639248970562395908195735212831158253855445196064820579492802⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_262_400 : bothSeg evalE (oGrid.idx 262) (oGrid.dm 262) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 262) oGrid.kl oGrid.kr 400 400 ⟨false, 1920677134396467639248970562395908195735212831158253855445196064820579492802⟩ ⟨false, 0⟩ ⟨false, 3100149658871816865661766166542502053188198695327723079340881173161936144014⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_262_800 : bothSeg evalE (oGrid.idx 262) (oGrid.dm 262) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 262) oGrid.kl oGrid.kr 400 800 ⟨false, 3100149658871816865661766166542502053188198695327723079340881173161936144014⟩ ⟨false, 0⟩ ⟨false, 3511818163073408586774198734348205834630339157256885319994804993164784539762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_262_1200 : bothSeg evalE (oGrid.idx 262) (oGrid.dm 262) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 262) oGrid.kl oGrid.kr 400 1200 ⟨false, 3511818163073408586774198734348205834630339157256885319994804993164784539762⟩ ⟨false, 0⟩ ⟨false, 3517459351031458327598756218708206220259735968954078355249625383513602889774⟩ ⟨false, 34576482740931409104193987219603731046185807789197920379418021025597664158⟩ = true := by
  decide +kernel

theorem b_262_1600 : bothSeg evalE (oGrid.idx 262) (oGrid.dm 262) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 262) oGrid.kl oGrid.kr 400 1600 ⟨false, 3517459351031458327598756218708206220259735968954078355249625383513602889774⟩ ⟨false, 34576482740931409104193987219603731046185807789197920379418021025597664158⟩ ⟨false, 3359829475301464780204242568894472375155314839525232055855043575293622878118⟩ ⟨false, 192602890512718214525646264139271066945981852717538671696596910592926675808⟩ = true := by
  decide +kernel

theorem b_262_2000 : bothSeg evalE (oGrid.idx 262) (oGrid.dm 262) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 262) oGrid.kl oGrid.kr 400 2000 ⟨false, 3359829475301464780204242568894472375155314839525232055855043575293622878118⟩ ⟨false, 192602890512718214525646264139271066945981852717538671696596910592926675808⟩ ⟨false, 3342150826160327079598881017457822979520610028715969348249917633151395146268⟩ ⟨false, 212997868922570258084732888258142403990023436359993930517564530007315786846⟩ = true := by
  decide +kernel

theorem b_262_2400 : bothLoop evalE (oGrid.idx 262) (oGrid.dm 262) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 262) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3342150826160327079598881017457822979520610028715969348249917633151395146268⟩ ⟨false, 212997868922570258084732888258142403990023436359993930517564530007315786846⟩ = true := by
  decide +kernel

theorem o_row_262 : oGrid.row evalE 262 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_262_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_262_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_262_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_262_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_262_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_262_2000).1 (bothLoop_sound b_262_2400).1))))))

theorem n_row_262 : nGrid.row evalE 262 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_262_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_262_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_262_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_262_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_262_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_262_2000).2 (bothLoop_sound b_262_2400).2))))))

theorem b_263_0 : bothSeg evalE (oGrid.idx 263) (oGrid.dm 263) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 263) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1912603085638503652747550617684009622774745854899616284917781740276744388266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_263_400 : bothSeg evalE (oGrid.idx 263) (oGrid.dm 263) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 263) oGrid.kl oGrid.kr 400 400 ⟨false, 1912603085638503652747550617684009622774745854899616284917781740276744388266⟩ ⟨false, 0⟩ ⟨false, 3086983524299715536148752995755630346957168008632923563034330346004769841354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_263_800 : bothSeg evalE (oGrid.idx 263) (oGrid.dm 263) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 263) oGrid.kl oGrid.kr 400 800 ⟨false, 3086983524299715536148752995755630346957168008632923563034330346004769841354⟩ ⟨false, 0⟩ ⟨false, 3496546748529335753246401329962457790042855144126410320993644997153603290452⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_263_1200 : bothSeg evalE (oGrid.idx 263) (oGrid.dm 263) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 263) oGrid.kl oGrid.kr 400 1200 ⟨false, 3496546748529335753246401329962457790042855144126410320993644997153603290452⟩ ⟨false, 0⟩ ⟨false, 3501794824765551852682486529886434573852355356707859928276600449921486426518⟩ ⟨false, 34537877255806266677853964439221170944682315295198122875449009552128775808⟩ = true := by
  decide +kernel

theorem b_263_1600 : bothSeg evalE (oGrid.idx 263) (oGrid.dm 263) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 263) oGrid.kl oGrid.kr 400 1600 ⟨false, 3501794824765551852682486529886434573852355356707859928276600449921486426518⟩ ⟨false, 34537877255806266677853964439221170944682315295198122875449009552128775808⟩ ⟨false, 3344135284375160840407004472718198157771215624888769090280281968693265159788⟩ ⟨false, 192595146558068893460511342632643835310730351954907374732420296216799201976⟩ = true := by
  decide +kernel

theorem b_263_2000 : bothSeg evalE (oGrid.idx 263) (oGrid.dm 263) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 263) oGrid.kl oGrid.kr 400 2000 ⟨false, 3344135284375160840407004472718198157771215624888769090280281968693265159788⟩ ⟨false, 192595146558068893460511342632643835310730351954907374732420296216799201976⟩ ⟨false, 3326700948194746919485849251551427822830860627872350358367793746126679671634⟩ ⟨false, 212811613608945677617642534750559448208029182524764834562888698293297875210⟩ = true := by
  decide +kernel

theorem b_263_2400 : bothLoop evalE (oGrid.idx 263) (oGrid.dm 263) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 263) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 3326700948194746919485849251551427822830860627872350358367793746126679671634⟩ ⟨false, 212811613608945677617642534750559448208029182524764834562888698293297875210⟩ = true := by
  decide +kernel

theorem o_row_263 : oGrid.row evalE 263 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_263_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_263_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_263_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_263_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_263_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_263_2000).1 (bothLoop_sound b_263_2400).1))))))

theorem n_row_263 : nGrid.row evalE 263 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_263_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_263_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_263_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_263_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_263_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_263_2000).2 (bothLoop_sound b_263_2400).2))))))

theorem o_blk_240 : allFrom (fun j => oGrid.row evalE j) 240 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 240) o_row_240 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 241) o_row_241 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 242) o_row_242 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 243) o_row_243 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 244) o_row_244 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 245) o_row_245 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 246) o_row_246 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 247) o_row_247 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 248) o_row_248 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 249) o_row_249 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 250) o_row_250 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 251) o_row_251 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 252) o_row_252 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 253) o_row_253 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 254) o_row_254 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 255) o_row_255 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 256) o_row_256 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 257) o_row_257 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 258) o_row_258 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 259) o_row_259 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 260) o_row_260 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 261) o_row_261 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 262) o_row_262 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 263) o_row_263 (allFrom_zero (fun j => oGrid.row evalE j) 264)))))))))))))))))))))))))

theorem n_blk_240 : allFrom (fun j => nGrid.row evalE j) 240 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 240) n_row_240 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 241) n_row_241 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 242) n_row_242 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 243) n_row_243 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 244) n_row_244 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 245) n_row_245 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 246) n_row_246 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 247) n_row_247 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 248) n_row_248 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 249) n_row_249 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 250) n_row_250 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 251) n_row_251 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 252) n_row_252 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 253) n_row_253 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 254) n_row_254 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 255) n_row_255 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 256) n_row_256 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 257) n_row_257 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 258) n_row_258 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 259) n_row_259 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 260) n_row_260 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 261) n_row_261 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 262) n_row_262 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 263) n_row_263 (allFrom_zero (fun j => nGrid.row evalE j) 264)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
