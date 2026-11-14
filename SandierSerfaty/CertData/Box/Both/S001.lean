/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 1 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `24`–`47`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_24_0 : bothSeg evalE (oGrid.idx 24) (oGrid.dm 24) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 24) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4753492480355323163801399611886700364627854016138289169533266280345209789578⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_24_400 : bothSeg evalE (oGrid.idx 24) (oGrid.dm 24) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 24) oGrid.kl oGrid.kr 400 400 ⟨false, 4753492480355323163801399611886700364627854016138289169533266280345209789578⟩ ⟨false, 0⟩ ⟨false, 7640986476917258239833709065288116055849952220176147523613242040820843292444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_24_800 : bothSeg evalE (oGrid.idx 24) (oGrid.dm 24) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 24) oGrid.kl oGrid.kr 400 800 ⟨false, 7640986476917258239833709065288116055849952220176147523613242040820843292444⟩ ⟨false, 0⟩ ⟨false, 8731252266664570579784371072529527248943338771303198255160920661244727948334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_24_1200 : bothSeg evalE (oGrid.idx 24) (oGrid.dm 24) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 24) oGrid.kl oGrid.kr 400 1200 ⟨false, 8731252266664570579784371072529527248943338771303198255160920661244727948334⟩ ⟨false, 0⟩ ⟨false, 8944011852605029093040449603666337525716036819659178613750726558787049425234⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_24_1600 : bothSeg evalE (oGrid.idx 24) (oGrid.dm 24) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 24) oGrid.kl oGrid.kr 400 1600 ⟨false, 8944011852605029093040449603666337525716036819659178613750726558787049425234⟩ ⟨false, 0⟩ ⟨false, 8780944941828745708572525708379328408965272623194962661120472024501518687848⟩ ⟨false, 165270078428333934890910362621620144606500047391487164520946326443473992934⟩ = true := by
  decide +kernel

theorem b_24_2000 : bothSeg evalE (oGrid.idx 24) (oGrid.dm 24) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 24) oGrid.kl oGrid.kr 400 2000 ⟨false, 8780944941828745708572525708379328408965272623194962661120472024501518687848⟩ ⟨false, 165270078428333934890910362621620144606500047391487164520946326443473992934⟩ ⟨false, 8686633282969910439646529479051349767595100261440557204552683049470670276842⟩ ⟨false, 260041446067653243878695626455386402839274582216628229925574853575319610058⟩ = true := by
  decide +kernel

theorem b_24_2400 : bothLoop evalE (oGrid.idx 24) (oGrid.dm 24) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 24) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8686633282969910439646529479051349767595100261440557204552683049470670276842⟩ ⟨false, 260041446067653243878695626455386402839274582216628229925574853575319610058⟩ = true := by
  decide +kernel

theorem o_row_24 : oGrid.row evalE 24 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_24_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_24_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_24_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_24_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_24_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_24_2000).1 (bothLoop_sound b_24_2400).1))))))

theorem n_row_24 : nGrid.row evalE 24 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_24_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_24_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_24_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_24_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_24_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_24_2000).2 (bothLoop_sound b_24_2400).2))))))

theorem b_25_0 : bothSeg evalE (oGrid.idx 25) (oGrid.dm 25) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 25) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4736898008465566285284465591147411348082561416428509510247604559245919277606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_25_400 : bothSeg evalE (oGrid.idx 25) (oGrid.dm 25) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 25) oGrid.kl oGrid.kr 400 400 ⟨false, 4736898008465566285284465591147411348082561416428509510247604559245919277606⟩ ⟨false, 0⟩ ⟨false, 7614851670076946709632497666031821940008670682617594346825065129535348355092⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_25_800 : bothSeg evalE (oGrid.idx 25) (oGrid.dm 25) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 25) oGrid.kl oGrid.kr 400 800 ⟨false, 7614851670076946709632497666031821940008670682617594346825065129535348355092⟩ ⟨false, 0⟩ ⟨false, 8701515427313405182058674718984779423062341143599610010524115643578150279902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_25_1200 : bothSeg evalE (oGrid.idx 25) (oGrid.dm 25) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 25) oGrid.kl oGrid.kr 400 1200 ⟨false, 8701515427313405182058674718984779423062341143599610010524115643578150279902⟩ ⟨false, 0⟩ ⟨false, 8913306150989136543380130031314353692919921308209911386913107819141327099922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_25_1600 : bothSeg evalE (oGrid.idx 25) (oGrid.dm 25) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 25) oGrid.kl oGrid.kr 400 1600 ⟨false, 8913306150989136543380130031314353692919921308209911386913107819141327099922⟩ ⟨false, 0⟩ ⟨false, 8749909173900629946768353879582455657596384803978828719221299817761447378640⟩ ⟨false, 165547423687303126292340029095387146768906354923868739396621290442465486638⟩ = true := by
  decide +kernel

theorem b_25_2000 : bothSeg evalE (oGrid.idx 25) (oGrid.dm 25) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 25) oGrid.kl oGrid.kr 400 2000 ⟨false, 8749909173900629946768353879582455657596384803978828719221299817761447378640⟩ ⟨false, 165547423687303126292340029095387146768906354923868739396621290442465486638⟩ ⟨false, 8656132711591294694660144208440300694814098232562526852668583605598777406360⟩ ⟨false, 259791560168960405638253913155717027442395079965153724873035060128306149010⟩ = true := by
  decide +kernel

theorem b_25_2400 : bothLoop evalE (oGrid.idx 25) (oGrid.dm 25) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 25) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8656132711591294694660144208440300694814098232562526852668583605598777406360⟩ ⟨false, 259791560168960405638253913155717027442395079965153724873035060128306149010⟩ = true := by
  decide +kernel

theorem o_row_25 : oGrid.row evalE 25 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_25_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_25_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_25_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_25_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_25_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_25_2000).1 (bothLoop_sound b_25_2400).1))))))

theorem n_row_25 : nGrid.row evalE 25 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_25_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_25_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_25_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_25_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_25_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_25_2000).2 (bothLoop_sound b_25_2400).2))))))

theorem b_26_0 : bothSeg evalE (oGrid.idx 26) (oGrid.dm 26) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 26) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4720352097525200152897671147921006598774276419638982377512617002362103509828⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_26_400 : bothSeg evalE (oGrid.idx 26) (oGrid.dm 26) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 26) oGrid.kl oGrid.kr 400 400 ⟨false, 4720352097525200152897671147921006598774276419638982377512617002362103509828⟩ ⟨false, 0⟩ ⟨false, 7588787797655082040034047386821552178967083264757111097184467451197497207562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_26_800 : bothSeg evalE (oGrid.idx 26) (oGrid.dm 26) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 26) oGrid.kl oGrid.kr 400 800 ⟨false, 7588787797655082040034047386821552178967083264757111097184467451197497207562⟩ ⟨false, 0⟩ ⟨false, 8671855729935631862702334187664440985919713095377044033436267867023092585142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_26_1200 : bothSeg evalE (oGrid.idx 26) (oGrid.dm 26) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 26) oGrid.kl oGrid.kr 400 1200 ⟨false, 8671855729935631862702334187664440985919713095377044033436267867023092585142⟩ ⟨false, 0⟩ ⟨false, 8882679128561302962598611986254397693736350300540590460937547626741575792444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_26_1600 : bothSeg evalE (oGrid.idx 26) (oGrid.dm 26) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 26) oGrid.kl oGrid.kr 400 1600 ⟨false, 8882679128561302962598611986254397693736350300540590460937547626741575792444⟩ ⟨false, 0⟩ ⟨false, 8718954485842272732904549683610755030735758349675481199745890809147904863120⟩ ⟨false, 165823935600101162884212119745628438616623515938979905807364800948220039954⟩ = true := by
  decide +kernel

theorem b_26_2000 : bothSeg evalE (oGrid.idx 26) (oGrid.dm 26) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 26) oGrid.kl oGrid.kr 400 2000 ⟨false, 8718954485842272732904549683610755030735758349675481199745890809147904863120⟩ ⟨false, 165823935600101162884212119745628438616623515938979905807364800948220039954⟩ ⟨false, 8625710940220406171530134773685607756963597394625185262764956539404195810842⟩ ⟨false, 259542997381391980027168794372819578949435122658501946797444896121699402814⟩ = true := by
  decide +kernel

theorem b_26_2400 : bothLoop evalE (oGrid.idx 26) (oGrid.dm 26) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 26) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8625710940220406171530134773685607756963597394625185262764956539404195810842⟩ ⟨false, 259542997381391980027168794372819578949435122658501946797444896121699402814⟩ = true := by
  decide +kernel

theorem o_row_26 : oGrid.row evalE 26 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_26_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_26_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_26_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_26_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_26_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_26_2000).1 (bothLoop_sound b_26_2400).1))))))

theorem n_row_26 : nGrid.row evalE 26 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_26_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_26_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_26_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_26_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_26_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_26_2000).2 (bothLoop_sound b_26_2400).2))))))

theorem b_27_0 : bothSeg evalE (oGrid.idx 27) (oGrid.dm 27) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 27) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4703854552263956112587453552817338943723924277976129058954083842246100776308⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_27_400 : bothSeg evalE (oGrid.idx 27) (oGrid.dm 27) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 27) oGrid.kl oGrid.kr 400 400 ⟨false, 4703854552263956112587453552817338943723924277976129058954083842246100776308⟩ ⟨false, 0⟩ ⟨false, 7562794751037919945048955878071734277388888567968264398098876618279704705544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_27_800 : bothSeg evalE (oGrid.idx 27) (oGrid.dm 27) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 27) oGrid.kl oGrid.kr 400 800 ⟨false, 7562794751037919945048955878071734277388888567968264398098876618279704705544⟩ ⟨false, 0⟩ ⟨false, 8642273042290492020856381105039037032834692133631375432181523221636322379552⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_27_1200 : bothSeg evalE (oGrid.idx 27) (oGrid.dm 27) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 27) oGrid.kl oGrid.kr 400 1200 ⟨false, 8642273042290492020856381105039037032834692133631375432181523221636322379552⟩ ⟨false, 0⟩ ⟨false, 8852130700901478817182608517231881853330739818531068558872827919187470177044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_27_1600 : bothSeg evalE (oGrid.idx 27) (oGrid.dm 27) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 27) oGrid.kl oGrid.kr 400 1600 ⟨false, 8852130700901478817182608517231881853330739818531068558872827919187470177044⟩ ⟨false, 0⟩ ⟨false, 8688080747482422896495564139744047849734766483975552023238297050267309576696⟩ ⟨false, 166097980310251874014062966037449775307006573400714819961680811714284060824⟩ = true := by
  decide +kernel

theorem b_27_2000 : bothSeg evalE (oGrid.idx 27) (oGrid.dm 27) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 27) oGrid.kl oGrid.kr 400 2000 ⟨false, 8688080747482422896495564139744047849734766483975552023238297050267309576696⟩ ⟨false, 166097980310251874014062966037449775307006573400714819961680811714284060824⟩ ⟨false, 8595367865896874840973520974425991217324347007282357112492812373154808217948⟩ ⟨false, 259294165786349654044476034267493246150553781436056994762303722963599437168⟩ = true := by
  decide +kernel

theorem b_27_2400 : bothLoop evalE (oGrid.idx 27) (oGrid.dm 27) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 27) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8595367865896874840973520974425991217324347007282357112492812373154808217948⟩ ⟨false, 259294165786349654044476034267493246150553781436056994762303722963599437168⟩ = true := by
  decide +kernel

theorem o_row_27 : oGrid.row evalE 27 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_27_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_27_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_27_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_27_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_27_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_27_2000).1 (bothLoop_sound b_27_2400).1))))))

theorem n_row_27 : nGrid.row evalE 27 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_27_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_27_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_27_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_27_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_27_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_27_2000).2 (bothLoop_sound b_27_2400).2))))))

theorem b_28_0 : bothSeg evalE (oGrid.idx 28) (oGrid.dm 28) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 28) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4687405206766001084338667310624164364183287971451171448943959597593043417194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_28_400 : bothSeg evalE (oGrid.idx 28) (oGrid.dm 28) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 28) oGrid.kl oGrid.kr 400 400 ⟨false, 4687405206766001084338667310624164364183287971451171448943959597593043417194⟩ ⟨false, 0⟩ ⟨false, 7536872354838548516979355096102584104304488576141253031464361646693523940988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_28_800 : bothSeg evalE (oGrid.idx 28) (oGrid.dm 28) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 28) oGrid.kl oGrid.kr 400 800 ⟨false, 7536872354838548516979355096102584104304488576141253031464361646693523940988⟩ ⟨false, 0⟩ ⟨false, 8612767203322164182392463372303496710289500683362894422904286707221670477512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_28_1200 : bothSeg evalE (oGrid.idx 28) (oGrid.dm 28) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 28) oGrid.kl oGrid.kr 400 1200 ⟨false, 8612767203322164182392463372303496710289500683362894422904286707221670477512⟩ ⟨false, 0⟩ ⟨false, 8821660662675199455447064180729728314385318729873605439917268045227259206488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_28_1600 : bothSeg evalE (oGrid.idx 28) (oGrid.dm 28) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 28) oGrid.kl oGrid.kr 400 1600 ⟨false, 8821660662675199455447064180729728314385318729873605439917268045227259206488⟩ ⟨false, 0⟩ ⟨false, 8657287845826375794092124535573987997966868509927563277517665962857380505634⟩ ⟨false, 166369692911857645392071832327061259310151597685801818466310775540326111514⟩ = true := by
  decide +kernel

theorem b_28_2000 : bothSeg evalE (oGrid.idx 28) (oGrid.dm 28) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 28) oGrid.kl oGrid.kr 400 2000 ⟨false, 8657287845826375794092124535573987997966868509927563277517665962857380505634⟩ ⟨false, 166369692911857645392071832327061259310151597685801818466310775540326111514⟩ ⟨false, 8565103371141956731129363403784630866247163023298990356205800419602837116578⟩ ⟨false, 259045186363467511976191382086478641139829194238328353722166905851564380892⟩ = true := by
  decide +kernel

theorem b_28_2400 : bothLoop evalE (oGrid.idx 28) (oGrid.dm 28) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 28) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8565103371141956731129363403784630866247163023298990356205800419602837116578⟩ ⟨false, 259045186363467511976191382086478641139829194238328353722166905851564380892⟩ = true := by
  decide +kernel

theorem o_row_28 : oGrid.row evalE 28 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_28_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_28_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_28_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_28_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_28_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_28_2000).1 (bothLoop_sound b_28_2400).1))))))

theorem n_row_28 : nGrid.row evalE 28 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_28_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_28_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_28_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_28_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_28_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_28_2000).2 (bothLoop_sound b_28_2400).2))))))

theorem b_29_0 : bothSeg evalE (oGrid.idx 29) (oGrid.dm 29) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 29) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4671004040989165471646992690610644402418482862663511507743032206712241021960⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_29_400 : bothSeg evalE (oGrid.idx 29) (oGrid.dm 29) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 29) oGrid.kl oGrid.kr 400 400 ⟨false, 4671004040989165471646992690610644402418482862663511507743032206712241021960⟩ ⟨false, 0⟩ ⟨false, 7511020527728384700554855689371827292339013005850038955653546704087006656548⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_29_800 : bothSeg evalE (oGrid.idx 29) (oGrid.dm 29) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 29) oGrid.kl oGrid.kr 400 800 ⟨false, 7511020527728384700554855689371827292339013005850038955653546704087006656548⟩ ⟨false, 0⟩ ⟨false, 8583338153339446566254271958204345147120123044821751548553761960518688878916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_29_1200 : bothSeg evalE (oGrid.idx 29) (oGrid.dm 29) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 29) oGrid.kl oGrid.kr 400 1200 ⟨false, 8583338153339446566254271958204345147120123044821751548553761960518688878916⟩ ⟨false, 0⟩ ⟨false, 8791268995662948383117607517020105073841970832453159393271410149639278962182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_29_1600 : bothSeg evalE (oGrid.idx 29) (oGrid.dm 29) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 29) oGrid.kl oGrid.kr 400 1600 ⟨false, 8791268995662948383117607517020105073841970832453159393271410149639278962182⟩ ⟨false, 0⟩ ⟨false, 8626575770136288188170185939219989514234589064631903010262843966777994674240⟩ ⟨false, 166640257790635214609806823772409252601536814750102316480188010913066448392⟩ = true := by
  decide +kernel

theorem b_29_2000 : bothSeg evalE (oGrid.idx 29) (oGrid.dm 29) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 29) oGrid.kl oGrid.kr 400 2000 ⟨false, 8626575770136288188170185939219989514234589064631903010262843966777994674240⟩ ⟨false, 166640257790635214609806823772409252601536814750102316480188010913066448392⟩ ⟨false, 8534917396174443275088811299202213896537452480713429237535637340993277449404⟩ ⟨false, 258797255257670494656436918277033159699965447456111717920213402268909192478⟩ = true := by
  decide +kernel

theorem b_29_2400 : bothLoop evalE (oGrid.idx 29) (oGrid.dm 29) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 29) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8534917396174443275088811299202213896537452480713429237535637340993277449404⟩ ⟨false, 258797255257670494656436918277033159699965447456111717920213402268909192478⟩ = true := by
  decide +kernel

theorem o_row_29 : oGrid.row evalE 29 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_29_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_29_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_29_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_29_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_29_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_29_2000).1 (bothLoop_sound b_29_2400).1))))))

theorem n_row_29 : nGrid.row evalE 29 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_29_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_29_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_29_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_29_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_29_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_29_2000).2 (bothLoop_sound b_29_2400).2))))))

theorem b_30_0 : bothSeg evalE (oGrid.idx 30) (oGrid.dm 30) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 30) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4654650895713907971744887336240355558756931037058016147665814816209106407816⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_30_400 : bothSeg evalE (oGrid.idx 30) (oGrid.dm 30) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 30) oGrid.kl oGrid.kr 400 400 ⟨false, 4654650895713907971744887336240355558756931037058016147665814816209106407816⟩ ⟨false, 0⟩ ⟨false, 7485239028538318259599846597883760633405777680066921991946148275315210255074⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_30_800 : bothSeg evalE (oGrid.idx 30) (oGrid.dm 30) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 30) oGrid.kl oGrid.kr 400 800 ⟨false, 7485239028538318259599846597883760633405777680066921991946148275315210255074⟩ ⟨false, 0⟩ ⟨false, 8553985630010107946875627027150591452889644519106831704921205067439197449250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_30_1200 : bothSeg evalE (oGrid.idx 30) (oGrid.dm 30) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 30) oGrid.kl oGrid.kr 400 1200 ⟨false, 8553985630010107946875627027150591452889644519106831704921205067439197449250⟩ ⟨false, 0⟩ ⟨false, 8760955428061159449135682770162955070389888523230492488346726991016472220144⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_30_1600 : bothSeg evalE (oGrid.idx 30) (oGrid.dm 30) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 30) oGrid.kl oGrid.kr 400 1600 ⟨false, 8760955428061159449135682770162955070389888523230492488346726991016472220144⟩ ⟨false, 0⟩ ⟨false, 8595944303035817264885886652674643448458798283404491319511490820079585365762⟩ ⟨false, 166909288669365578802488392309644096332706769715380000393974963624342928484⟩ = true := by
  decide +kernel

theorem b_30_2000 : bothSeg evalE (oGrid.idx 30) (oGrid.dm 30) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 30) oGrid.kl oGrid.kr 400 2000 ⟨false, 8595944303035817264885886652674643448458798283404491319511490820079585365762⟩ ⟨false, 166909288669365578802488392309644096332706769715380000393974963624342928484⟩ ⟨false, 8504809733131505855373481026227060028472788086443555563463535062572533530360⟩ ⟨false, 258550009480852933413872897751974968192670438010676260484148286313846308242⟩ = true := by
  decide +kernel

theorem b_30_2400 : bothLoop evalE (oGrid.idx 30) (oGrid.dm 30) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 30) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8504809733131505855373481026227060028472788086443555563463535062572533530360⟩ ⟨false, 258550009480852933413872897751974968192670438010676260484148286313846308242⟩ = true := by
  decide +kernel

theorem o_row_30 : oGrid.row evalE 30 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_30_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_30_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_30_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_30_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_30_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_30_2000).1 (bothLoop_sound b_30_2400).1))))))

theorem n_row_30 : nGrid.row evalE 30 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_30_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_30_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_30_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_30_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_30_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_30_2000).2 (bothLoop_sound b_30_2400).2))))))

theorem b_31_0 : bothSeg evalE (oGrid.idx 31) (oGrid.dm 31) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 31) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4638345533824786352458091104810666955571987728761277745191676452287350773252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_31_400 : bothSeg evalE (oGrid.idx 31) (oGrid.dm 31) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 31) oGrid.kl oGrid.kr 400 400 ⟨false, 4638345533824786352458091104810666955571987728761277745191676452287350773252⟩ ⟨false, 0⟩ ⟨false, 7459527723929474152495451633631869324963568313896972925237105407743002897470⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_31_800 : bothSeg evalE (oGrid.idx 31) (oGrid.dm 31) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 31) oGrid.kl oGrid.kr 400 800 ⟨false, 7459527723929474152495451633631869324963568313896972925237105407743002897470⟩ ⟨false, 0⟩ ⟨false, 8524709509721846622369648157654263263899809327569958011712188997065232039570⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_31_1200 : bothSeg evalE (oGrid.idx 31) (oGrid.dm 31) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 31) oGrid.kl oGrid.kr 400 1200 ⟨false, 8524709509721846622369648157654263263899809327569958011712188997065232039570⟩ ⟨false, 0⟩ ⟨false, 8730719849652270251750694271237167934278618431583573127361374186094137699244⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_31_1600 : bothSeg evalE (oGrid.idx 31) (oGrid.dm 31) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 31) oGrid.kl oGrid.kr 400 1600 ⟨false, 8730719849652270251750694271237167934278618431583573127361374186094137699244⟩ ⟨false, 0⟩ ⟨false, 8565393329808311374418217854324646245768916710046075192934316712870470632236⟩ ⟨false, 167175862173674883254550523444641124330121061083748942449712068936318529958⟩ = true := by
  decide +kernel

theorem b_31_2000 : bothSeg evalE (oGrid.idx 31) (oGrid.dm 31) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 31) oGrid.kl oGrid.kr 400 2000 ⟨false, 8565393329808311374418217854324646245768916710046075192934316712870470632236⟩ ⟨false, 167175862173674883254550523444641124330121061083748942449712068936318529958⟩ ⟨false, 8474780350632683546706966312555131454319245241586587634638568489662327993166⟩ ⟨false, 258302359149781303700993394656437049896184184746432328236351083660720741558⟩ = true := by
  decide +kernel

theorem b_31_2400 : bothLoop evalE (oGrid.idx 31) (oGrid.dm 31) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 31) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8474780350632683546706966312555131454319245241586587634638568489662327993166⟩ ⟨false, 258302359149781303700993394656437049896184184746432328236351083660720741558⟩ = true := by
  decide +kernel

theorem o_row_31 : oGrid.row evalE 31 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_31_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_31_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_31_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_31_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_31_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_31_2000).1 (bothLoop_sound b_31_2400).1))))))

theorem n_row_31 : nGrid.row evalE 31 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_31_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_31_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_31_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_31_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_31_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_31_2000).2 (bothLoop_sound b_31_2400).2))))))

theorem b_32_0 : bothSeg evalE (oGrid.idx 32) (oGrid.dm 32) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 32) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4622087849868427778958684320954244084475491588718112271882538227696934669178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_32_400 : bothSeg evalE (oGrid.idx 32) (oGrid.dm 32) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 32) oGrid.kl oGrid.kr 400 400 ⟨false, 4622087849868427778958684320954244084475491588718112271882538227696934669178⟩ ⟨false, 0⟩ ⟨false, 7433886325001773545070121855162274209080529693126816599298805368227034114934⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_32_800 : bothSeg evalE (oGrid.idx 32) (oGrid.dm 32) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 32) oGrid.kl oGrid.kr 400 800 ⟨false, 7433886325001773545070121855162274209080529693126816599298805368227034114934⟩ ⟨false, 0⟩ ⟨false, 8495509524838668243037714148531939274942443021337223820367002085301439829504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_32_1200 : bothSeg evalE (oGrid.idx 32) (oGrid.dm 32) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 32) oGrid.kl oGrid.kr 400 1200 ⟨false, 8495509524838668243037714148531939274942443021337223820367002085301439829504⟩ ⟨false, 0⟩ ⟨false, 8700561991190289583753934560632087458303568445133120045747548975207071109418⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_32_1600 : bothSeg evalE (oGrid.idx 32) (oGrid.dm 32) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 32) oGrid.kl oGrid.kr 400 1600 ⟨false, 8700561991190289583753934560632087458303568445133120045747548975207071109418⟩ ⟨false, 0⟩ ⟨false, 8534922285653262948732791764101125091384491848593185871169701452532914261290⟩ ⟨false, 167441016967676496442381300839709978241969021382139371646471105561188211192⟩ = true := by
  decide +kernel

theorem b_32_2000 : bothSeg evalE (oGrid.idx 32) (oGrid.dm 32) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 32) oGrid.kl oGrid.kr 400 2000 ⟨false, 8534922285653262948732791764101125091384491848593185871169701452532914261290⟩ ⟨false, 167441016967676496442381300839709978241969021382139371646471105561188211192⟩ ⟨false, 8444828639421175680177121057985167207389662346513412207540239618086472817750⟩ ⟨false, 258055527331615484478638639336655984607996393858701018553693753590415015932⟩ = true := by
  decide +kernel

theorem b_32_2400 : bothLoop evalE (oGrid.idx 32) (oGrid.dm 32) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 32) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8444828639421175680177121057985167207389662346513412207540239618086472817750⟩ ⟨false, 258055527331615484478638639336655984607996393858701018553693753590415015932⟩ = true := by
  decide +kernel

theorem o_row_32 : oGrid.row evalE 32 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_32_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_32_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_32_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_32_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_32_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_32_2000).1 (bothLoop_sound b_32_2400).1))))))

theorem n_row_32 : nGrid.row evalE 32 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_32_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_32_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_32_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_32_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_32_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_32_2000).2 (bothLoop_sound b_32_2400).2))))))

theorem b_33_0 : bothSeg evalE (oGrid.idx 33) (oGrid.dm 33) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 33) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4605877798726145276287471442851017681201695953601445748805682862626455481228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_33_400 : bothSeg evalE (oGrid.idx 33) (oGrid.dm 33) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 33) oGrid.kl oGrid.kr 400 400 ⟨false, 4605877798726145276287471442851017681201695953601445748805682862626455481228⟩ ⟨false, 0⟩ ⟨false, 7408314807314775652651382636094883924364147158105647990687932966257024498274⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_33_800 : bothSeg evalE (oGrid.idx 33) (oGrid.dm 33) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 33) oGrid.kl oGrid.kr 400 800 ⟨false, 7408314807314775652651382636094883924364147158105647990687932966257024498274⟩ ⟨false, 0⟩ ⟨false, 8466385645815735692602872372732859605712904042413825991459245876326042152710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_33_1200 : bothSeg evalE (oGrid.idx 33) (oGrid.dm 33) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 33) oGrid.kl oGrid.kr 400 1200 ⟨false, 8466385645815735692602872372732859605712904042413825991459245876326042152710⟩ ⟨false, 0⟩ ⟨false, 8670481820131673084328551984234928134439714377522528985582779451118946352786⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_33_1600 : bothSeg evalE (oGrid.idx 33) (oGrid.dm 33) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 33) oGrid.kl oGrid.kr 400 1600 ⟨false, 8670481820131673084328551984234928134439714377522528985582779451118946352786⟩ ⟨false, 0⟩ ⟨false, 8504531290204855739412229529017081313197139811535365701132080136725025912068⟩ ⟨false, 167704602725715449237354622167347246039574648681749257984775163842096470970⟩ = true := by
  decide +kernel

theorem b_33_2000 : bothSeg evalE (oGrid.idx 33) (oGrid.dm 33) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 33) oGrid.kl oGrid.kr 400 2000 ⟨false, 8504531290204855739412229529017081313197139811535365701132080136725025912068⟩ ⟨false, 167704602725715449237354622167347246039574648681749257984775163842096470970⟩ ⟨false, 8414954693545354452384389813899283418926432368041822762577400225933542536552⟩ ⟨false, 257809211002182984090967955841626724437800601771101975110355192811071073872⟩ = true := by
  decide +kernel

theorem b_33_2400 : bothLoop evalE (oGrid.idx 33) (oGrid.dm 33) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 33) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8414954693545354452384389813899283418926432368041822762577400225933542536552⟩ ⟨false, 257809211002182984090967955841626724437800601771101975110355192811071073872⟩ = true := by
  decide +kernel

theorem o_row_33 : oGrid.row evalE 33 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_33_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_33_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_33_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_33_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_33_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_33_2000).1 (bothLoop_sound b_33_2400).1))))))

theorem n_row_33 : nGrid.row evalE 33 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_33_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_33_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_33_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_33_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_33_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_33_2000).2 (bothLoop_sound b_33_2400).2))))))

theorem b_34_0 : bothSeg evalE (oGrid.idx 34) (oGrid.dm 34) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 34) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4589715154695903529900150121632672154466759601178810460979384223891393948252⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_34_400 : bothSeg evalE (oGrid.idx 34) (oGrid.dm 34) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 34) oGrid.kl oGrid.kr 400 400 ⟨false, 4589715154695903529900150121632672154466759601178810460979384223891393948252⟩ ⟨false, 0⟩ ⟨false, 7382813002993475500138469022515058218812799604771005236298693884363558214412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_34_800 : bothSeg evalE (oGrid.idx 34) (oGrid.dm 34) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 34) oGrid.kl oGrid.kr 400 800 ⟨false, 7382813002993475500138469022515058218812799604771005236298693884363558214412⟩ ⟨false, 0⟩ ⟨false, 8437337697939051502600234827204684582742496131615184228538947365143603976152⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_34_1200 : bothSeg evalE (oGrid.idx 34) (oGrid.dm 34) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 34) oGrid.kl oGrid.kr 400 1200 ⟨false, 8437337697939051502600234827204684582742496131615184228538947365143603976152⟩ ⟨false, 0⟩ ⟨false, 8640479178516887803955119472431611252438884416952792906411992501005171584508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_34_1600 : bothSeg evalE (oGrid.idx 34) (oGrid.dm 34) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 34) oGrid.kl oGrid.kr 400 1600 ⟨false, 8640479178516887803955119472431611252438884416952792906411992501005171584508⟩ ⟨false, 0⟩ ⟨false, 8474220311339192367370500690084244131299806067492255787857635234111664154580⟩ ⟨false, 167966181225364966676052800410777224919016491072673601388368943544279096054⟩ = true := by
  decide +kernel

theorem b_34_2000 : bothSeg evalE (oGrid.idx 34) (oGrid.dm 34) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 34) oGrid.kl oGrid.kr 400 2000 ⟨false, 8474220311339192367370500690084244131299806067492255787857635234111664154580⟩ ⟨false, 167966181225364966676052800410777224919016491072673601388368943544279096054⟩ ⟨false, 8385158470792199216914553648479788220178475301844657283216120372727575894242⟩ ⟨false, 257563085347493120200984785274349955287636657859195299250661712846944493934⟩ = true := by
  decide +kernel

theorem b_34_2400 : bothLoop evalE (oGrid.idx 34) (oGrid.dm 34) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 34) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8385158470792199216914553648479788220178475301844657283216120372727575894242⟩ ⟨false, 257563085347493120200984785274349955287636657859195299250661712846944493934⟩ = true := by
  decide +kernel

theorem o_row_34 : oGrid.row evalE 34 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_34_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_34_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_34_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_34_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_34_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_34_2000).1 (bothLoop_sound b_34_2400).1))))))

theorem n_row_34 : nGrid.row evalE 34 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_34_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_34_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_34_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_34_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_34_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_34_2000).2 (bothLoop_sound b_34_2400).2))))))

theorem b_35_0 : bothSeg evalE (oGrid.idx 35) (oGrid.dm 35) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 35) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4573599864231593323001032043094907785115264047578512660430534827935210430516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_35_400 : bothSeg evalE (oGrid.idx 35) (oGrid.dm 35) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 35) oGrid.kl oGrid.kr 400 400 ⟨false, 4573599864231593323001032043094907785115264047578512660430534827935210430516⟩ ⟨false, 0⟩ ⟨false, 7357380705510489629882921846608738939894206539028286315381788577556478015434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_35_800 : bothSeg evalE (oGrid.idx 35) (oGrid.dm 35) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 35) oGrid.kl oGrid.kr 400 800 ⟨false, 7357380705510489629882921846608738939894206539028286315381788577556478015434⟩ ⟨false, 0⟩ ⟨false, 8408365516827845228552303972341763718202105673342134647205744118466976573362⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_35_1200 : bothSeg evalE (oGrid.idx 35) (oGrid.dm 35) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 35) oGrid.kl oGrid.kr 400 1200 ⟨false, 8408365516827845228552303972341763718202105673342134647205744118466976573362⟩ ⟨false, 0⟩ ⟨false, 8610553914052408660467942442925018977221801976842928348170247430417929896666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_35_1600 : bothSeg evalE (oGrid.idx 35) (oGrid.dm 35) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 35) oGrid.kl oGrid.kr 400 1600 ⟨false, 8610553914052408660467942442925018977221801976842928348170247430417929896666⟩ ⟨false, 0⟩ ⟨false, 8443988902635743643688311006753714426101881555765479243739539899308295507886⟩ ⟨false, 168226312194643039969127202768371546125706477547329536182214083390206542980⟩ = true := by
  decide +kernel

theorem b_35_2000 : bothSeg evalE (oGrid.idx 35) (oGrid.dm 35) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 35) oGrid.kl oGrid.kr 400 2000 ⟨false, 8443988902635743643688311006753714426101881555765479243739539899308295507886⟩ ⟨false, 168226312194643039969127202768371546125706477547329536182214083390206542980⟩ ⟨false, 8355439513705291986303417776548271265645704454790148311445735671278151849098⟩ ⟨false, 257317653462739182532982952459780049716892544755245284369189745778287759492⟩ = true := by
  decide +kernel

theorem b_35_2400 : bothLoop evalE (oGrid.idx 35) (oGrid.dm 35) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 35) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8355439513705291986303417776548271265645704454790148311445735671278151849098⟩ ⟨false, 257317653462739182532982952459780049716892544755245284369189745778287759492⟩ = true := by
  decide +kernel

theorem o_row_35 : oGrid.row evalE 35 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_35_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_35_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_35_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_35_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_35_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_35_2000).1 (bothLoop_sound b_35_2400).1))))))

theorem n_row_35 : nGrid.row evalE 35 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_35_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_35_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_35_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_35_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_35_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_35_2000).2 (bothLoop_sound b_35_2400).2))))))

theorem b_36_0 : bothSeg evalE (oGrid.idx 36) (oGrid.dm 36) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 36) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4557531795547938740866631519720824055197243374445501865911300160727757421708⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_36_400 : bothSeg evalE (oGrid.idx 36) (oGrid.dm 36) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 36) oGrid.kl oGrid.kr 400 400 ⟨false, 4557531795547938740866631519720824055197243374445501865911300160727757421708⟩ ⟨false, 0⟩ ⟨false, 7332017768003064544221039004486656873672323960194378406834800615967488068922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_36_800 : bothSeg evalE (oGrid.idx 36) (oGrid.dm 36) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 36) oGrid.kl oGrid.kr 400 800 ⟨false, 7332017768003064544221039004486656873672323960194378406834800615967488068922⟩ ⟨false, 0⟩ ⟨false, 8379468920161249880148836860368828368810024982985714285367811417741306495228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_36_1200 : bothSeg evalE (oGrid.idx 36) (oGrid.dm 36) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 36) oGrid.kl oGrid.kr 400 1200 ⟨false, 8379468920161249880148836860368828368810024982985714285367811417741306495228⟩ ⟨false, 0⟩ ⟨false, 8580705811159483882102753454110188869105411537156142734813019651233244634226⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_36_1600 : bothSeg evalE (oGrid.idx 36) (oGrid.dm 36) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 36) oGrid.kl oGrid.kr 400 1600 ⟨false, 8580705811159483882102753454110188869105411537156142734813019651233244634226⟩ ⟨false, 0⟩ ⟨false, 8413837200585514306452816953019230799567981919208115412699608937056066248020⟩ ⟨false, 168484636285930499264409099524001295358773184610875807489473279235556346400⟩ = true := by
  decide +kernel

theorem b_36_2000 : bothSeg evalE (oGrid.idx 36) (oGrid.dm 36) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 36) oGrid.kl oGrid.kr 400 2000 ⟨false, 8413837200585514306452816953019230799567981919208115412699608937056066248020⟩ ⟨false, 168484636285930499264409099524001295358773184610875807489473279235556346400⟩ ⟨false, 8325798017971433837283554375890588581142291243503771748177057344187583820854⟩ ⟨false, 257072530246451520041648536224655515339647261209888659278658849251874549542⟩ = true := by
  decide +kernel

theorem b_36_2400 : bothLoop evalE (oGrid.idx 36) (oGrid.dm 36) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 36) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8325798017971433837283554375890588581142291243503771748177057344187583820854⟩ ⟨false, 257072530246451520041648536224655515339647261209888659278658849251874549542⟩ = true := by
  decide +kernel

theorem o_row_36 : oGrid.row evalE 36 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_36_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_36_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_36_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_36_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_36_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_36_2000).1 (bothLoop_sound b_36_2400).1))))))

theorem n_row_36 : nGrid.row evalE 36 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_36_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_36_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_36_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_36_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_36_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_36_2000).2 (bothLoop_sound b_36_2400).2))))))

theorem b_37_0 : bothSeg evalE (oGrid.idx 37) (oGrid.dm 37) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 37) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4541510743645139955643027747714759507880451602782925550039688561451032955194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_37_400 : bothSeg evalE (oGrid.idx 37) (oGrid.dm 37) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 37) oGrid.kl oGrid.kr 400 400 ⟨false, 4541510743645139955643027747714759507880451602782925550039688561451032955194⟩ ⟨false, 0⟩ ⟨false, 7306723998264271812988261001770410668984101675783753108297733656614820749138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_37_800 : bothSeg evalE (oGrid.idx 37) (oGrid.dm 37) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 37) oGrid.kl oGrid.kr 400 800 ⟨false, 7306723998264271812988261001770410668984101675783753108297733656614820749138⟩ ⟨false, 0⟩ ⟨false, 8350647727576745793965379188978507156111819956576442362928286743603493011480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_37_1200 : bothSeg evalE (oGrid.idx 37) (oGrid.dm 37) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 37) oGrid.kl oGrid.kr 400 1200 ⟨false, 8350647727576745793965379188978507156111819956576442362928286743603493011480⟩ ⟨false, 0⟩ ⟨false, 8550934740713539433336363061172235826265483980435294323615625625059614858332⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_37_1600 : bothSeg evalE (oGrid.idx 37) (oGrid.dm 37) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 37) oGrid.kl oGrid.kr 400 1600 ⟨false, 8550934740713539433336363061172235826265483980435294323615625625059614858332⟩ ⟨false, 0⟩ ⟨false, 8383764901353086539157905870262036481037654022560289029871730315390559317408⟩ ⟨false, 168741259546376323726003547332223749413508337633168260280346156769271490386⟩ = true := by
  decide +kernel

theorem b_37_2000 : bothSeg evalE (oGrid.idx 37) (oGrid.dm 37) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 37) oGrid.kl oGrid.kr 400 2000 ⟨false, 8383764901353086539157905870262036481037654022560289029871730315390559317408⟩ ⟨false, 168741259546376323726003547332223749413508337633168260280346156769271490386⟩ ⟨false, 8296233664294760323098284192610122381288991704731862866215541288445433751746⟩ ⟨false, 256827818893533553415406719026263175417469876570102008059125993238961186376⟩ = true := by
  decide +kernel

theorem b_37_2400 : bothLoop evalE (oGrid.idx 37) (oGrid.dm 37) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 37) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8296233664294760323098284192610122381288991704731862866215541288445433751746⟩ ⟨false, 256827818893533553415406719026263175417469876570102008059125993238961186376⟩ = true := by
  decide +kernel

theorem o_row_37 : oGrid.row evalE 37 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_37_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_37_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_37_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_37_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_37_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_37_2000).1 (bothLoop_sound b_37_2400).1))))))

theorem n_row_37 : nGrid.row evalE 37 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_37_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_37_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_37_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_37_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_37_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_37_2000).2 (bothLoop_sound b_37_2400).2))))))

theorem b_38_0 : bothSeg evalE (oGrid.idx 38) (oGrid.dm 38) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 38) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4525536600229696731660870224709102198892579289538500348468236235920744485858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_38_400 : bothSeg evalE (oGrid.idx 38) (oGrid.dm 38) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 38) oGrid.kl oGrid.kr 400 400 ⟨false, 4525536600229696731660870224709102198892579289538500348468236235920744485858⟩ ⟨false, 0⟩ ⟨false, 7281499216321360406205142831203586756234544052073591585078207028798151104060⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_38_800 : bothSeg evalE (oGrid.idx 38) (oGrid.dm 38) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 38) oGrid.kl oGrid.kr 400 800 ⟨false, 7281499216321360406205142831203586756234544052073591585078207028798151104060⟩ ⟨false, 0⟩ ⟨false, 8321901788890243778387735545372940889399985151398646067533498201855932007842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_38_1200 : bothSeg evalE (oGrid.idx 38) (oGrid.dm 38) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 38) oGrid.kl oGrid.kr 400 1200 ⟨false, 8321901788890243778387735545372940889399985151398646067533498201855932007842⟩ ⟨false, 0⟩ ⟨false, 8521240509169778175544780441313382728063821796759816134428480820201381813536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_38_1600 : bothSeg evalE (oGrid.idx 38) (oGrid.dm 38) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 38) oGrid.kl oGrid.kr 400 1600 ⟨false, 8521240509169778175544780441313382728063821796759816134428480820201381813536⟩ ⟨false, 0⟩ ⟨false, 8353771926326973385757769336880582550207928270062544471259201999632452581012⟩ ⟨false, 168995644888727044150839242982974151308242880230173540068120945015513083678⟩ = true := by
  decide +kernel

theorem b_38_2000 : bothSeg evalE (oGrid.idx 38) (oGrid.dm 38) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 38) oGrid.kl oGrid.kr 400 2000 ⟨false, 8353771926326973385757769336880582550207928270062544471259201999632452581012⟩ ⟨false, 168995644888727044150839242982974151308242880230173540068120945015513083678⟩ ⟨false, 8266746334190551336531804940659554177149196228461058566007692353101366144070⟩ ⟨false, 256582939682129839212675280633400798161462161385333400225286747687625610836⟩ = true := by
  decide +kernel

theorem b_38_2400 : bothLoop evalE (oGrid.idx 38) (oGrid.dm 38) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 38) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8266746334190551336531804940659554177149196228461058566007692353101366144070⟩ ⟨false, 256582939682129839212675280633400798161462161385333400225286747687625610836⟩ = true := by
  decide +kernel

theorem o_row_38 : oGrid.row evalE 38 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_38_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_38_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_38_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_38_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_38_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_38_2000).1 (bothLoop_sound b_38_2400).1))))))

theorem n_row_38 : nGrid.row evalE 38 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_38_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_38_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_38_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_38_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_38_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_38_2000).2 (bothLoop_sound b_38_2400).2))))))

theorem b_39_0 : bothSeg evalE (oGrid.idx 39) (oGrid.dm 39) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 39) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4509609239616135423805071302707615549875199778261568980004973854356193769426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_39_400 : bothSeg evalE (oGrid.idx 39) (oGrid.dm 39) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 39) oGrid.kl oGrid.kr 400 400 ⟨false, 4509609239616135423805071302707615549875199778261568980004973854356193769426⟩ ⟨false, 0⟩ ⟨false, 7256343356376189398652077070756851944087767397251899807690470033318266239224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_39_800 : bothSeg evalE (oGrid.idx 39) (oGrid.dm 39) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 39) oGrid.kl oGrid.kr 400 800 ⟨false, 7256343356376189398652077070756851944087767397251899807690470033318266239224⟩ ⟨false, 0⟩ ⟨false, 8293231023082848517990482797535439837229221369624289302715552326391132146126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_39_1200 : bothSeg evalE (oGrid.idx 39) (oGrid.dm 39) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 39) oGrid.kl oGrid.kr 400 1200 ⟨false, 8293231023082848517990482797535439837229221369624289302715552326391132146126⟩ ⟨false, 0⟩ ⟨false, 8491623073919055030040292663799568630244290453710481147403285888188343365700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_39_1600 : bothSeg evalE (oGrid.idx 39) (oGrid.dm 39) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 39) oGrid.kl oGrid.kr 400 1600 ⟨false, 8491623073919055030040292663799568630244290453710481147403285888188343365700⟩ ⟨false, 0⟩ ⟨false, 8323858043152940844057128304616517058421430550336141670045860539440536443948⟩ ⟨false, 169249016265248728388987221320433392646292102576366649158971116048741661530⟩ = true := by
  decide +kernel

theorem b_39_2000 : bothSeg evalE (oGrid.idx 39) (oGrid.dm 39) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 39) oGrid.kl oGrid.kr 400 2000 ⟨false, 8323858043152940844057128304616517058421430550336141670045860539440536443948⟩ ⟨false, 169249016265248728388987221320433392646292102576366649158971116048741661530⟩ ⟨false, 8237335829032518970274319574831680990184056585454779809646071961214220376190⟩ ⟨false, 256339215181584585536034309383175693207050552287043799216054752537662875748⟩ = true := by
  decide +kernel

theorem b_39_2400 : bothLoop evalE (oGrid.idx 39) (oGrid.dm 39) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 39) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8237335829032518970274319574831680990184056585454779809646071961214220376190⟩ ⟨false, 256339215181584585536034309383175693207050552287043799216054752537662875748⟩ = true := by
  decide +kernel

theorem o_row_39 : oGrid.row evalE 39 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_39_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_39_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_39_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_39_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_39_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_39_2000).1 (bothLoop_sound b_39_2400).1))))))

theorem n_row_39 : nGrid.row evalE 39 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_39_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_39_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_39_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_39_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_39_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_39_2000).2 (bothLoop_sound b_39_2400).2))))))

theorem b_40_0 : bothSeg evalE (oGrid.idx 40) (oGrid.dm 40) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 40) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4493728604883189659908669270491620731645936042317318527396235149034738886052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_40_400 : bothSeg evalE (oGrid.idx 40) (oGrid.dm 40) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 40) oGrid.kl oGrid.kr 400 400 ⟨false, 4493728604883189659908669270491620731645936042317318527396235149034738886052⟩ ⟨false, 0⟩ ⟨false, 7231256198956916740110682338431487191171985969425826766106878302404441998488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_40_800 : bothSeg evalE (oGrid.idx 40) (oGrid.dm 40) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 40) oGrid.kl oGrid.kr 400 800 ⟨false, 7231256198956916740110682338431487191171985969425826766106878302404441998488⟩ ⟨false, 0⟩ ⟨false, 8264635209568071839818914790856171558684105553466215787967339363133329367844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_40_1200 : bothSeg evalE (oGrid.idx 40) (oGrid.dm 40) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 40) oGrid.kl oGrid.kr 400 1200 ⟨false, 8264635209568071839818914790856171558684105553466215787967339363133329367844⟩ ⟨false, 0⟩ ⟨false, 8462082192446890926678141811312173358045548237530107343418006935255686183366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_40_1600 : bothSeg evalE (oGrid.idx 40) (oGrid.dm 40) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 40) oGrid.kl oGrid.kr 400 1600 ⟨false, 8462082192446890926678141811312173358045548237530107343418006935255686183366⟩ ⟨false, 0⟩ ⟨false, 8294023255340140371144190180658982890415123452997215755542346690640595548174⟩ ⟨false, 169500261443442317680187753206069090188331435210766752633824417301125634066⟩ = true := by
  decide +kernel

theorem b_40_2000 : bothSeg evalE (oGrid.idx 40) (oGrid.dm 40) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 40) oGrid.kl oGrid.kr 400 2000 ⟨false, 8294023255340140371144190180658982890415123452997215755542346690640595548174⟩ ⟨false, 169500261443442317680187753206069090188331435210766752633824417301125634066⟩ ⟨false, 8208002134688902115028997968953285330050349304171123969980686102098232342476⟩ ⟨false, 256095389085425027233586924703927645766999434328730164081382774169340808972⟩ = true := by
  decide +kernel

theorem b_40_2400 : bothLoop evalE (oGrid.idx 40) (oGrid.dm 40) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 40) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8208002134688902115028997968953285330050349304171123969980686102098232342476⟩ ⟨false, 256095389085425027233586924703927645766999434328730164081382774169340808972⟩ = true := by
  decide +kernel

theorem o_row_40 : oGrid.row evalE 40 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_40_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_40_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_40_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_40_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_40_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_40_2000).1 (bothLoop_sound b_40_2400).1))))))

theorem n_row_40 : nGrid.row evalE 40 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_40_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_40_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_40_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_40_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_40_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_40_2000).2 (bothLoop_sound b_40_2400).2))))))

theorem b_41_0 : bothSeg evalE (oGrid.idx 41) (oGrid.dm 41) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 41) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4477894468669685938268017671503769436466521156937458822669581540210841337294⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_41_400 : bothSeg evalE (oGrid.idx 41) (oGrid.dm 41) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 41) oGrid.kl oGrid.kr 400 400 ⟨false, 4477894468669685938268017671503769436466521156937458822669581540210841337294⟩ ⟨false, 0⟩ ⟨false, 7206237540763987617043602986541825488429832569607461434567413123051197373674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_41_800 : bothSeg evalE (oGrid.idx 41) (oGrid.dm 41) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 41) oGrid.kl oGrid.kr 400 800 ⟨false, 7206237540763987617043602986541825488429832569607461434567413123051197373674⟩ ⟨false, 0⟩ ⟨false, 8236114172116476484877115356872767371677417503443688898380223912523552197522⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_41_1200 : bothSeg evalE (oGrid.idx 41) (oGrid.dm 41) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 41) oGrid.kl oGrid.kr 400 1200 ⟨false, 8236114172116476484877115356872767371677417503443688898380223912523552197522⟩ ⟨false, 0⟩ ⟨false, 8432617724090100418959924837408321742143089070371900302286401791618332108310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_41_1600 : bothSeg evalE (oGrid.idx 41) (oGrid.dm 41) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 41) oGrid.kl oGrid.kr 400 1600 ⟨false, 8432617724090100418959924837408321742143089070371900302286401791618332108310⟩ ⟨false, 0⟩ ⟨false, 8264266948695507856418979724413207279073337858716111595641442309196611117802⟩ ⟨false, 169750127798135301472735644037049756014167947855417448944921450473714314720⟩ = true := by
  decide +kernel

theorem b_41_2000 : bothSeg evalE (oGrid.idx 41) (oGrid.dm 41) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 41) oGrid.kl oGrid.kr 400 2000 ⟨false, 8264266948695507856418979724413207279073337858716111595641442309196611117802⟩ ⟨false, 169750127798135301472735644037049756014167947855417448944921450473714314720⟩ ⟨false, 8178744608648274996315987538118905434583213783369951502829424573097948487874⟩ ⟨false, 255852400987566993943772945745381451905199588308754374015350994592237716930⟩ = true := by
  decide +kernel

theorem b_41_2400 : bothLoop evalE (oGrid.idx 41) (oGrid.dm 41) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 41) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8178744608648274996315987538118905434583213783369951502829424573097948487874⟩ ⟨false, 255852400987566993943772945745381451905199588308754374015350994592237716930⟩ = true := by
  decide +kernel

theorem o_row_41 : oGrid.row evalE 41 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_41_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_41_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_41_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_41_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_41_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_41_2000).1 (bothLoop_sound b_41_2400).1))))))

theorem n_row_41 : nGrid.row evalE 41 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_41_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_41_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_41_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_41_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_41_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_41_2000).2 (bothLoop_sound b_41_2400).2))))))

theorem b_42_0 : bothSeg evalE (oGrid.idx 42) (oGrid.dm 42) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 42) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4462106752308590419523397849469311309850595994266077888777765183241569775902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_42_400 : bothSeg evalE (oGrid.idx 42) (oGrid.dm 42) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 42) oGrid.kl oGrid.kr 400 400 ⟨false, 4462106752308590419523397849469311309850595994266077888777765183241569775902⟩ ⟨false, 0⟩ ⟨false, 7181287230022954400180923369700633595912945333478715761955413957874820492054⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_42_800 : bothSeg evalE (oGrid.idx 42) (oGrid.dm 42) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 42) oGrid.kl oGrid.kr 400 800 ⟨false, 7181287230022954400180923369700633595912945333478715761955413957874820492054⟩ ⟨false, 0⟩ ⟨false, 8207667735021628173432816863740118673492817868942433498456081890565626528120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_42_1200 : bothSeg evalE (oGrid.idx 42) (oGrid.dm 42) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 42) oGrid.kl oGrid.kr 400 1200 ⟨false, 8207667735021628173432816863740118673492817868942433498456081890565626528120⟩ ⟨false, 0⟩ ⟨false, 8403229470707194596907783162030230602402872065862317416354113675150085991524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_42_1600 : bothSeg evalE (oGrid.idx 42) (oGrid.dm 42) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 42) oGrid.kl oGrid.kr 400 1600 ⟨false, 8403229470707194596907783162030230602402872065862317416354113675150085991524⟩ ⟨false, 0⟩ ⟨false, 8234589248962193248507076983372189350124498136845713710949687961686830365520⟩ ⟨false, 169998028627044360274570480930017648789848323451930009235442940991876091170⟩ = true := by
  decide +kernel

theorem b_42_2000 : bothSeg evalE (oGrid.idx 42) (oGrid.dm 42) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 42) oGrid.kl oGrid.kr 400 2000 ⟨false, 8234589248962193248507076983372189350124498136845713710949687961686830365520⟩ ⟨false, 169998028627044360274570480930017648789848323451930009235442940991876091170⟩ ⟨false, 8149563382551790555402895835907719323118347420643974760446858890810113972978⟩ ⟨false, 255609451362739317858141840797504861428129089300503227931255675143813549886⟩ = true := by
  decide +kernel

theorem b_42_2400 : bothLoop evalE (oGrid.idx 42) (oGrid.dm 42) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 42) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8149563382551790555402895835907719323118347420643974760446858890810113972978⟩ ⟨false, 255609451362739317858141840797504861428129089300503227931255675143813549886⟩ = true := by
  decide +kernel

theorem o_row_42 : oGrid.row evalE 42 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_42_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_42_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_42_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_42_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_42_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_42_2000).1 (bothLoop_sound b_42_2400).1))))))

theorem n_row_42 : nGrid.row evalE 42 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_42_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_42_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_42_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_42_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_42_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_42_2000).2 (bothLoop_sound b_42_2400).2))))))

theorem b_43_0 : bothSeg evalE (oGrid.idx 43) (oGrid.dm 43) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 43) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4446365328149498229436257951051724266249320756775872009183321286926311404198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_43_400 : bothSeg evalE (oGrid.idx 43) (oGrid.dm 43) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 43) oGrid.kl oGrid.kr 400 400 ⟨false, 4446365328149498229436257951051724266249320756775872009183321286926311404198⟩ ⟨false, 0⟩ ⟨false, 7156405236652205579620165323769749381055077358309936155308041607839255044508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_43_800 : bothSeg evalE (oGrid.idx 43) (oGrid.dm 43) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 43) oGrid.kl oGrid.kr 400 800 ⟨false, 7156405236652205579620165323769749381055077358309936155308041607839255044508⟩ ⟨false, 0⟩ ⟨false, 8179295888728928306434768621617861639605022617440845396750097407014312691094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_43_1200 : bothSeg evalE (oGrid.idx 43) (oGrid.dm 43) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 43) oGrid.kl oGrid.kr 400 1200 ⟨false, 8179295888728928306434768621617861639605022617440845396750097407014312691094⟩ ⟨false, 0⟩ ⟨false, 8373917428600506836984840798428991429785050084159906950214789735712244055158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_43_1600 : bothSeg evalE (oGrid.idx 43) (oGrid.dm 43) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 43) oGrid.kl oGrid.kr 400 1600 ⟨false, 8373917428600506836984840798428991429785050084159906950214789735712244055158⟩ ⟨false, 0⟩ ⟨false, 8204990072729907157070399363274049204116545337517376621978484771110936216660⟩ ⟨false, 170244413173854394651799074731175162032484084014284504053543779593869554368⟩ = true := by
  decide +kernel

theorem b_43_2000 : bothSeg evalE (oGrid.idx 43) (oGrid.dm 43) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 43) oGrid.kl oGrid.kr 400 2000 ⟨false, 8204990072729907157070399363274049204116545337517376621978484771110936216660⟩ ⟨false, 170244413173854394651799074731175162032484084014284504053543779593869554368⟩ ⟨false, 8120458443052467087318182962937932929082928665259264526798198238106167874728⟩ ⟨false, 255367070237165827517561148956781296272195553954782047755855449412374334132⟩ = true := by
  decide +kernel

theorem b_43_2400 : bothLoop evalE (oGrid.idx 43) (oGrid.dm 43) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 43) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8120458443052467087318182962937932929082928665259264526798198238106167874728⟩ ⟨false, 255367070237165827517561148956781296272195553954782047755855449412374334132⟩ = true := by
  decide +kernel

theorem o_row_43 : oGrid.row evalE 43 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_43_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_43_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_43_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_43_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_43_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_43_2000).1 (bothLoop_sound b_43_2400).1))))))

theorem n_row_43 : nGrid.row evalE 43 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_43_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_43_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_43_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_43_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_43_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_43_2000).2 (bothLoop_sound b_43_2400).2))))))

theorem b_44_0 : bothSeg evalE (oGrid.idx 44) (oGrid.dm 44) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 44) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4430670009716798741629867000339568432590950840473592594810987432351417252858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_44_400 : bothSeg evalE (oGrid.idx 44) (oGrid.dm 44) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 44) oGrid.kl oGrid.kr 400 400 ⟨false, 4430670009716798741629867000339568432590950840473592594810987432351417252858⟩ ⟨false, 0⟩ ⟨false, 7131591218031693612310853726846502184302076822627850858580398276150105397558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_44_800 : bothSeg evalE (oGrid.idx 44) (oGrid.dm 44) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 44) oGrid.kl oGrid.kr 400 800 ⟨false, 7131591218031693612310853726846502184302076822627850858580398276150105397558⟩ ⟨false, 0⟩ ⟨false, 8150998305463628913271091037883407057471226086913870897472476174703611752444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_44_1200 : bothSeg evalE (oGrid.idx 44) (oGrid.dm 44) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 44) oGrid.kl oGrid.kr 400 1200 ⟨false, 8150998305463628913271091037883407057471226086913870897472476174703611752444⟩ ⟨false, 0⟩ ⟨false, 8344681295771615984038547087139667496582681355767860552289666058107447587412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_44_1600 : bothSeg evalE (oGrid.idx 44) (oGrid.dm 44) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 44) oGrid.kl oGrid.kr 400 1600 ⟨false, 8344681295771615984038547087139667496582681355767860552289666058107447587412⟩ ⟨false, 0⟩ ⟨false, 8175469125187557051959760833901593034916656692130695276514552283480491175740⟩ ⟨false, 170488968776014644304942661740902282993867057113894904685004373034450370104⟩ = true := by
  decide +kernel

theorem b_44_2000 : bothSeg evalE (oGrid.idx 44) (oGrid.dm 44) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 44) oGrid.kl oGrid.kr 400 2000 ⟨false, 8175469125187557051959760833901593034916656692130695276514552283480491175740⟩ ⟨false, 170488968776014644304942661740902282993867057113894904685004373034450370104⟩ ⟨false, 8091429422703504435517182890233973795644150930392318185885967898894239893230⟩ ⟨false, 255124934350983756254670970625374868667619719683272574187638947811748733934⟩ = true := by
  decide +kernel

theorem b_44_2400 : bothLoop evalE (oGrid.idx 44) (oGrid.dm 44) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 44) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8091429422703504435517182890233973795644150930392318185885967898894239893230⟩ ⟨false, 255124934350983756254670970625374868667619719683272574187638947811748733934⟩ = true := by
  decide +kernel

theorem o_row_44 : oGrid.row evalE 44 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_44_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_44_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_44_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_44_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_44_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_44_2000).1 (bothLoop_sound b_44_2400).1))))))

theorem n_row_44 : nGrid.row evalE 44 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_44_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_44_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_44_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_44_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_44_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_44_2000).2 (bothLoop_sound b_44_2400).2))))))

theorem b_45_0 : bothSeg evalE (oGrid.idx 45) (oGrid.dm 45) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 45) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4415020783994660816472664533113769682145643048823972713133002355966962649494⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_45_400 : bothSeg evalE (oGrid.idx 45) (oGrid.dm 45) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 45) oGrid.kl oGrid.kr 400 400 ⟨false, 4415020783994660816472664533113769682145643048823972713133002355966962649494⟩ ⟨false, 0⟩ ⟨false, 7106845146735594435158992341520733852935291765973607553008682317018586910860⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_45_800 : bothSeg evalE (oGrid.idx 45) (oGrid.dm 45) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 45) oGrid.kl oGrid.kr 400 800 ⟨false, 7106845146735594435158992341520733852935291765973607553008682317018586910860⟩ ⟨false, 0⟩ ⟨false, 8122774948514955387069214283749051854945411023425013678905739238280428775450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_45_1200 : bothSeg evalE (oGrid.idx 45) (oGrid.dm 45) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 45) oGrid.kl oGrid.kr 400 1200 ⟨false, 8122774948514955387069214283749051854945411023425013678905739238280428775450⟩ ⟨false, 0⟩ ⟨false, 8315521024231619037690894512356244504547413851558446627989917121747600725260⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_45_1600 : bothSeg evalE (oGrid.idx 45) (oGrid.dm 45) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 45) oGrid.kl oGrid.kr 400 1600 ⟨false, 8315521024231619037690894512356244504547413851558446627989917121747600725260⟩ ⟨false, 0⟩ ⟨false, 8146026501281382940978671145001940684089146747531955208343345531881658086054⟩ ⟨false, 170731939136765157071375180319470250305341696108418370122054196560502932056⟩ = true := by
  decide +kernel

theorem b_45_2000 : bothSeg evalE (oGrid.idx 45) (oGrid.dm 45) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 45) oGrid.kl oGrid.kr 400 2000 ⟨false, 8146026501281382940978671145001940684089146747531955208343345531881658086054⟩ ⟨false, 170731939136765157071375180319470250305341696108418370122054196560502932056⟩ ⟨false, 8062476438842846968801515135109814919606745946850163039108922791167728203176⟩ ⟨false, 254883261740368518413396075025233655829457224807043325885279045359680987512⟩ = true := by
  decide +kernel

theorem b_45_2400 : bothLoop evalE (oGrid.idx 45) (oGrid.dm 45) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 45) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8062476438842846968801515135109814919606745946850163039108922791167728203176⟩ ⟨false, 254883261740368518413396075025233655829457224807043325885279045359680987512⟩ = true := by
  decide +kernel

theorem o_row_45 : oGrid.row evalE 45 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_45_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_45_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_45_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_45_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_45_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_45_2000).1 (bothLoop_sound b_45_2400).1))))))

theorem n_row_45 : nGrid.row evalE 45 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_45_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_45_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_45_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_45_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_45_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_45_2000).2 (bothLoop_sound b_45_2400).2))))))

theorem b_46_0 : bothSeg evalE (oGrid.idx 46) (oGrid.dm 46) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 46) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4399417434278842507065586998806222694299859270437283542577020780058579956314⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_46_400 : bothSeg evalE (oGrid.idx 46) (oGrid.dm 46) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 46) oGrid.kl oGrid.kr 400 400 ⟨false, 4399417434278842507065586998806222694299859270437283542577020780058579956314⟩ ⟨false, 0⟩ ⟨false, 7082166739276433127576249986439881757230975274191228645346965341944877983444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_46_800 : bothSeg evalE (oGrid.idx 46) (oGrid.dm 46) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 46) oGrid.kl oGrid.kr 400 800 ⟨false, 7082166739276433127576249986439881757230975274191228645346965341944877983444⟩ ⟨false, 0⟩ ⟨false, 8094625519658121588744652892857359491634604059069721357116713359913497673006⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_46_1200 : bothSeg evalE (oGrid.idx 46) (oGrid.dm 46) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 46) oGrid.kl oGrid.kr 400 1200 ⟨false, 8094625519658121588744652892857359491634604059069721357116713359913497673006⟩ ⟨false, 0⟩ ⟨false, 8286436314254096080484627693430169588691462583627064144246618057422292117434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_46_1600 : bothSeg evalE (oGrid.idx 46) (oGrid.dm 46) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 46) oGrid.kl oGrid.kr 400 1600 ⟨false, 8286436314254096080484627693430169588691462583627064144246618057422292117434⟩ ⟨false, 0⟩ ⟨false, 8116661659229883238221441644330930288757722339469039445282029922011430616820⟩ ⟨false, 170973607255695000319588220058712694143574237873404661676467838049207633534⟩ = true := by
  decide +kernel

theorem b_46_2000 : bothSeg evalE (oGrid.idx 46) (oGrid.dm 46) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 46) oGrid.kl oGrid.kr 400 2000 ⟨false, 8116661659229883238221441644330930288757722339469039445282029922011430616820⟩ ⟨false, 170973607255695000319588220058712694143574237873404661676467838049207633534⟩ ⟨false, 8033598921945295979553192874963742817158117034245821554672826335061046085588⟩ ⟨false, 254642374275386979396905542063871430013062708728638840677405652337186964212⟩ = true := by
  decide +kernel

theorem b_46_2400 : bothLoop evalE (oGrid.idx 46) (oGrid.dm 46) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 46) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8033598921945295979553192874963742817158117034245821554672826335061046085588⟩ ⟨false, 254642374275386979396905542063871430013062708728638840677405652337186964212⟩ = true := by
  decide +kernel

theorem o_row_46 : oGrid.row evalE 46 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_46_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_46_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_46_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_46_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_46_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_46_2000).1 (bothLoop_sound b_46_2400).1))))))

theorem n_row_46 : nGrid.row evalE 46 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_46_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_46_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_46_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_46_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_46_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_46_2000).2 (bothLoop_sound b_46_2400).2))))))

theorem b_47_0 : bothSeg evalE (oGrid.idx 47) (oGrid.dm 47) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 47) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4383859834212540704758799834791434684454514667962535052650926379209318739594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_47_400 : bothSeg evalE (oGrid.idx 47) (oGrid.dm 47) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 47) oGrid.kl oGrid.kr 400 400 ⟨false, 4383859834212540704758799834791434684454514667962535052650926379209318739594⟩ ⟨false, 0⟩ ⟨false, 7057555972602966867380250618747272431948143816675463265554020263417802065064⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_47_800 : bothSeg evalE (oGrid.idx 47) (oGrid.dm 47) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 47) oGrid.kl oGrid.kr 400 800 ⟨false, 7057555972602966867380250618747272431948143816675463265554020263417802065064⟩ ⟨false, 0⟩ ⟨false, 8066550051279589626033670174691915900656703886636499145981067830434229156342⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_47_1200 : bothSeg evalE (oGrid.idx 47) (oGrid.dm 47) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 47) oGrid.kl oGrid.kr 400 1200 ⟨false, 8066550051279589626033670174691915900656703886636499145981067830434229156342⟩ ⟨false, 0⟩ ⟨false, 8257427210927728564651846800813450027531377864399214879692641064412176834364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_47_1600 : bothSeg evalE (oGrid.idx 47) (oGrid.dm 47) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 47) oGrid.kl oGrid.kr 400 1600 ⟨false, 8257427210927728564651846800813450027531377864399214879692641064412176834364⟩ ⟨false, 0⟩ ⟨false, 8087374936759756170398571971812551322904480221729290071890845972412553345958⟩ ⟨false, 171213165753816763458565768273028559424058119872360767759879445644484563934⟩ = true := by
  decide +kernel

theorem b_47_2000 : bothSeg evalE (oGrid.idx 47) (oGrid.dm 47) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 47) oGrid.kl oGrid.kr 400 2000 ⟨false, 8087374936759756170398571971812551322904480221729290071890845972412553345958⟩ ⟨false, 171213165753816763458565768273028559424058119872360767759879445644484563934⟩ ⟨false, 8004797206275247521359899264432367338159123255994104761568278752394613645836⟩ ⟨false, 254401386792492891929999272018314745417116385373371863940584236622253584922⟩ = true := by
  decide +kernel

theorem b_47_2400 : bothLoop evalE (oGrid.idx 47) (oGrid.dm 47) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 47) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 8004797206275247521359899264432367338159123255994104761568278752394613645836⟩ ⟨false, 254401386792492891929999272018314745417116385373371863940584236622253584922⟩ = true := by
  decide +kernel

theorem o_row_47 : oGrid.row evalE 47 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_47_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_47_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_47_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_47_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_47_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_47_2000).1 (bothLoop_sound b_47_2400).1))))))

theorem n_row_47 : nGrid.row evalE 47 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_47_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_47_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_47_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_47_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_47_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_47_2000).2 (bothLoop_sound b_47_2400).2))))))

theorem o_blk_24 : allFrom (fun j => oGrid.row evalE j) 24 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 24) o_row_24 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 25) o_row_25 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 26) o_row_26 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 27) o_row_27 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 28) o_row_28 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 29) o_row_29 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 30) o_row_30 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 31) o_row_31 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 32) o_row_32 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 33) o_row_33 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 34) o_row_34 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 35) o_row_35 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 36) o_row_36 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 37) o_row_37 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 38) o_row_38 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 39) o_row_39 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 40) o_row_40 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 41) o_row_41 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 42) o_row_42 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 43) o_row_43 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 44) o_row_44 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 45) o_row_45 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 46) o_row_46 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 47) o_row_47 (allFrom_zero (fun j => oGrid.row evalE j) 48)))))))))))))))))))))))))

theorem n_blk_24 : allFrom (fun j => nGrid.row evalE j) 24 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 24) n_row_24 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 25) n_row_25 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 26) n_row_26 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 27) n_row_27 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 28) n_row_28 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 29) n_row_29 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 30) n_row_30 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 31) n_row_31 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 32) n_row_32 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 33) n_row_33 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 34) n_row_34 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 35) n_row_35 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 36) n_row_36 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 37) n_row_37 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 38) n_row_38 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 39) n_row_39 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 40) n_row_40 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 41) n_row_41 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 42) n_row_42 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 43) n_row_43 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 44) n_row_44 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 45) n_row_45 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 46) n_row_46 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 47) n_row_47 (allFrom_zero (fun j => nGrid.row evalE j) 48)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
