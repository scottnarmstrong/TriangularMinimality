/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 5 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `120`–`143`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_120_0 : bothSeg evalE (oGrid.idx 120) (oGrid.dm 120) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 120) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3363730844970994712361153820819321492910481987074469877337927921706530664414⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_120_400 : bothSeg evalE (oGrid.idx 120) (oGrid.dm 120) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 120) oGrid.kl oGrid.kr 400 400 ⟨false, 3363730844970994712361153820819321492910481987074469877337927921706530664414⟩ ⟨false, 0⟩ ⟨false, 5433244318748006213814360472366179325231207207696696048866015080718798623024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_120_800 : bothSeg evalE (oGrid.idx 120) (oGrid.dm 120) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 120) oGrid.kl oGrid.kr 400 800 ⟨false, 5433244318748006213814360472366179325231207207696696048866015080718798623024⟩ ⟨false, 0⟩ ⟨false, 6206493969188327880173736326877257460784770144717281603208984808176752814830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_120_1200 : bothSeg evalE (oGrid.idx 120) (oGrid.dm 120) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 120) oGrid.kl oGrid.kr 400 1200 ⟨false, 6206493969188327880173736326877257460784770144717281603208984808176752814830⟩ ⟨false, 0⟩ ⟨false, 6332098811849502746278946308663455480872915835448226679939051951879898455880⟩ ⟨false, 1685061650270128315686730735705764908473986626554366918932027584939489192⟩ = true := by
  decide +kernel

theorem b_120_1600 : bothSeg evalE (oGrid.idx 120) (oGrid.dm 120) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 120) oGrid.kl oGrid.kr 400 1600 ⟨false, 6332098811849502746278946308663455480872915835448226679939051951879898455880⟩ ⟨false, 1685061650270128315686730735705764908473986626554366918932027584939489192⟩ ⟨false, 6149456295212994370538810197805168099617140566107206638361844337422629626626⟩ ⟨false, 184597003727533490846952949853374559598764023314649377798419977328495124002⟩ = true := by
  decide +kernel

theorem b_120_2000 : bothSeg evalE (oGrid.idx 120) (oGrid.dm 120) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 120) oGrid.kl oGrid.kr 400 2000 ⟨false, 6149456295212994370538810197805168099617140566107206638361844337422629626626⟩ ⟨false, 184597003727533490846952949853374559598764023314649377798419977328495124002⟩ ⟨false, 6096007127086932460494953665640467757205583541027818829446319393026052355514⟩ ⟨false, 238777655769263033538570786383530306887004538476981427463472941386641595414⟩ = true := by
  decide +kernel

theorem b_120_2400 : bothLoop evalE (oGrid.idx 120) (oGrid.dm 120) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 120) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6096007127086932460494953665640467757205583541027818829446319393026052355514⟩ ⟨false, 238777655769263033538570786383530306887004538476981427463472941386641595414⟩ = true := by
  decide +kernel

theorem o_row_120 : oGrid.row evalE 120 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_120_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_120_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_120_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_120_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_120_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_120_2000).1 (bothLoop_sound b_120_2400).1))))))

theorem n_row_120 : nGrid.row evalE 120 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_120_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_120_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_120_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_120_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_120_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_120_2000).2 (bothLoop_sound b_120_2400).2))))))

theorem b_121_0 : bothSeg evalE (oGrid.idx 121) (oGrid.dm 121) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 121) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3351235644188951750792838021960319011892488095063515777081380372664528015558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_121_400 : bothSeg evalE (oGrid.idx 121) (oGrid.dm 121) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 121) oGrid.kl oGrid.kr 400 400 ⟨false, 3351235644188951750792838021960319011892488095063515777081380372664528015558⟩ ⟨false, 0⟩ ⟨false, 5413219340678810778952753481159699525374291084136281364918381582281821167348⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_121_800 : bothSeg evalE (oGrid.idx 121) (oGrid.dm 121) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 121) oGrid.kl oGrid.kr 400 800 ⟨false, 5413219340678810778952753481159699525374291084136281364918381582281821167348⟩ ⟨false, 0⟩ ⟨false, 6183476538779865496729323219606890015867552830779533496581893392874516587456⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_121_1200 : bothSeg evalE (oGrid.idx 121) (oGrid.dm 121) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 121) oGrid.kl oGrid.kr 400 1200 ⟨false, 6183476538779865496729323219606890015867552830779533496581893392874516587456⟩ ⟨false, 0⟩ ⟨false, 6308162361833242479869909564841519408012894462839013634932899119510980755594⟩ ⟨false, 1811145934572315484623601427431986727382832218767366149254277176398819208⟩ = true := by
  decide +kernel

theorem b_121_1600 : bothSeg evalE (oGrid.idx 121) (oGrid.dm 121) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 121) oGrid.kl oGrid.kr 400 1600 ⟨false, 6308162361833242479869909564841519408012894462839013634932899119510980755594⟩ ⟨false, 1811145934572315484623601427431986727382832218767366149254277176398819208⟩ ⟨false, 6125514836498879040538443248479664539859690380836582529508834827507834409068⟩ ⟨false, 184728874785463103555704871541357005239318174607645130349200574595165026886⟩ = true := by
  decide +kernel

theorem b_121_2000 : bothSeg evalE (oGrid.idx 121) (oGrid.dm 121) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 121) oGrid.kl oGrid.kr 400 2000 ⟨false, 6125514836498879040538443248479664539859690380836582529508834827507834409068⟩ ⟨false, 184728874785463103555704871541357005239318174607645130349200574595165026886⟩ ⟨false, 6072381503644771453432439315045893893687259353991618688439125815103032036378⟩ ⟨false, 238595416302712839022295704613104562166738512402321008915332962475516652612⟩ = true := by
  decide +kernel

theorem b_121_2400 : bothLoop evalE (oGrid.idx 121) (oGrid.dm 121) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 121) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6072381503644771453432439315045893893687259353991618688439125815103032036378⟩ ⟨false, 238595416302712839022295704613104562166738512402321008915332962475516652612⟩ = true := by
  decide +kernel

theorem o_row_121 : oGrid.row evalE 121 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_121_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_121_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_121_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_121_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_121_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_121_2000).1 (bothLoop_sound b_121_2400).1))))))

theorem n_row_121 : nGrid.row evalE 121 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_121_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_121_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_121_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_121_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_121_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_121_2000).2 (bothLoop_sound b_121_2400).2))))))

theorem b_122_0 : bothSeg evalE (oGrid.idx 122) (oGrid.dm 122) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 122) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3338777716278288841467520585326672942834572721010287033227979507018881832496⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_122_400 : bothSeg evalE (oGrid.idx 122) (oGrid.dm 122) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 122) oGrid.kl oGrid.kr 400 400 ⟨false, 3338777716278288841467520585326672942834572721010287033227979507018881832496⟩ ⟨false, 0⟩ ⟨false, 5393250955403616280172967528957192272271885466898969430639071030634262804262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_122_800 : bothSeg evalE (oGrid.idx 122) (oGrid.dm 122) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 122) oGrid.kl oGrid.kr 400 800 ⟨false, 5393250955403616280172967528957192272271885466898969430639071030634262804262⟩ ⟨false, 0⟩ ⟨false, 6160522132033608499224009639921891869074963849477773556834199284586118880902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_122_1200 : bothSeg evalE (oGrid.idx 122) (oGrid.dm 122) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 122) oGrid.kl oGrid.kr 400 1200 ⟨false, 6160522132033608499224009639921891869074963849477773556834199284586118880902⟩ ⟨false, 0⟩ ⟨false, 6284285976492077718724028206426041933573203407579235957942159526255962599362⟩ ⟨false, 1942679657984126623986263294394362071233278061405841011615453904259307510⟩ = true := by
  decide +kernel

theorem b_122_1600 : bothSeg evalE (oGrid.idx 122) (oGrid.dm 122) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 122) oGrid.kl oGrid.kr 400 1600 ⟨false, 6284285976492077718724028206426041933573203407579235957942159526255962599362⟩ ⟨false, 1942679657984126623986263294394362071233278061405841011615453904259307510⟩ ⟨false, 6101640089290315308476475111422014610676947264586622873096988133011563578700⟩ ⟨false, 184859688509857786485436557966036099324240590299965254003958229785066160294⟩ = true := by
  decide +kernel

theorem b_122_2000 : bothSeg evalE (oGrid.idx 122) (oGrid.dm 122) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 122) oGrid.kl oGrid.kr 400 2000 ⟨false, 6101640089290315308476475111422014610676947264586622873096988133011563578700⟩ ⟨false, 184859688509857786485436557966036099324240590299965254003958229785066160294⟩ ⟨false, 6048820583432299278635913193172328622043161608938823399398458910692325024610⟩ ⟨false, 238413808928740666336310678641638575830918367453244456350972006902345746798⟩ = true := by
  decide +kernel

theorem b_122_2400 : bothLoop evalE (oGrid.idx 122) (oGrid.dm 122) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 122) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6048820583432299278635913193172328622043161608938823399398458910692325024610⟩ ⟨false, 238413808928740666336310678641638575830918367453244456350972006902345746798⟩ = true := by
  decide +kernel

theorem o_row_122 : oGrid.row evalE 122 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_122_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_122_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_122_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_122_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_122_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_122_2000).1 (bothLoop_sound b_122_2400).1))))))

theorem n_row_122 : nGrid.row evalE 122 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_122_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_122_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_122_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_122_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_122_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_122_2000).2 (bothLoop_sound b_122_2400).2))))))

theorem b_123_0 : bothSeg evalE (oGrid.idx 123) (oGrid.dm 123) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 123) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3326357035489293603042913163004410576733408950848651707327363920817059986456⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_123_400 : bothSeg evalE (oGrid.idx 123) (oGrid.dm 123) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 123) oGrid.kl oGrid.kr 400 400 ⟨false, 3326357035489293603042913163004410576733408950848651707327363920817059986456⟩ ⟨false, 0⟩ ⟨false, 5373339161501308509602810476518260661791051992786333621319350102516936488584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_123_800 : bothSeg evalE (oGrid.idx 123) (oGrid.dm 123) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 123) oGrid.kl oGrid.kr 400 800 ⟨false, 5373339161501308509602810476518260661791051992786333621319350102516936488584⟩ ⟨false, 0⟩ ⟨false, 6137630721083442482430769888094979352836914680764610985520909925148034357708⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_123_1200 : bothSeg evalE (oGrid.idx 123) (oGrid.dm 123) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 123) oGrid.kl oGrid.kr 400 1200 ⟨false, 6137630721083442482430769888094979352836914680764610985520909925148034357708⟩ ⟨false, 0⟩ ⟨false, 6260469467144109077135762932296634260731496703854843425967412398643284737960⟩ ⟨false, 2079948879424631562532708656831994600023744191406332004747338764633192236⟩ = true := by
  decide +kernel

theorem b_123_1600 : bothSeg evalE (oGrid.idx 123) (oGrid.dm 123) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 123) oGrid.kl oGrid.kr 400 1600 ⟨false, 6260469467144109077135762932296634260731496703854843425967412398643284737960⟩ ⟨false, 2079948879424631562532708656831994600023744191406332004747338764633192236⟩ ⟨false, 6077832252124800956702975739784053971500425951239268684229750818419728071568⟩ ⟨false, 184988999460224151277173869281886264583969726061158735797264260978502137754⟩ = true := by
  decide +kernel

theorem b_123_2000 : bothSeg evalE (oGrid.idx 123) (oGrid.dm 123) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 123) oGrid.kl oGrid.kr 400 2000 ⟨false, 6077832252124800956702975739784053971500425951239268684229750818419728071568⟩ ⟨false, 184988999460224151277173869281886264583969726061158735797264260978502137754⟩ ⟨false, 6025324578175018012806106841789966620897103260656989419637450276045166404606⟩ ⟨false, 238232982948350908722562922273663731873679086056920702360426955367120905938⟩ = true := by
  decide +kernel

theorem b_123_2400 : bothLoop evalE (oGrid.idx 123) (oGrid.dm 123) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 123) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6025324578175018012806106841789966620897103260656989419637450276045166404606⟩ ⟨false, 238232982948350908722562922273663731873679086056920702360426955367120905938⟩ = true := by
  decide +kernel

theorem o_row_123 : oGrid.row evalE 123 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_123_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_123_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_123_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_123_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_123_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_123_2000).1 (bothLoop_sound b_123_2400).1))))))

theorem n_row_123 : nGrid.row evalE 123 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_123_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_123_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_123_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_123_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_123_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_123_2000).2 (bothLoop_sound b_123_2400).2))))))

theorem b_124_0 : bothSeg evalE (oGrid.idx 124) (oGrid.dm 124) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 124) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3313973453200510277597362148011732281864845715650498252680892564908647839668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_124_400 : bothSeg evalE (oGrid.idx 124) (oGrid.dm 124) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 124) oGrid.kl oGrid.kr 400 400 ⟨false, 3313973453200510277597362148011732281864845715650498252680892564908647839668⟩ ⟨false, 0⟩ ⟨false, 5353483754876475912199209474086258057561335157319207374409904285820475826042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_124_800 : bothSeg evalE (oGrid.idx 124) (oGrid.dm 124) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 124) oGrid.kl oGrid.kr 400 800 ⟨false, 5353483754876475912199209474086258057561335157319207374409904285820475826042⟩ ⟨false, 0⟩ ⟨false, 6114802113553800456930547523680894425309185488583164407996296757510480228776⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_124_1200 : bothSeg evalE (oGrid.idx 124) (oGrid.dm 124) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 124) oGrid.kl oGrid.kr 400 1200 ⟨false, 6114802113553800456930547523680894425309185488583164407996296757510480228776⟩ ⟨false, 0⟩ ⟨false, 6236712728396976208532174141281030728295298093592858785850676582072353288758⟩ ⟨false, 2222887166214690210208146143192481104624259080561676127369570929291440180⟩ = true := by
  decide +kernel

theorem b_124_1600 : bothSeg evalE (oGrid.idx 124) (oGrid.dm 124) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 124) oGrid.kl oGrid.kr 400 1600 ⟨false, 6236712728396976208532174141281030728295298093592858785850676582072353288758⟩ ⟨false, 2222887166214690210208146143192481104624259080561676127369570929291440180⟩ ⟨false, 6054090829656966665397002836573398821315410550437261632061363371298754928390⟩ ⟨false, 185117126045120780318959996768978325498357005981354582475359773709819124608⟩ = true := by
  decide +kernel

theorem b_124_2000 : bothSeg evalE (oGrid.idx 124) (oGrid.dm 124) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 124) oGrid.kl oGrid.kr 400 2000 ⟨false, 6054090829656966665397002836573398821315410550437261632061363371298754928390⟩ ⟨false, 185117126045120780318959996768978325498357005981354582475359773709819124608⟩ ⟨false, 6001892992608475702645184523752277797283321844967472439396082265435395779834⟩ ⟨false, 238052780386220573635741896300493106580823332352160595379253124501005348184⟩ = true := by
  decide +kernel

theorem b_124_2400 : bothLoop evalE (oGrid.idx 124) (oGrid.dm 124) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 124) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6001892992608475702645184523752277797283321844967472439396082265435395779834⟩ ⟨false, 238052780386220573635741896300493106580823332352160595379253124501005348184⟩ = true := by
  decide +kernel

theorem o_row_124 : oGrid.row evalE 124 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_124_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_124_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_124_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_124_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_124_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_124_2000).1 (bothLoop_sound b_124_2400).1))))))

theorem n_row_124 : nGrid.row evalE 124 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_124_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_124_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_124_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_124_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_124_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_124_2000).2 (bothLoop_sound b_124_2400).2))))))

theorem b_125_0 : bothSeg evalE (oGrid.idx 125) (oGrid.dm 125) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 125) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3301626914686963603166041222713661107277112596801062795500934029401900527424⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_125_400 : bothSeg evalE (oGrid.idx 125) (oGrid.dm 125) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 125) oGrid.kl oGrid.kr 400 400 ⟨false, 3301626914686963603166041222713661107277112596801062795500934029401900527424⟩ ⟨false, 0⟩ ⟨false, 5333684691383577559161812718190317254074590632167047302907444510228725679680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_125_800 : bothSeg evalE (oGrid.idx 125) (oGrid.dm 125) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 125) oGrid.kl oGrid.kr 400 800 ⟨false, 5333684691383577559161812718190317254074590632167047302907444510228725679680⟩ ⟨false, 0⟩ ⟨false, 6092036287384924689293384859974344138289114891762018380453246926083094546566⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_125_1200 : bothSeg evalE (oGrid.idx 125) (oGrid.dm 125) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 125) oGrid.kl oGrid.kr 400 1200 ⟨false, 6092036287384924689293384859974344138289114891762018380453246926083094546566⟩ ⟨false, 0⟩ ⟨false, 6213015606689958533023381046610498493575055086722566397310800438601999975280⟩ ⟨false, 2371479566864890905508779899922978969474879815308742483461158774425474804⟩ = true := by
  decide +kernel

theorem b_125_1600 : bothSeg evalE (oGrid.idx 125) (oGrid.dm 125) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 125) oGrid.kl oGrid.kr 400 1600 ⟨false, 6213015606689958533023381046610498493575055086722566397310800438601999975280⟩ ⟨false, 2371479566864890905508779899922978969474879815308742483461158774425474804⟩ ⟨false, 6030416045203434877475198744347675727162715609748840385115894308960428750288⟩ ⟨false, 185244206639291804801517792793602628987310239273730014350475992883505325590⟩ = true := by
  decide +kernel

theorem b_125_2000 : bothSeg evalE (oGrid.idx 125) (oGrid.dm 125) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 125) oGrid.kl oGrid.kr 400 2000 ⟨false, 6030416045203434877475198744347675727162715609748840385115894308960428750288⟩ ⟨false, 185244206639291804801517792793602628987310239273730014350475992883505325590⟩ ⟨false, 5978526084812447083017448333207762024610151626059316532392639378915354699226⟩ ⟨false, 237873604881863754482839873161249827825517462996812982306132270573374698724⟩ = true := by
  decide +kernel

theorem b_125_2400 : bothLoop evalE (oGrid.idx 125) (oGrid.dm 125) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 125) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5978526084812447083017448333207762024610151626059316532392639378915354699226⟩ ⟨false, 237873604881863754482839873161249827825517462996812982306132270573374698724⟩ = true := by
  decide +kernel

theorem o_row_125 : oGrid.row evalE 125 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_125_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_125_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_125_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_125_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_125_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_125_2000).1 (bothLoop_sound b_125_2400).1))))))

theorem n_row_125 : nGrid.row evalE 125 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_125_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_125_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_125_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_125_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_125_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_125_2000).2 (bothLoop_sound b_125_2400).2))))))

theorem b_126_0 : bothSeg evalE (oGrid.idx 126) (oGrid.dm 126) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 126) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3289317308581424701487516497120419244364429681246044730116175385300279117918⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_126_400 : bothSeg evalE (oGrid.idx 126) (oGrid.dm 126) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 126) oGrid.kl oGrid.kr 400 400 ⟨false, 3289317308581424701487516497120419244364429681246044730116175385300279117918⟩ ⟨false, 0⟩ ⟨false, 5313941796093787313534440129920381926655843822215146444473285431133875343458⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_126_800 : bothSeg evalE (oGrid.idx 126) (oGrid.dm 126) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 126) oGrid.kl oGrid.kr 400 800 ⟨false, 5313941796093787313534440129920381926655843822215146444473285431133875343458⟩ ⟨false, 0⟩ ⟨false, 6069333022326481416939318337721849543944481233863386540067348503163103789020⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_126_1200 : bothSeg evalE (oGrid.idx 126) (oGrid.dm 126) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 126) oGrid.kl oGrid.kr 400 1200 ⟨false, 6069333022326481416939318337721849543944481233863386540067348503163103789020⟩ ⟨false, 0⟩ ⟨false, 6189377880726015278721460554383064992347857645678763033494186316089414473570⟩ ⟨false, 2525716545544937199915800852188513223682992569536221760222502682345698240⟩ = true := by
  decide +kernel

theorem b_126_1600 : bothSeg evalE (oGrid.idx 126) (oGrid.dm 126) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 126) oGrid.kl oGrid.kr 400 1600 ⟨false, 6189377880726015278721460554383064992347857645678763033494186316089414473570⟩ ⟨false, 2525716545544937199915800852188513223682992569536221760222502682345698240⟩ ⟨false, 6006807696898836147704587931785854666549214620097216800452862921063445184930⟩ ⟨false, 185369865018134354175555304381779031433598971571191950160728684424093609630⟩ = true := by
  decide +kernel

theorem b_126_2000 : bothSeg evalE (oGrid.idx 126) (oGrid.dm 126) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 126) oGrid.kl oGrid.kr 400 2000 ⟨false, 6006807696898836147704587931785854666549214620097216800452862921063445184930⟩ ⟨false, 185369865018134354175555304381779031433598971571191950160728684424093609630⟩ ⟨false, 5955223649849135810624885724579331767064596021056877766950973514021653308352⟩ ⟨false, 237694912216028079351270180625332364243254437779723647693921749811479724900⟩ = true := by
  decide +kernel

theorem b_126_2400 : bothLoop evalE (oGrid.idx 126) (oGrid.dm 126) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 126) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5955223649849135810624885724579331767064596021056877766950973514021653308352⟩ ⟨false, 237694912216028079351270180625332364243254437779723647693921749811479724900⟩ = true := by
  decide +kernel

theorem o_row_126 : oGrid.row evalE 126 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_126_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_126_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_126_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_126_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_126_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_126_2000).1 (bothLoop_sound b_126_2400).1))))))

theorem n_row_126 : nGrid.row evalE 126 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_126_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_126_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_126_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_126_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_126_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_126_2000).2 (bothLoop_sound b_126_2400).2))))))

theorem b_127_0 : bothSeg evalE (oGrid.idx 127) (oGrid.dm 127) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 127) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3277044520699037310889152553960018161237062470425096268975187822283561487604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_127_400 : bothSeg evalE (oGrid.idx 127) (oGrid.dm 127) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 127) oGrid.kl oGrid.kr 400 400 ⟨false, 3277044520699037310889152553960018161237062470425096268975187822283561487604⟩ ⟨false, 0⟩ ⟨false, 5294254928587858813853631624253197290408414014528059977248017417760755864066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_127_800 : bothSeg evalE (oGrid.idx 127) (oGrid.dm 127) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 127) oGrid.kl oGrid.kr 400 800 ⟨false, 5294254928587858813853631624253197290408414014528059977248017417760755864066⟩ ⟨false, 0⟩ ⟨false, 6046692192380529116582961543795019013852588786804992072622343873404745152862⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_127_1200 : bothSeg evalE (oGrid.idx 127) (oGrid.dm 127) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 127) oGrid.kl oGrid.kr 400 1200 ⟨false, 6046692192380529116582961543795019013852588786804992072622343873404745152862⟩ ⟨false, 0⟩ ⟨false, 6165799402789584008085609673391035752296140879494607882211143192340884651812⟩ ⟨false, 2685627102087817487412842483254266284387570702435287585864312287804418496⟩ = true := by
  decide +kernel

theorem b_127_1600 : bothSeg evalE (oGrid.idx 127) (oGrid.dm 127) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 127) oGrid.kl oGrid.kr 400 1600 ⟨false, 6165799402789584008085609673391035752296140879494607882211143192340884651812⟩ ⟨false, 2685627102087817487412842483254266284387570702435287585864312287804418496⟩ ⟨false, 5983265399625620653333511718220855267323450858760144308503362989159931249036⟩ ⟨false, 185494199847718339504296169558666585123971632238748989511629422483315301742⟩ = true := by
  decide +kernel

theorem b_127_2000 : bothSeg evalE (oGrid.idx 127) (oGrid.dm 127) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 127) oGrid.kl oGrid.kr 400 2000 ⟨false, 5983265399625620653333511718220855267323450858760144308503362989159931249036⟩ ⟨false, 185494199847718339504296169558666585123971632238748989511629422483315301742⟩ ⟨false, 5931985352501724321740534520099106612202073295554997866610477583024361317524⟩ ⟨false, 237516841049586138691620865750163443880498952044244634052367415405901103780⟩ = true := by
  decide +kernel

theorem b_127_2400 : bothLoop evalE (oGrid.idx 127) (oGrid.dm 127) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 127) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5931985352501724321740534520099106612202073295554997866610477583024361317524⟩ ⟨false, 237516841049586138691620865750163443880498952044244634052367415405901103780⟩ = true := by
  decide +kernel

theorem o_row_127 : oGrid.row evalE 127 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_127_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_127_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_127_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_127_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_127_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_127_2000).1 (bothLoop_sound b_127_2400).1))))))

theorem n_row_127 : nGrid.row evalE 127 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_127_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_127_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_127_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_127_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_127_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_127_2000).2 (bothLoop_sound b_127_2400).2))))))

theorem b_128_0 : bothSeg evalE (oGrid.idx 128) (oGrid.dm 128) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 128) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3264808432328414738772174618883146385080155744863028935907058866945949300240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_128_400 : bothSeg evalE (oGrid.idx 128) (oGrid.dm 128) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 128) oGrid.kl oGrid.kr 400 400 ⟨false, 3264808432328414738772174618883146385080155744863028935907058866945949300240⟩ ⟨false, 0⟩ ⟨false, 5274623946923079126372059936256335990008117095017765724629186103466924916836⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_128_800 : bothSeg evalE (oGrid.idx 128) (oGrid.dm 128) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 128) oGrid.kl oGrid.kr 400 800 ⟨false, 5274623946923079126372059936256335990008117095017765724629186103466924916836⟩ ⟨false, 0⟩ ⟨false, 6024113702456009539217304529065424433395989328156278116635016311393292329426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_128_1200 : bothSeg evalE (oGrid.idx 128) (oGrid.dm 128) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 128) oGrid.kl oGrid.kr 400 1200 ⟨false, 6024113702456009539217304529065424433395989328156278116635016311393292329426⟩ ⟨false, 0⟩ ⟨false, 6142279971536268114373252552947337999653699931425790044670238192169634076478⟩ ⟨false, 2851342359699236358992729458458326617774341107013189777178483126426450688⟩ = true := by
  decide +kernel

theorem b_128_1600 : bothSeg evalE (oGrid.idx 128) (oGrid.dm 128) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 128) oGrid.kl oGrid.kr 400 1600 ⟨false, 6142279971536268114373252552947337999653699931425790044670238192169634076478⟩ ⟨false, 2851342359699236358992729458458326617774341107013189777178483126426450688⟩ ⟨false, 5959789184448029810850170241268926056141789444864231955793073928472315446426⟩ ⟨false, 185617376156175504438742592622368074776509136713449635924889013547549324268⟩ = true := by
  decide +kernel

theorem b_128_2000 : bothSeg evalE (oGrid.idx 128) (oGrid.dm 128) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 128) oGrid.kl oGrid.kr 400 2000 ⟨false, 5959789184448029810850170241268926056141789444864231955793073928472315446426⟩ ⟨false, 185617376156175504438742592622368074776509136713449635924889013547549324268⟩ ⟨false, 5908811227579950942258245921095638799845285700382176229972849897851759965466⟩ ⟨false, 237339495300373964236726240133314176660330820639334157355375298252546081414⟩ = true := by
  decide +kernel

theorem b_128_2400 : bothLoop evalE (oGrid.idx 128) (oGrid.dm 128) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 128) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5908811227579950942258245921095638799845285700382176229972849897851759965466⟩ ⟨false, 237339495300373964236726240133314176660330820639334157355375298252546081414⟩ = true := by
  decide +kernel

theorem o_row_128 : oGrid.row evalE 128 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_128_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_128_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_128_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_128_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_128_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_128_2000).1 (bothLoop_sound b_128_2400).1))))))

theorem n_row_128 : nGrid.row evalE 128 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_128_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_128_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_128_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_128_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_128_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_128_2000).2 (bothLoop_sound b_128_2400).2))))))

theorem b_129_0 : bothSeg evalE (oGrid.idx 129) (oGrid.dm 129) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 129) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3252608967742427812692749993457604953810163050574692525106177248815221277526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_129_400 : bothSeg evalE (oGrid.idx 129) (oGrid.dm 129) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 129) oGrid.kl oGrid.kr 400 400 ⟨false, 3252608967742427812692749993457604953810163050574692525106177248815221277526⟩ ⟨false, 0⟩ ⟨false, 5255048696500537235777533818334899407640206648983328336524306943153924921234⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_129_800 : bothSeg evalE (oGrid.idx 129) (oGrid.dm 129) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 129) oGrid.kl oGrid.kr 400 800 ⟨false, 5255048696500537235777533818334899407640206648983328336524306943153924921234⟩ ⟨false, 0⟩ ⟨false, 6001597338877034006665454009611290097674308075359365040882047884703418958984⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_129_1200 : bothSeg evalE (oGrid.idx 129) (oGrid.dm 129) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 129) oGrid.kl oGrid.kr 400 1200 ⟨false, 6001597338877034006665454009611290097674308075359365040882047884703418958984⟩ ⟨false, 0⟩ ⟨false, 6118819429439285698180869768515462591525860282131283282683818048215298052106⟩ ⟨false, 3022777890516738678314447100341281914771565094820996822473555487412038708⟩ = true := by
  decide +kernel

theorem b_129_1600 : bothSeg evalE (oGrid.idx 129) (oGrid.dm 129) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 129) oGrid.kl oGrid.kr 400 1600 ⟨false, 6118819429439285698180869768515462591525860282131283282683818048215298052106⟩ ⟨false, 3022777890516738678314447100341281914771565094820996822473555487412038708⟩ ⟨false, 5936379005324850287567588045002687385212111921984265396562987958715109120968⟩ ⟨false, 185739153712847030664222440249511493700352524764576950314085518857398061152⟩ = true := by
  decide +kernel

theorem b_129_2000 : bothSeg evalE (oGrid.idx 129) (oGrid.dm 129) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 129) oGrid.kl oGrid.kr 400 2000 ⟨false, 5936379005324850287567588045002687385212111921984265396562987958715109120968⟩ ⟨false, 185739153712847030664222440249511493700352524764576950314085518857398061152⟩ ⟨false, 5885701253824618398347560189455796700950580317813510822787420953832904221604⟩ ⟨false, 237162631520053203926990335333986229240383622405720330617142558884178182406⟩ = true := by
  decide +kernel

theorem b_129_2400 : bothLoop evalE (oGrid.idx 129) (oGrid.dm 129) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 129) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5885701253824618398347560189455796700950580317813510822787420953832904221604⟩ ⟨false, 237162631520053203926990335333986229240383622405720330617142558884178182406⟩ = true := by
  decide +kernel

theorem o_row_129 : oGrid.row evalE 129 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_129_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_129_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_129_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_129_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_129_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_129_2000).1 (bothLoop_sound b_129_2400).1))))))

theorem n_row_129 : nGrid.row evalE 129 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_129_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_129_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_129_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_129_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_129_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_129_2000).2 (bothLoop_sound b_129_2400).2))))))

theorem b_130_0 : bothSeg evalE (oGrid.idx 130) (oGrid.dm 130) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 130) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3240446064389243340925649669848697428115264255467117594832367133454108742572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_130_400 : bothSeg evalE (oGrid.idx 130) (oGrid.dm 130) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 130) oGrid.kl oGrid.kr 400 400 ⟨false, 3240446064389243340925649669848697428115264255467117594832367133454108742572⟩ ⟨false, 0⟩ ⟨false, 5235529175699948497723697433905391648034431318065747722891392998980087708080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_130_800 : bothSeg evalE (oGrid.idx 130) (oGrid.dm 130) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 130) oGrid.kl oGrid.kr 400 800 ⟨false, 5235529175699948497723697433905391648034431318065747722891392998980087708080⟩ ⟨false, 0⟩ ⟨false, 5979143108576224791116564460325762195850946136358963228391746871846635241282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_130_1200 : bothSeg evalE (oGrid.idx 130) (oGrid.dm 130) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 130) oGrid.kl oGrid.kr 400 1200 ⟨false, 5979143108576224791116564460325762195850946136358963228391746871846635241282⟩ ⟨false, 0⟩ ⟨false, 6095417717155047829790452993178897033369088181647581814956886553438968221130⟩ ⟨false, 3200001988468828045515833067440514651868146876625343247876531835402166640⟩ = true := by
  decide +kernel

theorem b_130_1600 : bothSeg evalE (oGrid.idx 130) (oGrid.dm 130) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 130) oGrid.kl oGrid.kr 400 1600 ⟨false, 6095417717155047829790452993178897033369088181647581814956886553438968221130⟩ ⟨false, 3200001988468828045515833067440514651868146876625343247876531835402166640⟩ ⟨false, 5913034577360187278603977116634488113941165301356556079582477224952935155386⟩ ⟨false, 185860141003623964638256002933195814972782766254168441987095856933385974118⟩ = true := by
  decide +kernel

theorem b_130_2000 : bothSeg evalE (oGrid.idx 130) (oGrid.dm 130) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 130) oGrid.kl oGrid.kr 400 2000 ⟨false, 5913034577360187278603977116634488113941165301356556079582477224952935155386⟩ ⟨false, 185860141003623964638256002933195814972782766254168441987095856933385974118⟩ ⟨false, 5862655165598050350989534657391056830748939029378751489700186516740235021682⟩ ⟨false, 236986939031713552925310093401986724705810431697455267608879277988253464892⟩ = true := by
  decide +kernel

theorem b_130_2400 : bothLoop evalE (oGrid.idx 130) (oGrid.dm 130) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 130) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5862655165598050350989534657391056830748939029378751489700186516740235021682⟩ ⟨false, 236986939031713552925310093401986724705810431697455267608879277988253464892⟩ = true := by
  decide +kernel

theorem o_row_130 : oGrid.row evalE 130 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_130_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_130_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_130_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_130_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_130_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_130_2000).1 (bothLoop_sound b_130_2400).1))))))

theorem n_row_130 : nGrid.row evalE 130 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_130_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_130_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_130_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_130_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_130_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_130_2000).2 (bothLoop_sound b_130_2400).2))))))

theorem b_131_0 : bothSeg evalE (oGrid.idx 131) (oGrid.dm 131) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 131) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3228319571694747635064585576526756240376691496129166662991292571474365955852⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_131_400 : bothSeg evalE (oGrid.idx 131) (oGrid.dm 131) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 131) oGrid.kl oGrid.kr 400 400 ⟨false, 3228319571694747635064585576526756240376691496129166662991292571474365955852⟩ ⟨false, 0⟩ ⟨false, 5216065105288817213076585956978437120352656290018918111065335905991994305276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_131_800 : bothSeg evalE (oGrid.idx 131) (oGrid.dm 131) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 131) oGrid.kl oGrid.kr 400 800 ⟨false, 5216065105288817213076585956978437120352656290018918111065335905991994305276⟩ ⟨false, 0⟩ ⟨false, 5956750768055295377076015546148719080443173594198819667720943247237674096614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_131_1200 : bothSeg evalE (oGrid.idx 131) (oGrid.dm 131) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 131) oGrid.kl oGrid.kr 400 1200 ⟨false, 5956750768055295377076015546148719080443173594198819667720943247237674096614⟩ ⟨false, 0⟩ ⟨false, 6072074603600208903113858082959536046636670604577261402817035647523512535858⟩ ⟨false, 3383046349344435053848213727772935374649414492261357147833230488489381314⟩ = true := by
  decide +kernel

theorem b_131_1600 : bothSeg evalE (oGrid.idx 131) (oGrid.dm 131) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 131) oGrid.kl oGrid.kr 400 1600 ⟨false, 6072074603600208903113858082959536046636670604577261402817035647523512535858⟩ ⟨false, 3383046349344435053848213727772935374649414492261357147833230488489381314⟩ ⟨false, 5889755845207884587920286322382778205276779786185330656724132124582979397154⟩ ⟨false, 185979510734242069108318446266541753664898740090581526457864041286551576796⟩ = true := by
  decide +kernel

theorem b_131_2000 : bothSeg evalE (oGrid.idx 131) (oGrid.dm 131) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 131) oGrid.kl oGrid.kr 400 2000 ⟨false, 5889755845207884587920286322382778205276779786185330656724132124582979397154⟩ ⟨false, 185979510734242069108318446266541753664898740090581526457864041286551576796⟩ ⟨false, 5839672924514256975605536277448716893621797972793316525283522397152382680454⟩ ⟨false, 236811265523022468187618858497825557586837364104412280931173527580749440120⟩ = true := by
  decide +kernel

theorem b_131_2400 : bothLoop evalE (oGrid.idx 131) (oGrid.dm 131) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 131) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5839672924514256975605536277448716893621797972793316525283522397152382680454⟩ ⟨false, 236811265523022468187618858497825557586837364104412280931173527580749440120⟩ = true := by
  decide +kernel

theorem o_row_131 : oGrid.row evalE 131 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_131_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_131_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_131_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_131_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_131_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_131_2000).1 (bothLoop_sound b_131_2400).1))))))

theorem n_row_131 : nGrid.row evalE 131 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_131_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_131_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_131_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_131_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_131_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_131_2000).2 (bothLoop_sound b_131_2400).2))))))

theorem b_132_0 : bothSeg evalE (oGrid.idx 132) (oGrid.dm 132) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 132) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3216229445375467430961315108933751307115273151324534423217511092160498026864⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_132_400 : bothSeg evalE (oGrid.idx 132) (oGrid.dm 132) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 132) oGrid.kl oGrid.kr 400 400 ⟨false, 3216229445375467430961315108933751307115273151324534423217511092160498026864⟩ ⟨false, 0⟩ ⟨false, 5196656465782292839396762931964389877837691558269417114308432094909903060972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_132_800 : bothSeg evalE (oGrid.idx 132) (oGrid.dm 132) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 132) oGrid.kl oGrid.kr 400 800 ⟨false, 5196656465782292839396762931964389877837691558269417114308432094909903060972⟩ ⟨false, 0⟩ ⟨false, 5934420254872330734303964880258096624267565498008534323189552319784379102554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_132_1200 : bothSeg evalE (oGrid.idx 132) (oGrid.dm 132) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 132) oGrid.kl oGrid.kr 400 1200 ⟨false, 5934420254872330734303964880258096624267565498008534323189552319784379102554⟩ ⟨false, 0⟩ ⟨false, 6048790010596567836425619948672578858488388040717284255613229932884625529278⟩ ⟨false, 3572079911716938958137891581861591324953911121874409344782854128312473422⟩ = true := by
  decide +kernel

theorem b_132_1600 : bothSeg evalE (oGrid.idx 132) (oGrid.dm 132) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 132) oGrid.kl oGrid.kr 400 1600 ⟨false, 6048790010596567836425619948672578858488388040717284255613229932884625529278⟩ ⟨false, 3572079911716938958137891581861591324953911121874409344782854128312473422⟩ ⟨false, 5866542718452630002269475082004191874568120002441269920793444834830882030466⟩ ⟨false, 186097670974964777251884811368660408397239900744446236851443865550310662916⟩ = true := by
  decide +kernel

theorem b_132_2000 : bothSeg evalE (oGrid.idx 132) (oGrid.dm 132) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 132) oGrid.kl oGrid.kr 400 2000 ⟨false, 5866542718452630002269475082004191874568120002441269920793444834830882030466⟩ ⟨false, 186097670974964777251884811368660408397239900744446236851443865550310662916⟩ ⟨false, 5816754463782033071681023589519799294253204972834533892558616945807957647312⟩ ⟨false, 236636528854885325770774452892335916996025531552874431595222733698335200126⟩ = true := by
  decide +kernel

theorem b_132_2400 : bothLoop evalE (oGrid.idx 132) (oGrid.dm 132) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 132) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5816754463782033071681023589519799294253204972834533892558616945807957647312⟩ ⟨false, 236636528854885325770774452892335916996025531552874431595222733698335200126⟩ = true := by
  decide +kernel

theorem o_row_132 : oGrid.row evalE 132 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_132_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_132_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_132_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_132_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_132_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_132_2000).1 (bothLoop_sound b_132_2400).1))))))

theorem n_row_132 : nGrid.row evalE 132 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_132_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_132_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_132_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_132_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_132_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_132_2000).2 (bothLoop_sound b_132_2400).2))))))

theorem b_133_0 : bothSeg evalE (oGrid.idx 133) (oGrid.dm 133) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 133) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3204175562335746954567520427515116772573591911193431453252286016882761474720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_133_400 : bothSeg evalE (oGrid.idx 133) (oGrid.dm 133) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 133) oGrid.kl oGrid.kr 400 400 ⟨false, 3204175562335746954567520427515116772573591911193431453252286016882761474720⟩ ⟨false, 0⟩ ⟨false, 5177303085326445666046659662807045777508860023435672211060644898443452720434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_133_800 : bothSeg evalE (oGrid.idx 133) (oGrid.dm 133) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 133) oGrid.kl oGrid.kr 400 800 ⟨false, 5177303085326445666046659662807045777508860023435672211060644898443452720434⟩ ⟨false, 0⟩ ⟨false, 5912151405164191182305128623253667507663414926714997786304391574991895304632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_133_1200 : bothSeg evalE (oGrid.idx 133) (oGrid.dm 133) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 133) oGrid.kl oGrid.kr 400 1200 ⟨false, 5912151405164191182305128623253667507663414926714997786304391574991895304632⟩ ⟨false, 0⟩ ⟨false, 6025563760610585134932133475937726237575381307499971880947396264323715050358⟩ ⟨false, 3767052213809892556923869190274146979563442529296172653114626770610024194⟩ = true := by
  decide +kernel

theorem b_133_1600 : bothSeg evalE (oGrid.idx 133) (oGrid.dm 133) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 133) oGrid.kl oGrid.kr 400 1600 ⟨false, 6025563760610585134932133475937726237575381307499971880947396264323715050358⟩ ⟨false, 3767052213809892556923869190274146979563442529296172653114626770610024194⟩ ⟨false, 5843395102955811116734577784879379416456432622861846944622562590215088669334⟩ ⟨false, 186214433746512173411713895161405907296175291412248054504121444723582004774⟩ = true := by
  decide +kernel

theorem b_133_2000 : bothSeg evalE (oGrid.idx 133) (oGrid.dm 133) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 133) oGrid.kl oGrid.kr 400 2000 ⟨false, 5843395102955811116734577784879379416456432622861846944622562590215088669334⟩ ⟨false, 186214433746512173411713895161405907296175291412248054504121444723582004774⟩ ⟨false, 5793899695550941756749592441705990569110511419683798621369852734459067136014⟩ ⟨false, 236461888313025161537334690355765089733946884818776815324162979378572101700⟩ = true := by
  decide +kernel

theorem b_133_2400 : bothLoop evalE (oGrid.idx 133) (oGrid.dm 133) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 133) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5793899695550941756749592441705990569110511419683798621369852734459067136014⟩ ⟨false, 236461888313025161537334690355765089733946884818776815324162979378572101700⟩ = true := by
  decide +kernel

theorem o_row_133 : oGrid.row evalE 133 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_133_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_133_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_133_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_133_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_133_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_133_2000).1 (bothLoop_sound b_133_2400).1))))))

theorem n_row_133 : nGrid.row evalE 133 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_133_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_133_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_133_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_133_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_133_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_133_2000).2 (bothLoop_sound b_133_2400).2))))))

theorem b_134_0 : bothSeg evalE (oGrid.idx 134) (oGrid.dm 134) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 134) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3192157788771444389640055600511596596296957295406602630070144756408940332466⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_134_400 : bothSeg evalE (oGrid.idx 134) (oGrid.dm 134) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 134) oGrid.kl oGrid.kr 400 400 ⟨false, 3192157788771444389640055600511596596296957295406602630070144756408940332466⟩ ⟨false, 0⟩ ⟨false, 5158004804401226841129637623992719379094773204887297403756911543924180962662⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_134_800 : bothSeg evalE (oGrid.idx 134) (oGrid.dm 134) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 134) oGrid.kl oGrid.kr 400 800 ⟨false, 5158004804401226841129637623992719379094773204887297403756911543924180962662⟩ ⟨false, 0⟩ ⟨false, 5889944087664196971578631556700911531532561191079915712731078940761686322004⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_134_1200 : bothSeg evalE (oGrid.idx 134) (oGrid.dm 134) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 134) oGrid.kl oGrid.kr 400 1200 ⟨false, 5889944087664196971578631556700911531532561191079915712731078940761686322004⟩ ⟨false, 0⟩ ⟨false, 6002395710368158087059533492823157685330316309046240328988975972316111797738⟩ ⟨false, 3967840523312064717294114885109632587647199817775067749934811872328118748⟩ = true := by
  decide +kernel

theorem b_134_1600 : bothSeg evalE (oGrid.idx 134) (oGrid.dm 134) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 134) oGrid.kl oGrid.kr 400 1600 ⟨false, 6002395710368158087059533492823157685330316309046240328988975972316111797738⟩ ⟨false, 3967840523312064717294114885109632587647199817775067749934811872328118748⟩ ⟨false, 5820312602641701844510970471903683637611131937157410690943696869001044478932⟩ ⟨false, 186330399158854657261919766218911103536973842646692197885745829631004642780⟩ = true := by
  decide +kernel

theorem b_134_2000 : bothSeg evalE (oGrid.idx 134) (oGrid.dm 134) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 134) oGrid.kl oGrid.kr 400 2000 ⟨false, 5820312602641701844510970471903683637611131937157410690943696869001044478932⟩ ⟨false, 186330399158854657261919766218911103536973842646692197885745829631004642780⟩ ⟨false, 5771108261629350046043136386885103200993838303975961835609598921490928619066⟩ ⟨false, 236288531474920903983955943705756063134852412763996195892868198349464222320⟩ = true := by
  decide +kernel

theorem b_134_2400 : bothLoop evalE (oGrid.idx 134) (oGrid.dm 134) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 134) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5771108261629350046043136386885103200993838303975961835609598921490928619066⟩ ⟨false, 236288531474920903983955943705756063134852412763996195892868198349464222320⟩ = true := by
  decide +kernel

theorem o_row_134 : oGrid.row evalE 134 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_134_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_134_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_134_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_134_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_134_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_134_2000).1 (bothLoop_sound b_134_2400).1))))))

theorem n_row_134 : nGrid.row evalE 134 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_134_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_134_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_134_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_134_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_134_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_134_2000).2 (bothLoop_sound b_134_2400).2))))))

theorem b_135_0 : bothSeg evalE (oGrid.idx 135) (oGrid.dm 135) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 135) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3180176025248059175066819873503898108942323071993073547160808808411434470732⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_135_400 : bothSeg evalE (oGrid.idx 135) (oGrid.dm 135) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 135) oGrid.kl oGrid.kr 400 400 ⟨false, 3180176025248059175066819873503898108942323071993073547160808808411434470732⟩ ⟨false, 0⟩ ⟨false, 5138761505744303915880914873760240672546196441322206097487415867882803499832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_135_800 : bothSeg evalE (oGrid.idx 135) (oGrid.dm 135) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 135) oGrid.kl oGrid.kr 400 800 ⟨false, 5138761505744303915880914873760240672546196441322206097487415867882803499832⟩ ⟨false, 0⟩ ⟨false, 5867798150046458684645143612334599881496012626817784900555880808548319389746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_135_1200 : bothSeg evalE (oGrid.idx 135) (oGrid.dm 135) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 135) oGrid.kl oGrid.kr 400 1200 ⟨false, 5867798150046458684645143612334599881496012626817784900555880808548319389746⟩ ⟨false, 0⟩ ⟨false, 5979285756692653084577521995876215334827729437452379520049347882972068537792⟩ ⟨false, 4174418036155990068048964415372166843864846048610349753625900334507763690⟩ = true := by
  decide +kernel

theorem b_135_1600 : bothSeg evalE (oGrid.idx 135) (oGrid.dm 135) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 135) oGrid.kl oGrid.kr 400 1600 ⟨false, 5979285756692653084577521995876215334827729437452379520049347882972068537792⟩ ⟨false, 4174418036155990068048964415372166843864846048610349753625900334507763690⟩ ⟨false, 5797295293889523680019365972407255220280772160834810773465148691809701332192⟩ ⟨false, 186445500001060172818458752847795773377693154043607928105987954057857221424⟩ = true := by
  decide +kernel

theorem b_135_2000 : bothSeg evalE (oGrid.idx 135) (oGrid.dm 135) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 135) oGrid.kl oGrid.kr 400 2000 ⟨false, 5797295293889523680019365972407255220280772160834810773465148691809701332192⟩ ⟨false, 186445500001060172818458752847795773377693154043607928105987954057857221424⟩ ⟨false, 5748380264869187133807603974767140922662272290468242332871822152523146649752⟩ ⟨false, 236115876077665949184809199954197976046138313165928665451389541224705908668⟩ = true := by
  decide +kernel

theorem b_135_2400 : bothLoop evalE (oGrid.idx 135) (oGrid.dm 135) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 135) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5748380264869187133807603974767140922662272290468242332871822152523146649752⟩ ⟨false, 236115876077665949184809199954197976046138313165928665451389541224705908668⟩ = true := by
  decide +kernel

theorem o_row_135 : oGrid.row evalE 135 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_135_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_135_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_135_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_135_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_135_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_135_2000).1 (bothLoop_sound b_135_2400).1))))))

theorem n_row_135 : nGrid.row evalE 135 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_135_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_135_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_135_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_135_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_135_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_135_2000).2 (bothLoop_sound b_135_2400).2))))))

theorem b_136_0 : bothSeg evalE (oGrid.idx 136) (oGrid.dm 136) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 136) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3168230247905840655004576728780443755678232627190830052988747669039384404890⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_136_400 : bothSeg evalE (oGrid.idx 136) (oGrid.dm 136) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 136) oGrid.kl oGrid.kr 400 400 ⟨false, 3168230247905840655004576728780443755678232627190830052988747669039384404890⟩ ⟨false, 0⟩ ⟨false, 5119573081997941063137783486754735649887235378188187043666713499021879573898⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_136_800 : bothSeg evalE (oGrid.idx 136) (oGrid.dm 136) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 136) oGrid.kl oGrid.kr 400 800 ⟨false, 5119573081997941063137783486754735649887235378188187043666713499021879573898⟩ ⟨false, 0⟩ ⟨false, 5845713486989954902802281468047300483219788343767283766278449698158226696280⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_136_1200 : bothSeg evalE (oGrid.idx 136) (oGrid.dm 136) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 136) oGrid.kl oGrid.kr 400 1200 ⟨false, 5845713486989954902802281468047300483219788343767283766278449698158226696280⟩ ⟨false, 0⟩ ⟨false, 5956233769793354799527626505921419718773570260286139811696899889990241750856⟩ ⟨false, 4386797893171210803142082591168182444793854822210724065112083854969030370⟩ = true := by
  decide +kernel

theorem b_136_1600 : bothSeg evalE (oGrid.idx 136) (oGrid.dm 136) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 136) oGrid.kl oGrid.kr 400 1600 ⟨false, 5956233769793354799527626505921419718773570260286139811696899889990241750856⟩ ⟨false, 4386797893171210803142082591168182444793854822210724065112083854969030370⟩ ⟨false, 5774343100023545776540694186585389481835570981762047654922148633704933764442⟩ ⟨false, 186558965437662302302610439132477361768069877191675105093556113609788445238⟩ = true := by
  decide +kernel

theorem b_136_2000 : bothSeg evalE (oGrid.idx 136) (oGrid.dm 136) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 136) oGrid.kl oGrid.kr 400 2000 ⟨false, 5774343100023545776540694186585389481835570981762047654922148633704933764442⟩ ⟨false, 186558965437662302302610439132477361768069877191675105093556113609788445238⟩ ⟨false, 5725715638787855625029007407944081990071910463729130422521972197228531395934⟩ ⟨false, 235943378994426131723666309748177373276888565537183868516184896922765437638⟩ = true := by
  decide +kernel

theorem b_136_2400 : bothLoop evalE (oGrid.idx 136) (oGrid.dm 136) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 136) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5725715638787855625029007407944081990071910463729130422521972197228531395934⟩ ⟨false, 235943378994426131723666309748177373276888565537183868516184896922765437638⟩ = true := by
  decide +kernel

theorem o_row_136 : oGrid.row evalE 136 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_136_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_136_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_136_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_136_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_136_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_136_2000).1 (bothLoop_sound b_136_2400).1))))))

theorem n_row_136 : nGrid.row evalE 136 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_136_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_136_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_136_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_136_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_136_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_136_2000).2 (bothLoop_sound b_136_2400).2))))))

theorem b_137_0 : bothSeg evalE (oGrid.idx 137) (oGrid.dm 137) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 137) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3156320334267592029895329570991342013383260716975558371742072467511436401650⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_137_400 : bothSeg evalE (oGrid.idx 137) (oGrid.dm 137) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 137) oGrid.kl oGrid.kr 400 400 ⟨false, 3156320334267592029895329570991342013383260716975558371742072467511436401650⟩ ⟨false, 0⟩ ⟨false, 5100439407803351516640414600722606528755879441257981164443217947675442801812⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_137_800 : bothSeg evalE (oGrid.idx 137) (oGrid.dm 137) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 137) oGrid.kl oGrid.kr 400 800 ⟨false, 5100439407803351516640414600722606528755879441257981164443217947675442801812⟩ ⟨false, 0⟩ ⟨false, 5823690000004334890244397292725619309882230928880261229758538840857098311928⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_137_1200 : bothSeg evalE (oGrid.idx 137) (oGrid.dm 137) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 137) oGrid.kl oGrid.kr 400 1200 ⟨false, 5823690000004334890244397292725619309882230928880261229758538840857098311928⟩ ⟨false, 0⟩ ⟨false, 5933239663854449533526324475175303743979809477538682985320271030223869180812⟩ ⟨false, 4604976109925554229290967202044597761862162407530700791742108606543467494⟩ = true := by
  decide +kernel

theorem b_137_1600 : bothSeg evalE (oGrid.idx 137) (oGrid.dm 137) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 137) oGrid.kl oGrid.kr 400 1600 ⟨false, 5933239663854449533526324475175303743979809477538682985320271030223869180812⟩ ⟨false, 4604976109925554229290967202044597761862162407530700791742108606543467494⟩ ⟨false, 5751455604743056342202191289182784869006411335139084946314307439865186507296⟩ ⟨false, 186671261264018033411713259748080289812295434367437340882293194907146491576⟩ = true := by
  decide +kernel

theorem b_137_2000 : bothSeg evalE (oGrid.idx 137) (oGrid.dm 137) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 137) oGrid.kl oGrid.kr 400 2000 ⟨false, 5751455604743056342202191289182784869006411335139084946314307439865186507296⟩ ⟨false, 186671261264018033411713259748080289812295434367437340882293194907146491576⟩ ⟨false, 5703113994586438407865704815680188386474198468742843830989761626139247123154⟩ ⟨false, 235771491097333572843797845727619212686680281824378130049215635644061034806⟩ = true := by
  decide +kernel

theorem b_137_2400 : bothLoop evalE (oGrid.idx 137) (oGrid.dm 137) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 137) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5703113994586438407865704815680188386474198468742843830989761626139247123154⟩ ⟨false, 235771491097333572843797845727619212686680281824378130049215635644061034806⟩ = true := by
  decide +kernel

theorem o_row_137 : oGrid.row evalE 137 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_137_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_137_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_137_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_137_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_137_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_137_2000).1 (bothLoop_sound b_137_2400).1))))))

theorem n_row_137 : nGrid.row evalE 137 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_137_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_137_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_137_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_137_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_137_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_137_2000).2 (bothLoop_sound b_137_2400).2))))))

theorem b_138_0 : bothSeg evalE (oGrid.idx 138) (oGrid.dm 138) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 138) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3144446168407637664960402859341939248108670761005600070120915789150470617898⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_138_400 : bothSeg evalE (oGrid.idx 138) (oGrid.dm 138) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 138) oGrid.kl oGrid.kr 400 400 ⟨false, 3144446168407637664960402859341939248108670761005600070120915789150470617898⟩ ⟨false, 0⟩ ⟨false, 5081360352865709454876697278345266963101215044644806457141485874909698766950⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_138_800 : bothSeg evalE (oGrid.idx 138) (oGrid.dm 138) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 138) oGrid.kl oGrid.kr 400 800 ⟨false, 5081360352865709454876697278345266963101215044644806457141485874909698766950⟩ ⟨false, 0⟩ ⟨false, 5801727529226359550177446771369304688920519218372519809574039910145250882350⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_138_1200 : bothSeg evalE (oGrid.idx 138) (oGrid.dm 138) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 138) oGrid.kl oGrid.kr 400 1200 ⟨false, 5801727529226359550177446771369304688920519218372519809574039910145250882350⟩ ⟨false, 0⟩ ⟨false, 5910303361857523832998134063520521600752081819814963295344344283373987245546⟩ ⟨false, 4828899852339792844150780857818059588387281360896549180258751713017514270⟩ = true := by
  decide +kernel

theorem b_138_1600 : bothSeg evalE (oGrid.idx 138) (oGrid.dm 138) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 138) oGrid.kl oGrid.kr 400 1600 ⟨false, 5910303361857523832998134063520521600752081819814963295344344283373987245546⟩ ⟨false, 4828899852339792844150780857818059588387281360896549180258751713017514270⟩ ⟨false, 5728632911955433719966792800700725386180405391243297444333897334136676052456⟩ ⟨false, 186782078131495875410562365144932911667990264971075221539585432462843101520⟩ = true := by
  decide +kernel

theorem b_138_2000 : bothSeg evalE (oGrid.idx 138) (oGrid.dm 138) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 138) oGrid.kl oGrid.kr 400 2000 ⟨false, 5728632911955433719966792800700725386180405391243297444333897334136676052456⟩ ⟨false, 186782078131495875410562365144932911667990264971075221539585432462843101520⟩ ⟨false, 5680575471728779609423499310367424857873886241459528657556125217801066327646⟩ ⟨false, 235599682672919002830080086331277603258610924984003833389876180853503876462⟩ = true := by
  decide +kernel

theorem b_138_2400 : bothLoop evalE (oGrid.idx 138) (oGrid.dm 138) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 138) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5680575471728779609423499310367424857873886241459528657556125217801066327646⟩ ⟨false, 235599682672919002830080086331277603258610924984003833389876180853503876462⟩ = true := by
  decide +kernel

theorem o_row_138 : oGrid.row evalE 138 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_138_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_138_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_138_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_138_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_138_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_138_2000).1 (bothLoop_sound b_138_2400).1))))))

theorem n_row_138 : nGrid.row evalE 138 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_138_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_138_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_138_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_138_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_138_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_138_2000).2 (bothLoop_sound b_138_2400).2))))))

theorem b_139_0 : bothSeg evalE (oGrid.idx 139) (oGrid.dm 139) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 139) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3132607683140279844333899610988473193247892745284496107367824148590523792684⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_139_400 : bothSeg evalE (oGrid.idx 139) (oGrid.dm 139) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 139) oGrid.kl oGrid.kr 400 400 ⟨false, 3132607683140279844333899610988473193247892745284496107367824148590523792684⟩ ⟨false, 0⟩ ⟨false, 5062335817677379005392778565054850304868519102788091887374403857965629332538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_139_800 : bothSeg evalE (oGrid.idx 139) (oGrid.dm 139) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 139) oGrid.kl oGrid.kr 400 800 ⟨false, 5062335817677379005392778565054850304868519102788091887374403857965629332538⟩ ⟨false, 0⟩ ⟨false, 5779825976151089157504769910510002609606236779317500250414417820519779053280⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_139_1200 : bothSeg evalE (oGrid.idx 139) (oGrid.dm 139) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 139) oGrid.kl oGrid.kr 400 1200 ⟨false, 5779825976151089157504769910510002609606236779317500250414417820519779053280⟩ ⟨false, 0⟩ ⟨false, 5887424793770881099401195844084204961824233597757125389967904667686266798014⟩ ⟨false, 5058530514427984043999261904037982417868379390344135722726874419397167120⟩ = true := by
  decide +kernel

theorem b_139_1600 : bothSeg evalE (oGrid.idx 139) (oGrid.dm 139) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 139) oGrid.kl oGrid.kr 400 1600 ⟨false, 5887424793770881099401195844084204961824233597757125389967904667686266798014⟩ ⟨false, 5058530514427984043999261904037982417868379390344135722726874419397167120⟩ ⟨false, 5705875097314130763874370790859775080944634204543934393197843456591470614314⟩ ⟨false, 186891269661117773371721210453390213358797103320082716283396859981161631460⟩ = true := by
  decide +kernel

theorem b_139_2000 : bothSeg evalE (oGrid.idx 139) (oGrid.dm 139) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 139) oGrid.kl oGrid.kr 400 2000 ⟨false, 5705875097314130763874370790859775080944634204543934393197843456591470614314⟩ ⟨false, 186891269661117773371721210453390213358797103320082716283396859981161631460⟩ ⟨false, 5658100153505894883519672399690105198236935884584266180380616249009067102372⟩ ⟨false, 235428077491478974031094856421388540361361402773047191975177043484846513392⟩ = true := by
  decide +kernel

theorem b_139_2400 : bothLoop evalE (oGrid.idx 139) (oGrid.dm 139) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 139) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5658100153505894883519672399690105198236935884584266180380616249009067102372⟩ ⟨false, 235428077491478974031094856421388540361361402773047191975177043484846513392⟩ = true := by
  decide +kernel

theorem o_row_139 : oGrid.row evalE 139 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_139_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_139_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_139_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_139_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_139_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_139_2000).1 (bothLoop_sound b_139_2400).1))))))

theorem n_row_139 : nGrid.row evalE 139 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_139_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_139_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_139_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_139_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_139_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_139_2000).2 (bothLoop_sound b_139_2400).2))))))

theorem b_140_0 : bothSeg evalE (oGrid.idx 140) (oGrid.dm 140) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 140) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3120804763041290354978774983994908121543854036705758322782692455819109889336⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_140_400 : bothSeg evalE (oGrid.idx 140) (oGrid.dm 140) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 140) oGrid.kl oGrid.kr 400 400 ⟨false, 3120804763041290354978774983994908121543854036705758322782692455819109889336⟩ ⟨false, 0⟩ ⟨false, 5043365654422194785870442370670795473893477400217102324306899248430294122450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_140_800 : bothSeg evalE (oGrid.idx 140) (oGrid.dm 140) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 140) oGrid.kl oGrid.kr 400 800 ⟨false, 5043365654422194785870442370670795473893477400217102324306899248430294122450⟩ ⟨false, 0⟩ ⟨false, 5757985219014682072960189621556407091708606397290952592549873237286575895878⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_140_1200 : bothSeg evalE (oGrid.idx 140) (oGrid.dm 140) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 140) oGrid.kl oGrid.kr 400 1200 ⟨false, 5757985219014682072960189621556407091708606397290952592549873237286575895878⟩ ⟨false, 0⟩ ⟨false, 5864603827967471211557760539318078806815520381647331995720686211309761738238⟩ ⟨false, 5293866735730868399857138673332999337782440985940748325152447049922750534⟩ = true := by
  decide +kernel

theorem b_140_1600 : bothSeg evalE (oGrid.idx 140) (oGrid.dm 140) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 140) oGrid.kl oGrid.kr 400 1600 ⟨false, 5864603827967471211557760539318078806815520381647331995720686211309761738238⟩ ⟨false, 5293866735730868399857138673332999337782440985940748325152447049922750534⟩ ⟨false, 5683181531063631811724512502959070807732662142986508217923941796653693168498⟩ ⟨false, 187000227404930228948768983928062843852436803400733440687218469905699619600⟩ = true := by
  decide +kernel

theorem b_140_2000 : bothSeg evalE (oGrid.idx 140) (oGrid.dm 140) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 140) oGrid.kl oGrid.kr 400 2000 ⟨false, 5683181531063631811724512502959070807732662142986508217923941796653693168498⟩ ⟨false, 187000227404930228948768983928062843852436803400733440687218469905699619600⟩ ⟨false, 5635687428756101480827385484855910191156578278842778421513095033772373227626⟩ ⟨false, 235257703858615637660473264463161819484659520630080933176320904538574364782⟩ = true := by
  decide +kernel

theorem b_140_2400 : bothLoop evalE (oGrid.idx 140) (oGrid.dm 140) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 140) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5635687428756101480827385484855910191156578278842778421513095033772373227626⟩ ⟨false, 235257703858615637660473264463161819484659520630080933176320904538574364782⟩ = true := by
  decide +kernel

theorem o_row_140 : oGrid.row evalE 140 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_140_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_140_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_140_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_140_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_140_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_140_2000).1 (bothLoop_sound b_140_2400).1))))))

theorem n_row_140 : nGrid.row evalE 140 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_140_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_140_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_140_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_140_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_140_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_140_2000).2 (bothLoop_sound b_140_2400).2))))))

theorem b_141_0 : bothSeg evalE (oGrid.idx 141) (oGrid.dm 141) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 141) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3109037262466390978374946131929379063950723103854933906002482141478707362040⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_141_400 : bothSeg evalE (oGrid.idx 141) (oGrid.dm 141) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 141) oGrid.kl oGrid.kr 400 400 ⟨false, 3109037262466390978374946131929379063950723103854933906002482141478707362040⟩ ⟨false, 0⟩ ⟨false, 5024449633038318367583324042504006497979265266715740725737406884794308900528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_141_800 : bothSeg evalE (oGrid.idx 141) (oGrid.dm 141) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 141) oGrid.kl oGrid.kr 400 800 ⟨false, 5024449633038318367583324042504006497979265266715740725737406884794308900528⟩ ⟨false, 0⟩ ⟨false, 5736204997774377682886851082820605129164583212584366975201467583133880201356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_141_1200 : bothSeg evalE (oGrid.idx 141) (oGrid.dm 141) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 141) oGrid.kl oGrid.kr 400 1200 ⟨false, 5736204997774377682886851082820605129164583212584366975201467583133880201356⟩ ⟨false, 0⟩ ⟨false, 5841840272823713101285981412449735485024285466401052842513028222554208701636⟩ ⟨false, 5534831300650103127670376431352267246869576390332946110519576416301313856⟩ = true := by
  decide +kernel

theorem b_141_1600 : bothSeg evalE (oGrid.idx 141) (oGrid.dm 141) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 141) oGrid.kl oGrid.kr 400 1600 ⟨false, 5841840272823713101285981412449735485024285466401052842513028222554208701636⟩ ⟨false, 5534831300650103127670376431352267246869576390332946110519576416301313856⟩ ⟨false, 5660552315781971377439095946166655224097578908512512659757750343090251605134⟩ ⟨false, 187107984143263768699988503874726281262326495990543964089914944288181607172⟩ = true := by
  decide +kernel

theorem b_141_2000 : bothSeg evalE (oGrid.idx 141) (oGrid.dm 141) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 141) oGrid.kl oGrid.kr 400 2000 ⟨false, 5660552315781971377439095946166655224097578908512512659757750343090251605134⟩ ⟨false, 187107984143263768699988503874726281262326495990543964089914944288181607172⟩ ⟨false, 5613337455001012522336828782136042039710625185778403101884803804353357985736⟩ ⟨false, 235087951117332772524925472098652118856654149027243448379114768430358500126⟩ = true := by
  decide +kernel

theorem b_141_2400 : bothLoop evalE (oGrid.idx 141) (oGrid.dm 141) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 141) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5613337455001012522336828782136042039710625185778403101884803804353357985736⟩ ⟨false, 235087951117332772524925472098652118856654149027243448379114768430358500126⟩ = true := by
  decide +kernel

theorem o_row_141 : oGrid.row evalE 141 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_141_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_141_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_141_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_141_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_141_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_141_2000).1 (bothLoop_sound b_141_2400).1))))))

theorem n_row_141 : nGrid.row evalE 141 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_141_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_141_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_141_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_141_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_141_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_141_2000).2 (bothLoop_sound b_141_2400).2))))))

theorem b_142_0 : bothSeg evalE (oGrid.idx 142) (oGrid.dm 142) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 142) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3097305173941359841670821303490348659746116516594740940010484344268541984744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_142_400 : bothSeg evalE (oGrid.idx 142) (oGrid.dm 142) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 142) oGrid.kl oGrid.kr 400 400 ⟨false, 3097305173941359841670821303490348659746116516594740940010484344268541984744⟩ ⟨false, 0⟩ ⟨false, 5005587759988187058225564421665304143746244657379109724792714321639379423390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_142_800 : bothSeg evalE (oGrid.idx 142) (oGrid.dm 142) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 142) oGrid.kl oGrid.kr 400 800 ⟨false, 5005587759988187058225564421665304143746244657379109724792714321639379423390⟩ ⟨false, 0⟩ ⟨false, 5714485311312805102498803887221983687603006493856087355013914122070166495380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_142_1200 : bothSeg evalE (oGrid.idx 142) (oGrid.dm 142) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 142) oGrid.kl oGrid.kr 400 1200 ⟨false, 5714485311312805102498803887221983687603006493856087355013914122070166495380⟩ ⟨false, 0⟩ ⟨false, 5819134181682251843769225048535683140602498062361426119030564301206137981678⟩ ⟨false, 5781617123725506743255930763674058792595723266561246456391059737452250794⟩ = true := by
  decide +kernel

theorem b_142_1600 : bothSeg evalE (oGrid.idx 142) (oGrid.dm 142) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 142) oGrid.kl oGrid.kr 400 1600 ⟨false, 5819134181682251843769225048535683140602498062361426119030564301206137981678⟩ ⟨false, 5781617123725506743255930763674058792595723266561246456391059737452250794⟩ ⟨false, 5637987472399822487456636390168607570492555937753296016401376764729686147430⟩ ⟨false, 187214350682725064447651034628355225942297733518873024310918343863949461280⟩ = true := by
  decide +kernel

theorem b_142_2000 : bothSeg evalE (oGrid.idx 142) (oGrid.dm 142) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 142) oGrid.kl oGrid.kr 400 2000 ⟨false, 5637987472399822487456636390168607570492555937753296016401376764729686147430⟩ ⟨false, 187214350682725064447651034628355225942297733518873024310918343863949461280⟩ ⟨false, 5591050244808400718123472306479730461729294182848244751961536744083692803318⟩ ⟨false, 234918237987665237437443592823537055876663937166034965208714911407066382064⟩ = true := by
  decide +kernel

theorem b_142_2400 : bothLoop evalE (oGrid.idx 142) (oGrid.dm 142) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 142) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5591050244808400718123472306479730461729294182848244751961536744083692803318⟩ ⟨false, 234918237987665237437443592823537055876663937166034965208714911407066382064⟩ = true := by
  decide +kernel

theorem o_row_142 : oGrid.row evalE 142 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_142_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_142_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_142_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_142_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_142_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_142_2000).1 (bothLoop_sound b_142_2400).1))))))

theorem n_row_142 : nGrid.row evalE 142 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_142_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_142_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_142_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_142_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_142_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_142_2000).2 (bothLoop_sound b_142_2400).2))))))

theorem b_143_0 : bothSeg evalE (oGrid.idx 143) (oGrid.dm 143) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 143) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3085608369929876494035820158872688785097792189156662163963689612403776056852⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_143_400 : bothSeg evalE (oGrid.idx 143) (oGrid.dm 143) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 143) oGrid.kl oGrid.kr 400 400 ⟨false, 3085608369929876494035820158872688785097792189156662163963689612403776056852⟩ ⟨false, 0⟩ ⟨false, 4986779858687215608232835607572405122739019563345929710825223471554172782596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_143_800 : bothSeg evalE (oGrid.idx 143) (oGrid.dm 143) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 143) oGrid.kl oGrid.kr 400 800 ⟨false, 4986779858687215608232835607572405122739019563345929710825223471554172782596⟩ ⟨false, 0⟩ ⟨false, 5692826014306846894041198031534267361982751362247626269426325390328565480440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_143_1200 : bothSeg evalE (oGrid.idx 143) (oGrid.dm 143) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 143) oGrid.kl oGrid.kr 400 1200 ⟨false, 5692826014306846894041198031534267361982751362247626269426325390328565480440⟩ ⟨false, 0⟩ ⟨false, 5796485494051458022780791132434189206274927348198750214276199098749660512636⟩ ⟨false, 6033947319369313971046712419206900625924261928185776709896249034190907804⟩ = true := by
  decide +kernel

theorem b_143_1600 : bothSeg evalE (oGrid.idx 143) (oGrid.dm 143) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 143) oGrid.kl oGrid.kr 400 1600 ⟨false, 5796485494051458022780791132434189206274927348198750214276199098749660512636⟩ ⟨false, 6033947319369313971046712419206900625924261928185776709896249034190907804⟩ ⟨false, 5615486540068684841588734211175113314583907505592603111943211585736762075456⟩ ⟨false, 187319628415178771915916208907323258656442226147711713699613163808478893422⟩ = true := by
  decide +kernel

theorem b_143_2000 : bothSeg evalE (oGrid.idx 143) (oGrid.dm 143) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 143) oGrid.kl oGrid.kr 400 2000 ⟨false, 5615486540068684841588734211175113314583907505592603111943211585736762075456⟩ ⟨false, 187319628415178771915916208907323258656442226147711713699613163808478893422⟩ ⟨false, 5568825375434378956481820376501568897476258842477432359899263508105539418100⟩ ⟨false, 234749194395663581873344551667353490845355960559301948683608269210699549496⟩ = true := by
  decide +kernel

theorem b_143_2400 : bothLoop evalE (oGrid.idx 143) (oGrid.dm 143) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 143) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 5568825375434378956481820376501568897476258842477432359899263508105539418100⟩ ⟨false, 234749194395663581873344551667353490845355960559301948683608269210699549496⟩ = true := by
  decide +kernel

theorem o_row_143 : oGrid.row evalE 143 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_143_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_143_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_143_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_143_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_143_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_143_2000).1 (bothLoop_sound b_143_2400).1))))))

theorem n_row_143 : nGrid.row evalE 143 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_143_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_143_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_143_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_143_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_143_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_143_2000).2 (bothLoop_sound b_143_2400).2))))))

theorem o_blk_120 : allFrom (fun j => oGrid.row evalE j) 120 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 120) o_row_120 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 121) o_row_121 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 122) o_row_122 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 123) o_row_123 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 124) o_row_124 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 125) o_row_125 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 126) o_row_126 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 127) o_row_127 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 128) o_row_128 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 129) o_row_129 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 130) o_row_130 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 131) o_row_131 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 132) o_row_132 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 133) o_row_133 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 134) o_row_134 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 135) o_row_135 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 136) o_row_136 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 137) o_row_137 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 138) o_row_138 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 139) o_row_139 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 140) o_row_140 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 141) o_row_141 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 142) o_row_142 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 143) o_row_143 (allFrom_zero (fun j => oGrid.row evalE j) 144)))))))))))))))))))))))))

theorem n_blk_120 : allFrom (fun j => nGrid.row evalE j) 120 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 120) n_row_120 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 121) n_row_121 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 122) n_row_122 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 123) n_row_123 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 124) n_row_124 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 125) n_row_125 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 126) n_row_126 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 127) n_row_127 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 128) n_row_128 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 129) n_row_129 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 130) n_row_130 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 131) n_row_131 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 132) n_row_132 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 133) n_row_133 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 134) n_row_134 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 135) n_row_135 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 136) n_row_136 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 137) n_row_137 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 138) n_row_138 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 139) n_row_139 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 140) n_row_140 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 141) n_row_141 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 142) n_row_142 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 143) n_row_143 (allFrom_zero (fun j => nGrid.row evalE j) 144)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
