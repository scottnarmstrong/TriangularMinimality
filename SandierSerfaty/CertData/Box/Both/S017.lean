/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 17 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `408`–`431`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_408_0 : bothSeg evalE (oGrid.idx 408) (oGrid.dm 408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 408) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 982321880259671542787376455563247023003890345752458355233525025579646475672⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_408_400 : bothSeg evalE (oGrid.idx 408) (oGrid.dm 408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 408) oGrid.kl oGrid.kr 400 400 ⟨false, 982321880259671542787376455563247023003890345752458355233525025579646475672⟩ ⟨false, 0⟩ ⟨false, 1563129348064792001673757171254179853147362301215356692280921327531233571130⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_408_800 : bothSeg evalE (oGrid.idx 408) (oGrid.dm 408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 408) oGrid.kl oGrid.kr 400 800 ⟨false, 1563129348064792001673757171254179853147362301215356692280921327531233571130⟩ ⟨false, 0⟩ ⟨false, 1727062243244963727089051450099296528614775507425791134094947491473625305574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_408_1200 : bothSeg evalE (oGrid.idx 408) (oGrid.dm 408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 408) oGrid.kl oGrid.kr 400 1200 ⟨false, 1727062243244963727089051450099296528614775507425791134094947491473625305574⟩ ⟨false, 0⟩ ⟨false, 1667637402112853791339581393909183861730429455940552275987904988349359855224⟩ ⟨false, 62289582367490995375948922719588708170829468294972581657460371914391416458⟩ = true := by
  decide +kernel

theorem b_408_1600 : bothSeg evalE (oGrid.idx 408) (oGrid.dm 408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 408) oGrid.kl oGrid.kr 400 1600 ⟨false, 1667637402112853791339581393909183861730429455940552275987904988349359855224⟩ ⟨false, 62289582367490995375948922719588708170829468294972581657460371914391416458⟩ ⟨false, 1545093247040100298510204821641979136755466658360306912627451004950319420932⟩ ⟨false, 184833737440244488205325494986793433145792265875217945017914355313431850750⟩ = true := by
  decide +kernel

theorem b_408_2000 : bothSeg evalE (oGrid.idx 408) (oGrid.dm 408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 408) oGrid.kl oGrid.kr 400 2000 ⟨false, 1545093247040100298510204821641979136755466658360306912627451004950319420932⟩ ⟨false, 184833737440244488205325494986793433145792265875217945017914355313431850750⟩ ⟨false, 1546164301068882200155029405100922218008525068894017906652634566168592507534⟩ ⟨false, 191770586993357561525790858452093769841757794298652760490995694328448439944⟩ = true := by
  decide +kernel

theorem b_408_2400 : bothLoop evalE (oGrid.idx 408) (oGrid.dm 408) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 408) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1546164301068882200155029405100922218008525068894017906652634566168592507534⟩ ⟨false, 191770586993357561525790858452093769841757794298652760490995694328448439944⟩ = true := by
  decide +kernel

theorem o_row_408 : oGrid.row evalE 408 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_408_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_408_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_408_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_408_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_408_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_408_2000).1 (bothLoop_sound b_408_2400).1))))))

theorem n_row_408 : nGrid.row evalE 408 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_408_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_408_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_408_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_408_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_408_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_408_2000).2 (bothLoop_sound b_408_2400).2))))))

theorem b_409_0 : bothSeg evalE (oGrid.idx 409) (oGrid.dm 409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 409) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 977365278892850052731055577938451853103830555825333449474305044312027437554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_409_400 : bothSeg evalE (oGrid.idx 409) (oGrid.dm 409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 409) oGrid.kl oGrid.kr 400 400 ⟨false, 977365278892850052731055577938451853103830555825333449474305044312027437554⟩ ⟨false, 0⟩ ⟨false, 1554982063531874521939406081082233724529248068116934949156463292962426465188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_409_800 : bothSeg evalE (oGrid.idx 409) (oGrid.dm 409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 409) oGrid.kl oGrid.kr 400 800 ⟨false, 1554982063531874521939406081082233724529248068116934949156463292962426465188⟩ ⟨false, 0⟩ ⟨false, 1717606326889606565962185444003099294447223400796872843312034669316455013418⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_409_1200 : bothSeg evalE (oGrid.idx 409) (oGrid.dm 409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 409) oGrid.kl oGrid.kr 400 1200 ⟨false, 1717606326889606565962185444003099294447223400796872843312034669316455013418⟩ ⟨false, 0⟩ ⟨false, 1657581744800656648873424820321663951554310952566807706895229215471492497762⟩ ⟨false, 62795079924003957944322780242879784167606948312164390805703119045808129254⟩ = true := by
  decide +kernel

theorem b_409_1600 : bothSeg evalE (oGrid.idx 409) (oGrid.dm 409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 409) oGrid.kl oGrid.kr 400 1600 ⟨false, 1657581744800656648873424820321663951554310952566807706895229215471492497762⟩ ⟨false, 62795079924003957944322780242879784167606948312164390805703119045808129254⟩ ⟨false, 1535634294800701115275948529038760839939404225153386732064106619366909440990⟩ ⟨false, 184742529923959491541799071525782895782513675725585365636825715150391186026⟩ = true := by
  decide +kernel

theorem b_409_2000 : bothSeg evalE (oGrid.idx 409) (oGrid.dm 409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 409) oGrid.kl oGrid.kr 400 2000 ⟨false, 1535634294800701115275948529038760839939404225153386732064106619366909440990⟩ ⟨false, 184742529923959491541799071525782895782513675725585365636825715150391186026⟩ ⟨false, 1536724606240655604316338547279578256298409970915174272973634920751237146226⟩ ⟨false, 191677115723086460603702701060180734619390863199153116235360992532375126902⟩ = true := by
  decide +kernel

theorem b_409_2400 : bothLoop evalE (oGrid.idx 409) (oGrid.dm 409) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 409) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1536724606240655604316338547279578256298409970915174272973634920751237146226⟩ ⟨false, 191677115723086460603702701060180734619390863199153116235360992532375126902⟩ = true := by
  decide +kernel

theorem o_row_409 : oGrid.row evalE 409 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_409_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_409_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_409_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_409_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_409_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_409_2000).1 (bothLoop_sound b_409_2400).1))))))

theorem n_row_409 : nGrid.row evalE 409 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_409_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_409_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_409_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_409_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_409_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_409_2000).2 (bothLoop_sound b_409_2400).2))))))

theorem b_410_0 : bothSeg evalE (oGrid.idx 410) (oGrid.dm 410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 410) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 972426180479066762190035180166083551414512291627734375504888918583886534958⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_410_400 : bothSeg evalE (oGrid.idx 410) (oGrid.dm 410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 410) oGrid.kl oGrid.kr 400 400 ⟨false, 972426180479066762190035180166083551414512291627734375504888918583886534958⟩ ⟨false, 0⟩ ⟨false, 1546863415755238975094532887361192928894223743990324399636472713056654420682⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_410_800 : bothSeg evalE (oGrid.idx 410) (oGrid.dm 410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 410) oGrid.kl oGrid.kr 400 800 ⟨false, 1546863415755238975094532887361192928894223743990324399636472713056654420682⟩ ⟨false, 0⟩ ⟨false, 1708183966094308993087980901214688171803921503314085481302531487986245898762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_410_1200 : bothSeg evalE (oGrid.idx 410) (oGrid.dm 410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 410) oGrid.kl oGrid.kr 400 1200 ⟨false, 1708183966094308993087980901214688171803921503314085481302531487986245898762⟩ ⟨false, 0⟩ ⟨false, 1647562555709005815736763183352689147826716348469950821755718799650227601638⟩ ⟨false, 63299343809105312966942045716161377722288290813670982323084794897019757402⟩ = true := by
  decide +kernel

theorem b_410_1600 : bothSeg evalE (oGrid.idx 410) (oGrid.dm 410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 410) oGrid.kl oGrid.kr 400 1600 ⟨false, 1647562555709005815736763183352689147826716348469950821755718799650227601638⟩ ⟨false, 63299343809105312966942045716161377722288290813670982323084794897019757402⟩ ⟨false, 1526211454253949378762526182819744977710577943299169547842241313861172496222⟩ ⟨false, 184650445264161749941179046249105547838426695984452256236562280686074862818⟩ = true := by
  decide +kernel

theorem b_410_2000 : bothSeg evalE (oGrid.idx 410) (oGrid.dm 410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 410) oGrid.kl oGrid.kr 400 2000 ⟨false, 1526211454253949378762526182819744977710577943299169547842241313861172496222⟩ ⟨false, 184650445264161749941179046249105547838426695984452256236562280686074862818⟩ ⟨false, 1527321450710863384944316037894324756405223942925786966679626689734911494826⟩ ⟨false, 191582499041102708133342483985781878095314139857771617379059723076304182350⟩ = true := by
  decide +kernel

theorem b_410_2400 : bothLoop evalE (oGrid.idx 410) (oGrid.dm 410) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 410) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1527321450710863384944316037894324756405223942925786966679626689734911494826⟩ ⟨false, 191582499041102708133342483985781878095314139857771617379059723076304182350⟩ = true := by
  decide +kernel

theorem o_row_410 : oGrid.row evalE 410 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_410_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_410_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_410_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_410_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_410_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_410_2000).1 (bothLoop_sound b_410_2400).1))))))

theorem n_row_410 : nGrid.row evalE 410 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_410_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_410_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_410_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_410_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_410_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_410_2000).2 (bothLoop_sound b_410_2400).2))))))

theorem b_411_0 : bothSeg evalE (oGrid.idx 411) (oGrid.dm 411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 411) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 967504539700447852436417391074006258188069684080692758494976898627248312024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_411_400 : bothSeg evalE (oGrid.idx 411) (oGrid.dm 411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 411) oGrid.kl oGrid.kr 400 400 ⟨false, 967504539700447852436417391074006258188069684080692758494976898627248312024⟩ ⟨false, 0⟩ ⟨false, 1538773301325292389988079915580693228423792112463185879070662767913562607244⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_411_800 : bothSeg evalE (oGrid.idx 411) (oGrid.dm 411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 411) oGrid.kl oGrid.kr 400 800 ⟨false, 1538773301325292389988079915580693228423792112463185879070662767913562607244⟩ ⟨false, 0⟩ ⟨false, 1698794966499803619236874235633857693704410847619200250906435176706467126764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_411_1200 : bothSeg evalE (oGrid.idx 411) (oGrid.dm 411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 411) oGrid.kl oGrid.kr 400 1200 ⟨false, 1698794966499803619236874235633857693704410847619200250906435176706467126764⟩ ⟨false, 0⟩ ⟨false, 1637579910439032725986007321680204171434041335648296083018198526526095281404⟩ ⟨false, 63802551953045492552474107961404530093733997263254282721512424856689040306⟩ = true := by
  decide +kernel

theorem b_411_1600 : bothSeg evalE (oGrid.idx 411) (oGrid.dm 411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 411) oGrid.kl oGrid.kr 400 1600 ⟨false, 1637579910439032725986007321680204171434041335648296083018198526526095281404⟩ ⟨false, 63802551953045492552474107961404530093733997263254282721512424856689040306⟩ ⟨false, 1516824469124934498498478297453689648665171964480410605557115110865217582166⟩ ⟨false, 184557993267143720040003132187919052862603368431139760182595840517566739544⟩ = true := by
  decide +kernel

theorem b_411_2000 : bothSeg evalE (oGrid.idx 411) (oGrid.dm 411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 411) oGrid.kl oGrid.kr 400 2000 ⟨false, 1516824469124934498498478297453689648665171964480410605557115110865217582166⟩ ⟨false, 184557993267143720040003132187919052862603368431139760182595840517566739544⟩ ⟨false, 1517954636932446007599352605347166479080642032594779196919640686912666544360⟩ ⟨false, 191486696494675811789795655619193463740493319422859122975839318814848639152⟩ = true := by
  decide +kernel

theorem b_411_2400 : bothLoop evalE (oGrid.idx 411) (oGrid.dm 411) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 411) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1517954636932446007599352605347166479080642032594779196919640686912666544360⟩ ⟨false, 191486696494675811789795655619193463740493319422859122975839318814848639152⟩ = true := by
  decide +kernel

theorem o_row_411 : oGrid.row evalE 411 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_411_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_411_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_411_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_411_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_411_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_411_2000).1 (bothLoop_sound b_411_2400).1))))))

theorem n_row_411 : nGrid.row evalE 411 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_411_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_411_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_411_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_411_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_411_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_411_2000).2 (bothLoop_sound b_411_2400).2))))))

theorem b_412_0 : bothSeg evalE (oGrid.idx 412) (oGrid.dm 412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 412) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 962600310125588423915206546144510955782705942406059642115238516095695105698⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_412_400 : bothSeg evalE (oGrid.idx 412) (oGrid.dm 412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 412) oGrid.kl oGrid.kr 400 400 ⟨false, 962600310125588423915206546144510955782705942406059642115238516095695105698⟩ ⟨false, 0⟩ ⟨false, 1530711678122225281867852265348089206558415036842616245735936095562400458000⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_412_800 : bothSeg evalE (oGrid.idx 412) (oGrid.dm 412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 412) oGrid.kl oGrid.kr 400 800 ⟨false, 1530711678122225281867852265348089206558415036842616245735936095562400458000⟩ ⟨false, 0⟩ ⟨false, 1689439364788148836080696928528387442709734272694222420906869318040505133422⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_412_1200 : bothSeg evalE (oGrid.idx 412) (oGrid.dm 412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 412) oGrid.kl oGrid.kr 400 1200 ⟨false, 1689439364788148836080696928528387442709734272694222420906869318040505133422⟩ ⟨false, 0⟩ ⟨false, 1627633928025957073877735879419412482023120709613320374206552696104271385084⟩ ⟨false, 64304934879354474612364533325536704414285023587726747793768685459522960064⟩ = true := by
  decide +kernel

theorem b_412_1600 : bothSeg evalE (oGrid.idx 412) (oGrid.dm 412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 412) oGrid.kl oGrid.kr 400 1600 ⟨false, 1627633928025957073877735879419412482023120709613320374206552696104271385084⟩ ⟨false, 64304934879354474612364533325536704414285023587726747793768685459522960064⟩ ⟨false, 1507473328244537964155436260954888515280214026372571101895860707938769470736⟩ ⟨false, 184465534660773584334664151790060671157191706828476020104460673625024874412⟩ = true := by
  decide +kernel

theorem b_412_2000 : bothSeg evalE (oGrid.idx 412) (oGrid.dm 412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 412) oGrid.kl oGrid.kr 400 2000 ⟨false, 1507473328244537964155436260954888515280214026372571101895860707938769470736⟩ ⟨false, 184465534660773584334664151790060671157191706828476020104460673625024874412⟩ ⟨false, 1508624175936011749274632022373087313512509100289592797547523378165382779752⟩ ⟨false, 191390430529072626901107826476318805038145957240309313837244975008805063870⟩ = true := by
  decide +kernel

theorem b_412_2400 : bothLoop evalE (oGrid.idx 412) (oGrid.dm 412) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 412) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1508624175936011749274632022373087313512509100289592797547523378165382779752⟩ ⟨false, 191390430529072626901107826476318805038145957240309313837244975008805063870⟩ = true := by
  decide +kernel

theorem o_row_412 : oGrid.row evalE 412 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_412_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_412_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_412_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_412_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_412_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_412_2000).1 (bothLoop_sound b_412_2400).1))))))

theorem n_row_412 : nGrid.row evalE 412 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_412_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_412_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_412_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_412_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_412_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_412_2000).2 (bothLoop_sound b_412_2400).2))))))

theorem b_413_0 : bothSeg evalE (oGrid.idx 413) (oGrid.dm 413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 413) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 957713447237217873952334342722120459361400456454044795445904381204842561458⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_413_400 : bothSeg evalE (oGrid.idx 413) (oGrid.dm 413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 413) oGrid.kl oGrid.kr 400 400 ⟨false, 957713447237217873952334342722120459361400456454044795445904381204842561458⟩ ⟨false, 0⟩ ⟨false, 1522678453849001704961193882198382298770384247841127247211673079891199805986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_413_800 : bothSeg evalE (oGrid.idx 413) (oGrid.dm 413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 413) oGrid.kl oGrid.kr 400 800 ⟨false, 1522678453849001704961193882198382298770384247841127247211673079891199805986⟩ ⟨false, 0⟩ ⟨false, 1680117059371363231138761882295764984009038708356205047486029855217210136944⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_413_1200 : bothSeg evalE (oGrid.idx 413) (oGrid.dm 413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 413) oGrid.kl oGrid.kr 400 1200 ⟨false, 1680117059371363231138761882295764984009038708356205047486029855217210136944⟩ ⟨false, 0⟩ ⟨false, 1617724608961640743165365573897697579924816656209684402892532871063093103814⟩ ⟨false, 64805894014278263345393358382311619823341161850451243884337950928093179638⟩ = true := by
  decide +kernel

theorem b_413_1600 : bothSeg evalE (oGrid.idx 413) (oGrid.dm 413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 413) oGrid.kl oGrid.kr 400 1600 ⟨false, 1617724608961640743165365573897697579924816656209684402892532871063093103814⟩ ⟨false, 64805894014278263345393358382311619823341161850451243884337950928093179638⟩ ⟨false, 1498157913597713979972294381952977298786213594602743791896676399566448563838⟩ ⟨false, 184372589378205026538464550327031900961944223457391854880194422424737719614⟩ = true := by
  decide +kernel

theorem b_413_2000 : bothSeg evalE (oGrid.idx 413) (oGrid.dm 413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 413) oGrid.kl oGrid.kr 400 2000 ⟨false, 1498157913597713979972294381952977298786213594602743791896676399566448563838⟩ ⟨false, 184372589378205026538464550327031900961944223457391854880194422424737719614⟩ ⟨false, 1499330020998123461319649566000300148644030956710863944458075216114385565808⟩ ⟨false, 191293435569489204086930338382791017294127844555444992879094996122066286034⟩ = true := by
  decide +kernel

theorem b_413_2400 : bothLoop evalE (oGrid.idx 413) (oGrid.dm 413) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 413) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1499330020998123461319649566000300148644030956710863944458075216114385565808⟩ ⟨false, 191293435569489204086930338382791017294127844555444992879094996122066286034⟩ = true := by
  decide +kernel

theorem o_row_413 : oGrid.row evalE 413 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_413_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_413_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_413_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_413_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_413_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_413_2000).1 (bothLoop_sound b_413_2400).1))))))

theorem n_row_413 : nGrid.row evalE 413 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_413_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_413_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_413_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_413_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_413_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_413_2000).2 (bothLoop_sound b_413_2400).2))))))

theorem b_414_0 : bothSeg evalE (oGrid.idx 414) (oGrid.dm 414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 414) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 952843903976893042607857409255442778120253127099554518084484229013097732724⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_414_400 : bothSeg evalE (oGrid.idx 414) (oGrid.dm 414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 414) oGrid.kl oGrid.kr 400 400 ⟨false, 952843903976893042607857409255442778120253127099554518084484229013097732724⟩ ⟨false, 0⟩ ⟨false, 1514673570345412359553125602875536506190465546909067199739079694426154102126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_414_800 : bothSeg evalE (oGrid.idx 414) (oGrid.dm 414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 414) oGrid.kl oGrid.kr 400 800 ⟨false, 1514673570345412359553125602875536506190465546909067199739079694426154102126⟩ ⟨false, 0⟩ ⟨false, 1670827915595492642945251119934005167067271320105636678632622480993597996310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_414_1200 : bothSeg evalE (oGrid.idx 414) (oGrid.dm 414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 414) oGrid.kl oGrid.kr 400 1200 ⟨false, 1670827915595492642945251119934005167067271320105636678632622480993597996310⟩ ⟨false, 0⟩ ⟨false, 1607852123035320740368039851060172547205770521549620694904259246019550331332⟩ ⟨false, 65305001478567044238532889627836360796413452103019261283015690344339253652⟩ = true := by
  decide +kernel

theorem b_414_1600 : bothSeg evalE (oGrid.idx 414) (oGrid.dm 414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 414) oGrid.kl oGrid.kr 400 1600 ⟨false, 1607852123035320740368039851060172547205770521549620694904259246019550331332⟩ ⟨false, 65305001478567044238532889627836360796413452103019261283015690344339253652⟩ ⟨false, 1488878219876350821388826589695681065132305729121337705507357871222112474914⟩ ⟨false, 184278904637536963217746150992327842869878244531302250679917065141777110070⟩ = true := by
  decide +kernel

theorem b_414_2000 : bothSeg evalE (oGrid.idx 414) (oGrid.dm 414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 414) oGrid.kl oGrid.kr 400 2000 ⟨false, 1488878219876350821388826589695681065132305729121337705507357871222112474914⟩ ⟨false, 184278904637536963217746150992327842869878244531302250679917065141777110070⟩ ⟨false, 1490072220578440444253334516551990742201393802015151446675325081210500856648⟩ ⟨false, 191194622838201199951314663929791435342058658094225934982515230655853526116⟩ = true := by
  decide +kernel

theorem b_414_2400 : bothLoop evalE (oGrid.idx 414) (oGrid.dm 414) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 414) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1490072220578440444253334516551990742201393802015151446675325081210500856648⟩ ⟨false, 191194622838201199951314663929791435342058658094225934982515230655853526116⟩ = true := by
  decide +kernel

theorem o_row_414 : oGrid.row evalE 414 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_414_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_414_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_414_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_414_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_414_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_414_2000).1 (bothLoop_sound b_414_2400).1))))))

theorem n_row_414 : nGrid.row evalE 414 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_414_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_414_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_414_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_414_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_414_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_414_2000).2 (bothLoop_sound b_414_2400).2))))))

theorem b_415_0 : bothSeg evalE (oGrid.idx 415) (oGrid.dm 415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 415) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 947991635099390980748717908555121336427309624365223751868921622172758822638⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_415_400 : bothSeg evalE (oGrid.idx 415) (oGrid.dm 415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 415) oGrid.kl oGrid.kr 400 400 ⟨false, 947991635099390980748717908555121336427309624365223751868921622172758822638⟩ ⟨false, 0⟩ ⟨false, 1506696950934055282299325246078177527326561807234537253519062373398060806926⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_415_800 : bothSeg evalE (oGrid.idx 415) (oGrid.dm 415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 415) oGrid.kl oGrid.kr 400 800 ⟨false, 1506696950934055282299325246078177527326561807234537253519062373398060806926⟩ ⟨false, 0⟩ ⟨false, 1661571876184615003208513079052130089006430907952856652638673447371275200070⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_415_1200 : bothSeg evalE (oGrid.idx 415) (oGrid.dm 415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 415) oGrid.kl oGrid.kr 400 1200 ⟨false, 1661571876184615003208513079052130089006430907952856652638673447371275200070⟩ ⟨false, 0⟩ ⟨false, 1598016320803656202515272639471622020835421530905980028208654762517347455848⟩ ⟨false, 65803079412488041617417134033364260358311844159842376335547166864129789656⟩ = true := by
  decide +kernel

theorem b_415_1600 : bothSeg evalE (oGrid.idx 415) (oGrid.dm 415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 415) oGrid.kl oGrid.kr 400 1600 ⟨false, 1598016320803656202515272639471622020835421530905980028208654762517347455848⟩ ⟨false, 65803079412488041617417134033364260358311844159842376335547166864129789656⟩ ⟨false, 1479633945019056459129394387201667788832362825546048013374515943577090873076⟩ ⟨false, 184185455197087785003295386303318492361370549519774391169685985804386372428⟩ = true := by
  decide +kernel

theorem b_415_2000 : bothSeg evalE (oGrid.idx 415) (oGrid.dm 415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 415) oGrid.kl oGrid.kr 400 2000 ⟨false, 1479633945019056459129394387201667788832362825546048013374515943577090873076⟩ ⟨false, 184185455197087785003295386303318492361370549519774391169685985804386372428⟩ ⟨false, 1480850518596212596527821083605356575694053634832705614406227223126422021228⟩ ⟨false, 191095513638476651195661936956713474973505144459564318861286463414295434712⟩ = true := by
  decide +kernel

theorem b_415_2400 : bothLoop evalE (oGrid.idx 415) (oGrid.dm 415) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 415) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1480850518596212596527821083605356575694053634832705614406227223126422021228⟩ ⟨false, 191095513638476651195661936956713474973505144459564318861286463414295434712⟩ = true := by
  decide +kernel

theorem o_row_415 : oGrid.row evalE 415 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_415_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_415_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_415_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_415_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_415_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_415_2000).1 (bothLoop_sound b_415_2400).1))))))

theorem n_row_415 : nGrid.row evalE 415 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_415_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_415_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_415_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_415_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_415_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_415_2000).2 (bothLoop_sound b_415_2400).2))))))

theorem b_416_0 : bothSeg evalE (oGrid.idx 416) (oGrid.dm 416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 416) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 943156593901505022066069166639764020925674128754582476082022368159467084440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_416_400 : bothSeg evalE (oGrid.idx 416) (oGrid.dm 416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 416) oGrid.kl oGrid.kr 400 400 ⟨false, 943156593901505022066069166639764020925674128754582476082022368159467084440⟩ ⟨false, 0⟩ ⟨false, 1498748525556217834839540188491795665768627781645547213331767084216572704502⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_416_800 : bothSeg evalE (oGrid.idx 416) (oGrid.dm 416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 416) oGrid.kl oGrid.kr 400 800 ⟨false, 1498748525556217834839540188491795665768627781645547213331767084216572704502⟩ ⟨false, 0⟩ ⟨false, 1652348924521709326159228671861943035136481550505258443535824297638686231938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_416_1200 : bothSeg evalE (oGrid.idx 416) (oGrid.dm 416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 416) oGrid.kl oGrid.kr 400 1200 ⟨false, 1652348924521709326159228671861943035136481550505258443535824297638686231938⟩ ⟨false, 0⟩ ⟨false, 1588217605930417329171785681788333830615421304269529444289458006360167367542⟩ ⟨false, 66298838328684722246250732313289158457716197109247330856789674902665720186⟩ = true := by
  decide +kernel

theorem b_416_1600 : bothSeg evalE (oGrid.idx 416) (oGrid.dm 416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 416) oGrid.kl oGrid.kr 400 1600 ⟨false, 1588217605930417329171785681788333830615421304269529444289458006360167367542⟩ ⟨false, 66298838328684722246250732313289158457716197109247330856789674902665720186⟩ ⟨false, 1470425452516160887829766272922379135194967853068548526493283721483050043238⟩ ⟨false, 184090991742941163588270141179243853878169648310228248652963959779783044490⟩ = true := by
  decide +kernel

theorem b_416_2000 : bothSeg evalE (oGrid.idx 416) (oGrid.dm 416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 416) oGrid.kl oGrid.kr 400 2000 ⟨false, 1470425452516160887829766272922379135194967853068548526493283721483050043238⟩ ⟨false, 184090991742941163588270141179243853878169648310228248652963959779783044490⟩ ⟨false, 1471665344305079911053240366876239397221751947267164399804465253249981483568⟩ ⟨false, 190995348031250758782544667382623286255418755457902258445500450850650071962⟩ = true := by
  decide +kernel

theorem b_416_2400 : bothLoop evalE (oGrid.idx 416) (oGrid.dm 416) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 416) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1471665344305079911053240366876239397221751947267164399804465253249981483568⟩ ⟨false, 190995348031250758782544667382623286255418755457902258445500450850650071962⟩ = true := by
  decide +kernel

theorem o_row_416 : oGrid.row evalE 416 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_416_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_416_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_416_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_416_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_416_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_416_2000).1 (bothLoop_sound b_416_2400).1))))))

theorem n_row_416 : nGrid.row evalE 416 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_416_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_416_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_416_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_416_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_416_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_416_2000).2 (bothLoop_sound b_416_2400).2))))))

theorem b_417_0 : bothSeg evalE (oGrid.idx 417) (oGrid.dm 417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 417) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 938338735607564218595529480322614414612587842606373011610399390074130648464⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_417_400 : bothSeg evalE (oGrid.idx 417) (oGrid.dm 417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 417) oGrid.kl oGrid.kr 400 400 ⟨false, 938338735607564218595529480322614414612587842606373011610399390074130648464⟩ ⟨false, 0⟩ ⟨false, 1490828233129530931712222709670821987629451977359137312869426689836543132962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_417_800 : bothSeg evalE (oGrid.idx 417) (oGrid.dm 417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 417) oGrid.kl oGrid.kr 400 800 ⟨false, 1490828233129530931712222709670821987629451977359137312869426689836543132962⟩ ⟨false, 0⟩ ⟨false, 1643158896736336597451357141059427168631430008542594033823545100863567556092⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_417_1200 : bothSeg evalE (oGrid.idx 417) (oGrid.dm 417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 417) oGrid.kl oGrid.kr 400 1200 ⟨false, 1643158896736336597451357141059427168631430008542594033823545100863567556092⟩ ⟨false, 0⟩ ⟨false, 1578455686949440269252245190026198666985883722538165721495894704255484763688⟩ ⟨false, 66792645804348816978573569838166708437883466520005716417640294089015184162⟩ = true := by
  decide +kernel

theorem b_417_1600 : bothSeg evalE (oGrid.idx 417) (oGrid.dm 417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 417) oGrid.kl oGrid.kr 400 1600 ⟨false, 1578455686949440269252245190026198666985883722538165721495894704255484763688⟩ ⟨false, 66792645804348816978573569838166708437883466520005716417640294089015184162⟩ ⟨false, 1461252300199020481309717303696796786079688511463673399355762808950028782282⟩ ⟨false, 183996032554768604921101456167568589344078677594498038557772189394471165568⟩ = true := by
  decide +kernel

theorem b_417_2000 : bothSeg evalE (oGrid.idx 417) (oGrid.dm 417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 417) oGrid.kl oGrid.kr 400 2000 ⟨false, 1461252300199020481309717303696796786079688511463673399355762808950028782282⟩ ⟨false, 183996032554768604921101456167568589344078677594498038557772189394471165568⟩ ⟨false, 1462516301861720377022771497522909053749136091476250909229033774818087348422⟩ ⟨false, 190893413166669914121869448973687488175296641240474199588260302450392909542⟩ = true := by
  decide +kernel

theorem b_417_2400 : bothLoop evalE (oGrid.idx 417) (oGrid.dm 417) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 417) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1462516301861720377022771497522909053749136091476250909229033774818087348422⟩ ⟨false, 190893413166669914121869448973687488175296641240474199588260302450392909542⟩ = true := by
  decide +kernel

theorem o_row_417 : oGrid.row evalE 417 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_417_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_417_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_417_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_417_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_417_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_417_2000).1 (bothLoop_sound b_417_2400).1))))))

theorem n_row_417 : nGrid.row evalE 417 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_417_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_417_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_417_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_417_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_417_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_417_2000).2 (bothLoop_sound b_417_2400).2))))))

theorem b_418_0 : bothSeg evalE (oGrid.idx 418) (oGrid.dm 418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 418) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 933538015349807040276176717200048490801682825979511757901635702797615826052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_418_400 : bothSeg evalE (oGrid.idx 418) (oGrid.dm 418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 418) oGrid.kl oGrid.kr 400 400 ⟨false, 933538015349807040276176717200048490801682825979511757901635702797615826052⟩ ⟨false, 0⟩ ⟨false, 1482935993810071872693037832544298123336419006243393716876256200729190433454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_418_800 : bothSeg evalE (oGrid.idx 418) (oGrid.dm 418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 418) oGrid.kl oGrid.kr 400 800 ⟨false, 1482935993810071872693037832544298123336419006243393716876256200729190433454⟩ ⟨false, 0⟩ ⟨false, 1634001757743719736634447216236824716907329239359964218558955304333219724316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_418_1200 : bothSeg evalE (oGrid.idx 418) (oGrid.dm 418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 418) oGrid.kl oGrid.kr 400 1200 ⟨false, 1634001757743719736634447216236824716907329239359964218558955304333219724316⟩ ⟨false, 0⟩ ⟨false, 1568730702854394417510280533621058582903121069903803312310878186341910789780⟩ ⟨false, 67284362128807753327383494054318607313003824043419662312257337246600208918⟩ = true := by
  decide +kernel

theorem b_418_1600 : bothSeg evalE (oGrid.idx 418) (oGrid.dm 418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 418) oGrid.kl oGrid.kr 400 1600 ⟨false, 1568730702854394417510280533621058582903121069903803312310878186341910789780⟩ ⟨false, 67284362128807753327383494054318607313003824043419662312257337246600208918⟩ ⟨false, 1452114478035019032864320035183686593104827735637778273243253991636908371590⟩ ⟨false, 183900586948183137973343992491690597111297158309444701379881531951602627108⟩ = true := by
  decide +kernel

theorem b_418_2000 : bothSeg evalE (oGrid.idx 418) (oGrid.dm 418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 418) oGrid.kl oGrid.kr 400 2000 ⟨false, 1452114478035019032864320035183686593104827735637778273243253991636908371590⟩ ⟨false, 183900586948183137973343992491690597111297158309444701379881531951602627108⟩ ⟨false, 1453403412169594461053873444954207148423891381172653186739839391891377157104⟩ ⟨false, 190789931103481622595794100343128049837910446949945335920984218905308251994⟩ = true := by
  decide +kernel

theorem b_418_2400 : bothLoop evalE (oGrid.idx 418) (oGrid.dm 418) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 418) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1453403412169594461053873444954207148423891381172653186739839391891377157104⟩ ⟨false, 190789931103481622595794100343128049837910446949945335920984218905308251994⟩ = true := by
  decide +kernel

theorem o_row_418 : oGrid.row evalE 418 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_418_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_418_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_418_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_418_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_418_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_418_2000).1 (bothLoop_sound b_418_2400).1))))))

theorem n_row_418 : nGrid.row evalE 418 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_418_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_418_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_418_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_418_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_418_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_418_2000).2 (bothLoop_sound b_418_2400).2))))))

theorem b_419_0 : bothSeg evalE (oGrid.idx 419) (oGrid.dm 419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 419) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 928754386808588908719317452986104648384504854794269551482640658682329589800⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_419_400 : bothSeg evalE (oGrid.idx 419) (oGrid.dm 419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 419) oGrid.kl oGrid.kr 400 400 ⟨false, 928754386808588908719317452986104648384504854794269551482640658682329589800⟩ ⟨false, 0⟩ ⟨false, 1475071738755861427676226334434664109420678015623371402338868736946704352156⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_419_800 : bothSeg evalE (oGrid.idx 419) (oGrid.dm 419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 419) oGrid.kl oGrid.kr 400 800 ⟨false, 1475071738755861427676226334434664109420678015623371402338868736946704352156⟩ ⟨false, 0⟩ ⟨false, 1624877450567414381926751167309934700179981119025356579898064589336431704794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_419_1200 : bothSeg evalE (oGrid.idx 419) (oGrid.dm 419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 419) oGrid.kl oGrid.kr 400 1200 ⟨false, 1624877450567414381926751167309934700179981119025356579898064589336431704794⟩ ⟨false, 0⟩ ⟨false, 1559042792939797738021146349092720283078979298947376126589511211558851284738⟩ ⟨false, 67774362263835287891892890166477473971110568543807296179796133825056359532⟩ = true := by
  decide +kernel

theorem b_419_1600 : bothSeg evalE (oGrid.idx 419) (oGrid.dm 419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 419) oGrid.kl oGrid.kr 400 1600 ⟨false, 1559042792939797738021146349092720283078979298947376126589511211558851284738⟩ ⟨false, 67774362263835287891892890166477473971110568543807296179796133825056359532⟩ ⟨false, 1443011845484069424005581468255766826130085634267702130854116145823690823266⟩ ⟨false, 183805309719563601907457771003430930920004233223481291915191199560216821004⟩ = true := by
  decide +kernel

theorem b_419_2000 : bothSeg evalE (oGrid.idx 419) (oGrid.dm 419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 419) oGrid.kl oGrid.kr 400 2000 ⟨false, 1443011845484069424005581468255766826130085634267702130854116145823690823266⟩ ⟨false, 183805309719563601907457771003430930920004233223481291915191199560216821004⟩ ⟨false, 1444326592236598644525987342254570192668637976800325891380898480184487082364⟩ ⟨false, 190686527001378673402101517477644110298145777370877497682521946580622921354⟩ = true := by
  decide +kernel

theorem b_419_2400 : bothLoop evalE (oGrid.idx 419) (oGrid.dm 419) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 419) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1444326592236598644525987342254570192668637976800325891380898480184487082364⟩ ⟨false, 190686527001378673402101517477644110298145777370877497682521946580622921354⟩ = true := by
  decide +kernel

theorem o_row_419 : oGrid.row evalE 419 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_419_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_419_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_419_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_419_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_419_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_419_2000).1 (bothLoop_sound b_419_2400).1))))))

theorem n_row_419 : nGrid.row evalE 419 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_419_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_419_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_419_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_419_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_419_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_419_2000).2 (bothLoop_sound b_419_2400).2))))))

theorem b_420_0 : bothSeg evalE (oGrid.idx 420) (oGrid.dm 420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 420) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 923987805085330601280836224059661601296137258950833002668741909533072154184⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_420_400 : bothSeg evalE (oGrid.idx 420) (oGrid.dm 420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 420) oGrid.kl oGrid.kr 400 400 ⟨false, 923987805085330601280836224059661601296137258950833002668741909533072154184⟩ ⟨false, 0⟩ ⟨false, 1467235402843407034239754698743545377774080192817314178530432620379422037490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_420_800 : bothSeg evalE (oGrid.idx 420) (oGrid.dm 420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 420) oGrid.kl oGrid.kr 400 800 ⟨false, 1467235402843407034239754698743545377774080192817314178530432620379422037490⟩ ⟨false, 0⟩ ⟨false, 1615785855034802958361023696007439260894956846595434949456719268764772895380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_420_1200 : bothSeg evalE (oGrid.idx 420) (oGrid.dm 420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 420) oGrid.kl oGrid.kr 400 1200 ⟨false, 1615785855034802958361023696007439260894956846595434949456719268764772895380⟩ ⟨false, 0⟩ ⟨false, 1549391851289501674852349110768868295328656636631162284596420307344668482574⟩ ⟨false, 68262210983490190722196746152175999692049488534624885884742232947433625348⟩ = true := by
  decide +kernel

theorem b_420_1600 : bothSeg evalE (oGrid.idx 420) (oGrid.dm 420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 420) oGrid.kl oGrid.kr 400 1600 ⟨false, 1549391851289501674852349110768868295328656636631162284596420307344668482574⟩ ⟨false, 68262210983490190722196746152175999692049488534624885884742232947433625348⟩ ⟨false, 1433944328370139747871465044087923978575835639771186403364869914837948469984⟩ ⟨false, 183709733902852117703080812833120316444870485394600767116292625454153637938⟩ = true := by
  decide +kernel

theorem b_420_2000 : bothSeg evalE (oGrid.idx 420) (oGrid.dm 420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 420) oGrid.kl oGrid.kr 400 2000 ⟨false, 1433944328370139747871465044087923978575835639771186403364869914837948469984⟩ ⟨false, 183709733902852117703080812833120316444870485394600767116292625454153637938⟩ ⟨false, 1435285806292187546063118197393030397554656168129966233783132754015691341260⟩ ⟨false, 190581432209145912003985447710500096915992411393911069348653361704413692372⟩ = true := by
  decide +kernel

theorem b_420_2400 : bothLoop evalE (oGrid.idx 420) (oGrid.dm 420) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 420) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1435285806292187546063118197393030397554656168129966233783132754015691341260⟩ ⟨false, 190581432209145912003985447710500096915992411393911069348653361704413692372⟩ = true := by
  decide +kernel

theorem o_row_420 : oGrid.row evalE 420 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_420_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_420_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_420_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_420_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_420_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_420_2000).1 (bothLoop_sound b_420_2400).1))))))

theorem n_row_420 : nGrid.row evalE 420 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_420_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_420_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_420_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_420_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_420_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_420_2000).2 (bothLoop_sound b_420_2400).2))))))

theorem b_421_0 : bothSeg evalE (oGrid.idx 421) (oGrid.dm 421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 421) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 919238225745952992509381172212648787415912985617482541039490917460008056008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_421_400 : bothSeg evalE (oGrid.idx 421) (oGrid.dm 421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 421) oGrid.kl oGrid.kr 400 400 ⟨false, 919238225745952992509381172212648787415912985617482541039490917460008056008⟩ ⟨false, 0⟩ ⟨false, 1459426926243969200590652623444571653417023993493005176315619499844171876830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_421_800 : bothSeg evalE (oGrid.idx 421) (oGrid.dm 421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 421) oGrid.kl oGrid.kr 400 800 ⟨false, 1459426926243969200590652623444571653417023993493005176315619499844171876830⟩ ⟨false, 0⟩ ⟨false, 1606726888271274122451168830506623323354162458166376821568474139881352505784⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_421_1200 : bothSeg evalE (oGrid.idx 421) (oGrid.dm 421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 421) oGrid.kl oGrid.kr 400 1200 ⟨false, 1606726888271274122451168830506623323354162458166376821568474139881352505784⟩ ⟨false, 0⟩ ⟨false, 1539777832757397203809078497605822792697749653090341165039656889907725694650⟩ ⟨false, 68747495524184307514716093055613711781142173665710602144615953756365073494⟩ = true := by
  decide +kernel

theorem b_421_1600 : bothSeg evalE (oGrid.idx 421) (oGrid.dm 421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 421) oGrid.kl oGrid.kr 400 1600 ⟨false, 1539777832757397203809078497605822792697749653090341165039656889907725694650⟩ ⟨false, 68747495524184307514716093055613711781142173665710602144615953756365073494⟩ ⟨false, 1424911863894562183002160093898543140685870574684489066774212545722166909678⟩ ⟨false, 183613464387019328321634496762893363793021252071562700410060297941923858466⟩ = true := by
  decide +kernel

theorem b_421_2000 : bothSeg evalE (oGrid.idx 421) (oGrid.dm 421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 421) oGrid.kl oGrid.kr 400 2000 ⟨false, 1424911863894562183002160093898543140685870574684489066774212545722166909678⟩ ⟨false, 183613464387019328321634496762893363793021252071562700410060297941923858466⟩ ⟨false, 1426281081169633743778944561566199851212631350071320876196582929300669488778⟩ ⟨false, 190474359988956702318171887442378060538895783785828375320372381261713379150⟩ = true := by
  decide +kernel

theorem b_421_2400 : bothLoop evalE (oGrid.idx 421) (oGrid.dm 421) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 421) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1426281081169633743778944561566199851212631350071320876196582929300669488778⟩ ⟨false, 190474359988956702318171887442378060538895783785828375320372381261713379150⟩ = true := by
  decide +kernel

theorem o_row_421 : oGrid.row evalE 421 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_421_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_421_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_421_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_421_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_421_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_421_2000).1 (bothLoop_sound b_421_2400).1))))))

theorem n_row_421 : nGrid.row evalE 421 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_421_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_421_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_421_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_421_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_421_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_421_2000).2 (bothLoop_sound b_421_2400).2))))))

theorem b_422_0 : bothSeg evalE (oGrid.idx 422) (oGrid.dm 422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 422) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 914505602784282252990011630734609687380340999706358653210551995933437457678⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_422_400 : bothSeg evalE (oGrid.idx 422) (oGrid.dm 422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 422) oGrid.kl oGrid.kr 400 400 ⟨false, 914505602784282252990011630734609687380340999706358653210551995933437457678⟩ ⟨false, 0⟩ ⟨false, 1451646219270357252684881480906464446430949615937321401718813830660110216236⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_422_800 : bothSeg evalE (oGrid.idx 422) (oGrid.dm 422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 422) oGrid.kl oGrid.kr 400 800 ⟨false, 1451646219270357252684881480906464446430949615937321401718813830660110216236⟩ ⟨false, 0⟩ ⟨false, 1597700523641262853549772377182844554286064514895906770413710518916865134492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_422_1200 : bothSeg evalE (oGrid.idx 422) (oGrid.dm 422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 422) oGrid.kl oGrid.kr 400 1200 ⟨false, 1597700523641262853549772377182844554286064514895906770413710518916865134492⟩ ⟨false, 0⟩ ⟨false, 1530200784510120005918579614722222668525910968299444465124177245854633873560⟩ ⟨false, 69230054419748196872132843684197385264382469294867821533995597508357295570⟩ = true := by
  decide +kernel

theorem b_422_1600 : bothSeg evalE (oGrid.idx 422) (oGrid.dm 422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 422) oGrid.kl oGrid.kr 400 1600 ⟨false, 1530200784510120005918579614722222668525910968299444465124177245854633873560⟩ ⟨false, 69230054419748196872132843684197385264382469294867821533995597508357295570⟩ ⟨false, 1415914505039615891951623131674453377409640493347587564956355232003054312776⟩ ⟨false, 183516333890252310839089326731966676380652944246724721701817611359936856354⟩ = true := by
  decide +kernel

theorem b_422_2000 : bothSeg evalE (oGrid.idx 422) (oGrid.dm 422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 422) oGrid.kl oGrid.kr 400 2000 ⟨false, 1415914505039615891951623131674453377409640493347587564956355232003054312776⟩ ⟨false, 183516333890252310839089326731966676380652944246724721701817611359936856354⟩ ⟨false, 1417312457354405941539388259664225352541588123621070206730248722521823643186⟩ ⟨false, 190366186557950983191130798007702549453838628931489329508499687993781989878⟩ = true := by
  decide +kernel

theorem b_422_2400 : bothLoop evalE (oGrid.idx 422) (oGrid.dm 422) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 422) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1417312457354405941539388259664225352541588123621070206730248722521823643186⟩ ⟨false, 190366186557950983191130798007702549453838628931489329508499687993781989878⟩ = true := by
  decide +kernel

theorem o_row_422 : oGrid.row evalE 422 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_422_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_422_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_422_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_422_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_422_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_422_2000).1 (bothLoop_sound b_422_2400).1))))))

theorem n_row_422 : nGrid.row evalE 422 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_422_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_422_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_422_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_422_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_422_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_422_2000).2 (bothLoop_sound b_422_2400).2))))))

theorem b_423_0 : bothSeg evalE (oGrid.idx 423) (oGrid.dm 423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 423) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 909789891002063910553566765571660195258482623646481658383443134150980326288⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_423_400 : bothSeg evalE (oGrid.idx 423) (oGrid.dm 423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 423) oGrid.kl oGrid.kr 400 400 ⟨false, 909789891002063910553566765571660195258482623646481658383443134150980326288⟩ ⟨false, 0⟩ ⟨false, 1443893218511527024184710531945840635979737617228120584143733508052284761832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_423_800 : bothSeg evalE (oGrid.idx 423) (oGrid.dm 423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 423) oGrid.kl oGrid.kr 400 800 ⟨false, 1443893218511527024184710531945840635979737617228120584143733508052284761832⟩ ⟨false, 0⟩ ⟨false, 1588706657725238212733785229059715358639640031300965569232622825866809184608⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_423_1200 : bothSeg evalE (oGrid.idx 423) (oGrid.dm 423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 423) oGrid.kl oGrid.kr 400 1200 ⟨false, 1588706657725238212733785229059715358639640031300965569232622825866809184608⟩ ⟨false, 0⟩ ⟨false, 1520660579272301632987217440036843071574570815284171774884545081533294680522⟩ ⟨false, 69710969610306518205839511536870142839122235617296984951651732942401116980⟩ = true := by
  decide +kernel

theorem b_423_1600 : bothSeg evalE (oGrid.idx 423) (oGrid.dm 423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 423) oGrid.kl oGrid.kr 400 1600 ⟨false, 1520660579272301632987217440036843071574570815284171774884545081533294680522⟩ ⟨false, 69710969610306518205839511536870142839122235617296984951651732942401116980⟩ ⟨false, 1406952123596743645794611087052990868247930034113854234374109911551744835734⟩ ⟨false, 183419425285864505398445864520722346165763016787614525462086902923950961768⟩ = true := by
  decide +kernel

theorem b_423_2000 : bothSeg evalE (oGrid.idx 423) (oGrid.dm 423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 423) oGrid.kl oGrid.kr 400 2000 ⟨false, 1406952123596743645794611087052990868247930034113854234374109911551744835734⟩ ⟨false, 183419425285864505398445864520722346165763016787614525462086902923950961768⟩ ⟨false, 1408379872620967668528831064340484311708388149535808042411749429038822257534⟩ ⟨false, 190257117190447438145808277019215524042940401933943360307113371313797450774⟩ = true := by
  decide +kernel

theorem b_423_2400 : bothLoop evalE (oGrid.idx 423) (oGrid.dm 423) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 423) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1408379872620967668528831064340484311708388149535808042411749429038822257534⟩ ⟨false, 190257117190447438145808277019215524042940401933943360307113371313797450774⟩ = true := by
  decide +kernel

theorem o_row_423 : oGrid.row evalE 423 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_423_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_423_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_423_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_423_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_423_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_423_2000).1 (bothLoop_sound b_423_2400).1))))))

theorem n_row_423 : nGrid.row evalE 423 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_423_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_423_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_423_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_423_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_423_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_423_2000).2 (bothLoop_sound b_423_2400).2))))))

theorem b_424_0 : bothSeg evalE (oGrid.idx 424) (oGrid.dm 424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 424) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 905091048392072980396972847760570304855109494033283922636401169804692441844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_424_400 : bothSeg evalE (oGrid.idx 424) (oGrid.dm 424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 424) oGrid.kl oGrid.kr 400 400 ⟨false, 905091048392072980396972847760570304855109494033283922636401169804692441844⟩ ⟨false, 0⟩ ⟨false, 1436167862403878586990874775023202955997137983804785318299352114387666073818⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_424_800 : bothSeg evalE (oGrid.idx 424) (oGrid.dm 424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 424) oGrid.kl oGrid.kr 400 800 ⟨false, 1436167862403878586990874775023202955997137983804785318299352114387666073818⟩ ⟨false, 0⟩ ⟨false, 1579745145847415608700282837096362940698503383648906531019211894978320176766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_424_1200 : bothSeg evalE (oGrid.idx 424) (oGrid.dm 424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 424) oGrid.kl oGrid.kr 400 1200 ⟨false, 1579745145847415608700282837096362940698503383648906531019211894978320176766⟩ ⟨false, 0⟩ ⟨false, 1511156897607628165006687743703621508176335068586873934226508945142163974490⟩ ⟨false, 70189390283666214354225543482579285040863705835611965467327588155490631220⟩ = true := by
  decide +kernel

theorem b_424_1600 : bothSeg evalE (oGrid.idx 424) (oGrid.dm 424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 424) oGrid.kl oGrid.kr 400 1600 ⟨false, 1511156897607628165006687743703621508176335068586873934226508945142163974490⟩ ⟨false, 70189390283666214354225543482579285040863705835611965467327588155490631220⟩ ⟨false, 1398024404353728806480410517896595255344192486687294836157988883634837389486⟩ ⟨false, 183321883537565572880502769289605537873006287735191063535847649662817216224⟩ = true := by
  decide +kernel

theorem b_424_2000 : bothSeg evalE (oGrid.idx 424) (oGrid.dm 424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 424) oGrid.kl oGrid.kr 400 2000 ⟨false, 1398024404353728806480410517896595255344192486687294836157988883634837389486⟩ ⟨false, 183321883537565572880502769289605537873006287735191063535847649662817216224⟩ ⟨false, 1399483057698402127991664728929447189295654669347734869586934658212991789332⟩ ⟨false, 190145880862274985956739942761595694069936417953618798880974363751877804240⟩ = true := by
  decide +kernel

theorem b_424_2400 : bothLoop evalE (oGrid.idx 424) (oGrid.dm 424) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 424) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1399483057698402127991664728929447189295654669347734869586934658212991789332⟩ ⟨false, 190145880862274985956739942761595694069936417953618798880974363751877804240⟩ = true := by
  decide +kernel

theorem o_row_424 : oGrid.row evalE 424 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_424_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_424_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_424_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_424_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_424_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_424_2000).1 (bothLoop_sound b_424_2400).1))))))

theorem n_row_424 : nGrid.row evalE 424 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_424_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_424_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_424_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_424_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_424_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_424_2000).2 (bothLoop_sound b_424_2400).2))))))

theorem b_425_0 : bothSeg evalE (oGrid.idx 425) (oGrid.dm 425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 425) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 900409027689029805147954396738490862811850747895738291388708221985072789140⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_425_400 : bothSeg evalE (oGrid.idx 425) (oGrid.dm 425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 425) oGrid.kl oGrid.kr 400 400 ⟨false, 900409027689029805147954396738490862811850747895738291388708221985072789140⟩ ⟨false, 0⟩ ⟨false, 1428470089156868675179469810073658955630087562099766247615918605443187015752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_425_800 : bothSeg evalE (oGrid.idx 425) (oGrid.dm 425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 425) oGrid.kl oGrid.kr 400 800 ⟨false, 1428470089156868675179469810073658955630087562099766247615918605443187015752⟩ ⟨false, 0⟩ ⟨false, 1570816060208725096517268491404725229607538236662864798169414360474153776392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_425_1200 : bothSeg evalE (oGrid.idx 425) (oGrid.dm 425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 425) oGrid.kl oGrid.kr 400 1200 ⟨false, 1570816060208725096517268491404725229607538236662864798169414360474153776392⟩ ⟨false, 0⟩ ⟨false, 1501689930128051926317140350401905888652435032982511792787577110969825914038⟩ ⟨false, 70665589725132552627718413932247932498270585442807911506233254947463441478⟩ = true := by
  decide +kernel

theorem b_425_1600 : bothSeg evalE (oGrid.idx 425) (oGrid.dm 425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 425) oGrid.kl oGrid.kr 400 1600 ⟨false, 1501689930128051926317140350401905888652435032982511792787577110969825914038⟩ ⟨false, 70665589725132552627718413932247932498270585442807911506233254947463441478⟩ ⟨false, 1389131568801222398762461939993142726196105937795388346250996383141396489424⟩ ⟨false, 183223951051962080182396824341011094954599680629931358042813982775892866092⟩ = true := by
  decide +kernel

theorem b_425_2000 : bothSeg evalE (oGrid.idx 425) (oGrid.dm 425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 425) oGrid.kl oGrid.kr 400 2000 ⟨false, 1389131568801222398762461939993142726196105937795388346250996383141396489424⟩ ⟨false, 183223951051962080182396824341011094954599680629931358042813982775892866092⟩ ⟨false, 1390622265633553706927267342326784762546403142855835410255575741275961979820⟩ ⟨false, 190033598010114032165641675745200588586133911206670144745564444196012649334⟩ = true := by
  decide +kernel

theorem b_425_2400 : bothLoop evalE (oGrid.idx 425) (oGrid.dm 425) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 425) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1390622265633553706927267342326784762546403142855835410255575741275961979820⟩ ⟨false, 190033598010114032165641675745200588586133911206670144745564444196012649334⟩ = true := by
  decide +kernel

theorem o_row_425 : oGrid.row evalE 425 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_425_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_425_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_425_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_425_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_425_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_425_2000).1 (bothLoop_sound b_425_2400).1))))))

theorem n_row_425 : nGrid.row evalE 425 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_425_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_425_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_425_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_425_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_425_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_425_2000).2 (bothLoop_sound b_425_2400).2))))))

theorem b_426_0 : bothSeg evalE (oGrid.idx 426) (oGrid.dm 426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 426) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 895743784115039419258256178179458486349483062821907473233431327290692682970⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_426_400 : bothSeg evalE (oGrid.idx 426) (oGrid.dm 426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 426) oGrid.kl oGrid.kr 400 400 ⟨false, 895743784115039419258256178179458486349483062821907473233431327290692682970⟩ ⟨false, 0⟩ ⟨false, 1420799813913126097699753980715130189743626932103859322688624694085347000230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_426_800 : bothSeg evalE (oGrid.idx 426) (oGrid.dm 426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 426) oGrid.kl oGrid.kr 400 800 ⟨false, 1420799813913126097699753980715130189743626932103859322688624694085347000230⟩ ⟨false, 0⟩ ⟨false, 1561919265201756901576566873610967363944376081099917233871088244646648161238⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_426_1200 : bothSeg evalE (oGrid.idx 426) (oGrid.dm 426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 426) oGrid.kl oGrid.kr 400 1200 ⟨false, 1561919265201756901576566873610967363944376081099917233871088244646648161238⟩ ⟨false, 0⟩ ⟨false, 1492259469040725992907407350229544390214166572259822585785612289537788072370⟩ ⟨false, 71139859946719055903924363971093889916833145547352465762216165390335575098⟩ = true := by
  decide +kernel

theorem b_426_1600 : bothSeg evalE (oGrid.idx 426) (oGrid.dm 426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 426) oGrid.kl oGrid.kr 400 1600 ⟨false, 1492259469040725992907407350229544390214166572259822585785612289537788072370⟩ ⟨false, 71139859946719055903924363971093889916833145547352465762216165390335575098⟩ ⟨false, 1380273401655107801930248834525473058966438444176865125489567464794037323134⟩ ⟨false, 183125927332337246881082879675165221164561273630309926058260990134086324334⟩ = true := by
  decide +kernel

theorem b_426_2000 : bothSeg evalE (oGrid.idx 426) (oGrid.dm 426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 426) oGrid.kl oGrid.kr 400 2000 ⟨false, 1380273401655107801930248834525473058966438444176865125489567464794037323134⟩ ⟨false, 183125927332337246881082879675165221164561273630309926058260990134086324334⟩ ⟨false, 1381797313555244200153058211666096011021786394749012618225990948941832379960⟩ ⟨false, 189920119535278046129200353969327500513968056557836353273120995493524815034⟩ = true := by
  decide +kernel

theorem b_426_2400 : bothLoop evalE (oGrid.idx 426) (oGrid.dm 426) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 426) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1381797313555244200153058211666096011021786394749012618225990948941832379960⟩ ⟨false, 189920119535278046129200353969327500513968056557836353273120995493524815034⟩ = true := by
  decide +kernel

theorem o_row_426 : oGrid.row evalE 426 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_426_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_426_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_426_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_426_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_426_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_426_2000).1 (bothLoop_sound b_426_2400).1))))))

theorem n_row_426 : nGrid.row evalE 426 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_426_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_426_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_426_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_426_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_426_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_426_2000).2 (bothLoop_sound b_426_2400).2))))))

theorem b_427_0 : bothSeg evalE (oGrid.idx 427) (oGrid.dm 427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 427) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 891095274783267633167449155594458004892291080121829913309159430329784259918⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_427_400 : bothSeg evalE (oGrid.idx 427) (oGrid.dm 427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 427) oGrid.kl oGrid.kr 400 400 ⟨false, 891095274783267633167449155594458004892291080121829913309159430329784259918⟩ ⟨false, 0⟩ ⟨false, 1413156968415555486866330554921385625938566498254383901085678402521396508712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_427_800 : bothSeg evalE (oGrid.idx 427) (oGrid.dm 427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 427) oGrid.kl oGrid.kr 400 800 ⟨false, 1413156968415555486866330554921385625938566498254383901085678402521396508712⟩ ⟨false, 0⟩ ⟨false, 1553054553805058288780500035436216877785214944066299702938570496585943712222⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_427_1200 : bothSeg evalE (oGrid.idx 427) (oGrid.dm 427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 427) oGrid.kl oGrid.kr 400 1200 ⟨false, 1553054553805058288780500035436216877785214944066299702938570496585943712222⟩ ⟨false, 0⟩ ⟨false, 1482865366267668301683169743563787584002988816440853650103435015311646341594⟩ ⟨false, 71611575114174849251870254388134932059045111203690238847827376490323459862⟩ = true := by
  decide +kernel

theorem b_427_1600 : bothSeg evalE (oGrid.idx 427) (oGrid.dm 427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 427) oGrid.kl oGrid.kr 400 1600 ⟨false, 1482865366267668301683169743563787584002988816440853650103435015311646341594⟩ ⟨false, 71611575114174849251870254388134932059045111203690238847827376490323459862⟩ ⟨false, 1371449756964313311367383386859364921286599344683341585248449058950751089838⟩ ⟨false, 183027184417529839567656611092557594775434582961202303702813332851218711618⟩ = true := by
  decide +kernel

theorem b_427_2000 : bothSeg evalE (oGrid.idx 427) (oGrid.dm 427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 427) oGrid.kl oGrid.kr 400 2000 ⟨false, 1371449756964313311367383386859364921286599344683341585248449058950751089838⟩ ⟨false, 183027184417529839567656611092557594775434582961202303702813332851218711618⟩ ⟨false, 1373008118575506906764334269518455714088629562403200736829305252755644618080⟩ ⟨false, 189804267512359032897274464015037346903785812669689658601609825422798785290⟩ = true := by
  decide +kernel

theorem b_427_2400 : bothLoop evalE (oGrid.idx 427) (oGrid.dm 427) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 427) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1373008118575506906764334269518455714088629562403200736829305252755644618080⟩ ⟨false, 189804267512359032897274464015037346903785812669689658601609825422798785290⟩ = true := by
  decide +kernel

theorem o_row_427 : oGrid.row evalE 427 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_427_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_427_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_427_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_427_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_427_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_427_2000).1 (bothLoop_sound b_427_2400).1))))))

theorem n_row_427 : nGrid.row evalE 427 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_427_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_427_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_427_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_427_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_427_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_427_2000).2 (bothLoop_sound b_427_2400).2))))))

theorem b_428_0 : bothSeg evalE (oGrid.idx 428) (oGrid.dm 428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 428) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 886463454676972879327417414069972688830462757656928282118955623619290304484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_428_400 : bothSeg evalE (oGrid.idx 428) (oGrid.dm 428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 428) oGrid.kl oGrid.kr 400 400 ⟨false, 886463454676972879327417414069972688830462757656928282118955623619290304484⟩ ⟨false, 0⟩ ⟨false, 1405541487411793433382684372539433125311270527088876808299618254706835141850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_428_800 : bothSeg evalE (oGrid.idx 428) (oGrid.dm 428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 428) oGrid.kl oGrid.kr 400 800 ⟨false, 1405541487411793433382684372539433125311270527088876808299618254706835141850⟩ ⟨false, 0⟩ ⟨false, 1544222030488429071177653130756151694019799670213604207799566291111458791754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_428_1200 : bothSeg evalE (oGrid.idx 428) (oGrid.dm 428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 428) oGrid.kl oGrid.kr 400 1200 ⟨false, 1544222030488429071177653130756151694019799670213604207799566291111458791754⟩ ⟨false, 0⟩ ⟨false, 1473507640371045874822646438268206061352913800171557748444723885572971104992⟩ ⟨false, 72081110813571484672467959364542142240929240421807119930105431526508007842⟩ = true := by
  decide +kernel

theorem b_428_1600 : bothSeg evalE (oGrid.idx 428) (oGrid.dm 428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 428) oGrid.kl oGrid.kr 400 1600 ⟨false, 1473507640371045874822646438268206061352913800171557748444723885572971104992⟩ ⟨false, 72081110813571484672467959364542142240929240421807119930105431526508007842⟩ ⟨false, 1362660682446382816531325722657259243988198536782215968726011314119365377292⟩ ⟨false, 182928068738234542963788674975488959605644503811148899648818002980113735542⟩ = true := by
  decide +kernel

theorem b_428_2000 : bothSeg evalE (oGrid.idx 428) (oGrid.dm 428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 428) oGrid.kl oGrid.kr 400 2000 ⟨false, 1362660682446382816531325722657259243988198536782215968726011314119365377292⟩ ⟨false, 182928068738234542963788674975488959605644503811148899648818002980113735542⟩ ⟨false, 1364254740004737081423568974712245348027412355788244518632461856317949889256⟩ ⟨false, 189686969062714759743027039362936905845826053780000509655908507562775849644⟩ = true := by
  decide +kernel

theorem b_428_2400 : bothLoop evalE (oGrid.idx 428) (oGrid.dm 428) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 428) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1364254740004737081423568974712245348027412355788244518632461856317949889256⟩ ⟨false, 189686969062714759743027039362936905845826053780000509655908507562775849644⟩ = true := by
  decide +kernel

theorem o_row_428 : oGrid.row evalE 428 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_428_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_428_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_428_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_428_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_428_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_428_2000).1 (bothLoop_sound b_428_2400).1))))))

theorem n_row_428 : nGrid.row evalE 428 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_428_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_428_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_428_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_428_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_428_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_428_2000).2 (bothLoop_sound b_428_2400).2))))))

theorem b_429_0 : bothSeg evalE (oGrid.idx 429) (oGrid.dm 429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 429) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 881848279208456983197561646858497137521870115158806232300153474172816407162⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_429_400 : bothSeg evalE (oGrid.idx 429) (oGrid.dm 429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 429) oGrid.kl oGrid.kr 400 400 ⟨false, 881848279208456983197561646858497137521870115158806232300153474172816407162⟩ ⟨false, 0⟩ ⟨false, 1397953319054907158796992595475582801076297023263555834203175424795093391856⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_429_800 : bothSeg evalE (oGrid.idx 429) (oGrid.dm 429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 429) oGrid.kl oGrid.kr 400 800 ⟨false, 1397953319054907158796992595475582801076297023263555834203175424795093391856⟩ ⟨false, 0⟩ ⟨false, 1535421598483040513167464781287297372161713162403546763724666397172883632846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_429_1200 : bothSeg evalE (oGrid.idx 429) (oGrid.dm 429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 429) oGrid.kl oGrid.kr 400 1200 ⟨false, 1535421598483040513167464781287297372161713162403546763724666397172883632846⟩ ⟨false, 0⟩ ⟨false, 1464186175659257079296985226571066305676296824330824127336553391722172387788⟩ ⟨false, 72548072204795274659480147062767468172993030225994178045647929421558484678⟩ = true := by
  decide +kernel

theorem b_429_1600 : bothSeg evalE (oGrid.idx 429) (oGrid.dm 429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 429) oGrid.kl oGrid.kr 400 1600 ⟨false, 1464186175659257079296985226571066305676296824330824127336553391722172387788⟩ ⟨false, 72548072204795274659480147062767468172993030225994178045647929421558484678⟩ ⟨false, 1353906053757141509820784531372686207014464772735141738217375215599472122278⟩ ⟨false, 182828194106910844135680842261147566834825081821676567164826105544258750188⟩ = true := by
  decide +kernel

theorem b_429_2000 : bothSeg evalE (oGrid.idx 429) (oGrid.dm 429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 429) oGrid.kl oGrid.kr 400 2000 ⟨false, 1353906053757141509820784531372686207014464772735141738217375215599472122278⟩ ⟨false, 182828194106910844135680842261147566834825081821676567164826105544258750188⟩ ⟨false, 1355537112400288472522564078157279082942185910724594633515211896975285621368⟩ ⟨false, 189568066675868054277757345203580316320711233244867893411423227102527856836⟩ = true := by
  decide +kernel

theorem b_429_2400 : bothLoop evalE (oGrid.idx 429) (oGrid.dm 429) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 429) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1355537112400288472522564078157279082942185910724594633515211896975285621368⟩ ⟨false, 189568066675868054277757345203580316320711233244867893411423227102527856836⟩ = true := by
  decide +kernel

theorem o_row_429 : oGrid.row evalE 429 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_429_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_429_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_429_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_429_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_429_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_429_2000).1 (bothLoop_sound b_429_2400).1))))))

theorem n_row_429 : nGrid.row evalE 429 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_429_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_429_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_429_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_429_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_429_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_429_2000).2 (bothLoop_sound b_429_2400).2))))))

theorem b_430_0 : bothSeg evalE (oGrid.idx 430) (oGrid.dm 430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 430) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 877249704501810221396542160499353303490189127336055425567706878967886469176⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_430_400 : bothSeg evalE (oGrid.idx 430) (oGrid.dm 430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 430) oGrid.kl oGrid.kr 400 400 ⟨false, 877249704501810221396542160499353303490189127336055425567706878967886469176⟩ ⟨false, 0⟩ ⟨false, 1390392377007569342709740043902425963700783440878165898522945377791596572552⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_430_800 : bothSeg evalE (oGrid.idx 430) (oGrid.dm 430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 430) oGrid.kl oGrid.kr 400 800 ⟨false, 1390392377007569342709740043902425963700783440878165898522945377791596572552⟩ ⟨false, 0⟩ ⟨false, 1526653014495430246722715356617137356680773445069996758558680479984821158182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_430_1200 : bothSeg evalE (oGrid.idx 430) (oGrid.dm 430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 430) oGrid.kl oGrid.kr 400 1200 ⟨false, 1526653014495430246722715356617137356680773445069996758558680479984821158182⟩ ⟨false, 0⟩ ⟨false, 1454900845536398005319513891121089134176330840172369257240294412359620853212⟩ ⟨false, 73013433167967842405578328431017710870680881585074259637330274688557620994⟩ = true := by
  decide +kernel

theorem b_430_1600 : bothSeg evalE (oGrid.idx 430) (oGrid.dm 430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 430) oGrid.kl oGrid.kr 400 1600 ⟨false, 1454900845536398005319513891121089134176330840172369257240294412359620853212⟩ ⟨false, 73013433167967842405578328431017710870680881585074259637330274688557620994⟩ ⟨false, 1345185759665077221159376373056996361851864695788973901094279102755534633174⟩ ⟨false, 182728519039288626565715846495110483195147025968469615783345584292643841032⟩ = true := by
  decide +kernel

theorem b_430_2000 : bothSeg evalE (oGrid.idx 430) (oGrid.dm 430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 430) oGrid.kl oGrid.kr 400 2000 ⟨false, 1345185759665077221159376373056996361851864695788973901094279102755534633174⟩ ⟨false, 182728519039288626565715846495110483195147025968469615783345584292643841032⟩ ⟨false, 1346855132976300003872446276810542212933111376803873601552186387555062687534⟩ ⟨false, 189447749124569840945780040649020083608966412370643593003168394726412131014⟩ = true := by
  decide +kernel

theorem b_430_2400 : bothLoop evalE (oGrid.idx 430) (oGrid.dm 430) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 430) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1346855132976300003872446276810542212933111376803873601552186387555062687534⟩ ⟨false, 189447749124569840945780040649020083608966412370643593003168394726412131014⟩ = true := by
  decide +kernel

theorem o_row_430 : oGrid.row evalE 430 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_430_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_430_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_430_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_430_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_430_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_430_2000).1 (bothLoop_sound b_430_2400).1))))))

theorem n_row_430 : nGrid.row evalE 430 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_430_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_430_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_430_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_430_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_430_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_430_2000).2 (bothLoop_sound b_430_2400).2))))))

theorem b_431_0 : bothSeg evalE (oGrid.idx 431) (oGrid.dm 431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 431) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 872667686579236892174970358388932895395823938303085789238829110354389295894⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_431_400 : bothSeg evalE (oGrid.idx 431) (oGrid.dm 431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 431) oGrid.kl oGrid.kr 400 400 ⟨false, 872667686579236892174970358388932895395823938303085789238829110354389295894⟩ ⟨false, 0⟩ ⟨false, 1382858608401949495732292860297895252747176422284137104093026360710902531740⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_431_800 : bothSeg evalE (oGrid.idx 431) (oGrid.dm 431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 431) oGrid.kl oGrid.kr 400 800 ⟨false, 1382858608401949495732292860297895252747176422284137104093026360710902531740⟩ ⟨false, 0⟩ ⟨false, 1517916371825290604962310929816464959956681876207932387626826720812526706218⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_431_1200 : bothSeg evalE (oGrid.idx 431) (oGrid.dm 431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 431) oGrid.kl oGrid.kr 400 1200 ⟨false, 1517916371825290604962310929816464959956681876207932387626826720812526706218⟩ ⟨false, 0⟩ ⟨false, 1445651563044126824726123454192250826251732934614231563198403812046790628112⟩ ⟨false, 73476772044211306759308737555147947054777321225836523684819740766436706822⟩ = true := by
  decide +kernel

theorem b_431_1600 : bothSeg evalE (oGrid.idx 431) (oGrid.dm 431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 431) oGrid.kl oGrid.kr 400 1600 ⟨false, 1445651563044126824726123454192250826251732934614231563198403812046790628112⟩ ⟨false, 73476772044211306759308737555147947054777321225836523684819740766436706822⟩ ⟨false, 1336499715495568131533781141801069273049496425687613171302537736439704970722⟩ ⟨false, 182628619592769999951651049946329500257013830152454915580685816373522364212⟩ = true := by
  decide +kernel

theorem b_431_2000 : bothSeg evalE (oGrid.idx 431) (oGrid.dm 431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 431) oGrid.kl oGrid.kr 400 2000 ⟨false, 1336499715495568131533781141801069273049496425687613171302537736439704970722⟩ ⟨false, 182628619592769999951651049946329500257013830152454915580685816373522364212⟩ ⟨false, 1338208754150293089540464353265612904258551707494331036481892851472206702730⟩ ⟨false, 189325643018852569859675653023526204157635042097889934270607332463742295856⟩ = true := by
  decide +kernel

theorem b_431_2400 : bothLoop evalE (oGrid.idx 431) (oGrid.dm 431) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 431) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 1338208754150293089540464353265612904258551707494331036481892851472206702730⟩ ⟨false, 189325643018852569859675653023526204157635042097889934270607332463742295856⟩ = true := by
  decide +kernel

theorem o_row_431 : oGrid.row evalE 431 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_431_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_431_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_431_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_431_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_431_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_431_2000).1 (bothLoop_sound b_431_2400).1))))))

theorem n_row_431 : nGrid.row evalE 431 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_431_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_431_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_431_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_431_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_431_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_431_2000).2 (bothLoop_sound b_431_2400).2))))))

theorem o_blk_408 : allFrom (fun j => oGrid.row evalE j) 408 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 408) o_row_408 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 409) o_row_409 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 410) o_row_410 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 411) o_row_411 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 412) o_row_412 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 413) o_row_413 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 414) o_row_414 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 415) o_row_415 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 416) o_row_416 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 417) o_row_417 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 418) o_row_418 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 419) o_row_419 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 420) o_row_420 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 421) o_row_421 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 422) o_row_422 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 423) o_row_423 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 424) o_row_424 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 425) o_row_425 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 426) o_row_426 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 427) o_row_427 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 428) o_row_428 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 429) o_row_429 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 430) o_row_430 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 431) o_row_431 (allFrom_zero (fun j => oGrid.row evalE j) 432)))))))))))))))))))))))))

theorem n_blk_408 : allFrom (fun j => nGrid.row evalE j) 408 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 408) n_row_408 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 409) n_row_409 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 410) n_row_410 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 411) n_row_411 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 412) n_row_412 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 413) n_row_413 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 414) n_row_414 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 415) n_row_415 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 416) n_row_416 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 417) n_row_417 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 418) n_row_418 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 419) n_row_419 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 420) n_row_420 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 421) n_row_421 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 422) n_row_422 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 423) n_row_423 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 424) n_row_424 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 425) n_row_425 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 426) n_row_426 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 427) n_row_427 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 428) n_row_428 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 429) n_row_429 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 430) n_row_430 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 431) n_row_431 (allFrom_zero (fun j => nGrid.row evalE j) 432)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
