/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 3 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `72`–`95`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_72_0 : bothSeg evalE (oGrid.idx 72) (oGrid.dm 72) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 72) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 4009434265128873083717251185433293914956923844902507364734070800869631548380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_72_400 : bothSeg evalE (oGrid.idx 72) (oGrid.dm 72) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 72) oGrid.kl oGrid.kr 400 400 ⟨false, 4009434265128873083717251185433293914956923844902507364734070800869631548380⟩ ⟨false, 0⟩ ⟨false, 6463792481328106660541732525908387223435145857518035745679256083306963547448⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_72_800 : bothSeg evalE (oGrid.idx 72) (oGrid.dm 72) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 72) oGrid.kl oGrid.kr 400 800 ⟨false, 6463792481328106660541732525908387223435145857518035745679256083306963547448⟩ ⟨false, 0⟩ ⟨false, 7388223135082794963154596501701063631292025807974174566729630225959394283836⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_72_1200 : bothSeg evalE (oGrid.idx 72) (oGrid.dm 72) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 72) oGrid.kl oGrid.kr 400 1200 ⟨false, 7388223135082794963154596501701063631292025807974174566729630225959394283836⟩ ⟨false, 0⟩ ⟨false, 7556301703486832305532044013146108455768285160628898568162495458936058135318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_72_1600 : bothSeg evalE (oGrid.idx 72) (oGrid.dm 72) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 72) oGrid.kl oGrid.kr 400 1600 ⟨false, 7556301703486832305532044013146108455768285160628898568162495458936058135318⟩ ⟨false, 0⟩ ⟨false, 7380046873734353333128020537482625922650869513923714622632123000699137125844⟩ ⟨false, 176681020821298432435384909024094165307343455420200507193470502947092383336⟩ = true := by
  decide +kernel

theorem b_72_2000 : bothSeg evalE (oGrid.idx 72) (oGrid.dm 72) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 72) oGrid.kl oGrid.kr 400 2000 ⟨false, 7380046873734353333128020537482625922650869513923714622632123000699137125844⟩ ⟨false, 176681020821298432435384909024094165307343455420200507193470502947092383336⟩ ⟨false, 7308839744905593003591126043029451914517877412225625333866365595672689627956⟩ ⟨false, 248548709600621650633391141137620797508110139920428598660570726097573186902⟩ = true := by
  decide +kernel

theorem b_72_2400 : bothLoop evalE (oGrid.idx 72) (oGrid.dm 72) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 72) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7308839744905593003591126043029451914517877412225625333866365595672689627956⟩ ⟨false, 248548709600621650633391141137620797508110139920428598660570726097573186902⟩ = true := by
  decide +kernel

theorem o_row_72 : oGrid.row evalE 72 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_72_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_72_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_72_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_72_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_72_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_72_2000).1 (bothLoop_sound b_72_2400).1))))))

theorem n_row_72 : nGrid.row evalE 72 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_72_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_72_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_72_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_72_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_72_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_72_2000).2 (bothLoop_sound b_72_2400).2))))))

theorem b_73_0 : bothSeg evalE (oGrid.idx 73) (oGrid.dm 73) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 73) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3995023610890127300818787200825815950972576590060871007161526942956587671766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_73_400 : bothSeg evalE (oGrid.idx 73) (oGrid.dm 73) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 73) oGrid.kl oGrid.kr 400 400 ⟨false, 3995023610890127300818787200825815950972576590060871007161526942956587671766⟩ ⟨false, 0⟩ ⟨false, 6440884133653210606497894272536328393503180699310726070360792078935841387300⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_73_800 : bothSeg evalE (oGrid.idx 73) (oGrid.dm 73) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 73) oGrid.kl oGrid.kr 400 800 ⟨false, 6440884133653210606497894272536328393503180699310726070360792078935841387300⟩ ⟨false, 0⟩ ⟨false, 7362014790633527828034427372439106077385423828026096556314945456216211618802⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_73_1200 : bothSeg evalE (oGrid.idx 73) (oGrid.dm 73) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 73) oGrid.kl oGrid.kr 400 1200 ⟨false, 7362014790633527828034427372439106077385423828026096556314945456216211618802⟩ ⟨false, 0⟩ ⟨false, 7529202868411821134335949803005047903416255221143363683325402200639520509580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_73_1600 : bothSeg evalE (oGrid.idx 73) (oGrid.dm 73) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 73) oGrid.kl oGrid.kr 400 1600 ⟨false, 7529202868411821134335949803005047903416255221143363683325402200639520509580⟩ ⟨false, 0⟩ ⟨false, 7352729509325583085968173675878727618745596367218663420627319398972758658484⟩ ⟨false, 176879639908825940912697948187115825854652285866292593159163165649515978666⟩ = true := by
  decide +kernel

theorem b_73_2000 : bothSeg evalE (oGrid.idx 73) (oGrid.dm 73) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 73) oGrid.kl oGrid.kr 400 2000 ⟨false, 7352729509325583085968173675878727618745596367218663420627319398972758658484⟩ ⟨false, 176879639908825940912697948187115825854652285866292593159163165649515978666⟩ ⟨false, 7281946746982743879648452130330264695108375047811330494525467095651570951164⟩ ⟨false, 248324285912574071662123921248565241504943011502201290519212760986245444702⟩ = true := by
  decide +kernel

theorem b_73_2400 : bothLoop evalE (oGrid.idx 73) (oGrid.dm 73) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 73) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7281946746982743879648452130330264695108375047811330494525467095651570951164⟩ ⟨false, 248324285912574071662123921248565241504943011502201290519212760986245444702⟩ = true := by
  decide +kernel

theorem o_row_73 : oGrid.row evalE 73 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_73_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_73_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_73_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_73_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_73_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_73_2000).1 (bothLoop_sound b_73_2400).1))))))

theorem n_row_73 : nGrid.row evalE 73 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_73_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_73_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_73_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_73_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_73_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_73_2000).2 (bothLoop_sound b_73_2400).2))))))

theorem b_74_0 : bothSeg evalE (oGrid.idx 74) (oGrid.dm 74) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 74) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3980655513269273184429528346542088552035493177426050270697770001130561040108⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_74_400 : bothSeg evalE (oGrid.idx 74) (oGrid.dm 74) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 74) oGrid.kl oGrid.kr 400 400 ⟨false, 3980655513269273184429528346542088552035493177426050270697770001130561040108⟩ ⟨false, 0⟩ ⟨false, 6418039286652701340322760196789377132217853007427119554943096561002096525426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_74_800 : bothSeg evalE (oGrid.idx 74) (oGrid.dm 74) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 74) oGrid.kl oGrid.kr 400 800 ⟨false, 6418039286652701340322760196789377132217853007427119554943096561002096525426⟩ ⟨false, 0⟩ ⟨false, 7335876315982591013528344997017824136942300611267399585250842915923048392714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_74_1200 : bothSeg evalE (oGrid.idx 74) (oGrid.dm 74) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 74) oGrid.kl oGrid.kr 400 1200 ⟨false, 7335876315982591013528344997017824136942300611267399585250842915923048392714⟩ ⟨false, 0⟩ ⟨false, 7502175418389150728913125154874009491300022219891829737569036596029868481128⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_74_1600 : bothSeg evalE (oGrid.idx 74) (oGrid.dm 74) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 74) oGrid.kl oGrid.kr 400 1600 ⟨false, 7502175418389150728913125154874009491300022219891829737569036596029868481128⟩ ⟨false, 0⟩ ⟨false, 7325485902277019702442725084239361066693122218996025296094672416341459315416⟩ ⟨false, 177076266695009592715349494148639405477030772848116822318284948914682263910⟩ = true := by
  decide +kernel

theorem b_74_2000 : bothSeg evalE (oGrid.idx 74) (oGrid.dm 74) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 74) oGrid.kl oGrid.kr 400 2000 ⟨false, 7325485902277019702442725084239361066693122218996025296094672416341459315416⟩ ⟨false, 177076266695009592715349494148639405477030772848116822318284948914682263910⟩ ⟨false, 7255125157753501463267299938611901698513692457615879038004910161978800549318⟩ ⟨false, 248100407895824581500389202335834983922398899534240673556361654812035111822⟩ = true := by
  decide +kernel

theorem b_74_2400 : bothLoop evalE (oGrid.idx 74) (oGrid.dm 74) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 74) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7255125157753501463267299938611901698513692457615879038004910161978800549318⟩ ⟨false, 248100407895824581500389202335834983922398899534240673556361654812035111822⟩ = true := by
  decide +kernel

theorem o_row_74 : oGrid.row evalE 74 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_74_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_74_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_74_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_74_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_74_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_74_2000).1 (bothLoop_sound b_74_2400).1))))))

theorem n_row_74 : nGrid.row evalE 74 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_74_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_74_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_74_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_74_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_74_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_74_2000).2 (bothLoop_sound b_74_2400).2))))))

theorem b_75_0 : bothSeg evalE (oGrid.idx 75) (oGrid.dm 75) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 75) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3966329796771499129268058254211785667813600026365104604926618878178817229532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_75_400 : bothSeg evalE (oGrid.idx 75) (oGrid.dm 75) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 75) oGrid.kl oGrid.kr 400 400 ⟨false, 3966329796771499129268058254211785667813600026365104604926618878178817229532⟩ ⟨false, 0⟩ ⟨false, 6395257752211004777870979210207139178317277967412042592701631975061087071092⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_75_800 : bothSeg evalE (oGrid.idx 75) (oGrid.dm 75) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 75) oGrid.kl oGrid.kr 400 800 ⟨false, 6395257752211004777870979210207139178317277967412042592701631975061087071092⟩ ⟨false, 0⟩ ⟨false, 7309807569097534021409029569274786322783485001724993873562916027552654035432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_75_1200 : bothSeg evalE (oGrid.idx 75) (oGrid.dm 75) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 75) oGrid.kl oGrid.kr 400 1200 ⟨false, 7309807569097534021409029569274786322783485001724993873562916027552654035432⟩ ⟨false, 0⟩ ⟨false, 7475219145147455494925881514476171766684647720234415251434318420630231627614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_75_1600 : bothSeg evalE (oGrid.idx 75) (oGrid.dm 75) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 75) oGrid.kl oGrid.kr 400 1600 ⟨false, 7475219145147455494925881514476171766684647720234415251434318420630231627614⟩ ⟨false, 0⟩ ⟨false, 7298316086580837858095853912676833338654097436133419424742086507996985904996⟩ ⟨false, 177271513379359500642794660015374341680120560874392846104712510471815711514⟩ = true := by
  decide +kernel

theorem b_75_2000 : bothSeg evalE (oGrid.idx 75) (oGrid.dm 75) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 75) oGrid.kl oGrid.kr 400 2000 ⟨false, 7298316086580837858095853912676833338654097436133419424742086507996985904996⟩ ⟨false, 177271513379359500642794660015374341680120560874392846104712510471815711514⟩ ⟨false, 7228374999603705176649641818369065175028608722466617678140253045182111404424⟩ ⟨false, 247877293344070629259243103642347786960454036377498515259385257745896370482⟩ = true := by
  decide +kernel

theorem b_75_2400 : bothLoop evalE (oGrid.idx 75) (oGrid.dm 75) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 75) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7228374999603705176649641818369065175028608722466617678140253045182111404424⟩ ⟨false, 247877293344070629259243103642347786960454036377498515259385257745896370482⟩ = true := by
  decide +kernel

theorem o_row_75 : oGrid.row evalE 75 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_75_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_75_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_75_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_75_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_75_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_75_2000).1 (bothLoop_sound b_75_2400).1))))))

theorem n_row_75 : nGrid.row evalE 75 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_75_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_75_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_75_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_75_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_75_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_75_2000).2 (bothLoop_sound b_75_2400).2))))))

theorem b_76_0 : bothSeg evalE (oGrid.idx 76) (oGrid.dm 76) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 76) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3952046364931425039150525924315261621278758463093810696567545027629936537054⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_76_400 : bothSeg evalE (oGrid.idx 76) (oGrid.dm 76) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 76) oGrid.kl oGrid.kr 400 400 ⟨false, 3952046364931425039150525924315261621278758463093810696567545027629936537054⟩ ⟨false, 0⟩ ⟨false, 6372539369104392280190701013078829511109127838605321482568839659533453122914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_76_800 : bothSeg evalE (oGrid.idx 76) (oGrid.dm 76) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 76) oGrid.kl oGrid.kr 400 800 ⟨false, 6372539369104392280190701013078829511109127838605321482568839659533453122914⟩ ⟨false, 0⟩ ⟨false, 7283808321066050071121873634835709468077124019186400081030369891652802562236⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_76_1200 : bothSeg evalE (oGrid.idx 76) (oGrid.dm 76) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 76) oGrid.kl oGrid.kr 400 1200 ⟨false, 7283808321066050071121873634835709468077124019186400081030369891652802562236⟩ ⟨false, 0⟩ ⟨false, 7448333796132774807502569752494409175569814030238576969168700874844473919888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_76_1600 : bothSeg evalE (oGrid.idx 76) (oGrid.dm 76) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 76) oGrid.kl oGrid.kr 400 1600 ⟨false, 7448333796132774807502569752494409175569814030238576969168700874844473919888⟩ ⟨false, 0⟩ ⟨false, 7271219657766051170632317465830655463466680308472512494542049273723862004236⟩ ⟨false, 177465763620416930925258058280904429597395301154698817393357894073481595788⟩ = true := by
  decide +kernel

theorem b_76_2000 : bothSeg evalE (oGrid.idx 76) (oGrid.dm 76) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 76) oGrid.kl oGrid.kr 400 2000 ⟨false, 7271219657766051170632317465830655463466680308472512494542049273723862004236⟩ ⟨false, 177465763620416930925258058280904429597395301154698817393357894073481595788⟩ ⟨false, 7201695853038767506230594681815215383444356995294810693168277305599464794936⟩ ⟨false, 247655794160545804999379801746625052636515390223189770654498532779135894648⟩ = true := by
  decide +kernel

theorem b_76_2400 : bothLoop evalE (oGrid.idx 76) (oGrid.dm 76) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 76) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7201695853038767506230594681815215383444356995294810693168277305599464794936⟩ ⟨false, 247655794160545804999379801746625052636515390223189770654498532779135894648⟩ = true := by
  decide +kernel

theorem o_row_76 : oGrid.row evalE 76 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_76_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_76_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_76_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_76_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_76_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_76_2000).1 (bothLoop_sound b_76_2400).1))))))

theorem n_row_76 : nGrid.row evalE 76 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_76_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_76_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_76_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_76_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_76_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_76_2000).2 (bothLoop_sound b_76_2400).2))))))

theorem b_77_0 : bothSeg evalE (oGrid.idx 77) (oGrid.dm 77) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 77) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3937805022725525757345589926945354725713033430184868745708239214988161808898⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_77_400 : bothSeg evalE (oGrid.idx 77) (oGrid.dm 77) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 77) oGrid.kl oGrid.kr 400 400 ⟨false, 3937805022725525757345589926945354725713033430184868745708239214988161808898⟩ ⟨false, 0⟩ ⟨false, 6349883861103352097121776024553980759568279265781387065719012176627680879314⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_77_800 : bothSeg evalE (oGrid.idx 77) (oGrid.dm 77) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 77) oGrid.kl oGrid.kr 400 800 ⟨false, 6349883861103352097121776024553980759568279265781387065719012176627680879314⟩ ⟨false, 0⟩ ⟨false, 7257878320465390223234399811152702829564350922112350915097922976655933409700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_77_1200 : bothSeg evalE (oGrid.idx 77) (oGrid.dm 77) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 77) oGrid.kl oGrid.kr 400 1200 ⟨false, 7257878320465390223234399811152702829564350922112350915097922976655933409700⟩ ⟨false, 0⟩ ⟨false, 7421519029358945712883510078379723591660983048176502839942370108510282408258⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_77_1600 : bothSeg evalE (oGrid.idx 77) (oGrid.dm 77) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 77) oGrid.kl oGrid.kr 400 1600 ⟨false, 7421519029358945712883510078379723591660983048176502839942370108510282408258⟩ ⟨false, 0⟩ ⟨false, 7244196151750164153092712641029534913210247536673877997359837201830698574262⟩ ⟨false, 177658722717499310191050128670289866566069509489948081224753087074605642076⟩ = true := by
  decide +kernel

theorem b_77_2000 : bothSeg evalE (oGrid.idx 77) (oGrid.dm 77) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 77) oGrid.kl oGrid.kr 400 2000 ⟨false, 7244196151750164153092712641029534913210247536673877997359837201830698574262⟩ ⟨false, 177658722717499310191050128670289866566069509489948081224753087074605642076⟩ ⟨false, 7175087286215295289143156619993626928517955421825107873845005053760886533698⟩ ⟨false, 247435110446670536952259110217374774588346036615973283748238557048930549262⟩ = true := by
  decide +kernel

theorem b_77_2400 : bothLoop evalE (oGrid.idx 77) (oGrid.dm 77) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 77) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7175087286215295289143156619993626928517955421825107873845005053760886533698⟩ ⟨false, 247435110446670536952259110217374774588346036615973283748238557048930549262⟩ = true := by
  decide +kernel

theorem o_row_77 : oGrid.row evalE 77 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_77_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_77_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_77_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_77_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_77_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_77_2000).1 (bothLoop_sound b_77_2400).1))))))

theorem n_row_77 : nGrid.row evalE 77 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_77_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_77_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_77_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_77_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_77_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_77_2000).2 (bothLoop_sound b_77_2400).2))))))

theorem b_78_0 : bothSeg evalE (oGrid.idx 78) (oGrid.dm 78) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 78) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3923605726832824271870584726877531510268860393931726065164317195636566812162⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_78_400 : bothSeg evalE (oGrid.idx 78) (oGrid.dm 78) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 78) oGrid.kl oGrid.kr 400 400 ⟨false, 3923605726832824271870584726877531510268860393931726065164317195636566812162⟩ ⟨false, 0⟩ ⟨false, 6327291204772441262066450235714773619717497561529613254027710516016572705812⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_78_800 : bothSeg evalE (oGrid.idx 78) (oGrid.dm 78) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 78) oGrid.kl oGrid.kr 400 800 ⟨false, 6327291204772441262066450235714773619717497561529613254027710516016572705812⟩ ⟨false, 0⟩ ⟨false, 7232017593597575195383953020806203542794857495673081876399296143945770412232⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_78_1200 : bothSeg evalE (oGrid.idx 78) (oGrid.dm 78) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 78) oGrid.kl oGrid.kr 400 1200 ⟨false, 7232017593597575195383953020806203542794857495673081876399296143945770412232⟩ ⟨false, 0⟩ ⟨false, 7394774863943133198555450650333729047522605449294283967839350253280581600022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_78_1600 : bothSeg evalE (oGrid.idx 78) (oGrid.dm 78) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 78) oGrid.kl oGrid.kr 400 1600 ⟨false, 7394774863943133198555450650333729047522605449294283967839350253280581600022⟩ ⟨false, 0⟩ ⟨false, 7217246239405550458595599654663811522309813935866621010509050817049367761050⟩ ⟨false, 177849342164448288924925712395341165473241721713531923743755920954483181496⟩ = true := by
  decide +kernel

theorem b_78_2000 : bothSeg evalE (oGrid.idx 78) (oGrid.dm 78) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 78) oGrid.kl oGrid.kr 400 2000 ⟨false, 7217246239405550458595599654663811522309813935866621010509050817049367761050⟩ ⟨false, 177849342164448288924925712395341165473241721713531923743755920954483181496⟩ ⟨false, 7148549977552386044240481962332026101583841823934381040961854926145074466680⟩ ⟨false, 247214654896095987773596018876861190316900369761320779274981960703760126170⟩ = true := by
  decide +kernel

theorem b_78_2400 : bothLoop evalE (oGrid.idx 78) (oGrid.dm 78) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 78) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7148549977552386044240481962332026101583841823934381040961854926145074466680⟩ ⟨false, 247214654896095987773596018876861190316900369761320779274981960703760126170⟩ = true := by
  decide +kernel

theorem o_row_78 : oGrid.row evalE 78 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_78_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_78_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_78_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_78_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_78_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_78_2000).1 (bothLoop_sound b_78_2400).1))))))

theorem n_row_78 : nGrid.row evalE 78 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_78_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_78_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_78_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_78_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_78_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_78_2000).2 (bothLoop_sound b_78_2400).2))))))

theorem b_79_0 : bothSeg evalE (oGrid.idx 79) (oGrid.dm 79) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 79) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3909448371834298708757680453632152385284648955446377564427032728999783541264⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_79_400 : bothSeg evalE (oGrid.idx 79) (oGrid.dm 79) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 79) oGrid.kl oGrid.kr 400 400 ⟨false, 3909448371834298708757680453632152385284648955446377564427032728999783541264⟩ ⟨false, 0⟩ ⟨false, 6304761248514067130562590426558830711156343039612286668365438769528243563700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_79_800 : bothSeg evalE (oGrid.idx 79) (oGrid.dm 79) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 79) oGrid.kl oGrid.kr 400 800 ⟨false, 6304761248514067130562590426558830711156343039612286668365438769528243563700⟩ ⟨false, 0⟩ ⟨false, 7206225928754439144845054422718388175417007354426019425228740838520913845946⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_79_1200 : bothSeg evalE (oGrid.idx 79) (oGrid.dm 79) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 79) oGrid.kl oGrid.kr 400 1200 ⟨false, 7206225928754439144845054422718388175417007354426019425228740838520913845946⟩ ⟨false, 0⟩ ⟨false, 7368100987852508180195533591828427670063467913229502484900539773636551233334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_79_1600 : bothSeg evalE (oGrid.idx 79) (oGrid.dm 79) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 79) oGrid.kl oGrid.kr 400 1600 ⟨false, 7368100987852508180195533591828427670063467913229502484900539773636551233334⟩ ⟨false, 0⟩ ⟨false, 7190369002198295747679535394117607311940859137125618814922970737260084078456⟩ ⟨false, 178038319740839123941287513524605891904171748084229809888449394403295487494⟩ = true := by
  decide +kernel

theorem b_79_2000 : bothSeg evalE (oGrid.idx 79) (oGrid.dm 79) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 79) oGrid.kl oGrid.kr 400 2000 ⟨false, 7190369002198295747679535394117607311940859137125618814922970737260084078456⟩ ⟨false, 178038319740839123941287513524605891904171748084229809888449394403295487494⟩ ⟨false, 7122082970721276383995581824910344498982209460888453942198453434891299809332⟩ ⟨false, 246994704084049872402623348990234278271784097592587726356305438187737760190⟩ = true := by
  decide +kernel

theorem b_79_2400 : bothLoop evalE (oGrid.idx 79) (oGrid.dm 79) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 79) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7122082970721276383995581824910344498982209460888453942198453434891299809332⟩ ⟨false, 246994704084049872402623348990234278271784097592587726356305438187737760190⟩ = true := by
  decide +kernel

theorem o_row_79 : oGrid.row evalE 79 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_79_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_79_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_79_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_79_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_79_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_79_2000).1 (bothLoop_sound b_79_2400).1))))))

theorem n_row_79 : nGrid.row evalE 79 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_79_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_79_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_79_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_79_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_79_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_79_2000).2 (bothLoop_sound b_79_2400).2))))))

theorem b_80_0 : bothSeg evalE (oGrid.idx 80) (oGrid.dm 80) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 80) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3895332855693074370155164113234526739934140532190200316662587440531343787796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_80_400 : bothSeg evalE (oGrid.idx 80) (oGrid.dm 80) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 80) oGrid.kl oGrid.kr 400 400 ⟨false, 3895332855693074370155164113234526739934140532190200316662587440531343787796⟩ ⟨false, 0⟩ ⟨false, 6282293912818559116506044901642355745247697266317327208922863691022125613340⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_80_800 : bothSeg evalE (oGrid.idx 80) (oGrid.dm 80) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 80) oGrid.kl oGrid.kr 400 800 ⟨false, 6282293912818559116506044901642355745247697266317327208922863691022125613340⟩ ⟨false, 0⟩ ⟨false, 7180503256711413992365948905275382942623071802657923330734554104411615861648⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_80_1200 : bothSeg evalE (oGrid.idx 80) (oGrid.dm 80) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 80) oGrid.kl oGrid.kr 400 1200 ⟨false, 7180503256711413992365948905275382942623071802657923330734554104411615861648⟩ ⟨false, 0⟩ ⟨false, 7341497293328895863180350007664070983255808025620782464348561959569873610846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_80_1600 : bothSeg evalE (oGrid.idx 80) (oGrid.dm 80) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 80) oGrid.kl oGrid.kr 400 1600 ⟨false, 7341497293328895863180350007664070983255808025620782464348561959569873610846⟩ ⟨false, 0⟩ ⟨false, 7163564672215402686612148441598451565407994106825653503304107688704938609978⟩ ⟨false, 178226478341121501193529299370535550662538838474768105680843964374749136214⟩ = true := by
  decide +kernel

theorem b_80_2000 : bothSeg evalE (oGrid.idx 80) (oGrid.dm 80) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 80) oGrid.kl oGrid.kr 400 2000 ⟨false, 7163564672215402686612148441598451565407994106825653503304107688704938609978⟩ ⟨false, 178226478341121501193529299370535550662538838474768105680843964374749136214⟩ ⟨false, 7095686518204108062571231536386302313652568343538012800615355656702075854522⟩ ⟨false, 246776520208179283372528783774396049371508133222723046531573964367836256406⟩ = true := by
  decide +kernel

theorem b_80_2400 : bothLoop evalE (oGrid.idx 80) (oGrid.dm 80) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 80) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7095686518204108062571231536386302313652568343538012800615355656702075854522⟩ ⟨false, 246776520208179283372528783774396049371508133222723046531573964367836256406⟩ = true := by
  decide +kernel

theorem o_row_80 : oGrid.row evalE 80 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_80_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_80_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_80_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_80_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_80_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_80_2000).1 (bothLoop_sound b_80_2400).1))))))

theorem n_row_80 : nGrid.row evalE 80 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_80_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_80_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_80_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_80_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_80_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_80_2000).2 (bothLoop_sound b_80_2400).2))))))

theorem b_81_0 : bothSeg evalE (oGrid.idx 81) (oGrid.dm 81) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 81) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3881259044933368581065823539015412006970559685191216388175133335259945433320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_81_400 : bothSeg evalE (oGrid.idx 81) (oGrid.dm 81) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 81) oGrid.kl oGrid.kr 400 400 ⟨false, 3881259044933368581065823539015412006970559685191216388175133335259945433320⟩ ⟨false, 0⟩ ⟨false, 6259888939865577520276704705583387660599157752091923446342293288143436789532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_81_800 : bothSeg evalE (oGrid.idx 81) (oGrid.dm 81) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 81) oGrid.kl oGrid.kr 400 800 ⟨false, 6259888939865577520276704705583387660599157752091923446342293288143436789532⟩ ⟨false, 0⟩ ⟨false, 7154849376809649100849394311575248898343513096989915513319944000947709817366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_81_1200 : bothSeg evalE (oGrid.idx 81) (oGrid.dm 81) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 81) oGrid.kl oGrid.kr 400 1200 ⟨false, 7154849376809649100849394311575248898343513096989915513319944000947709817366⟩ ⟨false, 0⟩ ⟨false, 7314963495084570437930455326076584970353964742759698624327772262699405309898⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_81_1600 : bothSeg evalE (oGrid.idx 81) (oGrid.dm 81) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 81) oGrid.kl oGrid.kr 400 1600 ⟨false, 7314963495084570437930455326076584970353964742759698624327772262699405309898⟩ ⟨false, 0⟩ ⟨false, 7136832907157651123625565037567752674619063450321849595405905228927739776526⟩ ⟨false, 178413469135435316689670612008821329803047233739992119582258337638573957184⟩ = true := by
  decide +kernel

theorem b_81_2000 : bothSeg evalE (oGrid.idx 81) (oGrid.dm 81) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 81) oGrid.kl oGrid.kr 400 2000 ⟨false, 7136832907157651123625565037567752674619063450321849595405905228927739776526⟩ ⟨false, 178413469135435316689670612008821329803047233739992119582258337638573957184⟩ ⟨false, 7069360275016148293549553133403148638621822369080928441597689362079363879396⟩ ⟨false, 246559316766172404488163680013209051243132973383430664808038532248578165362⟩ = true := by
  decide +kernel

theorem b_81_2400 : bothLoop evalE (oGrid.idx 81) (oGrid.dm 81) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 81) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7069360275016148293549553133403148638621822369080928441597689362079363879396⟩ ⟨false, 246559316766172404488163680013209051243132973383430664808038532248578165362⟩ = true := by
  decide +kernel

theorem o_row_81 : oGrid.row evalE 81 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_81_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_81_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_81_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_81_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_81_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_81_2000).1 (bothLoop_sound b_81_2400).1))))))

theorem n_row_81 : nGrid.row evalE 81 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_81_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_81_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_81_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_81_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_81_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_81_2000).2 (bothLoop_sound b_81_2400).2))))))

theorem b_82_0 : bothSeg evalE (oGrid.idx 82) (oGrid.dm 82) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 82) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3867226842084193117933894072204750005397548151174152546960581949953289041504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_82_400 : bothSeg evalE (oGrid.idx 82) (oGrid.dm 82) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 82) oGrid.kl oGrid.kr 400 400 ⟨false, 3867226842084193117933894072204750005397548151174152546960581949953289041504⟩ ⟨false, 0⟩ ⟨false, 6237546243106582392149320594642038670147725748342552711212884664000924932690⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_82_800 : bothSeg evalE (oGrid.idx 82) (oGrid.dm 82) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 82) oGrid.kl oGrid.kr 400 800 ⟨false, 6237546243106582392149320594642038670147725748342552711212884664000924932690⟩ ⟨false, 0⟩ ⟨false, 7129264134210644454935669588769079118157454339088900994180692607555830009144⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_82_1200 : bothSeg evalE (oGrid.idx 82) (oGrid.dm 82) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 82) oGrid.kl oGrid.kr 400 1200 ⟨false, 7129264134210644454935669588769079118157454339088900994180692607555830009144⟩ ⟨false, 0⟩ ⟨false, 7288499359264233368727280410096793606882394641338494981088537146084006079980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_82_1600 : bothSeg evalE (oGrid.idx 82) (oGrid.dm 82) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 82) oGrid.kl oGrid.kr 400 1600 ⟨false, 7288499359264233368727280410096793606882394641338494981088537146084006079980⟩ ⟨false, 0⟩ ⟨false, 7110173795889577578650253612694958117641595799582869872964440917032851558506⟩ ⟨false, 178598787415817651973625584479368263819613815173950305147972976481747822712⟩ = true := by
  decide +kernel

theorem b_82_2000 : bothSeg evalE (oGrid.idx 82) (oGrid.dm 82) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 82) oGrid.kl oGrid.kr 400 2000 ⟨false, 7110173795889577578650253612694958117641595799582869872964440917032851558506⟩ ⟨false, 178598787415817651973625584479368263819613815173950305147972976481747822712⟩ ⟨false, 7043104329149751204404040630274929273048227213256510893600467116915080236572⟩ ⟨false, 246343035212745216942068387528271567059387874810791110056653989117448968088⟩ = true := by
  decide +kernel

theorem b_82_2400 : bothLoop evalE (oGrid.idx 82) (oGrid.dm 82) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 82) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7043104329149751204404040630274929273048227213256510893600467116915080236572⟩ ⟨false, 246343035212745216942068387528271567059387874810791110056653989117448968088⟩ = true := by
  decide +kernel

theorem o_row_82 : oGrid.row evalE 82 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_82_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_82_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_82_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_82_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_82_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_82_2000).1 (bothLoop_sound b_82_2400).1))))))

theorem n_row_82 : nGrid.row evalE 82 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_82_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_82_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_82_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_82_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_82_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_82_2000).2 (bothLoop_sound b_82_2400).2))))))

theorem b_83_0 : bothSeg evalE (oGrid.idx 83) (oGrid.dm 83) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 83) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3853236066102345822101992710125397762681513377506110388271473572489154338560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_83_400 : bothSeg evalE (oGrid.idx 83) (oGrid.dm 83) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 83) oGrid.kl oGrid.kr 400 400 ⟨false, 3853236066102345822101992710125397762681513377506110388271473572489154338560⟩ ⟨false, 0⟩ ⟨false, 6215265567951178514836842562538130160609898040511827560858209693640752530024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_83_800 : bothSeg evalE (oGrid.idx 83) (oGrid.dm 83) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 83) oGrid.kl oGrid.kr 400 800 ⟨false, 6215265567951178514836842562538130160609898040511827560858209693640752530024⟩ ⟨false, 0⟩ ⟨false, 7103747295229081918204928770697265339518186671586403027134509222976192756570⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_83_1200 : bothSeg evalE (oGrid.idx 83) (oGrid.dm 83) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 83) oGrid.kl oGrid.kr 400 1200 ⟨false, 7103747295229081918204928770697265339518186671586403027134509222976192756570⟩ ⟨false, 0⟩ ⟨false, 7262104590983078370450929918627585801122268668546014757787933562991463487028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_83_1600 : bothSeg evalE (oGrid.idx 83) (oGrid.dm 83) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 83) oGrid.kl oGrid.kr 400 1600 ⟨false, 7262104590983078370450929918627585801122268668546014757787933562991463487028⟩ ⟨false, 0⟩ ⟨false, 7083587055904579797541917733773486240867748618798928045618834728331795618824⟩ ⟨false, 178781978608147130723810629042530237156865671503233208187138315891532577344⟩ = true := by
  decide +kernel

theorem b_83_2000 : bothSeg evalE (oGrid.idx 83) (oGrid.dm 83) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 83) oGrid.kl oGrid.kr 400 2000 ⟨false, 7083587055904579797541917733773486240867748618798928045618834728331795618824⟩ ⟨false, 178781978608147130723810629042530237156865671503233208187138315891532577344⟩ ⟨false, 7016918396901628348480638840034506175402274723462081735263027173703943508086⟩ ⟨false, 246126737883305246697313745402471008663514074805800716096489923458294451546⟩ = true := by
  decide +kernel

theorem b_83_2400 : bothLoop evalE (oGrid.idx 83) (oGrid.dm 83) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 83) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 7016918396901628348480638840034506175402274723462081735263027173703943508086⟩ ⟨false, 246126737883305246697313745402471008663514074805800716096489923458294451546⟩ = true := by
  decide +kernel

theorem o_row_83 : oGrid.row evalE 83 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_83_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_83_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_83_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_83_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_83_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_83_2000).1 (bothLoop_sound b_83_2400).1))))))

theorem n_row_83 : nGrid.row evalE 83 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_83_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_83_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_83_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_83_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_83_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_83_2000).2 (bothLoop_sound b_83_2400).2))))))

theorem b_84_0 : bothSeg evalE (oGrid.idx 84) (oGrid.dm 84) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 84) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3839286650331428146373369855320676846213645566308663578087725949996009321618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_84_400 : bothSeg evalE (oGrid.idx 84) (oGrid.dm 84) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 84) oGrid.kl oGrid.kr 400 400 ⟨false, 3839286650331428146373369855320676846213645566308663578087725949996009321618⟩ ⟨false, 0⟩ ⟨false, 6193046952816044283637582852644527584594350073861675721444761457344531567808⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_84_800 : bothSeg evalE (oGrid.idx 84) (oGrid.dm 84) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 84) oGrid.kl oGrid.kr 400 800 ⟨false, 6193046952816044283637582852644527584594350073861675721444761457344531567808⟩ ⟨false, 0⟩ ⟨false, 7078298950377356976411392486122324146347344956987771958297200731836575536390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_84_1200 : bothSeg evalE (oGrid.idx 84) (oGrid.dm 84) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 84) oGrid.kl oGrid.kr 400 1200 ⟨false, 7078298950377356976411392486122324146347344956987771958297200731836575536390⟩ ⟨false, 0⟩ ⟨false, 7235779179100463262245982847525874499314845309684930600699009704087158836750⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_84_1600 : bothSeg evalE (oGrid.idx 84) (oGrid.dm 84) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 84) oGrid.kl oGrid.kr 400 1600 ⟨false, 7235779179100463262245982847525874499314845309684930600699009704087158836750⟩ ⟨false, 0⟩ ⟨false, 7057072539823108173646022226075973583249765454824902601905094728177364398682⟩ ⟨false, 178964054564568988721457807039601709280192688721353036896452465916440913936⟩ = true := by
  decide +kernel

theorem b_84_2000 : bothSeg evalE (oGrid.idx 84) (oGrid.dm 84) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 84) oGrid.kl oGrid.kr 400 2000 ⟨false, 7057072539823108173646022226075973583249765454824902601905094728177364398682⟩ ⟨false, 178964054564568988721457807039601709280192688721353036896452465916440913936⟩ ⟨false, 6990802349769960877525199205293960173930925142628813400227965691711021977984⟩ ⟨false, 245911912223689525115537779592942206569190046138208174267348601295797307650⟩ = true := by
  decide +kernel

theorem b_84_2400 : bothLoop evalE (oGrid.idx 84) (oGrid.dm 84) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 84) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6990802349769960877525199205293960173930925142628813400227965691711021977984⟩ ⟨false, 245911912223689525115537779592942206569190046138208174267348601295797307650⟩ = true := by
  decide +kernel

theorem o_row_84 : oGrid.row evalE 84 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_84_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_84_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_84_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_84_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_84_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_84_2000).1 (bothLoop_sound b_84_2400).1))))))

theorem n_row_84 : nGrid.row evalE 84 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_84_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_84_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_84_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_84_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_84_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_84_2000).2 (bothLoop_sound b_84_2400).2))))))

theorem b_85_0 : bothSeg evalE (oGrid.idx 85) (oGrid.dm 85) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 85) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3825378440215257687705667691263514966471318183170781946628861458965274118642⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_85_400 : bothSeg evalE (oGrid.idx 85) (oGrid.dm 85) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 85) oGrid.kl oGrid.kr 400 400 ⟨false, 3825378440215257687705667691263514966471318183170781946628861458965274118642⟩ ⟨false, 0⟩ ⟨false, 6170890054527533072844192315797012086575974941365834259067196642042902609276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_85_800 : bothSeg evalE (oGrid.idx 85) (oGrid.dm 85) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 85) oGrid.kl oGrid.kr 400 800 ⟨false, 6170890054527533072844192315797012086575974941365834259067196642042902609276⟩ ⟨false, 0⟩ ⟨false, 7052918694079597866705395020962092900462395571208694853792678714224351333010⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_85_1200 : bothSeg evalE (oGrid.idx 85) (oGrid.dm 85) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 85) oGrid.kl oGrid.kr 400 1200 ⟨false, 7052918694079597866705395020962092900462395571208694853792678714224351333010⟩ ⟨false, 0⟩ ⟨false, 7209522657669075817666372480631285193031786051957995884539286089484360465504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_85_1600 : bothSeg evalE (oGrid.idx 85) (oGrid.dm 85) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 85) oGrid.kl oGrid.kr 400 1600 ⟨false, 7209522657669075817666372480631285193031786051957995884539286089484360465504⟩ ⟨false, 0⟩ ⟨false, 7030630313652023779543973247660489908091174730320434177523577077549080916040⟩ ⟨false, 179145057131453272363492536716135089101985518628270135398227822557665016766⟩ = true := by
  decide +kernel

theorem b_85_2000 : bothSeg evalE (oGrid.idx 85) (oGrid.dm 85) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 85) oGrid.kl oGrid.kr 400 2000 ⟨false, 7030630313652023779543973247660489908091174730320434177523577077549080916040⟩ ⟨false, 179145057131453272363492536716135089101985518628270135398227822557665016766⟩ ⟨false, 6964756239248330255750344941495295076043068377838027344269472401063808759672⟩ ⟨false, 245698115546073491390786638074539860787176300682972736203226278617672317448⟩ = true := by
  decide +kernel

theorem b_85_2400 : bothLoop evalE (oGrid.idx 85) (oGrid.dm 85) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 85) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6964756239248330255750344941495295076043068377838027344269472401063808759672⟩ ⟨false, 245698115546073491390786638074539860787176300682972736203226278617672317448⟩ = true := by
  decide +kernel

theorem o_row_85 : oGrid.row evalE 85 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_85_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_85_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_85_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_85_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_85_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_85_2000).1 (bothLoop_sound b_85_2400).1))))))

theorem n_row_85 : nGrid.row evalE 85 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_85_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_85_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_85_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_85_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_85_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_85_2000).2 (bothLoop_sound b_85_2400).2))))))

theorem b_86_0 : bothSeg evalE (oGrid.idx 86) (oGrid.dm 86) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 86) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3811511435138214356757268258944322608907552146926965605499684052151996119530⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_86_400 : bothSeg evalE (oGrid.idx 86) (oGrid.dm 86) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 86) oGrid.kl oGrid.kr 400 400 ⟨false, 3811511435138214356757268258944322608907552146926965605499684052151996119530⟩ ⟨false, 0⟩ ⟨false, 6148794890863092998439346034417298900823998262986682393774561509827971581368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_86_800 : bothSeg evalE (oGrid.idx 86) (oGrid.dm 86) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 86) oGrid.kl oGrid.kr 400 800 ⟨false, 6148794890863092998439346034417298900823998262986682393774561509827971581368⟩ ⟨false, 0⟩ ⟨false, 7027606556313334027601523470305763194136849655999815254160135260613949207920⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_86_1200 : bothSeg evalE (oGrid.idx 86) (oGrid.dm 86) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 86) oGrid.kl oGrid.kr 400 1200 ⟨false, 7027606556313334027601523470305763194136849655999815254160135260613949207920⟩ ⟨false, 0⟩ ⟨false, 7183334925024194089009508630922084423514130433959644451970381109608622357182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_86_1600 : bothSeg evalE (oGrid.idx 86) (oGrid.dm 86) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 86) oGrid.kl oGrid.kr 400 1600 ⟨false, 7183334925024194089009508630922084423514130433959644451970381109608622357182⟩ ⟨false, 0⟩ ⟨false, 7004259794513142314778125676564443641026662269369399344484365149769171687134⟩ ⟨false, 179324326876879770016282046207491835574114890710508960903122961597943573686⟩ = true := by
  decide +kernel

theorem b_86_2000 : bothSeg evalE (oGrid.idx 86) (oGrid.dm 86) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 86) oGrid.kl oGrid.kr 400 2000 ⟨false, 7004259794513142314778125676564443641026662269369399344484365149769171687134⟩ ⟨false, 179324326876879770016282046207491835574114890710508960903122961597943573686⟩ ⟨false, 6938779494381533513919421233493723306855325830156018875357587905631951370466⟩ ⟨false, 245485177507390300054176501032324010287813061786554545613544508325279569784⟩ = true := by
  decide +kernel

theorem b_86_2400 : bothLoop evalE (oGrid.idx 86) (oGrid.dm 86) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 86) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6938779494381533513919421233493723306855325830156018875357587905631951370466⟩ ⟨false, 245485177507390300054176501032324010287813061786554545613544508325279569784⟩ = true := by
  decide +kernel

theorem o_row_86 : oGrid.row evalE 86 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_86_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_86_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_86_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_86_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_86_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_86_2000).1 (bothLoop_sound b_86_2400).1))))))

theorem n_row_86 : nGrid.row evalE 86 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_86_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_86_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_86_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_86_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_86_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_86_2000).2 (bothLoop_sound b_86_2400).2))))))

theorem b_87_0 : bothSeg evalE (oGrid.idx 87) (oGrid.dm 87) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 87) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3797685426106062075912064954846425393698611310363849635415736770697093329268⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_87_400 : bothSeg evalE (oGrid.idx 87) (oGrid.dm 87) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 87) oGrid.kl oGrid.kr 400 400 ⟨false, 3797685426106062075912064954846425393698611310363849635415736770697093329268⟩ ⟨false, 0⟩ ⟨false, 6126761221963945092309306928077318116001685809683320324914311937539078681372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_87_800 : bothSeg evalE (oGrid.idx 87) (oGrid.dm 87) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 87) oGrid.kl oGrid.kr 400 800 ⟨false, 6126761221963945092309306928077318116001685809683320324914311937539078681372⟩ ⟨false, 0⟩ ⟨false, 7002362348367012229671836763811324240120644564618496177283006627374374035994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_87_1200 : bothSeg evalE (oGrid.idx 87) (oGrid.dm 87) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 87) oGrid.kl oGrid.kr 400 1200 ⟨false, 7002362348367012229671836763811324240120644564618496177283006627374374035994⟩ ⟨false, 0⟩ ⟨false, 7157215765672176187438609513514138470317248750851752539716721643240168882760⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_87_1600 : bothSeg evalE (oGrid.idx 87) (oGrid.dm 87) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 87) oGrid.kl oGrid.kr 400 1600 ⟨false, 7157215765672176187438609513514138470317248750851752539716721643240168882760⟩ ⟨false, 0⟩ ⟨false, 6977961189626903521143600277813904305518413782796440081057162415522388016854⟩ ⟨false, 179501887875129008734698412160890517112161007049079260701561932431401618612⟩ = true := by
  decide +kernel

theorem b_87_2000 : bothSeg evalE (oGrid.idx 87) (oGrid.dm 87) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 87) oGrid.kl oGrid.kr 400 2000 ⟨false, 6977961189626903521143600277813904305518413782796440081057162415522388016854⟩ ⟨false, 179501887875129008734698412160890517112161007049079260701561932431401618612⟩ ⟨false, 6912872316057406690778269202337554628200640981673549479906962759038728261704⟩ ⟨false, 245272689445609323821701391011065822602390380544761644958667758238902088880⟩ = true := by
  decide +kernel

theorem b_87_2400 : bothLoop evalE (oGrid.idx 87) (oGrid.dm 87) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 87) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6912872316057406690778269202337554628200640981673549479906962759038728261704⟩ ⟨false, 245272689445609323821701391011065822602390380544761644958667758238902088880⟩ = true := by
  decide +kernel

theorem o_row_87 : oGrid.row evalE 87 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_87_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_87_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_87_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_87_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_87_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_87_2000).1 (bothLoop_sound b_87_2400).1))))))

theorem n_row_87 : nGrid.row evalE 87 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_87_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_87_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_87_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_87_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_87_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_87_2000).2 (bothLoop_sound b_87_2400).2))))))

theorem b_88_0 : bothSeg evalE (oGrid.idx 88) (oGrid.dm 88) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 88) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3783900370009118567428267370310243235941115911622958747012415775972005051676⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_88_400 : bothSeg evalE (oGrid.idx 88) (oGrid.dm 88) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 88) oGrid.kl oGrid.kr 400 400 ⟨false, 3783900370009118567428267370310243235941115911622958747012415775972005051676⟩ ⟨false, 0⟩ ⟨false, 6104788963212910210335566557296107323467217789126364200658727107087121481714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_88_800 : bothSeg evalE (oGrid.idx 88) (oGrid.dm 88) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 88) oGrid.kl oGrid.kr 400 800 ⟨false, 6104788963212910210335566557296107323467217789126364200658727107087121481714⟩ ⟨false, 0⟩ ⟨false, 6977185928327110323234234224925164083862311248438282377162331977215976806742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_88_1200 : bothSeg evalE (oGrid.idx 88) (oGrid.dm 88) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 88) oGrid.kl oGrid.kr 400 1200 ⟨false, 6977185928327110323234234224925164083862311248438282377162331977215976806742⟩ ⟨false, 0⟩ ⟨false, 7131164851603083637554999112737625683807157575853733979390131986354391052928⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_88_1600 : bothSeg evalE (oGrid.idx 88) (oGrid.dm 88) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 88) oGrid.kl oGrid.kr 400 1600 ⟨false, 7131164851603083637554999112737625683807157575853733979390131986354391052928⟩ ⟨false, 0⟩ ⟨false, 6951734256880613174487165201723032171279617903426778928970702872294493124454⟩ ⟨false, 179677990996900965473060928072521793663419492429604701419195724457613404140⟩ = true := by
  decide +kernel

theorem b_88_2000 : bothSeg evalE (oGrid.idx 88) (oGrid.dm 88) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 88) oGrid.kl oGrid.kr 400 2000 ⟨false, 6951734256880613174487165201723032171279617903426778928970702872294493124454⟩ ⟨false, 179677990996900965473060928072521793663419492429604701419195724457613404140⟩ ⟨false, 6887034466279913861955156782941682886946844209546526082930047907553489771368⟩ ⟨false, 245061211683485197108284403175986193492166877071619491942924778625233548534⟩ = true := by
  decide +kernel

theorem b_88_2400 : bothLoop evalE (oGrid.idx 88) (oGrid.dm 88) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 88) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6887034466279913861955156782941682886946844209546526082930047907553489771368⟩ ⟨false, 245061211683485197108284403175986193492166877071619491942924778625233548534⟩ = true := by
  decide +kernel

theorem o_row_88 : oGrid.row evalE 88 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_88_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_88_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_88_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_88_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_88_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_88_2000).1 (bothLoop_sound b_88_2400).1))))))

theorem n_row_88 : nGrid.row evalE 88 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_88_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_88_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_88_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_88_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_88_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_88_2000).2 (bothLoop_sound b_88_2400).2))))))

theorem b_89_0 : bothSeg evalE (oGrid.idx 89) (oGrid.dm 89) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 89) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3770156084361441181502352717384316475465049053114726792370723826604115982688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_89_400 : bothSeg evalE (oGrid.idx 89) (oGrid.dm 89) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 89) oGrid.kl oGrid.kr 400 400 ⟨false, 3770156084361441181502352717384316475465049053114726792370723826604115982688⟩ ⟨false, 0⟩ ⟨false, 6082877995152597496639074370982079482453998629711009523342292179754063047594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_89_800 : bothSeg evalE (oGrid.idx 89) (oGrid.dm 89) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 89) oGrid.kl oGrid.kr 400 800 ⟨false, 6082877995152597496639074370982079482453998629711009523342292179754063047594⟩ ⟨false, 0⟩ ⟨false, 6952077188181995036512999814599193860097550934774758940569995993150835402234⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_89_1200 : bothSeg evalE (oGrid.idx 89) (oGrid.dm 89) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 89) oGrid.kl oGrid.kr 400 1200 ⟨false, 6952077188181995036512999814599193860097550934774758940569995993150835402234⟩ ⟨false, 0⟩ ⟨false, 7105182053725585866896172229228406790131433599545574422926199728039140371016⟩ ⟨false, 1807330491739235023295177249848004793175595198852880358425723307521660⟩ = true := by
  decide +kernel

theorem b_89_1600 : bothSeg evalE (oGrid.idx 89) (oGrid.dm 89) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 89) oGrid.kl oGrid.kr 400 1600 ⟨false, 7105182053725585866896172229228406790131433599545574422926199728039140371016⟩ ⟨false, 1807330491739235023295177249848004793175595198852880358425723307521660⟩ ⟨false, 6925578877562517058860513261922639239867009143844077556511254927602620553504⟩ ⟨false, 179853322120115122465950251650961563976416741978398091858981611691551711776⟩ = true := by
  decide +kernel

theorem b_89_2000 : bothSeg evalE (oGrid.idx 89) (oGrid.dm 89) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 89) oGrid.kl oGrid.kr 400 2000 ⟨false, 6925578877562517058860513261922639239867009143844077556511254927602620553504⟩ ⟨false, 179853322120115122465950251650961563976416741978398091858981611691551711776⟩ ⟨false, 6861265831394116352984053935965307046673680822635546214219810661187696354076⟩ ⟨false, 244851249699418061693605203463728175948146182067905966479439281680922866068⟩ = true := by
  decide +kernel

theorem b_89_2400 : bothLoop evalE (oGrid.idx 89) (oGrid.dm 89) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 89) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6861265831394116352984053935965307046673680822635546214219810661187696354076⟩ ⟨false, 244851249699418061693605203463728175948146182067905966479439281680922866068⟩ = true := by
  decide +kernel

theorem o_row_89 : oGrid.row evalE 89 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_89_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_89_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_89_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_89_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_89_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_89_2000).1 (bothLoop_sound b_89_2400).1))))))

theorem n_row_89 : nGrid.row evalE 89 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_89_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_89_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_89_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_89_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_89_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_89_2000).2 (bothLoop_sound b_89_2400).2))))))

theorem b_90_0 : bothSeg evalE (oGrid.idx 90) (oGrid.dm 90) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 90) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3756452490920997594715009656460869119780752018025064858367437235607506390710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_90_400 : bothSeg evalE (oGrid.idx 90) (oGrid.dm 90) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 90) oGrid.kl oGrid.kr 400 400 ⟨false, 3756452490920997594715009656460869119780752018025064858367437235607506390710⟩ ⟨false, 0⟩ ⟨false, 6061028074887919832283236934168074573516990198288527085239767290817232094296⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_90_800 : bothSeg evalE (oGrid.idx 90) (oGrid.dm 90) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 90) oGrid.kl oGrid.kr 400 800 ⟨false, 6061028074887919832283236934168074573516990198288527085239767290817232094296⟩ ⟨false, 0⟩ ⟨false, 6927035932684040245707250709067160708701378759029084180154596269897086046732⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_90_1200 : bothSeg evalE (oGrid.idx 90) (oGrid.dm 90) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 90) oGrid.kl oGrid.kr 400 1200 ⟨false, 6927035932684040245707250709067160708701378759029084180154596269897086046732⟩ ⟨false, 0⟩ ⟨false, 7079267060906945431541793686854161720738789580742823190420336795419800552194⟩ ⟨false, 5680936240026165077921504841973480353879820177144334895866027926313400⟩ = true := by
  decide +kernel

theorem b_90_1600 : bothSeg evalE (oGrid.idx 90) (oGrid.dm 90) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 90) oGrid.kl oGrid.kr 400 1600 ⟨false, 7079267060906945431541793686854161720738789580742823190420336795419800552194⟩ ⟨false, 5680936240026165077921504841973480353879820177144334895866027926313400⟩ ⟨false, 6899494548259437175265131613391380396481479511021593384589513230523269251962⟩ ⟨false, 180027512265702606428526120724160316352729344380850256065483793843513325272⟩ = true := by
  decide +kernel

theorem b_90_2000 : bothSeg evalE (oGrid.idx 90) (oGrid.dm 90) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 90) oGrid.kl oGrid.kr 400 2000 ⟨false, 6899494548259437175265131613391380396481479511021593384589513230523269251962⟩ ⟨false, 180027512265702606428526120724160316352729344380850256065483793843513325272⟩ ⟨false, 6835565920059394582014691862255371633328628085807306478442313818453143426306⟩ ⟨false, 244642437123122841738075969874235398936195746632690748570737541361474241522⟩ = true := by
  decide +kernel

theorem b_90_2400 : bothLoop evalE (oGrid.idx 90) (oGrid.dm 90) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 90) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6835565920059394582014691862255371633328628085807306478442313818453143426306⟩ ⟨false, 244642437123122841738075969874235398936195746632690748570737541361474241522⟩ = true := by
  decide +kernel

theorem o_row_90 : oGrid.row evalE 90 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_90_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_90_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_90_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_90_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_90_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_90_2000).1 (bothLoop_sound b_90_2400).1))))))

theorem n_row_90 : nGrid.row evalE 90 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_90_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_90_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_90_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_90_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_90_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_90_2000).2 (bothLoop_sound b_90_2400).2))))))

theorem b_91_0 : bothSeg evalE (oGrid.idx 91) (oGrid.dm 91) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 91) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3742789482307741714137595358007379955175054366479290357346879014903096318762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_91_400 : bothSeg evalE (oGrid.idx 91) (oGrid.dm 91) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 91) oGrid.kl oGrid.kr 400 400 ⟨false, 3742789482307741714137595358007379955175054366479290357346879014903096318762⟩ ⟨false, 0⟩ ⟨false, 6039239086748317759544184648092307029767348532147311564135043445127663043780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_91_800 : bothSeg evalE (oGrid.idx 91) (oGrid.dm 91) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 91) oGrid.kl oGrid.kr 400 800 ⟨false, 6039239086748317759544184648092307029767348532147311564135043445127663043780⟩ ⟨false, 0⟩ ⟨false, 6902061999521742214155416954799690956460790985795969637831998518278380036962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_91_1200 : bothSeg evalE (oGrid.idx 91) (oGrid.dm 91) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 91) oGrid.kl oGrid.kr 400 1200 ⟨false, 6902061999521742214155416954799690956460790985795969637831998518278380036962⟩ ⟨false, 0⟩ ⟨false, 7053419573190835273210248326016639376626841753347836265450410363279009330230⟩ ⟨false, 11725636611907939398448382833738815689238532771790620305661196654454474⟩ = true := by
  decide +kernel

theorem b_91_1600 : bothSeg evalE (oGrid.idx 91) (oGrid.dm 91) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 91) oGrid.kl oGrid.kr 400 1600 ⟨false, 7053419573190835273210248326016639376626841753347836265450410363279009330230⟩ ⟨false, 11725636611907939398448382833738815689238532771790620305661196654454474⟩ ⟨false, 6873481687042362788157850772305110325881441645875535787279440146382522453966⟩ ⟨false, 180199469054734486548479848343362245152078221071656369422541868723572389268⟩ = true := by
  decide +kernel

theorem b_91_2000 : bothSeg evalE (oGrid.idx 91) (oGrid.dm 91) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 91) oGrid.kl oGrid.kr 400 2000 ⟨false, 6873481687042362788157850772305110325881441645875535787279440146382522453966⟩ ⟨false, 180199469054734486548479848343362245152078221071656369422541868723572389268⟩ ⟨false, 6809935155330668185694593459468033683032053840011623763230382963828444346082⟩ ⟨false, 244433823615930353297805747982941281984725442525003905706126625567274354262⟩ = true := by
  decide +kernel

theorem b_91_2400 : bothLoop evalE (oGrid.idx 91) (oGrid.dm 91) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 91) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6809935155330668185694593459468033683032053840011623763230382963828444346082⟩ ⟨false, 244433823615930353297805747982941281984725442525003905706126625567274354262⟩ = true := by
  decide +kernel

theorem o_row_91 : oGrid.row evalE 91 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_91_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_91_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_91_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_91_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_91_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_91_2000).1 (bothLoop_sound b_91_2400).1))))))

theorem n_row_91 : nGrid.row evalE 91 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_91_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_91_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_91_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_91_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_91_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_91_2000).2 (bothLoop_sound b_91_2400).2))))))

theorem b_92_0 : bothSeg evalE (oGrid.idx 92) (oGrid.dm 92) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 92) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3729166920514258534599676684106057913418926670789649610127180678820818648792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_92_400 : bothSeg evalE (oGrid.idx 92) (oGrid.dm 92) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 92) oGrid.kl oGrid.kr 400 400 ⟨false, 3729166920514258534599676684106057913418926670789649610127180678820818648792⟩ ⟨false, 0⟩ ⟨false, 6017510896292853289161625954815490738307259824593143830694737389020235039932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_92_800 : bothSeg evalE (oGrid.idx 92) (oGrid.dm 92) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 92) oGrid.kl oGrid.kr 400 800 ⟨false, 6017510896292853289161625954815490738307259824593143830694737389020235039932⟩ ⟨false, 0⟩ ⟨false, 6877155258803754447398432395284013233773225634634104412070424788885960558266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_92_1200 : bothSeg evalE (oGrid.idx 92) (oGrid.dm 92) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 92) oGrid.kl oGrid.kr 400 1200 ⟨false, 6877155258803754447398432395284013233773225634634104412070424788885960558266⟩ ⟨false, 0⟩ ⟨false, 7027639388474439092304952549115606265149650042971606586619621678493945736246⟩ ⟨false, 20071524629745849184727723266101094872703426226481587493827412801815296⟩ = true := by
  decide +kernel

theorem b_92_1600 : bothSeg evalE (oGrid.idx 92) (oGrid.dm 92) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 92) oGrid.kl oGrid.kr 400 1600 ⟨false, 7027639388474439092304952549115606265149650042971606586619621678493945736246⟩ ⟨false, 20071524629745849184727723266101094872703426226481587493827412801815296⟩ ⟨false, 6847540034439238812569210601351469952789215258186956998883931239280517576476⟩ ⟨false, 180369607555237394301224664715514266635990528088810611942462492942796831226⟩ = true := by
  decide +kernel

theorem b_92_2000 : bothSeg evalE (oGrid.idx 92) (oGrid.dm 92) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 92) oGrid.kl oGrid.kr 400 2000 ⟨false, 6847540034439238812569210601351469952789215258186956998883931239280517576476⟩ ⟨false, 180369607555237394301224664715514266635990528088810611942462492942796831226⟩ ⟨false, 6784373250247916805297882911702260835963663906233301538845092033313316485108⟩ ⟨false, 244225598370604420294511738813060728082339460665839273063542887866817585670⟩ = true := by
  decide +kernel

theorem b_92_2400 : bothLoop evalE (oGrid.idx 92) (oGrid.dm 92) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 92) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6784373250247916805297882911702260835963663906233301538845092033313316485108⟩ ⟨false, 244225598370604420294511738813060728082339460665839273063542887866817585670⟩ = true := by
  decide +kernel

theorem o_row_92 : oGrid.row evalE 92 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_92_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_92_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_92_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_92_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_92_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_92_2000).1 (bothLoop_sound b_92_2400).1))))))

theorem n_row_92 : nGrid.row evalE 92 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_92_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_92_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_92_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_92_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_92_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_92_2000).2 (bothLoop_sound b_92_2400).2))))))

theorem b_93_0 : bothSeg evalE (oGrid.idx 93) (oGrid.dm 93) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 93) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3715584713548407032232879327305338947499270494322994700036248243145510505070⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_93_400 : bothSeg evalE (oGrid.idx 93) (oGrid.dm 93) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 93) oGrid.kl oGrid.kr 400 400 ⟨false, 3715584713548407032232879327305338947499270494322994700036248243145510505070⟩ ⟨false, 0⟩ ⟨false, 5995843381001758804185183465505520710839923923735564631280630522640769030086⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_93_800 : bothSeg evalE (oGrid.idx 93) (oGrid.dm 93) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 93) oGrid.kl oGrid.kr 400 800 ⟨false, 5995843381001758804185183465505520710839923923735564631280630522640769030086⟩ ⟨false, 0⟩ ⟨false, 6852315613616733032123506021208985464538753553695673549814274947859389444248⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_93_1200 : bothSeg evalE (oGrid.idx 93) (oGrid.dm 93) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 93) oGrid.kl oGrid.kr 400 1200 ⟨false, 6852315613616733032123506021208985464538753553695673549814274947859389444248⟩ ⟨false, 0⟩ ⟨false, 7001926248226534437698750950215357838740644358498244466522959878939305348526⟩ ⟨false, 30840987648797294806251409608253675678873559771098223770398766306039988⟩ = true := by
  decide +kernel

theorem b_93_1600 : bothSeg evalE (oGrid.idx 93) (oGrid.dm 93) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 93) oGrid.kl oGrid.kr 400 1600 ⟨false, 7001926248226534437698750950215357838740644358498244466522959878939305348526⟩ ⟨false, 30840987648797294806251409608253675678873559771098223770398766306039988⟩ ⟨false, 6821669101791672656725374815817656374807601892687951931181882689192583109226⟩ ⟨false, 180538888256935145193574692420235014312214275086855496216386801752911116932⟩ = true := by
  decide +kernel

theorem b_93_2000 : bothSeg evalE (oGrid.idx 93) (oGrid.dm 93) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 93) oGrid.kl oGrid.kr 400 2000 ⟨false, 6821669101791672656725374815817656374807601892687951931181882689192583109226⟩ ⟨false, 180538888256935145193574692420235014312214275086855496216386801752911116932⟩ ⟨false, 6758879764334319415884825665408901048866140386072365954674833672221213534388⟩ ⟨false, 244018987300939792811521551010532705949624259087090189122342197833181057696⟩ = true := by
  decide +kernel

theorem b_93_2400 : bothLoop evalE (oGrid.idx 93) (oGrid.dm 93) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 93) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6758879764334319415884825665408901048866140386072365954674833672221213534388⟩ ⟨false, 244018987300939792811521551010532705949624259087090189122342197833181057696⟩ = true := by
  decide +kernel

theorem o_row_93 : oGrid.row evalE 93 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_93_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_93_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_93_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_93_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_93_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_93_2000).1 (bothLoop_sound b_93_2400).1))))))

theorem n_row_93 : nGrid.row evalE 93 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_93_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_93_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_93_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_93_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_93_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_93_2000).2 (bothLoop_sound b_93_2400).2))))))

theorem b_94_0 : bothSeg evalE (oGrid.idx 94) (oGrid.dm 94) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 94) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3702042792135451539327756092376019927052103847892608726464419026171455695650⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_94_400 : bothSeg evalE (oGrid.idx 94) (oGrid.dm 94) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 94) oGrid.kl oGrid.kr 400 400 ⟨false, 3702042792135451539327756092376019927052103847892608726464419026171455695650⟩ ⟨false, 0⟩ ⟨false, 5974236457933921391376505921658199816284289433892468317690123761360783834062⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_94_800 : bothSeg evalE (oGrid.idx 94) (oGrid.dm 94) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 94) oGrid.kl oGrid.kr 400 800 ⟨false, 5974236457933921391376505921658199816284289433892468317690123761360783834062⟩ ⟨false, 0⟩ ⟨false, 6827542974607858309554612548282591288612156740592979554998122738858727422724⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_94_1200 : bothSeg evalE (oGrid.idx 94) (oGrid.dm 94) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 94) oGrid.kl oGrid.kr 400 1200 ⟨false, 6827542974607858309554612548282591288612156740592979554998122738858727422724⟩ ⟨false, 0⟩ ⟨false, 6976280019938476194199829824400855544522502867499406092808044788622352382876⟩ ⟨false, 44523280928507507339838591578376604272764777524867658167056483934612710⟩ = true := by
  decide +kernel

theorem b_94_1600 : bothSeg evalE (oGrid.idx 94) (oGrid.dm 94) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 94) oGrid.kl oGrid.kr 400 1600 ⟨false, 6976280019938476194199829824400855544522502867499406092808044788622352382876⟩ ⟨false, 44523280928507507339838591578376604272764777524867658167056483934612710⟩ ⟨false, 6795869244379258424451725520724936047098874219181365144989856531995635159998⟩ ⟨false, 180707012556928479524681881426642687281955834983508445935042029229255408554⟩ = true := by
  decide +kernel

theorem b_94_2000 : bothSeg evalE (oGrid.idx 94) (oGrid.dm 94) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 94) oGrid.kl oGrid.kr 400 2000 ⟨false, 6795869244379258424451725520724936047098874219181365144989856531995635159998⟩ ⟨false, 180707012556928479524681881426642687281955834983508445935042029229255408554⟩ ⟨false, 6733455024388671186095671847276808584440412281753982727665825653005648334502⟩ ⟨false, 243813371608104374233332863116358379229021752495619528338104581886111422400⟩ = true := by
  decide +kernel

theorem b_94_2400 : bothLoop evalE (oGrid.idx 94) (oGrid.dm 94) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 94) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6733455024388671186095671847276808584440412281753982727665825653005648334502⟩ ⟨false, 243813371608104374233332863116358379229021752495619528338104581886111422400⟩ = true := by
  decide +kernel

theorem o_row_94 : oGrid.row evalE 94 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_94_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_94_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_94_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_94_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_94_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_94_2000).1 (bothLoop_sound b_94_2400).1))))))

theorem n_row_94 : nGrid.row evalE 94 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_94_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_94_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_94_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_94_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_94_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_94_2000).2 (bothLoop_sound b_94_2400).2))))))

theorem b_95_0 : bothSeg evalE (oGrid.idx 95) (oGrid.dm 95) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 95) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 3688541030090308395475385791400052066702388427629781960844958322374762847202⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_95_400 : bothSeg evalE (oGrid.idx 95) (oGrid.dm 95) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 95) oGrid.kl oGrid.kr 400 400 ⟨false, 3688541030090308395475385791400052066702388427629781960844958322374762847202⟩ ⟨false, 0⟩ ⟨false, 5952689905840421593426510920190106540348523942517023662668645318675337781072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_95_800 : bothSeg evalE (oGrid.idx 95) (oGrid.dm 95) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 95) oGrid.kl oGrid.kr 400 800 ⟨false, 5952689905840421593426510920190106540348523942517023662668645318675337781072⟩ ⟨false, 0⟩ ⟨false, 6802837099710659861473418696162769250696345092445208172348257383626044593610⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_95_1200 : bothSeg evalE (oGrid.idx 95) (oGrid.dm 95) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 95) oGrid.kl oGrid.kr 400 1200 ⟨false, 6802837099710659861473418696162769250696345092445208172348257383626044593610⟩ ⟨false, 0⟩ ⟨false, 6950700260808623684044758877652204511411275154809945979468664378279927806850⟩ ⟨false, 60869262527409762125268999056770165978192302268205107541742092732710122⟩ = true := by
  decide +kernel

theorem b_95_1600 : bothSeg evalE (oGrid.idx 95) (oGrid.dm 95) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 95) oGrid.kl oGrid.kr 400 1600 ⟨false, 6950700260808623684044758877652204511411275154809945979468664378279927806850⟩ ⟨false, 60869262527409762125268999056770165978192302268205107541742092732710122⟩ ⟨false, 6770139831560157644356871063699634398870215082653052978712376883672272130048⟩ ⟨false, 180873809861718836112196524208259408914374948465663431475674918689303642264⟩ = true := by
  decide +kernel

theorem b_95_2000 : bothSeg evalE (oGrid.idx 95) (oGrid.dm 95) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 95) oGrid.kl oGrid.kr 400 2000 ⟨false, 6770139831560157644356871063699634398870215082653052978712376883672272130048⟩ ⟨false, 180873809861718836112196524208259408914374948465663431475674918689303642264⟩ ⟨false, 6708098416455887217750981984770417364007863227095169946707187688368232814120⟩ ⟨false, 243608915569659815339769080867357812225726290211230362981884894877684867806⟩ = true := by
  decide +kernel

theorem b_95_2400 : bothLoop evalE (oGrid.idx 95) (oGrid.dm 95) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 95) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 6708098416455887217750981984770417364007863227095169946707187688368232814120⟩ ⟨false, 243608915569659815339769080867357812225726290211230362981884894877684867806⟩ = true := by
  decide +kernel

theorem o_row_95 : oGrid.row evalE 95 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_95_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_95_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_95_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_95_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_95_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_95_2000).1 (bothLoop_sound b_95_2400).1))))))

theorem n_row_95 : nGrid.row evalE 95 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_95_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_95_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_95_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_95_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_95_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_95_2000).2 (bothLoop_sound b_95_2400).2))))))

theorem o_blk_72 : allFrom (fun j => oGrid.row evalE j) 72 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 72) o_row_72 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 73) o_row_73 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 74) o_row_74 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 75) o_row_75 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 76) o_row_76 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 77) o_row_77 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 78) o_row_78 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 79) o_row_79 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 80) o_row_80 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 81) o_row_81 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 82) o_row_82 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 83) o_row_83 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 84) o_row_84 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 85) o_row_85 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 86) o_row_86 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 87) o_row_87 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 88) o_row_88 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 89) o_row_89 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 90) o_row_90 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 91) o_row_91 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 92) o_row_92 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 93) o_row_93 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 94) o_row_94 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 95) o_row_95 (allFrom_zero (fun j => oGrid.row evalE j) 96)))))))))))))))))))))))))

theorem n_blk_72 : allFrom (fun j => nGrid.row evalE j) 72 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 72) n_row_72 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 73) n_row_73 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 74) n_row_74 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 75) n_row_75 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 76) n_row_76 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 77) n_row_77 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 78) n_row_78 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 79) n_row_79 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 80) n_row_80 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 81) n_row_81 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 82) n_row_82 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 83) n_row_83 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 84) n_row_84 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 85) n_row_85 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 86) n_row_86 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 87) n_row_87 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 88) n_row_88 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 89) n_row_89 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 90) n_row_90 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 91) n_row_91 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 92) n_row_92 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 93) n_row_93 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 94) n_row_94 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 95) n_row_95 (allFrom_zero (fun j => nGrid.row evalE j) 96)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
