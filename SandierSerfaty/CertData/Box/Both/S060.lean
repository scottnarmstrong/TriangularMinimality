/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 60 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1440`–`1463`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1440_0 : bothSeg evalE (oGrid.idx 1440) (oGrid.dm 1440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1440) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 32404822396895028697821897304990852739345936921364487501548692953485740448⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1440_400 : bothSeg evalE (oGrid.idx 1440) (oGrid.dm 1440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1440) oGrid.kl oGrid.kr 400 400 ⟨false, 32404822396895028697821897304990852739345936921364487501548692953485740448⟩ ⟨false, 0⟩ ⟨false, 88581027171824758785269729923237380628130828183792413853982327416643661776⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1440_800 : bothSeg evalE (oGrid.idx 1440) (oGrid.dm 1440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1440) oGrid.kl oGrid.kr 400 800 ⟨false, 88581027171824758785269729923237380628130828183792413853982327416643661776⟩ ⟨false, 0⟩ ⟨false, 149233290572065904142337052288017516404194997984492408921567387836932418880⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1440_1200 : bothSeg evalE (oGrid.idx 1440) (oGrid.dm 1440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1440) oGrid.kl oGrid.kr 400 1200 ⟨false, 149233290572065904142337052288017516404194997984492408921567387836932418880⟩ ⟨false, 0⟩ ⟨false, 239285266318551977863941295832858575306130482558623327005913202065347760146⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1440_1600 : bothSeg evalE (oGrid.idx 1440) (oGrid.dm 1440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1440) oGrid.kl oGrid.kr 400 1600 ⟨false, 239285266318551977863941295832858575306130482558623327005913202065347760146⟩ ⟨false, 0⟩ ⟨false, 382561978118526508826790485692647443307281962563275383296345710636502600696⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1440_2000 : bothSeg evalE (oGrid.idx 1440) (oGrid.dm 1440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1440) oGrid.kl oGrid.kr 400 2000 ⟨false, 382561978118526508826790485692647443307281962563275383296345710636502600696⟩ ⟨false, 0⟩ ⟨false, 576813596141613949426814996130079556804387129086080240199214044154367700930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1440_2400 : bothLoop evalE (oGrid.idx 1440) (oGrid.dm 1440) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1440) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 576813596141613949426814996130079556804387129086080240199214044154367700930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1440 : oGrid.row evalE 1440 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1440_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1440_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1440_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1440_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1440_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1440_2000).1 (bothLoop_sound b_1440_2400).1))))))

theorem n_row_1440 : nGrid.row evalE 1440 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1440_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1440_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1440_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1440_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1440_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1440_2000).2 (bothLoop_sound b_1440_2400).2))))))

theorem b_1441_0 : bothSeg evalE (oGrid.idx 1441) (oGrid.dm 1441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1441) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 32837016155277915820527999871242837362152935121810111576171061032914365774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1441_400 : bothSeg evalE (oGrid.idx 1441) (oGrid.dm 1441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1441) oGrid.kl oGrid.kr 400 400 ⟨false, 32837016155277915820527999871242837362152935121810111576171061032914365774⟩ ⟨false, 0⟩ ⟨false, 89466865136797832729282578948595301179703636057662881171671952421260749754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1441_800 : bothSeg evalE (oGrid.idx 1441) (oGrid.dm 1441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1441) oGrid.kl oGrid.kr 400 800 ⟨false, 89466865136797832729282578948595301179703636057662881171671952421260749754⟩ ⟨false, 0⟩ ⟨false, 150073752695784812309924060135557403662116978916811456992506274156407804250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1441_1200 : bothSeg evalE (oGrid.idx 1441) (oGrid.dm 1441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1441) oGrid.kl oGrid.kr 400 1200 ⟨false, 150073752695784812309924060135557403662116978916811456992506274156407804250⟩ ⟨false, 0⟩ ⟨false, 240433525771524739616166370782199294266845594846972068753370291458875042594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1441_1600 : bothSeg evalE (oGrid.idx 1441) (oGrid.dm 1441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1441) oGrid.kl oGrid.kr 400 1600 ⟨false, 240433525771524739616166370782199294266845594846972068753370291458875042594⟩ ⟨false, 0⟩ ⟨false, 383977505316529478272520323288620537142926103159885735858883721705047442330⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1441_2000 : bothSeg evalE (oGrid.idx 1441) (oGrid.dm 1441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1441) oGrid.kl oGrid.kr 400 2000 ⟨false, 383977505316529478272520323288620537142926103159885735858883721705047442330⟩ ⟨false, 0⟩ ⟨false, 578464658288162572767825205216660563478767723133314943273282923122738259954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1441_2400 : bothLoop evalE (oGrid.idx 1441) (oGrid.dm 1441) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1441) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 578464658288162572767825205216660563478767723133314943273282923122738259954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1441 : oGrid.row evalE 1441 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1441_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1441_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1441_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1441_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1441_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1441_2000).1 (bothLoop_sound b_1441_2400).1))))))

theorem n_row_1441 : nGrid.row evalE 1441 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1441_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1441_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1441_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1441_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1441_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1441_2000).2 (bothLoop_sound b_1441_2400).2))))))

theorem b_1442_0 : bothSeg evalE (oGrid.idx 1442) (oGrid.dm 1442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1442) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 33270072319531875848440280282756678620595052453879306606848553464693247788⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1442_400 : bothSeg evalE (oGrid.idx 1442) (oGrid.dm 1442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1442) oGrid.kl oGrid.kr 400 400 ⟨false, 33270072319531875848440280282756678620595052453879306606848553464693247788⟩ ⟨false, 0⟩ ⟨false, 90350825582973059578643935021294118206777630553180169064353575326191998844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1442_800 : bothSeg evalE (oGrid.idx 1442) (oGrid.dm 1442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1442) oGrid.kl oGrid.kr 400 800 ⟨false, 90350825582973059578643935021294118206777630553180169064353575326191998844⟩ ⟨false, 0⟩ ⟨false, 150913054056069344268798877028664749473070340086957588649685983800678558752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1442_1200 : bothSeg evalE (oGrid.idx 1442) (oGrid.dm 1442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1442) oGrid.kl oGrid.kr 400 1200 ⟨false, 150913054056069344268798877028664749473070340086957588649685983800678558752⟩ ⟨false, 0⟩ ⟨false, 241580606255841719531892139581523737310069241703982971649047970340148720182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1442_1600 : bothSeg evalE (oGrid.idx 1442) (oGrid.dm 1442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1442) oGrid.kl oGrid.kr 400 1600 ⟨false, 241580606255841719531892139581523737310069241703982971649047970340148720182⟩ ⟨false, 0⟩ ⟨false, 385391870337657937317209693398437577544305775804787164799078185388067125064⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1442_2000 : bothSeg evalE (oGrid.idx 1442) (oGrid.dm 1442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1442) oGrid.kl oGrid.kr 400 2000 ⟨false, 385391870337657937317209693398437577544305775804787164799078185388067125064⟩ ⟨false, 0⟩ ⟨false, 580114593470015192903711975404467456818139908209519107454051811028797190584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1442_2400 : bothLoop evalE (oGrid.idx 1442) (oGrid.dm 1442) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1442) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 580114593470015192903711975404467456818139908209519107454051811028797190584⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1442 : oGrid.row evalE 1442 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1442_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1442_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1442_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1442_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1442_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1442_2000).1 (bothLoop_sound b_1442_2400).1))))))

theorem n_row_1442 : nGrid.row evalE 1442 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1442_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1442_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1442_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1442_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1442_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1442_2000).2 (bothLoop_sound b_1442_2400).2))))))

theorem b_1443_0 : bothSeg evalE (oGrid.idx 1443) (oGrid.dm 1443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1443) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 33704027469944159010146305344472743687822431514239240108830108097081121388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1443_400 : bothSeg evalE (oGrid.idx 1443) (oGrid.dm 1443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1443) oGrid.kl oGrid.kr 400 400 ⟨false, 33704027469944159010146305344472743687822431514239240108830108097081121388⟩ ⟨false, 0⟩ ⟨false, 91232749784155358611190826933210939378190142702363186404166796839461841114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1443_800 : bothSeg evalE (oGrid.idx 1443) (oGrid.dm 1443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1443) oGrid.kl oGrid.kr 400 800 ⟨false, 91232749784155358611190826933210939378190142702363186404166796839461841114⟩ ⟨false, 0⟩ ⟨false, 151751207359676447870539229806350151798369685645279072360593733606524681260⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1443_1200 : bothSeg evalE (oGrid.idx 1443) (oGrid.dm 1443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1443) oGrid.kl oGrid.kr 400 1200 ⟨false, 151751207359676447870539229806350151798369685645279072360593733606524681260⟩ ⟨false, 0⟩ ⟨false, 242726520440635338077895526446096977171272675335309818688725319072705507592⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1443_1600 : bothSeg evalE (oGrid.idx 1443) (oGrid.dm 1443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1443) oGrid.kl oGrid.kr 400 1600 ⟨false, 242726520440635338077895526446096977171272675335309818688725319072705507592⟩ ⟨false, 0⟩ ⟨false, 386805085786519326945393724668874818599850588517651542343277248931134647898⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1443_2000 : bothSeg evalE (oGrid.idx 1443) (oGrid.dm 1443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1443) oGrid.kl oGrid.kr 400 2000 ⟨false, 386805085786519326945393724668874818599850588517651542343277248931134647898⟩ ⟨false, 0⟩ ⟨false, 581763414226825469558795834932518438778502063140793691643318216605894711596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1443_2400 : bothLoop evalE (oGrid.idx 1443) (oGrid.dm 1443) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1443) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 581763414226825469558795834932518438778502063140793691643318216605894711596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1443 : oGrid.row evalE 1443 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1443_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1443_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1443_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1443_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1443_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1443_2000).1 (bothLoop_sound b_1443_2400).1))))))

theorem n_row_1443 : nGrid.row evalE 1443 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1443_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1443_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1443_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1443_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1443_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1443_2000).2 (bothLoop_sound b_1443_2400).2))))))

theorem b_1444_0 : bothSeg evalE (oGrid.idx 1444) (oGrid.dm 1444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1444) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 34138921373030149998442486686436052809495273974415932360613989973327603662⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1444_400 : bothSeg evalE (oGrid.idx 1444) (oGrid.dm 1444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1444) oGrid.kl oGrid.kr 400 400 ⟨false, 34138921373030149998442486686436052809495273974415932360613989973327603662⟩ ⟨false, 0⟩ ⟨false, 92112447007859681600689300312904889060387997341163116651671028526441341726⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1444_800 : bothSeg evalE (oGrid.idx 1444) (oGrid.dm 1444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1444) oGrid.kl oGrid.kr 400 800 ⟨false, 92112447007859681600689300312904889060387997341163116651671028526441341726⟩ ⟨false, 0⟩ ⟨false, 152588161934072213801379308190035724405301575165119274428302176942006341544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1444_1200 : bothSeg evalE (oGrid.idx 1444) (oGrid.dm 1444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1444) oGrid.kl oGrid.kr 400 1200 ⟨false, 152588161934072213801379308190035724405301575165119274428302176942006341544⟩ ⟨false, 0⟩ ⟨false, 243871217615864730394753546090842112083844456213352007644550398265992963356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1444_1600 : bothSeg evalE (oGrid.idx 1444) (oGrid.dm 1444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1444) oGrid.kl oGrid.kr 400 1600 ⟨false, 243871217615864730394753546090842112083844456213352007644550398265992963356⟩ ⟨false, 0⟩ ⟨false, 388217100888666079138928970356569870795108026056843310687064373407701089290⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1444_2000 : bothSeg evalE (oGrid.idx 1444) (oGrid.dm 1444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1444) oGrid.kl oGrid.kr 400 2000 ⟨false, 388217100888666079138928970356569870795108026056843310687064373407701089290⟩ ⟨false, 0⟩ ⟨false, 583411069719275937228500182063833443546123311334781542800661589560437578428⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1444_2400 : bothLoop evalE (oGrid.idx 1444) (oGrid.dm 1444) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1444) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 583411069719275937228500182063833443546123311334781542800661589560437578428⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1444 : oGrid.row evalE 1444 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1444_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1444_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1444_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1444_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1444_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1444_2000).1 (bothLoop_sound b_1444_2400).1))))))

theorem n_row_1444 : nGrid.row evalE 1444 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1444_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1444_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1444_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1444_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1444_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1444_2000).2 (bothLoop_sound b_1444_2400).2))))))

theorem b_1445_0 : bothSeg evalE (oGrid.idx 1445) (oGrid.dm 1445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1445) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 34574798162026037447529877938721080429277474249928076434068748368952594692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1445_400 : bothSeg evalE (oGrid.idx 1445) (oGrid.dm 1445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1445) oGrid.kl oGrid.kr 400 400 ⟨false, 34574798162026037447529877938721080429277474249928076434068748368952594692⟩ ⟨false, 0⟩ ⟨false, 92989762581123532685917175999799977452711243988501551415259565317117365816⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1445_800 : bothSeg evalE (oGrid.idx 1445) (oGrid.dm 1445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1445) oGrid.kl oGrid.kr 400 800 ⟨false, 92989762581123532685917175999799977452711243988501551415259565317117365816⟩ ⟨false, 0⟩ ⟨false, 153423928434715719385854028261536223416259928983541896009206752572383412390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1445_1200 : bothSeg evalE (oGrid.idx 1445) (oGrid.dm 1445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1445) oGrid.kl oGrid.kr 400 1200 ⟨false, 153423928434715719385854028261536223416259928983541896009206752572383412390⟩ ⟨false, 0⟩ ⟨false, 245014708399599319261916831125350336958396248628914419073170923308349864254⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1445_1600 : bothSeg evalE (oGrid.idx 1445) (oGrid.dm 1445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1445) oGrid.kl oGrid.kr 400 1600 ⟨false, 245014708399599319261916831125350336958396248628914419073170923308349864254⟩ ⟨false, 0⟩ ⟨false, 389627926197879004516552903337508807845166369389547122780194068882661255194⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1445_2000 : bothSeg evalE (oGrid.idx 1445) (oGrid.dm 1445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1445) oGrid.kl oGrid.kr 400 2000 ⟨false, 389627926197879004516552903337508807845166369389547122780194068882661255194⟩ ⟨false, 0⟩ ⟨false, 585057570436361312975896149788995054022604260496461587285627152151398101448⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1445_2400 : bothLoop evalE (oGrid.idx 1445) (oGrid.dm 1445) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1445) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 585057570436361312975896149788995054022604260496461587285627152151398101448⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1445 : oGrid.row evalE 1445 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1445_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1445_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1445_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1445_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1445_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1445_2000).1 (bothLoop_sound b_1445_2400).1))))))

theorem n_row_1445 : nGrid.row evalE 1445 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1445_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1445_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1445_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1445_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1445_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1445_2000).2 (bothLoop_sound b_1445_2400).2))))))

theorem b_1446_0 : bothSeg evalE (oGrid.idx 1446) (oGrid.dm 1446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1446) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 35011699433892131678514387163967244539845462545336928840786158089198918942⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1446_400 : bothSeg evalE (oGrid.idx 1446) (oGrid.dm 1446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1446) oGrid.kl oGrid.kr 400 400 ⟨false, 35011699433892131678514387163967244539845462545336928840786158089198918942⟩ ⟨false, 0⟩ ⟨false, 93864499054228853215918809840448439999458711739951139526890892233792135056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1446_800 : bothSeg evalE (oGrid.idx 1446) (oGrid.dm 1446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1446) oGrid.kl oGrid.kr 400 800 ⟨false, 93864499054228853215918809840448439999458711739951139526890892233792135056⟩ ⟨false, 0⟩ ⟨false, 154258463026844547502273673081827361139769125836069149126360165753917980520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1446_1200 : bothSeg evalE (oGrid.idx 1446) (oGrid.dm 1446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1446) oGrid.kl oGrid.kr 400 1200 ⟨false, 154258463026844547502273673081827361139769125836069149126360165753917980520⟩ ⟨false, 0⟩ ⟨false, 246156948919804063754353127351075903185917551064483066435034622346845906842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1446_1600 : bothSeg evalE (oGrid.idx 1446) (oGrid.dm 1446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1446) oGrid.kl oGrid.kr 400 1600 ⟨false, 246156948919804063754353127351075903185917551064483066435034622346845906842⟩ ⟨false, 0⟩ ⟨false, 391037517777952355897981614713585572347965168394477132201643716209668930254⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1446_2000 : bothSeg evalE (oGrid.idx 1446) (oGrid.dm 1446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1446) oGrid.kl oGrid.kr 400 2000 ⟨false, 391037517777952355897981614713585572347965168394477132201643716209668930254⟩ ⟨false, 0⟩ ⟨false, 586702872377173480151021462225737802916402600231015730821876449021081146266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1446_2400 : bothLoop evalE (oGrid.idx 1446) (oGrid.dm 1446) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1446) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 586702872377173480151021462225737802916402600231015730821876449021081146266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1446 : oGrid.row evalE 1446 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1446_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1446_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1446_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1446_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1446_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1446_2000).1 (bothLoop_sound b_1446_2400).1))))))

theorem n_row_1446 : nGrid.row evalE 1446 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1446_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1446_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1446_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1446_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1446_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1446_2000).2 (bothLoop_sound b_1446_2400).2))))))

theorem b_1447_0 : bothSeg evalE (oGrid.idx 1447) (oGrid.dm 1447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1447) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 35449670770937954837751785733117313367419959131399107606126773647018483762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1447_400 : bothSeg evalE (oGrid.idx 1447) (oGrid.dm 1447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1447) oGrid.kl oGrid.kr 400 400 ⟨false, 35449670770937954837751785733117313367419959131399107606126773647018483762⟩ ⟨false, 0⟩ ⟨false, 94736502056135742087455803325025429466384454515947721118277291410459603510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1447_800 : bothSeg evalE (oGrid.idx 1447) (oGrid.dm 1447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1447) oGrid.kl oGrid.kr 400 800 ⟨false, 94736502056135742087455803325025429466384454515947721118277291410459603510⟩ ⟨false, 0⟩ ⟨false, 155091763738952949521274438396306653373297588022661751469663508264201427480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1447_1200 : bothSeg evalE (oGrid.idx 1447) (oGrid.dm 1447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1447) oGrid.kl oGrid.kr 400 1200 ⟨false, 155091763738952949521274438396306653373297588022661751469663508264201427480⟩ ⟨false, 0⟩ ⟨false, 247297937167817352500856487496958534207673431991241810628300481640166550270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1447_1600 : bothSeg evalE (oGrid.idx 1447) (oGrid.dm 1447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1447) oGrid.kl oGrid.kr 400 1600 ⟨false, 247297937167817352500856487496958534207673431991241810628300481640166550270⟩ ⟨false, 0⟩ ⟨false, 392445873556171536702565086923556394238849264803866127971336092426231688742⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1447_2000 : bothSeg evalE (oGrid.idx 1447) (oGrid.dm 1447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1447) oGrid.kl oGrid.kr 400 2000 ⟨false, 392445873556171536702565086923556394238849264803866127971336092426231688742⟩ ⟨false, 0⟩ ⟨false, 588346973404379116943300845033673951801243670274993946990912231399205035514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1447_2400 : bothLoop evalE (oGrid.idx 1447) (oGrid.dm 1447) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1447) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 588346973404379116943300845033673951801243670274993946990912231399205035514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1447 : oGrid.row evalE 1447 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1447_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1447_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1447_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1447_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1447_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1447_2000).1 (bothLoop_sound b_1447_2400).1))))))

theorem n_row_1447 : nGrid.row evalE 1447 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1447_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1447_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1447_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1447_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1447_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1447_2000).2 (bothLoop_sound b_1447_2400).2))))))

theorem b_1448_0 : bothSeg evalE (oGrid.idx 1448) (oGrid.dm 1448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1448) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 35888759658460454181992460528520569837718964402991714874865626007490712728⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1448_400 : bothSeg evalE (oGrid.idx 1448) (oGrid.dm 1448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1448) oGrid.kl oGrid.kr 400 400 ⟨false, 35888759658460454181992460528520569837718964402991714874865626007490712728⟩ ⟨false, 0⟩ ⟨false, 95605567756412614950895916614867704787462154224406516033075600047004041592⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1448_800 : bothSeg evalE (oGrid.idx 1448) (oGrid.dm 1448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1448) oGrid.kl oGrid.kr 400 800 ⟨false, 95605567756412614950895916614867704787462154224406516033075600047004041592⟩ ⟨false, 0⟩ ⟨false, 155923794861729467960888502202624189383871986552772139928320509671386400972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1448_1200 : bothSeg evalE (oGrid.idx 1448) (oGrid.dm 1448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1448) oGrid.kl oGrid.kr 400 1200 ⟨false, 155923794861729467960888502202624189383871986552772139928320509671386400972⟩ ⟨false, 0⟩ ⟨false, 248437637397288357236317818145551416199931107667655442996245460135768769800⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1448_1600 : bothSeg evalE (oGrid.idx 1448) (oGrid.dm 1448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1448) oGrid.kl oGrid.kr 400 1600 ⟨false, 248437637397288357236317818145551416199931107667655442996245460135768769800⟩ ⟨false, 0⟩ ⟨false, 393852957722250269874718321715198667096400096816818341075560202974156784792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1448_2000 : bothSeg evalE (oGrid.idx 1448) (oGrid.dm 1448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1448) oGrid.kl oGrid.kr 400 2000 ⟨false, 393852957722250269874718321715198667096400096816818341075560202974156784792⟩ ⟨false, 0⟩ ⟨false, 589989837643156785459593309412695123395596469713531433268802635095359639848⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1448_2400 : bothLoop evalE (oGrid.idx 1448) (oGrid.dm 1448) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1448) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 589989837643156785459593309412695123395596469713531433268802635095359639848⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1448 : oGrid.row evalE 1448 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1448_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1448_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1448_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1448_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1448_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1448_2000).1 (bothLoop_sound b_1448_2400).1))))))

theorem n_row_1448 : nGrid.row evalE 1448 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1448_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1448_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1448_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1448_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1448_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1448_2000).2 (bothLoop_sound b_1448_2400).2))))))

theorem b_1449_0 : bothSeg evalE (oGrid.idx 1449) (oGrid.dm 1449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1449) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 36329013327342813053628754267575765093753871575723013569374145495663307188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1449_400 : bothSeg evalE (oGrid.idx 1449) (oGrid.dm 1449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1449) oGrid.kl oGrid.kr 400 400 ⟨false, 36329013327342813053628754267575765093753871575723013569374145495663307188⟩ ⟨false, 0⟩ ⟨false, 96471543849051254794369815165000863552214684794539126206716039377499502128⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1449_800 : bothSeg evalE (oGrid.idx 1449) (oGrid.dm 1449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1449) oGrid.kl oGrid.kr 400 800 ⟨false, 96471543849051254794369815165000863552214684794539126206716039377499502128⟩ ⟨false, 0⟩ ⟨false, 156754547086452960088646691029549336239014874352957003268615507469588944850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1449_1200 : bothSeg evalE (oGrid.idx 1449) (oGrid.dm 1449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1449) oGrid.kl oGrid.kr 400 1200 ⟨false, 156754547086452960088646691029549336239014874352957003268615507469588944850⟩ ⟨false, 0⟩ ⟨false, 249576040262572787877323721608057446640371064353705607298983549244836881432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1449_1600 : bothSeg evalE (oGrid.idx 1449) (oGrid.dm 1449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1449) oGrid.kl oGrid.kr 400 1600 ⟨false, 249576040262572787877323721608057446640371064353705607298983549244836881432⟩ ⟨false, 0⟩ ⟨false, 395258760866726168565416881068467198986604120487930903006557432928975578988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1449_2000 : bothSeg evalE (oGrid.idx 1449) (oGrid.dm 1449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1449) oGrid.kl oGrid.kr 400 2000 ⟨false, 395258760866726168565416881068467198986604120487930903006557432928975578988⟩ ⟨false, 0⟩ ⟨false, 591631455619592422557460757675402471535421852937175194081745949379724756790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1449_2400 : bothLoop evalE (oGrid.idx 1449) (oGrid.dm 1449) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1449) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 591631455619592422557460757675402471535421852937175194081745949379724756790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1449 : oGrid.row evalE 1449 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1449_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1449_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1449_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1449_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1449_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1449_2000).1 (bothLoop_sound b_1449_2400).1))))))

theorem n_row_1449 : nGrid.row evalE 1449 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1449_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1449_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1449_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1449_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1449_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1449_2000).2 (bothLoop_sound b_1449_2400).2))))))

theorem b_1450_0 : bothSeg evalE (oGrid.idx 1450) (oGrid.dm 1450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1450) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 36770480157333045358964785595564581289248774189383295007638773010016820382⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1450_400 : bothSeg evalE (oGrid.idx 1450) (oGrid.dm 1450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1450) oGrid.kl oGrid.kr 400 400 ⟨false, 36770480157333045358964785595564581289248774189383295007638773010016820382⟩ ⟨false, 0⟩ ⟨false, 97334238189770280337968261629662080857466298365097324746438171526116581408⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1450_800 : bothSeg evalE (oGrid.idx 1450) (oGrid.dm 1450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1450) oGrid.kl oGrid.kr 400 800 ⟨false, 97334238189770280337968261629662080857466298365097324746438171526116581408⟩ ⟨false, 0⟩ ⟨false, 157583998269948497185291550888889007198292921452165407088738792476558349450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1450_1200 : bothSeg evalE (oGrid.idx 1450) (oGrid.dm 1450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1450) oGrid.kl oGrid.kr 400 1200 ⟨false, 157583998269948497185291550888889007198292921452165407088738792476558349450⟩ ⟨false, 0⟩ ⟨false, 250713123583688523834517142086283847006775105831608253051470632151608333748⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1450_1600 : bothSeg evalE (oGrid.idx 1450) (oGrid.dm 1450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1450) oGrid.kl oGrid.kr 400 1600 ⟨false, 250713123583688523834517142086283847006775105831608253051470632151608333748⟩ ⟨false, 0⟩ ⟨false, 396663260745916183283110962938457828378752719843304394129736427737421869142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1450_2000 : bothSeg evalE (oGrid.idx 1450) (oGrid.dm 1450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1450) oGrid.kl oGrid.kr 400 2000 ⟨false, 396663260745916183283110962938457828378752719843304394129736427737421869142⟩ ⟨false, 0⟩ ⟨false, 593271805025634707147316775736356188029096461752705677315410298197307746406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1450_2400 : bothLoop evalE (oGrid.idx 1450) (oGrid.dm 1450) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1450) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 593271805025634707147316775736356188029096461752705677315410298197307746406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1450 : oGrid.row evalE 1450 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1450_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1450_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1450_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1450_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1450_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1450_2000).1 (bothLoop_sound b_1450_2400).1))))))

theorem n_row_1450 : nGrid.row evalE 1450 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1450_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1450_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1450_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1450_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1450_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1450_2000).2 (bothLoop_sound b_1450_2400).2))))))

theorem b_1451_0 : bothSeg evalE (oGrid.idx 1451) (oGrid.dm 1451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1451) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 37213209703624535510196541342785964671502210156628590632502790625209658636⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1451_400 : bothSeg evalE (oGrid.idx 1451) (oGrid.dm 1451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1451) oGrid.kl oGrid.kr 400 400 ⟨false, 37213209703624535510196541342785964671502210156628590632502790625209658636⟩ ⟨false, 0⟩ ⟨false, 98193480437386300177964616417748571972981531406778145380677515830595093274⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1451_800 : bothSeg evalE (oGrid.idx 1451) (oGrid.dm 1451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1451) oGrid.kl oGrid.kr 400 800 ⟨false, 98193480437386300177964616417748571972981531406778145380677515830595093274⟩ ⟨false, 0⟩ ⟨false, 158412120243734473271626396762892601163211290487124922870702361563201667700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1451_1200 : bothSeg evalE (oGrid.idx 1451) (oGrid.dm 1451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1451) oGrid.kl oGrid.kr 400 1200 ⟨false, 158412120243734473271626396762892601163211290487124922870702361563201667700⟩ ⟨false, 0⟩ ⟨false, 251848859155462455362102923341889096795770881963868066074754868675503354684⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1451_1600 : bothSeg evalE (oGrid.idx 1451) (oGrid.dm 1451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1451) oGrid.kl oGrid.kr 400 1600 ⟨false, 251848859155462455362102923341889096795770881963868066074754868675503354684⟩ ⟨false, 0⟩ ⟨false, 398066429091063259314360733221313930342889248381537332670543539522486563674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1451_2000 : bothSeg evalE (oGrid.idx 1451) (oGrid.dm 1451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1451) oGrid.kl oGrid.kr 400 2000 ⟨false, 398066429091063259314360733221313930342889248381537332670543539522486563674⟩ ⟨false, 0⟩ ⟨false, 594910857528241637764061933848972580396338677614282436820577435573209244066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1451_2400 : bothLoop evalE (oGrid.idx 1451) (oGrid.dm 1451) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1451) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 594910857528241637764061933848972580396338677614282436820577435573209244066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1451 : oGrid.row evalE 1451 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1451_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1451_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1451_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1451_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1451_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1451_2000).1 (bothLoop_sound b_1451_2400).1))))))

theorem n_row_1451 : nGrid.row evalE 1451 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1451_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1451_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1451_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1451_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1451_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1451_2000).2 (bothLoop_sound b_1451_2400).2))))))

theorem b_1452_0 : bothSeg evalE (oGrid.idx 1452) (oGrid.dm 1452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1452) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 37657255036487232954037136294040021435397960044829746607952330470296377258⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1452_400 : bothSeg evalE (oGrid.idx 1452) (oGrid.dm 1452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1452) oGrid.kl oGrid.kr 400 400 ⟨false, 37657255036487232954037136294040021435397960044829746607952330470296377258⟩ ⟨false, 0⟩ ⟨false, 99049089999448660438249375121904608042508280731371268285126648009269220518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1452_800 : bothSeg evalE (oGrid.idx 1452) (oGrid.dm 1452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1452) oGrid.kl oGrid.kr 400 800 ⟨false, 99049089999448660438249375121904608042508280731371268285126648009269220518⟩ ⟨false, 0⟩ ⟨false, 159238896170410445341697212839830153417314613787606510382823480310744749106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1452_1200 : bothSeg evalE (oGrid.idx 1452) (oGrid.dm 1452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1452) oGrid.kl oGrid.kr 400 1200 ⟨false, 159238896170410445341697212839830153417314613787606510382823480310744749106⟩ ⟨false, 0⟩ ⟨false, 252983230103918056986554514925257884239568222942113176546167548045618245012⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1452_1600 : bothSeg evalE (oGrid.idx 1452) (oGrid.dm 1452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1452) oGrid.kl oGrid.kr 400 1600 ⟨false, 252983230103918056986554514925257884239568222942113176546167548045618245012⟩ ⟨false, 0⟩ ⟨false, 399468248964723726456167772262546240880062214692533795391186686577715139342⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1452_2000 : bothSeg evalE (oGrid.idx 1452) (oGrid.dm 1452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1452) oGrid.kl oGrid.kr 400 2000 ⟨false, 399468248964723726456167772262546240880062214692533795391186686577715139342⟩ ⟨false, 0⟩ ⟨false, 596548596125767842450482913166928076779359558261303167647338469920670585266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1452_2400 : bothLoop evalE (oGrid.idx 1452) (oGrid.dm 1452) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1452) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 596548596125767842450482913166928076779359558261303167647338469920670585266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1452 : oGrid.row evalE 1452 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1452_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1452_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1452_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1452_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1452_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1452_2000).1 (bothLoop_sound b_1452_2400).1))))))

theorem n_row_1452 : nGrid.row evalE 1452 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1452_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1452_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1452_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1452_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1452_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1452_2000).2 (bothLoop_sound b_1452_2400).2))))))

theorem b_1453_0 : bothSeg evalE (oGrid.idx 1453) (oGrid.dm 1453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1453) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 38102668524814768731057278033910010950222325025398884107870375609296959390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1453_400 : bothSeg evalE (oGrid.idx 1453) (oGrid.dm 1453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1453) oGrid.kl oGrid.kr 400 400 ⟨false, 38102668524814768731057278033910010950222325025398884107870375609296959390⟩ ⟨false, 0⟩ ⟨false, 99900897623552370162779148920121212610056062404735784078499855602139721988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1453_800 : bothSeg evalE (oGrid.idx 1453) (oGrid.dm 1453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1453) oGrid.kl oGrid.kr 400 800 ⟨false, 99900897623552370162779148920121212610056062404735784078499855602139721988⟩ ⟨false, 0⟩ ⟨false, 160064308735718700410781128060584022466609579329367891918533880964314579014⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1453_1200 : bothSeg evalE (oGrid.idx 1453) (oGrid.dm 1453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1453) oGrid.kl oGrid.kr 400 1200 ⟨false, 160064308735718700410781128060584022466609579329367891918533880964314579014⟩ ⟨false, 0⟩ ⟨false, 254116219078336688321856747331963240675315054518394685067574212603355432396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1453_1600 : bothSeg evalE (oGrid.idx 1453) (oGrid.dm 1453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1453) oGrid.kl oGrid.kr 400 1600 ⟨false, 254116219078336688321856747331963240675315054518394685067574212603355432396⟩ ⟨false, 0⟩ ⟨false, 400868702952828416367255190039562063128132876627638294273003869124427209200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1453_2000 : bothSeg evalE (oGrid.idx 1453) (oGrid.dm 1453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1453) oGrid.kl oGrid.kr 400 2000 ⟨false, 400868702952828416367255190039562063128132876627638294273003869124427209200⟩ ⟨false, 0⟩ ⟨false, 598185003340025616259969333720623062279574881351112724527197246239831423886⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1453_2400 : bothLoop evalE (oGrid.idx 1453) (oGrid.dm 1453) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1453) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 598185003340025616259969333720623062279574881351112724527197246239831423886⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1453 : oGrid.row evalE 1453 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1453_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1453_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1453_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1453_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1453_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1453_2000).1 (bothLoop_sound b_1453_2400).1))))))

theorem n_row_1453 : nGrid.row evalE 1453 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1453_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1453_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1453_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1453_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1453_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1453_2000).2 (bothLoop_sound b_1453_2400).2))))))

theorem b_1454_0 : bothSeg evalE (oGrid.idx 1454) (oGrid.dm 1454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1454) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 38549499906895452433622414750767998037864962409955417550131637954443950756⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1454_400 : bothSeg evalE (oGrid.idx 1454) (oGrid.dm 1454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1454) oGrid.kl oGrid.kr 400 400 ⟨false, 38549499906895452433622414750767998037864962409955417550131637954443950756⟩ ⟨false, 0⟩ ⟨false, 100748718250529126547763529320324243625561118949358978068380337834512966514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1454_800 : bothSeg evalE (oGrid.idx 1454) (oGrid.dm 1454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1454) oGrid.kl oGrid.kr 400 800 ⟨false, 100748718250529126547763529320324243625561118949358978068380337834512966514⟩ ⟨false, 0⟩ ⟨false, 160888322555444681566251556805646550354343523733084425078544681046212287538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1454_1200 : bothSeg evalE (oGrid.idx 1454) (oGrid.dm 1454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1454) oGrid.kl oGrid.kr 400 1200 ⟨false, 160888322555444681566251556805646550354343523733084425078544681046212287538⟩ ⟨false, 0⟩ ⟨false, 255247790658157754458217792154663125002806757528583166711884796810208737468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1454_1600 : bothSeg evalE (oGrid.idx 1454) (oGrid.dm 1454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1454) oGrid.kl oGrid.kr 400 1600 ⟨false, 255247790658157754458217792154663125002806757528583166711884796810208737468⟩ ⟨false, 0⟩ ⟨false, 402267755571582639725146177739094637804225138076876867114987829471163773854⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1454_2000 : bothSeg evalE (oGrid.idx 1454) (oGrid.dm 1454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1454) oGrid.kl oGrid.kr 400 2000 ⟨false, 402267755571582639725146177739094637804225138076876867114987829471163773854⟩ ⟨false, 0⟩ ⟨false, 599820043623184818565698238056874111912211446074898528348631987207516575286⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1454_2400 : bothLoop evalE (oGrid.idx 1454) (oGrid.dm 1454) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1454) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 599820043623184818565698238056874111912211446074898528348631987207516575286⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1454 : oGrid.row evalE 1454 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1454_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1454_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1454_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1454_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1454_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1454_2000).1 (bothLoop_sound b_1454_2400).1))))))

theorem n_row_1454 : nGrid.row evalE 1454 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1454_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1454_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1454_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1454_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1454_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1454_2000).2 (bothLoop_sound b_1454_2400).2))))))

theorem b_1455_0 : bothSeg evalE (oGrid.idx 1455) (oGrid.dm 1455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1455) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 38997801562581481620724117875177156358363015179168658725922595102326910758⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1455_400 : bothSeg evalE (oGrid.idx 1455) (oGrid.dm 1455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1455) oGrid.kl oGrid.kr 400 400 ⟨false, 38997801562581481620724117875177156358363015179168658725922595102326910758⟩ ⟨false, 0⟩ ⟨false, 101592384155146595089877512489213422835197938709326253835617631429040794174⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1455_800 : bothSeg evalE (oGrid.idx 1455) (oGrid.dm 1455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1455) oGrid.kl oGrid.kr 400 800 ⟨false, 101592384155146595089877512489213422835197938709326253835617631429040794174⟩ ⟨false, 0⟩ ⟨false, 161710932012502642903282804273079192634198433456042898245297281090290320902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1455_1200 : bothSeg evalE (oGrid.idx 1455) (oGrid.dm 1455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1455) oGrid.kl oGrid.kr 400 1200 ⟨false, 161710932012502642903282804273079192634198433456042898245297281090290320902⟩ ⟨false, 0⟩ ⟨false, 256377939190064095805077962904863914278130387769256569404072511180618817298⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1455_1600 : bothSeg evalE (oGrid.idx 1455) (oGrid.dm 1455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1455) oGrid.kl oGrid.kr 400 1600 ⟨false, 256377939190064095805077962904863914278130387769256569404072511180618817298⟩ ⟨false, 0⟩ ⟨false, 403665401104551393069784326318153053666801283169335541927343459084034306408⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1455_2000 : bothSeg evalE (oGrid.idx 1455) (oGrid.dm 1455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1455) oGrid.kl oGrid.kr 400 2000 ⟨false, 403665401104551393069784326318153053666801283169335541927343459084034306408⟩ ⟨false, 0⟩ ⟨false, 601453711194858000057328615589682181545415822862950062264898988511923893666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1455_2400 : bothLoop evalE (oGrid.idx 1455) (oGrid.dm 1455) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1455) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 601453711194858000057328615589682181545415822862950062264898988511923893666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1455 : oGrid.row evalE 1455 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1455_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1455_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1455_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1455_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1455_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1455_2000).1 (bothLoop_sound b_1455_2400).1))))))

theorem n_row_1455 : nGrid.row evalE 1455 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1455_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1455_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1455_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1455_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1455_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1455_2000).2 (bothLoop_sound b_1455_2400).2))))))

theorem b_1456_0 : bothSeg evalE (oGrid.idx 1456) (oGrid.dm 1456) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1456) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 39447625020567336691790278125291493500367340614208271989617379066390420356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1456_400 : bothSeg evalE (oGrid.idx 1456) (oGrid.dm 1456) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1456) oGrid.kl oGrid.kr 400 400 ⟨false, 39447625020567336691790278125291493500367340614208271989617379066390420356⟩ ⟨false, 0⟩ ⟨false, 102431718902250000752545175036254390080845647026227124686110922023980467240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1456_800 : bothSeg evalE (oGrid.idx 1456) (oGrid.dm 1456) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1456) oGrid.kl oGrid.kr 400 800 ⟨false, 102431718902250000752545175036254390080845647026227124686110922023980467240⟩ ⟨false, 0⟩ ⟨false, 162532094768638037805911942948334845485348258584612500337735484894915983622⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1456_1200 : bothSeg evalE (oGrid.idx 1456) (oGrid.dm 1456) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1456) oGrid.kl oGrid.kr 400 1200 ⟨false, 162532094768638037805911942948334845485348258584612500337735484894915983622⟩ ⟨false, 0⟩ ⟨false, 257506622299684111847799848351169912987332378370091750747317918175019161044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1456_1600 : bothSeg evalE (oGrid.idx 1456) (oGrid.dm 1456) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1456) oGrid.kl oGrid.kr 400 1600 ⟨false, 257506622299684111847799848351169912987332378370091750747317918175019161044⟩ ⟨false, 0⟩ ⟨false, 405061597114361299792994907423072982551913679294269205018869617974285665780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1456_2000 : bothSeg evalE (oGrid.idx 1456) (oGrid.dm 1456) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1456) oGrid.kl oGrid.kr 400 2000 ⟨false, 405061597114361299792994907423072982551913679294269205018869617974285665780⟩ ⟨false, 0⟩ ⟨false, 603085963553802263884803088286331661584527675448839425984286182170017189914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1456_2400 : bothLoop evalE (oGrid.idx 1456) (oGrid.dm 1456) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1456) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 603085963553802263884803088286331661584527675448839425984286182170017189914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1456 : oGrid.row evalE 1456 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1456_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1456_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1456_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1456_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1456_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1456_2000).1 (bothLoop_sound b_1456_2400).1))))))

theorem n_row_1456 : nGrid.row evalE 1456 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1456_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1456_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1456_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1456_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1456_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1456_2000).2 (bothLoop_sound b_1456_2400).2))))))

theorem b_1457_0 : bothSeg evalE (oGrid.idx 1457) (oGrid.dm 1457) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1457) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 39899022628372844989021421131024223761178351188981784116974487135555467324⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1457_400 : bothSeg evalE (oGrid.idx 1457) (oGrid.dm 1457) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1457) oGrid.kl oGrid.kr 400 400 ⟨false, 39899022628372844989021421131024223761178351188981784116974487135555467324⟩ ⟨false, 0⟩ ⟨false, 103266540329912309668999394090662875977709229329980290997189110802314908528⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1457_800 : bothSeg evalE (oGrid.idx 1457) (oGrid.dm 1457) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1457) oGrid.kl oGrid.kr 400 800 ⟨false, 103266540329912309668999394090662875977709229329980290997189110802314908528⟩ ⟨false, 0⟩ ⟨false, 163351789213906883525144625125872837206473581053772431889677564761920584960⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1457_1200 : bothSeg evalE (oGrid.idx 1457) (oGrid.dm 1457) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1457) oGrid.kl oGrid.kr 400 1200 ⟨false, 163351789213906883525144625125872837206473581053772431889677564761920584960⟩ ⟨false, 0⟩ ⟨false, 258633818341070861768594957522368336485499964945391617153304508758948612888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1457_1600 : bothSeg evalE (oGrid.idx 1457) (oGrid.dm 1457) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1457) oGrid.kl oGrid.kr 400 1600 ⟨false, 258633818341070861768594957522368336485499964945391617153304508758948612888⟩ ⟨false, 0⟩ ⟨false, 406456321892179528224256033289329669442134893068028105712743700919419802480⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1457_2000 : bothSeg evalE (oGrid.idx 1457) (oGrid.dm 1457) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1457) oGrid.kl oGrid.kr 400 2000 ⟨false, 406456321892179528224256033289329669442134893068028105712743700919419802480⟩ ⟨false, 0⟩ ⟨false, 604716778927398103900022473205965617717446819959641131717718790783130927434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1457_2400 : bothLoop evalE (oGrid.idx 1457) (oGrid.dm 1457) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1457) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 604716778927398103900022473205965617717446819959641131717718790783130927434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1457 : oGrid.row evalE 1457 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1457_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1457_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1457_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1457_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1457_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1457_2000).1 (bothLoop_sound b_1457_2400).1))))))

theorem n_row_1457 : nGrid.row evalE 1457 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1457_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1457_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1457_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1457_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1457_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1457_2000).2 (bothLoop_sound b_1457_2400).2))))))

theorem b_1458_0 : bothSeg evalE (oGrid.idx 1458) (oGrid.dm 1458) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1458) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 40352044459137524521702588024554164455910189684746706376218953617679166662⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1458_400 : bothSeg evalE (oGrid.idx 1458) (oGrid.dm 1458) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1458) oGrid.kl oGrid.kr 400 400 ⟨false, 40352044459137524521702588024554164455910189684746706376218953617679166662⟩ ⟨false, 0⟩ ⟨false, 104096684575488852141272910720393340862080979253067116690875240354624660886⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1458_800 : bothSeg evalE (oGrid.idx 1458) (oGrid.dm 1458) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1458) oGrid.kl oGrid.kr 400 800 ⟨false, 104096684575488852141272910720393340862080979253067116690875240354624660886⟩ ⟨false, 0⟩ ⟨false, 164169989046062517339780912586605192456507741050811336971055736250532898930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1458_1200 : bothSeg evalE (oGrid.idx 1458) (oGrid.dm 1458) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1458) oGrid.kl oGrid.kr 400 1200 ⟨false, 164169989046062517339780912586605192456507741050811336971055736250532898930⟩ ⟨false, 0⟩ ⟨false, 259759500976088557216233299815928218897830421198738840750772986769313075532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1458_1600 : bothSeg evalE (oGrid.idx 1458) (oGrid.dm 1458) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1458) oGrid.kl oGrid.kr 400 1600 ⟨false, 259759500976088557216233299815928218897830421198738840750772986769313075532⟩ ⟨false, 0⟩ ⟨false, 407849549037100102097238895796138221033327993650834463154483376301667689752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1458_2000 : bothSeg evalE (oGrid.idx 1458) (oGrid.dm 1458) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1458) oGrid.kl oGrid.kr 400 2000 ⟨false, 407849549037100102097238895796138221033327993650834463154483376301667689752⟩ ⟨false, 0⟩ ⟨false, 606346130851035635281148097453975419586549125477519959787013332494553175602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1458_2400 : bothLoop evalE (oGrid.idx 1458) (oGrid.dm 1458) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1458) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 606346130851035635281148097453975419586549125477519959787013332494553175602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1458 : oGrid.row evalE 1458 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1458_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1458_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1458_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1458_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1458_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1458_2000).1 (bothLoop_sound b_1458_2400).1))))))

theorem n_row_1458 : nGrid.row evalE 1458 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1458_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1458_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1458_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1458_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1458_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1458_2000).2 (bothLoop_sound b_1458_2400).2))))))

theorem b_1459_0 : bothSeg evalE (oGrid.idx 1459) (oGrid.dm 1459) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1459) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 40806740835971955489019859160686550413463423373530864030582440301485124728⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1459_400 : bothSeg evalE (oGrid.idx 1459) (oGrid.dm 1459) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1459) oGrid.kl oGrid.kr 400 400 ⟨false, 40806740835971955489019859160686550413463423373530864030582440301485124728⟩ ⟨false, 0⟩ ⟨false, 104921971672504448378671098969043686499207502189422592696551061759456671174⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1459_800 : bothSeg evalE (oGrid.idx 1459) (oGrid.dm 1459) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1459) oGrid.kl oGrid.kr 400 800 ⟨false, 104921971672504448378671098969043686499207502189422592696551061759456671174⟩ ⟨false, 0⟩ ⟨false, 164986661301962510338245282444130399800673856413615591139889909109287279978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1459_1200 : bothSeg evalE (oGrid.idx 1459) (oGrid.dm 1459) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1459) oGrid.kl oGrid.kr 400 1200 ⟨false, 164986661301962510338245282444130399800673856413615591139889909109287279978⟩ ⟨false, 0⟩ ⟨false, 260883637205819213261692229099612043714946956853434670145497092675744763066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1459_1600 : bothSeg evalE (oGrid.idx 1459) (oGrid.dm 1459) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1459) oGrid.kl oGrid.kr 400 1600 ⟨false, 260883637205819213261692229099612043714946956853434670145497092675744763066⟩ ⟨false, 0⟩ ⟨false, 409241245487550369434185234849168681098195373153820370450420042946069946792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1459_2000 : bothSeg evalE (oGrid.idx 1459) (oGrid.dm 1459) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1459) oGrid.kl oGrid.kr 400 2000 ⟨false, 409241245487550369434185234849168681098195373153820370450420042946069946792⟩ ⟨false, 0⟩ ⟨false, 607973986199520983576894570455347182330415207042800572747926803559533741366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1459_2400 : bothLoop evalE (oGrid.idx 1459) (oGrid.dm 1459) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1459) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 607973986199520983576894570455347182330415207042800572747926803559533741366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1459 : oGrid.row evalE 1459 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1459_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1459_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1459_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1459_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1459_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1459_2000).1 (bothLoop_sound b_1459_2400).1))))))

theorem n_row_1459 : nGrid.row evalE 1459 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1459_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1459_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1459_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1459_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1459_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1459_2000).2 (bothLoop_sound b_1459_2400).2))))))

theorem b_1460_0 : bothSeg evalE (oGrid.idx 1460) (oGrid.dm 1460) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1460) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 41263157752591759546077603342795864932525259977596683186578983138094034580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1460_400 : bothSeg evalE (oGrid.idx 1460) (oGrid.dm 1460) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1460) oGrid.kl oGrid.kr 400 400 ⟨false, 41263157752591759546077603342795864932525259977596683186578983138094034580⟩ ⟨false, 0⟩ ⟨false, 105742237328784248709767757088418175142453981788983725093934566968978267844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1460_800 : bothSeg evalE (oGrid.idx 1460) (oGrid.dm 1460) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1460) oGrid.kl oGrid.kr 400 800 ⟨false, 105742237328784248709767757088418175142453981788983725093934566968978267844⟩ ⟨false, 0⟩ ⟨false, 165801780261545288310526566484799734949929212849055373791861952289771050010⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1460_1200 : bothSeg evalE (oGrid.idx 1460) (oGrid.dm 1460) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1460) oGrid.kl oGrid.kr 400 1200 ⟨false, 165801780261545288310526566484799734949929212849055373791861952289771050010⟩ ⟨false, 0⟩ ⟨false, 262006201274539007027724305919048988480013223913097485419943783725040532282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1460_1600 : bothSeg evalE (oGrid.idx 1460) (oGrid.dm 1460) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1460) oGrid.kl oGrid.kr 400 1600 ⟨false, 262006201274539007027724305919048988480013223913097485419943783725040532282⟩ ⟨false, 0⟩ ⟨false, 410631385425267179336012661315404076506282435109479079898892294193270739110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1460_2000 : bothSeg evalE (oGrid.idx 1460) (oGrid.dm 1460) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1460) oGrid.kl oGrid.kr 400 2000 ⟨false, 410631385425267179336012661315404076506282435109479079898892294193270739110⟩ ⟨false, 0⟩ ⟨false, 609600319091052381658997075682629483035805291242043303621096853020595134446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1460_2400 : bothLoop evalE (oGrid.idx 1460) (oGrid.dm 1460) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1460) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 609600319091052381658997075682629483035805291242043303621096853020595134446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1460 : oGrid.row evalE 1460 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1460_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1460_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1460_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1460_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1460_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1460_2000).1 (bothLoop_sound b_1460_2400).1))))))

theorem n_row_1460 : nGrid.row evalE 1460 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1460_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1460_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1460_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1460_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1460_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1460_2000).2 (bothLoop_sound b_1460_2400).2))))))

theorem b_1461_0 : bothSeg evalE (oGrid.idx 1461) (oGrid.dm 1461) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1461) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 41721346498108996587999905525196352213608335276049811154652528329541884968⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1461_400 : bothSeg evalE (oGrid.idx 1461) (oGrid.dm 1461) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1461) oGrid.kl oGrid.kr 400 400 ⟨false, 41721346498108996587999905525196352213608335276049811154652528329541884968⟩ ⟨false, 0⟩ ⟨false, 106557308356291755564285917690572303106433859245351331072826285726805943554⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1461_800 : bothSeg evalE (oGrid.idx 1461) (oGrid.dm 1461) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1461) oGrid.kl oGrid.kr 400 800 ⟨false, 106557308356291755564285917690572303106433859245351331072826285726805943554⟩ ⟨false, 0⟩ ⟨false, 166615308710974266634922743452701827333806718917843150393740027621798675748⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1461_1200 : bothSeg evalE (oGrid.idx 1461) (oGrid.dm 1461) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1461) oGrid.kl oGrid.kr 400 1200 ⟨false, 166615308710974266634922743452701827333806718917843150393740027621798675748⟩ ⟨false, 0⟩ ⟨false, 263127155932862150875914920322964218513549686694518601798407335230884340694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1461_1600 : bothSeg evalE (oGrid.idx 1461) (oGrid.dm 1461) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1461) oGrid.kl oGrid.kr 400 1600 ⟨false, 263127155932862150875914920322964218513549686694518601798407335230884340694⟩ ⟨false, 0⟩ ⟨false, 412019931538440573561628503212312493955211596448235664200504513393587206318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1461_2000 : bothSeg evalE (oGrid.idx 1461) (oGrid.dm 1461) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1461) oGrid.kl oGrid.kr 400 2000 ⟨false, 412019931538440573561628503212312493955211596448235664200504513393587206318⟩ ⟨false, 0⟩ ⟨false, 611225092150363781466626172471112188408763138409860055880230374298869357208⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1461_2400 : bothLoop evalE (oGrid.idx 1461) (oGrid.dm 1461) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1461) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 611225092150363781466626172471112188408763138409860055880230374298869357208⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1461 : oGrid.row evalE 1461 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1461_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1461_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1461_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1461_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1461_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1461_2000).1 (bothLoop_sound b_1461_2400).1))))))

theorem n_row_1461 : nGrid.row evalE 1461 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1461_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1461_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1461_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1461_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1461_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1461_2000).2 (bothLoop_sound b_1461_2400).2))))))

theorem b_1462_0 : bothSeg evalE (oGrid.idx 1462) (oGrid.dm 1462) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1462) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 42181349098387807358031248928537831762964419223599679877380955385248475768⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1462_400 : bothSeg evalE (oGrid.idx 1462) (oGrid.dm 1462) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1462) oGrid.kl oGrid.kr 400 400 ⟨false, 42181349098387807358031248928537831762964419223599679877380955385248475768⟩ ⟨false, 0⟩ ⟨false, 107367014186536708578184639978635426910768133922900376419800414102551847770⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1462_800 : bothSeg evalE (oGrid.idx 1462) (oGrid.dm 1462) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1462) oGrid.kl oGrid.kr 400 800 ⟨false, 107367014186536708578184639978635426910768133922900376419800414102551847770⟩ ⟨false, 0⟩ ⟨false, 167427212990203912393668837742699320829617779545833225486233006232085572640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1462_1200 : bothSeg evalE (oGrid.idx 1462) (oGrid.dm 1462) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1462) oGrid.kl oGrid.kr 400 1200 ⟨false, 167427212990203912393668837742699320829617779545833225486233006232085572640⟩ ⟨false, 0⟩ ⟨false, 264246467485306693384185577447349356638021116519039897948975021337237139590⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1462_1600 : bothSeg evalE (oGrid.idx 1462) (oGrid.dm 1462) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1462) oGrid.kl oGrid.kr 400 1600 ⟨false, 264246467485306693384185577447349356638021116519039897948975021337237139590⟩ ⟨false, 0⟩ ⟨false, 413406850069279406129317063796574359731238777593590875431120045424590582764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1462_2000 : bothSeg evalE (oGrid.idx 1462) (oGrid.dm 1462) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1462) oGrid.kl oGrid.kr 400 2000 ⟨false, 413406850069279406129317063796574359731238777593590875431120045424590582764⟩ ⟨false, 0⟩ ⟨false, 612848271556290393775906206348256259248001543956591893473945805651090128544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1462_2400 : bothLoop evalE (oGrid.idx 1462) (oGrid.dm 1462) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1462) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 612848271556290393775906206348256259248001543956591893473945805651090128544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1462 : oGrid.row evalE 1462 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1462_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1462_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1462_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1462_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1462_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1462_2000).1 (bothLoop_sound b_1462_2400).1))))))

theorem n_row_1462 : nGrid.row evalE 1462 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1462_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1462_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1462_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1462_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1462_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1462_2000).2 (bothLoop_sound b_1462_2400).2))))))

theorem b_1463_0 : bothSeg evalE (oGrid.idx 1463) (oGrid.dm 1463) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1463) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 42643209149276715123436193529397670802048253954064654959134729238354460526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1463_400 : bothSeg evalE (oGrid.idx 1463) (oGrid.dm 1463) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1463) oGrid.kl oGrid.kr 400 400 ⟨false, 42643209149276715123436193529397670802048253954064654959134729238354460526⟩ ⟨false, 0⟩ ⟨false, 108171185819570127428765546615141127159615974529854842185533144142396501060⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1463_800 : bothSeg evalE (oGrid.idx 1463) (oGrid.dm 1463) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1463) oGrid.kl oGrid.kr 400 800 ⟨false, 108171185819570127428765546615141127159615974529854842185533144142396501060⟩ ⟨false, 0⟩ ⟨false, 168237452859393105041534673518986288435884000287344894122289678540374594334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1463_1200 : bothSeg evalE (oGrid.idx 1463) (oGrid.dm 1463) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1463) oGrid.kl oGrid.kr 400 1200 ⟨false, 168237452859393105041534673518986288435884000287344894122289678540374594334⟩ ⟨false, 0⟩ ⟨false, 265364095656707619437709068501576500926555383012140577370009630176392668506⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1463_1600 : bothSeg evalE (oGrid.idx 1463) (oGrid.dm 1463) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1463) oGrid.kl oGrid.kr 400 1600 ⟨false, 265364095656707619437709068501576500926555383012140577370009630176392668506⟩ ⟨false, 0⟩ ⟨false, 414792100680424262263074566227477208504741636926926656535108077952900704154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1463_2000 : bothSeg evalE (oGrid.idx 1463) (oGrid.dm 1463) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1463) oGrid.kl oGrid.kr 400 2000 ⟨false, 414792100680424262263074566227477208504741636926926656535108077952900704154⟩ ⟨false, 0⟩ ⟨false, 614469816908181527317701703013893834602615480428997987452908757289393898468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1463_2400 : bothLoop evalE (oGrid.idx 1463) (oGrid.dm 1463) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1463) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 614469816908181527317701703013893834602615480428997987452908757289393898468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1463 : oGrid.row evalE 1463 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1463_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1463_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1463_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1463_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1463_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1463_2000).1 (bothLoop_sound b_1463_2400).1))))))

theorem n_row_1463 : nGrid.row evalE 1463 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1463_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1463_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1463_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1463_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1463_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1463_2000).2 (bothLoop_sound b_1463_2400).2))))))

theorem o_blk_1440 : allFrom (fun j => oGrid.row evalE j) 1440 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1440) o_row_1440 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1441) o_row_1441 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1442) o_row_1442 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1443) o_row_1443 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1444) o_row_1444 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1445) o_row_1445 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1446) o_row_1446 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1447) o_row_1447 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1448) o_row_1448 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1449) o_row_1449 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1450) o_row_1450 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1451) o_row_1451 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1452) o_row_1452 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1453) o_row_1453 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1454) o_row_1454 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1455) o_row_1455 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1456) o_row_1456 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1457) o_row_1457 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1458) o_row_1458 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1459) o_row_1459 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1460) o_row_1460 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1461) o_row_1461 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1462) o_row_1462 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1463) o_row_1463 (allFrom_zero (fun j => oGrid.row evalE j) 1464)))))))))))))))))))))))))

theorem n_blk_1440 : allFrom (fun j => nGrid.row evalE j) 1440 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1440) n_row_1440 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1441) n_row_1441 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1442) n_row_1442 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1443) n_row_1443 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1444) n_row_1444 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1445) n_row_1445 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1446) n_row_1446 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1447) n_row_1447 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1448) n_row_1448 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1449) n_row_1449 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1450) n_row_1450 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1451) n_row_1451 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1452) n_row_1452 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1453) n_row_1453 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1454) n_row_1454 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1455) n_row_1455 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1456) n_row_1456 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1457) n_row_1457 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1458) n_row_1458 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1459) n_row_1459 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1460) n_row_1460 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1461) n_row_1461 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1462) n_row_1462 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1463) n_row_1463 (allFrom_zero (fun j => nGrid.row evalE j) 1464)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
