/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 66 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1584`–`1607`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1584_0 : bothSeg evalE (oGrid.idx 1584) (oGrid.dm 1584) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1584) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 71065689372959942688781996825745792557630082328650297356309107239387951526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1584_400 : bothSeg evalE (oGrid.idx 1584) (oGrid.dm 1584) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1584) oGrid.kl oGrid.kr 400 400 ⟨false, 71065689372959942688781996825745792557630082328650297356309107239387951526⟩ ⟨false, 0⟩ ⟨false, 131981664692082046603481832276494403214339103476874073759850984152627766964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1584_800 : bothSeg evalE (oGrid.idx 1584) (oGrid.dm 1584) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1584) oGrid.kl oGrid.kr 400 800 ⟨false, 131981664692082046603481832276494403214339103476874073759850984152627766964⟩ ⟨false, 0⟩ ⟨false, 221897185438403927436848560234682154264372916778929213008256697703341265810⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1584_1200 : bothSeg evalE (oGrid.idx 1584) (oGrid.dm 1584) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1584) oGrid.kl oGrid.kr 400 1200 ⟨false, 221897185438403927436848560234682154264372916778929213008256697703341265810⟩ ⟨false, 0⟩ ⟨false, 356068095241080342288820466695038574208643626453904695508756397614118005436⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1584_1600 : bothSeg evalE (oGrid.idx 1584) (oGrid.dm 1584) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1584) oGrid.kl oGrid.kr 400 1600 ⟨false, 356068095241080342288820466695038574208643626453904695508756397614118005436⟩ ⟨false, 0⟩ ⟨false, 537974749930672076033144485398021230354365630498195570146372189030446808792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1584_2000 : bothSeg evalE (oGrid.idx 1584) (oGrid.dm 1584) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1584) oGrid.kl oGrid.kr 400 2000 ⟨false, 537974749930672076033144485398021230354365630498195570146372189030446808792⟩ ⟨false, 0⟩ ⟨false, 766475692966318072689039083947638951256065985075468908341860836503053607098⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1584_2400 : bothLoop evalE (oGrid.idx 1584) (oGrid.dm 1584) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1584) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 766475692966318072689039083947638951256065985075468908341860836503053607098⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1584 : oGrid.row evalE 1584 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1584_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1584_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1584_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1584_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1584_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1584_2000).1 (bothLoop_sound b_1584_2400).1))))))

theorem n_row_1584 : nGrid.row evalE 1584 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1584_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1584_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1584_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1584_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1584_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1584_2000).2 (bothLoop_sound b_1584_2400).2))))))

theorem b_1585_0 : bothSeg evalE (oGrid.idx 1585) (oGrid.dm 1585) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1585) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70697612688261122523678607462146775470313941830913368966679669337013980410⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1585_400 : bothSeg evalE (oGrid.idx 1585) (oGrid.dm 1585) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1585) oGrid.kl oGrid.kr 400 400 ⟨false, 70697612688261122523678607462146775470313941830913368966679669337013980410⟩ ⟨false, 0⟩ ⟨false, 131701019910057855061044394130708489254778163603605897920179063550568816384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1585_800 : bothSeg evalE (oGrid.idx 1585) (oGrid.dm 1585) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1585) oGrid.kl oGrid.kr 400 800 ⟨false, 131701019910057855061044394130708489254778163603605897920179063550568816384⟩ ⟨false, 0⟩ ⟨false, 221960324093950426730696836229612878773836314974683385376409278238876901858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1585_1200 : bothSeg evalE (oGrid.idx 1585) (oGrid.dm 1585) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1585) oGrid.kl oGrid.kr 400 1200 ⟨false, 221960324093950426730696836229612878773836314974683385376409278238876901858⟩ ⟨false, 0⟩ ⟨false, 356436075203539779073993851163055523435565323806473248699114528391608698712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1585_1600 : bothSeg evalE (oGrid.idx 1585) (oGrid.dm 1585) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1585) oGrid.kl oGrid.kr 400 1600 ⟨false, 356436075203539779073993851163055523435565323806473248699114528391608698712⟩ ⟨false, 0⟩ ⟨false, 538611805874054077885186255393856350732173243995348602392476395094966611674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1585_2000 : bothSeg evalE (oGrid.idx 1585) (oGrid.dm 1585) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1585) oGrid.kl oGrid.kr 400 2000 ⟨false, 538611805874054077885186255393856350732173243995348602392476395094966611674⟩ ⟨false, 0⟩ ⟨false, 767352725158802700356881314739181883289402865378163297597488131172265368942⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1585_2400 : bothLoop evalE (oGrid.idx 1585) (oGrid.dm 1585) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1585) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 767352725158802700356881314739181883289402865378163297597488131172265368942⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1585 : oGrid.row evalE 1585 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1585_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1585_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1585_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1585_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1585_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1585_2000).1 (bothLoop_sound b_1585_2400).1))))))

theorem n_row_1585 : nGrid.row evalE 1585 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1585_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1585_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1585_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1585_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1585_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1585_2000).2 (bothLoop_sound b_1585_2400).2))))))

theorem b_1586_0 : bothSeg evalE (oGrid.idx 1586) (oGrid.dm 1586) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1586) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70326205615819666791369239603706111263187110735144822274073041549604331442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1586_400 : bothSeg evalE (oGrid.idx 1586) (oGrid.dm 1586) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1586) oGrid.kl oGrid.kr 400 400 ⟨false, 70326205615819666791369239603706111263187110735144822274073041549604331442⟩ ⟨false, 0⟩ ⟨false, 131426185745693383777196859451289151216129031044983566349625925507790681896⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1586_800 : bothSeg evalE (oGrid.idx 1586) (oGrid.dm 1586) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1586) oGrid.kl oGrid.kr 400 800 ⟨false, 131426185745693383777196859451289151216129031044983566349625925507790681896⟩ ⟨false, 0⟩ ⟨false, 222029208318878421101973501137508916315052925085850405187162451754792222516⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1586_1200 : bothSeg evalE (oGrid.idx 1586) (oGrid.dm 1586) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1586) oGrid.kl oGrid.kr 400 1200 ⟨false, 222029208318878421101973501137508916315052925085850405187162451754792222516⟩ ⟨false, 0⟩ ⟨false, 356809778200181952983499304845462111900490751889625605450891623482795160290⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1586_1600 : bothSeg evalE (oGrid.idx 1586) (oGrid.dm 1586) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1586) oGrid.kl oGrid.kr 400 1600 ⟨false, 356809778200181952983499304845462111900490751889625605450891623482795160290⟩ ⟨false, 0⟩ ⟨false, 539254593483214021154520541941405794995497344754903780464586281975490234136⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1586_2000 : bothSeg evalE (oGrid.idx 1586) (oGrid.dm 1586) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1586) oGrid.kl oGrid.kr 400 2000 ⟨false, 539254593483214021154520541941405794995497344754903780464586281975490234136⟩ ⟨false, 0⟩ ⟨false, 768235515700761310225168318709748228167227548285912267125573709590419120394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1586_2400 : bothLoop evalE (oGrid.idx 1586) (oGrid.dm 1586) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1586) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 768235515700761310225168318709748228167227548285912267125573709590419120394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1586 : oGrid.row evalE 1586 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1586_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1586_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1586_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1586_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1586_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1586_2000).1 (bothLoop_sound b_1586_2400).1))))))

theorem n_row_1586 : nGrid.row evalE 1586 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1586_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1586_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1586_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1586_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1586_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1586_2000).2 (bothLoop_sound b_1586_2400).2))))))

theorem b_1587_0 : bothSeg evalE (oGrid.idx 1587) (oGrid.dm 1587) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1587) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69952107435923788244614316319173094807435530650674368915636274159985076932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1587_400 : bothSeg evalE (oGrid.idx 1587) (oGrid.dm 1587) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1587) oGrid.kl oGrid.kr 400 400 ⟨false, 69952107435923788244614316319173094807435530650674368915636274159985076932⟩ ⟨false, 0⟩ ⟨false, 131157725329197539231016418943974259012628918659416021067725662966590436076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1587_800 : bothSeg evalE (oGrid.idx 1587) (oGrid.dm 1587) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1587) oGrid.kl oGrid.kr 400 800 ⟨false, 131157725329197539231016418943974259012628918659416021067725662966590436076⟩ ⟨false, 0⟩ ⟨false, 222104401273205198062052750943551039616232618474749626410083408810242711468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1587_1200 : bothSeg evalE (oGrid.idx 1587) (oGrid.dm 1587) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1587) oGrid.kl oGrid.kr 400 1200 ⟨false, 222104401273205198062052750943551039616232618474749626410083408810242711468⟩ ⟨false, 0⟩ ⟨false, 357189767367805069092669325481490560562854749603116614294269705561393437816⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1587_1600 : bothSeg evalE (oGrid.idx 1587) (oGrid.dm 1587) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1587) oGrid.kl oGrid.kr 400 1600 ⟨false, 357189767367805069092669325481490560562854749603116614294269705561393437816⟩ ⟨false, 0⟩ ⟨false, 539903675845660603290483500413547346686395196373119172384805548477229729702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1587_2000 : bothSeg evalE (oGrid.idx 1587) (oGrid.dm 1587) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1587) oGrid.kl oGrid.kr 400 2000 ⟨false, 539903675845660603290483500413547346686395196373119172384805548477229729702⟩ ⟨false, 0⟩ ⟨false, 769124627626009929844377882378983042952432876499210999030151024164756449392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1587_2400 : bothLoop evalE (oGrid.idx 1587) (oGrid.dm 1587) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1587) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 769124627626009929844377882378983042952432876499210999030151024164756449392⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1587 : oGrid.row evalE 1587 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1587_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1587_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1587_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1587_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1587_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1587_2000).1 (bothLoop_sound b_1587_2400).1))))))

theorem n_row_1587 : nGrid.row evalE 1587 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1587_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1587_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1587_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1587_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1587_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1587_2000).2 (bothLoop_sound b_1587_2400).2))))))

theorem b_1588_0 : bothSeg evalE (oGrid.idx 1588) (oGrid.dm 1588) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1588) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69575956267299323399600578484314264826498034542038601796163194259040442580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1588_400 : bothSeg evalE (oGrid.idx 1588) (oGrid.dm 1588) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1588) oGrid.kl oGrid.kr 400 400 ⟨false, 69575956267299323399600578484314264826498034542038601796163194259040442580⟩ ⟨false, 0⟩ ⟨false, 130896208261222949281306368884625546576702547977959482954544920086300408900⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1588_800 : bothSeg evalE (oGrid.idx 1588) (oGrid.dm 1588) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1588) oGrid.kl oGrid.kr 400 800 ⟨false, 130896208261222949281306368884625546576702547977959482954544920086300408900⟩ ⟨false, 0⟩ ⟨false, 222186472587406585954493663933888533238707450442931426561885925765939090084⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1588_1200 : bothSeg evalE (oGrid.idx 1588) (oGrid.dm 1588) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1588) oGrid.kl oGrid.kr 400 1200 ⟨false, 222186472587406585954493663933888533238707450442931426561885925765939090084⟩ ⟨false, 0⟩ ⟨false, 357576612313749884165280259096233766357426322946146296721340297826611584700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1588_1600 : bothSeg evalE (oGrid.idx 1588) (oGrid.dm 1588) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1588) oGrid.kl oGrid.kr 400 1600 ⟨false, 357576612313749884165280259096233766357426322946146296721340297826611584700⟩ ⟨false, 0⟩ ⟨false, 540559622519539009304212786753777463708984247445707788133737468427397853958⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1588_2000 : bothSeg evalE (oGrid.idx 1588) (oGrid.dm 1588) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1588) oGrid.kl oGrid.kr 400 2000 ⟨false, 540559622519539009304212786753777463708984247445707788133737468427397853958⟩ ⟨false, 0⟩ ⟨false, 770020630439073574284522813165000056531147314074653956217843178552866394340⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1588_2400 : bothLoop evalE (oGrid.idx 1588) (oGrid.dm 1588) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1588) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 770020630439073574284522813165000056531147314074653956217843178552866394340⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1588 : oGrid.row evalE 1588 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1588_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1588_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1588_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1588_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1588_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1588_2000).1 (bothLoop_sound b_1588_2400).1))))))

theorem n_row_1588 : nGrid.row evalE 1588 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1588_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1588_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1588_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1588_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1588_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1588_2000).2 (bothLoop_sound b_1588_2400).2))))))

theorem b_1589_0 : bothSeg evalE (oGrid.idx 1589) (oGrid.dm 1589) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1589) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69198399247075352746194291560048704493157500773394891860336819861833417388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1589_400 : bothSeg evalE (oGrid.idx 1589) (oGrid.dm 1589) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1589) oGrid.kl oGrid.kr 400 400 ⟨false, 69198399247075352746194291560048704493157500773394891860336819861833417388⟩ ⟨false, 0⟩ ⟨false, 130642202126372022602993273511318729485157063243418194940245678289670840876⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1589_800 : bothSeg evalE (oGrid.idx 1589) (oGrid.dm 1589) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1589) oGrid.kl oGrid.kr 400 800 ⟨false, 130642202126372022602993273511318729485157063243418194940245678289670840876⟩ ⟨false, 0⟩ ⟨false, 222275989875922894914813697528526225082976477901005567203394004106355248130⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1589_1200 : bothSeg evalE (oGrid.idx 1589) (oGrid.dm 1589) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1589) oGrid.kl oGrid.kr 400 1200 ⟨false, 222275989875922894914813697528526225082976477901005567203394004106355248130⟩ ⟨false, 0⟩ ⟨false, 357970880629405449297973311540564872125181228412202146425092286333922346220⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1589_1600 : bothSeg evalE (oGrid.idx 1589) (oGrid.dm 1589) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1589) oGrid.kl oGrid.kr 400 1600 ⟨false, 357970880629405449297973311540564872125181228412202146425092286333922346220⟩ ⟨false, 0⟩ ⟨false, 541223001047136501439487336272521909171667034291248955381625989847231003972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1589_2000 : bothSeg evalE (oGrid.idx 1589) (oGrid.dm 1589) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1589) oGrid.kl oGrid.kr 400 2000 ⟨false, 541223001047136501439487336272521909171667034291248955381625989847231003972⟩ ⟨false, 0⟩ ⟨false, 770924091628691758368060384719288368138649527952403991409454575966992589394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1589_2400 : bothLoop evalE (oGrid.idx 1589) (oGrid.dm 1589) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1589) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 770924091628691758368060384719288368138649527952403991409454575966992589394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1589 : oGrid.row evalE 1589 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1589_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1589_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1589_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1589_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1589_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1589_2000).1 (bothLoop_sound b_1589_2400).1))))))

theorem n_row_1589 : nGrid.row evalE 1589 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1589_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1589_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1589_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1589_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1589_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1589_2000).2 (bothLoop_sound b_1589_2400).2))))))

theorem b_1590_0 : bothSeg evalE (oGrid.idx 1590) (oGrid.dm 1590) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1590) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 68820085476100152871702678652564748196836746099088604421942356954603174126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1590_400 : bothSeg evalE (oGrid.idx 1590) (oGrid.dm 1590) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1590) oGrid.kl oGrid.kr 400 400 ⟨false, 68820085476100152871702678652564748196836746099088604421942356954603174126⟩ ⟨false, 0⟩ ⟨false, 130396269140260682001315533964354021884937786955427259354174584811726183676⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1590_800 : bothSeg evalE (oGrid.idx 1590) (oGrid.dm 1590) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1590) oGrid.kl oGrid.kr 400 800 ⟨false, 130396269140260682001315533964354021884937786955427259354174584811726183676⟩ ⟨false, 0⟩ ⟨false, 222373515384222532117048734243984884235224543286291631334864657268093588544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1590_1200 : bothSeg evalE (oGrid.idx 1590) (oGrid.dm 1590) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1590) oGrid.kl oGrid.kr 400 1200 ⟨false, 222373515384222532117048734243984884235224543286291631334864657268093588544⟩ ⟨false, 0⟩ ⟨false, 358373134537272527284055847790199742098326485175038984717529323397802707782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1590_1600 : bothSeg evalE (oGrid.idx 1590) (oGrid.dm 1590) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1590) oGrid.kl oGrid.kr 400 1600 ⟨false, 358373134537272527284055847790199742098326485175038984717529323397802707782⟩ ⟨false, 0⟩ ⟨false, 541894373601945683776827678085648483053034563850913856158444118839230454468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1590_2000 : bothSeg evalE (oGrid.idx 1590) (oGrid.dm 1590) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1590) oGrid.kl oGrid.kr 400 2000 ⟨false, 541894373601945683776827678085648483053034563850913856158444118839230454468⟩ ⟨false, 0⟩ ⟨false, 771835573314881683868146585088238916497270632919720020410832556872994571488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1590_2400 : bothLoop evalE (oGrid.idx 1590) (oGrid.dm 1590) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1590) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 771835573314881683868146585088238916497270632919720020410832556872994571488⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1590 : oGrid.row evalE 1590 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1590_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1590_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1590_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1590_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1590_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1590_2000).1 (bothLoop_sound b_1590_2400).1))))))

theorem n_row_1590 : nGrid.row evalE 1590 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1590_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1590_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1590_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1590_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1590_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1590_2000).2 (bothLoop_sound b_1590_2400).2))))))

theorem b_1591_0 : bothSeg evalE (oGrid.idx 1591) (oGrid.dm 1591) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1591) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 68441661947721366351729659496980808453970550238385439192775985239533018384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1591_400 : bothSeg evalE (oGrid.idx 1591) (oGrid.dm 1591) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1591) oGrid.kl oGrid.kr 400 400 ⟨false, 68441661947721366351729659496980808453970550238385439192775985239533018384⟩ ⟨false, 0⟩ ⟨false, 130158955465200765776710337419739416557246998392989531004255659793019244986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1591_800 : bothSeg evalE (oGrid.idx 1591) (oGrid.dm 1591) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1591) oGrid.kl oGrid.kr 400 800 ⟨false, 130158955465200765776710337419739416557246998392989531004255659793019244986⟩ ⟨false, 0⟩ ⟨false, 222479595304484285478734536703228174542928635844682845929363595748959200684⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1591_1200 : bothSeg evalE (oGrid.idx 1591) (oGrid.dm 1591) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1591) oGrid.kl oGrid.kr 400 1200 ⟨false, 222479595304484285478734536703228174542928635844682845929363595748959200684⟩ ⟨false, 0⟩ ⟨false, 358783920206645678867421153615043919766021815227917620802851565179485528572⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1591_1600 : bothSeg evalE (oGrid.idx 1591) (oGrid.dm 1591) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1591) oGrid.kl oGrid.kr 400 1600 ⟨false, 358783920206645678867421153615043919766021815227917620802851565179485528572⟩ ⟨false, 0⟩ ⟨false, 542574286304346435941420107309609702244977472987814261470395473662312220344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1591_2000 : bothSeg evalE (oGrid.idx 1591) (oGrid.dm 1591) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1591) oGrid.kl oGrid.kr 400 2000 ⟨false, 542574286304346435941420107309609702244977472987814261470395473662312220344⟩ ⟨false, 0⟩ ⟨false, 772755621564620095842968344889804144724074739000818489303059179850050701518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1591_2400 : bothLoop evalE (oGrid.idx 1591) (oGrid.dm 1591) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1591) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 772755621564620095842968344889804144724074739000818489303059179850050701518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1591 : oGrid.row evalE 1591 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1591_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1591_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1591_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1591_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1591_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1591_2000).1 (bothLoop_sound b_1591_2400).1))))))

theorem n_row_1591 : nGrid.row evalE 1591 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1591_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1591_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1591_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1591_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1591_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1591_2000).2 (bothLoop_sound b_1591_2400).2))))))

theorem b_1592_0 : bothSeg evalE (oGrid.idx 1592) (oGrid.dm 1592) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1592) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 68063777369206245658627445198102464967567999556226275856975702135893305952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1592_400 : bothSeg evalE (oGrid.idx 1592) (oGrid.dm 1592) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1592) oGrid.kl oGrid.kr 400 400 ⟨false, 68063777369206245658627445198102464967567999556226275856975702135893305952⟩ ⟨false, 0⟩ ⟨false, 129930809560477376419217586745890078973964428543571119243817031979351052580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1592_800 : bothSeg evalE (oGrid.idx 1592) (oGrid.dm 1592) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1592) oGrid.kl oGrid.kr 400 800 ⟨false, 129930809560477376419217586745890078973964428543571119243817031979351052580⟩ ⟨false, 0⟩ ⟨false, 222594778125874555101860008999156939404812633180336427684103030661701182700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1592_1200 : bothSeg evalE (oGrid.idx 1592) (oGrid.dm 1592) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1592) oGrid.kl oGrid.kr 400 1200 ⟨false, 222594778125874555101860008999156939404812633180336427684103030661701182700⟩ ⟨false, 0⟩ ⟨false, 359203786103890297163242018777426134411053591329454126012893376310738270874⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1592_1600 : bothSeg evalE (oGrid.idx 1592) (oGrid.dm 1592) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1592) oGrid.kl oGrid.kr 400 1600 ⟨false, 359203786103890297163242018777426134411053591329454126012893376310738270874⟩ ⟨false, 0⟩ ⟨false, 543263287571882795191344815890281373360199960157993573635607224549752434860⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1592_2000 : bothSeg evalE (oGrid.idx 1592) (oGrid.dm 1592) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1592) oGrid.kl oGrid.kr 400 2000 ⟨false, 543263287571882795191344815890281373360199960157993573635607224549752434860⟩ ⟨false, 0⟩ ⟨false, 773684784742120087382802919275040531369189784966810502316760059456701791106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1592_2400 : bothLoop evalE (oGrid.idx 1592) (oGrid.dm 1592) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1592) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 773684784742120087382802919275040531369189784966810502316760059456701791106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1592 : oGrid.row evalE 1592 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1592_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1592_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1592_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1592_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1592_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1592_2000).1 (bothLoop_sound b_1592_2400).1))))))

theorem n_row_1592 : nGrid.row evalE 1592 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1592_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1592_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1592_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1592_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1592_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1592_2000).2 (bothLoop_sound b_1592_2400).2))))))

theorem b_1593_0 : bothSeg evalE (oGrid.idx 1593) (oGrid.dm 1593) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1593) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 67687081043796655194454588201145152994502798474698449880605150687745987542⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1593_400 : bothSeg evalE (oGrid.idx 1593) (oGrid.dm 1593) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1593) oGrid.kl oGrid.kr 400 400 ⟨false, 67687081043796655194454588201145152994502798474698449880605150687745987542⟩ ⟨false, 0⟩ ⟨false, 129712373016851965170518268408152450321831748208876955225104983800041712428⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1593_800 : bothSeg evalE (oGrid.idx 1593) (oGrid.dm 1593) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1593) oGrid.kl oGrid.kr 400 800 ⟨false, 129712373016851965170518268408152450321831748208876955225104983800041712428⟩ ⟨false, 0⟩ ⟨false, 222719605469050320986645417734269068711544140071141828834317867479071757318⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1593_1200 : bothSeg evalE (oGrid.idx 1593) (oGrid.dm 1593) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1593) oGrid.kl oGrid.kr 400 1200 ⟨false, 222719605469050320986645417734269068711544140071141828834317867479071757318⟩ ⟨false, 0⟩ ⟨false, 359633273826945378781397902224998099554682703357322619323429505502482006562⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1593_1600 : bothSeg evalE (oGrid.idx 1593) (oGrid.dm 1593) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1593) oGrid.kl oGrid.kr 400 1600 ⟨false, 359633273826945378781397902224998099554682703357322619323429505502482006562⟩ ⟨false, 0⟩ ⟨false, 543961918953765575421892081588335950291208825250011099398689162391826322008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1593_2000 : bothSeg evalE (oGrid.idx 1593) (oGrid.dm 1593) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1593) oGrid.kl oGrid.kr 400 2000 ⟨false, 543961918953765575421892081588335950291208825250011099398689162391826322008⟩ ⟨false, 0⟩ ⟨false, 774623604343333641305756816149819862048006280190866617522342862916897202640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1593_2400 : bothLoop evalE (oGrid.idx 1593) (oGrid.dm 1593) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1593) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 774623604343333641305756816149819862048006280190866617522342862916897202640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1593 : oGrid.row evalE 1593 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1593_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1593_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1593_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1593_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1593_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1593_2000).1 (bothLoop_sound b_1593_2400).1))))))

theorem n_row_1593 : nGrid.row evalE 1593 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1593_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1593_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1593_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1593_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1593_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1593_2000).2 (bothLoop_sound b_1593_2400).2))))))

theorem b_1594_0 : bothSeg evalE (oGrid.idx 1594) (oGrid.dm 1594) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1594) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 67312218783474690754447058675059365249657455188480463334677237004590530992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1594_400 : bothSeg evalE (oGrid.idx 1594) (oGrid.dm 1594) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1594) oGrid.kl oGrid.kr 400 400 ⟨false, 67312218783474690754447058675059365249657455188480463334677237004590530992⟩ ⟨false, 0⟩ ⟨false, 129504161789108125075825519682925598726523577814192484787904022712015933328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1594_800 : bothSeg evalE (oGrid.idx 1594) (oGrid.dm 1594) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1594) oGrid.kl oGrid.kr 400 800 ⟨false, 129504161789108125075825519682925598726523577814192484787904022712015933328⟩ ⟨false, 0⟩ ⟨false, 222854593318704819639103415971636916891533614051596119524052299780478915576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1594_1200 : bothSeg evalE (oGrid.idx 1594) (oGrid.dm 1594) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1594) oGrid.kl oGrid.kr 400 1200 ⟨false, 222854593318704819639103415971636916891533614051596119524052299780478915576⟩ ⟨false, 0⟩ ⟨false, 360072899337869004272701773075002211418262023837384354514099911483221890228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1594_1600 : bothSeg evalE (oGrid.idx 1594) (oGrid.dm 1594) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1594) oGrid.kl oGrid.kr 400 1600 ⟨false, 360072899337869004272701773075002211418262023837384354514099911483221890228⟩ ⟨false, 0⟩ ⟨false, 544670696363417695705856548423942507526355616754724099235826378830270459626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1594_2000 : bothSeg evalE (oGrid.idx 1594) (oGrid.dm 1594) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1594) oGrid.kl oGrid.kr 400 2000 ⟨false, 544670696363417695705856548423942507526355616754724099235826378830270459626⟩ ⟨false, 0⟩ ⟨false, 775572596228496881422241819208377874147734376606008127204396853108739535456⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1594_2400 : bothLoop evalE (oGrid.idx 1594) (oGrid.dm 1594) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1594) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 775572596228496881422241819208377874147734376606008127204396853108739535456⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1594 : oGrid.row evalE 1594 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1594_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1594_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1594_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1594_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1594_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1594_2000).1 (bothLoop_sound b_1594_2400).1))))))

theorem n_row_1594 : nGrid.row evalE 1594 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1594_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1594_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1594_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1594_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1594_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1594_2000).2 (bothLoop_sound b_1594_2400).2))))))

theorem b_1595_0 : bothSeg evalE (oGrid.idx 1595) (oGrid.dm 1595) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1595) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66939828886574341463558496385267302579659103634916610753765647374677694016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1595_400 : bothSeg evalE (oGrid.idx 1595) (oGrid.dm 1595) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1595) oGrid.kl oGrid.kr 400 400 ⟨false, 66939828886574341463558496385267302579659103634916610753765647374677694016⟩ ⟨false, 0⟩ ⟨false, 129306691317958456616524718567857774865930110342873612975897435534549954790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1595_800 : bothSeg evalE (oGrid.idx 1595) (oGrid.dm 1595) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1595) oGrid.kl oGrid.kr 400 800 ⟨false, 129306691317958456616524718567857774865930110342873612975897435534549954790⟩ ⟨false, 0⟩ ⟨false, 223000257145474293662022650223439282851924026881657368562190779596582820132⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1595_1200 : bothSeg evalE (oGrid.idx 1595) (oGrid.dm 1595) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1595) oGrid.kl oGrid.kr 400 1200 ⟨false, 223000257145474293662022650223439282851924026881657368562190779596582820132⟩ ⟨false, 0⟩ ⟨false, 360523178084744891986676299618862998498880841353701068227476092908259852344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1595_1600 : bothSeg evalE (oGrid.idx 1595) (oGrid.dm 1595) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1595) oGrid.kl oGrid.kr 400 1600 ⟨false, 360523178084744891986676299618862998498880841353701068227476092908259852344⟩ ⟨false, 0⟩ ⟨false, 545390135200380582458382813862367006959552391282633511705661254711224360782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1595_2000 : bothSeg evalE (oGrid.idx 1595) (oGrid.dm 1595) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1595) oGrid.kl oGrid.kr 400 2000 ⟨false, 545390135200380582458382813862367006959552391282633511705661254711224360782⟩ ⟨false, 0⟩ ⟨false, 776532275744036397456928060837750879294846542929660836661652973741326345746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1595_2400 : bothLoop evalE (oGrid.idx 1595) (oGrid.dm 1595) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1595) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 776532275744036397456928060837750879294846542929660836661652973741326345746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1595 : oGrid.row evalE 1595 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1595_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1595_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1595_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1595_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1595_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1595_2000).1 (bothLoop_sound b_1595_2400).1))))))

theorem n_row_1595 : nGrid.row evalE 1595 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1595_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1595_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1595_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1595_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1595_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1595_2000).2 (bothLoop_sound b_1595_2400).2))))))

theorem b_1596_0 : bothSeg evalE (oGrid.idx 1596) (oGrid.dm 1596) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1596) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66570550260530751958095961187282190913603763287621435955604944608463243814⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1596_400 : bothSeg evalE (oGrid.idx 1596) (oGrid.dm 1596) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1596) oGrid.kl oGrid.kr 400 400 ⟨false, 66570550260530751958095961187282190913603763287621435955604944608463243814⟩ ⟨false, 0⟩ ⟨false, 129120465854450788455643313150795810074327207973648644845766633682563192256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1596_800 : bothSeg evalE (oGrid.idx 1596) (oGrid.dm 1596) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1596) oGrid.kl oGrid.kr 400 800 ⟨false, 129120465854450788455643313150795810074327207973648644845766633682563192256⟩ ⟨false, 0⟩ ⟨false, 223157101230344096860201986573777152383130023086651685040490471841064097412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1596_1200 : bothSeg evalE (oGrid.idx 1596) (oGrid.dm 1596) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1596) oGrid.kl oGrid.kr 400 1200 ⟨false, 223157101230344096860201986573777152383130023086651685040490471841064097412⟩ ⟨false, 0⟩ ⟨false, 360984614326088307870818954205885925707402265428434955682962612718060220762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1596_1600 : bothSeg evalE (oGrid.idx 1596) (oGrid.dm 1596) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1596) oGrid.kl oGrid.kr 400 1600 ⟨false, 360984614326088307870818954205885925707402265428434955682962612718060220762⟩ ⟨false, 0⟩ ⟨false, 546120739674719927756125040283001664389372944271001455350129201179651282448⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1596_2000 : bothSeg evalE (oGrid.idx 1596) (oGrid.dm 1596) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1596) oGrid.kl oGrid.kr 400 2000 ⟨false, 546120739674719927756125040283001664389372944271001455350129201179651282448⟩ ⟨false, 0⟩ ⟨false, 777503147046974926158102828969382634769343990871938727236738626047708961540⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1596_2400 : bothLoop evalE (oGrid.idx 1596) (oGrid.dm 1596) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1596) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 777503147046974926158102828969382634769343990871938727236738626047708961540⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1596 : oGrid.row evalE 1596 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1596_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1596_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1596_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1596_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1596_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1596_2000).1 (bothLoop_sound b_1596_2400).1))))))

theorem n_row_1596 : nGrid.row evalE 1596 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1596_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1596_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1596_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1596_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1596_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1596_2000).2 (bothLoop_sound b_1596_2400).2))))))

theorem b_1597_0 : bothSeg evalE (oGrid.idx 1597) (oGrid.dm 1597) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1597) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66205011069444892508605077758077265076533984547498304746865825708141598330⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1597_400 : bothSeg evalE (oGrid.idx 1597) (oGrid.dm 1597) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1597) oGrid.kl oGrid.kr 400 400 ⟨false, 66205011069444892508605077758077265076533984547498304746865825708141598330⟩ ⟨false, 0⟩ ⟨false, 128945971732878947392377600399228959545388397848612174373024302180807760960⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1597_800 : bothSeg evalE (oGrid.idx 1597) (oGrid.dm 1597) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1597) oGrid.kl oGrid.kr 400 800 ⟨false, 128945971732878947392377600399228959545388397848612174373024302180807760960⟩ ⟨false, 0⟩ ⟨false, 223325611937559348954913735890585747491964389248571467810672323416971406906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1597_1200 : bothSeg evalE (oGrid.idx 1597) (oGrid.dm 1597) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1597) oGrid.kl oGrid.kr 400 1200 ⟨false, 223325611937559348954913735890585747491964389248571467810672323416971406906⟩ ⟨false, 0⟩ ⟨false, 361457694403756525305447583495849583967393545905957122580455877962374745674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1597_1600 : bothSeg evalE (oGrid.idx 1597) (oGrid.dm 1597) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1597) oGrid.kl oGrid.kr 400 1600 ⟨false, 361457694403756525305447583495849583967393545905957122580455877962374745674⟩ ⟨false, 0⟩ ⟨false, 546862996079935997904634899608227412883441346679175457913483465536029942160⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1597_2000 : bothSeg evalE (oGrid.idx 1597) (oGrid.dm 1597) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1597) oGrid.kl oGrid.kr 400 2000 ⟨false, 546862996079935997904634899608227412883441346679175457913483465536029942160⟩ ⟨false, 0⟩ ⟨false, 778485696377841582688514612267520347974187012282784295523863125900136753874⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1597_2400 : bothLoop evalE (oGrid.idx 1597) (oGrid.dm 1597) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1597) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 778485696377841582688514612267520347974187012282784295523863125900136753874⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1597 : oGrid.row evalE 1597 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1597_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1597_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1597_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1597_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1597_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1597_2000).1 (bothLoop_sound b_1597_2400).1))))))

theorem n_row_1597 : nGrid.row evalE 1597 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1597_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1597_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1597_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1597_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1597_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1597_2000).2 (bothLoop_sound b_1597_2400).2))))))

theorem b_1598_0 : bothSeg evalE (oGrid.idx 1598) (oGrid.dm 1598) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1598) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65843833874161041086600003701155934030234024525925964865656407643847561356⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1598_400 : bothSeg evalE (oGrid.idx 1598) (oGrid.dm 1598) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1598) oGrid.kl oGrid.kr 400 400 ⟨false, 65843833874161041086600003701155934030234024525925964865656407643847561356⟩ ⟨false, 0⟩ ⟨false, 128783687826831181838275624217574024245075743421161216274849985598138545690⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1598_800 : bothSeg evalE (oGrid.idx 1598) (oGrid.dm 1598) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1598) oGrid.kl oGrid.kr 400 800 ⟨false, 128783687826831181838275624217574024245075743421161216274849985598138545690⟩ ⟨false, 0⟩ ⟨false, 223506268170673244218950056727512168248966616597895525551288074470107043094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1598_1200 : bothSeg evalE (oGrid.idx 1598) (oGrid.dm 1598) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1598) oGrid.kl oGrid.kr 400 1200 ⟨false, 223506268170673244218950056727512168248966616597895525551288074470107043094⟩ ⟨false, 0⟩ ⟨false, 361942897198996939284595428098305380984556754859942434005670783888379806744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1598_1600 : bothSeg evalE (oGrid.idx 1598) (oGrid.dm 1598) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1598) oGrid.kl oGrid.kr 400 1600 ⟨false, 361942897198996939284595428098305380984556754859942434005670783888379806744⟩ ⟨false, 0⟩ ⟨false, 547617383249011596564269207258347600793018842886825802681048343944721046840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1598_2000 : bothSeg evalE (oGrid.idx 1598) (oGrid.dm 1598) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1598) oGrid.kl oGrid.kr 400 2000 ⟨false, 547617383249011596564269207258347600793018842886825802681048343944721046840⟩ ⟨false, 0⟩ ⟨false, 779480402516719746608158166532010036986635896644935772050394118205682085104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1598_2400 : bothLoop evalE (oGrid.idx 1598) (oGrid.dm 1598) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1598) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 779480402516719746608158166532010036986635896644935772050394118205682085104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1598 : oGrid.row evalE 1598 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1598_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1598_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1598_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1598_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1598_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1598_2000).1 (bothLoop_sound b_1598_2400).1))))))

theorem n_row_1598 : nGrid.row evalE 1598 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1598_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1598_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1598_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1598_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1598_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1598_2000).2 (bothLoop_sound b_1598_2400).2))))))

theorem b_1599_0 : bothSeg evalE (oGrid.idx 1599) (oGrid.dm 1599) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1599) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65487633885304201557638303175299924186063476172178816692190210394206026364⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1599_400 : bothSeg evalE (oGrid.idx 1599) (oGrid.dm 1599) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1599) oGrid.kl oGrid.kr 400 400 ⟨false, 65487633885304201557638303175299924186063476172178816692190210394206026364⟩ ⟨false, 0⟩ ⟨false, 128634075841971366684427157304928737979747832051920440767478752905165047328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1599_800 : bothSeg evalE (oGrid.idx 1599) (oGrid.dm 1599) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1599) oGrid.kl oGrid.kr 400 800 ⟨false, 128634075841971366684427157304928737979747832051920440767478752905165047328⟩ ⟨false, 0⟩ ⟨false, 223699531665328141900362336100388508754519368121296167151719519978036961706⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1599_1200 : bothSeg evalE (oGrid.idx 1599) (oGrid.dm 1599) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1599) oGrid.kl oGrid.kr 400 1200 ⟨false, 223699531665328141900362336100388508754519368121296167151719519978036961706⟩ ⟨false, 0⟩ ⟨false, 362440684425227962810181831186703063273219330729118278631924009709182012106⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1599_1600 : bothSeg evalE (oGrid.idx 1599) (oGrid.dm 1599) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1599) oGrid.kl oGrid.kr 400 1600 ⟨false, 362440684425227962810181831186703063273219330729118278631924009709182012106⟩ ⟨false, 0⟩ ⟨false, 548384362847192810301665472977104711598841145249748957516042250550247161438⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1599_2000 : bothSeg evalE (oGrid.idx 1599) (oGrid.dm 1599) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1599) oGrid.kl oGrid.kr 400 2000 ⟨false, 548384362847192810301665472977104711598841145249748957516042250550247161438⟩ ⟨false, 0⟩ ⟨false, 780487727076027730316212489983741446472440667119050292257338729609257405242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1599_2400 : bothLoop evalE (oGrid.idx 1599) (oGrid.dm 1599) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1599) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 780487727076027730316212489983741446472440667119050292257338729609257405242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1599 : oGrid.row evalE 1599 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1599_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1599_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1599_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1599_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1599_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1599_2000).1 (bothLoop_sound b_1599_2400).1))))))

theorem n_row_1599 : nGrid.row evalE 1599 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1599_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1599_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1599_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1599_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1599_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1599_2000).2 (bothLoop_sound b_1599_2400).2))))))

theorem b_1600_0 : bothSeg evalE (oGrid.idx 1600) (oGrid.dm 1600) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1600) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65137012459468084974461781294113003712030316878448053040562303641295299672⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1600_400 : bothSeg evalE (oGrid.idx 1600) (oGrid.dm 1600) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1600) oGrid.kl oGrid.kr 400 400 ⟨false, 65137012459468084974461781294113003712030316878448053040562303641295299672⟩ ⟨false, 0⟩ ⟨false, 128497585425013144541810336750261514075120545841689349555032615139996169082⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1600_800 : bothSeg evalE (oGrid.idx 1600) (oGrid.dm 1600) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1600) oGrid.kl oGrid.kr 400 800 ⟨false, 128497585425013144541810336750261514075120545841689349555032615139996169082⟩ ⟨false, 0⟩ ⟨false, 223905852098229593415805768800269415753215549370932402645097164416609338190⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1600_1200 : bothSeg evalE (oGrid.idx 1600) (oGrid.dm 1600) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1600) oGrid.kl oGrid.kr 400 1200 ⟨false, 223905852098229593415805768800269415753215549370932402645097164416609338190⟩ ⟨false, 0⟩ ⟨false, 362951505737012860479488928239486347581221791090382848606709151094084875928⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1600_1600 : bothSeg evalE (oGrid.idx 1600) (oGrid.dm 1600) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1600) oGrid.kl oGrid.kr 400 1600 ⟨false, 362951505737012860479488928239486347581221791090382848606709151094084875928⟩ ⟨false, 0⟩ ⟨false, 549164384480962691546637267477722793995208472960013159184560691794373652782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1600_2000 : bothSeg evalE (oGrid.idx 1600) (oGrid.dm 1600) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1600) oGrid.kl oGrid.kr 400 2000 ⟨false, 549164384480962691546637267477722793995208472960013159184560691794373652782⟩ ⟨false, 0⟩ ⟨false, 781508119609492384932146502128514897739416449099430570093509164849972084892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1600_2400 : bothLoop evalE (oGrid.idx 1600) (oGrid.dm 1600) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1600) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 781508119609492384932146502128514897739416449099430570093509164849972084892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1600 : oGrid.row evalE 1600 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1600_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1600_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1600_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1600_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1600_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1600_2000).1 (bothLoop_sound b_1600_2400).1))))))

theorem n_row_1600 : nGrid.row evalE 1600 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1600_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1600_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1600_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1600_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1600_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1600_2000).2 (bothLoop_sound b_1600_2400).2))))))

theorem b_1601_0 : bothSeg evalE (oGrid.idx 1601) (oGrid.dm 1601) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1601) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64792566395835125082960033177686429497539253850880440719533880814743993362⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1601_400 : bothSeg evalE (oGrid.idx 1601) (oGrid.dm 1601) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1601) oGrid.kl oGrid.kr 400 400 ⟨false, 64792566395835125082960033177686429497539253850880440719533880814743993362⟩ ⟨false, 0⟩ ⟨false, 128374644839003403378087510725924412657375526830738423358895211177574526782⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1601_800 : bothSeg evalE (oGrid.idx 1601) (oGrid.dm 1601) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1601) oGrid.kl oGrid.kr 400 800 ⟨false, 128374644839003403378087510725924412657375526830738423358895211177574526782⟩ ⟨false, 0⟩ ⟨false, 224125657762429706335548146612818064544783843687727650197139120149842589110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1601_1200 : bothSeg evalE (oGrid.idx 1601) (oGrid.dm 1601) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1601) oGrid.kl oGrid.kr 400 1200 ⟨false, 224125657762429706335548146612818064544783843687727650197139120149842589110⟩ ⟨false, 0⟩ ⟨false, 363475789405342919287123030950569715518877520100413993893243346158757310056⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1601_1600 : bothSeg evalE (oGrid.idx 1601) (oGrid.dm 1601) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1601) oGrid.kl oGrid.kr 400 1600 ⟨false, 363475789405342919287123030950569715518877520100413993893243346158757310056⟩ ⟨false, 0⟩ ⟨false, 549957876373324278975489346611839662862525378469369044814875220768540505200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1601_2000 : bothSeg evalE (oGrid.idx 1601) (oGrid.dm 1601) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1601) oGrid.kl oGrid.kr 400 2000 ⟨false, 549957876373324278975489346611839662862525378469369044814875220768540505200⟩ ⟨false, 0⟩ ⟨false, 782542008287432043637154501474858422519039037330689238307277969158217966076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1601_2400 : bothLoop evalE (oGrid.idx 1601) (oGrid.dm 1601) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1601) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 782542008287432043637154501474858422519039037330689238307277969158217966076⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1601 : oGrid.row evalE 1601 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1601_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1601_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1601_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1601_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1601_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1601_2000).1 (bothLoop_sound b_1601_2400).1))))))

theorem n_row_1601 : nGrid.row evalE 1601 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1601_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1601_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1601_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1601_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1601_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1601_2000).2 (bothLoop_sound b_1601_2400).2))))))

theorem b_1602_0 : bothSeg evalE (oGrid.idx 1602) (oGrid.dm 1602) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1602) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64454871861301768147324556348339221428020967994292368013050698924823936688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1602_400 : bothSeg evalE (oGrid.idx 1602) (oGrid.dm 1602) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1602) oGrid.kl oGrid.kr 400 400 ⟨false, 64454871861301768147324556348339221428020967994292368013050698924823936688⟩ ⟨false, 0⟩ ⟨false, 128265663429066276039112480395864046835372579673659452684982599287938165276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1602_800 : bothSeg evalE (oGrid.idx 1602) (oGrid.dm 1602) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1602) oGrid.kl oGrid.kr 400 800 ⟨false, 128265663429066276039112480395864046835372579673659452684982599287938165276⟩ ⟨false, 0⟩ ⟨false, 224359358033071030647175287100379965853689533383926249229927178723289603700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1602_1200 : bothSeg evalE (oGrid.idx 1602) (oGrid.dm 1602) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1602) oGrid.kl oGrid.kr 400 1200 ⟨false, 224359358033071030647175287100379965853689533383926249229927178723289603700⟩ ⟨false, 0⟩ ⟨false, 364013944783381142127614464912051567219636380664745798313885413457923917312⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1602_1600 : bothSeg evalE (oGrid.idx 1602) (oGrid.dm 1602) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1602) oGrid.kl oGrid.kr 400 1600 ⟨false, 364013944783381142127614464912051567219636380664745798313885413457923917312⟩ ⟨false, 0⟩ ⟨false, 550765247829544140806727146194397276947631505707712976664191894598230222888⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1602_2000 : bothSeg evalE (oGrid.idx 1602) (oGrid.dm 1602) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1602) oGrid.kl oGrid.kr 400 2000 ⟨false, 550765247829544140806727146194397276947631505707712976664191894598230222888⟩ ⟨false, 0⟩ ⟨false, 783589802362499987962057388840126704100130821462911168982665075557009288026⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1602_2400 : bothLoop evalE (oGrid.idx 1602) (oGrid.dm 1602) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1602) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 783589802362499987962057388840126704100130821462911168982665075557009288026⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1602 : oGrid.row evalE 1602 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1602_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1602_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1602_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1602_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1602_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1602_2000).1 (bothLoop_sound b_1602_2400).1))))))

theorem n_row_1602 : nGrid.row evalE 1602 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1602_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1602_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1602_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1602_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1602_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1602_2000).2 (bothLoop_sound b_1602_2400).2))))))

theorem b_1603_0 : bothSeg evalE (oGrid.idx 1603) (oGrid.dm 1603) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1603) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64124499012147346443585235127598502140617730604550375036546532288922094242⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1603_400 : bothSeg evalE (oGrid.idx 1603) (oGrid.dm 1603) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1603) oGrid.kl oGrid.kr 400 400 ⟨false, 64124499012147346443585235127598502140617730604550375036546532288922094242⟩ ⟨false, 0⟩ ⟨false, 128171039875937610766292075158966921139001801295756294659178428756488758616⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1603_800 : bothSeg evalE (oGrid.idx 1603) (oGrid.dm 1603) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1603) oGrid.kl oGrid.kr 400 800 ⟨false, 128171039875937610766292075158966921139001801295756294659178428756488758616⟩ ⟨false, 0⟩ ⟨false, 224607351620920916407910065421550462588852391975692929709337256811003000498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1603_1200 : bothSeg evalE (oGrid.idx 1603) (oGrid.dm 1603) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1603) oGrid.kl oGrid.kr 400 1200 ⟨false, 224607351620920916407910065421550462588852391975692929709337256811003000498⟩ ⟨false, 0⟩ ⟨false, 364566370559996413107695780851533130482851924773699353476906192735768279348⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1603_1600 : bothSeg evalE (oGrid.idx 1603) (oGrid.dm 1603) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1603) oGrid.kl oGrid.kr 400 1600 ⟨false, 364566370559996413107695780851533130482851924773699353476906192735768279348⟩ ⟨false, 0⟩ ⟨false, 551586897490686390118021048662836435080555235211583629379532464790343781328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1603_2000 : bothSeg evalE (oGrid.idx 1603) (oGrid.dm 1603) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1603) oGrid.kl oGrid.kr 400 2000 ⟨false, 551586897490686390118021048662836435080555235211583629379532464790343781328⟩ ⟨false, 0⟩ ⟨false, 784651900423218386130690673248877660605258618118958965340917747524921343990⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1603_2400 : bothLoop evalE (oGrid.idx 1603) (oGrid.dm 1603) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1603) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 784651900423218386130690673248877660605258618118958965340917747524921343990⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1603 : oGrid.row evalE 1603 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1603_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1603_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1603_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1603_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1603_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1603_2000).1 (bothLoop_sound b_1603_2400).1))))))

theorem n_row_1603 : nGrid.row evalE 1603 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1603_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1603_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1603_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1603_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1603_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1603_2000).2 (bothLoop_sound b_1603_2400).2))))))

theorem b_1604_0 : bothSeg evalE (oGrid.idx 1604) (oGrid.dm 1604) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1604) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63801999682314744155001885883639887062576690545480924688284048708771396124⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1604_400 : bothSeg evalE (oGrid.idx 1604) (oGrid.dm 1604) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1604) oGrid.kl oGrid.kr 400 400 ⟨false, 63801999682314744155001885883639887062576690545480924688284048708771396124⟩ ⟨false, 0⟩ ⟨false, 128091150735763555755620408933725720544857281354798979713614139090393020468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1604_800 : bothSeg evalE (oGrid.idx 1604) (oGrid.dm 1604) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1604) oGrid.kl oGrid.kr 400 800 ⟨false, 128091150735763555755620408933725720544857281354798979713614139090393020468⟩ ⟨false, 0⟩ ⟨false, 224870015112169985830141190382592233163151285553137002472356192372642343700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1604_1200 : bothSeg evalE (oGrid.idx 1604) (oGrid.dm 1604) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1604) oGrid.kl oGrid.kr 400 1200 ⟨false, 224870015112169985830141190382592233163151285553137002472356192372642343700⟩ ⟨false, 0⟩ ⟨false, 365133443299561777711979061369941691730905851799757337583520235739301640840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1604_1600 : bothSeg evalE (oGrid.idx 1604) (oGrid.dm 1604) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1604) oGrid.kl oGrid.kr 400 1600 ⟨false, 365133443299561777711979061369941691730905851799757337583520235739301640840⟩ ⟨false, 0⟩ ⟨false, 552423201873410815227966255761177333893645186181832838726585894930489804370⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1604_2000 : bothSeg evalE (oGrid.idx 1604) (oGrid.dm 1604) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1604) oGrid.kl oGrid.kr 400 2000 ⟨false, 552423201873410815227966255761177333893645186181832838726585894930489804370⟩ ⟨false, 0⟩ ⟨false, 785728678933776346502479954855958365660712501160962056347653782217846260446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1604_2400 : bothLoop evalE (oGrid.idx 1604) (oGrid.dm 1604) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1604) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 785728678933776346502479954855958365660712501160962056347653782217846260446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1604 : oGrid.row evalE 1604 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1604_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1604_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1604_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1604_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1604_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1604_2000).1 (bothLoop_sound b_1604_2400).1))))))

theorem n_row_1604 : nGrid.row evalE 1604 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1604_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1604_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1604_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1604_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1604_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1604_2000).2 (bothLoop_sound b_1604_2400).2))))))

theorem b_1605_0 : bothSeg evalE (oGrid.idx 1605) (oGrid.dm 1605) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1605) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63487909989927667682763043093689145726235554821419931948097065790091470930⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1605_400 : bothSeg evalE (oGrid.idx 1605) (oGrid.dm 1605) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1605) oGrid.kl oGrid.kr 400 400 ⟨false, 63487909989927667682763043093689145726235554821419931948097065790091470930⟩ ⟨false, 0⟩ ⟨false, 128026354367588604023313545709281816334626302502587644379155134183489209622⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1605_800 : bothSeg evalE (oGrid.idx 1605) (oGrid.dm 1605) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1605) oGrid.kl oGrid.kr 400 800 ⟨false, 128026354367588604023313545709281816334626302502587644379155134183489209622⟩ ⟨false, 0⟩ ⟨false, 225147706895920066063871002923075954983055740139975235935313492806661661878⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1605_1200 : bothSeg evalE (oGrid.idx 1605) (oGrid.dm 1605) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1605) oGrid.kl oGrid.kr 400 1200 ⟨false, 225147706895920066063871002923075954983055740139975235935313492806661661878⟩ ⟨false, 0⟩ ⟨false, 365715521369442184084867804656504634066641142237834092041160240100678311270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1605_1600 : bothSeg evalE (oGrid.idx 1605) (oGrid.dm 1605) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1605) oGrid.kl oGrid.kr 400 1600 ⟨false, 365715521369442184084867804656504634066641142237834092041160240100678311270⟩ ⟨false, 0⟩ ⟨false, 553274519297460471405293494789445289297846336034704540896297241792241958308⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1605_2000 : bothSeg evalE (oGrid.idx 1605) (oGrid.dm 1605) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1605) oGrid.kl oGrid.kr 400 2000 ⟨false, 553274519297460471405293494789445289297846336034704540896297241792241958308⟩ ⟨false, 0⟩ ⟨false, 786820496161517432377018219280152917429810732317298471860560720380274245520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1605_2400 : bothLoop evalE (oGrid.idx 1605) (oGrid.dm 1605) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1605) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 786820496161517432377018219280152917429810732317298471860560720380274245520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1605 : oGrid.row evalE 1605 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1605_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1605_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1605_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1605_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1605_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1605_2000).1 (bothLoop_sound b_1605_2400).1))))))

theorem n_row_1605 : nGrid.row evalE 1605 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1605_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1605_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1605_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1605_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1605_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1605_2000).2 (bothLoop_sound b_1605_2400).2))))))

theorem b_1606_0 : bothSeg evalE (oGrid.idx 1606) (oGrid.dm 1606) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1606) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63182755064329121841922599306554897717384646209257901375867283078558262282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1606_400 : bothSeg evalE (oGrid.idx 1606) (oGrid.dm 1606) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1606) oGrid.kl oGrid.kr 400 400 ⟨false, 63182755064329121841922599306554897717384646209257901375867283078558262282⟩ ⟨false, 0⟩ ⟨false, 127976992006325576468214247974575345496048880856068540769747779857769940804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1606_800 : bothSeg evalE (oGrid.idx 1606) (oGrid.dm 1606) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1606) oGrid.kl oGrid.kr 400 800 ⟨false, 127976992006325576468214247974575345496048880856068540769747779857769940804⟩ ⟨false, 0⟩ ⟨false, 225440768237154060565037265505134479896021855256030943181290265573169433278⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1606_1200 : bothSeg evalE (oGrid.idx 1606) (oGrid.dm 1606) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1606) oGrid.kl oGrid.kr 400 1200 ⟨false, 225440768237154060565037265505134479896021855256030943181290265573169433278⟩ ⟨false, 0⟩ ⟨false, 366312946012964163316786177521892022272988927134259459356705387592342121460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1606_1600 : bothSeg evalE (oGrid.idx 1606) (oGrid.dm 1606) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1606) oGrid.kl oGrid.kr 400 1600 ⟨false, 366312946012964163316786177521892022272988927134259459356705387592342121460⟩ ⟨false, 0⟩ ⟨false, 554141190958631211793432733600347957714627079110243230699776684741179477844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1606_2000 : bothSeg evalE (oGrid.idx 1606) (oGrid.dm 1606) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1606) oGrid.kl oGrid.kr 400 2000 ⟨false, 554141190958631211793432733600347957714627079110243230699776684741179477844⟩ ⟨false, 0⟩ ⟨false, 787927693249909116048705474162109249613200809488281992936293559158950607148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1606_2400 : bothLoop evalE (oGrid.idx 1606) (oGrid.dm 1606) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1606) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 787927693249909116048705474162109249613200809488281992936293559158950607148⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1606 : oGrid.row evalE 1606 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1606_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1606_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1606_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1606_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1606_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1606_2000).1 (bothLoop_sound b_1606_2400).1))))))

theorem n_row_1606 : nGrid.row evalE 1606 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1606_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1606_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1606_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1606_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1606_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1606_2000).2 (bothLoop_sound b_1606_2400).2))))))

theorem b_1607_0 : bothSeg evalE (oGrid.idx 1607) (oGrid.dm 1607) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1607) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62887034265043109987224311505299385054517307760470447273513352283199304046⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1607_400 : bothSeg evalE (oGrid.idx 1607) (oGrid.dm 1607) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1607) oGrid.kl oGrid.kr 400 400 ⟨false, 62887034265043109987224311505299385054517307760470447273513352283199304046⟩ ⟨false, 0⟩ ⟨false, 127943383767166544111627882131200038386125180481730612923929213136944683266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1607_800 : bothSeg evalE (oGrid.idx 1607) (oGrid.dm 1607) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1607) oGrid.kl oGrid.kr 400 800 ⟨false, 127943383767166544111627882131200038386125180481730612923929213136944683266⟩ ⟨false, 0⟩ ⟨false, 225749519281146760029159044676859968180807086352400912842245687477829643898⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1607_1200 : bothSeg evalE (oGrid.idx 1607) (oGrid.dm 1607) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1607) oGrid.kl oGrid.kr 400 1200 ⟨false, 225749519281146760029159044676859968180807086352400912842245687477829643898⟩ ⟨false, 0⟩ ⟨false, 366926037353826449713305182559581147190808327941087740567505949993115798544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1607_1600 : bothSeg evalE (oGrid.idx 1607) (oGrid.dm 1607) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1607) oGrid.kl oGrid.kr 400 1600 ⟨false, 366926037353826449713305182559581147190808327941087740567505949993115798544⟩ ⟨false, 0⟩ ⟨false, 555023536933182158528828471716731461155005280832647775015353213259762211226⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1607_2000 : bothSeg evalE (oGrid.idx 1607) (oGrid.dm 1607) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1607) oGrid.kl oGrid.kr 400 2000 ⟨false, 555023536933182158528828471716731461155005280832647775015353213259762211226⟩ ⟨false, 0⟩ ⟨false, 789050590222953173090006901916708734092149115698534930419758256229847793442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1607_2400 : bothLoop evalE (oGrid.idx 1607) (oGrid.dm 1607) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1607) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 789050590222953173090006901916708734092149115698534930419758256229847793442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1607 : oGrid.row evalE 1607 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1607_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1607_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1607_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1607_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1607_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1607_2000).1 (bothLoop_sound b_1607_2400).1))))))

theorem n_row_1607 : nGrid.row evalE 1607 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1607_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1607_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1607_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1607_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1607_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1607_2000).2 (bothLoop_sound b_1607_2400).2))))))

theorem o_blk_1584 : allFrom (fun j => oGrid.row evalE j) 1584 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1584) o_row_1584 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1585) o_row_1585 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1586) o_row_1586 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1587) o_row_1587 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1588) o_row_1588 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1589) o_row_1589 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1590) o_row_1590 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1591) o_row_1591 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1592) o_row_1592 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1593) o_row_1593 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1594) o_row_1594 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1595) o_row_1595 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1596) o_row_1596 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1597) o_row_1597 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1598) o_row_1598 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1599) o_row_1599 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1600) o_row_1600 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1601) o_row_1601 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1602) o_row_1602 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1603) o_row_1603 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1604) o_row_1604 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1605) o_row_1605 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1606) o_row_1606 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1607) o_row_1607 (allFrom_zero (fun j => oGrid.row evalE j) 1608)))))))))))))))))))))))))

theorem n_blk_1584 : allFrom (fun j => nGrid.row evalE j) 1584 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1584) n_row_1584 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1585) n_row_1585 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1586) n_row_1586 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1587) n_row_1587 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1588) n_row_1588 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1589) n_row_1589 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1590) n_row_1590 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1591) n_row_1591 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1592) n_row_1592 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1593) n_row_1593 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1594) n_row_1594 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1595) n_row_1595 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1596) n_row_1596 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1597) n_row_1597 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1598) n_row_1598 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1599) n_row_1599 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1600) n_row_1600 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1601) n_row_1601 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1602) n_row_1602 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1603) n_row_1603 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1604) n_row_1604 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1605) n_row_1605 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1606) n_row_1606 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1607) n_row_1607 (allFrom_zero (fun j => nGrid.row evalE j) 1608)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
