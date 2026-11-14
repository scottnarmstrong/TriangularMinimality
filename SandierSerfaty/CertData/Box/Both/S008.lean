/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 8 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `192`–`215`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_192_0 : bothSeg evalE (oGrid.idx 192) (oGrid.dm 192) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 192) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2553793131134780160328601738878767872504429338542960131215248807207378557764⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_192_400 : bothSeg evalE (oGrid.idx 192) (oGrid.dm 192) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 192) oGrid.kl oGrid.kr 400 400 ⟨false, 2553793131134780160328601738878767872504429338542960131215248807207378557764⟩ ⟨false, 0⟩ ⟨false, 4128769382698919638527168888011792785739743156921407730478283124979363793258⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_192_800 : bothSeg evalE (oGrid.idx 192) (oGrid.dm 192) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 192) oGrid.kl oGrid.kr 400 800 ⟨false, 4128769382698919638527168888011792785739743156921407730478283124979363793258⟩ ⟨false, 0⟩ ⟨false, 4702897053709775125001085797430319006147659005563769634333051439287906807376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_192_1200 : bothSeg evalE (oGrid.idx 192) (oGrid.dm 192) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 192) oGrid.kl oGrid.kr 400 1200 ⟨false, 4702897053709775125001085797430319006147659005563769634333051439287906807376⟩ ⟨false, 0⟩ ⟨false, 4756950303191255421983934982654767864001045232978116769097417700552622788044⟩ ⟨false, 22652602549021200666585704101440944323549221291182676745603106862430242724⟩ = true := by
  decide +kernel

theorem b_192_1600 : bothSeg evalE (oGrid.idx 192) (oGrid.dm 192) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 192) oGrid.kl oGrid.kr 400 1600 ⟨false, 4756950303191255421983934982654767864001045232978116769097417700552622788044⟩ ⟨false, 22652602549021200666585704101440944323549221291182676745603106862430242724⟩ ⟨false, 4588805495303331418890667198098917784437637514104498363751750337634834518658⟩ ⟨false, 191124447403623045500177823525531289413685037245147223014867964145603923212⟩ = true := by
  decide +kernel

theorem b_192_2000 : bothSeg evalE (oGrid.idx 192) (oGrid.dm 192) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 192) oGrid.kl oGrid.kr 400 2000 ⟨false, 4588805495303331418890667198098917784437637514104498363751750337634834518658⟩ ⟨false, 191124447403623045500177823525531289413685037245147223014867964145603923212⟩ ⟨false, 4554337397379957834131040939996718267085822774410805968680994912285464373820⟩ ⟨false, 226445881164569447027733565662279201400295718649952671744845476621237683006⟩ = true := by
  decide +kernel

theorem b_192_2400 : bothLoop evalE (oGrid.idx 192) (oGrid.dm 192) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 192) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4554337397379957834131040939996718267085822774410805968680994912285464373820⟩ ⟨false, 226445881164569447027733565662279201400295718649952671744845476621237683006⟩ = true := by
  decide +kernel

theorem o_row_192 : oGrid.row evalE 192 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_192_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_192_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_192_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_192_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_192_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_192_2000).1 (bothLoop_sound b_192_2400).1))))))

theorem n_row_192 : nGrid.row evalE 192 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_192_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_192_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_192_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_192_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_192_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_192_2000).2 (bothLoop_sound b_192_2400).2))))))

theorem b_193_0 : bothSeg evalE (oGrid.idx 193) (oGrid.dm 193) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 193) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2543746009480478361090410441574829233838419281055536335571088127957872993126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_193_400 : bothSeg evalE (oGrid.idx 193) (oGrid.dm 193) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 193) oGrid.kl oGrid.kr 400 400 ⟨false, 2543746009480478361090410441574829233838419281055536335571088127957872993126⟩ ⟨false, 0⟩ ⟨false, 4112505927789606527573136919778633673346496494722267030425060344330027360012⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_193_800 : bothSeg evalE (oGrid.idx 193) (oGrid.dm 193) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 193) oGrid.kl oGrid.kr 400 800 ⟨false, 4112505927789606527573136919778633673346496494722267030425060344330027360012⟩ ⟨false, 0⟩ ⟨false, 4684099513314510458273934897012196552292240187178402857953395305127859609740⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_193_1200 : bothSeg evalE (oGrid.idx 193) (oGrid.dm 193) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 193) oGrid.kl oGrid.kr 400 1200 ⟨false, 4684099513314510458273934897012196552292240187178402857953395305127859609740⟩ ⟨false, 0⟩ ⟨false, 4737189573323683475134151720689055001065197866395640209375454683973439642544⟩ ⟨false, 23006683890122488847039107948042252459054777509499281393320310088601990714⟩ = true := by
  decide +kernel

theorem b_193_1600 : bothSeg evalE (oGrid.idx 193) (oGrid.dm 193) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 193) oGrid.kl oGrid.kr 400 1600 ⟨false, 4737189573323683475134151720689055001065197866395640209375454683973439642544⟩ ⟨false, 23006683890122488847039107948042252459054777509499281393320310088601990714⟩ ⟨false, 4569347907997774226119169954217245519984624867522929179765296233265356356404⟩ ⟨false, 191176272582767365665768550073310223448329541066480000940881328203521031704⟩ = true := by
  decide +kernel

theorem b_193_2000 : bothSeg evalE (oGrid.idx 193) (oGrid.dm 193) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 193) oGrid.kl oGrid.kr 400 2000 ⟨false, 4569347907997774226119169954217245519984624867522929179765296233265356356404⟩ ⟨false, 191176272582767365665768550073310223448329541066480000940881328203521031704⟩ ⟨false, 4535113858803711329902144545644789754692912351077566443644534101585467712906⟩ ⟨false, 226265511167132748643343172661526134517234741895900059291575169075787311702⟩ = true := by
  decide +kernel

theorem b_193_2400 : bothLoop evalE (oGrid.idx 193) (oGrid.dm 193) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 193) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4535113858803711329902144545644789754692912351077566443644534101585467712906⟩ ⟨false, 226265511167132748643343172661526134517234741895900059291575169075787311702⟩ = true := by
  decide +kernel

theorem o_row_193 : oGrid.row evalE 193 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_193_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_193_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_193_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_193_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_193_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_193_2000).1 (bothLoop_sound b_193_2400).1))))))

theorem n_row_193 : nGrid.row evalE 193 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_193_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_193_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_193_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_193_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_193_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_193_2000).2 (bothLoop_sound b_193_2400).2))))))

theorem b_194_0 : bothSeg evalE (oGrid.idx 194) (oGrid.dm 194) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 194) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2533729709551226964746543130721812075937062187768267143063886567743341209558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_194_400 : bothSeg evalE (oGrid.idx 194) (oGrid.dm 194) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 194) oGrid.kl oGrid.kr 400 400 ⟨false, 2533729709551226964746543130721812075937062187768267143063886567743341209558⟩ ⟨false, 0⟩ ⟨false, 4096290405715045206322609232694068116131518498157471447273039726629639070992⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_194_800 : bothSeg evalE (oGrid.idx 194) (oGrid.dm 194) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 194) oGrid.kl oGrid.kr 400 800 ⟨false, 4096290405715045206322609232694068116131518498157471447273039726629639070992⟩ ⟨false, 0⟩ ⟨false, 4665356179011567652540494184038806702551662371793220269869704184473215563074⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_194_1200 : bothSeg evalE (oGrid.idx 194) (oGrid.dm 194) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 194) oGrid.kl oGrid.kr 400 1200 ⟨false, 4665356179011567652540494184038806702551662371793220269869704184473215563074⟩ ⟨false, 0⟩ ⟨false, 4717488329697840552981211289252205351258424235016765220268882147060128632344⟩ ⟨false, 23358046010887662689349748472274261520428154060974131913203085308090130546⟩ = true := by
  decide +kernel

theorem b_194_1600 : bothSeg evalE (oGrid.idx 194) (oGrid.dm 194) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 194) oGrid.kl oGrid.kr 400 1600 ⟨false, 4717488329697840552981211289252205351258424235016765220268882147060128632344⟩ ⟨false, 23358046010887662689349748472274261520428154060974131913203085308090130546⟩ ⟨false, 4549948066145405065419104624449004865626980793628426778251642120677975392804⟩ ⟨false, 191227037631345426544470260357655950212583170268571092331138581232883488614⟩ = true := by
  decide +kernel

theorem b_194_2000 : bothSeg evalE (oGrid.idx 194) (oGrid.dm 194) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 194) oGrid.kl oGrid.kr 400 2000 ⟨false, 4549948066145405065419104624449004865626980793628426778251642120677975392804⟩ ⟨false, 191227037631345426544470260357655950212583170268571092331138581232883488614⟩ ⟨false, 4515947948172625069121278383044454658351177177570096364354218623014869914408⟩ ⟨false, 226084129814387095978192846097855661419161204476049719338549620295907025656⟩ = true := by
  decide +kernel

theorem b_194_2400 : bothLoop evalE (oGrid.idx 194) (oGrid.dm 194) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 194) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4515947948172625069121278383044454658351177177570096364354218623014869914408⟩ ⟨false, 226084129814387095978192846097855661419161204476049719338549620295907025656⟩ = true := by
  decide +kernel

theorem o_row_194 : oGrid.row evalE 194 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_194_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_194_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_194_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_194_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_194_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_194_2000).1 (bothLoop_sound b_194_2400).1))))))

theorem n_row_194 : nGrid.row evalE 194 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_194_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_194_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_194_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_194_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_194_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_194_2000).2 (bothLoop_sound b_194_2400).2))))))

theorem b_195_0 : bothSeg evalE (oGrid.idx 195) (oGrid.dm 195) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 195) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2523744118828531435717322238014680259642214691344414707780702372871171953822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_195_400 : bothSeg evalE (oGrid.idx 195) (oGrid.dm 195) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 195) oGrid.kl oGrid.kr 400 400 ⟨false, 2523744118828531435717322238014680259642214691344414707780702372871171953822⟩ ⟨false, 0⟩ ⟨false, 4080122669274033726789804022560510462753672913236502105939362622221543403210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_195_800 : bothSeg evalE (oGrid.idx 195) (oGrid.dm 195) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 195) oGrid.kl oGrid.kr 400 800 ⟨false, 4080122669274033726789804022560510462753672913236502105939362622221543403210⟩ ⟨false, 0⟩ ⟨false, 4646666908609894167413229993186268876044748912454577652279585099401964997320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_195_1200 : bothSeg evalE (oGrid.idx 195) (oGrid.dm 195) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 195) oGrid.kl oGrid.kr 400 1200 ⟨false, 4646666908609894167413229993186268876044748912454577652279585099401964997320⟩ ⟨false, 0⟩ ⟨false, 4697846543920498899023523228751981123199715894015554463571024963661632367384⟩ ⟨false, 23706575685950748254745676154957179280575215937804937271612670602292164946⟩ = true := by
  decide +kernel

theorem b_195_1600 : bothSeg evalE (oGrid.idx 195) (oGrid.dm 195) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 195) oGrid.kl oGrid.kr 400 1600 ⟨false, 4697846543920498899023523228751981123199715894015554463571024963661632367384⟩ ⟨false, 23706575685950748254745676154957179280575215937804937271612670602292164946⟩ ⟨false, 4530605735252189906962739966635581678914228731928314125185354559282764032502⟩ ⟨false, 191276807115288004649377881978952572728863266318536178952272383519275770506⟩ = true := by
  decide +kernel

theorem b_195_2000 : bothSeg evalE (oGrid.idx 195) (oGrid.dm 195) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 195) oGrid.kl oGrid.kr 400 2000 ⟨false, 4530605735252189906962739966635581678914228731928314125185354559282764032502⟩ ⟨false, 191276807115288004649377881978952572728863266318536178952272383519275770506⟩ ⟨false, 4496839458770366176585386309106689221795183529731815317054291751014372696692⟩ ⟨false, 225901957433299788023656004153698744941366262147864581809550568661046550238⟩ = true := by
  decide +kernel

theorem b_195_2400 : bothLoop evalE (oGrid.idx 195) (oGrid.dm 195) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 195) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4496839458770366176585386309106689221795183529731815317054291751014372696692⟩ ⟨false, 225901957433299788023656004153698744941366262147864581809550568661046550238⟩ = true := by
  decide +kernel

theorem o_row_195 : oGrid.row evalE 195 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_195_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_195_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_195_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_195_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_195_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_195_2000).1 (bothLoop_sound b_195_2400).1))))))

theorem n_row_195 : nGrid.row evalE 195 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_195_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_195_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_195_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_195_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_195_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_195_2000).2 (bothLoop_sound b_195_2400).2))))))

theorem b_196_0 : bothSeg evalE (oGrid.idx 196) (oGrid.dm 196) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 196) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2513789213638977541376974923195662605577678280330230784924296306731730891580⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_196_400 : bothSeg evalE (oGrid.idx 196) (oGrid.dm 196) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 196) oGrid.kl oGrid.kr 400 400 ⟨false, 2513789213638977541376974923195662605577678280330230784924296306731730891580⟩ ⟨false, 0⟩ ⟨false, 4064002634387394140351899028294137621551669233976298835822896469144148445016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_196_800 : bothSeg evalE (oGrid.idx 196) (oGrid.dm 196) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 196) oGrid.kl oGrid.kr 400 800 ⟨false, 4064002634387394140351899028294137621551669233976298835822896469144148445016⟩ ⟨false, 0⟩ ⟨false, 4628031587627283907686008023874537378331451860641060520100948663415980050808⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_196_1200 : bothSeg evalE (oGrid.idx 196) (oGrid.dm 196) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 196) oGrid.kl oGrid.kr 400 1200 ⟨false, 4628031587627283907686008023874537378331451860641060520100948663415980050808⟩ ⟨false, 0⟩ ⟨false, 4678264296375977244962541721880916106246355018351033264550029307101140462932⟩ ⟨false, 24052089255343673009774583385665814187972630904544861124051353215931897272⟩ = true := by
  decide +kernel

theorem b_196_1600 : bothSeg evalE (oGrid.idx 196) (oGrid.dm 196) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 196) oGrid.kl oGrid.kr 400 1600 ⟨false, 4678264296375977244962541721880916106246355018351033264550029307101140462932⟩ ⟨false, 24052089255343673009774583385665814187972630904544861124051353215931897272⟩ ⟨false, 4511320937419088848499344290488871923491321769490347694261132455483464072214⟩ ⟨false, 191325811504073447528179733266381297782448903543183118286513499066191654866⟩ = true := by
  decide +kernel

theorem b_196_2000 : bothSeg evalE (oGrid.idx 196) (oGrid.dm 196) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 196) oGrid.kl oGrid.kr 400 2000 ⟨false, 4511320937419088848499344290488871923491321769490347694261132455483464072214⟩ ⟨false, 191325811504073447528179733266381297782448903543183118286513499066191654866⟩ ⟨false, 4477788437892270563472545905517820021949483870045653684814950463769964146434⟩ ⟨false, 225718924296425538326436300061454661047255544876234226230490501819332494954⟩ = true := by
  decide +kernel

theorem b_196_2400 : bothLoop evalE (oGrid.idx 196) (oGrid.dm 196) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 196) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4477788437892270563472545905517820021949483870045653684814950463769964146434⟩ ⟨false, 225718924296425538326436300061454661047255544876234226230490501819332494954⟩ = true := by
  decide +kernel

theorem o_row_196 : oGrid.row evalE 196 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_196_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_196_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_196_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_196_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_196_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_196_2000).1 (bothLoop_sound b_196_2400).1))))))

theorem n_row_196 : nGrid.row evalE 196 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_196_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_196_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_196_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_196_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_196_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_196_2000).2 (bothLoop_sound b_196_2400).2))))))

theorem b_197_0 : bothSeg evalE (oGrid.idx 197) (oGrid.dm 197) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 197) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2503864888002356954066376037784791450090864246570771101323566581633183489538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_197_400 : bothSeg evalE (oGrid.idx 197) (oGrid.dm 197) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 197) oGrid.kl oGrid.kr 400 400 ⟨false, 2503864888002356954066376037784791450090864246570771101323566581633183489538⟩ ⟨false, 0⟩ ⟨false, 4047930198330902466168340061378993879881235498140046081389721066429590663932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_197_800 : bothSeg evalE (oGrid.idx 197) (oGrid.dm 197) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 197) oGrid.kl oGrid.kr 400 800 ⟨false, 4047930198330902466168340061378993879881235498140046081389721066429590663932⟩ ⟨false, 0⟩ ⟨false, 4609450137469538817064876560078044336228432594561038677359118827828538153684⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_197_1200 : bothSeg evalE (oGrid.idx 197) (oGrid.dm 197) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 197) oGrid.kl oGrid.kr 400 1200 ⟨false, 4609450137469538817064876560078044336228432594561038677359118827828538153684⟩ ⟨false, 0⟩ ⟨false, 4658741706801465503302138707474944295893004762603721851919671843109213291098⟩ ⟨false, 24394354119917811029147309868551009947600854607329186087237341668530126564⟩ = true := by
  decide +kernel

theorem b_197_1600 : bothSeg evalE (oGrid.idx 197) (oGrid.dm 197) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 197) oGrid.kl oGrid.kr 400 1600 ⟨false, 4658741706801465503302138707474944295893004762603721851919671843109213291098⟩ ⟨false, 24394354119917811029147309868551009947600854607329186087237341668530126564⟩ ⟨false, 4492093570075228793579009858893424809412628195272980705394219552236374234436⟩ ⟨false, 191373866137352551151521308265622440055763702882953361688500413702499312182⟩ = true := by
  decide +kernel

theorem b_197_2000 : bothSeg evalE (oGrid.idx 197) (oGrid.dm 197) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 197) oGrid.kl oGrid.kr 400 2000 ⟨false, 4492093570075228793579009858893424809412628195272980705394219552236374234436⟩ ⟨false, 191373866137352551151521308265622440055763702882953361688500413702499312182⟩ ⟨false, 4458794796149048842122909276648237213808964794358503772945618338573447186958⟩ ⟨false, 225535229219041266568293985633869609912293794908217761572669232346362979638⟩ = true := by
  decide +kernel

theorem b_197_2400 : bothLoop evalE (oGrid.idx 197) (oGrid.dm 197) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 197) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4458794796149048842122909276648237213808964794358503772945618338573447186958⟩ ⟨false, 225535229219041266568293985633869609912293794908217761572669232346362979638⟩ = true := by
  decide +kernel

theorem o_row_197 : oGrid.row evalE 197 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_197_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_197_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_197_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_197_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_197_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_197_2000).1 (bothLoop_sound b_197_2400).1))))))

theorem n_row_197 : nGrid.row evalE 197 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_197_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_197_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_197_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_197_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_197_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_197_2000).2 (bothLoop_sound b_197_2400).2))))))

theorem b_198_0 : bothSeg evalE (oGrid.idx 198) (oGrid.dm 198) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 198) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2493971041827814219253208212138342749873074320327601872351352395007062989026⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_198_400 : bothSeg evalE (oGrid.idx 198) (oGrid.dm 198) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 198) oGrid.kl oGrid.kr 400 400 ⟨false, 2493971041827814219253208212138342749873074320327601872351352395007062989026⟩ ⟨false, 0⟩ ⟨false, 4031905214876888500680002568236365459453823048013994882655611310146986917510⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_198_800 : bothSeg evalE (oGrid.idx 198) (oGrid.dm 198) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 198) oGrid.kl oGrid.kr 400 800 ⟨false, 4031905214876888500680002568236365459453823048013994882655611310146986917510⟩ ⟨false, 0⟩ ⟨false, 4590922400460993068795593160160961853827251049789683341607216705118943397180⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_198_1200 : bothSeg evalE (oGrid.idx 198) (oGrid.dm 198) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 198) oGrid.kl oGrid.kr 400 1200 ⟨false, 4590922400460993068795593160160961853827251049789683341607216705118943397180⟩ ⟨false, 0⟩ ⟨false, 4639278793752574791236722259450584514997208665335274405337340526286021792120⟩ ⟨false, 24733212390943413546745258277213041277435887708948686217525969539075895114⟩ = true := by
  decide +kernel

theorem b_198_1600 : bothSeg evalE (oGrid.idx 198) (oGrid.dm 198) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 198) oGrid.kl oGrid.kr 400 1600 ⟨false, 4639278793752574791236722259450584514997208665335274405337340526286021792120⟩ ⟨false, 24733212390943413546745258277213041277435887708948686217525969539075895114⟩ ⟨false, 4472923302733984284951896228047791728974531044969387555326580771631109777558⟩ ⟨false, 191421013879124641660381636350617741555576794204023327076058176992108361532⟩ = true := by
  decide +kernel

theorem b_198_2000 : bothSeg evalE (oGrid.idx 198) (oGrid.dm 198) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 198) oGrid.kl oGrid.kr 400 2000 ⟨false, 4472923302733984284951896228047791728974531044969387555326580771631109777558⟩ ⟨false, 191421013879124641660381636350617741555576794204023327076058176992108361532⟩ ⟨false, 4439858232005154618106692838496496042048271281948330567439879851231803695600⟩ ⟨false, 225350463392195161391874453079055062108098387758755204629613398746411763108⟩ = true := by
  decide +kernel

theorem b_198_2400 : bothLoop evalE (oGrid.idx 198) (oGrid.dm 198) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 198) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4439858232005154618106692838496496042048271281948330567439879851231803695600⟩ ⟨false, 225350463392195161391874453079055062108098387758755204629613398746411763108⟩ = true := by
  decide +kernel

theorem o_row_198 : oGrid.row evalE 198 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_198_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_198_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_198_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_198_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_198_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_198_2000).1 (bothLoop_sound b_198_2400).1))))))

theorem n_row_198 : nGrid.row evalE 198 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_198_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_198_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_198_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_198_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_198_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_198_2000).2 (bothLoop_sound b_198_2400).2))))))

theorem b_199_0 : bothSeg evalE (oGrid.idx 199) (oGrid.dm 199) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 199) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2484107644533796831563847016301227103050536988710492416346867530101184576468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_199_400 : bothSeg evalE (oGrid.idx 199) (oGrid.dm 199) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 199) oGrid.kl oGrid.kr 400 400 ⟨false, 2484107644533796831563847016301227103050536988710492416346867530101184576468⟩ ⟨false, 0⟩ ⟨false, 4015927633939237586256829200403206028029923986003397507503662650135252781236⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_199_800 : bothSeg evalE (oGrid.idx 199) (oGrid.dm 199) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 199) oGrid.kl oGrid.kr 400 800 ⟨false, 4015927633939237586256829200403206028029923986003397507503662650135252781236⟩ ⟨false, 0⟩ ⟨false, 4572448329019788071161927953194518798598292571406550853038780226696795075220⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_199_1200 : bothSeg evalE (oGrid.idx 199) (oGrid.dm 199) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 199) oGrid.kl oGrid.kr 400 1200 ⟨false, 4572448329019788071161927953194518798598292571406550853038780226696795075220⟩ ⟨false, 0⟩ ⟨false, 4619875724932030465496253942714926256507016347142963579990796018169188964372⟩ ⟨false, 25068454091207306288678701265563051508909953993911820231639974720992162142⟩ = true := by
  decide +kernel

theorem b_199_1600 : bothSeg evalE (oGrid.idx 199) (oGrid.dm 199) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 199) oGrid.kl oGrid.kr 400 1600 ⟨false, 4619875724932030465496253942714926256507016347142963579990796018169188964372⟩ ⟨false, 25068454091207306288678701265563051508909953993911820231639974720992162142⟩ ⟨false, 4453810350173874629290492244480505935773944022477322012344375698217165268056⟩ ⟨false, 191467000451479219721974885811310443857614572155592602513117363396915623800⟩ = true := by
  decide +kernel

theorem b_199_2000 : bothSeg evalE (oGrid.idx 199) (oGrid.dm 199) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 199) oGrid.kl oGrid.kr 400 2000 ⟨false, 4453810350173874629290492244480505935773944022477322012344375698217165268056⟩ ⟨false, 191467000451479219721974885811310443857614572155592602513117363396915623800⟩ ⟨false, 4420978998637070061212573436634766146998299890374194489117207705594128650008⟩ ⟨false, 225164631072410955795709247343312950180871246247055963797422232774733202220⟩ = true := by
  decide +kernel

theorem b_199_2400 : bothLoop evalE (oGrid.idx 199) (oGrid.dm 199) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 199) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4420978998637070061212573436634766146998299890374194489117207705594128650008⟩ ⟨false, 225164631072410955795709247343312950180871246247055963797422232774733202220⟩ = true := by
  decide +kernel

theorem o_row_199 : oGrid.row evalE 199 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_199_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_199_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_199_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_199_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_199_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_199_2000).1 (bothLoop_sound b_199_2400).1))))))

theorem n_row_199 : nGrid.row evalE 199 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_199_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_199_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_199_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_199_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_199_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_199_2000).2 (bothLoop_sound b_199_2400).2))))))

theorem b_200_0 : bothSeg evalE (oGrid.idx 200) (oGrid.dm 200) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 200) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2474274541196278069403329567442595761127753586666388069646890956300529009950⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_200_400 : bothSeg evalE (oGrid.idx 200) (oGrid.dm 200) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 200) oGrid.kl oGrid.kr 400 400 ⟨false, 2474274541196278069403329567442595761127753586666388069646890956300529009950⟩ ⟨false, 0⟩ ⟨false, 3999997272529914887954720451765142841690953514838381236536685636116370633066⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_200_800 : bothSeg evalE (oGrid.idx 200) (oGrid.dm 200) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 200) oGrid.kl oGrid.kr 400 800 ⟨false, 3999997272529914887954720451765142841690953514838381236536685636116370633066⟩ ⟨false, 0⟩ ⟨false, 4554027724228426522847861008308093651776868190125638987712679219844384596918⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_200_1200 : bothSeg evalE (oGrid.idx 200) (oGrid.dm 200) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 200) oGrid.kl oGrid.kr 400 1200 ⟨false, 4554027724228426522847861008308093651776868190125638987712679219844384596918⟩ ⟨false, 0⟩ ⟨false, 4600532400654025328611038982376303776762005907658084719884368354628135142932⟩ ⟨false, 25399973504601681960492670296130233464008153159671393870914581979469669910⟩ = true := by
  decide +kernel

theorem b_200_1600 : bothSeg evalE (oGrid.idx 200) (oGrid.dm 200) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 200) oGrid.kl oGrid.kr 400 1600 ⟨false, 4600532400654025328611038982376303776762005907658084719884368354628135142932⟩ ⟨false, 25399973504601681960492670296130233464008153159671393870914581979469669910⟩ ⟨false, 4434754233874406567097770084798827586116518649582893936940035558378219154982⟩ ⟨false, 191512067108053922160879252893538445591088642860207984771488411242705941396⟩ = true := by
  decide +kernel

theorem b_200_2000 : bothSeg evalE (oGrid.idx 200) (oGrid.dm 200) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 200) oGrid.kl oGrid.kr 400 2000 ⟨false, 4434754233874406567097770084798827586116518649582893936940035558378219154982⟩ ⟨false, 191512067108053922160879252893538445591088642860207984771488411242705941396⟩ ⟨false, 4402156598984034679034290430428792801491442963854867614386654076042430494856⟩ ⟨false, 224977873801044707631822506717241520740305026727801829987161590191930195726⟩ = true := by
  decide +kernel

theorem b_200_2400 : bothLoop evalE (oGrid.idx 200) (oGrid.dm 200) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 200) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4402156598984034679034290430428792801491442963854867614386654076042430494856⟩ ⟨false, 224977873801044707631822506717241520740305026727801829987161590191930195726⟩ = true := by
  decide +kernel

theorem o_row_200 : oGrid.row evalE 200 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_200_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_200_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_200_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_200_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_200_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_200_2000).1 (bothLoop_sound b_200_2400).1))))))

theorem n_row_200 : nGrid.row evalE 200 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_200_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_200_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_200_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_200_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_200_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_200_2000).2 (bothLoop_sound b_200_2400).2))))))

theorem b_201_0 : bothSeg evalE (oGrid.idx 201) (oGrid.dm 201) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 201) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2464471687712736575935842983409447429765300845476673349603456683148099034000⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_201_400 : bothSeg evalE (oGrid.idx 201) (oGrid.dm 201) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 201) oGrid.kl oGrid.kr 400 400 ⟨false, 2464471687712736575935842983409447429765300845476673349603456683148099034000⟩ ⟨false, 0⟩ ⟨false, 3984114033619515005960614387076307265847945067077592018336593139671665156050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_201_800 : bothSeg evalE (oGrid.idx 201) (oGrid.dm 201) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 201) oGrid.kl oGrid.kr 400 800 ⟨false, 3984114033619515005960614387076307265847945067077592018336593139671665156050⟩ ⟨false, 0⟩ ⟨false, 4535660483282684489308263785707556698866046321260213567849961594864077254162⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_201_1200 : bothSeg evalE (oGrid.idx 201) (oGrid.dm 201) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 201) oGrid.kl oGrid.kr 400 1200 ⟨false, 4535660483282684489308263785707556698866046321260213567849961594864077254162⟩ ⟨false, 0⟩ ⟨false, 4581248960089610605364509640247989903446232258212434232828918207434978751988⟩ ⟨false, 25727540711692581751595393586496143895566608467553739322428469775477885650⟩ = true := by
  decide +kernel

theorem b_201_1600 : bothSeg evalE (oGrid.idx 201) (oGrid.dm 201) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 201) oGrid.kl oGrid.kr 400 1600 ⟨false, 4581248960089610605364509640247989903446232258212434232828918207434978751988⟩ ⟨false, 25727540711692581751595393586496143895566608467553739322428469775477885650⟩ ⟨false, 4415755063642896063980867825314073467915053265967357838334682404357887998788⟩ ⟨false, 191556223756332259050511540391267777642866453756929712786370879530009656404⟩ = true := by
  decide +kernel

theorem b_201_2000 : bothSeg evalE (oGrid.idx 201) (oGrid.dm 201) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 201) oGrid.kl oGrid.kr 400 2000 ⟨false, 4415755063642896063980867825314073467915053265967357838334682404357887998788⟩ ⟨false, 191556223756332259050511540391267777642866453756929712786370879530009656404⟩ ⟨false, 4383391180386527484690963866620941898770258489547430184814620102194037984054⟩ ⟨false, 224790004267227126452381801047725860078386117282744948071859743347577988114⟩ = true := by
  decide +kernel

theorem b_201_2400 : bothLoop evalE (oGrid.idx 201) (oGrid.dm 201) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 201) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4383391180386527484690963866620941898770258489547430184814620102194037984054⟩ ⟨false, 224790004267227126452381801047725860078386117282744948071859743347577988114⟩ = true := by
  decide +kernel

theorem o_row_201 : oGrid.row evalE 201 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_201_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_201_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_201_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_201_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_201_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_201_2000).1 (bothLoop_sound b_201_2400).1))))))

theorem n_row_201 : nGrid.row evalE 201 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_201_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_201_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_201_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_201_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_201_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_201_2000).2 (bothLoop_sound b_201_2400).2))))))

theorem b_202_0 : bothSeg evalE (oGrid.idx 202) (oGrid.dm 202) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 202) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2454699004607640185093104101602726499441996986972332624859655027634897121522⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_202_400 : bothSeg evalE (oGrid.idx 202) (oGrid.dm 202) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 202) oGrid.kl oGrid.kr 400 400 ⟨false, 2454699004607640185093104101602726499441996986972332624859655027634897121522⟩ ⟨false, 0⟩ ⟨false, 3968277809239166345400358774580415414629536675688305628883161214707886114210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_202_800 : bothSeg evalE (oGrid.idx 202) (oGrid.dm 202) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 202) oGrid.kl oGrid.kr 400 800 ⟨false, 3968277809239166345400358774580415414629536675688305628883161214707886114210⟩ ⟨false, 0⟩ ⟨false, 4517346502968869066951902524082472697260671363855554880627050846433317334664⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_202_1200 : bothSeg evalE (oGrid.idx 202) (oGrid.dm 202) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 202) oGrid.kl oGrid.kr 400 1200 ⟨false, 4517346502968869066951902524082472697260671363855554880627050846433317334664⟩ ⟨false, 0⟩ ⟨false, 4562025418569534320147962576026947248679009157883375539660225800039757386620⟩ ⟨false, 26051023437181024941093032719766168930577318709565111586582297792477409824⟩ = true := by
  decide +kernel

theorem b_202_1600 : bothSeg evalE (oGrid.idx 202) (oGrid.dm 202) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 202) oGrid.kl oGrid.kr 400 1600 ⟨false, 4562025418569534320147962576026947248679009157883375539660225800039757386620⟩ ⟨false, 26051023437181024941093032719766168930577318709565111586582297792477409824⟩ ⟨false, 4396812742731090616246127886672436680114809188954667263614269479392929804096⟩ ⟨false, 191599439089422960599543597647512997605961710011382894820612668296052199834⟩ = true := by
  decide +kernel

theorem b_202_2000 : bothSeg evalE (oGrid.idx 202) (oGrid.dm 202) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 202) oGrid.kl oGrid.kr 400 2000 ⟨false, 4396812742731090616246127886672436680114809188954667263614269479392929804096⟩ ⟨false, 191599439089422960599543597647512997605961710011382894820612668296052199834⟩ ⟨false, 4364682682965440430803805279677865817756365766845702632462195613224784041370⟩ ⟨false, 224601440526977641771276593419027365939783872389309557866310704505360728702⟩ = true := by
  decide +kernel

theorem b_202_2400 : bothLoop evalE (oGrid.idx 202) (oGrid.dm 202) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 202) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4364682682965440430803805279677865817756365766845702632462195613224784041370⟩ ⟨false, 224601440526977641771276593419027365939783872389309557866310704505360728702⟩ = true := by
  decide +kernel

theorem o_row_202 : oGrid.row evalE 202 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_202_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_202_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_202_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_202_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_202_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_202_2000).1 (bothLoop_sound b_202_2400).1))))))

theorem n_row_202 : nGrid.row evalE 202 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_202_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_202_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_202_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_202_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_202_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_202_2000).2 (bothLoop_sound b_202_2400).2))))))

theorem b_203_0 : bothSeg evalE (oGrid.idx 203) (oGrid.dm 203) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 203) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2444956438844434828138081331702288309114726367889736183940056961157630638426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_203_400 : bothSeg evalE (oGrid.idx 203) (oGrid.dm 203) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 203) oGrid.kl oGrid.kr 400 400 ⟨false, 2444956438844434828138081331702288309114726367889736183940056961157630638426⟩ ⟨false, 0⟩ ⟨false, 3952488559544810028136803359082690477395598635376070732852632790443225452282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_203_800 : bothSeg evalE (oGrid.idx 203) (oGrid.dm 203) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 203) oGrid.kl oGrid.kr 400 800 ⟨false, 3952488559544810028136803359082690477395598635376070732852632790443225452282⟩ ⟨false, 0⟩ ⟨false, 4499085743769711192572327885640298324839258349525004961132121784475945825172⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_203_1200 : bothSeg evalE (oGrid.idx 203) (oGrid.dm 203) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 203) oGrid.kl oGrid.kr 400 1200 ⟨false, 4499085743769711192572327885640298324839258349525004961132121784475945825172⟩ ⟨false, 0⟩ ⟨false, 4542861946505077340487671079043954162817239746034290919792403555845384928218⟩ ⟨false, 26370215444065464883446859300781914384849398655603359751617243664310038202⟩ = true := by
  decide +kernel

theorem b_203_1600 : bothSeg evalE (oGrid.idx 203) (oGrid.dm 203) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 203) oGrid.kl oGrid.kr 400 1600 ⟨false, 4542861946505077340487671079043954162817239746034290919792403555845384928218⟩ ⟨false, 26370215444065464883446859300781914384849398655603359751617243664310038202⟩ ⟨false, 4377926974537795008675952346292749722098355035590672494824952845480152578828⟩ ⟨false, 191641689958037129093062085038839257322413067789572636509118231974722981640⟩ = true := by
  decide +kernel

theorem b_203_2000 : bothSeg evalE (oGrid.idx 203) (oGrid.dm 203) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 203) oGrid.kl oGrid.kr 400 2000 ⟨false, 4377926974537795008675952346292749722098355035590672494824952845480152578828⟩ ⟨false, 191641689958037129093062085038839257322413067789572636509118231974722981640⟩ ⟨false, 4346030816128201944830805191097409409675106698029382717900702354769763391462⟩ ⟨false, 224411576809941582313631969615380837025407762441875169168941557747770875128⟩ = true := by
  decide +kernel

theorem b_203_2400 : bothLoop evalE (oGrid.idx 203) (oGrid.dm 203) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 203) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4346030816128201944830805191097409409675106698029382717900702354769763391462⟩ ⟨false, 224411576809941582313631969615380837025407762441875169168941557747770875128⟩ = true := by
  decide +kernel

theorem o_row_203 : oGrid.row evalE 203 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_203_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_203_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_203_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_203_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_203_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_203_2000).1 (bothLoop_sound b_203_2400).1))))))

theorem n_row_203 : nGrid.row evalE 203 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_203_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_203_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_203_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_203_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_203_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_203_2000).2 (bothLoop_sound b_203_2400).2))))))

theorem b_204_0 : bothSeg evalE (oGrid.idx 204) (oGrid.dm 204) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 204) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2435243910522042221544213166455951558156863768207640431214720623625299283664⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_204_400 : bothSeg evalE (oGrid.idx 204) (oGrid.dm 204) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 204) oGrid.kl oGrid.kr 400 400 ⟨false, 2435243910522042221544213166455951558156863768207640431214720623625299283664⟩ ⟨false, 0⟩ ⟨false, 3936746120533982517359199198974228189176875336635017853277943487784055819484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_204_800 : bothSeg evalE (oGrid.idx 204) (oGrid.dm 204) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 204) oGrid.kl oGrid.kr 400 800 ⟨false, 3936746120533982517359199198974228189176875336635017853277943487784055819484⟩ ⟨false, 0⟩ ⟨false, 4480878028408546985807038916085318644012791936212682329434158589010047291906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_204_1200 : bothSeg evalE (oGrid.idx 204) (oGrid.dm 204) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 204) oGrid.kl oGrid.kr 400 1200 ⟨false, 4480878028408546985807038916085318644012791936212682329434158589010047291906⟩ ⟨false, 0⟩ ⟨false, 4523758486737378388633945692125929876477773478650952169216247063268607112188⟩ ⟨false, 26685007805458090310377419632286551172874752617617296992966821036088648136⟩ = true := by
  decide +kernel

theorem b_204_1600 : bothSeg evalE (oGrid.idx 204) (oGrid.dm 204) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 204) oGrid.kl oGrid.kr 400 1600 ⟨false, 4523758486737378388633945692125929876477773478650952169216247063268607112188⟩ ⟨false, 26685007805458090310377419632286551172874752617617296992966821036088648136⟩ ⟨false, 4359097834749256886848736229586248156047013444858574154020995371006380216844⟩ ⟨false, 191683240389311819946873840101621193351582543264357579121821901813739187424⟩ = true := by
  decide +kernel

theorem b_204_2000 : bothSeg evalE (oGrid.idx 204) (oGrid.dm 204) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 204) oGrid.kl oGrid.kr 400 2000 ⟨false, 4359097834749256886848736229586248156047013444858574154020995371006380216844⟩ ⟨false, 191683240389311819946873840101621193351582543264357579121821901813739187424⟩ ⟨false, 4327435691779875658422467839210213190228238983242572951225431575369842605060⟩ ⟨false, 224221021708690622697375258754723849703701316131763918738359785405563528628⟩ = true := by
  decide +kernel

theorem b_204_2400 : bothLoop evalE (oGrid.idx 204) (oGrid.dm 204) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 204) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4327435691779875658422467839210213190228238983242572951225431575369842605060⟩ ⟨false, 224221021708690622697375258754723849703701316131763918738359785405563528628⟩ = true := by
  decide +kernel

theorem o_row_204 : oGrid.row evalE 204 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_204_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_204_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_204_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_204_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_204_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_204_2000).1 (bothLoop_sound b_204_2400).1))))))

theorem n_row_204 : nGrid.row evalE 204 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_204_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_204_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_204_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_204_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_204_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_204_2000).2 (bothLoop_sound b_204_2400).2))))))

theorem b_205_0 : bothSeg evalE (oGrid.idx 205) (oGrid.dm 205) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 205) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2425561290966143888302472587670328311646214142694060957516526373873282208188⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_205_400 : bothSeg evalE (oGrid.idx 205) (oGrid.dm 205) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 205) oGrid.kl oGrid.kr 400 400 ⟨false, 2425561290966143888302472587670328311646214142694060957516526373873282208188⟩ ⟨false, 0⟩ ⟨false, 3921050364181301002258959558613526033465812028569243403556462099450069943214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_205_800 : bothSeg evalE (oGrid.idx 205) (oGrid.dm 205) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 205) oGrid.kl oGrid.kr 400 800 ⟨false, 3921050364181301002258959558613526033465812028569243403556462099450069943214⟩ ⟨false, 0⟩ ⟨false, 4462723236384362690291969960658579877023342470103550593521562364590966242940⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_205_1200 : bothSeg evalE (oGrid.idx 205) (oGrid.dm 205) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 205) oGrid.kl oGrid.kr 400 1200 ⟨false, 4462723236384362690291969960658579877023342470103550593521562364590966242940⟩ ⟨false, 0⟩ ⟨false, 4504715058214850329518024383017011981283321159855328511197604575684342221126⟩ ⟨false, 26995252789576740719324676455674121453328572656966385002937728398163888254⟩ = true := by
  decide +kernel

theorem b_205_1600 : bothSeg evalE (oGrid.idx 205) (oGrid.dm 205) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 205) oGrid.kl oGrid.kr 400 1600 ⟨false, 4504715058214850329518024383017011981283321159855328511197604575684342221126⟩ ⟨false, 26995252789576740719324676455674121453328572656966385002937728398163888254⟩ ⟨false, 4340325092210206645304352070921770000108435763879987169029335903865434356238⟩ ⟨false, 191723901610556932039651905793811914638204943852574597312654717358672309270⟩ = true := by
  decide +kernel

theorem b_205_2000 : bothSeg evalE (oGrid.idx 205) (oGrid.dm 205) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 205) oGrid.kl oGrid.kr 400 2000 ⟨false, 4340325092210206645304352070921770000108435763879987169029335903865434356238⟩ ⟨false, 191723901610556932039651905793811914638204943852574597312654717358672309270⟩ ⟨false, 4308897088612889541871410301623058974997880104967044690099479892249816967128⟩ ⟨false, 224029480606038593624291007756242325716517039861563161724112584210443784496⟩ = true := by
  decide +kernel

theorem b_205_2400 : bothLoop evalE (oGrid.idx 205) (oGrid.dm 205) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 205) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4308897088612889541871410301623058974997880104967044690099479892249816967128⟩ ⟨false, 224029480606038593624291007756242325716517039861563161724112584210443784496⟩ = true := by
  decide +kernel

theorem o_row_205 : oGrid.row evalE 205 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_205_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_205_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_205_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_205_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_205_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_205_2000).1 (bothLoop_sound b_205_2400).1))))))

theorem n_row_205 : nGrid.row evalE 205 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_205_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_205_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_205_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_205_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_205_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_205_2000).2 (bothLoop_sound b_205_2400).2))))))

theorem b_206_0 : bothSeg evalE (oGrid.idx 206) (oGrid.dm 206) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 206) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2415908552203118148151080753957334190850428412750457096612977565405245690688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_206_400 : bothSeg evalE (oGrid.idx 206) (oGrid.dm 206) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 206) oGrid.kl oGrid.kr 400 400 ⟨false, 2415908552203118148151080753957334190850428412750457096612977565405245690688⟩ ⟨false, 0⟩ ⟨false, 3905401206690003949309658888773310756665819474770818592867484231898066495818⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_206_800 : bothSeg evalE (oGrid.idx 206) (oGrid.dm 206) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 206) oGrid.kl oGrid.kr 400 800 ⟨false, 3905401206690003949309658888773310756665819474770818592867484231898066495818⟩ ⟨false, 0⟩ ⟨false, 4444621269831432474233568007892153989616832601402423015170393195441307171958⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_206_1200 : bothSeg evalE (oGrid.idx 206) (oGrid.dm 206) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 206) oGrid.kl oGrid.kr 400 1200 ⟨false, 4444621269831432474233568007892153989616832601402423015170393195441307171958⟩ ⟨false, 0⟩ ⟨false, 4485731793302934835298428429159997667780018671852972717668231350186347617720⟩ ⟨false, 27300727553477725121839659106142793945936171877854692230147604031622502532⟩ = true := by
  decide +kernel

theorem b_206_1600 : bothSeg evalE (oGrid.idx 206) (oGrid.dm 206) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 206) oGrid.kl oGrid.kr 400 1600 ⟨false, 4485731793302934835298428429159997667780018671852972717668231350186347617720⟩ ⟨false, 27300727553477725121839659106142793945936171877854692230147604031622502532⟩ ⟨false, 4321608664562757587985222745508849141316622883253082815502583122977504870570⟩ ⟨false, 191763576206790066676472649535653064436792078136104829537364203512098940998⟩ = true := by
  decide +kernel

theorem b_206_2000 : bothSeg evalE (oGrid.idx 206) (oGrid.dm 206) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 206) oGrid.kl oGrid.kr 400 2000 ⟨false, 4321608664562757587985222745508849141316622883253082815502583122977504870570⟩ ⟨false, 191763576206790066676472649535653064436792078136104829537364203512098940998⟩ ⟨false, 4290414924590438466728549929998026702555309774505666059307643818009994520522⟩ ⟨false, 223836675620708854975933168299205430739134579175463747601514423044936571404⟩ = true := by
  decide +kernel

theorem b_206_2400 : bothLoop evalE (oGrid.idx 206) (oGrid.dm 206) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 206) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4290414924590438466728549929998026702555309774505666059307643818009994520522⟩ ⟨false, 223836675620708854975933168299205430739134579175463747601514423044936571404⟩ = true := by
  decide +kernel

theorem o_row_206 : oGrid.row evalE 206 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_206_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_206_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_206_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_206_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_206_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_206_2000).1 (bothLoop_sound b_206_2400).1))))))

theorem n_row_206 : nGrid.row evalE 206 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_206_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_206_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_206_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_206_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_206_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_206_2000).2 (bothLoop_sound b_206_2400).2))))))

theorem b_207_0 : bothSeg evalE (oGrid.idx 207) (oGrid.dm 207) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 207) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2406285561329100524798061593081263347194052722323921648634286621742032866768⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_207_400 : bothSeg evalE (oGrid.idx 207) (oGrid.dm 207) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 207) oGrid.kl oGrid.kr 400 400 ⟨false, 2406285561329100524798061593081263347194052722323921648634286621742032866768⟩ ⟨false, 0⟩ ⟨false, 3889798494523549841606827315281473808547740407350816487533396675916979453794⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_207_800 : bothSeg evalE (oGrid.idx 207) (oGrid.dm 207) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 207) oGrid.kl oGrid.kr 400 800 ⟨false, 3889798494523549841606827315281473808547740407350816487533396675916979453794⟩ ⟨false, 0⟩ ⟨false, 4426571961465254033560067532008738520250841164415598663113959103325972630506⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_207_1200 : bothSeg evalE (oGrid.idx 207) (oGrid.dm 207) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 207) oGrid.kl oGrid.kr 400 1200 ⟨false, 4426571961465254033560067532008738520250841164415598663113959103325972630506⟩ ⟨false, 0⟩ ⟨false, 4466808630289979548346003294263702748415946356246879973719504503106423118440⟩ ⟨false, 27601320858469439582421554499850864025306306702513748684494248996265707600⟩ = true := by
  decide +kernel

theorem b_207_1600 : bothSeg evalE (oGrid.idx 207) (oGrid.dm 207) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 207) oGrid.kl oGrid.kr 400 1600 ⟨false, 4466808630289979548346003294263702748415946356246879973719504503106423118440⟩ ⟨false, 27601320858469439582421554499850864025306306702513748684494248996265707600⟩ ⟨false, 4302948474627993881410473867852965193755786962194204716145503446165098762872⟩ ⟨false, 191802228550882971515861589877795381249938653460631905120141758958695309828⟩ = true := by
  decide +kernel

theorem b_207_2000 : bothSeg evalE (oGrid.idx 207) (oGrid.dm 207) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 207) oGrid.kl oGrid.kr 400 2000 ⟨false, 4302948474627993881410473867852965193755786962194204716145503446165098762872⟩ ⟨false, 191802228550882971515861589877795381249938653460631905120141758958695309828⟩ ⟨false, 4271989157920367336183203222588128794092581377844993726582503325851308190884⟩ ⟨false, 223642892980706091045557836598683292763148511001105265998799378726987189792⟩ = true := by
  decide +kernel

theorem b_207_2400 : bothLoop evalE (oGrid.idx 207) (oGrid.dm 207) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 207) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4271989157920367336183203222588128794092581377844993726582503325851308190884⟩ ⟨false, 223642892980706091045557836598683292763148511001105265998799378726987189792⟩ = true := by
  decide +kernel

theorem o_row_207 : oGrid.row evalE 207 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_207_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_207_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_207_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_207_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_207_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_207_2000).1 (bothLoop_sound b_207_2400).1))))))

theorem n_row_207 : nGrid.row evalE 207 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_207_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_207_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_207_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_207_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_207_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_207_2000).2 (bothLoop_sound b_207_2400).2))))))

theorem b_208_0 : bothSeg evalE (oGrid.idx 208) (oGrid.dm 208) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 208) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2396692273049349152730921760126715821624387453012827790056900023071318743934⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_208_400 : bothSeg evalE (oGrid.idx 208) (oGrid.dm 208) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 208) oGrid.kl oGrid.kr 400 400 ⟨false, 2396692273049349152730921760126715821624387453012827790056900023071318743934⟩ ⟨false, 0⟩ ⟨false, 3874242200946116717635352546827477297884427835371779688115627216550398355702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_208_800 : bothSeg evalE (oGrid.idx 208) (oGrid.dm 208) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 208) oGrid.kl oGrid.kr 400 800 ⟨false, 3874242200946116717635352546827477297884427835371779688115627216550398355702⟩ ⟨false, 0⟩ ⟨false, 4408575302659731296118245512519789765532431013501644795932095801888403774658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_208_1200 : bothSeg evalE (oGrid.idx 208) (oGrid.dm 208) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 208) oGrid.kl oGrid.kr 400 1200 ⟨false, 4408575302659731296118245512519789765532431013501644795932095801888403774658⟩ ⟨false, 0⟩ ⟨false, 4447945652098000696412522681392306575502048800187021946687986120356329427456⟩ ⟨false, 27896897265658802571327966521558845091557439206284162709661131142959980242⟩ = true := by
  decide +kernel

theorem b_208_1600 : bothSeg evalE (oGrid.idx 208) (oGrid.dm 208) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 208) oGrid.kl oGrid.kr 400 1600 ⟨false, 4447945652098000696412522681392306575502048800187021946687986120356329427456⟩ ⟨false, 27896897265658802571327966521558845091557439206284162709661131142959980242⟩ ⟨false, 4284344204323378704760428224389775584897379285410398448627252398186509830176⟩ ⟨false, 191839978509176259597005516759629042816449137706672147780427221280196031564⟩ = true := by
  decide +kernel

theorem b_208_2000 : bothSeg evalE (oGrid.idx 208) (oGrid.dm 208) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 208) oGrid.kl oGrid.kr 400 2000 ⟨false, 4284344204323378704760428224389775584897379285410398448627252398186509830176⟩ ⟨false, 191839978509176259597005516759629042816449137706672147780427221280196031564⟩ ⟨false, 4253619484146991194838564286433584374133105765570720981576847779208195183928⟩ ⟨false, 223447887421439580133799770170519461356372145005165638004014629818599009536⟩ = true := by
  decide +kernel

theorem b_208_2400 : bothLoop evalE (oGrid.idx 208) (oGrid.dm 208) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 208) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4253619484146991194838564286433584374133105765570720981576847779208195183928⟩ ⟨false, 223447887421439580133799770170519461356372145005165638004014629818599009536⟩ = true := by
  decide +kernel

theorem o_row_208 : oGrid.row evalE 208 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_208_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_208_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_208_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_208_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_208_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_208_2000).1 (bothLoop_sound b_208_2400).1))))))

theorem n_row_208 : nGrid.row evalE 208 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_208_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_208_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_208_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_208_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_208_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_208_2000).2 (bothLoop_sound b_208_2400).2))))))

theorem b_209_0 : bothSeg evalE (oGrid.idx 209) (oGrid.dm 209) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 209) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2387128606920038825827626523151459216131386033074929888879088435903183950462⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_209_400 : bothSeg evalE (oGrid.idx 209) (oGrid.dm 209) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 209) oGrid.kl oGrid.kr 400 400 ⟨false, 2387128606920038825827626523151459216131386033074929888879088435903183950462⟩ ⟨false, 0⟩ ⟨false, 3858732131608998110662586710249775486475765044281752250563005266405103905624⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_209_800 : bothSeg evalE (oGrid.idx 209) (oGrid.dm 209) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 209) oGrid.kl oGrid.kr 400 800 ⟨false, 3858732131608998110662586710249775486475765044281752250563005266405103905624⟩ ⟨false, 0⟩ ⟨false, 4390631087734540643777153061480853486929701314528096803049624253733698866558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_209_1200 : bothSeg evalE (oGrid.idx 209) (oGrid.dm 209) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 209) oGrid.kl oGrid.kr 400 1200 ⟨false, 4390631087734540643777153061480853486929701314528096803049624253733698866558⟩ ⟨false, 0⟩ ⟨false, 4429142846563583815352497174346246280077735413613714512470276248599314423610⟩ ⟨false, 28187306453100607823713864719402277925022357249435498433273638090266060570⟩ = true := by
  decide +kernel

theorem b_209_1600 : bothSeg evalE (oGrid.idx 209) (oGrid.dm 209) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 209) oGrid.kl oGrid.kr 400 1600 ⟨false, 4429142846563583815352497174346246280077735413613714512470276248599314423610⟩ ⟨false, 28187306453100607823713864719402277925022357249435498433273638090266060570⟩ ⟨false, 4265795998056509206093306411689823704143507247601654488625399006751141189246⟩ ⟨false, 191876673368829385734047287742081617532888323348260908445465170887003997518⟩ = true := by
  decide +kernel

theorem b_209_2000 : bothSeg evalE (oGrid.idx 209) (oGrid.dm 209) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 209) oGrid.kl oGrid.kr 400 2000 ⟨false, 4265795998056509206093306411689823704143507247601654488625399006751141189246⟩ ⟨false, 191876673368829385734047287742081617532888323348260908445465170887003997518⟩ ⟨false, 4235306059136731306269876094693796210783306721717364051469061679438546030736⟩ ⟨false, 223251767002983937185774997504045221302257717929888679244418001742576537664⟩ = true := by
  decide +kernel

theorem b_209_2400 : bothLoop evalE (oGrid.idx 209) (oGrid.dm 209) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 209) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4235306059136731306269876094693796210783306721717364051469061679438546030736⟩ ⟨false, 223251767002983937185774997504045221302257717929888679244418001742576537664⟩ = true := by
  decide +kernel

theorem o_row_209 : oGrid.row evalE 209 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_209_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_209_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_209_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_209_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_209_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_209_2000).1 (bothLoop_sound b_209_2400).1))))))

theorem n_row_209 : nGrid.row evalE 209 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_209_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_209_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_209_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_209_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_209_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_209_2000).2 (bothLoop_sound b_209_2400).2))))))

theorem b_210_0 : bothSeg evalE (oGrid.idx 210) (oGrid.dm 210) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 210) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2377594508222851391911928999442252894947057406494222734585316535056788775774⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_210_400 : bothSeg evalE (oGrid.idx 210) (oGrid.dm 210) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 210) oGrid.kl oGrid.kr 400 400 ⟨false, 2377594508222851391911928999442252894947057406494222734585316535056788775774⟩ ⟨false, 0⟩ ⟨false, 3843268258007620070780002551862174432225351264493667710582622504815578407294⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_210_800 : bothSeg evalE (oGrid.idx 210) (oGrid.dm 210) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 210) oGrid.kl oGrid.kr 400 800 ⟨false, 3843268258007620070780002551862174432225351264493667710582622504815578407294⟩ ⟨false, 0⟩ ⟨false, 4372739281333818375813168399388583342829730031330468421486560919819634043228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_210_1200 : bothSeg evalE (oGrid.idx 210) (oGrid.dm 210) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 210) oGrid.kl oGrid.kr 400 1200 ⟨false, 4372739281333818375813168399388583342829730031330468421486560919819634043228⟩ ⟨false, 0⟩ ⟨false, 4410400342120682938064167946290000281472512388060246388924940786438431488822⟩ ⟨false, 28472393283142753781542000101364713228682475380500770439975306357950477406⟩ = true := by
  decide +kernel

theorem b_210_1600 : bothSeg evalE (oGrid.idx 210) (oGrid.dm 210) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 210) oGrid.kl oGrid.kr 400 1600 ⟨false, 4410400342120682938064167946290000281472512388060246388924940786438431488822⟩ ⟨false, 28472393283142753781542000101364713228682475380500770439975306357950477406⟩ ⟨false, 4247303663062046044605537112533269950383773124019350562604929891988973706790⟩ ⟨false, 191912450191676593937497992833369248505859961019591243420715988570590757512⟩ = true := by
  decide +kernel

theorem b_210_2000 : bothSeg evalE (oGrid.idx 210) (oGrid.dm 210) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 210) oGrid.kl oGrid.kr 400 2000 ⟨false, 4247303663062046044605537112533269950383773124019350562604929891988973706790⟩ ⟨false, 191912450191676593937497992833369248505859961019591243420715988570590757512⟩ ⟨false, 4217048689404994484227718560237314410781643449086273627894997362417034856528⟩ ⟨false, 223054461238006525267118479912517656833504627858974408126400197528303535894⟩ = true := by
  decide +kernel

theorem b_210_2400 : bothLoop evalE (oGrid.idx 210) (oGrid.dm 210) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 210) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4217048689404994484227718560237314410781643449086273627894997362417034856528⟩ ⟨false, 223054461238006525267118479912517656833504627858974408126400197528303535894⟩ = true := by
  decide +kernel

theorem o_row_210 : oGrid.row evalE 210 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_210_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_210_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_210_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_210_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_210_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_210_2000).1 (bothLoop_sound b_210_2400).1))))))

theorem n_row_210 : nGrid.row evalE 210 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_210_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_210_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_210_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_210_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_210_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_210_2000).2 (bothLoop_sound b_210_2400).2))))))

theorem b_211_0 : bothSeg evalE (oGrid.idx 211) (oGrid.dm 211) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 211) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2368089898266406779355721402637472726409607757694178961554331074184936320520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_211_400 : bothSeg evalE (oGrid.idx 211) (oGrid.dm 211) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 211) oGrid.kl oGrid.kr 400 400 ⟨false, 2368089898266406779355721402637472726409607757694178961554331074184936320520⟩ ⟨false, 0⟩ ⟨false, 3827850441924217521740696924069522557351931195977775278661554395944178110552⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_211_800 : bothSeg evalE (oGrid.idx 211) (oGrid.dm 211) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 211) oGrid.kl oGrid.kr 400 800 ⟨false, 3827850441924217521740696924069522557351931195977775278661554395944178110552⟩ ⟨false, 0⟩ ⟨false, 4354899747861785185718718020321322277436877058420586159171988202963586673632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_211_1200 : bothSeg evalE (oGrid.idx 211) (oGrid.dm 211) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 211) oGrid.kl oGrid.kr 400 1200 ⟨false, 4354899747861785185718718020321322277436877058420586159171988202963586673632⟩ ⟨false, 0⟩ ⟨false, 4391718003895525089316178917781416352021134144465370183322117820994185803028⟩ ⟨false, 28752132268128273193394935541713437468461617886187333788255956701144143344⟩ = true := by
  decide +kernel

theorem b_211_1600 : bothSeg evalE (oGrid.idx 211) (oGrid.dm 211) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 211) oGrid.kl oGrid.kr 400 1600 ⟨false, 4391718003895525089316178917781416352021134144465370183322117820994185803028⟩ ⟨false, 28752132268128273193394935541713437468461617886187333788255956701144143344⟩ ⟨false, 4228866980127726474074262465361779321977747967603055465603817475159296080384⟩ ⟨false, 191947252410036238041068633488538987653286430445541987780039251271513925912⟩ = true := by
  decide +kernel

theorem b_211_2000 : bothSeg evalE (oGrid.idx 211) (oGrid.dm 211) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 211) oGrid.kl oGrid.kr 400 2000 ⟨false, 4228866980127726474074262465361779321977747967603055465603817475159296080384⟩ ⟨false, 191947252410036238041068633488538987653286430445541987780039251271513925912⟩ ⟨false, 4198847201631019003125071902347474112710318405504575990311768134633015129792⟩ ⟨false, 222855948220435835308014586749237332219207369980966218751746017826282140244⟩ = true := by
  decide +kernel

theorem b_211_2400 : bothLoop evalE (oGrid.idx 211) (oGrid.dm 211) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 211) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4198847201631019003125071902347474112710318405504575990311768134633015129792⟩ ⟨false, 222855948220435835308014586749237332219207369980966218751746017826282140244⟩ = true := by
  decide +kernel

theorem o_row_211 : oGrid.row evalE 211 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_211_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_211_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_211_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_211_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_211_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_211_2000).1 (bothLoop_sound b_211_2400).1))))))

theorem n_row_211 : nGrid.row evalE 211 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_211_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_211_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_211_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_211_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_211_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_211_2000).2 (bothLoop_sound b_211_2400).2))))))

theorem b_212_0 : bothSeg evalE (oGrid.idx 212) (oGrid.dm 212) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 212) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2358614642652505254458241306997984005165874778947802295389930754565819897016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_212_400 : bothSeg evalE (oGrid.idx 212) (oGrid.dm 212) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 212) oGrid.kl oGrid.kr 400 400 ⟨false, 2358614642652505254458241306997984005165874778947802295389930754565819897016⟩ ⟨false, 0⟩ ⟨false, 3812478559478006548819560454010477373265372854686731119969325747271619624980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_212_800 : bothSeg evalE (oGrid.idx 212) (oGrid.dm 212) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 212) oGrid.kl oGrid.kr 400 800 ⟨false, 3812478559478006548819560454010477373265372854686731119969325747271619624980⟩ ⟨false, 0⟩ ⟨false, 4337112328354975256982768791643906198694647600553093983461517982506820383892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_212_1200 : bothSeg evalE (oGrid.idx 212) (oGrid.dm 212) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 212) oGrid.kl oGrid.kr 400 1200 ⟨false, 4337112328354975256982768791643906198694647600553093983461517982506820383892⟩ ⟨false, 0⟩ ⟨false, 4373095912999190706821778015279186811354957081962565642024415003696765364422⟩ ⟨false, 29026285936818628331154941913887038643653108162606943389725305203189245886⟩ = true := by
  decide +kernel

theorem b_212_1600 : bothSeg evalE (oGrid.idx 212) (oGrid.dm 212) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 212) oGrid.kl oGrid.kr 400 1600 ⟨false, 4373095912999190706821778015279186811354957081962565642024415003696765364422⟩ ⟨false, 29026285936818628331154941913887038643653108162606943389725305203189245886⟩ ⟨false, 4210485980882540254891127712203335828040504384000426872627096397826823326102⟩ ⟨false, 191981097299428951011294998148151260995870371972111956572248205328982930320⟩ = true := by
  decide +kernel

theorem b_212_2000 : bothSeg evalE (oGrid.idx 212) (oGrid.dm 212) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 212) oGrid.kl oGrid.kr 400 2000 ⟨false, 4210485980882540254891127712203335828040504384000426872627096397826823326102⟩ ⟨false, 191981097299428951011294998148151260995870371972111956572248205328982930320⟩ ⟨false, 4180701622892514191042513652676866911580297209498641329300548994312117253758⟩ ⟨false, 222656384626183216156120819973818335975789889853819637618729692811900139852⟩ = true := by
  decide +kernel

theorem b_212_2400 : bothLoop evalE (oGrid.idx 212) (oGrid.dm 212) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 212) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4180701622892514191042513652676866911580297209498641329300548994312117253758⟩ ⟨false, 222656384626183216156120819973818335975789889853819637618729692811900139852⟩ = true := by
  decide +kernel

theorem o_row_212 : oGrid.row evalE 212 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_212_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_212_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_212_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_212_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_212_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_212_2000).1 (bothLoop_sound b_212_2400).1))))))

theorem n_row_212 : nGrid.row evalE 212 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_212_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_212_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_212_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_212_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_212_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_212_2000).2 (bothLoop_sound b_212_2400).2))))))

theorem b_213_0 : bothSeg evalE (oGrid.idx 213) (oGrid.dm 213) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 213) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2349168720486599923244002018392381775822958868969290923638779686040830150748⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_213_400 : bothSeg evalE (oGrid.idx 213) (oGrid.dm 213) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 213) oGrid.kl oGrid.kr 400 400 ⟨false, 2349168720486599923244002018392381775822958868969290923638779686040830150748⟩ ⟨false, 0⟩ ⟨false, 3797152515841213118662014476530986296684078572970234924878009904504322323270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_213_800 : bothSeg evalE (oGrid.idx 213) (oGrid.dm 213) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 213) oGrid.kl oGrid.kr 400 800 ⟨false, 3797152515841213118662014476530986296684078572970234924878009904504322323270⟩ ⟨false, 0⟩ ⟨false, 4319376966593526517071288447290398622434114241287827726534367979430896150804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_213_1200 : bothSeg evalE (oGrid.idx 213) (oGrid.dm 213) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 213) oGrid.kl oGrid.kr 400 1200 ⟨false, 4319376966593526517071288447290398622434114241287827726534367979430896150804⟩ ⟨false, 0⟩ ⟨false, 4354534155191868680178211974047495001759918276514872958442492783226677991722⟩ ⟨false, 29294736434257802197697417073156785262628172635342454842455249330625492108⟩ = true := by
  decide +kernel

theorem b_213_1600 : bothSeg evalE (oGrid.idx 213) (oGrid.dm 213) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 213) oGrid.kl oGrid.kr 400 1600 ⟨false, 4354534155191868680178211974047495001759918276514872958442492783226677991722⟩ ⟨false, 29294736434257802197697417073156785262628172635342454842455249330625492108⟩ ⟨false, 4192160461026011347339706404904238378258965266501211667405280947680214855870⟩ ⟨false, 192014328536938319600943511416146293246914053221660268512343144326264091800⟩ = true := by
  decide +kernel

theorem b_213_2000 : bothSeg evalE (oGrid.idx 213) (oGrid.dm 213) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 213) oGrid.kl oGrid.kr 400 2000 ⟨false, 4192160461026011347339706404904238378258965266501211667405280947680214855870⟩ ⟨false, 192014328536938319600943511416146293246914053221660268512343144326264091800⟩ ⟨false, 4162611763336084172072210578725830008978276278253225079854764796999296164418⟩ ⟨false, 222456127247458093303099145089360241757806609762876721612025807136429237202⟩ = true := by
  decide +kernel

theorem b_213_2400 : bothLoop evalE (oGrid.idx 213) (oGrid.dm 213) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 213) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4162611763336084172072210578725830008978276278253225079854764796999296164418⟩ ⟨false, 222456127247458093303099145089360241757806609762876721612025807136429237202⟩ = true := by
  decide +kernel

theorem o_row_213 : oGrid.row evalE 213 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_213_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_213_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_213_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_213_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_213_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_213_2000).1 (bothLoop_sound b_213_2400).1))))))

theorem n_row_213 : nGrid.row evalE 213 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_213_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_213_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_213_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_213_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_213_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_213_2000).2 (bothLoop_sound b_213_2400).2))))))

theorem b_214_0 : bothSeg evalE (oGrid.idx 214) (oGrid.dm 214) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 214) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2339752021050081569492518431517509711916179781505480628744167139321006721354⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_214_400 : bothSeg evalE (oGrid.idx 214) (oGrid.dm 214) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 214) oGrid.kl oGrid.kr 400 400 ⟨false, 2339752021050081569492518431517509711916179781505480628744167139321006721354⟩ ⟨false, 0⟩ ⟨false, 3781872176891912495181182202209414345693902757938922034013964354389553011406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_214_800 : bothSeg evalE (oGrid.idx 214) (oGrid.dm 214) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 214) oGrid.kl oGrid.kr 400 800 ⟨false, 3781872176891912495181182202209414345693902757938922034013964354389553011406⟩ ⟨false, 0⟩ ⟨false, 4301693505360401711150435427672843392766715189367620765634727897046510984754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_214_1200 : bothSeg evalE (oGrid.idx 214) (oGrid.dm 214) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 214) oGrid.kl oGrid.kr 400 1200 ⟨false, 4301693505360401711150435427672843392766715189367620765634727897046510984754⟩ ⟨false, 0⟩ ⟨false, 4336032612546440547424309989281660085806399454276128394610280336803264131838⟩ ⟨false, 29557411405532488917942976604931660157567248426110499966945607215723541128⟩ = true := by
  decide +kernel

theorem b_214_1600 : bothSeg evalE (oGrid.idx 214) (oGrid.dm 214) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 214) oGrid.kl oGrid.kr 400 1600 ⟨false, 4336032612546440547424309989281660085806399454276128394610280336803264131838⟩ ⟨false, 29557411405532488917942976604931660157567248426110499966945607215723541128⟩ ⟨false, 4173890202878243906511917201972149954259960119901896439654606691111613445192⟩ ⟨false, 192046686971561651813472118558706396457636425608906591304687049228802934206⟩ = true := by
  decide +kernel

theorem b_214_2000 : bothSeg evalE (oGrid.idx 214) (oGrid.dm 214) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 214) oGrid.kl oGrid.kr 400 2000 ⟨false, 4173890202878243906511917201972149954259960119901896439654606691111613445192⟩ ⟨false, 192046686971561651813472118558706396457636425608906591304687049228802934206⟩ ⟨false, 4144577436125517492511899463017764995118090771809652946965121772801284423628⟩ ⟨false, 222256720881415570974981289451848947651393804677617525340789651096431621290⟩ = true := by
  decide +kernel

theorem b_214_2400 : bothLoop evalE (oGrid.idx 214) (oGrid.dm 214) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 214) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4144577436125517492511899463017764995118090771809652946965121772801284423628⟩ ⟨false, 222256720881415570974981289451848947651393804677617525340789651096431621290⟩ = true := by
  decide +kernel

theorem o_row_214 : oGrid.row evalE 214 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_214_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_214_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_214_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_214_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_214_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_214_2000).1 (bothLoop_sound b_214_2400).1))))))

theorem n_row_214 : nGrid.row evalE 214 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_214_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_214_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_214_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_214_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_214_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_214_2000).2 (bothLoop_sound b_214_2400).2))))))

theorem b_215_0 : bothSeg evalE (oGrid.idx 215) (oGrid.dm 215) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 215) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 2330364458535934702834227071045515027321763007077401105052427041801258653068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_215_400 : bothSeg evalE (oGrid.idx 215) (oGrid.dm 215) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 215) oGrid.kl oGrid.kr 400 400 ⟨false, 2330364458535934702834227071045515027321763007077401105052427041801258653068⟩ ⟨false, 0⟩ ⟨false, 3766637437578537412965830583071830402709721389360116331935646981900271453232⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_215_800 : bothSeg evalE (oGrid.idx 215) (oGrid.dm 215) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 215) oGrid.kl oGrid.kr 400 800 ⟨false, 3766637437578537412965830583071830402709721389360116331935646981900271453232⟩ ⟨false, 0⟩ ⟨false, 4284061838377636825414433987766361552969155930014477643317339690094382531558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_215_1200 : bothSeg evalE (oGrid.idx 215) (oGrid.dm 215) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 215) oGrid.kl oGrid.kr 400 1200 ⟨false, 4284061838377636825414433987766361552969155930014477643317339690094382531558⟩ ⟨false, 0⟩ ⟨false, 4317591281704562179135669297062147716002756851836914052407574524335957478204⟩ ⟨false, 29814213152128942087954470875525337096054020460218103452864469997594368290⟩ = true := by
  decide +kernel

theorem b_215_1600 : bothSeg evalE (oGrid.idx 215) (oGrid.dm 215) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 215) oGrid.kl oGrid.kr 400 1600 ⟨false, 4317591281704562179135669297062147716002756851836914052407574524335957478204⟩ ⟨false, 29814213152128942087954470875525337096054020460218103452864469997594368290⟩ ⟨false, 4155675371661069608428040138623395246873469426671974466257751440799602892216⟩ ⟨false, 192077975035010443623695639465931201376243291496362009652232923174066883604⟩ = true := by
  decide +kernel

theorem b_215_2000 : bothSeg evalE (oGrid.idx 215) (oGrid.dm 215) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 215) oGrid.kl oGrid.kr 400 2000 ⟨false, 4155675371661069608428040138623395246873469426671974466257751440799602892216⟩ ⟨false, 192077975035010443623695639465931201376243291496362009652232923174066883604⟩ ⟨false, 4126598788202249546554042593526152323318011989124584462980629133418304295182⟩ ⟨false, 222057365730917575562322075322441288521171212991233286466285590278180107666⟩ = true := by
  decide +kernel

theorem b_215_2400 : bothLoop evalE (oGrid.idx 215) (oGrid.dm 215) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 215) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 4126598788202249546554042593526152323318011989124584462980629133418304295182⟩ ⟨false, 222057365730917575562322075322441288521171212991233286466285590278180107666⟩ = true := by
  decide +kernel

theorem o_row_215 : oGrid.row evalE 215 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_215_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_215_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_215_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_215_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_215_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_215_2000).1 (bothLoop_sound b_215_2400).1))))))

theorem n_row_215 : nGrid.row evalE 215 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_215_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_215_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_215_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_215_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_215_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_215_2000).2 (bothLoop_sound b_215_2400).2))))))

theorem o_blk_192 : allFrom (fun j => oGrid.row evalE j) 192 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 192) o_row_192 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 193) o_row_193 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 194) o_row_194 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 195) o_row_195 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 196) o_row_196 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 197) o_row_197 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 198) o_row_198 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 199) o_row_199 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 200) o_row_200 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 201) o_row_201 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 202) o_row_202 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 203) o_row_203 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 204) o_row_204 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 205) o_row_205 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 206) o_row_206 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 207) o_row_207 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 208) o_row_208 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 209) o_row_209 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 210) o_row_210 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 211) o_row_211 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 212) o_row_212 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 213) o_row_213 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 214) o_row_214 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 215) o_row_215 (allFrom_zero (fun j => oGrid.row evalE j) 216)))))))))))))))))))))))))

theorem n_blk_192 : allFrom (fun j => nGrid.row evalE j) 192 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 192) n_row_192 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 193) n_row_193 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 194) n_row_194 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 195) n_row_195 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 196) n_row_196 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 197) n_row_197 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 198) n_row_198 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 199) n_row_199 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 200) n_row_200 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 201) n_row_201 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 202) n_row_202 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 203) n_row_203 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 204) n_row_204 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 205) n_row_205 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 206) n_row_206 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 207) n_row_207 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 208) n_row_208 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 209) n_row_209 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 210) n_row_210 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 211) n_row_211 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 212) n_row_212 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 213) n_row_213 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 214) n_row_214 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 215) n_row_215 (allFrom_zero (fun j => nGrid.row evalE j) 216)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
