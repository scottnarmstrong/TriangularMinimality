/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 69 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1656`–`1679`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1656_0 : bothSeg evalE (oGrid.idx 1656) (oGrid.dm 1656) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1656) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64379227218149762034310398309087721216784116943517673049603920923570838444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1656_400 : bothSeg evalE (oGrid.idx 1656) (oGrid.dm 1656) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1656) oGrid.kl oGrid.kr 400 400 ⟨false, 64379227218149762034310398309087721216784116943517673049603920923570838444⟩ ⟨false, 0⟩ ⟨false, 146337571510401292834958678493283174881630732390688590840796374108758741270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1656_800 : bothSeg evalE (oGrid.idx 1656) (oGrid.dm 1656) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1656) oGrid.kl oGrid.kr 400 800 ⟨false, 146337571510401292834958678493283174881630732390688590840796374108758741270⟩ ⟨false, 0⟩ ⟨false, 260841027785020508919533084839163872889730784420501380659330425375244845908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1656_1200 : bothSeg evalE (oGrid.idx 1656) (oGrid.dm 1656) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1656) oGrid.kl oGrid.kr 400 1200 ⟨false, 260841027785020508919533084839163872889730784420501380659330425375244845908⟩ ⟨false, 0⟩ ⟨false, 416901610652404051008657906893356330892521449698724219820033776627651747824⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1656_1600 : bothSeg evalE (oGrid.idx 1656) (oGrid.dm 1656) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1656) oGrid.kl oGrid.kr 400 1600 ⟨false, 416901610652404051008657906893356330892521449698724219820033776627651747824⟩ ⟨false, 0⟩ ⟨false, 618200953232632628542863307685250275389669091873930837004653930586729415596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1656_2000 : bothSeg evalE (oGrid.idx 1656) (oGrid.dm 1656) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1656) oGrid.kl oGrid.kr 400 2000 ⟨false, 618200953232632628542863307685250275389669091873930837004653930586729415596⟩ ⟨false, 0⟩ ⟨false, 864045261008924317331697915784032878056899980877465461832628554437155693538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1656_2400 : bothLoop evalE (oGrid.idx 1656) (oGrid.dm 1656) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1656) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 864045261008924317331697915784032878056899980877465461832628554437155693538⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1656 : oGrid.row evalE 1656 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1656_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1656_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1656_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1656_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1656_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1656_2000).1 (bothLoop_sound b_1656_2400).1))))))

theorem n_row_1656 : nGrid.row evalE 1656 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1656_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1656_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1656_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1656_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1656_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1656_2000).2 (bothLoop_sound b_1656_2400).2))))))

theorem b_1657_0 : bothSeg evalE (oGrid.idx 1657) (oGrid.dm 1657) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1657) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64703936787248516593976913992364903703611223965761434880320737783741097284⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1657_400 : bothSeg evalE (oGrid.idx 1657) (oGrid.dm 1657) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1657) oGrid.kl oGrid.kr 400 400 ⟨false, 64703936787248516593976913992364903703611223965761434880320737783741097284⟩ ⟨false, 0⟩ ⟨false, 147032898561396898735397251761689871723418608306112515043735681165029356844⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1657_800 : bothSeg evalE (oGrid.idx 1657) (oGrid.dm 1657) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1657) oGrid.kl oGrid.kr 400 800 ⟨false, 147032898561396898735397251761689871723418608306112515043735681165029356844⟩ ⟨false, 0⟩ ⟨false, 261875531755250429394255695696498247531380037810428965163630484933013257736⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1657_1200 : bothSeg evalE (oGrid.idx 1657) (oGrid.dm 1657) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1657) oGrid.kl oGrid.kr 400 1200 ⟨false, 261875531755250429394255695696498247531380037810428965163630484933013257736⟩ ⟨false, 0⟩ ⟨false, 418239278859559206539504352594980804979311882878772251261274397537144319602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1657_1600 : bothSeg evalE (oGrid.idx 1657) (oGrid.dm 1657) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1657) oGrid.kl oGrid.kr 400 1600 ⟨false, 418239278859559206539504352594980804979311882878772251261274397537144319602⟩ ⟨false, 0⟩ ⟨false, 619808198359505997273141069698654204570062320795150642502626941925915352472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1657_2000 : bothSeg evalE (oGrid.idx 1657) (oGrid.dm 1657) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1657) oGrid.kl oGrid.kr 400 2000 ⟨false, 619808198359505997273141069698654204570062320795150642502626941925915352472⟩ ⟨false, 0⟩ ⟨false, 865894270617255418273437949855197238289691113949744843458772753725015419952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1657_2400 : bothLoop evalE (oGrid.idx 1657) (oGrid.dm 1657) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1657) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 865894270617255418273437949855197238289691113949744843458772753725015419952⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1657 : oGrid.row evalE 1657 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1657_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1657_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1657_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1657_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1657_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1657_2000).1 (bothLoop_sound b_1657_2400).1))))))

theorem n_row_1657 : nGrid.row evalE 1657 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1657_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1657_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1657_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1657_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1657_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1657_2000).2 (bothLoop_sound b_1657_2400).2))))))

theorem b_1658_0 : bothSeg evalE (oGrid.idx 1658) (oGrid.dm 1658) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1658) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65035260808932021883586024699292371660697130772033928294225016813213214624⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1658_400 : bothSeg evalE (oGrid.idx 1658) (oGrid.dm 1658) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1658) oGrid.kl oGrid.kr 400 400 ⟨false, 65035260808932021883586024699292371660697130772033928294225016813213214624⟩ ⟨false, 0⟩ ⟨false, 147734737811206630704456879054906100206510195352889953326071653114161503594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1658_800 : bothSeg evalE (oGrid.idx 1658) (oGrid.dm 1658) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1658) oGrid.kl oGrid.kr 400 800 ⟨false, 147734737811206630704456879054906100206510195352889953326071653114161503594⟩ ⟨false, 0⟩ ⟨false, 262916485053435824648316543314181291231057129296953214021175459609453449600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1658_1200 : bothSeg evalE (oGrid.idx 1658) (oGrid.dm 1658) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1658) oGrid.kl oGrid.kr 400 1200 ⟨false, 262916485053435824648316543314181291231057129296953214021175459609453449600⟩ ⟨false, 0⟩ ⟨false, 419583372391034121124148566742655969935774207624179690394241567893952078692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1658_1600 : bothSeg evalE (oGrid.idx 1658) (oGrid.dm 1658) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1658) oGrid.kl oGrid.kr 400 1600 ⟨false, 419583372391034121124148566742655969935774207624179690394241567893952078692⟩ ⟨false, 0⟩ ⟨false, 621421874124644060649645404191828412381766302048943216643117865572665917330⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1658_2000 : bothSeg evalE (oGrid.idx 1658) (oGrid.dm 1658) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1658) oGrid.kl oGrid.kr 400 2000 ⟨false, 621421874124644060649645404191828412381766302048943216643117865572665917330⟩ ⟨false, 0⟩ ⟨false, 867749733862401781277210011236506624225083313626055670659712432989108557996⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1658_2400 : bothLoop evalE (oGrid.idx 1658) (oGrid.dm 1658) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1658) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 867749733862401781277210011236506624225083313626055670659712432989108557996⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1658 : oGrid.row evalE 1658 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1658_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1658_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1658_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1658_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1658_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1658_2000).1 (bothLoop_sound b_1658_2400).1))))))

theorem n_row_1658 : nGrid.row evalE 1658 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1658_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1658_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1658_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1658_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1658_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1658_2000).2 (bothLoop_sound b_1658_2400).2))))))

theorem b_1659_0 : bothSeg evalE (oGrid.idx 1659) (oGrid.dm 1659) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1659) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65372780410096579123904662657101230310034259343884962875944288350871614442⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1659_400 : bothSeg evalE (oGrid.idx 1659) (oGrid.dm 1659) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1659) oGrid.kl oGrid.kr 400 400 ⟨false, 65372780410096579123904662657101230310034259343884962875944288350871614442⟩ ⟨false, 0⟩ ⟨false, 148442670477146447305834083322642684587831594604590956108845377806555924476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1659_800 : bothSeg evalE (oGrid.idx 1659) (oGrid.dm 1659) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1659) oGrid.kl oGrid.kr 400 800 ⟨false, 148442670477146447305834083322642684587831594604590956108845377806555924476⟩ ⟨false, 0⟩ ⟨false, 263963468927488345219431595815810269919490252317049600078866580175044024380⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1659_1200 : bothSeg evalE (oGrid.idx 1659) (oGrid.dm 1659) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1659) oGrid.kl oGrid.kr 400 1200 ⟨false, 263963468927488345219431595815810269919490252317049600078866580175044024380⟩ ⟨false, 0⟩ ⟨false, 420933472477088150611748874655123144003293839416231708793897869117670893280⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1659_1600 : bothSeg evalE (oGrid.idx 1659) (oGrid.dm 1659) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1659) oGrid.kl oGrid.kr 400 1600 ⟨false, 420933472477088150611748874655123144003293839416231708793897869117670893280⟩ ⟨false, 0⟩ ⟨false, 623041561715401620026962351545574087754212238554868235249794761520363850950⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1659_2000 : bothSeg evalE (oGrid.idx 1659) (oGrid.dm 1659) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1659) oGrid.kl oGrid.kr 400 2000 ⟨false, 623041561715401620026962351545574087754212238554868235249794761520363850950⟩ ⟨false, 0⟩ ⟨false, 869611231883049681056154897460176193434746368941158470978102435707070291594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1659_2400 : bothLoop evalE (oGrid.idx 1659) (oGrid.dm 1659) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1659) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 869611231883049681056154897460176193434746368941158470978102435707070291594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1659 : oGrid.row evalE 1659 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1659_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1659_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1659_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1659_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1659_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1659_2000).1 (bothLoop_sound b_1659_2400).1))))))

theorem n_row_1659 : nGrid.row evalE 1659 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1659_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1659_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1659_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1659_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1659_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1659_2000).2 (bothLoop_sound b_1659_2400).2))))))

theorem b_1660_0 : bothSeg evalE (oGrid.idx 1660) (oGrid.dm 1660) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1660) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 65716082357288569039853372786553551476914309690070242062794582394058425902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1660_400 : bothSeg evalE (oGrid.idx 1660) (oGrid.dm 1660) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1660) oGrid.kl oGrid.kr 400 400 ⟨false, 65716082357288569039853372786553551476914309690070242062794582394058425902⟩ ⟨false, 0⟩ ⟨false, 149156283416084260297213197462626823132694196675849010310946328380055718886⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1660_800 : bothSeg evalE (oGrid.idx 1660) (oGrid.dm 1660) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1660) oGrid.kl oGrid.kr 400 800 ⟨false, 149156283416084260297213197462626823132694196675849010310946328380055718886⟩ ⟨false, 0⟩ ⟨false, 265016070264878857357457495391970948750345161001056025325392051014236559326⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1660_1200 : bothSeg evalE (oGrid.idx 1660) (oGrid.dm 1660) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1660) oGrid.kl oGrid.kr 400 1200 ⟨false, 265016070264878857357457495391970948750345161001056025325392051014236559326⟩ ⟨false, 0⟩ ⟨false, 422289165987610652613549205238214207050894109561879034532604124321469583632⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1660_1600 : bothSeg evalE (oGrid.idx 1660) (oGrid.dm 1660) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1660) oGrid.kl oGrid.kr 400 1600 ⟨false, 422289165987610652613549205238214207050894109561879034532604124321469583632⟩ ⟨false, 0⟩ ⟨false, 624666847958846936171250420431257930494725483388942809467015077517138515284⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1660_2000 : bothSeg evalE (oGrid.idx 1660) (oGrid.dm 1660) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1660) oGrid.kl oGrid.kr 400 2000 ⟨false, 624666847958846936171250420431257930494725483388942809467015077517138515284⟩ ⟨false, 0⟩ ⟨false, 871478351457665867525236852629223903157644397192487393388323018930863346954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1660_2400 : bothLoop evalE (oGrid.idx 1660) (oGrid.dm 1660) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1660) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 871478351457665867525236852629223903157644397192487393388323018930863346954⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1660 : oGrid.row evalE 1660 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1660_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1660_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1660_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1660_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1660_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1660_2000).1 (bothLoop_sound b_1660_2400).1))))))

theorem n_row_1660 : nGrid.row evalE 1660 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1660_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1660_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1660_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1660_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1660_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1660_2000).2 (bothLoop_sound b_1660_2400).2))))))

theorem b_1661_0 : bothSeg evalE (oGrid.idx 1661) (oGrid.dm 1661) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1661) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66064758984974545659687695788593148554159705608164098260321488077209569484⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1661_400 : bothSeg evalE (oGrid.idx 1661) (oGrid.dm 1661) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1661) oGrid.kl oGrid.kr 400 400 ⟨false, 66064758984974545659687695788593148554159705608164098260321488077209569484⟩ ⟨false, 0⟩ ⟨false, 149875169052710144409385483173207326019445641666065623255506565782139719062⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1661_800 : bothSeg evalE (oGrid.idx 1661) (oGrid.dm 1661) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1661) oGrid.kl oGrid.kr 400 800 ⟨false, 149875169052710144409385483173207326019445641666065623255506565782139719062⟩ ⟨false, 0⟩ ⟨false, 266073881520907560744320913387102400192185572341548896243918483860630035166⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1661_1200 : bothSeg evalE (oGrid.idx 1661) (oGrid.dm 1661) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1661) oGrid.kl oGrid.kr 400 1200 ⟨false, 266073881520907560744320913387102400192185572341548896243918483860630035166⟩ ⟨false, 0⟩ ⟨false, 423650045360390934858533952024956302464740535438097026900164650482146122532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1661_1600 : bothSeg evalE (oGrid.idx 1661) (oGrid.dm 1661) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1661) oGrid.kl oGrid.kr 400 1600 ⟨false, 423650045360390934858533952024956302464740535438097026900164650482146122532⟩ ⟨false, 0⟩ ⟨false, 626297325250031539573606279940539043271280290094289444967092670791511237398⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1661_2000 : bothSeg evalE (oGrid.idx 1661) (oGrid.dm 1661) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1661) oGrid.kl oGrid.kr 400 2000 ⟨false, 626297325250031539573606279940539043271280290094289444967092670791511237398⟩ ⟨false, 0⟩ ⟨false, 873350684932767301376489592270774489512189318429214335600546235871212730710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1661_2400 : bothLoop evalE (oGrid.idx 1661) (oGrid.dm 1661) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1661) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 873350684932767301376489592270774489512189318429214335600546235871212730710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1661 : oGrid.row evalE 1661 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1661_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1661_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1661_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1661_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1661_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1661_2000).1 (bothLoop_sound b_1661_2400).1))))))

theorem n_row_1661 : nGrid.row evalE 1661 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1661_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1661_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1661_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1661_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1661_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1661_2000).2 (bothLoop_sound b_1661_2400).2))))))

theorem b_1662_0 : bothSeg evalE (oGrid.idx 1662) (oGrid.dm 1662) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1662) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66418411313719251677849444181266544283423304869929154057606078646266932650⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1662_400 : bothSeg evalE (oGrid.idx 1662) (oGrid.dm 1662) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1662) oGrid.kl oGrid.kr 400 400 ⟨false, 66418411313719251677849444181266544283423304869929154057606078646266932650⟩ ⟨false, 0⟩ ⟨false, 150598928497714468569613155558389005248112023849266973427940857617209814384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1662_800 : bothSeg evalE (oGrid.idx 1662) (oGrid.dm 1662) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1662) oGrid.kl oGrid.kr 400 800 ⟨false, 150598928497714468569613155558389005248112023849266973427940857617209814384⟩ ⟨false, 0⟩ ⟨false, 267136503836882027984907606492099437064474316069486812259786103355346457842⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1662_1200 : bothSeg evalE (oGrid.idx 1662) (oGrid.dm 1662) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1662) oGrid.kl oGrid.kr 400 1200 ⟨false, 267136503836882027984907606492099437064474316069486812259786103355346457842⟩ ⟨false, 0⟩ ⟨false, 425015711719296125692169488414478304356795391015060895814656793322401367604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1662_1600 : bothSeg evalE (oGrid.idx 1662) (oGrid.dm 1662) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1662) oGrid.kl oGrid.kr 400 1600 ⟨false, 425015711719296125692169488414478304356795391015060895814656793322401367604⟩ ⟨false, 0⟩ ⟨false, 627932594670167963106944292593593163906200222051743121191453791298866788256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1662_2000 : bothSeg evalE (oGrid.idx 1662) (oGrid.dm 1662) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1662) oGrid.kl oGrid.kr 400 2000 ⟨false, 627932594670167963106944292593593163906200222051743121191453791298866788256⟩ ⟨false, 0⟩ ⟨false, 875227833341098812040219818622722228562544401726488669506373045436681472964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1662_2400 : bothLoop evalE (oGrid.idx 1662) (oGrid.dm 1662) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1662) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 875227833341098812040219818622722228562544401726488669506373045436681472964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1662 : oGrid.row evalE 1662 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1662_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1662_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1662_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1662_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1662_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1662_2000).1 (bothLoop_sound b_1662_2400).1))))))

theorem n_row_1662 : nGrid.row evalE 1662 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1662_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1662_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1662_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1662_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1662_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1662_2000).2 (bothLoop_sound b_1662_2400).2))))))

theorem b_1663_0 : bothSeg evalE (oGrid.idx 1663) (oGrid.dm 1663) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1663) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66776643786468829702002389038240258536878830158250705413421056865564042182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1663_400 : bothSeg evalE (oGrid.idx 1663) (oGrid.dm 1663) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1663) oGrid.kl oGrid.kr 400 400 ⟨false, 66776643786468829702002389038240258536878830158250705413421056865564042182⟩ ⟨false, 0⟩ ⟨false, 151327166284071222889737547134927403465867426669228188216968971576882209388⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1663_800 : bothSeg evalE (oGrid.idx 1663) (oGrid.dm 1663) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1663) oGrid.kl oGrid.kr 400 800 ⟨false, 151327166284071222889737547134927403465867426669228188216968971576882209388⟩ ⟨false, 0⟩ ⟨false, 268203541776400440188391086352148168857263988832863431045572049608186770946⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1663_1200 : bothSeg evalE (oGrid.idx 1663) (oGrid.dm 1663) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1663) oGrid.kl oGrid.kr 400 1200 ⟨false, 268203541776400440188391086352148168857263988832863431045572049608186770946⟩ ⟨false, 0⟩ ⟨false, 426385769610554241036929152802789234636826379098166894146088703771398290498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1663_1600 : bothSeg evalE (oGrid.idx 1663) (oGrid.dm 1663) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1663) oGrid.kl oGrid.kr 400 1600 ⟨false, 426385769610554241036929152802789234636826379098166894146088703771398290498⟩ ⟨false, 0⟩ ⟨false, 629572260722912671344889886484091606230098283899879298480348562015396806208⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1663_2000 : bothSeg evalE (oGrid.idx 1663) (oGrid.dm 1663) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1663) oGrid.kl oGrid.kr 400 2000 ⟨false, 629572260722912671344889886484091606230098283899879298480348562015396806208⟩ ⟨false, 0⟩ ⟨false, 877109401137915952350787225600906742721019417688419020512373842007272583416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1663_2400 : bothLoop evalE (oGrid.idx 1663) (oGrid.dm 1663) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1663) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 877109401137915952350787225600906742721019417688419020512373842007272583416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1663 : oGrid.row evalE 1663 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1663_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1663_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1663_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1663_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1663_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1663_2000).1 (bothLoop_sound b_1663_2400).1))))))

theorem n_row_1663 : nGrid.row evalE 1663 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1663_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1663_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1663_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1663_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1663_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1663_2000).2 (bothLoop_sound b_1663_2400).2))))))

theorem b_1664_0 : bothSeg evalE (oGrid.idx 1664) (oGrid.dm 1664) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1664) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 67139071129601983523518551785343972665023573666769237346294178528618275738⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1664_400 : bothSeg evalE (oGrid.idx 1664) (oGrid.dm 1664) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1664) oGrid.kl oGrid.kr 400 400 ⟨false, 67139071129601983523518551785343972665023573666769237346294178528618275738⟩ ⟨false, 0⟩ ⟨false, 152059497228089295558283199609651474486355957510976537084341021050933333846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1664_800 : bothSeg evalE (oGrid.idx 1664) (oGrid.dm 1664) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1664) oGrid.kl oGrid.kr 400 800 ⟨false, 152059497228089295558283199609651474486355957510976537084341021050933333846⟩ ⟨false, 0⟩ ⟨false, 269274610186402772778236499015808464510495203705102555934229489880706135080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1664_1200 : bothSeg evalE (oGrid.idx 1664) (oGrid.dm 1664) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1664) oGrid.kl oGrid.kr 400 1200 ⟨false, 269274610186402772778236499015808464510495203705102555934229489880706135080⟩ ⟨false, 0⟩ ⟨false, 427759833863805201952055706816354070503566497863726357343943119654144657016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1664_1600 : bothSeg evalE (oGrid.idx 1664) (oGrid.dm 1664) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1664) oGrid.kl oGrid.kr 400 1600 ⟨false, 427759833863805201952055706816354070503566497863726357343943119654144657016⟩ ⟨false, 0⟩ ⟨false, 631215938195416940679943740689156649538152055268750258780412444424128619096⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1664_2000 : bothSeg evalE (oGrid.idx 1664) (oGrid.dm 1664) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1664) oGrid.kl oGrid.kr 400 2000 ⟨false, 631215938195416940679943740689156649538152055268750258780412444424128619096⟩ ⟨false, 0⟩ ⟨false, 878995003062035804054336336420269130695606521283494795532717270855035584744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1664_2400 : bothLoop evalE (oGrid.idx 1664) (oGrid.dm 1664) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1664) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 878995003062035804054336336420269130695606521283494795532717270855035584744⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1664 : oGrid.row evalE 1664 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1664_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1664_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1664_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1664_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1664_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1664_2000).1 (bothLoop_sound b_1664_2400).1))))))

theorem n_row_1664 : nGrid.row evalE 1664 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1664_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1664_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1664_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1664_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1664_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1664_2000).2 (bothLoop_sound b_1664_2400).2))))))

theorem b_1665_0 : bothSeg evalE (oGrid.idx 1665) (oGrid.dm 1665) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1665) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 67505315051512524027576908580989597783108149619615589931484970819871197514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1665_400 : bothSeg evalE (oGrid.idx 1665) (oGrid.dm 1665) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1665) oGrid.kl oGrid.kr 400 400 ⟨false, 67505315051512524027576908580989597783108149619615589931484970819871197514⟩ ⟨false, 0⟩ ⟨false, 152795543127995134252706157873968884431147913310964042250500658073492406932⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1665_800 : bothSeg evalE (oGrid.idx 1665) (oGrid.dm 1665) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1665) oGrid.kl oGrid.kr 400 800 ⟨false, 152795543127995134252706157873968884431147913310964042250500658073492406932⟩ ⟨false, 0⟩ ⟨false, 270349330895753366146014916455403864155977310140287769896667004484144287994⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1665_1200 : bothSeg evalE (oGrid.idx 1665) (oGrid.dm 1665) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1665) oGrid.kl oGrid.kr 400 1200 ⟨false, 270349330895753366146014916455403864155977310140287769896667004484144287994⟩ ⟨false, 0⟩ ⟨false, 429137526290683237406916376973167456293152979489132019416103917689774755910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1665_1600 : bothSeg evalE (oGrid.idx 1665) (oGrid.dm 1665) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1665) oGrid.kl oGrid.kr 400 1600 ⟨false, 429137526290683237406916376973167456293152979489132019416103917689774755910⟩ ⟨false, 0⟩ ⟨false, 632863248856909124855074655829762756298392228775660941419665750740099076822⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1665_2000 : bothSeg evalE (oGrid.idx 1665) (oGrid.dm 1665) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1665) oGrid.kl oGrid.kr 400 2000 ⟨false, 632863248856909124855074655829762756298392228775660941419665750740099076822⟩ ⟨false, 0⟩ ⟨false, 880884260834419168772755784382172912487191147394735729924723707097852236906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1665_2400 : bothLoop evalE (oGrid.idx 1665) (oGrid.dm 1665) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1665) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 880884260834419168772755784382172912487191147394735729924723707097852236906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1665 : oGrid.row evalE 1665 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1665_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1665_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1665_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1665_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1665_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1665_2000).1 (bothLoop_sound b_1665_2400).1))))))

theorem n_row_1665 : nGrid.row evalE 1665 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1665_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1665_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1665_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1665_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1665_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1665_2000).2 (bothLoop_sound b_1665_2400).2))))))

theorem b_1666_0 : bothSeg evalE (oGrid.idx 1666) (oGrid.dm 1666) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1666) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 67875006233638012784609514641732344538751406774560666807978412067221988142⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1666_400 : bothSeg evalE (oGrid.idx 1666) (oGrid.dm 1666) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1666) oGrid.kl oGrid.kr 400 400 ⟨false, 67875006233638012784609514641732344538751406774560666807978412067221988142⟩ ⟨false, 0⟩ ⟨false, 153534934754961505113508808228960598364968889164153726064301800371452786340⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1666_800 : bothSeg evalE (oGrid.idx 1666) (oGrid.dm 1666) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1666) oGrid.kl oGrid.kr 400 800 ⟨false, 153534934754961505113508808228960598364968889164153726064301800371452786340⟩ ⟨false, 0⟩ ⟨false, 271427334706269594189740420037714412086623996488561959586265586989290807448⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1666_1200 : bothSeg evalE (oGrid.idx 1666) (oGrid.dm 1666) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1666) oGrid.kl oGrid.kr 400 1200 ⟨false, 271427334706269594189740420037714412086623996488561959586265586989290807448⟩ ⟨false, 0⟩ ⟨false, 430518477675845385307884266961422429896831464763105470984294212318960457404⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1666_1600 : bothSeg evalE (oGrid.idx 1666) (oGrid.dm 1666) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1666) oGrid.kl oGrid.kr 400 1600 ⟨false, 430518477675845385307884266961422429896831464763105470984294212318960457404⟩ ⟨false, 0⟩ ⟨false, 634513823449723018948477451457105152586101146207795706698051638189853000140⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1666_2000 : bothSeg evalE (oGrid.idx 1666) (oGrid.dm 1666) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1666) oGrid.kl oGrid.kr 400 2000 ⟨false, 634513823449723018948477451457105152586101146207795706698051638189853000140⟩ ⟨false, 0⟩ ⟨false, 882776805149198857463718488832464797095542053206586011997463002715210138450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1666_2400 : bothLoop evalE (oGrid.idx 1666) (oGrid.dm 1666) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1666) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 882776805149198857463718488832464797095542053206586011997463002715210138450⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1666 : oGrid.row evalE 1666 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1666_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1666_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1666_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1666_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1666_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1666_2000).1 (bothLoop_sound b_1666_2400).1))))))

theorem n_row_1666 : nGrid.row evalE 1666 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1666_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1666_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1666_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1666_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1666_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1666_2000).2 (bothLoop_sound b_1666_2400).2))))))

theorem b_1667_0 : bothSeg evalE (oGrid.idx 1667) (oGrid.dm 1667) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1667) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 68247782277441518776592814905859222545205820164859126046244114175128893540⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1667_400 : bothSeg evalE (oGrid.idx 1667) (oGrid.dm 1667) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1667) oGrid.kl oGrid.kr 400 400 ⟨false, 68247782277441518776592814905859222545205820164859126046244114175128893540⟩ ⟨false, 0⟩ ⟨false, 154277309800089364733707224464408682329343581003750751241232839914049110618⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1667_800 : bothSeg evalE (oGrid.idx 1667) (oGrid.dm 1667) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1667) oGrid.kl oGrid.kr 400 800 ⟨false, 154277309800089364733707224464408682329343581003750751241232839914049110618⟩ ⟨false, 0⟩ ⟨false, 272508259339703646189209077903466266512407033213390054663651221627961351446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1667_1200 : bothSeg evalE (oGrid.idx 1667) (oGrid.dm 1667) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1667) oGrid.kl oGrid.kr 400 1200 ⟨false, 272508259339703646189209077903466266512407033213390054663651221627961351446⟩ ⟨false, 0⟩ ⟨false, 431902325723953107230448146926940642236991743704709256109465431908943791440⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1667_1600 : bothSeg evalE (oGrid.idx 1667) (oGrid.dm 1667) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1667) oGrid.kl oGrid.kr 400 1600 ⟨false, 431902325723953107230448146926940642236991743704709256109465431908943791440⟩ ⟨false, 0⟩ ⟨false, 636167299636279337263000246337220003897028496321968302289017237292577404988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1667_2000 : bothSeg evalE (oGrid.idx 1667) (oGrid.dm 1667) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1667) oGrid.kl oGrid.kr 400 2000 ⟨false, 636167299636279337263000246337220003897028496321968302289017237292577404988⟩ ⟨false, 0⟩ ⟨false, 884672273620661093828423566310572373810364223622542112299451703859538647974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1667_2400 : bothLoop evalE (oGrid.idx 1667) (oGrid.dm 1667) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1667) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 884672273620661093828423566310572373810364223622542112299451703859538647974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1667 : oGrid.row evalE 1667 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1667_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1667_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1667_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1667_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1667_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1667_2000).1 (bothLoop_sound b_1667_2400).1))))))

theorem n_row_1667 : nGrid.row evalE 1667 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1667_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1667_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1667_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1667_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1667_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1667_2000).2 (bothLoop_sound b_1667_2400).2))))))

theorem b_1668_0 : bothSeg evalE (oGrid.idx 1668) (oGrid.dm 1668) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1668) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 68623297059456518946959960661335033036201045576528336056313978626765547206⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1668_400 : bothSeg evalE (oGrid.idx 1668) (oGrid.dm 1668) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1668) oGrid.kl oGrid.kr 400 400 ⟨false, 68623297059456518946959960661335033036201045576528336056313978626765547206⟩ ⟨false, 0⟩ ⟨false, 155022322229452875852415896099636005344487115182465350501266818377313615706⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1668_800 : bothSeg evalE (oGrid.idx 1668) (oGrid.dm 1668) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1668) oGrid.kl oGrid.kr 400 800 ⟨false, 155022322229452875852415896099636005344487115182465350501266818377313615706⟩ ⟨false, 0⟩ ⟨false, 273591758792787452706100919785050764164378625554800681644831074601048834190⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1668_1200 : bothSeg evalE (oGrid.idx 1668) (oGrid.dm 1668) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1668) oGrid.kl oGrid.kr 400 1200 ⟨false, 273591758792787452706100919785050764164378625554800681644831074601048834190⟩ ⟨false, 0⟩ ⟨false, 433288724414717047543536122756559376221302560214830566389192159287807869864⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1668_1600 : bothSeg evalE (oGrid.idx 1668) (oGrid.dm 1668) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1668) oGrid.kl oGrid.kr 400 1600 ⟨false, 433288724414717047543536122756559376221302560214830566389192159287807869864⟩ ⟨false, 0⟩ ⟨false, 637823331354130335807028771758790255789966656105880736252388662620484899150⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1668_2000 : bothSeg evalE (oGrid.idx 1668) (oGrid.dm 1668) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1668) oGrid.kl oGrid.kr 400 2000 ⟨false, 637823331354130335807028771758790255789966656105880736252388662620484899150⟩ ⟨false, 0⟩ ⟨false, 886570320138290062353943486493922738706616749010989656776015527361000262760⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1668_2400 : bothLoop evalE (oGrid.idx 1668) (oGrid.dm 1668) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1668) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 886570320138290062353943486493922738706616749010989656776015527361000262760⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1668 : oGrid.row evalE 1668 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1668_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1668_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1668_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1668_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1668_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1668_2000).1 (bothLoop_sound b_1668_2400).1))))))

theorem n_row_1668 : nGrid.row evalE 1668 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1668_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1668_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1668_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1668_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1668_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1668_2000).2 (bothLoop_sound b_1668_2400).2))))))

theorem b_1669_0 : bothSeg evalE (oGrid.idx 1669) (oGrid.dm 1669) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1669) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69001209000551545416848880588356134092600901062490991612832941044195258270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1669_400 : bothSeg evalE (oGrid.idx 1669) (oGrid.dm 1669) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1669) oGrid.kl oGrid.kr 400 400 ⟨false, 69001209000551545416848880588356134092600901062490991612832941044195258270⟩ ⟨false, 0⟩ ⟨false, 155769630553364169595254494267187306288126048957396402942448713968861441910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1669_800 : bothSeg evalE (oGrid.idx 1669) (oGrid.dm 1669) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1669) oGrid.kl oGrid.kr 400 800 ⟨false, 155769630553364169595254494267187306288126048957396402942448713968861441910⟩ ⟨false, 0⟩ ⟨false, 274677491606497358350548875297978229315983943610460396120885303195355687474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1669_1200 : bothSeg evalE (oGrid.idx 1669) (oGrid.dm 1669) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1669) oGrid.kl oGrid.kr 400 1200 ⟨false, 274677491606497358350548875297978229315983943610460396120885303195355687474⟩ ⟨false, 0⟩ ⟨false, 434677332272161539766983043777795526246103593086076757200898539303950341006⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1669_1600 : bothSeg evalE (oGrid.idx 1669) (oGrid.dm 1669) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1669) oGrid.kl oGrid.kr 400 1600 ⟨false, 434677332272161539766983043777795526246103593086076757200898539303950341006⟩ ⟨false, 0⟩ ⟨false, 639481577085224182207559523129669687741523617491595973007633849753738767912⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1669_2000 : bothSeg evalE (oGrid.idx 1669) (oGrid.dm 1669) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1669) oGrid.kl oGrid.kr 400 2000 ⟨false, 639481577085224182207559523129669687741523617491595973007633849753738767912⟩ ⟨false, 0⟩ ⟨false, 888470603136032203831023515122040363850232090394619896582452278237854209218⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1669_2400 : bothLoop evalE (oGrid.idx 1669) (oGrid.dm 1669) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1669) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 888470603136032203831023515122040363850232090394619896582452278237854209218⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1669 : oGrid.row evalE 1669 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1669_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1669_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1669_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1669_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1669_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1669_2000).1 (bothLoop_sound b_1669_2400).1))))))

theorem n_row_1669 : nGrid.row evalE 1669 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1669_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1669_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1669_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1669_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1669_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1669_2000).2 (bothLoop_sound b_1669_2400).2))))))

theorem b_1670_0 : bothSeg evalE (oGrid.idx 1670) (oGrid.dm 1670) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1670) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69381191515743255799353844069128899558751748749424995344555275703028320422⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1670_400 : bothSeg evalE (oGrid.idx 1670) (oGrid.dm 1670) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1670) oGrid.kl oGrid.kr 400 400 ⟨false, 69381191515743255799353844069128899558751748749424995344555275703028320422⟩ ⟨false, 0⟩ ⟨false, 156518908276186530693235167395365693720187477733143765302986429694580907574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1670_800 : bothSeg evalE (oGrid.idx 1670) (oGrid.dm 1670) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1670) oGrid.kl oGrid.kr 400 800 ⟨false, 156518908276186530693235167395365693720187477733143765302986429694580907574⟩ ⟨false, 0⟩ ⟨false, 275765131315867217844835550225581140864057806632278003692434351444719849674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1670_1200 : bothSeg evalE (oGrid.idx 1670) (oGrid.dm 1670) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1670) oGrid.kl oGrid.kr 400 1200 ⟨false, 275765131315867217844835550225581140864057806632278003692434351444719849674⟩ ⟨false, 0⟩ ⟨false, 436067822814437536592029906606607037873071592454814659913779057150897837178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1670_1600 : bothSeg evalE (oGrid.idx 1670) (oGrid.dm 1670) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1670) oGrid.kl oGrid.kr 400 1600 ⟨false, 436067822814437536592029906606607037873071592454814659913779057150897837178⟩ ⟨false, 0⟩ ⟨false, 641141710305717749485151756387444182997883214041616288318398170703138434920⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1670_2000 : bothSeg evalE (oGrid.idx 1670) (oGrid.dm 1670) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1670) oGrid.kl oGrid.kr 400 2000 ⟨false, 641141710305717749485151756387444182997883214041616288318398170703138434920⟩ ⟨false, 0⟩ ⟨false, 890372796042108934777138066687849041499160981697153022877317259116971817044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1670_2400 : bothLoop evalE (oGrid.idx 1670) (oGrid.dm 1670) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1670) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 890372796042108934777138066687849041499160981697153022877317259116971817044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1670 : oGrid.row evalE 1670 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1670_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1670_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1670_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1670_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1670_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1670_2000).1 (bothLoop_sound b_1670_2400).1))))))

theorem n_row_1670 : nGrid.row evalE 1670 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1670_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1670_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1670_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1670_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1670_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1670_2000).2 (bothLoop_sound b_1670_2400).2))))))

theorem b_1671_0 : bothSeg evalE (oGrid.idx 1671) (oGrid.dm 1671) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1671) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69762929822845830393675540653472823684750425246343316108414641131259096694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1671_400 : bothSeg evalE (oGrid.idx 1671) (oGrid.dm 1671) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1671) oGrid.kl oGrid.kr 400 400 ⟨false, 69762929822845830393675540653472823684750425246343316108414641131259096694⟩ ⟨false, 0⟩ ⟨false, 157269840704983909462016987102753250889423884325979701550863066662612888692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1671_800 : bothSeg evalE (oGrid.idx 1671) (oGrid.dm 1671) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1671) oGrid.kl oGrid.kr 400 800 ⟨false, 157269840704983909462016987102753250889423884325979701550863066662612888692⟩ ⟨false, 0⟩ ⟨false, 276854363258637819165109905888219161393861508537971885432471882904704489164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1671_1200 : bothSeg evalE (oGrid.idx 1671) (oGrid.dm 1671) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1671) oGrid.kl oGrid.kr 400 1200 ⟨false, 276854363258637819165109905888219161393861508537971885432471882904704489164⟩ ⟨false, 0⟩ ⟨false, 437459881362471867344976192173249614185544837995406451017363681628809510126⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1671_1600 : bothSeg evalE (oGrid.idx 1671) (oGrid.dm 1671) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1671) oGrid.kl oGrid.kr 400 1600 ⟨false, 437459881362471867344976192173249614185544837995406451017363681628809510126⟩ ⟨false, 0⟩ ⟨false, 642803416294625737470680819226619844683977370167465224485337043077549795636⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1671_2000 : bothSeg evalE (oGrid.idx 1671) (oGrid.dm 1671) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1671) oGrid.kl oGrid.kr 400 2000 ⟨false, 642803416294625737470680819226619844683977370167465224485337043077549795636⟩ ⟨false, 0⟩ ⟨false, 892276584087665694544840454404027658405248548368965426345187204820378798904⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1671_2400 : bothLoop evalE (oGrid.idx 1671) (oGrid.dm 1671) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1671) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 892276584087665694544840454404027658405248548368965426345187204820378798904⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1671 : oGrid.row evalE 1671 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1671_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1671_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1671_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1671_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1671_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1671_2000).1 (bothLoop_sound b_1671_2400).1))))))

theorem n_row_1671 : nGrid.row evalE 1671 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1671_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1671_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1671_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1671_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1671_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1671_2000).2 (bothLoop_sound b_1671_2400).2))))))

theorem b_1672_0 : bothSeg evalE (oGrid.idx 1672) (oGrid.dm 1672) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1672) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70146122016380591625526916627435238794387045289669946436703643663966433468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1672_400 : bothSeg evalE (oGrid.idx 1672) (oGrid.dm 1672) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1672) oGrid.kl oGrid.kr 400 400 ⟨false, 70146122016380591625526916627435238794387045289669946436703643663966433468⟩ ⟨false, 0⟩ ⟨false, 158022126023430655907877218971082681510704491862532777167073095722025958982⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1672_800 : bothSeg evalE (oGrid.idx 1672) (oGrid.dm 1672) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1672) oGrid.kl oGrid.kr 400 800 ⟨false, 158022126023430655907877218971082681510704491862532777167073095722025958982⟩ ⟨false, 0⟩ ⟨false, 277944885649166529126482013791105120983285273114136967317906445003518254224⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1672_1200 : bothSeg evalE (oGrid.idx 1672) (oGrid.dm 1672) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1672) oGrid.kl oGrid.kr 400 1200 ⟨false, 277944885649166529126482013791105120983285273114136967317906445003518254224⟩ ⟨false, 0⟩ ⟨false, 438853206113876718258573666683023423673046531710539418194001165547856565892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1672_1600 : bothSeg evalE (oGrid.idx 1672) (oGrid.dm 1672) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1672) oGrid.kl oGrid.kr 400 1600 ⟨false, 438853206113876718258573666683023423673046531710539418194001165547856565892⟩ ⟨false, 0⟩ ⟨false, 644466393207730017228282707271754497546458112507072344203468813060001269692⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1672_2000 : bothSeg evalE (oGrid.idx 1672) (oGrid.dm 1672) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1672) oGrid.kl oGrid.kr 400 2000 ⟨false, 644466393207730017228282707271754497546458112507072344203468813060001269692⟩ ⟨false, 0⟩ ⟨false, 894181665380681215479909308217499441882895430468838769211561541886205545298⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1672_2400 : bothLoop evalE (oGrid.idx 1672) (oGrid.dm 1672) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1672) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 894181665380681215479909308217499441882895430468838769211561541886205545298⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1672 : oGrid.row evalE 1672 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1672_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1672_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1672_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1672_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1672_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1672_2000).1 (bothLoop_sound b_1672_2400).1))))))

theorem n_row_1672 : nGrid.row evalE 1672 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1672_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1672_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1672_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1672_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1672_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1672_2000).2 (bothLoop_sound b_1672_2400).2))))))

theorem b_1673_0 : bothSeg evalE (oGrid.idx 1673) (oGrid.dm 1673) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1673) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70530480317993084413158082910148178526699499491310564178273538175257753498⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1673_400 : bothSeg evalE (oGrid.idx 1673) (oGrid.dm 1673) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1673) oGrid.kl oGrid.kr 400 400 ⟨false, 70530480317993084413158082910148178526699499491310564178273538175257753498⟩ ⟨false, 0⟩ ⟨false, 158775476542228714639755998333927911889043329283685000248495447091056754908⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1673_800 : bothSeg evalE (oGrid.idx 1673) (oGrid.dm 1673) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1673) oGrid.kl oGrid.kr 400 800 ⟨false, 158775476542228714639755998333927911889043329283685000248495447091056754908⟩ ⟨false, 0⟩ ⟨false, 279036410828844400089864006629922912927323722232539205428458996576857507718⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1673_1200 : bothSeg evalE (oGrid.idx 1673) (oGrid.dm 1673) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1673) oGrid.kl oGrid.kr 400 1200 ⟨false, 279036410828844400089864006629922912927323722232539205428458996576857507718⟩ ⟨false, 0⟩ ⟨false, 440247509393366574228761610673752872710384238249081861930625819288431282504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1673_1600 : bothSeg evalE (oGrid.idx 1673) (oGrid.dm 1673) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1673) oGrid.kl oGrid.kr 400 1600 ⟨false, 440247509393366574228761610673752872710384238249081861930625819288431282504⟩ ⟨false, 0⟩ ⟨false, 646130353327996437161890977341728182592797435547968175972847326133895507372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1673_2000 : bothSeg evalE (oGrid.idx 1673) (oGrid.dm 1673) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1673) oGrid.kl oGrid.kr 400 2000 ⟨false, 646130353327996437161890977341728182592797435547968175972847326133895507372⟩ ⟨false, 0⟩ ⟨false, 896087752156384254806805558690744003998900855250609995723076980007245281220⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1673_2400 : bothLoop evalE (oGrid.idx 1673) (oGrid.dm 1673) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1673) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 896087752156384254806805558690744003998900855250609995723076980007245281220⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1673 : oGrid.row evalE 1673 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1673_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1673_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1673_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1673_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1673_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1673_2000).1 (bothLoop_sound b_1673_2400).1))))))

theorem n_row_1673 : nGrid.row evalE 1673 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1673_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1673_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1673_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1673_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1673_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1673_2000).2 (bothLoop_sound b_1673_2400).2))))))

theorem b_1674_0 : bothSeg evalE (oGrid.idx 1674) (oGrid.dm 1674) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1674) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70915735703259633011567997454491265014632109159585521129724777704120378944⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1674_400 : bothSeg evalE (oGrid.idx 1674) (oGrid.dm 1674) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1674) oGrid.kl oGrid.kr 400 400 ⟨false, 70915735703259633011567997454491265014632109159585521129724777704120378944⟩ ⟨false, 0⟩ ⟨false, 159529623325914296139936207385245997879925782953376659125645506998554656964⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1674_800 : bothSeg evalE (oGrid.idx 1674) (oGrid.dm 1674) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1674) oGrid.kl oGrid.kr 400 800 ⟨false, 159529623325914296139936207385245997879925782953376659125645506998554656964⟩ ⟨false, 0⟩ ⟨false, 280128669892902753342133596907474955841657360076206988214658557936710192832⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1674_1200 : bothSeg evalE (oGrid.idx 1674) (oGrid.dm 1674) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1674) oGrid.kl oGrid.kr 400 1200 ⟨false, 280128669892902753342133596907474955841657360076206988214658557936710192832⟩ ⟨false, 0⟩ ⟨false, 441642522279564637607553172920579477042977909421112420161965121188656091146⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1674_1600 : bothSeg evalE (oGrid.idx 1674) (oGrid.dm 1674) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1674) oGrid.kl oGrid.kr 400 1600 ⟨false, 441642522279564637607553172920579477042977909421112420161965121188656091146⟩ ⟨false, 0⟩ ⟨false, 647795027692381106355976693350915380523973254323853624018252039785633426570⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1674_2000 : bothSeg evalE (oGrid.idx 1674) (oGrid.dm 1674) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1674) oGrid.kl oGrid.kr 400 2000 ⟨false, 647795027692381106355976693350915380523973254323853624018252039785633426570⟩ ⟨false, 0⟩ ⟨false, 897994575404059803792162814885930388359804957961105876198589984571900506382⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1674_2400 : bothLoop evalE (oGrid.idx 1674) (oGrid.dm 1674) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1674) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 897994575404059803792162814885930388359804957961105876198589984571900506382⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1674 : oGrid.row evalE 1674 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1674_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1674_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1674_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1674_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1674_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1674_2000).1 (bothLoop_sound b_1674_2400).1))))))

theorem n_row_1674 : nGrid.row evalE 1674 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1674_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1674_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1674_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1674_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1674_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1674_2000).2 (bothLoop_sound b_1674_2400).2))))))

theorem b_1675_0 : bothSeg evalE (oGrid.idx 1675) (oGrid.dm 1675) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1675) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 71301637340072221065810508211214613865313858895597780535687602020597484980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1675_400 : bothSeg evalE (oGrid.idx 1675) (oGrid.dm 1675) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1675) oGrid.kl oGrid.kr 400 400 ⟨false, 71301637340072221065810508211214613865313858895597780535687602020597484980⟩ ⟨false, 0⟩ ⟨false, 160284315631242871124261055059946620671363670282009330252681262080261633660⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1675_800 : bothSeg evalE (oGrid.idx 1675) (oGrid.dm 1675) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1675) oGrid.kl oGrid.kr 400 800 ⟨false, 160284315631242871124261055059946620671363670282009330252681262080261633660⟩ ⟨false, 0⟩ ⟨false, 281221412128798085879540264192934792075008329594783319393847266503563103104⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1675_1200 : bothSeg evalE (oGrid.idx 1675) (oGrid.dm 1675) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1675) oGrid.kl oGrid.kr 400 1200 ⟨false, 281221412128798085879540264192934792075008329594783319393847266503563103104⟩ ⟨false, 0⟩ ⟨false, 443037994043387570761227756024969798438020720948838109299754406576168786228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1675_1600 : bothSeg evalE (oGrid.idx 1675) (oGrid.dm 1675) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1675) oGrid.kl oGrid.kr 400 1600 ⟨false, 443037994043387570761227756024969798438020720948838109299754406576168786228⟩ ⟨false, 0⟩ ⟨false, 649460165530215001879447103482306296455189332359628681829220039805942111626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1675_2000 : bothSeg evalE (oGrid.idx 1675) (oGrid.dm 1675) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1675) oGrid.kl oGrid.kr 400 2000 ⟨false, 649460165530215001879447103482306296455189332359628681829220039805942111626⟩ ⟨false, 0⟩ ⟨false, 899901884305433620915378376276694819394336327496655282980050716737315648270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1675_2400 : bothLoop evalE (oGrid.idx 1675) (oGrid.dm 1675) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1675) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 899901884305433620915378376276694819394336327496655282980050716737315648270⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1675 : oGrid.row evalE 1675 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1675_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1675_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1675_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1675_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1675_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1675_2000).1 (bothLoop_sound b_1675_2400).1))))))

theorem n_row_1675 : nGrid.row evalE 1675 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1675_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1675_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1675_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1675_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1675_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1675_2000).2 (bothLoop_sound b_1675_2400).2))))))

theorem b_1676_0 : bothSeg evalE (oGrid.idx 1676) (oGrid.dm 1676) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1676) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 71687954156669879308149821654798397866083587088457264482290317266167116178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1676_400 : bothSeg evalE (oGrid.idx 1676) (oGrid.dm 1676) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1676) oGrid.kl oGrid.kr 400 400 ⟨false, 71687954156669879308149821654798397866083587088457264482290317266167116178⟩ ⟨false, 0⟩ ⟨false, 161039322475220672426640157413695901072305853861829194787284639418926803346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1676_800 : bothSeg evalE (oGrid.idx 1676) (oGrid.dm 1676) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1676) oGrid.kl oGrid.kr 400 800 ⟨false, 161039322475220672426640157413695901072305853861829194787284639418926803346⟩ ⟨false, 0⟩ ⟨false, 282314406584243485028125523612248686198170960785062982038785185756225903846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1676_1200 : bothSeg evalE (oGrid.idx 1676) (oGrid.dm 1676) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1676) oGrid.kl oGrid.kr 400 1200 ⟨false, 282314406584243485028125523612248686198170960785062982038785185756225903846⟩ ⟨false, 0⟩ ⟨false, 444433693716076746826837130281778493456759323120153636170951717121985775186⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1676_1600 : bothSeg evalE (oGrid.idx 1676) (oGrid.dm 1676) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1676) oGrid.kl oGrid.kr 400 1600 ⟨false, 444433693716076746826837130281778493456759323120153636170951717121985775186⟩ ⟨false, 0⟩ ⟨false, 651125535831235084485511352208825270471371697329114386454656342064268949022⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1676_2000 : bothSeg evalE (oGrid.idx 1676) (oGrid.dm 1676) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1676) oGrid.kl oGrid.kr 400 2000 ⟨false, 651125535831235084485511352208825270471371697329114386454656342064268949022⟩ ⟨false, 0⟩ ⟨false, 901809447802703273479224114331720244653916263918809847468427097484644839052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1676_2400 : bothLoop evalE (oGrid.idx 1676) (oGrid.dm 1676) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1676) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 901809447802703273479224114331720244653916263918809847468427097484644839052⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1676 : oGrid.row evalE 1676 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1676_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1676_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1676_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1676_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1676_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1676_2000).1 (bothLoop_sound b_1676_2400).1))))))

theorem n_row_1676 : nGrid.row evalE 1676 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1676_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1676_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1676_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1676_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1676_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1676_2000).2 (bothLoop_sound b_1676_2400).2))))))

theorem b_1677_0 : bothSeg evalE (oGrid.idx 1677) (oGrid.dm 1677) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1677) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72074483243364433620176826232676849162925972220821174885430214739380705174⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1677_400 : bothSeg evalE (oGrid.idx 1677) (oGrid.dm 1677) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1677) oGrid.kl oGrid.kr 400 400 ⟨false, 72074483243364433620176826232676849162925972220821174885430214739380705174⟩ ⟨false, 0⟩ ⟨false, 161794441036830557128952093025688099533670401405475129217596711667047797426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1677_800 : bothSeg evalE (oGrid.idx 1677) (oGrid.dm 1677) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1677) oGrid.kl oGrid.kr 400 800 ⟨false, 161794441036830557128952093025688099533670401405475129217596711667047797426⟩ ⟨false, 0⟩ ⟨false, 283407450468934403621288870917402781877143071437565182656783008788188895546⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1677_1200 : bothSeg evalE (oGrid.idx 1677) (oGrid.dm 1677) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1677) oGrid.kl oGrid.kr 400 1200 ⟨false, 283407450468934403621288870917402781877143071437565182656783008788188895546⟩ ⟨false, 0⟩ ⟨false, 445829418490923861386394631268038623173434896210160268157420518242679951534⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1677_1600 : bothSeg evalE (oGrid.idx 1677) (oGrid.dm 1677) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1677) oGrid.kl oGrid.kr 400 1600 ⟨false, 445829418490923861386394631268038623173434896210160268157420518242679951534⟩ ⟨false, 0⟩ ⟨false, 652790935747309775426683006944690823025268763585031072337125365577205176674⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1677_2000 : bothSeg evalE (oGrid.idx 1677) (oGrid.dm 1677) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1677) oGrid.kl oGrid.kr 400 2000 ⟨false, 652790935747309775426683006944690823025268763585031072337125365577205176674⟩ ⟨false, 0⟩ ⟨false, 903717063000263540379757328172392785518428568094408307544032380650992419626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1677_2400 : bothLoop evalE (oGrid.idx 1677) (oGrid.dm 1677) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1677) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 903717063000263540379757328172392785518428568094408307544032380650992419626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1677 : oGrid.row evalE 1677 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1677_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1677_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1677_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1677_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1677_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1677_2000).1 (bothLoop_sound b_1677_2400).1))))))

theorem n_row_1677 : nGrid.row evalE 1677 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1677_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1677_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1677_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1677_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1677_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1677_2000).2 (bothLoop_sound b_1677_2400).2))))))

theorem b_1678_0 : bothSeg evalE (oGrid.idx 1678) (oGrid.dm 1678) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1678) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72461052824550705619324779299368379207379730125523772967259799245404528608⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1678_400 : bothSeg evalE (oGrid.idx 1678) (oGrid.dm 1678) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1678) oGrid.kl oGrid.kr 400 400 ⟨false, 72461052824550705619324779299368379207379730125523772967259799245404528608⟩ ⟨false, 0⟩ ⟨false, 162549499629042321095779294702273507826687518830696771769701343987555586274⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1678_800 : bothSeg evalE (oGrid.idx 1678) (oGrid.dm 1678) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1678) oGrid.kl oGrid.kr 400 800 ⟨false, 162549499629042321095779294702273507826687518830696771769701343987555586274⟩ ⟨false, 0⟩ ⟨false, 284500372126558887892961882908657426746050644618737803271692703365665903206⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1678_1200 : bothSeg evalE (oGrid.idx 1678) (oGrid.dm 1678) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1678) oGrid.kl oGrid.kr 400 1200 ⟨false, 284500372126558887892961882908657426746050644618737803271692703365665903206⟩ ⟨false, 0⟩ ⟨false, 447224996695280997216449154003620991110285011397254491288034029817996184652⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1678_1600 : bothSeg evalE (oGrid.idx 1678) (oGrid.dm 1678) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1678) oGrid.kl oGrid.kr 400 1600 ⟨false, 447224996695280997216449154003620991110285011397254491288034029817996184652⟩ ⟨false, 0⟩ ⟨false, 654456193564448886542421356032633398901752134968477780813356337588708912634⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1678_2000 : bothSeg evalE (oGrid.idx 1678) (oGrid.dm 1678) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1678) oGrid.kl oGrid.kr 400 2000 ⟨false, 654456193564448886542421356032633398901752134968477780813356337588708912634⟩ ⟨false, 0⟩ ⟨false, 905624558136716268193143250053494063659959735689155089051972185654146320606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1678_2400 : bothLoop evalE (oGrid.idx 1678) (oGrid.dm 1678) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1678) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 905624558136716268193143250053494063659959735689155089051972185654146320606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1678 : oGrid.row evalE 1678 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1678_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1678_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1678_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1678_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1678_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1678_2000).1 (bothLoop_sound b_1678_2400).1))))))

theorem n_row_1678 : nGrid.row evalE 1678 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1678_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1678_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1678_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1678_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1678_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1678_2000).2 (bothLoop_sound b_1678_2400).2))))))

theorem b_1679_0 : bothSeg evalE (oGrid.idx 1679) (oGrid.dm 1679) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1679) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72847540652622535728589686134173480826264900025836371731417347613805669634⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1679_400 : bothSeg evalE (oGrid.idx 1679) (oGrid.dm 1679) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1679) oGrid.kl oGrid.kr 400 400 ⟨false, 72847540652622535728589686134173480826264900025836371731417347613805669634⟩ ⟨false, 0⟩ ⟨false, 163304376092728835872778761495937862950793729243467370566537730836155965702⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1679_800 : bothSeg evalE (oGrid.idx 1679) (oGrid.dm 1679) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1679) oGrid.kl oGrid.kr 400 800 ⟨false, 163304376092728835872778761495937862950793729243467370566537730836155965702⟩ ⟨false, 0⟩ ⟨false, 285593049428713628044223562131061005656882878206659395485831611054822468916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1679_1200 : bothSeg evalE (oGrid.idx 1679) (oGrid.dm 1679) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1679) oGrid.kl oGrid.kr 400 1200 ⟨false, 285593049428713628044223562131061005656882878206659395485831611054822468916⟩ ⟨false, 0⟩ ⟨false, 448620306184476512070117738549391704239034927289431057825443196937883019330⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1679_1600 : bothSeg evalE (oGrid.idx 1679) (oGrid.dm 1679) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1679) oGrid.kl oGrid.kr 400 1600 ⟨false, 448620306184476512070117738549391704239034927289431057825443196937883019330⟩ ⟨false, 0⟩ ⟨false, 656121187096719373576285338457783781545875085033395392728523393539575564214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1679_2000 : bothSeg evalE (oGrid.idx 1679) (oGrid.dm 1679) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1679) oGrid.kl oGrid.kr 400 2000 ⟨false, 656121187096719373576285338457783781545875085033395392728523393539575564214⟩ ⟨false, 0⟩ ⟨false, 907531810978786050536372176389594689472658842466549499166175814764710008472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1679_2400 : bothLoop evalE (oGrid.idx 1679) (oGrid.dm 1679) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1679) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 907531810978786050536372176389594689472658842466549499166175814764710008472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1679 : oGrid.row evalE 1679 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1679_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1679_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1679_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1679_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1679_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1679_2000).1 (bothLoop_sound b_1679_2400).1))))))

theorem n_row_1679 : nGrid.row evalE 1679 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1679_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1679_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1679_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1679_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1679_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1679_2000).2 (bothLoop_sound b_1679_2400).2))))))

theorem o_blk_1656 : allFrom (fun j => oGrid.row evalE j) 1656 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1656) o_row_1656 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1657) o_row_1657 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1658) o_row_1658 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1659) o_row_1659 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1660) o_row_1660 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1661) o_row_1661 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1662) o_row_1662 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1663) o_row_1663 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1664) o_row_1664 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1665) o_row_1665 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1666) o_row_1666 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1667) o_row_1667 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1668) o_row_1668 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1669) o_row_1669 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1670) o_row_1670 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1671) o_row_1671 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1672) o_row_1672 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1673) o_row_1673 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1674) o_row_1674 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1675) o_row_1675 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1676) o_row_1676 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1677) o_row_1677 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1678) o_row_1678 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1679) o_row_1679 (allFrom_zero (fun j => oGrid.row evalE j) 1680)))))))))))))))))))))))))

theorem n_blk_1656 : allFrom (fun j => nGrid.row evalE j) 1656 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1656) n_row_1656 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1657) n_row_1657 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1658) n_row_1658 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1659) n_row_1659 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1660) n_row_1660 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1661) n_row_1661 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1662) n_row_1662 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1663) n_row_1663 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1664) n_row_1664 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1665) n_row_1665 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1666) n_row_1666 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1667) n_row_1667 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1668) n_row_1668 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1669) n_row_1669 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1670) n_row_1670 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1671) n_row_1671 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1672) n_row_1672 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1673) n_row_1673 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1674) n_row_1674 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1675) n_row_1675 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1676) n_row_1676 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1677) n_row_1677 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1678) n_row_1678 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1679) n_row_1679 (allFrom_zero (fun j => nGrid.row evalE j) 1680)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
