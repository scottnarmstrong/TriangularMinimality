/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 63 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1512`–`1535`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1512_0 : bothSeg evalE (oGrid.idx 1512) (oGrid.dm 1512) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1512) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 66897836682492321222360939816775759566775302362602528725206739353887326984⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1512_400 : bothSeg evalE (oGrid.idx 1512) (oGrid.dm 1512) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1512) oGrid.kl oGrid.kr 400 400 ⟨false, 66897836682492321222360939816775759566775302362602528725206739353887326984⟩ ⟨false, 0⟩ ⟨false, 137573951717907366294088428402366407388861708376415340144332842288829787476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1512_800 : bothSeg evalE (oGrid.idx 1512) (oGrid.dm 1512) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1512) oGrid.kl oGrid.kr 400 800 ⟨false, 137573951717907366294088428402366407388861708376415340144332842288829787476⟩ ⟨false, 0⟩ ⟨false, 204103409038324225320623572466862991079958970494548684751511590565664066452⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1512_1200 : bothSeg evalE (oGrid.idx 1512) (oGrid.dm 1512) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1512) oGrid.kl oGrid.kr 400 1200 ⟨false, 204103409038324225320623572466862991079958970494548684751511590565664066452⟩ ⟨false, 0⟩ ⟨false, 316268133274550356039249998183362824151866312145006442447388846344323938688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1512_1600 : bothSeg evalE (oGrid.idx 1512) (oGrid.dm 1512) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1512) oGrid.kl oGrid.kr 400 1600 ⟨false, 316268133274550356039249998183362824151866312145006442447388846344323938688⟩ ⟨false, 0⟩ ⟨false, 478827313364636628390267511169560524043053372032580146201808367752252507788⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1512_2000 : bothSeg evalE (oGrid.idx 1512) (oGrid.dm 1512) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1512) oGrid.kl oGrid.kr 400 2000 ⟨false, 478827313364636628390267511169560524043053372032580146201808367752252507788⟩ ⟨false, 0⟩ ⟨false, 690123661349586573415000067390308748065472158753245335269365472293156393018⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1512_2400 : bothLoop evalE (oGrid.idx 1512) (oGrid.dm 1512) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1512) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 690123661349586573415000067390308748065472158753245335269365472293156393018⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1512 : oGrid.row evalE 1512 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1512_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1512_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1512_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1512_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1512_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1512_2000).1 (bothLoop_sound b_1512_2400).1))))))

theorem n_row_1512 : nGrid.row evalE 1512 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1512_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1512_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1512_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1512_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1512_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1512_2000).2 (bothLoop_sound b_1512_2400).2))))))

theorem b_1513_0 : bothSeg evalE (oGrid.idx 1513) (oGrid.dm 1513) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1513) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 67366654753886535479060896832000266350523421835343321132334814537075761548⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1513_400 : bothSeg evalE (oGrid.idx 1513) (oGrid.dm 1513) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1513) oGrid.kl oGrid.kr 400 400 ⟨false, 67366654753886535479060896832000266350523421835343321132334814537075761548⟩ ⟨false, 0⟩ ⟨false, 137909565820284640271897109336337452958782669164665386594010027449036659548⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1513_800 : bothSeg evalE (oGrid.idx 1513) (oGrid.dm 1513) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1513) oGrid.kl oGrid.kr 400 800 ⟨false, 137909565820284640271897109336337452958782669164665386594010027449036659548⟩ ⟨false, 0⟩ ⟨false, 204696543497833358438550155576591598184037462634080787031822260841510281198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1513_1200 : bothSeg evalE (oGrid.idx 1513) (oGrid.dm 1513) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1513) oGrid.kl oGrid.kr 400 1200 ⟨false, 204696543497833358438550155576591598184037462634080787031822260841510281198⟩ ⟨false, 0⟩ ⟨false, 317167664860363118271653314702300507580230722547987696695856622331080502244⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1513_1600 : bothSeg evalE (oGrid.idx 1513) (oGrid.dm 1513) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1513) oGrid.kl oGrid.kr 400 1600 ⟨false, 317167664860363118271653314702300507580230722547987696695856622331080502244⟩ ⟨false, 0⟩ ⟨false, 479995163644468708455999556446230003160478770792379529221935368378534863494⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1513_2000 : bothSeg evalE (oGrid.idx 1513) (oGrid.dm 1513) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1513) oGrid.kl oGrid.kr 400 2000 ⟨false, 479995163644468708455999556446230003160478770792379529221935368378534863494⟩ ⟨false, 0⟩ ⟨false, 691529420753660302010047273765285195348606298824353608587727031978597849676⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1513_2400 : bothLoop evalE (oGrid.idx 1513) (oGrid.dm 1513) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1513) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 691529420753660302010047273765285195348606298824353608587727031978597849676⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1513 : oGrid.row evalE 1513 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1513_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1513_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1513_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1513_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1513_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1513_2000).1 (bothLoop_sound b_1513_2400).1))))))

theorem n_row_1513 : nGrid.row evalE 1513 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1513_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1513_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1513_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1513_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1513_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1513_2000).2 (bothLoop_sound b_1513_2400).2))))))

theorem b_1514_0 : bothSeg evalE (oGrid.idx 1514) (oGrid.dm 1514) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1514) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 67829999949374041506960600426623083404007721996327142194680052849256290976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1514_400 : bothSeg evalE (oGrid.idx 1514) (oGrid.dm 1514) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1514) oGrid.kl oGrid.kr 400 400 ⟨false, 67829999949374041506960600426623083404007721996327142194680052849256290976⟩ ⟨false, 0⟩ ⟨false, 138232440760607679718749329340010711973380220884959901154224421951727022044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1514_800 : bothSeg evalE (oGrid.idx 1514) (oGrid.dm 1514) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1514) oGrid.kl oGrid.kr 400 800 ⟨false, 138232440760607679718749329340010711973380220884959901154224421951727022044⟩ ⟨false, 0⟩ ⟨false, 205280904172904716185503255000477554506659416419091446044877842346411090490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1514_1200 : bothSeg evalE (oGrid.idx 1514) (oGrid.dm 1514) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1514) oGrid.kl oGrid.kr 400 1200 ⟨false, 205280904172904716185503255000477554506659416419091446044877842346411090490⟩ ⟨false, 0⟩ ⟨false, 318058402032492164739377083743045320883526680295355323465359974226105359686⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1514_1600 : bothSeg evalE (oGrid.idx 1514) (oGrid.dm 1514) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1514) oGrid.kl oGrid.kr 400 1600 ⟨false, 318058402032492164739377083743045320883526680295355323465359974226105359686⟩ ⟨false, 0⟩ ⟨false, 481154231948099747045096696307493207157389904031610689717709640687274552802⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1514_2000 : bothSeg evalE (oGrid.idx 1514) (oGrid.dm 1514) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1514) oGrid.kl oGrid.kr 400 2000 ⟨false, 481154231948099747045096696307493207157389904031610689717709640687274552802⟩ ⟨false, 0⟩ ⟨false, 692926428926686655237166893486386043307976919837632674072568657334816757226⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1514_2400 : bothLoop evalE (oGrid.idx 1514) (oGrid.dm 1514) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1514) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 692926428926686655237166893486386043307976919837632674072568657334816757226⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1514 : oGrid.row evalE 1514 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1514_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1514_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1514_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1514_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1514_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1514_2000).1 (bothLoop_sound b_1514_2400).1))))))

theorem n_row_1514 : nGrid.row evalE 1514 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1514_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1514_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1514_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1514_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1514_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1514_2000).2 (bothLoop_sound b_1514_2400).2))))))

theorem b_1515_0 : bothSeg evalE (oGrid.idx 1515) (oGrid.dm 1515) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1515) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 68287507866858908086822590733891499505979962555971315512344045091384758500⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1515_400 : bothSeg evalE (oGrid.idx 1515) (oGrid.dm 1515) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1515) oGrid.kl oGrid.kr 400 400 ⟨false, 68287507866858908086822590733891499505979962555971315512344045091384758500⟩ ⟨false, 0⟩ ⟨false, 138542496607082242172260038728279981913971389586846904618113024880829886030⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1515_800 : bothSeg evalE (oGrid.idx 1515) (oGrid.dm 1515) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1515) oGrid.kl oGrid.kr 400 800 ⟨false, 138542496607082242172260038728279981913971389586846904618113024880829886030⟩ ⟨false, 0⟩ ⟨false, 205856306686188689549122816011664923543293895490120244048651785849470013420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1515_1200 : bothSeg evalE (oGrid.idx 1515) (oGrid.dm 1515) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1515) oGrid.kl oGrid.kr 400 1200 ⟨false, 205856306686188689549122816011664923543293895490120244048651785849470013420⟩ ⟨false, 0⟩ ⟨false, 318940160383769686404507810825508420726093850922946460030129989435937336070⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1515_1600 : bothSeg evalE (oGrid.idx 1515) (oGrid.dm 1515) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1515) oGrid.kl oGrid.kr 400 1600 ⟨false, 318940160383769686404507810825508420726093850922946460030129989435937336070⟩ ⟨false, 0⟩ ⟨false, 482304333811892961215548374990037968262584286314553556550130778631035884140⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1515_2000 : bothSeg evalE (oGrid.idx 1515) (oGrid.dm 1515) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1515) oGrid.kl oGrid.kr 400 2000 ⟨false, 482304333811892961215548374990037968262584286314553556550130778631035884140⟩ ⟨false, 0⟩ ⟨false, 694314501345910818031552438243757727464632733007076871053282569790318781798⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1515_2400 : bothLoop evalE (oGrid.idx 1515) (oGrid.dm 1515) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1515) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 694314501345910818031552438243757727464632733007076871053282569790318781798⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1515 : oGrid.row evalE 1515 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1515_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1515_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1515_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1515_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1515_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1515_2000).1 (bothLoop_sound b_1515_2400).1))))))

theorem n_row_1515 : nGrid.row evalE 1515 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1515_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1515_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1515_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1515_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1515_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1515_2000).2 (bothLoop_sound b_1515_2400).2))))))

theorem b_1516_0 : bothSeg evalE (oGrid.idx 1516) (oGrid.dm 1516) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1516) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 68738809907406237392893050276415700868588888994172568115184346417213566712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1516_400 : bothSeg evalE (oGrid.idx 1516) (oGrid.dm 1516) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1516) oGrid.kl oGrid.kr 400 400 ⟨false, 68738809907406237392893050276415700868588888994172568115184346417213566712⟩ ⟨false, 0⟩ ⟨false, 138839633241015035917351574017535213888086917687770742406457533404221914596⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1516_800 : bothSeg evalE (oGrid.idx 1516) (oGrid.dm 1516) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1516) oGrid.kl oGrid.kr 400 800 ⟨false, 138839633241015035917351574017535213888086917687770742406457533404221914596⟩ ⟨false, 0⟩ ⟨false, 206422545036961487040029435498289046746364122320448256337474215125048902802⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1516_1200 : bothSeg evalE (oGrid.idx 1516) (oGrid.dm 1516) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1516) oGrid.kl oGrid.kr 400 1200 ⟨false, 206422545036961487040029435498289046746364122320448256337474215125048902802⟩ ⟨false, 0⟩ ⟨false, 319812733883753178332099146524884504413035870335333809895005830706273380734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1516_1600 : bothSeg evalE (oGrid.idx 1516) (oGrid.dm 1516) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1516) oGrid.kl oGrid.kr 400 1600 ⟨false, 319812733883753178332099146524884504413035870335333809895005830706273380734⟩ ⟨false, 0⟩ ⟨false, 483445263149042394957338190084534006849658108022237522300987599282490019916⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1516_2000 : bothSeg evalE (oGrid.idx 1516) (oGrid.dm 1516) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1516) oGrid.kl oGrid.kr 400 2000 ⟨false, 483445263149042394957338190084534006849658108022237522300987599282490019916⟩ ⟨false, 0⟩ ⟨false, 695693431865486950062698741991064112282870151881467231357177860742185255850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1516_2400 : bothLoop evalE (oGrid.idx 1516) (oGrid.dm 1516) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1516) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 695693431865486950062698741991064112282870151881467231357177860742185255850⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1516 : oGrid.row evalE 1516 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1516_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1516_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1516_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1516_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1516_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1516_2000).1 (bothLoop_sound b_1516_2400).1))))))

theorem n_row_1516 : nGrid.row evalE 1516 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1516_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1516_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1516_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1516_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1516_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1516_2000).2 (bothLoop_sound b_1516_2400).2))))))

theorem b_1517_0 : bothSeg evalE (oGrid.idx 1517) (oGrid.dm 1517) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1517) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69183531794983159024309066117727713541161785127603697053670386741241460958⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1517_400 : bothSeg evalE (oGrid.idx 1517) (oGrid.dm 1517) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1517) oGrid.kl oGrid.kr 400 400 ⟨false, 69183531794983159024309066117727713541161785127603697053670386741241460958⟩ ⟨false, 0⟩ ⟨false, 139123767560560215820389829176103057654430555224192898652959434390828163718⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1517_800 : bothSeg evalE (oGrid.idx 1517) (oGrid.dm 1517) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1517) oGrid.kl oGrid.kr 400 800 ⟨false, 139123767560560215820389829176103057654430555224192898652959434390828163718⟩ ⟨false, 0⟩ ⟨false, 206979429043314571445314213394891634594564725368254572611934243338324924444⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1517_1200 : bothSeg evalE (oGrid.idx 1517) (oGrid.dm 1517) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1517) oGrid.kl oGrid.kr 400 1200 ⟨false, 206979429043314571445314213394891634594564725368254572611934243338324924444⟩ ⟨false, 0⟩ ⟨false, 320675932320914644516126335281349167570888585412658575916565861323457507710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1517_1600 : bothSeg evalE (oGrid.idx 1517) (oGrid.dm 1517) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1517) oGrid.kl oGrid.kr 400 1600 ⟨false, 320675932320914644516126335281349167570888585412658575916565861323457507710⟩ ⟨false, 0⟩ ⟨false, 484576829691761955216278076416218368438352343270242964859697382855424583072⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1517_2000 : bothSeg evalE (oGrid.idx 1517) (oGrid.dm 1517) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1517) oGrid.kl oGrid.kr 400 2000 ⟨false, 484576829691761955216278076416218368438352343270242964859697382855424583072⟩ ⟨false, 0⟩ ⟨false, 697063030158667142510129412477122725887872257176443534808473224115900592128⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1517_2400 : bothLoop evalE (oGrid.idx 1517) (oGrid.dm 1517) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1517) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 697063030158667142510129412477122725887872257176443534808473224115900592128⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1517 : oGrid.row evalE 1517 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1517_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1517_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1517_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1517_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1517_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1517_2000).1 (bothLoop_sound b_1517_2400).1))))))

theorem n_row_1517 : nGrid.row evalE 1517 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1517_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1517_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1517_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1517_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1517_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1517_2000).2 (bothLoop_sound b_1517_2400).2))))))

theorem b_1518_0 : bothSeg evalE (oGrid.idx 1518) (oGrid.dm 1518) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1518) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 69621306101661239861692917891319103698046443277929947055361527145485233752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1518_400 : bothSeg evalE (oGrid.idx 1518) (oGrid.dm 1518) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1518) oGrid.kl oGrid.kr 400 400 ⟨false, 69621306101661239861692917891319103698046443277929947055361527145485233752⟩ ⟨false, 0⟩ ⟨false, 139394803504329765908293464444378146637679294603984947395460764451364371132⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1518_800 : bothSeg evalE (oGrid.idx 1518) (oGrid.dm 1518) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1518) oGrid.kl oGrid.kr 400 800 ⟨false, 139394803504329765908293464444378146637679294603984947395460764451364371132⟩ ⟨false, 0⟩ ⟨false, 207526756922108514181618493559860323511949806991500644176756735223611112896⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1518_1200 : bothSeg evalE (oGrid.idx 1518) (oGrid.dm 1518) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1518) oGrid.kl oGrid.kr 400 1200 ⟨false, 207526756922108514181618493559860323511949806991500644176756735223611112896⟩ ⟨false, 0⟩ ⟨false, 321529553882594220806628637516767219753806370289626674240482918552734415508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1518_1600 : bothSeg evalE (oGrid.idx 1518) (oGrid.dm 1518) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1518) oGrid.kl oGrid.kr 400 1600 ⟨false, 321529553882594220806628637516767219753806370289626674240482918552734415508⟩ ⟨false, 0⟩ ⟨false, 485698831571238866244214624478406519037087352443573550185644055636960928504⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1518_2000 : bothSeg evalE (oGrid.idx 1518) (oGrid.dm 1518) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1518) oGrid.kl oGrid.kr 400 2000 ⟨false, 485698831571238866244214624478406519037087352443573550185644055636960928504⟩ ⟨false, 0⟩ ⟨false, 698423094297754793183144764253814077824711885115691065749112242662794065276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1518_2400 : bothLoop evalE (oGrid.idx 1518) (oGrid.dm 1518) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1518) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 698423094297754793183144764253814077824711885115691065749112242662794065276⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1518 : oGrid.row evalE 1518 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1518_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1518_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1518_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1518_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1518_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1518_2000).1 (bothLoop_sound b_1518_2400).1))))))

theorem n_row_1518 : nGrid.row evalE 1518 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1518_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1518_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1518_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1518_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1518_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1518_2000).2 (bothLoop_sound b_1518_2400).2))))))

theorem b_1519_0 : bothSeg evalE (oGrid.idx 1519) (oGrid.dm 1519) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1519) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70051757872698078894328342683747015560541750128879931321362327990422223208⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1519_400 : bothSeg evalE (oGrid.idx 1519) (oGrid.dm 1519) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1519) oGrid.kl oGrid.kr 400 400 ⟨false, 70051757872698078894328342683747015560541750128879931321362327990422223208⟩ ⟨false, 0⟩ ⟨false, 139652674678201962463684645478168426543515792092114835564218225835939249974⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1519_800 : bothSeg evalE (oGrid.idx 1519) (oGrid.dm 1519) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1519) oGrid.kl oGrid.kr 400 800 ⟨false, 139652674678201962463684645478168426543515792092114835564218225835939249974⟩ ⟨false, 0⟩ ⟨false, 208064352276965374659628622306246949822203171327757144508113945821203553938⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1519_1200 : bothSeg evalE (oGrid.idx 1519) (oGrid.dm 1519) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1519) oGrid.kl oGrid.kr 400 1200 ⟨false, 208064352276965374659628622306246949822203171327757144508113945821203553938⟩ ⟨false, 0⟩ ⟨false, 322373422142992323348845041032088729424347992055203454567711249405831335536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1519_1600 : bothSeg evalE (oGrid.idx 1519) (oGrid.dm 1519) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1519) oGrid.kl oGrid.kr 400 1600 ⟨false, 322373422142992323348845041032088729424347992055203454567711249405831335536⟩ ⟨false, 0⟩ ⟨false, 486811092305625649686276317057792018061323397900330840793428110137702736708⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1519_2000 : bothSeg evalE (oGrid.idx 1519) (oGrid.dm 1519) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1519) oGrid.kl oGrid.kr 400 2000 ⟨false, 486811092305625649686276317057792018061323397900330840793428110137702736708⟩ ⟨false, 0⟩ ⟨false, 699773447742096507395491372387802380285765980199268390942056355200466419396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1519_2400 : bothLoop evalE (oGrid.idx 1519) (oGrid.dm 1519) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1519) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 699773447742096507395491372387802380285765980199268390942056355200466419396⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1519 : oGrid.row evalE 1519 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1519_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1519_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1519_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1519_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1519_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1519_2000).1 (bothLoop_sound b_1519_2400).1))))))

theorem n_row_1519 : nGrid.row evalE 1519 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1519_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1519_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1519_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1519_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1519_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1519_2000).2 (bothLoop_sound b_1519_2400).2))))))

theorem b_1520_0 : bothSeg evalE (oGrid.idx 1520) (oGrid.dm 1520) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1520) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70474501474046256281460823058315492730232516660490767371169316210212296950⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1520_400 : bothSeg evalE (oGrid.idx 1520) (oGrid.dm 1520) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1520) oGrid.kl oGrid.kr 400 400 ⟨false, 70474501474046256281460823058315492730232516660490767371169316210212296950⟩ ⟨false, 0⟩ ⟨false, 139897286319223554453237488195488904283128422351746147816674500123596742602⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1520_800 : bothSeg evalE (oGrid.idx 1520) (oGrid.dm 1520) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1520) oGrid.kl oGrid.kr 400 800 ⟨false, 139897286319223554453237488195488904283128422351746147816674500123596742602⟩ ⟨false, 0⟩ ⟨false, 208592013129656856913669095611829119782026552855235202231479894780748240474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1520_1200 : bothSeg evalE (oGrid.idx 1520) (oGrid.dm 1520) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1520) oGrid.kl oGrid.kr 400 1200 ⟨false, 208592013129656856913669095611829119782026552855235202231479894780748240474⟩ ⟨false, 0⟩ ⟨false, 323207335094557574787008585860107879488916758753825124121366775694718093372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1520_1600 : bothSeg evalE (oGrid.idx 1520) (oGrid.dm 1520) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1520) oGrid.kl oGrid.kr 400 1600 ⟨false, 323207335094557574787008585860107879488916758753825124121366775694718093372⟩ ⟨false, 0⟩ ⟨false, 487913409831427882657689808211009926100059504584601268867140387037809907922⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1520_2000 : bothSeg evalE (oGrid.idx 1520) (oGrid.dm 1520) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1520) oGrid.kl oGrid.kr 400 2000 ⟨false, 487913409831427882657689808211009926100059504584601268867140387037809907922⟩ ⟨false, 0⟩ ⟨false, 701113888369469776847712771157082582671303267725656990290401432099477707890⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1520_2400 : bothLoop evalE (oGrid.idx 1520) (oGrid.dm 1520) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1520) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 701113888369469776847712771157082582671303267725656990290401432099477707890⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1520 : oGrid.row evalE 1520 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1520_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1520_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1520_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1520_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1520_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1520_2000).1 (bothLoop_sound b_1520_2400).1))))))

theorem n_row_1520 : nGrid.row evalE 1520 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1520_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1520_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1520_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1520_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1520_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1520_2000).2 (bothLoop_sound b_1520_2400).2))))))

theorem b_1521_0 : bothSeg evalE (oGrid.idx 1521) (oGrid.dm 1521) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1521) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 70889169720724587243957367306566734627201619237102125443432368708863942646⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1521_400 : bothSeg evalE (oGrid.idx 1521) (oGrid.dm 1521) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1521) oGrid.kl oGrid.kr 400 400 ⟨false, 70889169720724587243957367306566734627201619237102125443432368708863942646⟩ ⟨false, 0⟩ ⟨false, 140128576084637055270058269680576964892783923210790505340226010392282210202⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1521_800 : bothSeg evalE (oGrid.idx 1521) (oGrid.dm 1521) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1521) oGrid.kl oGrid.kr 400 800 ⟨false, 140128576084637055270058269680576964892783923210790505340226010392282210202⟩ ⟨false, 0⟩ ⟨false, 209109570944102911242619521033424437369239891260388221441353628216957332894⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1521_1200 : bothSeg evalE (oGrid.idx 1521) (oGrid.dm 1521) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1521) oGrid.kl oGrid.kr 400 1200 ⟨false, 209109570944102911242619521033424437369239891260388221441353628216957332894⟩ ⟨false, 0⟩ ⟨false, 324031124171985175978008445762916469049450635292640893032425270785974602044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1521_1600 : bothSeg evalE (oGrid.idx 1521) (oGrid.dm 1521) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1521) oGrid.kl oGrid.kr 400 1600 ⟨false, 324031124171985175978008445762916469049450635292640893032425270785974602044⟩ ⟨false, 0⟩ ⟨false, 489005615527502401555236524263309421571492197194063039699745499632143086344⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1521_2000 : bothSeg evalE (oGrid.idx 1521) (oGrid.dm 1521) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1521) oGrid.kl oGrid.kr 400 2000 ⟨false, 489005615527502401555236524263309421571492197194063039699745499632143086344⟩ ⟨false, 0⟩ ⟨false, 702444247500081104262483024626001329129918651656401382969763184019811952532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1521_2400 : bothLoop evalE (oGrid.idx 1521) (oGrid.dm 1521) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1521) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 702444247500081104262483024626001329129918651656401382969763184019811952532⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1521 : oGrid.row evalE 1521 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1521_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1521_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1521_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1521_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1521_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1521_2000).1 (bothLoop_sound b_1521_2400).1))))))

theorem n_row_1521 : nGrid.row evalE 1521 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1521_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1521_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1521_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1521_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1521_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1521_2000).2 (bothLoop_sound b_1521_2400).2))))))

theorem b_1522_0 : bothSeg evalE (oGrid.idx 1522) (oGrid.dm 1522) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1522) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 71295378077970970185728124480182299853638886482731929543931165744882525846⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1522_400 : bothSeg evalE (oGrid.idx 1522) (oGrid.dm 1522) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1522) oGrid.kl oGrid.kr 400 400 ⟨false, 71295378077970970185728124480182299853638886482731929543931165744882525846⟩ ⟨false, 0⟩ ⟨false, 140346470361171718975451918894646785254924652169942816890847180395986876400⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1522_800 : bothSeg evalE (oGrid.idx 1522) (oGrid.dm 1522) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1522) oGrid.kl oGrid.kr 400 800 ⟨false, 140346470361171718975451918894646785254924652169942816890847180395986876400⟩ ⟨false, 0⟩ ⟨false, 209616840948678010065145679608627310173919890166310315670041656422345440384⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1522_1200 : bothSeg evalE (oGrid.idx 1522) (oGrid.dm 1522) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1522) oGrid.kl oGrid.kr 400 1200 ⟨false, 209616840948678010065145679608627310173919890166310315670041656422345440384⟩ ⟨false, 0⟩ ⟨false, 324844604574522952416895531460659072937037688914301451112008840259830146190⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1522_1600 : bothSeg evalE (oGrid.idx 1522) (oGrid.dm 1522) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1522) oGrid.kl oGrid.kr 400 1600 ⟨false, 324844604574522952416895531460659072937037688914301451112008840259830146190⟩ ⟨false, 0⟩ ⟨false, 490087524537363180805186829054934332185371788090053734838939508529821547256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1522_2000 : bothSeg evalE (oGrid.idx 1522) (oGrid.dm 1522) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1522) oGrid.kl oGrid.kr 400 2000 ⟨false, 490087524537363180805186829054934332185371788090053734838939508529821547256⟩ ⟨false, 0⟩ ⟨false, 703764340218871802974989908212263395191450454528139710876061695442931580834⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1522_2400 : bothLoop evalE (oGrid.idx 1522) (oGrid.dm 1522) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1522) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 703764340218871802974989908212263395191450454528139710876061695442931580834⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1522 : oGrid.row evalE 1522 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1522_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1522_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1522_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1522_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1522_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1522_2000).1 (bothLoop_sound b_1522_2400).1))))))

theorem n_row_1522 : nGrid.row evalE 1522 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1522_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1522_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1522_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1522_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1522_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1522_2000).2 (bothLoop_sound b_1522_2400).2))))))

theorem b_1523_0 : bothSeg evalE (oGrid.idx 1523) (oGrid.dm 1523) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1523) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 71692754336758299502016358817461451789446695510550223187915674705569954966⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1523_400 : bothSeg evalE (oGrid.idx 1523) (oGrid.dm 1523) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1523) oGrid.kl oGrid.kr 400 400 ⟨false, 71692754336758299502016358817461451789446695510550223187915674705569954966⟩ ⟨false, 0⟩ ⟨false, 140550930611321897028795615670833164432513288048860578702448468489201636786⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1523_800 : bothSeg evalE (oGrid.idx 1523) (oGrid.dm 1523) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1523) oGrid.kl oGrid.kr 400 800 ⟨false, 140550930611321897028795615670833164432513288048860578702448468489201636786⟩ ⟨false, 0⟩ ⟨false, 210113680123999311270456021528352083683588610822459361017053660454066179460⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1523_1200 : bothSeg evalE (oGrid.idx 1523) (oGrid.dm 1523) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1523) oGrid.kl oGrid.kr 400 1200 ⟨false, 210113680123999311270456021528352083683588610822459361017053660454066179460⟩ ⟨false, 0⟩ ⟨false, 325647633253759288654430190431785295814146344139644190592317030379125131524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1523_1600 : bothSeg evalE (oGrid.idx 1523) (oGrid.dm 1523) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1523) oGrid.kl oGrid.kr 400 1600 ⟨false, 325647633253759288654430190431785295814146344139644190592317030379125131524⟩ ⟨false, 0⟩ ⟨false, 491158993756969099827771150216356585983958086498687919518273916068690768640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1523_2000 : bothSeg evalE (oGrid.idx 1523) (oGrid.dm 1523) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1523) oGrid.kl oGrid.kr 400 2000 ⟨false, 491158993756969099827771150216356585983958086498687919518273916068690768640⟩ ⟨false, 0⟩ ⟨false, 705074023363305684758655647139389694986112855963539484606505068065839110408⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1523_2400 : bothLoop evalE (oGrid.idx 1523) (oGrid.dm 1523) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1523) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 705074023363305684758655647139389694986112855963539484606505068065839110408⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1523 : oGrid.row evalE 1523 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1523_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1523_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1523_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1523_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1523_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1523_2000).1 (bothLoop_sound b_1523_2400).1))))))

theorem n_row_1523 : nGrid.row evalE 1523 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1523_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1523_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1523_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1523_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1523_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1523_2000).2 (bothLoop_sound b_1523_2400).2))))))

theorem b_1524_0 : bothSeg evalE (oGrid.idx 1524) (oGrid.dm 1524) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1524) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72080918611184533074287269402252099550908014381047533482113416176873633416⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1524_400 : bothSeg evalE (oGrid.idx 1524) (oGrid.dm 1524) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1524) oGrid.kl oGrid.kr 400 400 ⟨false, 72080918611184533074287269402252099550908014381047533482113416176873633416⟩ ⟨false, 0⟩ ⟨false, 140741886803806357321574627116830276816279590618929024135229566273832137770⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1524_800 : bothSeg evalE (oGrid.idx 1524) (oGrid.dm 1524) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1524) oGrid.kl oGrid.kr 400 800 ⟨false, 140741886803806357321574627116830276816279590618929024135229566273832137770⟩ ⟨false, 0⟩ ⟨false, 210599909801385076156176962236545582776712411527996084025718781746941399468⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1524_1200 : bothSeg evalE (oGrid.idx 1524) (oGrid.dm 1524) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1524) oGrid.kl oGrid.kr 400 1200 ⟨false, 210599909801385076156176962236545582776712411527996084025718781746941399468⟩ ⟨false, 0⟩ ⟨false, 326440031512081317797254370856344082474720534530409878714590722191155161360⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1524_1600 : bothSeg evalE (oGrid.idx 1524) (oGrid.dm 1524) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1524) oGrid.kl oGrid.kr 400 1600 ⟨false, 326440031512081317797254370856344082474720534530409878714590722191155161360⟩ ⟨false, 0⟩ ⟨false, 492219844433181965308630604915060519001096346133591550862228397652489640068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1524_2000 : bothSeg evalE (oGrid.idx 1524) (oGrid.dm 1524) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1524) oGrid.kl oGrid.kr 400 2000 ⟨false, 492219844433181965308630604915060519001096346133591550862228397652489640068⟩ ⟨false, 0⟩ ⟨false, 706373118121827002976865354108799818527317417799406145711538470033686201914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1524_2400 : bothLoop evalE (oGrid.idx 1524) (oGrid.dm 1524) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1524) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 706373118121827002976865354108799818527317417799406145711538470033686201914⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1524 : oGrid.row evalE 1524 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1524_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1524_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1524_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1524_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1524_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1524_2000).1 (bothLoop_sound b_1524_2400).1))))))

theorem n_row_1524 : nGrid.row evalE 1524 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1524_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1524_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1524_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1524_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1524_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1524_2000).2 (bothLoop_sound b_1524_2400).2))))))

theorem b_1525_0 : bothSeg evalE (oGrid.idx 1525) (oGrid.dm 1525) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1525) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72459504513618024672028049150607179631417879219862136065556340865185207326⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1525_400 : bothSeg evalE (oGrid.idx 1525) (oGrid.dm 1525) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1525) oGrid.kl oGrid.kr 400 400 ⟨false, 72459504513618024672028049150607179631417879219862136065556340865185207326⟩ ⟨false, 0⟩ ⟨false, 140919308693166709691655750397020509033881393950839436181554892101845535250⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1525_800 : bothSeg evalE (oGrid.idx 1525) (oGrid.dm 1525) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1525) oGrid.kl oGrid.kr 400 800 ⟨false, 140919308693166709691655750397020509033881393950839436181554892101845535250⟩ ⟨false, 0⟩ ⟨false, 211075394993234004216805724439197666698572821172579742245180272488911804258⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1525_1200 : bothSeg evalE (oGrid.idx 1525) (oGrid.dm 1525) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1525) oGrid.kl oGrid.kr 400 1200 ⟨false, 211075394993234004216805724439197666698572821172579742245180272488911804258⟩ ⟨false, 0⟩ ⟨false, 327221664333054028353137754553809813541355017887479701817878165757518523558⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1525_1600 : bothSeg evalE (oGrid.idx 1525) (oGrid.dm 1525) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1525) oGrid.kl oGrid.kr 400 1600 ⟨false, 327221664333054028353137754553809813541355017887479701817878165757518523558⟩ ⟨false, 0⟩ ⟨false, 493269941494145451039556153838785640801262002488097734079998108529658663626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1525_2000 : bothSeg evalE (oGrid.idx 1525) (oGrid.dm 1525) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1525) oGrid.kl oGrid.kr 400 2000 ⟨false, 493269941494145451039556153838785640801262002488097734079998108529658663626⟩ ⟨false, 0⟩ ⟨false, 707661489364239313323238856177248536771646759736294831163905435456642558628⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1525_2400 : bothLoop evalE (oGrid.idx 1525) (oGrid.dm 1525) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1525) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 707661489364239313323238856177248536771646759736294831163905435456642558628⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1525 : oGrid.row evalE 1525 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1525_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1525_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1525_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1525_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1525_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1525_2000).1 (bothLoop_sound b_1525_2400).1))))))

theorem n_row_1525 : nGrid.row evalE 1525 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1525_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1525_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1525_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1525_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1525_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1525_2000).2 (bothLoop_sound b_1525_2400).2))))))

theorem b_1526_0 : bothSeg evalE (oGrid.idx 1526) (oGrid.dm 1526) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1526) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 72828142612516934978864773051394647578890606444338096092590800673747649312⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1526_400 : bothSeg evalE (oGrid.idx 1526) (oGrid.dm 1526) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1526) oGrid.kl oGrid.kr 400 400 ⟨false, 72828142612516934978864773051394647578890606444338096092590800673747649312⟩ ⟨false, 0⟩ ⟨false, 141083156106345336752523517934168242992993724181104333159857147363020330164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1526_800 : bothSeg evalE (oGrid.idx 1526) (oGrid.dm 1526) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1526) oGrid.kl oGrid.kr 400 800 ⟨false, 141083156106345336752523517934168242992993724181104333159857147363020330164⟩ ⟨false, 0⟩ ⟨false, 211539989642293475172814689507862339695014352699082839442319763246830335446⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1526_1200 : bothSeg evalE (oGrid.idx 1526) (oGrid.dm 1526) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1526) oGrid.kl oGrid.kr 400 1200 ⟨false, 211539989642293475172814689507862339695014352699082839442319763246830335446⟩ ⟨false, 0⟩ ⟨false, 327992385630688278810364338810893001503927714229619431950163317647953149352⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1526_1600 : bothSeg evalE (oGrid.idx 1526) (oGrid.dm 1526) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1526) oGrid.kl oGrid.kr 400 1600 ⟨false, 327992385630688278810364338810893001503927714229619431950163317647953149352⟩ ⟨false, 0⟩ ⟨false, 494309138798552945717441644362291042304301165715021549917807842445818247256⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1526_2000 : bothSeg evalE (oGrid.idx 1526) (oGrid.dm 1526) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1526) oGrid.kl oGrid.kr 400 2000 ⟨false, 494309138798552945717441644362291042304301165715021549917807842445818247256⟩ ⟨false, 0⟩ ⟨false, 708938990890973242539596992882487256970371187350775014110087800148904096008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1526_2400 : bothLoop evalE (oGrid.idx 1526) (oGrid.dm 1526) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1526) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 708938990890973242539596992882487256970371187350775014110087800148904096008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1526 : oGrid.row evalE 1526 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1526_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1526_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1526_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1526_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1526_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1526_2000).1 (bothLoop_sound b_1526_2400).1))))))

theorem n_row_1526 : nGrid.row evalE 1526 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1526_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1526_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1526_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1526_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1526_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1526_2000).2 (bothLoop_sound b_1526_2400).2))))))

theorem b_1527_0 : bothSeg evalE (oGrid.idx 1527) (oGrid.dm 1527) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1527) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73186470113259137539889002132512416148694462598740362087009425450617094512⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1527_400 : bothSeg evalE (oGrid.idx 1527) (oGrid.dm 1527) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1527) oGrid.kl oGrid.kr 400 400 ⟨false, 73186470113259137539889002132512416148694462598740362087009425450617094512⟩ ⟨false, 0⟩ ⟨false, 141233397732628163084995694725318808483573432414269293711721616279537618058⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1527_800 : bothSeg evalE (oGrid.idx 1527) (oGrid.dm 1527) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1527) oGrid.kl oGrid.kr 400 800 ⟨false, 141233397732628163084995694725318808483573432414269293711721616279537618058⟩ ⟨false, 0⟩ ⟨false, 211993559648679960618311141751544531079175008160385778580395264029318722840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1527_1200 : bothSeg evalE (oGrid.idx 1527) (oGrid.dm 1527) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1527) oGrid.kl oGrid.kr 400 1200 ⟨false, 211993559648679960618311141751544531079175008160385778580395264029318722840⟩ ⟨false, 0⟩ ⟨false, 328752061276460982328157622601977896738763069100854911713836283808451903136⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1527_1600 : bothSeg evalE (oGrid.idx 1527) (oGrid.dm 1527) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1527) oGrid.kl oGrid.kr 400 1600 ⟨false, 328752061276460982328157622601977896738763069100854911713836283808451903136⟩ ⟨false, 0⟩ ⟨false, 495337302162667571078207140669930374123561266093478114666237990986319571668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1527_2000 : bothSeg evalE (oGrid.idx 1527) (oGrid.dm 1527) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1527) oGrid.kl oGrid.kr 400 2000 ⟨false, 495337302162667571078207140669930374123561266093478114666237990986319571668⟩ ⟨false, 0⟩ ⟨false, 710205488460106427488603566901317668344997221139348663456703308162819084490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1527_2400 : bothLoop evalE (oGrid.idx 1527) (oGrid.dm 1527) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1527) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 710205488460106427488603566901317668344997221139348663456703308162819084490⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1527 : oGrid.row evalE 1527 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1527_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1527_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1527_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1527_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1527_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1527_2000).1 (bothLoop_sound b_1527_2400).1))))))

theorem n_row_1527 : nGrid.row evalE 1527 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1527_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1527_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1527_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1527_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1527_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1527_2000).2 (bothLoop_sound b_1527_2400).2))))))

theorem b_1528_0 : bothSeg evalE (oGrid.idx 1528) (oGrid.dm 1528) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1528) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73534123400753480425653330338625416494512845235543699621273325260376827472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1528_400 : bothSeg evalE (oGrid.idx 1528) (oGrid.dm 1528) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1528) oGrid.kl oGrid.kr 400 400 ⟨false, 73534123400753480425653330338625416494512845235543699621273325260376827472⟩ ⟨false, 0⟩ ⟨false, 141370003306786997193852862196252808070345964042755051271032774657711850026⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1528_800 : bothSeg evalE (oGrid.idx 1528) (oGrid.dm 1528) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1528) oGrid.kl oGrid.kr 400 800 ⟨false, 141370003306786997193852862196252808070345964042755051271032774657711850026⟩ ⟨false, 0⟩ ⟨false, 212435971227137341950782671095523738487510108676979974101047175067070205088⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1528_1200 : bothSeg evalE (oGrid.idx 1528) (oGrid.dm 1528) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1528) oGrid.kl oGrid.kr 400 1200 ⟨false, 212435971227137341950782671095523738487510108676979974101047175067070205088⟩ ⟨false, 0⟩ ⟨false, 329500557456573198200670688956804517597979434258316657555249516281861536710⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1528_1600 : bothSeg evalE (oGrid.idx 1528) (oGrid.dm 1528) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1528) oGrid.kl oGrid.kr 400 1600 ⟨false, 329500557456573198200670688956804517597979434258316657555249516281861536710⟩ ⟨false, 0⟩ ⟨false, 496354297717580107028076440140147600168454207642702891385946478559871686926⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1528_2000 : bothSeg evalE (oGrid.idx 1528) (oGrid.dm 1528) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1528) oGrid.kl oGrid.kr 400 2000 ⟨false, 496354297717580107028076440140147600168454207642702891385946478559871686926⟩ ⟨false, 0⟩ ⟨false, 711460848144621361243690695010625756307496854498560851816488711678352179230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1528_2400 : bothLoop evalE (oGrid.idx 1528) (oGrid.dm 1528) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1528) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 711460848144621361243690695010625756307496854498560851816488711678352179230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1528 : oGrid.row evalE 1528 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1528_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1528_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1528_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1528_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1528_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1528_2000).1 (bothLoop_sound b_1528_2400).1))))))

theorem n_row_1528 : nGrid.row evalE 1528 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1528_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1528_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1528_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1528_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1528_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1528_2000).2 (bothLoop_sound b_1528_2400).2))))))

theorem b_1529_0 : bothSeg evalE (oGrid.idx 1529) (oGrid.dm 1529) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1529) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 73870747245689848330171311201369316604535016292565052288290512454603768988⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1529_400 : bothSeg evalE (oGrid.idx 1529) (oGrid.dm 1529) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1529) oGrid.kl oGrid.kr 400 400 ⟨false, 73870747245689848330171311201369316604535016292565052288290512454603768988⟩ ⟨false, 0⟩ ⟨false, 141492953919575705580522758654990458059843978708375354716627201328707844906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1529_800 : bothSeg evalE (oGrid.idx 1529) (oGrid.dm 1529) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1529) oGrid.kl oGrid.kr 400 800 ⟨false, 141492953919575705580522758654990458059843978708375354716627201328707844906⟩ ⟨false, 0⟩ ⟨false, 212867105131887761092604994252854953287881102636963144542291361034619053920⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1529_1200 : bothSeg evalE (oGrid.idx 1529) (oGrid.dm 1529) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1529) oGrid.kl oGrid.kr 400 1200 ⟨false, 212867105131887761092604994252854953287881102636963144542291361034619053920⟩ ⟨false, 0⟩ ⟨false, 330237754896800756603215722524273757878281593532707917041496806127133306094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1529_1600 : bothSeg evalE (oGrid.idx 1529) (oGrid.dm 1529) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1529) oGrid.kl oGrid.kr 400 1600 ⟨false, 330237754896800756603215722524273757878281593532707917041496806127133306094⟩ ⟨false, 0⟩ ⟨false, 497360006134059450280740291921936655858542479957423403858799311445706816400⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1529_2000 : bothSeg evalE (oGrid.idx 1529) (oGrid.dm 1529) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1529) oGrid.kl oGrid.kr 400 2000 ⟨false, 497360006134059450280740291921936655858542479957423403858799311445706816400⟩ ⟨false, 0⟩ ⟨false, 712704950557255772705021991230489943344458838851185836713804414946524982458⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1529_2400 : bothLoop evalE (oGrid.idx 1529) (oGrid.dm 1529) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1529) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 712704950557255772705021991230489943344458838851185836713804414946524982458⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1529 : oGrid.row evalE 1529 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1529_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1529_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1529_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1529_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1529_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1529_2000).1 (bothLoop_sound b_1529_2400).1))))))

theorem n_row_1529 : nGrid.row evalE 1529 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1529_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1529_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1529_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1529_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1529_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1529_2000).2 (bothLoop_sound b_1529_2400).2))))))

theorem b_1530_0 : bothSeg evalE (oGrid.idx 1530) (oGrid.dm 1530) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1530) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 74195998612643445986446069256402305034012884626874708754412667627655314614⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1530_400 : bothSeg evalE (oGrid.idx 1530) (oGrid.dm 1530) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1530) oGrid.kl oGrid.kr 400 400 ⟨false, 74195998612643445986446069256402305034012884626874708754412667627655314614⟩ ⟨false, 0⟩ ⟨false, 141602266236055794603267701536527155809429492638885556058179537009100160548⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1530_800 : bothSeg evalE (oGrid.idx 1530) (oGrid.dm 1530) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1530) oGrid.kl oGrid.kr 400 800 ⟨false, 141602266236055794603267701536527155809429492638885556058179537009100160548⟩ ⟨false, 0⟩ ⟨false, 213286878207411573522237571993060173475218588739348671845144959928792247566⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1530_1200 : bothSeg evalE (oGrid.idx 1530) (oGrid.dm 1530) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1530) oGrid.kl oGrid.kr 400 1200 ⟨false, 213286878207411573522237571993060173475218588739348671845144959928792247566⟩ ⟨false, 0⟩ ⟨false, 330963570413273986137657870198148146783305836613998592090964205058203261376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1530_1600 : bothSeg evalE (oGrid.idx 1530) (oGrid.dm 1530) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1530) oGrid.kl oGrid.kr 400 1600 ⟨false, 330963570413273986137657870198148146783305836613998592090964205058203261376⟩ ⟨false, 0⟩ ⟨false, 498354344173332176017186575811765162167955822606434627077372087441063890202⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1530_2000 : bothSeg evalE (oGrid.idx 1530) (oGrid.dm 1530) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1530) oGrid.kl oGrid.kr 400 2000 ⟨false, 498354344173332176017186575811765162167955822606434627077372087441063890202⟩ ⟨false, 0⟩ ⟨false, 713937712401282109258496826218902945148931561978895754159411612640748817524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1530_2400 : bothLoop evalE (oGrid.idx 1530) (oGrid.dm 1530) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1530) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 713937712401282109258496826218902945148931561978895754159411612640748817524⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1530 : oGrid.row evalE 1530 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1530_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1530_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1530_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1530_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1530_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1530_2000).1 (bothLoop_sound b_1530_2400).1))))))

theorem n_row_1530 : nGrid.row evalE 1530 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1530_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1530_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1530_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1530_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1530_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1530_2000).2 (bothLoop_sound b_1530_2400).2))))))

theorem b_1531_0 : bothSeg evalE (oGrid.idx 1531) (oGrid.dm 1531) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1531) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 74509536931183934687381492126234583599740963533083867996516190796764028218⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1531_400 : bothSeg evalE (oGrid.idx 1531) (oGrid.dm 1531) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1531) oGrid.kl oGrid.kr 400 400 ⟨false, 74509536931183934687381492126234583599740963533083867996516190796764028218⟩ ⟨false, 0⟩ ⟨false, 141697936344500526544636760917164124518459145163570397669922548302258833206⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1531_800 : bothSeg evalE (oGrid.idx 1531) (oGrid.dm 1531) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1531) oGrid.kl oGrid.kr 400 800 ⟨false, 141697936344500526544636760917164124518459145163570397669922548302258833206⟩ ⟨false, 0⟩ ⟨false, 213695189054472079579792556477566375486421192367885409495214881781655546588⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1531_1200 : bothSeg evalE (oGrid.idx 1531) (oGrid.dm 1531) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1531) oGrid.kl oGrid.kr 400 1200 ⟨false, 213695189054472079579792556477566375486421192367885409495214881781655546588⟩ ⟨false, 0⟩ ⟨false, 331677902578502220140660258875885202569294603416895108837447069286333690474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1531_1600 : bothSeg evalE (oGrid.idx 1531) (oGrid.dm 1531) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1531) oGrid.kl oGrid.kr 400 1600 ⟨false, 331677902578502220140660258875885202569294603416895108837447069286333690474⟩ ⟨false, 0⟩ ⟨false, 499337210353106878531739983122496311011653131146520601632278812682364805042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1531_2000 : bothSeg evalE (oGrid.idx 1531) (oGrid.dm 1531) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1531) oGrid.kl oGrid.kr 400 2000 ⟨false, 499337210353106878531739983122496311011653131146520601632278812682364805042⟩ ⟨false, 0⟩ ⟨false, 715159032136531798441559263105528365842370819361826538203660574446897794114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1531_2400 : bothLoop evalE (oGrid.idx 1531) (oGrid.dm 1531) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1531) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 715159032136531798441559263105528365842370819361826538203660574446897794114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1531 : oGrid.row evalE 1531 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1531_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1531_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1531_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1531_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1531_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1531_2000).1 (bothLoop_sound b_1531_2400).1))))))

theorem n_row_1531 : nGrid.row evalE 1531 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1531_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1531_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1531_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1531_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1531_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1531_2000).2 (bothLoop_sound b_1531_2400).2))))))

theorem b_1532_0 : bothSeg evalE (oGrid.idx 1532) (oGrid.dm 1532) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1532) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 74811021844273360006593993178454898838931896454231914891893479223399979626⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1532_400 : bothSeg evalE (oGrid.idx 1532) (oGrid.dm 1532) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1532) oGrid.kl oGrid.kr 400 400 ⟨false, 74811021844273360006593993178454898838931896454231914891893479223399979626⟩ ⟨false, 0⟩ ⟨false, 141779973022035449906837793821645913744449786543188892004792056477123311934⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1532_800 : bothSeg evalE (oGrid.idx 1532) (oGrid.dm 1532) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1532) oGrid.kl oGrid.kr 400 800 ⟨false, 141779973022035449906837793821645913744449786543188892004792056477123311934⟩ ⟨false, 0⟩ ⟨false, 214091951822369488263301543206264540148902071645171995881805686566444640164⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1532_1200 : bothSeg evalE (oGrid.idx 1532) (oGrid.dm 1532) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1532) oGrid.kl oGrid.kr 400 1200 ⟨false, 214091951822369488263301543206264540148902071645171995881805686566444640164⟩ ⟨false, 0⟩ ⟨false, 332380665513627535970107673370728176567995692485761771760092097386130039060⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1532_1600 : bothSeg evalE (oGrid.idx 1532) (oGrid.dm 1532) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1532) oGrid.kl oGrid.kr 400 1600 ⟨false, 332380665513627535970107673370728176567995692485761771760092097386130039060⟩ ⟨false, 0⟩ ⟨false, 500308518739827745079493811562471668119440136120881866859010179316652375566⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1532_2000 : bothSeg evalE (oGrid.idx 1532) (oGrid.dm 1532) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1532) oGrid.kl oGrid.kr 400 2000 ⟨false, 500308518739827745079493811562471668119440136120881866859010179316652375566⟩ ⟨false, 0⟩ ⟨false, 716368823771648742831214415331689757584495444905500456326200250158505806976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1532_2400 : bothLoop evalE (oGrid.idx 1532) (oGrid.dm 1532) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1532) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 716368823771648742831214415331689757584495444905500456326200250158505806976⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1532 : oGrid.row evalE 1532 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1532_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1532_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1532_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1532_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1532_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1532_2000).1 (bothLoop_sound b_1532_2400).1))))))

theorem n_row_1532 : nGrid.row evalE 1532 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1532_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1532_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1532_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1532_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1532_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1532_2000).2 (bothLoop_sound b_1532_2400).2))))))

theorem b_1533_0 : bothSeg evalE (oGrid.idx 1533) (oGrid.dm 1533) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1533) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75100146511670061959322645087096583605943796901522708040565792234485185700⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1533_400 : bothSeg evalE (oGrid.idx 1533) (oGrid.dm 1533) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1533) oGrid.kl oGrid.kr 400 400 ⟨false, 75100146511670061959322645087096583605943796901522708040565792234485185700⟩ ⟨false, 0⟩ ⟨false, 141848414291924189612083809116120548038698084828861914601121954159328368882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1533_800 : bothSeg evalE (oGrid.idx 1533) (oGrid.dm 1533) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1533) oGrid.kl oGrid.kr 400 800 ⟨false, 141848414291924189612083809116120548038698084828861914601121954159328368882⟩ ⟨false, 0⟩ ⟨false, 214477108817425634891290155175877814170661864630058039543952404117369307536⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1533_1200 : bothSeg evalE (oGrid.idx 1533) (oGrid.dm 1533) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1533) oGrid.kl oGrid.kr 400 1200 ⟨false, 214477108817425634891290155175877814170661864630058039543952404117369307536⟩ ⟨false, 0⟩ ⟨false, 333071801496909248644323697452630003626940594200590424796822415938051589262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1533_1600 : bothSeg evalE (oGrid.idx 1533) (oGrid.dm 1533) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1533) oGrid.kl oGrid.kr 400 1600 ⟨false, 333071801496909248644323697452630003626940594200590424796822415938051589262⟩ ⟨false, 0⟩ ⟨false, 501268211557158884299603171460494664671868778128190086479538046507107091606⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1533_2000 : bothSeg evalE (oGrid.idx 1533) (oGrid.dm 1533) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1533) oGrid.kl oGrid.kr 400 2000 ⟨false, 501268211557158884299603171460494664671868778128190086479538046507107091606⟩ ⟨false, 0⟩ ⟨false, 717567029472573569528940734948256977667252629659589225436587365845553094412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1533_2400 : bothLoop evalE (oGrid.idx 1533) (oGrid.dm 1533) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1533) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 717567029472573569528940734948256977667252629659589225436587365845553094412⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1533 : oGrid.row evalE 1533 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1533_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1533_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1533_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1533_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1533_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1533_2000).1 (bothLoop_sound b_1533_2400).1))))))

theorem n_row_1533 : nGrid.row evalE 1533 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1533_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1533_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1533_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1533_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1533_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1533_2000).2 (bothLoop_sound b_1533_2400).2))))))

theorem b_1534_0 : bothSeg evalE (oGrid.idx 1534) (oGrid.dm 1534) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1534) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75376593006045135362205761242344444878981151377394613286442447760289988830⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1534_400 : bothSeg evalE (oGrid.idx 1534) (oGrid.dm 1534) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1534) oGrid.kl oGrid.kr 400 400 ⟨false, 75376593006045135362205761242344444878981151377394613286442447760289988830⟩ ⟨false, 0⟩ ⟨false, 141903286891248376674567228893695211223369113019527825515708757034158547732⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1534_800 : bothSeg evalE (oGrid.idx 1534) (oGrid.dm 1534) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1534) oGrid.kl oGrid.kr 400 800 ⟨false, 141903286891248376674567228893695211223369113019527825515708757034158547732⟩ ⟨false, 0⟩ ⟨false, 214850596697903572712878524362936208101310591566033811367267250238849303956⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1534_1200 : bothSeg evalE (oGrid.idx 1534) (oGrid.dm 1534) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1534) oGrid.kl oGrid.kr 400 1200 ⟨false, 214850596697903572712878524362936208101310591566033811367267250238849303956⟩ ⟨false, 0⟩ ⟨false, 333751247158643278914305903921396674268853069292263190398250320719126876414⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1534_1600 : bothSeg evalE (oGrid.idx 1534) (oGrid.dm 1534) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1534) oGrid.kl oGrid.kr 400 1600 ⟨false, 333751247158643278914305903921396674268853069292263190398250320719126876414⟩ ⟨false, 0⟩ ⟨false, 502216225380903529294518072931039484729514416207928623350332259536700927426⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1534_2000 : bothSeg evalE (oGrid.idx 1534) (oGrid.dm 1534) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1534) oGrid.kl oGrid.kr 400 2000 ⟨false, 502216225380903529294518072931039484729514416207928623350332259536700927426⟩ ⟨false, 0⟩ ⟨false, 718753585757462754322794992157752631214671753048682741474909860940214894158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1534_2400 : bothLoop evalE (oGrid.idx 1534) (oGrid.dm 1534) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1534) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 718753585757462754322794992157752631214671753048682741474909860940214894158⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1534 : oGrid.row evalE 1534 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1534_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1534_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1534_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1534_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1534_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1534_2000).1 (bothLoop_sound b_1534_2400).1))))))

theorem n_row_1534 : nGrid.row evalE 1534 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1534_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1534_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1534_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1534_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1534_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1534_2000).2 (bothLoop_sound b_1534_2400).2))))))

theorem b_1535_0 : bothSeg evalE (oGrid.idx 1535) (oGrid.dm 1535) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1535) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 75640054151143569697979321791638463900180469098764016249648257695736138376⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1535_400 : bothSeg evalE (oGrid.idx 1535) (oGrid.dm 1535) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1535) oGrid.kl oGrid.kr 400 400 ⟨false, 75640054151143569697979321791638463900180469098764016249648257695736138376⟩ ⟨false, 0⟩ ⟨false, 141944632884942584862990987502400855084736852994813059588511361004004390906⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1535_800 : bothSeg evalE (oGrid.idx 1535) (oGrid.dm 1535) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1535) oGrid.kl oGrid.kr 400 800 ⟨false, 141944632884942584862990987502400855084736852994813059588511361004004390906⟩ ⟨false, 0⟩ ⟨false, 215212367934447633126189032924003413219814488928693636457556640959801535474⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1535_1200 : bothSeg evalE (oGrid.idx 1535) (oGrid.dm 1535) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1535) oGrid.kl oGrid.kr 400 1200 ⟨false, 215212367934447633126189032924003413219814488928693636457556640959801535474⟩ ⟨false, 0⟩ ⟨false, 334418954941601990428768720819117909487861976946257509067799183203643813382⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1535_1600 : bothSeg evalE (oGrid.idx 1535) (oGrid.dm 1535) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1535) oGrid.kl oGrid.kr 400 1600 ⟨false, 334418954941601990428768720819117909487861976946257509067799183203643813382⟩ ⟨false, 0⟩ ⟨false, 503152512599443710024799298061427266077024947393426552909832707877067106576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1535_2000 : bothSeg evalE (oGrid.idx 1535) (oGrid.dm 1535) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1535) oGrid.kl oGrid.kr 400 2000 ⟨false, 503152512599443710024799298061427266077024947393426552909832707877067106576⟩ ⟨false, 0⟩ ⟨false, 719928444957128215186570223955115084546865864925823590644536764939314141454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1535_2400 : bothLoop evalE (oGrid.idx 1535) (oGrid.dm 1535) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1535) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 719928444957128215186570223955115084546865864925823590644536764939314141454⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1535 : oGrid.row evalE 1535 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1535_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1535_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1535_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1535_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1535_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1535_2000).1 (bothLoop_sound b_1535_2400).1))))))

theorem n_row_1535 : nGrid.row evalE 1535 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1535_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1535_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1535_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1535_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1535_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1535_2000).2 (bothLoop_sound b_1535_2400).2))))))

theorem o_blk_1512 : allFrom (fun j => oGrid.row evalE j) 1512 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1512) o_row_1512 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1513) o_row_1513 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1514) o_row_1514 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1515) o_row_1515 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1516) o_row_1516 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1517) o_row_1517 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1518) o_row_1518 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1519) o_row_1519 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1520) o_row_1520 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1521) o_row_1521 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1522) o_row_1522 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1523) o_row_1523 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1524) o_row_1524 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1525) o_row_1525 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1526) o_row_1526 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1527) o_row_1527 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1528) o_row_1528 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1529) o_row_1529 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1530) o_row_1530 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1531) o_row_1531 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1532) o_row_1532 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1533) o_row_1533 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1534) o_row_1534 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1535) o_row_1535 (allFrom_zero (fun j => oGrid.row evalE j) 1536)))))))))))))))))))))))))

theorem n_blk_1512 : allFrom (fun j => nGrid.row evalE j) 1512 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1512) n_row_1512 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1513) n_row_1513 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1514) n_row_1514 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1515) n_row_1515 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1516) n_row_1516 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1517) n_row_1517 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1518) n_row_1518 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1519) n_row_1519 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1520) n_row_1520 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1521) n_row_1521 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1522) n_row_1522 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1523) n_row_1523 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1524) n_row_1524 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1525) n_row_1525 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1526) n_row_1526 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1527) n_row_1527 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1528) n_row_1528 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1529) n_row_1529 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1530) n_row_1530 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1531) n_row_1531 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1532) n_row_1532 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1533) n_row_1533 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1534) n_row_1534 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1535) n_row_1535 (allFrom_zero (fun j => nGrid.row evalE j) 1536)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
