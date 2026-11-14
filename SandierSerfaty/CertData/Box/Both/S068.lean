/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 68 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `1632`–`1655`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_1632_0 : bothSeg evalE (oGrid.idx 1632) (oGrid.dm 1632) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1632) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59594132004365004206332572752663968609082095900029614572753068778957555274⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1632_400 : bothSeg evalE (oGrid.idx 1632) (oGrid.dm 1632) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1632) oGrid.kl oGrid.kr 400 400 ⟨false, 59594132004365004206332572752663968609082095900029614572753068778957555274⟩ ⟨false, 0⟩ ⟨false, 132700649399347319119509543619610679702649989282038081483096598984306261172⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1632_800 : bothSeg evalE (oGrid.idx 1632) (oGrid.dm 1632) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1632) oGrid.kl oGrid.kr 400 800 ⟨false, 132700649399347319119509543619610679702649989282038081483096598984306261172⟩ ⟨false, 0⟩ ⟨false, 239044918942610533096151782453302696843616369785976501375522641505692751594⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1632_1200 : bothSeg evalE (oGrid.idx 1632) (oGrid.dm 1632) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1632) oGrid.kl oGrid.kr 400 1200 ⟨false, 239044918942610533096151782453302696843616369785976501375522641505692751594⟩ ⟨false, 0⟩ ⟨false, 387822406188158577748596813096891778945979251207153138850700231476748508378⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1632_1600 : bothSeg evalE (oGrid.idx 1632) (oGrid.dm 1632) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1632) oGrid.kl oGrid.kr 400 1600 ⟨false, 387822406188158577748596813096891778945979251207153138850700231476748508378⟩ ⟨false, 0⟩ ⟨false, 582653609908816552655324634079383434417833931157565514096754987361879735430⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1632_2000 : bothSeg evalE (oGrid.idx 1632) (oGrid.dm 1632) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1632) oGrid.kl oGrid.kr 400 2000 ⟨false, 582653609908816552655324634079383434417833931157565514096754987361879735430⟩ ⟨false, 0⟩ ⟨false, 822702597416954456452900092502643187549544141331521883658291409891217709730⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1632_2400 : bothLoop evalE (oGrid.idx 1632) (oGrid.dm 1632) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1632) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 822702597416954456452900092502643187549544141331521883658291409891217709730⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1632 : oGrid.row evalE 1632 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1632_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1632_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1632_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1632_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1632_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1632_2000).1 (bothLoop_sound b_1632_2400).1))))))

theorem n_row_1632 : nGrid.row evalE 1632 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1632_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1632_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1632_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1632_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1632_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1632_2000).2 (bothLoop_sound b_1632_2400).2))))))

theorem b_1633_0 : bothSeg evalE (oGrid.idx 1633) (oGrid.dm 1633) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1633) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59648160316029964744074687086934829092968856056755217438945194454722395720⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1633_400 : bothSeg evalE (oGrid.idx 1633) (oGrid.dm 1633) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1633) oGrid.kl oGrid.kr 400 400 ⟨false, 59648160316029964744074687086934829092968856056755217438945194454722395720⟩ ⟨false, 0⟩ ⟨false, 133115311792975554146813666830150726888883576681497434012595196840903156114⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1633_800 : bothSeg evalE (oGrid.idx 1633) (oGrid.dm 1633) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1633) oGrid.kl oGrid.kr 400 800 ⟨false, 133115311792975554146813666830150726888883576681497434012595196840903156114⟩ ⟨false, 0⟩ ⟨false, 239800276314257519692467765414353331782061536909995897930490608172349872272⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1633_1200 : bothSeg evalE (oGrid.idx 1633) (oGrid.dm 1633) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1633) oGrid.kl oGrid.kr 400 1200 ⟨false, 239800276314257519692467765414353331782061536909995897930490608172349872272⟩ ⟨false, 0⟩ ⟨false, 388881498401246549671948176771489363623851948430356095704441555218042891508⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1633_1600 : bothSeg evalE (oGrid.idx 1633) (oGrid.dm 1633) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1633) oGrid.kl oGrid.kr 400 1600 ⟨false, 388881498401246549671948176771489363623851948430356095704441555218042891508⟩ ⟨false, 0⟩ ⟨false, 583982138416145613320480714806677721715144785692644047291970615121690056738⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1633_2000 : bothSeg evalE (oGrid.idx 1633) (oGrid.dm 1633) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1633) oGrid.kl oGrid.kr 400 2000 ⟨false, 583982138416145613320480714806677721715144785692644047291970615121690056738⟩ ⟨false, 0⟩ ⟨false, 824272323664412816732106400392962032866878067412623448863049157719506425138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1633_2400 : bothLoop evalE (oGrid.idx 1633) (oGrid.dm 1633) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1633) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 824272323664412816732106400392962032866878067412623448863049157719506425138⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1633 : oGrid.row evalE 1633 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1633_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1633_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1633_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1633_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1633_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1633_2000).1 (bothLoop_sound b_1633_2400).1))))))

theorem n_row_1633 : nGrid.row evalE 1633 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1633_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1633_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1633_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1633_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1633_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1633_2000).2 (bothLoop_sound b_1633_2400).2))))))

theorem b_1634_0 : bothSeg evalE (oGrid.idx 1634) (oGrid.dm 1634) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1634) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59716605147465275518797788950406981727953546408079944184507579772039649884⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1634_400 : bothSeg evalE (oGrid.idx 1634) (oGrid.dm 1634) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1634) oGrid.kl oGrid.kr 400 400 ⟨false, 59716605147465275518797788950406981727953546408079944184507579772039649884⟩ ⟨false, 0⟩ ⟨false, 133545893605031591505341717089382646165893983831197655080151834395329411116⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1634_800 : bothSeg evalE (oGrid.idx 1634) (oGrid.dm 1634) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1634) oGrid.kl oGrid.kr 400 800 ⟨false, 133545893605031591505341717089382646165893983831197655080151834395329411116⟩ ⟨false, 0⟩ ⟨false, 240571489501600994823520107729812989634598203842514628258566743973720298694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1634_1200 : bothSeg evalE (oGrid.idx 1634) (oGrid.dm 1634) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1634) oGrid.kl oGrid.kr 400 1200 ⟨false, 240571489501600994823520107729812989634598203842514628258566743973720298694⟩ ⟨false, 0⟩ ⟨false, 389956422871733137536194230305742403307784951932460492182960393289669044078⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1634_1600 : bothSeg evalE (oGrid.idx 1634) (oGrid.dm 1634) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1634) oGrid.kl oGrid.kr 400 1600 ⟨false, 389956422871733137536194230305742403307784951932460492182960393289669044078⟩ ⟨false, 0⟩ ⟨false, 585326505549927274921654381302059626735196615681812763788402326912952440050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1634_2000 : bothSeg evalE (oGrid.idx 1634) (oGrid.dm 1634) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1634) oGrid.kl oGrid.kr 400 2000 ⟨false, 585326505549927274921654381302059626735196615681812763788402326912952440050⟩ ⟨false, 0⟩ ⟨false, 825857912725218773830648775858571024759633118540927433793159917701288966732⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1634_2400 : bothLoop evalE (oGrid.idx 1634) (oGrid.dm 1634) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1634) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 825857912725218773830648775858571024759633118540927433793159917701288966732⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1634 : oGrid.row evalE 1634 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1634_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1634_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1634_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1634_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1634_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1634_2000).1 (bothLoop_sound b_1634_2400).1))))))

theorem n_row_1634 : nGrid.row evalE 1634 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1634_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1634_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1634_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1634_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1634_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1634_2000).2 (bothLoop_sound b_1634_2400).2))))))

theorem b_1635_0 : bothSeg evalE (oGrid.idx 1635) (oGrid.dm 1635) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1635) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59799315362225999651157762742779372323985565469691338938761278543802970054⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1635_400 : bothSeg evalE (oGrid.idx 1635) (oGrid.dm 1635) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1635) oGrid.kl oGrid.kr 400 400 ⟨false, 59799315362225999651157762742779372323985565469691338938761278543802970054⟩ ⟨false, 0⟩ ⟨false, 133992107004033231120181001162204828055776478722117352270083104037532652178⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1635_800 : bothSeg evalE (oGrid.idx 1635) (oGrid.dm 1635) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1635) oGrid.kl oGrid.kr 400 800 ⟨false, 133992107004033231120181001162204828055776478722117352270083104037532652178⟩ ⟨false, 0⟩ ⟨false, 241358270703551664536046601318144675686882192316016921475521503213941382684⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1635_1200 : bothSeg evalE (oGrid.idx 1635) (oGrid.dm 1635) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1635) oGrid.kl oGrid.kr 400 1200 ⟨false, 241358270703551664536046601318144675686882192316016921475521503213941382684⟩ ⟨false, 0⟩ ⟨false, 391046891779126096796320749949949664784871018053050984698821415799982622372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1635_1600 : bothSeg evalE (oGrid.idx 1635) (oGrid.dm 1635) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1635) oGrid.kl oGrid.kr 400 1600 ⟨false, 391046891779126096796320749949949664784871018053050984698821415799982622372⟩ ⟨false, 0⟩ ⟨false, 586686423444719817601902554886166127922460064361927580184680515731878872712⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1635_2000 : bothSeg evalE (oGrid.idx 1635) (oGrid.dm 1635) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1635) oGrid.kl oGrid.kr 400 2000 ⟨false, 586686423444719817601902554886166127922460064361927580184680515731878872712⟩ ⟨false, 0⟩ ⟨false, 827459076683631172646243987648964395511594177532395317451227004168297713666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1635_2400 : bothLoop evalE (oGrid.idx 1635) (oGrid.dm 1635) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1635) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 827459076683631172646243987648964395511594177532395317451227004168297713666⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1635 : oGrid.row evalE 1635 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1635_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1635_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1635_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1635_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1635_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1635_2000).1 (bothLoop_sound b_1635_2400).1))))))

theorem n_row_1635 : nGrid.row evalE 1635 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1635_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1635_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1635_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1635_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1635_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1635_2000).2 (bothLoop_sound b_1635_2400).2))))))

theorem b_1636_0 : bothSeg evalE (oGrid.idx 1636) (oGrid.dm 1636) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1636) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 59896121759490833409960831978612916050457306894466123188781714151962522972⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1636_400 : bothSeg evalE (oGrid.idx 1636) (oGrid.dm 1636) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1636) oGrid.kl oGrid.kr 400 400 ⟨false, 59896121759490833409960831978612916050457306894466123188781714151962522972⟩ ⟨false, 0⟩ ⟨false, 134453652004967341543148784731824976110754804022607878911697437377983142752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1636_800 : bothSeg evalE (oGrid.idx 1636) (oGrid.dm 1636) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1636) oGrid.kl oGrid.kr 400 800 ⟨false, 134453652004967341543148784731824976110754804022607878911697437377983142752⟩ ⟨false, 0⟩ ⟨false, 242160319965498876162782262331262438816413479481088765343326819851343669150⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1636_1200 : bothSeg evalE (oGrid.idx 1636) (oGrid.dm 1636) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1636) oGrid.kl oGrid.kr 400 1200 ⟨false, 242160319965498876162782262331262438816413479481088765343326819851343669150⟩ ⟨false, 0⟩ ⟨false, 392152605149486788686570051815777518008071314793860901348445790664098798792⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1636_1600 : bothSeg evalE (oGrid.idx 1636) (oGrid.dm 1636) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1636) oGrid.kl oGrid.kr 400 1600 ⟨false, 392152605149486788686570051815777518008071314793860901348445790664098798792⟩ ⟨false, 0⟩ ⟨false, 588061592081721958583902425627018315889798723162917188416259114621992543422⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1636_2000 : bothSeg evalE (oGrid.idx 1636) (oGrid.dm 1636) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1636) oGrid.kl oGrid.kr 400 2000 ⟨false, 588061592081721958583902425627018315889798723162917188416259114621992543422⟩ ⟨false, 0⟩ ⟨false, 829075515470618117073759010943982097413676203299371299718059641495181975520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1636_2400 : bothLoop evalE (oGrid.idx 1636) (oGrid.dm 1636) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1636) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 829075515470618117073759010943982097413676203299371299718059641495181975520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1636 : oGrid.row evalE 1636 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1636_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1636_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1636_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1636_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1636_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1636_2000).1 (bothLoop_sound b_1636_2400).1))))))

theorem n_row_1636 : nGrid.row evalE 1636 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1636_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1636_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1636_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1636_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1636_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1636_2000).2 (bothLoop_sound b_1636_2400).2))))))

theorem b_1637_0 : bothSeg evalE (oGrid.idx 1637) (oGrid.dm 1637) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1637) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60006833142837985480899411019312929941644929593942531229807481302943828944⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1637_400 : bothSeg evalE (oGrid.idx 1637) (oGrid.dm 1637) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1637) oGrid.kl oGrid.kr 400 400 ⟨false, 60006833142837985480899411019312929941644929593942531229807481302943828944⟩ ⟨false, 0⟩ ⟨false, 134930211551624462303328185218979106896251335538540992629123055114902973736⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1637_800 : bothSeg evalE (oGrid.idx 1637) (oGrid.dm 1637) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1637) oGrid.kl oGrid.kr 400 800 ⟨false, 134930211551624462303328185218979106896251335538540992629123055114902973736⟩ ⟨false, 0⟩ ⟨false, 242977320261645120458544792156101340589333134277529394340132290773381732834⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1637_1200 : bothSeg evalE (oGrid.idx 1637) (oGrid.dm 1637) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1637) oGrid.kl oGrid.kr 400 1200 ⟨false, 242977320261645120458544792156101340589333134277529394340132290773381732834⟩ ⟨false, 0⟩ ⟨false, 393273245937764503822330727977952579876197878956323700981208215501832042514⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1637_1600 : bothSeg evalE (oGrid.idx 1637) (oGrid.dm 1637) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1637) oGrid.kl oGrid.kr 400 1600 ⟨false, 393273245937764503822330727977952579876197878956323700981208215501832042514⟩ ⟨false, 0⟩ ⟨false, 589451694371107032860845824186946348538021504405024105672375818331355086576⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1637_2000 : bothSeg evalE (oGrid.idx 1637) (oGrid.dm 1637) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1637) oGrid.kl oGrid.kr 400 2000 ⟨false, 589451694371107032860845824186946348538021504405024105672375818331355086576⟩ ⟨false, 0⟩ ⟨false, 830706911946191074976716218577901750716932152001586721083933903305473668808⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1637_2400 : bothLoop evalE (oGrid.idx 1637) (oGrid.dm 1637) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1637) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 830706911946191074976716218577901750716932152001586721083933903305473668808⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1637 : oGrid.row evalE 1637 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1637_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1637_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1637_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1637_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1637_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1637_2000).1 (bothLoop_sound b_1637_2400).1))))))

theorem n_row_1637 : nGrid.row evalE 1637 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1637_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1637_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1637_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1637_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1637_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1637_2000).2 (bothLoop_sound b_1637_2400).2))))))

theorem b_1638_0 : bothSeg evalE (oGrid.idx 1638) (oGrid.dm 1638) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1638) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60131243771655793551119565772055390650111359700880727278228709998197549320⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1638_400 : bothSeg evalE (oGrid.idx 1638) (oGrid.dm 1638) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1638) oGrid.kl oGrid.kr 400 400 ⟨false, 60131243771655793551119565772055390650111359700880727278228709998197549320⟩ ⟨false, 0⟩ ⟨false, 135421457157855195153103960246933547014047743057657986025476811704920153876⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1638_800 : bothSeg evalE (oGrid.idx 1638) (oGrid.dm 1638) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1638) oGrid.kl oGrid.kr 400 800 ⟨false, 135421457157855195153103960246933547014047743057657986025476811704920153876⟩ ⟨false, 0⟩ ⟨false, 243808943136262322983962944600120157429512601319550170055461890832450320664⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1638_1200 : bothSeg evalE (oGrid.idx 1638) (oGrid.dm 1638) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1638) oGrid.kl oGrid.kr 400 1200 ⟨false, 243808943136262322983962944600120157429512601319550170055461890832450320664⟩ ⟨false, 0⟩ ⟨false, 394408485669052575441047986693035617685128863468476771336206674010505324668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1638_1600 : bothSeg evalE (oGrid.idx 1638) (oGrid.dm 1638) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1638) oGrid.kl oGrid.kr 400 1600 ⟨false, 394408485669052575441047986693035617685128863468476771336206674010505324668⟩ ⟨false, 0⟩ ⟨false, 590856401793278963731435368814051653009608865986277465621043685477200113900⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1638_2000 : bothSeg evalE (oGrid.idx 1638) (oGrid.dm 1638) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1638) oGrid.kl oGrid.kr 400 2000 ⟨false, 590856401793278963731435368814051653009608865986277465621043685477200113900⟩ ⟨false, 0⟩ ⟨false, 832352937540660773042293249774685851151574302935058480297444119752728051346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1638_2400 : bothLoop evalE (oGrid.idx 1638) (oGrid.dm 1638) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1638) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 832352937540660773042293249774685851151574302935058480297444119752728051346⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1638 : oGrid.row evalE 1638 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1638_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1638_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1638_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1638_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1638_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1638_2000).1 (bothLoop_sound b_1638_2400).1))))))

theorem n_row_1638 : nGrid.row evalE 1638 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1638_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1638_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1638_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1638_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1638_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1638_2000).2 (bothLoop_sound b_1638_2400).2))))))

theorem b_1639_0 : bothSeg evalE (oGrid.idx 1639) (oGrid.dm 1639) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1639) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60269127146832394040312592871713581645870817071989285883644693185913694228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1639_400 : bothSeg evalE (oGrid.idx 1639) (oGrid.dm 1639) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1639) oGrid.kl oGrid.kr 400 400 ⟨false, 60269127146832394040312592871713581645870817071989285883644693185913694228⟩ ⟨false, 0⟩ ⟨false, 135927046522811984780441712092284017978463804335074938489454907017201622656⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1639_800 : bothSeg evalE (oGrid.idx 1639) (oGrid.dm 1639) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1639) oGrid.kl oGrid.kr 400 800 ⟨false, 135927046522811984780441712092284017978463804335074938489454907017201622656⟩ ⟨false, 0⟩ ⟨false, 244654846318933525306493911422448266339672795713856032781676656379640771470⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1639_1200 : bothSeg evalE (oGrid.idx 1639) (oGrid.dm 1639) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1639) oGrid.kl oGrid.kr 400 1200 ⟨false, 244654846318933525306493911422448266339672795713856032781676656379640771470⟩ ⟨false, 0⟩ ⟨false, 395557982053829882850980908093939869516866299326864800877848220596466177436⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1639_1600 : bothSeg evalE (oGrid.idx 1639) (oGrid.dm 1639) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1639) oGrid.kl oGrid.kr 400 1600 ⟨false, 395557982053829882850980908093939869516866299326864800877848220596466177436⟩ ⟨false, 0⟩ ⟨false, 592275372014113623747617675457507829975377078181708154261764469145397099586⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1639_2000 : bothSeg evalE (oGrid.idx 1639) (oGrid.dm 1639) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1639) oGrid.kl oGrid.kr 400 2000 ⟨false, 592275372014113623747617675457507829975377078181708154261764469145397099586⟩ ⟨false, 0⟩ ⟨false, 834013249869878482088587605476724582715598858620215552576468239359242280476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1639_2400 : bothLoop evalE (oGrid.idx 1639) (oGrid.dm 1639) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1639) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 834013249869878482088587605476724582715598858620215552576468239359242280476⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1639 : oGrid.row evalE 1639 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1639_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1639_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1639_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1639_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1639_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1639_2000).1 (bothLoop_sound b_1639_2400).1))))))

theorem n_row_1639 : nGrid.row evalE 1639 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1639_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1639_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1639_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1639_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1639_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1639_2000).2 (bothLoop_sound b_1639_2400).2))))))

theorem b_1640_0 : bothSeg evalE (oGrid.idx 1640) (oGrid.dm 1640) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1640) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60420235808683036026541760085420198766766234614194202509620169741435381120⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1640_400 : bothSeg evalE (oGrid.idx 1640) (oGrid.dm 1640) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1640) oGrid.kl oGrid.kr 400 400 ⟨false, 60420235808683036026541760085420198766766234614194202509620169741435381120⟩ ⟨false, 0⟩ ⟨false, 136446621298161233691019191862880989088708507227833194255587417652185939962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1640_800 : bothSeg evalE (oGrid.idx 1640) (oGrid.dm 1640) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1640) oGrid.kl oGrid.kr 400 800 ⟨false, 136446621298161233691019191862880989088708507227833194255587417652185939962⟩ ⟨false, 0⟩ ⟨false, 245514671491764900721244372540197509401631817112819932471503910390315174068⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1640_1200 : bothSeg evalE (oGrid.idx 1640) (oGrid.dm 1640) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1640) oGrid.kl oGrid.kr 400 1200 ⟨false, 245514671491764900721244372540197509401631817112819932471503910390315174068⟩ ⟨false, 0⟩ ⟨false, 396721376755172689789503013897093716654934401606446683401129805421193495600⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1640_1600 : bothSeg evalE (oGrid.idx 1640) (oGrid.dm 1640) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1640) oGrid.kl oGrid.kr 400 1600 ⟨false, 396721376755172689789503013897093716654934401606446683401129805421193495600⟩ ⟨false, 0⟩ ⟨false, 593708246652170530776558736376177593315976124684631650214031581230264297044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1640_2000 : bothSeg evalE (oGrid.idx 1640) (oGrid.dm 1640) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1640) oGrid.kl oGrid.kr 400 2000 ⟨false, 593708246652170530776558736376177593315976124684631650214031581230264297044⟩ ⟨false, 0⟩ ⟨false, 835687490502447637525785157106401524826672142477946884548851943595159030080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1640_2400 : bothLoop evalE (oGrid.idx 1640) (oGrid.dm 1640) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1640) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 835687490502447637525785157106401524826672142477946884548851943595159030080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1640 : oGrid.row evalE 1640 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1640_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1640_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1640_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1640_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1640_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1640_2000).1 (bothLoop_sound b_1640_2400).1))))))

theorem n_row_1640 : nGrid.row evalE 1640 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1640_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1640_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1640_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1640_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1640_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1640_2000).2 (bothLoop_sound b_1640_2400).2))))))

theorem b_1641_0 : bothSeg evalE (oGrid.idx 1641) (oGrid.dm 1641) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1641) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60584306938288624147901344913299554926932513841981974458141650053751579368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1641_400 : bothSeg evalE (oGrid.idx 1641) (oGrid.dm 1641) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1641) oGrid.kl oGrid.kr 400 400 ⟨false, 60584306938288624147901344913299554926932513841981974458141650053751579368⟩ ⟨false, 0⟩ ⟨false, 136979812639974143962709965460649385833039100950793315890030483212903783368⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1641_800 : bothSeg evalE (oGrid.idx 1641) (oGrid.dm 1641) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1641) oGrid.kl oGrid.kr 400 800 ⟨false, 136979812639974143962709965460649385833039100950793315890030483212903783368⟩ ⟨false, 0⟩ ⟨false, 246388049841276497193004795903193415371421099079109767229190600857650006102⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1641_1200 : bothSeg evalE (oGrid.idx 1641) (oGrid.dm 1641) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1641) oGrid.kl oGrid.kr 400 1200 ⟨false, 246388049841276497193004795903193415371421099079109767229190600857650006102⟩ ⟨false, 0⟩ ⟨false, 397898300940645210391539039292250842396374973170460654625136609218883394984⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1641_1600 : bothSeg evalE (oGrid.idx 1641) (oGrid.dm 1641) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1641) oGrid.kl oGrid.kr 400 1600 ⟨false, 397898300940645210391539039292250842396374973170460654625136609218883394984⟩ ⟨false, 0⟩ ⟨false, 595154656830583271877262795001583312219349153731421576861536586736725871434⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1641_2000 : bothSeg evalE (oGrid.idx 1641) (oGrid.dm 1641) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1641) oGrid.kl oGrid.kr 400 2000 ⟨false, 595154656830583271877262795001583312219349153731421576861536586736725871434⟩ ⟨false, 0⟩ ⟨false, 837375290511614187671767300386608232199426507456357488906882607547182161464⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1641_2400 : bothLoop evalE (oGrid.idx 1641) (oGrid.dm 1641) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1641) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 837375290511614187671767300386608232199426507456357488906882607547182161464⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1641 : oGrid.row evalE 1641 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1641_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1641_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1641_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1641_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1641_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1641_2000).1 (bothLoop_sound b_1641_2400).1))))))

theorem n_row_1641 : nGrid.row evalE 1641 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1641_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1641_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1641_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1641_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1641_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1641_2000).2 (bothLoop_sound b_1641_2400).2))))))

theorem b_1642_0 : bothSeg evalE (oGrid.idx 1642) (oGrid.dm 1642) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1642) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60761063882818773033881173343806555092680650550145776634357027365297606746⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1642_400 : bothSeg evalE (oGrid.idx 1642) (oGrid.dm 1642) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1642) oGrid.kl oGrid.kr 400 400 ⟨false, 60761063882818773033881173343806555092680650550145776634357027365297606746⟩ ⟨false, 0⟩ ⟨false, 137526243454989127388350144172283212683653537135054945340590763240975308882⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1642_800 : bothSeg evalE (oGrid.idx 1642) (oGrid.dm 1642) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1642) oGrid.kl oGrid.kr 400 800 ⟨false, 137526243454989127388350144172283212683653537135054945340590763240975308882⟩ ⟨false, 0⟩ ⟨false, 247274604304664549034340362775879620839099176252874576568931315718457562004⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1642_1200 : bothSeg evalE (oGrid.idx 1642) (oGrid.dm 1642) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1642) oGrid.kl oGrid.kr 400 1200 ⟨false, 247274604304664549034340362775879620839099176252874576568931315718457562004⟩ ⟨false, 0⟩ ⟨false, 399088377528561744282166134856222550084986096708336450343456573696186401096⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1642_1600 : bothSeg evalE (oGrid.idx 1642) (oGrid.dm 1642) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1642) oGrid.kl oGrid.kr 400 1600 ⟨false, 399088377528561744282166134856222550084986096708336450343456573696186401096⟩ ⟨false, 0⟩ ⟨false, 596614225423321496505671119781459740389134122278690633714528487969219085754⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1642_2000 : bothSeg evalE (oGrid.idx 1642) (oGrid.dm 1642) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1642) oGrid.kl oGrid.kr 400 2000 ⟨false, 596614225423321496505671119781459740389134122278690633714528487969219085754⟩ ⟨false, 0⟩ ⟨false, 839076272721528511436125885230840147670771416163773649132158374884233546560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1642_2400 : bothLoop evalE (oGrid.idx 1642) (oGrid.dm 1642) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1642) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 839076272721528511436125885230840147670771416163773649132158374884233546560⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1642 : oGrid.row evalE 1642 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1642_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1642_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1642_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1642_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1642_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1642_2000).1 (bothLoop_sound b_1642_2400).1))))))

theorem n_row_1642 : nGrid.row evalE 1642 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1642_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1642_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1642_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1642_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1642_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1642_2000).2 (bothLoop_sound b_1642_2400).2))))))

theorem b_1643_0 : bothSeg evalE (oGrid.idx 1643) (oGrid.dm 1643) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1643) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 60950213343375235413115744868387328527900865718431508079415252997056597492⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1643_400 : bothSeg evalE (oGrid.idx 1643) (oGrid.dm 1643) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1643) oGrid.kl oGrid.kr 400 400 ⟨false, 60950213343375235413115744868387328527900865718431508079415252997056597492⟩ ⟨false, 0⟩ ⟨false, 138085526230964610385606516758158215096461313934027007084819845891609992174⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1643_800 : bothSeg evalE (oGrid.idx 1643) (oGrid.dm 1643) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1643) oGrid.kl oGrid.kr 400 800 ⟨false, 138085526230964610385606516758158215096461313934027007084819845891609992174⟩ ⟨false, 0⟩ ⟨false, 248173947400154183697472867797886584398632097933599348767670788080867689390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1643_1200 : bothSeg evalE (oGrid.idx 1643) (oGrid.dm 1643) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1643) oGrid.kl oGrid.kr 400 1200 ⟨false, 248173947400154183697472867797886584398632097933599348767670788080867689390⟩ ⟨false, 0⟩ ⟨false, 400291219018339207170300246844218418001766365507055365314923476586541188366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1643_1600 : bothSeg evalE (oGrid.idx 1643) (oGrid.dm 1643) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1643) oGrid.kl oGrid.kr 400 1600 ⟨false, 400291219018339207170300246844218418001766365507055365314923476586541188366⟩ ⟨false, 0⟩ ⟨false, 598086564885543305424969338060893095817988979939625457599570608688131862172⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1643_2000 : bothSeg evalE (oGrid.idx 1643) (oGrid.dm 1643) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1643) oGrid.kl oGrid.kr 400 2000 ⟨false, 598086564885543305424969338060893095817988979939625457599570608688131862172⟩ ⟨false, 0⟩ ⟨false, 840790049537597731749446637483327822512034080085826852109611849821043489680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1643_2400 : bothLoop evalE (oGrid.idx 1643) (oGrid.dm 1643) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1643) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 840790049537597731749446637483327822512034080085826852109611849821043489680⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1643 : oGrid.row evalE 1643 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1643_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1643_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1643_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1643_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1643_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1643_2000).1 (bothLoop_sound b_1643_2400).1))))))

theorem n_row_1643 : nGrid.row evalE 1643 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1643_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1643_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1643_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1643_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1643_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1643_2000).2 (bothLoop_sound b_1643_2400).2))))))

theorem b_1644_0 : bothSeg evalE (oGrid.idx 1644) (oGrid.dm 1644) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1644) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61151445750188659319915046905743851053897363975027040713930223690548219694⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1644_400 : bothSeg evalE (oGrid.idx 1644) (oGrid.dm 1644) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1644) oGrid.kl oGrid.kr 400 400 ⟨false, 61151445750188659319915046905743851053897363975027040713930223690548219694⟩ ⟨false, 0⟩ ⟨false, 138657262977883548953513823564812329378353423402694015318626370919992360966⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1644_800 : bothSeg evalE (oGrid.idx 1644) (oGrid.dm 1644) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1644) oGrid.kl oGrid.kr 400 800 ⟨false, 138657262977883548953513823564812329378353423402694015318626370919992360966⟩ ⟨false, 0⟩ ⟨false, 249085681168203838958440676132223720809718064398425275740386587235644217714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1644_1200 : bothSeg evalE (oGrid.idx 1644) (oGrid.dm 1644) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1644) oGrid.kl oGrid.kr 400 1200 ⟨false, 249085681168203838958440676132223720809718064398425275740386587235644217714⟩ ⟨false, 0⟩ ⟨false, 401506427431701372221142701981064786451937394330916940103390105967175929028⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1644_1600 : bothSeg evalE (oGrid.idx 1644) (oGrid.dm 1644) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1644) oGrid.kl oGrid.kr 400 1600 ⟨false, 401506427431701372221142701981064786451937394330916940103390105967175929028⟩ ⟨false, 0⟩ ⟨false, 599571277194799350598586009158462260230711039836164155270015606810736395828⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1644_2000 : bothSeg evalE (oGrid.idx 1644) (oGrid.dm 1644) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1644) oGrid.kl oGrid.kr 400 2000 ⟨false, 599571277194799350598586009158462260230711039836164155270015606810736395828⟩ ⟨false, 0⟩ ⟨false, 842516222887689740015475134844502696485098458366549933312206726720150300568⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1644_2400 : bothLoop evalE (oGrid.idx 1644) (oGrid.dm 1644) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1644) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 842516222887689740015475134844502696485098458366549933312206726720150300568⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1644 : oGrid.row evalE 1644 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1644_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1644_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1644_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1644_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1644_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1644_2000).1 (bothLoop_sound b_1644_2400).1))))))

theorem n_row_1644 : nGrid.row evalE 1644 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1644_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1644_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1644_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1644_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1644_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1644_2000).2 (bothLoop_sound b_1644_2400).2))))))

theorem b_1645_0 : bothSeg evalE (oGrid.idx 1645) (oGrid.dm 1645) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1645) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61364442820353222700456431829943907788946496678229019089290423789303328892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1645_400 : bothSeg evalE (oGrid.idx 1645) (oGrid.dm 1645) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1645) oGrid.kl oGrid.kr 400 400 ⟨false, 61364442820353222700456431829943907788946496678229019089290423789303328892⟩ ⟨false, 0⟩ ⟨false, 139241054080788248759420618430280167086222128304210987179189311425764970788⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1645_800 : bothSeg evalE (oGrid.idx 1645) (oGrid.dm 1645) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1645) oGrid.kl oGrid.kr 400 800 ⟨false, 139241054080788248759420618430280167086222128304210987179189311425764970788⟩ ⟨false, 0⟩ ⟨false, 250009406024339985576198844245441744640562192177880460817282587852602144756⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1645_1200 : bothSeg evalE (oGrid.idx 1645) (oGrid.dm 1645) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1645) oGrid.kl oGrid.kr 400 1200 ⟨false, 250009406024339985576198844245441744640562192177880460817282587852602144756⟩ ⟨false, 0⟩ ⟨false, 402733603165513417289238589890092365588886366428396407210062952819064168544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1645_1600 : bothSeg evalE (oGrid.idx 1645) (oGrid.dm 1645) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1645) oGrid.kl oGrid.kr 400 1600 ⟨false, 402733603165513417289238589890092365588886366428396407210062952819064168544⟩ ⟨false, 0⟩ ⟨false, 601067962703867241147541425644669220486333108485540098332951640457689725548⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1645_2000 : bothSeg evalE (oGrid.idx 1645) (oGrid.dm 1645) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1645) oGrid.kl oGrid.kr 400 2000 ⟨false, 601067962703867241147541425644669220486333108485540098332951640457689725548⟩ ⟨false, 0⟩ ⟨false, 844254393074967526667955039632450611358238982723872150662992247879215136200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1645_2400 : bothLoop evalE (oGrid.idx 1645) (oGrid.dm 1645) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1645) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 844254393074967526667955039632450611358238982723872150662992247879215136200⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1645 : oGrid.row evalE 1645 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1645_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1645_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1645_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1645_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1645_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1645_2000).1 (bothLoop_sound b_1645_2400).1))))))

theorem n_row_1645 : nGrid.row evalE 1645 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1645_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1645_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1645_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1645_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1645_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1645_2000).2 (bothLoop_sound b_1645_2400).2))))))

theorem b_1646_0 : bothSeg evalE (oGrid.idx 1646) (oGrid.dm 1646) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1646) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61588865245974992652636406973646329594331934413980389415105026225352646862⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1646_400 : bothSeg evalE (oGrid.idx 1646) (oGrid.dm 1646) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1646) oGrid.kl oGrid.kr 400 400 ⟨false, 61588865245974992652636406973646329594331934413980389415105026225352646862⟩ ⟨false, 0⟩ ⟨false, 139836484437216036643605696400862736079903521712734952758778656526408451892⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1646_800 : bothSeg evalE (oGrid.idx 1646) (oGrid.dm 1646) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1646) oGrid.kl oGrid.kr 400 800 ⟨false, 139836484437216036643605696400862736079903521712734952758778656526408451892⟩ ⟨false, 0⟩ ⟨false, 250944706896592701712847351845655112265762437996147316403968338661358388334⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1646_1200 : bothSeg evalE (oGrid.idx 1646) (oGrid.dm 1646) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1646) oGrid.kl oGrid.kr 400 1200 ⟨false, 250944706896592701712847351845655112265762437996147316403968338661358388334⟩ ⟨false, 0⟩ ⟨false, 403972331129217324297525918005796811724344898308927312388647061970546996012⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1646_1600 : bothSeg evalE (oGrid.idx 1646) (oGrid.dm 1646) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1646) oGrid.kl oGrid.kr 400 1600 ⟨false, 403972331129217324297525918005796811724344898308927312388647061970546996012⟩ ⟨false, 0⟩ ⟨false, 602576206278186801657332758864223604391996238737448415584881936953477497978⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1646_2000 : bothSeg evalE (oGrid.idx 1646) (oGrid.dm 1646) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1646) oGrid.kl oGrid.kr 400 2000 ⟨false, 602576206278186801657332758864223604391996238737448415584881936953477497978⟩ ⟨false, 0⟩ ⟨false, 846004144915324364117454750537480451690668941850734281997130816271646007790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1646_2400 : bothLoop evalE (oGrid.idx 1646) (oGrid.dm 1646) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1646) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 846004144915324364117454750537480451690668941850734281997130816271646007790⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1646 : oGrid.row evalE 1646 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1646_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1646_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1646_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1646_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1646_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1646_2000).1 (bothLoop_sound b_1646_2400).1))))))

theorem n_row_1646 : nGrid.row evalE 1646 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1646_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1646_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1646_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1646_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1646_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1646_2000).2 (bothLoop_sound b_1646_2400).2))))))

theorem b_1647_0 : bothSeg evalE (oGrid.idx 1647) (oGrid.dm 1647) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1647) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 61824364565979548801489425562292231697679453583366585750735490406447903518⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1647_400 : bothSeg evalE (oGrid.idx 1647) (oGrid.dm 1647) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1647) oGrid.kl oGrid.kr 400 400 ⟨false, 61824364565979548801489425562292231697679453583366585750735490406447903518⟩ ⟨false, 0⟩ ⟨false, 140443136626973928743971941415970614068890641051303604637841985853060934300⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1647_800 : bothSeg evalE (oGrid.idx 1647) (oGrid.dm 1647) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1647) oGrid.kl oGrid.kr 400 800 ⟨false, 140443136626973928743971941415970614068890641051303604637841985853060934300⟩ ⟨false, 0⟩ ⟨false, 251891166395270244316323567147128303364318330112035919498328285421746166016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1647_1200 : bothSeg evalE (oGrid.idx 1647) (oGrid.dm 1647) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1647) oGrid.kl oGrid.kr 400 1200 ⟨false, 251891166395270244316323567147128303364318330112035919498328285421746166016⟩ ⟨false, 0⟩ ⟨false, 405222193914606275962904227130249711035547583382295598883160515777715553174⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1647_1600 : bothSeg evalE (oGrid.idx 1647) (oGrid.dm 1647) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1647) oGrid.kl oGrid.kr 400 1600 ⟨false, 405222193914606275962904227130249711035547583382295598883160515777715553174⟩ ⟨false, 0⟩ ⟨false, 604095590465634328034691125864332093472374587835049366081871994213482668714⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1647_2000 : bothSeg evalE (oGrid.idx 1647) (oGrid.dm 1647) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1647) oGrid.kl oGrid.kr 400 2000 ⟨false, 604095590465634328034691125864332093472374587835049366081871994213482668714⟩ ⟨false, 0⟩ ⟨false, 847765060907157987288647431122100601511388713804073215033975248644698264080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1647_2400 : bothLoop evalE (oGrid.idx 1647) (oGrid.dm 1647) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1647) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 847765060907157987288647431122100601511388713804073215033975248644698264080⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1647 : oGrid.row evalE 1647 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1647_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1647_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1647_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1647_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1647_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1647_2000).1 (bothLoop_sound b_1647_2400).1))))))

theorem n_row_1647 : nGrid.row evalE 1647 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1647_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1647_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1647_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1647_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1647_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1647_2000).2 (bothLoop_sound b_1647_2400).2))))))

theorem b_1648_0 : bothSeg evalE (oGrid.idx 1648) (oGrid.dm 1648) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1648) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62070582184520771575311107815807619165344423693883556192100939407680928132⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1648_400 : bothSeg evalE (oGrid.idx 1648) (oGrid.dm 1648) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1648) oGrid.kl oGrid.kr 400 400 ⟨false, 62070582184520771575311107815807619165344423693883556192100939407680928132⟩ ⟨false, 0⟩ ⟨false, 141060590867568509322884677572047136033536812822575236777884676475141545372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1648_800 : bothSeg evalE (oGrid.idx 1648) (oGrid.dm 1648) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1648) oGrid.kl oGrid.kr 400 800 ⟨false, 141060590867568509322884677572047136033536812822575236777884676475141545372⟩ ⟨false, 0⟩ ⟨false, 252848364768388831546558585393380008432427093788784967512831009880952165818⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1648_1200 : bothSeg evalE (oGrid.idx 1648) (oGrid.dm 1648) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1648) oGrid.kl oGrid.kr 400 1200 ⟨false, 252848364768388831546558585393380008432427093788784967512831009880952165818⟩ ⟨false, 0⟩ ⟨false, 406482771751254263948516410169530912671623612097349616077218743693247180078⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1648_1600 : bothSeg evalE (oGrid.idx 1648) (oGrid.dm 1648) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1648) oGrid.kl oGrid.kr 400 1600 ⟨false, 406482771751254263948516410169530912671623612097349616077218743693247180078⟩ ⟨false, 0⟩ ⟨false, 605625695451952054994210959544065157596187738801799618893609104384495731664⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1648_2000 : bothSeg evalE (oGrid.idx 1648) (oGrid.dm 1648) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1648) oGrid.kl oGrid.kr 400 2000 ⟨false, 605625695451952054994210959544065157596187738801799618893609104384495731664⟩ ⟨false, 0⟩ ⟨false, 849536721186799985828173513944252690477538547604211075522217903866491781668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1648_2400 : bothLoop evalE (oGrid.idx 1648) (oGrid.dm 1648) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1648) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 849536721186799985828173513944252690477538547604211075522217903866491781668⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1648 : oGrid.row evalE 1648 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1648_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1648_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1648_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1648_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1648_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1648_2000).1 (bothLoop_sound b_1648_2400).1))))))

theorem n_row_1648 : nGrid.row evalE 1648 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1648_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1648_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1648_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1648_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1648_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1648_2000).2 (bothLoop_sound b_1648_2400).2))))))

theorem b_1649_0 : bothSeg evalE (oGrid.idx 1649) (oGrid.dm 1649) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1649) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62327145855269196866533511197903612428991903655129250579320043404899580024⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1649_400 : bothSeg evalE (oGrid.idx 1649) (oGrid.dm 1649) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1649) oGrid.kl oGrid.kr 400 400 ⟨false, 62327145855269196866533511197903612428991903655129250579320043404899580024⟩ ⟨false, 0⟩ ⟨false, 141688421772972541257146751235895554180841566009677140303204361254011535432⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1649_800 : bothSeg evalE (oGrid.idx 1649) (oGrid.dm 1649) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1649) oGrid.kl oGrid.kr 400 800 ⟨false, 141688421772972541257146751235895554180841566009677140303204361254011535432⟩ ⟨false, 0⟩ ⟨false, 253815876660439157205025502374605258617861562959287966355230611943416140520⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1649_1200 : bothSeg evalE (oGrid.idx 1649) (oGrid.dm 1649) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1649) oGrid.kl oGrid.kr 400 1200 ⟨false, 253815876660439157205025502374605258617861562959287966355230611943416140520⟩ ⟨false, 0⟩ ⟨false, 407753639265282429401867432943056893312581634963334298003234870690416351574⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1649_1600 : bothSeg evalE (oGrid.idx 1649) (oGrid.dm 1649) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1649) oGrid.kl oGrid.kr 400 1600 ⟨false, 407753639265282429401867432943056893312581634963334298003234870690416351574⟩ ⟨false, 0⟩ ⟨false, 607166095819514356133781772932226943464531816717186577848745209528619525958⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1649_2000 : bothSeg evalE (oGrid.idx 1649) (oGrid.dm 1649) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1649) oGrid.kl oGrid.kr 400 2000 ⟨false, 607166095819514356133781772932226943464531816717186577848745209528619525958⟩ ⟨false, 0⟩ ⟨false, 851318700287281928942143826740373229104722324042431557690184357129447763810⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1649_2400 : bothLoop evalE (oGrid.idx 1649) (oGrid.dm 1649) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1649) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 851318700287281928942143826740373229104722324042431557690184357129447763810⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1649 : oGrid.row evalE 1649 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1649_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1649_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1649_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1649_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1649_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1649_2000).1 (bothLoop_sound b_1649_2400).1))))))

theorem n_row_1649 : nGrid.row evalE 1649 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1649_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1649_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1649_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1649_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1649_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1649_2000).2 (bothLoop_sound b_1649_2400).2))))))

theorem b_1650_0 : bothSeg evalE (oGrid.idx 1650) (oGrid.dm 1650) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1650) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62593670907344450621467433990015859625120728895420316626163039536542119144⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1650_400 : bothSeg evalE (oGrid.idx 1650) (oGrid.dm 1650) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1650) oGrid.kl oGrid.kr 400 400 ⟨false, 62593670907344450621467433990015859625120728895420316626163039536542119144⟩ ⟨false, 0⟩ ⟨false, 142326199387813604772184970481273909061511922807455100188374783615872711640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1650_800 : bothSeg evalE (oGrid.idx 1650) (oGrid.dm 1650) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1650) oGrid.kl oGrid.kr 400 800 ⟨false, 142326199387813604772184970481273909061511922807455100188374783615872711640⟩ ⟨false, 0⟩ ⟨false, 254793272146574933747693351890357167839900317854287159748812212766874460806⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1650_1200 : bothSeg evalE (oGrid.idx 1650) (oGrid.dm 1650) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1650) oGrid.kl oGrid.kr 400 1200 ⟨false, 254793272146574933747693351890357167839900317854287159748812212766874460806⟩ ⟨false, 0⟩ ⟨false, 409034366513547432457990855664062718268943742498874765989890639478221411420⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1650_1600 : bothSeg evalE (oGrid.idx 1650) (oGrid.dm 1650) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1650) oGrid.kl oGrid.kr 400 1600 ⟨false, 409034366513547432457990855664062718268943742498874765989890639478221411420⟩ ⟨false, 0⟩ ⟨false, 608716361581515973177839363390650723070341269091253472450697472018751529910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1650_2000 : bothSeg evalE (oGrid.idx 1650) (oGrid.dm 1650) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1650) oGrid.kl oGrid.kr 400 2000 ⟨false, 608716361581515973177839363390650723070341269091253472450697472018751529910⟩ ⟨false, 0⟩ ⟨false, 853110568172523519442427782450131494384131730820586789438006340034108626372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1650_2400 : bothLoop evalE (oGrid.idx 1650) (oGrid.dm 1650) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1650) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 853110568172523519442427782450131494384131730820586789438006340034108626372⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1650 : oGrid.row evalE 1650 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1650_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1650_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1650_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1650_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1650_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1650_2000).1 (bothLoop_sound b_1650_2400).1))))))

theorem n_row_1650 : nGrid.row evalE 1650 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1650_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1650_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1650_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1650_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1650_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1650_2000).2 (bothLoop_sound b_1650_2400).2))))))

theorem b_1651_0 : bothSeg evalE (oGrid.idx 1651) (oGrid.dm 1651) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1651) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 62869763308597215087218717763098529873593282036868991782247148360409355232⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1651_400 : bothSeg evalE (oGrid.idx 1651) (oGrid.dm 1651) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1651) oGrid.kl oGrid.kr 400 400 ⟨false, 62869763308597215087218717763098529873593282036868991782247148360409355232⟩ ⟨false, 0⟩ ⟨false, 142973492466855513249021262555678012944404096251245804986777379772270755064⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1651_800 : bothSeg evalE (oGrid.idx 1651) (oGrid.dm 1651) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1651) oGrid.kl oGrid.kr 400 800 ⟨false, 142973492466855513249021262555678012944404096251245804986777379772270755064⟩ ⟨false, 0⟩ ⟨false, 255780120012094212708902428251493967549539929419404778889089332291933634766⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1651_1200 : bothSeg evalE (oGrid.idx 1651) (oGrid.dm 1651) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1651) oGrid.kl oGrid.kr 400 1200 ⟨false, 255780120012094212708902428251493967549539929419404778889089332291933634766⟩ ⟨false, 0⟩ ⟨false, 410324522263122599534377576258090320074928680276897697698205338999796199894⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1651_1600 : bothSeg evalE (oGrid.idx 1651) (oGrid.dm 1651) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1651) oGrid.kl oGrid.kr 400 1600 ⟨false, 410324522263122599534377576258090320074928680276897697698205338999796199894⟩ ⟨false, 0⟩ ⟨false, 610276061461453023214956782730194571822966511197252868363578142197742825658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1651_2000 : bothSeg evalE (oGrid.idx 1651) (oGrid.dm 1651) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1651) oGrid.kl oGrid.kr 400 2000 ⟨false, 610276061461453023214956782730194571822966511197252868363578142197742825658⟩ ⟨false, 0⟩ ⟨false, 854911893516813525828373697495923784774293079721810885015968836244521667160⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1651_2400 : bothLoop evalE (oGrid.idx 1651) (oGrid.dm 1651) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1651) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 854911893516813525828373697495923784774293079721810885015968836244521667160⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1651 : oGrid.row evalE 1651 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1651_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1651_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1651_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1651_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1651_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1651_2000).1 (bothLoop_sound b_1651_2400).1))))))

theorem n_row_1651 : nGrid.row evalE 1651 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1651_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1651_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1651_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1651_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1651_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1651_2000).2 (bothLoop_sound b_1651_2400).2))))))

theorem b_1652_0 : bothSeg evalE (oGrid.idx 1652) (oGrid.dm 1652) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1652) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63155017942145721641197243171271798197146423397429302762015964455819059316⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1652_400 : bothSeg evalE (oGrid.idx 1652) (oGrid.dm 1652) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1652) oGrid.kl oGrid.kr 400 400 ⟨false, 63155017942145721641197243171271798197146423397429302762015964455819059316⟩ ⟨false, 0⟩ ⟨false, 143629869090228364891399200545715170094704932581933403822801972259927041400⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1652_800 : bothSeg evalE (oGrid.idx 1652) (oGrid.dm 1652) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1652) oGrid.kl oGrid.kr 400 800 ⟨false, 143629869090228364891399200545715170094704932581933403822801972259927041400⟩ ⟨false, 0⟩ ⟨false, 256775988367669341322477253216530059265312212861389416325773643088403543008⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1652_1200 : bothSeg evalE (oGrid.idx 1652) (oGrid.dm 1652) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1652) oGrid.kl oGrid.kr 400 1200 ⟨false, 256775988367669341322477253216530059265312212861389416325773643088403543008⟩ ⟨false, 0⟩ ⟨false, 411623674606527707203183283346133603181648094875112019361660724649467684016⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1652_1600 : bothSeg evalE (oGrid.idx 1652) (oGrid.dm 1652) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1652) oGrid.kl oGrid.kr 400 1600 ⟨false, 411623674606527707203183283346133603181648094875112019361660724649467684016⟩ ⟨false, 0⟩ ⟨false, 611844763508352642715097225935226335575471126607175085111932028230575933986⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1652_2000 : bothSeg evalE (oGrid.idx 1652) (oGrid.dm 1652) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1652) oGrid.kl oGrid.kr 400 2000 ⟨false, 611844763508352642715097225935226335575471126607175085111932028230575933986⟩ ⟨false, 0⟩ ⟨false, 856722244320039351189409473860385248800136704501315177165047946499628468328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1652_2400 : bothLoop evalE (oGrid.idx 1652) (oGrid.dm 1652) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1652) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 856722244320039351189409473860385248800136704501315177165047946499628468328⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1652 : oGrid.row evalE 1652 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1652_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1652_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1652_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1652_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1652_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1652_2000).1 (bothLoop_sound b_1652_2400).1))))))

theorem n_row_1652 : nGrid.row evalE 1652 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1652_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1652_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1652_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1652_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1652_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1652_2000).2 (bothLoop_sound b_1652_2400).2))))))

theorem b_1653_0 : bothSeg evalE (oGrid.idx 1653) (oGrid.dm 1653) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1653) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63449019366363054759665292216375608388102810908425449559730286046955711544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1653_400 : bothSeg evalE (oGrid.idx 1653) (oGrid.dm 1653) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1653) oGrid.kl oGrid.kr 400 400 ⟨false, 63449019366363054759665292216375608388102810908425449559730286046955711544⟩ ⟨false, 0⟩ ⟨false, 144294896784629376566283143317400359711302149450305570570062390434162456982⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1653_800 : bothSeg evalE (oGrid.idx 1653) (oGrid.dm 1653) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1653) oGrid.kl oGrid.kr 400 800 ⟨false, 144294896784629376566283143317400359711302149450305570570062390434162456982⟩ ⟨false, 0⟩ ⟨false, 257780444770547701652243277465897188712319647988637057950443080918460687366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1653_1200 : bothSeg evalE (oGrid.idx 1653) (oGrid.dm 1653) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1653) oGrid.kl oGrid.kr 400 1200 ⟨false, 257780444770547701652243277465897188712319647988637057950443080918460687366⟩ ⟨false, 0⟩ ⟨false, 412931391082929548952082463717137340447065708327539286425149031237880150404⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1653_1600 : bothSeg evalE (oGrid.idx 1653) (oGrid.dm 1653) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1653) oGrid.kl oGrid.kr 400 1600 ⟨false, 412931391082929548952082463717137340447065708327539286425149031237880150404⟩ ⟨false, 0⟩ ⟨false, 613422035217973414637702110655462163488537038094007003852172565206210375262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1653_2000 : bothSeg evalE (oGrid.idx 1653) (oGrid.dm 1653) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1653) oGrid.kl oGrid.kr 400 2000 ⟨false, 613422035217973414637702110655462163488537038094007003852172565206210375262⟩ ⟨false, 0⟩ ⟨false, 858541188028887385239822346366402547921465107804760012421252683469016287168⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1653_2400 : bothLoop evalE (oGrid.idx 1653) (oGrid.dm 1653) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1653) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 858541188028887385239822346366402547921465107804760012421252683469016287168⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1653 : oGrid.row evalE 1653 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1653_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1653_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1653_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1653_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1653_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1653_2000).1 (bothLoop_sound b_1653_2400).1))))))

theorem n_row_1653 : nGrid.row evalE 1653 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1653_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1653_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1653_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1653_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1653_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1653_2000).2 (bothLoop_sound b_1653_2400).2))))))

theorem b_1654_0 : bothSeg evalE (oGrid.idx 1654) (oGrid.dm 1654) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1654) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 63751340996093762735388946767532015648344198727975918480580641567530337014⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1654_400 : bothSeg evalE (oGrid.idx 1654) (oGrid.dm 1654) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1654) oGrid.kl oGrid.kr 400 400 ⟨false, 63751340996093762735388946767532015648344198727975918480580641567530337014⟩ ⟨false, 0⟩ ⟨false, 144968143201069759232510015346539175923775680803606165740491620913741848820⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1654_800 : bothSeg evalE (oGrid.idx 1654) (oGrid.dm 1654) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1654) oGrid.kl oGrid.kr 400 800 ⟨false, 144968143201069759232510015346539175923775680803606165740491620913741848820⟩ ⟨false, 0⟩ ⟨false, 258793056902298491645679417048730445022839819972607466543869415272692677696⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1654_1200 : bothSeg evalE (oGrid.idx 1654) (oGrid.dm 1654) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1654) oGrid.kl oGrid.kr 400 1200 ⟨false, 258793056902298491645679417048730445022839819972607466543869415272692677696⟩ ⟨false, 0⟩ ⟨false, 414247239355888544246704343664266436910879527770882112935090886008911201796⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1654_1600 : bothSeg evalE (oGrid.idx 1654) (oGrid.dm 1654) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1654) oGrid.kl oGrid.kr 400 1600 ⟨false, 414247239355888544246704343664266436910879527770882112935090886008911201796⟩ ⟨false, 0⟩ ⟨false, 615007444210551838043354919044472614354549019735074751802319851513221218998⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1654_2000 : bothSeg evalE (oGrid.idx 1654) (oGrid.dm 1654) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1654) oGrid.kl oGrid.kr 400 2000 ⟨false, 615007444210551838043354919044472614354549019735074751802319851513221218998⟩ ⟨false, 0⟩ ⟨false, 860368292214589398898583044354884381890611951990173717012246012854438020470⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1654_2400 : bothLoop evalE (oGrid.idx 1654) (oGrid.dm 1654) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1654) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 860368292214589398898583044354884381890611951990173717012246012854438020470⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1654 : oGrid.row evalE 1654 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1654_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1654_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1654_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1654_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1654_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1654_2000).1 (bothLoop_sound b_1654_2400).1))))))

theorem n_row_1654 : nGrid.row evalE 1654 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1654_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1654_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1654_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1654_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1654_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1654_2000).2 (bothLoop_sound b_1654_2400).2))))))

theorem b_1655_0 : bothSeg evalE (oGrid.idx 1655) (oGrid.dm 1655) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1655) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 64061552693449365011116045452039042175944615772680994917010331367079994214⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1655_400 : bothSeg evalE (oGrid.idx 1655) (oGrid.dm 1655) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1655) oGrid.kl oGrid.kr 400 400 ⟨false, 64061552693449365011116045452039042175944615772680994917010331367079994214⟩ ⟨false, 0⟩ ⟨false, 145649177159515520057228778065528217902791020282846837498860178171939009176⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1655_800 : bothSeg evalE (oGrid.idx 1655) (oGrid.dm 1655) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1655) oGrid.kl oGrid.kr 400 800 ⟨false, 145649177159515520057228778065528217902791020282846837498860178171939009176⟩ ⟨false, 0⟩ ⟨false, 259813393613453433209296768063030760821838802639126682820840260195316254198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1655_1200 : bothSeg evalE (oGrid.idx 1655) (oGrid.dm 1655) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1655) oGrid.kl oGrid.kr 400 1200 ⟨false, 259813393613453433209296768063030760821838802639126682820840260195316254198⟩ ⟨false, 0⟩ ⟨false, 415570788257999274992445908531096205877352074437433455355247259821528790310⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1655_1600 : bothSeg evalE (oGrid.idx 1655) (oGrid.dm 1655) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1655) oGrid.kl oGrid.kr 400 1600 ⟨false, 415570788257999274992445908531096205877352074437433455355247259821528790310⟩ ⟨false, 0⟩ ⟨false, 616600559275442725306620905761761465381706605827174190944244915159617010980⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1655_2000 : bothSeg evalE (oGrid.idx 1655) (oGrid.dm 1655) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1655) oGrid.kl oGrid.kr 400 2000 ⟨false, 616600559275442725306620905761761465381706605827174190944244915159617010980⟩ ⟨false, 0⟩ ⟨false, 862203125617562866511938599531340392780078792560485971874352789974225670486⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_1655_2400 : bothLoop evalE (oGrid.idx 1655) (oGrid.dm 1655) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 1655) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 862203125617562866511938599531340392780078792560485971874352789974225670486⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem o_row_1655 : oGrid.row evalE 1655 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_1655_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_1655_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_1655_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_1655_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_1655_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_1655_2000).1 (bothLoop_sound b_1655_2400).1))))))

theorem n_row_1655 : nGrid.row evalE 1655 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_1655_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_1655_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_1655_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_1655_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_1655_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_1655_2000).2 (bothLoop_sound b_1655_2400).2))))))

theorem o_blk_1632 : allFrom (fun j => oGrid.row evalE j) 1632 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1632) o_row_1632 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1633) o_row_1633 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1634) o_row_1634 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1635) o_row_1635 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1636) o_row_1636 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1637) o_row_1637 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1638) o_row_1638 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1639) o_row_1639 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1640) o_row_1640 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1641) o_row_1641 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1642) o_row_1642 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1643) o_row_1643 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1644) o_row_1644 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1645) o_row_1645 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1646) o_row_1646 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1647) o_row_1647 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1648) o_row_1648 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1649) o_row_1649 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1650) o_row_1650 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1651) o_row_1651 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1652) o_row_1652 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1653) o_row_1653 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1654) o_row_1654 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 1655) o_row_1655 (allFrom_zero (fun j => oGrid.row evalE j) 1656)))))))))))))))))))))))))

theorem n_blk_1632 : allFrom (fun j => nGrid.row evalE j) 1632 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1632) n_row_1632 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1633) n_row_1633 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1634) n_row_1634 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1635) n_row_1635 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1636) n_row_1636 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1637) n_row_1637 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1638) n_row_1638 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1639) n_row_1639 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1640) n_row_1640 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1641) n_row_1641 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1642) n_row_1642 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1643) n_row_1643 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1644) n_row_1644 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1645) n_row_1645 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1646) n_row_1646 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1647) n_row_1647 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1648) n_row_1648 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1649) n_row_1649 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1650) n_row_1650 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1651) n_row_1651 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1652) n_row_1652 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1653) n_row_1653 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1654) n_row_1654 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 1655) n_row_1655 (allFrom_zero (fun j => nGrid.row evalE j) 1656)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
