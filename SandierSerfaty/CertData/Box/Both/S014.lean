/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Consts
public import SandierSerfaty.CertData.Box.Split

/-!
# The outer and negative-part rows (A8, A9), shard 14 (kernel)

Segments of at most `400` queries of a row of the common grid with literal checkpoints (`bothSeg`, each value computed once), the outer and negative rows, the blocks. Rows `336`–`359`.
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem b_336_0 : bothSeg evalE (oGrid.idx 336) (oGrid.dm 336) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 336) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1388332138751268653894100066241930850047156656980718160314133575154286498180⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_336_400 : bothSeg evalE (oGrid.idx 336) (oGrid.dm 336) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 336) oGrid.kl oGrid.kr 400 400 ⟨false, 1388332138751268653894100066241930850047156656980718160314133575154286498180⟩ ⟨false, 0⟩ ⟨false, 2229700932433438080481168300058005237087446120703284023302505703542794512198⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_336_800 : bothSeg evalE (oGrid.idx 336) (oGrid.dm 336) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 336) oGrid.kl oGrid.kr 400 800 ⟨false, 2229700932433438080481168300058005237087446120703284023302505703542794512198⟩ ⟨false, 0⟩ ⟨false, 2501244079120458416689226086257172635858681134625756890992966767301318613390⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_336_1200 : bothSeg evalE (oGrid.idx 336) (oGrid.dm 336) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 336) oGrid.kl oGrid.kr 400 1200 ⟨false, 2501244079120458416689226086257172635858681134625756890992966767301318613390⟩ ⟨false, 0⟩ ⟨false, 2482631998753961540081343254832220989474423337448986565830088617712273054062⟩ ⟨false, 33942861559550100832676002824295365491358773198166712813979342491844082590⟩ = true := by
  decide +kernel

theorem b_336_1600 : bothSeg evalE (oGrid.idx 336) (oGrid.dm 336) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 336) oGrid.kl oGrid.kr 400 1600 ⟨false, 2482631998753961540081343254832220989474423337448986565830088617712273054062⟩ ⟨false, 33942861559550100832676002824295365491358773198166712813979342491844082590⟩ ⟨false, 2326392082671640259150429227247390689882466100127180236143495177630082242234⟩ ⟨false, 190182777641871381763590030409125665083316010519973042500572782574034894418⟩ = true := by
  decide +kernel

theorem b_336_2000 : bothSeg evalE (oGrid.idx 336) (oGrid.dm 336) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 336) oGrid.kl oGrid.kr 400 2000 ⟨false, 2326392082671640259150429227247390689882466100127180236143495177630082242234⟩ ⟨false, 190182777641871381763590030409125665083316010519973042500572782574034894418⟩ ⟨false, 2323575718927936126465672125938614712530050221459243102771167292033967392698⟩ ⟨false, 199892434084122451500413680358056285602051149784662107449001252521895684234⟩ = true := by
  decide +kernel

theorem b_336_2400 : bothLoop evalE (oGrid.idx 336) (oGrid.dm 336) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 336) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2323575718927936126465672125938614712530050221459243102771167292033967392698⟩ ⟨false, 199892434084122451500413680358056285602051149784662107449001252521895684234⟩ = true := by
  decide +kernel

theorem o_row_336 : oGrid.row evalE 336 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_336_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_336_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_336_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_336_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_336_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_336_2000).1 (bothLoop_sound b_336_2400).1))))))

theorem n_row_336 : nGrid.row evalE 336 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_336_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_336_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_336_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_336_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_336_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_336_2000).2 (bothLoop_sound b_336_2400).2))))))

theorem b_337_0 : bothSeg evalE (oGrid.idx 337) (oGrid.dm 337) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 337) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1381986278592089573867193370186965688930416773567326488851267875031878711182⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_337_400 : bothSeg evalE (oGrid.idx 337) (oGrid.dm 337) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 337) oGrid.kl oGrid.kr 400 400 ⟨false, 1381986278592089573867193370186965688930416773567326488851267875031878711182⟩ ⟨false, 0⟩ ⟨false, 2219297847291286186524247709616772705906620584306591026617386600648112843110⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_337_800 : bothSeg evalE (oGrid.idx 337) (oGrid.dm 337) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 337) oGrid.kl oGrid.kr 400 800 ⟨false, 2219297847291286186524247709616772705906620584306591026617386600648112843110⟩ ⟨false, 0⟩ ⟨false, 2489158824980971905777604006941199950687266897951881499171647621908795521162⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_337_1200 : bothSeg evalE (oGrid.idx 337) (oGrid.dm 337) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 337) oGrid.kl oGrid.kr 400 1200 ⟨false, 2489158824980971905777604006941199950687266897951881499171647621908795521162⟩ ⟨false, 0⟩ ⟨false, 2470122281914231931485478531553245851089376107471805143431815383528769853936⟩ ⟨false, 34114647669842244735830420751525459015198360554066860682517891730204386910⟩ = true := by
  decide +kernel

theorem b_337_1600 : bothSeg evalE (oGrid.idx 337) (oGrid.dm 337) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 337) oGrid.kl oGrid.kr 400 1600 ⟨false, 2470122281914231931485478531553245851089376107471805143431815383528769853936⟩ ⟨false, 34114647669842244735830420751525459015198360554066860682517891730204386910⟩ ⟨false, 2314110470852293497880030457056948646296112231645623116648595144030616678100⟩ ⟨false, 190126458731780678341278495247822663808462236380248887465738131228357562746⟩ = true := by
  decide +kernel

theorem b_337_2000 : bothSeg evalE (oGrid.idx 337) (oGrid.dm 337) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 337) oGrid.kl oGrid.kr 400 2000 ⟨false, 2314110470852293497880030457056948646296112231645623116648595144030616678100⟩ ⟨false, 190126458731780678341278495247822663808462236380248887465738131228357562746⟩ ⟨false, 2311419129078485621081666359475719814467683201468829516976783249248914047400⟩ ⟨false, 199725212570010983949898849606003715085375196772919477033658738645839946762⟩ = true := by
  decide +kernel

theorem b_337_2400 : bothLoop evalE (oGrid.idx 337) (oGrid.dm 337) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 337) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2311419129078485621081666359475719814467683201468829516976783249248914047400⟩ ⟨false, 199725212570010983949898849606003715085375196772919477033658738645839946762⟩ = true := by
  decide +kernel

theorem o_row_337 : oGrid.row evalE 337 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_337_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_337_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_337_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_337_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_337_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_337_2000).1 (bothLoop_sound b_337_2400).1))))))

theorem n_row_337 : nGrid.row evalE 337 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_337_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_337_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_337_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_337_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_337_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_337_2000).2 (bothLoop_sound b_337_2400).2))))))

theorem b_338_0 : bothSeg evalE (oGrid.idx 338) (oGrid.dm 338) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 338) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1375661557359605446218948311264757820711751253657753266395073789108566074526⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_338_400 : bothSeg evalE (oGrid.idx 338) (oGrid.dm 338) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 338) oGrid.kl oGrid.kr 400 400 ⟨false, 1375661557359605446218948311264757820711751253657753266395073789108566074526⟩ ⟨false, 0⟩ ⟨false, 2208928862582808646821172727409645695044922745334494892878506174400768273090⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_338_800 : bothSeg evalE (oGrid.idx 338) (oGrid.dm 338) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 338) oGrid.kl oGrid.kr 400 800 ⟨false, 2208928862582808646821172727409645695044922745334494892878506174400768273090⟩ ⟨false, 0⟩ ⟨false, 2477113146750120062602752114174769684188856440595496306220545004065820842190⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_338_1200 : bothSeg evalE (oGrid.idx 338) (oGrid.dm 338) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 338) oGrid.kl oGrid.kr 400 1200 ⟨false, 2477113146750120062602752114174769684188856440595496306220545004065820842190⟩ ⟨false, 0⟩ ⟨false, 2457647006911803377792961456684921965023380705940952878045076826223407850430⟩ ⟨false, 34294549749441426385438309570419459088780332953534052191858344261639503020⟩ = true := by
  decide +kernel

theorem b_338_1600 : bothSeg evalE (oGrid.idx 338) (oGrid.dm 338) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 338) oGrid.kl oGrid.kr 400 1600 ⟨false, 2457647006911803377792961456684921965023380705940952878045076826223407850430⟩ ⟨false, 34294549749441426385438309570419459088780332953534052191858344261639503020⟩ ⟨false, 2301871727741495082770721650222506037038432826469130511885413009324700451702⟩ ⟨false, 190069828919749721407678116032835387073728212425356418351522161160346901748⟩ = true := by
  decide +kernel

theorem b_338_2000 : bothSeg evalE (oGrid.idx 338) (oGrid.dm 338) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 338) oGrid.kl oGrid.kr 400 2000 ⟨false, 2301871727741495082770721650222506037038432826469130511885413009324700451702⟩ ⟨false, 190069828919749721407678116032835387073728212425356418351522161160346901748⟩ ⟨false, 2299302815279623635594635985362720053144283146638391744753871872788569043900⟩ ⟨false, 199559861984936950148385732484707625516744789373727311687043942903033333282⟩ = true := by
  decide +kernel

theorem b_338_2400 : bothLoop evalE (oGrid.idx 338) (oGrid.dm 338) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 338) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2299302815279623635594635985362720053144283146638391744753871872788569043900⟩ ⟨false, 199559861984936950148385732484707625516744789373727311687043942903033333282⟩ = true := by
  decide +kernel

theorem o_row_338 : oGrid.row evalE 338 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_338_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_338_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_338_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_338_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_338_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_338_2000).1 (bothLoop_sound b_338_2400).1))))))

theorem n_row_338 : nGrid.row evalE 338 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_338_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_338_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_338_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_338_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_338_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_338_2000).2 (bothLoop_sound b_338_2400).2))))))

theorem b_339_0 : bothSeg evalE (oGrid.idx 339) (oGrid.dm 339) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 339) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1369357928207058722170133724256042128013478280997030005477086500673261114752⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_339_400 : bothSeg evalE (oGrid.idx 339) (oGrid.dm 339) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 339) oGrid.kl oGrid.kr 400 400 ⟨false, 1369357928207058722170133724256042128013478280997030005477086500673261114752⟩ ⟨false, 0⟩ ⟨false, 2198593894132793719141371313474561714664855807168047869298609870010136419698⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_339_800 : bothSeg evalE (oGrid.idx 339) (oGrid.dm 339) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 339) oGrid.kl oGrid.kr 400 800 ⟨false, 2198593894132793719141371313474561714664855807168047869298609870010136419698⟩ ⟨false, 0⟩ ⟨false, 2465106930687303476712320989414590266278898337826208293070603317437136000040⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_339_1200 : bothSeg evalE (oGrid.idx 339) (oGrid.dm 339) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 339) oGrid.kl oGrid.kr 400 1200 ⟨false, 2465106930687303476712320989414590266278898337826208293070603317437136000040⟩ ⟨false, 0⟩ ⟨false, 2445204791767181657324681679326937360871115550181216165815316463122069345384⟩ ⟨false, 34482689658524010433101608954738790853863648544853751586988935364422222512⟩ = true := by
  decide +kernel

theorem b_339_1600 : bothSeg evalE (oGrid.idx 339) (oGrid.dm 339) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 339) oGrid.kl oGrid.kr 400 1600 ⟨false, 2445204791767181657324681679326937360871115550181216165815316463122069345384⟩ ⟨false, 34482689658524010433101608954738790853863648544853751586988935364422222512⟩ ⟨false, 2289674460406341492426143200964750264765701889722947102235729298077529740432⟩ ⟨false, 190013021019364175331640087316925886959277309003122815166576100408961827464⟩ = true := by
  decide +kernel

theorem b_339_2000 : bothSeg evalE (oGrid.idx 339) (oGrid.dm 339) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 339) oGrid.kl oGrid.kr 400 2000 ⟨false, 2289674460406341492426143200964750264765701889722947102235729298077529740432⟩ ⟨false, 190013021019364175331640087316925886959277309003122815166576100408961827464⟩ ⟨false, 2287225428072752873565155722005569327659625844189554706843040520739125896906⟩ ⟨false, 199398128346219222886094482152447350755275585804031839028977247480228196742⟩ = true := by
  decide +kernel

theorem b_339_2400 : bothLoop evalE (oGrid.idx 339) (oGrid.dm 339) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 339) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2287225428072752873565155722005569327659625844189554706843040520739125896906⟩ ⟨false, 199398128346219222886094482152447350755275585804031839028977247480228196742⟩ = true := by
  decide +kernel

theorem o_row_339 : oGrid.row evalE 339 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_339_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_339_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_339_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_339_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_339_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_339_2000).1 (bothLoop_sound b_339_2400).1))))))

theorem n_row_339 : nGrid.row evalE 339 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_339_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_339_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_339_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_339_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_339_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_339_2000).2 (bothLoop_sound b_339_2400).2))))))

theorem b_340_0 : bothSeg evalE (oGrid.idx 340) (oGrid.dm 340) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 340) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1363075330118131246284020536594054233738201958023796415651033996048435523262⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_340_400 : bothSeg evalE (oGrid.idx 340) (oGrid.dm 340) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 340) oGrid.kl oGrid.kr 400 400 ⟨false, 1363075330118131246284020536594054233738201958023796415651033996048435523262⟩ ⟨false, 0⟩ ⟨false, 2188292863681535309972422399550055817961565051379159019587024159908629405658⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_340_800 : bothSeg evalE (oGrid.idx 340) (oGrid.dm 340) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 340) oGrid.kl oGrid.kr 400 800 ⟨false, 2188292863681535309972422399550055817961565051379159019587024159908629405658⟩ ⟨false, 0⟩ ⟨false, 2453140076327915520667051043860674168134561307413270463676520677096324643284⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_340_1200 : bothSeg evalE (oGrid.idx 340) (oGrid.dm 340) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 340) oGrid.kl oGrid.kr 400 1200 ⟨false, 2453140076327915520667051043860674168134561307413270463676520677096324643284⟩ ⟨false, 0⟩ ⟨false, 2432796436555447123232004068049839782486300291902229379419062875951228991328⟩ ⟨false, 34678548143392019891302026788549739463335287639815921611470527805405426332⟩ = true := by
  decide +kernel

theorem b_340_1600 : bothSeg evalE (oGrid.idx 340) (oGrid.dm 340) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 340) oGrid.kl oGrid.kr 400 1600 ⟨false, 2432796436555447123232004068049839782486300291902229379419062875951228991328⟩ ⟨false, 34678548143392019891302026788549739463335287639815921611470527805405426332⟩ ⟨false, 2277519471387235044378201906656746258042402960872621991943891506210447728746⟩ ⟨false, 189955513311604098745104188181643263907232618669423309086641897546186688914⟩ = true := by
  decide +kernel

theorem b_340_2000 : bothSeg evalE (oGrid.idx 340) (oGrid.dm 340) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 340) oGrid.kl oGrid.kr 400 2000 ⟨false, 2277519471387235044378201906656746258042402960872621991943891506210447728746⟩ ⟨false, 189955513311604098745104188181643263907232618669423309086641897546186688914⟩ ⟨false, 2275187771394980117330103494469763907508830609037856671983628731386477694966⟩ ⟨false, 199237591211740817843187158825078329274739980568994497722546311433200524130⟩ = true := by
  decide +kernel

theorem b_340_2400 : bothLoop evalE (oGrid.idx 340) (oGrid.dm 340) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 340) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2275187771394980117330103494469763907508830609037856671983628731386477694966⟩ ⟨false, 199237591211740817843187158825078329274739980568994497722546311433200524130⟩ = true := by
  decide +kernel

theorem o_row_340 : oGrid.row evalE 340 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_340_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_340_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_340_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_340_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_340_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_340_2000).1 (bothLoop_sound b_340_2400).1))))))

theorem n_row_340 : nGrid.row evalE 340 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_340_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_340_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_340_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_340_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_340_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_340_2000).2 (bothLoop_sound b_340_2400).2))))))

theorem b_341_0 : bothSeg evalE (oGrid.idx 341) (oGrid.dm 341) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 341) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1356813717753428595237907592896713084963384612855093478618567994627944823210⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_341_400 : bothSeg evalE (oGrid.idx 341) (oGrid.dm 341) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 341) oGrid.kl oGrid.kr 400 400 ⟨false, 1356813717753428595237907592896713084963384612855093478618567994627944823210⟩ ⟨false, 0⟩ ⟨false, 2178025697721352077065746436056872429255737821594938393696940003015875683640⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_341_800 : bothSeg evalE (oGrid.idx 341) (oGrid.dm 341) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 341) oGrid.kl oGrid.kr 400 800 ⟨false, 2178025697721352077065746436056872429255737821594938393696940003015875683640⟩ ⟨false, 0⟩ ⟨false, 2441212567965246318974297660534889543394256467362725402369389032835918853074⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_341_1200 : bothSeg evalE (oGrid.idx 341) (oGrid.dm 341) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 341) oGrid.kl oGrid.kr 400 1200 ⟨false, 2441212567965246318974297660534889543394256467362725402369389032835918853074⟩ ⟨false, 0⟩ ⟨false, 2420421879767426727453803933954686194610478968948797318245676851668177700104⟩ ⟨false, 34882138083670457371580189862084025143831000818638813951645886117798719308⟩ = true := by
  decide +kernel

theorem b_341_1600 : bothSeg evalE (oGrid.idx 341) (oGrid.dm 341) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 341) oGrid.kl oGrid.kr 400 1600 ⟨false, 2420421879767426727453803933954686194610478968948797318245676851668177700104⟩ ⟨false, 34882138083670457371580189862084025143831000818638813951645886117798719308⟩ ⟨false, 2265406736309596880639953640690390106912838595648459572425978740654221902330⟩ ⟨false, 189897281541500304185430483126380112841471374118976559771343997131754517082⟩ = true := by
  decide +kernel

theorem b_341_2000 : bothSeg evalE (oGrid.idx 341) (oGrid.dm 341) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 341) oGrid.kl oGrid.kr 400 2000 ⟨false, 2265406736309596880639953640690390106912838595648459572425978740654221902330⟩ ⟨false, 189897281541500304185430483126380112841471374118976559771343997131754517082⟩ ⟨false, 2263189822360374875137734242891340958392763373327542811816726715507624721420⟩ ⟨false, 199078807565394909974111778353580986841830572422124206841250638152378645814⟩ = true := by
  decide +kernel

theorem b_341_2400 : bothLoop evalE (oGrid.idx 341) (oGrid.dm 341) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 341) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2263189822360374875137734242891340958392763373327542811816726715507624721420⟩ ⟨false, 199078807565394909974111778353580986841830572422124206841250638152378645814⟩ = true := by
  decide +kernel

theorem o_row_341 : oGrid.row evalE 341 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_341_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_341_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_341_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_341_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_341_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_341_2000).1 (bothLoop_sound b_341_2400).1))))))

theorem n_row_341 : nGrid.row evalE 341 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_341_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_341_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_341_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_341_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_341_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_341_2000).2 (bothLoop_sound b_341_2400).2))))))

theorem b_342_0 : bothSeg evalE (oGrid.idx 342) (oGrid.dm 342) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 342) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1350573021244105014789888819477675373102778015570354651437196205570322069414⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_342_400 : bothSeg evalE (oGrid.idx 342) (oGrid.dm 342) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 342) oGrid.kl oGrid.kr 400 400 ⟨false, 1350573021244105014789888819477675373102778015570354651437196205570322069414⟩ ⟨false, 0⟩ ⟨false, 2167792297933364803289696473485779931674733515831901778753741775233254879394⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_342_800 : bothSeg evalE (oGrid.idx 342) (oGrid.dm 342) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 342) oGrid.kl oGrid.kr 400 800 ⟨false, 2167792297933364803289696473485779931674733515831901778753741775233254879394⟩ ⟨false, 0⟩ ⟨false, 2429324251848865686087988407786098861515195520528454148982135362901255054094⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_342_1200 : bothSeg evalE (oGrid.idx 342) (oGrid.dm 342) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 342) oGrid.kl oGrid.kr 400 1200 ⟨false, 2429324251848865686087988407786098861515195520528454148982135362901255054094⟩ ⟨false, 0⟩ ⟨false, 2408080991433965969423864509357214643045512702413201626066937108850628527924⟩ ⟨false, 35093437256269060612111920067147156616655373840656794612621162875537575402⟩ = true := by
  decide +kernel

theorem b_342_1600 : bothSeg evalE (oGrid.idx 342) (oGrid.dm 342) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 342) oGrid.kl oGrid.kr 400 1600 ⟨false, 2408080991433965969423864509357214643045512702413201626066937108850628527924⟩ ⟨false, 35093437256269060612111920067147156616655373840656794612621162875537575402⟩ ⟨false, 2253336096597799289335597227586688508101160022324934542969509730607765181638⟩ ⟨false, 189838332092435740700379201837673291561008053928923877710048541118400921688⟩ = true := by
  decide +kernel

theorem b_342_2000 : bothSeg evalE (oGrid.idx 342) (oGrid.dm 342) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 342) oGrid.kl oGrid.kr 400 2000 ⟨false, 2253336096597799289335597227586688508101160022324934542969509730607765181638⟩ ⟨false, 189838332092435740700379201837673291561008053928923877710048541118400921688⟩ ⟨false, 2251231404440245255529430024410549055681204778294618439990546264651052262470⟩ ⟨false, 198922301205181751196359077232790184960028343259711554861470953059735384078⟩ = true := by
  decide +kernel

theorem b_342_2400 : bothLoop evalE (oGrid.idx 342) (oGrid.dm 342) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 342) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2251231404440245255529430024410549055681204778294618439990546264651052262470⟩ ⟨false, 198922301205181751196359077232790184960028343259711554861470953059735384078⟩ = true := by
  decide +kernel

theorem o_row_342 : oGrid.row evalE 342 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_342_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_342_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_342_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_342_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_342_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_342_2000).1 (bothLoop_sound b_342_2400).1))))))

theorem n_row_342 : nGrid.row evalE 342 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_342_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_342_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_342_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_342_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_342_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_342_2000).2 (bothLoop_sound b_342_2400).2))))))

theorem b_343_0 : bothSeg evalE (oGrid.idx 343) (oGrid.dm 343) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 343) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1344353195625195131026359464933551111669171718313754131995373579737974474042⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_343_400 : bothSeg evalE (oGrid.idx 343) (oGrid.dm 343) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 343) oGrid.kl oGrid.kr 400 400 ⟨false, 1344353195625195131026359464933551111669171718313754131995373579737974474042⟩ ⟨false, 0⟩ ⟨false, 2157592589069134778645006175155093332098905563504051328848637373230786594804⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_343_800 : bothSeg evalE (oGrid.idx 343) (oGrid.dm 343) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 343) oGrid.kl oGrid.kr 400 800 ⟨false, 2157592589069134778645006175155093332098905563504051328848637373230786594804⟩ ⟨false, 0⟩ ⟨false, 2417475019593110048977012118342804150224953474011726732769549251115998688266⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_343_1200 : bothSeg evalE (oGrid.idx 343) (oGrid.dm 343) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 343) oGrid.kl oGrid.kr 400 1200 ⟨false, 2417475019593110048977012118342804150224953474011726732769549251115998688266⟩ ⟨false, 0⟩ ⟨false, 2395773747250108089277964914098549912953296580686047364846859525791382371042⟩ ⟨false, 35312894430115980660158351637962555476015184352068360950237654391113040386⟩ = true := by
  decide +kernel

theorem b_343_1600 : bothSeg evalE (oGrid.idx 343) (oGrid.dm 343) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 343) oGrid.kl oGrid.kr 400 1600 ⟨false, 2395773747250108089277964914098549912953296580686047364846859525791382371042⟩ ⟨false, 35312894430115980660158351637962555476015184352068360950237654391113040386⟩ ⟨false, 2241307514797676033927561626517599597141687717421200242272012603029741441212⟩ ⟨false, 189779126882548036010561639218912871287624047616915483525084577152753970216⟩ = true := by
  decide +kernel

theorem b_343_2000 : bothSeg evalE (oGrid.idx 343) (oGrid.dm 343) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 343) oGrid.kl oGrid.kr 400 2000 ⟨false, 2241307514797676033927561626517599597141687717421200242272012603029741441212⟩ ⟨false, 189779126882548036010561639218912871287624047616915483525084577152753970216⟩ ⟨false, 2239312498922126620057740367770822068644804737245006821347710064550401813048⟩ ⟨false, 198767450808179378587502816849958157765558973571618675510877550090237522816⟩ = true := by
  decide +kernel

theorem b_343_2400 : bothLoop evalE (oGrid.idx 343) (oGrid.dm 343) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 343) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2239312498922126620057740367770822068644804737245006821347710064550401813048⟩ ⟨false, 198767450808179378587502816849958157765558973571618675510877550090237522816⟩ = true := by
  decide +kernel

theorem o_row_343 : oGrid.row evalE 343 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_343_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_343_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_343_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_343_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_343_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_343_2000).1 (bothLoop_sound b_343_2400).1))))))

theorem n_row_343 : nGrid.row evalE 343 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_343_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_343_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_343_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_343_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_343_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_343_2000).2 (bothLoop_sound b_343_2400).2))))))

theorem b_344_0 : bothSeg evalE (oGrid.idx 344) (oGrid.dm 344) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 344) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1338154187386331394852115721397552362464555661257198391026153275801200317220⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_344_400 : bothSeg evalE (oGrid.idx 344) (oGrid.dm 344) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 344) oGrid.kl oGrid.kr 400 400 ⟨false, 1338154187386331394852115721397552362464555661257198391026153275801200317220⟩ ⟨false, 0⟩ ⟨false, 2147426494372836034498969874782161603902679056041074283498406758859377336656⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_344_800 : bothSeg evalE (oGrid.idx 344) (oGrid.dm 344) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 344) oGrid.kl oGrid.kr 400 800 ⟨false, 2147426494372836034498969874782161603902679056041074283498406758859377336656⟩ ⟨false, 0⟩ ⟨false, 2405664841740212975838471305838919336092694587250847220889014606806185937154⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_344_1200 : bothSeg evalE (oGrid.idx 344) (oGrid.dm 344) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 344) oGrid.kl oGrid.kr 400 1200 ⟨false, 2405664841740212975838471305838919336092694587250847220889014606806185937154⟩ ⟨false, 0⟩ ⟨false, 2383499976286729389468651708901440359966404820383677450492989477824037158394⟩ ⟨false, 35540138053456091641507535547307614914278127947487976085801022560054999708⟩ = true := by
  decide +kernel

theorem b_344_1600 : bothSeg evalE (oGrid.idx 344) (oGrid.dm 344) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 344) oGrid.kl oGrid.kr 400 1600 ⟨false, 2383499976286729389468651708901440359966404820383677450492989477824037158394⟩ ⟨false, 35540138053456091641507535547307614914278127947487976085801022560054999708⟩ ⟨false, 2229320868029052225851453948875606841682027447964152918927015525018139157256⟩ ⟨false, 189719246311133255258705295573141133198655500367012507651774975365953000846⟩ = true := by
  decide +kernel

theorem b_344_2000 : bothSeg evalE (oGrid.idx 344) (oGrid.dm 344) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 344) oGrid.kl oGrid.kr 400 2000 ⟨false, 2229320868029052225851453948875606841682027447964152918927015525018139157256⟩ ⟨false, 189719246311133255258705295573141133198655500367012507651774975365953000846⟩ ⟨false, 2227433001174917217561063371098336385683823715796908210503257738331096877882⟩ ⟨false, 198615139882341013498391041426567292400379693200668285656449466653830625620⟩ = true := by
  decide +kernel

theorem b_344_2400 : bothLoop evalE (oGrid.idx 344) (oGrid.dm 344) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 344) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2227433001174917217561063371098336385683823715796908210503257738331096877882⟩ ⟨false, 198615139882341013498391041426567292400379693200668285656449466653830625620⟩ = true := by
  decide +kernel

theorem o_row_344 : oGrid.row evalE 344 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_344_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_344_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_344_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_344_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_344_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_344_2000).1 (bothLoop_sound b_344_2400).1))))))

theorem n_row_344 : nGrid.row evalE 344 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_344_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_344_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_344_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_344_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_344_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_344_2000).2 (bothLoop_sound b_344_2400).2))))))

theorem b_345_0 : bothSeg evalE (oGrid.idx 345) (oGrid.dm 345) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 345) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1331975937551779578201487009422269286622395682519087549772946075634514138544⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_345_400 : bothSeg evalE (oGrid.idx 345) (oGrid.dm 345) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 345) oGrid.kl oGrid.kr 400 400 ⟨false, 1331975937551779578201487009422269286622395682519087549772946075634514138544⟩ ⟨false, 0⟩ ⟨false, 2137293932421747919800198548942655399465261959577847252990223935552943493604⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_345_800 : bothSeg evalE (oGrid.idx 345) (oGrid.dm 345) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 345) oGrid.kl oGrid.kr 400 800 ⟨false, 2137293932421747919800198548942655399465261959577847252990223935552943493604⟩ ⟨false, 0⟩ ⟨false, 2393893633793412571695104441955798749123734005273334734704116386049989098018⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_345_1200 : bothSeg evalE (oGrid.idx 345) (oGrid.dm 345) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 345) oGrid.kl oGrid.kr 400 1200 ⟨false, 2393893633793412571695104441955798749123734005273334734704116386049989098018⟩ ⟨false, 0⟩ ⟨false, 2371259757375508295061981817363606820827000839703638943962643871777229712744⟩ ⟨false, 35774993103339335247850179460125706128635155701311743585575514222617715710⟩ = true := by
  decide +kernel

theorem b_345_1600 : bothSeg evalE (oGrid.idx 345) (oGrid.dm 345) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 345) oGrid.kl oGrid.kr 400 1600 ⟨false, 2371259757375508295061981817363606820827000839703638943962643871777229712744⟩ ⟨false, 35774993103339335247850179460125706128635155701311743585575514222617715710⟩ ⟨false, 2217376153559506356530350720017826696338198333617598886303885164857305586356⟩ ⟨false, 189658596919341273779481276805905830617437661787351801244334221142541842098⟩ = true := by
  decide +kernel

theorem b_345_2000 : bothSeg evalE (oGrid.idx 345) (oGrid.dm 345) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 345) oGrid.kl oGrid.kr 400 2000 ⟨false, 2217376153559506356530350720017826696338198333617598886303885164857305586356⟩ ⟨false, 189658596919341273779481276805905830617437661787351801244334221142541842098⟩ ⟨false, 2215592905967930834917122270147970796870554681786768400967158428016419467938⟩ ⟨false, 198464738524719431328174727227926040268089417278033347565287326282419498900⟩ = true := by
  decide +kernel

theorem b_345_2400 : bothLoop evalE (oGrid.idx 345) (oGrid.dm 345) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 345) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2215592905967930834917122270147970796870554681786768400967158428016419467938⟩ ⟨false, 198464738524719431328174727227926040268089417278033347565287326282419498900⟩ = true := by
  decide +kernel

theorem o_row_345 : oGrid.row evalE 345 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_345_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_345_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_345_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_345_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_345_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_345_2000).1 (bothLoop_sound b_345_2400).1))))))

theorem n_row_345 : nGrid.row evalE 345 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_345_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_345_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_345_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_345_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_345_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_345_2000).2 (bothLoop_sound b_345_2400).2))))))

theorem b_346_0 : bothSeg evalE (oGrid.idx 346) (oGrid.dm 346) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 346) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1325818398650530970000407251635505232836541609737932894607011940184309017780⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_346_400 : bothSeg evalE (oGrid.idx 346) (oGrid.dm 346) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 346) oGrid.kl oGrid.kr 400 400 ⟨false, 1325818398650530970000407251635505232836541609737932894607011940184309017780⟩ ⟨false, 0⟩ ⟨false, 2127194823321965507063763389552999201002078287974797057152645264735030093814⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_346_800 : bothSeg evalE (oGrid.idx 346) (oGrid.dm 346) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 346) oGrid.kl oGrid.kr 400 800 ⟨false, 2127194823321965507063763389552999201002078287974797057152645264735030093814⟩ ⟨false, 0⟩ ⟨false, 2382161207564703181489342358643357702950330813060922207965002692517735125116⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_346_1200 : bothSeg evalE (oGrid.idx 346) (oGrid.dm 346) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 346) oGrid.kl oGrid.kr 400 1200 ⟨false, 2382161207564703181489342358643357702950330813060922207965002692517735125116⟩ ⟨false, 0⟩ ⟨false, 2359053062460869537148864422880746197675698940381431598274272511716498748444⟩ ⟨false, 36017184270650570908864306914676562152281525568305735810804187122941465714⟩ = true := by
  decide +kernel

theorem b_346_1600 : bothSeg evalE (oGrid.idx 346) (oGrid.dm 346) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 346) oGrid.kl oGrid.kr 400 1600 ⟨false, 2359053062460869537148864422880746197675698940381431598274272511716498748444⟩ ⟨false, 36017184270650570908864306914676562152281525568305735810804187122941465714⟩ ⟨false, 2205473339478535025689878197480835906739902535767382867928294690821416159066⟩ ⟨false, 189596907252985082367850532314586853088077930182354466156782008018024055092⟩ = true := by
  decide +kernel

theorem b_346_2000 : bothSeg evalE (oGrid.idx 346) (oGrid.dm 346) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 346) oGrid.kl oGrid.kr 400 2000 ⟨false, 2205473339478535025689878197480835906739902535767382867928294690821416159066⟩ ⟨false, 189596907252985082367850532314586853088077930182354466156782008018024055092⟩ ⟨false, 2203792193657638366507102838615824934690002635028681036601701957747386149624⟩ ⟨false, 198315042089170382664803304116006608693193461144442938377496573429627698788⟩ = true := by
  decide +kernel

theorem b_346_2400 : bothLoop evalE (oGrid.idx 346) (oGrid.dm 346) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 346) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2203792193657638366507102838615824934690002635028681036601701957747386149624⟩ ⟨false, 198315042089170382664803304116006608693193461144442938377496573429627698788⟩ = true := by
  decide +kernel

theorem o_row_346 : oGrid.row evalE 346 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_346_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_346_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_346_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_346_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_346_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_346_2000).1 (bothLoop_sound b_346_2400).1))))))

theorem n_row_346 : nGrid.row evalE 346 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_346_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_346_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_346_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_346_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_346_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_346_2000).2 (bothLoop_sound b_346_2400).2))))))

theorem b_347_0 : bothSeg evalE (oGrid.idx 347) (oGrid.dm 347) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 347) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1319681509979825247364407296191010569174895323803114935007648552971430967452⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_347_400 : bothSeg evalE (oGrid.idx 347) (oGrid.dm 347) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 347) oGrid.kl oGrid.kr 400 400 ⟨false, 1319681509979825247364407296191010569174895323803114935007648552971430967452⟩ ⟨false, 0⟩ ⟨false, 2117129085891600516419963321777111372857498518985388589877948181770733784762⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_347_800 : bothSeg evalE (oGrid.idx 347) (oGrid.dm 347) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 347) oGrid.kl oGrid.kr 400 800 ⟨false, 2117129085891600516419963321777111372857498518985388589877948181770733784762⟩ ⟨false, 0⟩ ⟨false, 2370467593343130734924127555874986672072097962374646242690996794052591560610⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_347_1200 : bothSeg evalE (oGrid.idx 347) (oGrid.dm 347) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 347) oGrid.kl oGrid.kr 400 1200 ⟨false, 2370467593343130734924127555874986672072097962374646242690996794052591560610⟩ ⟨false, 0⟩ ⟨false, 2346878963779740474948951975658527828942916801144359436575766934453070172882⟩ ⟨false, 36267906598834133252036846173872223914163649868486569207888376810450363862⟩ = true := by
  decide +kernel

theorem b_347_1600 : bothSeg evalE (oGrid.idx 347) (oGrid.dm 347) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 347) oGrid.kl oGrid.kr 400 1600 ⟨false, 2346878963779740474948951975658527828942916801144359436575766934453070172882⟩ ⟨false, 36267906598834133252036846173872223914163649868486569207888376810450363862⟩ ⟨false, 2193611464054739764691617035486124488995226613727986767236266941274170374878⟩ ⟨false, 189535406323834843509371786346275563861853837284859238547388369989350161866⟩ = true := by
  decide +kernel

theorem b_347_2000 : bothSeg evalE (oGrid.idx 347) (oGrid.dm 347) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 347) oGrid.kl oGrid.kr 400 2000 ⟨false, 2193611464054739764691617035486124488995226613727986767236266941274170374878⟩ ⟨false, 189535406323834843509371786346275563861853837284859238547388369989350161866⟩ ⟨false, 2192029920473599746346064947514184030085257117205189024118162904544776966114⟩ ⟨false, 198168565541826262490174566565784814378542608689843510176688496472760764386⟩ = true := by
  decide +kernel

theorem b_347_2400 : bothLoop evalE (oGrid.idx 347) (oGrid.dm 347) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 347) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2192029920473599746346064947514184030085257117205189024118162904544776966114⟩ ⟨false, 198168565541826262490174566565784814378542608689843510176688496472760764386⟩ = true := by
  decide +kernel

theorem o_row_347 : oGrid.row evalE 347 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_347_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_347_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_347_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_347_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_347_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_347_2000).1 (bothLoop_sound b_347_2400).1))))))

theorem n_row_347 : nGrid.row evalE 347 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_347_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_347_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_347_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_347_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_347_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_347_2000).2 (bothLoop_sound b_347_2400).2))))))

theorem b_348_0 : bothSeg evalE (oGrid.idx 348) (oGrid.dm 348) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 348) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1313565214932357663384963257875616722511061044300353758332563491381256179840⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_348_400 : bothSeg evalE (oGrid.idx 348) (oGrid.dm 348) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 348) oGrid.kl oGrid.kr 400 400 ⟨false, 1313565214932357663384963257875616722511061044300353758332563491381256179840⟩ ⟨false, 0⟩ ⟨false, 2107096632279345063958927867770086970511448906303138961558483668412451062228⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_348_800 : bothSeg evalE (oGrid.idx 348) (oGrid.dm 348) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 348) oGrid.kl oGrid.kr 400 800 ⟨false, 2107096632279345063958927867770086970511448906303138961558483668412451062228⟩ ⟨false, 0⟩ ⟨false, 2358812685404514232337771850903105039299300879137693350714102997030009930688⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_348_1200 : bothSeg evalE (oGrid.idx 348) (oGrid.dm 348) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 348) oGrid.kl oGrid.kr 400 1200 ⟨false, 2358812685404514232337771850903105039299300879137693350714102997030009930688⟩ ⟨false, 0⟩ ⟨false, 2334738111986076669488959810731649474606078373918337945057001505981639178412⟩ ⟨false, 36526798759700797476771948497925853378842000425174245804437477688708461880⟩ = true := by
  decide +kernel

theorem b_348_1600 : bothSeg evalE (oGrid.idx 348) (oGrid.dm 348) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 348) oGrid.kl oGrid.kr 400 1600 ⟨false, 2334738111986076669488959810731649474606078373918337945057001505981639178412⟩ ⟨false, 36526798759700797476771948497925853378842000425174245804437477688708461880⟩ ⟨false, 2181791141501397654493422049159726646775346616138163574695389287173907817600⟩ ⟨false, 189473769244379812472309710069848681209573758205348616166049696496439822692⟩ = true := by
  decide +kernel

theorem b_348_2000 : bothSeg evalE (oGrid.idx 348) (oGrid.dm 348) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 348) oGrid.kl oGrid.kr 400 2000 ⟨false, 2181791141501397654493422049159726646775346616138163574695389287173907817600⟩ ⟨false, 189473769244379812472309710069848681209573758205348616166049696496439822692⟩ ⟨false, 2180306691444251418945002782914728137869252790039777821677523135285097857544⟩ ⟨false, 198024649360062502228956424912168852391500431922963207369714419437064391636⟩ = true := by
  decide +kernel

theorem b_348_2400 : bothLoop evalE (oGrid.idx 348) (oGrid.dm 348) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 348) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2180306691444251418945002782914728137869252790039777821677523135285097857544⟩ ⟨false, 198024649360062502228956424912168852391500431922963207369714419437064391636⟩ = true := by
  decide +kernel

theorem o_row_348 : oGrid.row evalE 348 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_348_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_348_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_348_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_348_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_348_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_348_2000).1 (bothLoop_sound b_348_2400).1))))))

theorem n_row_348 : nGrid.row evalE 348 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_348_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_348_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_348_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_348_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_348_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_348_2000).2 (bothLoop_sound b_348_2400).2))))))

theorem b_349_0 : bothSeg evalE (oGrid.idx 349) (oGrid.dm 349) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 349) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1307469473139499459452958639966934194654212204906188246758183345341368015122⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_349_400 : bothSeg evalE (oGrid.idx 349) (oGrid.dm 349) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 349) oGrid.kl oGrid.kr 400 400 ⟨false, 1307469473139499459452958639966934194654212204906188246758183345341368015122⟩ ⟨false, 0⟩ ⟨false, 2097097394561353858596954881175388237484786085117850409086608160464259208050⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_349_800 : bothSeg evalE (oGrid.idx 349) (oGrid.dm 349) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 349) oGrid.kl oGrid.kr 400 800 ⟨false, 2097097394561353858596954881175388237484786085117850409086608160464259208050⟩ ⟨false, 0⟩ ⟨false, 2347196298007548477340793586793863219995915058139367808699592411021039120836⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_349_1200 : bothSeg evalE (oGrid.idx 349) (oGrid.dm 349) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 349) oGrid.kl oGrid.kr 400 1200 ⟨false, 2347196298007548477340793586793863219995915058139367808699592411021039120836⟩ ⟨false, 0⟩ ⟨false, 2322630425312547249025691469050746762498873572847434394423995584697056602732⟩ ⟨false, 36793313781647492790339176725334806045036750630403574521431125381290626650⟩ = true := by
  decide +kernel

theorem b_349_1600 : bothSeg evalE (oGrid.idx 349) (oGrid.dm 349) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 349) oGrid.kl oGrid.kr 400 1600 ⟨false, 2322630425312547249025691469050746762498873572847434394423995584697056602732⟩ ⟨false, 36793313781647492790339176725334806045036750630403574521431125381290626650⟩ ⟨false, 2170012240119486241154969172487065004614140944981272292221972402413090878842⟩ ⟨false, 189411498974708500661061473289016563929769378496565676723454307665256350540⟩ = true := by
  decide +kernel

theorem b_349_2000 : bothSeg evalE (oGrid.idx 349) (oGrid.dm 349) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 349) oGrid.kl oGrid.kr 400 2000 ⟨false, 2170012240119486241154969172487065004614140944981272292221972402413090878842⟩ ⟨false, 189411498974708500661061473289016563929769378496565676723454307665256350540⟩ ⟨false, 2168622417488209329835103015218080747900904092880017129415212543578008685142⟩ ⟨false, 197882068624276947183444222840212120651905742486288353360037621157127350278⟩ = true := by
  decide +kernel

theorem b_349_2400 : bothLoop evalE (oGrid.idx 349) (oGrid.dm 349) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 349) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2168622417488209329835103015218080747900904092880017129415212543578008685142⟩ ⟨false, 197882068624276947183444222840212120651905742486288353360037621157127350278⟩ = true := by
  decide +kernel

theorem o_row_349 : oGrid.row evalE 349 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_349_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_349_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_349_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_349_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_349_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_349_2000).1 (bothLoop_sound b_349_2400).1))))))

theorem n_row_349 : nGrid.row evalE 349 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_349_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_349_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_349_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_349_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_349_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_349_2000).2 (bothLoop_sound b_349_2400).2))))))

theorem b_350_0 : bothSeg evalE (oGrid.idx 350) (oGrid.dm 350) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 350) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1301394216408807796528872161899890400978525028045410865010696127082016450678⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_350_400 : bothSeg evalE (oGrid.idx 350) (oGrid.dm 350) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 350) oGrid.kl oGrid.kr 400 400 ⟨false, 1301394216408807796528872161899890400978525028045410865010696127082016450678⟩ ⟨false, 0⟩ ⟨false, 2087131277771054812707995433300466368232181221742138656364300611258234934386⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_350_800 : bothSeg evalE (oGrid.idx 350) (oGrid.dm 350) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 350) oGrid.kl oGrid.kr 400 800 ⟨false, 2087131277771054812707995433300466368232181221742138656364300611258234934386⟩ ⟨false, 0⟩ ⟨false, 2335618443421447845549941000805037518572619158031544588966964881246423015728⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_350_1200 : bothSeg evalE (oGrid.idx 350) (oGrid.dm 350) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 350) oGrid.kl oGrid.kr 400 1200 ⟨false, 2335618443421447845549941000805037518572619158031544588966964881246423015728⟩ ⟨false, 0⟩ ⟨false, 2310555928597325178614429311741810601721698025851089097798799964189274503638⟩ ⟨false, 37067308335834098558587943222074807023474574296570077453633616498326287490⟩ = true := by
  decide +kernel

theorem b_350_1600 : bothSeg evalE (oGrid.idx 350) (oGrid.dm 350) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 350) oGrid.kl oGrid.kr 400 1600 ⟨false, 2310555928597325178614429311741810601721698025851089097798799964189274503638⟩ ⟨false, 37067308335834098558587943222074807023474574296570077453633616498326287490⟩ ⟨false, 2158274780404749146847151845891847092063331236671987819342417218639493183560⟩ ⟨false, 189348456528410130325865409072038316681841363475671355910016362048107607568⟩ = true := by
  decide +kernel

theorem b_350_2000 : bothSeg evalE (oGrid.idx 350) (oGrid.dm 350) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 350) oGrid.kl oGrid.kr 400 2000 ⟨false, 2158274780404749146847151845891847092063331236671987819342417218639493183560⟩ ⟨false, 189348456528410130325865409072038316681841363475671355910016362048107607568⟩ ⟨false, 2156977125024424865709838830635181563497365664033231359670620157227239749252⟩ ⟨false, 197741961564228926220607782410242722500357609505190794292840824424790810248⟩ = true := by
  decide +kernel

theorem b_350_2400 : bothLoop evalE (oGrid.idx 350) (oGrid.dm 350) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 350) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2156977125024424865709838830635181563497365664033231359670620157227239749252⟩ ⟨false, 197741961564228926220607782410242722500357609505190794292840824424790810248⟩ = true := by
  decide +kernel

theorem o_row_350 : oGrid.row evalE 350 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_350_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_350_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_350_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_350_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_350_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_350_2000).1 (bothLoop_sound b_350_2400).1))))))

theorem n_row_350 : nGrid.row evalE 350 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_350_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_350_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_350_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_350_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_350_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_350_2000).2 (bothLoop_sound b_350_2400).2))))))

theorem b_351_0 : bothSeg evalE (oGrid.idx 351) (oGrid.dm 351) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 351) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1295339400786147835889278873987350406088330403935358047709550443248424563348⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_351_400 : bothSeg evalE (oGrid.idx 351) (oGrid.dm 351) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 351) oGrid.kl oGrid.kr 400 400 ⟨false, 1295339400786147835889278873987350406088330403935358047709550443248424563348⟩ ⟨false, 0⟩ ⟨false, 2077198220464997002742153338954657799596005338554358373933431120491036574002⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_351_800 : bothSeg evalE (oGrid.idx 351) (oGrid.dm 351) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 351) oGrid.kl oGrid.kr 400 800 ⟨false, 2077198220464997002742153338954657799596005338554358373933431120491036574002⟩ ⟨false, 0⟩ ⟨false, 2324079027288974199576579317765783170252924442199137733782854906734104365144⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_351_1200 : bothSeg evalE (oGrid.idx 351) (oGrid.dm 351) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 351) oGrid.kl oGrid.kr 400 1200 ⟨false, 2324079027288974199576579317765783170252924442199137733782854906734104365144⟩ ⟨false, 0⟩ ⟨false, 2298514513580512187548908402589760062534239397866958796614296908778865120594⟩ ⟨false, 37348750433241114440218956746032482729034631943515051330532910556728915154⟩ = true := by
  decide +kernel

theorem b_351_1600 : bothSeg evalE (oGrid.idx 351) (oGrid.dm 351) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 351) oGrid.kl oGrid.kr 400 1600 ⟨false, 2298514513580512187548908402589760062534239397866958796614296908778865120594⟩ ⟨false, 37348750433241114440218956746032482729034631943515051330532910556728915154⟩ ⟨false, 2146578555565542049910177475856949876876293842972171305747748941139801612572⟩ ⟨false, 189284708448211252078949883478842668386980186838302542197080878195792423176⟩ = true := by
  decide +kernel

theorem b_351_2000 : bothSeg evalE (oGrid.idx 351) (oGrid.dm 351) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 351) oGrid.kl oGrid.kr 400 2000 ⟨false, 2146578555565542049910177475856949876876293842972171305747748941139801612572⟩ ⟨false, 189284708448211252078949883478842668386980186838302542197080878195792423176⟩ ⟨false, 2145370631894452144973597981622269001829386526201426368428747541329645713948⟩ ⟨false, 197603190471640145379295154189057170036354441552453866685585242740488448104⟩ = true := by
  decide +kernel

theorem b_351_2400 : bothLoop evalE (oGrid.idx 351) (oGrid.dm 351) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 351) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2145370631894452144973597981622269001829386526201426368428747541329645713948⟩ ⟨false, 197603190471640145379295154189057170036354441552453866685585242740488448104⟩ = true := by
  decide +kernel

theorem o_row_351 : oGrid.row evalE 351 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_351_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_351_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_351_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_351_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_351_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_351_2000).1 (bothLoop_sound b_351_2400).1))))))

theorem n_row_351 : nGrid.row evalE 351 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_351_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_351_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_351_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_351_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_351_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_351_2000).2 (bothLoop_sound b_351_2400).2))))))

theorem b_352_0 : bothSeg evalE (oGrid.idx 352) (oGrid.dm 352) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 352) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1289304968714872118831751762768061349809325646868572837768214149415362221642⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_352_400 : bothSeg evalE (oGrid.idx 352) (oGrid.dm 352) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 352) oGrid.kl oGrid.kr 400 400 ⟨false, 1289304968714872118831751762768061349809325646868572837768214149415362221642⟩ ⟨false, 0⟩ ⟨false, 2067298133686212072534037856428941623015485323943257027802412517020647105406⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_352_800 : bothSeg evalE (oGrid.idx 352) (oGrid.dm 352) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 352) oGrid.kl oGrid.kr 400 800 ⟨false, 2067298133686212072534037856428941623015485323943257027802412517020647105406⟩ ⟨false, 0⟩ ⟨false, 2312577906761185867128894482481330548104526479530832381778969500842193616044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_352_1200 : bothSeg evalE (oGrid.idx 352) (oGrid.dm 352) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 352) oGrid.kl oGrid.kr 400 1200 ⟨false, 2312577906761185867128894482481330548104526479530832381778969500842193616044⟩ ⟨false, 0⟩ ⟨false, 2286506147680370995391588310489481527922034697999546451525431053842750740846⟩ ⟨false, 37637902918170608020598850893753807596843930105043378452668246138439081450⟩ = true := by
  decide +kernel

theorem b_352_1600 : bothSeg evalE (oGrid.idx 352) (oGrid.dm 352) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 352) oGrid.kl oGrid.kr 400 1600 ⟨false, 2286506147680370995391588310489481527922034697999546451525431053842750740846⟩ ⟨false, 37637902918170608020598850893753807596843930105043378452668246138439081450⟩ ⟨false, 2134923523202458693895267701446885271487091789250656422563711585307579285492⟩ ⟨false, 189220527396082909516919459936350064031786838853933407414387714673610536804⟩ = true := by
  decide +kernel

theorem b_352_2000 : bothSeg evalE (oGrid.idx 352) (oGrid.dm 352) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 352) oGrid.kl oGrid.kr 400 2000 ⟨false, 2134923523202458693895267701446885271487091789250656422563711585307579285492⟩ ⟨false, 189220527396082909516919459936350064031786838853933407414387714673610536804⟩ ⟨false, 2133802890430970050022421131484038082114410191142183051887597939529655011886⟩ ⟨false, 197465936095176028079237086932017292174181982731695185014163640605255363052⟩ = true := by
  decide +kernel

theorem b_352_2400 : bothLoop evalE (oGrid.idx 352) (oGrid.dm 352) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 352) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2133802890430970050022421131484038082114410191142183051887597939529655011886⟩ ⟨false, 197465936095176028079237086932017292174181982731695185014163640605255363052⟩ = true := by
  decide +kernel

theorem o_row_352 : oGrid.row evalE 352 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_352_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_352_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_352_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_352_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_352_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_352_2000).1 (bothLoop_sound b_352_2400).1))))))

theorem n_row_352 : nGrid.row evalE 352 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_352_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_352_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_352_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_352_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_352_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_352_2000).2 (bothLoop_sound b_352_2400).2))))))

theorem b_353_0 : bothSeg evalE (oGrid.idx 353) (oGrid.dm 353) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 353) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1283290866752687338601750297699602624187496977258678230673925127881416426698⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_353_400 : bothSeg evalE (oGrid.idx 353) (oGrid.dm 353) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 353) oGrid.kl oGrid.kr 400 400 ⟨false, 1283290866752687338601750297699602624187496977258678230673925127881416426698⟩ ⟨false, 0⟩ ⟨false, 2057430935121623478899492344307298583809380680071511367558145751174107879960⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_353_800 : bothSeg evalE (oGrid.idx 353) (oGrid.dm 353) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 353) oGrid.kl oGrid.kr 400 800 ⟨false, 2057430935121623478899492344307298583809380680071511367558145751174107879960⟩ ⟨false, 0⟩ ⟨false, 2301115043235418893585774758690046492781207501929883466244860930915593679366⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_353_1200 : bothSeg evalE (oGrid.idx 353) (oGrid.dm 353) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 353) oGrid.kl oGrid.kr 400 1200 ⟨false, 2301115043235418893585774758690046492781207501929883466244860930915593679366⟩ ⟨false, 0⟩ ⟨false, 2274530854509246266537005321948927646447231876993876064598561435074392441440⟩ ⟨false, 37934313005662037868086133182599834276871331231869711703559503317617647304⟩ = true := by
  decide +kernel

theorem b_353_1600 : bothSeg evalE (oGrid.idx 353) (oGrid.dm 353) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 353) oGrid.kl oGrid.kr 400 1600 ⟨false, 2274530854509246266537005321948927646447231876993876064598561435074392441440⟩ ⟨false, 37934313005662037868086133182599834276871331231869711703559503317617647304⟩ ⟨false, 2123309573370768780955371730882412661115688277775031938933461122613019362304⟩ ⟨false, 189155594144139523449719724249114819608414930450713837368659815778990726440⟩ = true := by
  decide +kernel

theorem b_353_2000 : bothSeg evalE (oGrid.idx 353) (oGrid.dm 353) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 353) oGrid.kl oGrid.kr 400 2000 ⟨false, 2123309573370768780955371730882412661115688277775031938933461122613019362304⟩ ⟨false, 189155594144139523449719724249114819608414930450713837368659815778990726440⟩ ⟨false, 2122273838935759740853346618387544336350499307394443073017047083900176206678⟩ ⟨false, 197331321147506113734267629452159275824471182762808339296429593388532138288⟩ = true := by
  decide +kernel

theorem b_353_2400 : bothLoop evalE (oGrid.idx 353) (oGrid.dm 353) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 353) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2122273838935759740853346618387544336350499307394443073017047083900176206678⟩ ⟨false, 197331321147506113734267629452159275824471182762808339296429593388532138288⟩ = true := by
  decide +kernel

theorem o_row_353 : oGrid.row evalE 353 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_353_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_353_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_353_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_353_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_353_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_353_2000).1 (bothLoop_sound b_353_2400).1))))))

theorem n_row_353 : nGrid.row evalE 353 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_353_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_353_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_353_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_353_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_353_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_353_2000).2 (bothLoop_sound b_353_2400).2))))))

theorem b_354_0 : bothSeg evalE (oGrid.idx 354) (oGrid.dm 354) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 354) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1277297042979709466315699542958033490413616622747964166759618170233862226962⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_354_400 : bothSeg evalE (oGrid.idx 354) (oGrid.dm 354) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 354) oGrid.kl oGrid.kr 400 400 ⟨false, 1277297042979709466315699542958033490413616622747964166759618170233862226962⟩ ⟨false, 0⟩ ⟨false, 2047596546001760983328034304005386173003959436127991684410000265286491056282⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_354_800 : bothSeg evalE (oGrid.idx 354) (oGrid.dm 354) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 354) oGrid.kl oGrid.kr 400 800 ⟨false, 2047596546001760983328034304005386173003959436127991684410000265286491056282⟩ ⟨false, 0⟩ ⟨false, 2289690350490565333839281277373354772900257820633688573365919844453814737654⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_354_1200 : bothSeg evalE (oGrid.idx 354) (oGrid.dm 354) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 354) oGrid.kl oGrid.kr 400 1200 ⟨false, 2289690350490565333839281277373354772900257820633688573365919844453814737654⟩ ⟨false, 0⟩ ⟨false, 2262588698720225463310857403773606899038965443308197082815267673873588168124⟩ ⟨false, 38238083621019173252858846995538000954858612545215984916038853783430318774⟩ = true := by
  decide +kernel

theorem b_354_1600 : bothSeg evalE (oGrid.idx 354) (oGrid.dm 354) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 354) oGrid.kl oGrid.kr 400 1600 ⟨false, 2262588698720225463310857403773606899038965443308197082815267673873588168124⟩ ⟨false, 38238083621019173252858846995538000954858612545215984916038853783430318774⟩ ⟨false, 2111736773683600602922135574816849985599736779877360917613372294883194829408⟩ ⟨false, 189090008657644033641580675952294914394087275976052150117934232773823657490⟩ = true := by
  decide +kernel

theorem b_354_2000 : bothSeg evalE (oGrid.idx 354) (oGrid.dm 354) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 354) oGrid.kl oGrid.kr 400 2000 ⟨false, 2111736773683600602922135574816849985599736779877360917613372294883194829408⟩ ⟨false, 189090008657644033641580675952294914394087275976052150117934232773823657490⟩ ⟨false, 2110783562747710813676546021128264423924564859739813977723708875114188265160⟩ ⟨false, 197198157196117382265526974508866818821737311232054378576087082821268563884⟩ = true := by
  decide +kernel

theorem b_354_2400 : bothLoop evalE (oGrid.idx 354) (oGrid.dm 354) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 354) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2110783562747710813676546021128264423924564859739813977723708875114188265160⟩ ⟨false, 197198157196117382265526974508866818821737311232054378576087082821268563884⟩ = true := by
  decide +kernel

theorem o_row_354 : oGrid.row evalE 354 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_354_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_354_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_354_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_354_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_354_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_354_2000).1 (bothLoop_sound b_354_2400).1))))))

theorem n_row_354 : nGrid.row evalE 354 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_354_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_354_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_354_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_354_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_354_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_354_2000).2 (bothLoop_sound b_354_2400).2))))))

theorem b_355_0 : bothSeg evalE (oGrid.idx 355) (oGrid.dm 355) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 355) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1271323441999013833233384180480090137378561843370044679214352623803002881734⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_355_400 : bothSeg evalE (oGrid.idx 355) (oGrid.dm 355) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 355) oGrid.kl oGrid.kr 400 400 ⟨false, 1271323441999013833233384180480090137378561843370044679214352623803002881734⟩ ⟨false, 0⟩ ⟨false, 2037794892299071961146749650046786935046125682487121937638691021575755827956⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_355_800 : bothSeg evalE (oGrid.idx 355) (oGrid.dm 355) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 355) oGrid.kl oGrid.kr 400 800 ⟨false, 2037794892299071961146749650046786935046125682487121937638691021575755827956⟩ ⟨false, 0⟩ ⟨false, 2278303676384658113894655273043653106728284736413249535152603913410853842186⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_355_1200 : bothSeg evalE (oGrid.idx 355) (oGrid.dm 355) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 355) oGrid.kl oGrid.kr 400 1200 ⟨false, 2278303676384658113894655273043653106728284736413249535152603913410853842186⟩ ⟨false, 0⟩ ⟨false, 2250678999383004754637063128285909473432620403365847275574400374704830511706⟩ ⟨false, 38549717874974342411829408261738355737339328862218567128796226355674255260⟩ = true := by
  decide +kernel

theorem b_355_1600 : bothSeg evalE (oGrid.idx 355) (oGrid.dm 355) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 355) oGrid.kl oGrid.kr 400 1600 ⟨false, 2250678999383004754637063128285909473432620403365847275574400374704830511706⟩ ⟨false, 38549717874974342411829408261738355737339328862218567128796226355674255260⟩ ⟨false, 2100204320179820075864212473425214117776352325624887206253639758913449683832⟩ ⟨false, 189024397078159021184680063122433711393607406603178636449556842147055083134⟩ = true := by
  decide +kernel

theorem b_355_2000 : bothSeg evalE (oGrid.idx 355) (oGrid.dm 355) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 355) oGrid.kl oGrid.kr 400 2000 ⟨false, 2100204320179820075864212473425214117776352325624887206253639758913449683832⟩ ⟨false, 189024397078159021184680063122433711393607406603178636449556842147055083134⟩ ⟨false, 2099331269588669539418637439045439589132593109644264797049303749501012437296⟩ ⟨false, 197067069295972359117781451071051090033534029268106992248349348505893761304⟩ = true := by
  decide +kernel

theorem b_355_2400 : bothLoop evalE (oGrid.idx 355) (oGrid.dm 355) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 355) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2099331269588669539418637439045439589132593109644264797049303749501012437296⟩ ⟨false, 197067069295972359117781451071051090033534029268106992248349348505893761304⟩ = true := by
  decide +kernel

theorem o_row_355 : oGrid.row evalE 355 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_355_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_355_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_355_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_355_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_355_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_355_2000).1 (bothLoop_sound b_355_2400).1))))))

theorem n_row_355 : nGrid.row evalE 355 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_355_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_355_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_355_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_355_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_355_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_355_2000).2 (bothLoop_sound b_355_2400).2))))))

theorem b_356_0 : bothSeg evalE (oGrid.idx 356) (oGrid.dm 356) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 356) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1265370017815924298658515752945221348766637718496402762452256453922161742230⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_356_400 : bothSeg evalE (oGrid.idx 356) (oGrid.dm 356) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 356) oGrid.kl oGrid.kr 400 400 ⟨false, 1265370017815924298658515752945221348766637718496402762452256453922161742230⟩ ⟨false, 0⟩ ⟨false, 2028025891371190657876050855255050844556077420006756534399212896237818226910⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_356_800 : bothSeg evalE (oGrid.idx 356) (oGrid.dm 356) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 356) oGrid.kl oGrid.kr 400 800 ⟨false, 2028025891371190657876050855255050844556077420006756534399212896237818226910⟩ ⟨false, 0⟩ ⟨false, 2266955011120054252387854589440155292249192736699339377765464622076160973044⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_356_1200 : bothSeg evalE (oGrid.idx 356) (oGrid.dm 356) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 356) oGrid.kl oGrid.kr 400 1200 ⟨false, 2266955011120054252387854589440155292249192736699339377765464622076160973044⟩ ⟨false, 0⟩ ⟨false, 2238802350538244113747964341808810304865853685363605253714951886319759705500⟩ ⟨false, 38868552979132290577660692659780762880168240666124413104366308751874871814⟩ = true := by
  decide +kernel

theorem b_356_1600 : bothSeg evalE (oGrid.idx 356) (oGrid.dm 356) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 356) oGrid.kl oGrid.kr 400 1600 ⟨false, 2238802350538244113747964341808810304865853685363605253714951886319759705500⟩ ⟨false, 38868552979132290577660692659780762880168240666124413104366308751874871814⟩ ⟨false, 2088712757577801397952982017238001580128689774669407638616974975819984437742⟩ ⟨false, 188958145939575006372643017230589487617332151360322028202343219251650139572⟩ = true := by
  decide +kernel

theorem b_356_2000 : bothSeg evalE (oGrid.idx 356) (oGrid.dm 356) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 356) oGrid.kl oGrid.kr 400 2000 ⟨false, 2088712757577801397952982017238001580128689774669407638616974975819984437742⟩ ⟨false, 188958145939575006372643017230589487617332151360322028202343219251650139572⟩ ⟨false, 2087917517852535866460835995101393665099226746377213999903052223282589414320⟩ ⟨false, 196937992280942474325830758996411493876759375466314076750024143702852122312⟩ = true := by
  decide +kernel

theorem b_356_2400 : bothLoop evalE (oGrid.idx 356) (oGrid.dm 356) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 356) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2087917517852535866460835995101393665099226746377213999903052223282589414320⟩ ⟨false, 196937992280942474325830758996411493876759375466314076750024143702852122312⟩ = true := by
  decide +kernel

theorem o_row_356 : oGrid.row evalE 356 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_356_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_356_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_356_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_356_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_356_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_356_2000).1 (bothLoop_sound b_356_2400).1))))))

theorem n_row_356 : nGrid.row evalE 356 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_356_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_356_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_356_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_356_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_356_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_356_2000).2 (bothLoop_sound b_356_2400).2))))))

theorem b_357_0 : bothSeg evalE (oGrid.idx 357) (oGrid.dm 357) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 357) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1259436709635726990810346735093039799664612989872538181876549762005625194186⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_357_400 : bothSeg evalE (oGrid.idx 357) (oGrid.dm 357) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 357) oGrid.kl oGrid.kr 400 400 ⟨false, 1259436709635726990810346735093039799664612989872538181876549762005625194186⟩ ⟨false, 0⟩ ⟨false, 2018289465818125053843714009652735392641412680410292930035209809030628253902⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_357_800 : bothSeg evalE (oGrid.idx 357) (oGrid.dm 357) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 357) oGrid.kl oGrid.kr 400 800 ⟨false, 2018289465818125053843714009652735392641412680410292930035209809030628253902⟩ ⟨false, 0⟩ ⟨false, 2255644266828392249326102682108788267658063199499508307814211019293113927788⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_357_1200 : bothSeg evalE (oGrid.idx 357) (oGrid.dm 357) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 357) oGrid.kl oGrid.kr 400 1200 ⟨false, 2255644266828392249326102682108788267658063199499508307814211019293113927788⟩ ⟨false, 0⟩ ⟨false, 2226958640322018874058413297286148528579149174238796086038754235135001563218⟩ ⟨false, 39194751001480663295299528649380093076995769817431732183804873407737847732⟩ = true := by
  decide +kernel

theorem b_357_1600 : bothSeg evalE (oGrid.idx 357) (oGrid.dm 357) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 357) oGrid.kl oGrid.kr 400 1600 ⟨false, 2226958640322018874058413297286148528579149174238796086038754235135001563218⟩ ⟨false, 39194751001480663295299528649380093076995769817431732183804873407737847732⟩ ⟨false, 2077261867382280548569034657768502625320321164141211246712420642179833843640⟩ ⟨false, 188891523941218988784678168167025996335823779915016571510138466362905567310⟩ = true := by
  decide +kernel

theorem b_357_2000 : bothSeg evalE (oGrid.idx 357) (oGrid.dm 357) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 357) oGrid.kl oGrid.kr 400 2000 ⟨false, 2077261867382280548569034657768502625320321164141211246712420642179833843640⟩ ⟨false, 188891523941218988784678168167025996335823779915016571510138466362905567310⟩ ⟨false, 2076542154059530798253704162499030693669864024953269973560128733722325889760⟩ ⟨false, 196810474845093352804257771089121241589569950351969730035736411208765476286⟩ = true := by
  decide +kernel

theorem b_357_2400 : bothLoop evalE (oGrid.idx 357) (oGrid.dm 357) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 357) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2076542154059530798253704162499030693669864024953269973560128733722325889760⟩ ⟨false, 196810474845093352804257771089121241589569950351969730035736411208765476286⟩ = true := by
  decide +kernel

theorem o_row_357 : oGrid.row evalE 357 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_357_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_357_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_357_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_357_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_357_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_357_2000).1 (bothLoop_sound b_357_2400).1))))))

theorem n_row_357 : nGrid.row evalE 357 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_357_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_357_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_357_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_357_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_357_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_357_2000).2 (bothLoop_sound b_357_2400).2))))))

theorem b_358_0 : bothSeg evalE (oGrid.idx 358) (oGrid.dm 358) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 358) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1253523470412288459918478494274051170362628610068769936035796066342396956858⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_358_400 : bothSeg evalE (oGrid.idx 358) (oGrid.dm 358) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 358) oGrid.kl oGrid.kr 400 400 ⟨false, 1253523470412288459918478494274051170362628610068769936035796066342396956858⟩ ⟨false, 0⟩ ⟨false, 2008585536588696304597439421040963830180533927346887998084090368571385758472⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_358_800 : bothSeg evalE (oGrid.idx 358) (oGrid.dm 358) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 358) oGrid.kl oGrid.kr 400 800 ⟨false, 2008585536588696304597439421040963830180533927346887998084090368571385758472⟩ ⟨false, 0⟩ ⟨false, 2244371289957285940118799469759472393431515122368558571101724439646306345798⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_358_1200 : bothSeg evalE (oGrid.idx 358) (oGrid.dm 358) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 358) oGrid.kl oGrid.kr 400 1200 ⟨false, 2244371289957285940118799469759472393431515122368558571101724439646306345798⟩ ⟨false, 0⟩ ⟨false, 2215147908766353777436691834123836169222928106793300149771982132607725043292⟩ ⟨false, 39527851972615506747772716747110927552732869031394610713477627342594986262⟩ = true := by
  decide +kernel

theorem b_358_1600 : bothSeg evalE (oGrid.idx 358) (oGrid.dm 358) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 358) oGrid.kl oGrid.kr 400 1600 ⟨false, 2215147908766353777436691834123836169222928106793300149771982132607725043292⟩ ⟨false, 39527851972615506747772716747110927552732869031394610713477627342594986262⟩ ⟨false, 2065851593735824760010578223838648088161030889436315726595422414215455077426⟩ ⟨false, 188824167003144524173886327032299008614630086388379033890037345734864952128⟩ = true := by
  decide +kernel

theorem b_358_2000 : bothSeg evalE (oGrid.idx 358) (oGrid.dm 358) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 358) oGrid.kl oGrid.kr 400 2000 ⟨false, 2065851593735824760010578223838648088161030889436315726595422414215455077426⟩ ⟨false, 188824167003144524173886327032299008614630086388379033890037345734864952128⟩ ⟨false, 2065205126156430654877049875783665282297853701162463960857003971272679843936⟩ ⟨false, 196684989065981947286590311197731035762911847568361171694639956493618940588⟩ = true := by
  decide +kernel

theorem b_358_2400 : bothLoop evalE (oGrid.idx 358) (oGrid.dm 358) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 358) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2065205126156430654877049875783665282297853701162463960857003971272679843936⟩ ⟨false, 196684989065981947286590311197731035762911847568361171694639956493618940588⟩ = true := by
  decide +kernel

theorem o_row_358 : oGrid.row evalE 358 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_358_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_358_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_358_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_358_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_358_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_358_2000).1 (bothLoop_sound b_358_2400).1))))))

theorem n_row_358 : nGrid.row evalE 358 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_358_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_358_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_358_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_358_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_358_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_358_2000).2 (bothLoop_sound b_358_2400).2))))))

theorem b_359_0 : bothSeg evalE (oGrid.idx 359) (oGrid.dm 359) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 359) oGrid.kl oGrid.kr 400 0 ⟨false, 0⟩ ⟨false, 0⟩ ⟨false, 1247630246435735772421041379388412779660364608210756988894004346824844903084⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_359_400 : bothSeg evalE (oGrid.idx 359) (oGrid.dm 359) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 359) oGrid.kl oGrid.kr 400 400 ⟨false, 1247630246435735772421041379388412779660364608210756988894004346824844903084⟩ ⟨false, 0⟩ ⟨false, 1998914028499679071991174595472828079662758982730287271101220604121402762240⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_359_800 : bothSeg evalE (oGrid.idx 359) (oGrid.dm 359) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 359) oGrid.kl oGrid.kr 400 800 ⟨false, 1998914028499679071991174595472828079662758982730287271101220604121402762240⟩ ⟨false, 0⟩ ⟨false, 2233136045602383674618912099153144128462151838253973953433803036604223903170⟩ ⟨false, 0⟩ = true := by
  decide +kernel

theorem b_359_1200 : bothSeg evalE (oGrid.idx 359) (oGrid.dm 359) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 359) oGrid.kl oGrid.kr 400 1200 ⟨false, 2233136045602383674618912099153144128462151838253973953433803036604223903170⟩ ⟨false, 0⟩ ⟨false, 2203370135984880258317584557449886869553467785928808853579185946048683556918⟩ ⟨false, 39867729015108126726045133517746315994276949326522574715794027583022367984⟩ = true := by
  decide +kernel

theorem b_359_1600 : bothSeg evalE (oGrid.idx 359) (oGrid.dm 359) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 359) oGrid.kl oGrid.kr 400 1600 ⟨false, 2203370135984880258317584557449886869553467785928808853579185946048683556918⟩ ⟨false, 39867729015108126726045133517746315994276949326522574715794027583022367984⟩ ⟨false, 2054481831115422605579820047821910421312455977781698303927922641032211278646⟩ ⟨false, 188756033884565779463809643145722764235288757473633124367057332599494646256⟩ = true := by
  decide +kernel

theorem b_359_2000 : bothSeg evalE (oGrid.idx 359) (oGrid.dm 359) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 359) oGrid.kl oGrid.kr 400 2000 ⟨false, 2054481831115422605579820047821910421312455977781698303927922641032211278646⟩ ⟨false, 188756033884565779463809643145722764235288757473633124367057332599494646256⟩ ⟨false, 2053906353722801725517841265193834119971576968782458475272723065019263018398⟩ ⟨false, 196561105508354261392967463471975614451796734870788871274706525462268645558⟩ = true := by
  decide +kernel

theorem b_359_2400 : bothLoop evalE (oGrid.idx 359) (oGrid.dm 359) oGrid.sm oGrid.thr (inRowB oGrid.jl oGrid.jr 359) oGrid.kl oGrid.kr nGrid.thr 379 2400 ⟨false, 2053906353722801725517841265193834119971576968782458475272723065019263018398⟩ ⟨false, 196561105508354261392967463471975614451796734870788871274706525462268645558⟩ = true := by
  decide +kernel

theorem o_row_359 : oGrid.row evalE 359 = true :=
  (outerLoop_of_seg (m := 2379) (bothSeg_sound b_359_0).1 (outerLoop_of_seg (m := 1979) (bothSeg_sound b_359_400).1 (outerLoop_of_seg (m := 1579) (bothSeg_sound b_359_800).1 (outerLoop_of_seg (m := 1179) (bothSeg_sound b_359_1200).1 (outerLoop_of_seg (m := 779) (bothSeg_sound b_359_1600).1 (outerLoop_of_seg (m := 379) (bothSeg_sound b_359_2000).1 (bothLoop_sound b_359_2400).1))))))

theorem n_row_359 : nGrid.row evalE 359 = true :=
  (negLoop_of_seg (m := 2379) (bothSeg_sound b_359_0).2 (negLoop_of_seg (m := 1979) (bothSeg_sound b_359_400).2 (negLoop_of_seg (m := 1579) (bothSeg_sound b_359_800).2 (negLoop_of_seg (m := 1179) (bothSeg_sound b_359_1200).2 (negLoop_of_seg (m := 779) (bothSeg_sound b_359_1600).2 (negLoop_of_seg (m := 379) (bothSeg_sound b_359_2000).2 (bothLoop_sound b_359_2400).2))))))

theorem o_blk_336 : allFrom (fun j => oGrid.row evalE j) 336 24 = true :=
  (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 336) o_row_336 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 337) o_row_337 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 338) o_row_338 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 339) o_row_339 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 340) o_row_340 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 341) o_row_341 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 342) o_row_342 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 343) o_row_343 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 344) o_row_344 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 345) o_row_345 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 346) o_row_346 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 347) o_row_347 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 348) o_row_348 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 349) o_row_349 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 350) o_row_350 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 351) o_row_351 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 352) o_row_352 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 353) o_row_353 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 354) o_row_354 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 355) o_row_355 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 356) o_row_356 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 357) o_row_357 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 358) o_row_358 (allFrom_cons (f := fun j => oGrid.row evalE j) (a := 359) o_row_359 (allFrom_zero (fun j => oGrid.row evalE j) 360)))))))))))))))))))))))))

theorem n_blk_336 : allFrom (fun j => nGrid.row evalE j) 336 24 = true :=
  (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 336) n_row_336 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 337) n_row_337 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 338) n_row_338 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 339) n_row_339 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 340) n_row_340 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 341) n_row_341 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 342) n_row_342 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 343) n_row_343 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 344) n_row_344 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 345) n_row_345 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 346) n_row_346 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 347) n_row_347 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 348) n_row_348 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 349) n_row_349 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 350) n_row_350 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 351) n_row_351 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 352) n_row_352 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 353) n_row_353 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 354) n_row_354 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 355) n_row_355 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 356) n_row_356 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 357) n_row_357 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 358) n_row_358 (allFrom_cons (f := fun j => nGrid.row evalE j) (a := 359) n_row_359 (allFrom_zero (fun j => nGrid.row evalE j) 360)))))))))))))))))))))))))

end SandierSerfaty.CertData.Box
