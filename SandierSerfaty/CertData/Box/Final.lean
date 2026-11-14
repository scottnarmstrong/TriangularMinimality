/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Box.Checks
public import SandierSerfaty.CertData.Box.KRow
public import SandierSerfaty.CertData.Box.Both.S000
public import SandierSerfaty.CertData.Box.Both.S001
public import SandierSerfaty.CertData.Box.Both.S002
public import SandierSerfaty.CertData.Box.Both.S003
public import SandierSerfaty.CertData.Box.Both.S004
public import SandierSerfaty.CertData.Box.Both.S005
public import SandierSerfaty.CertData.Box.Both.S006
public import SandierSerfaty.CertData.Box.Both.S007
public import SandierSerfaty.CertData.Box.Both.S008
public import SandierSerfaty.CertData.Box.Both.S009
public import SandierSerfaty.CertData.Box.Both.S010
public import SandierSerfaty.CertData.Box.Both.S011
public import SandierSerfaty.CertData.Box.Both.S012
public import SandierSerfaty.CertData.Box.Both.S013
public import SandierSerfaty.CertData.Box.Both.S014
public import SandierSerfaty.CertData.Box.Both.S015
public import SandierSerfaty.CertData.Box.Both.S016
public import SandierSerfaty.CertData.Box.Both.S017
public import SandierSerfaty.CertData.Box.Both.S018
public import SandierSerfaty.CertData.Box.Both.S019
public import SandierSerfaty.CertData.Box.Both.S020
public import SandierSerfaty.CertData.Box.Both.S021
public import SandierSerfaty.CertData.Box.Both.S022
public import SandierSerfaty.CertData.Box.Both.S023
public import SandierSerfaty.CertData.Box.Both.S024
public import SandierSerfaty.CertData.Box.Both.S025
public import SandierSerfaty.CertData.Box.Both.S026
public import SandierSerfaty.CertData.Box.Both.S027
public import SandierSerfaty.CertData.Box.Both.S028
public import SandierSerfaty.CertData.Box.Both.S029
public import SandierSerfaty.CertData.Box.Both.S030
public import SandierSerfaty.CertData.Box.Both.S031
public import SandierSerfaty.CertData.Box.Both.S032
public import SandierSerfaty.CertData.Box.Both.S033
public import SandierSerfaty.CertData.Box.Both.S034
public import SandierSerfaty.CertData.Box.Both.S035
public import SandierSerfaty.CertData.Box.Both.S036
public import SandierSerfaty.CertData.Box.Both.S037
public import SandierSerfaty.CertData.Box.Both.S038
public import SandierSerfaty.CertData.Box.Both.S039
public import SandierSerfaty.CertData.Box.Both.S040
public import SandierSerfaty.CertData.Box.Both.S041
public import SandierSerfaty.CertData.Box.Both.S042
public import SandierSerfaty.CertData.Box.Both.S043
public import SandierSerfaty.CertData.Box.Both.S044
public import SandierSerfaty.CertData.Box.Both.S045
public import SandierSerfaty.CertData.Box.Both.S046
public import SandierSerfaty.CertData.Box.Both.S047
public import SandierSerfaty.CertData.Box.Both.S048
public import SandierSerfaty.CertData.Box.Both.S049
public import SandierSerfaty.CertData.Box.Both.S050
public import SandierSerfaty.CertData.Box.Both.S051
public import SandierSerfaty.CertData.Box.Both.S052
public import SandierSerfaty.CertData.Box.Both.S053
public import SandierSerfaty.CertData.Box.Both.S054
public import SandierSerfaty.CertData.Box.Both.S055
public import SandierSerfaty.CertData.Box.Both.S056
public import SandierSerfaty.CertData.Box.Both.S057
public import SandierSerfaty.CertData.Box.Both.S058
public import SandierSerfaty.CertData.Box.Both.S059
public import SandierSerfaty.CertData.Box.Both.S060
public import SandierSerfaty.CertData.Box.Both.S061
public import SandierSerfaty.CertData.Box.Both.S062
public import SandierSerfaty.CertData.Box.Both.S063
public import SandierSerfaty.CertData.Box.Both.S064
public import SandierSerfaty.CertData.Box.Both.S065
public import SandierSerfaty.CertData.Box.Both.S066
public import SandierSerfaty.CertData.Box.Both.S067
public import SandierSerfaty.CertData.Box.Both.S068
public import SandierSerfaty.CertData.Box.Both.S069
public import SandierSerfaty.CertData.Box.Both.S070
public import SandierSerfaty.CertData.Box.A7.S000
public import SandierSerfaty.CertData.Box.A7.S001
public import SandierSerfaty.CertData.Box.A7.S002
public import SandierSerfaty.CertData.Box.A7.S003
public import SandierSerfaty.CertData.Box.A7.S004
public import SandierSerfaty.CertData.Box.A7.S005
public import SandierSerfaty.CertData.Box.A7.S006
public import SandierSerfaty.CertData.Box.A7.S007
public import SandierSerfaty.CertData.Box.A7.S008
public import SandierSerfaty.CertData.Box.A7.S009
public import SandierSerfaty.CertData.Box.A7.S010
public import SandierSerfaty.CertData.Box.A7.S011
public import SandierSerfaty.CertData.Box.A7.S012
public import SandierSerfaty.CertData.Box.A7.S013
public import SandierSerfaty.CertData.Box.A7.S014
public import SandierSerfaty.CertData.Box.A7.S015
public import SandierSerfaty.CertData.Box.A7.S016
public import SandierSerfaty.CertData.Box.A7.S017
public import SandierSerfaty.CertData.Box.A7.S018
public import SandierSerfaty.CertData.Box.A7.S019
public import SandierSerfaty.CertData.Box.A7.S020
public import SandierSerfaty.CertData.Box.A7.S021
public import SandierSerfaty.CertData.Box.Hess.S000
public import SandierSerfaty.CertData.Box.Hess.S001
public import SandierSerfaty.CertData.Box.Hess.S002
public import SandierSerfaty.CertData.Box.Hess.S003
public import SandierSerfaty.CertData.Box.Hess.S004
public import SandierSerfaty.CertData.Box.Hess.S005
public import SandierSerfaty.CertData.Box.Hess.S006
public import SandierSerfaty.CertData.Box.Hess.S007
public import SandierSerfaty.CertData.Box.Hess.S008
public import SandierSerfaty.CertData.Box.Hess.S009
public import SandierSerfaty.CertData.Box.Hess.S010
public import SandierSerfaty.CertData.Box.Hess.S011
public import SandierSerfaty.CertData.Box.Hess.S012
public import SandierSerfaty.CertData.Box.Hess.S013
public import SandierSerfaty.CertData.Box.Hess.S014
public import SandierSerfaty.CertData.Box.Hess.S015
public import SandierSerfaty.CertData.Box.Hess.S016
public import SandierSerfaty.CertData.Box.Hess.S017
public import SandierSerfaty.CertData.Box.Hess.S018
public import SandierSerfaty.CertData.Box.Hess.S019
public import SandierSerfaty.CertData.Box.Hess.S020
public import SandierSerfaty.CertData.Box.Hess.S021
public import SandierSerfaty.CertData.Box.Hess.S022
public import SandierSerfaty.CertData.Box.Hess.S023
public import SandierSerfaty.CertData.Box.Hess.S024
public import SandierSerfaty.CertData.Box.Hess.S025
public import SandierSerfaty.CertData.Box.Hess.S026
public import SandierSerfaty.CertData.Box.Hess.S027
public import SandierSerfaty.CertData.Box.Hess.S028
public import SandierSerfaty.CertData.Box.Hess.S029
public import SandierSerfaty.CertData.Box.Hess.S030
public import SandierSerfaty.CertData.Box.Hess.S031
public import SandierSerfaty.CertData.Box.Hess.S032
public import SandierSerfaty.CertData.Box.Hess.S033
public import SandierSerfaty.CertData.Box.Hess.S034
public import SandierSerfaty.CertData.Box.Hess.S035
public import SandierSerfaty.CertData.Box.Hess.S036
public import SandierSerfaty.CertData.Box.Hess.S037
public import SandierSerfaty.CertData.Box.Hess.S038
public import SandierSerfaty.CertData.Box.Hess.S039
public import SandierSerfaty.CertData.Box.Hess.S040
public import SandierSerfaty.CertData.Box.Hess.S041
public import SandierSerfaty.CertData.Box.Hess.S042
public import SandierSerfaty.CertData.Box.Hess.S043
public import SandierSerfaty.CertData.Box.Hess.S044
public import SandierSerfaty.CertData.Box.Hess.S045
public import SandierSerfaty.CertData.Box.Hess.S046
public import SandierSerfaty.CertData.Box.Hess.S047
public import SandierSerfaty.CertData.Box.Hess.S048
public import SandierSerfaty.CertData.Box.Hess.S049
public import SandierSerfaty.CertData.Box.Hess.S050
public import SandierSerfaty.CertData.Box.Hess.S051
public import SandierSerfaty.CertData.Box.Hess.S052
public import SandierSerfaty.CertData.Box.Hess.S053
public import SandierSerfaty.CertData.Box.Hess.S054
public import SandierSerfaty.CertData.Box.Hess.S055
public import SandierSerfaty.CertData.Box.Hess.S056
public import SandierSerfaty.CertData.Box.Hess.S057
public import SandierSerfaty.CertData.Box.Hess.S058
public import SandierSerfaty.CertData.Box.Hess.S059
public import SandierSerfaty.CertData.Box.Hess.S060
public import SandierSerfaty.CertData.Box.Hess.S061
public import SandierSerfaty.CertData.Box.Hess.S062
public import SandierSerfaty.CertData.Box.Hess.S063
public import SandierSerfaty.CertData.Box.Hess.S064
public import SandierSerfaty.CertData.Box.Hess.S065
public import SandierSerfaty.CertData.Box.Hess.S066
public import SandierSerfaty.CertData.Box.Hess.S067
public import SandierSerfaty.CertData.Box.Hess.S068
public import SandierSerfaty.CertData.Box.Hess.S069
public import SandierSerfaty.CertData.Box.Hess.S070
public import SandierSerfaty.CertData.Box.Hess.S071
public import SandierSerfaty.CertData.Box.Hess.S072
public import SandierSerfaty.CertData.Box.Hess.S073
public import SandierSerfaty.CertData.Box.Hess.S074
public import SandierSerfaty.CertData.Box.Hess.S075
public import SandierSerfaty.CertData.Box.Hess.S076
public import SandierSerfaty.CertData.Box.Hess.S077
public import SandierSerfaty.CertData.Box.Hess.S078
public import SandierSerfaty.CertData.Box.Hess.S079
public import SandierSerfaty.CertData.Box.Hess.S080
public import SandierSerfaty.CertData.Box.Hess.S081
public import SandierSerfaty.CertData.Box.Hess.S082
public import SandierSerfaty.CertData.Box.Hess.S083
public import SandierSerfaty.CertData.Box.Hess.S084
public import SandierSerfaty.CertData.Box.Hess.S085
public import SandierSerfaty.CertData.Box.Hess.S086
public import SandierSerfaty.CertData.Box.Hess.S087
public import SandierSerfaty.CertData.Box.Hess.S088
public import SandierSerfaty.CertData.Box.Hess.S089
public import SandierSerfaty.CertData.Box.Hess.S090
public import SandierSerfaty.CertData.Box.Hess.S091
public import SandierSerfaty.CertData.Box.Hess.S092
public import SandierSerfaty.CertData.Box.Hess.S093
public import SandierSerfaty.CertData.Box.Hess.S094
public import SandierSerfaty.CertData.Box.Hess.S095
public import SandierSerfaty.CertData.Box.Hess.S096
public import SandierSerfaty.CertData.Box.Hess.S097
public import SandierSerfaty.CertData.Box.Hess.S098
public import SandierSerfaty.CertData.Box.Hess.S099
public import SandierSerfaty.CertData.Box.Hess.S100
public import SandierSerfaty.CertData.Box.Hess.S101
public import SandierSerfaty.CertData.Box.Hess.S102
public import SandierSerfaty.CertData.Box.Hess.S103
public import SandierSerfaty.CertData.Box.Hess.S104
public import SandierSerfaty.CertData.Box.Hess.S105
public import SandierSerfaty.CertData.Box.Hess.S106
public import SandierSerfaty.CertData.Box.Hess.S107
public import SandierSerfaty.CertData.Box.Hess.S108
public import SandierSerfaty.CertData.Box.Hess.S109
public import SandierSerfaty.CertData.Box.Hess.S110
public import SandierSerfaty.CertData.Box.Hess.S111
public import SandierSerfaty.CertData.Box.Hess.S112
public import SandierSerfaty.CertData.Box.Hess.S113
public import SandierSerfaty.CertData.Box.Hess.S114
public import SandierSerfaty.CertData.Box.Hess.S115
public import SandierSerfaty.CertData.Box.Hess.S116
public import SandierSerfaty.CertData.Box.Hess.S117
public import SandierSerfaty.CertData.Box.Hess.S118
public import SandierSerfaty.CertData.Box.Hess.S119
public import SandierSerfaty.CertData.Box.Hess.S120
public import SandierSerfaty.CertData.Box.Hess.S121
public import SandierSerfaty.CertData.Box.Hess.S122
public import SandierSerfaty.CertData.Box.Hess.S123
public import SandierSerfaty.CertData.Box.Hess.S124
public import SandierSerfaty.CertData.Box.Hess.S125
public import SandierSerfaty.CertData.Box.Hess.S126
public import SandierSerfaty.CertData.Box.Hess.S127
public import SandierSerfaty.CertData.Box.Hess.S128
public import SandierSerfaty.CertData.Box.Hess.S129
public import SandierSerfaty.CertData.Box.Hess.S130
public import SandierSerfaty.CertData.Box.Hess.S131
public import SandierSerfaty.CertData.Box.Hess.S132
public import SandierSerfaty.CertData.Box.Hess.S133
public import SandierSerfaty.CertData.Box.Hess.S134
public import SandierSerfaty.CertData.Box.Hess.S135
public import SandierSerfaty.CertData.Box.Hess.S136
public import SandierSerfaty.CertData.Box.Hess.S137
public import SandierSerfaty.CertData.Box.Hess.S138
public import SandierSerfaty.CertData.Box.Hess.S139
public import SandierSerfaty.CertData.Box.Hess.S140
public import SandierSerfaty.CertData.Box.Hess.S141
public import SandierSerfaty.CertData.Box.Hess.S142
public import SandierSerfaty.CertData.Box.Hess.S143
public import SandierSerfaty.CertData.Box.Hess.S144
public import SandierSerfaty.CertData.Box.Hess.S145
public import SandierSerfaty.CertData.Box.Hess.S146
public import SandierSerfaty.CertData.Box.Hess.S147
public import SandierSerfaty.CertData.Box.Hess.S148
public import SandierSerfaty.CertData.Box.Hess.S149
public import SandierSerfaty.CertData.Box.Hess.S150
public import SandierSerfaty.CertData.Box.QCheck.S00
public import SandierSerfaty.CertData.Box.QCheck.S01
public import SandierSerfaty.CertData.Box.QCheck.S02
public import SandierSerfaty.CertData.Box.QCheck.S03
public import SandierSerfaty.CertData.Box.QCheck.S04
public import SandierSerfaty.CertData.Box.QCheck.S05
public import SandierSerfaty.CertData.Box.QCheck.S06
public import SandierSerfaty.CertData.Box.QCheck.S07

/-!
# The Boolean checks of the box assertions, assembled

`a7BI`, `outerGridB`, `negGridB`, `kRowB`, `hessBI` of `Lambda.certificateGoal_of_checks''` on the literal data, and the
`cellCheck` conjunction of the query cells (for `QRealizes`), from the shards. With `Box.Checks` these are all the
Boolean hypotheses of the box layer of `certificateGoal_of_checks''`; its remaining premises are the table model
(`Table.Encl.tbl_model`) and the enclosures of the constants (`ExteriorSigns`).
-/

public section

namespace SandierSerfaty.CertData.Box

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Box

theorem a7B_ok : a7BI a7Dat aIx = true :=
  a7BI_of a7_pre
    (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 84) (m := 3) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 80) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 76) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 72) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 68) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 64) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 60) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 56) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 52) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 48) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 44) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 40) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 36) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 32) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 28) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 24) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 20) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 16) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 12) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 8) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 4) (m := 4) (allLt_add (f := fun j => a7Dat.rowI aIx j a7Dat.nk) (n := 0) (m := 4) (allLt_zero (fun j => a7Dat.rowI aIx j a7Dat.nk)) a7_blk_0) a7_blk_4) a7_blk_8) a7_blk_12) a7_blk_16) a7_blk_20) a7_blk_24) a7_blk_28) a7_blk_32) a7_blk_36) a7_blk_40) a7_blk_44) a7_blk_48) a7_blk_52) a7_blk_56) a7_blk_60) a7_blk_64) a7_blk_68) a7_blk_72) a7_blk_76) a7_blk_80) a7_blk_84)

theorem outer_ok : outerGridB a7Dat oGrid evalE parLit = true :=
  outerGridB_of outer_pre
    (allLt_add (f := fun j => oGrid.row evalE j) (n := 1680) (m := 2) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1656) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1632) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1608) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1584) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1560) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1536) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1512) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1488) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1464) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1440) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1416) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1392) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1368) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1344) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1320) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1296) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1272) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1248) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1224) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1200) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1176) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1152) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1128) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1104) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1080) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1056) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1032) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 1008) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 984) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 960) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 936) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 912) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 888) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 864) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 840) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 816) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 792) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 768) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 744) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 720) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 696) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 672) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 648) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 624) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 600) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 576) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 552) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 528) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 504) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 480) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 456) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 432) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 408) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 384) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 360) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 336) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 312) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 288) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 264) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 240) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 216) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 192) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 168) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 144) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 120) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 96) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 72) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 48) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 24) (m := 24) (allLt_add (f := fun j => oGrid.row evalE j) (n := 0) (m := 24) (allLt_zero (fun j => oGrid.row evalE j)) o_blk_0) o_blk_24) o_blk_48) o_blk_72) o_blk_96) o_blk_120) o_blk_144) o_blk_168) o_blk_192) o_blk_216) o_blk_240) o_blk_264) o_blk_288) o_blk_312) o_blk_336) o_blk_360) o_blk_384) o_blk_408) o_blk_432) o_blk_456) o_blk_480) o_blk_504) o_blk_528) o_blk_552) o_blk_576) o_blk_600) o_blk_624) o_blk_648) o_blk_672) o_blk_696) o_blk_720) o_blk_744) o_blk_768) o_blk_792) o_blk_816) o_blk_840) o_blk_864) o_blk_888) o_blk_912) o_blk_936) o_blk_960) o_blk_984) o_blk_1008) o_blk_1032) o_blk_1056) o_blk_1080) o_blk_1104) o_blk_1128) o_blk_1152) o_blk_1176) o_blk_1200) o_blk_1224) o_blk_1248) o_blk_1272) o_blk_1296) o_blk_1320) o_blk_1344) o_blk_1368) o_blk_1392) o_blk_1416) o_blk_1440) o_blk_1464) o_blk_1488) o_blk_1512) o_blk_1536) o_blk_1560) o_blk_1584) o_blk_1608) o_blk_1632) o_blk_1656) o_blk_1680)

theorem neg_ok : negGridB a7Dat nGrid evalE parLit = true :=
  negGridB_of neg_pre
    (allLt_add (f := fun j => nGrid.row evalE j) (n := 1680) (m := 2) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1656) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1632) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1608) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1584) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1560) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1536) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1512) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1488) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1464) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1440) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1416) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1392) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1368) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1344) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1320) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1296) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1272) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1248) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1224) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1200) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1176) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1152) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1128) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1104) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1080) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1056) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1032) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 1008) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 984) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 960) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 936) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 912) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 888) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 864) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 840) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 816) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 792) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 768) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 744) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 720) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 696) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 672) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 648) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 624) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 600) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 576) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 552) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 528) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 504) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 480) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 456) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 432) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 408) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 384) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 360) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 336) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 312) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 288) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 264) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 240) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 216) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 192) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 168) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 144) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 120) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 96) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 72) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 48) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 24) (m := 24) (allLt_add (f := fun j => nGrid.row evalE j) (n := 0) (m := 24) (allLt_zero (fun j => nGrid.row evalE j)) n_blk_0) n_blk_24) n_blk_48) n_blk_72) n_blk_96) n_blk_120) n_blk_144) n_blk_168) n_blk_192) n_blk_216) n_blk_240) n_blk_264) n_blk_288) n_blk_312) n_blk_336) n_blk_360) n_blk_384) n_blk_408) n_blk_432) n_blk_456) n_blk_480) n_blk_504) n_blk_528) n_blk_552) n_blk_576) n_blk_600) n_blk_624) n_blk_648) n_blk_672) n_blk_696) n_blk_720) n_blk_744) n_blk_768) n_blk_792) n_blk_816) n_blk_840) n_blk_864) n_blk_888) n_blk_912) n_blk_936) n_blk_960) n_blk_984) n_blk_1008) n_blk_1032) n_blk_1056) n_blk_1080) n_blk_1104) n_blk_1128) n_blk_1152) n_blk_1176) n_blk_1200) n_blk_1224) n_blk_1248) n_blk_1272) n_blk_1296) n_blk_1320) n_blk_1344) n_blk_1368) n_blk_1392) n_blk_1416) n_blk_1440) n_blk_1464) n_blk_1488) n_blk_1512) n_blk_1536) n_blk_1560) n_blk_1584) n_blk_1608) n_blk_1632) n_blk_1656) n_blk_1680)

theorem k_ok : kRowB kGrid evalE parLit = true := kRowB_of k_pre k_row

theorem hess_ok : hessBI hessDat hIx = true :=
  hessBI_of hess_pre
    (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 150) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 149) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 148) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 147) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 146) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 145) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 144) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 143) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 142) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 141) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 140) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 139) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 138) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 137) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 136) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 135) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 134) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 133) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 132) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 131) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 130) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 129) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 128) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 127) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 126) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 125) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 124) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 123) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 122) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 121) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 120) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 119) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 118) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 117) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 116) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 115) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 114) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 113) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 112) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 111) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 110) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 109) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 108) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 107) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 106) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 105) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 104) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 103) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 102) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 101) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 100) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 99) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 98) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 97) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 96) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 95) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 94) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 93) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 92) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 91) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 90) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 89) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 88) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 87) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 86) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 85) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 84) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 83) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 82) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 81) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 80) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 79) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 78) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 77) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 76) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 75) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 74) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 73) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 72) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 71) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 70) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 69) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 68) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 67) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 66) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 65) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 64) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 63) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 62) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 61) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 60) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 59) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 58) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 57) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 56) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 55) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 54) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 53) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 52) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 51) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 50) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 49) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 48) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 47) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 46) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 45) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 44) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 43) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 42) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 41) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 40) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 39) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 38) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 37) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 36) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 35) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 34) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 33) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 32) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 31) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 30) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 29) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 28) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 27) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 26) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 25) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 24) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 23) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 22) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 21) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 20) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 19) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 18) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 17) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 16) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 15) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 14) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 13) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 12) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 11) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 10) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 9) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 8) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 7) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 6) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 5) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 4) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 3) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 2) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 1) (m := 1) (allLt_add (f := fun a => hessDat.rowI hIx a) (n := 0) (m := 1) (allLt_zero (fun a => hessDat.rowI hIx a)) h_blk_0) h_blk_1) h_blk_2) h_blk_3) h_blk_4) h_blk_5) h_blk_6) h_blk_7) h_blk_8) h_blk_9) h_blk_10) h_blk_11) h_blk_12) h_blk_13) h_blk_14) h_blk_15) h_blk_16) h_blk_17) h_blk_18) h_blk_19) h_blk_20) h_blk_21) h_blk_22) h_blk_23) h_blk_24) h_blk_25) h_blk_26) h_blk_27) h_blk_28) h_blk_29) h_blk_30) h_blk_31) h_blk_32) h_blk_33) h_blk_34) h_blk_35) h_blk_36) h_blk_37) h_blk_38) h_blk_39) h_blk_40) h_blk_41) h_blk_42) h_blk_43) h_blk_44) h_blk_45) h_blk_46) h_blk_47) h_blk_48) h_blk_49) h_blk_50) h_blk_51) h_blk_52) h_blk_53) h_blk_54) h_blk_55) h_blk_56) h_blk_57) h_blk_58) h_blk_59) h_blk_60) h_blk_61) h_blk_62) h_blk_63) h_blk_64) h_blk_65) h_blk_66) h_blk_67) h_blk_68) h_blk_69) h_blk_70) h_blk_71) h_blk_72) h_blk_73) h_blk_74) h_blk_75) h_blk_76) h_blk_77) h_blk_78) h_blk_79) h_blk_80) h_blk_81) h_blk_82) h_blk_83) h_blk_84) h_blk_85) h_blk_86) h_blk_87) h_blk_88) h_blk_89) h_blk_90) h_blk_91) h_blk_92) h_blk_93) h_blk_94) h_blk_95) h_blk_96) h_blk_97) h_blk_98) h_blk_99) h_blk_100) h_blk_101) h_blk_102) h_blk_103) h_blk_104) h_blk_105) h_blk_106) h_blk_107) h_blk_108) h_blk_109) h_blk_110) h_blk_111) h_blk_112) h_blk_113) h_blk_114) h_blk_115) h_blk_116) h_blk_117) h_blk_118) h_blk_119) h_blk_120) h_blk_121) h_blk_122) h_blk_123) h_blk_124) h_blk_125) h_blk_126) h_blk_127) h_blk_128) h_blk_129) h_blk_130) h_blk_131) h_blk_132) h_blk_133) h_blk_134) h_blk_135) h_blk_136) h_blk_137) h_blk_138) h_blk_139) h_blk_140) h_blk_141) h_blk_142) h_blk_143) h_blk_144) h_blk_145) h_blk_146) h_blk_147) h_blk_148) h_blk_149) h_blk_150)

theorem qcells_ok : allLt (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) qTbl.n = true :=
  (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3840) (m := 8) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3776) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3712) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3648) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3584) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3520) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3456) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3392) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3328) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3264) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3200) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3136) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3072) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 3008) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2944) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2880) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2816) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2752) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2688) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2624) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2560) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2496) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2432) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2368) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2304) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2240) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2176) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2112) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 2048) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1984) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1920) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1856) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1792) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1728) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1664) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1600) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1536) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1472) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1408) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1344) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1280) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1216) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1152) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1088) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 1024) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 960) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 896) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 832) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 768) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 704) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 640) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 576) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 512) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 448) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 384) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 320) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 256) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 192) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 128) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 64) (m := 64) (allLt_add (f := fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe) (n := 0) (m := 64) (allLt_zero (fun i => cellCheck (nodeAt i) (nodeAt (Nat.succ i)) (ctAt i) (ntAt i) (qCell i) qRf qRe)) qc_0) qc_64) qc_128) qc_192) qc_256) qc_320) qc_384) qc_448) qc_512) qc_576) qc_640) qc_704) qc_768) qc_832) qc_896) qc_960) qc_1024) qc_1088) qc_1152) qc_1216) qc_1280) qc_1344) qc_1408) qc_1472) qc_1536) qc_1600) qc_1664) qc_1728) qc_1792) qc_1856) qc_1920) qc_1984) qc_2048) qc_2112) qc_2176) qc_2240) qc_2304) qc_2368) qc_2432) qc_2496) qc_2560) qc_2624) qc_2688) qc_2752) qc_2816) qc_2880) qc_2944) qc_3008) qc_3072) qc_3136) qc_3200) qc_3264) qc_3328) qc_3392) qc_3456) qc_3520) qc_3584) qc_3648) qc_3712) qc_3776) qc_3840)

end SandierSerfaty.CertData.Box
