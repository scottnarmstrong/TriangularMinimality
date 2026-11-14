/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.S005
public import SandierSerfaty.CertData.Table.S006
public import SandierSerfaty.CertData.Table.S007
public import SandierSerfaty.CertData.Table.S008
public import SandierSerfaty.CertData.Table.S009
public import SandierSerfaty.CertData.Table.S010
public import SandierSerfaty.CertData.Table.S011
public import SandierSerfaty.CertData.Table.S012
public import SandierSerfaty.CertData.Table.S013
public import SandierSerfaty.CertData.Table.S014
public import SandierSerfaty.CertData.Table.S015
public import SandierSerfaty.CertData.Table.S016
public import SandierSerfaty.CertData.Table.S017
public import SandierSerfaty.CertData.Table.S018
public import SandierSerfaty.CertData.Table.S019
public import SandierSerfaty.CertData.Table.S020
public import SandierSerfaty.CertData.Table.S021
public import SandierSerfaty.CertData.Table.S022
public import SandierSerfaty.CertData.Table.S023
public import SandierSerfaty.CertData.Table.S024
public import SandierSerfaty.CertData.Table.S025
public import SandierSerfaty.CertData.Table.S026
public import SandierSerfaty.CertData.Table.S027
public import SandierSerfaty.CertData.Table.S028
public import SandierSerfaty.CertData.Table.S029
public import SandierSerfaty.Certificate.Assemble.Lists

/-!
# The chunks of segment 1, joined

The shard theorems of segment `1` joined into one statement over all its chunks (`Assemble.forall_lt_succ_of`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The check of the chunk `c` of segment `1`. -/
abbrev SegP1 (c : Nat) : Prop :=
  chunkB (chunkLenAt 1) dLit nodeAt ctAt ntAt ckAt 1 (knotCell 1 + chunkLenAt 1 * c) = true

/-- **All chunks of segment `1`** (364 chunks of 2 cells). -/
theorem seg1_chunks : ∀ c, c < chunkCnt 1 → SegP1 c := by
  have h0 : ∀ c, c < 0 → SegP1 c := forall_lt_zero'
  have h1 : ∀ c, c < 1 → SegP1 c := forall_lt_succ_of h0 chunk_784
  have h2 : ∀ c, c < 2 → SegP1 c := forall_lt_succ_of h1 chunk_786
  have h3 : ∀ c, c < 3 → SegP1 c := forall_lt_succ_of h2 chunk_788
  have h4 : ∀ c, c < 4 → SegP1 c := forall_lt_succ_of h3 chunk_790
  have h5 : ∀ c, c < 5 → SegP1 c := forall_lt_succ_of h4 chunk_792
  have h6 : ∀ c, c < 6 → SegP1 c := forall_lt_succ_of h5 chunk_794
  have h7 : ∀ c, c < 7 → SegP1 c := forall_lt_succ_of h6 chunk_796
  have h8 : ∀ c, c < 8 → SegP1 c := forall_lt_succ_of h7 chunk_798
  have h9 : ∀ c, c < 9 → SegP1 c := forall_lt_succ_of h8 chunk_800
  have h10 : ∀ c, c < 10 → SegP1 c := forall_lt_succ_of h9 chunk_802
  have h11 : ∀ c, c < 11 → SegP1 c := forall_lt_succ_of h10 chunk_804
  have h12 : ∀ c, c < 12 → SegP1 c := forall_lt_succ_of h11 chunk_806
  have h13 : ∀ c, c < 13 → SegP1 c := forall_lt_succ_of h12 chunk_808
  have h14 : ∀ c, c < 14 → SegP1 c := forall_lt_succ_of h13 chunk_810
  have h15 : ∀ c, c < 15 → SegP1 c := forall_lt_succ_of h14 chunk_812
  have h16 : ∀ c, c < 16 → SegP1 c := forall_lt_succ_of h15 chunk_814
  have h17 : ∀ c, c < 17 → SegP1 c := forall_lt_succ_of h16 chunk_816
  have h18 : ∀ c, c < 18 → SegP1 c := forall_lt_succ_of h17 chunk_818
  have h19 : ∀ c, c < 19 → SegP1 c := forall_lt_succ_of h18 chunk_820
  have h20 : ∀ c, c < 20 → SegP1 c := forall_lt_succ_of h19 chunk_822
  have h21 : ∀ c, c < 21 → SegP1 c := forall_lt_succ_of h20 chunk_824
  have h22 : ∀ c, c < 22 → SegP1 c := forall_lt_succ_of h21 chunk_826
  have h23 : ∀ c, c < 23 → SegP1 c := forall_lt_succ_of h22 chunk_828
  have h24 : ∀ c, c < 24 → SegP1 c := forall_lt_succ_of h23 chunk_830
  have h25 : ∀ c, c < 25 → SegP1 c := forall_lt_succ_of h24 chunk_832
  have h26 : ∀ c, c < 26 → SegP1 c := forall_lt_succ_of h25 chunk_834
  have h27 : ∀ c, c < 27 → SegP1 c := forall_lt_succ_of h26 chunk_836
  have h28 : ∀ c, c < 28 → SegP1 c := forall_lt_succ_of h27 chunk_838
  have h29 : ∀ c, c < 29 → SegP1 c := forall_lt_succ_of h28 chunk_840
  have h30 : ∀ c, c < 30 → SegP1 c := forall_lt_succ_of h29 chunk_842
  have h31 : ∀ c, c < 31 → SegP1 c := forall_lt_succ_of h30 chunk_844
  have h32 : ∀ c, c < 32 → SegP1 c := forall_lt_succ_of h31 chunk_846
  have h33 : ∀ c, c < 33 → SegP1 c := forall_lt_succ_of h32 chunk_848
  have h34 : ∀ c, c < 34 → SegP1 c := forall_lt_succ_of h33 chunk_850
  have h35 : ∀ c, c < 35 → SegP1 c := forall_lt_succ_of h34 chunk_852
  have h36 : ∀ c, c < 36 → SegP1 c := forall_lt_succ_of h35 chunk_854
  have h37 : ∀ c, c < 37 → SegP1 c := forall_lt_succ_of h36 chunk_856
  have h38 : ∀ c, c < 38 → SegP1 c := forall_lt_succ_of h37 chunk_858
  have h39 : ∀ c, c < 39 → SegP1 c := forall_lt_succ_of h38 chunk_860
  have h40 : ∀ c, c < 40 → SegP1 c := forall_lt_succ_of h39 chunk_862
  have h41 : ∀ c, c < 41 → SegP1 c := forall_lt_succ_of h40 chunk_864
  have h42 : ∀ c, c < 42 → SegP1 c := forall_lt_succ_of h41 chunk_866
  have h43 : ∀ c, c < 43 → SegP1 c := forall_lt_succ_of h42 chunk_868
  have h44 : ∀ c, c < 44 → SegP1 c := forall_lt_succ_of h43 chunk_870
  have h45 : ∀ c, c < 45 → SegP1 c := forall_lt_succ_of h44 chunk_872
  have h46 : ∀ c, c < 46 → SegP1 c := forall_lt_succ_of h45 chunk_874
  have h47 : ∀ c, c < 47 → SegP1 c := forall_lt_succ_of h46 chunk_876
  have h48 : ∀ c, c < 48 → SegP1 c := forall_lt_succ_of h47 chunk_878
  have h49 : ∀ c, c < 49 → SegP1 c := forall_lt_succ_of h48 chunk_880
  have h50 : ∀ c, c < 50 → SegP1 c := forall_lt_succ_of h49 chunk_882
  have h51 : ∀ c, c < 51 → SegP1 c := forall_lt_succ_of h50 chunk_884
  have h52 : ∀ c, c < 52 → SegP1 c := forall_lt_succ_of h51 chunk_886
  have h53 : ∀ c, c < 53 → SegP1 c := forall_lt_succ_of h52 chunk_888
  have h54 : ∀ c, c < 54 → SegP1 c := forall_lt_succ_of h53 chunk_890
  have h55 : ∀ c, c < 55 → SegP1 c := forall_lt_succ_of h54 chunk_892
  have h56 : ∀ c, c < 56 → SegP1 c := forall_lt_succ_of h55 chunk_894
  have h57 : ∀ c, c < 57 → SegP1 c := forall_lt_succ_of h56 chunk_896
  have h58 : ∀ c, c < 58 → SegP1 c := forall_lt_succ_of h57 chunk_898
  have h59 : ∀ c, c < 59 → SegP1 c := forall_lt_succ_of h58 chunk_900
  have h60 : ∀ c, c < 60 → SegP1 c := forall_lt_succ_of h59 chunk_902
  have h61 : ∀ c, c < 61 → SegP1 c := forall_lt_succ_of h60 chunk_904
  have h62 : ∀ c, c < 62 → SegP1 c := forall_lt_succ_of h61 chunk_906
  have h63 : ∀ c, c < 63 → SegP1 c := forall_lt_succ_of h62 chunk_908
  have h64 : ∀ c, c < 64 → SegP1 c := forall_lt_succ_of h63 chunk_910
  have h65 : ∀ c, c < 65 → SegP1 c := forall_lt_succ_of h64 chunk_912
  have h66 : ∀ c, c < 66 → SegP1 c := forall_lt_succ_of h65 chunk_914
  have h67 : ∀ c, c < 67 → SegP1 c := forall_lt_succ_of h66 chunk_916
  have h68 : ∀ c, c < 68 → SegP1 c := forall_lt_succ_of h67 chunk_918
  have h69 : ∀ c, c < 69 → SegP1 c := forall_lt_succ_of h68 chunk_920
  have h70 : ∀ c, c < 70 → SegP1 c := forall_lt_succ_of h69 chunk_922
  have h71 : ∀ c, c < 71 → SegP1 c := forall_lt_succ_of h70 chunk_924
  have h72 : ∀ c, c < 72 → SegP1 c := forall_lt_succ_of h71 chunk_926
  have h73 : ∀ c, c < 73 → SegP1 c := forall_lt_succ_of h72 chunk_928
  have h74 : ∀ c, c < 74 → SegP1 c := forall_lt_succ_of h73 chunk_930
  have h75 : ∀ c, c < 75 → SegP1 c := forall_lt_succ_of h74 chunk_932
  have h76 : ∀ c, c < 76 → SegP1 c := forall_lt_succ_of h75 chunk_934
  have h77 : ∀ c, c < 77 → SegP1 c := forall_lt_succ_of h76 chunk_936
  have h78 : ∀ c, c < 78 → SegP1 c := forall_lt_succ_of h77 chunk_938
  have h79 : ∀ c, c < 79 → SegP1 c := forall_lt_succ_of h78 chunk_940
  have h80 : ∀ c, c < 80 → SegP1 c := forall_lt_succ_of h79 chunk_942
  have h81 : ∀ c, c < 81 → SegP1 c := forall_lt_succ_of h80 chunk_944
  have h82 : ∀ c, c < 82 → SegP1 c := forall_lt_succ_of h81 chunk_946
  have h83 : ∀ c, c < 83 → SegP1 c := forall_lt_succ_of h82 chunk_948
  have h84 : ∀ c, c < 84 → SegP1 c := forall_lt_succ_of h83 chunk_950
  have h85 : ∀ c, c < 85 → SegP1 c := forall_lt_succ_of h84 chunk_952
  have h86 : ∀ c, c < 86 → SegP1 c := forall_lt_succ_of h85 chunk_954
  have h87 : ∀ c, c < 87 → SegP1 c := forall_lt_succ_of h86 chunk_956
  have h88 : ∀ c, c < 88 → SegP1 c := forall_lt_succ_of h87 chunk_958
  have h89 : ∀ c, c < 89 → SegP1 c := forall_lt_succ_of h88 chunk_960
  have h90 : ∀ c, c < 90 → SegP1 c := forall_lt_succ_of h89 chunk_962
  have h91 : ∀ c, c < 91 → SegP1 c := forall_lt_succ_of h90 chunk_964
  have h92 : ∀ c, c < 92 → SegP1 c := forall_lt_succ_of h91 chunk_966
  have h93 : ∀ c, c < 93 → SegP1 c := forall_lt_succ_of h92 chunk_968
  have h94 : ∀ c, c < 94 → SegP1 c := forall_lt_succ_of h93 chunk_970
  have h95 : ∀ c, c < 95 → SegP1 c := forall_lt_succ_of h94 chunk_972
  have h96 : ∀ c, c < 96 → SegP1 c := forall_lt_succ_of h95 chunk_974
  have h97 : ∀ c, c < 97 → SegP1 c := forall_lt_succ_of h96 chunk_976
  have h98 : ∀ c, c < 98 → SegP1 c := forall_lt_succ_of h97 chunk_978
  have h99 : ∀ c, c < 99 → SegP1 c := forall_lt_succ_of h98 chunk_980
  have h100 : ∀ c, c < 100 → SegP1 c := forall_lt_succ_of h99 chunk_982
  have h101 : ∀ c, c < 101 → SegP1 c := forall_lt_succ_of h100 chunk_984
  have h102 : ∀ c, c < 102 → SegP1 c := forall_lt_succ_of h101 chunk_986
  have h103 : ∀ c, c < 103 → SegP1 c := forall_lt_succ_of h102 chunk_988
  have h104 : ∀ c, c < 104 → SegP1 c := forall_lt_succ_of h103 chunk_990
  have h105 : ∀ c, c < 105 → SegP1 c := forall_lt_succ_of h104 chunk_992
  have h106 : ∀ c, c < 106 → SegP1 c := forall_lt_succ_of h105 chunk_994
  have h107 : ∀ c, c < 107 → SegP1 c := forall_lt_succ_of h106 chunk_996
  have h108 : ∀ c, c < 108 → SegP1 c := forall_lt_succ_of h107 chunk_998
  have h109 : ∀ c, c < 109 → SegP1 c := forall_lt_succ_of h108 chunk_1000
  have h110 : ∀ c, c < 110 → SegP1 c := forall_lt_succ_of h109 chunk_1002
  have h111 : ∀ c, c < 111 → SegP1 c := forall_lt_succ_of h110 chunk_1004
  have h112 : ∀ c, c < 112 → SegP1 c := forall_lt_succ_of h111 chunk_1006
  have h113 : ∀ c, c < 113 → SegP1 c := forall_lt_succ_of h112 chunk_1008
  have h114 : ∀ c, c < 114 → SegP1 c := forall_lt_succ_of h113 chunk_1010
  have h115 : ∀ c, c < 115 → SegP1 c := forall_lt_succ_of h114 chunk_1012
  have h116 : ∀ c, c < 116 → SegP1 c := forall_lt_succ_of h115 chunk_1014
  have h117 : ∀ c, c < 117 → SegP1 c := forall_lt_succ_of h116 chunk_1016
  have h118 : ∀ c, c < 118 → SegP1 c := forall_lt_succ_of h117 chunk_1018
  have h119 : ∀ c, c < 119 → SegP1 c := forall_lt_succ_of h118 chunk_1020
  have h120 : ∀ c, c < 120 → SegP1 c := forall_lt_succ_of h119 chunk_1022
  have h121 : ∀ c, c < 121 → SegP1 c := forall_lt_succ_of h120 chunk_1024
  have h122 : ∀ c, c < 122 → SegP1 c := forall_lt_succ_of h121 chunk_1026
  have h123 : ∀ c, c < 123 → SegP1 c := forall_lt_succ_of h122 chunk_1028
  have h124 : ∀ c, c < 124 → SegP1 c := forall_lt_succ_of h123 chunk_1030
  have h125 : ∀ c, c < 125 → SegP1 c := forall_lt_succ_of h124 chunk_1032
  have h126 : ∀ c, c < 126 → SegP1 c := forall_lt_succ_of h125 chunk_1034
  have h127 : ∀ c, c < 127 → SegP1 c := forall_lt_succ_of h126 chunk_1036
  have h128 : ∀ c, c < 128 → SegP1 c := forall_lt_succ_of h127 chunk_1038
  have h129 : ∀ c, c < 129 → SegP1 c := forall_lt_succ_of h128 chunk_1040
  have h130 : ∀ c, c < 130 → SegP1 c := forall_lt_succ_of h129 chunk_1042
  have h131 : ∀ c, c < 131 → SegP1 c := forall_lt_succ_of h130 chunk_1044
  have h132 : ∀ c, c < 132 → SegP1 c := forall_lt_succ_of h131 chunk_1046
  have h133 : ∀ c, c < 133 → SegP1 c := forall_lt_succ_of h132 chunk_1048
  have h134 : ∀ c, c < 134 → SegP1 c := forall_lt_succ_of h133 chunk_1050
  have h135 : ∀ c, c < 135 → SegP1 c := forall_lt_succ_of h134 chunk_1052
  have h136 : ∀ c, c < 136 → SegP1 c := forall_lt_succ_of h135 chunk_1054
  have h137 : ∀ c, c < 137 → SegP1 c := forall_lt_succ_of h136 chunk_1056
  have h138 : ∀ c, c < 138 → SegP1 c := forall_lt_succ_of h137 chunk_1058
  have h139 : ∀ c, c < 139 → SegP1 c := forall_lt_succ_of h138 chunk_1060
  have h140 : ∀ c, c < 140 → SegP1 c := forall_lt_succ_of h139 chunk_1062
  have h141 : ∀ c, c < 141 → SegP1 c := forall_lt_succ_of h140 chunk_1064
  have h142 : ∀ c, c < 142 → SegP1 c := forall_lt_succ_of h141 chunk_1066
  have h143 : ∀ c, c < 143 → SegP1 c := forall_lt_succ_of h142 chunk_1068
  have h144 : ∀ c, c < 144 → SegP1 c := forall_lt_succ_of h143 chunk_1070
  have h145 : ∀ c, c < 145 → SegP1 c := forall_lt_succ_of h144 chunk_1072
  have h146 : ∀ c, c < 146 → SegP1 c := forall_lt_succ_of h145 chunk_1074
  have h147 : ∀ c, c < 147 → SegP1 c := forall_lt_succ_of h146 chunk_1076
  have h148 : ∀ c, c < 148 → SegP1 c := forall_lt_succ_of h147 chunk_1078
  have h149 : ∀ c, c < 149 → SegP1 c := forall_lt_succ_of h148 chunk_1080
  have h150 : ∀ c, c < 150 → SegP1 c := forall_lt_succ_of h149 chunk_1082
  have h151 : ∀ c, c < 151 → SegP1 c := forall_lt_succ_of h150 chunk_1084
  have h152 : ∀ c, c < 152 → SegP1 c := forall_lt_succ_of h151 chunk_1086
  have h153 : ∀ c, c < 153 → SegP1 c := forall_lt_succ_of h152 chunk_1088
  have h154 : ∀ c, c < 154 → SegP1 c := forall_lt_succ_of h153 chunk_1090
  have h155 : ∀ c, c < 155 → SegP1 c := forall_lt_succ_of h154 chunk_1092
  have h156 : ∀ c, c < 156 → SegP1 c := forall_lt_succ_of h155 chunk_1094
  have h157 : ∀ c, c < 157 → SegP1 c := forall_lt_succ_of h156 chunk_1096
  have h158 : ∀ c, c < 158 → SegP1 c := forall_lt_succ_of h157 chunk_1098
  have h159 : ∀ c, c < 159 → SegP1 c := forall_lt_succ_of h158 chunk_1100
  have h160 : ∀ c, c < 160 → SegP1 c := forall_lt_succ_of h159 chunk_1102
  have h161 : ∀ c, c < 161 → SegP1 c := forall_lt_succ_of h160 chunk_1104
  have h162 : ∀ c, c < 162 → SegP1 c := forall_lt_succ_of h161 chunk_1106
  have h163 : ∀ c, c < 163 → SegP1 c := forall_lt_succ_of h162 chunk_1108
  have h164 : ∀ c, c < 164 → SegP1 c := forall_lt_succ_of h163 chunk_1110
  have h165 : ∀ c, c < 165 → SegP1 c := forall_lt_succ_of h164 chunk_1112
  have h166 : ∀ c, c < 166 → SegP1 c := forall_lt_succ_of h165 chunk_1114
  have h167 : ∀ c, c < 167 → SegP1 c := forall_lt_succ_of h166 chunk_1116
  have h168 : ∀ c, c < 168 → SegP1 c := forall_lt_succ_of h167 chunk_1118
  have h169 : ∀ c, c < 169 → SegP1 c := forall_lt_succ_of h168 chunk_1120
  have h170 : ∀ c, c < 170 → SegP1 c := forall_lt_succ_of h169 chunk_1122
  have h171 : ∀ c, c < 171 → SegP1 c := forall_lt_succ_of h170 chunk_1124
  have h172 : ∀ c, c < 172 → SegP1 c := forall_lt_succ_of h171 chunk_1126
  have h173 : ∀ c, c < 173 → SegP1 c := forall_lt_succ_of h172 chunk_1128
  have h174 : ∀ c, c < 174 → SegP1 c := forall_lt_succ_of h173 chunk_1130
  have h175 : ∀ c, c < 175 → SegP1 c := forall_lt_succ_of h174 chunk_1132
  have h176 : ∀ c, c < 176 → SegP1 c := forall_lt_succ_of h175 chunk_1134
  have h177 : ∀ c, c < 177 → SegP1 c := forall_lt_succ_of h176 chunk_1136
  have h178 : ∀ c, c < 178 → SegP1 c := forall_lt_succ_of h177 chunk_1138
  have h179 : ∀ c, c < 179 → SegP1 c := forall_lt_succ_of h178 chunk_1140
  have h180 : ∀ c, c < 180 → SegP1 c := forall_lt_succ_of h179 chunk_1142
  have h181 : ∀ c, c < 181 → SegP1 c := forall_lt_succ_of h180 chunk_1144
  have h182 : ∀ c, c < 182 → SegP1 c := forall_lt_succ_of h181 chunk_1146
  have h183 : ∀ c, c < 183 → SegP1 c := forall_lt_succ_of h182 chunk_1148
  have h184 : ∀ c, c < 184 → SegP1 c := forall_lt_succ_of h183 chunk_1150
  have h185 : ∀ c, c < 185 → SegP1 c := forall_lt_succ_of h184 chunk_1152
  have h186 : ∀ c, c < 186 → SegP1 c := forall_lt_succ_of h185 chunk_1154
  have h187 : ∀ c, c < 187 → SegP1 c := forall_lt_succ_of h186 chunk_1156
  have h188 : ∀ c, c < 188 → SegP1 c := forall_lt_succ_of h187 chunk_1158
  have h189 : ∀ c, c < 189 → SegP1 c := forall_lt_succ_of h188 chunk_1160
  have h190 : ∀ c, c < 190 → SegP1 c := forall_lt_succ_of h189 chunk_1162
  have h191 : ∀ c, c < 191 → SegP1 c := forall_lt_succ_of h190 chunk_1164
  have h192 : ∀ c, c < 192 → SegP1 c := forall_lt_succ_of h191 chunk_1166
  have h193 : ∀ c, c < 193 → SegP1 c := forall_lt_succ_of h192 chunk_1168
  have h194 : ∀ c, c < 194 → SegP1 c := forall_lt_succ_of h193 chunk_1170
  have h195 : ∀ c, c < 195 → SegP1 c := forall_lt_succ_of h194 chunk_1172
  have h196 : ∀ c, c < 196 → SegP1 c := forall_lt_succ_of h195 chunk_1174
  have h197 : ∀ c, c < 197 → SegP1 c := forall_lt_succ_of h196 chunk_1176
  have h198 : ∀ c, c < 198 → SegP1 c := forall_lt_succ_of h197 chunk_1178
  have h199 : ∀ c, c < 199 → SegP1 c := forall_lt_succ_of h198 chunk_1180
  have h200 : ∀ c, c < 200 → SegP1 c := forall_lt_succ_of h199 chunk_1182
  have h201 : ∀ c, c < 201 → SegP1 c := forall_lt_succ_of h200 chunk_1184
  have h202 : ∀ c, c < 202 → SegP1 c := forall_lt_succ_of h201 chunk_1186
  have h203 : ∀ c, c < 203 → SegP1 c := forall_lt_succ_of h202 chunk_1188
  have h204 : ∀ c, c < 204 → SegP1 c := forall_lt_succ_of h203 chunk_1190
  have h205 : ∀ c, c < 205 → SegP1 c := forall_lt_succ_of h204 chunk_1192
  have h206 : ∀ c, c < 206 → SegP1 c := forall_lt_succ_of h205 chunk_1194
  have h207 : ∀ c, c < 207 → SegP1 c := forall_lt_succ_of h206 chunk_1196
  have h208 : ∀ c, c < 208 → SegP1 c := forall_lt_succ_of h207 chunk_1198
  have h209 : ∀ c, c < 209 → SegP1 c := forall_lt_succ_of h208 chunk_1200
  have h210 : ∀ c, c < 210 → SegP1 c := forall_lt_succ_of h209 chunk_1202
  have h211 : ∀ c, c < 211 → SegP1 c := forall_lt_succ_of h210 chunk_1204
  have h212 : ∀ c, c < 212 → SegP1 c := forall_lt_succ_of h211 chunk_1206
  have h213 : ∀ c, c < 213 → SegP1 c := forall_lt_succ_of h212 chunk_1208
  have h214 : ∀ c, c < 214 → SegP1 c := forall_lt_succ_of h213 chunk_1210
  have h215 : ∀ c, c < 215 → SegP1 c := forall_lt_succ_of h214 chunk_1212
  have h216 : ∀ c, c < 216 → SegP1 c := forall_lt_succ_of h215 chunk_1214
  have h217 : ∀ c, c < 217 → SegP1 c := forall_lt_succ_of h216 chunk_1216
  have h218 : ∀ c, c < 218 → SegP1 c := forall_lt_succ_of h217 chunk_1218
  have h219 : ∀ c, c < 219 → SegP1 c := forall_lt_succ_of h218 chunk_1220
  have h220 : ∀ c, c < 220 → SegP1 c := forall_lt_succ_of h219 chunk_1222
  have h221 : ∀ c, c < 221 → SegP1 c := forall_lt_succ_of h220 chunk_1224
  have h222 : ∀ c, c < 222 → SegP1 c := forall_lt_succ_of h221 chunk_1226
  have h223 : ∀ c, c < 223 → SegP1 c := forall_lt_succ_of h222 chunk_1228
  have h224 : ∀ c, c < 224 → SegP1 c := forall_lt_succ_of h223 chunk_1230
  have h225 : ∀ c, c < 225 → SegP1 c := forall_lt_succ_of h224 chunk_1232
  have h226 : ∀ c, c < 226 → SegP1 c := forall_lt_succ_of h225 chunk_1234
  have h227 : ∀ c, c < 227 → SegP1 c := forall_lt_succ_of h226 chunk_1236
  have h228 : ∀ c, c < 228 → SegP1 c := forall_lt_succ_of h227 chunk_1238
  have h229 : ∀ c, c < 229 → SegP1 c := forall_lt_succ_of h228 chunk_1240
  have h230 : ∀ c, c < 230 → SegP1 c := forall_lt_succ_of h229 chunk_1242
  have h231 : ∀ c, c < 231 → SegP1 c := forall_lt_succ_of h230 chunk_1244
  have h232 : ∀ c, c < 232 → SegP1 c := forall_lt_succ_of h231 chunk_1246
  have h233 : ∀ c, c < 233 → SegP1 c := forall_lt_succ_of h232 chunk_1248
  have h234 : ∀ c, c < 234 → SegP1 c := forall_lt_succ_of h233 chunk_1250
  have h235 : ∀ c, c < 235 → SegP1 c := forall_lt_succ_of h234 chunk_1252
  have h236 : ∀ c, c < 236 → SegP1 c := forall_lt_succ_of h235 chunk_1254
  have h237 : ∀ c, c < 237 → SegP1 c := forall_lt_succ_of h236 chunk_1256
  have h238 : ∀ c, c < 238 → SegP1 c := forall_lt_succ_of h237 chunk_1258
  have h239 : ∀ c, c < 239 → SegP1 c := forall_lt_succ_of h238 chunk_1260
  have h240 : ∀ c, c < 240 → SegP1 c := forall_lt_succ_of h239 chunk_1262
  have h241 : ∀ c, c < 241 → SegP1 c := forall_lt_succ_of h240 chunk_1264
  have h242 : ∀ c, c < 242 → SegP1 c := forall_lt_succ_of h241 chunk_1266
  have h243 : ∀ c, c < 243 → SegP1 c := forall_lt_succ_of h242 chunk_1268
  have h244 : ∀ c, c < 244 → SegP1 c := forall_lt_succ_of h243 chunk_1270
  have h245 : ∀ c, c < 245 → SegP1 c := forall_lt_succ_of h244 chunk_1272
  have h246 : ∀ c, c < 246 → SegP1 c := forall_lt_succ_of h245 chunk_1274
  have h247 : ∀ c, c < 247 → SegP1 c := forall_lt_succ_of h246 chunk_1276
  have h248 : ∀ c, c < 248 → SegP1 c := forall_lt_succ_of h247 chunk_1278
  have h249 : ∀ c, c < 249 → SegP1 c := forall_lt_succ_of h248 chunk_1280
  have h250 : ∀ c, c < 250 → SegP1 c := forall_lt_succ_of h249 chunk_1282
  have h251 : ∀ c, c < 251 → SegP1 c := forall_lt_succ_of h250 chunk_1284
  have h252 : ∀ c, c < 252 → SegP1 c := forall_lt_succ_of h251 chunk_1286
  have h253 : ∀ c, c < 253 → SegP1 c := forall_lt_succ_of h252 chunk_1288
  have h254 : ∀ c, c < 254 → SegP1 c := forall_lt_succ_of h253 chunk_1290
  have h255 : ∀ c, c < 255 → SegP1 c := forall_lt_succ_of h254 chunk_1292
  have h256 : ∀ c, c < 256 → SegP1 c := forall_lt_succ_of h255 chunk_1294
  have h257 : ∀ c, c < 257 → SegP1 c := forall_lt_succ_of h256 chunk_1296
  have h258 : ∀ c, c < 258 → SegP1 c := forall_lt_succ_of h257 chunk_1298
  have h259 : ∀ c, c < 259 → SegP1 c := forall_lt_succ_of h258 chunk_1300
  have h260 : ∀ c, c < 260 → SegP1 c := forall_lt_succ_of h259 chunk_1302
  have h261 : ∀ c, c < 261 → SegP1 c := forall_lt_succ_of h260 chunk_1304
  have h262 : ∀ c, c < 262 → SegP1 c := forall_lt_succ_of h261 chunk_1306
  have h263 : ∀ c, c < 263 → SegP1 c := forall_lt_succ_of h262 chunk_1308
  have h264 : ∀ c, c < 264 → SegP1 c := forall_lt_succ_of h263 chunk_1310
  have h265 : ∀ c, c < 265 → SegP1 c := forall_lt_succ_of h264 chunk_1312
  have h266 : ∀ c, c < 266 → SegP1 c := forall_lt_succ_of h265 chunk_1314
  have h267 : ∀ c, c < 267 → SegP1 c := forall_lt_succ_of h266 chunk_1316
  have h268 : ∀ c, c < 268 → SegP1 c := forall_lt_succ_of h267 chunk_1318
  have h269 : ∀ c, c < 269 → SegP1 c := forall_lt_succ_of h268 chunk_1320
  have h270 : ∀ c, c < 270 → SegP1 c := forall_lt_succ_of h269 chunk_1322
  have h271 : ∀ c, c < 271 → SegP1 c := forall_lt_succ_of h270 chunk_1324
  have h272 : ∀ c, c < 272 → SegP1 c := forall_lt_succ_of h271 chunk_1326
  have h273 : ∀ c, c < 273 → SegP1 c := forall_lt_succ_of h272 chunk_1328
  have h274 : ∀ c, c < 274 → SegP1 c := forall_lt_succ_of h273 chunk_1330
  have h275 : ∀ c, c < 275 → SegP1 c := forall_lt_succ_of h274 chunk_1332
  have h276 : ∀ c, c < 276 → SegP1 c := forall_lt_succ_of h275 chunk_1334
  have h277 : ∀ c, c < 277 → SegP1 c := forall_lt_succ_of h276 chunk_1336
  have h278 : ∀ c, c < 278 → SegP1 c := forall_lt_succ_of h277 chunk_1338
  have h279 : ∀ c, c < 279 → SegP1 c := forall_lt_succ_of h278 chunk_1340
  have h280 : ∀ c, c < 280 → SegP1 c := forall_lt_succ_of h279 chunk_1342
  have h281 : ∀ c, c < 281 → SegP1 c := forall_lt_succ_of h280 chunk_1344
  have h282 : ∀ c, c < 282 → SegP1 c := forall_lt_succ_of h281 chunk_1346
  have h283 : ∀ c, c < 283 → SegP1 c := forall_lt_succ_of h282 chunk_1348
  have h284 : ∀ c, c < 284 → SegP1 c := forall_lt_succ_of h283 chunk_1350
  have h285 : ∀ c, c < 285 → SegP1 c := forall_lt_succ_of h284 chunk_1352
  have h286 : ∀ c, c < 286 → SegP1 c := forall_lt_succ_of h285 chunk_1354
  have h287 : ∀ c, c < 287 → SegP1 c := forall_lt_succ_of h286 chunk_1356
  have h288 : ∀ c, c < 288 → SegP1 c := forall_lt_succ_of h287 chunk_1358
  have h289 : ∀ c, c < 289 → SegP1 c := forall_lt_succ_of h288 chunk_1360
  have h290 : ∀ c, c < 290 → SegP1 c := forall_lt_succ_of h289 chunk_1362
  have h291 : ∀ c, c < 291 → SegP1 c := forall_lt_succ_of h290 chunk_1364
  have h292 : ∀ c, c < 292 → SegP1 c := forall_lt_succ_of h291 chunk_1366
  have h293 : ∀ c, c < 293 → SegP1 c := forall_lt_succ_of h292 chunk_1368
  have h294 : ∀ c, c < 294 → SegP1 c := forall_lt_succ_of h293 chunk_1370
  have h295 : ∀ c, c < 295 → SegP1 c := forall_lt_succ_of h294 chunk_1372
  have h296 : ∀ c, c < 296 → SegP1 c := forall_lt_succ_of h295 chunk_1374
  have h297 : ∀ c, c < 297 → SegP1 c := forall_lt_succ_of h296 chunk_1376
  have h298 : ∀ c, c < 298 → SegP1 c := forall_lt_succ_of h297 chunk_1378
  have h299 : ∀ c, c < 299 → SegP1 c := forall_lt_succ_of h298 chunk_1380
  have h300 : ∀ c, c < 300 → SegP1 c := forall_lt_succ_of h299 chunk_1382
  have h301 : ∀ c, c < 301 → SegP1 c := forall_lt_succ_of h300 chunk_1384
  have h302 : ∀ c, c < 302 → SegP1 c := forall_lt_succ_of h301 chunk_1386
  have h303 : ∀ c, c < 303 → SegP1 c := forall_lt_succ_of h302 chunk_1388
  have h304 : ∀ c, c < 304 → SegP1 c := forall_lt_succ_of h303 chunk_1390
  have h305 : ∀ c, c < 305 → SegP1 c := forall_lt_succ_of h304 chunk_1392
  have h306 : ∀ c, c < 306 → SegP1 c := forall_lt_succ_of h305 chunk_1394
  have h307 : ∀ c, c < 307 → SegP1 c := forall_lt_succ_of h306 chunk_1396
  have h308 : ∀ c, c < 308 → SegP1 c := forall_lt_succ_of h307 chunk_1398
  have h309 : ∀ c, c < 309 → SegP1 c := forall_lt_succ_of h308 chunk_1400
  have h310 : ∀ c, c < 310 → SegP1 c := forall_lt_succ_of h309 chunk_1402
  have h311 : ∀ c, c < 311 → SegP1 c := forall_lt_succ_of h310 chunk_1404
  have h312 : ∀ c, c < 312 → SegP1 c := forall_lt_succ_of h311 chunk_1406
  have h313 : ∀ c, c < 313 → SegP1 c := forall_lt_succ_of h312 chunk_1408
  have h314 : ∀ c, c < 314 → SegP1 c := forall_lt_succ_of h313 chunk_1410
  have h315 : ∀ c, c < 315 → SegP1 c := forall_lt_succ_of h314 chunk_1412
  have h316 : ∀ c, c < 316 → SegP1 c := forall_lt_succ_of h315 chunk_1414
  have h317 : ∀ c, c < 317 → SegP1 c := forall_lt_succ_of h316 chunk_1416
  have h318 : ∀ c, c < 318 → SegP1 c := forall_lt_succ_of h317 chunk_1418
  have h319 : ∀ c, c < 319 → SegP1 c := forall_lt_succ_of h318 chunk_1420
  have h320 : ∀ c, c < 320 → SegP1 c := forall_lt_succ_of h319 chunk_1422
  have h321 : ∀ c, c < 321 → SegP1 c := forall_lt_succ_of h320 chunk_1424
  have h322 : ∀ c, c < 322 → SegP1 c := forall_lt_succ_of h321 chunk_1426
  have h323 : ∀ c, c < 323 → SegP1 c := forall_lt_succ_of h322 chunk_1428
  have h324 : ∀ c, c < 324 → SegP1 c := forall_lt_succ_of h323 chunk_1430
  have h325 : ∀ c, c < 325 → SegP1 c := forall_lt_succ_of h324 chunk_1432
  have h326 : ∀ c, c < 326 → SegP1 c := forall_lt_succ_of h325 chunk_1434
  have h327 : ∀ c, c < 327 → SegP1 c := forall_lt_succ_of h326 chunk_1436
  have h328 : ∀ c, c < 328 → SegP1 c := forall_lt_succ_of h327 chunk_1438
  have h329 : ∀ c, c < 329 → SegP1 c := forall_lt_succ_of h328 chunk_1440
  have h330 : ∀ c, c < 330 → SegP1 c := forall_lt_succ_of h329 chunk_1442
  have h331 : ∀ c, c < 331 → SegP1 c := forall_lt_succ_of h330 chunk_1444
  have h332 : ∀ c, c < 332 → SegP1 c := forall_lt_succ_of h331 chunk_1446
  have h333 : ∀ c, c < 333 → SegP1 c := forall_lt_succ_of h332 chunk_1448
  have h334 : ∀ c, c < 334 → SegP1 c := forall_lt_succ_of h333 chunk_1450
  have h335 : ∀ c, c < 335 → SegP1 c := forall_lt_succ_of h334 chunk_1452
  have h336 : ∀ c, c < 336 → SegP1 c := forall_lt_succ_of h335 chunk_1454
  have h337 : ∀ c, c < 337 → SegP1 c := forall_lt_succ_of h336 chunk_1456
  have h338 : ∀ c, c < 338 → SegP1 c := forall_lt_succ_of h337 chunk_1458
  have h339 : ∀ c, c < 339 → SegP1 c := forall_lt_succ_of h338 chunk_1460
  have h340 : ∀ c, c < 340 → SegP1 c := forall_lt_succ_of h339 chunk_1462
  have h341 : ∀ c, c < 341 → SegP1 c := forall_lt_succ_of h340 chunk_1464
  have h342 : ∀ c, c < 342 → SegP1 c := forall_lt_succ_of h341 chunk_1466
  have h343 : ∀ c, c < 343 → SegP1 c := forall_lt_succ_of h342 chunk_1468
  have h344 : ∀ c, c < 344 → SegP1 c := forall_lt_succ_of h343 chunk_1470
  have h345 : ∀ c, c < 345 → SegP1 c := forall_lt_succ_of h344 chunk_1472
  have h346 : ∀ c, c < 346 → SegP1 c := forall_lt_succ_of h345 chunk_1474
  have h347 : ∀ c, c < 347 → SegP1 c := forall_lt_succ_of h346 chunk_1476
  have h348 : ∀ c, c < 348 → SegP1 c := forall_lt_succ_of h347 chunk_1478
  have h349 : ∀ c, c < 349 → SegP1 c := forall_lt_succ_of h348 chunk_1480
  have h350 : ∀ c, c < 350 → SegP1 c := forall_lt_succ_of h349 chunk_1482
  have h351 : ∀ c, c < 351 → SegP1 c := forall_lt_succ_of h350 chunk_1484
  have h352 : ∀ c, c < 352 → SegP1 c := forall_lt_succ_of h351 chunk_1486
  have h353 : ∀ c, c < 353 → SegP1 c := forall_lt_succ_of h352 chunk_1488
  have h354 : ∀ c, c < 354 → SegP1 c := forall_lt_succ_of h353 chunk_1490
  have h355 : ∀ c, c < 355 → SegP1 c := forall_lt_succ_of h354 chunk_1492
  have h356 : ∀ c, c < 356 → SegP1 c := forall_lt_succ_of h355 chunk_1494
  have h357 : ∀ c, c < 357 → SegP1 c := forall_lt_succ_of h356 chunk_1496
  have h358 : ∀ c, c < 358 → SegP1 c := forall_lt_succ_of h357 chunk_1498
  have h359 : ∀ c, c < 359 → SegP1 c := forall_lt_succ_of h358 chunk_1500
  have h360 : ∀ c, c < 360 → SegP1 c := forall_lt_succ_of h359 chunk_1502
  have h361 : ∀ c, c < 361 → SegP1 c := forall_lt_succ_of h360 chunk_1504
  have h362 : ∀ c, c < 362 → SegP1 c := forall_lt_succ_of h361 chunk_1506
  have h363 : ∀ c, c < 363 → SegP1 c := forall_lt_succ_of h362 chunk_1508
  have h364 : ∀ c, c < 364 → SegP1 c := forall_lt_succ_of h363 chunk_1510
  exact h364

end SandierSerfaty.CertData
