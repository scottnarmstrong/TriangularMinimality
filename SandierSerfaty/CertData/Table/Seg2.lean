/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.S030
public import SandierSerfaty.CertData.Table.S031
public import SandierSerfaty.CertData.Table.S032
public import SandierSerfaty.CertData.Table.S033
public import SandierSerfaty.CertData.Table.S034
public import SandierSerfaty.CertData.Table.S035
public import SandierSerfaty.CertData.Table.S036
public import SandierSerfaty.CertData.Table.S037
public import SandierSerfaty.CertData.Table.S038
public import SandierSerfaty.CertData.Table.S039
public import SandierSerfaty.CertData.Table.S040
public import SandierSerfaty.CertData.Table.S041
public import SandierSerfaty.CertData.Table.S042
public import SandierSerfaty.CertData.Table.S043
public import SandierSerfaty.CertData.Table.S044
public import SandierSerfaty.CertData.Table.S045
public import SandierSerfaty.CertData.Table.S046
public import SandierSerfaty.CertData.Table.S047
public import SandierSerfaty.CertData.Table.S048
public import SandierSerfaty.CertData.Table.S049
public import SandierSerfaty.CertData.Table.S050
public import SandierSerfaty.CertData.Table.S051
public import SandierSerfaty.CertData.Table.S052
public import SandierSerfaty.CertData.Table.S053
public import SandierSerfaty.CertData.Table.S054
public import SandierSerfaty.CertData.Table.S055
public import SandierSerfaty.CertData.Table.S056
public import SandierSerfaty.CertData.Table.S057
public import SandierSerfaty.CertData.Table.S058
public import SandierSerfaty.CertData.Table.S059
public import SandierSerfaty.CertData.Table.S060
public import SandierSerfaty.CertData.Table.S061
public import SandierSerfaty.CertData.Table.S062
public import SandierSerfaty.CertData.Table.S063
public import SandierSerfaty.CertData.Table.S064
public import SandierSerfaty.CertData.Table.S065
public import SandierSerfaty.CertData.Table.S066
public import SandierSerfaty.CertData.Table.S067
public import SandierSerfaty.CertData.Table.S068
public import SandierSerfaty.Certificate.Assemble.Lists

/-!
# The chunks of segment 2, joined

The shard theorems of segment `2` joined into one statement over all its chunks (`Assemble.forall_lt_succ_of`).
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The check of the chunk `c` of segment `2`. -/
abbrev SegP2 (c : Nat) : Prop :=
  chunkB (chunkLenAt 2) dLit nodeAt ctAt ntAt ckAt 2 (knotCell 2 + chunkLenAt 2 * c) = true

/-- **All chunks of segment `2`** (504 chunks of 1 cells). -/
theorem seg2_chunks : ∀ c, c < chunkCnt 2 → SegP2 c := by
  have h0 : ∀ c, c < 0 → SegP2 c := forall_lt_zero'
  have h1 : ∀ c, c < 1 → SegP2 c := forall_lt_succ_of h0 chunk_1512
  have h2 : ∀ c, c < 2 → SegP2 c := forall_lt_succ_of h1 chunk_1513
  have h3 : ∀ c, c < 3 → SegP2 c := forall_lt_succ_of h2 chunk_1514
  have h4 : ∀ c, c < 4 → SegP2 c := forall_lt_succ_of h3 chunk_1515
  have h5 : ∀ c, c < 5 → SegP2 c := forall_lt_succ_of h4 chunk_1516
  have h6 : ∀ c, c < 6 → SegP2 c := forall_lt_succ_of h5 chunk_1517
  have h7 : ∀ c, c < 7 → SegP2 c := forall_lt_succ_of h6 chunk_1518
  have h8 : ∀ c, c < 8 → SegP2 c := forall_lt_succ_of h7 chunk_1519
  have h9 : ∀ c, c < 9 → SegP2 c := forall_lt_succ_of h8 chunk_1520
  have h10 : ∀ c, c < 10 → SegP2 c := forall_lt_succ_of h9 chunk_1521
  have h11 : ∀ c, c < 11 → SegP2 c := forall_lt_succ_of h10 chunk_1522
  have h12 : ∀ c, c < 12 → SegP2 c := forall_lt_succ_of h11 chunk_1523
  have h13 : ∀ c, c < 13 → SegP2 c := forall_lt_succ_of h12 chunk_1524
  have h14 : ∀ c, c < 14 → SegP2 c := forall_lt_succ_of h13 chunk_1525
  have h15 : ∀ c, c < 15 → SegP2 c := forall_lt_succ_of h14 chunk_1526
  have h16 : ∀ c, c < 16 → SegP2 c := forall_lt_succ_of h15 chunk_1527
  have h17 : ∀ c, c < 17 → SegP2 c := forall_lt_succ_of h16 chunk_1528
  have h18 : ∀ c, c < 18 → SegP2 c := forall_lt_succ_of h17 chunk_1529
  have h19 : ∀ c, c < 19 → SegP2 c := forall_lt_succ_of h18 chunk_1530
  have h20 : ∀ c, c < 20 → SegP2 c := forall_lt_succ_of h19 chunk_1531
  have h21 : ∀ c, c < 21 → SegP2 c := forall_lt_succ_of h20 chunk_1532
  have h22 : ∀ c, c < 22 → SegP2 c := forall_lt_succ_of h21 chunk_1533
  have h23 : ∀ c, c < 23 → SegP2 c := forall_lt_succ_of h22 chunk_1534
  have h24 : ∀ c, c < 24 → SegP2 c := forall_lt_succ_of h23 chunk_1535
  have h25 : ∀ c, c < 25 → SegP2 c := forall_lt_succ_of h24 chunk_1536
  have h26 : ∀ c, c < 26 → SegP2 c := forall_lt_succ_of h25 chunk_1537
  have h27 : ∀ c, c < 27 → SegP2 c := forall_lt_succ_of h26 chunk_1538
  have h28 : ∀ c, c < 28 → SegP2 c := forall_lt_succ_of h27 chunk_1539
  have h29 : ∀ c, c < 29 → SegP2 c := forall_lt_succ_of h28 chunk_1540
  have h30 : ∀ c, c < 30 → SegP2 c := forall_lt_succ_of h29 chunk_1541
  have h31 : ∀ c, c < 31 → SegP2 c := forall_lt_succ_of h30 chunk_1542
  have h32 : ∀ c, c < 32 → SegP2 c := forall_lt_succ_of h31 chunk_1543
  have h33 : ∀ c, c < 33 → SegP2 c := forall_lt_succ_of h32 chunk_1544
  have h34 : ∀ c, c < 34 → SegP2 c := forall_lt_succ_of h33 chunk_1545
  have h35 : ∀ c, c < 35 → SegP2 c := forall_lt_succ_of h34 chunk_1546
  have h36 : ∀ c, c < 36 → SegP2 c := forall_lt_succ_of h35 chunk_1547
  have h37 : ∀ c, c < 37 → SegP2 c := forall_lt_succ_of h36 chunk_1548
  have h38 : ∀ c, c < 38 → SegP2 c := forall_lt_succ_of h37 chunk_1549
  have h39 : ∀ c, c < 39 → SegP2 c := forall_lt_succ_of h38 chunk_1550
  have h40 : ∀ c, c < 40 → SegP2 c := forall_lt_succ_of h39 chunk_1551
  have h41 : ∀ c, c < 41 → SegP2 c := forall_lt_succ_of h40 chunk_1552
  have h42 : ∀ c, c < 42 → SegP2 c := forall_lt_succ_of h41 chunk_1553
  have h43 : ∀ c, c < 43 → SegP2 c := forall_lt_succ_of h42 chunk_1554
  have h44 : ∀ c, c < 44 → SegP2 c := forall_lt_succ_of h43 chunk_1555
  have h45 : ∀ c, c < 45 → SegP2 c := forall_lt_succ_of h44 chunk_1556
  have h46 : ∀ c, c < 46 → SegP2 c := forall_lt_succ_of h45 chunk_1557
  have h47 : ∀ c, c < 47 → SegP2 c := forall_lt_succ_of h46 chunk_1558
  have h48 : ∀ c, c < 48 → SegP2 c := forall_lt_succ_of h47 chunk_1559
  have h49 : ∀ c, c < 49 → SegP2 c := forall_lt_succ_of h48 chunk_1560
  have h50 : ∀ c, c < 50 → SegP2 c := forall_lt_succ_of h49 chunk_1561
  have h51 : ∀ c, c < 51 → SegP2 c := forall_lt_succ_of h50 chunk_1562
  have h52 : ∀ c, c < 52 → SegP2 c := forall_lt_succ_of h51 chunk_1563
  have h53 : ∀ c, c < 53 → SegP2 c := forall_lt_succ_of h52 chunk_1564
  have h54 : ∀ c, c < 54 → SegP2 c := forall_lt_succ_of h53 chunk_1565
  have h55 : ∀ c, c < 55 → SegP2 c := forall_lt_succ_of h54 chunk_1566
  have h56 : ∀ c, c < 56 → SegP2 c := forall_lt_succ_of h55 chunk_1567
  have h57 : ∀ c, c < 57 → SegP2 c := forall_lt_succ_of h56 chunk_1568
  have h58 : ∀ c, c < 58 → SegP2 c := forall_lt_succ_of h57 chunk_1569
  have h59 : ∀ c, c < 59 → SegP2 c := forall_lt_succ_of h58 chunk_1570
  have h60 : ∀ c, c < 60 → SegP2 c := forall_lt_succ_of h59 chunk_1571
  have h61 : ∀ c, c < 61 → SegP2 c := forall_lt_succ_of h60 chunk_1572
  have h62 : ∀ c, c < 62 → SegP2 c := forall_lt_succ_of h61 chunk_1573
  have h63 : ∀ c, c < 63 → SegP2 c := forall_lt_succ_of h62 chunk_1574
  have h64 : ∀ c, c < 64 → SegP2 c := forall_lt_succ_of h63 chunk_1575
  have h65 : ∀ c, c < 65 → SegP2 c := forall_lt_succ_of h64 chunk_1576
  have h66 : ∀ c, c < 66 → SegP2 c := forall_lt_succ_of h65 chunk_1577
  have h67 : ∀ c, c < 67 → SegP2 c := forall_lt_succ_of h66 chunk_1578
  have h68 : ∀ c, c < 68 → SegP2 c := forall_lt_succ_of h67 chunk_1579
  have h69 : ∀ c, c < 69 → SegP2 c := forall_lt_succ_of h68 chunk_1580
  have h70 : ∀ c, c < 70 → SegP2 c := forall_lt_succ_of h69 chunk_1581
  have h71 : ∀ c, c < 71 → SegP2 c := forall_lt_succ_of h70 chunk_1582
  have h72 : ∀ c, c < 72 → SegP2 c := forall_lt_succ_of h71 chunk_1583
  have h73 : ∀ c, c < 73 → SegP2 c := forall_lt_succ_of h72 chunk_1584
  have h74 : ∀ c, c < 74 → SegP2 c := forall_lt_succ_of h73 chunk_1585
  have h75 : ∀ c, c < 75 → SegP2 c := forall_lt_succ_of h74 chunk_1586
  have h76 : ∀ c, c < 76 → SegP2 c := forall_lt_succ_of h75 chunk_1587
  have h77 : ∀ c, c < 77 → SegP2 c := forall_lt_succ_of h76 chunk_1588
  have h78 : ∀ c, c < 78 → SegP2 c := forall_lt_succ_of h77 chunk_1589
  have h79 : ∀ c, c < 79 → SegP2 c := forall_lt_succ_of h78 chunk_1590
  have h80 : ∀ c, c < 80 → SegP2 c := forall_lt_succ_of h79 chunk_1591
  have h81 : ∀ c, c < 81 → SegP2 c := forall_lt_succ_of h80 chunk_1592
  have h82 : ∀ c, c < 82 → SegP2 c := forall_lt_succ_of h81 chunk_1593
  have h83 : ∀ c, c < 83 → SegP2 c := forall_lt_succ_of h82 chunk_1594
  have h84 : ∀ c, c < 84 → SegP2 c := forall_lt_succ_of h83 chunk_1595
  have h85 : ∀ c, c < 85 → SegP2 c := forall_lt_succ_of h84 chunk_1596
  have h86 : ∀ c, c < 86 → SegP2 c := forall_lt_succ_of h85 chunk_1597
  have h87 : ∀ c, c < 87 → SegP2 c := forall_lt_succ_of h86 chunk_1598
  have h88 : ∀ c, c < 88 → SegP2 c := forall_lt_succ_of h87 chunk_1599
  have h89 : ∀ c, c < 89 → SegP2 c := forall_lt_succ_of h88 chunk_1600
  have h90 : ∀ c, c < 90 → SegP2 c := forall_lt_succ_of h89 chunk_1601
  have h91 : ∀ c, c < 91 → SegP2 c := forall_lt_succ_of h90 chunk_1602
  have h92 : ∀ c, c < 92 → SegP2 c := forall_lt_succ_of h91 chunk_1603
  have h93 : ∀ c, c < 93 → SegP2 c := forall_lt_succ_of h92 chunk_1604
  have h94 : ∀ c, c < 94 → SegP2 c := forall_lt_succ_of h93 chunk_1605
  have h95 : ∀ c, c < 95 → SegP2 c := forall_lt_succ_of h94 chunk_1606
  have h96 : ∀ c, c < 96 → SegP2 c := forall_lt_succ_of h95 chunk_1607
  have h97 : ∀ c, c < 97 → SegP2 c := forall_lt_succ_of h96 chunk_1608
  have h98 : ∀ c, c < 98 → SegP2 c := forall_lt_succ_of h97 chunk_1609
  have h99 : ∀ c, c < 99 → SegP2 c := forall_lt_succ_of h98 chunk_1610
  have h100 : ∀ c, c < 100 → SegP2 c := forall_lt_succ_of h99 chunk_1611
  have h101 : ∀ c, c < 101 → SegP2 c := forall_lt_succ_of h100 chunk_1612
  have h102 : ∀ c, c < 102 → SegP2 c := forall_lt_succ_of h101 chunk_1613
  have h103 : ∀ c, c < 103 → SegP2 c := forall_lt_succ_of h102 chunk_1614
  have h104 : ∀ c, c < 104 → SegP2 c := forall_lt_succ_of h103 chunk_1615
  have h105 : ∀ c, c < 105 → SegP2 c := forall_lt_succ_of h104 chunk_1616
  have h106 : ∀ c, c < 106 → SegP2 c := forall_lt_succ_of h105 chunk_1617
  have h107 : ∀ c, c < 107 → SegP2 c := forall_lt_succ_of h106 chunk_1618
  have h108 : ∀ c, c < 108 → SegP2 c := forall_lt_succ_of h107 chunk_1619
  have h109 : ∀ c, c < 109 → SegP2 c := forall_lt_succ_of h108 chunk_1620
  have h110 : ∀ c, c < 110 → SegP2 c := forall_lt_succ_of h109 chunk_1621
  have h111 : ∀ c, c < 111 → SegP2 c := forall_lt_succ_of h110 chunk_1622
  have h112 : ∀ c, c < 112 → SegP2 c := forall_lt_succ_of h111 chunk_1623
  have h113 : ∀ c, c < 113 → SegP2 c := forall_lt_succ_of h112 chunk_1624
  have h114 : ∀ c, c < 114 → SegP2 c := forall_lt_succ_of h113 chunk_1625
  have h115 : ∀ c, c < 115 → SegP2 c := forall_lt_succ_of h114 chunk_1626
  have h116 : ∀ c, c < 116 → SegP2 c := forall_lt_succ_of h115 chunk_1627
  have h117 : ∀ c, c < 117 → SegP2 c := forall_lt_succ_of h116 chunk_1628
  have h118 : ∀ c, c < 118 → SegP2 c := forall_lt_succ_of h117 chunk_1629
  have h119 : ∀ c, c < 119 → SegP2 c := forall_lt_succ_of h118 chunk_1630
  have h120 : ∀ c, c < 120 → SegP2 c := forall_lt_succ_of h119 chunk_1631
  have h121 : ∀ c, c < 121 → SegP2 c := forall_lt_succ_of h120 chunk_1632
  have h122 : ∀ c, c < 122 → SegP2 c := forall_lt_succ_of h121 chunk_1633
  have h123 : ∀ c, c < 123 → SegP2 c := forall_lt_succ_of h122 chunk_1634
  have h124 : ∀ c, c < 124 → SegP2 c := forall_lt_succ_of h123 chunk_1635
  have h125 : ∀ c, c < 125 → SegP2 c := forall_lt_succ_of h124 chunk_1636
  have h126 : ∀ c, c < 126 → SegP2 c := forall_lt_succ_of h125 chunk_1637
  have h127 : ∀ c, c < 127 → SegP2 c := forall_lt_succ_of h126 chunk_1638
  have h128 : ∀ c, c < 128 → SegP2 c := forall_lt_succ_of h127 chunk_1639
  have h129 : ∀ c, c < 129 → SegP2 c := forall_lt_succ_of h128 chunk_1640
  have h130 : ∀ c, c < 130 → SegP2 c := forall_lt_succ_of h129 chunk_1641
  have h131 : ∀ c, c < 131 → SegP2 c := forall_lt_succ_of h130 chunk_1642
  have h132 : ∀ c, c < 132 → SegP2 c := forall_lt_succ_of h131 chunk_1643
  have h133 : ∀ c, c < 133 → SegP2 c := forall_lt_succ_of h132 chunk_1644
  have h134 : ∀ c, c < 134 → SegP2 c := forall_lt_succ_of h133 chunk_1645
  have h135 : ∀ c, c < 135 → SegP2 c := forall_lt_succ_of h134 chunk_1646
  have h136 : ∀ c, c < 136 → SegP2 c := forall_lt_succ_of h135 chunk_1647
  have h137 : ∀ c, c < 137 → SegP2 c := forall_lt_succ_of h136 chunk_1648
  have h138 : ∀ c, c < 138 → SegP2 c := forall_lt_succ_of h137 chunk_1649
  have h139 : ∀ c, c < 139 → SegP2 c := forall_lt_succ_of h138 chunk_1650
  have h140 : ∀ c, c < 140 → SegP2 c := forall_lt_succ_of h139 chunk_1651
  have h141 : ∀ c, c < 141 → SegP2 c := forall_lt_succ_of h140 chunk_1652
  have h142 : ∀ c, c < 142 → SegP2 c := forall_lt_succ_of h141 chunk_1653
  have h143 : ∀ c, c < 143 → SegP2 c := forall_lt_succ_of h142 chunk_1654
  have h144 : ∀ c, c < 144 → SegP2 c := forall_lt_succ_of h143 chunk_1655
  have h145 : ∀ c, c < 145 → SegP2 c := forall_lt_succ_of h144 chunk_1656
  have h146 : ∀ c, c < 146 → SegP2 c := forall_lt_succ_of h145 chunk_1657
  have h147 : ∀ c, c < 147 → SegP2 c := forall_lt_succ_of h146 chunk_1658
  have h148 : ∀ c, c < 148 → SegP2 c := forall_lt_succ_of h147 chunk_1659
  have h149 : ∀ c, c < 149 → SegP2 c := forall_lt_succ_of h148 chunk_1660
  have h150 : ∀ c, c < 150 → SegP2 c := forall_lt_succ_of h149 chunk_1661
  have h151 : ∀ c, c < 151 → SegP2 c := forall_lt_succ_of h150 chunk_1662
  have h152 : ∀ c, c < 152 → SegP2 c := forall_lt_succ_of h151 chunk_1663
  have h153 : ∀ c, c < 153 → SegP2 c := forall_lt_succ_of h152 chunk_1664
  have h154 : ∀ c, c < 154 → SegP2 c := forall_lt_succ_of h153 chunk_1665
  have h155 : ∀ c, c < 155 → SegP2 c := forall_lt_succ_of h154 chunk_1666
  have h156 : ∀ c, c < 156 → SegP2 c := forall_lt_succ_of h155 chunk_1667
  have h157 : ∀ c, c < 157 → SegP2 c := forall_lt_succ_of h156 chunk_1668
  have h158 : ∀ c, c < 158 → SegP2 c := forall_lt_succ_of h157 chunk_1669
  have h159 : ∀ c, c < 159 → SegP2 c := forall_lt_succ_of h158 chunk_1670
  have h160 : ∀ c, c < 160 → SegP2 c := forall_lt_succ_of h159 chunk_1671
  have h161 : ∀ c, c < 161 → SegP2 c := forall_lt_succ_of h160 chunk_1672
  have h162 : ∀ c, c < 162 → SegP2 c := forall_lt_succ_of h161 chunk_1673
  have h163 : ∀ c, c < 163 → SegP2 c := forall_lt_succ_of h162 chunk_1674
  have h164 : ∀ c, c < 164 → SegP2 c := forall_lt_succ_of h163 chunk_1675
  have h165 : ∀ c, c < 165 → SegP2 c := forall_lt_succ_of h164 chunk_1676
  have h166 : ∀ c, c < 166 → SegP2 c := forall_lt_succ_of h165 chunk_1677
  have h167 : ∀ c, c < 167 → SegP2 c := forall_lt_succ_of h166 chunk_1678
  have h168 : ∀ c, c < 168 → SegP2 c := forall_lt_succ_of h167 chunk_1679
  have h169 : ∀ c, c < 169 → SegP2 c := forall_lt_succ_of h168 chunk_1680
  have h170 : ∀ c, c < 170 → SegP2 c := forall_lt_succ_of h169 chunk_1681
  have h171 : ∀ c, c < 171 → SegP2 c := forall_lt_succ_of h170 chunk_1682
  have h172 : ∀ c, c < 172 → SegP2 c := forall_lt_succ_of h171 chunk_1683
  have h173 : ∀ c, c < 173 → SegP2 c := forall_lt_succ_of h172 chunk_1684
  have h174 : ∀ c, c < 174 → SegP2 c := forall_lt_succ_of h173 chunk_1685
  have h175 : ∀ c, c < 175 → SegP2 c := forall_lt_succ_of h174 chunk_1686
  have h176 : ∀ c, c < 176 → SegP2 c := forall_lt_succ_of h175 chunk_1687
  have h177 : ∀ c, c < 177 → SegP2 c := forall_lt_succ_of h176 chunk_1688
  have h178 : ∀ c, c < 178 → SegP2 c := forall_lt_succ_of h177 chunk_1689
  have h179 : ∀ c, c < 179 → SegP2 c := forall_lt_succ_of h178 chunk_1690
  have h180 : ∀ c, c < 180 → SegP2 c := forall_lt_succ_of h179 chunk_1691
  have h181 : ∀ c, c < 181 → SegP2 c := forall_lt_succ_of h180 chunk_1692
  have h182 : ∀ c, c < 182 → SegP2 c := forall_lt_succ_of h181 chunk_1693
  have h183 : ∀ c, c < 183 → SegP2 c := forall_lt_succ_of h182 chunk_1694
  have h184 : ∀ c, c < 184 → SegP2 c := forall_lt_succ_of h183 chunk_1695
  have h185 : ∀ c, c < 185 → SegP2 c := forall_lt_succ_of h184 chunk_1696
  have h186 : ∀ c, c < 186 → SegP2 c := forall_lt_succ_of h185 chunk_1697
  have h187 : ∀ c, c < 187 → SegP2 c := forall_lt_succ_of h186 chunk_1698
  have h188 : ∀ c, c < 188 → SegP2 c := forall_lt_succ_of h187 chunk_1699
  have h189 : ∀ c, c < 189 → SegP2 c := forall_lt_succ_of h188 chunk_1700
  have h190 : ∀ c, c < 190 → SegP2 c := forall_lt_succ_of h189 chunk_1701
  have h191 : ∀ c, c < 191 → SegP2 c := forall_lt_succ_of h190 chunk_1702
  have h192 : ∀ c, c < 192 → SegP2 c := forall_lt_succ_of h191 chunk_1703
  have h193 : ∀ c, c < 193 → SegP2 c := forall_lt_succ_of h192 chunk_1704
  have h194 : ∀ c, c < 194 → SegP2 c := forall_lt_succ_of h193 chunk_1705
  have h195 : ∀ c, c < 195 → SegP2 c := forall_lt_succ_of h194 chunk_1706
  have h196 : ∀ c, c < 196 → SegP2 c := forall_lt_succ_of h195 chunk_1707
  have h197 : ∀ c, c < 197 → SegP2 c := forall_lt_succ_of h196 chunk_1708
  have h198 : ∀ c, c < 198 → SegP2 c := forall_lt_succ_of h197 chunk_1709
  have h199 : ∀ c, c < 199 → SegP2 c := forall_lt_succ_of h198 chunk_1710
  have h200 : ∀ c, c < 200 → SegP2 c := forall_lt_succ_of h199 chunk_1711
  have h201 : ∀ c, c < 201 → SegP2 c := forall_lt_succ_of h200 chunk_1712
  have h202 : ∀ c, c < 202 → SegP2 c := forall_lt_succ_of h201 chunk_1713
  have h203 : ∀ c, c < 203 → SegP2 c := forall_lt_succ_of h202 chunk_1714
  have h204 : ∀ c, c < 204 → SegP2 c := forall_lt_succ_of h203 chunk_1715
  have h205 : ∀ c, c < 205 → SegP2 c := forall_lt_succ_of h204 chunk_1716
  have h206 : ∀ c, c < 206 → SegP2 c := forall_lt_succ_of h205 chunk_1717
  have h207 : ∀ c, c < 207 → SegP2 c := forall_lt_succ_of h206 chunk_1718
  have h208 : ∀ c, c < 208 → SegP2 c := forall_lt_succ_of h207 chunk_1719
  have h209 : ∀ c, c < 209 → SegP2 c := forall_lt_succ_of h208 chunk_1720
  have h210 : ∀ c, c < 210 → SegP2 c := forall_lt_succ_of h209 chunk_1721
  have h211 : ∀ c, c < 211 → SegP2 c := forall_lt_succ_of h210 chunk_1722
  have h212 : ∀ c, c < 212 → SegP2 c := forall_lt_succ_of h211 chunk_1723
  have h213 : ∀ c, c < 213 → SegP2 c := forall_lt_succ_of h212 chunk_1724
  have h214 : ∀ c, c < 214 → SegP2 c := forall_lt_succ_of h213 chunk_1725
  have h215 : ∀ c, c < 215 → SegP2 c := forall_lt_succ_of h214 chunk_1726
  have h216 : ∀ c, c < 216 → SegP2 c := forall_lt_succ_of h215 chunk_1727
  have h217 : ∀ c, c < 217 → SegP2 c := forall_lt_succ_of h216 chunk_1728
  have h218 : ∀ c, c < 218 → SegP2 c := forall_lt_succ_of h217 chunk_1729
  have h219 : ∀ c, c < 219 → SegP2 c := forall_lt_succ_of h218 chunk_1730
  have h220 : ∀ c, c < 220 → SegP2 c := forall_lt_succ_of h219 chunk_1731
  have h221 : ∀ c, c < 221 → SegP2 c := forall_lt_succ_of h220 chunk_1732
  have h222 : ∀ c, c < 222 → SegP2 c := forall_lt_succ_of h221 chunk_1733
  have h223 : ∀ c, c < 223 → SegP2 c := forall_lt_succ_of h222 chunk_1734
  have h224 : ∀ c, c < 224 → SegP2 c := forall_lt_succ_of h223 chunk_1735
  have h225 : ∀ c, c < 225 → SegP2 c := forall_lt_succ_of h224 chunk_1736
  have h226 : ∀ c, c < 226 → SegP2 c := forall_lt_succ_of h225 chunk_1737
  have h227 : ∀ c, c < 227 → SegP2 c := forall_lt_succ_of h226 chunk_1738
  have h228 : ∀ c, c < 228 → SegP2 c := forall_lt_succ_of h227 chunk_1739
  have h229 : ∀ c, c < 229 → SegP2 c := forall_lt_succ_of h228 chunk_1740
  have h230 : ∀ c, c < 230 → SegP2 c := forall_lt_succ_of h229 chunk_1741
  have h231 : ∀ c, c < 231 → SegP2 c := forall_lt_succ_of h230 chunk_1742
  have h232 : ∀ c, c < 232 → SegP2 c := forall_lt_succ_of h231 chunk_1743
  have h233 : ∀ c, c < 233 → SegP2 c := forall_lt_succ_of h232 chunk_1744
  have h234 : ∀ c, c < 234 → SegP2 c := forall_lt_succ_of h233 chunk_1745
  have h235 : ∀ c, c < 235 → SegP2 c := forall_lt_succ_of h234 chunk_1746
  have h236 : ∀ c, c < 236 → SegP2 c := forall_lt_succ_of h235 chunk_1747
  have h237 : ∀ c, c < 237 → SegP2 c := forall_lt_succ_of h236 chunk_1748
  have h238 : ∀ c, c < 238 → SegP2 c := forall_lt_succ_of h237 chunk_1749
  have h239 : ∀ c, c < 239 → SegP2 c := forall_lt_succ_of h238 chunk_1750
  have h240 : ∀ c, c < 240 → SegP2 c := forall_lt_succ_of h239 chunk_1751
  have h241 : ∀ c, c < 241 → SegP2 c := forall_lt_succ_of h240 chunk_1752
  have h242 : ∀ c, c < 242 → SegP2 c := forall_lt_succ_of h241 chunk_1753
  have h243 : ∀ c, c < 243 → SegP2 c := forall_lt_succ_of h242 chunk_1754
  have h244 : ∀ c, c < 244 → SegP2 c := forall_lt_succ_of h243 chunk_1755
  have h245 : ∀ c, c < 245 → SegP2 c := forall_lt_succ_of h244 chunk_1756
  have h246 : ∀ c, c < 246 → SegP2 c := forall_lt_succ_of h245 chunk_1757
  have h247 : ∀ c, c < 247 → SegP2 c := forall_lt_succ_of h246 chunk_1758
  have h248 : ∀ c, c < 248 → SegP2 c := forall_lt_succ_of h247 chunk_1759
  have h249 : ∀ c, c < 249 → SegP2 c := forall_lt_succ_of h248 chunk_1760
  have h250 : ∀ c, c < 250 → SegP2 c := forall_lt_succ_of h249 chunk_1761
  have h251 : ∀ c, c < 251 → SegP2 c := forall_lt_succ_of h250 chunk_1762
  have h252 : ∀ c, c < 252 → SegP2 c := forall_lt_succ_of h251 chunk_1763
  have h253 : ∀ c, c < 253 → SegP2 c := forall_lt_succ_of h252 chunk_1764
  have h254 : ∀ c, c < 254 → SegP2 c := forall_lt_succ_of h253 chunk_1765
  have h255 : ∀ c, c < 255 → SegP2 c := forall_lt_succ_of h254 chunk_1766
  have h256 : ∀ c, c < 256 → SegP2 c := forall_lt_succ_of h255 chunk_1767
  have h257 : ∀ c, c < 257 → SegP2 c := forall_lt_succ_of h256 chunk_1768
  have h258 : ∀ c, c < 258 → SegP2 c := forall_lt_succ_of h257 chunk_1769
  have h259 : ∀ c, c < 259 → SegP2 c := forall_lt_succ_of h258 chunk_1770
  have h260 : ∀ c, c < 260 → SegP2 c := forall_lt_succ_of h259 chunk_1771
  have h261 : ∀ c, c < 261 → SegP2 c := forall_lt_succ_of h260 chunk_1772
  have h262 : ∀ c, c < 262 → SegP2 c := forall_lt_succ_of h261 chunk_1773
  have h263 : ∀ c, c < 263 → SegP2 c := forall_lt_succ_of h262 chunk_1774
  have h264 : ∀ c, c < 264 → SegP2 c := forall_lt_succ_of h263 chunk_1775
  have h265 : ∀ c, c < 265 → SegP2 c := forall_lt_succ_of h264 chunk_1776
  have h266 : ∀ c, c < 266 → SegP2 c := forall_lt_succ_of h265 chunk_1777
  have h267 : ∀ c, c < 267 → SegP2 c := forall_lt_succ_of h266 chunk_1778
  have h268 : ∀ c, c < 268 → SegP2 c := forall_lt_succ_of h267 chunk_1779
  have h269 : ∀ c, c < 269 → SegP2 c := forall_lt_succ_of h268 chunk_1780
  have h270 : ∀ c, c < 270 → SegP2 c := forall_lt_succ_of h269 chunk_1781
  have h271 : ∀ c, c < 271 → SegP2 c := forall_lt_succ_of h270 chunk_1782
  have h272 : ∀ c, c < 272 → SegP2 c := forall_lt_succ_of h271 chunk_1783
  have h273 : ∀ c, c < 273 → SegP2 c := forall_lt_succ_of h272 chunk_1784
  have h274 : ∀ c, c < 274 → SegP2 c := forall_lt_succ_of h273 chunk_1785
  have h275 : ∀ c, c < 275 → SegP2 c := forall_lt_succ_of h274 chunk_1786
  have h276 : ∀ c, c < 276 → SegP2 c := forall_lt_succ_of h275 chunk_1787
  have h277 : ∀ c, c < 277 → SegP2 c := forall_lt_succ_of h276 chunk_1788
  have h278 : ∀ c, c < 278 → SegP2 c := forall_lt_succ_of h277 chunk_1789
  have h279 : ∀ c, c < 279 → SegP2 c := forall_lt_succ_of h278 chunk_1790
  have h280 : ∀ c, c < 280 → SegP2 c := forall_lt_succ_of h279 chunk_1791
  have h281 : ∀ c, c < 281 → SegP2 c := forall_lt_succ_of h280 chunk_1792
  have h282 : ∀ c, c < 282 → SegP2 c := forall_lt_succ_of h281 chunk_1793
  have h283 : ∀ c, c < 283 → SegP2 c := forall_lt_succ_of h282 chunk_1794
  have h284 : ∀ c, c < 284 → SegP2 c := forall_lt_succ_of h283 chunk_1795
  have h285 : ∀ c, c < 285 → SegP2 c := forall_lt_succ_of h284 chunk_1796
  have h286 : ∀ c, c < 286 → SegP2 c := forall_lt_succ_of h285 chunk_1797
  have h287 : ∀ c, c < 287 → SegP2 c := forall_lt_succ_of h286 chunk_1798
  have h288 : ∀ c, c < 288 → SegP2 c := forall_lt_succ_of h287 chunk_1799
  have h289 : ∀ c, c < 289 → SegP2 c := forall_lt_succ_of h288 chunk_1800
  have h290 : ∀ c, c < 290 → SegP2 c := forall_lt_succ_of h289 chunk_1801
  have h291 : ∀ c, c < 291 → SegP2 c := forall_lt_succ_of h290 chunk_1802
  have h292 : ∀ c, c < 292 → SegP2 c := forall_lt_succ_of h291 chunk_1803
  have h293 : ∀ c, c < 293 → SegP2 c := forall_lt_succ_of h292 chunk_1804
  have h294 : ∀ c, c < 294 → SegP2 c := forall_lt_succ_of h293 chunk_1805
  have h295 : ∀ c, c < 295 → SegP2 c := forall_lt_succ_of h294 chunk_1806
  have h296 : ∀ c, c < 296 → SegP2 c := forall_lt_succ_of h295 chunk_1807
  have h297 : ∀ c, c < 297 → SegP2 c := forall_lt_succ_of h296 chunk_1808
  have h298 : ∀ c, c < 298 → SegP2 c := forall_lt_succ_of h297 chunk_1809
  have h299 : ∀ c, c < 299 → SegP2 c := forall_lt_succ_of h298 chunk_1810
  have h300 : ∀ c, c < 300 → SegP2 c := forall_lt_succ_of h299 chunk_1811
  have h301 : ∀ c, c < 301 → SegP2 c := forall_lt_succ_of h300 chunk_1812
  have h302 : ∀ c, c < 302 → SegP2 c := forall_lt_succ_of h301 chunk_1813
  have h303 : ∀ c, c < 303 → SegP2 c := forall_lt_succ_of h302 chunk_1814
  have h304 : ∀ c, c < 304 → SegP2 c := forall_lt_succ_of h303 chunk_1815
  have h305 : ∀ c, c < 305 → SegP2 c := forall_lt_succ_of h304 chunk_1816
  have h306 : ∀ c, c < 306 → SegP2 c := forall_lt_succ_of h305 chunk_1817
  have h307 : ∀ c, c < 307 → SegP2 c := forall_lt_succ_of h306 chunk_1818
  have h308 : ∀ c, c < 308 → SegP2 c := forall_lt_succ_of h307 chunk_1819
  have h309 : ∀ c, c < 309 → SegP2 c := forall_lt_succ_of h308 chunk_1820
  have h310 : ∀ c, c < 310 → SegP2 c := forall_lt_succ_of h309 chunk_1821
  have h311 : ∀ c, c < 311 → SegP2 c := forall_lt_succ_of h310 chunk_1822
  have h312 : ∀ c, c < 312 → SegP2 c := forall_lt_succ_of h311 chunk_1823
  have h313 : ∀ c, c < 313 → SegP2 c := forall_lt_succ_of h312 chunk_1824
  have h314 : ∀ c, c < 314 → SegP2 c := forall_lt_succ_of h313 chunk_1825
  have h315 : ∀ c, c < 315 → SegP2 c := forall_lt_succ_of h314 chunk_1826
  have h316 : ∀ c, c < 316 → SegP2 c := forall_lt_succ_of h315 chunk_1827
  have h317 : ∀ c, c < 317 → SegP2 c := forall_lt_succ_of h316 chunk_1828
  have h318 : ∀ c, c < 318 → SegP2 c := forall_lt_succ_of h317 chunk_1829
  have h319 : ∀ c, c < 319 → SegP2 c := forall_lt_succ_of h318 chunk_1830
  have h320 : ∀ c, c < 320 → SegP2 c := forall_lt_succ_of h319 chunk_1831
  have h321 : ∀ c, c < 321 → SegP2 c := forall_lt_succ_of h320 chunk_1832
  have h322 : ∀ c, c < 322 → SegP2 c := forall_lt_succ_of h321 chunk_1833
  have h323 : ∀ c, c < 323 → SegP2 c := forall_lt_succ_of h322 chunk_1834
  have h324 : ∀ c, c < 324 → SegP2 c := forall_lt_succ_of h323 chunk_1835
  have h325 : ∀ c, c < 325 → SegP2 c := forall_lt_succ_of h324 chunk_1836
  have h326 : ∀ c, c < 326 → SegP2 c := forall_lt_succ_of h325 chunk_1837
  have h327 : ∀ c, c < 327 → SegP2 c := forall_lt_succ_of h326 chunk_1838
  have h328 : ∀ c, c < 328 → SegP2 c := forall_lt_succ_of h327 chunk_1839
  have h329 : ∀ c, c < 329 → SegP2 c := forall_lt_succ_of h328 chunk_1840
  have h330 : ∀ c, c < 330 → SegP2 c := forall_lt_succ_of h329 chunk_1841
  have h331 : ∀ c, c < 331 → SegP2 c := forall_lt_succ_of h330 chunk_1842
  have h332 : ∀ c, c < 332 → SegP2 c := forall_lt_succ_of h331 chunk_1843
  have h333 : ∀ c, c < 333 → SegP2 c := forall_lt_succ_of h332 chunk_1844
  have h334 : ∀ c, c < 334 → SegP2 c := forall_lt_succ_of h333 chunk_1845
  have h335 : ∀ c, c < 335 → SegP2 c := forall_lt_succ_of h334 chunk_1846
  have h336 : ∀ c, c < 336 → SegP2 c := forall_lt_succ_of h335 chunk_1847
  have h337 : ∀ c, c < 337 → SegP2 c := forall_lt_succ_of h336 chunk_1848
  have h338 : ∀ c, c < 338 → SegP2 c := forall_lt_succ_of h337 chunk_1849
  have h339 : ∀ c, c < 339 → SegP2 c := forall_lt_succ_of h338 chunk_1850
  have h340 : ∀ c, c < 340 → SegP2 c := forall_lt_succ_of h339 chunk_1851
  have h341 : ∀ c, c < 341 → SegP2 c := forall_lt_succ_of h340 chunk_1852
  have h342 : ∀ c, c < 342 → SegP2 c := forall_lt_succ_of h341 chunk_1853
  have h343 : ∀ c, c < 343 → SegP2 c := forall_lt_succ_of h342 chunk_1854
  have h344 : ∀ c, c < 344 → SegP2 c := forall_lt_succ_of h343 chunk_1855
  have h345 : ∀ c, c < 345 → SegP2 c := forall_lt_succ_of h344 chunk_1856
  have h346 : ∀ c, c < 346 → SegP2 c := forall_lt_succ_of h345 chunk_1857
  have h347 : ∀ c, c < 347 → SegP2 c := forall_lt_succ_of h346 chunk_1858
  have h348 : ∀ c, c < 348 → SegP2 c := forall_lt_succ_of h347 chunk_1859
  have h349 : ∀ c, c < 349 → SegP2 c := forall_lt_succ_of h348 chunk_1860
  have h350 : ∀ c, c < 350 → SegP2 c := forall_lt_succ_of h349 chunk_1861
  have h351 : ∀ c, c < 351 → SegP2 c := forall_lt_succ_of h350 chunk_1862
  have h352 : ∀ c, c < 352 → SegP2 c := forall_lt_succ_of h351 chunk_1863
  have h353 : ∀ c, c < 353 → SegP2 c := forall_lt_succ_of h352 chunk_1864
  have h354 : ∀ c, c < 354 → SegP2 c := forall_lt_succ_of h353 chunk_1865
  have h355 : ∀ c, c < 355 → SegP2 c := forall_lt_succ_of h354 chunk_1866
  have h356 : ∀ c, c < 356 → SegP2 c := forall_lt_succ_of h355 chunk_1867
  have h357 : ∀ c, c < 357 → SegP2 c := forall_lt_succ_of h356 chunk_1868
  have h358 : ∀ c, c < 358 → SegP2 c := forall_lt_succ_of h357 chunk_1869
  have h359 : ∀ c, c < 359 → SegP2 c := forall_lt_succ_of h358 chunk_1870
  have h360 : ∀ c, c < 360 → SegP2 c := forall_lt_succ_of h359 chunk_1871
  have h361 : ∀ c, c < 361 → SegP2 c := forall_lt_succ_of h360 chunk_1872
  have h362 : ∀ c, c < 362 → SegP2 c := forall_lt_succ_of h361 chunk_1873
  have h363 : ∀ c, c < 363 → SegP2 c := forall_lt_succ_of h362 chunk_1874
  have h364 : ∀ c, c < 364 → SegP2 c := forall_lt_succ_of h363 chunk_1875
  have h365 : ∀ c, c < 365 → SegP2 c := forall_lt_succ_of h364 chunk_1876
  have h366 : ∀ c, c < 366 → SegP2 c := forall_lt_succ_of h365 chunk_1877
  have h367 : ∀ c, c < 367 → SegP2 c := forall_lt_succ_of h366 chunk_1878
  have h368 : ∀ c, c < 368 → SegP2 c := forall_lt_succ_of h367 chunk_1879
  have h369 : ∀ c, c < 369 → SegP2 c := forall_lt_succ_of h368 chunk_1880
  have h370 : ∀ c, c < 370 → SegP2 c := forall_lt_succ_of h369 chunk_1881
  have h371 : ∀ c, c < 371 → SegP2 c := forall_lt_succ_of h370 chunk_1882
  have h372 : ∀ c, c < 372 → SegP2 c := forall_lt_succ_of h371 chunk_1883
  have h373 : ∀ c, c < 373 → SegP2 c := forall_lt_succ_of h372 chunk_1884
  have h374 : ∀ c, c < 374 → SegP2 c := forall_lt_succ_of h373 chunk_1885
  have h375 : ∀ c, c < 375 → SegP2 c := forall_lt_succ_of h374 chunk_1886
  have h376 : ∀ c, c < 376 → SegP2 c := forall_lt_succ_of h375 chunk_1887
  have h377 : ∀ c, c < 377 → SegP2 c := forall_lt_succ_of h376 chunk_1888
  have h378 : ∀ c, c < 378 → SegP2 c := forall_lt_succ_of h377 chunk_1889
  have h379 : ∀ c, c < 379 → SegP2 c := forall_lt_succ_of h378 chunk_1890
  have h380 : ∀ c, c < 380 → SegP2 c := forall_lt_succ_of h379 chunk_1891
  have h381 : ∀ c, c < 381 → SegP2 c := forall_lt_succ_of h380 chunk_1892
  have h382 : ∀ c, c < 382 → SegP2 c := forall_lt_succ_of h381 chunk_1893
  have h383 : ∀ c, c < 383 → SegP2 c := forall_lt_succ_of h382 chunk_1894
  have h384 : ∀ c, c < 384 → SegP2 c := forall_lt_succ_of h383 chunk_1895
  have h385 : ∀ c, c < 385 → SegP2 c := forall_lt_succ_of h384 chunk_1896
  have h386 : ∀ c, c < 386 → SegP2 c := forall_lt_succ_of h385 chunk_1897
  have h387 : ∀ c, c < 387 → SegP2 c := forall_lt_succ_of h386 chunk_1898
  have h388 : ∀ c, c < 388 → SegP2 c := forall_lt_succ_of h387 chunk_1899
  have h389 : ∀ c, c < 389 → SegP2 c := forall_lt_succ_of h388 chunk_1900
  have h390 : ∀ c, c < 390 → SegP2 c := forall_lt_succ_of h389 chunk_1901
  have h391 : ∀ c, c < 391 → SegP2 c := forall_lt_succ_of h390 chunk_1902
  have h392 : ∀ c, c < 392 → SegP2 c := forall_lt_succ_of h391 chunk_1903
  have h393 : ∀ c, c < 393 → SegP2 c := forall_lt_succ_of h392 chunk_1904
  have h394 : ∀ c, c < 394 → SegP2 c := forall_lt_succ_of h393 chunk_1905
  have h395 : ∀ c, c < 395 → SegP2 c := forall_lt_succ_of h394 chunk_1906
  have h396 : ∀ c, c < 396 → SegP2 c := forall_lt_succ_of h395 chunk_1907
  have h397 : ∀ c, c < 397 → SegP2 c := forall_lt_succ_of h396 chunk_1908
  have h398 : ∀ c, c < 398 → SegP2 c := forall_lt_succ_of h397 chunk_1909
  have h399 : ∀ c, c < 399 → SegP2 c := forall_lt_succ_of h398 chunk_1910
  have h400 : ∀ c, c < 400 → SegP2 c := forall_lt_succ_of h399 chunk_1911
  have h401 : ∀ c, c < 401 → SegP2 c := forall_lt_succ_of h400 chunk_1912
  have h402 : ∀ c, c < 402 → SegP2 c := forall_lt_succ_of h401 chunk_1913
  have h403 : ∀ c, c < 403 → SegP2 c := forall_lt_succ_of h402 chunk_1914
  have h404 : ∀ c, c < 404 → SegP2 c := forall_lt_succ_of h403 chunk_1915
  have h405 : ∀ c, c < 405 → SegP2 c := forall_lt_succ_of h404 chunk_1916
  have h406 : ∀ c, c < 406 → SegP2 c := forall_lt_succ_of h405 chunk_1917
  have h407 : ∀ c, c < 407 → SegP2 c := forall_lt_succ_of h406 chunk_1918
  have h408 : ∀ c, c < 408 → SegP2 c := forall_lt_succ_of h407 chunk_1919
  have h409 : ∀ c, c < 409 → SegP2 c := forall_lt_succ_of h408 chunk_1920
  have h410 : ∀ c, c < 410 → SegP2 c := forall_lt_succ_of h409 chunk_1921
  have h411 : ∀ c, c < 411 → SegP2 c := forall_lt_succ_of h410 chunk_1922
  have h412 : ∀ c, c < 412 → SegP2 c := forall_lt_succ_of h411 chunk_1923
  have h413 : ∀ c, c < 413 → SegP2 c := forall_lt_succ_of h412 chunk_1924
  have h414 : ∀ c, c < 414 → SegP2 c := forall_lt_succ_of h413 chunk_1925
  have h415 : ∀ c, c < 415 → SegP2 c := forall_lt_succ_of h414 chunk_1926
  have h416 : ∀ c, c < 416 → SegP2 c := forall_lt_succ_of h415 chunk_1927
  have h417 : ∀ c, c < 417 → SegP2 c := forall_lt_succ_of h416 chunk_1928
  have h418 : ∀ c, c < 418 → SegP2 c := forall_lt_succ_of h417 chunk_1929
  have h419 : ∀ c, c < 419 → SegP2 c := forall_lt_succ_of h418 chunk_1930
  have h420 : ∀ c, c < 420 → SegP2 c := forall_lt_succ_of h419 chunk_1931
  have h421 : ∀ c, c < 421 → SegP2 c := forall_lt_succ_of h420 chunk_1932
  have h422 : ∀ c, c < 422 → SegP2 c := forall_lt_succ_of h421 chunk_1933
  have h423 : ∀ c, c < 423 → SegP2 c := forall_lt_succ_of h422 chunk_1934
  have h424 : ∀ c, c < 424 → SegP2 c := forall_lt_succ_of h423 chunk_1935
  have h425 : ∀ c, c < 425 → SegP2 c := forall_lt_succ_of h424 chunk_1936
  have h426 : ∀ c, c < 426 → SegP2 c := forall_lt_succ_of h425 chunk_1937
  have h427 : ∀ c, c < 427 → SegP2 c := forall_lt_succ_of h426 chunk_1938
  have h428 : ∀ c, c < 428 → SegP2 c := forall_lt_succ_of h427 chunk_1939
  have h429 : ∀ c, c < 429 → SegP2 c := forall_lt_succ_of h428 chunk_1940
  have h430 : ∀ c, c < 430 → SegP2 c := forall_lt_succ_of h429 chunk_1941
  have h431 : ∀ c, c < 431 → SegP2 c := forall_lt_succ_of h430 chunk_1942
  have h432 : ∀ c, c < 432 → SegP2 c := forall_lt_succ_of h431 chunk_1943
  have h433 : ∀ c, c < 433 → SegP2 c := forall_lt_succ_of h432 chunk_1944
  have h434 : ∀ c, c < 434 → SegP2 c := forall_lt_succ_of h433 chunk_1945
  have h435 : ∀ c, c < 435 → SegP2 c := forall_lt_succ_of h434 chunk_1946
  have h436 : ∀ c, c < 436 → SegP2 c := forall_lt_succ_of h435 chunk_1947
  have h437 : ∀ c, c < 437 → SegP2 c := forall_lt_succ_of h436 chunk_1948
  have h438 : ∀ c, c < 438 → SegP2 c := forall_lt_succ_of h437 chunk_1949
  have h439 : ∀ c, c < 439 → SegP2 c := forall_lt_succ_of h438 chunk_1950
  have h440 : ∀ c, c < 440 → SegP2 c := forall_lt_succ_of h439 chunk_1951
  have h441 : ∀ c, c < 441 → SegP2 c := forall_lt_succ_of h440 chunk_1952
  have h442 : ∀ c, c < 442 → SegP2 c := forall_lt_succ_of h441 chunk_1953
  have h443 : ∀ c, c < 443 → SegP2 c := forall_lt_succ_of h442 chunk_1954
  have h444 : ∀ c, c < 444 → SegP2 c := forall_lt_succ_of h443 chunk_1955
  have h445 : ∀ c, c < 445 → SegP2 c := forall_lt_succ_of h444 chunk_1956
  have h446 : ∀ c, c < 446 → SegP2 c := forall_lt_succ_of h445 chunk_1957
  have h447 : ∀ c, c < 447 → SegP2 c := forall_lt_succ_of h446 chunk_1958
  have h448 : ∀ c, c < 448 → SegP2 c := forall_lt_succ_of h447 chunk_1959
  have h449 : ∀ c, c < 449 → SegP2 c := forall_lt_succ_of h448 chunk_1960
  have h450 : ∀ c, c < 450 → SegP2 c := forall_lt_succ_of h449 chunk_1961
  have h451 : ∀ c, c < 451 → SegP2 c := forall_lt_succ_of h450 chunk_1962
  have h452 : ∀ c, c < 452 → SegP2 c := forall_lt_succ_of h451 chunk_1963
  have h453 : ∀ c, c < 453 → SegP2 c := forall_lt_succ_of h452 chunk_1964
  have h454 : ∀ c, c < 454 → SegP2 c := forall_lt_succ_of h453 chunk_1965
  have h455 : ∀ c, c < 455 → SegP2 c := forall_lt_succ_of h454 chunk_1966
  have h456 : ∀ c, c < 456 → SegP2 c := forall_lt_succ_of h455 chunk_1967
  have h457 : ∀ c, c < 457 → SegP2 c := forall_lt_succ_of h456 chunk_1968
  have h458 : ∀ c, c < 458 → SegP2 c := forall_lt_succ_of h457 chunk_1969
  have h459 : ∀ c, c < 459 → SegP2 c := forall_lt_succ_of h458 chunk_1970
  have h460 : ∀ c, c < 460 → SegP2 c := forall_lt_succ_of h459 chunk_1971
  have h461 : ∀ c, c < 461 → SegP2 c := forall_lt_succ_of h460 chunk_1972
  have h462 : ∀ c, c < 462 → SegP2 c := forall_lt_succ_of h461 chunk_1973
  have h463 : ∀ c, c < 463 → SegP2 c := forall_lt_succ_of h462 chunk_1974
  have h464 : ∀ c, c < 464 → SegP2 c := forall_lt_succ_of h463 chunk_1975
  have h465 : ∀ c, c < 465 → SegP2 c := forall_lt_succ_of h464 chunk_1976
  have h466 : ∀ c, c < 466 → SegP2 c := forall_lt_succ_of h465 chunk_1977
  have h467 : ∀ c, c < 467 → SegP2 c := forall_lt_succ_of h466 chunk_1978
  have h468 : ∀ c, c < 468 → SegP2 c := forall_lt_succ_of h467 chunk_1979
  have h469 : ∀ c, c < 469 → SegP2 c := forall_lt_succ_of h468 chunk_1980
  have h470 : ∀ c, c < 470 → SegP2 c := forall_lt_succ_of h469 chunk_1981
  have h471 : ∀ c, c < 471 → SegP2 c := forall_lt_succ_of h470 chunk_1982
  have h472 : ∀ c, c < 472 → SegP2 c := forall_lt_succ_of h471 chunk_1983
  have h473 : ∀ c, c < 473 → SegP2 c := forall_lt_succ_of h472 chunk_1984
  have h474 : ∀ c, c < 474 → SegP2 c := forall_lt_succ_of h473 chunk_1985
  have h475 : ∀ c, c < 475 → SegP2 c := forall_lt_succ_of h474 chunk_1986
  have h476 : ∀ c, c < 476 → SegP2 c := forall_lt_succ_of h475 chunk_1987
  have h477 : ∀ c, c < 477 → SegP2 c := forall_lt_succ_of h476 chunk_1988
  have h478 : ∀ c, c < 478 → SegP2 c := forall_lt_succ_of h477 chunk_1989
  have h479 : ∀ c, c < 479 → SegP2 c := forall_lt_succ_of h478 chunk_1990
  have h480 : ∀ c, c < 480 → SegP2 c := forall_lt_succ_of h479 chunk_1991
  have h481 : ∀ c, c < 481 → SegP2 c := forall_lt_succ_of h480 chunk_1992
  have h482 : ∀ c, c < 482 → SegP2 c := forall_lt_succ_of h481 chunk_1993
  have h483 : ∀ c, c < 483 → SegP2 c := forall_lt_succ_of h482 chunk_1994
  have h484 : ∀ c, c < 484 → SegP2 c := forall_lt_succ_of h483 chunk_1995
  have h485 : ∀ c, c < 485 → SegP2 c := forall_lt_succ_of h484 chunk_1996
  have h486 : ∀ c, c < 486 → SegP2 c := forall_lt_succ_of h485 chunk_1997
  have h487 : ∀ c, c < 487 → SegP2 c := forall_lt_succ_of h486 chunk_1998
  have h488 : ∀ c, c < 488 → SegP2 c := forall_lt_succ_of h487 chunk_1999
  have h489 : ∀ c, c < 489 → SegP2 c := forall_lt_succ_of h488 chunk_2000
  have h490 : ∀ c, c < 490 → SegP2 c := forall_lt_succ_of h489 chunk_2001
  have h491 : ∀ c, c < 491 → SegP2 c := forall_lt_succ_of h490 chunk_2002
  have h492 : ∀ c, c < 492 → SegP2 c := forall_lt_succ_of h491 chunk_2003
  have h493 : ∀ c, c < 493 → SegP2 c := forall_lt_succ_of h492 chunk_2004
  have h494 : ∀ c, c < 494 → SegP2 c := forall_lt_succ_of h493 chunk_2005
  have h495 : ∀ c, c < 495 → SegP2 c := forall_lt_succ_of h494 chunk_2006
  have h496 : ∀ c, c < 496 → SegP2 c := forall_lt_succ_of h495 chunk_2007
  have h497 : ∀ c, c < 497 → SegP2 c := forall_lt_succ_of h496 chunk_2008
  have h498 : ∀ c, c < 498 → SegP2 c := forall_lt_succ_of h497 chunk_2009
  have h499 : ∀ c, c < 499 → SegP2 c := forall_lt_succ_of h498 chunk_2010
  have h500 : ∀ c, c < 500 → SegP2 c := forall_lt_succ_of h499 chunk_2011
  have h501 : ∀ c, c < 501 → SegP2 c := forall_lt_succ_of h500 chunk_2012
  have h502 : ∀ c, c < 502 → SegP2 c := forall_lt_succ_of h501 chunk_2013
  have h503 : ∀ c, c < 503 → SegP2 c := forall_lt_succ_of h502 chunk_2014
  have h504 : ∀ c, c < 504 → SegP2 c := forall_lt_succ_of h503 chunk_2015
  exact h504

end SandierSerfaty.CertData
