/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Table.Page00
public import SandierSerfaty.CertData.Table.Page01
public import SandierSerfaty.CertData.Table.Page02
public import SandierSerfaty.CertData.Table.Page03
public import SandierSerfaty.CertData.Table.Page04
public import SandierSerfaty.CertData.Table.Page05
public import SandierSerfaty.CertData.Table.Page06
public import SandierSerfaty.CertData.Table.Page07
public import SandierSerfaty.CertData.Table.Page08
public import SandierSerfaty.CertData.Table.Page09
public import SandierSerfaty.CertData.Table.Page10
public import SandierSerfaty.CertData.Table.Page11
public import SandierSerfaty.CertData.Table.Page12
public import SandierSerfaty.CertData.Table.Page13
public import SandierSerfaty.CertData.Table.Page14
public import SandierSerfaty.CertData.Table.Page15
public import SandierSerfaty.CertData.Table.Page16
public import SandierSerfaty.CertData.Table.Page17
public import SandierSerfaty.CertData.Table.Page18
public import SandierSerfaty.CertData.Table.Page19
public import SandierSerfaty.CertData.Table.Page20
public import SandierSerfaty.CertData.Table.Page21
public import SandierSerfaty.CertData.Table.Page22
public import SandierSerfaty.CertData.Table.Page23
public import SandierSerfaty.CertData.Table.Page24
public import SandierSerfaty.CertData.Table.Page25
public import SandierSerfaty.CertData.Table.Page26
public import SandierSerfaty.CertData.Table.Page27
public import SandierSerfaty.CertData.Table.Page28
public import SandierSerfaty.CertData.Table.Page29
public import SandierSerfaty.CertData.Table.Page30
public import SandierSerfaty.CertData.Basis
public import SandierSerfaty.Certificate.Assemble.Defs

/-!
# The radial table (dispatch)

The global accessors `nodeAt`, `ctAt`, `ntAt`, `ckAt` of the table (binary `cond` trees over the blocks of the
pages), the number of cells `tblN`, the knot cells `knotCell j`.
-/

@[expose] public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The nodes, by block. -/
def nodeBlk (b k : Nat) : IV 128 :=
  cond (Nat.blt b 30) (cond (Nat.blt b 15) (cond (Nat.blt b 7) (cond (Nat.blt b 3) (cond (Nat.blt b 1) (
    nodeB_0 k) (cond (Nat.blt b 2) (
    nodeB_1 k) (
    nodeB_2 k))) (cond (Nat.blt b 5) (cond (Nat.blt b 4) (
    nodeB_3 k) (
    nodeB_4 k)) (cond (Nat.blt b 6) (
    nodeB_5 k) (
    nodeB_6 k)))) (cond (Nat.blt b 11) (cond (Nat.blt b 9) (cond (Nat.blt b 8) (
    nodeB_7 k) (
    nodeB_8 k)) (cond (Nat.blt b 10) (
    nodeB_9 k) (
    nodeB_10 k))) (cond (Nat.blt b 13) (cond (Nat.blt b 12) (
    nodeB_11 k) (
    nodeB_12 k)) (cond (Nat.blt b 14) (
    nodeB_13 k) (
    nodeB_14 k))))) (cond (Nat.blt b 22) (cond (Nat.blt b 18) (cond (Nat.blt b 16) (
    nodeB_15 k) (cond (Nat.blt b 17) (
    nodeB_16 k) (
    nodeB_17 k))) (cond (Nat.blt b 20) (cond (Nat.blt b 19) (
    nodeB_18 k) (
    nodeB_19 k)) (cond (Nat.blt b 21) (
    nodeB_20 k) (
    nodeB_21 k)))) (cond (Nat.blt b 26) (cond (Nat.blt b 24) (cond (Nat.blt b 23) (
    nodeB_22 k) (
    nodeB_23 k)) (cond (Nat.blt b 25) (
    nodeB_24 k) (
    nodeB_25 k))) (cond (Nat.blt b 28) (cond (Nat.blt b 27) (
    nodeB_26 k) (
    nodeB_27 k)) (cond (Nat.blt b 29) (
    nodeB_28 k) (
    nodeB_29 k)))))) (cond (Nat.blt b 45) (cond (Nat.blt b 37) (cond (Nat.blt b 33) (cond (Nat.blt b 31) (
    nodeB_30 k) (cond (Nat.blt b 32) (
    nodeB_31 k) (
    nodeB_32 k))) (cond (Nat.blt b 35) (cond (Nat.blt b 34) (
    nodeB_33 k) (
    nodeB_34 k)) (cond (Nat.blt b 36) (
    nodeB_35 k) (
    nodeB_36 k)))) (cond (Nat.blt b 41) (cond (Nat.blt b 39) (cond (Nat.blt b 38) (
    nodeB_37 k) (
    nodeB_38 k)) (cond (Nat.blt b 40) (
    nodeB_39 k) (
    nodeB_40 k))) (cond (Nat.blt b 43) (cond (Nat.blt b 42) (
    nodeB_41 k) (
    nodeB_42 k)) (cond (Nat.blt b 44) (
    nodeB_43 k) (
    nodeB_44 k))))) (cond (Nat.blt b 53) (cond (Nat.blt b 49) (cond (Nat.blt b 47) (cond (Nat.blt b 46) (
    nodeB_45 k) (
    nodeB_46 k)) (cond (Nat.blt b 48) (
    nodeB_47 k) (
    nodeB_48 k))) (cond (Nat.blt b 51) (cond (Nat.blt b 50) (
    nodeB_49 k) (
    nodeB_50 k)) (cond (Nat.blt b 52) (
    nodeB_51 k) (
    nodeB_52 k)))) (cond (Nat.blt b 57) (cond (Nat.blt b 55) (cond (Nat.blt b 54) (
    nodeB_53 k) (
    nodeB_54 k)) (cond (Nat.blt b 56) (
    nodeB_55 k) (
    nodeB_56 k))) (cond (Nat.blt b 59) (cond (Nat.blt b 58) (
    nodeB_57 k) (
    nodeB_58 k)) (cond (Nat.blt b 60) (
    nodeB_59 k) (
    nodeB_60 k))))))

/-- The node `i`. -/
def nodeAt (i : Nat) : IV 128 := nodeBlk (Nat.div i 64) (Nat.mod i 64)

/-- The cell tuples, by block. -/
def ctBlk (b k : Nat) : Tup :=
  cond (Nat.blt b 30) (cond (Nat.blt b 15) (cond (Nat.blt b 7) (cond (Nat.blt b 3) (cond (Nat.blt b 1) (
    ctB_0 k) (cond (Nat.blt b 2) (
    ctB_1 k) (
    ctB_2 k))) (cond (Nat.blt b 5) (cond (Nat.blt b 4) (
    ctB_3 k) (
    ctB_4 k)) (cond (Nat.blt b 6) (
    ctB_5 k) (
    ctB_6 k)))) (cond (Nat.blt b 11) (cond (Nat.blt b 9) (cond (Nat.blt b 8) (
    ctB_7 k) (
    ctB_8 k)) (cond (Nat.blt b 10) (
    ctB_9 k) (
    ctB_10 k))) (cond (Nat.blt b 13) (cond (Nat.blt b 12) (
    ctB_11 k) (
    ctB_12 k)) (cond (Nat.blt b 14) (
    ctB_13 k) (
    ctB_14 k))))) (cond (Nat.blt b 22) (cond (Nat.blt b 18) (cond (Nat.blt b 16) (
    ctB_15 k) (cond (Nat.blt b 17) (
    ctB_16 k) (
    ctB_17 k))) (cond (Nat.blt b 20) (cond (Nat.blt b 19) (
    ctB_18 k) (
    ctB_19 k)) (cond (Nat.blt b 21) (
    ctB_20 k) (
    ctB_21 k)))) (cond (Nat.blt b 26) (cond (Nat.blt b 24) (cond (Nat.blt b 23) (
    ctB_22 k) (
    ctB_23 k)) (cond (Nat.blt b 25) (
    ctB_24 k) (
    ctB_25 k))) (cond (Nat.blt b 28) (cond (Nat.blt b 27) (
    ctB_26 k) (
    ctB_27 k)) (cond (Nat.blt b 29) (
    ctB_28 k) (
    ctB_29 k)))))) (cond (Nat.blt b 45) (cond (Nat.blt b 37) (cond (Nat.blt b 33) (cond (Nat.blt b 31) (
    ctB_30 k) (cond (Nat.blt b 32) (
    ctB_31 k) (
    ctB_32 k))) (cond (Nat.blt b 35) (cond (Nat.blt b 34) (
    ctB_33 k) (
    ctB_34 k)) (cond (Nat.blt b 36) (
    ctB_35 k) (
    ctB_36 k)))) (cond (Nat.blt b 41) (cond (Nat.blt b 39) (cond (Nat.blt b 38) (
    ctB_37 k) (
    ctB_38 k)) (cond (Nat.blt b 40) (
    ctB_39 k) (
    ctB_40 k))) (cond (Nat.blt b 43) (cond (Nat.blt b 42) (
    ctB_41 k) (
    ctB_42 k)) (cond (Nat.blt b 44) (
    ctB_43 k) (
    ctB_44 k))))) (cond (Nat.blt b 53) (cond (Nat.blt b 49) (cond (Nat.blt b 47) (cond (Nat.blt b 46) (
    ctB_45 k) (
    ctB_46 k)) (cond (Nat.blt b 48) (
    ctB_47 k) (
    ctB_48 k))) (cond (Nat.blt b 51) (cond (Nat.blt b 50) (
    ctB_49 k) (
    ctB_50 k)) (cond (Nat.blt b 52) (
    ctB_51 k) (
    ctB_52 k)))) (cond (Nat.blt b 57) (cond (Nat.blt b 55) (cond (Nat.blt b 54) (
    ctB_53 k) (
    ctB_54 k)) (cond (Nat.blt b 56) (
    ctB_55 k) (
    ctB_56 k))) (cond (Nat.blt b 59) (cond (Nat.blt b 58) (
    ctB_57 k) (
    ctB_58 k)) (cond (Nat.blt b 60) (
    ctB_59 k) (
    ctB_60 k))))))

/-- The cell tuple `i`. -/
def ctAt (i : Nat) : Tup := ctBlk (Nat.div i 64) (Nat.mod i 64)

/-- The node tuples, by block. -/
def ntBlk (b k : Nat) : Tup :=
  cond (Nat.blt b 30) (cond (Nat.blt b 15) (cond (Nat.blt b 7) (cond (Nat.blt b 3) (cond (Nat.blt b 1) (
    ntB_0 k) (cond (Nat.blt b 2) (
    ntB_1 k) (
    ntB_2 k))) (cond (Nat.blt b 5) (cond (Nat.blt b 4) (
    ntB_3 k) (
    ntB_4 k)) (cond (Nat.blt b 6) (
    ntB_5 k) (
    ntB_6 k)))) (cond (Nat.blt b 11) (cond (Nat.blt b 9) (cond (Nat.blt b 8) (
    ntB_7 k) (
    ntB_8 k)) (cond (Nat.blt b 10) (
    ntB_9 k) (
    ntB_10 k))) (cond (Nat.blt b 13) (cond (Nat.blt b 12) (
    ntB_11 k) (
    ntB_12 k)) (cond (Nat.blt b 14) (
    ntB_13 k) (
    ntB_14 k))))) (cond (Nat.blt b 22) (cond (Nat.blt b 18) (cond (Nat.blt b 16) (
    ntB_15 k) (cond (Nat.blt b 17) (
    ntB_16 k) (
    ntB_17 k))) (cond (Nat.blt b 20) (cond (Nat.blt b 19) (
    ntB_18 k) (
    ntB_19 k)) (cond (Nat.blt b 21) (
    ntB_20 k) (
    ntB_21 k)))) (cond (Nat.blt b 26) (cond (Nat.blt b 24) (cond (Nat.blt b 23) (
    ntB_22 k) (
    ntB_23 k)) (cond (Nat.blt b 25) (
    ntB_24 k) (
    ntB_25 k))) (cond (Nat.blt b 28) (cond (Nat.blt b 27) (
    ntB_26 k) (
    ntB_27 k)) (cond (Nat.blt b 29) (
    ntB_28 k) (
    ntB_29 k)))))) (cond (Nat.blt b 45) (cond (Nat.blt b 37) (cond (Nat.blt b 33) (cond (Nat.blt b 31) (
    ntB_30 k) (cond (Nat.blt b 32) (
    ntB_31 k) (
    ntB_32 k))) (cond (Nat.blt b 35) (cond (Nat.blt b 34) (
    ntB_33 k) (
    ntB_34 k)) (cond (Nat.blt b 36) (
    ntB_35 k) (
    ntB_36 k)))) (cond (Nat.blt b 41) (cond (Nat.blt b 39) (cond (Nat.blt b 38) (
    ntB_37 k) (
    ntB_38 k)) (cond (Nat.blt b 40) (
    ntB_39 k) (
    ntB_40 k))) (cond (Nat.blt b 43) (cond (Nat.blt b 42) (
    ntB_41 k) (
    ntB_42 k)) (cond (Nat.blt b 44) (
    ntB_43 k) (
    ntB_44 k))))) (cond (Nat.blt b 53) (cond (Nat.blt b 49) (cond (Nat.blt b 47) (cond (Nat.blt b 46) (
    ntB_45 k) (
    ntB_46 k)) (cond (Nat.blt b 48) (
    ntB_47 k) (
    ntB_48 k))) (cond (Nat.blt b 51) (cond (Nat.blt b 50) (
    ntB_49 k) (
    ntB_50 k)) (cond (Nat.blt b 52) (
    ntB_51 k) (
    ntB_52 k)))) (cond (Nat.blt b 57) (cond (Nat.blt b 55) (cond (Nat.blt b 54) (
    ntB_53 k) (
    ntB_54 k)) (cond (Nat.blt b 56) (
    ntB_55 k) (
    ntB_56 k))) (cond (Nat.blt b 59) (cond (Nat.blt b 58) (
    ntB_57 k) (
    ntB_58 k)) (cond (Nat.blt b 60) (
    ntB_59 k) (
    ntB_60 k))))))

/-- The node tuple `i` (at the node `i + 1`). -/
def ntAt (i : Nat) : Tup := ntBlk (Nat.div i 64) (Nat.mod i 64)

/-- The checkpoints, by block. -/
def ckBlk (b k : Nat) : SState :=
  cond (Nat.blt b 30) (cond (Nat.blt b 15) (cond (Nat.blt b 7) (cond (Nat.blt b 3) (cond (Nat.blt b 1) (
    ckB_0 k) (cond (Nat.blt b 2) (
    ckB_1 k) (
    ckB_2 k))) (cond (Nat.blt b 5) (cond (Nat.blt b 4) (
    ckB_3 k) (
    ckB_4 k)) (cond (Nat.blt b 6) (
    ckB_5 k) (
    ckB_6 k)))) (cond (Nat.blt b 11) (cond (Nat.blt b 9) (cond (Nat.blt b 8) (
    ckB_7 k) (
    ckB_8 k)) (cond (Nat.blt b 10) (
    ckB_9 k) (
    ckB_10 k))) (cond (Nat.blt b 13) (cond (Nat.blt b 12) (
    ckB_11 k) (
    ckB_12 k)) (cond (Nat.blt b 14) (
    ckB_13 k) (
    ckB_14 k))))) (cond (Nat.blt b 22) (cond (Nat.blt b 18) (cond (Nat.blt b 16) (
    ckB_15 k) (cond (Nat.blt b 17) (
    ckB_16 k) (
    ckB_17 k))) (cond (Nat.blt b 20) (cond (Nat.blt b 19) (
    ckB_18 k) (
    ckB_19 k)) (cond (Nat.blt b 21) (
    ckB_20 k) (
    ckB_21 k)))) (cond (Nat.blt b 26) (cond (Nat.blt b 24) (cond (Nat.blt b 23) (
    ckB_22 k) (
    ckB_23 k)) (cond (Nat.blt b 25) (
    ckB_24 k) (
    ckB_25 k))) (cond (Nat.blt b 28) (cond (Nat.blt b 27) (
    ckB_26 k) (
    ckB_27 k)) (cond (Nat.blt b 29) (
    ckB_28 k) (
    ckB_29 k)))))) (cond (Nat.blt b 45) (cond (Nat.blt b 37) (cond (Nat.blt b 33) (cond (Nat.blt b 31) (
    ckB_30 k) (cond (Nat.blt b 32) (
    ckB_31 k) (
    ckB_32 k))) (cond (Nat.blt b 35) (cond (Nat.blt b 34) (
    ckB_33 k) (
    ckB_34 k)) (cond (Nat.blt b 36) (
    ckB_35 k) (
    ckB_36 k)))) (cond (Nat.blt b 41) (cond (Nat.blt b 39) (cond (Nat.blt b 38) (
    ckB_37 k) (
    ckB_38 k)) (cond (Nat.blt b 40) (
    ckB_39 k) (
    ckB_40 k))) (cond (Nat.blt b 43) (cond (Nat.blt b 42) (
    ckB_41 k) (
    ckB_42 k)) (cond (Nat.blt b 44) (
    ckB_43 k) (
    ckB_44 k))))) (cond (Nat.blt b 53) (cond (Nat.blt b 49) (cond (Nat.blt b 47) (cond (Nat.blt b 46) (
    ckB_45 k) (
    ckB_46 k)) (cond (Nat.blt b 48) (
    ckB_47 k) (
    ckB_48 k))) (cond (Nat.blt b 51) (cond (Nat.blt b 50) (
    ckB_49 k) (
    ckB_50 k)) (cond (Nat.blt b 52) (
    ckB_51 k) (
    ckB_52 k)))) (cond (Nat.blt b 57) (cond (Nat.blt b 55) (cond (Nat.blt b 54) (
    ckB_53 k) (
    ckB_54 k)) (cond (Nat.blt b 56) (
    ckB_55 k) (
    ckB_56 k))) (cond (Nat.blt b 59) (cond (Nat.blt b 58) (
    ckB_57 k) (
    ckB_58 k)) (cond (Nat.blt b 60) (
    ckB_59 k) (
    ckB_60 k))))))

/-- The checkpoint at the node `i`. -/
def ckAt (i : Nat) : SState := ckBlk (Nat.div i 64) (Nat.mod i 64)

/-- The number of cells. -/
def tblN : Nat := 3848

/-- The node index of the knot `κ_j`. -/
def knotCell : Nat → Nat
  | 0 => 0
  | 1 => 784
  | 2 => 1512
  | 3 => 2016
  | 4 => 2040
  | 5 => 3824
  | _ => 3848

/-- The chunk length (cells per declaration) of segment `j`. -/
def chunkLenAt : Nat → Nat
  | 0 => 8
  | 1 => 2
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | _ => 2

/-- The number of chunks of segment `j`. -/
def chunkCnt : Nat → Nat
  | 0 => 98
  | 1 => 364
  | 2 => 504
  | 3 => 12
  | 4 => 892
  | _ => 12

/-- The table seen by the interval queries. -/
def iTbl : ITable := ⟨tblN, nodeAt, ctAt⟩

end SandierSerfaty.CertData
