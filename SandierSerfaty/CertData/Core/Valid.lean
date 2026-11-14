/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Core.S00
public import SandierSerfaty.CertData.Core.S01
public import SandierSerfaty.CertData.Core.S02
public import SandierSerfaty.CertData.Core.S03
public import SandierSerfaty.CertData.Core.S04
public import SandierSerfaty.CertData.Core.S05
public import SandierSerfaty.CertData.Core.S06
public import SandierSerfaty.CertData.Core.S07
public import SandierSerfaty.CertData.Core.S08
public import SandierSerfaty.CertData.Core.S09
public import SandierSerfaty.CertData.Core.S10
public import SandierSerfaty.CertData.Core.S11
public import SandierSerfaty.CertData.Core.S12
public import SandierSerfaty.CertData.Core.S13
public import SandierSerfaty.CertData.Core.S14
public import SandierSerfaty.CertData.Core.S15
public import SandierSerfaty.CertData.Core.S16
public import SandierSerfaty.CertData.Core.S17
public import SandierSerfaty.CertData.Core.S18
public import SandierSerfaty.CertData.Core.S19
public import SandierSerfaty.CertData.Core.S20
public import SandierSerfaty.CertData.Core.S21
public import SandierSerfaty.CertData.Core.S22
public import SandierSerfaty.CertData.Core.S23
public import SandierSerfaty.CertData.Core.S24
public import SandierSerfaty.CertData.Core.S25
public import SandierSerfaty.CertData.Core.S26
public import SandierSerfaty.CertData.Core.S27
public import SandierSerfaty.CertData.Core.S28
public import SandierSerfaty.CertData.Core.S29
public import SandierSerfaty.CertData.BasisValid
public import SandierSerfaty.Certificate.Assemble.Lists
public import SandierSerfaty.Certificate.Basis.CoreSound
public import SandierSerfaty.Tails.RetainedCore

/-!
# Assertion A2: the finite core

The pieces joined (`Assemble.allCells_append_of`), the covering checks, and `Tails.FiniteCore` from `Basis.coreBounds_of_checks`.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-- The core cells, by segment. -/
def coreSeg : Nat → List (IV 128)
  | 0 => coreSeg0
  | 1 => coreSeg1
  | 2 => coreSeg2
  | 3 => coreSeg3
  | 4 => coreSeg4
  | _ => coreSeg5

theorem cover_0 : coverB (knotIV dLit 0).lo (knotIV dLit 1).hi coreSeg0 = true := by
  decide +kernel

theorem coreSeg_0_ok : coreSegCheck dLit 0 (coreSeg 0) = true := by
  simp only [coreSegCheck, Bool.and_eq_true]
  exact ⟨cover_0, allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (core_0_0_ok) core_0_1_ok) core_0_2_ok) core_0_3_ok) core_0_4_ok) core_0_5_ok) core_0_6_ok) core_0_7_ok) core_0_8_ok) core_0_9_ok) core_0_10_ok) core_0_11_ok) core_0_12_ok) core_0_13_ok) core_0_14_ok) core_0_15_ok) core_0_16_ok) core_0_17_ok) core_0_18_ok) core_0_19_ok) core_0_20_ok) core_0_21_ok) core_0_22_ok) core_0_23_ok) core_0_24_ok) core_0_25_ok) core_0_26_ok) core_0_27_ok⟩

theorem cover_1 : coverB (knotIV dLit 1).lo (knotIV dLit 2).hi coreSeg1 = true := by
  decide +kernel

theorem coreSeg_1_ok : coreSegCheck dLit 1 (coreSeg 1) = true := by
  simp only [coreSegCheck, Bool.and_eq_true]
  exact ⟨cover_1, allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (core_1_0_ok) core_1_1_ok) core_1_2_ok) core_1_3_ok) core_1_4_ok) core_1_5_ok) core_1_6_ok) core_1_7_ok) core_1_8_ok) core_1_9_ok) core_1_10_ok) core_1_11_ok) core_1_12_ok) core_1_13_ok) core_1_14_ok) core_1_15_ok) core_1_16_ok) core_1_17_ok) core_1_18_ok) core_1_19_ok) core_1_20_ok) core_1_21_ok) core_1_22_ok) core_1_23_ok) core_1_24_ok) core_1_25_ok) core_1_26_ok) core_1_27_ok) core_1_28_ok) core_1_29_ok) core_1_30_ok) core_1_31_ok) core_1_32_ok) core_1_33_ok) core_1_34_ok⟩

theorem cover_2 : coverB (knotIV dLit 2).lo (knotIV dLit 3).hi coreSeg2 = true := by
  decide +kernel

theorem coreSeg_2_ok : coreSegCheck dLit 2 (coreSeg 2) = true := by
  simp only [coreSegCheck, Bool.and_eq_true]
  exact ⟨cover_2, allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (core_2_0_ok) core_2_1_ok) core_2_2_ok) core_2_3_ok) core_2_4_ok) core_2_5_ok) core_2_6_ok) core_2_7_ok) core_2_8_ok) core_2_9_ok) core_2_10_ok) core_2_11_ok) core_2_12_ok) core_2_13_ok) core_2_14_ok) core_2_15_ok) core_2_16_ok) core_2_17_ok) core_2_18_ok) core_2_19_ok) core_2_20_ok) core_2_21_ok) core_2_22_ok) core_2_23_ok) core_2_24_ok) core_2_25_ok) core_2_26_ok) core_2_27_ok) core_2_28_ok) core_2_29_ok) core_2_30_ok) core_2_31_ok) core_2_32_ok) core_2_33_ok) core_2_34_ok) core_2_35_ok) core_2_36_ok) core_2_37_ok) core_2_38_ok) core_2_39_ok) core_2_40_ok) core_2_41_ok) core_2_42_ok) core_2_43_ok) core_2_44_ok) core_2_45_ok) core_2_46_ok) core_2_47_ok) core_2_48_ok) core_2_49_ok) core_2_50_ok) core_2_51_ok) core_2_52_ok) core_2_53_ok) core_2_54_ok) core_2_55_ok) core_2_56_ok) core_2_57_ok) core_2_58_ok) core_2_59_ok) core_2_60_ok) core_2_61_ok) core_2_62_ok) core_2_63_ok) core_2_64_ok) core_2_65_ok) core_2_66_ok) core_2_67_ok) core_2_68_ok) core_2_69_ok) core_2_70_ok) core_2_71_ok) core_2_72_ok) core_2_73_ok) core_2_74_ok) core_2_75_ok) core_2_76_ok) core_2_77_ok) core_2_78_ok) core_2_79_ok) core_2_80_ok) core_2_81_ok) core_2_82_ok) core_2_83_ok) core_2_84_ok) core_2_85_ok) core_2_86_ok) core_2_87_ok) core_2_88_ok) core_2_89_ok) core_2_90_ok) core_2_91_ok) core_2_92_ok) core_2_93_ok) core_2_94_ok) core_2_95_ok) core_2_96_ok) core_2_97_ok) core_2_98_ok) core_2_99_ok) core_2_100_ok) core_2_101_ok) core_2_102_ok) core_2_103_ok) core_2_104_ok) core_2_105_ok) core_2_106_ok) core_2_107_ok) core_2_108_ok) core_2_109_ok) core_2_110_ok) core_2_111_ok) core_2_112_ok) core_2_113_ok) core_2_114_ok) core_2_115_ok) core_2_116_ok) core_2_117_ok) core_2_118_ok) core_2_119_ok) core_2_120_ok) core_2_121_ok) core_2_122_ok) core_2_123_ok) core_2_124_ok) core_2_125_ok⟩

theorem cover_3 : coverB (knotIV dLit 3).lo (knotIV dLit 4).hi coreSeg3 = true := by
  decide +kernel

theorem coreSeg_3_ok : coreSegCheck dLit 3 (coreSeg 3) = true := by
  simp only [coreSegCheck, Bool.and_eq_true]
  exact ⟨cover_3, core_3_0_ok⟩

theorem cover_4 : coverB (knotIV dLit 4).lo (knotIV dLit 5).hi coreSeg4 = true := by
  decide +kernel

theorem coreSeg_4_ok : coreSegCheck dLit 4 (coreSeg 4) = true := by
  simp only [coreSegCheck, Bool.and_eq_true]
  exact ⟨cover_4, allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (allCells_append_of (core_4_0_ok) core_4_1_ok) core_4_2_ok) core_4_3_ok) core_4_4_ok) core_4_5_ok) core_4_6_ok) core_4_7_ok) core_4_8_ok) core_4_9_ok) core_4_10_ok) core_4_11_ok) core_4_12_ok) core_4_13_ok) core_4_14_ok) core_4_15_ok) core_4_16_ok) core_4_17_ok) core_4_18_ok) core_4_19_ok) core_4_20_ok) core_4_21_ok) core_4_22_ok) core_4_23_ok) core_4_24_ok) core_4_25_ok) core_4_26_ok) core_4_27_ok) core_4_28_ok) core_4_29_ok) core_4_30_ok) core_4_31_ok) core_4_32_ok) core_4_33_ok) core_4_34_ok) core_4_35_ok) core_4_36_ok) core_4_37_ok) core_4_38_ok) core_4_39_ok) core_4_40_ok) core_4_41_ok) core_4_42_ok⟩

theorem cover_5 : coverB (knotIV dLit 5).lo (knotIV dLit 6).hi coreSeg5 = true := by
  decide +kernel

theorem coreSeg_5_ok : coreSegCheck dLit 5 (coreSeg 5) = true := by
  simp only [coreSegCheck, Bool.and_eq_true]
  exact ⟨cover_5, core_5_0_ok⟩

/-- **Assertion A2**: the finite-core premise `Tails.FiniteCore` (`tail:finite-core-premise`). -/
theorem finiteCore : SandierSerfaty.Tails.FiniteCore := by
  have hc : ∀ j, j ≤ 5 → coreSegCheck dLit j (coreSeg j) = true := by
    intro j hj
    obtain rfl | rfl | rfl | rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    exacts [coreSeg_0_ok, coreSeg_1_ok, coreSeg_2_ok, coreSeg_3_ok, coreSeg_4_ok, coreSeg_5_ok]
  exact ⟨abs_coeff_one_lt, fun j hj t ht hb hl => (coreBounds_of_checks dLit_valid hc j hj t ht hb hl).1,
    fun j hj t ht hb hl => (coreBounds_of_checks dLit_valid hc j hj t ht hb hl).2⟩

end SandierSerfaty.CertData
