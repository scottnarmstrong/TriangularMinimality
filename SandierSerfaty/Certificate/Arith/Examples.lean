/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.Log
public import SandierSerfaty.Certificate.Arith.Fx

/-!
# Kernel regression checks of the certificate arithmetic

Small `decide +kernel` checks of the computational definitions, evaluated in a module that imports them:
this checks the module system, since `decide +kernel` here must
unfold the `@[expose]` bodies of `SInt`, `IV`, `Fx` and `Log` across module boundaries. Each check ends in a
literal comparison that forces the evaluation of its left side (rule K2 of `scripts/check_kernel_rules.py`). The values are cross-checked against
the soundness laws only informally (they are regression tests, not lemmas used downstream).
-/

public section

namespace SandierSerfaty.Certificate.Arith.Examples

/-- `1/3 · 3 ∈ [1 - 2^-127, 1 + 2^-127]` in `IV 128`. -/
example : IV.subsetB (IV.mul (IV.ofFrac (P := 128) ⟨false, 1⟩ 3) (IV.ofNat 3))
    (IV.addRad (IV.ofNat 1) 2) = true := by decide +kernel

/-- Sign dispatch: `[-1, 2] · [-3, 1] = [-6, 3]` exactly. -/
example : (IV.mul (P := 128) ⟨⟨true, 1 <<< 128⟩, ⟨false, 2 <<< 128⟩⟩
    ⟨⟨true, 3 <<< 128⟩, ⟨false, 1 <<< 128⟩⟩).lo.mag = 6 <<< 128 := by decide +kernel

/-- `√2 ∈ [1.41421356, 1.41421357]`, by the checked proposal. -/
example : (IV.sqrtCheck (P := 128) (IV.ofNat 2) (IV.sqrtProposal (P := 128) (IV.ofNat 2)).1
    (IV.sqrtProposal (P := 128) (IV.ofNat 2)).2 &&
    IV.subsetB (IV.ofNatPair (P := 128) (IV.sqrtProposal (P := 128) (IV.ofNat 2)).1
      (IV.sqrtProposal (P := 128) (IV.ofNat 2)).2)
      ⟨⟨false, (141421356 <<< 128) / 100000000⟩, ⟨false, (141421357 <<< 128) / 100000000 + 1⟩⟩) =
    true := by decide +kernel

/-- `log (53/100) ∈ [-0.63488, -0.63487]` and the enclosure is at most `2^-118` wide. -/
example : (IV.subsetB (IV.logPos (IV.ofFrac ⟨false, 53⟩ 100))
      ⟨⟨true, (63488 <<< 128) / 100000⟩, ⟨true, (63487 <<< 128) / 100000⟩⟩ &&
    SInt.ble (SInt.sub (IV.logPos (IV.ofFrac ⟨false, 53⟩ 100)).hi (IV.logPos (IV.ofFrac ⟨false, 53⟩ 100)).lo)
      ⟨false, 1024⟩) = true := by decide +kernel

/-- `log 2 ∈ [0.693147, 0.693148]`. -/
example : IV.subsetB (IV.logPos (IV.ofNat 2))
    ⟨⟨false, (693147 <<< 128) / 1000000⟩, ⟨false, (693148 <<< 128) / 1000000⟩⟩ = true := by
  decide +kernel

/-- The midpoint product truncates toward zero: `(-1/3)·3 = -(1 - 2^-128)` up to one ulp. -/
example : Fx.ble (Fx.sub (Fx.mul (Fx.ofRatDown (P := 128) (-1 / 3)) (Fx.ofNat 3)) (Fx.ofInt (-1)))
    ⟨⟨false, 2⟩⟩ = true := by decide +kernel

end SandierSerfaty.Certificate.Arith.Examples
