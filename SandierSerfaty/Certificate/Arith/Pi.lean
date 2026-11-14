/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.PiHigh
public import SandierSerfaty.Certificate.Arith.IVLemmas

/-!
# The enclosure of `π` at precision `2^-128`

`piIV` is the interval `[⌊π_lo·2^128⌋, ⌈π_hi·2^128⌉] / 2^128` with `π_lo = piLowRat 18 5` and
`π_hi = piUpRat 18 5` the Machin bounds of `SandierSerfaty.Certificate.Arith.PiHigh` (width below
`10^-50`), stored once as a literal, so that no check re-evaluates the Machin series. The literal endpoints are checked against the rationals by
`decide +kernel` (`piIV_lo_le`, `piIV_hi_ge`), and `mem_piIV` is the enclosure.
-/

@[expose] public section

namespace SandierSerfaty.Certificate.Arith

/-- The enclosure of `π` at precision `2^-128` (two ulps wide). -/
def piIV : IV 128 :=
  ⟨⟨false, 1069028584064966747859680373161870783300⟩,
    ⟨false, 1069028584064966747859680373161870783301⟩⟩

/-- The literal lower endpoint lies below the Machin lower bound. -/
theorem piIV_lo_le :
    ((1069028584064966747859680373161870783300 : ℕ) : ℚ) ≤ piLowRat 18 5 * 2 ^ 128 := by
  decide +kernel

/-- The literal upper endpoint lies above the Machin upper bound. -/
theorem piIV_hi_ge :
    piUpRat 18 5 * 2 ^ 128 ≤ ((1069028584064966747859680373161870783301 : ℕ) : ℚ) := by
  decide +kernel

theorem mem_piIV : IV.Mem Real.pi piIV := by
  have h1 := piLowRat_lt_pi 18 5
  have h2 := pi_lt_piUpRat 18 5
  have l : ((1069028584064966747859680373161870783300 : ℕ) : ℝ) ≤ (piLowRat 18 5 : ℝ) * 2 ^ 128 := by
    exact_mod_cast piIV_lo_le
  have u : (piUpRat 18 5 : ℝ) * 2 ^ 128 ≤ ((1069028584064966747859680373161870783301 : ℕ) : ℝ) := by
    exact_mod_cast piIV_hi_ge
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [piIV, SInt.toInt_false, Int.cast_natCast]
    nlinarith
  · simp only [piIV, SInt.toInt_false, Int.cast_natCast]
    nlinarith

end SandierSerfaty.Certificate.Arith
