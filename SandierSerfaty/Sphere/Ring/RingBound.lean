/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.MinBound
public import SandierSerfaty.Sphere.Lower.Statements

/-!
# The ring bound `min 𝔎 ≤ C_U n` (sphere note, Theorem 5.13, last assertion)

* `Sphere.Lower.ringBoundStatement`: **`Lower.RingBoundStatement`**, `𝔎(Y) ≤ C_U n` for every
  minimizer `Y` and every `n ≥ 2`. For `n ≥ 102` compare with the ring configuration `Y_n`
  (`Sphere.normalizedEnergy_ringConfig_le`, the crude form of Theorem 5.13, which needs only
  Proposition 5.12 (i)); the finitely many `n < 102` are absorbed in the constant. The sharp form
  `min 𝔎 ≤ C_ring n + C n^{3/4}` is `Sphere.IsSphereMinimizer.normalizedEnergy_le_ring`.
-/

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- **The ring bound** (sphere note, Theorem 5.13): `min 𝔎 ≤ C_U n` for all `n ≥ 2`. -/
theorem ringBoundStatement : RingBoundStatement := by
  obtain ⟨C, hC, hring⟩ := normalizedEnergy_ringConfig_le
  obtain ⟨M, hM, hsmall⟩ := exists_normalizedEnergy_le_of_lt
  refine ⟨C + M, fun n hn Y hY => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  rcases le_or_gt 102 n with h | h
  · have := (hY.normalizedEnergy_le_ringConfig h).trans (hring n h)
    nlinarith
  · have := hsmall n h Y hY
    nlinarith

end Lower

end Sphere

end SandierSerfaty

end
