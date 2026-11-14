/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Dual.DualIdentityMain
public import SandierSerfaty.Torus.Separation

/-!
# The dual identity on separated square-torus configurations

For a separated configuration of `n ≥ 1` points of `T_n = ℂ / (√n ℤ[i])` (`IsSeparatedConfig`: distinct classes, lifted
distances `≥ r_* = 1/√π`), the periodic sites satisfy `SepSites` with `d₀ = d_* = 1/(2√π)`, and the torus has
covolume `n`, so `dual_identity` applies with `Γ = squareLattice n`, `N = n` (paper proof of `dual:identity`):

`torusEnergy (squareLattice n) a = ∑_{e ∈ voronoiIncidences} sectorJ R P (a e.1) e.2 + ½ ∫ |∇(h - H)|²`.
-/

open Set

public section

namespace SandierSerfaty

namespace Dual

open Torus Analysis

/-- The edge distance of separated square-torus configurations: `d_* = r_* / 2 = 1/(2√π)`. -/
@[expose] noncomputable def dStar : ℝ := 1 / (2 * √Real.pi)

theorem dStar_pos : 0 < dStar := by
  unfold dStar; have := Real.pi_pos; positivity

theorem sepSites_of_isSeparatedConfig (n : ℕ) [NeZero n] (a : Fin n → ℂ)
    (h : IsSeparatedConfig n a) : SepSites (periodicSites (squareLattice n) a) dStar := by
  refine sepSites_periodicSites (squareLattice n) a dStar_pos ?_
  rintro p ⟨i, γ₁, hγ₁, rfl⟩ q ⟨j, γ₂, hγ₂, rfl⟩ hne
  have hsub : a i + γ₁ - (a j + γ₂) = a i - a j - (γ₂ - γ₁) := by ring
  have hne' : a i - a j - (γ₂ - γ₁) ≠ 0 := by
    intro h0; apply hne; linear_combination h0
  have := h.2 i j (γ₂ - γ₁) ((squareLattice n).sub_mem hγ₂ hγ₁) hne'
  rw [hsub]
  have h2 : 2 * dStar = 1 / √Real.pi := by
    unfold dStar; have := Real.sqrt_pos.2 Real.pi_pos; field_simp
  linarith

/-- **The dual identity on a separated square-torus configuration.** -/
theorem dual_identity_of_separated {ι : Type*} {R : RadialData ι} (n : ℕ) [NeZero n]
    (a : Fin n → ℂ) (h : IsSeparatedConfig n a) (hR : R.IsAdmissible dStar) :
    torusEnergy (squareLattice n) a =
      ∑ e ∈ voronoiIncidences (squareLattice n) a,
          sectorJ R (periodicSites (squareLattice n) a) (a e.1) e.2 +
        (1 / 2 : ℝ) * ∫ x in torusDomain (squareLattice n),
          gradSq (fun y => greenSum (squareLattice n) a y -
            gluedH R (periodicSites (squareLattice n) a) y) x :=
  dual_identity (covolume_squareLattice n) h.1 hR (sepSites_of_isSeparatedConfig n a h)

end Dual

end SandierSerfaty

end
