/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.ChartGreen

/-!
# The puncture energy (sphere note, Definition 2.3)

For `G ⊆ ℂ` open and finitely many punctures `P ⊆ G`, a function `H` is *admissible* on `(G, P)`
(`Sphere.PunctureAdmissible`) if it is `C²` off `P`, if `H - g(· - p)` extends to a `C¹` function near
each puncture `p`, and if `|∇H|²` is integrable on `G ∖ ⋃ B(p, ε)` for every `ε > 0`. Its
*puncture energy* is
```
W_G(H) = lim_{η ↓ 0} [½ ∫_{G ∖ ⋃ B(p, η)} |∇H|² + π |P| log η].
```
`Sphere.punctureTrunc` is the quantity inside the limit and `Sphere.punctureEnergy` the limit (the
`limUnder` along `η ↓ 0`; it has its value only when the limit exists, which for admissible `H` is
Lemma 2.4).
-/

open MeasureTheory Set Filter Topology Laplacian SandierSerfaty.Analysis
open scoped ContDiff

public section

namespace SandierSerfaty

namespace Sphere

/-- The truncated energy `½ ∫_{G ∖ ⋃ B(p, η)} |∇H|² + π |P| log η`. -/
@[expose] noncomputable def punctureTrunc (G : Set ℂ) (P : Finset ℂ) (H : ℂ → ℝ) (η : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (∫ x in G \ ⋃ p ∈ P, Metric.ball p η, ‖gradient H x‖ ^ 2) +
    Real.pi * P.card * Real.log η

/-- The puncture energy `W_G(H) = lim_{η ↓ 0} punctureTrunc G P H η`. -/
@[expose] noncomputable def punctureEnergy (G : Set ℂ) (P : Finset ℂ) (H : ℂ → ℝ) : ℝ :=
  limUnder (𝓝[>] 0) (punctureTrunc G P H)

/-- Admissibility of `H` on `(G, P)` (Definition 2.3). -/
structure PunctureAdmissible (G : Set ℂ) (P : Finset ℂ) (H : ℂ → ℝ) : Prop where
  isOpen : IsOpen G
  subset : (P : Set ℂ) ⊆ G
  c2 : ∀ x ∈ G, x ∉ (P : Set ℂ) → ContDiffAt ℝ 2 H x
  local_form : ∀ p ∈ P, ∃ s : ℂ → ℝ, ContDiffAt ℝ 1 s p ∧
    ∀ᶠ x in 𝓝[≠] p, H x = s x - Real.log ‖x - p‖
  finite_energy : ∀ ε : ℝ, 0 < ε →
    IntegrableOn (fun x => ‖gradient H x‖ ^ 2) (G \ ⋃ p ∈ P, Metric.ball p ε)

theorem univ_sdiff_iUnion_ball (P : Finset ℂ) (η : ℝ) :
    (Set.univ : Set ℂ) \ ⋃ p ∈ P, Metric.ball p η = Omega P η := by
  ext x
  simp [Omega, Metric.mem_ball, dist_eq_norm]

theorem punctureTrunc_univ_eq (P : Finset ℂ) (H : ℂ → ℝ) (η : ℝ) :
    punctureTrunc Set.univ P H η =
      (1 / 2 : ℝ) * (∫ x in Omega P η, gradSq H x) + Real.pi * P.card * Real.log η := by
  unfold punctureTrunc
  rw [univ_sdiff_iUnion_ball]
  simp only [norm_gradient_sq, gradSq]

end Sphere

end SandierSerfaty

end
