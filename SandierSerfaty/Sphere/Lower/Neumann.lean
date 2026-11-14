/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Scaling
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Defs.SquareLattice

/-!
# Squares and the Neumann puncture energy via reflection (sphere note, Definition 6.1)

* `Lower.sqAt a₀ t = a₀ + [0, t]²` (closed square) and `Lower.sqShrink a₀ t s = Q^s`, the concentric closed
  square `{x ∈ Q | dist(x, ∂Q) ≥ s}` (Definition 6.8 notation).
* `Lower.reflectPts a₀ Y`: the `4 n̄` reflected points (even reflection across the sides of `Q = a₀ + [0,t]²`,
  taken modulo the lattice `2t ℤ[i]`, i.e. the four sign changes of `y - a₀`).
* `Lower.neumannPot a₀ m Y`: the potential `u_Y`, density `m`: `x ↦ h̃(σ x)`, `σ = √m`, where `h̃` is the
  torus potential on `ℂ/√(4 n̄) ℤ[i]` of the reflected, scaled configuration `σ Y`.
* `Lower.neumannEnergy a₀ t m Y = W_{Q°}(u_Y)`, the puncture energy on the open square.
-/

open Filter Topology

public section

namespace SandierSerfaty

namespace Sphere

namespace Lower

/-- The closed square `a₀ + [0, t]²`. -/
@[expose] def sqAt (a₀ : ℂ) (t : ℝ) : Set ℂ :=
  {z | a₀.re ≤ z.re ∧ z.re ≤ a₀.re + t ∧ a₀.im ≤ z.im ∧ z.im ≤ a₀.im + t}

/-- `Q^s = {x ∈ Q | dist(x, ∂Q) ≥ s}` for `Q = a₀ + [0, t]²`: the concentric closed square of side `t - 2 s`. -/
@[expose] def sqShrink (a₀ : ℂ) (t s : ℝ) : Set ℂ :=
  sqAt (a₀ + (⟨s, s⟩ : ℂ)) (t - 2 * s)

/-- The four evenly reflected copies of `y` (through the corner `a₀`; across the sides of the square this is the
same modulo `2 t ℤ[i]`). -/
@[expose] noncomputable def reflect4 (a₀ y : ℂ) : Fin 4 → ℂ :=
  ![y, a₀ + ⟨-(y - a₀).re, (y - a₀).im⟩, a₀ + ⟨(y - a₀).re, -(y - a₀).im⟩, 2 * a₀ - y]

/-- The `4 n̄` reflected points, indexed by `Fin 4 × Fin n̄ ≃ Fin (4 n̄)`. -/
@[expose] noncomputable def reflectPts (a₀ : ℂ) {nb : ℕ} (Y : Fin nb → ℂ) : Fin (4 * nb) → ℂ :=
  fun k => reflect4 a₀ (Y (finProdFinEquiv.symm k).2) (finProdFinEquiv.symm k).1

/-- The Neumann potential `u_Y` of Definition 6.1 on `Q = a₀ + [0,t]²` with density `m` and `n̄ = nb`
points `Y`: `u_Y(x) = ũ(σ x)` with `σ = √m` and `ũ` the torus potential of the reflection of `σ Y` on the torus
`ℂ/(2 √n̄ ℤ[i]) = ℂ/√(4 n̄) ℤ[i]`. -/
@[expose] noncomputable def neumannPot (a₀ : ℂ) (m : ℝ) {nb : ℕ} (Y : Fin nb → ℂ) (x : ℂ) : ℝ :=
  torusPotential (squareLattice (4 * nb))
    (reflectPts (Real.sqrt m • a₀) (fun i => Real.sqrt m • Y i)) (Real.sqrt m • x)

/-- The Neumann puncture energy `W^Neu_Q(Y; m) = W_{Q°}(u_Y)` (Definition 6.1). -/
@[expose] noncomputable def neumannEnergy (a₀ : ℂ) (t m : ℝ) {nb : ℕ} (Y : Fin nb → ℂ) : ℝ :=
  punctureEnergy (interior (sqAt a₀ t)) (Finset.univ.image Y) (neumannPot a₀ m Y)

end Lower

end Sphere

end SandierSerfaty

end
