/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Triangular minimality for planar Coulomb renormalized energy

A standalone, Mathlib-only statement of the main results of the paper *Triangular minimality for planar
Coulomb renormalized energy*: Theorem 1.1 (the triangular lattice minimizes the renormalized energy among
all admissible fields), Theorem 1.2 (the lower bound on square tori) and Corollary 1.3 (the linear term of
the optimal logarithmic energy of `n` points on the sphere). With them we state the facts that make the
definitions meaningful (existence of the puncture limits, existence and uniqueness of the torus potential)
and the corresponding minimality results for the jellium energy of Chapter 11 of S. Serfaty, *Lectures on
Coulomb and Riesz gases* (cited as "Lectures"), in the case treated by the paper: dimension `d = 2`, the
logarithmic kernel (`s = 0`) and background density `m = 1`. The other results of Chapter 11 are not
stated here. Theorem, section and equation numbers refer to the paper unless the Lectures are named.

## Setting

* **The plane** is `ℂ`, with its Euclidean norm and Lebesgue measure `volume`. A vector field is a map
  `E : ℂ → ℂ`, `E = E₁ + i E₂`, and the gradient `gradient f` of `f : ℂ → ℝ` is `∂₁f + i ∂₂f`. A
  configuration of charges is a set `Λ : Set ℂ`, so every point is simple. Distributional equations are
  tested against smooth compactly supported real functions.
* **The sphere** `S²` is the unit sphere `Metric.sphere 0 1` of `EuclideanSpace ℝ (Fin 3)`, with the
  Euclidean norm of `ℝ³`.
* **Lattices and tori.** A lattice is a `Submodule ℤ ℂ` that is discrete and spans `ℂ` over `ℝ`
  (`DiscreteTopology Γ`, `IsZLattice ℝ Γ`). A function on the torus `ℂ/Γ` is a `Γ`-periodic function on
  `ℂ`, and integrals over the torus are integrals over a fundamental domain `torusDomain Γ`. The torus
  `T_n = ℝ²/(√n ℤ²)` of Theorem 1.2 is `ℂ / squareLattice n`, and `triangularLattice` is the lattice `Λ_△`
  of (1.5). The lattice `triangularLattice` has covolume `1`, and `squareLattice n` has covolume `n` for
  `n ≥ 1`, so they satisfy the hypotheses of the torus theorems below with `N = 1` and `N = n`. These two
  facts are elementary and are not stated as theorems here.
* **Cutoff families exist.** Families satisfying `IsCutoffFamily` exist, for instance
  `χ R x = ψ(R - |Re x|) ψ(R - |Im x|)` for one smooth `ψ : ℝ → [0, 1]` with `ψ = 0` on `(-∞, 1/4]` and
  `ψ = 1` on `[1, ∞)`. So Theorem 1.1 is not vacuous. (This is not stated as a theorem here.)
* **Values in `[-∞, +∞]`.** Energies that may be infinite take values in `EReal`.

## Energies and their normalizations

* `torusEnergy Γ a` is the energy (1.6) of `N` charges `a` on a torus `ℂ/Γ` of area `N`, built from their
  mean-zero potential `torusPotential Γ a`. Its value for the one-point triangular torus `ℂ/Λ_△` is the
  constant `triangularEnergy`, written `W_tri` below.
* `wholeEnergy χ Λ E` is the renormalized energy `W(E)` of (1.3)–(1.4) for the cutoff family `χ` of (1.1).
  Theorems 1.1 and 1.2 are stated with `W_tri` in place of the paper's triangular value `W(E_△)`;
  `paperTriangularField_spec` proves `W(E_△) = W_tri` for every cutoff family, so the two forms agree.
  The torus form does not depend on a cutoff family. Theorem 1.1 is split into two theorems, the lower
  bound `triangularEnergy_le_wholeEnergy` and the triangular value `paperTriangularField_spec`, both for
  every cutoff family; the identity `inf_{E ∈ 𝒜₁} W(E) = W(E_△)` follows at once from the two and is not
  stated as a separate formula.
* The energies of the Lectures (`cubeEnergy`, `neutralEnergy`, `jelliumEnergy`, `configEnergy`) put the
  factor `1/(4π)` in front of `∫|E|²` where the paper puts `½`, a factor `2π` smaller. The triangular value
  of the Lectures is therefore `W_tri / (2π)` (`triangularField_spec`). This is an identity for the
  triangular field only: the two energies also renormalize differently (punctured disks for the paper,
  truncated fields with nearest-neighbour radii for the Lectures), and for a general field they are related
  by an inequality, not an identity. The fields of the Lectures have the opposite sign,
  `-div E = 2π(∑_p δ_p - 1)`, so the triangular field there is `triangularField = ∇h_△ = -E_△`.
* We write `W^neu(E, 1)` for `neutralEnergy C E`, to distinguish it from the energy `W(E, 1) = W_{C₀}(E, 1)`
  of Definition 11.4 of the Lectures (`jelliumEnergy C₀ C E`). `W^neu(E, 1)` omits the term
  `C₀ (#(C ∩ □_R) - R²)` of Definition 11.4 and is `+∞` when the configuration does not have density one;
  `exists_jelliumEnergy_eq_neutralEnergy` shows that `W_{C₀}(E, 1) = W^neu(E, 1)` for every large `C₀`.

## Results

* `triangularEnergy_le_wholeEnergy` (Theorem 1.1): `W(E) ≥ W_tri` for every cutoff family and every
  `E ∈ 𝒜₁`.
* `paperTriangularField_spec` (Theorem 1.1): `E_△ ∈ 𝒜₁` and `W(E_△) = W_tri` for every cutoff family.
* `mul_triangularEnergy_le_torusEnergy` (Theorem 1.2): `𝒲_n(h) ≥ n W_tri` on the square torus `T_n`.
* `sphereLogEnergy_asymptotics` (Corollary 1.3): the asymptotic expansion of `E_log(n)`, with the constant
  `C_BHS` of (1.8).
* `tendsto_punctureFunctional`, `torusDomain_spec`, `existsUnique_isTorusPotential`, `torusPotential_spec`,
  `tendsto_torusEnergy`: the local puncture limit exists; `torusDomain Γ` is a fundamental domain; the torus
  potential exists and is unique; the torus energy is a genuine limit.
* `div_two_pi_triangularEnergy_le_neutralEnergy`, `triangularField_spec`, `configEnergy_triangularLattice`,
  `exists_jelliumEnergy_eq_neutralEnergy`: the triangular lattice minimizes the jellium energy of the
  Lectures (`d = 2`, `s = 0`, `m = 1`), for fields and for configurations, and the energy used here agrees
  with the Lectures' `W_{C₀}` for large `C₀`. (The Lectures define these energies; their minimality at the
  triangular lattice is the paper's result, transferred to the normalization of the Lectures.)
-/

public section

namespace SandierSerfatyChallenge

/-! ## Lattices, tori and the torus energy -/

section Torus

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

/-- The square lattice `√n ℤ²` of the torus `T_n = ℝ²/(√n ℤ²)` of Theorem 1.2, written as `√n ℤ[i] ⊂ ℂ`. -/
@[expose] noncomputable def squareLattice (n : ℕ) : Submodule ℤ ℂ :=
  Submodule.span ℤ {(⟨√n, 0⟩ : ℂ), ⟨0, √n⟩}

/-- The triangular lattice of covolume one (1.5):
`Λ_△ = √(2/√3) (ℤ(1, 0) + ℤ(1/2, √3/2))`. -/
@[expose] noncomputable def triangularLattice : Submodule ℤ ℂ :=
  Submodule.span ℤ {(√(2 / √3) : ℝ) • (⟨1, 0⟩ : ℂ), (√(2 / √3) : ℝ) • (⟨1 / 2, √3 / 2⟩ : ℂ)}

/-- A fundamental domain of `Γ` acting on `ℂ` by translation, for Lebesgue measure. The choice is arbitrary
(when `Γ` is a lattice, `torusDomain_spec` shows that it is a fundamental domain and that integrals of
`Γ`-periodic functions over it do not depend on the choice). -/
@[expose] noncomputable def torusDomain (Γ : Submodule ℤ ℂ) : Set ℂ :=
  Classical.epsilon fun F : Set ℂ => IsAddFundamentalDomain Γ F volume

/-- `h` is the mean-zero `Γ`-periodic solution of `-Δh = 2π(∑ᵢ δ_{a i} - 1)` on the torus `ℂ/Γ`, written in
classical form: `h` is `Γ`-periodic; it is smooth off the charges `a i + Γ`, with `Δh = 2π` there; at each
charge `h + log |· - a i|` has a finite limit, so that `h` has the singularity `-log |· - a i|`; its integral
over a fundamental domain is zero; and, by convention, `h = 0` at the charges, where the equation does not
determine it.

The paper speaks of the mean-zero periodic distributional solution; the two notions agree. If `h` satisfies
these conditions, then near a charge `a i` the function `h + log |· - a i| - (π/2) |· - a i|²` is harmonic
on a punctured disk and bounded, so it extends smoothly across `a i`. Hence `h` is `-log |· - a i|` plus a
smooth function there, and since `Δ log |·| = 2π δ₀`, `h` solves `-Δh = 2π(∑ᵢ δ_{a i} - 1)` in the sense of
distributions. Conversely, a distributional solution is smooth off the charges (Weyl's lemma) and has this
local form at each charge (cf. Lemma 2.1), so it satisfies the conditions after its value is fixed on the
null set of charges. Two solutions differ by a periodic harmonic function, a constant, which the mean-zero
condition makes `0`. -/
@[expose] def IsTorusPotential (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) (h : ℂ → ℝ) : Prop :=
  (∀ γ ∈ Γ, ∀ x, h (x + γ) = h x) ∧
  ContDiffOn ℝ ∞ h {x | ∀ i, x - a i ∉ Γ} ∧
  (∀ x, (∀ i, x - a i ∉ Γ) → Δ h x = 2 * Real.pi) ∧
  (∀ i, ∃ c : ℝ, Tendsto (fun x ↦ h x + Real.log ‖x - a i‖) (𝓝[≠] (a i)) (𝓝 c)) ∧
  (∫ x in torusDomain Γ, h x) = 0 ∧
  (∀ x, (∃ i, x - a i ∈ Γ) → h x = 0)

/-- The torus potential of the charges `a` on `ℂ/Γ`, chosen by `Classical.epsilon`. When `Γ` is a lattice of
covolume `N` and the `N` charges have pairwise distinct classes, it is the unique `h` with
`IsTorusPotential Γ a h` (`existsUnique_isTorusPotential`, `torusPotential_spec`). -/
@[expose] noncomputable def torusPotential (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) : ℂ → ℝ :=
  Classical.epsilon (IsTorusPotential Γ a)

/-- The energy (1.6) of `N` charges on the torus `ℂ/Γ`:
`lim_{η↓0} [½ ∫_{T ∖ ⋃ᵢ B(a i, η)} |∇h|² + πN log η]`, where `h` is the torus potential, `T` is the
fundamental domain `torusDomain Γ`, and the balls are removed periodically. For `Γ = √n ℤ[i]` and `N = n` it
is the energy `𝒲_n(h)` of Theorem 1.2. The limit exists and is finite (`tendsto_torusEnergy`). -/
@[expose] noncomputable def torusEnergy (Γ : Submodule ℤ ℂ) {N : ℕ} (a : Fin N → ℂ) : ℝ :=
  limUnder (𝓝[>] 0) fun η : ℝ ↦
    (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
      ‖gradient (torusPotential Γ a) x‖ ^ 2) + Real.pi * N * Real.log η

/-- `W_tri`, the energy (1.6) of the one-point triangular torus `ℂ/Λ_△` with its charge at `0`. It equals the
paper's triangular value `W(E_△)` (`paperTriangularField_spec`; cf. Lemma 2.3). -/
@[expose] noncomputable def triangularEnergy : ℝ :=
  torusEnergy triangularLattice (fun _ : Fin 1 ↦ 0)

end Torus

/-! ## The whole-plane renormalized energy -/

section Whole

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

/-- A cutoff family in the sense of (1.1): for every real `R > 1`, `χ R` is smooth with compact support,
`0 ≤ χ R ≤ 1`, the support of `χ R` lies in `K_R = [-R, R]²`, `χ R = 1` on `K_{R-1}`, and
`sup_{R>1} ‖∇(χ R)‖_∞ < ∞` (Euclidean norm of the gradient). -/
@[expose] def IsCutoffFamily (χ : ℝ → ℂ → ℝ) : Prop :=
  (∀ R : ℝ, 1 < R →
    ContDiff ℝ ∞ (χ R) ∧ HasCompactSupport (χ R) ∧
    (∀ x, 0 ≤ χ R x ∧ χ R x ≤ 1) ∧
    tsupport (χ R) ⊆ Set.Icc (-R) R ×ℂ Set.Icc (-R) R ∧
    (∀ x ∈ Set.Icc (-(R - 1)) (R - 1) ×ℂ Set.Icc (-(R - 1)) (R - 1), χ R x = 1)) ∧
  ∃ L : ℝ, ∀ R : ℝ, 1 < R → ∀ x : ℂ, ‖gradient (χ R) x‖ ≤ L

/-- The admissible class `𝒜₁` of (1.2), as a predicate on the pair `(Λ, E)` of a configuration and a field:
`Λ` is locally finite, `E` is locally integrable, and in the sense of distributions
`div E = 2π(ν_Λ - 1)` with `ν_Λ = ∑_{p ∈ Λ} δ_p` (tested against real `φ ∈ C_c^∞`:
`∫ ⟪E, ∇φ⟫ = -2π(∑_{p ∈ Λ} φ p - ∫ φ)`), `curl E = 0` (`∫ ⟪E, i∇φ⟫ = 0`), and
`sup_{R>1} ν_Λ(B_R)/|B_R| < ∞`. Here `E = E₁ + i E₂` and `∇φ = ∂₁φ + i ∂₂φ`. -/
@[expose] def IsAdmissibleField (Λ : Set ℂ) (E : ℂ → ℂ) : Prop :=
  (∀ R : ℝ, (Λ ∩ Metric.closedBall 0 R).Finite) ∧ LocallyIntegrable E volume ∧
  (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, inner ℝ (E x) (gradient φ x)) = -(2 * Real.pi * ((∑ᶠ p ∈ Λ, φ p) - (∫ x, φ x)))) ∧
  (∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ x, inner ℝ (E x) (Complex.I * gradient φ x)) = 0) ∧
  ∃ Θ : ℝ, ∀ R : ℝ, 1 < R → ((Λ ∩ Metric.ball 0 R).ncard : ℝ) ≤ Θ * (Real.pi * R ^ 2)

/-- The truncated functional `½ ∫_{ℂ ∖ ⋃_{p ∈ Λ} B(p, η)} ξ |E|² + π log η ∑_{p ∈ Λ} ξ(p)` inside the limit
in (1.3), valued in `[-∞, +∞]`. The integral of `ξ |E|²` is the difference of the lower Lebesgue integrals of
its positive and negative parts, so a non-integrable integrand gives `±∞` (or the `EReal` convention
`⊤ - ⊤ = ⊥`), never a default value `0`. -/
@[expose] noncomputable def punctureFunctional (Λ : Set ℂ) (E : ℂ → ℂ) (ξ : ℂ → ℝ) (η : ℝ) : EReal :=
  (((1 / 2 : ℝ)) : EReal) *
      (((∫⁻ x in (⋃ p ∈ Λ, Metric.ball p η)ᶜ, ENNReal.ofReal (ξ x * ‖E x‖ ^ 2) : ℝ≥0∞) : EReal) -
        ((∫⁻ x in (⋃ p ∈ Λ, Metric.ball p η)ᶜ, ENNReal.ofReal (-(ξ x * ‖E x‖ ^ 2)) : ℝ≥0∞) : EReal)) +
    ((Real.pi * Real.log η * ∑ᶠ p ∈ Λ, ξ p : ℝ) : EReal)

/-- The local energy `W(E, ξ)` of (1.3): the limit as `η ↓ 0` of `punctureFunctional Λ E ξ η`, written as a
`limsup` in `[-∞, +∞]`. For `E ∈ 𝒜₁` and smooth compactly supported `ξ`, the limit exists and is finite
(`tendsto_punctureFunctional`). -/
@[expose] noncomputable def localEnergy (Λ : Set ℂ) (E : ℂ → ℂ) (ξ : ℂ → ℝ) : EReal :=
  limsup (punctureFunctional Λ E ξ) (𝓝[>] 0)

/-- The whole-plane energy (1.4) for the cutoff family `χ`: `W(E) = limsup_{R→∞} W(E, χ_R)/|K_R|` with
`|K_R| = (2R)²`, in `[-∞, +∞]`; the puncture limit is taken first. -/
@[expose] noncomputable def wholeEnergy (χ : ℝ → ℂ → ℝ) (Λ : Set ℂ) (E : ℂ → ℂ) : EReal :=
  limsup (fun R : ℝ ↦ ((((2 * R) ^ 2)⁻¹ : ℝ) : EReal) * localEnergy Λ E (χ R)) atTop

/-- The triangular field `E_△ = -∇h_△` of Section 1, where `h_△` is the mean-zero periodic solution of
`-Δh = 2π(δ₀ - 1)` on `ℂ/Λ_△` (the torus potential of one charge at `0`). -/
@[expose] noncomputable def paperTriangularField : ℂ → ℂ :=
  fun x ↦ -(gradient (torusPotential triangularLattice (fun _ : Fin 1 ↦ 0)) x)

end Whole

/-! ## Logarithmic energy on the sphere -/

section Sphere

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

/-- The logarithmic interaction `-log ‖x - y‖` of two points of `ℝ³`, with value `+∞` for a collision. -/
@[expose] noncomputable def logPairEnergy (x y : EuclideanSpace ℝ (Fin 3)) : EReal :=
  if x = y then ⊤ else ((-Real.log ‖x - y‖ : ℝ) : EReal)

/-- The logarithmic energy `-∑_{i ≠ j} log ‖y_i - y_j‖` of `n` points of the unit sphere `S² ⊂ ℝ³`,
summed over ordered pairs, with value `+∞` if two points collide (Corollary 1.3). -/
@[expose] noncomputable def logConfigEnergy {n : ℕ}
    (y : Fin n → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EReal :=
  ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, logPairEnergy (y p.1) (y p.2)

/-- The optimal logarithmic energy `E_log(n)` of Corollary 1.3, the infimum of `logConfigEnergy` over all
`n`-point configurations on `S²`. The paper writes a minimum; it is one, since the energy is lower
semicontinuous on the compact set `(S²)ⁿ`, but attainment is not stated as a theorem here, and the
asymptotics of Corollary 1.3 concern only the value. -/
@[expose] noncomputable def sphereLogEnergy (n : ℕ) : EReal :=
  ⨅ y : Fin n → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, logConfigEnergy y

/-- The constant `C_BHS = 2 log 2 + ½ log(2/3) + 3 log(√π / Γ(1/3))` of (1.8). -/
@[expose] noncomputable def bhsConstant : ℝ :=
  2 * Real.log 2 + (1 / 2) * Real.log (2 / 3) + 3 * Real.log (Real.sqrt Real.pi / Real.Gamma (1 / 3))

end Sphere

/-! ## The jellium energy of Serfaty's lectures

The definitions of Chapter 11 of S. Serfaty, *Lectures on Coulomb and Riesz gases*, in dimension two with
the logarithmic kernel `g = -log |·|` and density `m = 1`. Configurations are sets (so their points are
simple), and integrals over the plane use Lebesgue measure. -/

section Jellium

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

/-- The class `Elec(C, 1)` of electric fields of the configuration `C` (Lectures, Definition 11.1,
(11.2.1)): `C` is locally finite, `E` is locally integrable, and `-div E = 2π(∑_{p ∈ C} δ_p - 1)` in the
sense of distributions, that is, `∫ ⟪E, ∇φ⟫ = 2π(∑_{p ∈ C} φ p - ∫ φ)` for every smooth compactly supported
real `φ`. (The sign of `E` is opposite to the paper's `𝒜₁`.) -/
@[expose] def elec (C : Set ℂ) : Set (ℂ → ℂ) :=
  {E | (∀ R : ℝ, (C ∩ Metric.closedBall 0 R).Finite) ∧ LocallyIntegrable E volume ∧
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, inner ℝ (E x) (gradient φ x)) = 2 * Real.pi * ((∑ᶠ p ∈ C, φ p) - (∫ x, φ x))}

/-- The truncated logarithm `f_η(x) = (g(x) - g(η))₊ = (-log |x| + log η)₊` (Lectures, (4.1.18)). -/
@[expose] noncomputable def truncLog (η : ℝ) (x : ℂ) : ℝ :=
  max (-Real.log ‖x‖ - -Real.log η) 0

/-- The truncated field `E_η(x) = E(x) - ∑_{p ∈ C} ∇f_{η_p}(x - p)` (Lectures, (11.2.4)), for a radius
`η_p` attached to each point `p` (the values of `η` off `C` are not used). The sum is finite at every `x`
when `C` is locally finite and `η` is bounded. -/
@[expose] noncomputable def truncField (C : Set ℂ) (η : ℂ → ℝ) (E : ℂ → ℂ) (x : ℂ) : ℂ :=
  E x - ∑ᶠ p ∈ C, gradient (truncLog (η p)) (x - p)

/-- The nearest-neighbour radius `r_p = ¼ min(min_{q ∈ C, q ≠ p} |q - p|, 1)` (Lectures, (11.2.2)). -/
@[expose] noncomputable def nnRadius (C : Set ℂ) (p : ℂ) : ℝ :=
  (1 / 4) * sInf (insert 1 ((fun q ↦ ‖q - p‖) '' (C \ {p})))

/-- The closed square `□_ℓ = [-ℓ/2, ℓ/2]²` of side length `ℓ`, centred at `0`. -/
@[expose] def cube (ℓ : ℝ) : Set ℂ :=
  Set.Icc (-(ℓ / 2)) (ℓ / 2) ×ℂ Set.Icc (-(ℓ / 2)) (ℓ / 2)

/-- The radius `r̃_p` relative to the square `□_ℓ` (Lectures, (11.2.3)): `r_p` if `p ∈ □_ℓ` and
`dist(p, ∂□_ℓ) ≥ 2`; `¼` if `p ∉ □_ℓ` or `dist(p, ∂□_ℓ) ≤ 1`; and `t r_p + (1 - t) ¼` if `p ∈ □_ℓ` and
`dist(p, ∂□_ℓ) = 1 + t` with `t ∈ [0, 1]`. -/
@[expose] noncomputable def cubeRadius (C : Set ℂ) (ℓ : ℝ) (p : ℂ) : ℝ :=
  open scoped Classical in
  if p ∈ cube ℓ ∧ 2 ≤ Metric.infDist p (frontier (cube ℓ)) then nnRadius C p
  else if p ∉ cube ℓ ∨ Metric.infDist p (frontier (cube ℓ)) ≤ 1 then 1 / 4
  else (Metric.infDist p (frontier (cube ℓ)) - 1) * nnRadius C p +
    (1 - (Metric.infDist p (frontier (cube ℓ)) - 1)) * (1 / 4)

/-- The energy of `E` in the square `□_ℓ` (Lectures, (11.2.6)):
`F^{□_ℓ}(E, 1) = (1/4π) ∫_{□_ℓ} |E_r̃|² - ½ ∑_{p ∈ C ∩ □_ℓ} g(r̃_p) - ∑_{p ∈ C ∩ □_ℓ} ∫ f_{r̃_p}(x - p) dx`,
points on the boundary of `□_ℓ` included. The field integral is a lower Lebesgue integral, so `F = +∞`
when `E_r̃` is not square integrable on `□_ℓ`. -/
@[expose] noncomputable def cubeEnergy (C : Set ℂ) (E : ℂ → ℂ) (ℓ : ℝ) : EReal :=
  ((1 / (4 * Real.pi) : ℝ) : EReal) *
      (((∫⁻ x in cube ℓ, ENNReal.ofReal (‖truncField C (cubeRadius C ℓ) E x‖ ^ 2)) : ℝ≥0∞) : EReal) +
    (((-(1 / 2 : ℝ)) * (∑ᶠ p ∈ C ∩ cube ℓ, -Real.log (cubeRadius C ℓ p)) -
      (∑ᶠ p ∈ C ∩ cube ℓ, (∫ x, truncLog (cubeRadius C ℓ p) (x - p))) : ℝ) : EReal)

/-- The neutral jellium energy at density one: `W^neu(E, 1) = limsup_{ℓ→∞} ℓ⁻² F^{□_ℓ}(E, 1)` over real
`ℓ` when the configuration has density one (`#(C ∩ □_ℓ)/ℓ² → 1`), and `+∞` otherwise. It agrees with the
energy `W(E, 1) = W_{C₀}(E, 1)` of the Lectures (Definition 11.4) for every large constant `C₀`
(`exists_jelliumEnergy_eq_neutralEnergy`); in particular `W_{C₀}(E, 1) = +∞` too when the configuration does
not have density one (cf. Lemma 11.9 of the Lectures). -/
@[expose] noncomputable def neutralEnergy (C : Set ℂ) (E : ℂ → ℂ) : EReal :=
  open scoped Classical in
  if Tendsto (fun ℓ : ℝ ↦ ((C ∩ cube ℓ).ncard : ℝ) / ℓ ^ 2) atTop (𝓝 1) then
    limsup (fun ℓ : ℝ ↦ (((ℓ ^ 2)⁻¹ : ℝ) : EReal) * cubeEnergy C E ℓ) atTop
  else ⊤

/-- The jellium energy `W_{C₀}(E, 1) = limsup_{R→∞} R⁻² [F^{□_R}(E, 1) + C₀ (#(C ∩ □_R) - R²)]` of the
Lectures (Definition 11.4, (11.2.12)), over real `R`. -/
@[expose] noncomputable def jelliumEnergy (C0 : ℝ) (C : Set ℂ) (E : ℂ → ℂ) : EReal :=
  limsup (fun R : ℝ ↦ (((R ^ 2)⁻¹ : ℝ) : EReal) *
    (cubeEnergy C E R + ((C0 * (((C ∩ cube R).ncard : ℝ) - R ^ 2) : ℝ) : EReal))) atTop

/-- The energy of a configuration (Lectures, Definition 11.6, (11.2.14)):
`𝕎(C, 1) = inf {W^neu(E, 1) : E ∈ Elec(C, 1), E a gradient}`, with `inf ∅ = +∞`. The Lectures take the
infimum of `W_{C₀}(E, 1)`; the two infima are equal for every large `C₀`, because the integrands are equal
for each `E` (`exists_jelliumEnergy_eq_neutralEnergy`). "Gradient" is meant in the sense of distributions:
`E = ∇H` for some locally integrable `H`, that is, `∫ H ∇φ = -∫ φ E` for every smooth compactly supported
real `φ`. -/
@[expose] noncomputable def configEnergy (C : Set ℂ) : EReal :=
  ⨅ (E : ℂ → ℂ) (_ : E ∈ elec C)
    (_ : ∃ H : ℂ → ℝ, LocallyIntegrable H volume ∧ ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ →
      HasCompactSupport φ → (∫ x, H x • gradient φ x) = -(∫ x, φ x • E x)),
    neutralEnergy C E

/-- The triangular field in the sign convention of the Lectures, `∇h_△ = -E_△`, where `h_△` is the
mean-zero periodic solution of `-Δh = 2π(δ₀ - 1)` on `ℂ/Λ_△`; it satisfies `-div ∇h_△ = 2π(∑_{p ∈ Λ_△} δ_p - 1)`. -/
@[expose] noncomputable def triangularField : ℂ → ℂ :=
  gradient (torusPotential triangularLattice (fun _ : Fin 1 ↦ 0))

end Jellium

/-! ## The main results -/

section Main

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

/-- **Theorem 1.1**, the lower bound. For every cutoff family `χ` as in (1.1) and every field `E ∈ 𝒜₁` (with
charges `Λ`), `W(E) ≥ W_tri` in `[-∞, +∞]`. Since `W_tri = W(E_△)` for every cutoff family
(`paperTriangularField_spec`), this is the inequality `W(E) ≥ W(E_△)` of Theorem 1.1. In particular
`W(E) = -∞` is impossible, and fields of energy `+∞` are included. -/
theorem triangularEnergy_le_wholeEnergy (χ : ℝ → ℂ → ℝ) (hχ : IsCutoffFamily χ)
    (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E) :
    (triangularEnergy : EReal) ≤ wholeEnergy χ Λ E := by
  sorry

/-- **Theorem 1.1**, the triangular value. The triangular field is admissible, `E_△ ∈ 𝒜₁` with charges
`Λ_△`, and for every cutoff family `W(E_△) = W_tri`, a real number (cf. Lemma 2.3). With
`triangularEnergy_le_wholeEnergy` this gives the rest of Theorem 1.1: the triangular value is finite and
`inf_{E ∈ 𝒜₁} W(E) = W(E_△)`, attained at `E_△`, for every cutoff family. (The infimum identity follows at
once from the two theorems and is not stated as a separate formula.) -/
theorem paperTriangularField_spec :
    IsAdmissibleField (triangularLattice : Set ℂ) paperTriangularField ∧
      ∀ χ : ℝ → ℂ → ℝ, IsCutoffFamily χ →
        wholeEnergy χ (triangularLattice : Set ℂ) paperTriangularField = (triangularEnergy : EReal) := by
  sorry

/-- **Theorem 1.2.** For every integer `n ≥ 2` and every `n` points of `T_n = ℂ/(√n ℤ[i])` with pairwise
distinct classes, the energy (1.6) of their mean-zero potential is at least `n W_tri`, which is
`n W(E_△)` by `paperTriangularField_spec`. -/
theorem mul_triangularEnergy_le_torusEnergy (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    n * triangularEnergy ≤ torusEnergy (squareLattice n) a := by
  sorry

/-- **Corollary 1.3** (spherical logarithmic energy). As `n → ∞` through the integers,
`E_log(n) = (½ - log 2) n² - (n/2) log n + C_BHS n + o(n)`: there is a remainder `r(n) = o(n)` for which the
identity holds for every `n ≥ 2`; in particular `E_log(n)` is finite for `n ≥ 2`. -/
theorem sphereLogEnergy_asymptotics :
    ∃ r : ℕ → ℝ, (r =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 2 ≤ n →
      sphereLogEnergy n =
        ((((1 / 2 : ℝ) - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + bhsConstant * n + r n : ℝ) :
          EReal) := by
  sorry

end Main

/-! ## The definitions are meaningful

The local puncture limit exists (the remark after (1.4)); the torus potential exists and is unique; and the
puncture limit (1.6) defining the torus energy exists. -/

section WellPosed

open MeasureTheory Filter Topology Asymptotics
open scoped ContDiff ENNReal

/-- The local puncture limit in (1.3) exists and is finite (Lemma 2.1, which covers every smooth compactly
supported weight): for `E ∈ 𝒜₁` and every smooth compactly supported `ξ`, of any sign,
`punctureFunctional Λ E ξ η` converges to a real number as `η ↓ 0`. So the `limsup` in `localEnergy` is a
limit. -/
theorem tendsto_punctureFunctional (Λ : Set ℂ) (E : ℂ → ℂ) (hE : IsAdmissibleField Λ E)
    (ξ : ℂ → ℝ) (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ) :
    ∃ w : ℝ, Tendsto (punctureFunctional Λ E ξ) (𝓝[>] 0) (𝓝 (w : EReal)) := by
  sorry

end WellPosed

section WellPosedTorus

open MeasureTheory Filter Topology Laplacian
open scoped ContDiff

/-- For a lattice `Γ`, `torusDomain Γ` is a fundamental domain, and the integral over it of a `Γ`-periodic
function equals its integral over any other fundamental domain. -/
theorem torusDomain_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    IsAddFundamentalDomain Γ (torusDomain Γ) volume ∧
      ∀ (F : Set ℂ), IsAddFundamentalDomain Γ F volume → ∀ f : ℂ → ℝ,
        (∀ γ ∈ Γ, ∀ x, f (x + γ) = f x) → ∫ x in torusDomain Γ, f x = ∫ x in F, f x := by
  sorry

/-- Existence and uniqueness of the torus potential, for `N` charges with pairwise distinct classes on a
lattice torus `ℂ/Γ` of area `N`. -/
theorem existsUnique_isTorusPotential (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    ∃! h : ℂ → ℝ, IsTorusPotential Γ a h := by
  sorry

/-- `torusPotential Γ a` is the torus potential: it satisfies `IsTorusPotential Γ a`, and it is the only
function that does. -/
theorem torusPotential_spec (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    IsTorusPotential Γ a (torusPotential Γ a) ∧
      ∀ h : ℂ → ℝ, IsTorusPotential Γ a h → h = torusPotential Γ a := by
  sorry

/-- The puncture limit (1.6) defining `torusEnergy` exists and is finite, for `N` charges with pairwise
distinct classes on a lattice torus `ℂ/Γ` of area `N`. -/
theorem tendsto_torusEnergy (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
    {N : ℕ} (hΓ : ZLattice.covolume Γ = N) (a : Fin N → ℂ) (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    Tendsto (fun η : ℝ ↦
        (1 / 2 : ℝ) * (∫ x in torusDomain Γ \ ⋃ i, ⋃ γ ∈ Γ, Metric.ball (a i + γ) η,
          ‖gradient (torusPotential Γ a) x‖ ^ 2) + Real.pi * N * Real.log η)
      (𝓝[>] 0) (𝓝 (torusEnergy Γ a)) := by
  sorry

end WellPosedTorus

/-! ## The jellium results

In the normalization of the Lectures the triangular value is `W_tri / (2π)`. -/

section JelliumResults

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

/-- **Minimality of the triangular lattice for the jellium energy of the Lectures, fields.** For every
configuration `C` and every `E ∈ Elec(C, 1)`, `W^neu(E, 1) ≥ W_tri / (2π)`. (The Lectures define the energy;
the minimality is the paper's result, in the normalization of the Lectures.) If `C` does not have density
one, `W^neu(E, 1) = +∞` by definition and the bound is trivial; with
`exists_jelliumEnergy_eq_neutralEnergy` the bound holds for `W_{C₀}(E, 1)` and every large `C₀`. -/
theorem div_two_pi_triangularEnergy_le_neutralEnergy (C : Set ℂ) (E : ℂ → ℂ) (hE : E ∈ elec C) :
    ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ≤ neutralEnergy C E := by
  sorry

/-- The triangular field attains the bound: `∇h_△ ∈ Elec(Λ_△, 1)` and `W^neu(∇h_△, 1) = W_tri / (2π)`
(Lectures, Proposition 11.11, with one point per period cell). -/
theorem triangularField_spec :
    triangularField ∈ elec (triangularLattice : Set ℂ) ∧
      neutralEnergy (triangularLattice : Set ℂ) triangularField =
        ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) := by
  sorry

/-- **Minimality of the triangular lattice for the jellium energy of the Lectures, configurations.**
`𝕎(Λ_△, 1) = W_tri / (2π)`, and `𝕎(Λ_△, 1) ≤ 𝕎(C, 1)` for every configuration `C` (Lectures,
Definition 11.6). -/
theorem configEnergy_triangularLattice :
    configEnergy (triangularLattice : Set ℂ) = ((triangularEnergy / (2 * Real.pi) : ℝ) : EReal) ∧
      ∀ C : Set ℂ, configEnergy (triangularLattice : Set ℂ) ≤ configEnergy C := by
  sorry

/-- The energy `W_{C₀}` of the Lectures (Definition 11.4) agrees with `neutralEnergy` for every large constant
`C₀`: there is `C₀*` such that `W_{C₀}(E, 1) = W^neu(E, 1)` for every `C₀ ≥ C₀*`, every configuration `C`
and every `E ∈ Elec(C, 1)`. So the two minimality statements above hold for `W_{C₀}` as well. -/
theorem exists_jelliumEnergy_eq_neutralEnergy :
    ∃ C0star : ℝ, ∀ C0 : ℝ, C0star ≤ C0 → ∀ (C : Set ℂ), ∀ E ∈ elec C,
      jelliumEnergy C0 C E = neutralEnergy C E := by
  sorry

end JelliumResults

end SandierSerfatyChallenge

end
