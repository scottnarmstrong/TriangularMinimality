/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.TruncField
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Local energies and weak charge fields

Definitions of the screening layer, in the
book's sign convention (as in `SandierSerfaty.elec`):

* `SandierSerfaty.tauM m r = π log r - π² m r²`, the self-energy correction of a charge truncated at
  radius `r` against a background of density `m` (`= 2π(-½ g(r) - m ∫ f_r)`);
* `SandierSerfaty.locEnergy m C α E D = ½ ∫_D |E_α|² + ∑_{p ∈ C ∩ D} τ_m(α_p)` (comparison note's `G_D(α)`);
* `SandierSerfaty.IsChargeField U m C E`: `-div E = 2π (∑_{p ∈ C} δ_p - m)` weakly in `U`;
* `SandierSerfaty.IsNeumannChargeField Q m Y E`: the zero-flux version on a closed set `Q`;
* `SandierSerfaty.cQuarter m = -τ_m(¼) = π log 4 + π² m / 16`;
* `SandierSerfaty.truncInteraction C α β`, the interaction term of Lemma 4.13 (field form).

`SandierSerfaty.isChargeField_of_mem_elec`: every `E ∈ elec C` is a charge field of density `1` in
every set `U`.
-/

open MeasureTheory Metric
open scoped ContDiff ENNReal NNReal

public section

namespace SandierSerfaty

/-- `τ_m(r) = π log r - π² m r² = 2π(-½ g(r) - m ∫ f_r)`. -/
@[expose] noncomputable def tauM (m r : ℝ) : ℝ := Real.pi * Real.log r - Real.pi ^ 2 * m * r ^ 2

/-- `G^m_D(α) = ½ ∫_D |E_α|² + ∑_{p ∈ C ∩ D} τ_m(α_p)` (`= 2π F` for `D = □_ℓ`, `α = r̃`, `m = 1`).
The field integral is a lower Lebesgue integral, so `G = +∞` when `E_α ∉ L²(D)`. -/
@[expose] noncomputable def locEnergy (m : ℝ) (C : Set ℂ) (α : ℂ → ℝ) (E : ℂ → ℂ) (D : Set ℂ) :
    EReal :=
  ((1 / 2 : ℝ) : EReal) *
      (((∫⁻ x in D, ENNReal.ofReal (‖truncField C α E x‖ ^ 2)) : ℝ≥0∞) : EReal) +
    ((∑ᶠ p ∈ C ∩ D, tauM m (α p) : ℝ) : EReal)

/-- `-div E = 2π(∑_{p∈C} δ_p - m)` weakly in the set `U` (book sign, as in `elec`): `E` is locally
integrable on `U` and the identity holds for smooth compactly supported test functions supported
in `U`. -/
@[expose] def IsChargeField (U : Set ℂ) (m : ℝ) (C : Set ℂ) (E : ℂ → ℂ) : Prop :=
  LocallyIntegrableOn E U volume ∧
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ x, inner ℝ (E x) (gradient φ x)) = 2 * Real.pi * ((∑ᶠ p ∈ C, φ p) - m * ∫ x, φ x)

/-- Zero-flux (Neumann) charge field on the closed set `Q`: `-div E = 2π (∑_{y ∈ Y} δ_y - m)` in `Q`
with zero normal flux, tested against restrictions to `Q` of smooth compactly supported functions
(no traces, no `H¹`). -/
@[expose] def IsNeumannChargeField (Q : Set ℂ) (m : ℝ) (Y : Finset ℂ) (E : ℂ → ℂ) : Prop :=
  IntegrableOn E Q volume ∧
    ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x in Q, inner ℝ (E x) (gradient φ x)) =
        2 * Real.pi * ((∑ y ∈ Y, φ y) - m * ∫ x in Q, φ x)

/-- `c₀(m) = -τ_m(¼) = π log 4 + π² m / 16`. -/
@[expose] noncomputable def cQuarter (m : ℝ) : ℝ := -tauM m (1 / 4)

/-- The interaction term of Lemma 4.13 (field form):
`π ∑_{i : α_i < β_i} ∑_{q ≠ i} ⟨f_{α_i,β_i}(·-i), δ_q^{(α_q)} + δ_q^{(β_q)}⟩`, with
`f_{α,β} = f_α - f_β` and `δ_q^{(r)}` the normalized arclength measure on `∂B(q, r)`. -/
@[expose] noncomputable def truncInteraction (C : Set ℂ) (α β : ℂ → ℝ) : ℝ :=
  Real.pi * ∑ᶠ i ∈ {p ∈ C | α p < β p}, ∑ᶠ q ∈ C \ {i},
    (Real.circleAverage (fun x ↦ truncLog (α i) (x - i) - truncLog (β i) (x - i)) q (α q) +
      Real.circleAverage (fun x ↦ truncLog (α i) (x - i) - truncLog (β i) (x - i)) q (β q))

/-- **I0.** Every `E ∈ elec C` is a charge field of density `1` in every set `U`. -/
theorem isChargeField_of_mem_elec {C : Set ℂ} {E : ℂ → ℂ} (hE : E ∈ elec C) (U : Set ℂ) :
    IsChargeField U 1 C E :=
  ⟨hE.2.1.locallyIntegrableOn U, fun φ hφ hc _ ↦ by rw [hE.2.2 φ hφ hc, one_mul]⟩

theorem cQuarter_eq (m : ℝ) : cQuarter m = Real.pi * Real.log 4 + Real.pi ^ 2 * m / 16 := by
  unfold cQuarter tauM
  rw [one_div, Real.log_inv]
  ring

end SandierSerfaty

end
