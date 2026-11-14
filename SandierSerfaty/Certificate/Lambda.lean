/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Lambda.Eval
public import SandierSerfaty.Certificate.Lambda.Calculus
public import SandierSerfaty.Certificate.Lambda.Deriv
public import SandierSerfaty.Certificate.Lambda.Point
public import SandierSerfaty.Certificate.Lambda.LoopSound
public import SandierSerfaty.Certificate.Lambda.Sound
public import SandierSerfaty.Certificate.Lambda.Model
public import SandierSerfaty.Certificate.Lambda.GoalIdx

/-!
# The fine certified enclosure of `λ`

Facade of the paper's certified computation of `λ` with enclosure width of order
`10⁻⁶`, used by the box layer (the exterior signs A4–A6 keep the coarse `Query.lamEnc`):

* `Eval`: the evaluator `lamFine` (strict kernel rules): the formula `cal:constants` multiplied out, the origin
  term `comp:lambda-origin` on `[0, s₀]`, midpoint sums with per-step error bounds `comp:lambda-derivatives` on
  `[s₀, x₀]` and `[0, x₀]`, second-order Taylor values at table nodes from the node tuples;
* `Calculus`: Taylor bounds from ranges of one-sided second derivatives and the midpoint rule with a Lipschitz
  derivative;
* `Deriv`: the derivatives of the two integrands and the bounds `|q''| ≤ C'/p² + 8C/(p s²)`,
  `Lip((e ∘ t)') ≤ E' + E/p`;
* `Point`: the realization `FRealized` (box realization + node tuples) and the soundness of the point evaluations
  and of the bound lookup;
* `LoopSound`: the two midpoint sums;
* `Sound`: **`lamFine_sound`** (`Calibration.lam ∈ lamFine …`);
* `Model`: the realization `TableModel` of the whole table by the segment models (the first segment transferred
  from its inner closed form), and `TableRealized`, `FRealized`, `QRealizes` from it;
* `GoalIdx`: **`certificateGoal_of_checks''`**, the final assembly from Boolean checks and the table model, with the
  fine `λ` and the checked-index A7 and Hessian rows.

The primed assembly `Goal` and the regression module `Examples` were removed by the dead-code sweep DEAD-1.
-/

public section
