/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Goal
public import SandierSerfaty.Certificate.Box.Encl2
public import SandierSerfaty.Certificate.Box.NumGoal
public import SandierSerfaty.Certificate.Box.CtxIdxSound
public import SandierSerfaty.Certificate.Box.A7Idx
public import SandierSerfaty.Certificate.Box.HessIdxSound
public import SandierSerfaty.Certificate.Box.InnerIdx
public import SandierSerfaty.Certificate.Box.NumCheckIdx
public import SandierSerfaty.Certificate.Box.CertIdx

/-!
# The box assertions of the certificate

Facade of the finite checks and the derived theorems of paper §6 for the region `𝒟 = [b, .697] × [0, .65]`:

* `Prim`, `Interp`, `Rows`, `Grid`, `Outer`, `Negative`: real analysis of the assertions A7 (derivative bounds),
  A8 (outer grid: the successive 1-D interpolation, the midpoint rule) and A9 (negative part), certificate-free;
* `Eval`, `EvalSound`, `LoopSound`: the row loops (midpoint values `G` in the `Fx 128` fixed point, exact integer
  accumulators) and the static error budget of one value, including the exterior formula;
* `CtxDef`, `Radial2`, `SecondDeriv`, `CtxSound`, `CtxSound2`, `A7`: the second-derivative queries `G_dd`, `G_ss` as right
  derivatives and the derivative assertion A7 from the rectangle checks;
* `Hessian`, `HessCell`, `HessLocal`, `HessDef`, `HessSound`, `Inner`: the Hessian assertion A10: `K ≤ 2g` on `𝒟₀` from
  `theta`-increments inside the Hessian cells (no second derivative of `g`), the check, its soundness, and
  `inner_of_certificate`;
* `CtxIdx`, `CtxIdxSound`, `A7Idx`, `HessIdx`, `HessIdxSound`, `InnerIdx`: the A7 and Hessian checks with the
  checked-index lookup `Query.lookupIdx` (the generator proposes an index range per query, the kernel checks two node
  comparisons) and their soundness, with the statements of `A7` / `HessSound` / `Inner` (`derivBounds_of_a7I`,
  `hess_localHessI`, `inner_of_certificateI`); `NumCheckIdx`,
  `CertIdx`: the Booleans `a7BI`, `hessBI` and `outer_of_certificateI`, `negative_of_certificateI`;
* `KRowDef`, `KBound`: the upper bound of `K = 2 g_p(x₀)` from a row at a dyadic point near `p`;
* `EvalData`, `Cert`: `EvalHyp` from the enclosures and one Boolean test, `outer_of_certificate`,
  `negative_of_certificate`;
* `Encl2`: the producer of `Box.Encl2` (and of `ITable.Encl`) from the table chunks: `CellModel`, `TableRealized`,
  `TableRealized.encl2`;
* `NumDef`, `NumSound`, `NumCheck`, `NumScalar`, `NumGoal`: the numeric side conditions of `Goal` as `Nat`/`ℚ` Booleans
  (`outerGridB`, `negGridB`, `kRowB`, `hessB`, `a7B`, `kcB`, `outThrB`, `negThrB`, `deltaB`) and `certificateGoal_of_checks`;
* `Goal`: `certificateGoal_of_data`, the five fields of `Assembly.CertificateGoal` from the finite data.

The `decide +kernel` regression modules `Examples`, `IdxExamples` and `NumExamples` were removed by the dead-code
sweep DEAD-1.
-/

public section
