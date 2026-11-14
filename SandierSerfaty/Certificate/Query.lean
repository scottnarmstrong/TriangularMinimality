/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Taylor
public import SandierSerfaty.Certificate.Query.Cell
public import SandierSerfaty.Certificate.Query.CellSound
public import SandierSerfaty.Certificate.Query.Table
public import SandierSerfaty.Certificate.Query.FxG
public import SandierSerfaty.Certificate.Query.FxGReal
public import SandierSerfaty.Certificate.Query.FxGSound
public import SandierSerfaty.Certificate.Query.Lookup
public import SandierSerfaty.Certificate.Query.LookupSound
public import SandierSerfaty.Certificate.Query.TableBridge
public import SandierSerfaty.Certificate.Query.Const
public import SandierSerfaty.Certificate.Query.ConstSound
public import SandierSerfaty.Certificate.Query.Lam
public import SandierSerfaty.Certificate.Query.LamSound
public import SandierSerfaty.Certificate.Query.DerivG
public import SandierSerfaty.Certificate.Query.DerivGSound
public import SandierSerfaty.Certificate.Query.ExteriorSigns

/-!
# The query layer of the certificate

Facade of the queries of the kernel-checked certificate:

* `Taylor`: the first-order Taylor bound at a cell endpoint;
* `Cell`, `CellSound`, `Table`: the Taylor data `QCell` of a table cell, the check `cellCheck` tying it to the
  stored node/cell tuples, and `CellValid` (`cellCheck_sound`);
* `FxG`, `FxGReal`, `FxGSound`: the value-`G` query of the hot loop in the midpoint fixed point `Fx 128`
  (`evalG`: checked square root, checked cell, Taylor values) and its **static error budget**
  (`evalG_sound`: `|v - G(d, s)| ≤ deltaG`, one bound for every query);
* `Lookup`, `LookupSound`, `TableBridge`: the interval lookup `lookup` (hull of the cells meeting a query
  interval), the realization predicate `ITable.Encl` and the passage from the table chunks;
* `Const`, `ConstSound`: A4 (`B(l)`, the exact `f₀`, `e` at nodes) and A6 (`a6Check`, the exterior signs);
* `Lam`, `LamSound`: a coarse enclosure of `λ` (`lamEnc`, `lamEnc_sound`) by a rectangle rule with interval hulls;
* `DerivG`, `DerivGSound`: the derivative-`G` queries `gdOf`, `gsOf` on a rectangle `Dd × Ss` of `(d, s)`
  (`mkDCtx`: checked square root, `t ∈ [b, l]`, table lookup; soundness `mkDCtx_sound`, `gdOf_mem`,
  `gsOf_mem`);
* `ExteriorSigns`: `f_l_pos_slope_pos_of_certificate`, the two exterior-sign fields of `Assembly.CertificateGoal`
  from the finite data.

The regression module `Examples` was removed by the dead-code sweep DEAD-1.
-/

public section
