/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.CoeffEval
public import SandierSerfaty.Certificate.Basis.CoeffSound
public import SandierSerfaty.Certificate.Basis.Eval
public import SandierSerfaty.Certificate.Basis.Sound
public import SandierSerfaty.Certificate.Basis.Deriv
public import SandierSerfaty.Certificate.Basis.Core
public import SandierSerfaty.Certificate.Basis.CoreSound
public import SandierSerfaty.Certificate.Basis.Data
public import SandierSerfaty.Certificate.Basis.DataSound

/-!
# The radial basis of the certificate: coefficients (A1), pieces, finite core (A2)

Facade of the basis layer of the kernel-checked certificate:

* `CoeffEval`, `CoeffSound` (assertion A1): exact-integer box sums of the lattice coefficients `c_m` with the
  tail bound `tail:coefficient-square`; `coeffsCheck_sound`, and `absLtOneB_sound` for `|c_1| < 1`;
* `Eval`, `Sound`: the jets on a cell of the pieces `Cal.Piece.u i j`, `Cal.Piece.D i j` and of
  `B̃ = ∑_{i ≤ 38} Piece.u i j` (`basis`, `basis_sound`), mirroring `Cal.Piece.*` segment by segment;
* `Data`, `DataSound`: the interval constants of the basis from `π`, `p`, `R₀` and the coefficients
  (`mkData_valid`), and their transfer to literal constants (`BasisData.Valid.of_subB`);
* `Deriv`: classical derivatives from jet enclosures on nondegenerate cells;
* `Core`, `CoreSound` (assertion A2): the finite-core test `tail:finite-core-premise` with covering
  (`coreSegCheck_sound`, `coreBounds_of_checks`: the fields of `Tails.FiniteCore` written out).

The regression module `Examples` was removed by the dead-code sweep DEAD-1.
-/

public section
