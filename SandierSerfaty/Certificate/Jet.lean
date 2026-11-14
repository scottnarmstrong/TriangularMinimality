/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Jet.IJet
public import SandierSerfaty.Certificate.Jet.Encl
public import SandierSerfaty.Certificate.Jet.Comp
public import SandierSerfaty.Certificate.Jet.Poly

/-!
# Interval Taylor jets of the certificate

Facade of the jet layer of the kernel-checked certificate:

* `IJet` (`IJet`): order-three interval Taylor jets `(c0, c1, c2, c3)` with the operations of the C++ jets of
  `verification/core.hpp` (sums, products, powers, composition with `1/·`, `log`, `√`, division by a positive
  jet, `cpol`, `der` into the order-two jets `IJet2`), written to the kernel rules (no Mathlib);
* `JetEncl` (`Encl`): `JetEncl T F J`, the jet `J` encloses `F, F', F''/2, F'''/6` on `T` through
  `Tails.Jet3` derivative witnesses; the laws of the linear and product operations, `der`, and hulls;
* `Comp`: the Faà di Bruno law of composition and the laws of `invPos`, `divPos`, `log`, `sqrt`;
* `Poly`: the laws of Horner evaluation, the Taylor shift and `cpol`.

The regression module `Examples` was removed by the dead-code sweep DEAD-1.
-/

public section
