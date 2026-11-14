/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.FxLemmas
public import SandierSerfaty.Certificate.Arith.IVLemmas
public import SandierSerfaty.Certificate.Arith.LogLemmas
public import SandierSerfaty.Certificate.Arith.Pi

/-!
# The certificate arithmetic

Facade of the arithmetic core of the kernel-checked certificate:

* `SInt` (sign-magnitude integers) and its laws `SIntLemmas`;
* `IV P`: exact-endpoint intervals with inclusion laws (`IVLemmas`);
* `Fx P`: the midpoint fixed point of the hot loop with one-ulp error laws, a lawful `CertArith` backend
  (`FxLemmas`);
* `Log`/`LogLemmas`: enclosures of `log`; `Pi`: the `IV 128` enclosure of `π`;
* the arithmetic interface `Interface` (`CertArith`, `LawfulCertArith`) and `PiHigh` (`atanS`, Machin bounds).

The computational modules (`SInt`, `IV`, `Fx`, `Log`) import no Mathlib and follow the kernel rules checked by
`scripts/check_kernel_rules.py`; `Examples` holds cross-module `decide +kernel` regression checks.
-/

public section
