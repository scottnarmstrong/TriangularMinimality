/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Eval

/-!
# The exterior signs (assertion A6): the interval evaluator

paper `comp:tail-signs`: `f(l) = f₀(l) - λ l²/2 - μ > 0` and
`-π B(l) - λ/2 > 0`. With `μ = f₀(R₀) - e(R₀)/3 - λ R₀²/2` (`cal:constants`) and `l = R₀ + 19/250`,

  `f(l) = f₀(l) - f₀(R₀) + e(R₀)/3 - λ (19/250)(2R₀ + 19/250)/2`,   `slope = -π B(l) - λ/2`.

`fLEnc`, `slopeEnc` evaluate these on enclosures of `f₀(l)`, `f₀(R₀)`, `e(R₀)`, `B(l)`, `λ`, `π`, `R₀`;
`a6Check` tests the two enclosures for positivity. Soundness: `SandierSerfaty.Certificate.Query.ConstSound`.
Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis

/-- `l² - R₀² = (19/250)(2R₀ + 19/250)`. -/
def lSqSubR2 (r0 : IV 128) : IV 128 :=
  IV.mul (frac false 19 250) (IV.add (IV.mulNat r0 2) (frac false 19 250))

/-- `f(l) = f₀(l) - f₀(R₀) + e(R₀)/3 - λ (l² - R₀²)/2`. -/
def fLEnc (r0 f0l f0R eR lam : IV 128) : IV 128 :=
  IV.sub (IV.add (IV.sub f0l f0R) (IV.divNat eR 3)) (IV.divPow2 (IV.mul lam (lSqSubR2 r0)) 1)

/-- `-π B(l) - λ/2`. -/
def slopeEnc (pi bl lam : IV 128) : IV 128 := IV.sub (IV.neg (IV.mul pi bl)) (IV.divPow2 lam 1)

/-- `μ = f₀(R₀) - e(R₀)/3 - λ R₀²/2` (`cal:constants`). -/
def muEnc (r0 f0R eR lam : IV 128) : IV 128 :=
  IV.sub (IV.sub f0R (IV.divNat eR 3)) (IV.divPow2 (IV.mul lam (IV.sq r0)) 1)

/-- **The test A6**: both enclosures are positive. -/
def a6Check (pi r0 f0l f0R eR bl lam : IV 128) : Bool :=
  and (IV.posB (fLEnc r0 f0l f0R eR lam)) (IV.posB (slopeEnc pi bl lam))

end SandierSerfaty.Certificate.Query
