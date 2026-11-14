/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Eval

/-!
# `Nat`-level checks of the numeric side conditions of the box assertions

The grids of the outer / negative-part / `K` / Hessian assertions are given by mantissas `m : ℕ` (the node is
`m / 2^128`). The numeric side conditions of `Box.certificateGoal_of_data` (grid steps, monotonicity, comparisons with
rational literals, the fourth-power closeness facts) are inequalities between such nodes and rational literals; here they
are `Nat` Booleans (kernel primitives by name, no `Int`), soundness in `NumSound`:

* `allLt f n`: `∀ j < n, f j`; `monoB`, `stepB`: the nodes are nondecreasing / have steps `≤ sh / 2^128`;
* `leLitB m num den`: `m / 2^128 ≤ num / den`; `geLitB m num den`: `num / den ≤ m / 2^128`;
* `closeLoB`, `closeHiB`: `((m - r)/2^128)^4 ≤ 1/q` and `1/q ≤ ((m + r)/2^128)^4` (the closeness of a dyadic node to
  `p` or `x₀`, `p⁴ = 1/12`, `x₀⁴ = 1/108`).
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Box

/-- `2^128`. -/
def bigP : Nat := Nat.shiftLeft 1 128

/-- `f 0 ∧ … ∧ f (n - 1)`. -/
def allLt (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | Nat.succ n => and (allLt f n) (f n)

/-- The conjunction of a list of Booleans. -/
def andL : List Bool → Bool
  | [] => true
  | b :: bs => and b (andL bs)

/-- `m / 2^128 - num / den ≤ r / 2^128`. -/
def subLeB (m num den r : Nat) : Bool :=
  Nat.ble (Nat.mul m den) (Nat.add (Nat.mul num bigP) (Nat.mul r den))

/-- `m / 2^128 ≤ num / den + r / 2^129`. -/
def nearB (m num den r : Nat) : Bool :=
  Nat.ble (Nat.mul (Nat.mul 2 m) den) (Nat.add (Nat.mul (Nat.mul 2 num) bigP) (Nat.mul r den))

/-- The mantissas `sm 0, …, sm n` are nondecreasing. -/
def monoB (sm : Nat → Nat) (n : Nat) : Bool := allLt (fun k => Nat.ble (sm k) (sm (Nat.succ k))) n

/-- The steps of the nodes `sm 0, …, sm n` are at most `sh` (units `2^-128`). -/
def stepB (sm : Nat → Nat) (n sh : Nat) : Bool :=
  allLt (fun k => Nat.ble (sm (Nat.succ k)) (Nat.add (sm k) sh)) n

/-- `m / 2^128 ≤ num / den`. -/
def leLitB (m num den : Nat) : Bool := Nat.ble (Nat.mul m den) (Nat.mul num bigP)

/-- `num / den ≤ m / 2^128`. -/
def geLitB (m num den : Nat) : Bool := Nat.ble (Nat.mul num bigP) (Nat.mul m den)

/-- `(m - r)/2^128` is a lower approximation of the fourth root of `1/q`: `r ≤ m` and `((m - r)/2^128)^4 ≤ 1/q`. -/
def closeLoB (m r q : Nat) : Bool :=
  and (Nat.ble r m) (Nat.ble (Nat.mul q (Nat.pow (Nat.sub m r) 4)) (Nat.pow bigP 4))

/-- `(m + r)/2^128` is an upper approximation of the fourth root of `1/q`: `1/q ≤ ((m + r)/2^128)^4`. -/
def closeHiB (m r q : Nat) : Bool := Nat.ble (Nat.pow bigP 4) (Nat.mul q (Nat.pow (Nat.add m r) 4))

end SandierSerfaty.Certificate.Box
