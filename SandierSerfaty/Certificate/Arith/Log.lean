/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.IV

/-!
# Enclosures of the logarithm

The logarithm is evaluated through the series
`log (1 + w) - log (1 - w) = Σ_k 2 w^(2k+1) / (2k+1)` (Mathlib `Real.hasSum_log_sub_log_of_abs_lt_one`),
with the argument reduced by a power of two.

* `atanhLo a b W N` / `atanhHi a b W N` (`0 ≤ a < b`, `w = a/b`): lower and upper bounds of
  `(log (1 + w) - log (1 - w))·2^W` from `N` terms, with the powers `w^(2k+1)·2^W` rounded down
  (resp. up) and, for the upper bound, the tail `2 w^(2N+1) / ((2N+1)(1 - w²))` added.
* `logPoint P G N l2lo l2hi m`: an enclosure of `log (m / 2^P)` (`0 < m`) at precision `2^-P`, computed with
  `G` guard bits from `y = m / 2^s ∈ [2/3, 4/3)` (`s` from `Nat.log2 m`), so `|w| ≤ 1/5`, and an enclosure
  `[l2lo, l2hi] / 2^(P+G)` of `log 2`.
* `IV.logPos a`: an enclosure of `log x` for every `x ∈ a` (`0 < a.lo`), from the two endpoints (`log` is
  increasing).
* `log2Lo144`, `log2Hi144`: the literal enclosure of `log 2` at `2^-144` used at `P = 128`, `G = 16`.

The choice of `s` and of `N` affects only the width: the laws in `SandierSerfaty.Certificate.Arith.LogLemmas`
hold for every input. The definitions follow the kernel rules of `SandierSerfaty.Certificate.Arith.SInt`.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Arith

/-- Lower bound chain: `p ≤ w^(2k+1)·2^W`, `acc ≤ Σ_{i<k} 2 w^(2i+1)/(2i+1)·2^W`; `a2 = a²`, `b2 = b²`. -/
def atanhLoAux (a2 b2 : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, k, p, acc =>
    atanhLoAux a2 b2 n (Nat.add k 1) (Nat.div (Nat.mul p a2) b2)
      (Nat.add acc (Nat.div (Nat.mul 2 p) (Nat.add (Nat.mul 2 k) 1)))

/-- Upper bound chain: `p ≥ w^(2k+1)·2^W`, `acc ≥ Σ_{i<k} 2 w^(2i+1)/(2i+1)·2^W`; at the end the tail
`2 p b² / ((2k+1)(b² - a²))` (rounded up) is added. -/
def atanhHiAux (a2 b2 : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, k, p, acc =>
    Nat.add acc (SInt.cdivNat (Nat.mul (Nat.mul 2 p) b2) (Nat.mul (Nat.add (Nat.mul 2 k) 1) (Nat.sub b2 a2)))
  | n + 1, k, p, acc =>
    atanhHiAux a2 b2 n (Nat.add k 1) (SInt.cdivNat (Nat.mul p a2) b2)
      (Nat.add acc (SInt.cdivNat (Nat.mul 2 p) (Nat.add (Nat.mul 2 k) 1)))

/-- A lower bound of `(log (1 + a/b) - log (1 - a/b))·2^W` from `N` terms. -/
def atanhLo (a b W N : Nat) : Nat :=
  atanhLoAux (Nat.mul a a) (Nat.mul b b) N 0 (Nat.div (Nat.shiftLeft a W) b) 0

/-- An upper bound of `(log (1 + a/b) - log (1 - a/b))·2^W` from `N` terms and the tail bound. -/
def atanhHi (a b W N : Nat) : Nat :=
  atanhHiAux (Nat.mul a a) (Nat.mul b b) N 0 (SInt.cdivNat (Nat.shiftLeft a W) b) 0

/-- The reduction exponent: `s = ⌊log₂ m⌋ + 1` if `3m ≥ 4·2^⌊log₂ m⌋`, else `⌊log₂ m⌋`, so that
`m / 2^s ∈ [2/3, 4/3)`. Any `s` gives a sound enclosure; this one gives `|w| ≤ 1/5`. -/
def logShift (m : Nat) : Nat :=
  cond (Nat.ble (Nat.shiftLeft 4 (Nat.log2 m)) (Nat.mul 3 m)) (Nat.add (Nat.log2 m) 1) (Nat.log2 m)

/-- The signed integer `s - P`. -/
def shiftDiff (s P : Nat) : SInt := cond (Nat.ble P s) ⟨false, Nat.sub s P⟩ ⟨true, Nat.sub P s⟩

/-- Lower endpoint (scaled by `2^(P+G)`) of `log (m / 2^s)`, `t = 2^s`. -/
def logYLo (W N m t : Nat) : SInt :=
  cond (Nat.ble t m) ⟨false, atanhLo (Nat.sub m t) (Nat.add m t) W N⟩
    ⟨true, atanhHi (Nat.sub t m) (Nat.add m t) W N⟩

/-- Upper endpoint (scaled by `2^(P+G)`) of `log (m / 2^s)`, `t = 2^s`. -/
def logYHi (W N m t : Nat) : SInt :=
  cond (Nat.ble t m) ⟨false, atanhHi (Nat.sub m t) (Nat.add m t) W N⟩
    ⟨true, atanhLo (Nat.sub t m) (Nat.add m t) W N⟩

/-- Lower endpoint (scaled by `2^W`) of `c · log 2` for a signed integer `c`. -/
def mulLog2Lo (c : SInt) (l2lo l2hi : Nat) : SInt :=
  cond c.isNeg ⟨true, Nat.mul c.mag l2hi⟩ ⟨false, Nat.mul c.mag l2lo⟩

/-- Upper endpoint (scaled by `2^W`) of `c · log 2` for a signed integer `c`. -/
def mulLog2Hi (c : SInt) (l2lo l2hi : Nat) : SInt :=
  cond c.isNeg ⟨true, Nat.mul c.mag l2lo⟩ ⟨false, Nat.mul c.mag l2hi⟩

/-- An enclosure of `log (m / 2^P)` (for `0 < m`) at precision `2^-P`: `G` guard bits, `N` series terms, and
`[l2lo, l2hi] / 2^(P+G)` an enclosure of `log 2`. -/
def logPoint (P G N l2lo l2hi m : Nat) : IV P :=
  ⟨SInt.fshift (SInt.add (logYLo (Nat.add P G) N m (Nat.shiftLeft 1 (logShift m)))
      (mulLog2Lo (shiftDiff (logShift m) P) l2lo l2hi)) G,
    SInt.cshift (SInt.add (logYHi (Nat.add P G) N m (Nat.shiftLeft 1 (logShift m)))
      (mulLog2Hi (shiftDiff (logShift m) P) l2lo l2hi)) G⟩

/-- A lower literal of `log 2 · 2^144` (the value of `atanhLo 1 3 144 50`, checked in `LogLemmas`). -/
def log2Lo144 : Nat := 15457698658747239244624307340191628289589468

/-- An upper literal of `log 2 · 2^144` (the value of `atanhHi 1 3 144 50`, checked in `LogLemmas`). -/
def log2Hi144 : Nat := 15457698658747239244624307340191628289589522

namespace IV

/-- An enclosure of `log x` for every `x ∈ a`, for `0 < a.lo` (checked by `IV.posB`), at `P = 128` with
`16` guard bits and `32` series terms. -/
def logPos (a : IV 128) : IV 128 :=
  ⟨(logPoint 128 16 32 log2Lo144 log2Hi144 a.lo.mag).lo,
    (logPoint 128 16 32 log2Lo144 log2Hi144 a.hi.mag).hi⟩

end IV

end SandierSerfaty.Certificate.Arith
