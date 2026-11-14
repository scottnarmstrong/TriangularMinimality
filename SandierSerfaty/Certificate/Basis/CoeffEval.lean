/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Arith.IV

/-!
# The lattice coefficients `c_m`: box sums in exact integers (assertion A1, evaluator)

paper `comp:coefficient-summand`
(assertion A1). For `(n, q) ≠ (0, 0)` put `A = n + 2q`, `B = n` and `W = A² + 3B² = 4(n² + nq + q²)`; then
`n ρ + q = (A + i√3 B)/2` and

  `Re (n ρ + q)^{-k} = 2^k X_k / W^k`,  `X_k + i√3 Y_k = (A + i√3 B)^k`,

where `(X_k, Y_k)` are integers computed by exact multiplication in `ℤ[√-3]` (`Z3`), as the C++ `cs` does
(`verification/core.hpp`, `re6`/`im6` and the recurrence by the sixth power). Each term is rounded outward to
`2^-P` (`IV.ofFrac`); the terms of all modes `m₀, …, m₀ + cnt - 1` are accumulated in one pass over the square
`|n|, |q| ≤ D` (`boxSums`). The coefficient is then

  `c_m ∈ a^{-6m} (S_m + [-E_m, E_m]) / (6m)`,  `E_m = 8 (4/3)^{3m} D^{2-6m} / (6m - 2)`,

with `a^{-6m} = (√3/2)^{3m}` (`tail:coefficient-square`, `Tails.abs_coeff_sub_boxSum_le`). `coeffsCheck` compares
the result with literal enclosures; its soundness (`coeffsCheck_sound`) is in
`SandierSerfaty.Certificate.Basis.CoeffSound`. `absLtOneB` is the test `|c_1| < 1`.

The definitions follow the kernel rules (`-- kernel-rules: strict`): `Nat` primitives by name, `cond`,
structural recursion, no `let`. No Mathlib import.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith

/-- An element `re + i√3 im` of `ℤ[√-3]`, with sign-magnitude parts. -/
structure Z3 where
  /-- The rational part. -/
  re : SInt
  /-- The coefficient of `i√3`. -/
  im : SInt
deriving Inhabited, Repr

namespace Z3

/-- Product: `(x + i√3 y)(u + i√3 v) = (xu - 3yv) + i√3 (xv + yu)`. -/
def mul (a b : Z3) : Z3 :=
  ⟨SInt.sub (SInt.mul a.re b.re) (SInt.mulNat (SInt.mul a.im b.im) 3),
    SInt.add (SInt.mul a.re b.im) (SInt.mul a.im b.re)⟩

/-- The unit `1`. -/
def one : Z3 := ⟨⟨false, 1⟩, ⟨false, 0⟩⟩

/-- Power by repeated multiplication. -/
def pow (a : Z3) : Nat → Z3
  | 0 => one
  | n + 1 => mul (pow a n) a

end Z3

variable {P : Nat}

/-- The term `2^k X / W^k`, rounded outward. -/
def termIV (X : SInt) (k W : Nat) : IV P := IV.ofFrac (SInt.shiftLeft X k) (Nat.pow W k)

/-- Add the terms of the modes `m, m + 1, …` (one per accumulator): `z = w₆^m` is the current power and
`k = 6 m` its exponent. -/
def accTerms (w6 : Z3) (W : Nat) : Z3 → Nat → List (IV P) → List (IV P)
  | _, _, [] => []
  | z, k, a :: as => IV.add a (termIV z.re k W) :: accTerms w6 W (Z3.mul z w6) (Nat.add k 6) as

/-- `A = n + 2q`. -/
def ptA (n q : SInt) : SInt := SInt.add n (SInt.mulNat q 2)

/-- `W = A² + 3n²`. -/
def ptW (A n : SInt) : Nat := Nat.add (Nat.mul A.mag A.mag) (Nat.mul 3 (Nat.mul n.mag n.mag))

/-- The point step with `W` and the sixth power `w₆ = (A + i√3 n)^6` passed explicitly: nothing for the
origin (`W = 0`). -/
def pointStepAux (m0 W : Nat) (w6 : Z3) (accs : List (IV P)) : List (IV P) :=
  cond (Nat.beq W 0) accs (accTerms w6 W (Z3.pow w6 m0) (Nat.mul 6 m0) accs)

/-- Add the terms of the point `(n, q)` for the modes `m₀, m₀ + 1, …`. -/
def pointStep (m0 : Nat) (n q : SInt) (accs : List (IV P)) : List (IV P) :=
  pointStepAux m0 (ptW (ptA n q) n) (Z3.pow ⟨ptA n q, n⟩ 6) accs

/-- The row `n`: the points `(n, c - D)` for `c < cnt` (called with `cnt = 2D + 1`). -/
def rowLoop (m0 D : Nat) (n : SInt) : Nat → List (IV P) → List (IV P)
  | 0, accs => accs
  | c + 1, accs => rowLoop m0 D n c (pointStep m0 n (SInt.sub ⟨false, c⟩ ⟨false, D⟩) accs)

/-- The rows `c - D` for `c < cnt` (called with `cnt = 2D + 1`). -/
def boxLoop (m0 D : Nat) : Nat → List (IV P) → List (IV P)
  | 0, accs => accs
  | c + 1, accs =>
    boxLoop m0 D c (rowLoop m0 D (SInt.sub ⟨false, c⟩ ⟨false, D⟩) (Nat.add (Nat.mul 2 D) 1) accs)

/-- `cnt` zero accumulators. -/
def zeros : Nat → List (IV P)
  | 0 => []
  | n + 1 => ⟨SInt.zero, SInt.zero⟩ :: zeros n

/-- The box sums `∑_{|n|,|q| ≤ D} Re (n ρ + q)^{-6m}` for `m = m₀, …, m₀ + cnt - 1`. -/
def boxSums (m0 cnt D : Nat) : List (IV P) :=
  boxLoop m0 D (Nat.add (Nat.mul 2 D) 1) (zeros cnt)

/-- An upper bound of `E_m 2^P = 8 (4/3)^{3m} D^{2-6m}/(6m - 2) · 2^P` (rounded up). -/
def tailRad (P m D : Nat) : Nat :=
  SInt.cdivNat (Nat.shiftLeft (Nat.mul 8 (Nat.pow 4 (Nat.mul 3 m))) P)
    (Nat.mul (Nat.mul (Nat.pow 3 (Nat.mul 3 m)) (Nat.pow D (Nat.sub (Nat.mul 6 m) 2)))
      (Nat.sub (Nat.mul 6 m) 2))

/-- Interval power by repeated multiplication. -/
def ivPow (a : IV P) : Nat → IV P
  | 0 => IV.ofNat 1
  | n + 1 => IV.mul (ivPow a n) a

/-- The enclosure `a^{-6m} (S + [-E, E])/(6m)` of `c_m`, from an enclosure `s3h` of `√3/2`
(`a^{-6m} = (√3/2)^{3m}`). -/
def coeffEncl (s3h : IV P) (m D : Nat) (S : IV P) : IV P :=
  IV.mul (ivPow s3h (Nat.mul 3 m)) (IV.divNat (IV.addRad S (tailRad P m D)) (Nat.mul 6 m))

/-- The enclosures of `c_m, c_{m+1}, …` from the box sums. -/
def coeffsFrom (s3h : IV P) (D : Nat) : Nat → List (IV P) → List (IV P)
  | _, [] => []
  | m, S :: Ss => coeffEncl s3h m D S :: coeffsFrom s3h D (Nat.add m 1) Ss

/-- Elementwise inclusion of two lists of intervals (of equal length). -/
def subsetList : List (IV P) → List (IV P) → Bool
  | [], [] => true
  | a :: as, b :: bs => and (IV.subsetB a b) (subsetList as bs)
  | _, _ => false

/-- The enclosure of `√3/2` from checked endpoints `[l, h]/2^P` of `√3`. -/
def sqrt3Half (l h : Nat) : IV P := IV.divPow2 (IV.ofNatPair l h) 1

/-- **Assertion A1** (one block): with `[l, h]/2^P ∋ √3` (checked by squaring) and `1 ≤ m₀`, `1 ≤ D`, the
literal intervals `cos` enclose `c_{m₀}, c_{m₀+1}, …` (`Basis.coeffsCheck_sound`). -/
def coeffsCheck (l h m0 D : Nat) (cos : List (IV P)) : Bool :=
  and (IV.sqrtCheck (IV.ofNat 3 : IV P) l h)
    (subsetList (coeffsFrom (sqrt3Half l h) D m0 (boxSums m0 cos.length D)) cos)

/-- `|x| < 1` for every `x` in the interval. -/
def absLtOneB (a : IV P) : Bool :=
  and (SInt.blt ⟨true, Nat.shiftLeft 1 P⟩ a.lo) (SInt.blt a.hi ⟨false, Nat.shiftLeft 1 P⟩)

end SandierSerfaty.Certificate.Basis
