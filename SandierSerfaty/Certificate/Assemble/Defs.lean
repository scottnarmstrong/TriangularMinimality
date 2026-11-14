/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.Eval
public import SandierSerfaty.Certificate.Query.Lam

/-!
# The checks of the certificate run on the generated data

The stored table of the certificate is given by functions on the global node indices (`node i`, the cell
tuple `ct i` of the cell `[node i, node (i + 1)]`, the node tuple `nt i` at `node (i + 1)`, the checkpoint `ck i`
at the node `i`, read only at the first node of a chunk); the generated data modules realize them by binary
`cond` trees over literal blocks (`SandierSerfaty.CertData.Table.Data`). The shards check:

* `chunkB L d node ct nt ck j i`: the chunk check `Table.chunkCheck` of the `L` cells `i, …, i + L - 1` of
  segment `j ≥ 1`, from the checkpoint `ck i` to the checkpoint `ck (i + L)` (the chunk length may differ
  between segments);
* `innerB L pi node ct nt i`: the check `Table.innerCheck` of the first segment on the same cells;
* `nodesB d node K n`: node separation and nondegeneracy of `node 0, …, node n`, and the node `K j` (`j ≤ 6`)
  contains the knot enclosure `Basis.knotIV d j`;
* `optEqB o I`: the option `o` is `some I` (to state a computed enclosure as a literal, e.g. `lamEnc`).

Soundness of the assembly: `SandierSerfaty.Certificate.Assemble.Table`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Assemble

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query

/-- The nodes `node i, …, node (i + k)`. -/
def nodesFrom (node : Nat → IV 128) : Nat → Nat → List (IV 128)
  | i, 0 => [node i]
  | i, Nat.succ k => node i :: nodesFrom node (Nat.succ i) k

/-- The tuples `f i, …, f (i + k - 1)`. -/
def tupsFrom (f : Nat → Tup) : Nat → Nat → List Tup
  | _, 0 => []
  | i, Nat.succ k => f i :: tupsFrom f (Nat.succ i) k

/-- **The chunk of segment `j ≥ 1` starting at the node `i`** (chunk length `L`): the `L` steps from the
checkpoint `ck i` at `node i` to the checkpoint `ck (i + L)` at `node (i + L)`. -/
def chunkB (L : Nat) (d : BasisData) (node : Nat → IV 128) (ct nt : Nat → Tup) (ck : Nat → SState) (j i : Nat) :
    Bool :=
  chunkCheck d j (ck i) (nodesFrom node i L) (tupsFrom ct i L) (tupsFrom nt i L) (ck (Nat.add i L))

/-- **The chunk of the first segment starting at the node `i`** (exact inner form; chunk length `L`). -/
def innerB (L : Nat) (pi : IV 128) (node : Nat → IV 128) (ct nt : Nat → Tup) (i : Nat) : Bool :=
  innerCheck pi (nodesFrom node i L) (tupsFrom ct i L) (tupsFrom nt i L)

/-- `node i` is nondegenerate and lies strictly below `node (i + 1)`, for `i < m` (counting down). -/
def sepFrom (node : Nat → IV 128) : Nat → Nat → Bool
  | _, 0 => true
  | i, Nat.succ m =>
    and (and (SInt.blt (node i).lo (node i).hi) (SInt.blt (node i).hi (node (Nat.succ i)).lo))
      (sepFrom node (Nat.succ i) m)

/-- The knots `j, j + 1, …` lie in the nodes `K j, K (j + 1), …` (`cnt` of them). -/
def knotsFrom (d : BasisData) (node : Nat → IV 128) (K : Nat → Nat) : Nat → Nat → Bool
  | _, 0 => true
  | j, Nat.succ cnt => and (IV.subsetB (knotIV d j) (node (K j))) (knotsFrom d node K (Nat.succ j) cnt)

/-- **The nodes check**: `node 0, …, node n` separated and nondegenerate (the last one too), and the seven knot
enclosures inside the nodes `K 0, …, K 6`. -/
def nodesB (d : BasisData) (node : Nat → IV 128) (K : Nat → Nat) (n : Nat) : Bool :=
  and (and (sepFrom node 0 n) (SInt.blt (node n).lo (node n).hi)) (knotsFrom d node K 0 7)

/-! ### Assertion A1 by rows, with literal checkpoints

`Basis.coeffsCheck` sums the whole box in one declaration; its accumulator is threaded lazily, so the kernel term
nests once per lattice point and a box of side `2D + 1 = 513` hits the kernel's deep-recursion guard. Here the
box is summed row by row: `rowCk c` is a literal enclosure of the accumulator after the rows `0, …, c`, and every
row is recomputed from the previous checkpoint and compared with the next one (`subsetList` forces the
accumulator after each row). -/

/-- The accumulator before the row `c`: zeros for `c = 0`, else the checkpoint of the row `c - 1`. -/
def prevAcc (cnt : Nat) (rowCk : Nat → List (IV 128)) : Nat → List (IV 128)
  | 0 => zeros cnt
  | Nat.succ c => rowCk c

/-- **The row `c`** (the points `(c - D, c' - D)`, `c' ≤ 2D`) of the box sums of the modes `m₀, m₀ + 1, …`. -/
def rowB (m0 D cnt : Nat) (rowCk : Nat → List (IV 128)) (c : Nat) : Bool :=
  subsetList (rowLoop m0 D (SInt.sub ⟨false, c⟩ ⟨false, D⟩) (Nat.add (Nat.mul 2 D) 1) (prevAcc cnt rowCk c))
    (rowCk c)

/-- The rows `c, c + 1, …, c + r - 1`. -/
def rowsB (m0 D cnt : Nat) (rowCk : Nat → List (IV 128)) : Nat → Nat → Bool
  | _, 0 => true
  | c, Nat.succ r => and (rowB m0 D cnt rowCk c) (rowsB m0 D cnt rowCk (Nat.succ c) r)

/-- **The coefficients from the last checkpoint** (`[l, h]/2^128 ∋ √3` checked by squaring): the enclosures
`a^{-6m} (S_m ± E_m)/(6m)` lie in the literal list `cos`. -/
def coeffFinB (l h m0 D : Nat) (rowCk : Nat → List (IV 128)) (cos : List (IV 128)) : Bool :=
  and (IV.sqrtCheck (IV.ofNat 3 : IV 128) l h)
    (subsetList (coeffsFrom (sqrt3Half l h) D m0 (rowCk (Nat.mul 2 D))) cos)

/-- Equality of sign-magnitude integers. -/
def sintEqB (a b : SInt) : Bool := and (cond a.isNeg b.isNeg (not b.isNeg)) (Nat.beq a.mag b.mag)

/-- Equality of intervals. -/
def ivEqB (a b : IV 128) : Bool := and (sintEqB a.lo b.lo) (sintEqB a.hi b.hi)

/-- `o = some I`. -/
def optEqB : Option (IV 128) → IV 128 → Bool
  | none, _ => false
  | some a, b => ivEqB a b

end SandierSerfaty.Certificate.Assemble
