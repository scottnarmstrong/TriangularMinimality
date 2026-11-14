/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.Lookup
public import SandierSerfaty.Certificate.Basis.Eval

/-!
# The fine certified enclosure of `λ` (paper `comp:lambda-origin`, `comp:lambda-derivatives`, `comp:K-quadrature`)

`λ` is evaluated from its defining formula `cal:constants`, multiplied out as
(`Calibration.lam_mul_x₀`)

  `λ x₀ = (f₀(R₀) - f₀(p))/x₀ - x₀ e(R₀)/p² + ∫₀^{x₀} q + (1/p²) ∫₀^{x₀} e(t(s)) ds`,

with `t(s) = √(p² + s²)` and `q(s) = (f₀(t(s)) - f₀(p))/s²`, exactly as in the paper:

* `∫₀^{s₀} q`, `s₀ = 1/100`, by the Taylor enclosure `comp:lambda-origin` (`originEnc`;
  `Calibration.lambda_origin`): `f₀'(p)` from the table, the range of `f₀''` on `[p, t(s₀)]` by a lookup;
* `∫_{s₀}^{x₀} q` by a midpoint sum with `Nq` equal steps (`qSum`), each step with the symmetric error
  `h³ M_k/24`, `M_k = C'/p² + 8C/(p σ_k²)` (`comp:lambda-derivatives`, with the step's left end `σ_k` in place of
  `s₀`);
* `∫₀^{x₀} e(t)` by a midpoint sum with `Ne` equal steps (`eSum`), error `h³ (E' + E/p)/24` per step;
* the values at the midpoints by the *second-order* Taylor expansion at a table node `y = a_{i+1}`:
  `f₀(t) ∈ f₀(y) + f₀'(y)(t - y) + Θ (t - y)²/2` with the node tuple `nt i` (value and derivative at `a_{i+1}`,
  tiny radii) and `Θ` the hull of the second-derivative enclosures of the two cells `i`, `i + 1` (`fAt`, `eAt`);
  the point `t` must lie in `[a_i, a_{i+2}]` (`pairOK`, checked on the outward node intervals). The index is
  found by a monotone walk (`locate`; untrusted, only the check is used by the proof);
* `C, C', E, E'` (the sup bounds of `|f₀'|, |f₀''|, |e'|, |e''|` on `[p, R₀]`) from one lookup over `[p, R₀]`.

Every table enclosure is widened by `rad` (`≥ 10⁻¹¹·2^128`, the infinite-mode error,
`Tails.uniform_error_of_finiteCore`), so the result encloses the exact `λ` (`Lambda.Sound.lamFine_sound`).
Kernel rules: strict (no `let`, `Nat` primitives by name, `cond`, structural recursion only).
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query

/-- The radial table with its node tuples: `nt i` encloses the value and the derivatives at the right node
`a_{i+1}` of cell `i` (the node tuples of `Table.TableEncloses`). -/
structure FTable where
  /-- Nodes and cell tuples. -/
  T : ITable
  /-- The node tuple at `a_{i+1}`. -/
  nt : Nat → Tup

/-! ### Points of the table -/

/-- The cells `i`, `i + 1` exist and `X ⊆ [node_i.hi, node_{i+2}.lo]` (so every `t ∈ X` lies in `[a_i, a_{i+2}]`). -/
def pairOK (F : FTable) (i : Nat) (X : IV 128) : Bool :=
  and (Nat.blt (Nat.succ i) F.T.n)
    (and (SInt.ble (F.T.node i).hi X.lo) (SInt.ble X.hi (F.T.node (Nat.succ (Nat.succ i))).lo))

/-- `X` lies left of the midpoint of `[a_{i+1}, a_{i+2}]` (a preference only: it centres the expansion). -/
def leftHalf (F : FTable) (i : Nat) (X : IV 128) : Bool :=
  SInt.ble (SInt.add X.hi X.hi) (SInt.add (F.T.node (Nat.succ i)).hi (F.T.node (Nat.succ (Nat.succ i))).lo)

/-- The first index `≥ i` (at most `fuel` tries) passing `pairOK` with `X` in the left half of the second cell
(so that `X` is near `a_{i+1}`), or the last tried. Untrusted: only `pairOK` is used by the proof. -/
def seek (F : FTable) (X : IV 128) : Nat → Nat → Nat
  | 0, i => i
  | Nat.succ fuel, i => cond (and (pairOK F i X) (leftHalf F i X)) i (seek F X fuel (Nat.succ i))

/-- The walk from `i` (at most `n` tries). -/
def locate (F : FTable) (X : IV 128) (i : Nat) : Nat := seek F X F.T.n i

/-- The second-derivative hull of `f₀` on the cells `i`, `i + 1`, widened by `rad`. -/
def f2Hull (F : FTable) (rad i : Nat) : IV 128 :=
  IV.addRad (IV.hull (F.T.cell i).f2 (F.T.cell (Nat.succ i)).f2) rad

/-- The (right) second-derivative hull of `e` on the cells `i`, `i + 1`, widened by `rad`. -/
def e2Hull (F : FTable) (rad i : Nat) : IV 128 :=
  IV.addRad (IV.hull (F.T.cell i).e2 (F.T.cell (Nat.succ i)).e2) rad

/-- `v + d₁ D + c₂ D²/2`. -/
def taylor2 (v d1 c2 D : IV 128) : IV 128 :=
  IV.add (IV.add v (IV.mul d1 D)) (IV.divPow2 (IV.mul c2 (IV.sq D)) 1)

/-- `X - a_{i+1}`. -/
def offset (F : FTable) (i : Nat) (X : IV 128) : IV 128 := IV.sub X (F.T.node (Nat.succ i))

/-- `f₀(t)` for `t ∈ X`, by the expansion at `a_{i+1}`. -/
def fAt (F : FTable) (rad i : Nat) (X : IV 128) : IV 128 :=
  taylor2 (IV.addRad (F.nt i).f0 rad) (IV.addRad (F.nt i).f1 rad) (f2Hull F rad i) (offset F i X)

/-- `e(t)` for `t ∈ X`, by the expansion at `a_{i+1}`. -/
def eAt (F : FTable) (rad i : Nat) (X : IV 128) : IV 128 :=
  taylor2 (IV.addRad (F.nt i).e0 rad) (IV.addRad (F.nt i).e1 rad) (e2Hull F rad i) (offset F i X)

/-- `f₀'(t)` for `t ∈ X`, by the expansion at `a_{i+1}`. -/
def f1At (F : FTable) (rad i : Nat) (X : IV 128) : IV 128 :=
  IV.add (IV.addRad (F.nt i).f1 rad) (IV.mul (f2Hull F rad i) (offset F i X))

/-- `f₀` at a point set `X`, in the pair `i` (checked). -/
def fPtAt (F : FTable) (rad : Nat) (X : IV 128) (i : Nat) : Option (IV 128) :=
  cond (pairOK F i X) (some (fAt F rad i X)) none

/-- `e` at a point set `X`, in the pair `i` (checked). -/
def ePtAt (F : FTable) (rad : Nat) (X : IV 128) (i : Nat) : Option (IV 128) :=
  cond (pairOK F i X) (some (eAt F rad i X)) none

/-- `f₀'` at a point set `X`, in the pair `i` (checked). -/
def f1PtAt (F : FTable) (rad : Nat) (X : IV 128) (i : Nat) : Option (IV 128) :=
  cond (pairOK F i X) (some (f1At F rad i X)) none

/-- `f₀` at `X` (pair found by the walk from `0`). -/
def fPt (F : FTable) (rad : Nat) (X : IV 128) : Option (IV 128) := fPtAt F rad X (locate F X 0)

/-- `e` at `X`. -/
def ePt (F : FTable) (rad : Nat) (X : IV 128) : Option (IV 128) := ePtAt F rad X (locate F X 0)

/-- `f₀'` at `X`. -/
def f1Pt (F : FTable) (rad : Nat) (X : IV 128) : Option (IV 128) := f1PtAt F rad X (locate F X 0)

/-! ### Interval helpers -/

/-- `[-E.hi, E.hi]`: contains every `δ` with `|δ| ≤ ε` for some `ε ∈ E`. -/
def symHi (E : IV 128) : IV 128 := ⟨SInt.neg E.hi, E.hi⟩

/-- The point `max(|lo|, |hi|)`, a bound of `|x|` for `x ∈ a`. -/
def magIV (a : IV 128) : IV 128 := IV.point ⟨false, Nat.max a.lo.mag a.hi.mag⟩

/-- `x³`. -/
def cube (a : IV 128) : IV 128 := IV.mul (IV.sq a) a

/-- `h³/24`. -/
def cube24 (H : IV 128) : IV 128 := IV.divNat (cube H) 24

/-! ### The midpoint grids -/

/-- The grid node `A + W k/N`. -/
def gNode (A W : IV 128) (N k : Nat) : IV 128 := IV.add A (IV.divNat (IV.mulNat W k) N)

/-- The midpoint `A + W (2k + 1)/(2N)` of the step `k`. -/
def gMid (A W : IV 128) (N k : Nat) : IV 128 :=
  IV.add A (IV.divNat (IV.mulNat W (Nat.add (Nat.mul 2 k) 1)) (Nat.mul 2 N))

/-- The data of one midpoint sum. -/
structure QCtx where
  /-- `p`. -/
  p : IV 128
  /-- `p²`. -/
  p2 : IV 128
  /-- The left end of the grid. -/
  A : IV 128
  /-- The length of the grid. -/
  W : IV 128
  /-- The number of steps. -/
  N : Nat
  /-- The widening of the table data. -/
  rad : Nat
  /-- `f₀(p)` (read by the first integrand only). -/
  F0 : IV 128
  /-- A point bound of the first derivative (`C` or `E`). -/
  B1 : IV 128
  /-- A point bound of the second derivative (`C'` or `E'`). -/
  B2 : IV 128

/-- The step `h = W/N`. -/
def QCtx.h (c : QCtx) : IV 128 := IV.divNat c.W c.N

/-- `C'/p² + 8 C/(p σ²)`, the bound of `q''` on a step starting at `σ ∈ S`. -/
def qBound (c : QCtx) (S : IV 128) : IV 128 :=
  IV.add (IV.divPos c.B2 c.p2) (IV.divPos (IV.mulNat c.B1 8) (IV.mul c.p (IV.sq S)))

/-- `E' + E/p`, the bound of `(e ∘ t)''`. -/
def eBound (c : QCtx) : IV 128 := IV.add c.B2 (IV.divPos c.B1 c.p)

/-- The term `h q(m) ± h³ M_k/24` of the first integrand (value at `X ∋ t(m)`, pair `j`). -/
def qVal (F : FTable) (c : QCtx) (k j : Nat) (M X : IV 128) : IV 128 :=
  IV.add (IV.mul c.h (IV.divPos (IV.sub (fAt F c.rad j X) c.F0) (IV.sq M)))
    (symHi (IV.mul (cube24 c.h) (qBound c (gNode c.A c.W c.N k))))

/-- The term `h e(t(m)) ± h³ (E' + E/p)/24` of the second integrand. -/
def eVal (F : FTable) (c : QCtx) (j : Nat) (X : IV 128) : IV 128 :=
  IV.add (IV.mul c.h (eAt F c.rad j X)) (symHi (IV.mul (cube24 c.h) (eBound c)))

/-- The first-integrand term at the checked root `X` and pair `j`. -/
def qTermX (F : FTable) (c : QCtx) (k : Nat) (M X : IV 128) (j : Nat) : Option (Nat × IV 128) :=
  cond (and (pairOK F j X) (and (IV.posB (IV.sq M))
      (and (IV.posB (IV.mul c.p (IV.sq (gNode c.A c.W c.N k)))) (IV.posB c.p2))))
    (some (j, qVal F c k j M X)) none

/-- The first-integrand term at the proposed root `lh` of `T2 = p² + m²`. -/
def qTermL (F : FTable) (c : QCtx) (k i : Nat) (M T2 : IV 128) (lh : Nat × Nat) : Option (Nat × IV 128) :=
  cond (IV.sqrtCheck T2 lh.1 lh.2)
    (qTermX F c k M (IV.ofNatPair lh.1 lh.2) (locate F (IV.ofNatPair lh.1 lh.2) i)) none

/-- The first-integrand term `k`, walking from the pair `i`; returns the pair used and the term. -/
def qTerm (F : FTable) (c : QCtx) (k i : Nat) : Option (Nat × IV 128) :=
  qTermL F c k i (gMid c.A c.W c.N k) (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))
    (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k))))

/-- The second-integrand term at the checked root `X` and pair `j`. -/
def eTermX (F : FTable) (c : QCtx) (X : IV 128) (j : Nat) : Option (Nat × IV 128) :=
  cond (and (pairOK F j X) (IV.posB c.p)) (some (j, eVal F c j X)) none

/-- The second-integrand term at the proposed root `lh` of `T2`. -/
def eTermL (F : FTable) (c : QCtx) (i : Nat) (T2 : IV 128) (lh : Nat × Nat) : Option (Nat × IV 128) :=
  cond (IV.sqrtCheck T2 lh.1 lh.2)
    (eTermX F c (IV.ofNatPair lh.1 lh.2) (locate F (IV.ofNatPair lh.1 lh.2) i)) none

/-- The second-integrand term `k`, walking from the pair `i`. -/
def eTerm (F : FTable) (c : QCtx) (k i : Nat) : Option (Nat × IV 128) :=
  eTermL F c i (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k)))
    (IV.sqrtProposal (IV.add c.p2 (IV.sq (gMid c.A c.W c.N k))))

/-- The sum of `n` terms `k, k + 1, …` of `step` added to `acc`, threading the pair index. -/
def runLoop (step : Nat → Nat → Option (Nat × IV 128)) : Nat → Nat → Nat → IV 128 → Option (IV 128)
  | 0, _, _, acc => some acc
  | Nat.succ n, k, i, acc =>
    match step k i with
    | none => none
    | some r => runLoop step n (Nat.succ k) r.1 (IV.add acc r.2)

/-- The midpoint sum of the first integrand on `[s₀, x₀]`. -/
def qSum (F : FTable) (c : QCtx) : Option (IV 128) := runLoop (qTerm F c) c.N 0 0 (IV.ofNat 0)

/-- The midpoint sum of the second integrand on `[0, x₀]`. -/
def eSum (F : FTable) (c : QCtx) : Option (IV 128) := runLoop (eTerm F c) c.N 0 0 (IV.ofNat 0)

/-! ### The origin, the assembly -/

/-- The parameters of the fine quadrature: the step counts `Nq`, `Ne`, the widening `rad` (`≥ 10⁻¹¹·2^128`) and
`s₀ = s0n/s0d` (the paper: `Nq = Ne = 45000`, `s₀ = 1/100`). -/
structure LamPar where
  /-- The steps of the first integrand on `[s₀, x₀]`. -/
  Nq : Nat
  /-- The steps of the second integrand on `[0, x₀]`. -/
  Ne : Nat
  /-- The widening of every table enclosure. -/
  rad : Nat
  /-- The numerator of `s₀`. -/
  s0n : Nat
  /-- The denominator of `s₀`. -/
  s0d : Nat

/-- `s₀ = s0n/s0d`. -/
def s0Of (P : LamPar) : IV 128 := IV.ofFrac ⟨false, P.s0n⟩ P.s0d

/-- `comp:lambda-origin` divided by `p`: `(f₀'(p)(s₀/2 - s₀³/(24p²) + [0, s₀⁵/(80p⁴)])
+ (s₀³/6) [p/(t₀ + p)², 1/(4p)] Y)/p`, with `S0 ∋ s₀`, `F1 ∋ f₀'(p)`, `Y ⊇ f₀''([p, t₀])`, `T0 ∋ t₀ = t(s₀)`. -/
def originEnc (p p2 S0 F1 Y T0 : IV 128) : IV 128 :=
  IV.divPos
    (IV.add
      (IV.mul F1 (IV.add (IV.sub (IV.divPow2 S0 1) (IV.divPos (IV.divNat (cube S0) 24) p2))
        (IV.hull (IV.ofNat 0) (IV.divPos (IV.divNat (IV.mul (IV.sq (IV.sq S0)) S0) 80) (IV.sq p2)))))
      (IV.mul (IV.mul (IV.divNat (cube S0) 6) (IV.hull (IV.divPos p (IV.sq (IV.add T0 p))) (IV.invPos (IV.mulNat p 4))))
        Y))
    p

/-- `((FR - FP)/x₀ - x₀ ER/p² + I₀ + IQ + IE/p²)/x₀`. -/
def lamAssemble (x0 p2 FR FP ER I0 IQ IE : IV 128) : IV 128 :=
  IV.divPos (IV.add (IV.add (IV.add (IV.sub (IV.divPos (IV.sub FR FP) x0) (IV.divPos (IV.mul x0 ER) p2)) I0) IQ)
    (IV.divPos IE p2)) x0

/-- The checks of the divisors and of `0 < s₀ < x₀`. -/
def posChecks (p p2 x0 S0 T0 : IV 128) : Bool :=
  and (and (IV.posB p) (IV.posB p2)) (and (and (IV.posB x0) (and (IV.posB S0) (IV.ltB S0 x0)))
    (and (IV.posB (IV.sq p2)) (and (IV.posB (IV.sq (IV.add T0 p))) (IV.posB (IV.mulNat p 4)))))

/-- `x₀ = R₀/2`. -/
def x0Of (d : BasisData) : IV 128 := IV.divPow2 d.r0 1

/-- The context of the first integrand on `[s₀, x₀]`. -/
def qCtxOf (d : BasisData) (N rad : Nat) (S0 : IV 128) (cB : Tup) (FP : IV 128) : QCtx :=
  ⟨d.p, d.p2, S0, IV.sub (x0Of d) S0, N, rad, FP, magIV (IV.addRad cB.f1 rad), magIV (IV.addRad cB.f2 rad)⟩

/-- The context of the second integrand on `[0, x₀]`. -/
def eCtxOf (d : BasisData) (N rad : Nat) (cB : Tup) : QCtx :=
  ⟨d.p, d.p2, IV.ofNat 0, x0Of d, N, rad, IV.ofNat 0, magIV (IV.addRad cB.e1 rad), magIV (IV.addRad cB.e2 rad)⟩

/-- The last stage: the two sums. -/
def lamFineS (d : BasisData) (P : LamPar) (S0 T0 : IV 128) (cY : Tup) (FP FP1 FR ER : IV 128) :
    Option (IV 128) → Option (IV 128) → Option (IV 128)
  | some IQ, some IE =>
    cond (and (and (Nat.blt 0 P.s0d) (and (Nat.blt 0 P.Nq) (Nat.blt 0 P.Ne))) (posChecks d.p d.p2 (x0Of d) S0 T0))
      (some (lamAssemble (x0Of d) d.p2 FR FP ER (originEnc d.p d.p2 S0 FP1 (IV.addRad cY.f2 P.rad) T0) IQ IE))
      none
  | _, _ => none

/-- The stage after the point values. -/
def lamFineP (F : FTable) (d : BasisData) (P : LamPar) (S0 T0 : IV 128) (cB cY : Tup) :
    Option (IV 128) → Option (IV 128) → Option (IV 128) → Option (IV 128) → Option (IV 128)
  | some FP, some FP1, some FR, some ER =>
    lamFineS d P S0 T0 cY FP FP1 FR ER (qSum F (qCtxOf d P.Nq P.rad S0 cB FP)) (eSum F (eCtxOf d P.Ne P.rad cB))
  | _, _, _, _ => none

/-- The stage after the two lookups. -/
def lamFineL (F : FTable) (d : BasisData) (P : LamPar) (S0 T0 : IV 128) :
    Option Tup → Option Tup → Option (IV 128)
  | some cB, some cY =>
    lamFineP F d P S0 T0 cB cY (fPt F P.rad d.p) (f1Pt F P.rad d.p) (fPt F P.rad d.r0) (ePt F P.rad d.r0)
  | _, _ => none

/-- The stage after the root `t₀ = √(p² + s₀²)` (proposed `lh`, checked). -/
def lamFineT (F : FTable) (d : BasisData) (P : LamPar) (S0 : IV 128) (lh : Nat × Nat) : Option (IV 128) :=
  cond (IV.sqrtCheck (IV.add d.p2 (IV.sq S0)) lh.1 lh.2)
    (lamFineL F d P S0 (IV.ofNatPair lh.1 lh.2) (lookup F.T (IV.hull d.p d.r0))
      (lookup F.T (IV.hull d.p (IV.ofNatPair lh.1 lh.2))))
    none

/-- **The fine enclosure of `λ`** with the parameters `P`. -/
def lamFine (F : FTable) (d : BasisData) (P : LamPar) : Option (IV 128) :=
  lamFineT F d P (s0Of P) (IV.sqrtProposal (IV.add d.p2 (IV.sq (s0Of P))))

end SandierSerfaty.Certificate.Lambda
