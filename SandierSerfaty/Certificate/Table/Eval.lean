/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Core
public import SandierSerfaty.Certificate.Basis.Data

/-!
# The radial table: propagation of `S̃₁, S̃₂, H̃_k` and the tuple `(f̃₀, f̃₀', f̃₀'', ẽ, ẽ', ẽ'')`

The evaluator side of the table of paper `comp:breakpoints`, `comp:node-separation`, `comp:initial-integrals` (`comp:propagation`, `comp:midpoint`,
`comp:cell-integrals`, `comp:radial-odes`, `comp:table-tuple`) and of the C++ `table()` and `fh` of
`verification/core.hpp`. All jets here are order-two
interval jets (`IJet2`): the tuple needs `f̃₀, ẽ` to order two only, and the sector functions are recovered to
order two from their differential equations

  `S̃₁' = t B̃`,  `S̃₂' = -2 B̃₁ + t B̃₁²`,  `H̃_k' = B̃₁ - k H̃_k / t`.

* `Pt`: the jets at an evaluation set (a cell or a node) of one segment `j`: `t`, `1/t`, `log t`, `B̃₁`,
  `Y₁ = t B̃`, `Y₂ = -2B̃₁ + t B̃₁²`, and the basis jets `D_i` with their exponents;
* `s1J`, `s2J`, `hJ`: the order-two jets of `S̃₁, S̃₂, H̃_k` from an enclosure of their value
  (`comp:jet-ode`, `Y_{j+1} = [F]_j/(j+1)`; for `H̃_k` the coefficients are solved in increasing order);
* `fh pt S`: the six-tuple from the jets and a sector state `S` (values of `S̃₁, S̃₂` and of `H̃_{k_i}` for the
  modes `i = 0, …, 38`), with the bilinear sums written as `∑_i X_i ∑_j c_{ij} X_j`;
* `stepState`: the midpoint propagation `[v, u]` (`comp:midpoint`, error `(u - v)³/24 · sup|Y''|`);
  `cellState`: the values on the cell `[v, u]` (`comp:cell-integrals`);
* `chunkCheck d j S nodes cellTups nodeTups S'`: from a checkpoint state `S` at the first node, propagate along
  the nodes of segment `j`, check node separation and nondegeneracy, check that the computed tuples lie in the
  stored ones, and that the final state lies in the checkpoint `S'` (each chunk is recomputed from a literal
  checkpoint, so the chunks are checked independently).

Soundness: `SandierSerfaty.Certificate.Table.Model` (`fh_sound`), `SandierSerfaty.Certificate.Table.StepSound`
(`chunkCheck_sound`), `Inner`, `Init`; the bridge to `Cal.Trunc`: `Bridge`, `InnerBridge`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Table

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis

/-- A sector state: enclosures of `S̃₁, S̃₂` and of `H̃_{k_i}` for the modes `i = 0, …, 38`. -/
structure SState where
  /-- `S̃₁`. -/
  s1 : IV 128
  /-- `S̃₂`. -/
  s2 : IV 128
  /-- `H̃_{k_i}`, `i = 0, …, 38`. -/
  hs : List (IV 128)
deriving Inhabited, Repr

/-- A table tuple: enclosures of `f̃₀, f̃₀', f̃₀'', ẽ, ẽ', ẽ''`. -/
structure Tup where
  /-- `f̃₀`. -/
  f0 : IV 128
  /-- `f̃₀'`. -/
  f1 : IV 128
  /-- `f̃₀''`. -/
  f2 : IV 128
  /-- `ẽ`. -/
  e0 : IV 128
  /-- `ẽ'`. -/
  e1 : IV 128
  /-- `ẽ''`. -/
  e2 : IV 128
deriving Inhabited, Repr

/-- The jets at an evaluation set of one segment. -/
structure Pt where
  /-- `t`. -/
  t : IJet2 128
  /-- `1/t`. -/
  w : IJet2 128
  /-- `log t`. -/
  lg : IJet2 128
  /-- `B̃₁ = B̃' + 1/t`. -/
  b1 : IJet2 128
  /-- `Y₁ = t B̃`. -/
  y1 : IJet2 128
  /-- `Y₂ = -2 B̃₁ + t B̃₁²`. -/
  y2 : IJet2 128
  /-- The jets of `D_0, …, D_38`. -/
  ds : List (IJet 128)
  /-- The exponents `k_0, …, k_38`. -/
  ks : List Nat

/-- `Y₂ = -2 B̃₁ + t B̃₁²` from the jets of `t` and `B̃₁`. -/
def y2Of (t b1 : IJet2 128) : IJet2 128 :=
  IJet2.add (IJet2.scale (IV.neg (IV.ofNat 2)) b1) (IJet2.mul t (IJet2.mul b1 b1))

/-- The jets at `X` from the basis output and the jet `L` of `log`. -/
def mkPtOf (X : IV 128) (out : BasisOut) (L : IJet 128) : Pt :=
  ⟨IJet.trunc (IJet.var X), IJet.trunc (IJet.invPos (IJet.var X)), IJet.trunc L,
    IJet.der (IJet.add out.bsum L), IJet.trunc (IJet.mul (IJet.var X) out.bsum),
    y2Of (IJet.trunc (IJet.var X)) (IJet.der (IJet.add out.bsum L)), out.ds, out.ks⟩

/-- The jets at the evaluation set `X` of segment `j`. -/
def mkPt (d : BasisData) (j : Nat) (X : IV 128) : Pt := mkPtOf X (basis d j X) (IJet.log (IJet.var X))

/-! ### The sector functions to order two -/

/-- `S̃₁` from its value `V`: `(V, Y₁, Y₁'/2)`. -/
def s1J (pt : Pt) (V : IV 128) : IJet2 128 := ⟨V, pt.y1.c0, IV.divPow2 pt.y1.c1 1⟩

/-- `S̃₂` from its value `V`: `(V, Y₂, Y₂'/2)`. -/
def s2J (pt : Pt) (V : IV 128) : IJet2 128 := ⟨V, pt.y2.c0, IV.divPow2 pt.y2.c1 1⟩

/-- The first coefficient of `H̃_k`: `B̃₁ - k H/t`. -/
def hX1 (pt : Pt) (k : Nat) (V : IV 128) : IV 128 := IV.sub pt.b1.c0 (IV.mulNat (IV.mul V pt.w.c0) k)

/-- `H̃_k` from its value `V`: `(V, X₁, X₂)` with `X₁ = B̃₁ - k V/t`, `X₂ = (B̃₁' - k (X₁/t - V/t²))/2`. -/
def hJWith (pt : Pt) (k : Nat) (V X1 : IV 128) : IJet2 128 :=
  ⟨V, X1, IV.divPow2 (IV.sub pt.b1.c1 (IV.mulNat (IV.add (IV.mul X1 pt.w.c0) (IV.mul V pt.w.c1)) k)) 1⟩

/-- `H̃_k` from its value `V`. -/
def hJ (pt : Pt) (k : Nat) (V : IV 128) : IJet2 128 := hJWith pt k V (hX1 pt k V)

/-! ### The tuple -/

/-- `∑_i D_i/(k_i + 2)`. -/
def dsumL : List Nat → List (IJet 128) → IJet2 128
  | k :: ks, D :: ds => IJet2.add (IJet2.scale (frac false 1 (Nat.add k 2)) (IJet.trunc D)) (dsumL ks ds)
  | _, _ => IJet2.const ivZero

/-- `∑_i (-2 D_i + 2 k_i D_i H_{k_i})`. -/
def linL (pt : Pt) : List Nat → List (IJet 128) → List (IV 128) → IJet2 128
  | k :: ks, D :: ds, V :: vs =>
    IJet2.add
      (IJet2.add (IJet2.scale (IV.neg (IV.ofNat 2)) (IJet.trunc D))
        (IJet2.scale (IV.ofNat (Nat.mul 2 k)) (IJet2.mul (IJet.trunc D) (hJ pt k V))))
      (linL pt ks ds vs)
  | _, _, _ => IJet2.const ivZero

/-- `∑_j (k_i k_j/(k_i + k_j)) D_j` for a fixed `k_i`. -/
def quadIn (ki : Nat) : List Nat → List (IJet 128) → IJet2 128
  | k :: ks, D :: ds =>
    IJet2.add (IJet2.scale (frac false (Nat.mul ki k) (Nat.add ki k)) (IJet.trunc D)) (quadIn ki ks ds)
  | _, _ => IJet2.const ivZero

/-- `∑_i D_i ∑_j (k_i k_j/(k_i + k_j)) D_j`. -/
def quadL (aks : List Nat) (ads : List (IJet 128)) : List Nat → List (IJet 128) → IJet2 128
  | k :: ks, D :: ds => IJet2.add (IJet2.mul (IJet.trunc D) (quadIn k aks ads)) (quadL aks ads ks ds)
  | _, _ => IJet2.const ivZero

/-- `Q_i = t D_i' - k_i D_i`. -/
def qOf (pt : Pt) (k : Nat) (D : IJet 128) : IJet2 128 :=
  IJet2.sub (IJet2.mul pt.t (IJet.der D)) (IJet2.scale (IV.ofNat k) (IJet.trunc D))

/-- `∑_j Q_j/(k_i + k_j)` for a fixed `k_i`. -/
def eIn (pt : Pt) (ki : Nat) : List Nat → List (IJet 128) → IJet2 128
  | k :: ks, D :: ds => IJet2.add (IJet2.scale (frac false 1 (Nat.add ki k)) (qOf pt k D)) (eIn pt ki ks ds)
  | _, _ => IJet2.const ivZero

/-- `∑_i Q_i ∑_j Q_j/(k_i + k_j)`. -/
def eL (pt : Pt) (aks : List Nat) (ads : List (IJet 128)) : List Nat → List (IJet 128) → IJet2 128
  | k :: ks, D :: ds => IJet2.add (IJet2.mul (qOf pt k D) (eIn pt k aks ads)) (eL pt aks ads ks ds)
  | _, _ => IJet2.const ivZero

/-- `f̃₀ = -2π (S̃₁ + t² ∑ D_i/(k_i+2)) - ½ (log t + S̃₂ + ∑ (-2D_i + 2k_i D_i H̃_{k_i}) + ∑∑ …)`. -/
def fJ (pi : IV 128) (pt : Pt) (S : SState) : IJet2 128 :=
  IJet2.sub
    (IJet2.scale (IV.neg (IV.mulNat pi 2))
      (IJet2.add (s1J pt S.s1) (IJet2.mul (IJet2.mul pt.t pt.t) (dsumL pt.ks pt.ds))))
    (IJet2.scale (frac false 1 2)
      (IJet2.add (IJet2.add (IJet2.add pt.lg (s2J pt S.s2)) (linL pt pt.ks pt.ds S.hs))
        (quadL pt.ks pt.ds pt.ks pt.ds)))

/-- `ẽ = ½ ∑_i Q_i ∑_j Q_j/(k_i + k_j)`. -/
def eJ (pt : Pt) : IJet2 128 := IJet2.scale (frac false 1 2) (eL pt pt.ks pt.ds pt.ks pt.ds)

/-- The tuple `(f̃₀, f̃₀', f̃₀'', ẽ, ẽ', ẽ'')` from the order-two jets. -/
def tupOf (f e : IJet2 128) : Tup := ⟨f.c0, f.c1, IV.mulNat f.c2 2, e.c0, e.c1, IV.mulNat e.c2 2⟩

/-- **The tuple** at the evaluation set of `pt` with the sector state `S`. -/
def fh (pi : IV 128) (pt : Pt) (S : SState) : Tup := tupOf (fJ pi pt S) (eJ pt)

/-! ### Propagation -/

/-- An upper bound of `h³/24 · sup|Y''| · 2^128` from `h ≤ Hhi/2^128` and the coefficient `c₂ ∋ Y''/2`. -/
def errRad (Hhi : Nat) (c2 : IV 128) : Nat :=
  SInt.cdivNat (Nat.mul (Nat.pow Hhi 3) (magHi c2)) (Nat.mul 12 (Nat.shiftLeft 1 384))

/-- The midpoint step `S + H·Y(m) ± h³/24 sup|Y''|` from the midpoint value `ym` and the cell jet `yc`. -/
def midStep (S Hiv : IV 128) (ym : IV 128) (yc : IJet2 128) : IV 128 :=
  IV.addRad (IV.add S (IV.mul Hiv ym)) (errRad Hiv.hi.mag yc.c2)

/-- The jet of `r/u` on the evaluation set of `pt` (`ui` encloses `u`). -/
def ratioJ (pt : Pt) (ui : IV 128) : IJet2 128 := IJet2.scale (IV.invPos ui) pt.t

/-- Sixth power of an order-two jet. -/
def pow6J (a : IJet2 128) : IJet2 128 := IJet2.mul (IJet2.mul (IJet2.mul a a) a) (IJet2.mul (IJet2.mul a a) a)

/-- The propagated `H̃_k` (`comp:propagation`): `(v/u)^k H(v) + ∫_v^u (r/u)^k B̃₁(r) dr`, by the midpoint rule
with the current powers `sv ∋ (v/u)^k`, `pm`, `pc` (jets of `(r/u)^k` at the midpoint and on the cell). -/
def hNew (Hiv : IV 128) (ptm ptc : Pt) (sv : IV 128) (pm pc : IJet2 128) (h : IV 128) : IV 128 :=
  midStep (IV.mul sv h) Hiv (IJet2.mul pm ptm.b1).c0 (IJet2.mul pc ptc.b1)

/-- The propagated `H̃_{k_i}` for the modes `i ≥ 1` (`k_i = 6i`), the powers advanced by the sixth powers. -/
def hLoop (Hiv : IV 128) (ptm ptc : Pt) (sv6 : IV 128) (pm6 pc6 : IJet2 128) :
    IV 128 → IJet2 128 → IJet2 128 → List (IV 128) → List (IV 128)
  | _, _, _, [] => []
  | sv, pm, pc, h :: hs =>
    hNew Hiv ptm ptc sv pm pc h :: hLoop Hiv ptm ptc sv6 pm6 pc6 (IV.mul sv sv6) (IJet2.mul pm pm6)
      (IJet2.mul pc pc6) hs

/-- The propagated `H̃` list: mode `0` (`k = 6`) and the modes `1, 2, …` (`k = 6, 12, …`). -/
def hsStep (Hiv : IV 128) (ptm ptc : Pt) (sv6 : IV 128) (pm6 pc6 : IJet2 128) : List (IV 128) → List (IV 128)
  | [] => []
  | h :: hs => hNew Hiv ptm ptc sv6 pm6 pc6 h :: hLoop Hiv ptm ptc sv6 pm6 pc6 sv6 pm6 pc6 hs

/-- The state at the node `u` from the state `S` at the node `v` (`Hiv = u - v`, `ptm` the jets at the
midpoint, `ptc` on the cell `[v, u]`). -/
def stepWith (Hiv : IV 128) (ptm ptc : Pt) (sv6 : IV 128) (pm6 pc6 : IJet2 128) (S : SState) : SState :=
  ⟨midStep S.s1 Hiv ptm.y1.c0 ptc.y1, midStep S.s2 Hiv ptm.y2.c0 ptc.y2, hsStep Hiv ptm ptc sv6 pm6 pc6 S.hs⟩

/-- The interval `[lo, hi]` of two endpoints. -/
def mkIV (lo hi : SInt) : IV 128 := ⟨lo, hi⟩

/-- The interval `[0, Hhi]`. -/
def zeroTo (Hiv : IV 128) : IV 128 := ⟨SInt.zero, Hiv.hi⟩

/-- The cell values of `H̃_{k_i}`: `(v/T)^k H(v) ± h sup|B̃₁|`, for the modes `i ≥ 1`. -/
def hCellLoop (rad : Nat) (cv6 : IV 128) : IV 128 → List (IV 128) → List (IV 128)
  | _, [] => []
  | cv, h :: hs => IV.addRad (IV.mul cv h) rad :: hCellLoop rad cv6 (IV.mul cv cv6) hs

/-- The cell values of the `H̃` list (mode `0` and the modes `1, 2, …`). -/
def hsCell (rad : Nat) (cv6 : IV 128) : List (IV 128) → List (IV 128)
  | [] => []
  | h :: hs => IV.addRad (IV.mul cv6 h) rad :: hCellLoop rad cv6 cv6 hs

/-- The state on the cell `[v, u]` (`comp:cell-integrals`), with `cv6 ∋ (v/t)^6` on the cell. -/
def cellState (Hiv : IV 128) (ptc : Pt) (cv6 : IV 128) (S : SState) : SState :=
  ⟨IV.add S.s1 (IV.mul (zeroTo Hiv) ptc.y1.c0), IV.add S.s2 (IV.mul (zeroTo Hiv) ptc.y2.c0),
    hsCell (SInt.cdivNat (Nat.mul Hiv.hi.mag (magHi ptc.b1.c0)) (Nat.shiftLeft 1 128)) cv6 S.hs⟩

/-! ### Comparisons and the chunk check -/

/-- `a ⊆ b` for tuples. -/
def tupSub (a b : Tup) : Bool :=
  and (and (IV.subsetB a.f0 b.f0) (and (IV.subsetB a.f1 b.f1) (IV.subsetB a.f2 b.f2)))
    (and (IV.subsetB a.e0 b.e0) (and (IV.subsetB a.e1 b.e1) (IV.subsetB a.e2 b.e2)))

/-- `a ⊆ b` for states. -/
def stateSub (a b : SState) : Bool :=
  and (and (IV.subsetB a.s1 b.s1) (IV.subsetB a.s2 b.s2)) (subList a.hs b.hs)

/-- The evaluation set is positive and nondegenerate. -/
def okSet (X : IV 128) : Bool := and (IV.posB X) (SInt.blt X.lo X.hi)

/-- One step of the chunk, with the jets at the midpoint, on the cell and at the node `u` given. -/
def stepCheckWith (pi : IV 128) (v u : IV 128) (ptc ptu : Pt) (S S' : SState) (ct nt : Tup) : Bool :=
  and (and (SInt.blt v.hi u.lo) (and (okSet (IV.divPow2 (IV.add v u) 1)) (and (okSet (mkIV v.lo u.hi)) (okSet u))))
    (and (tupSub (fh pi ptc (cellState (IV.sub u v) ptc (ivPow (IV.divPos v (mkIV v.lo u.hi)) 6) S)) ct)
      (tupSub (fh pi ptu S') nt))

/-- The state at `u` from the state at `v` on segment `j`, with the jets given. -/
def stepState (v u : IV 128) (ptm ptc : Pt) (S : SState) : SState :=
  stepWith (IV.sub u v) ptm ptc (ivPow (IV.divPos v u) 6) (pow6J (ratioJ ptm u)) (pow6J (ratioJ ptc u)) S

/-- One step from the node `v` to the node `u` of segment `j`: the check and the new state. -/
def stepCheck (d : BasisData) (j : Nat) (v u : IV 128) (S : SState) (ct nt : Tup) : Bool :=
  stepCheckWith d.pi v u (mkPt d j (mkIV v.lo u.hi)) (mkPt d j u) S
    (stepState v u (mkPt d j (IV.divPow2 (IV.add v u) 1)) (mkPt d j (mkIV v.lo u.hi)) S) ct nt

/-- The state after one step. -/
def stepNext (d : BasisData) (j : Nat) (v u : IV 128) (S : SState) : SState :=
  stepState v u (mkPt d j (IV.divPow2 (IV.add v u) 1)) (mkPt d j (mkIV v.lo u.hi)) S

/-- **The chunk check** on segment `j`: from the state `S` at the first node, along the nodes, against the
stored cell tuples and node tuples (one per step), ending inside the checkpoint `S'`. -/
def chunkCheck (d : BasisData) (j : Nat) : SState → List (IV 128) → List Tup → List Tup → SState → Bool
  | S, [_], [], [], S' => stateSub S S'
  | S, v :: u :: rest, ct :: cts, nt :: nts, S' =>
    and (stepCheck d j v u S ct nt) (chunkCheck d j (stepNext d j v u S) (u :: rest) cts nts S')
  | _, _, _, _, _ => false

/-! ### The first segment: the exact inner form -/

/-- The jet of the inner closed form `f̃₀ = (πt² - ½) log t - (3/8) π² t⁴` (`comp:inner-exact`) on `X`. -/
def fInnerJ (pi X : IV 128) : IJet2 128 :=
  IJet2.sub
    (IJet2.mul (IJet2.sub (IJet2.scale pi (IJet.trunc (IJet.sq (IJet.var X)))) (IJet2.const (frac false 1 2)))
      (IJet.trunc (IJet.log (IJet.var X))))
    (IJet2.scale (IV.mul (frac false 3 8) (IV.sq pi)) (IJet.trunc (IJet.pow (IJet.var X) 4)))

/-- The tuple of the first segment on `X`: the inner closed form and `ẽ = 0`. -/
def fhInner (pi X : IV 128) : Tup := tupOf (fInnerJ pi X) (IJet2.const ivZero)

/-- **The check of the first segment** `[b, p - c]`: separated positive nodes, the cell tuples on
`[v.lo, u.hi]` and the node tuples at `u` inside the stored ones (no propagation: the closed form holds on the
whole segment). -/
def innerCheck (pi : IV 128) : List (IV 128) → List Tup → List Tup → Bool
  | [_], [], [] => true
  | v :: u :: rest, ct :: cts, nt :: nts =>
    and (and (SInt.blt v.hi u.lo) (and (IV.posB v) (IV.posB u)))
      (and (and (tupSub (fhInner pi (mkIV v.lo u.hi)) ct) (tupSub (fhInner pi u) nt)) (innerCheck pi (u :: rest) cts nts))
  | _, _, _ => false

/-! ### The initial state at `p - c` -/

/-- The monomials `(e_i, v_i t^{e_i})` of `B̃₁` for the modes of the list (`e = k`, `v = k s_i`), from the
running power `tk = t^k`. -/
def termsFrom (t6 : IV 128) : List ModeData → IV 128 → List (Nat × IV 128)
  | [], _ => []
  | md :: mds, tk => (md.k, IV.mul (IV.mulNat md.sc md.k) tk) :: termsFrom t6 mds (IV.mul tk t6)

/-- The monomials of `B̃₁ = π t + ∑ k_m a_m t^{k_m - 1}` multiplied by `t`: `(2, π t²)` and `(k_m, k_m a_m t^{k_m})`
(`comp:initial-integrals`). -/
def initTerms (d : BasisData) (X : IV 128) : List (Nat × IV 128) :=
  (2, IV.mul d.pi (IV.sq X)) :: termsFrom (ivPow X 6) d.modes (ivPow X 6)

/-- `∑_m s_m t^{k_m + 2}/(k_m + 2)`. -/
def s1Sum (t2 t6 : IV 128) : List ModeData → IV 128 → IV 128
  | [], _ => ⟨SInt.zero, SInt.zero⟩
  | md :: mds, tk => IV.add (IV.divNat (IV.mul (IV.mul md.sc tk) t2) (Nat.add md.k 2)) (s1Sum t2 t6 mds (IV.mul tk t6))

/-- `S̃₁(t) = t²/2 (1/2 - log t) + π t⁴/8 + ∑_m a_m t^{k_m + 2}/(k_m + 2)`. -/
def s1Init (d : BasisData) (X : IV 128) : IV 128 :=
  IV.add (IV.add (IV.mul (IV.divPow2 (IV.sq X) 1) (IV.sub (frac false 1 2) (IV.logPos X)))
      (IV.divNat (IV.mul d.pi (IV.sq (IV.sq X))) 8))
    (s1Sum (IV.sq X) (ivPow X 6) d.modes (ivPow X 6))

/-- `∑_j w_j/(e_j + c)`. -/
def termSum (c : Nat) : List (Nat × IV 128) → IV 128
  | [] => ⟨SInt.zero, SInt.zero⟩
  | (e, w) :: ts => IV.add (IV.divNat w (Nat.add e c)) (termSum c ts)

/-- `∑_i w_i ∑_j w_j/(e_i + e_j)`. -/
def termSum2 (all : List (Nat × IV 128)) : List (Nat × IV 128) → IV 128
  | [] => ⟨SInt.zero, SInt.zero⟩
  | (e, w) :: ts => IV.add (IV.mul w (termSum e all)) (termSum2 all ts)

/-- `S̃₂(t) = -2 ∑_i w_i/e_i + ∑_{i,j} w_i w_j/(e_i + e_j)`. -/
def s2Init (tms : List (Nat × IV 128)) : IV 128 :=
  IV.sub (termSum2 tms tms) (IV.mulNat (termSum 0 tms) 2)

/-- `H̃_{k_i}(t) = ∑_j w_j/(e_j + k_i)` for the exponents of the list. -/
def hInitL (tms : List (Nat × IV 128)) : List Nat → List (IV 128)
  | [] => []
  | k :: ks => termSum k tms :: hInitL tms ks

/-- The initial state at the node `X ∋ p - c` from the monomials. -/
def initStateOf (d : BasisData) (X : IV 128) (tms : List (Nat × IV 128)) : SState :=
  ⟨s1Init d X, s2Init tms, hInitL tms (6 :: ksOf d.modes)⟩

/-- **The initial checkpoint** at the node `X ∋ p - c`: the closed forms of `comp:initial-integrals` lie in
the literal state `S`. -/
def initCheck (d : BasisData) (X : IV 128) (S : SState) : Bool :=
  and (IV.posB X) (stateSub (initStateOf d X (initTerms d X)) S)

end SandierSerfaty.Certificate.Table
