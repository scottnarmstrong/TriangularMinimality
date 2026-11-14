/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Jet.IJet

/-!
# The radial basis on a cell: jets of the pieces `u_i`, `D_i` and of `B̃ = ∑ u_i`

The evaluator side of the piece functions `Cal.Piece.u i j`, `Cal.Piece.D i j` (the C++
`basis(t, seg)` of the paper's verification code, `verification/core.hpp`). On a cell
`T` of segment `j` (the closed segments `Cal.seg j` between the knots
`b, p - c, p, R₀, R₀ + .001, R₀ + h_s, l`), `basis d j X` returns interval jets of

* `B̃ = ∑_{i=0}^{38} Piece.u i j` (field `bsum`), and
* the list `[Piece.D 0 j, …, Piece.D 38 j]` (field `ds`), with the exponents `k_i` alongside (`ks`).

The pieces, mode `i ≥ 1` with exponent `k = 6i` (the running power `t^{6i}` is carried along the modes):

| `j` | `w_i` | `b_i` | `u_i` | `D_i` |
|-----|-------|-------|-------|-------|
| 0 | `s_i t^k` | `0` | `w` | `b - w` |
| 1 | `s_i t^k` | `S((t-p+c)/c)(T₀ + T₁ h + T₂ h²)`, `h = t - p` | `w` | `b - w` |
| 2 | `s_i t^k` | `∑_j e_j z^j`, `z = t² - p²` (`V_i`) | `w` | `b - w` |
| 3 | `s_i t^k (1 - S(10(t - R₀)))` | `V_i(R₀) + P V_i'(R₀) + Q V_i''(R₀)` | `w` | `b - w` |
| 4, 5 | as 3 | as 3 (4), `V_i(R₀)` (5) | `w + τ (b - w)` | `(1 - τ)(b - w)` |
| 6 | as 3 | `V_i(R₀)` | `b` | `0` |

with `s_i = (-1)^i c_i`, `S` the quintic `10y³ - 15y⁴ + 6y⁵` (`Squintic`), `τ = S((t - R₀ - .001)/h_s)`,
`P = P(t - R₀)`, `Q = Q(t - R₀)` the continuation polynomials. Mode `0` is `w₀ = γ = -log t + π t²/2` and
`b₀ = γ` (`j ≤ 2`), `γ(R₀) + P γ'(R₀) + Q γ''(R₀)` (`j = 3, 4`), `γ(R₀)` (`j ≥ 5`); `D₀ = 0` for `j ≤ 2`.
Every polynomial is evaluated by `IJet.cpol` (re-expanded about the cell midpoint), as the C++ `cpol`,
except the edge polynomial `V_i` (Horner in `z = t² - p²`, as the C++ `hor`).

The interval constants (π, `p`, `p - c`, `p²`, `R₀`, `R₀ + .001`, the 2-jet of `γ` at `R₀`, and per mode
`k_i, s_i, T₀, T₁, T₂`, the edge coefficients and the 2-jet of `V_i` at `R₀`) are a `BasisData`; their
soundness predicate `BasisData.Valid` is in `SandierSerfaty.Certificate.Basis.Sound`.

Kernel rules: `-- kernel-rules: strict` (no Mathlib, `Nat` primitives, `cond`, no `let`).
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet

/-- The interval constants of one mode `i ≥ 1`. -/
structure ModeData where
  /-- The exponent `k_i = 6 i`. -/
  k : Nat
  /-- `s_i = (-1)^i c_i`. -/
  sc : IV 128
  /-- `T_{0i} = c_i p^k`. -/
  t0 : IV 128
  /-- `T_{1i}`. -/
  t1 : IV 128
  /-- `T_{2i}`. -/
  t2 : IV 128
  /-- The edge coefficients `c_i (-1)^j C(k, 2j) p^{k-2j}`, `j = 0, …, k/2` (lowest degree first). -/
  edge : List (IV 128)
  /-- `V_i(R₀)`. -/
  vr : IV 128
  /-- `V_i'(R₀)`. -/
  va : IV 128
  /-- `V_i''(R₀)`. -/
  vb : IV 128
deriving Inhabited, Repr

/-- The interval constants of the basis. -/
structure BasisData where
  /-- `π`. -/
  pi : IV 128
  /-- `p`. -/
  p : IV 128
  /-- `p - c` (`c = 3/50`). -/
  pc : IV 128
  /-- `p²`. -/
  p2 : IV 128
  /-- `R₀`. -/
  r0 : IV 128
  /-- `R₀ + 1/1000`. -/
  r1 : IV 128
  /-- `γ(R₀)`. -/
  g0 : IV 128
  /-- `γ'(R₀)`. -/
  g1 : IV 128
  /-- `γ''(R₀)`. -/
  g2 : IV 128
  /-- The modes `1, …, 38`. -/
  modes : List ModeData
deriving Inhabited, Repr

/-! ### Literal polynomials -/

/-- The rational `num/den` as an interval (rounded outward). -/
def frac (neg : Bool) (num den : Nat) : IV 128 := IV.ofFrac ⟨neg, num⟩ den

/-- The quintic `S(y) = 10y³ - 15y⁴ + 6y⁵` (lowest degree first). -/
def sqCoeffs : List (IV 128) :=
  [ivZero, ivZero, ivZero, IV.ofNat 10, IV.neg (IV.ofNat 15), IV.ofNat 6]

/-- `P(z) = z - 6z³/h_s² + 8z⁴/h_s³ - 3z⁵/h_s⁴` with `h_s = 3/40`. -/
def pCoeffs : List (IV 128) :=
  [ivZero, ivOne, ivZero, frac true 3200 3, frac false 512000 27, frac true 2560000 27]

/-- `Q(z) = z²/2 - 3z³/(2h_s) + 3z⁴/(2h_s²) - z⁵/(2h_s³)` with `h_s = 3/40`. -/
def qCoeffs : List (IV 128) :=
  [ivZero, ivZero, frac false 1 2, IV.neg (IV.ofNat 20), frac false 800 3, frac true 32000 27]

/-! ### Shared jets of a cell -/

/-- `γ(t) = -log t + π t²/2`, with an enclosure `pi` of `π`. -/
def gammaPi (pi : IV 128) (T : IJet 128) : IJet 128 :=
  IJet.add (IJet.neg (IJet.log T)) (IJet.scale (IV.divPow2 pi 1) (IJet.sq T))

/-- `γ(t) = -log t + π t²/2`. -/
def gammaJ (d : BasisData) (T : IJet 128) : IJet 128 := gammaPi d.pi T

/-- The quintic of a jet. -/
def quinticJ (y : IJet 128) : IJet 128 := IJet.cpol sqCoeffs y

/-- `τ = S((t - R₀ - .001)/h_s)` (the active ramp of segments 4, 5). -/
def tauJ (d : BasisData) (T : IJet 128) : IJet 128 :=
  quinticJ (IJet.scale (frac false 40 3) (IJet.subIV T d.r1))

/-- `S(10 (t - R₀))` (the cutoff of `U_m`, active from `R₀`). -/
def gcJ (d : BasisData) (T : IJet 128) : IJet 128 :=
  quinticJ (IJet.scale (IV.ofNat 10) (IJet.subIV T d.r0))

/-- `S((t - p + c)/c)` (the inner continuation, segment 1). -/
def cuJ (d : BasisData) (T : IJet 128) : IJet 128 :=
  quinticJ (IJet.scale (frac false 50 3) (IJet.subIV T d.pc))

/-- `P(t - R₀)`. -/
def pJ (d : BasisData) (T : IJet 128) : IJet 128 := IJet.cpol pCoeffs (IJet.subIV T d.r0)

/-- `Q(t - R₀)`. -/
def qJ (d : BasisData) (T : IJet 128) : IJet 128 := IJet.cpol qCoeffs (IJet.subIV T d.r0)

/-- The continuation `v₀ + P v₁ + Q v₂`. -/
def contJ (Pj Qj : IJet 128) (v0 v1 v2 : IV 128) : IJet 128 :=
  IJet.addIV (IJet.add (IJet.scale v1 Pj) (IJet.scale v2 Qj)) v0

/-- The jets shared by the modes of a cell. -/
structure Ctx where
  /-- The variable. -/
  t : IJet 128
  /-- `t^6`. -/
  t6 : IJet 128
  /-- `t - p`. -/
  h : IJet 128
  /-- `t² - p²`. -/
  z : IJet 128
  /-- `S(10 (t - R₀))`. -/
  gc : IJet 128
  /-- `S((t - p + c)/c)`. -/
  cu : IJet 128
  /-- `τ`. -/
  tau : IJet 128
  /-- `P(t - R₀)`. -/
  pr : IJet 128
  /-- `Q(t - R₀)`. -/
  qr : IJet 128

/-- The shared jets of the cell `X`. -/
def mkCtx (d : BasisData) (X : IV 128) : Ctx :=
  ⟨IJet.var X, IJet.pow (IJet.var X) 6, IJet.subIV (IJet.var X) d.p,
    IJet.subIV (IJet.sq (IJet.var X)) d.p2, gcJ d (IJet.var X), cuJ d (IJet.var X), tauJ d (IJet.var X),
    pJ d (IJet.var X), qJ d (IJet.var X)⟩

/-! ### One mode -/

/-- `w_i` from the running power `tk = t^{k_i}`. -/
def modeW (c : Ctx) (j : Nat) (md : ModeData) (tk : IJet 128) : IJet 128 :=
  cond (Nat.ble j 2) (IJet.scale md.sc tk)
    (IJet.scale md.sc (IJet.mul tk (IJet.sub (IJet.const ivOne) c.gc)))

/-- `b_i`. -/
def modeB (c : Ctx) (j : Nat) (md : ModeData) : IJet 128 :=
  cond (Nat.beq j 0) (IJet.const ivZero)
    (cond (Nat.beq j 1) (IJet.mul c.cu (IJet.horner c.h [md.t0, md.t1, md.t2]))
      (cond (Nat.beq j 2) (IJet.horner c.z md.edge)
        (cond (Nat.ble j 4) (contJ c.pr c.qr md.vr md.va md.vb) (IJet.const md.vr))))

/-- `u_i` from `w_i`, `b_i`. -/
def mixU (c : Ctx) (j : Nat) (w b : IJet 128) : IJet 128 :=
  cond (Nat.ble j 3) w
    (cond (Nat.ble j 5) (IJet.add w (IJet.mul c.tau (IJet.sub b w))) b)

/-- `D_i` from `w_i`, `b_i`. -/
def mixD (c : Ctx) (j : Nat) (w b : IJet 128) : IJet 128 :=
  cond (Nat.ble j 3) (IJet.sub b w)
    (cond (Nat.ble j 5) (IJet.mul (IJet.sub (IJet.const ivOne) c.tau) (IJet.sub b w)) (IJet.const ivZero))

/-! ### Mode 0 -/

/-- `b₀`. -/
def modeB0 (d : BasisData) (c : Ctx) (j : Nat) (g : IJet 128) : IJet 128 :=
  cond (Nat.ble j 2) g (cond (Nat.ble j 4) (contJ c.pr c.qr d.g0 d.g1 d.g2) (IJet.const d.g0))

/-- `D₀` (zero for `j ≤ 2`, where `b₀ = w₀ = γ`). -/
def modeD0 (d : BasisData) (c : Ctx) (j : Nat) (g : IJet 128) : IJet 128 :=
  cond (Nat.ble j 2) (IJet.const ivZero) (mixD c j g (modeB0 d c j g))

/-- `u₀`. -/
def modeU0 (d : BasisData) (c : Ctx) (j : Nat) (g : IJet 128) : IJet 128 :=
  cond (Nat.ble j 2) g (mixU c j g (modeB0 d c j g))

/-! ### All modes -/

/-- The output of the basis on a cell. -/
structure BasisOut where
  /-- The jet of `B̃ = ∑_{i ≤ 38} u_i`. -/
  bsum : IJet 128
  /-- The jets of `D_0, …, D_38`. -/
  ds : List (IJet 128)
  /-- The exponents `k_0, …, k_38`. -/
  ks : List Nat

/-- The jets of `D_i` for the modes of the list, from the running power `tk = t^{k_i}`. -/
def dsLoop (c : Ctx) (j : Nat) : List ModeData → IJet 128 → List (IJet 128)
  | [], _ => []
  | md :: mds, tk =>
    mixD c j (modeW c j md tk) (modeB c j md) :: dsLoop c j mds (IJet.mul tk c.t6)

/-- The sum of `u_i` for the modes of the list, added to `acc`. -/
def uLoop (c : Ctx) (j : Nat) : List ModeData → IJet 128 → IJet 128 → IJet 128
  | [], _, acc => acc
  | md :: mds, tk, acc =>
    uLoop c j mds (IJet.mul tk c.t6) (IJet.add acc (mixU c j (modeW c j md tk) (modeB c j md)))

/-- The exponents of the modes. -/
def ksOf : List ModeData → List Nat
  | [] => []
  | md :: mds => md.k :: ksOf mds

/-- The basis with the shared jets and `γ` given. -/
def basisWith (d : BasisData) (c : Ctx) (j : Nat) (g : IJet 128) : BasisOut :=
  ⟨uLoop c j d.modes c.t6 (modeU0 d c j g), modeD0 d c j g :: dsLoop c j d.modes c.t6, 6 :: ksOf d.modes⟩

/-- **The basis** on the cell `X` of segment `j`. Sound when `IV.posB X` (`basis_sound`). -/
def basis (d : BasisData) (j : Nat) (X : IV 128) : BasisOut :=
  basisWith d (mkCtx d X) j (gammaJ d (IJet.var X))

end SandierSerfaty.Certificate.Basis
