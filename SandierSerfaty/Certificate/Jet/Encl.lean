/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Jet.IJet
public import SandierSerfaty.Certificate.Arith.IVLemmas
public import SandierSerfaty.Tails.JetCalc

/-!
# Jet enclosures and the laws of the linear and product operations

`JetEncl T F J` says that the interval jet `J` encloses the Taylor coefficients of the real function `F` at
every point of the set `T`: there are derivative witnesses
`F₁, F₂, F₃` with `F' = F₁`, `F₁' = F₂`, `F₂' = F₃` at every point of `T` (the jet calculus
`SandierSerfaty.Tails.Jet3` of §6, with `𝔸 = ℝ`), and for `t ∈ T`

  `F t ∈ J.c0`, `F₁ t ∈ J.c1`, `F₂ t / 2 ∈ J.c2`, `F₃ t / 6 ∈ J.c3`.

The derivatives are two-sided `HasDerivAt` at the points of `T` (no openness of `T` is assumed): this is what
composition with `log`, `√` and `1/·` needs, since their side conditions (positivity) are known on `T` only.
On an open subset of `T` the witnesses are the iterated derivatives (`Tails.Jet3.iteratedDeriv_eq`).
Witnesses rather than
`iteratedDeriv` are used because Mathlib has no `iteratedDeriv_mul`.

`JetEncl2 T F J` is the order-two analogue for `IJet2`, the type of the derivative `IJet.der`.

This file holds the laws of the constructors, the linear operations, products and powers, hulls and the
order-two jets; composition (`inv`, `log`, `√`) is in `SandierSerfaty.Certificate.Jet.Comp`, polynomials in
`SandierSerfaty.Certificate.Jet.Poly`.
-/

open Set Filter

public section

namespace SandierSerfaty.Certificate.Jet

open SandierSerfaty.Certificate.Arith SandierSerfaty.Tails

variable {P : ℕ}

/-! ### Interval facts -/

theorem mem_of_eq {x y : ℝ} {a : IV P} (h : IV.Mem x a) (e : x = y) : IV.Mem y a := e ▸ h

theorem mem_ivZero : IV.Mem (0 : ℝ) (ivZero : IV P) := by
  simp [IV.Mem, ivZero]

theorem mem_ivOne : IV.Mem (1 : ℝ) (ivOne : IV P) := by
  simpa [ivOne] using IV.mem_ofNat (P := P) 1

/-- The midpoint interval is the exact point `⌊(lo + hi)/2⌋ / 2^P`. -/
theorem mem_ivMid (a : IV P) :
    IV.Mem ((((SInt.fshift (SInt.add a.lo a.hi) 1).toInt : ℤ) : ℝ) / 2 ^ P) (ivMid a) :=
  IV.mem_point _

/-- A bound `|x| ≤ magR a` for every `x ∈ a`. -/
@[expose] noncomputable def magR (a : IV P) : ℝ :=
  max |((a.lo.toInt : ℤ) : ℝ)| |((a.hi.toInt : ℤ) : ℝ)| / 2 ^ P

theorem abs_le_magR {x : ℝ} {a : IV P} (h : IV.Mem x a) : |x| ≤ magR a := by
  have hp := IV.two_pow_pos' P
  unfold magR
  rw [le_div_iff₀ hp]
  obtain ⟨h1, h2⟩ := h
  have : |x * 2 ^ P| = |x| * 2 ^ P := by rw [abs_mul, abs_of_pos hp]
  rw [← this, abs_le]
  constructor
  · have := neg_abs_le ((a.lo.toInt : ℤ) : ℝ)
    have := le_max_left |((a.lo.toInt : ℤ) : ℝ)| |((a.hi.toInt : ℤ) : ℝ)|
    linarith
  · have := le_abs_self ((a.hi.toInt : ℤ) : ℝ)
    have := le_max_right |((a.lo.toInt : ℤ) : ℝ)| |((a.hi.toInt : ℤ) : ℝ)|
    linarith

/-! ### The enclosure predicates -/

/-- The interval jet `J` encloses the Taylor coefficients `F, F', F''/2, F'''/6` at every point of `T`, through
derivative witnesses `F₁, F₂, F₃` (`Tails.Jet3 T F F₁ F₂ F₃`). -/
@[expose] def JetEncl (T : Set ℝ) (F : ℝ → ℝ) (J : IJet P) : Prop :=
  ∃ F₁ F₂ F₃ : ℝ → ℝ, Jet3 T F F₁ F₂ F₃ ∧
    ∀ t ∈ T, IV.Mem (F t) J.c0 ∧ IV.Mem (F₁ t) J.c1 ∧ IV.Mem (F₂ t / 2) J.c2 ∧ IV.Mem (F₃ t / 6) J.c3

/-- The order-two jet `J` encloses `F, F', F''/2` at every point of `T`, through witnesses `F₁, F₂`. -/
@[expose] def JetEncl2 (T : Set ℝ) (F : ℝ → ℝ) (J : IJet2 P) : Prop :=
  ∃ F₁ F₂ : ℝ → ℝ, (∀ x ∈ T, HasDerivAt F (F₁ x) x) ∧ (∀ x ∈ T, HasDerivAt F₁ (F₂ x) x) ∧
    ∀ t ∈ T, IV.Mem (F t) J.c0 ∧ IV.Mem (F₁ t) J.c1 ∧ IV.Mem (F₂ t / 2) J.c2

namespace JetEncl

variable {T : Set ℝ} {F G : ℝ → ℝ} {A B : IJet P}

/-- Building an enclosure from a jet on a larger set. -/
theorem of_jet3 {U : Set ℝ} {F₁ F₂ F₃ : ℝ → ℝ} (hj : Jet3 U F F₁ F₂ F₃) (hT : T ⊆ U)
    (hb : ∀ t ∈ T, IV.Mem (F t) A.c0 ∧ IV.Mem (F₁ t) A.c1 ∧ IV.Mem (F₂ t / 2) A.c2 ∧
      IV.Mem (F₃ t / 6) A.c3) : JetEncl T F A :=
  ⟨F₁, F₂, F₃, hj.mono hT, hb⟩

theorem mono {T' : Set ℝ} (h : JetEncl T F A) (hT : T' ⊆ T) : JetEncl T' F A := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := h
  exact ⟨F₁, F₂, F₃, hj.mono hT, fun t ht => hb t (hT ht)⟩

theorem mem_c0 (h : JetEncl T F A) {t : ℝ} (ht : t ∈ T) : IV.Mem (F t) A.c0 := by
  obtain ⟨F₁, F₂, F₃, -, hb⟩ := h
  exact (hb t ht).1

/-- The function may be changed away from `T`, as long as it agrees near every point of `T`. -/
theorem congr (h : JetEncl T F A) (hFG : ∀ x ∈ T, F =ᶠ[nhds x] G) : JetEncl T G A := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := h
  refine ⟨F₁, F₂, F₃, ⟨fun x hx => (hj.d0 x hx).congr_of_eventuallyEq (hFG x hx).symm, hj.d1, hj.d2⟩,
    fun t ht => ?_⟩
  rw [← (hFG t ht).eq_of_nhds]
  exact hb t ht

/-! ### Constructors and linear operations -/

theorem const {c : ℝ} {a : IV P} (ha : IV.Mem c a) : JetEncl T (fun _ => c) (IJet.const a) :=
  ⟨_, _, _, Jet3.const c T, fun _ _ =>
    ⟨ha, mem_ivZero, mem_of_eq mem_ivZero (by ring), mem_of_eq mem_ivZero (by ring)⟩⟩

theorem var {x : IV P} (hT : ∀ t ∈ T, IV.Mem t x) : JetEncl T (fun t => t) (IJet.var x) :=
  ⟨_, _, _, Jet3.id T, fun t ht =>
    ⟨hT t ht, mem_ivOne, mem_of_eq mem_ivZero (by ring), mem_of_eq mem_ivZero (by ring)⟩⟩

theorem add (hA : JetEncl T F A) (hB : JetEncl T G B) :
    JetEncl T (fun t => F t + G t) (IJet.add A B) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  obtain ⟨G₁, G₂, G₃, hk, hc⟩ := hB
  refine ⟨_, _, _, hj.add hk, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  obtain ⟨b0, b1, b2, b3⟩ := hc t ht
  exact ⟨IV.mem_add a0 b0, IV.mem_add a1 b1, mem_of_eq (IV.mem_add a2 b2) (by ring),
    mem_of_eq (IV.mem_add a3 b3) (by ring)⟩

theorem sub (hA : JetEncl T F A) (hB : JetEncl T G B) :
    JetEncl T (fun t => F t - G t) (IJet.sub A B) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  obtain ⟨G₁, G₂, G₃, hk, hc⟩ := hB
  refine ⟨_, _, _, hj.sub hk, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  obtain ⟨b0, b1, b2, b3⟩ := hc t ht
  exact ⟨IV.mem_sub a0 b0, IV.mem_sub a1 b1, mem_of_eq (IV.mem_sub a2 b2) (by ring),
    mem_of_eq (IV.mem_sub a3 b3) (by ring)⟩

theorem neg (hA : JetEncl T F A) : JetEncl T (fun t => -F t) (IJet.neg A) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  refine ⟨fun x => -F₁ x, fun x => -F₂ x, fun x => -F₃ x,
    ⟨fun x hx => (hj.d0 x hx).neg, fun x hx => (hj.d1 x hx).neg, fun x hx => (hj.d2 x hx).neg⟩,
    fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  exact ⟨IV.mem_neg a0, IV.mem_neg a1, mem_of_eq (IV.mem_neg a2) (by ring), mem_of_eq (IV.mem_neg a3) (by ring)⟩

theorem addIV {c : ℝ} {C : IV P} (hA : JetEncl T F A) (hc : IV.Mem c C) :
    JetEncl T (fun t => F t + c) (IJet.addIV A C) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  refine ⟨_, _, _, hj.add (Jet3.const c T), fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  exact ⟨IV.mem_add a0 hc, mem_of_eq a1 (by ring), mem_of_eq a2 (by ring), mem_of_eq a3 (by ring)⟩

theorem subIV {c : ℝ} {C : IV P} (hA : JetEncl T F A) (hc : IV.Mem c C) :
    JetEncl T (fun t => F t - c) (IJet.subIV A C) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  refine ⟨_, _, _, hj.sub (Jet3.const c T), fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  exact ⟨IV.mem_sub a0 hc, mem_of_eq a1 (by ring), mem_of_eq a2 (by ring), mem_of_eq a3 (by ring)⟩

theorem scale {c : ℝ} {C : IV P} (hc : IV.Mem c C) (hA : JetEncl T F A) :
    JetEncl T (fun t => c * F t) (IJet.scale C A) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  refine ⟨_, _, _, hj.const_mul c, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  exact ⟨IV.mem_mul hc a0, IV.mem_mul hc a1, mem_of_eq (IV.mem_mul hc a2) (by ring),
    mem_of_eq (IV.mem_mul hc a3) (by ring)⟩

/-! ### Products and powers -/

theorem mul (hA : JetEncl T F A) (hB : JetEncl T G B) :
    JetEncl T (fun t => F t * G t) (IJet.mul A B) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  obtain ⟨G₁, G₂, G₃, hk, hc⟩ := hB
  refine ⟨_, _, _, hj.mul hk, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  obtain ⟨b0, b1, b2, b3⟩ := hc t ht
  refine ⟨IV.mem_mul a0 b0, mem_of_eq (IV.mem_add (IV.mem_mul a0 b1) (IV.mem_mul a1 b0)) (by ring),
    mem_of_eq (IV.mem_add (IV.mem_add (IV.mem_mul a0 b2) (IV.mem_mul a1 b1)) (IV.mem_mul a2 b0)) (by ring),
    mem_of_eq (IV.mem_add (IV.mem_add (IV.mem_mul a0 b3) (IV.mem_mul a1 b2))
      (IV.mem_add (IV.mem_mul a2 b1) (IV.mem_mul a3 b0))) (by ring)⟩

theorem sq (hA : JetEncl T F A) : JetEncl T (fun t => F t ^ 2) (IJet.sq A) := by
  have e : (fun t => F t ^ 2) = fun t => F t * F t := funext fun t => by ring
  rw [e]
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  refine ⟨_, _, _, hj.mul hj, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  refine ⟨mem_of_eq (IV.mem_sq a0) (by ring), mem_of_eq (IV.mem_mulPow2 (IV.mem_mul a0 a1) 1) (by ring),
    mem_of_eq (IV.mem_add (IV.mem_mulPow2 (IV.mem_mul a0 a2) 1) (IV.mem_sq a1)) (by ring),
    mem_of_eq (IV.mem_mulPow2 (IV.mem_add (IV.mem_mul a0 a3) (IV.mem_mul a1 a2)) 1) (by ring)⟩

theorem pow (hA : JetEncl T F A) (n : ℕ) : JetEncl T (fun t => F t ^ n) (IJet.pow A n) := by
  induction n with
  | zero =>
    show JetEncl T (fun t => F t ^ 0) (IJet.const ivOne)
    simpa using const (T := T) (mem_ivOne (P := P))
  | succ n ih =>
    show JetEncl T (fun t => F t ^ (n + 1)) (IJet.mul (IJet.pow A n) A)
    simpa only [pow_succ] using ih.mul hA

/-! ### Hulls and inclusion -/

theorem hull_left (hA : JetEncl T F A) (B : IJet P) : JetEncl T F (IJet.hull A B) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  refine ⟨F₁, F₂, F₃, hj, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  exact ⟨IV.mem_hull_left a0, IV.mem_hull_left a1, IV.mem_hull_left a2, IV.mem_hull_left a3⟩

theorem hull_right (hB : JetEncl T F B) (A : IJet P) : JetEncl T F (IJet.hull A B) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hB
  refine ⟨F₁, F₂, F₃, hj, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hb t ht
  exact ⟨IV.mem_hull_right a0, IV.mem_hull_right a1, IV.mem_hull_right a2, IV.mem_hull_right a3⟩

theorem pos (hA : JetEncl T F A) (h : IJet.posB A = true) {t : ℝ} (ht : t ∈ T) : 0 < F t :=
  IV.posB_sound h (hA.mem_c0 ht)

/-! ### The derivative and the order-two jets -/

/-- The derivative of an enclosed function is enclosed, to order two, by `der`. -/
theorem der (hA : JetEncl T F A) :
    ∃ F₁ : ℝ → ℝ, (∀ x ∈ T, HasDerivAt F (F₁ x) x) ∧ JetEncl2 T F₁ (IJet.der A) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  refine ⟨F₁, hj.d0, F₂, F₃, hj.d1, hj.d2, fun t ht => ?_⟩
  obtain ⟨-, a1, a2, a3⟩ := hb t ht
  exact ⟨a1, mem_of_eq (IV.mem_mulNat a2 2) (by push_cast; ring),
    mem_of_eq (IV.mem_mulNat a3 3) (by push_cast; ring)⟩

theorem trunc (hA : JetEncl T F A) : JetEncl2 T F (IJet.trunc A) := by
  obtain ⟨F₁, F₂, F₃, hj, hb⟩ := hA
  exact ⟨F₁, F₂, hj.d0, hj.d1, fun t ht => ⟨(hb t ht).1, (hb t ht).2.1, (hb t ht).2.2.1⟩⟩

end JetEncl

namespace JetEncl2

variable {T : Set ℝ} {F G : ℝ → ℝ} {A B : IJet2 P}

theorem mono {T' : Set ℝ} (h : JetEncl2 T F A) (hT : T' ⊆ T) : JetEncl2 T' F A := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := h
  exact ⟨F₁, F₂, fun x hx => d0 x (hT hx), fun x hx => d1 x (hT hx), fun t ht => hb t (hT ht)⟩

theorem const {c : ℝ} {a : IV P} (ha : IV.Mem c a) : JetEncl2 T (fun _ => c) (IJet2.const a) :=
  ⟨fun _ => 0, fun _ => 0, fun x _ => hasDerivAt_const x c, fun x _ => hasDerivAt_const x 0,
    fun _ _ => ⟨ha, mem_ivZero, mem_of_eq mem_ivZero (by ring)⟩⟩

theorem add (hA : JetEncl2 T F A) (hB : JetEncl2 T G B) :
    JetEncl2 T (fun t => F t + G t) (IJet2.add A B) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hA
  obtain ⟨G₁, G₂, e0, e1, hc⟩ := hB
  refine ⟨_, _, fun x hx => (d0 x hx).add (e0 x hx), fun x hx => (d1 x hx).add (e1 x hx),
    fun t ht => ?_⟩
  obtain ⟨a0, a1, a2⟩ := hb t ht
  obtain ⟨b0, b1, b2⟩ := hc t ht
  exact ⟨IV.mem_add a0 b0, IV.mem_add a1 b1, mem_of_eq (IV.mem_add a2 b2) (by ring)⟩

theorem sub (hA : JetEncl2 T F A) (hB : JetEncl2 T G B) :
    JetEncl2 T (fun t => F t - G t) (IJet2.sub A B) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hA
  obtain ⟨G₁, G₂, e0, e1, hc⟩ := hB
  refine ⟨_, _, fun x hx => (d0 x hx).sub (e0 x hx), fun x hx => (d1 x hx).sub (e1 x hx),
    fun t ht => ?_⟩
  obtain ⟨a0, a1, a2⟩ := hb t ht
  obtain ⟨b0, b1, b2⟩ := hc t ht
  exact ⟨IV.mem_sub a0 b0, IV.mem_sub a1 b1, mem_of_eq (IV.mem_sub a2 b2) (by ring)⟩

theorem neg (hA : JetEncl2 T F A) : JetEncl2 T (fun t => -F t) (IJet2.neg A) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hA
  refine ⟨_, _, fun x hx => (d0 x hx).neg, fun x hx => (d1 x hx).neg, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2⟩ := hb t ht
  exact ⟨IV.mem_neg a0, IV.mem_neg a1, mem_of_eq (IV.mem_neg a2) (by ring)⟩

theorem scale {c : ℝ} {C : IV P} (hc : IV.Mem c C) (hA : JetEncl2 T F A) :
    JetEncl2 T (fun t => c * F t) (IJet2.scale C A) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hA
  refine ⟨_, _, fun x hx => (d0 x hx).const_mul c, fun x hx => (d1 x hx).const_mul c,
    fun t ht => ?_⟩
  obtain ⟨a0, a1, a2⟩ := hb t ht
  exact ⟨IV.mem_mul hc a0, IV.mem_mul hc a1, mem_of_eq (IV.mem_mul hc a2) (by ring)⟩

theorem mul (hA : JetEncl2 T F A) (hB : JetEncl2 T G B) :
    JetEncl2 T (fun t => F t * G t) (IJet2.mul A B) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hA
  obtain ⟨G₁, G₂, e0, e1, hc⟩ := hB
  refine ⟨_, _, fun x hx => (d0 x hx).mul (e0 x hx),
    fun x hx => ((d1 x hx).mul (e0 x hx)).add ((d0 x hx).mul (e1 x hx)), fun t ht => ?_⟩
  obtain ⟨a0, a1, a2⟩ := hb t ht
  obtain ⟨b0, b1, b2⟩ := hc t ht
  exact ⟨IV.mem_mul a0 b0, mem_of_eq (IV.mem_add (IV.mem_mul a0 b1) (IV.mem_mul a1 b0)) (by ring),
    mem_of_eq (IV.mem_add (IV.mem_add (IV.mem_mul a0 b2) (IV.mem_mul a1 b1)) (IV.mem_mul a2 b0))
      (by ring)⟩

theorem hull_left (hA : JetEncl2 T F A) (B : IJet2 P) : JetEncl2 T F (IJet2.hull A B) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hA
  exact ⟨F₁, F₂, d0, d1, fun t ht => ⟨IV.mem_hull_left (hb t ht).1, IV.mem_hull_left (hb t ht).2.1,
    IV.mem_hull_left (hb t ht).2.2⟩⟩

theorem hull_right (hB : JetEncl2 T F B) (A : IJet2 P) : JetEncl2 T F (IJet2.hull A B) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hB
  exact ⟨F₁, F₂, d0, d1, fun t ht => ⟨IV.mem_hull_right (hb t ht).1, IV.mem_hull_right (hb t ht).2.1,
    IV.mem_hull_right (hb t ht).2.2⟩⟩

end JetEncl2

end SandierSerfaty.Certificate.Jet
