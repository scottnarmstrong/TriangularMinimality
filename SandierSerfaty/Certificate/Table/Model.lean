/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.Eval
public import SandierSerfaty.Certificate.Basis.CoreSound
public import SandierSerfaty.Certificate.Basis.DataSound

/-!
# The real model of the table and the soundness of `fh`

On a segment `j`, with the pieces `Cal.Piece.u i j`, `Cal.Piece.D i j` (smooth on `(0, ∞)`):

* `Bp j = ∑_{i ≤ 38} Piece.u i j` (`B̃` on the segment), `B1p j = Bp' + 1/t` (`B̃₁`), `Y1 j = t Bp`,
  `Y2 j = -2 B1p + t B1p²` (the integrands of `S̃₁, S̃₂`), `Qm i j = t D_i' - k_i D_i`;
* `F0m j S1 S2 H` and `Em j`: the functions `f̃₀`, `ẽ` of `cal:f0-e` on the segment, with sector functions
  `S1, S2` and `H i` (`H̃_{k_i}` of mode `i`) as arguments; `SectorODE j I S1 S2 H` says that they satisfy the
  radial ODEs `comp:radial-odes` on `I`.

`PtValid j T pt`: the jets of `pt` enclose `t, 1/t, log t, B1p, Y1, Y2` and the `D_i`, `D_i'` on `T`
(`mkPt_valid`, on a positive nondegenerate cell). From enclosures of the values of the sector functions and the
ODEs, `s1J_sound`, `s2J_sound`, `hJ_sound` give their order-two jets (`comp:jet-ode`), and `fh_sound` gives
the enclosure of the six-tuple (`TupEncl`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Table

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis
open SandierSerfaty.Calibration SandierSerfaty.Tails

/-! ### The real model -/

/-- `B̃` on segment `j`. -/
@[expose] noncomputable def Bp (j : ℕ) (t : ℝ) : ℝ := ∑ i ∈ Finset.range 39, Piece.u i j t

/-- `B̃₁ = B̃' + 1/t` on segment `j`. -/
@[expose] noncomputable def B1p (j : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) t + t⁻¹

/-- The integrand `t B̃` of `S̃₁`. -/
@[expose] noncomputable def Y1 (j : ℕ) (t : ℝ) : ℝ := t * Bp j t

/-- The integrand `-2 B̃₁ + t B̃₁²` of `S̃₂`. -/
@[expose] noncomputable def Y2 (j : ℕ) (t : ℝ) : ℝ := -2 * B1p j t + t * (B1p j t * B1p j t)

/-- `D_i'` on segment `j`. -/
@[expose] noncomputable def D1 (i j : ℕ) (t : ℝ) : ℝ := iteratedDeriv 1 (Piece.D i j) t

/-- `Q_i = t D_i' - k_i D_i` on segment `j`. -/
@[expose] noncomputable def Qm (i j : ℕ) (t : ℝ) : ℝ := t * D1 i j t - (k i : ℝ) * Piece.D i j t

/-- `∑_{n < N} D_{m+n}/(k_{m+n} + 2)`. -/
@[expose] noncomputable def dsumR (j m N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (1 / ((k (m + n) : ℝ) + 2)) * Piece.D (m + n) j t

/-- `∑_{n < N} (-2 D + 2k D H)` (mode `m + n`). -/
@[expose] noncomputable def linR (j : ℕ) (H : ℕ → ℝ → ℝ) (m N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (-2 * Piece.D (m + n) j t + (2 * k (m + n) : ℝ) * (Piece.D (m + n) j t * H (m + n) t))

/-- `∑_{n < N} (k_a k_{m+n}/(k_a + k_{m+n})) D_{m+n}`. -/
@[expose] noncomputable def quadInR (j a m N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, ((k a * k (m + n) : ℕ) / ((k a + k (m + n) : ℕ) : ℝ)) * Piece.D (m + n) j t

/-- `∑_{n < N} D_{m+n} ∑_{n' < 39} (k k'/(k + k')) D_{n'}`. -/
@[expose] noncomputable def quadR (j m N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Piece.D (m + n) j t * quadInR j (m + n) 0 39 t

/-- `∑_{n < N} Q_{m+n}/(k_a + k_{m+n})`. -/
@[expose] noncomputable def eInR (j a m N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, (1 / ((k a + k (m + n) : ℕ) : ℝ)) * Qm (m + n) j t

/-- `∑_{n < N} Q_{m+n} ∑_{n' < 39} Q_{n'}/(k + k')`. -/
@[expose] noncomputable def eR (j m N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Qm (m + n) j t * eInR j (m + n) 0 39 t

/-- `f̃₀` on segment `j` with sector functions `S1, S2, H` (`cal:f0-e`; `H i = H̃_{k_i}`). -/
@[expose] noncomputable def F0m (j : ℕ) (S1 S2 : ℝ → ℝ) (H : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  -(Real.pi * 2) * (S1 t + t * t * dsumR j 0 39 t) -
    1 / 2 * (Real.log t + S2 t + linR j H 0 39 t + quadR j 0 39 t)

/-- `ẽ = ½ ∑_i Q_i ∑_j Q_j/(k_i + k_j)` on segment `j`. -/
@[expose] noncomputable def Em (j : ℕ) (t : ℝ) : ℝ := 1 / 2 * eR j 0 39 t

/-- The sector functions satisfy the radial ODEs `comp:radial-odes` of segment `j` on `I`. -/
structure SectorODE (j : ℕ) (I : Set ℝ) (S1 S2 : ℝ → ℝ) (H : ℕ → ℝ → ℝ) : Prop where
  s1 : ∀ t ∈ I, HasDerivAt S1 (Y1 j t) t
  s2 : ∀ t ∈ I, HasDerivAt S2 (Y2 j t) t
  h : ∀ i, i < 39 → ∀ t ∈ I, HasDerivAt (H i) (B1p j t - (k i : ℝ) * H i t / t) t

theorem SectorODE.mono {j : ℕ} {I I' : Set ℝ} {S1 S2 : ℝ → ℝ} {H : ℕ → ℝ → ℝ}
    (h : SectorODE j I S1 S2 H) (hI : I' ⊆ I) : SectorODE j I' S1 S2 H :=
  ⟨fun t ht => h.s1 t (hI ht), fun t ht => h.s2 t (hI ht), fun i hi t ht => h.h i hi t (hI ht)⟩

/-- The tuple `tp` encloses `F, F', F'', E, E', E''` at every point of `T` (derivative witnesses). -/
@[expose] def TupEncl (T : Set ℝ) (F E : ℝ → ℝ) (tp : Tup) : Prop :=
  ∃ F₁ F₂ E₁ E₂ : ℝ → ℝ, (∀ x ∈ T, HasDerivAt F (F₁ x) x ∧ HasDerivAt F₁ (F₂ x) x ∧
      HasDerivAt E (E₁ x) x ∧ HasDerivAt E₁ (E₂ x) x) ∧
    ∀ t ∈ T, IV.Mem (F t) tp.f0 ∧ IV.Mem (F₁ t) tp.f1 ∧ IV.Mem (F₂ t) tp.f2 ∧ IV.Mem (E t) tp.e0 ∧
      IV.Mem (E₁ t) tp.e1 ∧ IV.Mem (E₂ t) tp.e2

theorem TupEncl.of_tupSub {T : Set ℝ} {F E : ℝ → ℝ} {a b : Tup} (h : TupEncl T F E a)
    (hs : tupSub a b = true) : TupEncl T F E b := by
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := h
  simp only [tupSub, Bool.and_eq_true] at hs
  obtain ⟨⟨s0, s1, s2⟩, t0, t1, t2⟩ := hs
  exact ⟨F₁, F₂, E₁, E₂, hd, fun t ht => by
    obtain ⟨m0, m1, m2, n0, n1, n2⟩ := hm t ht
    exact ⟨IV.mem_of_subsetB s0 m0, IV.mem_of_subsetB s1 m1, IV.mem_of_subsetB s2 m2,
      IV.mem_of_subsetB t0 n0, IV.mem_of_subsetB t1 n1, IV.mem_of_subsetB t2 n2⟩⟩

theorem TupEncl.mono {T T' : Set ℝ} {F E : ℝ → ℝ} {a : Tup} (h : TupEncl T F E a) (hT : T' ⊆ T) :
    TupEncl T' F E a := by
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := h
  exact ⟨F₁, F₂, E₁, E₂, fun x hx => hd x (hT hx), fun t ht => hm t (hT ht)⟩

theorem tupEncl_tupOf {T : Set ℝ} {F E : ℝ → ℝ} {f e : IJet2 128} (hf : JetEncl2 T F f)
    (he : JetEncl2 T E e) : TupEncl T F E (tupOf f e) := by
  obtain ⟨F₁, F₂, d0, d1, hb⟩ := hf
  obtain ⟨E₁, E₂, e0, e1, hc⟩ := he
  refine ⟨F₁, F₂, E₁, E₂, fun x hx => ⟨d0 x hx, d1 x hx, e0 x hx, e1 x hx⟩, fun t ht => ?_⟩
  obtain ⟨a0, a1, a2⟩ := hb t ht
  obtain ⟨b0, b1, b2⟩ := hc t ht
  exact ⟨a0, a1, mem_of_eq (IV.mem_mulNat a2 2) (by push_cast; ring), b0, b1,
    mem_of_eq (IV.mem_mulNat b2 2) (by push_cast; ring)⟩

/-! ### Jets at an evaluation set -/

theorem jetEncl2_of_eq {T : Set ℝ} {F G : ℝ → ℝ} {J : IJet2 128} (h : JetEncl2 T F J) (e : ∀ t, F t = G t) :
    JetEncl2 T G J := by
  have : F = G := funext e
  rwa [this] at h

/-- The jets of the basis `D`'s and of their derivatives, modes `m, m + 1, …`. -/
@[expose] def DList (T : Set ℝ) (j : ℕ) : ℕ → List (IJet 128) → Prop
  | _, [] => True
  | m, D :: ds => (JetEncl T (Piece.D m j) D ∧ JetEncl2 T (D1 m j) (IJet.der D)) ∧ DList T j (m + 1) ds

/-- The jets at an evaluation set enclose their real functions on `T`. -/
structure PtValid (j : ℕ) (T : Set ℝ) (pt : Pt) : Prop where
  t : JetEncl2 T (fun t => t) pt.t
  w : JetEncl2 T (fun t => t⁻¹) pt.w
  lg : JetEncl2 T Real.log pt.lg
  b1 : JetEncl2 T (B1p j) pt.b1
  y1 : JetEncl2 T (Y1 j) pt.y1
  y2 : JetEncl2 T (Y2 j) pt.y2
  ds : DList T j 0 pt.ds
  ks : KList 0 pt.ks
  len : pt.ds.length = 39
  klen : pt.ks.length = 39
  pos : ∀ t ∈ T, 0 < t

theorem DList.mono {T T' : Set ℝ} {j : ℕ} (hT : T' ⊆ T) : ∀ {m : ℕ} {ds : List (IJet 128)}, DList T j m ds →
    DList T' j m ds
  | _, [], _ => trivial
  | _, _ :: _, ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1.mono hT, h2.mono hT⟩, DList.mono hT h3⟩

theorem PtValid.mono {j : ℕ} {T T' : Set ℝ} {pt : Pt} (h : PtValid j T pt) (hT : T' ⊆ T) : PtValid j T' pt :=
  ⟨h.t.mono hT, h.w.mono hT, h.lg.mono hT, h.b1.mono hT, h.y1.mono hT, h.y2.mono hT, h.ds.mono hT, h.ks,
    h.len, h.klen, fun t ht => h.pos t (hT ht)⟩

/-- On a nondegenerate positive cell, the jet of a piece gives the order-two jet of its derivative. -/
theorem der_explicit {X : IV 128} (hX : IV.posB X = true) (hlt : SInt.blt X.lo X.hi = true) {F : ℝ → ℝ}
    (hF : ContDiffOn ℝ ⊤ F (Ioi 0)) {J : IJet 128} (h : JetEncl {t | IV.Mem t X} F J) :
    JetEncl2 {t | IV.Mem t X} (iteratedDeriv 1 F) (IJet.der J) := by
  have hG := jet3_iteratedDeriv isOpen_Ioi (hF.of_le (by norm_cast))
  refine ⟨iteratedDeriv 2 F, iteratedDeriv 3 F, fun x hx => hG.d1 x (IV.posB_sound hX hx),
    fun x hx => hG.d2 x (IV.posB_sound hX hx), fun t ht => ?_⟩
  obtain ⟨-, m1, m2, m3⟩ := jetEncl_witness_mem hlt (piece_jet3 hF hX) h ht
  exact ⟨m1, mem_of_eq (IV.mem_mulNat m2 2) (by push_cast; ring),
    mem_of_eq (IV.mem_mulNat m3 3) (by push_cast; ring)⟩

theorem dList_of {X : IV 128} (hX : IV.posB X = true) (hlt : SInt.blt X.lo X.hi = true) {j : ℕ} :
    ∀ {m : ℕ} {ds : List (IJet 128)}, JetEnclFrom {t | IV.Mem t X} (fun n => Piece.D n j) m ds →
      DList {t | IV.Mem t X} j m ds
  | _, [], _ => trivial
  | m, _ :: _, ⟨h1, h2⟩ => ⟨⟨h1, der_explicit hX hlt (contDiffOn_Piece_D m j) h1⟩, dList_of hX hlt h2⟩

/-- **The jets at an evaluation set.** -/
theorem mkPt_valid {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 6) {X : IV 128}
    (hok : okSet X = true) : PtValid j {t | IV.Mem t X} (mkPt d j X) := by
  simp only [okSet, Bool.and_eq_true] at hok
  obtain ⟨hX, hlt⟩ := hok
  have hT : ∀ s, IV.Mem s X → s ∈ Ioi (0 : ℝ) := fun s hs => IV.posB_sound hX hs
  obtain ⟨hB, hDs, hks⟩ := basis_sound hd hX hj
  have hv : JetEncl {t | IV.Mem t X} (fun t => t) (IJet.var X) := JetEncl.var fun s hs => hs
  have hL := hv.log hX
  have hA := hB.add hL
  -- `B̃₁` from the explicit jet of `B̃ + log`
  have hG : Jet3 (Ioi 0) (fun s => ∑ i ∈ Finset.range 39, Piece.u i j s + Real.log s)
      (fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 1 (Piece.u i j) s + s⁻¹)
      (fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) s + -s⁻¹ ^ 2)
      (fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) s + 2 * s⁻¹ ^ 3) :=
    (jet3_sum _ fun i _ => jet3_iteratedDeriv isOpen_Ioi
      ((contDiffOn_Piece_u i j).of_le (by norm_cast))).add jet3_log
  have hb1 : JetEncl2 {t | IV.Mem t X} (B1p j) (IJet.der (IJet.add (basis d j X).bsum (IJet.log (IJet.var X)))) := by
    refine ⟨fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 2 (Piece.u i j) s + -s⁻¹ ^ 2,
      fun s => ∑ i ∈ Finset.range 39, iteratedDeriv 3 (Piece.u i j) s + 2 * s⁻¹ ^ 3,
      fun x hx => hG.d1 x (hT x hx), fun x hx => hG.d2 x (hT x hx), fun t ht => ?_⟩
    obtain ⟨-, m1, m2, m3⟩ := jetEncl_witness_mem hlt (hG.mono fun s hs => hT s hs) hA ht
    exact ⟨m1, mem_of_eq (IV.mem_mulNat m2 2) (by push_cast; ring),
      mem_of_eq (IV.mem_mulNat m3 3) (by push_cast; ring)⟩
  have ht2 : JetEncl2 {t | IV.Mem t X} (fun t => t) (IJet.trunc (IJet.var X)) := hv.trunc
  have hy2 : JetEncl2 {t | IV.Mem t X} (Y2 j)
      (y2Of (IJet.trunc (IJet.var X)) (IJet.der (IJet.add (basis d j X).bsum (IJet.log (IJet.var X))))) := by
    have := (JetEncl2.scale (IV.mem_neg (IV.mem_ofNat (P := 128) 2)) hb1).add (ht2.mul (hb1.mul hb1))
    exact jetEncl2_of_eq this fun t => by simp [Y2]
  have hlen : (basis d j X).ds.length = 39 := by simp [basis, basisWith, dsLoop_length, hd.len]
  have hklen : (basis d j X).ks.length = 39 := by simp [basis, basisWith, ksOf_length, hd.len]
  exact ⟨ht2, (hv.invPos hX).trunc, hL.trunc, hb1,
    jetEncl2_of_eq (hv.mul hB).trunc fun t => rfl, hy2, dList_of hX hlt hDs, hks, hlen, hklen,
    fun s hs => hT s hs⟩

/-! ### The sector functions -/

section Sector

variable {j : ℕ} {T : Set ℝ} {pt : Pt}

theorem s1J_sound (hp : PtValid j T pt) {S1 : ℝ → ℝ} (hS : ∀ x ∈ T, HasDerivAt S1 (Y1 j x) x)
    {V : IV 128} (hV : ∀ x ∈ T, IV.Mem (S1 x) V) : JetEncl2 T S1 (s1J pt V) := by
  obtain ⟨Y₁, Y₂, d0, d1, hb⟩ := hp.y1
  refine ⟨Y1 j, Y₁, hS, d0, fun t ht => ⟨hV t ht, (hb t ht).1, ?_⟩⟩
  simpa [s1J] using IV.mem_divPow2 (hb t ht).2.1 1

theorem s2J_sound (hp : PtValid j T pt) {S2 : ℝ → ℝ} (hS : ∀ x ∈ T, HasDerivAt S2 (Y2 j x) x)
    {V : IV 128} (hV : ∀ x ∈ T, IV.Mem (S2 x) V) : JetEncl2 T S2 (s2J pt V) := by
  obtain ⟨Y₁, Y₂, d0, d1, hb⟩ := hp.y2
  refine ⟨Y2 j, Y₁, hS, d0, fun t ht => ⟨hV t ht, (hb t ht).1, ?_⟩⟩
  simpa [s2J] using IV.mem_divPow2 (hb t ht).2.1 1

/-- `H̃_k` to order two from its value and `H' = B̃₁ - k H/t` (the coefficients solved in increasing order). -/
theorem hJ_sound (hp : PtValid j T pt) {H : ℝ → ℝ} {kk : ℕ}
    (hH : ∀ x ∈ T, HasDerivAt H (B1p j x - (kk : ℝ) * H x / x) x) {V : IV 128}
    (hV : ∀ x ∈ T, IV.Mem (H x) V) : JetEncl2 T H (hJ pt kk V) := by
  obtain ⟨b₁, b₂, bd0, bd1, hb⟩ := hp.b1
  obtain ⟨w₁, w₂, wd0, wd1, hw⟩ := hp.w
  have hw1 : ∀ x ∈ T, w₁ x = -(x ^ 2)⁻¹ := fun x hx =>
    (wd0 x hx).unique (hasDerivAt_inv (ne_of_gt (hp.pos x hx)))
  set H₁ : ℝ → ℝ := fun x => B1p j x - (H x * x⁻¹) * kk with hH₁
  have hH' : ∀ x ∈ T, HasDerivAt H (H₁ x) x := fun x hx =>
    (hH x hx).congr_deriv (by simp only [hH₁]; ring)
  refine ⟨H₁, fun x => b₁ x - (H₁ x * x⁻¹ + H x * w₁ x) * kk, hH', fun x hx => ?_, fun t ht => ?_⟩
  · have h1 := ((hH' x hx).mul (wd0 x hx)).mul_const (kk : ℝ)
    have h2 := (bd0 x hx).sub h1
    refine (h2.congr_deriv rfl).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    rfl
  · obtain ⟨b0, b1, -⟩ := hb t ht
    obtain ⟨w0, w1', -⟩ := hw t ht
    have hX1 : IV.Mem (H₁ t) (hX1 pt kk V) := IV.mem_sub b0 (IV.mem_mulNat (IV.mem_mul (hV t ht) w0) kk)
    refine ⟨hV t ht, hX1, ?_⟩
    have := IV.mem_divPow2 (IV.mem_sub b1 (IV.mem_mulNat (IV.mem_add (IV.mem_mul hX1 w0)
      (IV.mem_mul (hV t ht) w1')) kk)) 1
    simpa [hJ, hJWith] using this

end Sector

/-! ### The sums of the tuple -/

section Sums

variable {j : ℕ} {T : Set ℝ} {pt : Pt}

theorem mem_frac_inv (a : ℕ) (ha : 0 < a) : IV.Mem (1 / (a : ℝ)) (frac false 1 a) := by
  simpa using mem_frac_pos 1 a ha

theorem dsumL_sound : ∀ (ks : List ℕ) (ds : List (IJet 128)) (m : ℕ), KList m ks → DList T j m ds →
    ks.length = ds.length → JetEncl2 T (dsumR j m ds.length) (dsumL ks ds)
  | [], [], m, _, _, _ => jetEncl2_of_eq (JetEncl2.const (P := 128) mem_ivZero) fun t => by simp [dsumR]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: ks, D :: ds, m, ⟨hx, hks⟩, ⟨⟨hD, _⟩, hds⟩, hl => by
    have ih := dsumL_sound ks ds (m + 1) hks hds (by simpa using hl)
    have hc : IV.Mem (1 / ((k m : ℝ) + 2)) (frac false 1 (Nat.add x 2)) := by
      have := mem_frac_inv (Nat.add x 2) (by simp only [Nat.add_eq]; omega)
      simpa [hx] using this
    have := (JetEncl2.scale hc hD.trunc).add ih
    refine jetEncl2_of_eq this fun t => ?_
    simp only [dsumR, List.length_cons, Finset.sum_range_succ', add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

/-- The `H̃` jets of the modes `m, m + 1, …` from the state values. -/
@[expose] def HJList (T : Set ℝ) (pt : Pt) (H : ℕ → ℝ → ℝ) : ℕ → List ℕ → List (IV 128) → Prop
  | m, x :: ks, V :: vs => JetEncl2 T (H m) (hJ pt x V) ∧ HJList T pt H (m + 1) ks vs
  | _, _, _ => True

theorem linL_sound {H : ℕ → ℝ → ℝ} : ∀ (ks : List ℕ) (ds : List (IJet 128)) (vs : List (IV 128)) (m : ℕ),
    KList m ks → DList T j m ds → HJList T pt H m ks vs → ks.length = ds.length → vs.length = ds.length →
    JetEncl2 T (linR j H m ds.length) (linL pt ks ds vs)
  | [], [], [], m, _, _, _, _, _ => jetEncl2_of_eq (JetEncl2.const (P := 128) mem_ivZero) fun t => by simp [linR]
  | [], _ :: _, _, _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, _, h, _ => by simp at h
  | _, [], _ :: _, _, _, _, _, _, h => by simp at h
  | _, _ :: _, [], _, _, _, _, _, h => by simp at h
  | x :: ks, D :: ds, V :: vs, m, ⟨hx, hks⟩, ⟨⟨hD, _⟩, hds⟩, ⟨hHm, hHs⟩, hl, hl' => by
    have ih := linL_sound ks ds vs (m + 1) hks hds hHs (by simpa using hl) (by simpa using hl')
    have h2 : IV.Mem ((2 * k m : ℕ) : ℝ) (IV.ofNat (P := 128) (Nat.mul 2 x)) := by
      simpa [hx] using IV.mem_ofNat (P := 128) (Nat.mul 2 x)
    have := ((JetEncl2.scale (IV.mem_neg (IV.mem_ofNat (P := 128) 2)) hD.trunc).add
      (JetEncl2.scale h2 (hD.trunc.mul hHm))).add ih
    refine jetEncl2_of_eq this fun t => ?_
    simp only [linR, List.length_cons, Finset.sum_range_succ', add_zero]
    rw [add_comm (∑ n ∈ Finset.range ds.length, _)]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

theorem quadIn_sound {a : ℕ} {x₀ : ℕ} (ha : x₀ = k a) : ∀ (ks : List ℕ) (ds : List (IJet 128)) (m : ℕ),
    KList m ks → DList T j m ds → ks.length = ds.length →
    JetEncl2 T (quadInR j a m ds.length) (quadIn x₀ ks ds)
  | [], [], m, _, _, _ => jetEncl2_of_eq (JetEncl2.const (P := 128) mem_ivZero) fun t => by simp [quadInR]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: ks, D :: ds, m, ⟨hx, hks⟩, ⟨⟨hD, _⟩, hds⟩, hl => by
    have ih := quadIn_sound ha ks ds (m + 1) hks hds (by simpa using hl)
    have hpos : 0 < Nat.add x₀ x := by simp only [Nat.add_eq]; rw [ha]; have := k_pos a; omega
    have hc : IV.Mem (((k a * k m : ℕ) : ℝ) / ((k a + k m : ℕ) : ℝ)) (frac false (Nat.mul x₀ x) (Nat.add x₀ x)) := by
      have := mem_frac_pos (Nat.mul x₀ x) (Nat.add x₀ x) hpos
      simpa [ha, hx] using this
    have := (JetEncl2.scale hc hD.trunc).add ih
    refine jetEncl2_of_eq this fun t => ?_
    simp only [quadInR, List.length_cons, Finset.sum_range_succ', add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

theorem quadL_sound {aks : List ℕ} {ads : List (IJet 128)} (hak : KList 0 aks) (had : DList T j 0 ads)
    (hal : aks.length = ads.length) (h39 : ads.length = 39) :
    ∀ (ks : List ℕ) (ds : List (IJet 128)) (m : ℕ), KList m ks → DList T j m ds → ks.length = ds.length →
      JetEncl2 T (quadR j m ds.length) (quadL aks ads ks ds)
  | [], [], m, _, _, _ => jetEncl2_of_eq (JetEncl2.const (P := 128) mem_ivZero) fun t => by simp [quadR]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: ks, D :: ds, m, ⟨hx, hks⟩, ⟨⟨hD, _⟩, hds⟩, hl => by
    have ih := quadL_sound hak had hal h39 ks ds (m + 1) hks hds (by simpa using hl)
    have hin := quadIn_sound (a := m) hx aks ads 0 hak had hal
    rw [h39] at hin
    have := (hD.trunc.mul hin).add ih
    refine jetEncl2_of_eq this fun t => ?_
    simp only [quadR, List.length_cons, Finset.sum_range_succ', add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

theorem qOf_sound (hp : PtValid j T pt) {m x : ℕ} (hx : x = k m) {D : IJet 128}
    (hD : JetEncl T (Piece.D m j) D ∧ JetEncl2 T (D1 m j) (IJet.der D)) :
    JetEncl2 T (Qm m j) (qOf pt x D) := by
  have := (hp.t.mul hD.2).sub (JetEncl2.scale (IV.mem_ofNat (P := 128) x) hD.1.trunc)
  exact jetEncl2_of_eq this fun t => by simp [Qm, hx]

theorem eIn_sound (hp : PtValid j T pt) {a : ℕ} {x₀ : ℕ} (ha : x₀ = k a) :
    ∀ (ks : List ℕ) (ds : List (IJet 128)) (m : ℕ), KList m ks → DList T j m ds → ks.length = ds.length →
      JetEncl2 T (eInR j a m ds.length) (eIn pt x₀ ks ds)
  | [], [], m, _, _, _ => jetEncl2_of_eq (JetEncl2.const (P := 128) mem_ivZero) fun t => by simp [eInR]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: ks, D :: ds, m, ⟨hx, hks⟩, ⟨hD, hds⟩, hl => by
    have ih := eIn_sound hp ha ks ds (m + 1) hks hds (by simpa using hl)
    have hpos : 0 < Nat.add x₀ x := by simp only [Nat.add_eq]; rw [ha]; have := k_pos a; omega
    have hc : IV.Mem (1 / ((k a + k m : ℕ) : ℝ)) (frac false 1 (Nat.add x₀ x)) := by
      have := mem_frac_inv (Nat.add x₀ x) hpos
      simpa [ha, hx] using this
    have := (JetEncl2.scale hc (qOf_sound hp hx hD)).add ih
    refine jetEncl2_of_eq this fun t => ?_
    simp only [eInR, List.length_cons, Finset.sum_range_succ', add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

theorem eL_sound (hp : PtValid j T pt) {aks : List ℕ} {ads : List (IJet 128)} (hak : KList 0 aks)
    (had : DList T j 0 ads) (hal : aks.length = ads.length) (h39 : ads.length = 39) :
    ∀ (ks : List ℕ) (ds : List (IJet 128)) (m : ℕ), KList m ks → DList T j m ds → ks.length = ds.length →
      JetEncl2 T (eR j m ds.length) (eL pt aks ads ks ds)
  | [], [], m, _, _, _ => jetEncl2_of_eq (JetEncl2.const (P := 128) mem_ivZero) fun t => by simp [eR]
  | [], _ :: _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, h => by simp at h
  | x :: ks, D :: ds, m, ⟨hx, hks⟩, ⟨hD, hds⟩, hl => by
    have ih := eL_sound hp hak had hal h39 ks ds (m + 1) hks hds (by simpa using hl)
    have hin := eIn_sound hp (a := m) hx aks ads 0 hak had hal
    rw [h39] at hin
    have := ((qOf_sound hp hx hD).mul hin).add ih
    refine jetEncl2_of_eq this fun t => ?_
    simp only [eR, List.length_cons, Finset.sum_range_succ', add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

end Sums

/-! ### The tuple -/

/-- The state encloses the values of the sector functions at every point of `T`. -/
structure StateOn (T : Set ℝ) (S1 S2 : ℝ → ℝ) (H : ℕ → ℝ → ℝ) (S : SState) : Prop where
  s1 : ∀ x ∈ T, IV.Mem (S1 x) S.s1
  s2 : ∀ x ∈ T, IV.Mem (S2 x) S.s2
  hs : ∀ x ∈ T, EnclFrom (fun i => H i x) 0 S.hs
  len : S.hs.length = 39

theorem hjList_of {j : ℕ} {T : Set ℝ} {pt : Pt} (hp : PtValid j T pt) {H : ℕ → ℝ → ℝ}
    (hH : ∀ i, i < 39 → ∀ x ∈ T, HasDerivAt (H i) (B1p j x - (k i : ℝ) * H i x / x) x) :
    ∀ (ks : List ℕ) (vs : List (IV 128)) (m : ℕ), KList m ks → m + ks.length ≤ 39 →
      (∀ x ∈ T, EnclFrom (fun i => H i x) m vs) → HJList T pt H m ks vs
  | [], _, _, _, _, _ => by simp [HJList]
  | _ :: _, [], _, _, _, _ => by simp [HJList]
  | x :: ks, V :: vs, m, ⟨hx, hks⟩, hl, hV => by
    refine ⟨?_, hjList_of hp hH ks vs (m + 1) hks (by simp at hl; omega) fun y hy => (hV y hy).2⟩
    rw [hx]
    exact hJ_sound hp (hH m (by simp at hl; omega)) fun y hy => (hV y hy).1

/-- **Soundness of `fh`**: from valid jets, a state enclosing the sector functions on `T` and the ODEs, the
tuple encloses `(f̃₀, f̃₀', f̃₀'', ẽ, ẽ', ẽ'')` of the model on `T`. -/
theorem fh_sound {j : ℕ} {T : Set ℝ} {pt : Pt} (hp : PtValid j T pt) {pi : IV 128}
    (hpi : IV.Mem Real.pi pi) {S1 S2 : ℝ → ℝ} {H : ℕ → ℝ → ℝ} (hode : SectorODE j T S1 S2 H) {S : SState}
    (hS : StateOn T S1 S2 H S) : TupEncl T (F0m j S1 S2 H) (Em j) (fh pi pt S) := by
  have hkl : pt.ks.length = pt.ds.length := by rw [hp.klen, hp.len]
  have hvl : S.hs.length = pt.ds.length := by rw [hS.len, hp.len]
  have hd := dsumL_sound pt.ks pt.ds 0 hp.ks hp.ds hkl
  have hhj := hjList_of hp hode.h pt.ks S.hs 0 hp.ks (by rw [hp.klen]) hS.hs
  have hl := linL_sound pt.ks pt.ds S.hs 0 hp.ks hp.ds hhj hkl hvl
  have hq := quadL_sound hp.ks hp.ds hkl hp.len pt.ks pt.ds 0 hp.ks hp.ds hkl
  have he := eL_sound hp hp.ks hp.ds hkl hp.len pt.ks pt.ds 0 hp.ks hp.ds hkl
  rw [hp.len] at hd hl hq he
  have h1 := s1J_sound hp hode.s1 hS.s1
  have h2 := s2J_sound hp hode.s2 hS.s2
  have hf : JetEncl2 T (F0m j S1 S2 H) (fJ pi pt S) := by
    have hc : IV.Mem (-(Real.pi * 2)) (IV.neg (IV.mulNat pi 2)) := by
      simpa using IV.mem_neg (IV.mem_mulNat hpi 2)
    have := (JetEncl2.scale hc (h1.add ((hp.t.mul hp.t).mul hd))).sub
      (JetEncl2.scale (mem_frac_inv 2 (by norm_num)) (((hp.lg.add h2).add hl).add hq))
    exact jetEncl2_of_eq this fun t => by simp [F0m]
  have hE : JetEncl2 T (Em j) (eJ pt) :=
    jetEncl2_of_eq (JetEncl2.scale (mem_frac_inv 2 (by norm_num)) he) fun t => by simp [Em]
  exact tupEncl_tupOf hf hE

end SandierSerfaty.Certificate.Table

