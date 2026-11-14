/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Eval
public import SandierSerfaty.Certificate.Jet.Poly
public import SandierSerfaty.Certificate.Jet.Comp
public import SandierSerfaty.Calibration.Spline

/-!
# Soundness of the radial basis

`basis_sound`: if the interval constants are valid (`BasisData.Valid`: they enclose `π, p, p - c, p², R₀,
R₀ + .001`, the 2-jet of `γ` at `R₀` and, per mode `i = 1, …, 38`, `(-1)^i c_i`, `T₀, T₁, T₂`, the edge
coefficients and the 2-jet of `V_i` at `R₀`) and the cell `X` is positive, then on `T = {t | t ∈ X}` and for every
segment `j ≤ 6`

* `(basis d j X).bsum` encloses the jet of `∑_{i ≤ 38} Piece.u i j` (`JetEncl`), and
* `(basis d j X).ds` encloses the jets of `Piece.D 0 j, …, Piece.D 38 j` (`JetEnclFrom`), with the exponents
  `(basis d j X).ks = [k 0, …, k 38]` (`KList`).

The pieces are the functions `Cal.Piece.u`, `Cal.Piece.D` of `SandierSerfaty.Calibration.Pieces` (globally
smooth on `(0, ∞)`, equal to the splines on the closed segments): the real side of each evaluator branch is a
rewriting of the piece by ring identities (`squintic_eq`, `Ppoly_eq`, `Qpoly_eq`, `V_eq_horner`, ...).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Calibration

/-! ### Generalities -/

theorem jetEncl_of_eq {T : Set ℝ} {F G : ℝ → ℝ} {J : IJet 128} (h : JetEncl T F J) (e : ∀ t, F t = G t) :
    JetEncl T G J := by
  have : F = G := funext e
  rwa [this] at h

/-- The list `l` encloses the jets of `F m, F (m + 1), …` on `T`. -/
@[expose] def JetEnclFrom (T : Set ℝ) (F : ℕ → ℝ → ℝ) : ℕ → List (IJet 128) → Prop
  | _, [] => True
  | m, a :: as => JetEncl T (F m) a ∧ JetEnclFrom T F (m + 1) as

/-- The list `l` is `k m, k (m + 1), …`. -/
@[expose] def KList : ℕ → List ℕ → Prop
  | _, [] => True
  | m, x :: xs => x = k m ∧ KList (m + 1) xs

theorem mem_frac (neg : Bool) (num den : ℕ) (hd : 0 < den) :
    IV.Mem ((if neg then -(num : ℝ) else num) / den) (frac neg num den) := by
  have := IV.mem_ofFrac (P := 128) ⟨neg, num⟩ hd
  cases neg <;> simpa [SInt.toInt_mk, frac] using this

theorem mem_frac_pos (num den : ℕ) (hd : 0 < den) : IV.Mem ((num : ℝ) / den) (frac false num den) := by
  simpa using mem_frac false num den hd

theorem mem_frac_neg (num den : ℕ) (hd : 0 < den) : IV.Mem (-(num : ℝ) / den) (frac true num den) := by
  simpa using mem_frac true num den hd

theorem mem_ofNat' (n : ℕ) : IV.Mem (n : ℝ) (IV.ofNat n : IV 128) := IV.mem_ofNat n

/-! ### Real polynomial identities -/

/-- The real coefficients of the quintic. -/
@[expose] noncomputable def sqR : List ℝ := [0, 0, 0, 10, -15, 6]

/-- The real coefficients of `P` (`h_s = 3/40`). -/
@[expose] noncomputable def pR : List ℝ := [0, 1, 0, -3200 / 3, 512000 / 27, -2560000 / 27]

/-- The real coefficients of `Q` (`h_s = 3/40`). -/
@[expose] noncomputable def qR : List ℝ := [0, 0, 1 / 2, -20, 800 / 3, -32000 / 27]

theorem squintic_eq (y : ℝ) : Squintic y = hornerR sqR y := by
  simp [Squintic, sqR, hornerR]; ring

theorem Ppoly_eq (z : ℝ) : Ppoly z = hornerR pR z := by
  simp [Ppoly, pR, hornerR, hs]; ring

theorem Qpoly_eq (z : ℝ) : Qpoly z = hornerR qR z := by
  simp [Qpoly, qR, hornerR, hs]; ring

theorem forall₂_sq : List.Forall₂ IV.Mem sqR sqCoeffs := by
  simp only [sqR, sqCoeffs, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨mem_ivZero, mem_ivZero, mem_ivZero, ?_, ?_, ?_⟩
  · simpa using mem_ofNat' 10
  · simpa using IV.mem_neg (mem_ofNat' 15)
  · simpa using mem_ofNat' 6

theorem forall₂_p : List.Forall₂ IV.Mem pR pCoeffs := by
  simp only [pR, pCoeffs, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨mem_ivZero, mem_ivOne, mem_ivZero, ?_, ?_, ?_⟩
  · simpa [neg_div] using mem_frac_neg 3200 3 (by norm_num)
  · simpa using mem_frac_pos 512000 27 (by norm_num)
  · simpa [neg_div] using mem_frac_neg 2560000 27 (by norm_num)

theorem forall₂_q : List.Forall₂ IV.Mem qR qCoeffs := by
  simp only [qR, qCoeffs, List.forall₂_cons, List.Forall₂.nil, and_true]
  refine ⟨mem_ivZero, mem_ivZero, ?_, ?_, ?_, ?_⟩
  · simpa using mem_frac_pos 1 2 (by norm_num)
  · simpa using IV.mem_neg (mem_ofNat' 20)
  · simpa using mem_frac_pos 800 3 (by norm_num)
  · simpa [neg_div] using mem_frac_neg 32000 27 (by norm_num)

/-- `hornerR` of a mapped `List.range'` is the power sum. -/
theorem hornerR_map_range' (f : ℕ → ℝ) (x : ℝ) :
    ∀ (n a : ℕ), hornerR ((List.range' a n).map f) x = ∑ j ∈ Finset.range n, f (a + j) * x ^ j
  | 0, a => by simp
  | n + 1, a => by
    rw [List.range'_succ, List.map_cons, hornerR_cons, hornerR_map_range' f x n (a + 1),
      Finset.sum_range_succ']
    simp only [pow_succ, pow_zero, add_zero, mul_one]
    rw [Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show a + 1 + j = a + (j + 1) by omega]; ring

/-- The real edge coefficients `c_i (-1)^j C(k, 2j) p^{k-2j}`, `j = 0, …, k/2`. -/
@[expose] noncomputable def edgeR (i : ℕ) : List ℝ :=
  (List.range (k i / 2 + 1)).map fun j =>
    coeff i * ((-1 : ℝ) ^ j * (Nat.choose (k i) (2 * j) : ℝ) * p ^ (k i - 2 * j))

theorem V_eq_horner (i : ℕ) (r : ℝ) : V i r = hornerR (edgeR i) (r ^ 2 - p ^ 2) := by
  rw [edgeR, List.range_eq_range', hornerR_map_range', V, Vsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [zero_add]; ring

/-! ### Validity of the constants -/

/-- The constants of mode `i ≥ 1` enclose the true ones. -/
structure ModeValid (i : ℕ) (md : ModeData) : Prop where
  k_eq : md.k = 6 * i
  sc : IV.Mem ((-1 : ℝ) ^ i * coeff i) md.sc
  t0 : IV.Mem (T0 i) md.t0
  t1 : IV.Mem (T1 i) md.t1
  t2 : IV.Mem (T2 i) md.t2
  edge : List.Forall₂ IV.Mem (edgeR i) md.edge
  vr : IV.Mem (V i R₀) md.vr
  va : IV.Mem (deriv (V i) R₀) md.va
  vb : IV.Mem (deriv (deriv (V i)) R₀) md.vb

/-- The modes `i, i + 1, …` of the list are valid. -/
@[expose] def ModesValid : ℕ → List ModeData → Prop
  | _, [] => True
  | i, md :: mds => ModeValid i md ∧ ModesValid (i + 1) mds

/-- The constants of the basis enclose the true ones (modes `1, …, 38`). -/
structure BasisData.Valid (d : BasisData) : Prop where
  mpi : IV.Mem Real.pi d.pi
  mp : IV.Mem Calibration.p d.p
  mpc : IV.Mem (Calibration.p - Calibration.c) d.pc
  mp2 : IV.Mem (Calibration.p ^ 2) d.p2
  mr0 : IV.Mem R₀ d.r0
  mr1 : IV.Mem (R₀ + 1 / 1000) d.r1
  mg0 : IV.Mem (gamma R₀) d.g0
  mg1 : IV.Mem (deriv gamma R₀) d.g1
  mg2 : IV.Mem (deriv (deriv gamma) R₀) d.g2
  modes : ModesValid 1 d.modes
  len : d.modes.length = 38

/-! ### The shared jets of a cell -/

/-- The shared jets enclose their real functions on `T`. -/
structure CtxValid (T : Set ℝ) (cx : Ctx) : Prop where
  t : JetEncl T (fun t => t) cx.t
  t6 : JetEncl T (fun t => t ^ 6) cx.t6
  h : JetEncl T (fun t => t - p) cx.h
  z : JetEncl T (fun t => t ^ 2 - p ^ 2) cx.z
  gc : JetEncl T (fun t => Squintic ((t - R₀) / (1 / 10))) cx.gc
  cu : JetEncl T (fun t => Squintic ((t - p + c) / c)) cx.cu
  tau : JetEncl T (fun t => Squintic ((t - R₀ - 1 / 1000) / hs)) cx.tau
  pr : JetEncl T (fun t => Ppoly (t - R₀)) cx.pr
  qr : JetEncl T (fun t => Qpoly (t - R₀)) cx.qr

theorem quinticJ_sound {T : Set ℝ} {F : ℝ → ℝ} {Y : IJet 128} (h : JetEncl T F Y) :
    JetEncl T (fun t => Squintic (F t)) (quinticJ Y) :=
  jetEncl_of_eq (h.cpol forall₂_sq) fun _ => (squintic_eq _).symm

theorem mkCtx_valid {d : BasisData} (hd : d.Valid) {X : IV 128} :
    CtxValid {t | IV.Mem t X} (mkCtx d X) := by
  have hv : JetEncl {t | IV.Mem t X} (fun t => t) (IJet.var X) := JetEncl.var fun t ht => ht
  refine ⟨hv, hv.pow 6, hv.subIV hd.mp, (hv.sq).subIV hd.mp2, ?_, ?_, ?_, ?_, ?_⟩
  · refine jetEncl_of_eq (quinticJ_sound ((hv.subIV hd.mr0).scale (mem_ofNat' 10))) fun t => ?_
    congr 1; push_cast; ring
  · refine jetEncl_of_eq (quinticJ_sound ((hv.subIV hd.mpc).scale (mem_frac_pos 50 3 (by norm_num))))
      fun t => ?_
    congr 1; simp only [c]; push_cast; ring
  · refine jetEncl_of_eq (quinticJ_sound ((hv.subIV hd.mr1).scale (mem_frac_pos 40 3 (by norm_num))))
      fun t => ?_
    congr 1; simp only [hs]; push_cast; ring
  · exact jetEncl_of_eq ((hv.subIV hd.mr0).cpol forall₂_p) fun t => (Ppoly_eq _).symm
  · exact jetEncl_of_eq ((hv.subIV hd.mr0).cpol forall₂_q) fun t => (Qpoly_eq _).symm

theorem gammaJ_sound {d : BasisData} (hd : d.Valid) {X : IV 128} (hX : IV.posB X = true) :
    JetEncl {t | IV.Mem t X} gamma (gammaJ d (IJet.var X)) := by
  have hv : JetEncl {t | IV.Mem t X} (fun t => t) (IJet.var X) := JetEncl.var fun t ht => ht
  have hl := hv.log hX
  have := (hl.neg).add ((hv.sq).scale (IV.mem_divPow2 hd.mpi 1))
  refine jetEncl_of_eq this fun t => ?_
  simp only [gamma]; ring

/-! ### One mode -/

section Mode

variable {T : Set ℝ} {cx : Ctx} {d : BasisData}

theorem contJ_sound (hc : CtxValid T cx) {v₀ v₁ v₂ : ℝ} {a₀ a₁ a₂ : IV 128} (h₀ : IV.Mem v₀ a₀)
    (h₁ : IV.Mem v₁ a₁) (h₂ : IV.Mem v₂ a₂) :
    JetEncl T (contPolyC v₀ v₁ v₂) (contJ cx.pr cx.qr a₀ a₁ a₂) := by
  refine jetEncl_of_eq (((hc.pr.scale h₁).add (hc.qr.scale h₂)).addIV h₀) fun t => ?_
  simp only [contPolyC]; ring

theorem modeW_sound (hc : CtxValid T cx) {i : ℕ} (hi : 1 ≤ i) {md : ModeData} (hmd : ModeValid i md)
    {tk : IJet 128} (htk : JetEncl T (fun t => t ^ (6 * i)) tk) {j : ℕ} (hj : j ≤ 6) :
    JetEncl T (Piece.w i j) (modeW cx j md tk) := by
  have hi0 : i ≠ 0 := by omega
  have hk : k i = 6 * i := k_of_pos (by omega)
  have h1 : JetEncl T (fun t => (-1 : ℝ) ^ i * coeff i * t ^ k i * 1) (IJet.scale md.sc tk) :=
    jetEncl_of_eq (htk.scale hmd.sc) fun t => by rw [hk]; ring
  have h2 : JetEncl T (fun t => (-1 : ℝ) ^ i * coeff i * t ^ k i * (1 - Squintic ((t - R₀) / (1 / 10))))
      (IJet.scale md.sc (IJet.mul tk (IJet.sub (IJet.const ivOne) cx.gc))) :=
    jetEncl_of_eq ((htk.mul ((JetEncl.const (P := 128) mem_ivOne).sub hc.gc)).scale hmd.sc) fun t => by rw [hk]; ring
  interval_cases j <;> simp only [modeW] <;> simp <;>
    first
    | exact jetEncl_of_eq h1 fun t => by simp [Piece.w, hi0]
    | exact jetEncl_of_eq h2 fun t => by simp [Piece.w, hi0]

theorem modeB_sound (hc : CtxValid T cx) {i : ℕ} (hi : 1 ≤ i) {md : ModeData} (hmd : ModeValid i md)
    {j : ℕ} (hj : j ≤ 6) : JetEncl T (Piece.b i j) (modeB cx j md) := by
  have hi0 : i ≠ 0 := by omega
  have h0 : JetEncl T (fun _ => (0 : ℝ)) (IJet.const ivZero) := JetEncl.const (P := 128) mem_ivZero
  have h1 : JetEncl T (bPoly i) (IJet.mul cx.cu (IJet.horner cx.h [md.t0, md.t1, md.t2])) := by
    refine jetEncl_of_eq (hc.cu.mul (hc.h.horner (List.Forall₂.cons hmd.t0 (List.Forall₂.cons hmd.t1
      (List.Forall₂.cons hmd.t2 List.Forall₂.nil))))) fun t => ?_
    simp only [bPoly, hornerR]; ring
  have h2 : JetEncl T (V i) (IJet.horner cx.z md.edge) :=
    jetEncl_of_eq (hc.z.horner hmd.edge) fun t => (V_eq_horner i t).symm
  have h3 : JetEncl T (contPoly (V i)) (contJ cx.pr cx.qr md.vr md.va md.vb) :=
    contJ_sound hc hmd.vr hmd.va hmd.vb
  have h5 : JetEncl T (fun _ => V i R₀) (IJet.const md.vr) := JetEncl.const hmd.vr
  interval_cases j <;> simp only [modeB] <;> simp <;>
    first
    | exact jetEncl_of_eq h0 fun t => by simp [Piece.b, hi0]
    | exact jetEncl_of_eq h1 fun t => by simp [Piece.b, hi0]
    | exact jetEncl_of_eq h2 fun t => by simp [Piece.b, hi0]
    | exact jetEncl_of_eq h3 fun t => by simp [Piece.b, hi0]
    | exact jetEncl_of_eq h5 fun t => by simp [Piece.b, hi0]

/-- The mixing of `w` and `b` by `τ` into `u` and `D`. -/
theorem mix_sound (hc : CtxValid T cx) {W Bf : ℝ → ℝ} {w b : IJet 128} (hw : JetEncl T W w)
    (hb : JetEncl T Bf b) {j : ℕ} (hj : j ≤ 6) :
    JetEncl T (fun t => (1 - Piece.tau j t) * W t + Piece.tau j t * Bf t) (mixU cx j w b) ∧
      JetEncl T (fun t => Bf t - ((1 - Piece.tau j t) * W t + Piece.tau j t * Bf t)) (mixD cx j w b) := by
  have hmidU : JetEncl T (fun t => W t + Squintic ((t - R₀ - 1 / 1000) / hs) * (Bf t - W t))
      (IJet.add w (IJet.mul cx.tau (IJet.sub b w))) := hw.add (hc.tau.mul (hb.sub hw))
  have hmidD : JetEncl T (fun t => (1 - Squintic ((t - R₀ - 1 / 1000) / hs)) * (Bf t - W t))
      (IJet.mul (IJet.sub (IJet.const ivOne) cx.tau) (IJet.sub b w)) :=
    ((JetEncl.const (P := 128) mem_ivOne).sub hc.tau).mul (hb.sub hw)
  have hz : JetEncl T (fun _ => (0 : ℝ)) (IJet.const ivZero) := JetEncl.const (P := 128) mem_ivZero
  interval_cases j <;> simp only [mixU, mixD] <;> simp <;> refine ⟨?_, ?_⟩ <;>
    first
    | exact jetEncl_of_eq hw fun t => by simp [Piece.tau]
    | exact jetEncl_of_eq (hb.sub hw) fun t => by simp [Piece.tau]
    | exact jetEncl_of_eq hmidU fun t => by simp [Piece.tau]; ring
    | exact jetEncl_of_eq hmidD fun t => by simp [Piece.tau]; ring
    | exact jetEncl_of_eq hb fun t => by simp [Piece.tau]
    | exact jetEncl_of_eq hz fun t => by simp [Piece.tau]

theorem mode_sound (hc : CtxValid T cx) {i : ℕ} (hi : 1 ≤ i) {md : ModeData} (hmd : ModeValid i md)
    {tk : IJet 128} (htk : JetEncl T (fun t => t ^ (6 * i)) tk) {j : ℕ} (hj : j ≤ 6) :
    JetEncl T (Piece.u i j) (mixU cx j (modeW cx j md tk) (modeB cx j md)) ∧
      JetEncl T (Piece.D i j) (mixD cx j (modeW cx j md tk) (modeB cx j md)) := by
  obtain ⟨hu, hD⟩ := mix_sound hc (modeW_sound hc hi hmd htk hj) (modeB_sound hc hi hmd hj) hj
  exact ⟨jetEncl_of_eq hu fun t => rfl, jetEncl_of_eq hD fun t => rfl⟩

theorem modeB0_sound (hd : d.Valid) (hc : CtxValid T cx) {g : IJet 128} (hg : JetEncl T gamma g)
    {j : ℕ} (hj : j ≤ 6) : JetEncl T (Piece.b 0 j) (modeB0 d cx j g) := by
  have h3 : JetEncl T (contPoly gamma) (contJ cx.pr cx.qr d.g0 d.g1 d.g2) := contJ_sound hc hd.mg0 hd.mg1 hd.mg2
  have h5 : JetEncl T (fun _ => gamma R₀) (IJet.const d.g0) := JetEncl.const hd.mg0
  interval_cases j <;> simp only [modeB0] <;> simp <;>
    first
    | exact jetEncl_of_eq hg fun t => by simp [Piece.b]
    | exact jetEncl_of_eq h3 fun t => by simp [Piece.b]
    | exact jetEncl_of_eq h5 fun t => by simp [Piece.b]

theorem mode0_sound (hd : d.Valid) (hc : CtxValid T cx) {g : IJet 128} (hg : JetEncl T gamma g)
    {j : ℕ} (hj : j ≤ 6) :
    JetEncl T (Piece.u 0 j) (modeU0 d cx j g) ∧ JetEncl T (Piece.D 0 j) (modeD0 d cx j g) := by
  have hw : JetEncl T (Piece.w 0 j) g := jetEncl_of_eq hg fun t => by simp [Piece.w]
  obtain ⟨hu, hD⟩ := mix_sound hc hw (modeB0_sound hd hc hg hj) hj
  have hu' : JetEncl T (Piece.u 0 j) (mixU cx j g (modeB0 d cx j g)) := jetEncl_of_eq hu fun t => rfl
  have hD' : JetEncl T (Piece.D 0 j) (mixD cx j g (modeB0 d cx j g)) := jetEncl_of_eq hD fun t => rfl
  have hz : JetEncl T (fun _ => (0 : ℝ)) (IJet.const ivZero) := JetEncl.const (P := 128) mem_ivZero
  rcases Nat.lt_or_ge j 3 with hj3 | hj3
  · have hb : Nat.ble j 2 = true := Nat.ble_eq_true_of_le (by omega)
    simp only [modeU0, modeD0, hb, Bool.cond_true]
    have hτ : ∀ t, Piece.tau j t = 0 := fun t => by interval_cases j <;> simp [Piece.tau]
    have hb0 : ∀ t, Piece.b 0 j t = gamma t := fun t => by interval_cases j <;> simp [Piece.b]
    refine ⟨jetEncl_of_eq hg fun t => ?_, jetEncl_of_eq hz fun t => ?_⟩
    · simp [Piece.u, Piece.w, hτ, hb0]
    · simp [Piece.D, Piece.u, Piece.w, hτ, hb0]
  · have hb : Nat.ble j 2 = false := by
      cases h : Nat.ble j 2
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) (by omega)
    simp only [modeU0, modeD0, hb, Bool.cond_false]
    exact ⟨hu', hD'⟩

end Mode

/-! ### All modes -/

section Loops

variable {T : Set ℝ} {cx : Ctx}

theorem uLoop_sound (hc : CtxValid T cx) {j : ℕ} (hj : j ≤ 6) :
    ∀ (mds : List ModeData) (i : ℕ) (tk acc : IJet 128) (A : ℝ → ℝ), 1 ≤ i → ModesValid i mds →
      JetEncl T (fun t => t ^ (6 * i)) tk → JetEncl T A acc →
      JetEncl T (fun t => A t + ∑ n ∈ Finset.range mds.length, Piece.u (i + n) j t) (uLoop cx j mds tk acc)
  | [], i, tk, acc, A, _, _, _, hA => jetEncl_of_eq hA fun t => by simp
  | md :: mds, i, tk, acc, A, hi, ⟨hmd, hmds⟩, htk, hA => by
    have htk' : JetEncl T (fun t => t ^ (6 * (i + 1))) (IJet.mul tk cx.t6) :=
      jetEncl_of_eq (htk.mul hc.t6) fun t => by ring
    have hacc := hA.add (mode_sound hc hi hmd htk hj).1
    have := uLoop_sound hc hj mds (i + 1) _ _ _ (by omega) hmds htk' hacc
    refine jetEncl_of_eq this fun t => ?_
    simp only [List.length_cons, Finset.sum_range_succ', add_zero]
    simp only [show ∀ n, i + 1 + n = i + (n + 1) from fun n => by omega]
    ring

theorem dsLoop_sound (hc : CtxValid T cx) {j : ℕ} (hj : j ≤ 6) :
    ∀ (mds : List ModeData) (i : ℕ) (tk : IJet 128), 1 ≤ i → ModesValid i mds →
      JetEncl T (fun t => t ^ (6 * i)) tk → JetEnclFrom T (fun n => Piece.D n j) i (dsLoop cx j mds tk)
  | [], _, _, _, _, _ => trivial
  | md :: mds, i, tk, hi, ⟨hmd, hmds⟩, htk => by
    have htk' : JetEncl T (fun t => t ^ (6 * (i + 1))) (IJet.mul tk cx.t6) :=
      jetEncl_of_eq (htk.mul hc.t6) fun t => by ring
    exact ⟨(mode_sound hc hi hmd htk hj).2, dsLoop_sound hc hj mds (i + 1) _ (by omega) hmds htk'⟩

theorem ksOf_klist : ∀ (mds : List ModeData) (i : ℕ), 1 ≤ i → ModesValid i mds → KList i (ksOf mds)
  | [], _, _, _ => trivial
  | md :: mds, i, hi, ⟨hmd, hmds⟩ => ⟨by rw [hmd.k_eq, k_of_pos (by omega)], ksOf_klist mds (i + 1)
      (by omega) hmds⟩

end Loops

/-- **Soundness of the basis.** If the constants are valid and the cell `X` is positive, then on
`T = {t | t ∈ X}` and for every segment `j ≤ 6`, `bsum` encloses the jet of `B̃ = ∑_{i ≤ 38} Piece.u i j`, `ds`
the jets of `Piece.D 0 j, …, Piece.D 38 j`, and `ks = [k 0, …, k 38]`. -/
theorem basis_sound {d : BasisData} (hd : d.Valid) {X : IV 128} (hX : IV.posB X = true) {j : ℕ}
    (hj : j ≤ 6) :
    JetEncl {t | IV.Mem t X} (fun t => ∑ i ∈ Finset.range 39, Piece.u i j t) (basis d j X).bsum ∧
      JetEnclFrom {t | IV.Mem t X} (fun n => Piece.D n j) 0 (basis d j X).ds ∧
      KList 0 (basis d j X).ks := by
  have hc := mkCtx_valid hd (X := X)
  have hg := gammaJ_sound hd hX
  obtain ⟨hu0, hD0⟩ := mode0_sound hd hc hg hj
  have ht6 : JetEncl {t | IV.Mem t X} (fun t => t ^ (6 * 1)) (mkCtx d X).t6 :=
    jetEncl_of_eq hc.t6 fun t => by ring
  refine ⟨?_, ⟨hD0, dsLoop_sound hc hj d.modes 1 _ le_rfl hd.modes ht6⟩,
    ⟨by simp [k], ksOf_klist d.modes 1 le_rfl hd.modes⟩⟩
  have := uLoop_sound hc hj d.modes 1 _ _ _ le_rfl hd.modes ht6 hu0
  rw [hd.len] at this
  refine jetEncl_of_eq this fun t => ?_
  rw [Finset.sum_range_succ' (fun i => Piece.u i j t) 38]
  simp only [add_comm 1]
  ring

end SandierSerfaty.Certificate.Basis
