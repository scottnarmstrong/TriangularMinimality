/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Basis.Data
public import SandierSerfaty.Certificate.Basis.Sound
public import SandierSerfaty.Certificate.Basis.Deriv
public import SandierSerfaty.Certificate.Basis.CoeffSound

/-!
# Validity of the computed basis constants

* `mkData_valid`: if `piI ∋ π`, the list `cos` encloses `c_1, …, c_38` (assertion A1, `EnclFrom coeff 1 cos`)
  and `dataOK pI rI cos = true`, then `mkData piI pI rI cos` is valid (`BasisData.Valid`);
* `BasisData.Valid.of_subB`: validity passes to literal constants that contain the computed ones
  (`dataSubB`), so that the certificate shards read literal constants and the computation is checked once.

Ingredients: `fourthRootOK_sound` (`p⁴ = 1/12`, `R₀⁴ = 4/27`), the binomial recurrence `choose2Step_eq`, the
edge coefficients `edgeAux_sound`, and the derivatives of `γ` and `V_i` at `R₀` read off their jets on the
nondegenerate cell of `R₀` (`jetEncl_deriv`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Basis

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Calibration

/-! ### Fourth roots -/

-- The proof manipulates the literal `2 ^ 512`; allow its evaluation (no warning, same proof).
set_option exponentiation.threshold 600 in
theorem fourthRootOK_sound {num den : ℕ} (hden : 0 < den) {a : IV 128} (h : fourthRootOK num den a = true)
    {x : ℝ} (hx : 0 ≤ x) (hx4 : x ^ 4 = (num : ℝ) / den) : IV.Mem x a := by
  simp only [fourthRootOK, Bool.and_eq_true, Nat.ble_eq, Nat.mul_eq, Nat.pow_eq, SInt.nat_shiftLeft_eq,
    one_mul] at h
  obtain ⟨⟨hl, hh⟩, h1, h2⟩ := h
  have hlo : a.lo.isNeg = false := by cases hc : a.lo.isNeg <;> simp_all [-Nat.reducePow]
  have hhi : a.hi.isNeg = false := by cases hc : a.hi.isNeg <;> simp_all [-Nat.reducePow]
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have hd : (0 : ℝ) < den := by exact_mod_cast hden
  have e512 : ((2 : ℝ) ^ 128) ^ 4 = 2 ^ 512 := by rw [← pow_mul]
  have eX : (x * 2 ^ 128) ^ 4 = (num : ℝ) * 2 ^ 512 / den := by
    rw [mul_pow, hx4, e512, div_mul_eq_mul_div]
  have hX : 0 ≤ x * 2 ^ 128 := by positivity
  have elo : ((a.lo.toInt : ℤ) : ℝ) = a.lo.mag := by rw [SInt.toInt_eq, hlo]; simp
  have ehi : ((a.hi.toInt : ℤ) : ℝ) = a.hi.mag := by rw [SInt.toInt_eq, hhi]; simp
  have h1' : (den : ℝ) * (a.lo.mag : ℝ) ^ 4 ≤ (num : ℝ) * 2 ^ 512 := by exact_mod_cast h1
  have h2' : (num : ℝ) * 2 ^ 512 ≤ (den : ℝ) * (a.hi.mag : ℝ) ^ 4 := by exact_mod_cast h2
  refine ⟨?_, ?_⟩
  · rw [elo]
    refine (pow_le_pow_iff_left₀ (by positivity) hX (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
    rw [eX, le_div_iff₀ hd]; linarith
  · rw [ehi]
    refine (pow_le_pow_iff_left₀ hX (by positivity) (by norm_num : (4 : ℕ) ≠ 0)).mp ?_
    rw [eX, div_le_iff₀ hd]; linarith

/-! ### Binomials and edge coefficients -/

theorem choose2Step_eq (k j : ℕ) : choose2Step (Nat.choose k (2 * j)) k j = Nat.choose k (2 * (j + 1)) := by
  have e1 := Nat.choose_succ_right_eq k (2 * j)
  have e2 := Nat.choose_succ_right_eq k (2 * j + 1)
  have key : Nat.choose k (2 * j) * (k - 2 * j) * (k - (2 * j + 1)) =
      Nat.choose k (2 * (j + 1)) * ((2 * j + 1) * (2 * j + 2)) := by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]
    calc Nat.choose k (2 * j) * (k - 2 * j) * (k - (2 * j + 1))
        = Nat.choose k (2 * j + 1) * (2 * j + 1) * (k - (2 * j + 1)) := by rw [← e1]
      _ = (Nat.choose k (2 * j + 1) * (k - (2 * j + 1))) * (2 * j + 1) := by ring
      _ = (Nat.choose k (2 * j + 1 + 1) * (2 * j + 1 + 1)) * (2 * j + 1) := by rw [e2]
      _ = Nat.choose k (2 * j + 1 + 1) * ((2 * j + 1) * (2 * j + 2)) := by ring
  simp only [choose2Step, Nat.mul_eq, Nat.add_eq, Nat.sub_eq, SInt.nat_div_eq]
  rw [key, Nat.mul_div_cancel _ (by positivity)]

theorem mem_sgnIV {y : ℝ} {x : IV 128} (h : IV.Mem y x) (j : ℕ) : IV.Mem ((-1 : ℝ) ^ j * y) (sgnIV j x) := by
  unfold sgnIV
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have hb : Nat.beq (Nat.mod j 2) 1 = false := by
      rw [show Nat.mod j 2 = j % 2 from rfl, hj]; rfl
    rw [hb, Bool.cond_false, (Nat.even_iff.mpr hj).neg_one_pow, one_mul]
    exact h
  · have hb : Nat.beq (Nat.mod j 2) 1 = true := by
      rw [show Nat.mod j 2 = j % 2 from rfl, hj]; rfl
    rw [hb, Bool.cond_true, (Nat.odd_iff.mpr hj).neg_one_pow, neg_one_mul]
    exact IV.mem_neg h

theorem edgeAux_sound {c p' : ℝ} {co pI : IV 128} (hc : IV.Mem c co) (hp : IV.Mem p' pI) (k : ℕ) :
    ∀ (cnt j : ℕ), List.Forall₂ IV.Mem
      ((List.range' j cnt).map fun j => c * ((-1 : ℝ) ^ j * (Nat.choose k (2 * j) : ℝ) * p' ^ (k - 2 * j)))
      (edgeAux co pI k j (Nat.choose k (2 * j)) cnt)
  | 0, _ => List.Forall₂.nil
  | cnt + 1, j => by
    rw [List.range'_succ, List.map_cons]
    refine List.Forall₂.cons ?_ ?_
    · have := IV.mem_mul hc (mem_sgnIV (IV.mem_mul (IV.mem_ofNat (Nat.choose k (2 * j)))
        (mem_ivPow hp (Nat.sub k (Nat.mul 2 j)))) j)
      exact mem_of_eq this (by simp only [Nat.sub_eq, Nat.mul_eq]; ring)
    · have := edgeAux_sound hc hp k cnt (j + 1)
      rw [← choose2Step_eq] at this
      exact this

theorem edgeList_sound {i : ℕ} (hi : 1 ≤ i) {co pI : IV 128} (hc : IV.Mem (coeff i) co)
    (hp : IV.Mem p pI) : List.Forall₂ IV.Mem (edgeR i) (edgeList co pI (Nat.mul 6 i)) := by
  have hk : k i = 6 * i := k_of_pos (by omega)
  have := edgeAux_sound hc hp (6 * i) (6 * i / 2 + 1) 0
  rw [edgeR, hk, List.range_eq_range']
  simpa [edgeList, Nat.choose_zero_right, SInt.nat_div_eq] using this

/-! ### The modes -/

theorem mkMode_valid {pI rI : IV 128} (hp : IV.Mem p pI) (hr : IV.Mem R₀ rI) (hpos : IV.posB pI = true)
    (hp2pos : IV.posB (IV.sq pI) = true) (hlt : SInt.blt rI.lo rI.hi = true) {i : ℕ} (hi : 1 ≤ i)
    {co : IV 128} (hc : IV.Mem (coeff i) co) : ModeValid i (mkMode pI (IV.sq pI) rI co i) := by
  have hk : k i = 6 * i := k_of_pos (by omega)
  have hk6 : 6 ≤ 6 * i := by omega
  have hp2 : IV.Mem (p ^ 2) (IV.sq pI) := IV.mem_sq hp
  have hedge := edgeList_sound hi hc hp
  have ht0 : IV.Mem (T0 i) (IV.mul co (ivPow pI (6 * i))) := by
    have := IV.mem_mul hc (mem_ivPow hp (6 * i))
    simpa [T0, hk] using this
  -- the jet of the edge polynomial on the cell of `R₀`
  have hv : JetEncl {t | IV.Mem t rI} (fun t => t) (IJet.var rI) := JetEncl.var fun t ht => ht
  have hVJ : JetEncl {t | IV.Mem t rI} (V i) (IJet.horner (zAt (IV.sq pI) rI) (edgeList co pI (Nat.mul 6 i))) :=
    jetEncl_of_eq ((hv.sq.subIV hp2).horner hedge) fun t => (V_eq_horner i t).symm
  obtain ⟨v0, v1, v2⟩ := jetEncl_deriv hlt isOpen_univ (fun _ _ => mem_univ _)
    ((contDiff_V i).contDiffOn.of_le (by norm_cast)) hVJ hr
  have hpp : 0 < p := p_pos
  have hkR : ((Nat.mul (6 * i) (Nat.sub (6 * i) 1) : ℕ) : ℝ) = (k i : ℝ) * ((k i : ℝ) - 1) := by
    rw [hk]; simp only [Nat.mul_eq, Nat.sub_eq]; push_cast [show 1 ≤ 6 * i by omega]; ring
  have hN2 : ((Nat.mul (Nat.mul (6 * i) (Nat.sub (6 * i) 1))
      (Nat.sub (Nat.mul (Nat.sub (6 * i) 2) (Nat.sub (6 * i) 3)) 3) : ℕ) : ℝ) =
      (k i : ℝ) * ((k i : ℝ) - 1) * (((k i : ℝ) - 2) * ((k i : ℝ) - 3) - 3) := by
    have h3 : 3 ≤ (6 * i - 2) * (6 * i - 3) := by
      have : 4 ≤ 6 * i - 2 := by omega
      have : 3 ≤ 6 * i - 3 := by omega
      nlinarith
    rw [hk]; simp only [Nat.mul_eq, Nat.sub_eq]
    push_cast [show 1 ≤ 6 * i by omega, show 2 ≤ 6 * i by omega, show 3 ≤ 6 * i by omega, h3]
    ring
  refine ⟨rfl, ?_, ht0, ?_, ?_, hedge, v0, v1, ?_⟩
  · exact mem_sgnIV hc i
  · have := IV.mem_neg (IV.mem_divPos hpos (IV.mem_mulNat ht0 (Nat.mul (6 * i) (Nat.sub (6 * i) 1))) hp)
    refine mem_of_eq this ?_
    rw [hkR, T1]; field_simp
  · have := IV.mem_divPos hp2pos (IV.mem_divNat (IV.mem_mulNat ht0 (Nat.mul (Nat.mul (6 * i) (Nat.sub (6 * i) 1))
      (Nat.sub (Nat.mul (Nat.sub (6 * i) 2) (Nat.sub (6 * i) 3)) 3))) (by norm_num : 0 < 6)) hp2
    refine mem_of_eq this ?_
    rw [hN2, T2]; field_simp; ring
  · have := IV.mem_mulNat v2 2
    exact mem_of_eq this (by push_cast; ring)

theorem modesFrom_valid {pI rI : IV 128} (hp : IV.Mem p pI) (hr : IV.Mem R₀ rI) (hpos : IV.posB pI = true)
    (hp2pos : IV.posB (IV.sq pI) = true) (hlt : SInt.blt rI.lo rI.hi = true) :
    ∀ (cos : List (IV 128)) (i : ℕ), 1 ≤ i → EnclFrom coeff i cos →
      ModesValid i (modesFrom pI (IV.sq pI) rI i cos)
  | [], _, _, _ => trivial
  | co :: cos, i, hi, ⟨hc, hcs⟩ =>
    ⟨mkMode_valid hp hr hpos hp2pos hlt hi hc, modesFrom_valid hp hr hpos hp2pos hlt cos (i + 1) (by omega) hcs⟩

theorem modesFrom_length (pI p2 rI : IV 128) : ∀ (cos : List (IV 128)) (i : ℕ),
    (modesFrom pI p2 rI i cos).length = cos.length
  | [], _ => rfl
  | _ :: cos, i => by simp [modesFrom, modesFrom_length pI p2 rI cos]

/-! ### The data -/

theorem deriv_gamma_mem {piI rI : IV 128} (hpi : IV.Mem Real.pi piI) (hr : IV.Mem R₀ rI)
    (hpos : IV.posB rI = true) (hlt : SInt.blt rI.lo rI.hi = true) :
    IV.Mem (gamma R₀) (gammaPi piI (IJet.var rI)).c0 ∧ IV.Mem (deriv gamma R₀) (gammaPi piI (IJet.var rI)).c1 ∧
      IV.Mem (deriv (deriv gamma) R₀) (IV.mulNat (gammaPi piI (IJet.var rI)).c2 2) := by
  have hv : JetEncl {t | IV.Mem t rI} (fun t => t) (IJet.var rI) := JetEncl.var fun t ht => ht
  have hg : JetEncl {t | IV.Mem t rI} gamma (gammaPi piI (IJet.var rI)) := by
    have := (hv.log hpos).neg.add ((hv.sq).scale (IV.mem_divPow2 hpi 1))
    refine jetEncl_of_eq this fun t => ?_
    simp only [gamma]; ring
  obtain ⟨g0, g1, g2⟩ := jetEncl_deriv hlt isOpen_Ioi (fun t ht => IV.posB_sound hpos ht)
    (contDiffOn_gamma.of_le (by norm_cast)) hg hr
  exact ⟨g0, g1, mem_of_eq (IV.mem_mulNat g2 2) (by push_cast; ring)⟩

/-- **Validity of the computed basis constants.** -/
theorem mkData_valid {piI pI rI : IV 128} {cos : List (IV 128)} (hpi : IV.Mem Real.pi piI)
    (hco : EnclFrom coeff 1 cos) (hok : dataOK pI rI cos = true) : (mkData piI pI rI cos).Valid := by
  simp only [dataOK, Bool.and_eq_true, Nat.beq_eq] at hok
  obtain ⟨⟨hp4, hr4⟩, ⟨hrpos, hlt⟩, ⟨hppos, hp2pos⟩, hlen⟩ := hok
  have hp : IV.Mem p pI :=
    fourthRootOK_sound (by norm_num) hp4 p_pos.le (by rw [p_pow_four]; norm_num)
  have hr : IV.Mem R₀ rI :=
    fourthRootOK_sound (by norm_num) hr4 R₀_pos.le (by rw [R₀_pow_four]; norm_num)
  obtain ⟨g0, g1, g2⟩ := deriv_gamma_mem hpi hr hrpos hlt
  refine ⟨hpi, hp, ?_, IV.mem_sq hp, hr, ?_, g0, g1, g2, ?_, ?_⟩
  · exact IV.mem_sub hp (by simpa [c] using mem_frac_pos 3 50 (by norm_num))
  · exact IV.mem_add hr (by simpa using mem_frac_pos 1 1000 (by norm_num))
  · exact modesFrom_valid hp hr hppos hp2pos hlt cos 1 le_rfl hco
  · show (modesFrom pI (IV.sq pI) rI 1 cos).length = 38
    rw [modesFrom_length, hlen]

/-! ### Transfer to literal constants -/

theorem forall₂_of_subList : ∀ {rs : List ℝ} {as bs : List (IV 128)}, List.Forall₂ IV.Mem rs as →
    subList as bs = true → List.Forall₂ IV.Mem rs bs
  | [], [], [], _, _ => List.Forall₂.nil
  | _, [], _ :: _, _, h => by simp [subList] at h
  | _, _ :: _, [], _, h => by simp [subList] at h
  | r :: rs, a :: as, b :: bs, List.Forall₂.cons hr hrs, h => by
    simp only [subList, Bool.and_eq_true] at h
    exact List.Forall₂.cons (IV.mem_of_subsetB h.1 hr) (forall₂_of_subList hrs h.2)

theorem ModeValid.of_subB {i : ℕ} {a b : ModeData} (ha : ModeValid i a) (h : modeSubB a b = true) :
    ModeValid i b := by
  simp only [modeSubB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨hk, hsc⟩, ht0, ht1⟩, ⟨ht2, hed⟩, hvr, hva, hvb⟩ := h
  exact ⟨hk ▸ ha.k_eq, IV.mem_of_subsetB hsc ha.sc, IV.mem_of_subsetB ht0 ha.t0, IV.mem_of_subsetB ht1 ha.t1,
    IV.mem_of_subsetB ht2 ha.t2, forall₂_of_subList ha.edge hed, IV.mem_of_subsetB hvr ha.vr,
    IV.mem_of_subsetB hva ha.va, IV.mem_of_subsetB hvb ha.vb⟩

theorem ModesValid.of_subB : ∀ {i : ℕ} {as bs : List ModeData}, ModesValid i as → modesSubB as bs = true →
    ModesValid i bs ∧ bs.length = as.length
  | _, [], [], _, _ => ⟨trivial, rfl⟩
  | _, [], _ :: _, _, h => by simp [modesSubB] at h
  | _, _ :: _, [], _, h => by simp [modesSubB] at h
  | i, a :: as, b :: bs, ⟨ha, has⟩, h => by
    simp only [modesSubB, Bool.and_eq_true] at h
    obtain ⟨hv, hl⟩ := ModesValid.of_subB has h.2
    exact ⟨⟨ha.of_subB h.1, hv⟩, by simp [hl]⟩

/-- Validity passes to literal constants containing valid computed ones. -/
theorem BasisData.Valid.of_subB {a b : BasisData} (ha : a.Valid) (h : dataSubB a b = true) : b.Valid := by
  simp only [dataSubB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hpi, hp⟩, hpc, hp2⟩, ⟨⟨hr0, hr1⟩, hg0, hg1⟩, hg2, hm⟩ := h
  obtain ⟨hv, hl⟩ := ModesValid.of_subB ha.modes hm
  exact ⟨IV.mem_of_subsetB hpi ha.mpi, IV.mem_of_subsetB hp ha.mp, IV.mem_of_subsetB hpc ha.mpc,
    IV.mem_of_subsetB hp2 ha.mp2, IV.mem_of_subsetB hr0 ha.mr0, IV.mem_of_subsetB hr1 ha.mr1,
    IV.mem_of_subsetB hg0 ha.mg0, IV.mem_of_subsetB hg1 ha.mg1, IV.mem_of_subsetB hg2 ha.mg2, hv,
    hl.trans ha.len⟩

end SandierSerfaty.Certificate.Basis
