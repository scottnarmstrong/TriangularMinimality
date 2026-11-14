/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.ChartBox
public import SandierSerfaty.Screening.MassCuts

/-!
# The filler partition (screening note, Lemma 4.21)

The screening note, Lemma 4.21 (`lem:fillpart`). Let `P` be a rectangle
(`Rect`, any orthogonal frame) of sides `w` (along `u`) and `h` (along `v`), `μ` measurable on `P` with
`m/2 ≤ μ ≤ 3m/2` a.e., `∫_P μ = n ∈ ℕ`, `w√m ≥ 2` and `h√m ≥ 2`. Then `P` is the union of `n` closed
sub-rectangles (same frame) with pairwise disjoint interiors, each of `μ`-mass `1`, with sides along `u`
in `[1/(6√m), 6/√m]` and along `v` in `[1/(3√m), 4/√m]` (`exists_fillerPartition`, output
`IsFillerPartition`).

Construction (as in the screening note, with the simplest row split): `n_r = ⌊w√m⌋`, `K' = ⌊n/n_r⌋` rows of
masses `n_r, …, n_r, n - (K' - 1) n_r ∈ [n_r, 2n_r)`, cut where the cumulative mass of the rows reaches
`n_r, 2n_r, …` (`exists_mass_cuts`); each row is cut where its cumulative mass reaches `1, 2, …`.

Supporting lemmas on boxes of a rectangle: `Rect.setIntegral_box_add_left/right` (additivity) and
`Rect.setIntegral_box_bounds` (the density bounds integrated over a box).
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty.Screening

namespace Rect

variable (P : Rect) {μ : ℂ → ℝ}

theorem setIntegral_box_add_left {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) {J : Set ℝ}
    (hJ : MeasurableSet J) (hμ : IntegrableOn μ (P.box (Icc x z) J)) :
    ∫ p in P.box (Icc x z) J, μ p = (∫ p in P.box (Icc x y) J, μ p) + ∫ p in P.box (Icc y z) J, μ p := by
  have hsub1 : P.box (Icc x y) J ⊆ P.box (Icc x z) J := box_mono (Icc_subset_Icc le_rfl hyz) subset_rfl
  have hsub2 : P.box (Icc y z) J ⊆ P.box (Icc x z) J := box_mono (Icc_subset_Icc hxy le_rfl) subset_rfl
  have hdisj : AEDisjoint volume (P.box (Icc x y) J) (P.box (Icc y z) J) := by
    refine measure_mono_null ?_ (P.volume_box_singleton_left y J)
    rw [box_inter, inter_self]
    refine box_mono ?_ subset_rfl
    rintro r ⟨⟨_, h1⟩, h2, _⟩
    exact le_antisymm h1 h2
  rw [← setIntegral_union₀ hdisj (measurableSet_box measurableSet_Icc hJ).nullMeasurableSet
    (hμ.mono_set hsub1) (hμ.mono_set hsub2), ← box_union_left, Icc_union_Icc_eq_Icc hxy hyz]

theorem setIntegral_box_add_right {I : Set ℝ} (hI : MeasurableSet I) {x y z : ℝ} (hxy : x ≤ y)
    (hyz : y ≤ z) (hμ : IntegrableOn μ (P.box I (Icc x z))) :
    ∫ p in P.box I (Icc x z), μ p = (∫ p in P.box I (Icc x y), μ p) + ∫ p in P.box I (Icc y z), μ p := by
  have hsub1 : P.box I (Icc x y) ⊆ P.box I (Icc x z) := box_mono subset_rfl (Icc_subset_Icc le_rfl hyz)
  have hsub2 : P.box I (Icc y z) ⊆ P.box I (Icc x z) := box_mono subset_rfl (Icc_subset_Icc hxy le_rfl)
  have hdisj : AEDisjoint volume (P.box I (Icc x y)) (P.box I (Icc y z)) := by
    refine measure_mono_null ?_ (P.volume_box_singleton_right I y)
    rw [box_inter, inter_self]
    refine box_mono subset_rfl ?_
    rintro r ⟨⟨_, h1⟩, h2, _⟩
    exact le_antisymm h1 h2
  rw [← setIntegral_union₀ hdisj (measurableSet_box hI measurableSet_Icc).nullMeasurableSet
    (hμ.mono_set hsub1) (hμ.mono_set hsub2), ← box_union_right, Icc_union_Icc_eq_Icc hxy hyz]

theorem volume_real_box_Icc {x y v v' : ℝ} (hxy : x ≤ y) (hvv' : v ≤ v') :
    volume.real (P.box (Icc x y) (Icc v v')) = (y - x) * (v' - v) := by
  rw [volume_real_box, Real.volume_real_Icc, Real.volume_real_Icc, max_eq_left (by linarith),
    max_eq_left (by linarith)]

/-- The density bounds integrated over a box. -/
theorem setIntegral_box_bounds {x y v v' lo hi : ℝ} (hxy : x ≤ y) (hvv' : v ≤ v')
    (hμi : IntegrableOn μ (P.box (Icc x y) (Icc v v')))
    (hμ : ∀ᵐ p, p ∈ P.box (Icc x y) (Icc v v') → μ p ∈ Icc lo hi) :
    lo * ((y - x) * (v' - v)) ≤ ∫ p in P.box (Icc x y) (Icc v v'), μ p ∧
      ∫ p in P.box (Icc x y) (Icc v v'), μ p ≤ hi * ((y - x) * (v' - v)) := by
  have hS := measurableSet_box (H := P) (measurableSet_Icc (a := x) (b := y))
    (measurableSet_Icc (a := v) (b := v'))
  have hae : ∀ᵐ p ∂(volume.restrict (P.box (Icc x y) (Icc v v'))), μ p ∈ Icc lo hi :=
    (ae_restrict_iff' hS).2 hμ
  have hfin : volume (P.box (Icc x y) (Icc v v')) ≠ ⊤ := by
    rw [volume_box_Icc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hc : ∀ c : ℝ, ∫ _p in P.box (Icc x y) (Icc v v'), c = c * ((y - x) * (v' - v)) := by
    intro c
    rw [setIntegral_const, P.volume_real_box_Icc hxy hvv', smul_eq_mul, mul_comm]
  constructor
  · rw [← hc]
    exact setIntegral_mono_ae_restrict (integrableOn_const hfin) hμi
      (hae.mono fun p hp => hp.1)
  · rw [← hc]
    exact setIntegral_mono_ae_restrict hμi (integrableOn_const hfin) (hae.mono fun p hp => hp.2)

end Rect

/-- **Output of the filler partition** (screening note, Lemma 4.21): `n` sub-rectangles `piece p`, `p ∈ I`, of
`P` (same frame), of `μ`-mass `1`, with sides in `[1/(6√m), 6/√m] × [1/(3√m), 4/√m]`, pairwise null
intersections and disjoint interiors, covering `P`. -/
structure IsFillerPartition (P : Rect) (μ : ℂ → ℝ) (m : ℝ) (n : ℕ) (I : Finset (ℕ × ℕ))
    (piece : ℕ × ℕ → Rect) : Prop where
  card : I.card = n
  sub : ∀ p ∈ I, ∃ a b, piece p = P.sub a b (piece p).width (piece p).height ∧ 0 ≤ a ∧
    a + (piece p).width ≤ P.width ∧ 0 ≤ b ∧ b + (piece p).height ≤ P.height
  mass : ∀ p ∈ I, ∫ x in (piece p).carrier, μ x = 1
  width_mem : ∀ p ∈ I, (piece p).width ∈ Icc (1 / (6 * √m)) (6 / √m)
  height_mem : ∀ p ∈ I, (piece p).height ∈ Icc (1 / (3 * √m)) (4 / √m)
  null_inter : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → volume ((piece p).carrier ∩ (piece q).carrier) = 0
  disjoint_open : ∀ p ∈ I, ∀ q ∈ I, p ≠ q → Disjoint (piece p).openCarrier (piece q).openCarrier
  cover : ⋃ p ∈ I, (piece p).carrier = P.carrier

/-- The size bounds of the pieces (pure arithmetic, `s = √m`). -/
theorem filler_size_bounds {s w β α nr nrow : ℝ} (hs : 0 < s) (hw : 0 < w) (hβ : 0 < β)
    (hnr : w * s / 2 ≤ nr) (hnrow1 : nr ≤ nrow) (hnrow2 : nrow ≤ 2 * (w * s))
    (hrow1 : s ^ 2 / 2 * w * β ≤ nrow) (hrow2 : nrow ≤ 3 * s ^ 2 / 2 * w * β)
    (hp1 : s ^ 2 / 2 * β * α ≤ 1) (hp2 : 1 ≤ 3 * s ^ 2 / 2 * β * α) :
    β ∈ Icc (1 / (3 * s)) (4 / s) ∧ α ∈ Icc (1 / (6 * s)) (6 / s) := by
  have hws : 0 < w * s := mul_pos hw hs
  -- `1 ≤ 3sβ` and `sβ ≤ 4`
  have hb1 : 1 ≤ 3 * s * β := by
    have : w * s / 2 ≤ 3 * s ^ 2 / 2 * w * β := by linarith
    have h2 : w * s * 1 ≤ w * s * (3 * s * β) := by linarith
    exact le_of_mul_le_mul_left h2 hws
  have hb2 : s * β ≤ 4 := by
    have : s ^ 2 / 2 * w * β ≤ 2 * (w * s) := by linarith
    have h2 : w * s * (s * β) ≤ w * s * 4 := by linarith
    exact le_of_mul_le_mul_left h2 hws
  have hα0 : 0 < α := by
    by_contra h0; push Not at h0
    have : 3 * s ^ 2 / 2 * β * α ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
    linarith
  have hsα : 0 ≤ s * α := (mul_pos hs hα0).le
  have ha1 : 1 ≤ 6 * s * α := by linarith [mul_le_mul_of_nonneg_right hb2 hsα]
  have ha2 : s * α ≤ 6 := by linarith [mul_le_mul_of_nonneg_left hb1 hsα]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ hs]; linarith
  · rw [div_le_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ hs]; linarith

/-- **The filler partition** (screening note, Lemma 4.21). -/
theorem exists_fillerPartition (P : Rect) {m : ℝ} (hm : 0 < m) {μ : ℂ → ℝ}
    (hμm : AEStronglyMeasurable μ (volume.restrict P.carrier))
    (hμ : ∀ᵐ x, x ∈ P.carrier → μ x ∈ Icc (m / 2) (3 * m / 2))
    {n : ℕ} (hn : ∫ x in P.carrier, μ x = n) (hw : 2 ≤ P.width * √m) (hh : 2 ≤ P.height * √m) :
    ∃ I piece, IsFillerPartition P μ m n I piece := by
  have hμi : IntegrableOn μ P.carrier := by
    have : IsFiniteMeasure (volume.restrict P.carrier) :=
      isFiniteMeasure_restrict.2 P.isCompact_carrier.measure_lt_top.ne
    refine Integrable.mono' (integrable_const (3 * m / 2)) hμm ?_
    exact (ae_restrict_iff' P.measurableSet_carrier).2 (hμ.mono fun x hx hxP => by
      have := hx hxP
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2])
  set w := P.width with hwdef
  set h := P.height with hhdef
  set s := √m with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hm
  have hss : s ^ 2 = m := Real.sq_sqrt hm.le
  have hw0 : 0 < w := by
    by_contra h0; push Not at h0; linarith [mul_nonpos_of_nonpos_of_nonneg h0 hs.le]
  have hh0 : 0 < h := by
    by_contra h0; push Not at h0; linarith [mul_nonpos_of_nonpos_of_nonneg h0 hs.le]
  -- integrability and bounds on boxes of `P`
  have hboxP : ∀ {x y v v' : ℝ}, 0 ≤ x → y ≤ w → 0 ≤ v → v' ≤ h →
      P.box (Icc x y) (Icc v v') ⊆ P.carrier := fun hx hy hv hv' =>
    Rect.box_mono (Icc_subset_Icc hx hy) (Icc_subset_Icc hv hv')
  have hint : ∀ {x y v v' : ℝ}, 0 ≤ x → y ≤ w → 0 ≤ v → v' ≤ h →
      IntegrableOn μ (P.box (Icc x y) (Icc v v')) := fun hx hy hv hv' =>
    hμi.mono_set (hboxP hx hy hv hv')
  have hbd : ∀ {x y v v' : ℝ}, 0 ≤ x → x ≤ y → y ≤ w → 0 ≤ v → v ≤ v' → v' ≤ h →
      m / 2 * ((y - x) * (v' - v)) ≤ ∫ p in P.box (Icc x y) (Icc v v'), μ p ∧
        ∫ p in P.box (Icc x y) (Icc v v'), μ p ≤ 3 * m / 2 * ((y - x) * (v' - v)) :=
    fun hx hxy hy hv hvv' hv' => P.setIntegral_box_bounds hxy hvv' (hint hx hy hv hv')
      (hμ.mono fun p hp hpb => hp (hboxP hx hy hv hv' hpb))
  -- the row masses
  set nr : ℕ := ⌊w * s⌋₊ with hnrdef
  have hnr1 : w * s / 2 ≤ nr := by
    have := Nat.lt_floor_add_one (w * s); linarith
  have hnr2 : (nr : ℝ) ≤ w * s := Nat.floor_le (by positivity)
  have hnr_pos : 1 ≤ nr := by
    rw [hnrdef, Nat.one_le_floor_iff]; linarith
  have hnR : (nr : ℝ) ≤ n := by
    have h1 := (hbd le_rfl hw0.le le_rfl le_rfl hh0.le le_rfl).1
    rw [Rect.carrier_eq_box] at hn
    rw [← hn]
    refine le_trans ?_ h1
    have : w * s * 1 ≤ w * s * (h * s / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_pos hw0 hs).le
    rw [← hss]; linarith
  have hnr_le_n : nr ≤ n := by exact_mod_cast hnR
  set K' : ℕ := n / nr with hK'def
  have hK'1 : 1 ≤ K' := (Nat.one_le_div_iff (by omega)).2 hnr_le_n
  have hK'2 : K' * nr ≤ n := Nat.div_mul_le_self n nr
  have hK'3 : n < (K' + 1) * nr := by
    have := Nat.lt_div_mul_add (a := n) (b := nr) (by omega)
    rw [add_mul, one_mul]; exact this
  set nrow : ℕ → ℕ := fun i => if i + 1 < K' then nr else n - (K' - 1) * nr with hnrowdef
  set T : ℕ → ℝ := fun i => if i < K' then ((i * nr : ℕ) : ℝ) else (n : ℝ) with hTdef
  have hTstep : ∀ i < K', T (i + 1) - T i = nrow i := by
    intro i hi
    by_cases hi1 : i + 1 < K'
    · simp only [hTdef, hnrowdef, hi, hi1, ↓reduceIte]; push_cast; ring
    · have hiK : i = K' - 1 := by omega
      have : (K' - 1) * nr ≤ n := le_trans (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) hK'2
      simp only [hTdef, hnrowdef, hi, hi1, ↓reduceIte]
      rw [Nat.cast_sub this, hiK]
  have hnrow : ∀ i < K', nr ≤ nrow i ∧ nrow i ≤ 2 * nr := by
    intro i hi
    simp only [hnrowdef]
    split_ifs with hi1
    · omega
    · have h1 : (K' - 1) * nr + nr = K' * nr := by
        rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hK'1]
      constructor
      · omega
      · have : (K' + 1) * nr = K' * nr + nr := by ring
        omega
  -- the cumulative mass of the rows
  set F : ℝ → ℝ := fun v => ∫ p in P.box (Icc 0 w) (Icc 0 v), μ p with hFdef
  have hFsub : ∀ v ∈ Icc 0 h, ∀ v' ∈ Icc 0 h, v ≤ v' →
      F v' - F v = ∫ p in P.box (Icc 0 w) (Icc v v'), μ p := by
    intro v hv v' hv' hvv'
    simp only [hFdef]
    rw [P.setIntegral_box_add_right measurableSet_Icc hv.1 hvv' (hint le_rfl le_rfl le_rfl hv'.2)]
    ring
  have hFslope : ∀ v ∈ Icc 0 h, ∀ v' ∈ Icc 0 h, v ≤ v' →
      m / 2 * w * (v' - v) ≤ F v' - F v ∧ F v' - F v ≤ 3 * m / 2 * w * (v' - v) := by
    intro v hv v' hv' hvv'
    rw [hFsub v hv v' hv' hvv']
    have := hbd le_rfl hw0.le le_rfl hv.1 hvv' hv'.2
    rw [sub_zero] at this
    constructor <;> linarith [this.1, this.2]
  have hFcont : ContinuousOn F (Icc 0 h) := by
    refine Metric.continuousOn_iff.2 fun v hv ε hε => ?_
    refine ⟨ε / (3 * m / 2 * w + 1), by positivity, fun v' hv' hd => ?_⟩
    rw [Real.dist_eq] at hd ⊢
    have hK : 0 ≤ 3 * m / 2 * w := by positivity
    have hle : |F v' - F v| ≤ 3 * m / 2 * w * |v' - v| := by
      have hc : 0 ≤ m / 2 * w := by positivity
      rcases le_total v v' with h1 | h1
      · have := hFslope v hv v' hv' h1
        have hn : 0 ≤ F v' - F v := le_trans (mul_nonneg hc (sub_nonneg.2 h1)) this.1
        rw [abs_of_nonneg hn, abs_of_nonneg (sub_nonneg.2 h1)]; exact this.2
      · have := hFslope v' hv' v hv h1
        have hn : 0 ≤ F v - F v' := le_trans (mul_nonneg hc (sub_nonneg.2 h1)) this.1
        rw [abs_sub_comm, abs_sub_comm v' v, abs_of_nonneg hn, abs_of_nonneg (sub_nonneg.2 h1)]
        exact this.2
    calc |F v' - F v| ≤ 3 * m / 2 * w * |v' - v| := hle
      _ ≤ (3 * m / 2 * w + 1) * |v' - v| := by
        rw [add_mul, one_mul]; exact le_add_of_nonneg_right (abs_nonneg _)
      _ < (3 * m / 2 * w + 1) * (ε / (3 * m / 2 * w + 1)) := by gcongr
      _ = ε := by field_simp
  have hF0 : F 0 = 0 := by
    simp only [hFdef, Icc_self]
    exact setIntegral_measure_zero _ (P.volume_box_singleton_right _ 0)
  have hFh : F h = n := by simp only [hFdef]; rw [← hn, Rect.carrier_eq_box]
  have hT0 : T 0 = 0 := by
    simp only [hTdef, show 0 < K' by omega, ↓reduceIte]; simp
  have hTN : T K' = F h := by simp [hTdef, hFh]
  have hTmono : ∀ k < K', T k ≤ T (k + 1) := fun k hk => by
    have := hTstep k hk; have : (0 : ℝ) ≤ nrow k := Nat.cast_nonneg _; linarith
  obtain ⟨v, hv0, hvK, hvF, hvstep⟩ := exists_mass_cuts hh0.le hFcont hF0
    (c₁ := m / 2 * w) (c₂ := 3 * m / 2 * w) (by positivity) hFslope hT0 hTN hTmono
  -- each row
  have hrow : ∀ i, ∃ x : ℕ → ℝ, i < K' → x 0 = 0 ∧ x (nrow i) = w ∧
      (∀ k ≤ nrow i, x k ∈ Icc 0 w ∧
        ∫ p in P.box (Icc 0 (x k)) (Icc (v i) (v (i + 1))), μ p = k) ∧
      ∀ k < nrow i, x k ≤ x (k + 1) ∧
        m / 2 * (v (i + 1) - v i) * (x (k + 1) - x k) ≤ 1 ∧
        1 ≤ 3 * m / 2 * (v (i + 1) - v i) * (x (k + 1) - x k) := by
    intro i
    by_cases hi : i < K'
    swap
    · exact ⟨fun _ => 0, fun h => absurd h hi⟩
    have hvi := (hvF i hi.le).1
    have hvi1 := (hvF (i + 1) hi).1
    obtain ⟨hvle, hv1, hv2⟩ := hvstep i hi
    rw [hTstep i hi] at hv1 hv2
    have hnr0 : (1 : ℝ) ≤ nrow i := by exact_mod_cast (hnr_pos.trans (hnrow i hi).1)
    have hβ : 0 < v (i + 1) - v i := by
      by_contra h0; push Not at h0
      have : 3 * m / 2 * w * (v (i + 1) - v i) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
      linarith
    set G : ℝ → ℝ := fun u => ∫ p in P.box (Icc 0 u) (Icc (v i) (v (i + 1))), μ p with hGdef
    have hGslope : ∀ x ∈ Icc 0 w, ∀ y ∈ Icc 0 w, x ≤ y →
        m / 2 * (v (i + 1) - v i) * (y - x) ≤ G y - G x ∧
          G y - G x ≤ 3 * m / 2 * (v (i + 1) - v i) * (y - x) := by
      intro x hx y hy hxy
      have hadd := P.setIntegral_box_add_left hx.1 hxy measurableSet_Icc
        (hint le_rfl hy.2 hvi.1 hvi1.2)
      have := hbd hx.1 hxy hy.2 hvi.1 hvle hvi1.2
      simp only [hGdef]
      rw [hadd]
      constructor <;> linarith [this.1, this.2]
    have hGcont : ContinuousOn G (Icc 0 w) := by
      refine Metric.continuousOn_iff.2 fun u hu ε hε => ?_
      set K := 3 * m / 2 * (v (i + 1) - v i)
      have hK : 0 ≤ K := by positivity
      refine ⟨ε / (K + 1), by positivity, fun u' hu' hd => ?_⟩
      rw [Real.dist_eq] at hd ⊢
      have hle : |G u' - G u| ≤ K * |u' - u| := by
        have hc : 0 ≤ m / 2 * (v (i + 1) - v i) := by positivity
        rcases le_total u u' with h1 | h1
        · have := hGslope u hu u' hu' h1
          have hn : 0 ≤ G u' - G u := le_trans (mul_nonneg hc (sub_nonneg.2 h1)) this.1
          rw [abs_of_nonneg hn, abs_of_nonneg (sub_nonneg.2 h1)]; exact this.2
        · have := hGslope u' hu' u hu h1
          have hn : 0 ≤ G u - G u' := le_trans (mul_nonneg hc (sub_nonneg.2 h1)) this.1
          rw [abs_sub_comm, abs_sub_comm u' u, abs_of_nonneg hn, abs_of_nonneg (sub_nonneg.2 h1)]
          exact this.2
      calc |G u' - G u| ≤ K * |u' - u| := hle
        _ ≤ (K + 1) * |u' - u| := by
          rw [add_mul, one_mul]; exact le_add_of_nonneg_right (abs_nonneg _)
        _ < (K + 1) * (ε / (K + 1)) := by gcongr
        _ = ε := by field_simp
    have hG0 : G 0 = 0 := by
      simp only [hGdef, Icc_self]
      exact setIntegral_measure_zero _ (P.volume_box_singleton_left 0 _)
    have hGw : G w = nrow i := by
      have := hFsub (v i) hvi (v (i + 1)) hvi1 hvle
      simp only [hGdef]
      rw [← this, (hvF (i + 1) hi).2, (hvF i hi.le).2, hTstep i hi]
    obtain ⟨x, hx0, hxN, hxF, hxstep⟩ := exists_mass_cuts hw0.le hGcont hG0
      (c₁ := m / 2 * (v (i + 1) - v i)) (c₂ := 3 * m / 2 * (v (i + 1) - v i)) (by positivity)
      hGslope (T := fun k => (k : ℝ)) (N := nrow i) (by simp) hGw.symm
      (fun k _ => by push_cast; linarith)
    refine ⟨x, fun _ => ⟨hx0, hxN, fun k hk => ⟨(hxF k hk).1, (hxF k hk).2⟩, fun k hk => ?_⟩⟩
    obtain ⟨h1, h2, h3⟩ := hxstep k hk
    push_cast at h2 h3
    exact ⟨h1, by linarith, by linarith⟩
  choose X hX using hrow
  -- the pieces
  set I : Finset (ℕ × ℕ) :=
    ((Finset.range K').sigma fun i => Finset.range (nrow i)).map
      (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding with hIdef
  have hmemI : ∀ p : ℕ × ℕ, p ∈ I ↔ p.1 < K' ∧ p.2 < nrow p.1 := by
    intro p
    simp only [hIdef, Finset.mem_map_equiv, Finset.mem_sigma, Finset.mem_range]
    rfl
  set piece : ℕ × ℕ → Rect := fun p =>
    P.sub (X p.1 p.2) (v p.1) (X p.1 (p.2 + 1) - X p.1 p.2) (v (p.1 + 1) - v p.1) with hpiecedef
  have hpiece : ∀ p ∈ I, (piece p).carrier =
      P.box (Icc (X p.1 p.2) (X p.1 (p.2 + 1))) (Icc (v p.1) (v (p.1 + 1))) := by
    intro p _
    simp only [hpiecedef, Rect.carrier_sub, add_sub_cancel]
  have hpieceO : ∀ p ∈ I, (piece p).openCarrier =
      P.box (Ioo (X p.1 p.2) (X p.1 (p.2 + 1))) (Ioo (v p.1) (v (p.1 + 1))) := by
    intro p _
    simp only [hpiecedef, Rect.openCarrier_sub, add_sub_cancel]
  -- monotonicity of the row cuts and of the cuts within a row
  have hvmono : ∀ k < K', v k ≤ v (k + 1) := fun k hk => (hvstep k hk).1
  have hXmono : ∀ i < K', ∀ k < nrow i, X i k ≤ X i (k + 1) := fun i hi k hk =>
    ((hX i hi).2.2.2 k hk).1
  -- the overlap of two pieces
  have hnull : ∀ p ∈ I, ∀ q ∈ I, p ≠ q →
      (∃ y, (piece p).carrier ∩ (piece q).carrier ⊆ P.box univ {y}) ∨
        (∃ y, (piece p).carrier ∩ (piece q).carrier ⊆ P.box {y} univ) := by
    intro p hp q hq hpq
    obtain ⟨hp1, hp2⟩ := (hmemI p).1 hp
    obtain ⟨hq1, hq2⟩ := (hmemI q).1 hq
    rw [hpiece p hp, hpiece q hq, Rect.box_inter]
    by_cases hrow : p.1 = q.1
    · right
      have hcol : p.2 ≠ q.2 := fun h => hpq (Prod.ext hrow h)
      rcases lt_or_gt_of_ne hcol with hlt | hlt
      · refine ⟨X p.1 (p.2 + 1), Rect.box_mono ?_ (subset_univ _)⟩
        rintro r ⟨⟨_, h1⟩, h2, _⟩
        have := le_of_monotone_seq (hXmono p.1 hp1) hlt (by rw [hrow]; exact hq2.le)
        rw [← hrow] at h2
        exact le_antisymm h1 (this.trans h2)
      · refine ⟨X p.1 p.2, Rect.box_mono ?_ (subset_univ _)⟩
        rintro r ⟨⟨h1, _⟩, _, h2⟩
        have := le_of_monotone_seq (hXmono p.1 hp1) hlt hp2.le
        rw [← hrow] at h2
        exact le_antisymm (h2.trans this) h1
    · left
      rcases lt_or_gt_of_ne hrow with hlt | hlt
      · refine ⟨v (p.1 + 1), Rect.box_mono (subset_univ _) ?_⟩
        rintro r ⟨⟨_, h1⟩, h2, _⟩
        exact le_antisymm h1 ((le_of_monotone_seq hvmono hlt hq1.le).trans h2)
      · refine ⟨v p.1, Rect.box_mono (subset_univ _) ?_⟩
        rintro r ⟨⟨h1, _⟩, _, h2⟩
        exact le_antisymm (h2.trans (le_of_monotone_seq hvmono hlt hp1.le)) h1
  have hsize : ∀ p ∈ I, (piece p).height ∈ Icc (1 / (3 * √m)) (4 / √m) ∧
      (piece p).width ∈ Icc (1 / (6 * √m)) (6 / √m) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := (hmemI p).1 hp
    obtain ⟨hvle, hv1, hv2⟩ := hvstep p.1 hp1
    rw [hTstep p.1 hp1] at hv1 hv2
    obtain ⟨-, hp3, hp4⟩ := (hX p.1 hp1).2.2.2 p.2 hp2
    have hn1 := hnrow p.1 hp1
    have hn1r : (nr : ℝ) ≤ nrow p.1 := by exact_mod_cast hn1.1
    have hn2r : (nrow p.1 : ℝ) ≤ 2 * nr := by exact_mod_cast hn1.2
    have hβ : 0 < v (p.1 + 1) - v p.1 := by
      have : (1 : ℝ) ≤ nrow p.1 := by exact_mod_cast (hnr_pos.trans hn1.1)
      by_contra h0; push Not at h0
      have : 3 * m / 2 * w * (v (p.1 + 1) - v p.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) h0
      linarith
    rw [← hss] at hv1 hv2 hp3 hp4
    exact filler_size_bounds (nr := (nr : ℝ)) (nrow := (nrow p.1 : ℝ))
      (α := X p.1 (p.2 + 1) - X p.1 p.2) hs hw0 hβ hnr1 hn1r (by linarith) hv1 hv2 hp3 hp4
  refine ⟨I, piece, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- card
    rw [hIdef, Finset.card_map, Finset.card_sigma]
    simp only [Finset.card_range]
    have : ∀ i ∈ Finset.range K', (nrow i : ℝ) = T (i + 1) - T i := fun i hi =>
      (hTstep i (Finset.mem_range.1 hi)).symm
    have hsum : ((∑ i ∈ Finset.range K', nrow i : ℕ) : ℝ) = n := by
      push_cast
      rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun i => T i), hTN, hT0, sub_zero, hFh]
    exact_mod_cast hsum
  · -- sub
    intro p hp
    obtain ⟨hp1, hp2⟩ := (hmemI p).1 hp
    have hx := (hX p.1 hp1).2.2.1
    refine ⟨X p.1 p.2, v p.1, rfl, (hx p.2 hp2.le).1.1, ?_, ((hvF p.1 hp1.le).1).1, ?_⟩
    · simp only [hpiecedef, Rect.sub_width, add_sub_cancel]
      exact (hx (p.2 + 1) hp2).1.2
    · simp only [hpiecedef, Rect.sub_height, add_sub_cancel]
      exact ((hvF (p.1 + 1) hp1).1).2
  · -- mass
    intro p hp
    obtain ⟨hp1, hp2⟩ := (hmemI p).1 hp
    have hx := (hX p.1 hp1).2.2.1
    have h0 := hx p.2 hp2.le
    have h1 := hx (p.2 + 1) hp2
    rw [hpiece p hp]
    have hadd := P.setIntegral_box_add_left h0.1.1 (hXmono p.1 hp1 p.2 hp2) measurableSet_Icc
      (hint le_rfl h1.1.2 ((hvF p.1 hp1.le).1).1 ((hvF (p.1 + 1) hp1).1).2)
    rw [h1.2, h0.2] at hadd
    push_cast at hadd
    linarith
  · -- widths
    intro p hp
    exact (hsize p hp).2
  · -- heights
    intro p hp
    exact (hsize p hp).1
  · -- null intersections
    intro p hp q hq hpq
    rcases hnull p hp q hq hpq with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact measure_mono_null hy (P.volume_box_singleton_right _ y)
    · exact measure_mono_null hy (P.volume_box_singleton_left y _)
  · -- disjoint interiors
    intro p hp q hq hpq
    obtain ⟨hp1, hp2⟩ := (hmemI p).1 hp
    obtain ⟨hq1, hq2⟩ := (hmemI q).1 hq
    rw [hpieceO p hp, hpieceO q hq, Set.disjoint_left]
    intro z hzp hzq
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := Rect.mem_box.1 hzp
    obtain ⟨⟨c1, c2⟩, d1, d2⟩ := Rect.mem_box.1 hzq
    by_cases hrow : p.1 = q.1
    · have hcol : p.2 ≠ q.2 := fun h => hpq (Prod.ext hrow h)
      rw [← hrow] at c1 c2 hq2
      rcases lt_or_gt_of_ne hcol with hlt | hlt
      · have := le_of_monotone_seq (hXmono p.1 hp1) hlt hq2.le; linarith
      · have := le_of_monotone_seq (hXmono p.1 hp1) hlt hp2.le; linarith
    · rcases lt_or_gt_of_ne hrow with hlt | hlt
      · have := le_of_monotone_seq hvmono hlt hq1.le; linarith
      · have := le_of_monotone_seq hvmono hlt hp1.le; linarith
  · -- cover
    ext z
    simp only [mem_iUnion, exists_prop]
    constructor
    · rintro ⟨p, hp, hz⟩
      have hsub := (hmemI p).1 hp
      obtain ⟨a, b, he, ha, haw, hb, hbh⟩ := (show ∃ a b, piece p = P.sub a b (piece p).width
          (piece p).height ∧ 0 ≤ a ∧ a + (piece p).width ≤ P.width ∧ 0 ≤ b ∧
          b + (piece p).height ≤ P.height from by
        have hx := (hX p.1 hsub.1).2.2.1
        refine ⟨X p.1 p.2, v p.1, rfl, (hx p.2 hsub.2.le).1.1, ?_, ((hvF p.1 hsub.1.le).1).1, ?_⟩
        · simp only [hpiecedef, Rect.sub_width, add_sub_cancel]
          exact (hx (p.2 + 1) hsub.2).1.2
        · simp only [hpiecedef, Rect.sub_height, add_sub_cancel]
          exact ((hvF (p.1 + 1) hsub.1).1).2)
      rw [he, Rect.carrier_sub] at hz
      exact Rect.box_mono (Icc_subset_Icc ha haw) (Icc_subset_Icc hb hbh) hz
    · intro hz
      obtain ⟨hzu, hzv⟩ := Rect.mem_box.1 (Rect.carrier_eq_box (H := P) ▸ hz)
      obtain ⟨i, hi, hvi⟩ := exists_mem_Icc_of_monotone hK'1 hvmono
        (show (P.coords z).im ∈ Icc (v 0) (v K') by rw [hv0, hvK]; exact hzv)
      have hXi := hX i hi
      have hnri : 1 ≤ nrow i := hnr_pos.trans (hnrow i hi).1
      obtain ⟨k, hk, hxk⟩ := exists_mem_Icc_of_monotone hnri (hXmono i hi)
        (show (P.coords z).re ∈ Icc (X i 0) (X i (nrow i)) by rw [hXi.1, hXi.2.1]; exact hzu)
      refine ⟨(i, k), (hmemI _).2 ⟨hi, hk⟩, ?_⟩
      rw [hpiece _ ((hmemI _).2 ⟨hi, hk⟩)]
      exact ⟨hxk, hvi⟩

end SandierSerfaty.Screening

end
