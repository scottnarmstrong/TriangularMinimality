/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.LocalCount
public import SandierSerfaty.Screening.Depth

/-!
# The screening data (screening note, §4.3: standing data, keep and drop, soft cut)

The screening note, §4.3 (Definitions 4.8, 4.10). The data of the internal
screening theorem (Theorem 4.2) after the good cut `d` is fixed are bundled in `Scr.Data`, and the
hypotheses in the `Prop` structure `Scr.Hyp` (one structure instead of a dozen binders: elaboration
cost). In the notation of the screening note (`δ` the depth of `Q = sq c t`, `U = int sq c (t - 1)`,
`Φ = E_{1/4}`, `ℓ = ℓc` the internal column width):

* `Data.K`: the kept charges `{p ∈ C : δ(p) ≥ d + 6}`; `Data.Ds`: the dropped charges near the cut
  `D* = {q ∈ C : d - 5/4 < δ(q) < d + 6}` (finite sets, as `Finset`s);
* `Data.psi`: the ramp `ψ = min(1, max(0, δ - d + 1))`;
* `Data.X = Φ + ∑_{p ∈ K} ∇f_{1/4}(· - p) - ∑_{q ∈ D*} W_q`. On `{δ > d - 1}` this is the
  screening note's `X = E - ∑_{D*} K_q` (Lemma 4.11(a)); off that set only `ψ X` and `∇ψ · X` are used,
  and both vanish there;
* `Data.g = 2πm(1 - ψ) + 2πψ ∑_{q ∈ D*} u_q - ∇ψ · X`, the soft-cut source;
* `Data.nD x = #{q ∈ D* : |q - x| < ¼}` (the screening note's `n`).

Basic facts: regions, finiteness, the ramp (Lipschitz, values, gradient), the count `n`.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Real

public section

namespace SandierSerfaty.Screening.Scr

/-- The data of the screening construction after the good cut (screening note, §4.3). -/
structure Data where
  /-- centre of the square `Q = sq c t` -/
  c : ℂ
  /-- side of `Q` -/
  t : ℝ
  /-- density -/
  m : ℝ
  /-- the (internal) column width `ℓc` -/
  ℓ : ℝ
  /-- the layer width `ℓt` -/
  ℓt : ℝ
  /-- the good cut -/
  d : ℝ
  /-- bound for `S_d = ∫_{R_d} |Φ|²` -/
  Sd : ℝ
  /-- radius of the new charges -/
  r₀ : ℝ
  /-- number of charges -/
  N : ℕ
  /-- charges -/
  C : Set ℂ
  /-- radii -/
  α : ℂ → ℝ
  /-- field -/
  E : ℂ → ℂ

namespace Data

variable (D : Data)

/-- The depth `δ` in `Q`. -/
@[expose] noncomputable def dep (x : ℂ) : ℝ := sqDepth D.c D.t x

/-- The square `Q`. -/
@[expose] def Q : Set ℂ := sq D.c D.t

/-- The open set `U = int sq c (t - 1) = {δ > ½}` where `E` is a charge field. -/
@[expose] def U : Set ℂ := interior (sq D.c (D.t - 1))

/-- `Φ = E_{1/4}`. -/
@[expose] noncomputable def Φ : ℂ → ℂ := truncField D.C (fun _ => 1 / 4) D.E

/-- The ring `R_d = {d - 5 ≤ δ ≤ d + 11}`. -/
@[expose] def R : Set ℂ := goodRing D.c D.t D.d

/-- The kept charges as a set. -/
@[expose] def Kset : Set ℂ := {p | p ∈ D.C ∧ D.d + 6 ≤ D.dep p}

/-- The dropped charges near the cut as a set. -/
@[expose] def Dset : Set ℂ := {q | q ∈ D.C ∧ D.d - 5 / 4 < D.dep q ∧ D.dep q < D.d + 6}

open scoped Classical in
/-- The kept charges `K`. -/
@[expose] noncomputable def K : Finset ℂ := if h : D.Kset.Finite then h.toFinset else ∅

open scoped Classical in
/-- The dropped charges `D*` near the cut. -/
@[expose] noncomputable def Ds : Finset ℂ := if h : D.Dset.Finite then h.toFinset else ∅

/-- The ramp `ψ = min(1, max(0, δ - d + 1))`. -/
@[expose] noncomputable def psi (x : ℂ) : ℝ := min 1 (max 0 (D.dep x - D.d + 1))

/-- `X = Φ + ∑_{p ∈ K} ∇f_{1/4}(· - p) - ∑_{q ∈ D*} W_q`. -/
@[expose] noncomputable def X (x : ℂ) : ℂ :=
  D.Φ x + ∑ p ∈ D.K, gradient (truncLog (1 / 4)) (x - p) - ∑ q ∈ D.Ds, radialW (1 / 4) (x - q)

/-- The smeared dropped charges `∑_{q ∈ D*} u_q`. -/
@[expose] noncomputable def uSum (x : ℂ) : ℝ := ∑ q ∈ D.Ds, radialU (1 / 4) (x - q)

/-- The soft-cut source `g = 2πm(1 - ψ) + 2πψ ∑_{D*} u_q - ∇ψ · X`. -/
@[expose] noncomputable def g (x : ℂ) : ℝ :=
  2 * π * D.m * (1 - D.psi x) + 2 * π * D.psi x * D.uSum x - inner ℝ (D.X x) (gradient D.psi x)

/-- `n(x) = #{q ∈ D* : |q - x| < ¼}`. -/
@[expose] noncomputable def nD (x : ℂ) : ℝ := ((D.Ds.filter fun q => ‖q - x‖ < 1 / 4).card : ℝ)

/-- The strip bound of Lemma 4.17 (from the pointwise bound `|g| ≤ 2πm + 36n + 1_Ā |Φ|`, the count
bound `∫ n² ≤ 2((9π/4)m)² |T| + (81/32) S_d` and AM–GM with the parameter `ε = 500/(mℓ)`), for a
top strip of width `w` (area `9w`). -/
@[expose] noncomputable def stripBound (m ℓ Sd w : ℝ) : ℝ :=
  (2 * π * m + 37 / (2 * (500 / (m * ℓ)))) * (9 * w) +
    18 * (500 / (m * ℓ)) * (2 * (9 * π / 4 * m) ^ 2 * (9 * w) + 81 / 32 * Sd) +
      500 / (m * ℓ) / 2 * Sd

/-- The hypotheses of the internal screening theorem (screening note, Theorem 4.2) after the good cut. -/
structure Hyp : Prop where
  m_pos : 0 < D.m
  N_eq : D.m * D.t ^ 2 = D.N
  /-- (K2) -/
  K2 : 1 / D.ℓ ≤ D.m / 8
  /-- (K4) -/
  K4 : 36 ≤ D.ℓ
  ℓ_le : 8 * D.ℓ ≤ D.ℓt
  t_ge : 8 * D.ℓt ≤ D.t
  d_mem : D.d ∈ Icc D.ℓt (3 / 2 * D.ℓt)
  hC : ∀ R : ℝ, (D.C ∩ closedBall 0 R).Finite
  hE : IsChargeField D.U D.m D.C D.E
  hα : ∀ p ∈ D.C, 0 < D.α p ∧ D.α p ≤ 1 / 4
  hα4 : ∀ p ∈ D.C, p ∉ sq D.c (D.t - 2) → D.α p = 1 / 4
  hdisj : ∀ p ∈ D.C ∩ sq D.c (D.t - 2 * D.ℓt), ∀ q ∈ D.C ∩ sq D.c (D.t - 2 * D.ℓt), p ≠ q →
    D.α p + D.α q ≤ ‖p - q‖
  hL2 : ∫⁻ x in D.Q, ENNReal.ofReal (‖truncField D.C D.α D.E x‖ ^ 2) ≠ ⊤
  Sd_nonneg : 0 ≤ D.Sd
  hSd : ∫⁻ x in D.R, ENNReal.ofReal (‖D.Φ x‖ ^ 2) ≤ ENNReal.ofReal D.Sd
  r₀_pos : 0 < D.r₀
  r₀_le : D.r₀ ≤ 1 / 4
  r₀_le' : D.r₀ ≤ 1 / (16 * √D.m)
  /-- (K1), in the form needed by the strip estimate (screening note Def 4.16, Lemma 4.17) -/
  strip_num : ∀ w ∈ Icc D.ℓ (3 * D.ℓ), stripBound D.m D.ℓ D.Sd w ≤ π / 2 * D.m * w * D.ℓ - 2 * π

variable {D}

/-! ### The depth -/

theorem dep_def (x : ℂ) : D.dep x = sqDepth D.c D.t x := rfl

theorem abs_dep_sub_le (x y : ℂ) : |D.dep x - D.dep y| ≤ ‖x - y‖ := abs_sqDepth_sub_le _ _ x y

theorem dep_le_add (x y : ℂ) : D.dep x ≤ D.dep y + ‖x - y‖ := by
  have := abs_dep_sub_le (D := D) x y; linarith [le_abs_self (D.dep x - D.dep y)]

theorem continuous_dep : Continuous D.dep := continuous_sqDepth _ _

theorem mem_Q_iff {x : ℂ} : x ∈ D.Q ↔ 0 ≤ D.dep x := mem_sq_iff_sqDepth_nonneg

theorem mem_U_iff {x : ℂ} : x ∈ D.U ↔ 1 / 2 < D.dep x := by
  rw [U, show D.t - 1 = D.t - 2 * (1 / 2) by ring]
  exact mem_interior_sq_iff_lt_sqDepth

theorem mem_interior_Q_iff {x : ℂ} : x ∈ interior D.Q ↔ 0 < D.dep x := by
  have := mem_interior_sq_iff_lt_sqDepth (c := D.c) (x := x) (t := D.t) (s := 0)
  rw [mul_zero, sub_zero] at this
  exact this

theorem isOpen_U : IsOpen D.U := isOpen_interior

theorem measurableSet_Q : MeasurableSet D.Q := measurableSet_sq _ _

theorem measurableSet_R : MeasurableSet D.R := measurableSet_goodRing _ _ _

theorem mem_R_iff {x : ℂ} : x ∈ D.R ↔ D.d - 5 ≤ D.dep x ∧ D.dep x ≤ D.d + 11 := Iff.rfl

/-- A closed depth band `{a ≤ δ ≤ b}` with `a ≥ 0` is compact. -/
theorem isCompact_dep_ge (a : ℝ) : IsCompact {x | a ≤ D.dep x} := by
  have : {x | a ≤ D.dep x} = sq D.c (D.t - 2 * a) := by
    ext x; exact mem_sq_iff_le_sqDepth.symm
  rw [this]; exact isCompact_sq _ _

/-! ### Consequences of the hypotheses -/

namespace Hyp

variable (h : D.Hyp)
include h

theorem ℓ_pos : 0 < D.ℓ := by linarith [h.K4]

theorem ℓt_ge : 288 ≤ D.ℓt := by linarith [h.K4, h.ℓ_le]

theorem d_ge : D.ℓt ≤ D.d := h.d_mem.1

theorem d_le : D.d ≤ 3 / 2 * D.ℓt := h.d_mem.2

theorem d_ge_ℓ : 8 * D.ℓ ≤ D.d := h.ℓ_le.trans h.d_ge

theorem d_pos : 288 ≤ D.d := (h.ℓt_ge).trans h.d_ge

/-- The ring lies in `{ℓt/2 ≤ δ < 2ℓt}`. -/
theorem R_subset_layer : D.R ⊆ {x | D.ℓt / 2 ≤ D.dep x ∧ D.dep x < 2 * D.ℓt} :=
  goodRing_subset (by linarith [h.ℓt_ge]) h.d_mem

theorem R_subset_U : D.R ⊆ D.U := fun x hx => by
  rw [mem_U_iff]; have := h.R_subset_layer hx; linarith [this.1, h.ℓt_ge]

omit h in
theorem isCompact_R : IsCompact D.R :=
  (isCompact_dep_ge (D := D) (D.d - 5)).of_isClosed_subset
    ((isClosed_le continuous_const continuous_dep).inter
      (isClosed_le continuous_dep continuous_const)) fun _ hx => hx.1

theorem hC_finite_of_dep_ge {a : ℝ} : {p | p ∈ D.C ∧ a ≤ D.dep p}.Finite := by
  have hb : Bornology.IsBounded {x | a ≤ D.dep x} := (isCompact_dep_ge (D := D) a).isBounded
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  exact (h.hC R).subset fun p hp => ⟨hp.1, hR hp.2⟩

theorem Kset_finite : D.Kset.Finite := h.hC_finite_of_dep_ge

theorem Dset_finite : D.Dset.Finite :=
  (h.hC_finite_of_dep_ge (a := D.d - 5 / 4)).subset fun _ hp => ⟨hp.1, hp.2.1.le⟩

theorem mem_K {p : ℂ} : p ∈ D.K ↔ p ∈ D.C ∧ D.d + 6 ≤ D.dep p := by
  classical
  rw [K, dite_eq_left_of_eq_true (eq_true h.Kset_finite), Set.Finite.mem_toFinset]; rfl

theorem mem_Ds {q : ℂ} : q ∈ D.Ds ↔ q ∈ D.C ∧ D.d - 5 / 4 < D.dep q ∧ D.dep q < D.d + 6 := by
  classical
  rw [Ds, dite_eq_left_of_eq_true (eq_true h.Dset_finite), Set.Finite.mem_toFinset]; rfl

theorem K_subset_C : (D.K : Set ℂ) ⊆ D.C := fun _ hp => (h.mem_K.1 hp).1

theorem Ds_subset_C : (D.Ds : Set ℂ) ⊆ D.C := fun _ hp => (h.mem_Ds.1 hp).1

theorem disjoint_K_Ds : Disjoint D.K D.Ds := by
  rw [Finset.disjoint_left]
  intro p hpK hpD
  linarith [(h.mem_K.1 hpK).2, (h.mem_Ds.1 hpD).2.2]

/-- Charges neither kept nor near the cut have `δ ≤ d - 5/4`. -/
theorem dep_le_of_notMem {p : ℂ} (hp : p ∈ D.C) (hK : p ∉ D.K) (hD : p ∉ D.Ds) :
    D.dep p ≤ D.d - 5 / 4 := by
  by_contra hlt
  push Not at hlt
  by_cases h6 : D.d + 6 ≤ D.dep p
  · exact hK (h.mem_K.2 ⟨hp, h6⟩)
  · exact hD (h.mem_Ds.2 ⟨hp, hlt, not_le.1 h6⟩)

/-- The charge field is locally integrable on `U`. -/
theorem integrableOn_Φ {S : Set ℂ} (hS : IsCompact S) (hSU : S ⊆ D.U) : IntegrableOn D.Φ S :=
  integrableOn_truncField h.hC h.hE.1 (fun _ _ => by norm_num) ⟨1 / 4, fun _ _ => le_rfl⟩ hS hSU

theorem integrableOn_Φ_R : IntegrableOn D.Φ D.R := h.integrableOn_Φ isCompact_R h.R_subset_U

end Hyp

/-! ### The ramp `ψ` -/

theorem psi_nonneg (x : ℂ) : 0 ≤ D.psi x := le_min zero_le_one (le_max_left _ _)

theorem psi_le_one (x : ℂ) : D.psi x ≤ 1 := min_le_left _ _

theorem psi_eq_one {x : ℂ} (hx : D.d ≤ D.dep x) : D.psi x = 1 :=
  min_eq_left (le_max_of_le_right (by linarith))

theorem psi_eq_zero {x : ℂ} (hx : D.dep x ≤ D.d - 1) : D.psi x = 0 := by
  rw [psi, max_eq_left (by linarith), min_eq_right zero_le_one]

theorem lipschitzWith_psi : LipschitzWith 1 D.psi := by
  have h1 : LipschitzWith 1 fun x => D.dep x - D.d + 1 := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, NNReal.coe_one, one_mul, dist_eq_norm]
    calc |D.dep a - D.d + 1 - (D.dep b - D.d + 1)| = |D.dep a - D.dep b| := by ring_nf
      _ ≤ ‖a - b‖ := abs_dep_sub_le a b
  exact (h1.const_max 0).const_min 1

theorem continuous_psi : Continuous D.psi := lipschitzWith_psi.continuous

theorem norm_gradient_psi_le (x : ℂ) : ‖gradient D.psi x‖ ≤ 1 := by
  simpa using norm_gradient_le_of_lipschitz lipschitzWith_psi x

theorem gradient_psi_of_lt {x : ℂ} (hx : D.d < D.dep x) : gradient D.psi x = 0 := by
  have hev : D.psi =ᶠ[nhds x] fun _ => 1 := by
    filter_upwards [(isOpen_lt continuous_const continuous_dep).mem_nhds hx] with y hy
    exact psi_eq_one (le_of_lt hy)
  simp only [gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]

theorem gradient_psi_of_lt' {x : ℂ} (hx : D.dep x < D.d - 1) : gradient D.psi x = 0 := by
  have hev : D.psi =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_dep continuous_const).mem_nhds hx] with y hy
    exact psi_eq_zero (le_of_lt hy)
  simp only [gradient, hev.fderiv_eq, fderiv_const_apply, map_zero]

/-- The closed ramp band `Ā = {d - 1 ≤ δ ≤ d}`, off which `∇ψ = 0`. -/
@[expose] def Abar (D : Data) : Set ℂ := {x | D.d - 1 ≤ D.dep x ∧ D.dep x ≤ D.d}

theorem measurableSet_Abar : MeasurableSet D.Abar := measurableSet_sqDepth_Icc _ _ _ _

theorem gradient_psi_of_notMem {x : ℂ} (hx : x ∉ D.Abar) : gradient D.psi x = 0 := by
  simp only [Abar, mem_ofPred_eq, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact gradient_psi_of_lt' hx
  · exact gradient_psi_of_lt hx

theorem Abar_subset_R : D.Abar ⊆ D.R := fun _ hx => by
  obtain ⟨h1, h2⟩ := hx
  rw [mem_R_iff]
  exact ⟨by linarith, by linarith⟩

/-! ### Smeared charges and the count `n` -/

theorem radialU_quarter_eq (x q : ℂ) :
    radialU (1 / 4) (x - q) = if ‖q - x‖ < 1 / 4 then 16 / π else 0 := by
  split_ifs with hq
  · exact radialU_quarter_of_mem (by rwa [mem_ball, dist_zero_right, norm_sub_rev])
  · exact radialU_of_notMem (by rwa [mem_ball, dist_zero_right, norm_sub_rev])

theorem uSum_eq (x : ℂ) : D.uSum x = 16 / π * D.nD x := by
  rw [uSum, nD, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [radialU_quarter_eq]
  split_ifs <;> simp

theorem nD_nonneg (x : ℂ) : 0 ≤ D.nD x := Nat.cast_nonneg _

theorem uSum_nonneg (x : ℂ) : 0 ≤ D.uSum x := by
  rw [uSum_eq]; have := nD_nonneg (D := D) x; positivity

theorem norm_sum_radialW_le (x : ℂ) : ‖∑ q ∈ D.Ds, radialW (1 / 4) (x - q)‖ ≤ 4 * D.nD x := by
  rw [nD, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  split_ifs with hq
  · simpa using norm_radialW_quarter_le (x - q)
  · rw [radialW_of_notMem (by rw [mem_ball, dist_zero_right, norm_sub_rev]; exact hq)]
    simp

end Data

end SandierSerfaty.Screening.Scr

end
