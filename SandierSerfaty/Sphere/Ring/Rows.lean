/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Chordal
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Row configurations and their row sums (sphere note, Definition 5.1, Lemma 5.2 (i)–(ii))

A row configuration (Definition 5.1) has heights `t k`, counts `N k` and phases `φ k`; its points are
`ℳ(φ k + 2π a / N k, t k)`, `0 ≤ a < N k`, `0 ≤ k < K` (rows are indexed from `0`).

* `Sphere.neg_log_norm_mercator_sub_eq`: the Mercator form of the chordal identity (Lemma 3.1) in the
  form `-log ‖ℳ(s,t) - ℳ(s',t')‖ = -(t-t')/2 - log |1 - e^{ζ'-ζ}| + ½ log cosh t + ½ log cosh t'`;
* `Sphere.RowConfig.rowSum_self`: Lemma 5.2 (i) composed with Lemma 3.1, the ordered pairs inside row `k`;
* `Sphere.RowConfig.rowSum_of_ne`: Lemma 5.2 (ii) composed with Lemma 3.1, the pairs of rows `k ≠ l`,
  with the gcd/lcm term `X k l` (`Sphere.RowConfig.X_comm`: `X k l = X l k`);
* `Sphere.RowConfig.configEnergy_points`: the row decomposition of the energy (first step of
  Proposition 5.5).

Lemma 5.2 (i)–(ii) are stated in the sphere note for `-log |2 sinh(w/2)|`; here they are stated for the
chordal energy itself, which is what Proposition 5.5 consumes (the difference is the term
`½ log cosh t + ½ log cosh t'` of Lemma 3.1).
-/

open Complex Finset

public section

namespace SandierSerfaty

namespace Sphere

/-! ### The Mercator form of the chordal identity -/

theorem norm_mercator_sub_eq (s t s' t' : ℝ) :
    ‖mercator s t - mercator s' t'‖ =
      Real.exp ((t - t') / 2) *
          ‖1 - Complex.exp (((t' : ℂ) + (s' : ℂ) * I) - ((t : ℂ) + (s : ℂ) * I))‖ /
        Real.sqrt (Real.cosh t * Real.cosh t') := by
  rw [mercator_eq_stereo, mercator_eq_stereo, norm_stereo_sub, lam_exp, lam_exp]
  set ζ : ℂ := (t : ℂ) + (s : ℂ) * I with hζ
  set ζ' : ℂ := (t' : ℂ) + (s' : ℂ) * I with hζ'
  have hsplit : Complex.exp ζ - Complex.exp ζ' =
      Complex.exp ζ * (1 - Complex.exp (ζ' - ζ)) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  have hn : ‖Complex.exp ζ‖ = Real.exp t := by
    rw [Complex.norm_exp]; simp [hζ]
  have hc0 : 0 < Real.cosh t := Real.cosh_pos t
  have hc0' : 0 < Real.cosh t' := Real.cosh_pos t'
  have hsq : Real.sqrt (Real.exp (-t) / Real.cosh t * (Real.exp (-t') / Real.cosh t')) =
      Real.exp (-(t + t') / 2) / Real.sqrt (Real.cosh t * Real.cosh t') := by
    have e : Real.exp (-t) / Real.cosh t * (Real.exp (-t') / Real.cosh t') =
        Real.exp (-(t + t') / 2) ^ 2 / (Real.cosh t * Real.cosh t') := by
      rw [← Real.exp_nat_mul]
      push_cast
      rw [show (2 : ℝ) * (-(t + t') / 2) = -t + -t' by ring, Real.exp_add]
      field_simp
    rw [e, Real.sqrt_div (by positivity), Real.sqrt_sq (Real.exp_pos _).le]
  rw [hsplit, norm_mul, hn, hsq]
  have : Real.exp (-(t + t') / 2) * Real.exp t = Real.exp ((t - t') / 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [← this]
  ring

/-- **Mercator form of the chordal identity**, in logarithms. -/
theorem neg_log_norm_mercator_sub_eq (s t s' t' : ℝ)
    (h : (1 : ℂ) - Complex.exp (((t' : ℂ) + (s' : ℂ) * I) - ((t : ℂ) + (s : ℂ) * I)) ≠ 0) :
    -Real.log ‖mercator s t - mercator s' t'‖ =
      -((t - t') / 2) -
          Real.log ‖1 - Complex.exp (((t' : ℂ) + (s' : ℂ) * I) - ((t : ℂ) + (s : ℂ) * I))‖ +
        Real.log (Real.cosh t) / 2 + Real.log (Real.cosh t') / 2 := by
  have hc0 : 0 < Real.cosh t := Real.cosh_pos t
  have hc0' : 0 < Real.cosh t' := Real.cosh_pos t'
  have hn : 0 < ‖1 - Complex.exp (((t' : ℂ) + (s' : ℂ) * I) - ((t : ℂ) + (s : ℂ) * I))‖ :=
    norm_pos_iff.2 h
  rw [norm_mercator_sub_eq, Real.log_div (by positivity) (by positivity),
    Real.log_mul (Real.exp_pos _).ne' hn.ne', Real.log_exp, Real.log_sqrt (by positivity),
    Real.log_mul hc0.ne' hc0'.ne']
  ring

/-! ### Products over roots of unity -/

/-- `∏_{a < N} (1 - ω^a z) = 1 - z^N` for a primitive `N`-th root of unity `ω`. -/
theorem prod_one_sub_pow_mul {N : ℕ} (hN : 0 < N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) (z : ℂ) :
    ∏ a ∈ range N, (1 - ω ^ a * z) = 1 - z ^ N := by
  have h := X_pow_sub_C_eq_prod hω hN (rfl : z ^ N = z ^ N)
  have h1 := congrArg (Polynomial.eval 1) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    one_pow, Polynomial.eval_prod] at h1
  exact h1.symm

/-- `∏_{b < γ M} (1 - ξ^b c) = (1 - c^M)^γ` for a primitive `M`-th root of unity `ξ`. -/
theorem prod_range_mul_one_sub_pow_mul {M : ℕ} (hM : 0 < M) {ξ : ℂ} (hξ : IsPrimitiveRoot ξ M)
    (c : ℂ) (γ : ℕ) :
    ∏ b ∈ range (γ * M), (1 - ξ ^ b * c) = (1 - c ^ M) ^ γ := by
  induction γ with
  | zero => simp
  | succ γ ih =>
    rw [Nat.succ_mul, prod_range_add, ih, pow_succ]
    congr 1
    rw [← prod_one_sub_pow_mul hM hξ c]
    refine prod_congr rfl fun x _ => ?_
    rw [pow_add, pow_mul', hξ.pow_eq_one, one_pow, one_mul]

/-- `∑_{j < N} -log |1 - ω^j| = -log N` for a primitive `N`-th root of unity `ω` (the `j = 0` term is
`-log 0 = 0`). -/
theorem sum_neg_log_norm_one_sub_pow {N : ℕ} (hN : 0 < N) {ω : ℂ} (hω : IsPrimitiveRoot ω N) :
    ∑ j ∈ range N, -Real.log ‖1 - ω ^ j‖ = -Real.log N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ', pow_zero, sub_self, norm_zero, Real.log_zero, neg_zero, add_zero,
    sum_neg_distrib]
  congr 1
  have hne : ∀ j ∈ range m, ‖1 - ω ^ (j + 1)‖ ≠ 0 := by
    intro j hj
    rw [norm_ne_zero_iff, sub_ne_zero]
    exact (hω.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero j)
      (by simpa using (mem_range.1 hj))).symm
  rw [← Real.log_prod hne, ← norm_prod, hω.prod_one_sub_pow_eq_order]
  push_cast
  rw [show ((m : ℂ) + 1) = ((m + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]

/-! ### Energies over a general index type -/

/-- The logarithmic energy `∑_{i ≠ j} -log ‖yᵢ - yⱼ‖` of a configuration indexed by a finite type. -/
@[expose] noncomputable def configEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ι → R3) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, -Real.log ‖Y i - Y j‖

/-- The diagonal terms are `-log 0 = 0`, so the energy is the sum over all ordered pairs. -/
theorem configEnergy_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : ι → R3) :
    configEnergy Y = ∑ i, ∑ j, -Real.log ‖Y i - Y j‖ := by
  unfold configEnergy
  refine sum_congr rfl fun i _ => ?_
  rw [← add_sum_erase _ _ (mem_univ i), sub_self, norm_zero, Real.log_zero, neg_zero, zero_add]

theorem sphereEnergy_comp_equiv {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (e : Fin n ≃ ι)
    (Y : ι → R3) : sphereEnergy (Y ∘ e) = configEnergy Y := by
  have h : sphereEnergy (Y ∘ e) = configEnergy (Y ∘ e) := rfl
  rw [h, configEnergy_eq_sum, configEnergy_eq_sum]
  simp only [Function.comp_apply]
  rw [← e.sum_comp (fun i => ∑ j, -Real.log ‖Y i - Y j‖)]
  refine sum_congr rfl fun i _ => ?_
  exact e.sum_comp (fun j => -Real.log ‖Y (e i) - Y j‖)

/-! ### Row configurations -/

/-- A **row configuration** (Definition 5.1): `K` rows; row `k < K` has height `t k`, count `N k` and
phase `φ k`. The values of `t`, `N`, `φ` at `k ≥ K` are irrelevant. -/
structure RowConfig where
  /-- The number of rows. -/
  K : ℕ
  /-- The counts. -/
  N : ℕ → ℕ
  /-- The heights. -/
  t : ℕ → ℝ
  /-- The phases. -/
  φ : ℕ → ℝ

namespace RowConfig

variable (R : RowConfig)

/-- The longitude `φ k + 2π a / N k` of point `a` of row `k`. -/
@[expose] noncomputable def angle (k a : ℕ) : ℝ := R.φ k + 2 * Real.pi * a / R.N k

/-- Point `a` of row `k`: `ℳ(φ k + 2π a / N k, t k)`. -/
@[expose] noncomputable def point (k a : ℕ) : R3 := mercator (R.angle k a) (R.t k)

/-- The points of the configuration, indexed by `Σ k : Fin K, Fin (N k)`. -/
@[expose] noncomputable def points : (Σ k : Fin R.K, Fin (R.N k)) → R3 := fun i => R.point i.1 i.2

/-- The total number of points `∑_k N k`. -/
@[expose] def card : ℕ := ∑ k ∈ range R.K, R.N k

/-- The interaction term `X_{kl} = -γ log |1 - e^{-LD} e^{iL(φ_l - φ_k)}|` of Lemma 5.2 (ii), with
`γ = gcd(N_k, N_l)`, `L = lcm(N_k, N_l)`, `D = |t_k - t_l|`. -/
@[expose] noncomputable def X (k l : ℕ) : ℝ :=
  -((Nat.gcd (R.N k) (R.N l) : ℕ) : ℝ) *
    Real.log ‖1 - Complex.exp ((-((Nat.lcm (R.N k) (R.N l) : ℕ) * |R.t k - R.t l|) : ℝ) : ℂ) *
      Complex.exp ((((Nat.lcm (R.N k) (R.N l) : ℕ) * (R.φ l - R.φ k) : ℝ) : ℂ) * I)‖

theorem X_comm (k l : ℕ) : R.X k l = R.X l k := by
  unfold X
  rw [Nat.gcd_comm, Nat.lcm_comm, abs_sub_comm]
  congr 2
  rw [← Complex.norm_conj]
  congr 1
  simp only [map_sub, map_one, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, map_mul,
    Complex.conj_I]
  congr 3
  push_cast
  ring

/-- The complex Mercator coordinate `t k + i (φ k + 2π a / N k)` of point `a` of row `k`. -/
@[expose] noncomputable def zeta (k a : ℕ) : ℂ := (R.t k : ℂ) + (R.angle k a : ℂ) * I

theorem neg_log_norm_point_sub (k a l b : ℕ)
    (h : (1 : ℂ) - Complex.exp (R.zeta l b - R.zeta k a) ≠ 0) :
    -Real.log ‖R.point k a - R.point l b‖ =
      -((R.t k - R.t l) / 2) - Real.log ‖1 - Complex.exp (R.zeta l b - R.zeta k a)‖ +
        Real.log (Real.cosh (R.t k)) / 2 + Real.log (Real.cosh (R.t l)) / 2 :=
  neg_log_norm_mercator_sub_eq _ _ _ _ h

/-- `e^{ζ_{k,b} - ζ_{k,a}} = ω^b (ω^a)⁻¹`, `ω = e^{2πi/N}`. -/
theorem exp_zeta_sub_self (k a b : ℕ) (hN : 0 < R.N k) :
    Complex.exp (R.zeta k b - R.zeta k a) =
      Complex.exp (2 * Real.pi * I / R.N k) ^ b * (Complex.exp (2 * Real.pi * I / R.N k) ^ a)⁻¹ := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  have : (R.N k : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [zeta, angle]
  push_cast
  field_simp
  ring

/-- **Lemma 5.2 (i)** (with Lemma 3.1): the ordered pairs inside row `k` contribute
`-N log N + N (N - 1) log cosh t_k`. -/
theorem rowSum_self (k : ℕ) (hN : 0 < R.N k) :
    ∑ a ∈ range (R.N k), ∑ b ∈ range (R.N k), -Real.log ‖R.point k a - R.point k b‖ =
      -((R.N k : ℝ) * Real.log (R.N k)) +
        (R.N k : ℝ) * ((R.N k : ℝ) - 1) * Real.log (Real.cosh (R.t k)) := by
  set N := R.N k with hNdef
  set ω : ℂ := Complex.exp (2 * Real.pi * I / N) with hωdef
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN.ne'
  have hω0 : ω ≠ 0 := Complex.exp_ne_zero _
  set lc := Real.log (Real.cosh (R.t k))
  -- the termwise formula
  have hterm : ∀ a ∈ range N, ∀ b ∈ range N, -Real.log ‖R.point k a - R.point k b‖ =
      -Real.log ‖1 - ω ^ b * (ω ^ a)⁻¹‖ + if b = a then 0 else lc := by
    intro a ha b hb
    rw [mem_range] at ha hb
    by_cases hab : b = a
    · subst hab
      simp [hω0]
    · rw [ite_eq_right hab, ← R.exp_zeta_sub_self k a b hN, R.neg_log_norm_point_sub]
      · ring
      · rw [R.exp_zeta_sub_self k a b hN, sub_ne_zero, ne_comm, ne_eq,
          mul_inv_eq_one₀ (pow_ne_zero _ hω0)]
        exact fun h => hab (hω.pow_inj hb ha h)
  -- reindexing the inner sum
  have hinner : ∀ a ∈ range N, ∑ b ∈ range N, -Real.log ‖1 - ω ^ b * (ω ^ a)⁻¹‖ = -Real.log N := by
    intro a ha
    rw [mem_range] at ha
    have : NeZero N := ⟨hN.ne'⟩
    rw [← sum_neg_log_norm_one_sub_pow hN hω, ← Fin.sum_univ_eq_sum_range
      (fun b => -Real.log ‖1 - ω ^ b * (ω ^ a)⁻¹‖), ← Fin.sum_univ_eq_sum_range
      (fun j => -Real.log ‖1 - ω ^ j‖)]
    rw [← Equiv.sum_comp (Equiv.addRight (⟨a, ha⟩ : Fin N))]
    refine sum_congr rfl fun j _ => ?_
    simp only [Equiv.coe_addRight, Fin.val_add]
    have hmod : ∀ m, ω ^ (m % N) = ω ^ m := fun m => by
      conv_rhs => rw [← Nat.mod_add_div m N]
      rw [pow_add, pow_mul, hω.pow_eq_one, one_pow, mul_one]
    congr 4
    rw [hmod, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hω0), mul_one]
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => hterm a ha b hb]
  simp only [sum_add_distrib]
  rw [sum_congr rfl hinner]
  have hcount : ∀ a ∈ range N, (∑ b ∈ range N, if b = a then (0 : ℝ) else lc) = (N - 1) * lc := by
    intro a ha
    rw [← sum_erase_add _ _ ha, ite_eq_left rfl, add_zero,
      sum_congr rfl fun b hb => ite_eq_right (ne_of_mem_erase hb), sum_const, card_erase_of_mem ha,
      card_range, nsmul_eq_mul, Nat.cast_sub (by omega)]
    simp
  rw [sum_congr rfl hcount]
  simp only [sum_const, card_range, nsmul_eq_mul]
  ring

theorem norm_exp_zeta_sub (k a l b : ℕ) :
    ‖Complex.exp (R.zeta l b - R.zeta k a)‖ = Real.exp (R.t l - R.t k) := by
  rw [Complex.norm_exp]
  simp [zeta]

/-- The double product behind Lemma 5.2 (ii): for `t_l < t_k`,
`∑_{a,b} -log |1 - e^{ζ_{l,b} - ζ_{k,a}}| = X_{kl}`. -/
theorem sum_sum_neg_log_norm_one_sub_exp (k l : ℕ) (hk : 0 < R.N k) (hl : 0 < R.N l)
    (h : R.t l < R.t k) :
    ∑ a ∈ range (R.N k), ∑ b ∈ range (R.N l),
        -Real.log ‖1 - Complex.exp (R.zeta l b - R.zeta k a)‖ = R.X k l := by
  set Nk := R.N k with hNk
  set Nl := R.N l with hNl
  set γ := Nat.gcd Nk Nl with hγ
  have hγ0 : 0 < γ := Nat.gcd_pos_of_pos_left _ hk
  set M := Nl / γ with hM
  set P := Nk / γ with hP
  have hNlM : Nl = γ * M := (Nat.mul_div_cancel' (Nat.gcd_dvd_right Nk Nl)).symm
  have hNkP : Nk = γ * P := (Nat.mul_div_cancel' (Nat.gcd_dvd_left Nk Nl)).symm
  have hM0 : 0 < M := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hNlM; omega
  have hL : Nat.lcm Nk Nl = Nk * M := by
    rw [Nat.lcm, hM, Nat.mul_div_assoc _ (Nat.gcd_dvd_right Nk Nl)]
  have hcop : Nat.Coprime P M := Nat.coprime_div_gcd_div_gcd hγ0
  -- the roots of unity
  set ω : ℂ := Complex.exp (-(2 * Real.pi * I / Nk)) with hωdef
  have hω : IsPrimitiveRoot ω Nk := by
    rw [hωdef, Complex.exp_neg]; exact (Complex.isPrimitiveRoot_exp Nk hk.ne').inv
  set ξ : ℂ := Complex.exp (2 * Real.pi * I * ((P : ℂ) / M)) with hξdef
  have hξ : IsPrimitiveRoot ξ M := Complex.isPrimitiveRoot_exp_of_coprime P M hM0.ne' hcop
  have hξn : ‖ξ‖ = 1 := hξ.norm'_eq_one hM0.ne'
  have hωn : ‖ω‖ = 1 := hω.norm'_eq_one hk.ne'
  set z : ℕ → ℂ := fun b => Complex.exp (R.zeta l b - R.zeta k 0) with hzdef
  set c : ℂ := Complex.exp ((Nk : ℂ) * (R.zeta l 0 - R.zeta k 0)) with hcdef
  have hNk0 : (Nk : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hNl0 : (Nl : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hM0' : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  have hγ0' : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ0.ne'
  have hfac : ∀ a b : ℕ, Complex.exp (R.zeta l b - R.zeta k a) = ω ^ a * z b := by
    intro a b
    rw [hωdef, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [zeta, angle, ← hNk, ← hNl]
    push_cast
    field_simp
    ring
  have hzpow : ∀ b : ℕ, z b ^ Nk = ξ ^ b * c := by
    intro b
    rw [hzdef, hξdef, hcdef]
    simp only
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    have hNlc : (Nl : ℂ) = γ * M := by exact_mod_cast hNlM
    have hNkc : (Nk : ℂ) = γ * P := by exact_mod_cast hNkP
    simp only [zeta, angle, ← hNk, ← hNl]
    push_cast
    rw [hNlc, hNkc]
    field_simp
    ring
  have hzn : ∀ b : ℕ, ‖z b‖ = Real.exp (R.t l - R.t k) := fun b => by
    rw [hzdef]; simp only; rw [norm_exp_zeta_sub]
  have hcn : ‖c‖ = Real.exp (Nk * (R.t l - R.t k)) := by
    rw [hcdef, Complex.norm_exp]; simp [zeta]
  have hlt1 : Real.exp (R.t l - R.t k) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hlt2 : Real.exp (Nk * (R.t l - R.t k)) < 1 :=
    Real.exp_lt_one_iff.2 (mul_neg_of_pos_of_neg (by exact_mod_cast hk) (by linarith))
  -- inner product over `a`
  have hinner : ∀ b ∈ range Nl, ∑ a ∈ range Nk,
      -Real.log ‖1 - Complex.exp (R.zeta l b - R.zeta k a)‖ = -Real.log ‖1 - ξ ^ b * c‖ := by
    intro b _
    simp_rw [hfac]
    rw [sum_neg_distrib, ← Real.log_prod, ← norm_prod, prod_one_sub_pow_mul hk hω, hzpow]
    intro a _
    rw [norm_ne_zero_iff, sub_ne_zero]
    intro h1
    have := congrArg norm h1
    rw [norm_one, norm_mul, norm_pow, hωn, one_pow, one_mul, hzn] at this
    linarith
  rw [sum_comm, sum_congr rfl hinner, sum_neg_distrib, ← Real.log_prod, ← norm_prod, hNlM,
    prod_range_mul_one_sub_pow_mul hM0 hξ c γ, norm_pow, Real.log_pow]
  · unfold X
    rw [← hNk, ← hNl, ← hγ, hL]
    have hc : c ^ M = Complex.exp ((-((Nk * M : ℕ) * |R.t k - R.t l|) : ℝ) : ℂ) *
        Complex.exp ((((Nk * M : ℕ) * (R.φ l - R.φ k) : ℝ) : ℂ) * I) := by
      rw [hcdef, ← Complex.exp_nat_mul, ← Complex.exp_add, abs_of_pos (by linarith)]
      congr 1
      simp only [zeta, angle]
      push_cast
      ring
    rw [hc]
    ring
  · intro b _
    rw [norm_ne_zero_iff, sub_ne_zero]
    intro h1
    have := congrArg norm h1
    rw [norm_one, norm_mul, norm_pow, hξn, one_pow, one_mul, hcn] at this
    linarith

/-- **Lemma 5.2 (ii)** (with Lemma 3.1), for `t_l < t_k`. -/
theorem rowSum_of_lt (k l : ℕ) (hk : 0 < R.N k) (hl : 0 < R.N l) (h : R.t l < R.t k) :
    ∑ a ∈ range (R.N k), ∑ b ∈ range (R.N l), -Real.log ‖R.point k a - R.point l b‖ =
      -((R.N k : ℝ) * R.N l * |R.t k - R.t l| / 2) + R.X k l +
        (R.N k : ℝ) * R.N l * (Real.log (Real.cosh (R.t k)) + Real.log (Real.cosh (R.t l))) / 2 := by
  have hterm : ∀ a ∈ range (R.N k), ∀ b ∈ range (R.N l), -Real.log ‖R.point k a - R.point l b‖ =
      -Real.log ‖1 - Complex.exp (R.zeta l b - R.zeta k a)‖ +
        (-((R.t k - R.t l) / 2) + Real.log (Real.cosh (R.t k)) / 2 +
          Real.log (Real.cosh (R.t l)) / 2) := by
    intro a _ b _
    rw [R.neg_log_norm_point_sub]
    · ring
    · rw [sub_ne_zero]
      intro h1
      have := congrArg norm h1
      rw [norm_one, norm_exp_zeta_sub] at this
      have : Real.exp (R.t l - R.t k) < 1 := Real.exp_lt_one_iff.2 (by linarith)
      linarith
  rw [sum_congr rfl fun a ha => sum_congr rfl fun b hb => hterm a ha b hb]
  simp only [sum_add_distrib]
  rw [R.sum_sum_neg_log_norm_one_sub_exp k l hk hl h]
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [abs_of_pos (by linarith)]
  ring

/-- **Lemma 5.2 (ii)** (with Lemma 3.1): for rows at distinct heights, the pairs `(a, b)` with `a` in
row `k` and `b` in row `l` contribute `-½ N_k N_l |t_k - t_l| + X_{kl} + ½ N_k N_l (log cosh t_k +
log cosh t_l)`. -/
theorem rowSum_of_ne (k l : ℕ) (hk : 0 < R.N k) (hl : 0 < R.N l) (h : R.t k ≠ R.t l) :
    ∑ a ∈ range (R.N k), ∑ b ∈ range (R.N l), -Real.log ‖R.point k a - R.point l b‖ =
      -((R.N k : ℝ) * R.N l * |R.t k - R.t l| / 2) + R.X k l +
        (R.N k : ℝ) * R.N l * (Real.log (Real.cosh (R.t k)) + Real.log (Real.cosh (R.t l))) / 2 := by
  rcases lt_or_gt_of_ne h with h' | h'
  · rw [sum_comm]
    simp_rw [norm_sub_rev (R.point k _)]
    rw [R.rowSum_of_lt l k hl hk h', X_comm, abs_sub_comm]
    ring
  · exact R.rowSum_of_lt k l hk hl h'

/-- The block `∑_{a,b} -log ‖y_{k,a} - y_{l,b}‖` of the energy between rows `k` and `l`. -/
@[expose] noncomputable def blockSum (k l : ℕ) : ℝ :=
  ∑ a ∈ range (R.N k), ∑ b ∈ range (R.N l), -Real.log ‖R.point k a - R.point l b‖

theorem configEnergy_points_eq_sum :
    configEnergy R.points = ∑ k ∈ range R.K, ∑ l ∈ range R.K, R.blockSum k l := by
  rw [configEnergy_eq_sum, Fintype.sum_sigma,
    ← Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ range R.K, R.blockSum k l)]
  refine sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun l => R.blockSum k l)]
  simp only [Fintype.sum_sigma]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  unfold blockSum
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun a _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-- **Row decomposition of the energy** (first step of Proposition 5.5): for nonempty rows at pairwise
distinct heights,
`E = -∑_k N_k log N_k - ½ ∑_{k,l} N_k N_l |t_k - t_l| + (n - 1) ∑_k N_k log cosh t_k + ∑_{k ≠ l} X_{kl}`. -/
theorem configEnergy_points (hN : ∀ k < R.K, 0 < R.N k)
    (ht : ∀ k < R.K, ∀ l < R.K, k ≠ l → R.t k ≠ R.t l) :
    configEnergy R.points =
      -∑ k ∈ range R.K, (R.N k : ℝ) * Real.log (R.N k) -
          (∑ k ∈ range R.K, ∑ l ∈ range R.K, (R.N k : ℝ) * R.N l * |R.t k - R.t l|) / 2 +
        ((R.card : ℝ) - 1) * ∑ k ∈ range R.K, (R.N k : ℝ) * Real.log (Real.cosh (R.t k)) +
          ∑ k ∈ range R.K, ∑ l ∈ (range R.K).erase k, R.X k l := by
  set lc : ℕ → ℝ := fun k => Real.log (Real.cosh (R.t k)) with hlc
  have hblock : ∀ k ∈ range R.K, ∀ l ∈ range R.K, R.blockSum k l =
      -((R.N k : ℝ) * R.N l * |R.t k - R.t l| / 2) + (R.N k : ℝ) * R.N l * (lc k + lc l) / 2 +
        if l = k then -((R.N k : ℝ) * Real.log (R.N k)) - R.N k * lc k else R.X k l := by
    intro k hk l hl
    rw [mem_range] at hk hl
    by_cases hkl : l = k
    · subst hkl
      rw [ite_eq_left rfl, blockSum, R.rowSum_self l (hN l hk), sub_self, abs_zero]
      simp only [hlc]
      ring
    · rw [ite_eq_right hkl, blockSum, R.rowSum_of_ne k l (hN k hk) (hN l hl)
        (ht k hk l hl (Ne.symm hkl))]
      simp only [hlc]
      ring
  rw [configEnergy_points_eq_sum,
    sum_congr rfl fun k hk => sum_congr rfl fun l hl => hblock k hk l hl]
  simp only [sum_add_distrib]
  have hite : ∀ k ∈ range R.K, (∑ l ∈ range R.K,
      if l = k then -((R.N k : ℝ) * Real.log (R.N k)) - R.N k * lc k else R.X k l) =
      ∑ l ∈ (range R.K).erase k, R.X k l + (-((R.N k : ℝ) * Real.log (R.N k)) - R.N k * lc k) := by
    intro k hk
    rw [← sum_erase_add _ _ hk, ite_eq_left rfl]
    congr 1
    exact sum_congr rfl fun l hl => ite_eq_right (ne_of_mem_erase hl)
  rw [sum_congr rfl hite]
  have hsym : ∑ k ∈ range R.K, ∑ l ∈ range R.K, (R.N k : ℝ) * R.N l * (lc k + lc l) / 2 =
      (R.card : ℝ) * ∑ k ∈ range R.K, (R.N k : ℝ) * lc k := by
    have e1 : ∑ k ∈ range R.K, ∑ l ∈ range R.K, (R.N k : ℝ) * R.N l * (lc k + lc l) / 2 =
        (∑ k ∈ range R.K, ∑ l ∈ range R.K, (R.N l : ℝ) * (R.N k * lc k)) / 2 +
          (∑ k ∈ range R.K, ∑ l ∈ range R.K, (R.N k : ℝ) * (R.N l * lc l)) / 2 := by
      rw [← add_div, ← sum_add_distrib, sum_div]
      refine sum_congr rfl fun k _ => ?_
      rw [← sum_add_distrib, sum_div]
      refine sum_congr rfl fun l _ => ?_
      ring
    rw [e1, sum_comm (f := fun k l => (R.N l : ℝ) * (R.N k * lc k))]
    simp only [← sum_mul, ← mul_sum]
    unfold card
    push_cast
    ring
  rw [hsym]
  simp only [sum_neg_distrib, sum_div, sum_add_distrib, sum_sub_distrib]
  ring

end RowConfig

end Sphere

end SandierSerfaty

end
