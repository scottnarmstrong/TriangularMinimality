/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Ring.Geometry

/-!
# Barycentre depth (sphere note, Lemma 5.8 (G4))

* `Sphere.ringDensity_eq_mass`: `ϱ = (2/n) Φ (n - Φ)`;
* `Sphere.slabBary n c d`: the `ν`-barycentre of the mass slab `{c ≤ Φ ≤ d}`;
  `Sphere.ringHeight_eq_slabBary`: the heights of `Y_n` are slab barycentres;
* `Sphere.slab_moment_bounds`: on a bounded slab `[α, β] = [τ(a), τ(b)]` with `m ≤ ϱ ≤ M`,
  `N (t - α)` and `N (β - t)` lie in `[m L²/2, M L²/2]` and `N ∈ [m L, M L]` (`N = b - a`,
  `L = β - α`, `t` the barycentre);
* `Sphere.slabBary_depth_Iic`, `Sphere.slabBary_depth_Ici`: on the polar slabs the barycentre lies
  at distance `≥ e^{-2} (n - b)/n` (resp. `e^{-2} a / n`) from the finite end;
* `Sphere.ringHeight_depth_left`, `Sphere.ringHeight_depth_right`: **(G4)** with `c₀ = 3/112`: for
  `n ≥ 102` and every row `k`, `t_k` lies at distance `≥ c₀ / N_k` from the finite ends of `I_k`.
-/

open MeasureTheory Set

public section

namespace SandierSerfaty

namespace Sphere

theorem ringDensity_eq_mass {n : ℝ} (hn : n ≠ 0) (t : ℝ) :
    ringDensity n t = 2 / n * ringMass n t * (n - ringMass n t) := by
  have hc := (Real.cosh_pos t).ne'
  have hcs : Real.cosh t ^ 2 - Real.sinh t ^ 2 = 1 := by rw [Real.cosh_sq]; ring
  rw [ringDensity, ringMass, Real.tanh_eq_sinh_div_cosh]
  have e : 2 / n * (n / 2 * (1 + Real.sinh t / Real.cosh t)) *
      (n - n / 2 * (1 + Real.sinh t / Real.cosh t)) =
      n / 2 * ((Real.cosh t ^ 2 - Real.sinh t ^ 2) / Real.cosh t ^ 2) := by
    field_simp; ring
  rw [e, hcs]; ring

/-- `∫_α^β (s - α) ds = (β - α)²/2`. -/
theorem integral_sub_left (α β : ℝ) : ∫ s in α..β, (s - α) = (β - α) ^ 2 / 2 := by
  have h : ∀ x ∈ uIcc α β, HasDerivAt (fun s => (s - α) * (s - α) / 2) (x - α) x := fun x _ =>
    ((((hasDerivAt_id' x).sub_const α).mul ((hasDerivAt_id' x).sub_const α)).div_const 2).congr_deriv
      (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((continuous_id.sub continuous_const).intervalIntegrable _ _)]
  ring

/-- `∫_α^β (β - s) ds = (β - α)²/2`. -/
theorem integral_sub_right (α β : ℝ) : ∫ s in α..β, (β - s) = (β - α) ^ 2 / 2 := by
  have h : ∀ x ∈ uIcc α β, HasDerivAt (fun s => -((β - s) * (β - s) / 2)) (β - x) x := fun x _ =>
    ((((hasDerivAt_id' x).const_sub β).mul ((hasDerivAt_id' x).const_sub β)).div_const 2).neg.congr_deriv
      (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((continuous_const.sub continuous_id).intervalIntegrable _ _)]
  ring

/-- The `ν`-barycentre `(d - c)⁻¹ ∫_{c ≤ Φ ≤ d} t dν` of the mass slab `{c ≤ Φ ≤ d}`. -/
@[expose] noncomputable def slabBary (n c d : ℝ) : ℝ :=
  (d - c)⁻¹ * ∫ s in {t | c ≤ ringMass n t ∧ ringMass n t ≤ d}, s * ringDensity n s

theorem ringHeight_eq_slabBary {n k : ℕ} (hk : k < ringK n) :
    ringHeight n k = slabBary n (ringState n k).1 (ringState n (k + 1)).1 := by
  have h : ((ringState n (k + 1)).1 : ℝ) - (ringState n k).1 = ringN n k := by
    rw [(ringStep_spec_at hk).1]; push_cast; ring
  rw [ringHeight, slabBary, h]

theorem slab_eq_Icc {n c d : ℝ} (hc : 0 < c) (hcn : c < n) (hd : 0 < d) (hdn : d < n) :
    {t | c ≤ ringMass n t ∧ ringMass n t ≤ d} = Icc (ringQuantile n c) (ringQuantile n d) := by
  ext t; simp [le_ringMass_iff hc hcn, ringMass_le_iff hd hdn]

theorem ringQuantile_lt {n a b : ℝ} (ha : 0 < a) (hab : a < b) (hbn : b < n) :
    ringQuantile n a < ringQuantile n b := by
  have hn : 0 < n := by linarith
  have h1 := ringMass_quantile ha (hab.trans hbn)
  have h2 := ringMass_quantile (ha.trans hab) hbn
  exact (ringMass_strictMono hn).lt_iff_lt.1 (by rw [h1, h2]; exact hab)

/-- On a bounded slab, the zeroth and first moments as interval integrals. -/
theorem slab_moments {n a b : ℝ} (ha : 0 < a) (hab : a < b) (hbn : b < n) :
    b - a = ∫ s in ringQuantile n a..ringQuantile n b, ringDensity n s ∧
      (b - a) * (slabBary n a b - ringQuantile n a) =
        ∫ s in ringQuantile n a..ringQuantile n b, (s - ringQuantile n a) * ringDensity n s ∧
      (b - a) * (ringQuantile n b - slabBary n a b) =
        ∫ s in ringQuantile n a..ringQuantile n b, (ringQuantile n b - s) * ringDensity n s := by
  set α := ringQuantile n a
  set β := ringQuantile n b
  have hαβ : α ≤ β := (ringQuantile_lt ha hab hbn).le
  have hcont := continuous_ringDensity n
  have h0 : ∫ s in α..β, ringDensity n s = b - a := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_ringMass n x)
      (hcont.intervalIntegrable _ _), ringMass_quantile (ha.trans hab) hbn,
      ringMass_quantile ha (hab.trans hbn)]
  have hI : ∫ s in {t | a ≤ ringMass n t ∧ ringMass n t ≤ b}, s * ringDensity n s =
      ∫ s in α..β, s * ringDensity n s := by
    rw [slab_eq_Icc ha (hab.trans hbn) (ha.trans hab) hbn, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hαβ]
  have hm1 : IntervalIntegrable (fun s => s * ringDensity n s) volume α β :=
    (continuous_id.mul hcont).intervalIntegrable _ _
  have hm0 : IntervalIntegrable (fun s => ringDensity n s) volume α β := hcont.intervalIntegrable _ _
  have hba : b - a ≠ 0 := by linarith
  refine ⟨h0.symm, ?_, ?_⟩
  · have e : (fun s => (s - α) * ringDensity n s) = fun s => s * ringDensity n s - α * ringDensity n s := by
      funext s; ring
    rw [e, intervalIntegral.integral_sub hm1 (hm0.const_mul α), intervalIntegral.integral_const_mul,
      h0, slabBary, hI]
    field_simp
  · have e : (fun s => (β - s) * ringDensity n s) = fun s => β * ringDensity n s - s * ringDensity n s := by
      funext s; ring
    rw [e, intervalIntegral.integral_sub (hm0.const_mul β) hm1, intervalIntegral.integral_const_mul,
      h0, slabBary, hI]
    field_simp

/-- **Moment bounds.** On a bounded slab `[α, β] = [τ(a), τ(b)]` with `m ≤ ϱ ≤ M`, the barycentre
`t` satisfies `m L²/2 ≤ N (t - α), N (β - t) ≤ M L²/2` and `m L ≤ N ≤ M L`, where `N = b - a`,
`L = β - α`. -/
theorem slab_moment_bounds {n a b m M : ℝ} (ha : 0 < a) (hab : a < b) (hbn : b < n)
    (hm : ∀ t ∈ Icc (ringQuantile n a) (ringQuantile n b), m ≤ ringDensity n t)
    (hM : ∀ t ∈ Icc (ringQuantile n a) (ringQuantile n b), ringDensity n t ≤ M) :
    m * (ringQuantile n b - ringQuantile n a) ^ 2 / 2 ≤
        (b - a) * (slabBary n a b - ringQuantile n a) ∧
      (b - a) * (slabBary n a b - ringQuantile n a) ≤
        M * (ringQuantile n b - ringQuantile n a) ^ 2 / 2 ∧
      m * (ringQuantile n b - ringQuantile n a) ^ 2 / 2 ≤
        (b - a) * (ringQuantile n b - slabBary n a b) ∧
      (b - a) * (ringQuantile n b - slabBary n a b) ≤
        M * (ringQuantile n b - ringQuantile n a) ^ 2 / 2 ∧
      m * (ringQuantile n b - ringQuantile n a) ≤ b - a ∧
      b - a ≤ M * (ringQuantile n b - ringQuantile n a) := by
  obtain ⟨h0, h1, h2⟩ := slab_moments (n := n) ha hab hbn
  set α := ringQuantile n a
  set β := ringQuantile n b
  have hαβ : α ≤ β := (ringQuantile_lt ha hab hbn).le
  have hcont := continuous_ringDensity n
  have hlin1 := integral_sub_left α β
  have hlin2 := integral_sub_right α β
  have ii : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g volume α β :=
    fun g hg => hg.intervalIntegrable _ _
  have c1 : Continuous fun s => (s - α) * ringDensity n s := (continuous_id.sub continuous_const).mul hcont
  have c2 : Continuous fun s => (β - s) * ringDensity n s := (continuous_const.sub continuous_id).mul hcont
  have hc : ∀ c : ℝ, ∫ _ in α..β, c = c * (β - α) := fun c => by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1]
    calc m * (β - α) ^ 2 / 2 = ∫ s in α..β, m * (s - α) := by
          rw [intervalIntegral.integral_const_mul, hlin1]; ring
      _ ≤ _ := intervalIntegral.integral_mono_on hαβ (ii _ (by fun_prop)) (ii _ c1) fun s hs => by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hm s hs) (by linarith [hs.1])
  · rw [h1]
    calc _ ≤ ∫ s in α..β, M * (s - α) :=
          intervalIntegral.integral_mono_on hαβ (ii _ c1) (ii _ (by fun_prop)) fun s hs => by
            rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hM s hs) (by linarith [hs.1])
      _ = M * (β - α) ^ 2 / 2 := by rw [intervalIntegral.integral_const_mul, hlin1]; ring
  · rw [h2]
    calc m * (β - α) ^ 2 / 2 = ∫ s in α..β, m * (β - s) := by
          rw [intervalIntegral.integral_const_mul, hlin2]; ring
      _ ≤ _ := intervalIntegral.integral_mono_on hαβ (ii _ (by fun_prop)) (ii _ c2) fun s hs => by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hm s hs) (by linarith [hs.2])
  · rw [h2]
    calc _ ≤ ∫ s in α..β, M * (β - s) :=
          intervalIntegral.integral_mono_on hαβ (ii _ c2) (ii _ (by fun_prop)) fun s hs => by
            rw [mul_comm M]; exact mul_le_mul_of_nonneg_left (hM s hs) (by linarith [hs.2])
      _ = M * (β - α) ^ 2 / 2 := by rw [intervalIntegral.integral_const_mul, hlin2]; ring
  · rw [h0, ← hc]
    exact intervalIntegral.integral_mono_on hαβ intervalIntegrable_const (ii _ hcont) hm
  · rw [h0, ← hc]
    exact intervalIntegral.integral_mono_on hαβ (ii _ hcont) intervalIntegrable_const hM

/-- On a bounded slab `[τ(a), τ(b)]`, `(2/n) a (n - b) ≤ ϱ ≤ (2/n) b (n - a)`. -/
theorem ringDensity_mem_slab {n a b t : ℝ} (ha : 0 < a) (hab : a < b) (hbn : b < n)
    (ht : t ∈ Icc (ringQuantile n a) (ringQuantile n b)) :
    2 / n * a * (n - b) ≤ ringDensity n t ∧ ringDensity n t ≤ 2 / n * b * (n - a) := by
  have hn : 0 < n := by linarith
  have h1 : a ≤ ringMass n t := (le_ringMass_iff ha (hab.trans hbn) t).2 ht.1
  have h2 : ringMass n t ≤ b := (ringMass_le_iff (ha.trans hab) hbn t).2 ht.2
  rw [ringDensity_eq_mass hn.ne']
  have h2n : 0 < 2 / n := by positivity
  constructor
  · rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 (by linarith) (by linarith) (by linarith)) h2n.le
  · rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul h2 (by linarith) (by linarith) (by linarith)) h2n.le

/-- **Barycentre depth on a bounded slab**: the barycentre lies at distance
`≥ L a (n - b) / (2 b (n - a))` from both ends of `[τ(a), τ(b)]` (`L = τ(b) - τ(a)`). -/
theorem slabBary_depth {n a b : ℝ} (ha : 0 < a) (hab : a < b) (hbn : b < n) :
    (ringQuantile n b - ringQuantile n a) * (a * (n - b)) / (2 * (b * (n - a))) ≤
        slabBary n a b - ringQuantile n a ∧
      (ringQuantile n b - ringQuantile n a) * (a * (n - b)) / (2 * (b * (n - a))) ≤
        ringQuantile n b - slabBary n a b := by
  have hn : 0 < n := by linarith
  obtain ⟨h1, -, h3, -, -, h6⟩ := slab_moment_bounds (n := n) (m := 2 / n * a * (n - b))
    (M := 2 / n * b * (n - a)) ha hab hbn (fun t ht => (ringDensity_mem_slab ha hab hbn ht).1)
    (fun t ht => (ringDensity_mem_slab ha hab hbn ht).2)
  set L := ringQuantile n b - ringQuantile n a
  have hL : 0 < L := sub_pos.2 (ringQuantile_lt ha hab hbn)
  have hN : 0 < b - a := by linarith
  have hq : 0 < b * (n - a) := mul_pos (by linarith) (by linarith)
  have hp : 0 < a * (n - b) := mul_pos ha (by linarith)
  -- `L a (n-b) / (2 b (n-a)) = (m L²/2) / (M L)`
  have key : ∀ x : ℝ, 2 / n * a * (n - b) * L ^ 2 / 2 ≤ (b - a) * x → L * (a * (n - b)) /
      (2 * (b * (n - a))) ≤ x := by
    intro x hx
    rw [div_le_iff₀ (by positivity)]
    have h6' : (b - a) * (b * (n - a)) ≤ 2 / n * b * (n - a) * L * (b * (n - a)) :=
      mul_le_mul_of_nonneg_right h6 hq.le
    have hx' : 0 ≤ x := by
      by_contra hneg
      push Not at hneg
      have : (b - a) * x < 0 := mul_neg_of_pos_of_neg hN hneg
      have : 0 < 2 / n * a * (n - b) * L ^ 2 / 2 := by positivity
      linarith
    -- `(b - a) x ≥ (1/n) a (n - b) L²` and `b - a ≤ (2/n) b (n - a) L`
    have e : L * (a * (n - b)) * (b - a) ≤ x * (2 * (b * (n - a))) * (b - a) := by
      have : L * (a * (n - b)) * (b - a) ≤ L * (a * (n - b)) * (2 / n * b * (n - a) * L) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      have h' : L * (a * (n - b)) * (2 / n * b * (n - a) * L) =
          (2 / n * a * (n - b) * L ^ 2 / 2) * (2 * (b * (n - a))) := by ring
      nlinarith
    exact le_of_mul_le_mul_right e hN
  exact ⟨key _ h1, key _ h3⟩

/-! ### The polar slabs -/

/-- `Φ(s) ≥ e^{-2} Φ(β)` for `s ∈ [β - 1, β]`. -/
theorem exp_neg_two_mul_ringMass_le {n β s : ℝ} (hn : 0 < n) (hs : β - 1 ≤ s) :
    Real.exp (-2) * ringMass n β ≤ ringMass n s := by
  rw [ringMass_eq, ringMass_eq, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : Real.exp (-2) * Real.exp (-(2 * s)) ≤ Real.exp (-(2 * β)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  nlinarith [Real.exp_pos (-(2 * s)), Real.exp_pos (-(2 * β))]

/-- `n - Φ(s) ≥ e^{-2} (n - Φ(α))` for `s ∈ [α, α + 1]`. -/
theorem exp_neg_two_mul_sub_ringMass_le {n α s : ℝ} (hn : 0 < n) (hs : s ≤ α + 1) :
    Real.exp (-2) * (n - ringMass n α) ≤ n - ringMass n s := by
  have e : ∀ u, n - ringMass n u = n / (1 + Real.exp (2 * u)) := by
    intro u
    rw [ringMass_eq]
    have h1 : 0 < 1 + Real.exp (-(2 * u)) := by positivity
    have h2 : 0 < 1 + Real.exp (2 * u) := by positivity
    have hE : Real.exp (-(2 * u)) * Real.exp (2 * u) = 1 := by rw [← Real.exp_add]; simp
    field_simp
    linarith
  rw [e, e, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : Real.exp (-2) * Real.exp (2 * s) ≤ Real.exp (2 * α) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  nlinarith [Real.exp_pos (2 * s), Real.exp_pos (2 * α)]

/-- **Depth on the south polar slab** `(-∞, τ(b)]`: the barycentre lies at distance
`≥ e^{-2} (n - b)/n` below `τ(b)`. -/
theorem slabBary_depth_Iic {n b : ℝ} (hb : 0 < b) (hbn : b < n) :
    Real.exp (-2) * (n - b) / n ≤ ringQuantile n b - slabBary n 0 b := by
  have hn : 0 < n := hb.trans hbn
  set β := ringQuantile n b
  set S := {t | (0 : ℝ) ≤ ringMass n t ∧ ringMass n t ≤ b}
  have hS : MeasurableSet S := measurableSet_slab n 0 b
  obtain ⟨hρi, hρ⟩ := integral_density_slab hn le_rfl hb hbn.le
  have hmi : IntegrableOn (fun s => s * ringDensity n s) S := (integrable_mul_ringDensity n).integrableOn
  have hβ : ringMass n β = b := ringMass_quantile hb hbn
  have hsub : Icc (β - 1) β ⊆ S := fun s hs =>
    ⟨(ringMass_pos hn s).le, hβ ▸ (ringMass_strictMono hn).monotone hs.2⟩
  have hfi' : IntegrableOn (fun s => β * ringDensity n s - s * ringDensity n s) S :=
    (hρi.const_mul β).sub hmi
  have hfi : IntegrableOn (fun s => (β - s) * ringDensity n s) S :=
    hfi'.congr_fun (fun s _ => by ring) hS
  have hnn : ∀ s ∈ S, 0 ≤ (β - s) * ringDensity n s := fun s hs =>
    mul_nonneg (sub_nonneg.2 ((ringMass_le_iff hb hbn s).1 hs.2)) (ringDensity_pos hn s).le
  -- `b (β - c) = ∫_S (β - s) ϱ`
  have hmom : b * (β - slabBary n 0 b) = ∫ s in S, (β - s) * ringDensity n s := by
    have e : (fun s => (β - s) * ringDensity n s) = fun s => β * ringDensity n s - s * ringDensity n s := by
      funext s; ring
    rw [e, integral_sub (hρi.const_mul β) hmi, integral_const_mul, hρ, slabBary]
    simp only [sub_zero]
    field_simp
  -- the lower bound of `ϱ` on `[β - 1, β]`
  set m := 2 / n * (Real.exp (-2) * b) * (n - b)
  have hm : ∀ s ∈ Icc (β - 1) β, m ≤ ringDensity n s := by
    intro s hs
    rw [ringDensity_eq_mass hn.ne']
    have h1 : Real.exp (-2) * b ≤ ringMass n s := hβ ▸ exp_neg_two_mul_ringMass_le hn hs.1
    have h2 : ringMass n s ≤ b := hβ ▸ (ringMass_strictMono hn).monotone hs.2
    have h2n : 0 < 2 / n := by positivity
    have hprod : Real.exp (-2) * b * (n - b) ≤ ringMass n s * (n - ringMass n s) :=
      mul_le_mul h1 (by linarith) (by linarith) (ringMass_pos hn s).le
    calc m = 2 / n * (Real.exp (-2) * b * (n - b)) := by simp only [m]; ring
      _ ≤ 2 / n * (ringMass n s * (n - ringMass n s)) := mul_le_mul_of_nonneg_left hprod h2n.le
      _ = _ := by ring
  have hlow : m / 2 ≤ ∫ s in S, (β - s) * ringDensity n s := by
    calc m / 2 = ∫ s in (β - 1)..β, (β - s) * m := by
          rw [intervalIntegral.integral_mul_const, integral_sub_right]
          ring
      _ ≤ ∫ s in (β - 1)..β, (β - s) * ringDensity n s :=
          intervalIntegral.integral_mono_on (by linarith)
            (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable _ _)
            (((continuous_const.sub continuous_id).mul (continuous_ringDensity n)).intervalIntegrable _ _)
            fun s hs => mul_le_mul_of_nonneg_left (hm s hs) (by linarith [hs.2])
      _ = ∫ s in Icc (β - 1) β, (β - s) * ringDensity n s := by
          rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
      _ ≤ ∫ s in S, (β - s) * ringDensity n s :=
          setIntegral_mono_set hfi (ae_restrict_of_forall_mem hS hnn)
            hsub.eventuallyLE
  rw [← hmom] at hlow
  rw [div_le_iff₀ hn]
  have : m / 2 = Real.exp (-2) * (n - b) * b / n := by simp only [m]; field_simp
  rw [this, div_le_iff₀ hn] at hlow
  exact le_of_mul_le_mul_left
    (by linarith : b * (Real.exp (-2) * (n - b)) ≤ b * ((β - slabBary n 0 b) * n)) hb

/-- **Depth on the north polar slab** `[τ(a), ∞)`: the barycentre lies at distance `≥ e^{-2} a/n`
above `τ(a)`. -/
theorem slabBary_depth_Ici {n a : ℝ} (ha : 0 < a) (han : a < n) :
    Real.exp (-2) * a / n ≤ slabBary n a n - ringQuantile n a := by
  have hn : 0 < n := ha.trans han
  set α := ringQuantile n a
  set S := {t | a ≤ ringMass n t ∧ ringMass n t ≤ n}
  have hS : MeasurableSet S := measurableSet_slab n a n
  obtain ⟨hρi, hρ⟩ := integral_density_slab hn ha.le han le_rfl
  have hmi : IntegrableOn (fun s => s * ringDensity n s) S := (integrable_mul_ringDensity n).integrableOn
  have hα : ringMass n α = a := ringMass_quantile ha han
  have hsub : Icc α (α + 1) ⊆ S := fun s hs =>
    ⟨hα ▸ (ringMass_strictMono hn).monotone hs.1, (ringMass_lt hn s).le⟩
  have hfi' : IntegrableOn (fun s => s * ringDensity n s - α * ringDensity n s) S :=
    hmi.sub (hρi.const_mul α)
  have hfi : IntegrableOn (fun s => (s - α) * ringDensity n s) S :=
    hfi'.congr_fun (fun s _ => by ring) hS
  have hnn : ∀ s ∈ S, 0 ≤ (s - α) * ringDensity n s := fun s hs =>
    mul_nonneg (sub_nonneg.2 ((le_ringMass_iff ha han s).1 hs.1)) (ringDensity_pos hn s).le
  have hmom : (n - a) * (slabBary n a n - α) = ∫ s in S, (s - α) * ringDensity n s := by
    have e : (fun s => (s - α) * ringDensity n s) = fun s => s * ringDensity n s - α * ringDensity n s := by
      funext s; ring
    rw [e, integral_sub hmi (hρi.const_mul α), integral_const_mul, hρ, slabBary]
    have : n - a ≠ 0 := by linarith
    field_simp
    rfl
  set m := 2 / n * a * (Real.exp (-2) * (n - a))
  have hm : ∀ s ∈ Icc α (α + 1), m ≤ ringDensity n s := by
    intro s hs
    rw [ringDensity_eq_mass hn.ne']
    have h1 : a ≤ ringMass n s := hα ▸ (ringMass_strictMono hn).monotone hs.1
    have h2 : Real.exp (-2) * (n - a) ≤ n - ringMass n s := hα ▸ exp_neg_two_mul_sub_ringMass_le hn hs.2
    have : 0 < Real.exp (-2) * (n - a) := mul_pos (Real.exp_pos _) (by linarith)
    have h2n : 0 < 2 / n := by positivity
    have hprod : a * (Real.exp (-2) * (n - a)) ≤ ringMass n s * (n - ringMass n s) :=
      mul_le_mul h1 h2 this.le (ringMass_pos hn s).le
    calc m = 2 / n * (a * (Real.exp (-2) * (n - a))) := by simp only [m]; ring
      _ ≤ 2 / n * (ringMass n s * (n - ringMass n s)) := mul_le_mul_of_nonneg_left hprod h2n.le
      _ = _ := by ring
  have hlow : m / 2 ≤ ∫ s in S, (s - α) * ringDensity n s := by
    calc m / 2 = ∫ s in α..(α + 1), (s - α) * m := by
          rw [intervalIntegral.integral_mul_const, integral_sub_left]
          ring
      _ ≤ ∫ s in α..(α + 1), (s - α) * ringDensity n s :=
          intervalIntegral.integral_mono_on (by linarith)
            (((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable _ _)
            (((continuous_id.sub continuous_const).mul (continuous_ringDensity n)).intervalIntegrable _ _)
            fun s hs => mul_le_mul_of_nonneg_left (hm s hs) (by linarith [hs.1])
      _ = ∫ s in Icc α (α + 1), (s - α) * ringDensity n s := by
          rw [intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]
      _ ≤ ∫ s in S, (s - α) * ringDensity n s :=
          setIntegral_mono_set hfi (ae_restrict_of_forall_mem hS hnn)
            hsub.eventuallyLE
  rw [← hmom] at hlow
  rw [div_le_iff₀ hn]
  have : m / 2 = Real.exp (-2) * a * (n - a) / n := by simp only [m]; field_simp
  rw [this, div_le_iff₀ hn] at hlow
  have hna : 0 < n - a := by linarith
  exact le_of_mul_le_mul_left
    (by linarith : (n - a) * (Real.exp (-2) * a) ≤ (n - a) * ((slabBary n a n - α) * n)) hna

/-! ### (G4) for the ring configuration -/

theorem one_div_56_lt_exp_neg_two : 1 / 56 < Real.exp (-2) := by
  have h : 1 / 2 ≤ Real.exp (-(1 / 2)) := by linarith [Real.add_one_le_exp (-(1 / 2))]
  have e : Real.exp (-2) = Real.exp (-(1 / 2)) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [e]
  have : (1 / 2 : ℝ) ^ 4 ≤ Real.exp (-(1 / 2)) ^ 4 := pow_le_pow_left₀ (by norm_num) h 4
  linarith

/-- Interior rows (`1 ≤ k`, `k + 1 < K`): `3 ≤ N_k ≤ 6 A_k`, `2 N_k ≤ n - A_k`, `A_k < A_{k+1} < n`. -/
theorem ringInterior_facts {n k : ℕ} (hn : 10 ≤ n) (hk1 : 1 ≤ k) (hk : k + 1 < ringK n) :
    (3 : ℝ) ≤ ringN n k ∧ (ringN n k : ℝ) ≤ 6 * (ringState n k).1 ∧
      2 * (ringN n k : ℝ) ≤ n - (ringState n k).1 ∧
      ((ringState n (k + 1)).1 : ℝ) = (ringState n k).1 + ringN n k ∧
      (0 : ℝ) < (ringState n k).1 ∧ ((ringState n (k + 1)).1 : ℝ) < n := by
  have hs := ringStep_spec_at (n := n) (k := k) (by omega)
  have hlt : (ringState n (k + 1)).1 < n := ringState_lt_of_lt_ringK hk
  have hle : (ringState n k).1 ≤ n := by omega
  have h2 := two_mul_ringN_le hk
  have hN3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN hn k (by omega)
  have hA3 : (3 : ℝ) ≤ (ringState n k).1 := by exact_mod_cast three_le_ringState hn hk1 (by omega)
  obtain ⟨-, hhi⟩ := ringN_mem_Icc hn hk1 hk
  have hsq := ringTarget_sq_le_left n (ringState n k).1 hle
  have hc := two_sqrt_three_pi_lt
  have hx0 := ringTarget_nonneg n (ringState n k).1
  refine ⟨hN3, ?_, ?_, by rw [hs.1]; push_cast; ring, by linarith, by exact_mod_cast hlt⟩
  · set N := (ringN n k : ℝ)
    set x := ringTarget n (ringState n k).1
    have : N ^ 2 ≤ 25 / 16 * x ^ 2 := by
      have := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ N) hhi 2; linarith
    linarith [mul_le_mul_of_nonneg_right hc.le (by linarith : (0 : ℝ) ≤ (ringState n k).1),
      mul_le_mul_of_nonneg_right hN3 (by linarith : (0 : ℝ) ≤ N)]
  · have hna : ((n - (ringState n k).1 : ℕ) : ℝ) = n - (ringState n k).1 := by push_cast [hle]; ring
    rw [← hna]; exact_mod_cast h2

/-- **(G4)**, upper end: for `n ≥ 102` and every non-final row, `t_k + (3/112)/N_k ≤ τ(A_{k+1})`. -/
theorem ringHeight_depth_right {n k : ℕ} (hn : 102 ≤ n) (hk : k + 1 < ringK n) :
    ringHeight n k + 3 / (112 * ringN n k) ≤ ringQuantile n (ringState n (k + 1)).1 := by
  have hN3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN (by omega) k (by omega)
  have hc0 : 3 / (112 * (ringN n k : ℝ)) ≤ 1 / 112 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have he := one_div_56_lt_exp_neg_two
  rw [ringHeight_eq_slabBary (by omega)]
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have hs := ringStep_spec_at (n := n) (k := 0) (by omega)
    have hlt : (ringState n 1).1 < n := ringState_lt_of_lt_ringK hk
    have h2 := two_mul_ringN_le hk
    have h0 : (ringState n 0).1 = 0 := rfl
    have hb : (ringState n 1).1 = ringN n 0 := by rw [hs.1, h0]; ring
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hbpos : (0 : ℝ) < (ringState n 1).1 := by rw [hb]; linarith
    have hd := slabBary_depth_Iic (n := (n : ℝ)) hbpos (by exact_mod_cast hlt)
    rw [h0, Nat.cast_zero]
    have h2' : 2 * ((ringState n 1).1 : ℝ) ≤ n := by
      rw [hb]; rw [h0] at h2; exact_mod_cast (by omega : 2 * ringN n 0 ≤ n)
    have : 1 / 112 ≤ Real.exp (-2) * (n - (ringState n 1).1) / n := by
      rw [le_div_iff₀ hn']
      linarith [mul_le_mul_of_nonneg_right he.le (by linarith : (0 : ℝ) ≤ n - (ringState n 1).1)]
    linarith
  · obtain ⟨hN3, hN6, h2, hb, ha0, hbn⟩ := ringInterior_facts (by omega) hk1 hk
    obtain ⟨hL, -⟩ := ringSlab_length_mem (by omega) hk1 hk
    rw [hb] at hbn hL ⊢
    obtain ⟨-, hd⟩ := slabBary_depth ha0 (by linarith) hbn
    set a := ((ringState n k).1 : ℝ)
    set N := (ringN n k : ℝ)
    set L := ringQuantile n (a + N) - ringQuantile n a
    have hN0 : 0 < N := by linarith
    have hr : a * (n - (a + N)) * 14 ≥ (a + N) * (n - a) := by
      linarith [mul_le_mul_of_nonneg_right hN6 (by linarith : (0 : ℝ) ≤ n - a),
        mul_le_mul_of_nonneg_left h2 ha0.le]
    have hpos : 0 < (a + N) * (n - a) := mul_pos (by linarith) (by linarith)
    have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
    have key : 3 / (112 * N) ≤ L * (a * (n - (a + N))) / (2 * ((a + N) * (n - a))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hL' : 3 ≤ L * (4 * N) := by rwa [div_le_iff₀ (by positivity)] at hL
      linarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr.le hL0.le) hN0.le,
        mul_le_mul_of_nonneg_right hL' hpos.le]
    linarith

/-- **(G4)**, lower end: for `n ≥ 102` and every row `k ≥ 1`, `τ(A_k) + (3/112)/N_k ≤ t_k`. -/
theorem ringHeight_depth_left {n k : ℕ} (hn : 102 ≤ n) (hk1 : 1 ≤ k) (hk : k < ringK n) :
    ringQuantile n (ringState n k).1 + 3 / (112 * ringN n k) ≤ ringHeight n k := by
  have hN3 : (3 : ℝ) ≤ ringN n k := by exact_mod_cast three_le_ringN (by omega) k hk
  have hc0 : 3 / (112 * (ringN n k : ℝ)) ≤ 1 / 112 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have he := one_div_56_lt_exp_neg_two
  rw [ringHeight_eq_slabBary hk]
  rcases lt_or_eq_of_le (show k + 1 ≤ ringK n by omega) with hk' | hk'
  · obtain ⟨hN3, hN6, h2, hb, ha0, hbn⟩ := ringInterior_facts (by omega) hk1 hk'
    obtain ⟨hL, -⟩ := ringSlab_length_mem (by omega) hk1 hk'
    rw [hb] at hbn hL ⊢
    obtain ⟨hd, -⟩ := slabBary_depth ha0 (by linarith) hbn
    set a := ((ringState n k).1 : ℝ)
    set N := (ringN n k : ℝ)
    set L := ringQuantile n (a + N) - ringQuantile n a
    have hN0 : 0 < N := by linarith
    have hr : a * (n - (a + N)) * 14 ≥ (a + N) * (n - a) := by
      linarith [mul_le_mul_of_nonneg_right hN6 (by linarith : (0 : ℝ) ≤ n - a),
        mul_le_mul_of_nonneg_left h2 ha0.le]
    have hpos : 0 < (a + N) * (n - a) := mul_pos (by linarith) (by linarith)
    have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
    have key : 3 / (112 * N) ≤ L * (a * (n - (a + N))) / (2 * ((a + N) * (n - a))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hL' : 3 ≤ L * (4 * N) := by rwa [div_le_iff₀ (by positivity)] at hL
      linarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr.le hL0.le) hN0.le,
        mul_le_mul_of_nonneg_right hL' hpos.le]
    linarith
  · -- the last row
    have hs := ringStep_spec_at hk
    have hfin : (ringState n (k + 1)).1 = n := by rw [hk']; exact ringState_ringK n
    have h51 := (hs.2.2.1 hfin).1
    have hlt : (ringState n k).1 < n := ringState_lt_of_lt_ringK hk
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hA : (n : ℝ) ≤ 2 * (ringState n k).1 := by exact_mod_cast (by omega : n ≤ 2 * (ringState n k).1)
    have ha0 : (0 : ℝ) < (ringState n k).1 := by linarith
    rw [hfin]
    have hd := slabBary_depth_Ici (n := (n : ℝ)) ha0 (by exact_mod_cast hlt)
    have : 1 / 112 ≤ Real.exp (-2) * (ringState n k).1 / n := by
      rw [le_div_iff₀ hn']; linarith [mul_le_mul_of_nonneg_right he.le ha0.le]
    linarith

end Sphere

end SandierSerfaty

end
