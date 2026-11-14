/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.EnergyIdentity
public import SandierSerfaty.Calibration.AngleDensity
public import SandierSerfaty.Calibration.RadialAdmissible
public import SandierSerfaty.Calibration.Exterior
public import SandierSerfaty.Calibration.Stationarity
public import SandierSerfaty.Dual.SignedEndpoints
public import SandierSerfaty.Dual.SectorToEnergy

/-!
# The square-torus bound reduced to the certificate (`mul_triangularEnergy_le_torusEnergy`)

`torusBound_of_certificateGoal : CertificateGoal → ∀ n ≥ 2, ∀ a (distinct classes), n * triangularEnergy ≤
torusEnergy (squareLattice n) a` has *exactly* the conclusion of the square-torus bound
`mul_triangularEnergy_le_torusEnergy` (paper Theorem 1.2). The hypothesis `CertificateGoal` is the finite,
numerical content of the paper's computation (paper §6); it is proved in `CertData.CertificateGoal`.

## The route (everything except the certificate is proved here or in the modules imported above)

1. `positive_tail`: from the two sign fields and the exterior formula (`Calibration.exterior_formula`),
   `G d s > 0` whenever `d > 0` and `t = √(d² + s²) ≥ l` (paper `comp:positive-tail`).
2. `primitive_bound`: `K ≤ 2 g_d(x)` for all `d ≥ b`, `x ≥ 0` — on the compact box `𝒟` from the two
   region fields, for `x ≥ .65` because `G > 0` there (`g_d` increasing), for `d ≥ .697` because `G > 0` on
   `s ≥ 0` (`g_d ≥ 0`); paper `comp:scalar` proof.
3. `negative_part`: `∫₀^∞ max {0, -G(d, s)} ≤ -K` for `d ≥ b`: the integrand vanishes for `s ≥ .65` and for
   `d ≥ .697` (positive tail); on `[0, .65]` it is the `negative` field.
4. `signed_endpoints` (`Dual/SignedEndpoints.lean`) turns 2 and 3 plus evenness of `G` into
   `K ≤ g_d(d tan α) + g_d(d tan β)`; `sectorBound_of_primitive_bound` (`Calibration/AngleDensity.lean`) gives
   `SectorBound radialData b K λ μ` (`dual:sector-input`);
5. `mul_triangularEnergy_le_torusEnergy_of_sectorBound` (`Dual/SectorToEnergy.lean`) with `d₀ = b ≤ d_*`
   (`b_lt_dStar`), `radialData_isAdmissible`, `K ≤ 0` and `Calibration.energy_identity`
   (`6K + λ + 2πμ = W_△`) gives the statement of the square-torus bound.

## The fields of `CertificateGoal` and the certificate assertions A1–A10

The assertions A1–A10 number the finite checks that the certificate performs (the modules under
`SandierSerfaty/Certificate`). Every field is a statement about the explicit exact functions of paper §4 (`Calibration.G`, `Calibration.g`,
`Calibration.K`, `Calibration.lam`, `Calibration.B`, `Calibration.f`) on a compact set or at one point: a
finite/numerical claim, not a form of the square-torus bound. Paper `comp:scalar` is the *conjunction* of these fields (with the
derived facts of steps 1–3).

| field | paper | certificate assertions | proved in |
|---|---|---|---|
| `f_l_pos` : `0 < f l` | `comp:tail-signs`, `comp:positive-tail` | A4 (enclosures of `B l`, `f₀ l`), A5 (enclosure of `λ`, `μ`), A6 | `Certificate.Query.ExteriorSigns` (lookup, `Fx`/`IV` evaluation, A4–A6) |
| `slope_pos` : `0 < -π B l - λ/2` | same | A4, A5, A6 | `Certificate.Query.ExteriorSigns` |
| `outer` : `K ≤ 2 g_d(x)` on `𝒟 ∖ int 𝒟₀` | `comp:outer-grid`, `comp:outer-assertion` | A7 (derivative bounds `L₁…L₄`), A8 (≈4.58 M value-`G` outer nodes), plus A3 (table), A2/`FiniteCore` and the §5 tails | `Certificate.Box` (`outer_bound`; midpoint and bilinear lemmas, `δ_G`) |
| `inner` : `K ≤ 2 g_d(x)` on `𝒟₀` | `comp:hessian`, `comp:inner-conclusion` | A10 (Hessian cells), A7; stationarity `Calibration.stationarity` (on main) | `Certificate.Box` (`inner_bound`; `φ = 2g` is `C²`, 1-D Taylor along segments) |
| `negative` : `∫₀^{.65} max {0,-G(d,·)} ≤ -K` for `d ∈ [b, .697]` | `comp:negative-part`, `comp:negative-assertion` | A9 (≈ fused with A8), A5 (`K`), A7 | `Certificate.Box` (`negative_part`) |

Not a field, by design:

* `K < 0` (A6, `comp:tail-signs`). It is proved by the certificate anyway, but this module needs only
  `K ≤ 0`, which follows from `outer` at `(b, 0)`.
* `FiniteCore` (A2) and the enclosures A1, A3–A5. They are the certificate's *internal* route to the exact
  fields above (`Tails.uniform_error_of_finiteCore` transfers the finite-mode enclosures to the exact
  infinite-mode functions), so they do not appear in the interface. The reduction consumes the exact statements only.
* The side facts `l < .697`, `√(b² + .65²) > l`, `b < d_*`, `(p, x₀) ∈ int 𝒟₀`: proved by `norm_num`
  (`Calibration/Constants.lean`, `RadialAdmissible.lean`).
* `outer` and `inner` use the non-strict `≤`: the paper proves strict `>` outside `int 𝒟₀` and `≥ K` on `𝒟₀`;
  the weaker form is all the geometry needs.
-/

open MeasureTheory Set Real

public section

namespace SandierSerfaty

namespace Assembly

open Calibration

/-- **The certificate's obligations** (paper §7, `comp:scalar` in region-split form; assertions A1–A10). A `Prop`
structure of finite/numerical statements about the exact calibration objects of paper §4; see the module
docstring for the field ↔ assertion ↔ module table. -/
structure CertificateGoal : Prop where
  /-- Exterior sign (A4–A6, `comp:tail-signs`): `f(l) = f₀(l) - λ l²/2 - μ > 0`.
  Proved from the enclosures of `f₀(l)`, `λ`, `μ`. -/
  f_l_pos : 0 < f l
  /-- Exterior slope sign (A4–A6, `comp:tail-signs`): `-π B(l) - λ/2 > 0`.
  Proved from the enclosures of `B(l)` and `λ`. -/
  slope_pos : 0 < -Real.pi * B l - lam / 2
  /-- Outer region (A7–A8, `comp:outer-assertion`): `2 g_d(x) ≥ K` on
  `𝒟 ∖ int 𝒟₀`, `𝒟 = [b, .697] × [0, .65]`, `𝒟₀ = [.52528, .5493] × [.2942, .32621]`
  (`Calibration.boxD`, `Calibration.boxD₀`). -/
  outer : ∀ q ∈ boxD \ interior boxD₀, K ≤ 2 * g q.1 q.2
  /-- Inner region (A10, `comp:inner-conclusion`): `2 g_d(x) ≥ K` on `𝒟₀`
  (Hessian positivity plus `Calibration.stationarity`). -/
  inner : ∀ q ∈ boxD₀, K ≤ 2 * g q.1 q.2
  /-- Negative part (A9, `comp:negative-assertion`):
  `∫₀^{.65} max {0, -G(d, s)} ds ≤ -K` for `b ≤ d ≤ .697`. -/
  negative : ∀ d ∈ Icc b (697 / 1000 : ℝ),
    ∫ s in (0 : ℝ)..(65 / 100 : ℝ), max 0 (-G d s) ≤ -K

namespace CertificateGoal

variable (hC : CertificateGoal)
include hC

/-- **`comp:positive-tail`**: `G(d, s) > 0` if `t = √(d² + s²) ≥ l`. -/
theorem positive_tail {d s : ℝ} (hd : 0 < d) (ht : l ≤ tt d s) : 0 < G d s := by
  have hl := l_pos'
  have ht0 : 0 < tt d s := lt_of_lt_of_le hl ht
  obtain ⟨he, hf₀⟩ := exterior_formula ht
  have hf : f (tt d s) = f l + (-Real.pi * B l - lam / 2) * (tt d s ^ 2 - l ^ 2) := by
    unfold f
    rw [hf₀]
    ring
  have hsq : 0 ≤ tt d s ^ 2 - l ^ 2 := by nlinarith
  have h1 : 0 < f (tt d s) := by
    rw [hf]
    linarith [hC.f_l_pos, hC.slope_pos, mul_nonneg hC.slope_pos.le hsq]
  unfold G
  rw [he]
  simpa using mul_pos (div_pos hd (pow_pos ht0 2)) h1

/-- `K ≤ 0` (follows from `outer` at `(b, 0)`, where `g_b(0) = 0`). -/
theorem K_le_zero : K ≤ 0 := by
  have hq : ((b, 0) : ℝ × ℝ) ∈ boxD \ interior boxD₀ := by
    refine ⟨⟨⟨le_rfl, by unfold b; norm_num⟩, ⟨le_rfl, by norm_num⟩⟩, ?_⟩
    intro h
    have := interior_subset h
    unfold boxD₀ at this
    have h1 := this.1.1
    unfold b at h1
    norm_num at h1
  have := hC.outer _ hq
  simpa [g] using this

/-- `G d s > 0` whenever `d ≥ b` and `s ≥ .65` (`√(b² + .65²) > l`), or `d ≥ .697`, `s` arbitrary. -/
theorem G_pos_of {d s : ℝ} (hd : b ≤ d)
    (h : 65 / 100 ≤ |s| ∨ 697 / 1000 ≤ d) : 0 < G d s := by
  have hd0 : 0 < d := lt_of_lt_of_le b_pos hd
  refine hC.positive_tail hd0 ?_
  unfold tt
  rcases h with h | h
  · refine l_lt_sqrt.le.trans (Real.sqrt_le_sqrt ?_)
    have h1 : (65 / 100 : ℝ) ^ 2 ≤ s ^ 2 := by
      rw [← sq_abs s]; exact pow_le_pow_left₀ (by norm_num) h 2
    have h2 : b ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ b_pos.le hd 2
    linarith
  · have hd2 : (697 / 1000 : ℝ) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
    exact l_lt.le.trans ((Real.le_sqrt_of_sq_le (by linarith [sq_nonneg s]) :
      (697 / 1000 : ℝ) ≤ √(d ^ 2 + s ^ 2)))

/-- `K ≤ 2 g_d(x)` on the compact box `𝒟` (regions `outer` and `inner`). -/
theorem box_bound {d x : ℝ} (hd : b ≤ d) (hd' : d ≤ 697 / 1000) (hx : 0 ≤ x) (hx' : x ≤ 65 / 100) :
    K ≤ 2 * g d x := by
  have hq : ((d, x) : ℝ × ℝ) ∈ boxD := ⟨⟨hd, hd'⟩, ⟨hx, hx'⟩⟩
  by_cases hi : ((d, x) : ℝ × ℝ) ∈ interior boxD₀
  · exact hC.inner _ (interior_subset hi)
  · exact hC.outer _ ⟨hq, hi⟩

/-- **The primitive bound** `2 g_d(x) ≥ K` for all `d ≥ b`, `x ≥ 0` (`comp:scalar`). -/
theorem primitive_bound {d x : ℝ} (hd : b ≤ d) (hx : 0 ≤ x) : K ≤ 2 * g d x := by
  have hd0 : 0 < d := lt_of_lt_of_le b_pos hd
  have hcont := continuous_G hd0
  by_cases h1 : 697 / 1000 ≤ d
  · have : 0 ≤ g d x := intervalIntegral.integral_nonneg hx fun s _ =>
      (hC.G_pos_of hd (Or.inr h1)).le
    linarith [hC.K_le_zero]
  · push Not at h1
    by_cases h2 : x ≤ 65 / 100
    · exact hC.box_bound hd h1.le hx h2
    · push Not at h2
      have hsplit : g d x = g d (65 / 100) + ∫ s in (65 / 100 : ℝ)..x, G d s := by
        unfold g
        rw [intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
          (hcont.intervalIntegrable _ _)]
      have hnn : 0 ≤ ∫ s in (65 / 100 : ℝ)..x, G d s :=
        intervalIntegral.integral_nonneg h2.le fun s hs =>
          (hC.G_pos_of hd (Or.inl (by rw [abs_of_nonneg (by linarith [hs.1])]; exact hs.1))).le
      have := hC.box_bound hd h1.le (by norm_num) le_rfl
      linarith

/-- **The negative-part bound** `∫₀^∞ max {0, -G(d, s)} ds ≤ -K` for `d ≥ b`, as the `lintegral` of
`Dual.signed_endpoints`. -/
theorem negative_part {d : ℝ} (hd : b ≤ d) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max 0 (-G d s)) ≤ ENNReal.ofReal (-K) := by
  have hd0 : 0 < d := lt_of_lt_of_le b_pos hd
  have hcont : Continuous fun s => max 0 (-G d s) := continuous_const.max (continuous_G hd0).neg
  have hzero : ∀ s, 0 < G d s → ENNReal.ofReal (max 0 (-G d s)) = 0 := fun s hs => by
    rw [max_eq_left (by linarith)]; simp
  by_cases h1 : 697 / 1000 ≤ d
  · have : ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max 0 (-G d s)) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0)
        (fun s _ => hzero s (hC.G_pos_of hd (Or.inr h1)))]
      simp
    rw [this]; exact zero_le
  · push Not at h1
    have hsub : Ioi (0 : ℝ) ⊆ Ioc 0 (65 / 100) ∪ Ioi (65 / 100) := by
      intro s hs
      rcases le_or_gt s (65 / 100) with h | h
      · exact Or.inl ⟨hs, h⟩
      · exact Or.inr h
    have hI : ∫⁻ s in Ioi (65 / 100 : ℝ), ENNReal.ofReal (max 0 (-G d s)) = 0 := by
      rw [setLIntegral_congr_fun measurableSet_Ioi (g := fun _ => 0) (fun s hs => by
        have hs' : (65 / 100 : ℝ) < s := hs
        exact hzero s (hC.G_pos_of hd (Or.inl (by rw [abs_of_nonneg (by linarith)]; exact hs'.le))))]
      simp
    have hJ : ∫⁻ s in Ioc (0 : ℝ) (65 / 100), ENNReal.ofReal (max 0 (-G d s)) =
        ENNReal.ofReal (∫ s in (0 : ℝ)..(65 / 100), max 0 (-G d s)) := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Ioc)
          (Filter.Eventually.of_forall fun s => le_max_left _ _)]
    calc ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (max 0 (-G d s))
        ≤ ∫⁻ s in Ioc (0 : ℝ) (65 / 100) ∪ Ioi (65 / 100), ENNReal.ofReal (max 0 (-G d s)) :=
          lintegral_mono_set hsub
      _ ≤ (∫⁻ s in Ioc (0 : ℝ) (65 / 100), ENNReal.ofReal (max 0 (-G d s))) +
            ∫⁻ s in Ioi (65 / 100 : ℝ), ENNReal.ofReal (max 0 (-G d s)) := lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal (-K) := by
          rw [hI, add_zero, hJ]
          exact ENNReal.ofReal_le_ofReal (hC.negative d ⟨hd, h1.le⟩)

/-- **The sector input** `(dual:sector-input)` at `d₀ = b` from the certificate. -/
theorem sectorBound : Dual.SectorBound radialData b K lam mu := by
  refine sectorBound_of_primitive_bound b_pos fun d hd α β hα hβ hαβ => ?_
  exact Dual.signed_endpoints (G := G) b_pos (fun d _ s => G_neg d s)
    (fun d hd => (continuous_G (lt_of_lt_of_le b_pos hd)).locallyIntegrable)
    (fun d hd x hx => hC.primitive_bound hd hx) (fun d hd => hC.negative_part hd) hd hα hβ hαβ

end CertificateGoal

/-- **The square-torus bound (paper Theorem 1.2), conditional on the certificate.** The conclusion is exactly
that of `SandierSerfaty.mul_triangularEnergy_le_torusEnergy`; the only hypothesis beyond its own is
`CertificateGoal`. -/
theorem torusBound_of_certificateGoal (hC : CertificateGoal) (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    n * triangularEnergy ≤ torusEnergy (squareLattice n) a :=
  Dual.mul_triangularEnergy_le_torusEnergy_of_sectorBound b_pos b_lt_dStar.le
    (radialData_isAdmissible b_pos) hC.K_le_zero hC.sectorBound energy_identity n hn a ha

end Assembly

end SandierSerfaty

end
