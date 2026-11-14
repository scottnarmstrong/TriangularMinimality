/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.GreenSeries
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential

/-!
# `cal:green-expansion`: the expansion of the triangular Green function at a lattice point

Paper Lemma `cal:green-expansion`, equation `cal:green-series`. The mean-zero
triangular Green function `h_△ = torusPotential Λ_△ (fun _ : Fin 1 ↦ 0)` satisfies, for `0 < ‖z‖ < a`,
`h_△ z = - log ‖z‖ + C_△ + π ‖z‖² / 2 + ∑_{m ≥ 1} c_m Re (z^{6 m})`,
where `c_m = Cal.coeff m` and `C_△ = Cal.CTri = torusRobin Λ_△` is the regular part at the origin.

* `Cal.green_expansion`: the expansion, as a `HasSum` and as a `tsum`;
* `Cal.tendsto_hTri_add_log`: `h_△ z + log ‖z‖ → C_△` as `z → 0` (so `C_△` is the regular part);
* `Cal.triPair_G_eq_zero_of_not_dvd`, `Cal.triPair_G_im`: `G_n(Λ_△) = 0` unless `6 ∣ n`, and `G_n(Λ_△)` is
  real; so `coeff m` is the whole coefficient.

The convergence statement is `|z| < a` (the paper's "away from
`|z| = a`" should read "on `|z| < a`"). Locally uniform convergence with all derivatives is
`GreenSeriesDeriv.lean`.

## Proof (the paper's, made holomorphic)

In the coordinate `w = z / a`, with `Ĝ = thetaGreen0 ρ` the theta Green function of `ℤ + ℤρ`
(`ρ = e^{πi/3}`; `h_△ (a w) = Ĝ w - c` off the lattice, `GreenSymmetry.lean`):

1. `θ(w) = w q(w)`, `q` zero-free on the unit disc, `q = q 0 · e^M` there, so
   `Ĝ w = - log ‖w‖ + C₀ + (π / (2 Im ρ)) ‖w‖² + Re F w` with `F` holomorphic on the unit disc
   (`GreenLog.lean`);
2. `(q'/q)'` and `℘` differ by a constant, by Liouville (`GreenLiouville.lean`);
3. rotation symmetry `Ĝ (ρ w) = Ĝ w` kills `F'(0)` and `F''(0)`, hence the constant, so `F'' = ℘[L - 0]`;
   the Taylor coefficients of `F` are `G_n / n` (`GreenSeries.lean`); and `G_n = 0` unless `6 ∣ n`.
-/

open Filter Topology Metric Complex

public section

namespace SandierSerfaty

namespace Calibration

open ClosedForm Torus

/-- The triangular Green function `h_△`: the torus potential of the triangular lattice with one charge
at the origin. -/
@[expose] noncomputable def hTri : ℂ → ℝ :=
  torusPotential triangularLattice (fun _ : Fin 1 => (0 : ℂ))

/-- The regular part `C_△ = lim_{z → 0} (h_△ z + log ‖z‖)` of the triangular Green function (the
Robin constant of `Λ_△`). -/
@[expose] noncomputable def CTri : ℝ := torusRobin triangularLattice

theorem hTri_eq_torusGreen {z : ℂ} (hz : z ∉ triangularLattice) :
    hTri z = torusGreen triangularLattice z := by
  have hcov : ZLattice.covolume triangularLattice = ((1 : ℕ) : ℝ) := by
    simpa using Torus.covolume_triangularLattice
  have := Torus.torusPotential_apply (a := fun _ : Fin 1 => (0 : ℂ)) hcov
    (fun i j _ => Subsingleton.elim i j) (x := z) (by intro i; simpa [sub_zero] using hz)
  simpa [hTri] using this

theorem div_mem_hexLattice_of_mem {z : ℂ} (hz : z ∈ triangularLattice) :
    z / (a : ℂ) ∈ hexPair.lattice := by
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  rw [← triPair_lattice, PeriodPair.mem_lattice, triPair_ω₁, triPair_ω₂] at hz
  obtain ⟨m, n, rfl⟩ := hz
  refine mem_hexPair_lattice.2 ⟨n, m, ?_⟩
  field_simp
  ring

/-- A point of `0 < ‖z‖ < a` is not a lattice point (the nearest lattice points are at distance `a`). -/
theorem notMem_triangularLattice_of_norm_lt {z : ℂ} (hz0 : z ≠ 0) (hza : ‖z‖ < a) :
    z ∉ triangularLattice := by
  intro h
  have h1 := div_mem_hexLattice_of_mem h
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  have hw1 : ‖z / (a : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg a_pos.le, div_lt_one a_pos]
    exact hza
  exact notMem_hexLattice_of_norm_lt_one hw1 (div_ne_zero hz0 ha) h1

/-! ### The Eisenstein sums of the triangular lattice -/

/-- `G_n(Λ_△)` is real. -/
theorem triPair_G_im (n : ℕ) : (triPair.G n).im = 0 := by
  rw [triPair_G]
  have hr : ((a : ℂ) ^ n)⁻¹ = (((a ^ n)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hr, Complex.im_ofReal_mul, hexG_im, mul_zero]

theorem triPair_G_eq_ofReal (n : ℕ) : triPair.G n = ((triPair.G n).re : ℂ) :=
  Complex.ext rfl (by simpa using triPair_G_im n)

/-- The coefficient `c_m` is the whole coefficient: `G_{6m}(Λ_△) = 6m c_m`. -/
theorem triPair_G_six_mul (m : ℕ) (hm : 0 < m) :
    triPair.G (6 * m) = (((6 * m : ℕ) : ℝ) * coeff m : ℝ) := by
  have h6 : ((6 * m : ℕ) : ℝ) ≠ 0 := by positivity
  rw [triPair_G_eq_ofReal (6 * m)]
  congr 1
  unfold coeff
  field_simp

/-! ### The expansion -/

theorem pi_div_two_mul_sq (x : ℝ) :
    Real.pi / (2 * rho.im) * (x / a) ^ 2 = Real.pi * x ^ 2 / 2 := by
  have h3 := sqrt_three_pos
  rw [div_pow, a_sq, rho_im]
  field_simp

theorem re_green_term (n : ℕ) (w : ℂ) :
    (hexPair.G n / (n : ℂ) * w ^ n).re = (hexPair.G n).re / n * (w ^ n).re := by
  have hG' : hexPair.G n = ((hexPair.G n).re : ℂ) := Complex.ext rfl (by simpa using hexG_im _)
  rw [hG', ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.re_ofReal_mul]
  simp

theorem coeff_term (m : ℕ) (z : ℂ) :
    coeff (m + 1) * (z ^ (6 * (m + 1))).re =
      (hexPair.G (6 * (m + 1))).re / ((6 * (m + 1) : ℕ) : ℝ) *
        ((z / (a : ℂ)) ^ (6 * (m + 1))).re := by
  set n := 6 * (m + 1) with hn
  have ha : a ^ n ≠ 0 := (pow_pos a_pos n).ne'
  have h1 : (triPair.G n).re = (a ^ n)⁻¹ * (hexPair.G n).re := by
    rw [triPair_G]
    have hr : ((a : ℂ) ^ n)⁻¹ = (((a ^ n)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [hr, Complex.re_ofReal_mul]
  have h2 : ((z / (a : ℂ)) ^ n).re = (z ^ n).re / a ^ n := by
    rw [div_pow, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  unfold coeff
  rw [← hn, h1, h2]
  have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by rw [hn]; positivity
  field_simp

theorem tendsto_greenOne_sub_const {c : ℝ} {C : ℝ}
    (hCt : Tendsto (fun w : ℂ => thetaGreen0 rho w + Real.log ‖w‖) (𝓝[≠] 0) (𝓝 C))
    (hc : ∀ z, z ∉ triangularLattice → torusGreen triangularLattice z = greenOne (a : ℂ) rho z - c) :
    Tendsto (fun z => torusGreen triangularLattice z + Real.log ‖z‖) (𝓝[≠] 0)
      (𝓝 (C + Real.log a - c)) := by
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  have hmap : Tendsto (fun z : ℂ => z / (a : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => z / (a : ℂ)) (𝓝 0) (𝓝 (0 / (a : ℂ))) :=
        (continuous_id.div_const _).tendsto 0
      rw [zero_div] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa [ha] using hz
  have h1 := (hCt.comp hmap).add_const (Real.log a - c)
  have h2 : C + (Real.log a - c) = C + Real.log a - c := by ring
  rw [h2] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_notMem_lattice triangularLattice, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  simp only [Function.comp]
  rw [hc z hz]
  have : Real.log ‖z / (a : ℂ)‖ = Real.log ‖z‖ - Real.log a := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg a_pos.le,
      Real.log_div (norm_ne_zero_iff.2 hz0') a_pos.ne']
  rw [this]
  simp only [greenOne]
  ring

/-- **`cal:green-expansion`**, series form: for `0 < ‖z‖ < a` the series
`∑_{m ≥ 1} c_m Re (z^{6 m})` sums to `h_△ z + log ‖z‖ - C_△ - π ‖z‖² / 2`. -/
theorem green_expansion_hasSum {z : ℂ} (hz0 : z ≠ 0) (hza : ‖z‖ < a) :
    HasSum (fun m : ℕ => coeff (m + 1) * (z ^ (6 * (m + 1))).re)
      (hTri z + Real.log ‖z‖ - CTri - Real.pi * ‖z‖ ^ 2 / 2) := by
  obtain ⟨c, hc⟩ := exists_torusGreen_eq_greenOne_sub
  obtain ⟨C, Φ, hCt, -, hΦs, hΦre⟩ := exists_green_series
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast a_pos.ne'
  have hCTri : CTri = C + Real.log a - c :=
    tendsto_nhds_unique (tendsto_torusGreen_add_log triangularLattice)
      (tendsto_greenOne_sub_const hCt hc)
  have hnorm : ‖z / (a : ℂ)‖ = ‖z‖ / a := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg a_pos.le]
  have hw : z / (a : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, hnorm, div_lt_one a_pos]; exact hza
  have hw0 : z / (a : ℂ) ≠ 0 := div_ne_zero hz0 ha
  have hz : z ∉ triangularLattice := notMem_triangularLattice_of_norm_lt hz0 hza
  have hs : HasSum (fun m : ℕ => (hexPair.G (6 * (m + 1))).re / ((6 * (m + 1) : ℕ) : ℝ) *
      ((z / (a : ℂ)) ^ (6 * (m + 1))).re) (Φ (z / (a : ℂ))).re := by
    have := Complex.reCLM.hasSum (hΦs _ hw)
    convert this using 1
    · funext m
      simp only [Complex.reCLM_apply]
      exact (re_green_term _ _).symm
    · simp
  have hlog : Real.log ‖z / (a : ℂ)‖ = Real.log ‖z‖ - Real.log a := by
    rw [hnorm, Real.log_div (norm_ne_zero_iff.2 hz0) a_pos.ne']
  have hh : hTri z = thetaGreen0 rho (z / (a : ℂ)) - c := by
    rw [hTri_eq_torusGreen hz, hc z hz]; rfl
  have hq := pi_div_two_mul_sq ‖z‖
  convert hs using 1
  · funext m
    exact coeff_term m z
  · have e := hΦre _ hw hw0
    rw [hlog] at e
    rw [hnorm, hq] at e
    rw [hh, hCTri]
    linarith

/-- **`cal:green-expansion`**: for `0 < ‖z‖ < a`,
`h_△ z = - log ‖z‖ + C_△ + π ‖z‖² / 2 + ∑_{m ≥ 1} c_m Re (z^{6 m})`. -/
theorem green_expansion {z : ℂ} (hz0 : z ≠ 0) (hza : ‖z‖ < a) :
    hTri z = -Real.log ‖z‖ + CTri + Real.pi * ‖z‖ ^ 2 / 2 +
      ∑' m : ℕ, coeff (m + 1) * (z ^ (6 * (m + 1))).re := by
  have := (green_expansion_hasSum hz0 hza).tsum_eq
  linarith

end Calibration

end SandierSerfaty

end
