/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Analysis.HarmonicMax
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Harmonic functions with removable (bounded) singularities: the maximum principle across punctures

Mathlib has no removable-singularity theorem for harmonic functions, and no Dirichlet problem on
disks (the Poisson integral is not known to attain its boundary values). Without a Dirichlet solver,
the existence of a harmonic extension across a puncture is out of reach, but the *maximum principle*
across a puncture needs only the weak maximum principle on annuli and a logarithmic barrier
(`SandierSerfaty.Analysis.HarmonicMax`). This is what the uniqueness of the torus potential uses.

* `exists_ne_eq_of_isMaxOn_puncture`: if `v` is continuous on a disk, harmonic off the center `c`, and
  has its maximum over the disk at `c`, then `v` attains this maximum at another point of the disk.
* `eq_of_isMaxOn_of_harmonicOnNhd_compl`: a continuous function on `ℂ`, harmonic off a closed countable
  set `P` of isolated points, that attains its maximum is constant.
-/

open Metric Real Set Filter Topology

public section

namespace InnerProductSpace

/-- `log ‖z - c‖` is harmonic at every `z ≠ c`. -/
theorem harmonicAt_log_norm_sub {c z : ℂ} (hz : z ≠ c) :
    HarmonicAt (fun y : ℂ => Real.log ‖y - c‖) z :=
  AnalyticAt.harmonicAt_log_norm (f := fun y : ℂ => y - c) (by fun_prop) (sub_ne_zero.2 hz)

/-- A comparison on an annulus: with `v ≤ v c` on the disk, `v z + (δ / D) (log ‖z - c‖ - log ε)` is
bounded by `v c` on the annulus `ε < ‖z - c‖ < r`, if `v ≤ v c - δ` on the outer circle. -/
private theorem annulus_comparison {v : ℂ → ℝ} {c : ℂ} {ρ r ε δ M m : ℝ}
    (hr : r < ρ) (hε : 0 < ε) (hεr : ε < r)
    (hv : ContinuousOn v (ball c ρ)) (hh : HarmonicOnNhd v (ball c ρ \ {c}))
    (hmax : ∀ z ∈ ball c ρ, v z ≤ M) (hm : ∀ z ∈ sphere c r, v z ≤ m) (hδ : δ = M - m) :
    ∀ z, ε < ‖z - c‖ → ‖z - c‖ < r →
      v z + δ / (Real.log r - Real.log ε) * (Real.log ‖z - c‖ - Real.log ε) ≤ M := by
  set U : Set ℂ := {y | ε < ‖y - c‖ ∧ ‖y - c‖ < r} with hU
  set D : ℝ := Real.log r - Real.log ε with hD
  have hD0 : 0 < D := sub_pos.2 (Real.log_lt_log hε hεr)
  have hr0 : 0 < r := hε.trans hεr
  set w : ℂ → ℝ := fun y =>
    v y + δ / D * Real.log ‖y - c‖ + (-(δ / D) * Real.log ε) with hw
  have hn : Continuous fun y : ℂ => ‖y - c‖ := by fun_prop
  have hUo : IsOpen U := (isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const)
  have hUb : Bornology.IsBounded U := by
    refine (Metric.isBounded_ball (x := c) (r := r)).subset ?_
    intro y hy
    simpa [mem_ball, dist_eq_norm] using hy.2
  have hUball : ∀ y ∈ U, y ∈ ball c ρ ∧ y ≠ c := by
    intro y hy
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]; linarith [hy.2]
    · intro h
      have := hy.1
      rw [h, sub_self, norm_zero] at this
      linarith
  have hS : closure U ⊆ {y | ε ≤ ‖y - c‖ ∧ ‖y - c‖ ≤ r} := by
    apply closure_minimal
    · intro y hy; exact ⟨hy.1.le, hy.2.le⟩
    · exact (isClosed_le continuous_const hn).inter (isClosed_le hn continuous_const)
  have hSball : ∀ y ∈ closure U, y ∈ ball c ρ ∧ y ≠ c := by
    intro y hy
    have := hS hy
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm]; linarith [this.2]
    · intro h
      have := this.1
      rw [h, sub_self, norm_zero] at this
      linarith
  have hwh : HarmonicOnNhd w U := by
    intro y hy
    have h1 : HarmonicAt v y := hh y ⟨(hUball y hy).1, (hUball y hy).2⟩
    have h2 : HarmonicAt (fun y : ℂ => Real.log ‖y - c‖) y := harmonicAt_log_norm_sub (hUball y hy).2
    exact (h1.add (h2.const_smul (c := δ / D))).add (harmonicAt_const _)
  have hwc : ContinuousOn w (closure U) := by
    have h1 : ContinuousOn v (closure U) := hv.mono fun y hy => (hSball y hy).1
    have h2 : ContinuousOn (fun y : ℂ => Real.log ‖y - c‖) (closure U) :=
      ContinuousOn.log (by fun_prop) (fun y hy => norm_ne_zero_iff.2 (sub_ne_zero.2 (hSball y hy).2))
    exact (h1.add (continuousOn_const.mul h2)).add continuousOn_const
  have hfr : ∀ y ∈ frontier U, w y ≤ M := by
    intro y hy
    rw [hUo.frontier_eq] at hy
    obtain ⟨hyc, hyU⟩ := hy
    have hyS := hS hyc
    have hyb := (hSball y hyc).1
    have hcases : ‖y - c‖ = ε ∨ ‖y - c‖ = r := by
      by_contra hcon
      push Not at hcon
      exact hyU ⟨lt_of_le_of_ne hyS.1 (Ne.symm hcon.1), lt_of_le_of_ne hyS.2 hcon.2⟩
    rcases hcases with h | h
    · simp only [hw, h]
      have : δ / D * Real.log ε + -(δ / D) * Real.log ε = 0 := by ring
      linarith [hmax y hyb]
    · have hys : y ∈ sphere c r := by rw [mem_sphere, dist_eq_norm]; exact h
      simp only [hw, h]
      have h1 : δ / D * Real.log r + -(δ / D) * Real.log ε = δ := by
        have e : δ / D * Real.log r + -(δ / D) * Real.log ε = δ / D * D := by rw [hD]; ring
        rw [e, div_mul_cancel₀ _ hD0.ne']
      have := hm y hys
      linarith
  intro z hz1 hz2
  have hzU : z ∈ U := ⟨hz1, hz2⟩
  have := HarmonicOnNhd.le_of_forall_frontier_le hUo hUb hwh hwc hfr z (subset_closure hzU)
  simp only [hw] at this
  linarith

/-- **Maximum principle across a puncture.** If `v` is continuous on the disk `ball c ρ`, harmonic on
the punctured disk, and `v z ≤ v c` on the disk, then `v` attains the value `v c` at a point of the
punctured disk. -/
theorem exists_ne_eq_of_isMaxOn_puncture {v : ℂ → ℝ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hv : ContinuousOn v (ball c ρ)) (hh : HarmonicOnNhd v (ball c ρ \ {c}))
    (hmax : ∀ z ∈ ball c ρ, v z ≤ v c) : ∃ z ∈ ball c ρ, z ≠ c ∧ v z = v c := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ z ∈ ball c ρ, z ≠ c → v z < v c := fun z hz hne =>
    lt_of_le_of_ne (hmax z hz) (hcon z hz hne)
  set r : ℝ := ρ / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrρ : r < ρ := by linarith
  have hsph : sphere c r ⊆ ball c ρ := fun z hz => by
    rw [mem_sphere, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]; linarith
  obtain ⟨z₁, hz₁, hz₁max⟩ := (isCompact_sphere c r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hr0.le) (hv.mono hsph)
  have hz₁ne : z₁ ≠ c := by
    intro h
    rw [h, mem_sphere, dist_self] at hz₁
    linarith
  set δ : ℝ := v c - v z₁ with hδ
  have hδ0 : 0 < δ := sub_pos.2 (hlt z₁ (hsph hz₁) hz₁ne)
  -- `v ≤ v c - δ` on the punctured disk of radius `r`
  have hbound : ∀ z, 0 < ‖z - c‖ → ‖z - c‖ < r → v z ≤ v c - δ := by
    intro z hz0 hzr
    set t := ‖z - c‖ with ht
    have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ∈ Ioo 0 t := Ioo_mem_nhdsGT hz0
    have hlim : Tendsto (fun ε : ℝ => δ * ((Real.log r - Real.log t) / (Real.log r - Real.log ε)))
        (𝓝[>] 0) (𝓝 (δ * 0)) := by
      refine Tendsto.const_mul _ ?_
      refine tendsto_const_nhds.div_atTop ?_
      have : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop :=
        tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left _ (Real.log r) this
    have hle : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        v z ≤ v c - δ + δ * ((Real.log r - Real.log t) / (Real.log r - Real.log ε)) := by
      filter_upwards [hev] with ε hε
      have hD : 0 < Real.log r - Real.log ε :=
        sub_pos.2 (Real.log_lt_log hε.1 (hε.2.trans hzr))
      have key := annulus_comparison (M := v c) (m := v z₁) hrρ hε.1 (hε.2.trans hzr) hv hh hmax
        (fun y hy => isMaxOn_iff.1 hz₁max y hy) rfl z hε.2 hzr
      have e : δ / (Real.log r - Real.log ε) * (Real.log t - Real.log ε) =
          δ - δ * ((Real.log r - Real.log t) / (Real.log r - Real.log ε)) := by
        field_simp; ring
      rw [e] at key
      linarith
    have := ge_of_tendsto (hlim.const_add (v c - δ)) hle
    simpa using this
  -- contradiction with continuity of `v` at `c`
  have hcont : ContinuousAt v c := hv.continuousAt (ball_mem_nhds c hρ)
  have hev : ∀ᶠ z in 𝓝[≠] c, v c - δ < v z ∧ ‖z - c‖ < r := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    refine (hcont.eventually (lt_mem_nhds (by linarith : v c - δ < v c))).and ?_
    have : ContinuousAt (fun z : ℂ => ‖z - c‖) c := by fun_prop
    exact this.eventually (gt_mem_nhds (by simpa using hr0))
  obtain ⟨z, ⟨hz1, hz2⟩, hzne⟩ := (hev.and self_mem_nhdsWithin).exists
  have hz0 : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzne)
  have := hbound z hz0 hz2
  linarith

/-- **A continuous function on `ℂ`, harmonic off a closed countable set of isolated points, that
attains its maximum is constant.** (The strong maximum principle across the punctures.) -/
theorem eq_of_isMaxOn_of_harmonicOnNhd_compl {P : Set ℂ} (hPcl : IsClosed P) (hPct : P.Countable)
    (hPd : ∀ p ∈ P, ∀ᶠ q in 𝓝[≠] p, q ∉ P) {v : ℂ → ℝ} (hv : Continuous v)
    (hh : HarmonicOnNhd v Pᶜ) {x₀ : ℂ} (hmax : ∀ x, v x ≤ v x₀) : ∀ x, v x = v x₀ := by
  -- Step 1: the maximum is attained off `P`.
  have hstep : ∃ y ∈ Pᶜ, v y = v x₀ := by
    by_cases hx₀ : x₀ ∈ P
    · have hev := hPd x₀ hx₀
      rw [Filter.Eventually, mem_nhdsWithin] at hev
      obtain ⟨u, hu, hx₀u, hus⟩ := hev
      obtain ⟨ρ, hρ, hρu⟩ := Metric.isOpen_iff.1 hu x₀ hx₀u
      have hsub : ball x₀ ρ \ {x₀} ⊆ Pᶜ := fun q hq =>
        hus ⟨hρu hq.1, hq.2⟩
      obtain ⟨z, hz, hzne, hzv⟩ := exists_ne_eq_of_isMaxOn_puncture hρ hv.continuousOn
        (hh.mono hsub) (fun z _ => hmax z)
      exact ⟨z, hsub ⟨hz, hzne⟩, hzv⟩
    · exact ⟨x₀, hx₀, rfl⟩
  obtain ⟨y, hyP, hyv⟩ := hstep
  -- Step 2: the strong maximum principle on the connected open set `Pᶜ`.
  have hconn : IsPreconnected Pᶜ := by
    have : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
    exact (hPct.isPathConnected_compl_of_one_lt_rank this).isConnected.isPreconnected
  have heq := HarmonicOnNhd.eqOn_of_isPreconnected (M := v x₀) hPcl.isOpen_compl hconn hh
    (fun z _ => hmax z) hyP hyv
  -- Step 3: density of `Pᶜ`.
  have hdense : Dense Pᶜ := hPct.dense_compl ℝ
  exact fun x => congrFun (Continuous.ext_on hdense hv continuous_const
    (fun z hz => by simpa using heq z hz) ) x

end InnerProductSpace

end
