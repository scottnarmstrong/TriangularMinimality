/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.EdgePoly

/-!
# The radial data `b_i, U_m, τ, u_i, B, D_i` of the Voronoi test potential

paper `cal:inner-continuation`, `cal:radial-data`. The definitions follow the
paper literally (a cascade of cases, with the clipped `S` and the continuation `cont` of `Cutoff.lean`):

* `bInner m r = S((r - p + c)/c) (T_{0m} + T_{1m}(r - p) + T_{2m}(r - p)²)` (the inner continuation);
* `bRad i r`: for `i = 0`, `γ` up to `R₀` and `𝓗γ` above; for `i ≥ 1`, `0` up to `p - c`, `bInner` on
  `(p - c, p)`, `V_i` on `[p, R₀]`, `𝓗V_i` above. The inner continuation is for `m ≥ 1` only and
  `b₀ = γ` on `(0, R₀]` (the inner continuation involves `c_m`, which is defined for `m ≥ 1` only);
* `tau r = S((r - R₀ - 1/1000)/h_s)` (`h_s = 3/40`), `U m r = (-1)^m c_m r^{k_m} (1 - S((r - R₀)/(1/10)))`;
* `u 0 = (1 - τ) γ + τ b₀`, `u m = (1 - τ) U_m + τ b_m`, `B r = ∑' i, u i r`, `D i = bRad i - u i`
  (with `B₁ r = B' r + 1/r` of paper `cal:radial-integrals`).

`C²` of the splines on `(0, ∞)` (`contDiffOn_b`, `contDiffOn_u`, `contDiffOn_D`) is proved structurally:
`b_m` is the nested gluing `0 | bPoly | V_m | 𝓗V_m` of globally smooth pieces (`bRad_eq_glue`), the 2-jets
matching by `Squintic`'s jets at `0, 1`, the identities `V_m^{(j)}(p) = (T_{0m}, T_{1m}, 2 T_{2m})` and the
`P, Q` jets; `τ`, `U_m` are compositions of the `C²` function `S` with affine maps, so `u_i = (1-τ) w_i + τ b_i`
and `D_i = b_i - u_i` are `C²` as sums of products. The `C³` pieces on the closed segments are in
`Pieces.lean`.
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Calibration

/-- The inner continuation `S((r - p + c)/c) (T_{0m} + T_{1m}(r - p) + T_{2m}(r - p)²)` (paper `cal:inner-continuation`). -/
@[expose] noncomputable def bInner (m : ℕ) (r : ℝ) : ℝ :=
  S ((r - p + c) / c) * (T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2)

/-- The radial data `b_i` (paper `cal:inner-continuation`; for `i = 0` the inner continuation is not used). -/
@[expose] noncomputable def bRad (i : ℕ) (r : ℝ) : ℝ :=
  if i = 0 then (if r ≤ R₀ then gamma r else cont gamma r)
  else if r ≤ p - c then 0
  else if r < p then bInner i r
  else if r ≤ R₀ then V i r
  else cont (V i) r

/-- The cutoff `τ(r) = S((r - R₀ - 1/1000)/(3/40))` (paper §5.3). -/
@[expose] noncomputable def tau (r : ℝ) : ℝ := S ((r - R₀ - 1 / 1000) / hs)

/-- `U_m(r) = (-1)^m c_m r^{k_m} (1 - S((r - R₀)/(1/10)))` (paper §5.3); only `m ≥ 1` is used. -/
@[expose] noncomputable def U (m : ℕ) (r : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * coeff m * r ^ k m * (1 - S ((r - R₀) / (1 / 10)))

/-- The radial data `u_i` (paper `cal:radial-data`): `u₀ = (1 - τ) γ + τ b₀`,
`u_m = (1 - τ) U_m + τ b_m`. -/
@[expose] noncomputable def u (i : ℕ) (r : ℝ) : ℝ :=
  if i = 0 then (1 - tau r) * gamma r + tau r * bRad 0 r
  else (1 - tau r) * U i r + tau r * bRad i r

/-- `D_i = b_i - u_i` (paper `cal:radial-data`). -/
@[expose] noncomputable def D (i : ℕ) (r : ℝ) : ℝ := bRad i r - u i r

/-- `B = ∑_{i ≥ 0} u_i` (paper `cal:radial-data`). -/
@[expose] noncomputable def B (r : ℝ) : ℝ := ∑' i, u i r

/-- `B₁(t) = B'(t) + 1/t` (paper `cal:radial-integrals`). -/
@[expose] noncomputable def B₁ (r : ℝ) : ℝ := deriv B r + 1 / r

/-! ### Values: `τ`, vanishing of `D_i`, constancy beyond `l` -/

theorem tau_of_le {r : ℝ} (hr : r ≤ R₀ + 1 / 1000) : tau r = 0 := by
  unfold tau; apply S_of_nonpos
  have := hs_pos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le

theorem tau_of_ge {r : ℝ} (hr : l ≤ r) : tau r = 1 := by
  unfold tau; apply S_of_one_le
  have := hs_pos
  rw [le_div_iff₀ this, one_mul]
  have := l_eq
  linarith

theorem tau_of_mem_Icc {r : ℝ} (h0 : R₀ + 1 / 1000 ≤ r) (h1 : r ≤ l) :
    tau r = Squintic ((r - R₀ - 1 / 1000) / hs) := by
  unfold tau; apply S_of_mem_Icc
  · exact div_nonneg (by linarith) hs_pos.le
  · rw [div_le_one hs_pos]; have := l_eq; linarith

theorem bRad_zero_of_le_R₀ {r : ℝ} (hr : r ≤ R₀) : bRad 0 r = gamma r := by simp [bRad, hr]

theorem bRad_zero_of_gt {r : ℝ} (hr : R₀ < r) : bRad 0 r = cont gamma r := by simp [bRad, hr.not_ge]

theorem bRad_of_le_inner {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : r ≤ p - c) : bRad m r = 0 := by
  simp [bRad, hm.ne', hr]

theorem bRad_of_mem_inner {m : ℕ} (hm : 0 < m) {r : ℝ} (h0 : p - c < r) (h1 : r < p) :
    bRad m r = bInner m r := by
  simp [bRad, hm.ne', h0.not_ge, h1]

theorem bRad_of_mem_edge {m : ℕ} (hm : 0 < m) {r : ℝ} (h0 : p ≤ r) (h1 : r ≤ R₀) : bRad m r = V m r := by
  have : ¬ r ≤ p - c := by have := c_pos; linarith
  simp [bRad, hm.ne', this, h0.not_gt, h1]

theorem bRad_of_gt {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : R₀ < r) : bRad m r = cont (V m) r := by
  have h1 : ¬ r ≤ p - c := by have := p_lt_R₀; have := c_pos; linarith
  have h2 : ¬ r < p := by have := p_lt_R₀; linarith
  simp [bRad, hm.ne', h1, h2, hr.not_ge]

/-- Beyond `R₀ + h_s` the continuation is constant: `b_0 = γ(R₀)`, `b_m = V_m(R₀)`. -/
theorem bRad_of_ge {i : ℕ} {r : ℝ} (hr : R₀ + hs ≤ r) :
    bRad i r = if i = 0 then gamma R₀ else V i R₀ := by
  have hR := R₀_pos; have := hs_pos
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [bRad_zero_of_gt (by linarith), cont_of_ge _ hr]; simp
  · rw [bRad_of_gt hi (by linarith), cont_of_ge _ hr]; simp [hi.ne']

theorem u_of_le {i : ℕ} {r : ℝ} (hr : r ≤ R₀ + 1 / 1000) :
    u i r = if i = 0 then gamma r else U i r := by
  by_cases hi : i = 0
  · simp [u, hi, tau_of_le hr]
  · simp [u, hi, tau_of_le hr]

theorem u_of_ge {i : ℕ} {r : ℝ} (hr : l ≤ r) : u i r = bRad i r := by
  by_cases hi : i = 0
  · simp [u, hi, tau_of_ge hr]
  · simp [u, hi, tau_of_ge hr]

/-- `D_i(r) = 0` for `r ≥ l` (paper `cal:radial-endpoints`). -/
theorem D_of_ge {i : ℕ} {r : ℝ} (hr : l ≤ r) : D i r = 0 := by
  simp [D, u_of_ge hr]

/-- `S((r - R₀)/(1/10)) = 0` for `r ≤ R₀`. -/
theorem S_U_of_le {r : ℝ} (hr : r ≤ R₀) : S ((r - R₀) / (1 / 10)) = 0 := by
  apply S_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)

/-- On `(−∞, R₀]` the radial data are the hexagon data: `u_0 = γ`, `u_m = (-1)^m c_m r^{k_m}`
(paper proof of Lemma `cal:energy-identity`). -/
theorem u_zero_of_le_R₀ {r : ℝ} (hr : r ≤ R₀) : u 0 r = gamma r := by
  rw [u_of_le (by linarith)]; simp

theorem u_of_le_R₀ {m : ℕ} (hm : 0 < m) {r : ℝ} (hr : r ≤ R₀) :
    u m r = (-1 : ℝ) ^ m * coeff m * r ^ k m := by
  rw [u_of_le (by linarith)]
  simp only [hm.ne', ↓reduceIte]
  unfold U
  rw [S_U_of_le hr]; ring

theorem D_zero_of_le_R₀ {r : ℝ} (hr : r ≤ R₀) : D 0 r = 0 := by
  rw [D, u_zero_of_le_R₀ hr, bRad_zero_of_le_R₀ hr]; ring

/-- For `r ≥ l`, `u_i r` does not depend on `r`; hence `B r = B l` (paper `cal:radial-endpoints`). -/
theorem u_eq_of_ge {i : ℕ} {r : ℝ} (hr : l ≤ r) : u i r = u i l := by
  rw [u_of_ge hr, u_of_ge le_rfl]
  have h1 : R₀ + hs ≤ r := by have := R₀_add_hs_lt_l; linarith
  have h2 : R₀ + hs ≤ l := by have := R₀_add_hs_lt_l; linarith
  rw [bRad_of_ge h1, bRad_of_ge h2]

theorem B_eq_of_ge {r : ℝ} (hr : l ≤ r) : B r = B l := by
  unfold B; exact tsum_congr fun i => u_eq_of_ge hr

/-! ### `C²` regularity -/

theorem contDiff_tau : ContDiff ℝ 2 tau := by
  have h := contDiff_S.comp (f := fun r : ℝ => (r - R₀ - 1 / 1000) / hs) (by fun_prop)
  exact h

theorem contDiff_U (m : ℕ) : ContDiff ℝ 2 (U m) := by
  have h := contDiff_S.comp (f := fun r : ℝ => (r - R₀) / (1 / 10)) (by fun_prop)
  unfold U
  have h' : ContDiff ℝ 2 fun r : ℝ => 1 - S ((r - R₀) / (1 / 10)) := contDiff_const.sub h
  exact (by fun_prop : ContDiff ℝ 2 fun r : ℝ => (-1 : ℝ) ^ m * coeff m * r ^ k m).mul h'

/-- The globally smooth inner piece `Squintic((r - p + c)/c) (T_{0m} + T_{1m}(r - p) + T_{2m}(r - p)²)`:
it equals `bInner m` on `[p - c, p]`. -/
@[expose] noncomputable def bPoly (m : ℕ) (r : ℝ) : ℝ :=
  Squintic ((r - p + c) / c) * (T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2)

theorem bInner_eq_bPoly {m : ℕ} {r : ℝ} (h0 : p - c ≤ r) (h1 : r ≤ p) : bInner m r = bPoly m r := by
  unfold bInner bPoly
  rw [S_of_mem_Icc]
  · have := c_pos; exact div_nonneg (by linarith) this.le
  · have := c_pos; rw [div_le_one this]; linarith

theorem contDiff_bPoly (m : ℕ) : ContDiff ℝ ⊤ (bPoly m) := by
  have := contDiff_Squintic
  have h := this.comp (f := fun r : ℝ => (r - p + c) / c) (by fun_prop)
  unfold bPoly
  exact h.mul (by fun_prop)

/-- First derivative of `bPoly` (explicit). -/
noncomputable def bPoly1 (m : ℕ) (r : ℝ) : ℝ :=
  Squintic1 ((r - p + c) / c) / c * (T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2) +
    Squintic ((r - p + c) / c) * (T1 m + 2 * T2 m * (r - p))

/-- Second derivative of `bPoly` (explicit). -/
noncomputable def bPoly2 (m : ℕ) (r : ℝ) : ℝ :=
  Squintic2 ((r - p + c) / c) / c ^ 2 * (T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2) +
    2 * (Squintic1 ((r - p + c) / c) / c) * (T1 m + 2 * T2 m * (r - p)) +
    Squintic ((r - p + c) / c) * (2 * T2 m)

theorem hasDerivAt_aff (r : ℝ) : HasDerivAt (fun r : ℝ => (r - p + c) / c) (1 / c) r := by
  have := (((hasDerivAt_id r).sub_const p).add_const c).div_const c
  simpa using this

theorem hasDerivAt_Tq (m : ℕ) (r : ℝ) :
    HasDerivAt (fun r : ℝ => T0 m + T1 m * (r - p) + T2 m * (r - p) ^ 2)
      (T1 m + 2 * T2 m * (r - p)) r := by
  have h1 : HasDerivAt (fun r : ℝ => r - p) 1 r := (hasDerivAt_id r).sub_const p
  have h2 := (h1.pow 2).const_mul (T2 m)
  have := ((h1.const_mul (T1 m)).const_add (T0 m)).add h2
  refine this.congr_deriv ?_
  simp; ring

theorem hasDerivAt_bPoly (m : ℕ) (r : ℝ) : HasDerivAt (bPoly m) (bPoly1 m r) r := by
  have h1 := (hasDerivAt_Squintic ((r - p + c) / c)).comp r (hasDerivAt_aff r)
  have h2 := h1.mul (hasDerivAt_Tq m r)
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold bPoly1; simp only [Function.comp_apply]; ring
  · simp [bPoly]

theorem hasDerivAt_bPoly1 (m : ℕ) (r : ℝ) : HasDerivAt (bPoly1 m) (bPoly2 m r) r := by
  have hq : HasDerivAt (fun r : ℝ => T1 m + 2 * T2 m * (r - p)) (2 * T2 m) r := by
    have := ((hasDerivAt_id r).sub_const p).const_mul (2 * T2 m)
    simpa using this.const_add (T1 m)
  have A := ((hasDerivAt_Squintic1 ((r - p + c) / c)).comp r (hasDerivAt_aff r)).div_const c
  have B' := A.mul (hasDerivAt_Tq m r)
  have C' := ((hasDerivAt_Squintic ((r - p + c) / c)).comp r (hasDerivAt_aff r)).mul hq
  have F := B'.add C'
  refine (F.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · unfold bPoly2; simp; ring
  · simp [bPoly1]

theorem deriv_bPoly (m : ℕ) : deriv (bPoly m) = bPoly1 m :=
  funext fun r => (hasDerivAt_bPoly m r).deriv

theorem deriv_bPoly1 (m : ℕ) : deriv (bPoly1 m) = bPoly2 m :=
  funext fun r => (hasDerivAt_bPoly1 m r).deriv

/-- The 2-jet of `bPoly m` at `p - c` vanishes (`S` starts flat). -/
theorem bPoly_jet_inner (m : ℕ) :
    bPoly m (p - c) = 0 ∧ deriv (bPoly m) (p - c) = 0 ∧ deriv (deriv (bPoly m)) (p - c) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bPoly]
  · simp [deriv_bPoly, bPoly1]
  · simp [deriv_bPoly, deriv_bPoly1, bPoly2]

/-- The 2-jet of `bPoly m` at `p` is `(T_{0m}, T_{1m}, 2 T_{2m})` (`S` has reached `1` flatly). -/
theorem bPoly_jet_edge (m : ℕ) :
    bPoly m p = T0 m ∧ deriv (bPoly m) p = T1 m ∧ deriv (deriv (bPoly m)) p = 2 * T2 m := by
  refine ⟨?_, ?_, ?_⟩
  · simp [bPoly, div_self c_pos.ne']
  · simp [deriv_bPoly, bPoly1, div_self c_pos.ne']
  · simp [deriv_bPoly, deriv_bPoly1, bPoly2, div_self c_pos.ne']

theorem bRad_eq_glue {m : ℕ} (hm : 0 < m) :
    bRad m = glue (p - c) (fun _ => 0) (glue p (bPoly m) (glue R₀ (V m) (cont (V m)))) := by
  funext r
  by_cases h1 : r ≤ p - c
  · rw [glue_of_le h1, bRad_of_le_inner hm h1]
  · push Not at h1
    rw [glue_of_gt h1]
    by_cases h2 : r ≤ p
    · rw [glue_of_le h2]
      rcases h2.eq_or_lt with rfl | h2
      · rw [bRad_of_mem_edge hm le_rfl p_lt_R₀.le, V_p, (bPoly_jet_edge m).1]
      · rw [bRad_of_mem_inner hm h1 h2, bInner_eq_bPoly h1.le h2.le]
    · push Not at h2
      rw [glue_of_gt h2]
      by_cases h3 : r ≤ R₀
      · rw [glue_of_le h3, bRad_of_mem_edge hm h2.le h3]
      · push Not at h3
        rw [glue_of_gt h3, bRad_of_gt hm h3]

theorem bRad_zero_eq_glue : bRad 0 = glue R₀ gamma (cont gamma) := by
  funext r
  by_cases h : r ≤ R₀
  · rw [glue_of_le h, bRad_zero_of_le_R₀ h]
  · push Not at h
    rw [glue_of_gt h, bRad_zero_of_gt h]

/-- `b_i` is `C²` on `(0, ∞)` (paper §5.3: "every `b_i` is `C²` away from the origin"). -/
theorem contDiffOn_bRad (i : ℕ) : ContDiffOn ℝ 2 (bRad i) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos i with rfl | hm
  · rw [bRad_zero_eq_glue]
    exact contDiffOn_glue_cont ((contDiffOn_gamma).of_le (by simp))
  · rw [bRad_eq_glue hm]
    have hR := R₀_pos
    have hpc : 0 < p - c := lt_of_le_of_lt b_pos.le b_lt_p_sub_c
    have hp : 0 < p := p_pos
    have hV : ContDiffOn ℝ 2 (V i) (Ioi 0) := ((contDiff_V i).of_le (by simp)).contDiffOn
    have hrest : ContDiffOn ℝ 2 (glue R₀ (V i) (cont (V i))) (Ioi 0) := contDiffOn_glue_cont hV
    have hev : glue R₀ (V i) (cont (V i)) =ᶠ[nhds p] V i :=
      eventuallyEq_glue_left (V i) (cont (V i)) p_lt_R₀
    have hmid : ContDiffOn ℝ 2 (glue p (bPoly i) (glue R₀ (V i) (cont (V i)))) (Ioi 0) := by
      obtain ⟨j0, j1, j2⟩ := bPoly_jet_edge i
      refine contDiffOn_glue_two isOpen_Ioi (by simpa using hp)
        ((contDiff_bPoly i).of_le (by simp)).contDiffOn hrest ?_ ?_ ?_
      · rw [hev.eq_of_nhds, j0, V_p]
      · rw [hev.deriv_eq, j1, deriv_V_p]
      · rw [hev.deriv.deriv_eq, j2, deriv_deriv_V_p]
    have hev' : glue p (bPoly i) (glue R₀ (V i) (cont (V i))) =ᶠ[nhds (p - c)] bPoly i :=
      eventuallyEq_glue_left (bPoly i) _ p_sub_c_lt_p
    obtain ⟨j0, j1, j2⟩ := bPoly_jet_inner i
    refine contDiffOn_glue_two isOpen_Ioi (by simpa using hpc) contDiffOn_const hmid ?_ ?_ ?_
    · rw [hev'.eq_of_nhds, j0]
    · rw [hev'.deriv_eq, j1]; simp
    · rw [hev'.deriv.deriv_eq, j2]; simp

theorem contDiffOn_u (i : ℕ) : ContDiffOn ℝ 2 (u i) (Ioi 0) := by
  have ht : ContDiffOn ℝ 2 tau (Ioi 0) := contDiff_tau.contDiffOn
  have hb := contDiffOn_bRad i
  by_cases hi : i = 0
  · subst hi
    have e : u 0 = fun r => (1 - tau r) * gamma r + tau r * bRad 0 r := by
      funext r; simp [u]
    rw [e]
    exact ((contDiffOn_const.sub ht).mul ((contDiffOn_gamma).of_le (by simp))).add (ht.mul hb)
  · have e : u i = fun r => (1 - tau r) * U i r + tau r * bRad i r := by
      funext r; simp [u, hi]
    rw [e]
    exact ((contDiffOn_const.sub ht).mul ((contDiff_U i).contDiffOn)).add (ht.mul hb)

theorem contDiffOn_D (i : ℕ) : ContDiffOn ℝ 2 (D i) (Ioi 0) :=
  (contDiffOn_bRad i).sub (contDiffOn_u i)

end Calibration

end SandierSerfaty
