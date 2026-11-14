/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Box.Radial2
public import SandierSerfaty.Certificate.Query.DerivGSound

/-!
# The second derivatives `G_ss`, `G_dd` of `comp:G-derivatives` as right derivatives

With `y = 1/t²`, `di = 1/d`, `ti = 1/t`, `r_v = v/t` (`v ∈ {d, s}`), paper §7 (`comp:rational-derivatives`,
`comp:G-derivatives`):

* `GssF d s y di ti F0 F1 F2 E0 E1 E2` is the right-hand side of `G_ss` for the radial data `F0 = f(t)`,
  `F1 = f'(t)`, `F2 = f''(t)`, `E0 = e(t)`, `E1 = e'(t)`, `E2 = e''(t)`;
* `GddF d s y di ti F0 F1 F2 E0 E1 E2` is that of `G_dd`.

`hasDerivWithinAt_Gs` / `hasDerivWithinAt_Gd`: at `d > 0`, `s ≥ 0`, the functions `G_s(d, ·)` and `G_d(·, s)` have the
right derivatives `GssF`, `GddF` (the radial data is `f''(t) = f₀''(t) - λ` and any right derivative `E` of the exact
`e'` at `t`); `radial_assembly` is the product-rule bookkeeping common to both. No second derivative of `e` beyond a
right derivative is used.
-/

open Set Filter Topology

public section

namespace SandierSerfaty.Certificate.Box

open SandierSerfaty.Calibration SandierSerfaty.Certificate.Query

/-- The product-rule bookkeeping of `comp:G-derivatives`: the right derivative of
`P₁ f(t) + P₂ f'(t) r + P₃ e(t) + P₄ e'(t) r`, where `t' = r` and `r' = (1 - r²)/t`. -/
theorem radial_assembly {S : Set ℝ} {w : ℝ} {t r P1 P2 P3 P4 f df e e1 : ℝ → ℝ} {p1 p2 p3 p4 F2 E : ℝ}
    (hT : HasDerivWithinAt t (r w) S w) (hmaps : MapsTo t S (Ici (t w)))
    (hr : HasDerivWithinAt r ((1 - r w ^ 2) / t w) S w)
    (h1 : HasDerivWithinAt P1 p1 S w) (h2 : HasDerivWithinAt P2 p2 S w) (h3 : HasDerivWithinAt P3 p3 S w)
    (h4 : HasDerivWithinAt P4 p4 S w)
    (hf : HasDerivAt f (df (t w)) (t w)) (hdf : HasDerivAt df F2 (t w)) (he : HasDerivAt e (e1 (t w)) (t w))
    (hde : HasDerivWithinAt e1 E (Ici (t w)) (t w)) :
    HasDerivWithinAt (fun v => P1 v * f (t v) + P2 v * df (t v) * r v + P3 v * e (t v) + P4 v * e1 (t v) * r v)
      (p1 * f (t w) + P1 w * (df (t w) * r w) +
        (p2 * df (t w) * r w + P2 w * (F2 * r w * r w + df (t w) * ((1 - r w ^ 2) / t w))) +
        (p3 * e (t w) + P3 w * (e1 (t w) * r w)) +
        (p4 * e1 (t w) * r w + P4 w * (E * r w * r w + e1 (t w) * ((1 - r w ^ 2) / t w)))) S w := by
  have a1 : HasDerivWithinAt (fun v => f (t v)) (df (t w) * r w) S w := hf.comp_hasDerivWithinAt w hT
  have a2 : HasDerivWithinAt (fun v => df (t v)) (F2 * r w) S w := hdf.comp_hasDerivWithinAt w hT
  have a3 : HasDerivWithinAt (fun v => e (t v)) (e1 (t w) * r w) S w := he.comp_hasDerivWithinAt w hT
  have a4 : HasDerivWithinAt (fun v => e1 (t v)) (r w • E) S w := hde.scomp w hT hmaps
  have b1 := h1.fun_mul a1
  have b2 := (h2.fun_mul a2).fun_mul hr
  have b3 := h3.fun_mul a3
  have b4 := (h4.fun_mul a4).fun_mul hr
  have := ((b1.fun_add b2).fun_add b3).fun_add b4
  refine this.congr_deriv ?_
  simp only [smul_eq_mul]
  ring

/-- `G_ss` for the radial data `F0, F1, F2` (of `f, f', f''`) and `E0, E1, E2` (of `e, e', e''`). -/
@[expose] noncomputable def GssF (d s y di ti F0 F1 F2 E0 E1 E2 : ℝ) : ℝ :=
  (-(d * y ^ 2 * 2) + 8 * d * s ^ 2 * y ^ 3) * F0 + 2 * (-(d * s * y ^ 2 * 2)) * F1 * (s * ti) +
    d * y * (F2 * (s * ti) * (s * ti) + F1 * ((1 - (s * ti) ^ 2) * ti)) +
    (-(d * y ^ 2 * 2) + 8 * d * s ^ 2 * y ^ 3) * E0 + 2 * (-(d * s * y ^ 2 * 2)) * E1 * (s * ti) +
    (-(s ^ 2 * (di * y))) * (E2 * (s * ti) * (s * ti) + E1 * ((1 - (s * ti) ^ 2) * ti))

/-- `G_dd` for the radial data. -/
@[expose] noncomputable def GddF (d s y di ti F0 F1 F2 E0 E1 E2 : ℝ) : ℝ :=
  (2 * d * (d ^ 2 - 3 * s ^ 2) * y ^ 3) * F0 + 2 * ((1 - d ^ 2 * y * 2) * y) * F1 * (d * ti) +
    d * y * (F2 * (d * ti) * (d * ti) + F1 * ((1 - (d * ti) ^ 2) * ti)) +
    (2 * d * (d ^ 2 - 3 * s ^ 2) * y ^ 3 - 2 * di ^ 3) * E0 +
    2 * ((1 - d ^ 2 * y * 2) * y + di ^ 2) * E1 * (d * ti) +
    (-(s ^ 2 * (di * y))) * (E2 * (d * ti) * (d * ti) + E1 * ((1 - (d * ti) ^ 2) * ti))

theorem hasDerivAt_yinv_s {d : ℝ} (hd : 0 < d) (w : ℝ) :
    HasDerivAt (fun w => (d ^ 2 + w ^ 2)⁻¹) (-(2 * w) * ((d ^ 2 + w ^ 2)⁻¹) ^ 2) w := by
  have h : HasDerivAt (fun w : ℝ => d ^ 2 + w ^ 2) (2 * w) w := by
    simpa using (hasDerivAt_pow 2 w).const_add (d ^ 2)
  have := h.inv (by positivity)
  refine this.congr_deriv ?_
  rw [div_eq_mul_inv, inv_pow]

/-- coefficient `A_s` -/
theorem hasDerivAt_A_s {d : ℝ} (hd : 0 < d) (w : ℝ) :
    HasDerivAt (fun w => d * (d ^ 2 + w ^ 2)⁻¹) (-(d * w * ((d ^ 2 + w ^ 2)⁻¹) ^ 2 * 2)) w := by
  have := (hasDerivAt_yinv_s hd w).const_mul d
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_As_s {d : ℝ} (hd : 0 < d) (w : ℝ) :
    HasDerivAt (fun w => -(d * w * ((d ^ 2 + w ^ 2)⁻¹) ^ 2 * 2))
      (-(d * ((d ^ 2 + w ^ 2)⁻¹) ^ 2 * 2) + 8 * d * w ^ 2 * ((d ^ 2 + w ^ 2)⁻¹) ^ 3) w := by
  have hy := hasDerivAt_yinv_s hd w
  have h1 : HasDerivAt (fun w : ℝ => d * w) d w := by simpa using (hasDerivAt_id w).const_mul d
  have h2 := (h1.fun_mul (hy.fun_pow 2)).mul_const 2
  have := h2.fun_neg
  refine this.congr_deriv ?_
  ring

theorem hasDerivAt_Z_s {d : ℝ} (hd : 0 < d) (w : ℝ) :
    HasDerivAt (fun w => -(w ^ 2 * (d⁻¹ * (d ^ 2 + w ^ 2)⁻¹))) (-(d * w * ((d ^ 2 + w ^ 2)⁻¹) ^ 2 * 2)) w := by
  have hy := hasDerivAt_yinv_s hd w
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
  have h2 := h1.fun_mul (hy.const_mul d⁻¹)
  have := h2.fun_neg
  refine this.congr_deriv ?_
  have hq : d ^ 2 + w ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### d-direction coefficients -/

theorem hasDerivAt_yinv_d {s : ℝ} (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u => (u ^ 2 + s ^ 2)⁻¹) (-(2 * u) * ((u ^ 2 + s ^ 2)⁻¹) ^ 2) u := by
  have h : HasDerivAt (fun u : ℝ => u ^ 2 + s ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).add_const (s ^ 2)
  have := h.inv (by positivity)
  refine this.congr_deriv ?_
  rw [div_eq_mul_inv, inv_pow]

/-- `A = d/t²` has derivative `A_d = (1 - 2 d² y) y`. -/
theorem hasDerivAt_A_d {s : ℝ} (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u => u * (u ^ 2 + s ^ 2)⁻¹) ((1 - u ^ 2 * (u ^ 2 + s ^ 2)⁻¹ * 2) * (u ^ 2 + s ^ 2)⁻¹) u := by
  have := (hasDerivAt_id u).fun_mul (hasDerivAt_yinv_d (s := s) u hu)
  refine this.congr_deriv ?_
  simp only [id]
  ring

theorem hasDerivAt_Ad_d {s : ℝ} (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u => (1 - u ^ 2 * (u ^ 2 + s ^ 2)⁻¹ * 2) * (u ^ 2 + s ^ 2)⁻¹)
      (2 * u * (u ^ 2 - 3 * s ^ 2) * ((u ^ 2 + s ^ 2)⁻¹) ^ 3) u := by
  have hy := hasDerivAt_yinv_d (s := s) u hu
  have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
  have h2 := (((h1.fun_mul hy).mul_const 2).const_sub 1).fun_mul hy
  refine h2.congr_deriv ?_
  have hq : u ^ 2 + s ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem hasDerivAt_Z_d {s : ℝ} (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u => -(s ^ 2 * (u⁻¹ * (u ^ 2 + s ^ 2)⁻¹)))
      ((1 - u ^ 2 * (u ^ 2 + s ^ 2)⁻¹ * 2) * (u ^ 2 + s ^ 2)⁻¹ + (u⁻¹) ^ 2) u := by
  have hy := hasDerivAt_yinv_d (s := s) u hu
  have h1 : HasDerivAt (fun u : ℝ => u⁻¹) (-(u ^ 2)⁻¹) u := hasDerivAt_inv hu.ne'
  have h2 := (h1.fun_mul hy).const_mul (s ^ 2)
  have := h2.fun_neg
  refine this.congr_deriv ?_
  have hq : u ^ 2 + s ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem hasDerivAt_inv_sq {u : ℝ} (hu : 0 < u) : HasDerivAt (fun u : ℝ => (u⁻¹) ^ 2) (-(2 * (u⁻¹) ^ 3)) u := by
  have h1 : HasDerivAt (fun u : ℝ => u⁻¹) (-(u ^ 2)⁻¹) u := hasDerivAt_inv hu.ne'
  refine (h1.fun_pow 2).congr_deriv ?_
  field_simp
  norm_num
  field_simp

theorem hasDerivAt_Zd_d {s : ℝ} (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u => (1 - u ^ 2 * (u ^ 2 + s ^ 2)⁻¹ * 2) * (u ^ 2 + s ^ 2)⁻¹ + (u⁻¹) ^ 2)
      (2 * u * (u ^ 2 - 3 * s ^ 2) * ((u ^ 2 + s ^ 2)⁻¹) ^ 3 - 2 * (u⁻¹) ^ 3) u := by
  have h2 := (hasDerivAt_Ad_d (s := s) u hu).fun_add (hasDerivAt_inv_sq hu)
  refine h2.congr_deriv ?_
  ring

theorem hasDerivAt_df {t F2 : ℝ} (hF2 : HasDerivAt (deriv f₀) F2 t) : HasDerivAt df (F2 - lam) t := by
  have := hF2.sub ((hasDerivAt_id t).const_mul lam)
  refine this.congr_deriv ?_
  simp

/-- `G_ss`, right derivative of `G_s(d, ·)`. -/
theorem hasDerivWithinAt_Gs {d s : ℝ} (hd : 0 < d) (hs : 0 ≤ s) {F2 E : ℝ}
    (hF2 : HasDerivAt (deriv f₀) F2 (tt d s)) (hE : HasDerivWithinAt (deriv e) E (Ici (tt d s)) (tt d s)) :
    HasDerivWithinAt (Gs d)
      (GssF d s ((d ^ 2 + s ^ 2)⁻¹) d⁻¹ (tt d s)⁻¹ (f (tt d s)) (df (tt d s)) (F2 - lam) (e (tt d s))
        (deriv e (tt d s)) E) (Ici s) s := by
  have ht0 : 0 < tt d s := tt_pos hd
  have hT : HasDerivWithinAt (tt d) (s * (tt d s)⁻¹) (Ici s) s :=
    ((hasDerivAt_tt_s hd s).hasDerivWithinAt).congr_deriv (by rw [div_eq_mul_inv])
  have hmaps : MapsTo (tt d) (Ici s) (Ici (tt d s)) := by
    intro w hw
    have hw' : s ≤ w := hw
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hr : HasDerivWithinAt (fun w => w * (tt d w)⁻¹) ((1 - (s * (tt d s)⁻¹) ^ 2) / tt d s) (Ici s) s := by
    have := ((hasDerivAt_id s).fun_mul ((hasDerivAt_tt_s hd s).inv ht0.ne')).hasDerivWithinAt (s := Ici s)
    refine this.congr_deriv ?_
    simp only [id, Pi.inv_apply]
    field_simp
    ring
  have key := radial_assembly (S := Ici s) (w := s) (t := tt d) (r := fun w => w * (tt d w)⁻¹)
    (P1 := fun w => -(d * w * ((d ^ 2 + w ^ 2)⁻¹) ^ 2 * 2)) (P2 := fun w => d * (d ^ 2 + w ^ 2)⁻¹)
    (P3 := fun w => -(d * w * ((d ^ 2 + w ^ 2)⁻¹) ^ 2 * 2))
    (P4 := fun w => -(w ^ 2 * (d⁻¹ * (d ^ 2 + w ^ 2)⁻¹))) (f := f) (df := df) (e := e) (e1 := deriv e)
    (p1 := -(d * ((d ^ 2 + s ^ 2)⁻¹) ^ 2 * 2) + 8 * d * s ^ 2 * ((d ^ 2 + s ^ 2)⁻¹) ^ 3)
    (p2 := -(d * s * ((d ^ 2 + s ^ 2)⁻¹) ^ 2 * 2))
    (p3 := -(d * ((d ^ 2 + s ^ 2)⁻¹) ^ 2 * 2) + 8 * d * s ^ 2 * ((d ^ 2 + s ^ 2)⁻¹) ^ 3)
    (p4 := -(d * s * ((d ^ 2 + s ^ 2)⁻¹) ^ 2 * 2)) (F2 := F2 - lam) (E := E)
    hT hmaps hr (hasDerivAt_As_s hd s).hasDerivWithinAt (hasDerivAt_A_s hd s).hasDerivWithinAt
    (hasDerivAt_As_s hd s).hasDerivWithinAt (hasDerivAt_Z_s hd s).hasDerivWithinAt (hasDerivAt_f ht0)
    (hasDerivAt_df hF2) ((differentiableAt_e ht0).hasDerivAt) hE
  refine (key.congr (fun w _ => ?_) ?_).congr_deriv ?_
  · rw [gs_eq hd]; push_cast; ring
  · rw [gs_eq hd]; push_cast; ring
  · unfold GssF; ring

/-- `G_dd`, right derivative of `G_d(·, s)`. -/
theorem hasDerivWithinAt_Gd {d s : ℝ} (hd : 0 < d) {F2 E : ℝ}
    (hF2 : HasDerivAt (deriv f₀) F2 (tt d s)) (hE : HasDerivWithinAt (deriv e) E (Ici (tt d s)) (tt d s)) :
    HasDerivWithinAt (fun u => Gd u s)
      (GddF d s ((d ^ 2 + s ^ 2)⁻¹) d⁻¹ (tt d s)⁻¹ (f (tt d s)) (df (tt d s)) (F2 - lam) (e (tt d s))
        (deriv e (tt d s)) E) (Ici d) d := by
  have ht0 : 0 < tt d s := tt_pos hd
  have hT : HasDerivWithinAt (fun u => tt u s) (d * (tt d s)⁻¹) (Ici d) d :=
    ((hasDerivAt_tt_d hd s).hasDerivWithinAt).congr_deriv (by rw [div_eq_mul_inv])
  have hmaps : MapsTo (fun u => tt u s) (Ici d) (Ici (tt d s)) := by
    intro w hw
    have hw' : d ≤ w := hw
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hr : HasDerivWithinAt (fun u => u * (tt u s)⁻¹) ((1 - (d * (tt d s)⁻¹) ^ 2) / tt d s) (Ici d) d := by
    have := ((hasDerivAt_id d).fun_mul ((hasDerivAt_tt_d hd s).inv ht0.ne')).hasDerivWithinAt (s := Ici d)
    refine this.congr_deriv ?_
    simp only [id, Pi.inv_apply]
    field_simp
    ring
  have key := radial_assembly (S := Ici d) (w := d) (t := fun u => tt u s) (r := fun u => u * (tt u s)⁻¹)
    (P1 := fun u => (1 - u ^ 2 * (u ^ 2 + s ^ 2)⁻¹ * 2) * (u ^ 2 + s ^ 2)⁻¹)
    (P2 := fun u => u * (u ^ 2 + s ^ 2)⁻¹)
    (P3 := fun u => (1 - u ^ 2 * (u ^ 2 + s ^ 2)⁻¹ * 2) * (u ^ 2 + s ^ 2)⁻¹ + (u⁻¹) ^ 2)
    (P4 := fun u => -(s ^ 2 * (u⁻¹ * (u ^ 2 + s ^ 2)⁻¹))) (f := f) (df := df) (e := e) (e1 := deriv e)
    (p1 := 2 * d * (d ^ 2 - 3 * s ^ 2) * ((d ^ 2 + s ^ 2)⁻¹) ^ 3)
    (p2 := (1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * 2) * (d ^ 2 + s ^ 2)⁻¹)
    (p3 := 2 * d * (d ^ 2 - 3 * s ^ 2) * ((d ^ 2 + s ^ 2)⁻¹) ^ 3 - 2 * (d⁻¹) ^ 3)
    (p4 := (1 - d ^ 2 * (d ^ 2 + s ^ 2)⁻¹ * 2) * (d ^ 2 + s ^ 2)⁻¹ + (d⁻¹) ^ 2) (F2 := F2 - lam) (E := E)
    hT hmaps hr (hasDerivAt_Ad_d d hd).hasDerivWithinAt (hasDerivAt_A_d d hd).hasDerivWithinAt
    (hasDerivAt_Zd_d d hd).hasDerivWithinAt (hasDerivAt_Z_d d hd).hasDerivWithinAt (hasDerivAt_f ht0)
    (hasDerivAt_df hF2) ((differentiableAt_e ht0).hasDerivAt) hE
  refine (key.congr (fun u hu => ?_) ?_).congr_deriv ?_
  · have hu0 : 0 < u := lt_of_lt_of_le hd hu
    rw [gd_eq hu0]; push_cast; ring
  · rw [gd_eq hd]; push_cast; ring
  · unfold GddF; ring

end SandierSerfaty.Certificate.Box
