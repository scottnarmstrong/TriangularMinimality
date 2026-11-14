/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Calibration.Constants
public import SandierSerfaty.Calibration.Glue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The clipped quintic `S`, the polynomials `P`, `Q`, and the continuation `𝓗`

paper `cal:continuation`.

* `Squintic y = 10y³ - 15y⁴ + 6y⁵`, the quintic of `S` (a polynomial, smooth on all of `ℝ`);
* `S y` is `0` for `y ≤ 0`, `Squintic y` for `0 < y < 1`, `1` for `y ≥ 1` (paper §5.3); it is `C²`
  (`contDiff_S`), by the jets `(Squintic, Squintic', Squintic'')(0) = (0, 0, 0)` and `(1, 0, 0)` at `1`;
* `Ppoly`, `Qpoly` are the polynomials `P`, `Q` of paper §5.3 (named so as not to clash with the
  radial function `Cal.Q i t` of paper `cal:radial-integrals`), with `(P, P', P'')(0) = (0, 1, 0)`, `(Q, Q', Q'')(0) = (0, 0, 1)`
  and all six values vanishing at `h_s` (paper §5.3);
* `contPoly V` is the polynomial `V(R₀) + P(r - R₀) V'(R₀) + Q(r - R₀) V''(R₀)`, and `cont V` the
  continuation `𝓗V` of paper `cal:continuation`: `contPoly V` for `r ≤ R₀ + h_s`, the constant `V R₀` beyond.
  (The paper defines `𝓗V` for `r ≥ R₀` only; `cont` extends it to `r < R₀` by the same polynomial, which is
  never used.) `contDiffOn_glue_cont`: if `V` is `C²` on `(0, ∞)` then `V` glued to `𝓗V` at `R₀` is `C²`
  on `(0, ∞)`.
* `gamma r = -log r + π r²/2` (paper §5.2).
-/

open Set Filter

public section

namespace SandierSerfaty

namespace Calibration

/-! ### The quintic -/

/-- The quintic `10y³ - 15y⁴ + 6y⁵` of the cutoff `S`. -/
@[expose] def Squintic (y : ℝ) : ℝ := 10 * y ^ 3 - 15 * y ^ 4 + 6 * y ^ 5

/-- `Squintic'`. -/
@[expose] def Squintic1 (y : ℝ) : ℝ := 30 * y ^ 2 - 60 * y ^ 3 + 30 * y ^ 4

/-- `Squintic''`. -/
@[expose] def Squintic2 (y : ℝ) : ℝ := 60 * y - 180 * y ^ 2 + 120 * y ^ 3

/-- The clipped polynomial `S` (paper §5.3): `0` for `y ≤ 0`, `10y³ - 15y⁴ + 6y⁵` for `0 < y < 1`,
`1` for `y ≥ 1`. -/
@[expose] noncomputable def S (y : ℝ) : ℝ := if y ≤ 0 then 0 else if y < 1 then Squintic y else 1

theorem hasDerivAt_Squintic (y : ℝ) : HasDerivAt Squintic (Squintic1 y) y := by
  have h := (((hasDerivAt_pow 3 y).const_mul 10).sub ((hasDerivAt_pow 4 y).const_mul 15)).add
    ((hasDerivAt_pow 5 y).const_mul 6)
  unfold Squintic
  refine h.congr_deriv ?_
  unfold Squintic1; simp; ring

theorem hasDerivAt_Squintic1 (y : ℝ) : HasDerivAt Squintic1 (Squintic2 y) y := by
  have h := (((hasDerivAt_pow 2 y).const_mul 30).sub ((hasDerivAt_pow 3 y).const_mul 60)).add
    ((hasDerivAt_pow 4 y).const_mul 30)
  unfold Squintic1
  refine h.congr_deriv ?_
  unfold Squintic2; simp; ring

theorem deriv_Squintic : deriv Squintic = Squintic1 := funext fun y => (hasDerivAt_Squintic y).deriv

theorem deriv_Squintic1 : deriv Squintic1 = Squintic2 :=
  funext fun y => (hasDerivAt_Squintic1 y).deriv

theorem contDiff_Squintic : ContDiff ℝ ⊤ Squintic := by
  unfold Squintic; fun_prop

@[simp] theorem Squintic_zero : Squintic 0 = 0 := by simp [Squintic]
@[simp] theorem Squintic1_zero : Squintic1 0 = 0 := by simp [Squintic1]
@[simp] theorem Squintic2_zero : Squintic2 0 = 0 := by simp [Squintic2]
@[simp] theorem Squintic_one : Squintic 1 = 1 := by norm_num [Squintic]
@[simp] theorem Squintic1_one : Squintic1 1 = 0 := by norm_num [Squintic1]
@[simp] theorem Squintic2_one : Squintic2 1 = 0 := by norm_num [Squintic2]

theorem S_of_nonpos {y : ℝ} (hy : y ≤ 0) : S y = 0 := by simp [S, hy]

theorem S_of_mem_Icc {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : S y = Squintic y := by
  rcases h0.eq_or_lt with rfl | h0
  · rw [S_of_nonpos le_rfl, Squintic_zero]
  · rcases h1.eq_or_lt with rfl | h1
    · simp [S]
    · simp [S, h0.not_ge, h1]

theorem S_of_one_le {y : ℝ} (hy : 1 ≤ y) : S y = 1 := by
  rcases hy.eq_or_lt with rfl | hy
  · simp [S]
  · simp [S, (zero_lt_one.trans hy).not_ge, hy.not_gt]

/-- `S` as the nested gluing `0 | Squintic | 1`. -/
theorem S_eq_glue : S = glue 0 (fun _ => 0) (glue 1 Squintic (fun _ => 1)) := by
  funext y
  by_cases h0 : y ≤ 0
  · rw [glue_of_le h0, S_of_nonpos h0]
  · push Not at h0
    rw [glue_of_gt h0]
    by_cases h1 : y ≤ 1
    · rw [glue_of_le h1, S_of_mem_Icc h0.le h1]
    · push Not at h1
      rw [glue_of_gt h1, S_of_one_le h1.le]

theorem contDiff_S : ContDiff ℝ 2 S := by
  rw [← contDiffOn_univ, S_eq_glue]
  have hSq : ContDiffOn ℝ 2 Squintic univ := (contDiff_Squintic.of_le (by simp)).contDiffOn
  have h1 : ContDiffOn ℝ 2 (glue 1 Squintic (fun _ => 1)) univ :=
    contDiffOn_glue_two isOpen_univ (mem_univ _) hSq contDiffOn_const (by simp)
      (by simp [deriv_Squintic]) (by simp [deriv_Squintic, deriv_Squintic1])
  refine contDiffOn_glue_two isOpen_univ (mem_univ _) contDiffOn_const h1 ?_ ?_ ?_
  · simp [glue_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  · rw [(eventuallyEq_glue_left Squintic (fun _ => (1 : ℝ)) (show (0 : ℝ) < 1 by norm_num)).deriv_eq]
    simp [deriv_Squintic]
  · have := (eventuallyEq_glue_left Squintic (fun _ => (1 : ℝ)) (show (0 : ℝ) < 1 by norm_num))
    rw [this.deriv.deriv_eq]
    simp [deriv_Squintic, deriv_Squintic1]

/-! ### The polynomials `P`, `Q` and the continuation `𝓗` -/

/-- The polynomial `P(z) = z - 6z³/h_s² + 8z⁴/h_s³ - 3z⁵/h_s⁴` (paper §5.3). -/
@[expose] noncomputable def Ppoly (z : ℝ) : ℝ := z - 6 * z ^ 3 / hs ^ 2 + 8 * z ^ 4 / hs ^ 3 - 3 * z ^ 5 / hs ^ 4

/-- `P'`. -/
@[expose] noncomputable def Ppoly1 (z : ℝ) : ℝ := 1 - 18 * z ^ 2 / hs ^ 2 + 32 * z ^ 3 / hs ^ 3 - 15 * z ^ 4 / hs ^ 4

/-- `P''`. -/
@[expose] noncomputable def Ppoly2 (z : ℝ) : ℝ := -36 * z / hs ^ 2 + 96 * z ^ 2 / hs ^ 3 - 60 * z ^ 3 / hs ^ 4

/-- The polynomial `Q(z) = z²/2 - 3z³/(2h_s) + 3z⁴/(2h_s²) - z⁵/(2h_s³)` (paper §5.3). -/
@[expose] noncomputable def Qpoly (z : ℝ) : ℝ :=
  z ^ 2 / 2 - 3 * z ^ 3 / (2 * hs) + 3 * z ^ 4 / (2 * hs ^ 2) - z ^ 5 / (2 * hs ^ 3)

/-- `Q'`. -/
@[expose] noncomputable def Qpoly1 (z : ℝ) : ℝ :=
  z - 9 * z ^ 2 / (2 * hs) + 6 * z ^ 3 / hs ^ 2 - 5 * z ^ 4 / (2 * hs ^ 3)

/-- `Q''`. -/
@[expose] noncomputable def Qpoly2 (z : ℝ) : ℝ := 1 - 9 * z / hs + 18 * z ^ 2 / hs ^ 2 - 10 * z ^ 3 / hs ^ 3

theorem hasDerivAt_Ppoly (z : ℝ) : HasDerivAt Ppoly (Ppoly1 z) z := by
  have h := ((((hasDerivAt_id z).sub (((hasDerivAt_pow 3 z).const_mul 6).div_const (hs ^ 2))).add
    (((hasDerivAt_pow 4 z).const_mul 8).div_const (hs ^ 3))).sub
    (((hasDerivAt_pow 5 z).const_mul 3).div_const (hs ^ 4)))
  have e : Ppoly = fun z => id z - 6 * z ^ 3 / hs ^ 2 + 8 * z ^ 4 / hs ^ 3 - 3 * z ^ 5 / hs ^ 4 := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold Ppoly1; simp; ring

theorem hasDerivAt_Ppoly1 (z : ℝ) : HasDerivAt Ppoly1 (Ppoly2 z) z := by
  have h := ((((hasDerivAt_const z (1 : ℝ)).sub (((hasDerivAt_pow 2 z).const_mul 18).div_const (hs ^ 2))).add
    (((hasDerivAt_pow 3 z).const_mul 32).div_const (hs ^ 3))).sub
    (((hasDerivAt_pow 4 z).const_mul 15).div_const (hs ^ 4)))
  have e : Ppoly1 = fun z => (fun _ => (1 : ℝ)) z - 18 * z ^ 2 / hs ^ 2 + 32 * z ^ 3 / hs ^ 3 - 15 * z ^ 4 / hs ^ 4 := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold Ppoly2; simp; ring

theorem hasDerivAt_Qpoly (z : ℝ) : HasDerivAt Qpoly (Qpoly1 z) z := by
  have h := ((((hasDerivAt_pow 2 z).div_const 2).sub (((hasDerivAt_pow 3 z).const_mul 3).div_const (2 * hs))).add
    (((hasDerivAt_pow 4 z).const_mul 3).div_const (2 * hs ^ 2))).sub
    (((hasDerivAt_pow 5 z)).div_const (2 * hs ^ 3))
  have e : Qpoly = fun z => z ^ 2 / 2 - 3 * z ^ 3 / (2 * hs) + 3 * z ^ 4 / (2 * hs ^ 2) - z ^ 5 / (2 * hs ^ 3) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold Qpoly1; simp; ring

theorem hasDerivAt_Qpoly1 (z : ℝ) : HasDerivAt Qpoly1 (Qpoly2 z) z := by
  have h := ((((hasDerivAt_id z).sub (((hasDerivAt_pow 2 z).const_mul 9).div_const (2 * hs))).add
    (((hasDerivAt_pow 3 z).const_mul 6).div_const (hs ^ 2))).sub
    (((hasDerivAt_pow 4 z).const_mul 5).div_const (2 * hs ^ 3)))
  have e : Qpoly1 = fun z => id z - 9 * z ^ 2 / (2 * hs) + 6 * z ^ 3 / hs ^ 2 - 5 * z ^ 4 / (2 * hs ^ 3) := rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold Qpoly2; simp; ring

theorem contDiff_Ppoly : ContDiff ℝ ⊤ Ppoly := by unfold Ppoly; fun_prop
theorem contDiff_Qpoly : ContDiff ℝ ⊤ Qpoly := by unfold Qpoly; fun_prop

@[simp] theorem Ppoly_zero : Ppoly 0 = 0 := by simp [Ppoly]
@[simp] theorem Ppoly1_zero : Ppoly1 0 = 1 := by simp [Ppoly1]
@[simp] theorem Ppoly2_zero : Ppoly2 0 = 0 := by simp [Ppoly2]
@[simp] theorem Qpoly_zero : Qpoly 0 = 0 := by simp [Qpoly]
@[simp] theorem Qpoly1_zero : Qpoly1 0 = 0 := by simp [Qpoly1]
@[simp] theorem Qpoly2_zero : Qpoly2 0 = 1 := by simp [Qpoly2]

/-- All six values of `P, P', P'', Q, Q', Q''` vanish at `h_s` (paper §5.3). -/
theorem Ppoly_hs : Ppoly hs = 0 := by unfold Ppoly hs; norm_num
theorem Ppoly1_hs : Ppoly1 hs = 0 := by unfold Ppoly1 hs; norm_num
theorem Ppoly2_hs : Ppoly2 hs = 0 := by unfold Ppoly2 hs; norm_num
theorem Qpoly_hs : Qpoly hs = 0 := by unfold Qpoly hs; norm_num
theorem Qpoly1_hs : Qpoly1 hs = 0 := by unfold Qpoly1 hs; norm_num
theorem Qpoly2_hs : Qpoly2 hs = 0 := by unfold Qpoly2 hs; norm_num

/-- The polynomial continuation with prescribed 2-jet `(v₀, v₁, v₂)` at `R₀`:
`v₀ + P(r - R₀) v₁ + Q(r - R₀) v₂`. -/
@[expose] noncomputable def contPolyC (v₀ v₁ v₂ : ℝ) (r : ℝ) : ℝ :=
  v₀ + Ppoly (r - R₀) * v₁ + Qpoly (r - R₀) * v₂

/-- The polynomial `V(R₀) + P(r - R₀) V'(R₀) + Q(r - R₀) V''(R₀)` of `(cal:continuation)`. -/
@[expose] noncomputable def contPoly (V : ℝ → ℝ) (r : ℝ) : ℝ :=
  contPolyC (V R₀) (deriv V R₀) (deriv (deriv V) R₀) r

/-- The continuation `𝓗V` of `V` beyond `R₀` (paper `cal:continuation`). -/
@[expose] noncomputable def cont (V : ℝ → ℝ) (r : ℝ) : ℝ :=
  if r ≤ R₀ + hs then contPoly V r else V R₀

theorem cont_eq_glue (V : ℝ → ℝ) : cont V = glue (R₀ + hs) (contPoly V) (fun _ => V R₀) := rfl

theorem cont_of_le (V : ℝ → ℝ) {r : ℝ} (hr : r ≤ R₀ + hs) : cont V r = contPoly V r := by
  simp [cont, hr]

theorem cont_of_ge (V : ℝ → ℝ) {r : ℝ} (hr : R₀ + hs ≤ r) : cont V r = V R₀ := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [cont_of_le V le_rfl]
    simp [contPoly, contPolyC, Ppoly_hs, Qpoly_hs]
  · simp [cont, hr.not_ge]

theorem contPoly_eq (V : ℝ → ℝ) :
    contPoly V = contPolyC (V R₀) (deriv V R₀) (deriv (deriv V) R₀) := rfl

theorem hasDerivAt_contPolyC (v₀ v₁ v₂ r : ℝ) :
    HasDerivAt (contPolyC v₀ v₁ v₂) (Ppoly1 (r - R₀) * v₁ + Qpoly1 (r - R₀) * v₂) r := by
  have hs1 : HasDerivAt (fun r : ℝ => r - R₀) 1 r := (hasDerivAt_id r).sub_const R₀
  have hP := ((hasDerivAt_Ppoly (r - R₀)).comp r hs1).mul_const v₁
  have hQ := ((hasDerivAt_Qpoly (r - R₀)).comp r hs1).mul_const v₂
  have := (hP.add hQ).const_add v₀
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · ring
  · simp [contPolyC]; ring

theorem hasDerivAt_contPolyC1 (v₁ v₂ r : ℝ) :
    HasDerivAt (fun r => Ppoly1 (r - R₀) * v₁ + Qpoly1 (r - R₀) * v₂)
      (Ppoly2 (r - R₀) * v₁ + Qpoly2 (r - R₀) * v₂) r := by
  have hs1 : HasDerivAt (fun r : ℝ => r - R₀) 1 r := (hasDerivAt_id r).sub_const R₀
  have hP := ((hasDerivAt_Ppoly1 (r - R₀)).comp r hs1).mul_const v₁
  have hQ := ((hasDerivAt_Qpoly1 (r - R₀)).comp r hs1).mul_const v₂
  refine ((hP.add hQ).congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · ring
  · simp

theorem deriv_contPolyC (v₀ v₁ v₂ : ℝ) :
    deriv (contPolyC v₀ v₁ v₂) = fun r => Ppoly1 (r - R₀) * v₁ + Qpoly1 (r - R₀) * v₂ :=
  funext fun r => (hasDerivAt_contPolyC v₀ v₁ v₂ r).deriv

theorem deriv_deriv_contPolyC (v₀ v₁ v₂ : ℝ) :
    deriv (deriv (contPolyC v₀ v₁ v₂)) = fun r => Ppoly2 (r - R₀) * v₁ + Qpoly2 (r - R₀) * v₂ := by
  rw [deriv_contPolyC]
  exact funext fun r => (hasDerivAt_contPolyC1 v₁ v₂ r).deriv

theorem contDiff_contPolyC (v₀ v₁ v₂ : ℝ) : ContDiff ℝ ⊤ (contPolyC v₀ v₁ v₂) := by
  unfold contPolyC
  have := contDiff_Ppoly; have := contDiff_Qpoly
  fun_prop

theorem contDiff_contPoly (V : ℝ → ℝ) : ContDiff ℝ ⊤ (contPoly V) := contDiff_contPolyC _ _ _

/-- The 2-jet of `contPolyC v₀ v₁ v₂` at `R₀` is `(v₀, v₁, v₂)`. -/
theorem contPolyC_jet_R₀ (v₀ v₁ v₂ : ℝ) :
    contPolyC v₀ v₁ v₂ R₀ = v₀ ∧ deriv (contPolyC v₀ v₁ v₂) R₀ = v₁ ∧
      deriv (deriv (contPolyC v₀ v₁ v₂)) R₀ = v₂ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contPolyC]
  · simp [deriv_contPolyC]
  · simp [deriv_deriv_contPolyC]

/-- The 2-jet of `contPolyC v₀ v₁ v₂` at `R₀ + h_s` is `(v₀, 0, 0)`: it joins the constant. -/
theorem contPolyC_jet_hs (v₀ v₁ v₂ : ℝ) :
    contPolyC v₀ v₁ v₂ (R₀ + hs) = v₀ ∧ deriv (contPolyC v₀ v₁ v₂) (R₀ + hs) = 0 ∧
      deriv (deriv (contPolyC v₀ v₁ v₂)) (R₀ + hs) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [contPolyC, Ppoly_hs, Qpoly_hs]
  · simp [deriv_contPolyC, Ppoly1_hs, Qpoly1_hs]
  · simp [deriv_deriv_contPolyC, Ppoly2_hs, Qpoly2_hs]

/-- `𝓗V` is `C²` on `(0, ∞)` (it is a polynomial up to `R₀ + h_s` and constant afterwards, the
2-jets matching). -/
theorem contDiffOn_cont (V : ℝ → ℝ) : ContDiffOn ℝ 2 (cont V) (Ioi 0) := by
  rw [cont_eq_glue]
  obtain ⟨j0, j1, j2⟩ := contPolyC_jet_hs (V R₀) (deriv V R₀) (deriv (deriv V) R₀)
  refine contDiffOn_glue_two isOpen_Ioi (by have := R₀_pos; have := hs_pos; simp only [mem_Ioi]; linarith)
    ((contDiff_contPoly V).of_le (by simp)).contDiffOn contDiffOn_const j0 ?_ ?_
  · rw [contPoly_eq]; simpa using j1
  · rw [contPoly_eq]; simpa using j2

/-- If `V` is `C²` on `(0, ∞)` then `V` glued to `𝓗V` at `R₀` is `C²` on `(0, ∞)`: the 2-jets of `V` and
of `𝓗V` agree at `R₀` because `(P, P', P'')(0) = (0, 1, 0)` and `(Q, Q', Q'')(0) = (0, 0, 1)`. -/
theorem contDiffOn_glue_cont {V : ℝ → ℝ} (hV : ContDiffOn ℝ 2 V (Ioi 0)) :
    ContDiffOn ℝ 2 (glue R₀ V (cont V)) (Ioi 0) := by
  obtain ⟨j0, j1, j2⟩ := contPolyC_jet_R₀ (V R₀) (deriv V R₀) (deriv (deriv V) R₀)
  have hev : cont V =ᶠ[nhds R₀] contPoly V :=
    eventuallyEq_glue_left (contPoly V) (fun _ => V R₀) (a := R₀ + hs) (x := R₀)
      (by have := hs_pos; linarith)
  refine contDiffOn_glue_two isOpen_Ioi (by have := R₀_pos; simpa using this) hV
    (contDiffOn_cont V) ?_ ?_ ?_
  · rw [hev.eq_of_nhds]; exact j0.symm
  · rw [hev.deriv_eq]; exact j1.symm
  · rw [hev.deriv.deriv_eq]; exact j2.symm

/-! ### The radial part `γ` -/

/-- `γ(r) = -log r + π r²/2` (paper §5.2). -/
@[expose] noncomputable def gamma (r : ℝ) : ℝ := -Real.log r + Real.pi * r ^ 2 / 2

theorem contDiffOn_gamma : ContDiffOn ℝ ⊤ gamma (Ioi 0) := by
  have hlog : ContDiffOn ℝ ⊤ Real.log (Ioi 0) :=
    Real.contDiffOn_log.mono (fun x hx => ne_of_gt hx)
  unfold gamma
  exact (hlog.neg).add (by fun_prop)

end Calibration

end SandierSerfaty
