/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Sphere.Minimizer
public import SandierSerfaty.Sphere.Lower.Statements
public import SandierSerfaty.Statements.Sphere.Defs.SphereLogEnergy
public import SandierSerfaty.Statements.Sphere.Defs.BhsConstant
public import SandierSerfaty.ClosedForm.TriangularEnergyClosedForm

/-!
# The statement of paper Corollary 1.3 versus the sphere development

The statement of `sphereLogEnergy_asymptotics` (paper Corollary 1.3) works with `logPairEnergy`, `logConfigEnergy` and
`sphereLogEnergy n = ⨅ y, logConfigEnergy y` in `EReal` over configurations in the unit sphere, and the
constant `bhsConstant`. The sphere development works with the real energy `Sphere.sphereEnergy`, its
normalization `Sphere.normalizedEnergy` and minimizers `Sphere.IsSphereMinimizer`. This file proves:

* `Sphere.Bridge.logConfigEnergy_eq_of_injective`: for distinct points, `logConfigEnergy y` is the real
  `sphereEnergy` of the points; `logConfigEnergy_eq_top_of_not_injective`: a collision gives `⊤`;
* `Sphere.Bridge.sphereLogEnergy_eq`: `sphereLogEnergy n = sphereEnergy Y` for every minimizer `Y`
  (every `n`);
* `Sphere.Bridge.sphereLogEnergy_eq_normalizedEnergy`: the same with the normalization of `𝔎`;
* `Sphere.Bridge.bhsConstant_eq_triangularEnergy`: `C_BHS = W_tri / π + ½ log π + log 2`, and
  `bhsConstant_eq_cTri`: `C_BHS = C_tri = ½ log (4π) + W_tri / π` (sphere note, Definition 2.5);
* `Sphere.Bridge.sphereLogEnergyAsymptotics_iff`: the statement of paper Corollary 1.3 is equivalent to
  `min 𝔎 = C_tri n + o(n)` for minimizers.
-/

open Filter Asymptotics

public section

namespace SandierSerfaty

namespace Sphere

namespace Bridge

theorem sum_offDiag_eq {β : Type*} [AddCommMonoid β] {n : ℕ} (f : Fin n → Fin n → β) :
    ∑ p ∈ (Finset.univ : Finset (Fin n)).offDiag, f p.1 p.2 =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  classical
  have e : (Finset.univ : Finset (Fin n)).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => p.1 ≠ p.2) := by
    ext p; simp [Finset.mem_offDiag]
  rw [e, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  congr 1
  ext j; simp [eq_comm]

theorem coe_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem finsetSum_ne_bot {ι : Type*} (s : Finset ι) {f : ι → EReal} (hf : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact EReal.add_ne_bot_iff.2 ⟨hf a (Finset.mem_insert_self a s),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)⟩

theorem finsetSum_eq_top {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → EReal} {a : ι}
    (ha : a ∈ s) (hfa : f a = ⊤) (hf : ∀ i ∈ s, f i ≠ ⊥) : ∑ i ∈ s, f i = ⊤ := by
  rw [← Finset.add_sum_erase s f ha, hfa]
  exact EReal.top_add_of_ne_bot (finsetSum_ne_bot _ fun i hi => hf i (Finset.mem_of_mem_erase hi))

theorem logPairEnergy_ne_bot (x y : EuclideanSpace ℝ (Fin 3)) : logPairEnergy x y ≠ ⊥ := by
  unfold logPairEnergy
  split_ifs
  · exact top_ne_bot
  · exact EReal.coe_ne_bot _

/-- For pairwise distinct points of the sphere, the configuration energy `logConfigEnergy` is the real
`sphereEnergy`. -/
theorem logConfigEnergy_eq_of_injective {n : ℕ}
    (y : Fin n → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hy : Function.Injective y) :
    logConfigEnergy y = ((sphereEnergy (fun i => (y i : R3)) : ℝ) : EReal) := by
  unfold logConfigEnergy
  rw [sum_offDiag_eq (fun i j => logPairEnergy (y i) (y j)), sphereEnergy, coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coe_finsetSum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne : (y i : EuclideanSpace ℝ (Fin 3)) ≠ y j := fun h =>
    (Finset.ne_of_mem_erase hj) (hy (Subtype.ext h)).symm
  simp [logPairEnergy, hne]

/-- A collision gives energy `⊤`. -/
theorem logConfigEnergy_eq_top_of_not_injective {n : ℕ}
    (y : Fin n → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hy : ¬ Function.Injective y) :
    logConfigEnergy y = ⊤ := by
  classical
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, y i = y j ∧ i ≠ j := by
    by_contra h
    exact hy fun i j hij => by_contra fun hne => h ⟨i, j, hij, hne⟩
  unfold logConfigEnergy
  refine finsetSum_eq_top (a := (i, j)) (Finset.mem_offDiag.2 ⟨Finset.mem_univ _,
    Finset.mem_univ _, hne⟩) ?_ fun p _ => logPairEnergy_ne_bot _ _
  simp [logPairEnergy, hij]

/-- The points of a minimizer, as points of the sphere. -/
def toSphere {n : ℕ} {Y : Fin n → R3} (hY : IsSphereMinimizer Y) :
    Fin n → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  fun i => ⟨Y i, by simpa using hY.norm_eq i⟩

/-- **`E_log(n)` is the minimal `sphereEnergy`**: for every minimizer `Y` (they exist for every `n`,
`exists_isSphereMinimizer`), `sphereLogEnergy n = sphereEnergy Y`. -/
theorem sphereLogEnergy_eq {n : ℕ} {Y : Fin n → R3} (hY : IsSphereMinimizer Y) :
    sphereLogEnergy n = ((sphereEnergy Y : ℝ) : EReal) := by
  have hinj : Function.Injective (toSphere hY) := fun i j h =>
    hY.injective (congrArg Subtype.val h)
  have hval : logConfigEnergy (toSphere hY) = ((sphereEnergy Y : ℝ) : EReal) :=
    logConfigEnergy_eq_of_injective _ hinj
  refine le_antisymm (hval ▸ iInf_le _ _) (le_iInf fun y => ?_)
  by_cases hy : Function.Injective y
  · rw [logConfigEnergy_eq_of_injective y hy, EReal.coe_le_coe_iff]
    refine hY.le _ (fun i => by simp) fun i j h => hy (Subtype.ext h)
  · rw [logConfigEnergy_eq_top_of_not_injective y hy]; exact le_top

/-- `E_log(n)` in terms of the normalized energy `𝔎` of a minimizer. -/
theorem sphereLogEnergy_eq_normalizedEnergy {n : ℕ} {Y : Fin n → R3} (hY : IsSphereMinimizer Y) :
    sphereLogEnergy n =
      ((((1 / 2 : ℝ) - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + normalizedEnergy Y :
        ℝ) : EReal) := by
  rw [sphereLogEnergy_eq hY, EReal.coe_eq_coe_iff, normalizedEnergy]
  ring

/-- `C_BHS = W_tri / π + ½ log π + log 2` ([Bétermin–Sandier 2018, Theorem 1.5] / the sphere note's `C_tri`), from the closed form
`ClosedForm.triangularEnergy_eq`. -/
theorem bhsConstant_eq_triangularEnergy :
    bhsConstant = triangularEnergy / Real.pi + (1 / 2) * Real.log Real.pi + Real.log 2 := by
  have hπ := Real.pi_pos
  have hG : 0 < Real.Gamma (1 / 3) := Real.Gamma_pos_of_pos (by norm_num)
  have h2 : (0 : ℝ) < √2 := Real.sqrt_pos.2 (by norm_num)
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.2 (by norm_num)
  have hsπ : (0 : ℝ) < √Real.pi := Real.sqrt_pos.2 hπ
  set G := Real.Gamma (1 / 3) with hGdef
  have e1 : Real.log (2 * √2 * Real.pi / (√3 * G ^ 3)) =
      Real.log 2 + Real.log √2 + Real.log Real.pi - (Real.log √3 + 3 * Real.log G) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (x := 2 * √2) (y := Real.pi) (by positivity) hπ.ne',
      Real.log_mul (x := 2) (y := √2) (by norm_num) h2.ne',
      Real.log_mul (x := √3) (y := G ^ 3) h3.ne' (by positivity), Real.log_pow]
    push_cast; ring
  have e2 : Real.log (√Real.pi / G) = Real.log √Real.pi - Real.log G := Real.log_div hsπ.ne' hG.ne'
  have e3 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  rw [ClosedForm.triangularEnergy_eq, mul_div_cancel_left₀ _ hπ.ne', e1]
  unfold bhsConstant
  rw [← hGdef, e2, e3, Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.log_sqrt hπ.le]
  ring

/-- `C_BHS = C_tri = ½ log (4π) + W_tri / π`. -/
theorem bhsConstant_eq_cTri : bhsConstant = Lower.cTri := by
  rw [bhsConstant_eq_triangularEnergy, Lower.cTri,
    Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

/-- **Paper Corollary 1.3 in the sphere development's terms**: the statement of
`sphereLogEnergy_asymptotics` (written out, not imported) is equivalent to
`𝔎(Y) = C_tri n + o(n)` uniformly over minimizers `Y` of `n ≥ 2` points. -/
theorem sphereLogEnergyAsymptotics_iff :
    (∃ r : ℕ → ℝ, (r =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 2 ≤ n →
      sphereLogEnergy n =
        ((((1 / 2 : ℝ) - Real.log 2) * (n : ℝ) ^ 2 - (n : ℝ) / 2 * Real.log n + bhsConstant * n +
          r n : ℝ) : EReal)) ↔
    (∃ r : ℕ → ℝ, (r =o[atTop] fun n : ℕ ↦ (n : ℝ)) ∧ ∀ n : ℕ, 2 ≤ n →
      ∀ Y : Fin n → R3, IsSphereMinimizer Y → normalizedEnergy Y = Lower.cTri * n + r n) := by
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, fun n hn Y hY => ?_⟩
    have := h n hn
    rw [sphereLogEnergy_eq_normalizedEnergy hY, EReal.coe_eq_coe_iff, bhsConstant_eq_cTri] at this
    linarith
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, fun n hn => ?_⟩
    obtain ⟨Y, hY⟩ := exists_isSphereMinimizer n
    rw [sphereLogEnergy_eq_normalizedEnergy hY, EReal.coe_eq_coe_iff, h n hn Y hY,
      bhsConstant_eq_cTri]
    ring

end Bridge

end Sphere

end SandierSerfaty

end
