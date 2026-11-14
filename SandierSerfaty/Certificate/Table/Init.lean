/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Table.StepSound

/-!
# The initial checkpoint of the propagation (`comp:initial-integrals`)

At the node `p - c` the propagation starts from the exact values

* `S̃₁(t) = t²/2 (1/2 - log t) + π t⁴/8 + ∑_{m=1}^{38} a_m t^{k_m+2}/(k_m + 2)`,
* `S̃₂(t) = -2 ∑_i v_i t^{e_i}/e_i + ∑_{i,j} v_i v_j t^{e_i+e_j}/(e_i + e_j)`,
* `H̃_k(t) = ∑_i v_i t^{e_i}/(e_i + k)`,

with `a_m = (-1)^m c_m`, `(e_0, v_0) = (2, π)`, `(e_m, v_m) = (k_m, k_m a_m)`. These are the functions `S1init`,
`S2init`, `Hinit` below; `initCheck_sound` shows that a literal checkpoint accepted by `initCheck` encloses them
at every point of the node interval. (That the truncated sector functions `Cal.Trunc.S₁, S₂, H` take these
values on `(0, p - c]` is the analytic part of the bridge of the table model to `Cal.Trunc`.)
-/

open Set

public section

namespace SandierSerfaty.Certificate.Table

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Jet SandierSerfaty.Certificate.Basis
open SandierSerfaty.Calibration

/-- The exponents `e_0 = 2`, `e_m = k_m` of the monomials of `t B̃₁` on the first segment. -/
@[expose] def eI (i : ℕ) : ℕ := if i = 0 then 2 else k i

/-- The monomials `w_0 = π t²`, `w_m = k_m a_m t^{k_m}` (`a_m = (-1)^m c_m`). -/
@[expose] noncomputable def wI (t : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then Real.pi * t ^ 2 else (k i : ℝ) * ((-1) ^ i * coeff i) * t ^ k i

/-- `S̃₁` on the first segment. -/
@[expose] noncomputable def S1init (t : ℝ) : ℝ :=
  t ^ 2 / 2 * (1 / 2 - Real.log t) + Real.pi * t ^ 4 / 8 +
    ∑ n ∈ Finset.range 38, (-1) ^ (n + 1) * coeff (n + 1) * t ^ k (n + 1) * t ^ 2 / ((k (n + 1) + 2 : ℕ) : ℝ)

/-- `∑_{i ≤ 38} w_i/(e_i + c)`. -/
@[expose] noncomputable def termSumR (c : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 39, wI t i / ((eI i + c : ℕ) : ℝ)

/-- `S̃₂` on the first segment. -/
@[expose] noncomputable def S2init (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 39, wI t i * termSumR (eI i) t - termSumR 0 t * 2

/-- `H̃_k` on the first segment. -/
@[expose] noncomputable def Hinit (c : ℕ) (t : ℝ) : ℝ := termSumR c t

/-- The list encloses the monomials `(e_m, w_m), (e_{m+1}, w_{m+1}), …` at `t`. -/
@[expose] def TermsEncl (t : ℝ) : ℕ → List (ℕ × IV 128) → Prop
  | _, [] => True
  | m, p :: ps => p.1 = eI m ∧ IV.Mem (wI t m) p.2 ∧ TermsEncl t (m + 1) ps

theorem eI_pos (i : ℕ) : 0 < eI i := by
  unfold eI; split_ifs
  · norm_num
  · exact k_pos i

theorem termsFrom_encl {t : ℝ} {t6 : IV 128} (h6 : IV.Mem (t ^ 6) t6) :
    ∀ (mds : List ModeData) (m : ℕ) (tk : IV 128), 1 ≤ m → ModesValid m mds → IV.Mem (t ^ (6 * m)) tk →
      TermsEncl t m (termsFrom t6 mds tk)
  | [], _, _, _, _, _ => trivial
  | md :: mds, m, tk, hm, ⟨hmd, hmds⟩, htk => by
    have hm0 : m ≠ 0 := by omega
    have hk : k m = 6 * m := k_of_pos (by omega)
    refine ⟨?_, ?_, termsFrom_encl h6 mds (m + 1) _ (by omega) hmds ?_⟩
    · simp [eI, hm0, hmd.k_eq, hk]
    · have := IV.mem_mul (IV.mem_mulNat hmd.sc md.k) htk
      refine mem_of_eq this ?_
      simp only [wI, hm0, ite_false, hmd.k_eq, hk]
      push_cast; ring
    · exact mem_of_eq (IV.mem_mul htk h6) (by rw [show 6 * (m + 1) = 6 * m + 6 by ring, pow_add])

theorem termsFrom_length (t6 : IV 128) : ∀ (mds : List ModeData) (tk : IV 128),
    (termsFrom t6 mds tk).length = mds.length
  | [], _ => rfl
  | _ :: mds, tk => by simp [termsFrom, termsFrom_length t6 mds]

theorem termSum_mem {t : ℝ} (c : ℕ) : ∀ (ts : List (ℕ × IV 128)) (m : ℕ), TermsEncl t m ts →
    IV.Mem (∑ n ∈ Finset.range ts.length, wI t (m + n) / ((eI (m + n) + c : ℕ) : ℝ)) (termSum c ts)
  | [], _, _ => by simp [termSum, IV.Mem, SInt.zero, SInt.toInt_mk]
  | (e, w) :: ts, m, ⟨he, hw, hts⟩ => by
    simp only at he hw
    subst he
    have ih := termSum_mem c ts (m + 1) hts
    have hd := IV.mem_divNat hw (show 0 < Nat.add (eI m) c by simp only [Nat.add_eq]; have := eI_pos m; omega)
    refine mem_of_eq (IV.mem_add hd ih) ?_
    rw [List.length_cons, Finset.sum_range_succ' _ ts.length, add_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

theorem termSum2_mem {t : ℝ} {all : List (ℕ × IV 128)} (hall : TermsEncl t 0 all) (h39 : all.length = 39) :
    ∀ (ts : List (ℕ × IV 128)) (m : ℕ), TermsEncl t m ts →
      IV.Mem (∑ n ∈ Finset.range ts.length, wI t (m + n) * termSumR (eI (m + n)) t) (termSum2 all ts)
  | [], _, _ => by simp [termSum2, IV.Mem, SInt.zero, SInt.toInt_mk]
  | (e, w) :: ts, m, ⟨he, hw, hts⟩ => by
    simp only at he hw
    subst he
    have ih := termSum2_mem hall h39 ts (m + 1) hts
    have hin := termSum_mem (eI m) all 0 hall
    rw [h39] at hin
    simp only [zero_add] at hin
    refine mem_of_eq (IV.mem_add (IV.mem_mul hw hin) ih) ?_
    rw [List.length_cons, Finset.sum_range_succ' _ ts.length, add_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]

theorem hInitL_encl {t : ℝ} {tms : List (ℕ × IV 128)} (htms : TermsEncl t 0 tms) (h39 : tms.length = 39) :
    ∀ (ks : List ℕ) (m : ℕ), KList m ks → EnclFrom (fun i => Hinit (k i) t) m (hInitL tms ks)
  | [], _, _ => trivial
  | x :: ks, m, ⟨hx, hks⟩ => by
    refine ⟨?_, hInitL_encl htms h39 ks (m + 1) hks⟩
    have := termSum_mem x tms 0 htms
    rw [h39] at this
    simpa [Hinit, termSumR, hx] using this

theorem hInitL_length (tms : List (ℕ × IV 128)) : ∀ ks : List ℕ, (hInitL tms ks).length = ks.length
  | [] => rfl
  | _ :: ks => by simp [hInitL, hInitL_length tms ks]

theorem s1Sum_mem {t : ℝ} {t2 t6 : IV 128} (h2 : IV.Mem (t ^ 2) t2) (h6 : IV.Mem (t ^ 6) t6) :
    ∀ (mds : List ModeData) (m : ℕ) (tk : IV 128), 1 ≤ m → ModesValid m mds → IV.Mem (t ^ (6 * m)) tk →
      IV.Mem (∑ n ∈ Finset.range mds.length, (-1) ^ (m + n) * coeff (m + n) * t ^ k (m + n) * t ^ 2 /
        ((k (m + n) + 2 : ℕ) : ℝ)) (s1Sum t2 t6 mds tk)
  | [], _, _, _, _, _ => by simp [s1Sum, IV.Mem, SInt.zero, SInt.toInt_mk]
  | md :: mds, m, tk, hm, ⟨hmd, hmds⟩, htk => by
    have hk : k m = 6 * m := k_of_pos (by omega)
    have ih := s1Sum_mem h2 h6 mds (m + 1) _ (by omega) hmds
      (mem_of_eq (IV.mem_mul htk h6) (by rw [show 6 * (m + 1) = 6 * m + 6 by ring, pow_add]))
    have hd := IV.mem_divNat (IV.mem_mul (IV.mem_mul hmd.sc htk) h2) (show 0 < Nat.add md.k 2 by
      simp only [Nat.add_eq]; omega)
    refine mem_of_eq (IV.mem_add hd ih) ?_
    rw [List.length_cons, Finset.sum_range_succ' _ mds.length, add_zero, add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun n _ => by rw [show m + 1 + n = m + (n + 1) by omega]
    · rw [hk, hmd.k_eq]

/-- **Soundness of the initial checkpoint.** If `initCheck d X S = true` and `t ∈ X`, the state `S` encloses the
closed forms `S1init t`, `S2init t`, `Hinit (k i) t`. -/
theorem initCheck_sound {d : BasisData} (hd : d.Valid) {X : IV 128} {S : SState} (hc : initCheck d X S = true)
    {t : ℝ} (ht : IV.Mem t X) : StateOn {t} S1init S2init (fun i => Hinit (k i)) S := by
  simp only [initCheck, Bool.and_eq_true] at hc
  obtain ⟨hX, hsub⟩ := hc
  have h2 : IV.Mem (t ^ 2) (IV.sq X) := IV.mem_sq ht
  have h6 : IV.Mem (t ^ 6) (ivPow X 6) := mem_ivPow ht 6
  have htms : TermsEncl t 0 (initTerms d X) := by
    refine ⟨rfl, ?_, termsFrom_encl h6 d.modes 1 _ le_rfl hd.modes (by simpa using h6)⟩
    simpa [wI] using IV.mem_mul hd.mpi h2
  have h39 : (initTerms d X).length = 39 := by simp [initTerms, termsFrom_length, hd.len]
  -- the computed state
  have hs1 : IV.Mem (S1init t) (s1Init d X) := by
    have hl := IV.mem_logPos hX ht
    have a1 := IV.mem_mul (IV.mem_divPow2 h2 1) (IV.mem_sub (by simpa using mem_frac_pos 1 2 (by norm_num)) hl)
    have a2 := IV.mem_divNat (IV.mem_mul hd.mpi (IV.mem_sq h2)) (show 0 < 8 by norm_num)
    have a3 := s1Sum_mem h2 h6 d.modes 1 _ le_rfl hd.modes (by simpa using h6)
    rw [hd.len] at a3
    refine mem_of_eq (IV.mem_add (IV.mem_add a1 a2) a3) ?_
    simp only [S1init]
    congr 1
    ring
  have hs2 : IV.Mem (S2init t) (s2Init (initTerms d X)) := by
    have a1 := termSum2_mem htms h39 _ 0 htms
    have a2 := termSum_mem 0 _ 0 htms
    rw [h39] at a1 a2
    refine mem_of_eq (IV.mem_sub a1 (IV.mem_mulNat a2 2)) ?_
    simp [S2init, termSumR]
  have hk : KList 0 (6 :: ksOf d.modes) := ⟨by simp [k], ksOf_klist d.modes 1 le_rfl hd.modes⟩
  have hH := hInitL_encl htms h39 _ 0 hk
  simp only [stateSub, Bool.and_eq_true] at hsub
  obtain ⟨⟨u1, u2⟩, u3⟩ := hsub
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · rw [hx]; exact IV.mem_of_subsetB u1 hs1
  · rw [hx]; exact IV.mem_of_subsetB u2 hs2
  · rw [hx]; exact enclFrom_of_subList u3 hH
  · rw [← subList_length u3]
    simp [initStateOf, hInitL_length, ksOf_length, hd.len]

end SandierSerfaty.Certificate.Table
