/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Assemble.Defs
public import SandierSerfaty.Certificate.Basis.CoeffSound

/-!
# Assertion A1 by rows: soundness

The row-checkpointed form of `Basis.coeffsCheck` (`Assemble.rowB`, `rowsB`, `coeffFinB`): if every row
`c ≤ 2D` of the box passes `rowB` against the literal checkpoints `rowCk` and the final test `coeffFinB`
passes, then the literal list `cos` encloses `coeff m₀, coeff (m₀ + 1), …` (`coeffs_of_rows`), exactly the
conclusion of `Basis.coeffsCheck_sound`. The proof reuses the loop lemmas of `Basis.CoeffSound`
(`enclFrom_rowLoop`, `boxSumR_eq`, `enclFrom_coeffsFrom`).

Also: `enclFrom_append` (enclosures of concatenated coefficient blocks) and the splitting of `rowsB`.
-/

open Finset

public section

namespace SandierSerfaty.Certificate.Assemble

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Calibration

theorem enclFrom_append {g : ℕ → ℝ} :
    ∀ {m : ℕ} {l1 l2 : List (IV 128)}, EnclFrom g m l1 → EnclFrom g (m + l1.length) l2 → EnclFrom g m (l1 ++ l2)
  | _, [], _, _, h2 => by simpa using h2
  | m, a :: as, l2, ⟨h1, h1'⟩, h2 =>
    ⟨h1, enclFrom_append h1' (by simpa [Nat.add_assoc, Nat.add_comm 1] using h2)⟩

/-- The row `c` of the box sum. -/
noncomputable def rowSum (D : ℕ) (j c : ℕ) : ℝ :=
  ∑ c' ∈ range (2 * D + 1), cterm j ((c : ℤ) - D, (c' : ℤ) - D)

theorem enclFrom_rows {m0 D cnt : ℕ} (hm : 1 ≤ m0) {rowCk : ℕ → List (IV 128)} :
    ∀ C : ℕ, (∀ c, c ≤ C → rowB m0 D cnt rowCk c = true) →
      EnclFrom (fun j => ∑ c ∈ range (C + 1), rowSum D j c) m0 (rowCk C)
  | 0, h => by
    have h0 := h 0 le_rfl
    simp only [rowB, prevAcc] at h0
    have := enclFrom_rowLoop hm D (SInt.sub ⟨false, 0⟩ ⟨false, D⟩) (Nat.add (Nat.mul 2 D) 1) _ _
      (enclFrom_zeros (P := 128) m0 cnt)
    rw [toInt_sub_nat, show Nat.add (Nat.mul 2 D) 1 = 2 * D + 1 from rfl] at this
    refine enclFrom_of_subsetList h0 (EnclFrom.congr (fun j _ => ?_) this)
    simp [rowSum]
  | C + 1, h => by
    have ih := enclFrom_rows hm C fun c hc => h c (by omega)
    have h1 := h (C + 1) le_rfl
    simp only [rowB, prevAcc] at h1
    have := enclFrom_rowLoop hm D (SInt.sub ⟨false, C + 1⟩ ⟨false, D⟩) (Nat.add (Nat.mul 2 D) 1) _ _ ih
    rw [toInt_sub_nat, show Nat.add (Nat.mul 2 D) 1 = 2 * D + 1 from rfl] at this
    refine enclFrom_of_subsetList h1 (EnclFrom.congr (fun j _ => ?_) this)
    rw [sum_range_succ _ (C + 1)]
    rfl

/-- **Assertion A1 from the rows.** -/
theorem coeffs_of_rows {l h m0 D cnt : ℕ} (hm : 1 ≤ m0) (hD : 1 ≤ D) {rowCk : ℕ → List (IV 128)}
    {cos : List (IV 128)} (hr : ∀ c, c ≤ 2 * D → rowB m0 D cnt rowCk c = true)
    (hf : coeffFinB l h m0 D rowCk cos = true) : EnclFrom coeff m0 cos := by
  simp only [coeffFinB, Bool.and_eq_true] at hf
  have hE := enclFrom_rows hm (2 * D) hr
  have hE' : EnclFrom (fun j => boxSumR j D) m0 (rowCk (2 * D)) :=
    EnclFrom.congr (fun j _ => by rw [boxSumR_eq]; rfl) hE
  have h3 := IV.mem_sqrt_of_sqrtCheck hf.1 (IV.mem_ofNat (P := 128) 3)
  have hs : IV.Mem (√3 / 2) (sqrt3Half l h : IV 128) := by
    have := IV.mem_divPow2 (by simpa using h3) 1
    simpa [sqrt3Half] using this
  exact enclFrom_of_subsetList hf.2 (enclFrom_coeffsFrom hs hD hm hE')

theorem rowsB_sound {m0 D cnt : ℕ} {rowCk : ℕ → List (IV 128)} :
    ∀ {c r : ℕ}, rowsB m0 D cnt rowCk c r = true → ∀ i, c ≤ i → i < c + r → rowB m0 D cnt rowCk i = true
  | _, 0, _, i, h1, h2 => absurd h2 (by omega)
  | c, r + 1, h, i, h1, h2 => by
    simp only [rowsB, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · exact e ▸ h.1
    · exact rowsB_sound h.2 i lt (by omega)

/-- Extending a row range by a consecutive one. -/
theorem rows_extend {m0 D cnt : ℕ} {rowCk : ℕ → List (IV 128)} {c r s : ℕ}
    (h1 : ∀ i, c ≤ i → i < c + r → rowB m0 D cnt rowCk i = true) (h2 : rowsB m0 D cnt rowCk (c + r) s = true) :
    ∀ i, c ≤ i → i < c + (r + s) → rowB m0 D cnt rowCk i = true := fun i hi hi' => by
  rcases lt_or_ge i (c + r) with h | h
  · exact h1 i hi h
  · exact rowsB_sound h2 i h (by omega)

end SandierSerfaty.Certificate.Assemble
