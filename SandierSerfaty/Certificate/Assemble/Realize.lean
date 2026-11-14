/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Assemble.Table
public import SandierSerfaty.Certificate.Lambda.Model

/-!
# The whole radial table realized by the segment models

`tableModel_of_checks`: from the same checks as `Assemble.tableEncl_of_checks` (the nodes, the chunks of the six
segments, the initial checkpoint), **`Lambda.TableModel ⟨⟨K 6, node, ct⟩, nt⟩ (realNode node K)`**: every cell of
the segments `1, …, 5` with its right node tuple encloses the model of its segment (`Assemble.seg_sound`), and every
cell of the first segment, checked against the exact inner closed form (`Assemble.inner_sound`), encloses the model
`F0m 0`, `Em 0` (`Lambda.TupEncl.model_of_inner`). This is the realization behind `Box.TableRealized`,
`Lambda.FRealized` and `Box.QRealizes` (`TableModel.tableRealized`, `.fRealized`, `.qRealizes`).
-/

open Set

public section

namespace SandierSerfaty.Certificate.Assemble

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Calibration
open SandierSerfaty.Tails

/-- **The table model from its checks.** The hypotheses are those of `tableEncl_of_checks`. -/
theorem tableModel_of_checks {d : BasisData} (hd : d.Valid) {node : ℕ → IV 128}
    {ct nt : ℕ → Tup} {ck : ℕ → SState} {K Ls Ns : ℕ → ℕ} (hK0 : K 0 = 0)
    (hK : ∀ j, j ≤ 5 → K (j + 1) = K j + Ls j * Ns j) (hL : ∀ j, j ≤ 5 → 1 ≤ Ls j)
    (hN : ∀ j, j ≤ 5 → 1 ≤ Ns j) (hnodes : nodesB d node K (K 6) = true)
    (hinner : ∀ c < Ns 0, innerB (Ls 0) d.pi node ct nt (K 0 + Ls 0 * c) = true)
    (hinit : initCheck d (node (K 1)) (ck (K 1)) = true)
    (hchunks : ∀ j, 1 ≤ j → j ≤ 5 → ∀ c < Ns j, chunkB (Ls j) d node ct nt ck j (K j + Ls j * c) = true) :
    TableModel ⟨⟨K 6, node, ct⟩, nt⟩ (realNode node K) := by
  set a := realNode node K with ha_def
  have hKup : KnotsUp K := by
    have hpos : ∀ j, j ≤ 5 → K j < K (j + 1) := fun j hj => by
      rw [hK j hj]; have := Nat.mul_le_mul (hL j hj) (hN j hj); omega
    exact ⟨hpos 0 (by norm_num), hpos 1 (by norm_num), hpos 2 (by norm_num), hpos 3 (by norm_num),
      hpos 4 (by norm_num), hpos 5 le_rfl⟩
  obtain ⟨hmem, hlt⟩ := nodesB_sound hd hKup hnodes
  have hmono : ∀ i, i < K 6 → a i ≤ a (i + 1) := fun i hi => (hlt i hi).le
  have hmo := mono_of_step (a := a) (i0 := 0) (n := K 6) fun i _ hi => hmono i hi
  have haK : ∀ j, j ≤ 6 → a (K j) = knot j := fun j hj => realNode_K hKup hj
  have hKm : ∀ j j', j ≤ j' → j' ≤ 6 → K j ≤ K j' := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hKup
    intro j j' hjj hj'
    have hj6 : j ≤ 6 := by omega
    interval_cases j <;> interval_cases j' <;> omega
  -- the segments `1, …, 5`, chained by their checkpoints
  have segj : ∀ j, 1 ≤ j → j ≤ 5 → StateOn {a (K j)} Trunc.S₁ Trunc.S₂ TH (ck (K j)) →
      (∀ i, K j ≤ i → i < K (j + 1) →
        TupEncl (Icc (a i) (a (i + 1))) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (ct i) ∧
          TupEncl {a (i + 1)} (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (nt i)) ∧
        StateOn {a (K (j + 1))} Trunc.S₁ Trunc.S₂ TH (ck (K (j + 1))) := by
    intro j hj1 hj h0
    have hKj := hK j hj
    have := seg_sound hd hj (hL j hj) (node := node) (ct := ct) (nt := nt) (ck := ck) (a := a) (i0 := K j)
      (N := Ns j) (hchunks j hj1 hj) (fun i _ hi => hmem i (by have := hKm (j + 1) 6 (by omega) le_rfl; omega))
      (fun i _ hi => hmono i (by have := hKm (j + 1) 6 (by omega) le_rfl; omega))
      (by rw [← hKj, haK j (by omega), haK (j + 1) (by omega), seg_eq_Icc hj1 hj]) h0
    rw [← hKj] at this
    exact this
  have h01 : StateOn {a (K 1)} Trunc.S₁ Trunc.S₂ TH (ck (K 1)) :=
    initCheck_sound_trunc hd hinit (hmem (K 1) (hKm 1 6 (by norm_num) le_rfl)) (by rw [haK 1 (by norm_num)]; rfl)
  have s1 := segj 1 le_rfl (by norm_num) h01
  have s2 := segj 2 (by norm_num) (by norm_num) s1.2
  have s3 := segj 3 (by norm_num) (by norm_num) s2.2
  have s4 := segj 4 (by norm_num) (by norm_num) s3.2
  have s5 := segj 5 (by norm_num) le_rfl s4.2
  have hcells : ∀ j, 1 ≤ j → j ≤ 5 → ∀ i, K j ≤ i → i < K (j + 1) →
      TupEncl (Icc (a i) (a (i + 1))) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (ct i) ∧
        TupEncl {a (i + 1)} (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (nt i) := by
    intro j hj1 hj
    obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    exacts [s1.1, s2.1, s3.1, s4.1, s5.1]
  have hsegi : ∀ j, 1 ≤ j → j ≤ 5 → ∀ i, K j ≤ i → i < K (j + 1) → Icc (a i) (a (i + 1)) ⊆ seg j := by
    intro j hj1 hj i hi1 hi2
    rw [seg_eq_Icc hj1 hj, ← haK j (by omega), ← haK (j + 1) (by omega)]
    have := hKm (j + 1) 6 (by omega) le_rfl
    exact Icc_subset_Icc (hmo _ _ (Nat.zero_le _) hi1 (by omega)) (hmo _ _ (Nat.zero_le _) hi2 this)
  -- the first segment
  have hK16 := hKm 1 6 (by norm_num) le_rfl
  have hin := inner_sound (L := Ls 0) (hd.mpi) (hL 0 (by norm_num)) (node := node) (ct := ct) (nt := nt)
    (a := a) (i0 := K 0) (N := Ns 0) hinner (fun i _ hi => hmem i (by
      have := hK 0 (by norm_num); simp only [zero_add] at this; omega))
  rw [← hK 0 (by norm_num)] at hin
  have hseg0 : ∀ i, K 0 ≤ i → i < K 1 → Icc (a i) (a (i + 1)) ⊆ seg 0 := by
    intro i hi1 hi2 t ht
    have h1 : a (K 0) ≤ a i := hmo _ _ (Nat.zero_le _) hi1 (by omega)
    have h2 : a (i + 1) ≤ a (K 1) := hmo _ _ (Nat.zero_le _) hi2 hK16
    rw [haK 0 (by norm_num)] at h1
    rw [haK 1 (by norm_num)] at h2
    exact ⟨b_pos.trans_le (h1.trans ht.1), ht.2.trans h2⟩
  refine ⟨fun i hi => hmem i hi, fun i hi => hlt i hi, by rw [← hK0]; exact haK 0 (by norm_num),
    haK 6 le_rfl, fun i hi => ?_⟩
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hKup
  by_cases h0 : i < K 1
  · have hs := hseg0 i (by omega) h0
    have hie := hin i (by omega) h0
    exact ⟨0, by norm_num, hs, TupEncl.model_of_inner hs hie.1,
      TupEncl.model_of_inner (fun t ht => hs ⟨by rw [mem_singleton_iff.mp ht]; exact hmono i hi, by
        rw [mem_singleton_iff.mp ht]⟩) hie.2⟩
  · obtain ⟨j, hj1, hj, hi1, hi2⟩ : ∃ j, 1 ≤ j ∧ j ≤ 5 ∧ K j ≤ i ∧ i < K (j + 1) := by
      by_cases h2 : i < K 2
      · exact ⟨1, le_rfl, by norm_num, by omega, h2⟩
      by_cases h3 : i < K 3
      · exact ⟨2, by norm_num, by norm_num, by omega, h3⟩
      by_cases h4 : i < K 4
      · exact ⟨3, by norm_num, by norm_num, by omega, h4⟩
      by_cases h5 : i < K 5
      · exact ⟨4, by norm_num, by norm_num, by omega, h5⟩
      · exact ⟨5, by norm_num, le_rfl, by omega, hi⟩
    exact ⟨j, by omega, hsegi j hj1 hj i hi1 hi2, hcells j hj1 hj i hi1 hi2⟩

end SandierSerfaty.Certificate.Assemble
