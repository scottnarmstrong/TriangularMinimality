/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Assemble.Defs
public import SandierSerfaty.Certificate.Query.TableBridge
public import SandierSerfaty.Certificate.Table.InnerBridge

/-!
# The whole radial table from its chunk checks

The generated table is given by global accessors `node`, `ct`, `nt`, `ck` and the knot cells `K 0 = 0 < K 1 <
⋯ < K 6 = n`; segment `j` is cut into `N j` chunks of `L j` cells, checked by `innerB` (segment `0`, the exact
inner form) and `chunkB` (segments `1, …, 5`, propagation from literal checkpoints), with the initial checkpoint
checked by `initCheck` and the nodes by `nodesB`. This module proves, for any such data:

* `nodesB_sound`: the real nodes `realNode node K i` (the knot `κ_j` at the node `K j`, the midpoint of the node
  interval elsewhere) lie in the node intervals and increase strictly;
* `seg_sound`: a segment `j ≥ 1` whose chunks pass, started from a checkpoint enclosing the truncated sector
  functions, encloses `Trunc.f₀`, `Trunc.e` and their derivatives on every cell (the model of
  `Table.chunkCheck_sound`) and ends in a checkpoint enclosing them (`Table.chunks_sound_trunc`);
* `inner_sound`, `inner_cell_enclosures`: the same for the first segment, with the derivatives of `Trunc.f₀`,
  `Trunc.e` identified on `seg 0` (the inner closed form and `0`);
* `tableEncl_of_checks`: **the realization `ITable.Encl ⟨K 6, node, ct⟩ (realNode node K)`** of the whole
  table (the hypothesis of `Query.lamEnc_sound` and of the lookups), and the node tuples of the segments `≥ 1`
  enclose `Trunc.f₀`, `Trunc.e` at the right end of their cell.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Assemble

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Calibration SandierSerfaty.Tails

/-! ### Lists of real nodes -/

/-- The reals `a i, …, a (i + k)`. -/
@[expose] def realsFrom (a : ℕ → ℝ) : ℕ → ℕ → List ℝ
  | i, 0 => [a i]
  | i, k + 1 => a i :: realsFrom a (i + 1) k

theorem forall₂_realsFrom {a : ℕ → ℝ} {node : ℕ → IV 128} :
    ∀ (i k : ℕ), (∀ m, i ≤ m → m ≤ i + k → IV.Mem (a m) (node m)) →
      List.Forall₂ IV.Mem (realsFrom a i k) (nodesFrom node i k)
  | i, 0, h => List.Forall₂.cons (h i le_rfl (by omega)) List.Forall₂.nil
  | i, k + 1, h => List.Forall₂.cons (h i le_rfl (by omega))
      (forall₂_realsFrom (i + 1) k fun m h1 h2 => h m (by omega) (by omega))

theorem lastR_realsFrom (a : ℕ → ℝ) : ∀ (x : ℝ) (i k : ℕ), lastR x (realsFrom a i k) = a (i + k)
  | x, i, 0 => by simp [realsFrom, lastR]
  | x, i, k + 1 => by
    rw [realsFrom, lastR, lastR_realsFrom a (a i) (i + 1) k]
    congr 1
    omega

theorem tableEncloses_get {j : ℕ} {S1 S2 : ℝ → ℝ} {H : ℕ → ℝ → ℝ} {a : ℕ → ℝ} {ct nt : ℕ → Tup} :
    ∀ (i k : ℕ), TableEncloses j S1 S2 H (realsFrom a i k) (tupsFrom ct i k) (tupsFrom nt i k) →
      ∀ m, i ≤ m → m < i + k →
        TupEncl (Icc (a m) (a (m + 1))) (F0m j S1 S2 H) (Em j) (ct m) ∧
          TupEncl {a (m + 1)} (F0m j S1 S2 H) (Em j) (nt m)
  | _, 0, _, m, _, h2 => absurd h2 (by omega)
  | i, k + 1, h, m, h1, h2 => by
    have h' : TupEncl (Icc (a i) (a (i + 1))) (F0m j S1 S2 H) (Em j) (ct i) ∧
        TupEncl {a (i + 1)} (F0m j S1 S2 H) (Em j) (nt i) ∧
        TableEncloses j S1 S2 H (realsFrom a (i + 1) k) (tupsFrom ct (i + 1) k) (tupsFrom nt (i + 1) k) := by
      cases k <;> exact h
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · subst e; exact ⟨h'.1, h'.2.1⟩
    · exact tableEncloses_get (i + 1) k h'.2.2 m lt (by omega)

theorem innerEncloses_get {a : ℕ → ℝ} {ct nt : ℕ → Tup} :
    ∀ (i k : ℕ), InnerEncloses (realsFrom a i k) (tupsFrom ct i k) (tupsFrom nt i k) →
      ∀ m, i ≤ m → m < i + k →
        TupEncl (Icc (a m) (a (m + 1))) F0inner (fun _ => 0) (ct m) ∧ TupEncl {a (m + 1)} F0inner (fun _ => 0) (nt m)
  | _, 0, _, m, _, h2 => absurd h2 (by omega)
  | i, k + 1, h, m, h1, h2 => by
    have h' : TupEncl (Icc (a i) (a (i + 1))) F0inner (fun _ => 0) (ct i) ∧
        TupEncl {a (i + 1)} F0inner (fun _ => 0) (nt i) ∧
        InnerEncloses (realsFrom a (i + 1) k) (tupsFrom ct (i + 1) k) (tupsFrom nt (i + 1) k) := by
      cases k <;> exact h
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · subst e; exact ⟨h'.1, h'.2.1⟩
    · exact innerEncloses_get (i + 1) k h'.2.2 m lt (by omega)

theorem mono_of_step {a : ℕ → ℝ} {i0 n : ℕ} (h : ∀ i, i0 ≤ i → i < n → a i ≤ a (i + 1)) :
    ∀ m m', i0 ≤ m → m ≤ m' → m' ≤ n → a m ≤ a m' := by
  intro m m' h1 h2 h3
  induction m', h2 using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih => exact (ih (by omega)).trans (h k (by omega) (by omega))

/-! ### A segment `j ≥ 1` -/

/-- **A segment of the table** (`1 ≤ j ≤ 5`): its chunks of `L` cells starting at the nodes `i₀ + L c`,
`c < N`, pass `chunkB`; the real nodes lie in the node intervals, increase, and span a part of `seg j`; the first
checkpoint encloses the truncated sector functions. Then every cell tuple encloses the model `F0m j`, `Em j` with
its derivatives on its cell, every node tuple at its node, and the last checkpoint encloses the truncated sector
functions at the last node. -/
theorem seg_sound {d : BasisData} (hd : d.Valid) {j : ℕ} (hj : j ≤ 5) {L : ℕ} (hL : 1 ≤ L)
    {node : ℕ → IV 128} {ct nt : ℕ → Tup} {ck : ℕ → SState} {a : ℕ → ℝ} {i0 N : ℕ}
    (hc : ∀ c < N, chunkB L d node ct nt ck j (i0 + L * c) = true)
    (ha : ∀ i, i0 ≤ i → i ≤ i0 + L * N → IV.Mem (a i) (node i))
    (hmono : ∀ i, i0 ≤ i → i < i0 + L * N → a i ≤ a (i + 1))
    (hseg : Icc (a i0) (a (i0 + L * N)) ⊆ seg j)
    (h0 : StateOn {a i0} Trunc.S₁ Trunc.S₂ TH (ck i0)) :
    (∀ i, i0 ≤ i → i < i0 + L * N →
      TupEncl (Icc (a i) (a (i + 1))) (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (ct i) ∧
        TupEncl {a (i + 1)} (F0m j Trunc.S₁ Trunc.S₂ TH) (Em j) (nt i)) ∧
      StateOn {a (i0 + L * N)} Trunc.S₁ Trunc.S₂ TH (ck (i0 + L * N)) := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hmo := mono_of_step hmono
  have hc' : ∀ c < N, chunkCheck d j (ck (i0 + (L' + 1) * c))
      (node (i0 + (L' + 1) * c) :: nodesFrom node (i0 + (L' + 1) * c + 1) L')
      (tupsFrom ct (i0 + (L' + 1) * c) (L' + 1)) (tupsFrom nt (i0 + (L' + 1) * c) (L' + 1))
      (ck (i0 + (L' + 1) * (c + 1))) = true := by
    intro c hcN
    have h := hc c hcN
    rw [show i0 + (L' + 1) * (c + 1) = Nat.add (i0 + (L' + 1) * c) (L' + 1) by rw [Nat.add_eq]; ring]
    exact h
  have ha' : ∀ c < N, IV.Mem (a (i0 + (L' + 1) * c)) (node (i0 + (L' + 1) * c)) := fun c hcN =>
    ha _ (by omega) (by nlinarith)
  have hτ : ∀ c < N, List.Forall₂ IV.Mem (realsFrom a (i0 + (L' + 1) * c + 1) L')
      (nodesFrom node (i0 + (L' + 1) * c + 1) L') := fun c hcN =>
    forall₂_realsFrom _ _ fun m h1 h2 => ha m (by omega) (by nlinarith)
  have hlink : ∀ c < N, lastR (a (i0 + (L' + 1) * c)) (realsFrom a (i0 + (L' + 1) * c + 1) L') =
      a (i0 + (L' + 1) * (c + 1)) := fun c _ => by
    rw [lastR_realsFrom]; congr 1; ring
  have hseg' : ∀ c < N, Icc (a (i0 + (L' + 1) * c)) (lastR (a (i0 + (L' + 1) * c))
      (realsFrom a (i0 + (L' + 1) * c + 1) L')) ⊆ seg j := fun c hcN => by
    rw [hlink c hcN]
    refine fun t ht => hseg ⟨(hmo i0 _ le_rfl (by omega) (by nlinarith)).trans ht.1,
      ht.2.trans (hmo _ _ (by omega) (by nlinarith) le_rfl)⟩
  refine ⟨fun i hi1 hi2 => ?_, ?_⟩
  · obtain ⟨c, r, hr, rfl⟩ : ∃ c r, r < L' + 1 ∧ i = i0 + (L' + 1) * c + r :=
      ⟨(i - i0) / (L' + 1), (i - i0) % (L' + 1), Nat.mod_lt _ (by omega), by
        have := Nat.div_add_mod (i - i0) (L' + 1); omega⟩
    have hcN : c < N := by
      by_contra hcon
      push Not at hcon
      have : (L' + 1) * N ≤ (L' + 1) * c := Nat.mul_le_mul_left _ hcon
      omega
    have hT := (chunks_sound_trunc hd (by omega) (ckpt := fun c => ck (i0 + (L' + 1) * c))
      (v := fun c => node (i0 + (L' + 1) * c)) (vs := fun c => nodesFrom node (i0 + (L' + 1) * c + 1) L')
      (cts := fun c => tupsFrom ct (i0 + (L' + 1) * c) (L' + 1))
      (nts := fun c => tupsFrom nt (i0 + (L' + 1) * c) (L' + 1)) (a := fun c => a (i0 + (L' + 1) * c))
      (τs := fun c => realsFrom a (i0 + (L' + 1) * c + 1) L') hc' ha' hτ hlink hseg' h0 c hcN).1
    exact tableEncloses_get (i0 + (L' + 1) * c) (L' + 1) hT _ (by omega) (by omega)
  · have := chunks_stateOn_trunc hd (by omega) (ckpt := fun c => ck (i0 + (L' + 1) * c))
      (v := fun c => node (i0 + (L' + 1) * c)) (vs := fun c => nodesFrom node (i0 + (L' + 1) * c + 1) L')
      (cts := fun c => tupsFrom ct (i0 + (L' + 1) * c) (L' + 1))
      (nts := fun c => tupsFrom nt (i0 + (L' + 1) * c) (L' + 1)) (a := fun c => a (i0 + (L' + 1) * c))
      (τs := fun c => realsFrom a (i0 + (L' + 1) * c + 1) L') hc' ha' hτ hlink hseg' h0 N le_rfl
    exact this

/-! ### The first segment -/

/-- **The first segment of the table**: its chunks pass `innerB`; then every cell tuple encloses the inner
closed form `F0inner` and `0` (for `ẽ`) with their derivatives on its cell, and every node tuple at its node. -/
theorem inner_sound {pi : IV 128} (hpi : IV.Mem Real.pi pi) {L : ℕ} (hL : 1 ≤ L) {node : ℕ → IV 128}
    {ct nt : ℕ → Tup} {a : ℕ → ℝ} {i0 N : ℕ} (hc : ∀ c < N, innerB L pi node ct nt (i0 + L * c) = true)
    (ha : ∀ i, i0 ≤ i → i ≤ i0 + L * N → IV.Mem (a i) (node i)) :
    ∀ i, i0 ≤ i → i < i0 + L * N →
      TupEncl (Icc (a i) (a (i + 1))) F0inner (fun _ => 0) (ct i) ∧ TupEncl {a (i + 1)} F0inner (fun _ => 0) (nt i) := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  intro i hi1 hi2
  obtain ⟨c, r, hr, rfl⟩ : ∃ c r, r < L' + 1 ∧ i = i0 + (L' + 1) * c + r :=
    ⟨(i - i0) / (L' + 1), (i - i0) % (L' + 1), Nat.mod_lt _ (by omega), by
      have := Nat.div_add_mod (i - i0) (L' + 1); omega⟩
  have hcN : c < N := by
    by_contra hcon
    push Not at hcon
    have : (L' + 1) * N ≤ (L' + 1) * c := Nat.mul_le_mul_left _ hcon
    omega
  have hI := innerCheck_sound hpi (node (i0 + (L' + 1) * c)) (nodesFrom node (i0 + (L' + 1) * c + 1) L')
    (tupsFrom ct (i0 + (L' + 1) * c) (L' + 1)) (tupsFrom nt (i0 + (L' + 1) * c) (L' + 1))
    (a (i0 + (L' + 1) * c)) (realsFrom a (i0 + (L' + 1) * c + 1) L') (hc c hcN)
    (ha _ (by omega) (by linarith))
    (forall₂_realsFrom _ _ fun m h1 h2 => ha m (by omega) (by nlinarith))
  exact innerEncloses_get (i0 + (L' + 1) * c) (L' + 1) hI _ (by omega) (by omega)

/-- **The cell enclosures on the first segment**: on a cell `[a, b] ⊆ seg 0` the values and first
derivatives of `Trunc.f₀`, `Trunc.e` are those of the closed form `F0inner` and of `0`. -/
theorem inner_cell_enclosures (hc : FiniteCore) {a b : ℝ} (hseg : Icc a b ⊆ seg 0) {ct : Tup}
    (h : TupEncl (Icc a b) F0inner (fun _ => 0) ct) :
    ∀ t ∈ Icc a b, IV.Mem (Trunc.f₀ t) ct.f0 ∧ IV.Mem (deriv Trunc.f₀ t) ct.f1 ∧
      IV.Mem (Trunc.e t) ct.e0 ∧ IV.Mem (deriv Trunc.e t) ct.e1 := by
  obtain ⟨F₁, F₂, E₁, E₂, hd, hm⟩ := h
  intro t ht
  obtain ⟨m0, m1, -, n0, n1, -⟩ := hm t ht
  obtain ⟨d0, -, d2, -⟩ := hd t ht
  have hts := hseg ht
  obtain ⟨G₁, G₂, jt⟩ := exists_jet_Trunc_f₀ hc
  have hf1 : HasDerivAt Trunc.f₀ (G₁ t) t := jt.d0 t (seg_subset_Ioi hts)
  have hf2 : HasDerivWithinAt Trunc.f₀ (F₁ t) (seg 0) t :=
    d0.hasDerivWithinAt.congr (fun y hy => trunc_f₀_inner hy) (trunc_f₀_inner hts)
  have ef : deriv Trunc.f₀ t = F₁ t := by
    rw [hf1.deriv]; exact (uniqueDiffOn_seg (j := 0) (by norm_num) t hts).eq_deriv (seg 0) hf1.hasDerivWithinAt hf2
  have he1 : HasDerivAt Trunc.e (sTe1 t) t := hasDerivAt_Trunc_e (seg_subset_Ioi hts)
  have he2 : HasDerivWithinAt Trunc.e (E₁ t) (seg 0) t :=
    d2.hasDerivWithinAt.congr (fun y hy => trunc_e_inner hy) (trunc_e_inner hts)
  have ee : deriv Trunc.e t = E₁ t := by
    rw [he1.deriv]; exact (uniqueDiffOn_seg (j := 0) (by norm_num) t hts).eq_deriv (seg 0) he1.hasDerivWithinAt he2
  rw [trunc_f₀_inner hts, trunc_e_inner hts, ef, ee]
  exact ⟨m0, m1, n0, n1⟩

/-! ### The real nodes -/

/-- The midpoint of an interval (as a real number). -/
@[expose] noncomputable def midR (v : IV 128) : ℝ := (((v.lo.toInt : ℤ) : ℝ) + ((v.hi.toInt : ℤ) : ℝ)) / 2 / 2 ^ 128

theorem mem_midR {v : IV 128} (h : SInt.blt v.lo v.hi = true) : IV.Mem (midR v) v := by
  have h' : ((v.lo.toInt : ℤ) : ℝ) < ((v.hi.toInt : ℤ) : ℝ) := by exact_mod_cast (SInt.blt_iff _ _).mp h
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have e : midR v * 2 ^ 128 = (((v.lo.toInt : ℤ) : ℝ) + ((v.hi.toInt : ℤ) : ℝ)) / 2 := by
    unfold midR; field_simp
  refine ⟨?_, ?_⟩ <;> rw [e] <;> linarith

/-- The real node `i`: the knot `κ_j` at the node `K j` (`j ≤ 6`), the midpoint of the node interval elsewhere. -/
@[expose] noncomputable def realNode (node : ℕ → IV 128) (K : ℕ → ℕ) (i : ℕ) : ℝ :=
  if i = K 0 then knot 0 else if i = K 1 then knot 1 else if i = K 2 then knot 2 else if i = K 3 then knot 3
  else if i = K 4 then knot 4 else if i = K 5 then knot 5 else if i = K 6 then knot 6 else midR (node i)

/-- The knot cells increase strictly. -/
@[expose] def KnotsUp (K : ℕ → ℕ) : Prop :=
  K 0 < K 1 ∧ K 1 < K 2 ∧ K 2 < K 3 ∧ K 3 < K 4 ∧ K 4 < K 5 ∧ K 5 < K 6

theorem realNode_K {node : ℕ → IV 128} {K : ℕ → ℕ} (hK : KnotsUp K) {j : ℕ} (hj : j ≤ 6) :
    realNode node K (K j) = knot j := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hK
  interval_cases j <;> simp only [realNode] <;> split_ifs <;> first | rfl | omega

theorem realNode_of_ne {node : ℕ → IV 128} {K : ℕ → ℕ} {i : ℕ} (h : ∀ j ≤ 6, i ≠ K j) :
    realNode node K i = midR (node i) := by
  simp [realNode, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 4 (by norm_num),
    h 5 (by norm_num), h 6 le_rfl]

theorem sepFrom_sound {node : ℕ → IV 128} :
    ∀ (i m : ℕ), sepFrom node i m = true → ∀ k, i ≤ k → k < i + m →
      SInt.blt (node k).lo (node k).hi = true ∧ SInt.blt (node k).hi (node (k + 1)).lo = true
  | _, 0, _, k, _, h2 => absurd h2 (by omega)
  | i, m + 1, h, k, h1, h2 => by
    simp only [sepFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · subst e; exact h.1
    · exact sepFrom_sound (i + 1) m h.2 k lt (by omega)

theorem knotsFrom_sound {d : BasisData} {node : ℕ → IV 128} {K : ℕ → ℕ} :
    ∀ (j cnt : ℕ), knotsFrom d node K j cnt = true → ∀ k, j ≤ k → k < j + cnt →
      IV.subsetB (knotIV d k) (node (K k)) = true
  | _, 0, _, k, _, h2 => absurd h2 (by omega)
  | j, cnt + 1, h, k, h1, h2 => by
    simp only [knotsFrom, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with e | lt
    · subst e; exact h.1
    · exact knotsFrom_sound (j + 1) cnt h.2 k lt (by omega)

/-- **The nodes**: the real nodes lie in the node intervals and increase strictly. -/
theorem nodesB_sound {d : BasisData} (hd : d.Valid) {node : ℕ → IV 128} {K : ℕ → ℕ} (hK : KnotsUp K) {n : ℕ}
    (h : nodesB d node K n = true) :
    (∀ i, i ≤ n → IV.Mem (realNode node K i) (node i)) ∧
      (∀ i, i < n → realNode node K i < realNode node K (i + 1)) := by
  simp only [nodesB, Bool.and_eq_true] at h
  obtain ⟨⟨hs, hn⟩, hk⟩ := h
  have hmem : ∀ i, i ≤ n → IV.Mem (realNode node K i) (node i) := by
    intro i hi
    by_cases hex : ∃ j ≤ 6, i = K j
    · obtain ⟨j, hj, rfl⟩ := hex
      rw [realNode_K hK hj]
      exact IV.mem_of_subsetB (knotsFrom_sound 0 7 hk j (by omega) (by omega)) (mem_knotIV hd hj)
    · push Not at hex
      rw [realNode_of_ne hex]
      rcases Nat.lt_or_eq_of_le hi with hlt | e
      · exact mem_midR (sepFrom_sound 0 n hs i (by omega) (by omega)).1
      · subst e; exact mem_midR hn
  refine ⟨hmem, fun i hi => ?_⟩
  have hsep := (SInt.blt_iff _ _).mp (sepFrom_sound 0 n hs i (by omega) (by omega)).2
  have hsep' : ((node i).hi.toInt : ℝ) < ((node (i + 1)).lo.toInt : ℝ) := by exact_mod_cast hsep
  have hp : (0 : ℝ) < 2 ^ 128 := by positivity
  have h1 := (hmem i hi.le).2
  have h2 := (hmem (i + 1) hi).1
  linarith

/-! ### The whole table -/

theorem seg_eq_Icc {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ 5) : seg j = Icc (knot j) (knot (j + 1)) := by
  interval_cases j <;> rfl

/-- **The whole table from its checks.** `K` are the knot cells (`K 0 = 0`), segment `j ≤ 5` consists of
`N j` chunks of `L j` cells starting at `K j`, so `K (j + 1) = K j + L j N j`. If the nodes, the chunks of the
first segment, the initial checkpoint at `K 1` and the chunks of the segments `1, …, 5` pass their checks, then
the real nodes realize the table (`ITable.Encl`), and every node tuple of a segment `≥ 1` encloses `Trunc.f₀`,
`Trunc.e` at the right end of its cell. -/
theorem tableEncl_of_checks (hc : FiniteCore) {d : BasisData} (hd : d.Valid) {node : ℕ → IV 128}
    {ct nt : ℕ → Tup} {ck : ℕ → SState} {K Ls Ns : ℕ → ℕ} (hK0 : K 0 = 0)
    (hK : ∀ j, j ≤ 5 → K (j + 1) = K j + Ls j * Ns j) (hL : ∀ j, j ≤ 5 → 1 ≤ Ls j)
    (hN : ∀ j, j ≤ 5 → 1 ≤ Ns j) (hnodes : nodesB d node K (K 6) = true)
    (hinner : ∀ c < Ns 0, innerB (Ls 0) d.pi node ct nt (K 0 + Ls 0 * c) = true)
    (hinit : initCheck d (node (K 1)) (ck (K 1)) = true)
    (hchunks : ∀ j, 1 ≤ j → j ≤ 5 → ∀ c < Ns j, chunkB (Ls j) d node ct nt ck j (K j + Ls j * c) = true) :
    ITable.Encl ⟨K 6, node, ct⟩ (realNode node K) ∧
      ∀ j, 1 ≤ j → j ≤ 5 → ∀ i, K j ≤ i → i < K (j + 1) →
        IV.Mem (Trunc.f₀ (realNode node K (i + 1))) (nt i).f0 ∧ IV.Mem (Trunc.e (realNode node K (i + 1))) (nt i).e0 := by
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
    have hKj6 := hKm (j + 1) 6 (by omega) le_rfl
    have := seg_sound hd hj (hL j hj) (node := node) (ct := ct) (nt := nt) (ck := ck) (a := a) (i0 := K j)
      (N := Ns j) (hchunks j hj1 hj) (fun i _ hi => hmem i (by omega)) (fun i _ hi => hmono i (by omega))
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
  have hK01 : K 1 = K 0 + Ls 0 * Ns 0 := hK 0 (by norm_num)
  have hin := inner_sound (L := Ls 0) (hd.mpi) (hL 0 (by norm_num)) (node := node) (ct := ct) (nt := nt)
    (a := a) (i0 := K 0) (N := Ns 0) hinner (fun i _ hi => hmem i (by omega))
  rw [← hK 0 (by norm_num)] at hin
  have hseg0 : ∀ i, K 0 ≤ i → i < K 1 → Icc (a i) (a (i + 1)) ⊆ seg 0 := by
    intro i hi1 hi2 t ht
    have h1 : a (K 0) ≤ a i := hmo _ _ (Nat.zero_le _) hi1 (by have := hKm 1 6 (by norm_num) le_rfl; omega)
    have h2 : a (i + 1) ≤ a (K 1) := hmo _ _ (Nat.zero_le _) hi2 (hKm 1 6 (by norm_num) le_rfl)
    rw [haK 0 (by norm_num)] at h1
    rw [haK 1 (by norm_num)] at h2
    exact ⟨b_pos.trans_le (h1.trans ht.1), ht.2.trans h2⟩
  -- every cell
  have hall : ∀ i, i < K 6 → ∀ t ∈ Icc (a i) (a (i + 1)),
      IV.Mem (Trunc.f₀ t) (ct i).f0 ∧ IV.Mem (deriv Trunc.f₀ t) (ct i).f1 ∧
        IV.Mem (Trunc.e t) (ct i).e0 ∧ IV.Mem (deriv Trunc.e t) (ct i).e1 := by
    intro i hi
    have hKs := hKup
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hKs
    by_cases h0 : i < K 1
    · exact inner_cell_enclosures hc (hseg0 i (by omega) h0) (hin i (by omega) h0).1
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
      exact cell_enclosures hc (by omega) (hsegi j hj1 hj i hi1 hi2) (hcells j hj1 hj i hi1 hi2).1
  refine ⟨⟨fun i hi => hmem i hi, fun i hi => hmono i hi, by rw [← hK0]; exact haK 0 (by norm_num),
    haK 6 le_rfl, fun i hi t ht => (hall i hi t ht).1, fun i hi t ht => (hall i hi t ht).2.1,
    fun i hi t ht => (hall i hi t ht).2.2.1, fun i hi t ht => (hall i hi t ht).2.2.2⟩, ?_⟩
  intro j hj1 hj i hi1 hi2
  exact (hcells j hj1 hj i hi1 hi2).2.mem_trunc (by omega)
    (fun t ht => by rw [mem_singleton_iff.mp ht]; exact hsegi j hj1 hj i hi1 hi2 ⟨(hmono i (by
      have := hKm (j + 1) 6 (by omega) le_rfl; omega)), le_rfl⟩) rfl

end SandierSerfaty.Certificate.Assemble
