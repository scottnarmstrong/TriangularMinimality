/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Geometry.VoronoiVertex
public import SandierSerfaty.Geometry.VoronoiPeriodic

/-!
# The incidence bound `M₀ ≤ 6n`

For a lattice `Γ ⊆ ℂ` and `n` points `a : Fin n → ℂ` distinct modulo `Γ`, the face–edge incidences
of the periodic Voronoi diagram modulo `Γ` are the pairs `(i, q)` with `q` a Voronoi neighbour of
`a i` among the periodic sites (`voronoiIncidences Γ a`; `M₀` is the side
count). An incidence is a site of the fundamental configuration together with an actual neighbour
in `ℂ`, so loops and self-adjacency modulo `Γ` (for instance `(i, a i + γ)` and `(i, a i - γ)`) are
counted separately, as in the paper.

* `finite_voronoiIncidences`: there are finitely many incidences;
* `card_le_six_mul`: the abstract count. If each incidence is a triangle with apex angle `θ` and
  base angles `A₊, A₋` (`θ + A₊ + A₋ = π`), the apex angles total at most `2πn`, and the ends,
  grouped by the vertex they sit at, form groups of at least six with base angles totalling at most
  `2π`, then there are at most `6n` incidences;
* `card_voronoiIncidences_le`: **`M₀ ≤ 6n`**, for every lattice, every `n` and every configuration
  distinct modulo `Γ`.

The proof uses a sector fan and packing argument: no Euler characteristic, no cyclic
order of polygon vertices, no polygon angle sums. Deviation from the paper (stronger, harmless): no
separation hypothesis and no restriction to the square torus `L ℤ²`; the paper states the bound for
separated square-torus configurations.

Source: paper §4, Lemma `geo:voronoi`.
-/

open Metric Set Real

public section

namespace SandierSerfaty

/-- **The abstract angle count.** Each incidence `i ∈ I` is a triangle with apex angle `θ i` and
two base angles `A i b` (`b : Bool` labels the end) summing to `π`. If the apex angles total at most
`2πn`, and the ends, grouped by the vertex `v i b` they sit at, have at least six members and base
angles totalling at most `2π` at each vertex, then `#I ≤ 6n`. -/
theorem card_le_six_mul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (I : Finset ι) (θ : ι → ℝ)
    (A : ι → Bool → ℝ) (v : ι → Bool → κ) (n : ℕ)
    (htri : ∀ i ∈ I, θ i + A i true + A i false = π)
    (hθ : ∑ i ∈ I, θ i ≤ 2 * π * n)
    (hcard : ∀ w, ∀ e ∈ I ×ˢ (Finset.univ : Finset Bool), v e.1 e.2 = w →
      6 ≤ ((I ×ˢ (Finset.univ : Finset Bool)).filter (fun e => v e.1 e.2 = w)).card)
    (hang : ∀ w, ∑ e ∈ (I ×ˢ (Finset.univ : Finset Bool)).filter (fun e => v e.1 e.2 = w),
      A e.1 e.2 ≤ 2 * π) :
    I.card ≤ 6 * n := by
  set E := I ×ˢ (Finset.univ : Finset Bool) with hE
  set W := E.image (fun e => v e.1 e.2) with hW
  have hEA : ∑ e ∈ E, A e.1 e.2 = ∑ i ∈ I, (A i true + A i false) := by
    rw [hE, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
  have hfib : ∑ e ∈ E, A e.1 e.2 =
      ∑ w ∈ W, ∑ e ∈ E.filter (fun e => v e.1 e.2 = w), A e.1 e.2 :=
    (Finset.sum_fiberwise_of_maps_to (fun e he => Finset.mem_image_of_mem _ he) _).symm
  have hcardfib : (E.card : ℝ) = ∑ w ∈ W, ((E.filter (fun e => v e.1 e.2 = w)).card : ℝ) := by
    rw [← Nat.cast_sum, Finset.card_eq_sum_card_fiberwise (f := fun e : ι × Bool => v e.1 e.2)
      (fun e he => Finset.mem_image_of_mem _ he)]
  have hW6 : ∀ w ∈ W, (6 : ℝ) ≤ ((E.filter (fun e => v e.1 e.2 = w)).card : ℝ) := by
    intro w hw
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hw
    exact_mod_cast hcard _ e he rfl
  have hA : ∑ e ∈ E, A e.1 e.2 ≤ π / 3 * E.card := by
    rw [hfib, hcardfib, Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    have h6 := hW6 w hw
    have h2 := hang w
    have : π / 3 * 6 ≤ π / 3 * ((E.filter (fun e => v e.1 e.2 = w)).card : ℝ) :=
      mul_le_mul_of_nonneg_left h6 (by positivity)
    linarith
  have hEcard : (E.card : ℝ) = 2 * I.card := by
    rw [hE, Finset.card_product, Finset.card_univ, Fintype.card_bool]; push_cast; ring
  have hsum : π * I.card = ∑ i ∈ I, θ i + ∑ e ∈ E, A e.1 e.2 := by
    rw [hEA, ← Finset.sum_add_distrib]
    calc π * I.card = ∑ _i ∈ I, π := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = _ := Finset.sum_congr rfl fun i hi => by rw [← add_assoc]; exact (htri i hi).symm
  have h1 : π * I.card ≤ 2 * π * n + π / 3 * (2 * I.card) := by
    rw [hsum, ← hEcard]; linarith
  have h2 : π * (I.card : ℝ) ≤ π * (6 * n) := by linarith
  have h' : (I.card : ℝ) ≤ 6 * n := le_of_mul_le_mul_left h2 Real.pi_pos
  exact_mod_cast h'

section Periodic

variable (Γ : Submodule ℤ ℂ) [DiscreteTopology Γ] [IsZLattice ℝ Γ] {n : ℕ} (a : Fin n → ℂ)

/-- Periodic sites satisfy the standing hypotheses. -/
theorem isVoronoiSiteSet_periodicSites : IsVoronoiSiteSet (periodicSites Γ a) :=
  ⟨locallyFiniteSites_periodicSites Γ a, fun _ hp =>
    isBounded_ball.subset (voronoiCell_subset_ball Γ a hp)⟩

/-- Neighbours are within twice the lattice radius. -/
theorem norm_sub_lt_of_isVoronoiNeighbor {p q : ℂ}
    (h : IsVoronoiNeighbor (periodicSites Γ a) p q) : ‖q - p‖ < 2 * latticeRadius Γ := by
  obtain ⟨s, hs, -⟩ := h.2.2.2
  have hy := voronoiCell_subset_ball Γ a h.1 hs
  rw [mem_ball, dist_eq_norm] at hy
  have heq := norm_bisectorPoint_sub_eq h.ne s
  have := norm_sub_le_norm_sub_add_norm_sub q (bisectorPoint p q s) p
  rw [norm_sub_rev q (bisectorPoint p q s)] at this
  linarith

theorem finite_voronoiIncidences :
    {e : Fin n × ℂ | IsVoronoiNeighbor (periodicSites Γ a) (a e.1) e.2}.Finite := by
  refine (Set.finite_univ.prod (Set.finite_iUnion fun i : Fin n =>
    locallyFiniteSites_periodicSites Γ a (a i) (2 * latticeRadius Γ))).subset ?_
  rintro ⟨i, q⟩ h
  refine ⟨Set.mem_univ _, mem_iUnion.2 ⟨i, h.2.1, ?_⟩⟩
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_lt_of_isVoronoiNeighbor Γ a h).le

/-- Face–edge incidences modulo `Γ` (`M₀` is the side count): pairs `(i, q)` with `q` a
Voronoi neighbour of `a i` among the periodic sites. -/
@[expose] noncomputable def voronoiIncidences : Finset (Fin n × ℂ) :=
  (finite_voronoiIncidences Γ a).toFinset

theorem mem_voronoiIncidences {e : Fin n × ℂ} :
    e ∈ voronoiIncidences Γ a ↔ IsVoronoiNeighbor (periodicSites Γ a) (a e.1) e.2 :=
  Set.Finite.mem_toFinset _

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
/-- Translating an incidence by a lattice vector. -/
theorem isVoronoiNeighbor_periodicSites_add {γ : ℂ} (hγ : γ ∈ Γ) {p q : ℂ} :
    IsVoronoiNeighbor (periodicSites Γ a) (p + γ) (q + γ) ↔
      IsVoronoiNeighbor (periodicSites Γ a) p q :=
  isVoronoiNeighbor_add_add_iff (fun _ => add_mem_periodicSites_iff Γ a hγ) p q

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem facetEnd_periodicSites_add {γ : ℂ} (hγ : γ ∈ Γ) (p q : ℂ) (b : Bool) :
    facetEnd (periodicSites Γ a) (p + γ) (q + γ) b = facetEnd (periodicSites Γ a) p q b + γ :=
  facetEnd_add_add (fun _ => add_mem_periodicSites_iff Γ a hγ) p q b

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem sectorBaseAngle_periodicSites_add {γ : ℂ} (hγ : γ ∈ Γ) (p q : ℂ) (b : Bool) :
    sectorBaseAngle (periodicSites Γ a) (p + γ) (q + γ) b =
      sectorBaseAngle (periodicSites Γ a) p q b :=
  sectorBaseAngle_add_add (fun _ => add_mem_periodicSites_iff Γ a hγ) p q b

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
/-- Moving an incidence `(r, q)` to the lift `b` of the site `r`. -/
theorem isVoronoiNeighbor_periodicSites_sub {r b q : ℂ} (h : r - b ∈ Γ) :
    IsVoronoiNeighbor (periodicSites Γ a) b (q - (r - b)) ↔
      IsVoronoiNeighbor (periodicSites Γ a) r q := by
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ Γ, b = r - γ := ⟨r - b, h, by ring⟩
  rw [show r - (r - γ) = γ by ring, sub_eq_add_neg r γ, sub_eq_add_neg q γ]
  exact isVoronoiNeighbor_periodicSites_add Γ a (Γ.neg_mem hγ)

omit [DiscreteTopology Γ] [IsZLattice ℝ Γ] in
theorem facetEnd_periodicSites_sub {r b q : ℂ} (h : r - b ∈ Γ) (c : Bool) :
    facetEnd (periodicSites Γ a) b (q - (r - b)) c =
      facetEnd (periodicSites Γ a) r q c - (r - b) := by
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ ∈ Γ, b = r - γ := ⟨r - b, h, by ring⟩
  rw [show r - (r - γ) = γ by ring, sub_eq_add_neg r γ, sub_eq_add_neg q γ,
    facetEnd_periodicSites_add Γ a (Γ.neg_mem hγ), sub_eq_add_neg]

/-- **Site sum.** The apex angles of all incidences total at most `2πn`. -/
theorem sum_sectorAngle_voronoiIncidences_le :
    ∑ e ∈ voronoiIncidences Γ a, (sectorAlpha (periodicSites Γ a) (a e.1) e.2 +
      sectorBeta (periodicSites Γ a) (a e.1) e.2) ≤ 2 * π * n := by
  classical
  set P := periodicSites Γ a
  set I := voronoiIncidences Γ a
  have hP := isVoronoiSiteSet_periodicSites Γ a
  rw [← Finset.sum_fiberwise_of_maps_to (g := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  calc _ ≤ ∑ _i : Fin n, 2 * π := Finset.sum_le_sum fun i _ => ?_
    _ = 2 * π * n := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hinj : Set.InjOn Prod.snd (I.filter fun e => e.1 = i : Set (Fin n × ℂ)) := by
    rintro ⟨i₁, q₁⟩ h₁ ⟨i₂, q₂⟩ h₂ hq
    simp only [Finset.coe_filter, mem_ofPred_eq] at h₁ h₂
    simp only at hq
    rw [h₁.2, h₂.2, hq]
  calc ∑ e ∈ I.filter (fun e => e.1 = i), (sectorAlpha P (a e.1) e.2 + sectorBeta P (a e.1) e.2)
      = ∑ e ∈ I.filter (fun e => e.1 = i), (sectorAlpha P (a i) e.2 + sectorBeta P (a i) e.2) :=
        Finset.sum_congr rfl fun e he => by rw [(Finset.mem_filter.1 he).2]
    _ = ∑ q ∈ (I.filter (fun e => e.1 = i)).image Prod.snd,
          (sectorAlpha P (a i) q + sectorBeta P (a i) q) :=
        (Finset.sum_image (f := fun q => sectorAlpha P (a i) q + sectorBeta P (a i) q) hinj).symm
    _ ≤ 2 * π := sum_sectorAngle_le hP (a i) _ fun q hq => by
        obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hq
        have he' := Finset.mem_filter.1 he
        have := (mem_voronoiIncidences Γ a).1 he'.1
        rwa [he'.2] at this

/-- **M₀ ≤ 6n.** For every lattice `Γ ⊆ ℂ` and every configuration `a : Fin n → ℂ` of points
distinct modulo `Γ`, the periodic Voronoi diagram has at most `6n` face–edge incidences modulo
`Γ`. -/
theorem card_voronoiIncidences_le (ha : ∀ i j, a i - a j ∈ Γ → i = j) :
    (voronoiIncidences Γ a).card ≤ 6 * n := by
  classical
  set P := periodicSites Γ a with hPdef
  set I := voronoiIncidences Γ a with hI
  have hP := isVoronoiSiteSet_periodicSites Γ a
  set v : Fin n × ℂ → Bool → ℂ ⧸ Γ.toAddSubgroup :=
    fun e b => (QuotientAddGroup.mk (facetEnd P (a e.1) e.2 b) : ℂ ⧸ Γ.toAddSubgroup) with hv
  have hmk : ∀ z z' : ℂ, (QuotientAddGroup.mk z : ℂ ⧸ Γ.toAddSubgroup) = QuotientAddGroup.mk z' ↔
      z' - z ∈ Γ := fun z z' => by
    rw [QuotientAddGroup.eq, Submodule.mem_toAddSubgroup, neg_add_eq_sub]
  refine card_le_six_mul I (fun e => sectorAlpha P (a e.1) e.2 + sectorBeta P (a e.1) e.2)
    (fun e b => sectorBaseAngle P (a e.1) e.2 b) v n
    (fun e _ => sectorAngle_add_sectorBaseAngle P (a e.1) e.2)
    (sum_sectorAngle_voronoiIncidences_le Γ a) ?_ ?_
  · -- at least six ends in every nonempty fibre
    rintro w ⟨⟨i, q⟩, b⟩ he hw
    have hiq := (mem_voronoiIncidences Γ a).1 (Finset.mem_product.1 he).1
    have : Nonempty (Fin n) := ⟨i⟩
    obtain ⟨S, hS6, hS⟩ := exists_six_endpoints hP hiq b
    set x := facetEnd P (a i) q b with hx
    have hsite : ∀ e ∈ S, ∃ j : Fin n, e.1 - a j ∈ Γ := fun e he' =>
      (mem_periodicSites_iff Γ a).1 (hS e he').1.1
    choose! j hj using hsite
    set φ : ℂ × ℂ × Bool → (Fin n × ℂ) × Bool :=
      fun e => ((j e, e.2.1 - (e.1 - a (j e))), e.2.2) with hφ
    have hφmem : ∀ e ∈ S, φ e ∈ (I ×ˢ Finset.univ).filter (fun e => v e.1 e.2 = w) := by
      rintro ⟨r, q', c⟩ he'
      obtain ⟨hn, hend⟩ := hS _ he'
      simp only at hn hend
      have hjr := hj _ he'
      simp only at hjr
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨(mem_voronoiIncidences Γ a).2 ?_,
        Finset.mem_univ _⟩, ?_⟩
      · simp only [φ]
        rw [isVoronoiNeighbor_periodicSites_sub Γ a hjr]
        exact hn
      · rw [← hw]
        simp only [φ, hv]
        rw [facetEnd_periodicSites_sub Γ a hjr, hend, hmk, ← hx, sub_sub_cancel]
        exact hjr
    have hφinj : Set.InjOn φ S := by
      rintro ⟨r₁, q₁, c₁⟩ h₁ ⟨r₂, q₂, c₂⟩ h₂ heq
      simp only [φ, Prod.mk.injEq] at heq
      obtain ⟨⟨hj', hq'⟩, hc⟩ := heq
      subst hc
      obtain ⟨-, hend₁⟩ := hS _ h₁
      obtain ⟨-, hend₂⟩ := hS _ h₂
      simp only at hend₁ hend₂
      have hj₁ := hj _ h₁
      have hj₂ := hj _ h₂
      simp only at hj₁ hj₂
      have e₁ := facetEnd_periodicSites_sub Γ a (q := q₁) hj₁ c₁
      have e₂ := facetEnd_periodicSites_sub Γ a (q := q₂) hj₂ c₁
      rw [hend₁] at e₁
      rw [hend₂] at e₂
      rw [hq', hj'] at e₁
      have hr : r₁ = r₂ := by
        have := e₁.symm.trans e₂
        linear_combination -this
      rw [hj', hr] at hq'
      have hq : q₁ = q₂ := by linear_combination hq'
      rw [hr, hq]
    calc 6 ≤ S.card := hS6
      _ ≤ _ := Finset.card_le_card_of_injOn φ hφmem hφinj
  · -- the base angles in every fibre total at most `2π`
    intro w
    set F := (I ×ˢ (Finset.univ : Finset Bool)).filter (fun e => v e.1 e.2 = w) with hF
    set x : ℂ := Quotient.out w with hx
    have hxw : (QuotientAddGroup.mk x : ℂ ⧸ Γ.toAddSubgroup) = w := QuotientAddGroup.out_eq' w
    have hmemF : ∀ e ∈ F, IsVoronoiNeighbor P (a e.1.1) e.1.2 ∧
        facetEnd P (a e.1.1) e.1.2 e.2 - x ∈ Γ := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.1 he
      refine ⟨(mem_voronoiIncidences Γ a).1 (Finset.mem_product.1 he1).1, ?_⟩
      have := he2.trans hxw.symm
      simp only [hv] at this
      rw [hmk] at this
      simpa using Γ.neg_mem this
    set γ : (Fin n × ℂ) × Bool → ℂ := fun e => facetEnd P (a e.1.1) e.1.2 e.2 - x with hγ
    set ψ : (Fin n × ℂ) × Bool → ℂ × ℂ × Bool :=
      fun e => (a e.1.1 + -γ e, e.1.2 + -γ e, e.2) with hψ
    have hψS : ∀ e' ∈ F.image ψ, IsVoronoiNeighbor P e'.1 e'.2.1 ∧
        facetEnd P e'.1 e'.2.1 e'.2.2 = x := by
      intro e' he'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 he'
      obtain ⟨hn, hmemΓ⟩ := hmemF e he
      have hneg : -γ e ∈ Γ := Γ.neg_mem hmemΓ
      refine ⟨(isVoronoiNeighbor_periodicSites_add Γ a hneg).2 hn, ?_⟩
      simp only [ψ]
      rw [facetEnd_periodicSites_add Γ a hneg]
      simp only [γ]; ring
    have hψinj : Set.InjOn ψ F := by
      rintro ⟨⟨i₁, q₁⟩, b₁⟩ h₁ ⟨⟨i₂, q₂⟩, b₂⟩ h₂ heq
      simp only [ψ, Prod.mk.injEq] at heq
      obtain ⟨ha', hq', hb⟩ := heq
      subst hb
      have hΓ₁ := (hmemF _ h₁).2
      have hΓ₂ := (hmemF _ h₂).2
      have hdiff : a i₁ - a i₂ ∈ Γ := by
        have : a i₁ - a i₂ = γ ((i₁, q₁), b₁) - γ ((i₂, q₂), b₁) := by
          linear_combination ha'
        rw [this]
        exact Γ.sub_mem hΓ₁ hΓ₂
      have hi := ha i₁ i₂ hdiff
      subst hi
      have hγeq : γ ((i₁, q₁), b₁) = γ ((i₁, q₂), b₁) := by linear_combination -ha'
      have hq : q₁ = q₂ := by linear_combination hq' + hγeq
      rw [hq]
    calc ∑ e ∈ F, sectorBaseAngle P (a e.1.1) e.1.2 e.2
        = ∑ e ∈ F, sectorBaseAngle P (ψ e).1 (ψ e).2.1 (ψ e).2.2 :=
          Finset.sum_congr rfl fun e he => by
            simp only [ψ]
            rw [sectorBaseAngle_periodicSites_add Γ a (Γ.neg_mem (hmemF e he).2)]
      _ = ∑ e' ∈ F.image ψ, sectorBaseAngle P e'.1 e'.2.1 e'.2.2 :=
          (Finset.sum_image (f := fun e' => sectorBaseAngle P e'.1 e'.2.1 e'.2.2) hψinj).symm
      _ ≤ 2 * π := sum_sectorBaseAngle_le hP x _ hψS

end Periodic

end SandierSerfaty

end
