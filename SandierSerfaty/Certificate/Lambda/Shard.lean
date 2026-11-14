/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Lambda.Eval
public import SandierSerfaty.Certificate.Assemble.Lists

/-!
# Kernel shards of the fine `λ` quadrature

One evaluation of `Lambda.lamFine` with the paper's `Nq = Ne = 45000` costs about 8 ms per step in the kernel, far
beyond one declaration. The two midpoint sums are cut into segments of `L` steps with literal checkpoints (the pair
index and the accumulator after every segment, proposed by the generator), and the prelude (the root `t₀`, the two
lookups, the four point values, the two integrand contexts) is stated with literal results:

* `runLoopSt`, `runSeg`: `n` steps of `runLoop` from a state, compared with a literal state (structural equality);
* `runLoop_chain`, `qSum_of_chain`, `eSum_of_chain`: a sum from its segments;
* `tupEqB`, `optTupEqB`, `qctxEqB`: structural equalities of tuples and contexts (`Assemble.ivEqB` for intervals);
* `lamFine_eq_of`: `lamFine F d P = some I` from the prelude equalities, the two sums and the last stage.

No new mathematics: every statement is about the Boolean definitions of `Lambda.Eval`; the soundness of the
result is `Lambda.lamFine_sound`. Kernel rules: strict.
-/

-- kernel-rules: strict

@[expose] public section

namespace SandierSerfaty.Certificate.Lambda

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Assemble

/-! ### Structural equalities -/

/-- Equality of tuples. -/
def tupEqB (a b : Tup) : Bool :=
  and (and (ivEqB a.f0 b.f0) (and (ivEqB a.f1 b.f1) (ivEqB a.f2 b.f2)))
    (and (ivEqB a.e0 b.e0) (and (ivEqB a.e1 b.e1) (ivEqB a.e2 b.e2)))

/-- `o = some t`. -/
def optTupEqB : Option Tup → Tup → Bool
  | none, _ => false
  | some a, b => tupEqB a b

/-- Equality of integrand contexts. -/
def qctxEqB (a b : QCtx) : Bool :=
  and (and (and (ivEqB a.p b.p) (ivEqB a.p2 b.p2)) (and (ivEqB a.A b.A) (ivEqB a.W b.W)))
    (and (and (Nat.beq a.N b.N) (Nat.beq a.rad b.rad))
      (and (ivEqB a.F0 b.F0) (and (ivEqB a.B1 b.B1) (ivEqB a.B2 b.B2))))

theorem tupEqB_eq {a b : Tup} (h : tupEqB a b = true) : a = b := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := b
  simp only [tupEqB, Bool.and_eq_true] at h
  obtain ⟨⟨h0, h1, h2⟩, h3, h4, h5⟩ := h
  rw [ivEqB_eq h0, ivEqB_eq h1, ivEqB_eq h2, ivEqB_eq h3, ivEqB_eq h4, ivEqB_eq h5]

theorem optTupEqB_sound : ∀ {o : Option Tup} {t : Tup}, optTupEqB o t = true → o = some t
  | none, _, h => by simp [optTupEqB] at h
  | some a, _, h => by rw [tupEqB_eq h]

theorem qctxEqB_eq {a b : QCtx} (h : qctxEqB a b = true) : a = b := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8⟩ := b
  simp only [qctxEqB, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2, h3⟩, ⟨h4, h5⟩, h6, h7, h8⟩ := h
  rw [ivEqB_eq h0, ivEqB_eq h1, ivEqB_eq h2, ivEqB_eq h3, h4, h5, ivEqB_eq h6, ivEqB_eq h7, ivEqB_eq h8]

/-! ### Segments of the midpoint sums -/

/-- The state (pair index, accumulator) after `n` steps of `runLoop` from the step `k`. -/
def runLoopSt (step : Nat → Nat → Option (Nat × IV 128)) : Nat → Nat → Nat → IV 128 → Option (Nat × IV 128)
  | 0, _, i, acc => some (i, acc)
  | Nat.succ n, k, i, acc =>
    match step k i with
    | none => none
    | some r => runLoopSt step n (Nat.succ k) r.1 (IV.add acc r.2)

/-- `n` steps from the step `k` and the state `(i, acc)` end in the state `(i', acc')`. -/
def runSeg (step : Nat → Nat → Option (Nat × IV 128)) (n k i : Nat) (acc : IV 128) (i' : Nat) (acc' : IV 128) :
    Bool :=
  match runLoopSt step n k i acc with
  | none => false
  | some r => and (Nat.beq r.1 i') (ivEqB r.2 acc')

theorem runLoop_of_seg {step : Nat → Nat → Option (Nat × IV 128)} {m : Nat} :
    ∀ {n k i : Nat} {acc : IV 128} {i' : Nat} {acc' : IV 128}, runSeg step n k i acc i' acc' = true →
    runLoop step (n + m) k i acc = runLoop step m (k + n) i' acc'
  | 0, k, i, acc, i', acc', h => by
    simp only [runSeg, runLoopSt, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨rfl, h2⟩ := h
    rw [ivEqB_eq h2]; simp
  | n + 1, k, i, acc, i', acc', h => by
    simp only [runSeg, runLoopSt] at h
    rw [Nat.add_right_comm]
    simp only [runLoop]
    cases hs : step k i with
    | none => simp [hs] at h
    | some r =>
      simp only [hs] at h ⊢
      have := runLoop_of_seg (m := m) (n := n) (k := k + 1) (i := r.1) (acc := IV.add acc r.2) (i' := i')
        (acc' := acc') (by simpa [runSeg] using h)
      rw [this, show k + 1 + n = k + (n + 1) by omega]

/-- **A sum from its segments**: the segments `c' < C` of `L` steps, from the checkpoints `ck c'` to `ck (c' + 1)`. -/
theorem runLoop_chain {step : Nat → Nat → Option (Nat × IV 128)} {L : Nat} {ck : Nat → Nat × IV 128} {m : Nat} :
    ∀ C, (∀ c, c < C → runSeg step L (L * c) (ck c).1 (ck c).2 (ck (c + 1)).1 (ck (c + 1)).2 = true) →
      runLoop step (L * C + m) 0 (ck 0).1 (ck 0).2 = runLoop step m (L * C) (ck C).1 (ck C).2
  | 0, _ => by simp
  | C + 1, h => by
    have ih := runLoop_chain (m := L + m) C fun c hc => h c (by omega)
    have hs := runLoop_of_seg (m := m) (h C (by omega))
    rw [show L * (C + 1) + m = L * C + (L + m) by rw [Nat.mul_succ]; omega, ih, hs, ← Nat.mul_succ]

/-- **The first sum from its segments** (`c.N = L C` steps, starting from the state `(0, 0)`). -/
theorem qSum_of_chain {F : FTable} {c : QCtx} {L C : Nat} {ck : Nat → Nat × IV 128} (hN : c.N = L * C)
    (h0 : and (Nat.beq (ck 0).1 0) (ivEqB (ck 0).2 (IV.ofNat 0)) = true)
    (hs : ∀ c', c' < C → runSeg (qTerm F c) L (L * c') (ck c').1 (ck c').2 (ck (c' + 1)).1 (ck (c' + 1)).2 = true) :
    qSum F c = some (ck C).2 := by
  simp only [Bool.and_eq_true, Nat.beq_eq] at h0
  have := runLoop_chain (m := 0) C hs
  rw [Nat.add_zero, h0.1, ivEqB_eq h0.2] at this
  unfold qSum
  rw [hN, this]
  rfl

/-- **The second sum from its segments.** -/
theorem eSum_of_chain {F : FTable} {c : QCtx} {L C : Nat} {ck : Nat → Nat × IV 128} (hN : c.N = L * C)
    (h0 : and (Nat.beq (ck 0).1 0) (ivEqB (ck 0).2 (IV.ofNat 0)) = true)
    (hs : ∀ c', c' < C → runSeg (eTerm F c) L (L * c') (ck c').1 (ck c').2 (ck (c' + 1)).1 (ck (c' + 1)).2 = true) :
    eSum F c = some (ck C).2 := by
  simp only [Bool.and_eq_true, Nat.beq_eq] at h0
  have := runLoop_chain (m := 0) C hs
  rw [Nat.add_zero, h0.1, ivEqB_eq h0.2] at this
  unfold eSum
  rw [hN, this]
  rfl

/-! ### The composition -/

/-- **`lamFine` from its parts**: the proposed root `lh` of `t₀² = p² + s₀²` and its check, the two lookups, the four
point values, the two sums on the literal contexts `cQ`, `cE` (identified with the computed ones) and the last
stage. -/
theorem lamFine_eq_of {F : FTable} {d : BasisData} {P : LamPar} {lh : Nat × Nat} {cB cY : Tup}
    {FP FP1 FR ER IQ IE I : IV 128} {cQ cE : QCtx}
    (hlh : and (Nat.beq (IV.sqrtProposal (IV.add d.p2 (IV.sq (s0Of P)))).1 lh.1)
      (Nat.beq (IV.sqrtProposal (IV.add d.p2 (IV.sq (s0Of P)))).2 lh.2) = true)
    (hsq : IV.sqrtCheck (IV.add d.p2 (IV.sq (s0Of P))) lh.1 lh.2 = true)
    (hB : optTupEqB (lookup F.T (IV.hull d.p d.r0)) cB = true)
    (hY : optTupEqB (lookup F.T (IV.hull d.p (IV.ofNatPair lh.1 lh.2))) cY = true)
    (hFP : optEqB (fPt F P.rad d.p) FP = true) (hFP1 : optEqB (f1Pt F P.rad d.p) FP1 = true)
    (hFR : optEqB (fPt F P.rad d.r0) FR = true) (hER : optEqB (ePt F P.rad d.r0) ER = true)
    (hcQ : qctxEqB (qCtxOf d P.Nq P.rad (s0Of P) cB FP) cQ = true)
    (hcE : qctxEqB (eCtxOf d P.Ne P.rad cB) cE = true)
    (hQ : qSum F cQ = some IQ) (hE : eSum F cE = some IE)
    (hfin : optEqB (lamFineS d P (s0Of P) (IV.ofNatPair lh.1 lh.2) cY FP FP1 FR ER (some IQ) (some IE)) I = true) :
    lamFine F d P = some I := by
  have e0 : IV.sqrtProposal (IV.add d.p2 (IV.sq (s0Of P))) = lh := by
    simp only [Bool.and_eq_true, Nat.beq_eq] at hlh
    exact Prod.ext hlh.1 hlh.2
  unfold lamFine lamFineT
  rw [e0, hsq, optTupEqB_sound hB, optTupEqB_sound hY]
  simp only [Bool.cond_true, lamFineL]
  rw [optEqB_sound hFP, optEqB_sound hFP1, optEqB_sound hFR, optEqB_sound hER]
  simp only [lamFineP]
  rw [qctxEqB_eq hcQ, qctxEqB_eq hcE, hQ, hE]
  exact optEqB_sound hfin

end SandierSerfaty.Certificate.Lambda
