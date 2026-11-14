/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.CertData.Lam.Q00
public import SandierSerfaty.CertData.Lam.Q01
public import SandierSerfaty.CertData.Lam.Q02
public import SandierSerfaty.CertData.Lam.Q03
public import SandierSerfaty.CertData.Lam.Q04
public import SandierSerfaty.CertData.Lam.E00
public import SandierSerfaty.CertData.Lam.E01
public import SandierSerfaty.CertData.Lam.E02
public import SandierSerfaty.CertData.Lam.E03
public import SandierSerfaty.CertData.Lam.E04
public import SandierSerfaty.CertData.Lam.Pre

/-!
# The fine λ, assembled

The segments joined (`Assemble.forall_lt_succ_of`, `Lambda.qSum_of_chain`, `Lambda.eSum_of_chain`) and `Lambda.lamFine_eq_of`: `lamFine flTbl dLit lamPar = some lamFLit`.
-/

public section

namespace SandierSerfaty.CertData

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Certificate.Query SandierSerfaty.Certificate.Lambda SandierSerfaty.Certificate.Assemble

/-- The segment `c` of the sum Q. -/
abbrev SegQ (c : Nat) : Prop :=
  runSeg (qTerm flTbl cQLit) lamL (lamL * c) (qCk c).1 (qCk c).2 (qCk (c + 1)).1 (qCk (c + 1)).2 = true

theorem q_all : ∀ c, c < 45 → SegQ c := by
  have h0 : ∀ c, c < 0 → SegQ c := forall_lt_zero'
  have h1 : ∀ c, c < 1 → SegQ c := forall_lt_succ_of h0 q_0
  have h2 : ∀ c, c < 2 → SegQ c := forall_lt_succ_of h1 q_1
  have h3 : ∀ c, c < 3 → SegQ c := forall_lt_succ_of h2 q_2
  have h4 : ∀ c, c < 4 → SegQ c := forall_lt_succ_of h3 q_3
  have h5 : ∀ c, c < 5 → SegQ c := forall_lt_succ_of h4 q_4
  have h6 : ∀ c, c < 6 → SegQ c := forall_lt_succ_of h5 q_5
  have h7 : ∀ c, c < 7 → SegQ c := forall_lt_succ_of h6 q_6
  have h8 : ∀ c, c < 8 → SegQ c := forall_lt_succ_of h7 q_7
  have h9 : ∀ c, c < 9 → SegQ c := forall_lt_succ_of h8 q_8
  have h10 : ∀ c, c < 10 → SegQ c := forall_lt_succ_of h9 q_9
  have h11 : ∀ c, c < 11 → SegQ c := forall_lt_succ_of h10 q_10
  have h12 : ∀ c, c < 12 → SegQ c := forall_lt_succ_of h11 q_11
  have h13 : ∀ c, c < 13 → SegQ c := forall_lt_succ_of h12 q_12
  have h14 : ∀ c, c < 14 → SegQ c := forall_lt_succ_of h13 q_13
  have h15 : ∀ c, c < 15 → SegQ c := forall_lt_succ_of h14 q_14
  have h16 : ∀ c, c < 16 → SegQ c := forall_lt_succ_of h15 q_15
  have h17 : ∀ c, c < 17 → SegQ c := forall_lt_succ_of h16 q_16
  have h18 : ∀ c, c < 18 → SegQ c := forall_lt_succ_of h17 q_17
  have h19 : ∀ c, c < 19 → SegQ c := forall_lt_succ_of h18 q_18
  have h20 : ∀ c, c < 20 → SegQ c := forall_lt_succ_of h19 q_19
  have h21 : ∀ c, c < 21 → SegQ c := forall_lt_succ_of h20 q_20
  have h22 : ∀ c, c < 22 → SegQ c := forall_lt_succ_of h21 q_21
  have h23 : ∀ c, c < 23 → SegQ c := forall_lt_succ_of h22 q_22
  have h24 : ∀ c, c < 24 → SegQ c := forall_lt_succ_of h23 q_23
  have h25 : ∀ c, c < 25 → SegQ c := forall_lt_succ_of h24 q_24
  have h26 : ∀ c, c < 26 → SegQ c := forall_lt_succ_of h25 q_25
  have h27 : ∀ c, c < 27 → SegQ c := forall_lt_succ_of h26 q_26
  have h28 : ∀ c, c < 28 → SegQ c := forall_lt_succ_of h27 q_27
  have h29 : ∀ c, c < 29 → SegQ c := forall_lt_succ_of h28 q_28
  have h30 : ∀ c, c < 30 → SegQ c := forall_lt_succ_of h29 q_29
  have h31 : ∀ c, c < 31 → SegQ c := forall_lt_succ_of h30 q_30
  have h32 : ∀ c, c < 32 → SegQ c := forall_lt_succ_of h31 q_31
  have h33 : ∀ c, c < 33 → SegQ c := forall_lt_succ_of h32 q_32
  have h34 : ∀ c, c < 34 → SegQ c := forall_lt_succ_of h33 q_33
  have h35 : ∀ c, c < 35 → SegQ c := forall_lt_succ_of h34 q_34
  have h36 : ∀ c, c < 36 → SegQ c := forall_lt_succ_of h35 q_35
  have h37 : ∀ c, c < 37 → SegQ c := forall_lt_succ_of h36 q_36
  have h38 : ∀ c, c < 38 → SegQ c := forall_lt_succ_of h37 q_37
  have h39 : ∀ c, c < 39 → SegQ c := forall_lt_succ_of h38 q_38
  have h40 : ∀ c, c < 40 → SegQ c := forall_lt_succ_of h39 q_39
  have h41 : ∀ c, c < 41 → SegQ c := forall_lt_succ_of h40 q_40
  have h42 : ∀ c, c < 42 → SegQ c := forall_lt_succ_of h41 q_41
  have h43 : ∀ c, c < 43 → SegQ c := forall_lt_succ_of h42 q_42
  have h44 : ∀ c, c < 44 → SegQ c := forall_lt_succ_of h43 q_43
  have h45 : ∀ c, c < 45 → SegQ c := forall_lt_succ_of h44 q_44
  exact h45

/-- The segment `c` of the sum E. -/
abbrev SegE (c : Nat) : Prop :=
  runSeg (eTerm flTbl cELit) lamL (lamL * c) (eCk c).1 (eCk c).2 (eCk (c + 1)).1 (eCk (c + 1)).2 = true

theorem e_all : ∀ c, c < 45 → SegE c := by
  have h0 : ∀ c, c < 0 → SegE c := forall_lt_zero'
  have h1 : ∀ c, c < 1 → SegE c := forall_lt_succ_of h0 e_0
  have h2 : ∀ c, c < 2 → SegE c := forall_lt_succ_of h1 e_1
  have h3 : ∀ c, c < 3 → SegE c := forall_lt_succ_of h2 e_2
  have h4 : ∀ c, c < 4 → SegE c := forall_lt_succ_of h3 e_3
  have h5 : ∀ c, c < 5 → SegE c := forall_lt_succ_of h4 e_4
  have h6 : ∀ c, c < 6 → SegE c := forall_lt_succ_of h5 e_5
  have h7 : ∀ c, c < 7 → SegE c := forall_lt_succ_of h6 e_6
  have h8 : ∀ c, c < 8 → SegE c := forall_lt_succ_of h7 e_7
  have h9 : ∀ c, c < 9 → SegE c := forall_lt_succ_of h8 e_8
  have h10 : ∀ c, c < 10 → SegE c := forall_lt_succ_of h9 e_9
  have h11 : ∀ c, c < 11 → SegE c := forall_lt_succ_of h10 e_10
  have h12 : ∀ c, c < 12 → SegE c := forall_lt_succ_of h11 e_11
  have h13 : ∀ c, c < 13 → SegE c := forall_lt_succ_of h12 e_12
  have h14 : ∀ c, c < 14 → SegE c := forall_lt_succ_of h13 e_13
  have h15 : ∀ c, c < 15 → SegE c := forall_lt_succ_of h14 e_14
  have h16 : ∀ c, c < 16 → SegE c := forall_lt_succ_of h15 e_15
  have h17 : ∀ c, c < 17 → SegE c := forall_lt_succ_of h16 e_16
  have h18 : ∀ c, c < 18 → SegE c := forall_lt_succ_of h17 e_17
  have h19 : ∀ c, c < 19 → SegE c := forall_lt_succ_of h18 e_18
  have h20 : ∀ c, c < 20 → SegE c := forall_lt_succ_of h19 e_19
  have h21 : ∀ c, c < 21 → SegE c := forall_lt_succ_of h20 e_20
  have h22 : ∀ c, c < 22 → SegE c := forall_lt_succ_of h21 e_21
  have h23 : ∀ c, c < 23 → SegE c := forall_lt_succ_of h22 e_22
  have h24 : ∀ c, c < 24 → SegE c := forall_lt_succ_of h23 e_23
  have h25 : ∀ c, c < 25 → SegE c := forall_lt_succ_of h24 e_24
  have h26 : ∀ c, c < 26 → SegE c := forall_lt_succ_of h25 e_25
  have h27 : ∀ c, c < 27 → SegE c := forall_lt_succ_of h26 e_26
  have h28 : ∀ c, c < 28 → SegE c := forall_lt_succ_of h27 e_27
  have h29 : ∀ c, c < 29 → SegE c := forall_lt_succ_of h28 e_28
  have h30 : ∀ c, c < 30 → SegE c := forall_lt_succ_of h29 e_29
  have h31 : ∀ c, c < 31 → SegE c := forall_lt_succ_of h30 e_30
  have h32 : ∀ c, c < 32 → SegE c := forall_lt_succ_of h31 e_31
  have h33 : ∀ c, c < 33 → SegE c := forall_lt_succ_of h32 e_32
  have h34 : ∀ c, c < 34 → SegE c := forall_lt_succ_of h33 e_33
  have h35 : ∀ c, c < 35 → SegE c := forall_lt_succ_of h34 e_34
  have h36 : ∀ c, c < 36 → SegE c := forall_lt_succ_of h35 e_35
  have h37 : ∀ c, c < 37 → SegE c := forall_lt_succ_of h36 e_36
  have h38 : ∀ c, c < 38 → SegE c := forall_lt_succ_of h37 e_37
  have h39 : ∀ c, c < 39 → SegE c := forall_lt_succ_of h38 e_38
  have h40 : ∀ c, c < 40 → SegE c := forall_lt_succ_of h39 e_39
  have h41 : ∀ c, c < 41 → SegE c := forall_lt_succ_of h40 e_40
  have h42 : ∀ c, c < 42 → SegE c := forall_lt_succ_of h41 e_41
  have h43 : ∀ c, c < 43 → SegE c := forall_lt_succ_of h42 e_42
  have h44 : ∀ c, c < 44 → SegE c := forall_lt_succ_of h43 e_43
  have h45 : ∀ c, c < 45 → SegE c := forall_lt_succ_of h44 e_44
  exact h45

/-- The first sum. -/
theorem qsum_ok : qSum flTbl cQLit = some (qCk 45).2 :=
  qSum_of_chain (L := lamL) (C := 45) rfl q0_ok q_all

/-- The second sum. -/
theorem esum_ok : eSum flTbl cELit = some (eCk 45).2 :=
  eSum_of_chain (L := lamL) (C := 45) rfl e0_ok e_all

/-- **The fine `λ` evaluates to the literal enclosure.** -/
theorem lamFine_ok : lamFine flTbl dLit lamPar = some lamFLit :=
  lamFine_eq_of lh_ok sq_ok cB_ok cY_ok fp_ok fp1_ok fr_ok er_ok cQ_ok cE_ok qsum_ok esum_ok fin_ok

end SandierSerfaty.CertData
