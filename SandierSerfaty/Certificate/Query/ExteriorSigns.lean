/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Certificate.Query.LamSound

/-!
# The exterior sign fields of the certificate goal (`f_l_pos`, `slope_pos`)

`f_l_pos_slope_pos_of_certificate` proves the two `Assembly.CertificateGoal` fields

  `0 < Cal.f l`   and   `0 < -π · Cal.B l - Cal.lam / 2`

(paper `comp:tail-signs`, assertions A4, A5 (λ), A6) from the *finite data of the
certificate*, with the exact `Cal` objects in the conclusion:

* `hc : FiniteCore` (the finite-core premise of §5, discharged by the A2 checks);
* `hd : d.Valid`, `hp2`: valid interval constants of the basis (A1, `Basis.mkData_valid`);
* `hT : T.Encl a`: the stored table is realized by real nodes (A3: `Table.chunks_sound_trunc`,
  `Query.cell_enclosures`);
* `hlam : lamEnc T d N rad = some lamI`: the coarse `λ` quadrature (`Query.Lam`);
* `hnR`, `hnL`: the node tuples at `R₀` and `l` enclose `f̃₀(R₀)`, `ẽ(R₀)`, `f̃₀(l)`
  (`Table.TupEncl.mem_trunc`);
* `hchk`: the interval test `Query.a6Check` on the widened enclosures (`Query.Const`).

Every hypothesis is either a `Bool` check evaluated by `decide +kernel` on literals or a soundness statement
of the table chunks proved elsewhere; none is the conclusion. The data are produced by `CertGen`.
-/

open Set

public section

namespace SandierSerfaty.Certificate.Query

open SandierSerfaty.Certificate.Arith SandierSerfaty.Certificate.Basis SandierSerfaty.Certificate.Table
open SandierSerfaty.Calibration SandierSerfaty.Tails

theorem R₀_mem_Icc : R₀ ∈ Icc Calibration.b Calibration.l :=
  ⟨(Calibration.b_lt_p.trans Calibration.p_lt_R₀).le, Calibration.R₀_lt_l.le⟩

theorem l_mem_Icc : Calibration.l ∈ Icc Calibration.b Calibration.l :=
  ⟨(Calibration.b_lt_p.trans (Calibration.p_lt_R₀.trans Calibration.R₀_lt_l)).le, le_rfl⟩

/-- **`f_l_pos` and `slope_pos` from the finite data of the certificate.** -/
theorem f_l_pos_slope_pos_of_certificate (hc : FiniteCore) {d : BasisData} (hd : d.Valid)
    (hp2 : IV.posB d.p2 = true) {T : ITable} {a : ℕ → ℝ} (hT : T.Encl a) {N rad : ℕ} (hN : 0 < N)
    (hrad : (2 : ℝ) ^ 128 / 10 ^ 11 ≤ rad) {lamI : IV 128} (hlam : lamEnc T d N rad = some lamI)
    {X : IV 128} (hX : IV.posB X = true) (hlX : IV.Mem Calibration.l X) {nR nL : Tup}
    (hnR : IV.Mem (Trunc.f₀ R₀) nR.f0 ∧ IV.Mem (Trunc.e R₀) nR.e0)
    (hnL : IV.Mem (Trunc.f₀ Calibration.l) nL.f0)
    (hchk : a6Check d.pi d.r0 (IV.addRad nL.f0 rad) (IV.addRad nR.f0 rad) (IV.addRad nR.e0 rad)
      (IV.addRad (basis d 5 X).bsum.c0 rad) lamI = true) :
    0 < Calibration.f Calibration.l ∧ 0 < -Real.pi * Calibration.B Calibration.l - Calibration.lam / 2 :=
  a6_sound hchk hd.mpi hd.mr0 (mem_f0_exact hc l_mem_Icc hnL hrad) (mem_f0_exact hc R₀_mem_Icc hnR.1 hrad)
    (mem_e_exact hc R₀_mem_Icc hnR.2 hrad) (mem_B_l hd hX hlX hrad) (lamEnc_sound hc hT hd hp2 hN hrad hlam)

end SandierSerfaty.Certificate.Query
