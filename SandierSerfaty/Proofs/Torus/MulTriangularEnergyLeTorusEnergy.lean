/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Torus.Defs.SquareLattice
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import SandierSerfaty.Assembly.TorusBoundOfCertificate
public import SandierSerfaty.CertData.CertificateGoal

/-!
# Proof of `SandierSerfaty.mul_triangularEnergy_le_torusEnergy`

`SandierSerfaty.Proofs.mul_triangularEnergy_le_torusEnergy` proves the statement
`SandierSerfaty.mul_triangularEnergy_le_torusEnergy` of the module
`SandierSerfaty.Statements.Torus.Theorems.MulTriangularEnergyLeTorusEnergy`. It is
`Assembly.torusBound_of_certificateGoal` applied to the kernel-checked certificate
`SandierSerfaty.CertData.certificateGoal`, which proves the numerical facts of paper §7.
-/



public section

namespace SandierSerfaty.Proofs

theorem mul_triangularEnergy_le_torusEnergy (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℂ)
    (ha : ∀ i j, a i - a j ∈ squareLattice n → i = j) :
    n * triangularEnergy ≤ torusEnergy (squareLattice n) a :=
  Assembly.torusBound_of_certificateGoal SandierSerfaty.CertData.certificateGoal n hn a ha

end SandierSerfaty.Proofs

end
