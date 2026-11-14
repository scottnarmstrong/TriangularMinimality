/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec
import SandierSerfaty.Statements.Torus.Theorems.ExistsUniqueIsTorusPotential
import SandierSerfaty.Statements.Torus.Theorems.TorusPotentialSpec
import SandierSerfaty.Statements.Torus.Theorems.TendstoTorusEnergy
import SandierSerfaty.Statements.Torus.Theorems.MulTriangularEnergyLeTorusEnergy
import SandierSerfaty.Statements.Jellium.Theorems.TriangularFieldSpec
import SandierSerfaty.Statements.Jellium.Theorems.ExistsJelliumEnergyEqNeutralEnergy
import SandierSerfaty.Statements.Jellium.Theorems.DivTwoPiTriangularEnergyLeNeutralEnergy
import SandierSerfaty.Statements.Jellium.Theorems.ConfigEnergyTriangularLattice
import SandierSerfaty.Statements.Whole.Theorems.PaperTriangularFieldSpec
import SandierSerfaty.Statements.Whole.Theorems.TendstoPunctureFunctional
import SandierSerfaty.Statements.Whole.Theorems.TriangularEnergyLeWholeEnergy
import SandierSerfaty.Statements.Sphere.Theorems.SphereLogEnergyAsymptotics
import SandierSerfaty.CertData.CertificateGoal

/-!
# Axioms of all the stated theorems

Prints the axioms of the 13 stated theorems and of the kernel certificate. Run as
`lake env lean scripts/Axioms.lean` after `lake build SandierSerfatyCert` (the certificate library
is not a default target); `python3 scripts/check-axioms.py` runs it and checks that each theorem
depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`. In particular none
depends on `Lean.ofReduceBool`, so the certificate is checked by the kernel alone.
-/

#print axioms SandierSerfaty.torusDomain_spec
#print axioms SandierSerfaty.existsUnique_isTorusPotential
#print axioms SandierSerfaty.torusPotential_spec
#print axioms SandierSerfaty.tendsto_torusEnergy
#print axioms SandierSerfaty.mul_triangularEnergy_le_torusEnergy
#print axioms SandierSerfaty.triangularField_spec
#print axioms SandierSerfaty.exists_jelliumEnergy_eq_neutralEnergy
#print axioms SandierSerfaty.div_two_pi_triangularEnergy_le_neutralEnergy
#print axioms SandierSerfaty.configEnergy_triangularLattice
#print axioms SandierSerfaty.paperTriangularField_spec
#print axioms SandierSerfaty.tendsto_punctureFunctional
#print axioms SandierSerfaty.triangularEnergy_le_wholeEnergy
#print axioms SandierSerfaty.sphereLogEnergy_asymptotics
#print axioms SandierSerfaty.CertData.certificateGoal
