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
import SandierSerfaty.Statements.Jellium.Theorems.TriangularFieldSpec
import SandierSerfaty.Statements.Jellium.Theorems.ExistsJelliumEnergyEqNeutralEnergy
import SandierSerfaty.Statements.Whole.Theorems.PaperTriangularFieldSpec
import SandierSerfaty.Statements.Whole.Theorems.TendstoPunctureFunctional

/-!
# Axioms of the theorems of the core library

Prints the axioms of the eight stated theorems that do not depend on the numerical certificate. Run
as `lake env lean scripts/AxiomsCore.lean` after `lake build`; `python3 scripts/check-axioms.py
--core` runs it and checks that each theorem depends on no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`. The five theorems that rest on the certificate are in
`scripts/Axioms.lean`.
-/

#print axioms SandierSerfaty.torusDomain_spec
#print axioms SandierSerfaty.existsUnique_isTorusPotential
#print axioms SandierSerfaty.torusPotential_spec
#print axioms SandierSerfaty.tendsto_torusEnergy
#print axioms SandierSerfaty.triangularField_spec
#print axioms SandierSerfaty.exists_jelliumEnergy_eq_neutralEnergy
#print axioms SandierSerfaty.paperTriangularField_spec
#print axioms SandierSerfaty.tendsto_punctureFunctional
