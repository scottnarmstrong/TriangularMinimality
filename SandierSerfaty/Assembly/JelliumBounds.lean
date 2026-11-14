/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Assembly.NeutralEnergyOfScreening
public import SandierSerfaty.Assembly.TriangularConfigEnergy
public import SandierSerfaty.Screening.ScreenTheorem

/-!
# The jellium bounds from the square-torus bound

The screening theorem I4 (`SandierSerfaty.Screening.exists_screened_neumannChargeField`, the screening note's
Theorem 4.1) is proved, so the assemblies `neutralEnergyBound_of_screening_torusBound` and `triangularConfigEnergy_of_neutralEnergyBound` reduce the neutral-energy bound
`div_two_pi_triangularEnergy_le_neutralEnergy` and the value of the jellium energy of the triangular lattice
`configEnergy_triangularLattice` (both in Serfaty's Chapter 11) to the square-torus bound (paper Theorem 1.2)
alone.
-/

public section

namespace SandierSerfaty.Assembly

/-- The screening statement holds: it is the screening theorem I4. -/
theorem screeningStatement : ScreeningStatement := fun hmLo hm =>
  SandierSerfaty.Screening.exists_screened_neumannChargeField hmLo hm

/-- The neutral-energy bound follows from the square-torus bound. -/
theorem neutralEnergyBound_of_torusBound (h : TorusBoundStatement) : NeutralEnergyBoundStatement := neutralEnergyBound_of_screening_torusBound screeningStatement h

/-- The jellium energy of the triangular lattice follows from the square-torus bound. -/
theorem triangularConfigEnergy_of_torusBound (h : TorusBoundStatement) : TriangularConfigEnergyStatement := triangularConfigEnergy_of_neutralEnergyBound (neutralEnergyBound_of_torusBound h)

end SandierSerfaty.Assembly

end
