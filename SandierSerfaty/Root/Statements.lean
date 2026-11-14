/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Statements.Jellium.Defs.ConfigEnergy
public import SandierSerfaty.Statements.Jellium.Defs.Cube
public import SandierSerfaty.Statements.Jellium.Defs.CubeEnergy
public import SandierSerfaty.Statements.Jellium.Defs.CubeRadius
public import SandierSerfaty.Statements.Jellium.Defs.Elec
public import SandierSerfaty.Statements.Jellium.Defs.JelliumEnergy
public import SandierSerfaty.Statements.Jellium.Defs.NeutralEnergy
public import SandierSerfaty.Statements.Jellium.Defs.NnRadius
public import SandierSerfaty.Statements.Jellium.Defs.TriangularField
public import SandierSerfaty.Statements.Jellium.Defs.TruncField
public import SandierSerfaty.Statements.Jellium.Defs.TruncLog
public import SandierSerfaty.Statements.Jellium.Theorems.ExistsJelliumEnergyEqNeutralEnergy
public import SandierSerfaty.Statements.Jellium.Theorems.TriangularFieldSpec
public import SandierSerfaty.Statements.Sphere.Defs.BhsConstant
public import SandierSerfaty.Statements.Sphere.Defs.LogConfigEnergy
public import SandierSerfaty.Statements.Sphere.Defs.LogPairEnergy
public import SandierSerfaty.Statements.Sphere.Defs.SphereLogEnergy
public import SandierSerfaty.Statements.Torus.Defs.IsTorusPotential
public import SandierSerfaty.Statements.Torus.Defs.SquareLattice
public import SandierSerfaty.Statements.Torus.Defs.TorusDomain
public import SandierSerfaty.Statements.Torus.Defs.TorusEnergy
public import SandierSerfaty.Statements.Torus.Defs.TorusPotential
public import SandierSerfaty.Statements.Torus.Defs.TriangularEnergy
public import SandierSerfaty.Statements.Torus.Defs.TriangularLattice
public import SandierSerfaty.Statements.Torus.Theorems.ExistsUniqueIsTorusPotential
public import SandierSerfaty.Statements.Torus.Theorems.TendstoTorusEnergy
public import SandierSerfaty.Statements.Torus.Theorems.TorusDomainSpec
public import SandierSerfaty.Statements.Torus.Theorems.TorusPotentialSpec
public import SandierSerfaty.Statements.Whole.Defs.IsAdmissibleField
public import SandierSerfaty.Statements.Whole.Defs.IsCutoffFamily
public import SandierSerfaty.Statements.Whole.Defs.LocalEnergy
public import SandierSerfaty.Statements.Whole.Defs.PaperTriangularField
public import SandierSerfaty.Statements.Whole.Defs.PunctureFunctional
public import SandierSerfaty.Statements.Whole.Defs.WholeEnergy
public import SandierSerfaty.Statements.Whole.Theorems.PaperTriangularFieldSpec
public import SandierSerfaty.Statements.Whole.Theorems.TendstoPunctureFunctional

/-!
# Root part

Part of the generated root `SandierSerfaty.lean`. It imports the modules of one area of the library (the imports
above), except those that the root skips. It is generated; do not edit it by hand, and never import it.
-/

public section
