/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Sylvia Serfaty
-/
module

public import SandierSerfaty.Screening.AeAtMostOne
public import SandierSerfaty.Screening.Averaging
public import SandierSerfaty.Screening.CarryField
public import SandierSerfaty.Screening.ChartBox
public import SandierSerfaty.Screening.ColumnCut
public import SandierSerfaty.Screening.ColumnCutProps
public import SandierSerfaty.Screening.ColumnFiller
public import SandierSerfaty.Screening.ColumnFlux
public import SandierSerfaty.Screening.ColumnMass
public import SandierSerfaty.Screening.ColumnPartition
public import SandierSerfaty.Screening.CubeCutoff
public import SandierSerfaty.Screening.CubeEnergyBound
public import SandierSerfaty.Screening.Defs
public import SandierSerfaty.Screening.Density
public import SandierSerfaty.Screening.Depth
public import SandierSerfaty.Screening.EnergyExpansion
public import SandierSerfaty.Screening.FieldGluing
public import SandierSerfaty.Screening.FillerPartition
public import SandierSerfaty.Screening.FluxCell
public import SandierSerfaty.Screening.KeepDrop
public import SandierSerfaty.Screening.LipschitzApprox
public import SandierSerfaty.Screening.LocEnergy
public import SandierSerfaty.Screening.LocalCount
public import SandierSerfaty.Screening.MassCuts
public import SandierSerfaty.Screening.Mollify
public import SandierSerfaty.Screening.Monotonicity
public import SandierSerfaty.Screening.NeumannPairing
public import SandierSerfaty.Screening.NeutralBridge
public import SandierSerfaty.Screening.Pairing
public import SandierSerfaty.Screening.PieceField
public import SandierSerfaty.Screening.Pinwheel
public import SandierSerfaty.Screening.PinwheelRegions
public import SandierSerfaty.Screening.ProjectionGradient
public import SandierSerfaty.Screening.ProjectionTest
public import SandierSerfaty.Screening.ProjectionTorus
public import SandierSerfaty.Screening.RadialFields
public import SandierSerfaty.Screening.RectangleCore
public import SandierSerfaty.Screening.RectangleEnergy
public import SandierSerfaty.Screening.RectangleSolver
public import SandierSerfaty.Screening.ScreenAssembly
public import SandierSerfaty.Screening.ScreenConstants
public import SandierSerfaty.Screening.ScreenData
public import SandierSerfaty.Screening.ScreenEnergy
public import SandierSerfaty.Screening.ScreenFluxEnergy
public import SandierSerfaty.Screening.ScreenNeumann
public import SandierSerfaty.Screening.ScreenPoints
public import SandierSerfaty.Screening.ScreenPointwise
public import SandierSerfaty.Screening.ScreenSign
public import SandierSerfaty.Screening.ScreenTheorem
public import SandierSerfaty.Screening.SoftCut
public import SandierSerfaty.Screening.SoftCutBounds
public import SandierSerfaty.Screening.SquareCell
public import SandierSerfaty.Screening.TorusProjection
public import SandierSerfaty.Screening.TruncDiff
public import SandierSerfaty.Screening.TruncFieldWeak
public import SandierSerfaty.Screening.TruncLogCalculus
public import SandierSerfaty.Screening.TruncLogPairing

/-!
# Root part

Part of the generated root `SandierSerfaty.lean`. It imports the modules of one area of the library (the imports
above), except those that the root skips. It is generated; do not edit it by hand, and never import it.
-/

public section
